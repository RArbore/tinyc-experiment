use core::iter::zip;

use egg::{Id, Symbol};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::analysis::interval::Interval;
use crate::nonssa::{Block, BlockId, Expr, NonSSAFunc};
use crate::ssa::{Dataflow, SSABlock, SSABlockId, SSAProgram};

pub fn create_ssa(nonssa: &FxHashMap<Symbol, NonSSAFunc>) -> SSAProgram {
    let deps = deps(&nonssa);
    let mut context = AIContext {
        deps,
        ssa: Default::default(),
        states: Default::default(),
        created_ssa_blocks: Default::default(),
        callers: FxHashMap::from_iter([("main".into(), FxHashSet::default())]),
        input_analysis: FxHashMap::from_iter([("main".into(), vec![])]),
        output_analysis: Default::default(),
        to_visit: vec![("main".into(), 0)],
    };

    while let Some((func, block)) = context.to_visit.pop() {
        context.visit_block(&nonssa, func, block);
    }

    context.ssa.canon_cfg();
    context.ssa
}

#[derive(Debug)]
struct AIContext {
    deps: FxHashMap<Symbol, FxHashMap<BlockId, FxHashSet<BlockId>>>,
    ssa: SSAProgram,

    states: FxHashMap<(Symbol, BlockId), AIState>,
    created_ssa_blocks: FxHashMap<(Symbol, BlockId), SSABlockId>,

    callers: FxHashMap<Symbol, FxHashSet<Symbol>>,
    input_analysis: FxHashMap<Symbol, Vec<Interval>>,
    output_analysis: FxHashMap<Symbol, Vec<Interval>>,

    to_visit: Vec<(Symbol, BlockId)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AIState {
    vars: FxHashMap<Symbol, Id>,
    ssa_block: SSABlockId,
}

impl AIContext {
    fn set_block(&mut self, func: Symbol, block: BlockId, ssa_block: SSABlock) -> SSABlockId {
        if let Some(old_ssa_block) = self.created_ssa_blocks.get(&(func, block)).copied() {
            self.ssa.cfg[old_ssa_block] = ssa_block;
            old_ssa_block
        } else {
            let id = self.ssa.cfg.len();
            self.ssa.cfg.push(ssa_block);
            self.created_ssa_blocks.insert((func, block), id);
            id
        }
    }

    fn update_state(&mut self, func: Symbol, block: BlockId, state: AIState) {
        if self
            .states
            .get(&(func, block))
            .map(|old_state| old_state != &state)
            .unwrap_or(true)
        {
            self.states.insert((func, block), state);
            self.to_visit
                .extend(self.deps[&func][&block].iter().map(|block| (func, *block)));
        }
    }

    fn visit_block(
        &mut self,
        nonssa: &FxHashMap<Symbol, NonSSAFunc>,
        func: Symbol,
        block: BlockId,
    ) {
        match &nonssa[&func].cfg[block] {
            Block::Entry => self.visit_entry(nonssa, func, block),
            Block::Guard(pred, cond) => self.visit_guard(func, block, *pred, cond),
            Block::Assign(pred, var, expr) => self.visit_assign(func, block, *pred, *var, expr),
            Block::Merge(pred1, pred2) => self.visit_merge(func, block, *pred1, *pred2),
            Block::Store(pred, pointer, expr) => {
                self.visit_store(func, block, *pred, pointer, expr)
            }
            Block::Call(pred, vars, callee, args) => {
                self.visit_call(func, block, *pred, vars, *callee, args)
            }
            Block::Return(pred, exprs) => self.visit_return(func, block, *pred, exprs),
        }
    }

    fn visit_entry(
        &mut self,
        nonssa: &FxHashMap<Symbol, NonSSAFunc>,
        func: Symbol,
        block: BlockId,
    ) {
        let input_analysis = &self.input_analysis[&func];
        let vars = nonssa[&func]
            .params
            .iter()
            .enumerate()
            .map(|(idx, param)| {
                let param_id = self.ssa.intern_param(func, idx, input_analysis[idx]);
                (*param, self.ssa.add_data(Dataflow::Param(param_id)))
            })
            .collect();
        let ssa_block = self.set_block(func, block, SSABlock::Entry);
        let state = AIState { vars, ssa_block };
        self.update_state(func, block, state);
        self.ssa.entries.insert(func, ssa_block);
    }

    fn visit_guard(&mut self, func: Symbol, block: BlockId, pred: BlockId, cond: &Expr) {
        if let Some(mut state) = self.states.get(&(func, pred)).cloned() {
            let value = self.add_expr(cond, &state);
            if !self.ssa.is_always_false(value) {
                state.ssa_block =
                    self.set_block(func, block, SSABlock::Guard(state.ssa_block, value));
                self.update_state(func, block, state);
            }
        }
    }

    fn visit_assign(
        &mut self,
        func: Symbol,
        block: BlockId,
        pred: BlockId,
        var: Symbol,
        expr: &Expr,
    ) {
        if let Some(mut state) = self.states.get(&(func, pred)).cloned() {
            let value = self.add_expr(expr, &state);
            state.vars.insert(var, value);
            self.update_state(func, block, state);
        }
    }

    fn visit_merge(&mut self, func: Symbol, block: BlockId, pred1: BlockId, pred2: BlockId) {
        match (
            self.states.get(&(func, pred1)).cloned(),
            self.states.get(&(func, pred2)).cloned(),
        ) {
            (Some(state1), Some(state2)) => {
                let ssa_block = self.set_block(
                    func,
                    block,
                    SSABlock::Merge(state1.ssa_block, state2.ssa_block),
                );

                let mut new_vars = FxHashMap::default();
                for (var, value1) in &state1.vars {
                    if let Some(value2) = state2.vars.get(var) {
                        if value1 == value2 {
                            new_vars.insert(*var, *value1);
                        } else {
                            let joined = self.ssa.analysis(*value1).join(&self.ssa.analysis(*value2));
                            let knot = self.ssa.intern_knot(ssa_block, *var, joined);
                            let knot = self.ssa.add_data(Dataflow::Knot(knot));
                            new_vars.insert(*var, knot);
                        }
                    }
                }

                let state = AIState {
                    vars: new_vars,
                    ssa_block,
                };
                self.update_state(func, block, state);
            }
            (None, Some(state)) | (Some(state), None) => self.update_state(func, block, state),
            (None, None) => {}
        }
    }

    fn visit_store(
        &mut self,
        func: Symbol,
        block: BlockId,
        pred: BlockId,
        pointer: &Expr,
        expr: &Expr,
    ) {
        if let Some(mut state) = self.states.get(&(func, pred)).cloned() {
            let pointer_value = self.add_expr(pointer, &state);
            let to_store_value = self.add_expr(expr, &state);
            state.ssa_block = self.set_block(
                func,
                block,
                SSABlock::Store(state.ssa_block, pointer_value, to_store_value),
            );
            self.update_state(func, block, state);
        }
    }

    fn visit_call(
        &mut self,
        func: Symbol,
        block: BlockId,
        pred: BlockId,
        vars: &Vec<Symbol>,
        callee: Symbol,
        args: &Vec<Expr>,
    ) {
        if let Some(mut state) = self.states.get(&(func, pred)).cloned() {
            let arg_values: Vec<_> = args
                .iter()
                .map(|expr| self.add_expr(expr, &state))
                .collect();
            let mut changed = false;
            if let Some(input_analysis) = self.input_analysis.get_mut(&callee) {
                for (old_analysis, arg_value) in zip(input_analysis.iter_mut(), &arg_values) {
                    let joined = old_analysis.join(&self.ssa.analysis(*arg_value));
                    if *old_analysis != joined {
                        *old_analysis = joined;
                        changed = true;
                    }
                }
            } else {
                self.input_analysis.insert(
                    callee,
                    arg_values
                        .iter()
                        .map(|arg_value| self.ssa.analysis(*arg_value))
                        .collect(),
                );
                changed = true;
            }
            if changed {
                self.to_visit.push((callee, 0));
            }
            self.callers.entry(callee).or_default().insert(func);

            if let Some(output_analysis) = self.output_analysis.get(&callee).cloned() {
                state.ssa_block = self.set_block(
                    func,
                    block,
                    SSABlock::Call(state.ssa_block, callee, arg_values),
                );
                for (idx, var) in vars.iter().enumerate() {
                    let call = self
                        .ssa
                        .intern_call(state.ssa_block, idx, output_analysis[idx]);
                    let call = self.ssa.add_data(Dataflow::Call(call));
                    state.vars.insert(*var, call);
                }
                self.update_state(func, block, state);
            }
        }
    }

    fn visit_return(&mut self, func: Symbol, block: BlockId, pred: BlockId, exprs: &Vec<Expr>) {
        if let Some(mut state) = self.states.get(&(func, pred)).cloned() {
            let values: Vec<_> = exprs
                .iter()
                .map(|expr| self.add_expr(expr, &state))
                .collect();
            let mut changed = false;
            if let Some(output_analysis) = self.output_analysis.get_mut(&func) {
                for (old_analysis, value) in zip(output_analysis.iter_mut(), &values) {
                    let new_analysis = self.ssa.analysis(*value);
                    if *old_analysis != new_analysis {
                        *old_analysis = new_analysis;
                        changed = true;
                    }
                }
            } else {
                self.output_analysis.insert(
                    func,
                    values
                        .iter()
                        .map(|value| self.ssa.analysis(*value))
                        .collect(),
                );
                changed = true;
            }
            if changed {
                self.to_visit
                    .extend(self.callers[&func].iter().map(|caller| (*caller, 0)));
            }

            state.ssa_block =
                self.set_block(func, block, SSABlock::Return(state.ssa_block, values));
            self.update_state(func, block, state);
        }
    }

    fn add_expr(&mut self, expr: &Expr, state: &AIState) -> Id {
        match expr {
            Expr::Number(cons) => self.ssa.add_data(Dataflow::Constant(*cons)),
            Expr::Variable(var) => state.vars[var],
            Expr::Unary { op, input } => {
                let input = self.add_expr(input, state);
                self.ssa.add_data(Dataflow::Unary(*op, input))
            }
            Expr::Binary { op, lhs, rhs } => {
                let lhs = self.add_expr(lhs, state);
                let rhs = self.add_expr(rhs, state);
                self.ssa.add_data(Dataflow::Binary(*op, [lhs, rhs]))
            }
            Expr::Load { pointer } => {
                let pointer = self.add_expr(pointer, state);
                self.ssa.add_data(Dataflow::Load(state.ssa_block, pointer))
            }
        }
    }
}

fn deps(
    nonssa: &FxHashMap<Symbol, NonSSAFunc>,
) -> FxHashMap<Symbol, FxHashMap<BlockId, FxHashSet<BlockId>>> {
    nonssa
        .iter()
        .map(|(_, func)| {
            let mut deps = FxHashMap::default();
            for id in 0..func.cfg.len() {
                deps.insert(id, FxHashSet::default());
            }
            for (id, block) in func.cfg.iter().enumerate() {
                match block {
                    Block::Entry => {}
                    Block::Guard(pred, ..)
                    | Block::Assign(pred, ..)
                    | Block::Store(pred, ..)
                    | Block::Call(pred, ..)
                    | Block::Return(pred, ..) => {
                        deps.entry(*pred).or_default().insert(id);
                    }
                    Block::Merge(pred1, pred2) => {
                        deps.entry(*pred1).or_default().insert(id);
                        deps.entry(*pred2).or_default().insert(id);
                    }
                }
            }
            (func.name, deps)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::ai::create_ssa;
    use crate::imp::ast::convert_to_cfg;
    use crate::imp::grammar::ProgramParser;

    #[test]
    fn translate1() {
        let program = r#"
fn main() { x <- foo(5, 1); y <- foo(3, 5 - 4); return x * y; }
fn foo(x, y) return x + y;
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let nonssa = parsed
            .into_iter()
            .map(|(name, func)| (name, convert_to_cfg(func)))
            .collect();
        let ssa = create_ssa(&nonssa);
    }

    #[test]
    fn translate2() {
        let program = r#"
fn main() { x <- foo(7); return x; }
fn foo(x) { x <- foo(x + 1); return x; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let nonssa = parsed
            .into_iter()
            .map(|(name, func)| (name, convert_to_cfg(func)))
            .collect();
        let ssa = create_ssa(&nonssa);
    }

    #[test]
    fn translate3() {
        let program = r#"
fn main() { if 0 { x <- foo(24); } else { x = 42; } return x; }
fn foo(x) { return x; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let nonssa = parsed
            .into_iter()
            .map(|(name, func)| (name, convert_to_cfg(func)))
            .collect();
        let ssa = create_ssa(&nonssa);
    }

    #[test]
    fn translate4() {
        let program = r#"
fn main() { x = 1; while x < 100 { x = x + (1 * 5); } return x; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let nonssa = parsed
            .into_iter()
            .map(|(name, func)| (name, convert_to_cfg(func)))
            .collect();
        let ssa = create_ssa(&nonssa);
    }

    #[test]
    fn translate5() {
        let program = r#"
fn main() { x = 1; while x < 100 { x = x + (1 * 5); } foo(); return x; }
fn foo() { x = 5; y = 8; while y < 100 { x = x + 1; } baz(); return y; }
fn baz() { return 42; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let nonssa = parsed
            .into_iter()
            .map(|(name, func)| (name, convert_to_cfg(func)))
            .collect();
        let ssa = create_ssa(&nonssa);
    }

    #[test]
    fn translate6() {
        let program = r#"
fn main() { x <- foo(7); return x; }
fn foo(x) { if x { x <- foo(x - 1); return x + 1; } else { return 0; } }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let nonssa = parsed
            .into_iter()
            .map(|(name, func)| (name, convert_to_cfg(func)))
            .collect();
        let ssa = create_ssa(&nonssa);
    }
}
