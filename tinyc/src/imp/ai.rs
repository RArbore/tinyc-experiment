use core::cell::RefCell;
use core::iter::zip;

use egg::{Id, Symbol};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::analysis::interval::Interval;
use crate::imp::ast::{ExprAST, FuncAST, LabelId, StmtAST};
use crate::ssa::{Block, BlockId, Dataflow, SSAProgram, UnaryOp};

pub fn create_ssa(ast: &FxHashMap<Symbol, FuncAST>) -> SSAProgram {
    let mut state = FIA {
        ast,
        ssa: Default::default(),
        callgraph: Default::default(),
    };
    if let Some(main) = ast.get(&Symbol::from("main")) {
        state
            .callgraph
            .param_nodes
            .insert(Symbol::from("main"), vec![]);
        state.interp_func(main, vec![]);
    }
    state.ssa.canon_cfg();
    state.ssa
}

// Flow insensitive abstraction (the SSA program being built and the call graph).
#[derive(Debug)]
struct FIA<'a> {
    ast: &'a FxHashMap<Symbol, FuncAST>,
    ssa: SSAProgram,
    callgraph: Callgraph,
}

#[derive(Debug, Default)]
struct Callgraph {
    callers: FxHashMap<Symbol, FxHashSet<(Symbol, LabelId)>>,
    param_nodes: FxHashMap<Symbol, Vec<Id>>,
}

// Flow sensitive abstraction (mapping from program variable to e-class ID).
#[derive(Debug, Clone)]
struct FSA<'a> {
    vars: FxHashMap<Symbol, Id>,
    func: Symbol,
    block: BlockId,
    returned: &'a RefCell<FxHashSet<(BlockId, Vec<Id>)>>,
}

impl<'a> FIA<'a> {
    fn interp_func(&mut self, func: &'a FuncAST, args: Vec<Id>) -> Option<(Vec<Id>, BlockId)> {
        let entry = self.ssa.add_block(Block::Entry);
        self.ssa.add_entry(func.name, entry);
        let (values, block) = self.interp_func_naked(func, args, func.name, entry)?;
        let return_block = self.ssa.add_block(Block::Return(block, values.clone()));
        Some((values, return_block))
    }

    fn interp_func_naked(
        &mut self,
        func: &'a FuncAST,
        args: Vec<Id>,
        func_name: Symbol,
        block: BlockId,
    ) -> Option<(Vec<Id>, BlockId)> {
        let returned = Default::default();
        let fsa = FSA {
            vars: zip(func.params.iter(), args)
                .map(|(name, id)| (*name, id))
                .collect(),
            func: func_name,
            block,
            returned: &returned,
        };
        assert!(self.interp_stmt(&func.body, fsa).is_none());

        let mut returned = returned.into_inner().into_iter();
        let (mut acc_block, mut acc_values) = returned.next()?;
        for (new_block, new_values) in returned {
            acc_block = self.ssa.add_block(Block::Merge(acc_block, new_block));
            assert_eq!(acc_values.len(), new_values.len());
            for idx in 0..acc_values.len() {
                if acc_values[idx] != new_values[idx] {
                    acc_values[idx] = self
                        .ssa
                        .add_data(Dataflow::Phi(acc_block, [acc_values[idx], new_values[idx]]));
                }
            }
        }
        Some((acc_values, acc_block))
    }

    fn interp_stmt<'b>(&mut self, stmt: &'a StmtAST, fsa: FSA<'b>) -> Option<FSA<'b>> {
        match stmt {
            StmtAST::Block { body } => self.interp_block(body, fsa),
            StmtAST::Assign { var, expr, .. } => Some(self.interp_assign(*var, expr, fsa)),
            StmtAST::Store { pointer, expr, .. } => Some(self.interp_store(pointer, expr, fsa)),
            StmtAST::Call {
                vars,
                callee,
                args,
                label,
            } => self.interp_call(vars, *callee, args, *label, fsa),
            StmtAST::IfElse {
                cond,
                then_body,
                else_body,
                ..
            } => self.interp_ifelse(cond, then_body, else_body, fsa),
            StmtAST::While { cond, body, .. } => self.interp_while(cond, body, fsa),
            StmtAST::Return { exprs, .. } => {
                self.interp_return(exprs, fsa);
                None
            }
        }
    }

    fn interp_block<'b>(&mut self, body: &'a Vec<StmtAST>, mut fsa: FSA<'b>) -> Option<FSA<'b>> {
        for stmt in body {
            if let Some(new_fsa) = self.interp_stmt(stmt, fsa) {
                fsa = new_fsa
            } else {
                return None;
            }
        }
        Some(fsa)
    }

    fn interp_assign<'b>(&mut self, var: Symbol, expr: &'a ExprAST, mut fsa: FSA<'b>) -> FSA<'b> {
        let value = self.interp_expr(expr, &fsa);
        fsa.vars.insert(var, value);
        fsa
    }

    fn interp_store<'b>(
        &mut self,
        pointer: &'a ExprAST,
        expr: &'a ExprAST,
        mut fsa: FSA<'b>,
    ) -> FSA<'b> {
        let pointer = self.interp_expr(pointer, &fsa);
        let expr = self.interp_expr(expr, &fsa);
        let store = self.ssa.add_block(Block::Store(fsa.block, pointer, expr));
        fsa.block = store;
        fsa
    }

    fn interp_call<'b>(
        &mut self,
        vars: &'a Vec<Symbol>,
        callee: Symbol,
        args: &'a Vec<ExprAST>,
        label: LabelId,
        mut fsa: FSA<'b>,
    ) -> Option<FSA<'b>> {
        let args: Vec<_> = args.iter().map(|arg| self.interp_expr(arg, &fsa)).collect();
        let callers = self.callgraph.callers.entry(callee).or_default();
        callers.insert((fsa.func, label));

        let outputs = if callers.len() < 2 {
            self.callgraph.param_nodes.insert(callee, args.clone());
            let (outputs, block) =
                self.interp_func_naked(&self.ast[&callee], args, fsa.func, fsa.block)?;
            fsa.block = block;
            outputs
        } else {
            let param_nodes: Vec<_> = zip(&args, &self.callgraph.param_nodes[&callee])
                .enumerate()
                .map(|(idx, (new_arg, old_arg))| {
                    if *new_arg == *old_arg {
                        *new_arg
                    } else {
                        let param = self.ssa.intern_param(callee, idx, Interval::top());
                        self.ssa.add_data(Dataflow::Param(param))
                    }
                })
                .collect();
            let old_param_nodes = self
                .callgraph
                .param_nodes
                .insert(callee, param_nodes.clone());
            if old_param_nodes.as_ref() != Some(&param_nodes) {
                self.interp_func(&self.ast[&callee], param_nodes);
            }

            fsa.block = self.ssa.add_block(Block::Call(fsa.block, callee, args));
            (0..vars.len())
                .map(|idx| {
                    let call = self.ssa.intern_call(fsa.block, idx, Interval::top());
                    self.ssa.add_data(Dataflow::Call(call))
                })
                .collect()
        };

        for (var, output) in zip(vars, outputs.into_iter()) {
            fsa.vars.insert(*var, output);
        }
        Some(fsa)
    }

    fn interp_ifelse<'b>(
        &mut self,
        cond: &'a ExprAST,
        then_body: &'a StmtAST,
        else_body: &'a StmtAST,
        mut fsa: FSA<'b>,
    ) -> Option<FSA<'b>> {
        let then_cond = self.interp_expr(cond, &fsa);
        let else_cond = self.ssa.add_data(Dataflow::Unary(UnaryOp::Not, then_cond));
        let then_always_false = self.is_always_false(then_cond);
        let else_always_false = self.is_always_false(else_cond);

        let mut then_fsa = None;
        if !then_always_false {
            let then_block = if else_always_false {
                fsa.block
            } else {
                self.ssa.add_block(Block::Child(fsa.block, then_cond))
            };
            let mut ctx = fsa.clone();
            ctx.block = then_block;
            then_fsa = self.interp_stmt(then_body, ctx);
        }

        let mut else_fsa = None;
        if !else_always_false {
            let else_block = if then_always_false {
                fsa.block
            } else {
                self.ssa.add_block(Block::Child(fsa.block, else_cond))
            };
            let mut ctx = fsa.clone();
            ctx.block = else_block;
            else_fsa = self.interp_stmt(else_body, ctx);
        }

        match (then_fsa, else_fsa) {
            (Some(then_fsa), Some(else_fsa)) => {
                let merge = self
                    .ssa
                    .add_block(Block::Merge(then_fsa.block, else_fsa.block));
                for (var, then_value) in &then_fsa.vars {
                    if let Some(else_value) = else_fsa.vars.get(var) {
                        let value = if then_value == else_value {
                            *then_value
                        } else {
                            let knot = self.ssa.intern_knot(merge, *var, Interval::top());
                            self.ssa.add_data(Dataflow::Knot(knot))
                        };
                        fsa.vars.insert(*var, value);
                    }
                }
                Some(fsa)
            }
            (fsa, None) | (None, fsa) => fsa,
        }
    }

    fn interp_while<'b>(
        &mut self,
        cond: &'a ExprAST,
        body: &'a StmtAST,
        mut fsa: FSA<'b>,
    ) -> Option<FSA<'b>> {
        let mut then_cond = self.interp_expr(cond, &fsa);
        if self.is_always_false(then_cond) {
            return Some(fsa);
        }

        let mut header = fsa.block;
        let mut loop_fsa = fsa.clone();
        loop_fsa.block = self.ssa.add_block(Block::Child(header, then_cond));

        if let Some(mut loop_fsa) = self.interp_stmt(body, loop_fsa) {
            header = self.ssa.add_block(Block::Entry);
            let mut old_header_vars = FxHashMap::default();
            loop {
                let mut new_vars = fsa.vars.clone();
                for (var, init_value) in &fsa.vars {
                    if let Some(loop_value) = loop_fsa.vars.get(var) {
                        let value = if init_value == loop_value {
                            *init_value
                        } else {
                            let knot = self.ssa.intern_knot(header, *var, Interval::top());
                            self.ssa.add_data(Dataflow::Knot(knot))
                        };
                        new_vars.insert(*var, value);
                    }
                }
                if new_vars == old_header_vars {
                    fsa.vars = new_vars;
                    self.ssa
                        .set_block(Block::Merge(fsa.block, loop_fsa.block), header);
                    break;
                }
                old_header_vars = new_vars.clone();

                let mut new_loop_fsa = fsa.clone();
                new_loop_fsa.vars = new_vars;
                then_cond = self.interp_expr(cond, &new_loop_fsa);
                new_loop_fsa.block = self.ssa.add_block(Block::Child(header, then_cond));
                loop_fsa = self.interp_stmt(body, new_loop_fsa).unwrap();
            }
        }

        let else_cond = self.ssa.add_data(Dataflow::Unary(UnaryOp::Not, then_cond));
        if self.is_always_false(else_cond) {
            None
        } else {
            fsa.block = self.ssa.add_block(Block::Child(header, else_cond));
            Some(fsa)
        }
    }

    fn interp_return<'b>(&mut self, exprs: &'a Vec<ExprAST>, fsa: FSA<'b>) {
        let values: Vec<_> = exprs
            .iter()
            .map(|expr| self.interp_expr(expr, &fsa))
            .collect();
        fsa.returned.borrow_mut().insert((fsa.block, values));
    }

    fn interp_expr<'b>(&mut self, expr: &'a ExprAST, fsa: &FSA<'b>) -> Id {
        match expr {
            ExprAST::Number(cons) => self.ssa.add_data(Dataflow::Constant(*cons)),
            ExprAST::Variable(var) => fsa.vars[var],
            ExprAST::Unary { op, input } => {
                let input = self.interp_expr(input, fsa);
                self.ssa.add_data(Dataflow::Unary(*op, input))
            }
            ExprAST::Binary { op, lhs, rhs } => {
                let lhs = self.interp_expr(lhs, fsa);
                let rhs = self.interp_expr(rhs, fsa);
                self.ssa.add_data(Dataflow::Binary(*op, [lhs, rhs]))
            }
            ExprAST::Load { pointer } => {
                let pointer = self.interp_expr(pointer, fsa);
                self.ssa.add_data(Dataflow::Load(fsa.block, pointer))
            }
        }
    }

    fn is_always_false(&mut self, value: Id) -> bool {
        self.ssa.is_always_false(value)
    }
}

#[cfg(test)]
mod tests {
    use crate::imp::ai::create_ssa;
    use crate::imp::grammar::ProgramParser;

    #[test]
    fn translate1() {
        let program = r#"
fn main() { x <- foo(5); y <- foo(3); return x * y; }
fn foo(x) return x + 1;
"#;
        let mut counter = 0;
        let parsed = ProgramParser::new().parse(&mut counter, &program).unwrap();
        let _ssa = create_ssa(&parsed);
    }

    #[test]
    fn translate2() {
        let program = r#"
fn main() { x <- foo(7); return x; }
fn foo(x) { x <- foo(x + 1); return x; }
"#;
        let mut counter = 0;
        let parsed = ProgramParser::new().parse(&mut counter, &program).unwrap();
        let _ssa = create_ssa(&parsed);
    }

    #[test]
    fn translate3() {
        let program = r#"
fn main() { if 0 { x <- foo(24); } else { x = 42; } return x; }
fn foo(x) { return x; }
"#;
        let mut counter = 0;
        let parsed = ProgramParser::new().parse(&mut counter, &program).unwrap();
        let _ssa = create_ssa(&parsed);
    }

    #[test]
    fn translate4() {
        let program = r#"
fn main() { x = 1; while x < 100 { x = x + (1 * 5); } foo(); return x; }
fn foo() { x = 5; y = 8; while y < 100 { x = x + 1; } baz(); return y; }
fn baz() { return 42; }
"#;
        let mut counter = 0;
        let parsed = ProgramParser::new().parse(&mut counter, &program).unwrap();
        let _ssa = create_ssa(&parsed);
    }
}
