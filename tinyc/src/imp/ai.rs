use core::cell::RefCell;
use core::iter::zip;

use egg::{Id, Symbol};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::analysis::interval::Interval;
use crate::imp::ast::{ImpFunc, ImpStmt, LabelId};
use crate::nonssa::{Expr, UnaryOp};
use crate::ssa::{Dataflow, SSABlock, SSABlockId, SSAProgram};

pub fn create_ssa(ast: &FxHashMap<Symbol, ImpFunc>) -> SSAProgram {
    let mut state = FIA {
        ast,
        ssa: Default::default(),
        callgraph: Default::default(),
        callers_to_revisit: Default::default(),
    };
    state
        .callgraph
        .input_values
        .insert(Symbol::from("main"), vec![]);
    state.callers_to_revisit.push(Symbol::from("main"));
    while let Some(func) = state.callers_to_revisit.pop() {
        state.interp_func(
            ast.get(&func).unwrap(),
            state.callgraph.input_values[&func].clone(),
        );
    }
    state.ssa.canon_cfg();
    state.ssa
}

// Flow insensitive abstraction (the SSA program being built and the call graph).
#[derive(Debug)]
struct FIA<'a> {
    ast: &'a FxHashMap<Symbol, ImpFunc>,
    ssa: SSAProgram,
    callgraph: Callgraph,
    callers_to_revisit: Vec<Symbol>,
}

#[derive(Debug, Default)]
struct Callgraph {
    callers: FxHashMap<Symbol, FxHashSet<Symbol>>,
    callsites: FxHashMap<Symbol, FxHashMap<LabelId, Vec<Id>>>,
    input_values: FxHashMap<Symbol, Vec<Id>>,
    output_analyses: FxHashMap<Symbol, Vec<Interval>>,
}

// Flow sensitive abstraction (mapping from program variable to e-class ID).
#[derive(Debug, Clone)]
struct FSA<'a> {
    vars: FxHashMap<Symbol, Id>,
    func: Symbol,
    block: SSABlockId,
    returned: &'a RefCell<FxHashSet<(SSABlockId, Vec<Id>)>>,
}

impl<'a> FIA<'a> {
    fn interp_func(&mut self, func: &'a ImpFunc, args: Vec<Id>) -> Option<(Vec<Id>, SSABlockId)> {
        let entry = self.ssa.add_block(SSABlock::Entry);
        self.ssa.add_entry(func.name, entry);
        let (values, block) = self.interp_func_naked(func, args, func.name, entry)?;
        let return_block = self.ssa.add_block(SSABlock::Return(block, values.clone()));

        let mut output_changed = !self.callgraph.output_analyses.contains_key(&func.name);
        let output_analyses = self
            .callgraph
            .output_analyses
            .entry(func.name)
            .or_insert_with(|| {
                (0..values.len())
                    .map(|idx| self.ssa.analysis(values[idx]))
                    .collect()
            });
        for idx in 0..values.len() {
            let widened = output_analyses[idx].widen(&self.ssa.analysis(values[idx]));
            if widened != output_analyses[idx] {
                output_changed = true;
                output_analyses[idx] = widened;
            }
        }
        if output_changed && let Some(callers) = self.callgraph.callers.get(&func.name) {
            self.callers_to_revisit.extend(callers.iter().copied());
        }

        Some((values, return_block))
    }

    fn interp_func_naked(
        &mut self,
        func: &'a ImpFunc,
        args: Vec<Id>,
        func_name: Symbol,
        block: SSABlockId,
    ) -> Option<(Vec<Id>, SSABlockId)> {
        let returned = Default::default();
        assert_eq!(func.params.len(), args.len());
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
            acc_block = self.ssa.add_block(SSABlock::Merge(acc_block, new_block));
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

    fn interp_stmt<'b>(&mut self, stmt: &'a ImpStmt, fsa: FSA<'b>) -> Option<FSA<'b>> {
        match stmt {
            ImpStmt::Block { body } => self.interp_block(body, fsa),
            ImpStmt::Assign { var, expr, .. } => Some(self.interp_assign(*var, expr, fsa)),
            ImpStmt::Store { pointer, expr, .. } => Some(self.interp_store(pointer, expr, fsa)),
            ImpStmt::Call {
                vars,
                callee,
                args,
                label,
            } => self.interp_call(vars, *callee, args, *label, fsa),
            ImpStmt::IfElse {
                cond,
                then_body,
                else_body,
                ..
            } => self.interp_ifelse(cond, then_body, else_body, fsa),
            ImpStmt::While { cond, body, .. } => self.interp_while(cond, body, fsa),
            ImpStmt::Return { exprs, .. } => {
                self.interp_return(exprs, fsa);
                None
            }
        }
    }

    fn interp_block<'b>(&mut self, body: &'a Vec<ImpStmt>, mut fsa: FSA<'b>) -> Option<FSA<'b>> {
        for stmt in body {
            if let Some(new_fsa) = self.interp_stmt(stmt, fsa) {
                fsa = new_fsa
            } else {
                return None;
            }
        }
        Some(fsa)
    }

    fn interp_assign<'b>(&mut self, var: Symbol, expr: &'a Expr, mut fsa: FSA<'b>) -> FSA<'b> {
        let value = self.interp_expr(expr, &fsa);
        fsa.vars.insert(var, value);
        fsa
    }

    fn interp_store<'b>(&mut self, pointer: &'a Expr, expr: &'a Expr, mut fsa: FSA<'b>) -> FSA<'b> {
        let pointer = self.interp_expr(pointer, &fsa);
        let expr = self.interp_expr(expr, &fsa);
        let store = self
            .ssa
            .add_block(SSABlock::Store(fsa.block, pointer, expr));
        fsa.block = store;
        fsa
    }

    fn interp_call<'b>(
        &mut self,
        vars: &'a Vec<Symbol>,
        callee: Symbol,
        args: &'a Vec<Expr>,
        label: LabelId,
        mut fsa: FSA<'b>,
    ) -> Option<FSA<'b>> {
        let args: Vec<_> = args.iter().map(|arg| self.interp_expr(arg, &fsa)).collect();
        self.callgraph
            .callers
            .entry(callee)
            .or_default()
            .insert(fsa.func);
        let callsites = self.callgraph.callsites.entry(callee).or_default();
        let old_args = callsites.insert(label, args.clone());

        let outputs = if callsites.len() < 2 {
            let (outputs, block) =
                self.interp_func_naked(&self.ast[&callee], args, fsa.func, fsa.block)?;
            fsa.block = block;
            outputs
        } else {
            let mut joined_analyses = vec![None; args.len()];
            for idx in 0..args.len() {
                for (_, other_args) in callsites.iter() {
                    if args[idx] != other_args[idx] {
                        let widened = old_args
                            .as_ref()
                            .map(|old_args| {
                                self.ssa
                                    .analysis(old_args[idx])
                                    .widen(&self.ssa.analysis(args[idx]))
                            })
                            .unwrap_or(self.ssa.analysis(args[idx]));
                        joined_analyses[idx] = Some(
                            joined_analyses[idx]
                                .unwrap_or(widened)
                                .join(&self.ssa.analysis(other_args[idx])),
                        );
                    }
                }
            }
            let joined_args = (0..args.len())
                .map(|idx| {
                    joined_analyses[idx]
                        .map(|analysis| {
                            let param = self.ssa.intern_param(callee, idx, analysis);
                            self.ssa.add_data(Dataflow::Param(param))
                        })
                        .unwrap_or(args[idx])
                })
                .collect();

            if self.callgraph.input_values.get(&callee) != Some(&joined_args) {
                self.callgraph
                    .input_values
                    .insert(callee, joined_args.clone());
                self.interp_func(&self.ast[&callee], joined_args);
            }

            if let Some(output_analyses) = self.callgraph.output_analyses.get(&callee) {
                fsa.block = self.ssa.add_block(SSABlock::Call(fsa.block, callee, args));
                (0..vars.len())
                    .map(|idx| {
                        let call = self.ssa.intern_call(fsa.block, idx, output_analyses[idx]);
                        self.ssa.add_data(Dataflow::Call(call))
                    })
                    .collect()
            } else {
                return None;
            }
        };

        for (var, output) in zip(vars, outputs.into_iter()) {
            fsa.vars.insert(*var, output);
        }
        Some(fsa)
    }

    fn interp_ifelse<'b>(
        &mut self,
        cond: &'a Expr,
        then_body: &'a ImpStmt,
        else_body: &'a ImpStmt,
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
                self.ssa.add_block(SSABlock::Child(fsa.block, then_cond))
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
                self.ssa.add_block(SSABlock::Child(fsa.block, else_cond))
            };
            let mut ctx = fsa.clone();
            ctx.block = else_block;
            else_fsa = self.interp_stmt(else_body, ctx);
        }

        match (then_fsa, else_fsa) {
            (Some(then_fsa), Some(else_fsa)) => {
                let merge = self
                    .ssa
                    .add_block(SSABlock::Merge(then_fsa.block, else_fsa.block));
                for (var, then_value) in &then_fsa.vars {
                    if let Some(else_value) = else_fsa.vars.get(var) {
                        let value = if then_value == else_value {
                            *then_value
                        } else {
                            let analysis = self
                                .ssa
                                .analysis(*then_value)
                                .join(&self.ssa.analysis(*else_value));
                            let knot = self.ssa.intern_knot(merge, *var, analysis);
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
        cond: &'a Expr,
        body: &'a ImpStmt,
        mut fsa: FSA<'b>,
    ) -> Option<FSA<'b>> {
        let mut then_cond = self.interp_expr(cond, &fsa);
        if self.is_always_false(then_cond) {
            return Some(fsa);
        }

        let mut header = fsa.block;
        let mut loop_fsa = fsa.clone();
        loop_fsa.block = self.ssa.add_block(SSABlock::Child(header, then_cond));

        if let Some(mut loop_fsa) = self.interp_stmt(body, loop_fsa) {
            header = self.ssa.add_block(SSABlock::Entry);
            let mut old_header_values = FxHashMap::default();
            let mut old_loop_analyses: FxHashMap<Symbol, Interval> = FxHashMap::default();
            loop {
                let mut new_vars = fsa.vars.clone();
                for (var, init_value) in &fsa.vars {
                    if let Some(loop_value) = loop_fsa.vars.get(var) {
                        let value = if init_value == loop_value {
                            *init_value
                        } else {
                            let widened = if let Some(old_loop) = old_loop_analyses.get(var) {
                                old_loop.widen(&self.ssa.analysis(*loop_value))
                            } else {
                                self.ssa.analysis(*loop_value)
                            };
                            let analysis = self.ssa.analysis(*init_value).join(&widened);
                            let knot = self.ssa.intern_knot(header, *var, analysis);
                            self.ssa.add_data(Dataflow::Knot(knot))
                        };
                        new_vars.insert(*var, value);
                        old_loop_analyses.insert(*var, self.ssa.analysis(value));
                    }
                }

                if new_vars == old_header_values {
                    fsa.vars = new_vars;
                    self.ssa
                        .set_block(SSABlock::Merge(fsa.block, loop_fsa.block), header);
                    break;
                }
                old_header_values = new_vars.clone();

                let mut new_loop_fsa = fsa.clone();
                new_loop_fsa.vars = new_vars;
                then_cond = self.interp_expr(cond, &new_loop_fsa);
                new_loop_fsa.block = self.ssa.add_block(SSABlock::Child(header, then_cond));
                loop_fsa = self.interp_stmt(body, new_loop_fsa).unwrap();
            }
        }

        let else_cond = self.ssa.add_data(Dataflow::Unary(UnaryOp::Not, then_cond));
        if self.is_always_false(else_cond) {
            None
        } else {
            fsa.block = self.ssa.add_block(SSABlock::Child(header, else_cond));
            Some(fsa)
        }
    }

    fn interp_return<'b>(&mut self, exprs: &'a Vec<Expr>, fsa: FSA<'b>) {
        let values: Vec<_> = exprs
            .iter()
            .map(|expr| self.interp_expr(expr, &fsa))
            .collect();
        fsa.returned.borrow_mut().insert((fsa.block, values));
    }

    fn interp_expr<'b>(&mut self, expr: &'a Expr, fsa: &FSA<'b>) -> Id {
        match expr {
            Expr::Number(cons) => self.ssa.add_data(Dataflow::Constant(*cons)),
            Expr::Variable(var) => fsa.vars[var],
            Expr::Unary { op, input } => {
                let input = self.interp_expr(input, fsa);
                self.ssa.add_data(Dataflow::Unary(*op, input))
            }
            Expr::Binary { op, lhs, rhs } => {
                let lhs = self.interp_expr(lhs, fsa);
                let rhs = self.interp_expr(rhs, fsa);
                self.ssa.add_data(Dataflow::Binary(*op, [lhs, rhs]))
            }
            Expr::Load { pointer } => {
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
fn main() { x <- foo(5, 1); y <- foo(3, 5 - 4); return x * y; }
fn foo(x, y) return x + y;
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let ssa = create_ssa(&parsed);
        assert_eq!(ssa.param_map.len(), 1);
        assert_eq!(ssa.knot_map.len(), 0);
        assert_eq!(ssa.call_map.len(), 3);
    }

    #[test]
    fn translate2() {
        let program = r#"
fn main() { x <- foo(7); return x; }
fn foo(x) { x <- foo(x + 1); return x; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let ssa = create_ssa(&parsed);
        assert_eq!(ssa.param_map.len(), 2);
        assert_eq!(ssa.knot_map.len(), 0);
        assert_eq!(ssa.call_map.len(), 0);
    }

    #[test]
    fn translate3() {
        let program = r#"
fn main() { if 0 { x <- foo(24); } else { x = 42; } return x; }
fn foo(x) { return x; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let ssa = create_ssa(&parsed);
        assert_eq!(ssa.param_map.len(), 0);
        assert_eq!(ssa.knot_map.len(), 0);
        assert_eq!(ssa.call_map.len(), 0);
    }

    #[test]
    fn translate4() {
        let program = r#"
fn main() { x = 1; while x < 100 { x = x + (1 * 5); } return x; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let ssa = create_ssa(&parsed);
        assert_eq!(ssa.param_map.len(), 0);
        assert_eq!(ssa.knot_map.len(), 2);
        assert_eq!(ssa.call_map.len(), 0);
    }

    #[test]
    fn translate5() {
        let program = r#"
fn main() { x = 1; while x < 100 { x = x + (1 * 5); } foo(); return x; }
fn foo() { x = 5; y = 8; while y < 100 { x = x + 1; } baz(); return y; }
fn baz() { return 42; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let ssa = create_ssa(&parsed);
        assert_eq!(ssa.param_map.len(), 0);
        assert_eq!(ssa.knot_map.len(), 4);
        assert_eq!(ssa.call_map.len(), 0);
    }

    #[test]
    fn translate6() {
        let program = r#"
fn main() { x <- foo(7); return x; }
fn foo(x) { if x { x <- foo(x - 1); return x + 1; } else { return 0; } }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let ssa = create_ssa(&parsed);
        assert_eq!(ssa.param_map.len(), 2);
        assert_eq!(ssa.knot_map.len(), 0);
        assert_eq!(ssa.call_map.len(), 6);
    }
}
