use core::cell::RefCell;
use core::iter::zip;

use egg::Id;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::imp::ast::{ExprAST, FuncAST, StmtAST};
use crate::ssa::{Block, BlockId, Dataflow, SSAProgram};

pub fn create_ssa<'a>(ast: &'a FxHashMap<String, FuncAST>) -> SSAProgram<'a> {
    let mut state = FIA {
        ast,
        ssa: Default::default(),
        callgraph: Default::default(),
    };
    if let Some(main) = ast.get("main") {
        state.interp_func(main, vec![], BlockId::MAX, 0);
    }
    state.ssa
}

// Flow insensitive abstraction (the SSA program being built and the call graph).
#[derive(Debug)]
struct FIA<'a> {
    ast: &'a FxHashMap<String, FuncAST>,
    ssa: SSAProgram<'a>,
    callgraph: Callgraph<'a>,
}

#[derive(Debug, Default)]
struct Callgraph<'a> {
    callers: FxHashMap<&'a str, FxHashMap<BlockId, Vec<Id>>>,
    params: FxHashMap<&'a str, Vec<Id>>,
}

// Flow sensitive abstraction (mapping from program variable to e-class ID).
#[derive(Debug, Clone)]
struct FSA<'a, 'b> {
    vars: FxHashMap<&'a str, Id>,
    block: BlockId,
    returned: &'b RefCell<FxHashSet<Vec<Id>>>,
}

impl<'a> FIA<'a> {
    fn interp_func(
        &mut self,
        func: &'a FuncAST,
        args: Vec<Id>,
        caller: BlockId,
        num_outputs: usize,
    ) -> Vec<Id> {
        assert_eq!(func.params.len(), args.len());
        let callers = self.callgraph.callers.entry(&func.name).or_default();
        callers.insert(caller, args);
        let num_callers = callers.len();

        let mut output: Vec<_> = (0..num_outputs)
            .map(|idx| {
                let call = self.ssa.intern_call(caller, idx);
                self.ssa.add_data(Dataflow::Call(call))
            })
            .collect();
        let params = (0..func.params.len())
            .map(|idx| {
                let args_at_idx = callers.iter().map(|(_, args)| args[idx]);
                if let Some(same) = are_all_same(args_at_idx) {
                    same
                } else {
                    let param = self.ssa.intern_param(&func.name, idx);
                    self.ssa.add_data(Dataflow::Param(param))
                }
            })
            .collect();

        if self.callgraph.params.get(&func.name as &str) != Some(&params) {
            self.callgraph
                .params
                .insert(&func.name as &str, params.clone());
            let entry = self.ssa.add_block(Block::Entry);
            self.ssa.add_entry(&func.name, entry);
            let returned = Default::default();
            let fsa = FSA {
                vars: zip(func.params.iter(), params)
                    .map(|(name, id)| (name as _, id))
                    .collect(),
                block: entry,
                returned: &returned,
            };
            assert!(self.interp_stmt(&func.body, fsa).is_none());

            let returned = returned.into_inner();
            returned
                .iter()
                .for_each(|output| assert_eq!(output.len(), num_outputs));
            for idx in 0..num_outputs {
                if num_callers < 2
                    && let Some(same) = are_all_same(returned.iter().map(|output| output[idx]))
                {
                    output[idx] = same;
                }
            }
        }

        output
    }

    fn interp_stmt<'b>(&mut self, stmt: &'a StmtAST, fsa: FSA<'a, 'b>) -> Option<FSA<'a, 'b>> {
        match stmt {
            StmtAST::Block { body } => self.interp_block(body, fsa),
            StmtAST::Assign { var, expr, .. } => Some(self.interp_assign(var, expr, fsa)),
            StmtAST::Store { pointer, expr, .. } => Some(self.interp_store(pointer, expr, fsa)),
            StmtAST::Call {
                vars, callee, args, ..
            } => Some(self.interp_call(vars, callee, args, fsa)),
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

    fn interp_block<'b>(
        &mut self,
        body: &'a Vec<StmtAST>,
        mut fsa: FSA<'a, 'b>,
    ) -> Option<FSA<'a, 'b>> {
        for stmt in body {
            if let Some(new_fsa) = self.interp_stmt(stmt, fsa) {
                fsa = new_fsa
            } else {
                return None;
            }
        }
        Some(fsa)
    }

    fn interp_assign<'b>(
        &mut self,
        var: &'a str,
        expr: &'a ExprAST,
        mut fsa: FSA<'a, 'b>,
    ) -> FSA<'a, 'b> {
        let value = self.interp_expr(expr, &fsa);
        fsa.vars.insert(var, value);
        fsa
    }

    fn interp_store<'b>(
        &mut self,
        pointer: &'a ExprAST,
        expr: &'a ExprAST,
        mut fsa: FSA<'a, 'b>,
    ) -> FSA<'a, 'b> {
        let pointer = self.interp_expr(pointer, &fsa);
        let expr = self.interp_expr(expr, &fsa);
        let store = self.ssa.add_block(Block::Store(fsa.block, pointer, expr));
        fsa.block = store;
        fsa
    }

    fn interp_call<'b>(
        &mut self,
        vars: &'a Vec<String>,
        callee: &'a str,
        args: &'a Vec<ExprAST>,
        mut fsa: FSA<'a, 'b>,
    ) -> FSA<'a, 'b> {
        let args: Vec<_> = args.iter().map(|arg| self.interp_expr(arg, &fsa)).collect();
        let caller = self
            .ssa
            .add_block(Block::Call(fsa.block, callee, args.clone()));
        let outputs = self.interp_func(&self.ast[callee], args, caller, vars.len());
        fsa.block = caller;
        for (var, output) in zip(vars, outputs.into_iter()) {
            fsa.vars.insert(var, output);
        }
        fsa
    }

    fn interp_ifelse<'b>(
        &mut self,
        cond: &'a ExprAST,
        then_body: &'a StmtAST,
        else_body: &'a StmtAST,
        fsa: FSA<'a, 'b>,
    ) -> Option<FSA<'a, 'b>> {
        todo!()
    }

    fn interp_while<'b>(
        &mut self,
        cond: &'a ExprAST,
        body: &'a StmtAST,
        fsa: FSA<'a, 'b>,
    ) -> Option<FSA<'a, 'b>> {
        todo!()
    }

    fn interp_return<'b>(&mut self, exprs: &'a Vec<ExprAST>, fsa: FSA<'a, 'b>) {
        let values: Vec<_> = exprs
            .iter()
            .map(|expr| self.interp_expr(expr, &fsa))
            .collect();
        self.ssa.add_block(Block::Return(fsa.block, values.clone()));
        fsa.returned.borrow_mut().insert(values);
    }

    fn interp_expr<'b>(&mut self, expr: &'a ExprAST, fsa: &FSA<'a, 'b>) -> Id {
        match expr {
            ExprAST::Number(cons) => self.ssa.add_data(Dataflow::Constant(*cons)),
            ExprAST::Variable(var) => fsa.vars[var as &str],
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
}

fn are_all_same<D, I>(mut iter: I) -> Option<D>
where
    D: Eq,
    I: Iterator<Item = D>,
{
    let mut same = iter.next();
    for data in iter {
        if same != Some(data) {
            same = None;
            break;
        }
    }
    same
}

#[cfg(test)]
mod tests {
    use crate::imp::ai::create_ssa;
    use crate::imp::grammar::ProgramParser;

    #[test]
    fn translate1() {
        let program = r#"
fn main() { x <- foo(5); y <- foo(3); z = x + y; *z = z; return; }
fn foo(x) return x + 1;
"#;
        let mut counter = 0;
        let parsed = ProgramParser::new().parse(&mut counter, &program).unwrap();
        let ssa = create_ssa(&parsed);
    }
}
