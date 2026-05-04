use core::iter::zip;

use egg::Id;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::imp::ast::{ExprAST, FuncAST, StmtAST};
use crate::ssa::{BlockId, Dataflow, SSAProgram};

pub fn create_ssa<'a>(ast: &'a FxHashMap<String, FuncAST>) -> SSAProgram<'a> {
    let mut state = FIA::default();
    if let Some(main) = ast.get("main") {
        state.interp_func(main, vec![], BlockId::MAX, 0);
    }
    state.ssa
}

// Flow insensitive abstraction (the SSA program being built and the call graph).
#[derive(Debug, Default)]
struct FIA<'a> {
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
struct FSA<'a> {
    vars: Option<FxHashMap<&'a str, Id>>,
    returned: FxHashSet<Vec<Id>>,
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
        if self.callgraph.params.get(&func.name as &str) == Some(&params) {
            return output;
        }

        let fsa = FSA {
            vars: Some(
                zip(func.params.iter(), params)
                    .map(|(name, id)| (name as _, id))
                    .collect(),
            ),
            returned: FxHashSet::default(),
        };
        let fsa = self.interp_stmt(&func.body, fsa);
        fsa.returned
            .iter()
            .for_each(|output| assert_eq!(output.len(), num_outputs));

        for idx in 0..num_outputs {
            if let Some(same) = are_all_same(fsa.returned.iter().map(|output| output[idx])) {
                output[idx] = same;
            }
        }
        output
    }

    fn interp_stmt(&mut self, stmt: &'a StmtAST, fsa: FSA<'a>) -> FSA<'a> {
        match stmt {
            StmtAST::Block { body } => self.interp_block(body, fsa),
            StmtAST::Assign { var, expr, .. } => self.interp_assign(var, expr, fsa),
            StmtAST::Store { pointer, expr, .. } => self.interp_store(pointer, expr, fsa),
            StmtAST::Call {
                vars, callee, args, ..
            } => self.interp_call(vars, callee, args, fsa),
            StmtAST::IfElse {
                cond,
                then_body,
                else_body,
                ..
            } => self.interp_ifelse(cond, then_body, else_body, fsa),
            StmtAST::While { cond, body, .. } => self.interp_while(cond, body, fsa),
            StmtAST::Return { exprs, .. } => self.interp_return(exprs, fsa),
        }
    }

    fn interp_block(&self, body: &Vec<StmtAST>, fsa: FSA<'a>) -> FSA<'a> {
        todo!()
    }

    fn interp_assign(&self, var: &str, expr: &ExprAST, fsa: FSA<'a>) -> FSA<'a> {
        todo!()
    }

    fn interp_store(&self, pointer: &ExprAST, expr: &ExprAST, fsa: FSA<'a>) -> FSA<'a> {
        todo!()
    }

    fn interp_call(
        &self,
        vars: &Vec<String>,
        callee: &str,
        args: &Vec<ExprAST>,
        fsa: FSA<'a>,
    ) -> FSA<'a> {
        todo!()
    }

    fn interp_ifelse(
        &self,
        cond: &ExprAST,
        then_body: &StmtAST,
        else_body: &StmtAST,
        fsa: FSA<'a>,
    ) -> FSA<'a> {
        todo!()
    }

    fn interp_while(&self, cond: &ExprAST, body: &StmtAST, fsa: FSA<'a>) -> FSA<'a> {
        todo!()
    }

    fn interp_return(&self, exprs: &Vec<ExprAST>, fsa: FSA<'a>) -> FSA<'a> {
        todo!()
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
