use core::iter::zip;

use egg::Id;
use rustc_hash::FxHashMap;

use crate::imp::ast::{ExprAST, FuncAST, StmtAST};
use crate::ssa::{BlockId, SSAProgram};

pub fn create_ssa<'a>(ast: &'a FxHashMap<String, FuncAST>) -> SSAProgram<'a> {
    let mut state = FIA::default();
    if let Some(main) = ast.get("main") {
        state.interp_func(main, vec![], None);
    }
    state.ssa
}

// Flow insensitive abstraction (the SSA program being built and a backwards index of the call
// graph).
#[derive(Debug, Default)]
struct FIA<'a> {
    ssa: SSAProgram<'a>,
    callers: FxHashMap<&'a str, Vec<BlockId>>,
}

// Flow sensitive abstraction (mapping from program variable to e-class ID).
#[derive(Debug, Default, Clone)]
struct FSA<'a> {
    vars: FxHashMap<&'a str, Id>,
}

impl<'a> FIA<'a> {
    fn interp_func(
        &mut self,
        func: &'a FuncAST,
        args: Vec<Id>,
        caller: Option<BlockId>,
    ) -> Vec<Id> {
        let mut fsa = FSA::default();
        for (param, arg) in zip(&func.params, &args) {
            fsa.vars.insert(param, *arg);
        }
        self.interp_stmt(&func.body, fsa);
        todo!()
    }

    fn interp_stmt(&mut self, stmt: &'a StmtAST, mut fsa: FSA) {
        todo!()
    }
}
