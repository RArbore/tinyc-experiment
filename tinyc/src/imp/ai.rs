use core::cell::RefCell;

use rustc_hash::FxHashMap;

use crate::imp::ast::{ExprAST, FuncAST, StmtAST};
use crate::ssa::SSAProgram;

pub fn create_ssa<'a>(ast: &'a FxHashMap<String, FuncAST>) -> SSAProgram<'a> {
    let ssa = RefCell::new(Default::default());

    ssa.into_inner()
}
