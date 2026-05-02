use core::cell::RefCell;

use rustc_hash::FxHashMap;

use crate::imp::ast::FuncAST;
use crate::ssa::{SSABuilder, SSAProgram};

pub fn create_ssa<'a>(ast: &'a FxHashMap<String, FuncAST>) -> SSAProgram<'a> {
    let ssa = RefCell::new(Default::default());

    if let Some(main) = ast.get("main") {
        let ctx = SSABuilder::entry(&main.name, main.params.iter().map(|s| s as _), &ssa);
    }

    ssa.into_inner()
}
