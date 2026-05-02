use egg::{EGraph, Id, define_language};
use rustc_hash::FxHashMap;

use crate::ast::{BinaryOp, FuncAST, UnaryOp};

pub type BlockId = usize;
type ParamId = usize;
type KnotId = usize;
type CallId = usize;

define_language! {
    pub enum Dataflow {
        Constant(i64),
        Param(ParamId),
        Phi(BlockId, [Id; 2]),
        Unary(UnaryOp, Id),
        Binary(BinaryOp, [Id; 2]),
        "Load" = Load(Id),
        Call(CallId),
        Knot(KnotId),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Block<'a> {
    Entry,
    Child(BlockId, Id),
    Merge(BlockId, BlockId),
    Store(BlockId, Id, Id),
    Call(BlockId, &'a str, Vec<Id>),
    Return(BlockId, Id),
}

#[derive(Debug, Default)]
pub struct SSAProgram<'a> {
    dfg: EGraph<Dataflow, ()>,
    cfg: Vec<Block<'a>>,

    param_map: FxHashMap<(&'a str, usize), ParamId>,
    knot_map: FxHashMap<(BlockId, &'a str), KnotId>,
    call_map: FxHashMap<(BlockId, usize), CallId>,
}

pub fn create_ssa<'a>(program: &'a FxHashMap<String, FuncAST>) -> SSAProgram<'a> {
    let Some(main) = program.get("main") else {
        return Default::default();
    };

    todo!()
}
