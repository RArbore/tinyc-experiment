use core::cell::RefCell;

use derive_more::FromStr;
use egg::{EGraph, Id, define_language};
use rustc_hash::FxHashMap;

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash, FromStr)]
pub enum UnaryOp {
    Neg,
    Not,
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash, FromStr)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    EE,
    NE,
    LT,
    LE,
    GT,
    GE,
}

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

    // Intern pairs of function name and parameter index to ParamId.
    param_map: FxHashMap<(&'a str, usize), ParamId>,
    // Intern pairs of BlockId and variable name to KnotId.
    knot_map: FxHashMap<(BlockId, &'a str), KnotId>,
    // Intern pairs of BlockId (of Call blocks) and return value index to CallId.
    call_map: FxHashMap<(BlockId, usize), CallId>,
}

impl<'a> SSAProgram<'a> {
    fn add_block(&mut self, block: Block<'a>) -> BlockId {
        let id = self.cfg.len();
        self.cfg.push(block);
        id
    }

    fn erase_blocks(&mut self, remove_from: BlockId) {
        self.cfg.truncate(remove_from);
    }

    fn intern_param(&mut self, var: &'a str, idx: usize) -> ParamId {
        if let Some(id) = self.param_map.get(&(var, idx)) {
            *id
        } else {
            let id = self.param_map.len();
            self.param_map.insert((var, idx), id);
            id
        }
    }

    fn intern_knot(&mut self, block: BlockId, var: &'a str) -> ParamId {
        if let Some(id) = self.knot_map.get(&(block, var)) {
            *id
        } else {
            let id = self.knot_map.len();
            self.knot_map.insert((block, var), id);
            id
        }
    }

    fn intern_call(&mut self, block: BlockId, idx: usize) -> ParamId {
        if let Some(id) = self.call_map.get(&(block, idx)) {
            *id
        } else {
            let id = self.call_map.len();
            self.call_map.insert((block, idx), id);
            id
        }
    }
}

#[derive(Debug)]
pub struct SSABuilder<'a, 'b> {
    ssa: &'b RefCell<SSAProgram<'a>>,

    vars: FxHashMap<&'a str, Id>,
    function: &'a str,
    block: BlockId,
}

impl<'a, 'b> SSABuilder<'a, 'b> {
    pub fn entry<I>(function: &'a str, params: I, ssa: &'b RefCell<SSAProgram<'a>>) -> Self
    where
        I: Iterator<Item = &'a str>,
    {
        let block = ssa.borrow_mut().add_block(Block::Entry);
        SSABuilder {
            ssa,
            vars: params
                .enumerate()
                .map(|(idx, var)| {
                    let mut ssa = ssa.borrow_mut();
                    let param_id = ssa.intern_param(var, idx);
                    let value = ssa.dfg.add(Dataflow::Param(param_id));
                    (var, value)
                })
                .collect(),
            function,
            block,
        }
    }
}
