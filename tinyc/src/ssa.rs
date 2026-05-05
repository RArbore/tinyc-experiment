use derive_more::FromStr;
use egg::{EGraph, Id, define_language, Symbol};
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
pub type ParamId = usize;
pub type KnotId = usize;
pub type CallId = usize;

define_language! {
    pub enum Dataflow {
        Constant(i64),
        Unary(UnaryOp, Id),
        Binary(BinaryOp, [Id; 2]),
        Phi(BlockId, [Id; 2]),
        Load(BlockId, Id),
        Param(ParamId),
        Knot(KnotId),
        Call(CallId),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Block {
    Entry,
    Child(BlockId, Id),
    Merge(BlockId, BlockId),
    Store(BlockId, Id, Id),
    Call(BlockId, Symbol, Vec<Id>),
    Return(BlockId, Vec<Id>),
}

#[derive(Debug, Default)]
pub struct SSAProgram {
    dfg: EGraph<Dataflow, ()>,
    cfg: Vec<Block>,
    entries: FxHashMap<Symbol, BlockId>,

    // Intern pairs of function name and parameter index to ParamId.
    param_map: FxHashMap<(Symbol, usize), ParamId>,
    // Intern pairs of BlockId and variable name to KnotId.
    knot_map: FxHashMap<(BlockId, Symbol), KnotId>,
    // Intern tuples of BlockId (of a Call node) and return value index to CallId.
    call_map: FxHashMap<(BlockId, usize), CallId>,
}

impl SSAProgram {
    pub fn add_data(&mut self, data: Dataflow) -> Id {
        self.dfg.add(data)
    }

    pub fn add_block(&mut self, block: Block) -> BlockId {
        let id = self.cfg.len();
        self.cfg.push(block);
        id
    }

    pub fn add_entry(&mut self, function: Symbol, block: BlockId) {
        self.entries.insert(function, block);
    }

    pub fn intern_param(&mut self, function: Symbol, idx: usize) -> ParamId {
        if let Some(id) = self.param_map.get(&(function, idx)) {
            *id
        } else {
            let id = self.param_map.len();
            self.param_map.insert((function, idx), id);
            id
        }
    }

    pub fn intern_knot(&mut self, block: BlockId, var: Symbol) -> ParamId {
        if let Some(id) = self.knot_map.get(&(block, var)) {
            *id
        } else {
            let id = self.knot_map.len();
            self.knot_map.insert((block, var), id);
            id
        }
    }

    pub fn intern_call(&mut self, caller: BlockId, idx: usize) -> ParamId {
        if let Some(id) = self.call_map.get(&(caller, idx)) {
            *id
        } else {
            let id = self.call_map.len();
            self.call_map.insert((caller, idx), id);
            id
        }
    }
}
