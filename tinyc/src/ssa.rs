use core::cell::RefCell;
use core::mem::replace;

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
        Load(BlockId, Id),
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
    fn add_data(&mut self, data: Dataflow) -> Id {
        self.dfg.add(data)
    }

    fn add_block(&mut self, block: Block<'a>) -> BlockId {
        let id = self.cfg.len();
        self.cfg.push(block);
        id
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

#[derive(Debug, Clone)]
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

    pub fn assign(&mut self, var: &'a str, value: Id) {
        self.vars.insert(var, value);
    }

    pub fn number(&self, num: i64) -> Id {
        self.ssa.borrow_mut().add_data(Dataflow::Constant(num))
    }

    pub fn variable(&self, var: &str) -> Id {
        self.vars[var]
    }

    pub fn unary(&self, op: UnaryOp, input: Id) -> Id {
        self.ssa.borrow_mut().add_data(Dataflow::Unary(op, input))
    }

    pub fn binary(&self, op: BinaryOp, lhs: Id, rhs: Id) -> Id {
        self.ssa
            .borrow_mut()
            .add_data(Dataflow::Binary(op, [lhs, rhs]))
    }

    pub fn load(&self, pointer: Id) -> Id {
        self.ssa
            .borrow_mut()
            .add_data(Dataflow::Load(self.block, pointer))
    }

    pub fn store(&mut self, pointer: Id, value: Id) {
        self.block = self
            .ssa
            .borrow_mut()
            .add_block(Block::Store(self.block, pointer, value));
    }

    pub fn is_always_false(&self, value: Id) -> bool {
        self.ssa.borrow().dfg[value]
            .iter()
            .any(|data| *data == Dataflow::Constant(0))
    }

    pub fn branch(&self, cond: Id) -> Option<Self> {
        if self.is_always_false(cond) {
            None
        } else {
            let block = self
                .ssa
                .borrow_mut()
                .add_block(Block::Child(self.block, cond));
            let mut branched = self.clone();
            branched.block = block;
            Some(branched)
        }
    }

    fn intersect<'c>(
        a: &'c FxHashMap<&'a str, Id>,
        b: &'c FxHashMap<&'a str, Id>,
        dfg: &'c EGraph<Dataflow, ()>,
    ) -> impl Iterator<Item = (&'a str, Id)> + 'c {
        a.into_iter().filter_map(|(name, a)| {
            if let Some(b) = b.get(name)
                && dfg.find(*a) == dfg.find(*b)
            {
                Some((*name, dfg.find(*a)))
            } else {
                None
            }
        })
    }

    fn difference<'c>(
        a: &'c FxHashMap<&'a str, Id>,
        b: &'c FxHashMap<&'a str, Id>,
        dfg: &'c EGraph<Dataflow, ()>,
    ) -> impl Iterator<Item = (&'a str, Id, Id)> + 'c {
        a.into_iter().filter_map(|(name, a)| {
            if let Some(b) = b.get(name)
                && dfg.find(*a) != dfg.find(*b)
            {
                Some((*name, dfg.find(*a), dfg.find(*b)))
            } else {
                None
            }
        })
    }

    pub fn forward_merge(a: &Self, b: &Self) -> Self {
        assert_eq!(a.function, b.function);
        let block = a.ssa.borrow_mut().add_block(Block::Merge(a.block, b.block));
        let mut vars: FxHashMap<&str, Id> =
            Self::intersect(&a.vars, &b.vars, &a.ssa.borrow().dfg).collect();
        let differences: Vec<_> = Self::difference(&a.vars, &b.vars, &a.ssa.borrow().dfg).collect();
        for (name, a_value, b_value) in differences {
            let phi = a
                .ssa
                .borrow_mut()
                .add_data(Dataflow::Phi(block, [a_value, b_value]));
            vars.insert(name, phi);
        }
        SSABuilder {
            ssa: a.ssa,
            vars,
            function: a.function,
            block,
        }
    }

    pub fn backward_merge(&mut self, other: &Self) {
        assert_eq!(self.function, other.function);
        let old_self_block = replace(&mut self.ssa.borrow_mut().cfg[self.block], Block::Entry);
        let old_self_block = self.ssa.borrow_mut().add_block(old_self_block);
        self.ssa.borrow_mut().cfg[self.block] = Block::Merge(old_self_block, other.block);
        let mut vars: FxHashMap<&str, Id> =
            Self::intersect(&self.vars, &other.vars, &self.ssa.borrow().dfg).collect();
        let differences: Vec<_> =
            Self::difference(&self.vars, &other.vars, &self.ssa.borrow().dfg).collect();
        for (name, _, _) in differences {
            let knot = self.ssa.borrow_mut().intern_knot(self.block, name);
            let knot = self.ssa.borrow_mut().add_data(Dataflow::Knot(knot));
            vars.insert(name, knot);
        }
        self.vars = vars;
    }
}
