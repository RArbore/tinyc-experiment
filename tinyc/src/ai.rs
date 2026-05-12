use core::cell::RefCell;
use core::mem::take;
use std::rc::Rc;

use egg::{Id, Symbol};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::nonssa::{Block, BlockId, Expr, NonSSAFunc, UnaryOp};
use crate::ssa::{Dataflow, SSABlock, SSABlockId, SSAProgram};

pub fn create_ssa(nonssa: FxHashMap<Symbol, NonSSAFunc>) -> SSAProgram {
    let deps = deps(&nonssa);
    let mut context = AIContext {
        nonssa,
        deps,
        ssa: Default::default(),
        states: Default::default(),
        to_visit: FxHashSet::from_iter([("main".into(), 0)]),
    };

    while !context.to_visit.is_empty() {
        let to_visit = take(&mut context.to_visit);
        for (func, block) in to_visit {
            context.visit_block(func, block);
        }
    }

    context.ssa
}

#[derive(Debug)]
struct AIContext {
    nonssa: FxHashMap<Symbol, NonSSAFunc>,
    deps: FxHashMap<Symbol, FxHashMap<BlockId, FxHashSet<BlockId>>>,
    ssa: SSAProgram,

    states: FxHashMap<(Symbol, BlockId), AIState>,

    to_visit: FxHashSet<(Symbol, BlockId)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AIState {
    vars: FxHashMap<Symbol, Id>,
    ssa_block: SSABlockId,
}

impl AIContext {
    fn try_old_ssa_block(&self, func: Symbol, block: BlockId) -> Option<SSABlockId> {
        self.states.get(&(func, block)).map(|state| state.ssa_block)
    }

    fn set_block(&mut self, func: Symbol, block: BlockId, ssa_block: SSABlock) -> SSABlockId {
        if let Some(old_ssa_block) = self.try_old_ssa_block(func, block) {
            self.ssa.cfg[old_ssa_block] = ssa_block;
            old_ssa_block
        } else {
            let id = self.ssa.cfg.len();
            self.ssa.cfg.push(ssa_block);
            id
        }
    }
    
    fn update_state(&mut self, func: Symbol, block: BlockId, state: AIState) {
        if let Some(old_state) = self.states.get(&(func, block))
            && old_state != &state
        {
            self.states.insert((func, block), state);
            self.to_visit
                .extend(self.deps[&func][&block].iter().map(|block| (func, *block)));
        }
    }

    fn visit_block(&mut self, func: Symbol, block: BlockId) {
        match &self.nonssa[&func].cfg[block] {
            Block::Entry => self.visit_entry(func, block),
            Block::Guard(pred, cond) => todo!(),
            Block::Assign(pred, var, expr) => todo!(),
            Block::Merge(pred1, pred2) => todo!(),
            Block::Store(pred, pointer, expr) => todo!(),
            Block::Call(pred, vars, callee, args) => todo!(),
            Block::Return(pred, exprs) => todo!(),
        }
    }

    fn visit_entry(&mut self, func: Symbol, block: BlockId) {
        let nonssa_func = &self.nonssa[&func];
        let vars = nonssa_func
            .params
            .iter()
            .enumerate()
            .map(|(idx, param)| (*param, self.ssa.add_data(Dataflow::Param(idx))))
            .collect();
        let ssa_block = self.set_block(func, block, SSABlock::Entry);
        let state = AIState {
            vars,
            ssa_block,
        };
        self.update_state(func, block, state);
    }
}

fn deps(
    nonssa: &FxHashMap<Symbol, NonSSAFunc>,
) -> FxHashMap<Symbol, FxHashMap<BlockId, FxHashSet<BlockId>>> {
    nonssa
        .iter()
        .map(|(_, func)| {
            let mut deps = FxHashMap::default();
            for id in 0..func.cfg.len() {
                deps.insert(id, FxHashSet::default());
            }
            for (id, block) in func.cfg.iter().enumerate() {
                match block {
                    Block::Entry => {}
                    Block::Guard(pred, ..)
                    | Block::Assign(pred, ..)
                    | Block::Store(pred, ..)
                    | Block::Call(pred, ..)
                    | Block::Return(pred, ..) => {
                        deps.entry(*pred).or_default().insert(id);
                    }
                    Block::Merge(pred1, pred2) => {
                        deps.entry(*pred1).or_default().insert(id);
                        deps.entry(*pred2).or_default().insert(id);
                    }
                }
            }
            (func.name, deps)
        })
        .collect()
}
