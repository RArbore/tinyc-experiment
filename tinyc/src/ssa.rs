use core::cmp::max;
use core::fmt::{Display, Formatter, Result};

use egg::{EGraph, Id, Symbol, define_language};
use rustc_hash::FxHashMap;

use crate::analysis::interval::{Interval, IntervalAnalysis};
use crate::nonssa::{BinaryOp, UnaryOp};

pub type SSABlockId = usize;
pub type ParamId = usize;
pub type KnotId = usize;
pub type CallId = usize;

define_language! {
    pub enum Dataflow {
        Constant(i64),
        Unary(UnaryOp, Id),
        Binary(BinaryOp, [Id; 2]),
        Phi(SSABlockId, [Id; 2]),
        Load(SSABlockId, Id),
        Param(ParamId),
        Knot(KnotId),
        Call(CallId),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SSABlock {
    Entry,
    Guard(SSABlockId, Id),
    Merge(SSABlockId, SSABlockId),
    Store(SSABlockId, Id, Id),
    Call(SSABlockId, Symbol, Vec<Id>),
    Return(SSABlockId, Vec<Id>),
}

#[derive(Debug, Default)]
pub struct SSAProgram {
    pub dfg: EGraph<Dataflow, IntervalAnalysis>,
    pub cfg: Vec<SSABlock>,
    pub entries: FxHashMap<Symbol, SSABlockId>,
    pub exits: FxHashMap<Symbol, SSABlockId>,

    // Intern tuples of function name, parameter index, and analysis to ParamId.
    pub param_map: FxHashMap<(Symbol, usize, Interval), ParamId>,
    // Intern tuples of BlockId, variable name, and analysis to KnotId.
    pub knot_map: FxHashMap<(SSABlockId, Symbol, Interval), KnotId>,
    // Intern tuples of BlockId (of a Call node), return value index, and analysis to CallId.
    pub call_map: FxHashMap<(SSABlockId, usize, Interval), CallId>,
}

impl SSAProgram {
    pub fn add_data(&mut self, data: Dataflow) -> Id {
        self.dfg.add(data)
    }

    pub fn add_block(&mut self, block: SSABlock) -> SSABlockId {
        let id = self.cfg.len();
        self.cfg.push(block);
        id
    }

    pub fn set_block(&mut self, block: SSABlock, id: SSABlockId) {
        self.cfg[id] = block;
    }

    pub fn is_always_false(&mut self, value: Id) -> bool {
        self.dfg.rebuild();
        self.dfg[value].nodes.contains(&Dataflow::Constant(0))
    }

    pub fn analysis(&mut self, value: Id) -> Interval {
        self.dfg.rebuild();
        self.dfg[value].data
    }

    pub fn canon_cfg(&mut self) {
        for block in &mut self.cfg {
            match block {
                SSABlock::Entry | SSABlock::Merge(_, _) => {}
                SSABlock::Guard(_, cond) => *cond = self.dfg.find(*cond),
                SSABlock::Store(_, ptr, value) => {
                    *ptr = self.dfg.find(*ptr);
                    *value = self.dfg.find(*value);
                }
                SSABlock::Call(_, _, ids) | SSABlock::Return(_, ids) => {
                    ids.iter_mut().for_each(|id| *id = self.dfg.find(*id))
                }
            }
        }
    }

    pub fn intern_param(&mut self, function: Symbol, idx: usize, analysis: Interval) -> ParamId {
        if let Some(id) = self.param_map.get(&(function, idx, analysis)) {
            *id
        } else {
            let id = self.param_map.len();
            self.param_map.insert((function, idx, analysis), id);
            self.dfg.analysis.param_intervals.push(analysis);
            id
        }
    }

    pub fn intern_knot(&mut self, block: SSABlockId, var: Symbol, analysis: Interval) -> ParamId {
        if let Some(id) = self.knot_map.get(&(block, var, analysis)) {
            *id
        } else {
            let id = self.knot_map.len();
            self.knot_map.insert((block, var, analysis), id);
            self.dfg.analysis.knot_intervals.push(analysis);
            id
        }
    }

    pub fn intern_call(&mut self, caller: SSABlockId, idx: usize, analysis: Interval) -> ParamId {
        if let Some(id) = self.call_map.get(&(caller, idx, analysis)) {
            *id
        } else {
            let id = self.call_map.len();
            self.call_map.insert((caller, idx, analysis), id);
            self.dfg.analysis.call_intervals.push(analysis);
            id
        }
    }
}

impl Display for SSAProgram {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        writeln!(f, "DFG:")?;
        let mut classes: Vec<_> = self.dfg.classes().collect();
        let indent = max(
            max(classes.len(), 1).ilog10(),
            max(self.cfg.len(), 1).ilog10(),
        ) + 3;
        classes.sort_by_key(|class| class.id);
        for class in classes {
            write!(f, "{}:", class.id)?;
            for _ in 0..(indent - usize::from(class.id).checked_ilog10().unwrap_or(0) - 2) {
                write!(f, " ")?;
            }
            writeln!(f, "{:?}", class.nodes[0])?;
            for node in &class.nodes[1..] {
                for _ in 0..indent {
                    write!(f, " ")?;
                }
                writeln!(f, "{:?}", node)?;
            }
        }

        writeln!(f, "\nCFG:")?;
        for (id, block) in self.cfg.iter().enumerate() {
            write!(f, "{}:", id)?;
            for _ in 0..(indent - usize::from(id).checked_ilog10().unwrap_or(0) - 2) {
                write!(f, " ")?;
            }
            writeln!(f, "{:?}", block)?;
        }

        writeln!(f, "\nEntries:")?;
        for (func, entry) in &self.entries {
            writeln!(f, "{}: {}", func, entry)?;
        }

        if !self.param_map.is_empty() {
            writeln!(f, "\nParam IDs:")?;
            for ((func, idx, analysis), id) in &self.param_map {
                writeln!(f, "{}, {}, {}: {}", func, idx, analysis, id)?;
            }
        }

        if !self.knot_map.is_empty() {
            writeln!(f, "\nKnot IDs:")?;
            for ((block, var, analysis), id) in &self.knot_map {
                writeln!(f, "{}, {}, {}: {}", block, var, analysis, id)?;
            }
        }

        if !self.call_map.is_empty() {
            writeln!(f, "\nCall IDs:")?;
            for ((caller, idx, analysis), id) in &self.call_map {
                writeln!(f, "{}, {}, {}: {}", caller, idx, analysis, id)?;
            }
        }

        Ok(())
    }
}
