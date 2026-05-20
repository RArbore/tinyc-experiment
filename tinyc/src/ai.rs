use core::hash::Hash;
use core::iter::zip;
use core::mem::take;

use egg::{Id, Symbol};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::analysis::interval::Interval;
use crate::ssa::{Dataflow, SSABlock, SSABlockId, SSAProgram};

pub fn megapass(ssa: &mut SSAProgram) {
    let intra_func_deps = intra_func_deps(ssa);
    let old_entries = ssa.entries.clone();
    let inverse_old_entries = old_entries
        .iter()
        .map(|(func, block)| (*block, *func))
        .collect();
    let mut old_block_to_phis: FxHashMap<SSABlockId, FxHashSet<Id>> = FxHashMap::default();
    for eclass in ssa.dfg.classes() {
        for node in &eclass.nodes {
            if let Dataflow::Phi(block, _) = node {
                old_block_to_phis
                    .entry(*block)
                    .or_default()
                    .insert(eclass.id);
            }
        }
    }
    let main_entry = ssa.entries[&("main".into())];
    ssa.entries.clear();
    ssa.exits.clear();

    let mut context = AIContext {
        ssa: take(ssa),
        intra_func_deps,
        old_entries,
        inverse_old_entries,
        old_block_to_phis,
        states: Default::default(),
        created_blocks: Default::default(),
        callers: FxHashMap::from_iter([("main".into(), FxHashSet::default())]),
        input_analysis: FxHashMap::from_iter([("main".into(), vec![])]),
        output_analysis: Default::default(),
        intraprocedural_block_deps: Default::default(),
        interprocedural_call_deps: Default::default(),
        widening_new_blocks: Default::default(),
        widening_funcs: Default::default(),
        widening_new_blocks_dirty: false,
        widening_funcs_dirty: false,
        old_analysis_at_new_block: Default::default(),
        to_visit: vec![main_entry],
        knots_to_tie: Default::default(),
    };

    while let Some(block) = context.to_visit.pop() {
        context.visit_block(block);
    }

    context.tie_knots();
    context.ssa.canon_cfg();
    *ssa = context.ssa
}

#[derive(Debug)]
struct AIContext {
    ssa: SSAProgram,
    intra_func_deps: FxHashMap<SSABlockId, FxHashSet<SSABlockId>>,
    old_entries: FxHashMap<Symbol, SSABlockId>,
    inverse_old_entries: FxHashMap<SSABlockId, Symbol>,
    old_block_to_phis: FxHashMap<SSABlockId, FxHashSet<Id>>,

    states: FxHashMap<SSABlockId, AIState>,
    created_blocks: FxHashMap<SSABlockId, SSABlockId>,

    callers: FxHashMap<Symbol, FxHashSet<SSABlockId>>,
    input_analysis: FxHashMap<Symbol, Vec<Interval>>,
    output_analysis: FxHashMap<Symbol, Vec<Interval>>,

    intraprocedural_block_deps: FxHashMap<SSABlockId, FxHashSet<SSABlockId>>,
    interprocedural_call_deps: FxHashMap<Symbol, FxHashSet<Symbol>>,
    widening_new_blocks: FxHashSet<SSABlockId>,
    widening_funcs: FxHashSet<Symbol>,
    widening_new_blocks_dirty: bool,
    widening_funcs_dirty: bool,
    old_analysis_at_new_block: FxHashMap<SSABlockId, FxHashMap<Id, Interval>>,

    to_visit: Vec<SSABlockId>,
    knots_to_tie: FxHashMap<(SSABlockId, Id), Id>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AIState {
    phis: FxHashMap<Id, Id>,

    new_block: SSABlockId,
    func: Symbol,
}

impl AIContext {
    fn set_block(
        &mut self,
        func: Symbol,
        old_block_id: SSABlockId,
        new_block: SSABlock,
    ) -> SSABlockId {
        let new_block_id =
            if let Some(old_new_block_id) = self.created_blocks.get(&old_block_id).copied() {
                self.ssa.cfg[old_new_block_id] = new_block;
                old_new_block_id
            } else {
                let new_block_id = self.ssa.cfg.len();
                self.ssa.cfg.push(new_block);
                self.created_blocks.insert(old_block_id, new_block_id);
                new_block_id
            };

        self.intraprocedural_block_deps
            .entry(new_block_id)
            .or_default();
        self.interprocedural_call_deps.entry(func).or_default();
        match self.ssa.cfg[new_block_id] {
            SSABlock::Entry => {}
            SSABlock::Guard(pred, ..) | SSABlock::Store(pred, ..) | SSABlock::Return(pred, ..) => {
                self.widening_new_blocks_dirty |= self
                    .intraprocedural_block_deps
                    .entry(pred)
                    .or_default()
                    .insert(new_block_id);
            }
            SSABlock::Call(pred, callee, ..) => {
                self.widening_new_blocks_dirty |= self
                    .intraprocedural_block_deps
                    .entry(pred)
                    .or_default()
                    .insert(new_block_id);
                self.widening_funcs_dirty |= self
                    .interprocedural_call_deps
                    .entry(func)
                    .or_default()
                    .insert(callee);
            }
            SSABlock::Merge(pred1, pred2) => {
                self.widening_new_blocks_dirty |= self
                    .intraprocedural_block_deps
                    .entry(pred1)
                    .or_default()
                    .insert(new_block_id);
                self.widening_new_blocks_dirty |= self
                    .intraprocedural_block_deps
                    .entry(pred2)
                    .or_default()
                    .insert(new_block_id);
            }
        }

        new_block_id
    }

    fn update_state(&mut self, old_block: SSABlockId, state: AIState) {
        if self
            .states
            .get(&old_block)
            .map(|old_state| old_state != &state)
            .unwrap_or(true)
        {
            self.states.insert(old_block, state);
            self.to_visit
                .extend(self.intra_func_deps[&old_block].iter().copied());
        }
    }

    fn is_widening_new_block(&mut self, id: SSABlockId) -> bool {
        if self.widening_new_blocks_dirty {
            let mut headers = Vec::from_iter(cycle_headers(
                &self.intraprocedural_block_deps,
                self.ssa.entries.values().copied(),
            ));
            while let Some(header) = headers.pop() {
                match self.ssa.cfg[header] {
                    SSABlock::Entry => panic!(),
                    SSABlock::Guard(pred, ..) => headers.push(pred),
                    SSABlock::Store(pred, ..) => headers.push(pred),
                    SSABlock::Call(pred, ..) => headers.push(pred),
                    SSABlock::Return(pred, ..) => headers.push(pred),
                    SSABlock::Merge(..) => {
                        self.widening_new_blocks.insert(header);
                    }
                }
            }
            self.widening_new_blocks.extend(headers);
            self.widening_funcs_dirty = false;
        }

        self.widening_new_blocks.contains(&id)
    }

    fn is_widening_func(&mut self, func: Symbol) -> bool {
        if self.widening_funcs_dirty {
            let headers =
                cycle_headers(&self.interprocedural_call_deps, ["main".into()].into_iter());
            self.widening_funcs.extend(headers);
            self.widening_funcs_dirty = false;
        }

        self.widening_funcs.contains(&func)
    }

    fn visit_block(&mut self, old_block: SSABlockId) {
        match self.ssa.cfg[old_block].clone() {
            SSABlock::Entry => self.visit_entry(old_block),
            SSABlock::Guard(pred, cond) => self.visit_guard(old_block, pred, cond),
            SSABlock::Merge(pred1, pred2) => self.visit_merge(old_block, pred1, pred2),
            SSABlock::Store(pred, pointer, expr) => {
                self.visit_store(old_block, pred, pointer, expr)
            }
            SSABlock::Call(pred, callee, args) => self.visit_call(old_block, pred, callee, args),
            SSABlock::Return(pred, exprs) => self.visit_return(old_block, pred, exprs),
        }
    }

    fn visit_entry(&mut self, old_block: SSABlockId) {
        let func = self.inverse_old_entries[&old_block];
        let new_block = self.set_block(func, old_block, SSABlock::Entry);
        let state = AIState {
            phis: Default::default(),
            new_block,
            func,
        };
        self.ssa.entries.insert(func, new_block);
        self.update_state(old_block, state);
    }

    fn visit_guard(&mut self, old_block: SSABlockId, pred: SSABlockId, cond: Id) {
        if let Some(mut state) = self.states.get(&pred).cloned() {
            let value = self.visit_id(cond, &state);
            if !self.ssa.is_always_false(value) {
                state.new_block = self.set_block(
                    state.func,
                    old_block,
                    SSABlock::Guard(state.new_block, value),
                );
                self.update_state(old_block, state);
            }
        }
    }

    fn visit_merge(&mut self, old_block: SSABlockId, pred1: SSABlockId, pred2: SSABlockId) {
        match (
            self.states.get(&pred1).cloned(),
            self.states.get(&pred2).cloned(),
        ) {
            (Some(state1), Some(state2)) => {
                let new_block = self.set_block(
                    state1.func,
                    old_block,
                    SSABlock::Merge(state1.new_block, state2.new_block),
                );
                let is_widening = self.is_widening_new_block(new_block);

                let mut phis = FxHashMap::default();
                for (old_phi_id, id1) in &state1.phis {
                    if let Some(id2) = state2.phis.get(&old_phi_id) {
                        assert_eq!(*id1, *id2);
                        phis.insert(*old_phi_id, *id1);
                    }
                }
                for old_phi_id in self.old_block_to_phis[&old_block].clone() {
                    for node in self.ssa.dfg[old_phi_id].nodes.clone() {
                        if let Dataflow::Phi(block, inputs) = node {
                            assert_eq!(old_block, block);
                            let lhs = self.visit_id(inputs[0], &state1);
                            let rhs = self.visit_id(inputs[1], &state2);
                            if lhs == rhs {
                                phis.insert(old_phi_id, lhs);
                            } else {
                                let mut analysis =
                                    self.ssa.analysis(lhs).join(&self.ssa.analysis(rhs));
                                if is_widening
                                    && let Some(old_analysis) =
                                        self.old_analysis_at_new_block.get(&new_block)
                                {
                                    analysis = old_analysis[&old_phi_id].widen(&analysis);
                                }
                                let knot = self.ssa.intern_knot(new_block, old_phi_id, analysis);
                                let knot = self.ssa.add_data(Dataflow::Knot(knot));
                                phis.insert(old_phi_id, knot);
                                self.knots_to_tie.insert((old_block, old_phi_id), knot);
                            }
                            break;
                        }
                    }
                }

                if is_widening {
                    for (old_phi_id, id) in &phis {
                        self.old_analysis_at_new_block
                            .entry(new_block)
                            .or_default()
                            .insert(*old_phi_id, self.ssa.analysis(*id));
                    }
                }

                let state = AIState {
                    phis,
                    new_block,
                    func: state1.func,
                };
                self.update_state(old_block, state);
            }
            (Some(mut state), None) => {
                for old_phi_id in &self.old_block_to_phis[&old_block] {
                    for node in self.ssa.dfg[*old_phi_id].nodes.clone() {
                        if let Dataflow::Phi(block, inputs) = node {
                            assert_eq!(old_block, block);
                            state.phis.insert(*old_phi_id, inputs[0]);
                            break;
                        }
                    }
                }
                self.update_state(old_block, state)
            },
            (None, Some(mut state)) => {
                for old_phi_id in &self.old_block_to_phis[&old_block] {
                    for node in self.ssa.dfg[*old_phi_id].nodes.clone() {
                        if let Dataflow::Phi(block, inputs) = node {
                            assert_eq!(old_block, block);
                            state.phis.insert(*old_phi_id, inputs[1]);
                            break;
                        }
                    }
                }
                self.update_state(old_block, state)
            },
            (None, None) => {}
        }
    }

    fn visit_store(&mut self, old_block: SSABlockId, pred: SSABlockId, pointer: Id, to_store: Id) {
        if let Some(mut state) = self.states.get(&pred).cloned() {
            let pointer_value = self.visit_id(pointer, &state);
            let to_store_value = self.visit_id(to_store, &state);
            state.new_block = self.set_block(
                state.func,
                old_block,
                SSABlock::Store(state.new_block, pointer_value, to_store_value),
            );
            self.update_state(old_block, state);
        }
    }

    fn visit_call(
        &mut self,
        old_block: SSABlockId,
        pred: SSABlockId,
        callee: Symbol,
        args: Vec<Id>,
    ) {
        if let Some(mut state) = self.states.get(&pred).cloned() {
            let is_widening = self.is_widening_func(callee);
            let arg_values: Vec<_> = args.iter().map(|arg| self.visit_id(*arg, &state)).collect();
            let mut changed = false;
            if let Some(input_analysis) = self.input_analysis.get_mut(&callee) {
                for (old_analysis, arg_value) in zip(input_analysis.iter_mut(), &arg_values) {
                    let new_analysis = if is_widening {
                        old_analysis.widen(&self.ssa.analysis(*arg_value))
                    } else {
                        old_analysis.join(&self.ssa.analysis(*arg_value))
                    };
                    if *old_analysis != new_analysis {
                        *old_analysis = new_analysis;
                        changed = true;
                    }
                }
            } else {
                self.input_analysis.insert(
                    callee,
                    arg_values
                        .iter()
                        .map(|arg_value| self.ssa.analysis(*arg_value))
                        .collect(),
                );
                changed = true;
            }
            if changed {
                self.to_visit.push(self.old_entries[&callee]);
            }

            state.new_block = self.set_block(
                state.func,
                old_block,
                SSABlock::Call(state.new_block, callee, arg_values),
            );
            self.callers.entry(callee).or_default().insert(old_block);

            if self.output_analysis.get(&callee).is_some() {
                self.update_state(old_block, state);
            }
        }
    }

    fn visit_return(&mut self, old_block: SSABlockId, pred: SSABlockId, values: Vec<Id>) {
        if let Some(mut state) = self.states.get(&pred).cloned() {
            let is_widening = self.is_widening_func(state.func);
            let values: Vec<_> = values.iter().map(|id| self.visit_id(*id, &state)).collect();
            let mut changed = false;
            if let Some(output_analysis) = self.output_analysis.get_mut(&state.func) {
                for (old_analysis, value) in zip(output_analysis.iter_mut(), &values) {
                    let mut new_analysis = self.ssa.analysis(*value);
                    if is_widening {
                        new_analysis = old_analysis.widen(&new_analysis);
                    }
                    if *old_analysis != new_analysis {
                        *old_analysis = new_analysis;
                        changed = true;
                    }
                }
            } else {
                self.output_analysis.insert(
                    state.func,
                    values
                        .iter()
                        .map(|value| self.ssa.analysis(*value))
                        .collect(),
                );
                changed = true;
            }
            if changed {
                let callers = self.callers[&state.func].iter().copied();
                self.to_visit.extend(callers);
            }

            state.new_block = self.set_block(
                state.func,
                old_block,
                SSABlock::Return(state.new_block, values),
            );
            self.ssa.exits.insert(state.func, state.new_block);
            self.update_state(old_block, state);
        }
    }

    fn visit_id(&mut self, id: Id, state: &AIState) -> Id {
        use Dataflow::*;
        let mut unioned = None;
        for node in self.ssa.dfg[id].nodes.clone() {
            let new_id = match node {
                Constant(_) => id,
                Unary(op, id) => {
                    let id = self.visit_id(id, state);
                    self.ssa.add_data(Unary(op, id))
                }
                Binary(op, ids) => {
                    let lhs = self.visit_id(ids[0], state);
                    let rhs = self.visit_id(ids[1], state);
                    self.ssa.add_data(Binary(op, [lhs, rhs]))
                }
                Phi(_, _) => state.phis[&id],
                Load(old_block, id) => {
                    let new_block = self.states[&old_block].new_block;
                    let id = self.visit_id(id, state);
                    self.ssa.add_data(Load(new_block, id))
                }
                Param(param_id) => {
                    let (func, idx, _) = self.ssa.param(param_id);
                    let interval = self.input_analysis[&func][idx];
                    let param_id = self.ssa.intern_param(func, idx, interval);
                    self.ssa.add_data(Param(param_id))
                }
                Knot(_) => panic!(),
                Call(call_id) => {
                    let (old_caller, idx, _) = self.ssa.call(call_id);
                    let SSABlock::Call(_, callee, _) = self.ssa.cfg[old_caller] else {
                        panic!()
                    };
                    let interval = self.output_analysis[&callee][idx];
                    let new_caller = self.states[&old_caller].new_block;
                    let call_id = self.ssa.intern_call(new_caller, idx, interval);
                    self.ssa.add_data(Call(call_id))
                }
            };
            if let Some(unioned) = unioned {
                self.ssa.dfg.union(unioned, new_id);
            } else {
                unioned = Some(new_id);
            }
        }
        unioned.unwrap()
    }

    fn tie_knots(&mut self) {
        self.ssa.dfg.rebuild();
    }
}

fn intra_func_deps(ssa: &SSAProgram) -> FxHashMap<SSABlockId, FxHashSet<SSABlockId>> {
    let mut deps: FxHashMap<SSABlockId, FxHashSet<SSABlockId>> = FxHashMap::default();
    for (id, block) in ssa.cfg.iter().enumerate() {
        deps.entry(id).or_default();
        match block {
            SSABlock::Entry => {}
            SSABlock::Guard(pred, ..)
            | SSABlock::Store(pred, ..)
            | SSABlock::Call(pred, ..)
            | SSABlock::Return(pred, ..) => {
                deps.entry(*pred).or_default().insert(id);
            }
            SSABlock::Merge(pred1, pred2) => {
                deps.entry(*pred1).or_default().insert(id);
                deps.entry(*pred2).or_default().insert(id);
            }
        }
    }
    deps
}

fn cycle_headers<T, I>(graph: &FxHashMap<T, FxHashSet<T>>, roots: I) -> FxHashSet<T>
where
    T: Copy + Eq + Hash,
    I: Iterator<Item = T>,
{
    let mut headers = FxHashSet::default();
    let mut visited = FxHashSet::default();
    let order = dfs(graph, roots);
    for node in order {
        for succ in &graph[&node] {
            if !visited.contains(succ) {
                headers.insert(*succ);
            }
        }
        visited.insert(node);
    }
    headers
}

fn dfs<T, I>(graph: &FxHashMap<T, FxHashSet<T>>, roots: I) -> Vec<T>
where
    T: Copy + Eq + Hash,
    I: Iterator<Item = T>,
{
    let mut order = vec![];
    let mut visited = FxHashSet::default();
    for root in roots {
        dfs_helper(graph, root, &mut order, &mut visited);
    }
    order
}

fn dfs_helper<T>(
    graph: &FxHashMap<T, FxHashSet<T>>,
    node: T,
    order: &mut Vec<T>,
    visited: &mut FxHashSet<T>,
) where
    T: Copy + Eq + Hash,
{
    if !visited.contains(&node) {
        visited.insert(node);
        for succ in &graph[&node] {
            dfs_helper(graph, *succ, order, visited);
        }
        order.push(node);
    }
}

#[cfg(test)]
mod tests {
    use rustc_hash::{FxHashMap, FxHashSet};

    use crate::ai::megapass;
    use crate::imp::ast::naive_ssa_translate;
    use crate::imp::grammar::ProgramParser;

    use super::*;

    #[test]
    fn detect_no_cycle() {
        let mut graph: FxHashMap<usize, FxHashSet<usize>> = FxHashMap::default();
        graph.entry(0).or_default().insert(1);
        graph.entry(0).or_default().insert(2);
        graph.entry(1).or_default().insert(3);
        graph.entry(2).or_default().insert(3);
        graph.entry(3).or_default();
        graph.entry(4).or_default().insert(5);
        graph.entry(5).or_default();
        let headers = cycle_headers(&graph, [0, 4].into_iter());
        assert!(headers.is_empty());
    }

    #[test]
    fn detect_cycle() {
        let mut graph: FxHashMap<usize, FxHashSet<usize>> = FxHashMap::default();
        graph.entry(0).or_default().insert(1);
        graph.entry(0).or_default().insert(2);
        graph.entry(1).or_default().insert(3);
        graph.entry(2).or_default().insert(3);
        graph.entry(3).or_default().insert(4);
        graph.entry(4).or_default().insert(1);
        graph.entry(0).or_default().insert(5);
        graph.entry(5).or_default().insert(5);
        let headers = cycle_headers(&graph, [0].into_iter());
        assert_eq!(headers.len(), 2);
        assert!(headers.contains(&1) || headers.contains(&3) || headers.contains(&4));
        assert!(headers.contains(&5));
    }

    fn get_return_analysis(ssa: &SSAProgram, func: &str) -> Interval {
        let SSABlock::Return(_, values) = &ssa.cfg[ssa.exits[&(func.into())]] else {
            panic!()
        };
        assert_eq!(values.len(), 1);
        ssa.analysis(values[0])
    }

    #[test]
    fn translate1() {
        let program = r#"
fn main() { x <- foo(5, 1); y <- foo(3, 5 - 4); return x * y; }
fn foo(x, y) return x + y;
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let mut ssa = naive_ssa_translate(&parsed);
        assert!(get_return_analysis(&ssa, "main").is_top());
        assert!(get_return_analysis(&ssa, "foo").is_top());
        megapass(&mut ssa);
        assert!(get_return_analysis(&ssa, "main").leq(&Interval::from_low_high(16, 36)));
        assert!(get_return_analysis(&ssa, "foo").leq(&Interval::from_low_high(4, 6)));
    }

    #[test]
    fn translate2() {
        let program = r#"
fn main() { x <- foo(7); return x; }
fn foo(x) { x <- foo(x + 1); return x; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let mut ssa = naive_ssa_translate(&parsed);
        megapass(&mut ssa);
        assert_eq!(ssa.entries.len(), 2);
        assert!(ssa.exits.is_empty());
    }

    #[test]
    fn translate3() {
        let program = r#"
fn main() { if 0 { x <- foo(24); } else { x = 42; } return x; }
fn foo(x) { return x; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let mut ssa = naive_ssa_translate(&parsed);
        megapass(&mut ssa);
        assert_eq!(ssa.entries.len(), 1);
        assert_eq!(ssa.exits.len(), 1);
        assert!(get_return_analysis(&ssa, "main").is_cons(42));
    }

    #[test]
    fn translate4() {
        let program = r#"
fn main() { x = 1; while x < 100 { x = x + (1 * 5); } return x; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let mut ssa = naive_ssa_translate(&parsed);
        megapass(&mut ssa);
        assert!(get_return_analysis(&ssa, "main").leq(&Interval::from_low(1)));
    }

    #[test]
    fn translate5() {
        let program = r#"
fn main() { x = 1; while x < 100 { x = x + (1 * 5); } foo(); return x; }
fn foo() { x = 5; y = 8; while y < 100 { x = x + 1; } baz(); return y; }
fn baz() { return 42; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let mut ssa = naive_ssa_translate(&parsed);
        megapass(&mut ssa);

        assert!(ssa.exits.is_empty());
    }

    #[test]
    fn translate6() {
        let program = r#"
fn main() { x <- foo(7); return x; }
fn foo(x) { if x { x <- foo(x - 1); return x + 1; } else { return 0; } }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        let mut ssa = naive_ssa_translate(&parsed);
        megapass(&mut ssa);

        let SSABlock::Return(_, values) = &ssa.cfg[ssa.exits[&("main".into())]] else {
            panic!()
        };
        assert_eq!(values.len(), 1);
        assert!(ssa.analysis(values[0]).leq(&Interval::from_low(0)));
    }
}
