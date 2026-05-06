use core::cell::RefCell;
use core::iter::zip;

use egg::{Id, Symbol};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::imp::ast::{ExprAST, FuncAST, StmtAST};
use crate::ssa::{Block, BlockId, Dataflow, SSAProgram};

pub fn create_ssa(ast: &FxHashMap<Symbol, FuncAST>) -> SSAProgram {
    let mut state = FIA {
        ast,
        ssa: Default::default(),
        callgraph: Default::default(),
    };
    if let Some(main) = ast.get(&Symbol::from("main")) {
        state.interp_func(main, vec![]);
    }
    state.ssa
}

// Flow insensitive abstraction (the SSA program being built and the call graph).
#[derive(Debug)]
struct FIA<'a> {
    ast: &'a FxHashMap<Symbol, FuncAST>,
    ssa: SSAProgram,
    callgraph: Callgraph,
}

#[derive(Debug, Default)]
struct Callgraph {
    callers: FxHashMap<Symbol, FxHashMap<BlockId, Vec<Id>>>,
    param_nodes: FxHashMap<Symbol, Vec<Id>>,
}

// Flow sensitive abstraction (mapping from program variable to e-class ID).
#[derive(Debug, Clone)]
struct FSA<'a> {
    vars: FxHashMap<Symbol, Id>,
    block: BlockId,
    returned: &'a RefCell<FxHashSet<(BlockId, Vec<Id>)>>,
}

impl<'a> FIA<'a> {
    fn interp_func(&mut self, func: &'a FuncAST, args: Vec<Id>) -> Vec<Id> {
        let entry = self.ssa.add_block(Block::Entry);
        self.ssa.add_entry(func.name, entry);
        let returned = Default::default();
        let fsa = FSA {
            vars: zip(func.params.iter(), args)
                .map(|(name, id)| (*name, id))
                .collect(),
            block: entry,
            returned: &returned,
        };
        assert!(self.interp_stmt(&func.body, fsa).is_none());

        let mut returned = returned.into_inner().into_iter();
        let (mut acc_block, mut acc_values) = returned.next().unwrap();
        for (new_block, new_values) in returned {
            acc_block = self.ssa.add_block(Block::Merge(acc_block, new_block));
            assert_eq!(acc_values.len(), new_values.len());
            for idx in 0..acc_values.len() {
                if acc_values[idx] != new_values[idx] {
                    acc_values[idx] = self
                        .ssa
                        .add_data(Dataflow::Phi(acc_block, [acc_values[idx], new_values[idx]]));
                }
            }
        }

        self.ssa
            .add_block(Block::Return(acc_block, acc_values.clone()));
        acc_values
    }

    fn interp_stmt<'b>(&mut self, stmt: &'a StmtAST, fsa: FSA<'b>) -> Option<FSA<'b>> {
        match stmt {
            StmtAST::Block { body } => self.interp_block(body, fsa),
            StmtAST::Assign { var, expr, .. } => Some(self.interp_assign(*var, expr, fsa)),
            StmtAST::Store { pointer, expr, .. } => Some(self.interp_store(pointer, expr, fsa)),
            StmtAST::Call {
                vars, callee, args, ..
            } => Some(self.interp_call(vars, *callee, args, fsa)),
            StmtAST::IfElse {
                cond,
                then_body,
                else_body,
                ..
            } => self.interp_ifelse(cond, then_body, else_body, fsa),
            StmtAST::While { cond, body, .. } => self.interp_while(cond, body, fsa),
            StmtAST::Return { exprs, .. } => {
                self.interp_return(exprs, fsa);
                None
            }
        }
    }

    fn interp_block<'b>(&mut self, body: &'a Vec<StmtAST>, mut fsa: FSA<'b>) -> Option<FSA<'b>> {
        for stmt in body {
            if let Some(new_fsa) = self.interp_stmt(stmt, fsa) {
                fsa = new_fsa
            } else {
                return None;
            }
        }
        Some(fsa)
    }

    fn interp_assign<'b>(&mut self, var: Symbol, expr: &'a ExprAST, mut fsa: FSA<'b>) -> FSA<'b> {
        let value = self.interp_expr(expr, &fsa);
        fsa.vars.insert(var, value);
        fsa
    }

    fn interp_store<'b>(
        &mut self,
        pointer: &'a ExprAST,
        expr: &'a ExprAST,
        mut fsa: FSA<'b>,
    ) -> FSA<'b> {
        let pointer = self.interp_expr(pointer, &fsa);
        let expr = self.interp_expr(expr, &fsa);
        let store = self.ssa.add_block(Block::Store(fsa.block, pointer, expr));
        fsa.block = store;
        fsa
    }

    fn interp_call<'b>(
        &mut self,
        vars: &'a Vec<Symbol>,
        callee: Symbol,
        args: &'a Vec<ExprAST>,
        mut fsa: FSA<'b>,
    ) -> FSA<'b> {
        let args: Vec<_> = args.iter().map(|arg| self.interp_expr(arg, &fsa)).collect();
        let callers = self.callgraph.callers.entry(callee).or_default();
        callers.insert(fsa.block, args.clone());

        let outputs = if callers.len() < 2 {
            self.callgraph.param_nodes.insert(callee, args.clone());
            fsa.block = self.ssa.add_block(Block::Call(fsa.block, callee, args.clone()));
            self.interp_func(&self.ast[&callee], args)
        } else {
            let param_nodes: Vec<_> = zip(&args, &self.callgraph.param_nodes[&callee])
                .enumerate()
                .map(|(idx, (new_arg, old_arg))| {
                    if *new_arg == *old_arg {
                        *new_arg
                    } else {
                        let param = self.ssa.intern_param(callee, idx);
                        self.ssa.add_data(Dataflow::Param(param))
                    }
                })
                .collect();
            let old_param_nodes = self
                .callgraph
                .param_nodes
                .insert(callee, param_nodes.clone());
            if old_param_nodes.as_ref() != Some(&param_nodes) {
                self.interp_func(&self.ast[&callee], param_nodes);
            }
            fsa.block = self.ssa.add_block(Block::Call(fsa.block, callee, args));
            (0..vars.len())
                .map(|idx| {
                    let call = self.ssa.intern_call(fsa.block, idx);
                    self.ssa.add_data(Dataflow::Call(call))
                })
                .collect()
        };
        for (var, output) in zip(vars, outputs.into_iter()) {
            fsa.vars.insert(*var, output);
        }
        fsa
    }

    fn interp_ifelse<'b>(
        &mut self,
        cond: &'a ExprAST,
        then_body: &'a StmtAST,
        else_body: &'a StmtAST,
        fsa: FSA<'b>,
    ) -> Option<FSA<'b>> {
        todo!()
    }

    fn interp_while<'b>(
        &mut self,
        cond: &'a ExprAST,
        body: &'a StmtAST,
        fsa: FSA<'b>,
    ) -> Option<FSA<'b>> {
        todo!()
    }

    fn interp_return<'b>(&mut self, exprs: &'a Vec<ExprAST>, fsa: FSA<'b>) {
        let values: Vec<_> = exprs
            .iter()
            .map(|expr| self.interp_expr(expr, &fsa))
            .collect();
        fsa.returned.borrow_mut().insert((fsa.block, values));
    }

    fn interp_expr<'b>(&mut self, expr: &'a ExprAST, fsa: &FSA<'b>) -> Id {
        match expr {
            ExprAST::Number(cons) => self.ssa.add_data(Dataflow::Constant(*cons)),
            ExprAST::Variable(var) => fsa.vars[var],
            ExprAST::Unary { op, input } => {
                let input = self.interp_expr(input, fsa);
                self.ssa.add_data(Dataflow::Unary(*op, input))
            }
            ExprAST::Binary { op, lhs, rhs } => {
                let lhs = self.interp_expr(lhs, fsa);
                let rhs = self.interp_expr(rhs, fsa);
                self.ssa.add_data(Dataflow::Binary(*op, [lhs, rhs]))
            }
            ExprAST::Load { pointer } => {
                let pointer = self.interp_expr(pointer, fsa);
                self.ssa.add_data(Dataflow::Load(fsa.block, pointer))
            }
        }
    }
}

fn are_all_same<D, I>(mut iter: I) -> Option<D>
where
    D: Eq,
    I: Iterator<Item = D>,
{
    let mut same = iter.next();
    for data in iter {
        if same != Some(data) {
            same = None;
            break;
        }
    }
    same
}

#[cfg(test)]
mod tests {
    use crate::imp::ai::create_ssa;
    use crate::imp::grammar::ProgramParser;

    #[test]
    fn translate1() {
        let program = r#"
fn main() { x <- foo(5); y <- foo(3); return x + y; }
fn foo(x) return x + 1;
"#;
        let mut counter = 0;
        let parsed = ProgramParser::new().parse(&mut counter, &program).unwrap();
        let ssa = create_ssa(&parsed);
        panic!("{}", ssa);
    }

    #[test]
    fn translate2() {
        let program = r#"
fn main() { x <- foo(7); return x; }
fn foo(x) { x <- foo(x + 1); return x; }
"#;
        let mut counter = 0;
        let parsed = ProgramParser::new().parse(&mut counter, &program).unwrap();
        let ssa = create_ssa(&parsed);
        panic!("{}", ssa);
    }
}
