use core::fmt::{Display, Formatter, Result};
use core::iter::zip;
use core::mem::take;

use egg::{Id, Symbol};
use rustc_hash::FxHashMap;

use crate::analysis::interval::Interval;
use crate::nonssa::{Expr, UnaryOp};
use crate::ssa::{Dataflow, SSABlock, SSABlockId, SSAProgram};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImpFunc {
    pub name: Symbol,
    pub params: Vec<Symbol>,
    pub body: ImpStmt,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImpStmt {
    Block {
        body: Vec<ImpStmt>,
    },
    Assign {
        var: Symbol,
        expr: Expr,
    },
    Store {
        pointer: Expr,
        expr: Expr,
    },
    Call {
        vars: Vec<Symbol>,
        callee: Symbol,
        args: Vec<Expr>,
    },
    IfElse {
        cond: Expr,
        then_body: Box<ImpStmt>,
        else_body: Box<ImpStmt>,
    },
    While {
        cond: Expr,
        body: Box<ImpStmt>,
    },
    Return {
        exprs: Vec<Expr>,
    },
}

pub fn naive_ssa_translate(program: &FxHashMap<Symbol, ImpFunc>) -> SSAProgram {
    let mut ssa = SSAProgram::default();
    for (name, func) in program {
        let vars = func
            .params
            .iter()
            .enumerate()
            .map(|(idx, param)| {
                let param_id = ssa.intern_param(*name, idx, Interval::top());
                let id = ssa.add_data(Dataflow::Param(param_id));
                (*param, id)
            })
            .collect();
        let entry = ssa.add_block(SSABlock::Entry);
        ssa.entries.insert(*name, entry);
        let mut context = FuncSSAContext {
            ssa,
            vars,
            block: Some(entry),
            returns: FxHashMap::default(),
        };
        context.visit_stmt(&func.body);

        ssa = context.ssa;
        let mut returns = context.returns.drain();
        let (mut block, mut ids) = returns.next().unwrap();
        for (other_block, other_ids) in returns {
            block = ssa.add_block(SSABlock::Merge(block, other_block));
            for (id, other_id) in zip(ids.iter_mut(), other_ids) {
                if *id != other_id {
                    *id = ssa.add_data(Dataflow::Phi(block, [*id, other_id]));
                }
            }
        }
        let return_block = ssa.add_block(SSABlock::Return(block, ids));
        ssa.exits.insert(*name, return_block);
    }

    ssa
}

struct FuncSSAContext {
    ssa: SSAProgram,
    vars: FxHashMap<Symbol, Id>,
    block: Option<SSABlockId>,
    returns: FxHashMap<SSABlockId, Vec<Id>>,
}

impl FuncSSAContext {
    fn visit_stmt(&mut self, stmt: &ImpStmt) {
        match stmt {
            ImpStmt::Block { body } => self.visit_block(body),
            ImpStmt::Assign { var, expr } => self.visit_assign(*var, expr),
            ImpStmt::Store { pointer, expr } => self.visit_store(pointer, expr),
            ImpStmt::Call { vars, callee, args } => self.visit_call(vars, *callee, args),
            ImpStmt::IfElse {
                cond,
                then_body,
                else_body,
            } => self.visit_ifelse(cond, then_body, else_body),
            ImpStmt::While { cond, body } => self.visit_while(cond, body),
            ImpStmt::Return { exprs } => self.visit_return(exprs),
        }
    }

    fn visit_block(&mut self, body: &Vec<ImpStmt>) {
        for stmt in body {
            self.visit_stmt(stmt);
            if self.block.is_none() {
                return;
            }
        }
    }

    fn visit_assign(&mut self, var: Symbol, expr: &Expr) {
        let id = self.add_expr(expr);
        self.vars.insert(var, id);
    }

    fn visit_store(&mut self, pointer: &Expr, expr: &Expr) {
        let pointer = self.add_expr(pointer);
        let expr = self.add_expr(expr);
        let store = self
            .ssa
            .add_block(SSABlock::Store(self.block.unwrap(), pointer, expr));
        self.block = Some(store);
    }

    fn visit_call(&mut self, vars: &Vec<Symbol>, callee: Symbol, args: &Vec<Expr>) {
        let ids = args.iter().map(|expr| self.add_expr(expr)).collect();
        let call = self
            .ssa
            .add_block(SSABlock::Call(self.block.unwrap(), callee, ids));
        self.block = Some(call);
        for (idx, var) in vars.iter().enumerate() {
            let call = self.ssa.intern_call(call, idx, Interval::top());
            let call = self.ssa.add_data(Dataflow::Call(call));
            self.vars.insert(*var, call);
        }
    }

    fn visit_ifelse(&mut self, cond: &Expr, then_body: &ImpStmt, else_body: &ImpStmt) {
        let then_cond = self.add_expr(cond);
        let else_cond = self.ssa.add_data(Dataflow::Unary(UnaryOp::Not, then_cond));
        let then_guard = self
            .ssa
            .add_block(SSABlock::Guard(self.block.unwrap(), then_cond));
        let else_guard = self
            .ssa
            .add_block(SSABlock::Guard(self.block.unwrap(), else_cond));
        let before_vars = self.vars.clone();
        self.block = Some(then_guard);
        self.visit_stmt(then_body);
        let then_vars = take(&mut self.vars);
        let then_block = self.block;
        self.vars = before_vars;
        self.block = Some(else_guard);
        self.visit_stmt(else_body);
        let else_vars = take(&mut self.vars);
        let else_block = self.block;
        match (then_block, else_block) {
            (Some(then_block), Some(else_block)) => {
                let merge = self.ssa.add_block(SSABlock::Merge(then_block, else_block));
                for (var, then_id) in then_vars {
                    if let Some(else_id) = else_vars.get(&var).copied() {
                        let phi = self.ssa.add_data(Dataflow::Phi(merge, [then_id, else_id]));
                        self.vars.insert(var, phi);
                    }
                }
                self.block = Some(merge);
            }
            (None, block) => {
                self.block = block;
                self.vars = else_vars;
            }
            (block, None) => {
                self.block = block;
                self.vars = then_vars;
            }
        }
    }

    fn visit_while(&mut self, cond: &Expr, body: &ImpStmt) {
        let init_vars = self.vars.clone();
        let before_header = self.block.unwrap();
        let header = self.ssa.add_block(SSABlock::Entry);
        for (idx, (_, id)) in self.vars.iter_mut().enumerate() {
            let knot = self.ssa.intern_knot(header, idx.into(), Interval::top());
            let knot = self.ssa.add_data(Dataflow::Knot(knot));
            *id = knot;
        }
        self.block = Some(header);
        let then_cond = self.add_expr(cond);
        let else_cond = self.ssa.add_data(Dataflow::Unary(UnaryOp::Not, then_cond));
        let then_guard = self.ssa.add_block(SSABlock::Guard(header, then_cond));
        let else_guard = self.ssa.add_block(SSABlock::Guard(header, else_cond));
        self.block = Some(then_guard);
        self.visit_stmt(body);
        if let Some(iter_block) = self.block {
            self.ssa
                .set_block(SSABlock::Merge(before_header, iter_block), header);
            for (idx, (var, init)) in init_vars.into_iter().enumerate() {
                let iter = self.vars[&var];
                let phi = self.ssa.add_data(Dataflow::Phi(header, [init, iter]));
                let knot = self.ssa.intern_knot(header, idx.into(), Interval::top());
                let knot = self.ssa.add_data(Dataflow::Knot(knot));
                self.ssa.dfg.union(phi, knot);
                self.ssa.dfg[phi].nodes.retain(|node| {
                    if let Dataflow::Knot(_) = node {
                        false
                    } else {
                        true
                    }
                });
            }
            self.block = Some(else_guard);
        } else {
            self.vars = init_vars.clone();
            self.block = Some(before_header);
            let then_cond = self.add_expr(cond);
            let else_cond = self.ssa.add_data(Dataflow::Unary(UnaryOp::Not, then_cond));
            let then_guard = self
                .ssa
                .add_block(SSABlock::Guard(before_header, then_cond));
            let else_guard = self
                .ssa
                .add_block(SSABlock::Guard(before_header, else_cond));
            self.block = Some(then_guard);
            self.visit_stmt(body);
            assert!(self.block.is_none());
            self.vars = init_vars;
            self.block = Some(else_guard);
        }
    }

    fn visit_return(&mut self, exprs: &Vec<Expr>) {
        let ids = exprs.iter().map(|expr| self.add_expr(expr)).collect();
        self.returns.insert(self.block.unwrap(), ids);
        self.block = None;
    }

    fn add_expr(&mut self, expr: &Expr) -> Id {
        match expr {
            Expr::Number(cons) => self.ssa.add_data(Dataflow::Constant(*cons)),
            Expr::Variable(var) => self.vars[var],
            Expr::Unary { op, input } => {
                let input = self.add_expr(input);
                self.ssa.add_data(Dataflow::Unary(*op, input))
            }
            Expr::Binary { op, lhs, rhs } => {
                let lhs = self.add_expr(lhs);
                let rhs = self.add_expr(rhs);
                self.ssa.add_data(Dataflow::Binary(*op, [lhs, rhs]))
            }
            Expr::Load { pointer } => {
                let pointer = self.add_expr(pointer);
                self.ssa
                    .add_data(Dataflow::Load(self.block.unwrap(), pointer))
            }
        }
    }
}

impl Display for ImpFunc {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "fn {}(", self.name.as_str())?;
        for idx in 0..self.params.len() {
            if idx != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", self.params[idx].as_str())?;
        }
        write!(f, ") {}", self.body)
    }
}

impl Display for ImpStmt {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            ImpStmt::Block { body } => {
                write!(f, "{{ ")?;
                for stmt in body {
                    stmt.fmt(f)?;
                    write!(f, " ")?;
                }
                write!(f, "}}")
            }
            ImpStmt::Assign { var, expr, .. } => write!(f, "{} = {};", var.as_str(), expr),
            ImpStmt::Store { pointer, expr, .. } => write!(f, "*{} = {};", pointer, expr),
            ImpStmt::Call {
                vars, callee, args, ..
            } => {
                for idx in 0..vars.len() {
                    if idx != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", vars[idx].as_str())?;
                }
                write!(f, " <- {}(", callee.as_str())?;
                for idx in 0..args.len() {
                    if idx != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", args[idx])?;
                }
                write!(f, ");")
            }
            ImpStmt::IfElse {
                cond,
                then_body,
                else_body,
                ..
            } => {
                write!(
                    f,
                    "if {} {{ {} }} else {{ {} }}",
                    cond, then_body, else_body
                )
            }
            ImpStmt::While { cond, body, .. } => write!(f, "while {} {{ {} }}", cond, body),
            ImpStmt::Return { exprs: expr, .. } => {
                write!(f, "return ")?;
                for idx in 0..expr.len() {
                    if idx != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", expr[idx])?;
                }
                write!(f, ";")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use egg::Symbol;

    use crate::imp::grammar::ProgramParser;

    #[test]
    fn parse1() {
        let program = r#"
fn test1(x) return x;
fn test2(y) { *y = 3; y <- test1(y); return y, *y + 1; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        assert_eq!(
            format!("{}", parsed[&Symbol::from("test1")]),
            "fn test1(x) return x;"
        );
        assert_eq!(
            format!("{}", parsed[&Symbol::from("test2")]),
            "fn test2(y) { *y = 3; y <- test1(y); return y, (*y + 1); }"
        );
    }

    #[test]
    fn parse2() {
        let program = r#"
fn test(x, y) { while x < 7 { x = x + 1; } if y < x { return y; } return x + 9; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        assert_eq!(
            format!("{}", parsed[&Symbol::from("test")]),
            "fn test(x, y) { while (x < 7) { { x = (x + 1); } } if (y < x) { { return y; } } else { { } } return (x + 9); }"
        );
    }
}
