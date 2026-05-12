use core::fmt::{Display, Formatter, Result};

use egg::Symbol;

use crate::nonssa::{Block, BlockId, Expr, NonSSAFunc, UnaryOp};

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

pub fn convert_to_cfg(func: ImpFunc) -> NonSSAFunc {
    let mut new_func = NonSSAFunc {
        name: func.name,
        params: func.params,
        cfg: vec![Block::Entry],
    };
    convert_to_cfg_helper(0, func.body, &mut new_func.cfg);
    new_func
}

fn convert_to_cfg_helper(pred: BlockId, stmt: ImpStmt, cfg: &mut Vec<Block>) -> Option<BlockId> {
    let add_block = |block, cfg: &mut Vec<Block>| {
        let id = cfg.len();
        cfg.push(block);
        id
    };
    match stmt {
        ImpStmt::Block { body } => {
            let mut id = pred;
            for stmt in body {
                id = convert_to_cfg_helper(id, stmt, cfg)?;
            }
            Some(id)
        }
        ImpStmt::Assign { var, expr } => Some(add_block(Block::Assign(pred, var, expr), cfg)),
        ImpStmt::Store { pointer, expr } => Some(add_block(Block::Store(pred, pointer, expr), cfg)),
        ImpStmt::Call { vars, callee, args } => {
            Some(add_block(Block::Call(pred, vars, callee, args), cfg))
        }
        ImpStmt::IfElse {
            cond,
            then_body,
            else_body,
        } => {
            let then_guard = add_block(Block::Guard(pred, cond.clone()), cfg);
            let else_guard = add_block(
                Block::Guard(
                    pred,
                    Expr::Unary {
                        op: UnaryOp::Not,
                        input: Box::new(cond),
                    },
                ),
                cfg,
            );
            let then_block = convert_to_cfg_helper(then_guard, *then_body, cfg);
            let else_block = convert_to_cfg_helper(else_guard, *else_body, cfg);
            match (then_block, else_block) {
                (Some(then_block), Some(else_block)) => {
                    Some(add_block(Block::Merge(then_block, else_block), cfg))
                }
                (None, block) | (block, None) => block,
            }
        }
        ImpStmt::While { cond, body } => {
            let header = add_block(Block::Entry, cfg);
            let then_guard = add_block(Block::Guard(header, cond.clone()), cfg);
            let else_guard = add_block(
                Block::Guard(
                    header,
                    Expr::Unary {
                        op: UnaryOp::Not,
                        input: Box::new(cond),
                    },
                ),
                cfg,
            );
            let body_block = convert_to_cfg_helper(then_guard, *body, cfg);
            cfg[header] = if let Some(body_block) = body_block {
                Block::Merge(pred, body_block)
            } else {
                Block::Guard(pred, Expr::Number(1))
            };
            Some(else_guard)
        }
        ImpStmt::Return { exprs } => {
            add_block(Block::Return(pred, exprs), cfg);
            None
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
