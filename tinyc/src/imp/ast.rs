use core::fmt::{Display, Formatter, Result};

use egg::Symbol;

use crate::nonssa::Expr;

pub type LabelId = usize;
pub fn inc_label(counter: &mut LabelId) -> LabelId {
    let label = *counter;
    *counter += 1;
    label
}

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
        label: LabelId,
    },
    Store {
        pointer: Expr,
        expr: Expr,
        label: LabelId,
    },
    Call {
        vars: Vec<Symbol>,
        callee: Symbol,
        args: Vec<Expr>,
        label: LabelId,
    },
    IfElse {
        cond: Expr,
        then_body: Box<ImpStmt>,
        else_body: Box<ImpStmt>,
        merge: LabelId,
    },
    While {
        cond: Expr,
        body: Box<ImpStmt>,
        header: LabelId,
        exit: LabelId,
    },
    Return {
        exprs: Vec<Expr>,
        label: LabelId,
    },
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
        let mut counter = 0;
        let parsed = ProgramParser::new().parse(&mut counter, &program).unwrap();
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
        let mut counter = 0;
        let parsed = ProgramParser::new().parse(&mut counter, &program).unwrap();
        assert_eq!(
            format!("{}", parsed[&Symbol::from("test")]),
            "fn test(x, y) { while (x < 7) { { x = (x + 1); } } if (y < x) { { return y; } } else { { } } return (x + 9); }"
        );
    }
}
