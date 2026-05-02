use core::fmt::{Display, Formatter, Result};

use derive_more::FromStr;

pub type Label = usize;
pub fn inc_label(counter: &mut Label) -> Label {
    let label = *counter;
    *counter += 1;
    label
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncAST {
    pub name: String,
    pub params: Vec<String>,
    pub body: StmtAST,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StmtAST {
    Block {
        body: Vec<StmtAST>,
    },
    Assign {
        var: String,
        expr: ExprAST,
        label: Label,
    },
    Store {
        pointer: ExprAST,
        expr: ExprAST,
        label: Label,
    },
    Call {
        vars: Vec<String>,
        callee: String,
        args: Vec<ExprAST>,
    },
    IfElse {
        cond: ExprAST,
        then_body: Box<StmtAST>,
        else_body: Box<StmtAST>,
        merge: Label,
    },
    While {
        cond: ExprAST,
        body: Box<StmtAST>,
        header: Label,
        exit: Label,
    },
    Return {
        exprs: Vec<ExprAST>,
        label: Label,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprAST {
    Number(i64),
    Variable(String),
    Unary {
        op: UnaryOp,
        input: Box<ExprAST>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<ExprAST>,
        rhs: Box<ExprAST>,
    },
    Load {
        pointer: Box<ExprAST>,
    },
}

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

impl Display for FuncAST {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "fn {}(", self.name)?;
        for idx in 0..self.params.len() {
            if idx != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", self.params[idx])?;
        }
        write!(f, ") {}", self.body)
    }
}

impl Display for StmtAST {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            StmtAST::Block { body } => {
                write!(f, "{{ ")?;
                for stmt in body {
                    stmt.fmt(f)?;
                    write!(f, " ")?;
                }
                write!(f, "}}")
            }
            StmtAST::Assign { var, expr, .. } => write!(f, "{} = {};", var, expr),
            StmtAST::Store { pointer, expr, .. } => write!(f, "*{} = {};", pointer, expr),
            StmtAST::Call { vars, callee, args } => {
                for idx in 0..vars.len() {
                    if idx != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", vars[idx])?;
                }
                write!(f, " <- {}(", callee)?;
                for idx in 0..args.len() {
                    if idx != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", args[idx])?;
                }
                write!(f, ");")
            }
            StmtAST::IfElse {
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
            StmtAST::While { cond, body, .. } => write!(f, "while {} {{ {} }}", cond, body),
            StmtAST::Return { exprs: expr, .. } => {
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

impl Display for ExprAST {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            ExprAST::Number(num) => num.fmt(f),
            ExprAST::Variable(name) => name.fmt(f),
            ExprAST::Unary { op, input } => write!(f, "{}{}", op, input),
            ExprAST::Binary { op, lhs, rhs } => write!(f, "({} {} {})", lhs, op, rhs),
            ExprAST::Load { pointer } => write!(f, "*{}", pointer),
        }
    }
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            UnaryOp::Neg => "-".fmt(f),
            UnaryOp::Not => "!".fmt(f),
        }
    }
}

impl Display for BinaryOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            BinaryOp::Add => "+".fmt(f),
            BinaryOp::Sub => "-".fmt(f),
            BinaryOp::Mul => "*".fmt(f),
            BinaryOp::EE => "==".fmt(f),
            BinaryOp::NE => "!=".fmt(f),
            BinaryOp::LT => "<".fmt(f),
            BinaryOp::LE => "<=".fmt(f),
            BinaryOp::GT => ">".fmt(f),
            BinaryOp::GE => ">=".fmt(f),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::grammar::ProgramParser;

    #[test]
    fn parse1() {
        let program = r#"
fn test1(x) return x;
fn test2(y) { *y = 3; y <- test1(y); return y, *y + 1; }
"#;
        let mut counter = 0;
        let parsed = ProgramParser::new().parse(&mut counter, &program).unwrap();
        assert_eq!(format!("{}", parsed["test1"]), "fn test1(x) return x;");
        assert_eq!(
            format!("{}", parsed["test2"]),
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
            format!("{}", parsed["test"]),
            "fn test(x, y) { while (x < 7) { { x = (x + 1); } } if (y < x) { { return y; } } else { { } } return (x + 9); }"
        );
    }
}
