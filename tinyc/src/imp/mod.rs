use lalrpop_util::lalrpop_mod;

pub mod ai;
pub mod ast;

lalrpop_mod!(pub grammar, "/imp/grammar.rs");
