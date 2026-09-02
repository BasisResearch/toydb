//! Parses raw SQL strings into a structured Abstract Syntax Tree.

pub mod ast;
#[cfg(test)]
pub(crate) mod differential;
pub mod float_trust;
mod lexer;
pub mod parse_error;
mod parser;
mod printer;
mod stream;
pub mod unicode_trust;
pub mod verified;
pub mod verified_control;
pub mod verified_expression;
pub mod verified_function_list;
pub mod verified_integer;
pub mod verified_lexer;
pub mod verified_lists;
pub mod verified_minparen;
pub mod verified_precedence;
pub mod verified_production;
pub mod verified_roundtrip;
pub mod verified_simple_statement;
pub mod verified_statements;
pub mod verified_stmt;
pub mod verified_stmt_prec;

pub use lexer::{Keyword, Lexer, Token, is_ident};
pub use parser::Parser;
pub use printer::{print_expr, print_statement};
