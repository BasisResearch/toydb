//! Structural mirror of the expression grammar: `SExpr` and `view_expr`.
//!
//! `SExpr` is the `Seq`-based mirror of the whole `ast::Expression` grammar
//! (operator children are `Box<SExpr>`, function arguments are `Seq<SExpr>`).
//! It exists because `ast::Expression::Function` carries a `Vec<Expression>`,
//! which is opaque in the spec logic: Verus has no spec-level `Vec` constructor
//! and `Vec` equality is not view-determined, so a spec-level parser cannot
//! build or compare a `Function` node. Every mirror component is
//! spec-constructible and extensional, so theorems about `SExpr` close with a
//! real `==`, and the exec parser is verified against the mirror at the level of
//! the structural view `view_expr: ast::Expression -> SExpr`.
//!
//! What lives here is the mirror *vocabulary* — the type, the view, the
//! printable domain (`printable_se`), the fuel measure (`sdepth`), the token
//! boundary (`boundary`), and the small exec helpers the parser shares
//! (`parse_literal_exec`, `build_unary`, `build_binary`, `print_lit_exec`).
//!
//! It also carries `sprint` / `sprint_args`, the fully parenthesized canonical
//! printer. That printer has no executable twin — it is the *domain
//! description* for `verified_precedence::lemma_prec`, which proves the
//! production parser inverts it. Fully parenthesized and minimally
//! parenthesized prints are disjoint token classes for every non-atomic
//! expression, so `lemma_prec` and `verified_minparen::min_roundtrip` give the
//! parser two independent proved-correct input classes; neither subsumes the
//! other.
//!
//! The *mirror parser* that used to sit beside `sprint` (`sparse`,
//! `sparse_operator`, `sparse_args`, with the `mirror_roundtrip` /
//! `mirror_injective` corollaries) is gone: it was a second parser nothing
//! executed, and `lemma_prec` states the same round trip over the production
//! parser instead. The injectivity those corollaries carried is now
//! `verified_minparen::min_print_injective` and its statement-level counterpart
//! `verified_minparen_stmt::stmt_min_print_injective`.
//!
//! Trust surface is unchanged: the only axioms are the `float_trust` boundary
//! reused through `literal_views` / `parse_literal_views`.

// scaffolding.
#![allow(dead_code, unused_variables)]
// Proof/verification scaffolding, not idiomatic library code: exempt from the
// crate's `warn(clippy::all)` so proof-shaped constructs don't trip `-D warnings`.
#![allow(clippy::all)]

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use vstd::prelude::*;

// Types are real items (visible to plain rustc); the spec fns these modules
// export are erased from non-Verus builds, so they are referenced by full path
// rather than imported by name.
#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::verified_expression::{BinaryTag, UnaryTag};
#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::verified_production::TokenView;
#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::{Keyword, ast, float_trust, verified_expression, verified_production};

verus! {

// ---- Seq-based mirror of the full expression grammar -----------------------

/// The literal carried by an `IS` operator: the printer only emits `IS NULL`
/// and `IS NAN`, so the mirror records exactly that choice.
#[derive(PartialEq, Eq, Structural)]
pub enum IsLit {
    Null,
    NaN,
}

/// Mirror of `ast::Expression` whose function arguments are a `Seq`, not a
/// `Vec`. Every field is spec-constructible and extensional, so `SExpr`
/// equality is structural and the roundtrip below closes with `==`.
pub enum SExpr {
    All,
    Column(Option<String>, String),
    Literal(ast::Literal),
    Unary(UnaryTag, Box<SExpr>),
    Factorial(Box<SExpr>),
    Is(Box<SExpr>, IsLit),
    Binary(BinaryTag, Box<SExpr>, Box<SExpr>),
    Function(String, Seq<SExpr>),
}

/// Structural view of a production expression as a mirror expression: identical
/// everywhere except that the function argument `Vec` becomes a `Seq`.
pub open spec fn view_expr(e: ast::Expression) -> SExpr
    decreases e,
{
    match e {
        ast::Expression::All => SExpr::All,
        ast::Expression::Column(table, column) => SExpr::Column(table, column),
        ast::Expression::Literal(literal) => SExpr::Literal(literal),
        ast::Expression::Function(name, arguments) =>
            SExpr::Function(name, view_args(arguments@)),
        ast::Expression::Operator(operator) => match operator {
            ast::Operator::Not(inner) => SExpr::Unary(UnaryTag::Not, Box::new(view_expr(*inner))),
            ast::Operator::Identity(inner) =>
                SExpr::Unary(UnaryTag::Identity, Box::new(view_expr(*inner))),
            ast::Operator::Negate(inner) =>
                SExpr::Unary(UnaryTag::Negate, Box::new(view_expr(*inner))),
            ast::Operator::Factorial(inner) => SExpr::Factorial(Box::new(view_expr(*inner))),
            ast::Operator::Is(inner, literal) => SExpr::Is(
                Box::new(view_expr(*inner)),
                match literal {
                    ast::Literal::Null => IsLit::Null,
                    _ => IsLit::NaN,
                },
            ),
            ast::Operator::And(left, right) =>
                SExpr::Binary(BinaryTag::And, Box::new(view_expr(*left)), Box::new(view_expr(*right))),
            ast::Operator::Or(left, right) =>
                SExpr::Binary(BinaryTag::Or, Box::new(view_expr(*left)), Box::new(view_expr(*right))),
            ast::Operator::Equal(left, right) =>
                SExpr::Binary(BinaryTag::Equal, Box::new(view_expr(*left)), Box::new(view_expr(*right))),
            ast::Operator::GreaterThan(left, right) =>
                SExpr::Binary(BinaryTag::GreaterThan, Box::new(view_expr(*left)), Box::new(view_expr(*right))),
            ast::Operator::GreaterThanOrEqual(left, right) =>
                SExpr::Binary(BinaryTag::GreaterThanOrEqual, Box::new(view_expr(*left)), Box::new(view_expr(*right))),
            ast::Operator::LessThan(left, right) =>
                SExpr::Binary(BinaryTag::LessThan, Box::new(view_expr(*left)), Box::new(view_expr(*right))),
            ast::Operator::LessThanOrEqual(left, right) =>
                SExpr::Binary(BinaryTag::LessThanOrEqual, Box::new(view_expr(*left)), Box::new(view_expr(*right))),
            ast::Operator::NotEqual(left, right) =>
                SExpr::Binary(BinaryTag::NotEqual, Box::new(view_expr(*left)), Box::new(view_expr(*right))),
            ast::Operator::Add(left, right) =>
                SExpr::Binary(BinaryTag::Add, Box::new(view_expr(*left)), Box::new(view_expr(*right))),
            ast::Operator::Divide(left, right) =>
                SExpr::Binary(BinaryTag::Divide, Box::new(view_expr(*left)), Box::new(view_expr(*right))),
            ast::Operator::Exponentiate(left, right) =>
                SExpr::Binary(BinaryTag::Exponentiate, Box::new(view_expr(*left)), Box::new(view_expr(*right))),
            ast::Operator::Multiply(left, right) =>
                SExpr::Binary(BinaryTag::Multiply, Box::new(view_expr(*left)), Box::new(view_expr(*right))),
            ast::Operator::Remainder(left, right) =>
                SExpr::Binary(BinaryTag::Remainder, Box::new(view_expr(*left)), Box::new(view_expr(*right))),
            ast::Operator::Subtract(left, right) =>
                SExpr::Binary(BinaryTag::Subtract, Box::new(view_expr(*left)), Box::new(view_expr(*right))),
            ast::Operator::Like(left, right) =>
                SExpr::Binary(BinaryTag::Like, Box::new(view_expr(*left)), Box::new(view_expr(*right))),
        },
    }
}

pub open spec fn view_args(args: Seq<ast::Expression>) -> Seq<SExpr>
    decreases args,
{
    if args.len() == 0 {
        Seq::empty()
    } else {
        seq![view_expr(args[0])] + view_args(args.drop_first())
    }
}

// ---- printer domain --------------------------------------------------------

/// Whether the canonical printer can encode this mirror expression. Function
/// arguments use the structural `all_printable_se` rather than a `forall` so
/// that printability threads through the argument recursion definitionally.
pub open spec fn printable_se(e: SExpr) -> bool
    decreases e,
{
    match e {
        SExpr::All => true,
        SExpr::Column(_, _) => true,
        SExpr::Literal(literal) => verified_production::printable_literal(literal),
        SExpr::Unary(_, inner) => printable_se(*inner),
        SExpr::Factorial(inner) => printable_se(*inner),
        SExpr::Is(inner, _) => printable_se(*inner),
        SExpr::Binary(_, left, right) => printable_se(*left) && printable_se(*right),
        SExpr::Function(_, args) => all_printable_se(args),
    }
}

pub open spec fn all_printable_se(args: Seq<SExpr>) -> bool
    decreases args,
{
    if args.len() == 0 {
        true
    } else {
        printable_se(args[0]) && all_printable_se(args.drop_first())
    }
}

// ---- canonical token encoding for tags -------------------------------------

pub open spec fn unary_tok(tag: UnaryTag) -> TokenView {
    match tag {
        UnaryTag::Identity => TokenView::Plus,
        UnaryTag::Negate => TokenView::Minus,
        UnaryTag::Not => TokenView::Keyword(Keyword::Not),
    }
}

pub open spec fn binary_tok(tag: BinaryTag) -> TokenView {
    match tag {
        BinaryTag::And => TokenView::Keyword(Keyword::And),
        BinaryTag::Or => TokenView::Keyword(Keyword::Or),
        BinaryTag::Equal => TokenView::Equal,
        BinaryTag::GreaterThan => TokenView::GreaterThan,
        BinaryTag::GreaterThanOrEqual => TokenView::GreaterThanOrEqual,
        BinaryTag::LessThan => TokenView::LessThan,
        BinaryTag::LessThanOrEqual => TokenView::LessThanOrEqual,
        BinaryTag::NotEqual => TokenView::NotEqual,
        BinaryTag::Add => TokenView::Plus,
        BinaryTag::Divide => TokenView::Slash,
        BinaryTag::Exponentiate => TokenView::Caret,
        BinaryTag::Multiply => TokenView::Asterisk,
        BinaryTag::Remainder => TokenView::Percent,
        BinaryTag::Subtract => TokenView::Minus,
        BinaryTag::Like => TokenView::Keyword(Keyword::Like),
    }
}

pub open spec fn islit_tok(lit: IsLit) -> TokenView {
    match lit {
        IsLit::Null => TokenView::Keyword(Keyword::Null),
        IsLit::NaN => TokenView::Keyword(Keyword::NaN),
    }
}

// ---- canonical printer over the mirror -------------------------------------

// ---- fuel measure ----------------------------------------------------------

/// The fully parenthesized canonical printer: every operator node is wrapped in
/// parentheses, so the token stream determines the tree without consulting any
/// precedence table.
///
/// It has no executable twin — it is the *domain description* for
/// `verified_precedence::lemma_prec`, which proves the production parser
/// (`sparse_prec`) inverts it. That makes fully parenthesized SQL a second,
/// disjoint input class on which the production parser is proved correct,
/// alongside the minimal-parenthesization class covered by
/// `verified_minparen::min_roundtrip`.
pub open spec fn sprint(e: SExpr) -> Seq<TokenView>
    decreases e,
{
    match e {
        SExpr::All => seq![TokenView::Asterisk],
        SExpr::Column(None, column) => seq![TokenView::Ident(column)],
        SExpr::Column(Some(table), column) =>
            seq![TokenView::Ident(table), TokenView::Period, TokenView::Ident(column)],
        SExpr::Literal(literal) => verified_production::literal_views(literal).unwrap(),
        SExpr::Unary(tag, inner) =>
            seq![TokenView::OpenParen, unary_tok(tag)] + sprint(*inner) + seq![TokenView::CloseParen],
        SExpr::Factorial(inner) =>
            seq![TokenView::OpenParen] + sprint(*inner)
                + seq![TokenView::Exclamation, TokenView::CloseParen],
        SExpr::Is(inner, lit) =>
            seq![TokenView::OpenParen] + sprint(*inner)
                + seq![TokenView::Keyword(Keyword::Is), islit_tok(lit), TokenView::CloseParen],
        SExpr::Binary(tag, left, right) =>
            seq![TokenView::OpenParen] + sprint(*left) + seq![binary_tok(tag)]
                + sprint(*right) + seq![TokenView::CloseParen],
        SExpr::Function(name, args) =>
            seq![TokenView::Ident(name), TokenView::OpenParen] + sprint_args(args)
                + seq![TokenView::CloseParen],
    }
}
pub open spec fn sprint_args(args: Seq<SExpr>) -> Seq<TokenView>
    decreases args,
{
    if args.len() == 0 {
        Seq::empty()
    } else if args.len() == 1 {
        sprint(args[0])
    } else {
        sprint(args[0]) + seq![TokenView::Comma] + sprint_args(args.drop_first())
    }
}

/// The fully parenthesized print starts with a token that can only begin an
/// atom: never a prefix operator, never a close paren. This is what lets
/// `lemma_prec` pin the parser's first dispatch.
pub proof fn sprint_head(e: SExpr)
    requires printable_se(e),
    ensures
        sprint(e).len() > 0,
        verified_expression::prefix_operator(sprint(e)[0]) is None,
        sprint(e)[0] != TokenView::CloseParen,
{
    reveal(printable_se);
    match e {
        SExpr::All => {
            assert(sprint(e)[0] == TokenView::Asterisk);
        },
        SExpr::Column(table, column) => match table {
            Some(t) => { assert(sprint(e)[0] == TokenView::Ident(t)); },
            None => { assert(sprint(e)[0] == TokenView::Ident(column)); },
        },
        SExpr::Literal(l) => {
            reveal(verified_production::literal_views);
            assert(sprint(e) == verified_production::literal_views(l).unwrap());
            match l {
                ast::Literal::Null => {},
                ast::Literal::Boolean(_) => {},
                ast::Literal::Integer(_) => {},
                ast::Literal::Float(_) => {},
                ast::Literal::String(_) => {},
            }
        },
        SExpr::Unary(_, _) => { assert(sprint(e)[0] == TokenView::OpenParen); },
        SExpr::Factorial(_) => { assert(sprint(e)[0] == TokenView::OpenParen); },
        SExpr::Is(_, _) => { assert(sprint(e)[0] == TokenView::OpenParen); },
        SExpr::Binary(_, _, _) => { assert(sprint(e)[0] == TokenView::OpenParen); },
        SExpr::Function(name, _) => { assert(sprint(e)[0] == TokenView::Ident(name)); },
    }
}

pub open spec fn sdepth(e: SExpr) -> nat
    decreases e,
{
    match e {
        SExpr::All => 1,
        SExpr::Column(_, _) => 1,
        SExpr::Literal(_) => 1,
        SExpr::Unary(_, inner) => 1 + sdepth(*inner),
        SExpr::Factorial(inner) => 1 + sdepth(*inner),
        SExpr::Is(inner, _) => 1 + sdepth(*inner),
        SExpr::Binary(_, left, right) => {
            let l = sdepth(*left);
            let r = sdepth(*right);
            1 + if l >= r { l } else { r }
        },
        SExpr::Function(_, args) => 1 + slist_depth(args),
    }
}

pub open spec fn slist_depth(args: Seq<SExpr>) -> nat
    decreases args,
{
    if args.len() == 0 {
        1
    } else {
        let d = sdepth(args[0]);
        let rest = slist_depth(args.drop_first());
        1 + (if d >= rest { d } else { rest })
    }
}

// ---- boundary predicate ----------------------------------------------------

/// A trailing token stream is a safe boundary for a bare atom when it opens with
/// neither `.` (else a bare column is re-read as qualified) nor `(` (else it is
/// re-read as a function call).
pub open spec fn boundary(tail: Seq<TokenView>) -> bool {
    tail.len() == 0 || (tail[0] != TokenView::Period && tail[0] != TokenView::OpenParen)
}

// ---- mirror parser ---------------------------------------------------------

// ---- tag <-> token inverses ------------------------------------------------

pub proof fn unary_tok_prefix(tag: UnaryTag)
    ensures verified_expression::prefix_operator(unary_tok(tag)) == Some(tag),
{
    match tag {
        UnaryTag::Identity => {},
        UnaryTag::Negate => {},
        UnaryTag::Not => {},
    }
}

pub proof fn binary_tok_roundtrip(tag: BinaryTag)
    ensures
        verified_expression::binary_from_token(binary_tok(tag)) == Some(tag),
        binary_tok(tag) != TokenView::Exclamation,
        binary_tok(tag) != TokenView::Keyword(Keyword::Is),
        binary_tok(tag) != TokenView::CloseParen,
        binary_tok(tag) != TokenView::Period,
        binary_tok(tag) != TokenView::OpenParen,
{
    match tag {
        BinaryTag::And => {},
        BinaryTag::Or => {},
        BinaryTag::Equal => {},
        BinaryTag::GreaterThan => {},
        BinaryTag::GreaterThanOrEqual => {},
        BinaryTag::LessThan => {},
        BinaryTag::LessThanOrEqual => {},
        BinaryTag::NotEqual => {},
        BinaryTag::Add => {},
        BinaryTag::Divide => {},
        BinaryTag::Exponentiate => {},
        BinaryTag::Multiply => {},
        BinaryTag::Remainder => {},
        BinaryTag::Subtract => {},
        BinaryTag::Like => {},
    }
}

// ---- printer head facts ----------------------------------------------------

// ---- fuel bound: sdepth <= printed length ----------------------------------

pub proof fn sdepth_positive(e: SExpr)
    ensures sdepth(e) >= 1,
{
}

// ---- headline: the mirror roundtrip over the full grammar -------------------

// ============================================================================
// E3: executable parser over real `ast::Expression`, refining `sparse`.
//
// The exec parser reads a `Vec<Token>` (production tokens) by an explicit
// cursor `pos` and builds real `ast::Expression` values with `Box` children
// and `Vec` arguments. Its ghost input is `token_views` of the remaining
// tokens; it is verified to refine `sparse` at the `view_expr` level.
// ============================================================================

/// `token_views` preserves length.
pub proof fn token_views_len(s: Seq<super::Token>)
    ensures verified_production::token_views(s).len() == s.len(),
    decreases s.len(),
{
    reveal_with_fuel(verified_production::token_views, 1);
    if s.len() > 0 {
        token_views_len(s.drop_first());
    }
}

/// The view of a suffix: its head is the view of the token at `pos`, and its
/// tail is the view of the next suffix. This is the single bridge the exec
/// parser uses to step the cursor.
pub proof fn token_views_suffix(s: Seq<super::Token>, pos: int)
    requires 0 <= pos < s.len(),
    ensures
        verified_production::token_views(s.subrange(pos, s.len() as int)).len() > 0,
        verified_production::token_views(s.subrange(pos, s.len() as int))[0]
            == verified_production::token_view(s[pos]),
        verified_production::token_views(s.subrange(pos, s.len() as int)).drop_first()
            == verified_production::token_views(s.subrange(pos + 1, s.len() as int)),
{
    let sub = s.subrange(pos, s.len() as int);
    reveal_with_fuel(verified_production::token_views, 1);
    token_views_len(sub);
    assert(sub[0] == s[pos]);
    assert(sub.drop_first() =~= s.subrange(pos + 1, s.len() as int));
}

/// Exec digit check refining `verified_integer::all_digits`.
pub fn all_digits_exec(bytes: &[u8]) -> (r: bool)
    ensures r == super::verified_integer::all_digits(bytes@),
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        true
    } else {
        let b = bytes[bytes.len() - 1];
        if 48u8 <= b && b <= 57u8 {
            let prefix = vstd::slice::slice_subrange(bytes, 0, bytes.len() - 1);
            assert(prefix@ =~= bytes@.drop_last());
            all_digits_exec(prefix)
        } else {
            false
        }
    }
}

/// Exec single-token literal parser refining `parse_literal_views` on the
/// one-element view sequence.
pub fn parse_literal_exec(tok: &super::Token) -> (r: Option<ast::Literal>)
    ensures r == verified_production::parse_literal_views(
        seq![verified_production::token_view(*tok)],
    ),
{
    reveal(verified_production::parse_literal_views);
    let ghost tv = seq![verified_production::token_view(*tok)];
    match tok {
        super::Token::Keyword(Keyword::Null) => Some(ast::Literal::Null),
        super::Token::Keyword(Keyword::True) => Some(ast::Literal::Boolean(true)),
        super::Token::Keyword(Keyword::False) => Some(ast::Literal::Boolean(false)),
        super::Token::Number(bytes) => {
            if all_digits_exec(bytes.as_slice()) {
                match super::verified_integer::parse_i64(bytes.as_slice()) {
                    Some(value) => Some(ast::Literal::Integer(value)),
                    None => None,
                }
            } else {
                match float_trust::parse_f64(bytes.as_slice()) {
                    Some(value) => Some(ast::Literal::Float(value)),
                    None => None,
                }
            }
        },
        super::Token::String(value) => Some(ast::Literal::String(value.clone())),
        _ => None,
    }
}

/// Exec prefix-operator detection refining `prefix_operator`.
pub fn prefix_op_exec(tok: &super::Token) -> (r: Option<UnaryTag>)
    ensures r == verified_expression::prefix_operator(verified_production::token_view(*tok)),
{
    match tok {
        super::Token::Plus => Some(UnaryTag::Identity),
        super::Token::Minus => Some(UnaryTag::Negate),
        super::Token::Keyword(Keyword::Not) => Some(UnaryTag::Not),
        _ => None,
    }
}

/// Exec binary-operator detection refining `binary_from_token`.
pub fn binary_tag_exec(tok: &super::Token) -> (r: Option<BinaryTag>)
    ensures r == verified_expression::binary_from_token(verified_production::token_view(*tok)),
{
    match tok {
        super::Token::Keyword(Keyword::And) => Some(BinaryTag::And),
        super::Token::Keyword(Keyword::Or) => Some(BinaryTag::Or),
        super::Token::Equal => Some(BinaryTag::Equal),
        super::Token::GreaterThan => Some(BinaryTag::GreaterThan),
        super::Token::GreaterThanOrEqual => Some(BinaryTag::GreaterThanOrEqual),
        super::Token::LessThan => Some(BinaryTag::LessThan),
        super::Token::LessThanOrEqual => Some(BinaryTag::LessThanOrEqual),
        super::Token::NotEqual => Some(BinaryTag::NotEqual),
        // `<>` is a second spelling of not-equal; mirrors binary_from_token.
        super::Token::LessOrGreaterThan => Some(BinaryTag::NotEqual),
        super::Token::Plus => Some(BinaryTag::Add),
        super::Token::Slash => Some(BinaryTag::Divide),
        super::Token::Caret => Some(BinaryTag::Exponentiate),
        super::Token::Asterisk => Some(BinaryTag::Multiply),
        super::Token::Percent => Some(BinaryTag::Remainder),
        super::Token::Minus => Some(BinaryTag::Subtract),
        super::Token::Keyword(Keyword::Like) => Some(BinaryTag::Like),
        _ => None,
    }
}

/// Build the `ast::Operator` for a unary tag, matching the mirror's `Unary`.
pub fn build_unary(tag: UnaryTag, inner: ast::Expression) -> (r: ast::Expression)
    ensures view_expr(r) == SExpr::Unary(tag, Box::new(view_expr(inner))),
{
    match tag {
        UnaryTag::Identity => ast::Expression::Operator(ast::Operator::Identity(Box::new(inner))),
        UnaryTag::Negate => ast::Expression::Operator(ast::Operator::Negate(Box::new(inner))),
        UnaryTag::Not => ast::Expression::Operator(ast::Operator::Not(Box::new(inner))),
    }
}

/// Build the `ast::Operator` for a binary tag, matching the mirror's `Binary`.
pub fn build_binary(tag: BinaryTag, left: ast::Expression, right: ast::Expression) -> (r: ast::Expression)
    ensures view_expr(r) == SExpr::Binary(tag, Box::new(view_expr(left)), Box::new(view_expr(right))),
{
    match tag {
        BinaryTag::And => ast::Expression::Operator(ast::Operator::And(Box::new(left), Box::new(right))),
        BinaryTag::Or => ast::Expression::Operator(ast::Operator::Or(Box::new(left), Box::new(right))),
        BinaryTag::Equal => ast::Expression::Operator(ast::Operator::Equal(Box::new(left), Box::new(right))),
        BinaryTag::GreaterThan => ast::Expression::Operator(ast::Operator::GreaterThan(Box::new(left), Box::new(right))),
        BinaryTag::GreaterThanOrEqual => ast::Expression::Operator(ast::Operator::GreaterThanOrEqual(Box::new(left), Box::new(right))),
        BinaryTag::LessThan => ast::Expression::Operator(ast::Operator::LessThan(Box::new(left), Box::new(right))),
        BinaryTag::LessThanOrEqual => ast::Expression::Operator(ast::Operator::LessThanOrEqual(Box::new(left), Box::new(right))),
        BinaryTag::NotEqual => ast::Expression::Operator(ast::Operator::NotEqual(Box::new(left), Box::new(right))),
        BinaryTag::Add => ast::Expression::Operator(ast::Operator::Add(Box::new(left), Box::new(right))),
        BinaryTag::Divide => ast::Expression::Operator(ast::Operator::Divide(Box::new(left), Box::new(right))),
        BinaryTag::Exponentiate => ast::Expression::Operator(ast::Operator::Exponentiate(Box::new(left), Box::new(right))),
        BinaryTag::Multiply => ast::Expression::Operator(ast::Operator::Multiply(Box::new(left), Box::new(right))),
        BinaryTag::Remainder => ast::Expression::Operator(ast::Operator::Remainder(Box::new(left), Box::new(right))),
        BinaryTag::Subtract => ast::Expression::Operator(ast::Operator::Subtract(Box::new(left), Box::new(right))),
        BinaryTag::Like => ast::Expression::Operator(ast::Operator::Like(Box::new(left), Box::new(right))),
    }
}

// ---- the executable parser -------------------------------------------------

/// Exec single-token literal printer refining `literal_views`.
pub fn print_lit_exec(l: &ast::Literal) -> (r: Vec<super::Token>)
    requires verified_production::printable_literal(*l),
    ensures verified_production::token_views(r@) == verified_production::literal_views(*l).unwrap(),
{
    reveal(verified_production::literal_views);
    reveal_with_fuel(verified_production::token_views, 2);
    let mut r: Vec<super::Token> = Vec::new();
    match l {
        ast::Literal::Null => r.push(super::Token::Keyword(Keyword::Null)),
        ast::Literal::Boolean(true) => r.push(super::Token::Keyword(Keyword::True)),
        ast::Literal::Boolean(false) => r.push(super::Token::Keyword(Keyword::False)),
        ast::Literal::Integer(n) => r.push(super::Token::Number(super::verified_integer::print_i64(*n))),
        ast::Literal::Float(x) => r.push(super::Token::Number(float_trust::format_f64(*x))),
        ast::Literal::String(s) => r.push(super::Token::String(s.clone())),
    }
    proof { assert(r@.drop_first() =~= Seq::<super::Token>::empty()); }
    r
}

/// `view_args` preserves length.
pub proof fn view_args_len(s: Seq<ast::Expression>)
    ensures view_args(s).len() == s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        view_args_len(s.drop_first());
    }
}

/// Head/tail unfolding of `view_args`.
pub proof fn view_args_step(s: Seq<ast::Expression>)
    requires s.len() > 0,
    ensures
        view_args(s).len() > 0,
        view_args(s)[0] == view_expr(s[0]),
        view_args(s).drop_first() == view_args(s.drop_first()),
{
    assert(view_args(s) =~= seq![view_expr(s[0])] + view_args(s.drop_first()));
}

/// The head element's depth is below the list depth (termination of the
/// printer's list -> element recursion).
pub proof fn slist_depth_head_decreases(args: Seq<ast::Expression>)
    requires args.len() > 0,
    ensures sdepth(view_expr(args[0])) < slist_depth(view_args(args)),
{
    view_args_step(args);
}

/// The tail's list depth is below the list depth (termination of the printer's
/// list -> tail recursion).
pub proof fn slist_depth_tail_decreases(args: Seq<ast::Expression>)
    requires args.len() > 0,
    ensures slist_depth(view_args(args.drop_first())) < slist_depth(view_args(args)),
{
    view_args_step(args);
}

} // verus!
