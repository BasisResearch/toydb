//! Unified full-grammar expression roundtrip over an executable parser.
//!
//! `verified_expression` proves the print/parse roundtrip for every
//! *function-free* production expression, using a `spec fn` parser that builds
//! `ast::Expression` values directly and compares them with `==`. That path
//! cannot reach `Expression::Function`, because its `Vec<Expression>` payload
//! is opaque in the spec logic: Verus has no spec-level `Vec` constructor and
//! `Vec` equality is not view-determined. `verified_function_list` shows the
//! escape for functions in isolation — an *executable* parser that builds real
//! `Vec`s at runtime, verified against a `Seq`-based mirror AST at the level of
//! a structural view.
//!
//! A `Function` can nest under any operator and any expression can be a
//! function argument, so the two paths cannot be composed piecewise: the whole
//! expression nest must move to the executable/mirror style at once. This
//! module is that unification. `SExpr` is the `Seq`-based mirror of the entire
//! `ast::Expression` grammar (operator children are `Box<SExpr>`, function
//! arguments are `Seq<SExpr>`); it carries the canonical printer `sprint`, the
//! fuel measure `sdepth`, the mirror parser `sparse`, and the roundtrip proof
//! `lemma_sparse_sprint`. Because every mirror component is spec-constructible
//! and extensional, the mirror roundtrip closes with real `==` on `SExpr`.
//!
//! The bridge to production values is `view_expr: ast::Expression -> SExpr`.
//! The live consumers are `verified_precedence` (whose production parser
//! `parse_expression_full` refines `sparse_prec`, itself stated over this
//! mirror) and the statement layer (`verified_stmt` / `verified_stmt_prec` /
//! `verified_control`), which reuse `SExpr`, `view_expr`, `sparse` and the
//! roundtrip lemmas. The executable twin that used to sit on this scaffold
//! (`parse_expr_exec` / `print_expr_exec` for the fully-parenthesised grammar,
//! plus their wrap/roundtrip helpers) was never called by production and was
//! deleted in phase 4 (`plans/phase-4-delete-twins.md`); `print_lit_exec`
//! stays, serving `verified_minparen`'s min-parens printer.
//!
//! Trust surface is unchanged: the only axioms are the `float_trust` boundary
//! reused through `literal_views` / `parse_literal_views`.

// Ghost bindings are erased by the non-Verus build; the module is verification
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

pub open spec fn islit_literal(lit: IsLit) -> ast::Literal {
    match lit {
        IsLit::Null => ast::Literal::Null,
        IsLit::NaN => ast::Literal::Float(float_trust::spec_canonical_nan()),
    }
}

// ---- canonical printer over the mirror -------------------------------------

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

// ---- fuel measure ----------------------------------------------------------

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

pub open spec fn sparse(input: Seq<TokenView>, fuel: nat) -> (Option<SExpr>, Seq<TokenView>)
    decreases fuel, 1nat,
{
    if fuel == 0 || input.len() == 0 {
        (None, input)
    } else {
        match input[0] {
            TokenView::OpenParen => sparse_operator(input, fuel),
            TokenView::Asterisk => (Some(SExpr::All), input.drop_first()),
            TokenView::Ident(name) => {
                if input.len() >= 2 && input[1] == TokenView::OpenParen {
                    match sparse_args(input.drop_first().drop_first(), (fuel - 1) as nat) {
                        (Some(args), rest) if rest.len() > 0 && rest[0] == TokenView::CloseParen =>
                            (Some(SExpr::Function(name, args)), rest.drop_first()),
                        _ => (None, input),
                    }
                } else if input.len() >= 3 && input[1] == TokenView::Period {
                    match input[2] {
                        TokenView::Ident(column) => (
                            Some(SExpr::Column(Some(name), column)),
                            input.drop_first().drop_first().drop_first(),
                        ),
                        _ => (None, input),
                    }
                } else {
                    (Some(SExpr::Column(None, name)), input.drop_first())
                }
            },
            TokenView::Number(bytes) => match verified_production::parse_literal_views(seq![TokenView::Number(bytes)]) {
                Some(literal) => (Some(SExpr::Literal(literal)), input.drop_first()),
                None => (None, input),
            },
            TokenView::Keyword(Keyword::Null)
            | TokenView::Keyword(Keyword::True)
            | TokenView::Keyword(Keyword::False)
            | TokenView::String(_) => match verified_production::parse_literal_views(seq![input[0]]) {
                Some(literal) => (Some(SExpr::Literal(literal)), input.drop_first()),
                None => (None, input),
            },
            _ => (None, input),
        }
    }
}

/// The parenthesised operator forms. `input[0]` is known to be `OpenParen`.
pub open spec fn sparse_operator(input: Seq<TokenView>, fuel: nat) -> (Option<SExpr>, Seq<TokenView>)
    decreases fuel, 0nat,
{
    if fuel == 0 || input.len() < 2 {
        (None, input)
    } else {
        match verified_expression::prefix_operator(input[1]) {
            Some(tag) => match sparse(input.drop_first().drop_first(), (fuel - 1) as nat) {
                (Some(inner), rest) if rest.len() > 0 && rest[0] == TokenView::CloseParen =>
                    (Some(SExpr::Unary(tag, Box::new(inner))), rest.drop_first()),
                _ => (None, input),
            },
            None => match sparse(input.drop_first(), (fuel - 1) as nat) {
                (Some(left), after_left) if after_left.len() > 0 => {
                    if after_left[0] == TokenView::Exclamation {
                        if after_left.len() > 1 && after_left[1] == TokenView::CloseParen {
                            (
                                Some(SExpr::Factorial(Box::new(left))),
                                after_left.drop_first().drop_first(),
                            )
                        } else {
                            (None, input)
                        }
                    } else if after_left[0] == TokenView::Keyword(Keyword::Is) {
                        if after_left.len() >= 3 && after_left[2] == TokenView::CloseParen {
                            let lit = match after_left[1] {
                                TokenView::Keyword(Keyword::Null) => Some(IsLit::Null),
                                TokenView::Keyword(Keyword::NaN) => Some(IsLit::NaN),
                                _ => None,
                            };
                            match lit {
                                Some(lit) => (
                                    Some(SExpr::Is(Box::new(left), lit)),
                                    after_left.drop_first().drop_first().drop_first(),
                                ),
                                None => (None, input),
                            }
                        } else {
                            (None, input)
                        }
                    } else {
                        match verified_expression::binary_from_token(after_left[0]) {
                            Some(tag) => match sparse(after_left.drop_first(), (fuel - 1) as nat) {
                                (Some(right), rest) if rest.len() > 0 && rest[0] == TokenView::CloseParen =>
                                    (
                                        Some(SExpr::Binary(tag, Box::new(left), Box::new(right))),
                                        rest.drop_first(),
                                    ),
                                _ => (None, input),
                            },
                            None => (None, input),
                        }
                    }
                },
                _ => (None, input),
            },
        }
    }
}

pub open spec fn sparse_args(input: Seq<TokenView>, fuel: nat) -> (Option<Seq<SExpr>>, Seq<TokenView>)
    decreases fuel, 0nat,
{
    if fuel == 0 || input.len() == 0 {
        (None, input)
    } else if input[0] == TokenView::CloseParen {
        (Some(Seq::empty()), input)
    } else {
        match sparse(input, (fuel - 1) as nat) {
            (Some(e), rest) => {
                if rest.len() == 0 {
                    (None, input)
                } else if rest[0] == TokenView::CloseParen {
                    (Some(seq![e]), rest)
                } else if rest[0] == TokenView::Comma {
                    match sparse_args(rest.drop_first(), (fuel - 1) as nat) {
                        (Some(more), rest2) => (Some(seq![e] + more), rest2),
                        (None, _) => (None, input),
                    }
                } else {
                    (None, input)
                }
            },
            (None, _) => (None, input),
        }
    }
}

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

/// The first token of any printed expression is an atom-start token: never a
/// prefix-operator token (so parenthesised parsing routes to the postfix/binary
/// branch), and never `)` (so argument-list parsing does not stop early).
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

// ---- fuel bound: sdepth <= printed length ----------------------------------

pub proof fn sdepth_positive(e: SExpr)
    ensures sdepth(e) >= 1,
{
}

pub proof fn sdepth_le_len(e: SExpr)
    requires printable_se(e),
    ensures sdepth(e) <= sprint(e).len(),
    decreases e,
{
    reveal(printable_se);
    match e {
        SExpr::All => { assert(sprint(e).len() == 1); },
        SExpr::Column(table, _) => {
            match table {
                Some(_) => { assert(sprint(e).len() == 3); },
                None => { assert(sprint(e).len() == 1); },
            }
        },
        SExpr::Literal(l) => {
            reveal(verified_production::literal_views);
            assert(sprint(e) == verified_production::literal_views(l).unwrap());
            assert(verified_production::literal_views(l).unwrap().len() == 1);
        },
        SExpr::Unary(_, inner) => { sdepth_le_len(*inner); },
        SExpr::Factorial(inner) => { sdepth_le_len(*inner); },
        SExpr::Is(inner, _) => { sdepth_le_len(*inner); },
        SExpr::Binary(_, left, right) => {
            sdepth_le_len(*left);
            sdepth_le_len(*right);
        },
        SExpr::Function(_, args) => { slist_depth_le_len(args); },
    }
}

// ---- headline: the mirror roundtrip over the full grammar -------------------

/// Parsing the canonical print of any printable mirror expression, followed by
/// an arbitrary boundary-respecting tail, recovers the expression exactly and
/// leaves the tail unconsumed.
#[verifier::rlimit(4000)]
pub proof fn lemma_sparse_sprint(e: SExpr, tail: Seq<TokenView>, fuel: nat)
    requires
        printable_se(e),
        fuel >= sdepth(e),
        boundary(tail),
    ensures
        sparse(sprint(e) + tail, fuel) == (Some(e), tail),
    decreases e,
{
    reveal(printable_se);
    reveal_with_fuel(sparse, 1);
    let tokens = sprint(e) + tail;
    match e {
        SExpr::All => {
            assert(tokens[0] == TokenView::Asterisk);
            assert(tokens.drop_first() =~= tail);
        },
        SExpr::Column(table, column) => match table {
            None => {
                assert(tokens[0] == TokenView::Ident(column));
                if tokens.len() >= 2 {
                    assert(tokens[1] == tail[0]);
                }
                assert(tokens.drop_first() =~= tail);
            },
            Some(t) => {
                assert(tokens.len() >= 3);
                assert(tokens[0] == TokenView::Ident(t));
                assert(tokens[1] == TokenView::Period);
                assert(tokens[2] == TokenView::Ident(column));
                assert(tokens.drop_first().drop_first().drop_first() =~= tail);
            },
        },
        SExpr::Literal(l) => {
            reveal(verified_production::literal_views);
            reveal(verified_production::parse_literal_views);
            verified_production::literal_roundtrip(l);
            let lv = verified_production::literal_views(l).unwrap();
            assert(sprint(e) == lv);
            assert(lv.len() == 1);
            assert(seq![tokens[0]] =~= lv);
            assert(tokens.drop_first() =~= tail);
        },
        SExpr::Unary(tag, inner) => {
            reveal_with_fuel(sparse_operator, 1);
            unary_tok_prefix(tag);
            let inner_tail = seq![TokenView::CloseParen] + tail;
            lemma_sparse_sprint(*inner, inner_tail, (fuel - 1) as nat);
            assert(tokens[0] == TokenView::OpenParen);
            assert(tokens.len() >= 2);
            assert(tokens[1] == unary_tok(tag));
            assert(tokens.drop_first().drop_first() =~= sprint(*inner) + inner_tail);
            assert(inner_tail[0] == TokenView::CloseParen);
            assert(inner_tail.drop_first() =~= tail);
        },
        SExpr::Factorial(inner) => {
            reveal_with_fuel(sparse_operator, 1);
            sprint_head(*inner);
            let inner_tail = seq![TokenView::Exclamation, TokenView::CloseParen] + tail;
            lemma_sparse_sprint(*inner, inner_tail, (fuel - 1) as nat);
            assert(tokens[0] == TokenView::OpenParen);
            assert(tokens.len() >= 2);
            assert(tokens[1] == sprint(*inner)[0]);
            assert(tokens.drop_first() =~= sprint(*inner) + inner_tail);
            assert(inner_tail[0] == TokenView::Exclamation);
            assert(inner_tail[1] == TokenView::CloseParen);
            assert(inner_tail.drop_first().drop_first() =~= tail);
        },
        SExpr::Is(inner, lit) => {
            reveal_with_fuel(sparse_operator, 1);
            sprint_head(*inner);
            let inner_tail =
                seq![TokenView::Keyword(Keyword::Is), islit_tok(lit), TokenView::CloseParen] + tail;
            lemma_sparse_sprint(*inner, inner_tail, (fuel - 1) as nat);
            assert(tokens[0] == TokenView::OpenParen);
            assert(tokens.len() >= 2);
            assert(tokens[1] == sprint(*inner)[0]);
            assert(tokens.drop_first() =~= sprint(*inner) + inner_tail);
            assert(inner_tail[0] == TokenView::Keyword(Keyword::Is));
            assert(inner_tail[1] == islit_tok(lit));
            assert(inner_tail[2] == TokenView::CloseParen);
            assert(inner_tail.drop_first().drop_first().drop_first() =~= tail);
            match lit {
                IsLit::Null => {},
                IsLit::NaN => {},
            }
        },
        SExpr::Binary(tag, left, right) => {
            reveal_with_fuel(sparse_operator, 1);
            binary_tok_roundtrip(tag);
            sprint_head(*left);
            let right_tail = seq![TokenView::CloseParen] + tail;
            let left_tail = seq![binary_tok(tag)] + sprint(*right) + right_tail;
            lemma_sparse_sprint(*left, left_tail, (fuel - 1) as nat);
            lemma_sparse_sprint(*right, right_tail, (fuel - 1) as nat);
            assert(tokens[0] == TokenView::OpenParen);
            assert(tokens.len() >= 2);
            assert(tokens[1] == sprint(*left)[0]);
            assert(tokens.drop_first() =~= sprint(*left) + left_tail);
            assert(left_tail[0] == binary_tok(tag));
            assert(left_tail.drop_first() =~= sprint(*right) + right_tail);
            assert(right_tail[0] == TokenView::CloseParen);
            assert(right_tail.drop_first() =~= tail);
        },
        SExpr::Function(name, args) => {
            let inner_tail = seq![TokenView::CloseParen] + tail;
            lemma_sparse_args_sprint(args, inner_tail, (fuel - 1) as nat);
            assert(tokens[0] == TokenView::Ident(name));
            assert(tokens.len() >= 2);
            assert(tokens[1] == TokenView::OpenParen);
            assert(tokens.drop_first().drop_first() =~= sprint_args(args) + inner_tail);
            assert(inner_tail[0] == TokenView::CloseParen);
            assert(inner_tail.drop_first() =~= tail);
        },
    }
}

/// Comma-list companion: parsing the canonical print of a printable argument
/// sequence, closed by a `)`-led tail, recovers the sequence exactly.
pub proof fn lemma_sparse_args_sprint(args: Seq<SExpr>, tail: Seq<TokenView>, fuel: nat)
    requires
        all_printable_se(args),
        fuel >= slist_depth(args),
        tail.len() > 0,
        tail[0] == TokenView::CloseParen,
    ensures
        sparse_args(sprint_args(args) + tail, fuel) == (Some(args), tail),
    decreases args,
{
    reveal_with_fuel(sparse_args, 1);
    if args.len() == 0 {
        assert(sprint_args(args) + tail =~= tail);
        assert(Seq::<SExpr>::empty() =~= args);
    } else if args.len() == 1 {
        sprint_head(args[0]);
        lemma_sparse_sprint(args[0], tail, (fuel - 1) as nat);
        assert(sprint_args(args) + tail =~= sprint(args[0]) + tail);
        assert(seq![args[0]] =~= args);
    } else {
        let rest_args = args.drop_first();
        let comma_tail = seq![TokenView::Comma] + sprint_args(rest_args) + tail;
        sprint_head(args[0]);
        lemma_sparse_sprint(args[0], comma_tail, (fuel - 1) as nat);
        lemma_sparse_args_sprint(rest_args, tail, (fuel - 1) as nat);
        assert(sprint_args(args) + tail =~= sprint(args[0]) + comma_tail);
        assert(comma_tail[0] == TokenView::Comma);
        assert(comma_tail.drop_first() =~= sprint_args(rest_args) + tail);
        assert(seq![args[0]] + rest_args =~= args);
    }
}

/// The canonical mirror printer roundtrips: parsing a full print recovers the
/// expression and consumes all of it.
pub proof fn mirror_roundtrip(e: SExpr)
    requires printable_se(e),
    ensures sparse(sprint(e), sdepth(e)) == (Some(e), Seq::<TokenView>::empty()),
{
    lemma_sparse_sprint(e, Seq::empty(), sdepth(e));
    assert(sprint(e) + Seq::<TokenView>::empty() =~= sprint(e));
}

/// The canonical mirror printer is injective on its printable domain.
pub proof fn mirror_injective(left: SExpr, right: SExpr)
    requires printable_se(left), printable_se(right),
    ensures sprint(left) == sprint(right) ==> left == right,
{
    if sprint(left) == sprint(right) {
        let fuel = if sdepth(left) >= sdepth(right) { sdepth(left) } else { sdepth(right) };
        lemma_sparse_sprint(left, Seq::empty(), fuel);
        lemma_sparse_sprint(right, Seq::empty(), fuel);
        assert(sprint(left) + Seq::<TokenView>::empty() =~= sprint(left));
        assert(sprint(right) + Seq::<TokenView>::empty() =~= sprint(right));
    }
}

pub proof fn slist_depth_le_len(args: Seq<SExpr>)
    requires all_printable_se(args),
    ensures slist_depth(args) <= sprint_args(args).len() + 1,
    decreases args,
{
    if args.len() == 0 {
    } else if args.len() == 1 {
        sdepth_le_len(args[0]);
        assert(sprint_args(args) == sprint(args[0]));
        assert(slist_depth(args.drop_first()) == 1);
    } else {
        sdepth_le_len(args[0]);
        slist_depth_le_len(args.drop_first());
        assert(sprint_args(args)
            == sprint(args[0]) + seq![TokenView::Comma] + sprint_args(args.drop_first()));
    }
}

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

/// Structural injectivity of the canonical printer on the printable domain: two
/// printable expressions with the same canonical print have the same structural
/// view. Corollary of `mirror_injective` through the `view_expr` bridge.
pub proof fn roundtrip_injective(left: ast::Expression, right: ast::Expression)
    requires
        printable_se(view_expr(left)),
        printable_se(view_expr(right)),
        sprint(view_expr(left)) == sprint(view_expr(right)),
    ensures
        view_expr(left) == view_expr(right),
{
    mirror_injective(view_expr(left), view_expr(right));
}

} // verus!
