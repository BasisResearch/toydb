//! Full-grammar statement roundtrip in the mirror + executable style.
//!
//! This is the statement-level analogue of `verified_roundtrip`: `SStmt` is a
//! `Seq`-based mirror of `ast::Statement` whose expression children are the
//! expression mirror `SExpr` (through the existing `view_expr` bridge) and whose
//! containers (`Vec`s, join trees, the `BTreeMap` set) become `Seq`s. It carries
//! the canonical statement printer `sprint_stmt`, the fuel measure `sdepth_stmt`,
//! the mirror parser `sparse_stmt`, and the roundtrip proof
//! `lemma_sparse_stmt_sprint`. The bridge to production values is
//! `view_stmt: ast::Statement -> SStmt`; the executable layer
//! (`parse_stmt_exec` / `print_stmt_exec`) refines the mirror at the `view_stmt`
//! level, delegating every embedded expression to `parse_expr_exec` /
//! `print_expr_exec` from `verified_roundtrip`.
//!
//! Trust surface is unchanged: the only axioms remain the `float_trust`
//! boundary, reached transitively through the expression layer.
//!
//! The mirror grows one phase at a time (S0-S5 in
//! `verus-parser-roundtrip-plan.md`). Statement kinds that are not yet mirrored
//! map to `SStmt::Unsupported`, which is outside the printable domain, so the
//! roundtrip lemma never has to reason about them.

#![allow(dead_code, unused_variables)]

#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use super::verified_production::TokenView;
#[allow(unused_imports)]
use super::verified_roundtrip::{
    boundary, lemma_sparse_sprint, printable_se, sdepth, sparse, sprint, view_expr, SExpr,
};
#[allow(unused_imports)]
use super::{ast, verified_integer, verified_production, verified_roundtrip, Keyword};

verus! {

// ---- Seq-based mirror of the statement grammar (grown per phase S0-S5) ------

/// Mirror of `ast::Statement`. Expression children are `SExpr` (via `view_expr`)
/// and containers become `Seq`s. `Unsupported` is the placeholder for statement
/// kinds not yet mirrored; it is outside `printable_stmt`, so the roundtrip
/// proof never touches it.
pub enum SStmt {
    Begin { read_only: bool, as_of: Option<u64> },
    Commit,
    Rollback,
    DropTable { name: String, if_exists: bool },
    Delete { table: String, where_clause: Option<SExpr> },
    Explain(Box<SStmt>),
    Unsupported,
}

/// Structural view of a production statement as a mirror statement.
pub open spec fn view_stmt(s: ast::Statement) -> SStmt
    decreases s,
{
    match s {
        ast::Statement::Begin { read_only, as_of } => SStmt::Begin { read_only, as_of },
        ast::Statement::Commit => SStmt::Commit,
        ast::Statement::Rollback => SStmt::Rollback,
        ast::Statement::DropTable { name, if_exists } => SStmt::DropTable { name, if_exists },
        ast::Statement::Delete { table, where_clause } => SStmt::Delete {
            table,
            where_clause: match where_clause {
                Some(e) => Some(view_expr(e)),
                None => None,
            },
        },
        ast::Statement::Explain(inner) => SStmt::Explain(Box::new(view_stmt(*inner))),
        _ => SStmt::Unsupported,
    }
}

/// Whether a mirror statement is a (nested) `Explain`, used to forbid the
/// degenerate `EXPLAIN EXPLAIN ...` which the printer would not disambiguate.
pub open spec fn is_sexplain(s: SStmt) -> bool {
    match s {
        SStmt::Explain(_) => true,
        _ => false,
    }
}

// ---- printer domain --------------------------------------------------------

/// Whether the canonical statement printer can encode this mirror statement.
pub open spec fn printable_stmt(s: SStmt) -> bool
    decreases s,
{
    match s {
        SStmt::Begin { .. } => true,
        SStmt::Commit => true,
        SStmt::Rollback => true,
        SStmt::DropTable { .. } => true,
        SStmt::Delete { where_clause: Some(e), .. } => printable_se(e),
        SStmt::Delete { where_clause: None, .. } => true,
        SStmt::Explain(inner) => !is_sexplain(*inner) && printable_stmt(*inner),
        SStmt::Unsupported => false,
    }
}

// ---- canonical statement printer over the mirror ---------------------------

pub open spec fn sprint_stmt(s: SStmt) -> Seq<TokenView>
    decreases s,
{
    match s {
        SStmt::Begin { read_only, as_of } => {
            let prefix = if read_only {
                seq![
                    TokenView::Keyword(Keyword::Begin),
                    TokenView::Keyword(Keyword::Read),
                    TokenView::Keyword(Keyword::Only),
                ]
            } else {
                seq![TokenView::Keyword(Keyword::Begin)]
            };
            prefix + match as_of {
                Some(version) => seq![
                    TokenView::Keyword(Keyword::As),
                    TokenView::Keyword(Keyword::Of),
                    TokenView::Keyword(Keyword::System),
                    TokenView::Keyword(Keyword::Time),
                    TokenView::Number(verified_integer::decimal_digits(version)),
                ],
                None => Seq::empty(),
            }
        },
        SStmt::Commit => seq![TokenView::Keyword(Keyword::Commit)],
        SStmt::Rollback => seq![TokenView::Keyword(Keyword::Rollback)],
        SStmt::DropTable { name, if_exists: false } => seq![
            TokenView::Keyword(Keyword::Drop),
            TokenView::Keyword(Keyword::Table),
            TokenView::Ident(name),
        ],
        SStmt::DropTable { name, if_exists: true } => seq![
            TokenView::Keyword(Keyword::Drop),
            TokenView::Keyword(Keyword::Table),
            TokenView::Keyword(Keyword::If),
            TokenView::Keyword(Keyword::Exists),
            TokenView::Ident(name),
        ],
        SStmt::Delete { table, where_clause: None } => seq![
            TokenView::Keyword(Keyword::Delete),
            TokenView::Keyword(Keyword::From),
            TokenView::Ident(table),
        ],
        SStmt::Delete { table, where_clause: Some(e) } => seq![
            TokenView::Keyword(Keyword::Delete),
            TokenView::Keyword(Keyword::From),
            TokenView::Ident(table),
            TokenView::Keyword(Keyword::Where),
        ] + sprint(e),
        SStmt::Explain(inner) => seq![TokenView::Keyword(Keyword::Explain)] + sprint_stmt(*inner),
        SStmt::Unsupported => Seq::empty(),
    }
}

// ---- fuel measure ----------------------------------------------------------

pub open spec fn sdepth_stmt(s: SStmt) -> nat
    decreases s,
{
    match s {
        SStmt::Delete { where_clause: Some(e), .. } => 1 + sdepth(e),
        SStmt::Explain(inner) => 1 + sdepth_stmt(*inner),
        _ => 1,
    }
}

// ---- mirror parser ---------------------------------------------------------

/// `BEGIN` forms. `input[0]` is known to be `BEGIN`.
pub open spec fn sparse_begin(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>) {
    let (read_only, after) = if input.len() >= 3
        && input[1] == TokenView::Keyword(Keyword::Read)
        && input[2] == TokenView::Keyword(Keyword::Only) {
        (true, input.drop_first().drop_first().drop_first())
    } else {
        (false, input.drop_first())
    };
    if after.len() >= 5
        && after[0] == TokenView::Keyword(Keyword::As)
        && after[1] == TokenView::Keyword(Keyword::Of)
        && after[2] == TokenView::Keyword(Keyword::System)
        && after[3] == TokenView::Keyword(Keyword::Time) {
        match after[4] {
            TokenView::Number(bytes) => match verified_integer::parse_digits_spec(bytes) {
                Some(version) => (
                    Some(SStmt::Begin { read_only, as_of: Some(version) }),
                    after.drop_first().drop_first().drop_first().drop_first().drop_first(),
                ),
                None => (Some(SStmt::Begin { read_only, as_of: None }), after),
            },
            _ => (Some(SStmt::Begin { read_only, as_of: None }), after),
        }
    } else {
        (Some(SStmt::Begin { read_only, as_of: None }), after)
    }
}

/// `DROP TABLE` forms. `input[0]` is known to be `DROP`.
pub open spec fn sparse_drop(input: Seq<TokenView>) -> (Option<SStmt>, Seq<TokenView>) {
    if input.len() >= 4
        && input[1] == TokenView::Keyword(Keyword::Table)
        && input[2] == TokenView::Keyword(Keyword::If)
        && input[3] == TokenView::Keyword(Keyword::Exists) {
        if input.len() >= 5 {
            match input[4] {
                TokenView::Ident(name) => (
                    Some(SStmt::DropTable { name, if_exists: true }),
                    input.drop_first().drop_first().drop_first().drop_first().drop_first(),
                ),
                _ => (None, input),
            }
        } else {
            (None, input)
        }
    } else if input.len() >= 3 && input[1] == TokenView::Keyword(Keyword::Table) {
        match input[2] {
            TokenView::Ident(name) => (
                Some(SStmt::DropTable { name, if_exists: false }),
                input.drop_first().drop_first().drop_first(),
            ),
            _ => (None, input),
        }
    } else {
        (None, input)
    }
}

/// `DELETE FROM` forms. `input[0]` is known to be `DELETE`.
pub open spec fn sparse_delete(input: Seq<TokenView>, fuel: nat) -> (Option<SStmt>, Seq<TokenView>) {
    if input.len() < 3 || input[1] != TokenView::Keyword(Keyword::From) {
        (None, input)
    } else {
        match input[2] {
            TokenView::Ident(table) => {
                if input.len() >= 4 && input[3] == TokenView::Keyword(Keyword::Where) {
                    match sparse(input.drop_first().drop_first().drop_first().drop_first(), fuel) {
                        (Some(e), rest) => (
                            Some(SStmt::Delete { table, where_clause: Some(e) }),
                            rest,
                        ),
                        (None, _) => (None, input),
                    }
                } else {
                    (
                        Some(SStmt::Delete { table, where_clause: None }),
                        input.drop_first().drop_first().drop_first(),
                    )
                }
            },
            _ => (None, input),
        }
    }
}

pub open spec fn sparse_stmt(input: Seq<TokenView>, fuel: nat) -> (Option<SStmt>, Seq<TokenView>)
    decreases fuel,
{
    if fuel == 0 || input.len() == 0 {
        (None, input)
    } else {
        match input[0] {
            TokenView::Keyword(Keyword::Commit) => (Some(SStmt::Commit), input.drop_first()),
            TokenView::Keyword(Keyword::Rollback) => (Some(SStmt::Rollback), input.drop_first()),
            TokenView::Keyword(Keyword::Begin) => sparse_begin(input),
            TokenView::Keyword(Keyword::Drop) => sparse_drop(input),
            TokenView::Keyword(Keyword::Delete) => sparse_delete(input, fuel),
            TokenView::Keyword(Keyword::Explain) => {
                match sparse_stmt(input.drop_first(), (fuel - 1) as nat) {
                    (Some(inner), rest) if !is_sexplain(inner) => (
                        Some(SStmt::Explain(Box::new(inner))),
                        rest,
                    ),
                    _ => (None, input),
                }
            },
            _ => (None, input),
        }
    }
}

// ---- headline: the mirror statement roundtrip ------------------------------

/// Parsing the canonical print of any printable mirror statement recovers it
/// exactly and consumes all of it.
#[verifier::rlimit(4000)]
pub proof fn lemma_sparse_stmt_sprint(s: SStmt, fuel: nat)
    requires
        printable_stmt(s),
        fuel >= sdepth_stmt(s),
    ensures
        sparse_stmt(sprint_stmt(s), fuel) == (Some(s), Seq::<TokenView>::empty()),
    decreases s,
{
    reveal(printable_stmt);
    reveal_with_fuel(sparse_stmt, 1);
    let tokens = sprint_stmt(s);
    match s {
        SStmt::Commit => {
            assert(tokens[0] == TokenView::Keyword(Keyword::Commit));
            assert(tokens.drop_first() =~= Seq::<TokenView>::empty());
        },
        SStmt::Rollback => {
            assert(tokens[0] == TokenView::Keyword(Keyword::Rollback));
            assert(tokens.drop_first() =~= Seq::<TokenView>::empty());
        },
        SStmt::Begin { read_only, as_of } => {
            let (r_prefix, after0) = if read_only {
                (
                    seq![
                        TokenView::Keyword(Keyword::Begin),
                        TokenView::Keyword(Keyword::Read),
                        TokenView::Keyword(Keyword::Only),
                    ],
                    3int,
                )
            } else {
                (seq![TokenView::Keyword(Keyword::Begin)], 1int)
            };
            assert(tokens[0] == TokenView::Keyword(Keyword::Begin));
            // sparse_begin recomputes the read_only prefix positionally.
            match as_of {
                None => {
                    if read_only {
                        assert(tokens =~= r_prefix);
                        assert(tokens.drop_first().drop_first().drop_first() =~= Seq::<TokenView>::empty());
                    } else {
                        assert(tokens =~= r_prefix);
                        assert(tokens.drop_first() =~= Seq::<TokenView>::empty());
                    }
                },
                Some(version) => {
                    verified_integer::print_parse_u64_roundtrip(version);
                    let as_of_toks = seq![
                        TokenView::Keyword(Keyword::As),
                        TokenView::Keyword(Keyword::Of),
                        TokenView::Keyword(Keyword::System),
                        TokenView::Keyword(Keyword::Time),
                        TokenView::Number(verified_integer::decimal_digits(version)),
                    ];
                    if read_only {
                        assert(tokens =~= r_prefix + as_of_toks);
                        assert(tokens[1] == TokenView::Keyword(Keyword::Read));
                        assert(tokens[2] == TokenView::Keyword(Keyword::Only));
                        assert(tokens.drop_first().drop_first().drop_first() =~= as_of_toks);
                        assert(as_of_toks.drop_first().drop_first().drop_first().drop_first().drop_first()
                            =~= Seq::<TokenView>::empty());
                    } else {
                        assert(tokens =~= r_prefix + as_of_toks);
                        assert(tokens[1] == TokenView::Keyword(Keyword::As));
                        assert(tokens.drop_first() =~= as_of_toks);
                        assert(as_of_toks.drop_first().drop_first().drop_first().drop_first().drop_first()
                            =~= Seq::<TokenView>::empty());
                    }
                },
            }
        },
        SStmt::DropTable { name, if_exists } => {
            if if_exists {
                assert(tokens[0] == TokenView::Keyword(Keyword::Drop));
                assert(tokens[1] == TokenView::Keyword(Keyword::Table));
                assert(tokens[2] == TokenView::Keyword(Keyword::If));
                assert(tokens[3] == TokenView::Keyword(Keyword::Exists));
                assert(tokens[4] == TokenView::Ident(name));
                assert(tokens.drop_first().drop_first().drop_first().drop_first().drop_first()
                    =~= Seq::<TokenView>::empty());
            } else {
                assert(tokens[0] == TokenView::Keyword(Keyword::Drop));
                assert(tokens[1] == TokenView::Keyword(Keyword::Table));
                assert(tokens[2] == TokenView::Ident(name));
                assert(tokens[2] != TokenView::Keyword(Keyword::If));
                assert(tokens.drop_first().drop_first().drop_first() =~= Seq::<TokenView>::empty());
            }
        },
        SStmt::Delete { table, where_clause } => {
            match where_clause {
                None => {
                    assert(tokens[0] == TokenView::Keyword(Keyword::Delete));
                    assert(tokens[1] == TokenView::Keyword(Keyword::From));
                    assert(tokens[2] == TokenView::Ident(table));
                    assert(tokens.len() == 3);
                    assert(tokens.drop_first().drop_first().drop_first() =~= Seq::<TokenView>::empty());
                },
                Some(e) => {
                    lemma_sparse_sprint(e, Seq::<TokenView>::empty(), fuel);
                    let head = seq![
                        TokenView::Keyword(Keyword::Delete),
                        TokenView::Keyword(Keyword::From),
                        TokenView::Ident(table),
                        TokenView::Keyword(Keyword::Where),
                    ];
                    assert(tokens =~= head + sprint(e));
                    assert(tokens[0] == TokenView::Keyword(Keyword::Delete));
                    assert(tokens[1] == TokenView::Keyword(Keyword::From));
                    assert(tokens[2] == TokenView::Ident(table));
                    assert(tokens[3] == TokenView::Keyword(Keyword::Where));
                    assert(tokens.drop_first().drop_first().drop_first().drop_first() =~= sprint(e));
                    assert(sprint(e) + Seq::<TokenView>::empty() =~= sprint(e));
                },
            }
        },
        SStmt::Explain(inner) => {
            lemma_sparse_stmt_sprint(*inner, (fuel - 1) as nat);
            assert(tokens[0] == TokenView::Keyword(Keyword::Explain));
            assert(tokens.drop_first() =~= sprint_stmt(*inner));
        },
        SStmt::Unsupported => {
            assert(false);
        },
    }
}

/// The canonical mirror statement printer roundtrips at self-supplied fuel.
pub proof fn mirror_roundtrip_stmt(s: SStmt)
    requires printable_stmt(s),
    ensures sparse_stmt(sprint_stmt(s), sdepth_stmt(s)) == (Some(s), Seq::<TokenView>::empty()),
{
    lemma_sparse_stmt_sprint(s, sdepth_stmt(s));
}

/// The canonical mirror statement printer is injective on its printable domain.
pub proof fn mirror_injective_stmt(left: SStmt, right: SStmt)
    requires printable_stmt(left), printable_stmt(right),
    ensures sprint_stmt(left) == sprint_stmt(right) ==> left == right,
{
    if sprint_stmt(left) == sprint_stmt(right) {
        let fuel = if sdepth_stmt(left) >= sdepth_stmt(right) {
            sdepth_stmt(left)
        } else {
            sdepth_stmt(right)
        };
        lemma_sparse_stmt_sprint(left, fuel);
        lemma_sparse_stmt_sprint(right, fuel);
    }
}

} // verus!
