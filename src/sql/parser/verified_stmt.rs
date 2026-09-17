//! Statement-level structural model: the `SStmt` view of `ast::Statement`.
//!
//! This module is the *bridge*, not a parser. It defines `SStmt`/`SFrom`/
//! `SColumn` — `Seq`-based mirrors of the AST whose equality is
//! view-determined — and the `view_*` functions that map an `ast::Statement`
//! onto them. Everything downstream (`verified_minparen_stmt`'s round-trip
//! theorems, `verified_stmt_prec`'s parser) states its contracts over these
//! views.
//!
//! It also carries the two pieces of reasoning the UPDATE arm needs, both
//! about `BTreeMap`'s sorted-key iteration order rather than about syntax:
//! the string-ordering lemmas (`axiom_string_obeys_cmp`, `str_leq`,
//! `lemma_sorted_keys_*`) and the map/assignment-list bijection
//! (`lemma_update_bijection`, `lemma_update_view_boundary`).
//!
//! The fully parenthesized spec grammar that used to live here (`sparse_stmt`,
//! `sparse_select`, ...) is gone: its production twin is
//! `verified_stmt_prec::sparse_control_*`, and the round-trip and injectivity
//! properties it carried are now stated over that parser in
//! `verified_minparen_stmt` (`stmt_min_roundtrip`, `stmt_min_dual`,
//! `stmt_min_print_injective`, `stmt_min_parse_injective`).

// Proof/verification scaffolding, not idiomatic library code: exempt from the
// crate's `warn(clippy::all)` so proof-shaped constructs don't trip `-D warnings`.
#![allow(clippy::all)]

#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use super::verified_production::TokenView;
#[allow(unused_imports)]
use super::verified_roundtrip::SExpr;
// Ghost (spec/proof) helpers: stripped under a plain `cargo build`, so gate the
// imports behind `verus_keep_ghost` to keep the non-Verus build resolving.
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::verified_roundtrip::{view_args, view_expr};
#[allow(unused_imports)]
use super::{Keyword, ast, verified_integer};
#[allow(unused_imports)]
use crate::sql::types::DataType;
#[allow(unused_imports)]
use core::cmp::Ordering;
// `std_specs` is gated behind `verus_keep_ghost`; these trait imports are only
// needed for the `cmp_spec`/`eq_spec` proof helpers below, so gate them too or a
// plain `cargo build`/`cargo test` fails to resolve them.
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use vstd::std_specs::cmp::{OrdSpec, PartialEqSpec, PartialOrdSpec};

verus! {


/// Mirror of `ast::Statement`. Expression children are `SExpr` (via `view_expr`)
/// and containers become `Seq`s. `Unsupported` is the placeholder for statement
pub enum SStmt {
    Begin { read_only: bool, as_of: Option<u64> },
    Commit,
    Rollback,
    CreateTable { name: String, columns: Seq<SColumn> },
    DropTable { name: String, if_exists: bool },
    Delete { table: String, where_clause: Option<SExpr> },
    Insert { table: String, columns: Option<Seq<String>>, values: Seq<Seq<SExpr>> },
    Update { table: String, set: Seq<(String, Option<SExpr>)>, where_clause: Option<SExpr> },
    Select {
        select: Seq<(SExpr, Option<String>)>,
        from: Seq<SFrom>,
        where_clause: Option<SExpr>,
        group_by: Seq<SExpr>,
        having: Option<SExpr>,
        order_by: Seq<(SExpr, ast::Direction)>,
        limit: Option<SExpr>,
        offset: Option<SExpr>,
    },
    Explain(Box<SStmt>),
    Unsupported,
}

pub open spec fn view_select_list(items: Seq<(ast::Expression, Option<String>)>) -> Seq<(SExpr, Option<String>)>
    decreases items,
{
    if items.len() == 0 {
        Seq::empty()
    } else {
        seq![(view_expr(items[0].0), items[0].1)] + view_select_list(items.drop_first())
    }
}

pub open spec fn view_froms(froms: Seq<ast::From>) -> Seq<SFrom>
    decreases froms,
{
    if froms.len() == 0 {
        Seq::empty()
    } else {
        seq![view_from(froms[0])] + view_froms(froms.drop_first())
    }
}

pub open spec fn view_order_list(items: Seq<(ast::Expression, ast::Direction)>) -> Seq<(SExpr, ast::Direction)>
    decreases items,
{
    if items.len() == 0 {
        Seq::empty()
    } else {
        seq![(view_expr(items[0].0), items[0].1)] + view_order_list(items.drop_first())
    }
}

/// View a `Vec<Vec<Expression>>` row list as `Seq<Seq<SExpr>>`.
pub open spec fn view_rows(rows: Seq<Vec<ast::Expression>>) -> Seq<Seq<SExpr>>
    decreases rows,
{
    if rows.len() == 0 {
        Seq::empty()
    } else {
        seq![view_args(rows[0]@)] + view_rows(rows.drop_first())
    }
}

/// Mirror of `ast::Column`: identical except the `default` expression becomes an
/// `SExpr`. `datatype` is carried directly (`DataType` is `Copy` and has an
/// external type spec).
pub struct SColumn {
    pub name: String,
    pub datatype: DataType,
    pub primary_key: bool,
    pub nullable: Option<bool>,
    pub default: Option<SExpr>,
    pub unique: bool,
    pub index: bool,
    pub references: Option<String>,
}

pub open spec fn view_column(c: ast::Column) -> SColumn {
    SColumn {
        name: c.name,
        datatype: c.datatype,
        primary_key: c.primary_key,
        nullable: c.nullable,
        default: match c.default {
            Some(e) => Some(view_expr(e)),
            None => None,
        },
        unique: c.unique,
        index: c.index,
        references: c.references,
    }
}

pub open spec fn view_columns(cols: Seq<ast::Column>) -> Seq<SColumn>
    decreases cols,
{
    if cols.len() == 0 {
        Seq::empty()
    } else {
        seq![view_column(cols[0])] + view_columns(cols.drop_first())
    }
}

/// Structural view of a production statement as a mirror statement.
pub open spec fn view_stmt(s: ast::Statement) -> SStmt
    decreases s,
{
    match s {
        ast::Statement::Begin { read_only, as_of } => SStmt::Begin { read_only, as_of },
        ast::Statement::Commit => SStmt::Commit,
        ast::Statement::Rollback => SStmt::Rollback,
        ast::Statement::CreateTable { name, columns } =>
            SStmt::CreateTable { name, columns: view_columns(columns@) },
        ast::Statement::DropTable { name, if_exists } => SStmt::DropTable { name, if_exists },
        ast::Statement::Delete { table, where_clause } => SStmt::Delete {
            table,
            where_clause: match where_clause {
                Some(e) => Some(view_expr(e)),
                None => None,
            },
        },
        ast::Statement::Insert { table, columns, values } => SStmt::Insert {
            table,
            columns: match columns {
                Some(cols) => Some(cols@),
                None => None,
            },
            values: view_rows(values@),
        },
        ast::Statement::Select {
            select, from, where_clause, group_by, having, order_by, limit, offset,
        } => SStmt::Select {
            select: view_select_list(select@),
            from: view_froms(from@),
            where_clause: match where_clause {
                Some(e) => Some(view_expr(e)),
                None => None,
            },
            group_by: view_args(group_by@),
            having: match having {
                Some(e) => Some(view_expr(e)),
                None => None,
            },
            order_by: view_order_list(order_by@),
            limit: match limit {
                Some(e) => Some(view_expr(e)),
                None => None,
            },
            offset: match offset {
                Some(e) => Some(view_expr(e)),
                None => None,
            },
        },
        // S4: `Update.set` is a `BTreeMap`, whose spec view is an *unordered*
        // `Map`. The ghost `order` (built by the executable, sorted-`iter()`
        // bridge) recovers the canonical assignment ordering, so `view_update_arm`
        // is total over multi-assignment UPDATEs: when `order` is a valid
        // bijection over `set` (`wf_update`) it builds the sorted mirror
        // sequence; it only falls to `Unsupported` for a malformed `order`.
        ast::Statement::Update { table, set, order, where_clause } =>
            view_update_arm(table, set@, order@, where_clause),
        ast::Statement::Explain(inner) => SStmt::Explain(Box::new(view_stmt(*inner))),
        _ => SStmt::Unsupported,
    }
}

/// Well-formedness of an UPDATE's ghost `order` against its `set` map: the
/// order lists each assigned column exactly once (`no_dups`) and lists all of
/// them and only them (`order.to_set() == set.dom()`). Together with the value
/// map this is a bijection `Seq<(String, Option<SExpr>)> <-> Map<...>` on the
/// UPDATE assignment set (see `lemma_update_bijection`).
pub open spec fn wf_update(
    set: vstd::map::Map<String, Option<ast::Expression>>,
    order: Seq<String>,
) -> bool {
    &&& order.no_duplicates()
    &&& order.to_set() == set.dom()
}

/// Build the mirror assignment sequence from the ghost `order`: read the keys in
/// `order` and pair each with its value from `set`. Total (no `dom().choose()`,
/// no `len == 1` special case) when `wf_update(set, order)` holds.
pub open spec fn view_update_assigns(
    set: vstd::map::Map<String, Option<ast::Expression>>,
    order: Seq<String>,
) -> Seq<(String, Option<SExpr>)> {
    order.map_values(|k: String| (k, view_opt(set[k])))
}

pub open spec fn view_update_arm(
    table: String,
    set: vstd::map::Map<String, Option<ast::Expression>>,
    order: Seq<String>,
    where_clause: Option<ast::Expression>,
) -> SStmt {
    if wf_update(set, order) {
        SStmt::Update {
            table,
            set: view_update_assigns(set, order),
            where_clause: view_opt(where_clause),
        }
    } else {
        SStmt::Unsupported
    }
}

//
// A `From` item is a left-deep join tree whose right child is always a table.

pub struct SJoinStep {
    pub join_type: ast::JoinType,
    pub right: SFrom,
    pub predicate: Option<SExpr>,
}

pub enum SFrom {
    Table { name: String, alias: Option<String> },
    Join { left: Box<SFrom>, right: Box<SFrom>, join_type: ast::JoinType, predicate: Option<SExpr> },
}

pub open spec fn view_from(f: ast::From) -> SFrom
    decreases f,
{
    match f {
        ast::From::Table { name, alias } => SFrom::Table { name, alias },
        ast::From::Join { left, right, join_type, predicate } => SFrom::Join {
            left: Box::new(view_from(*left)),
            right: Box::new(view_from(*right)),
            join_type,
            predicate: match predicate {
                Some(e) => Some(view_expr(e)),
                None => None,
            },
        },
    }
}

pub open spec fn from_head(f: SFrom) -> SFrom
    decreases f,
{
    match f {
        SFrom::Table { .. } => f,
        SFrom::Join { left, .. } => from_head(*left),
    }
}

pub open spec fn from_steps(f: SFrom) -> Seq<SJoinStep>
    decreases f,
{
    match f {
        SFrom::Table { .. } => Seq::empty(),
        SFrom::Join { left, right, join_type, predicate } =>
            from_steps(*left) + seq![SJoinStep { join_type, right: *right, predicate }],
    }
}

pub open spec fn apply_step(acc: SFrom, step: SJoinStep) -> SFrom {
    SFrom::Join {
        left: Box::new(acc),
        right: Box::new(step.right),
        join_type: step.join_type,
        predicate: step.predicate,
    }
}

pub open spec fn fold_joins(head: SFrom, steps: Seq<SJoinStep>) -> SFrom
    decreases steps,
{
    if steps.len() == 0 {
        head
    } else {
        fold_joins(apply_step(head, steps[0]), steps.drop_first())
    }
}

pub open spec fn is_cross(jt: ast::JoinType) -> bool {
    match jt {
        ast::JoinType::Cross => true,
        _ => false,
    }
}

#[verifier::external_body]
pub proof fn axiom_string_obeys_cmp()
    ensures vstd::laws_cmp::obeys_cmp::<String>(),
{
}

/// Trusted: `String`'s `PartialEq` is by-value, so `eq_spec` coincides with `==`
/// (`obeys_concrete_eq`). Needed to turn `cmp_spec(x, y) is Equal` into `x == y`
/// when proving the key order is a *total ordering* (antisymmetry).
#[verifier::external_body]
pub proof fn axiom_string_concrete_eq()
    ensures vstd::laws_eq::obeys_concrete_eq::<String>(),
{
}

/// Non-strict key order on `String`, derived from the `Ord` model: `a <= b` iff
/// `a.cmp_spec(&b)` is `Less` or `Equal`. This is the total order the sorted
/// canonical UPDATE-assignment form is sorted by; it matches vstd's BTreeMap
/// `increasing_seq` (which uses the *strict* `is Less`) on distinct keys.
pub open spec fn str_leq(a: String, b: String) -> bool {
    a.cmp_spec(&b) is Less
        || a.cmp_spec(&b) is Equal
}

/// `str_leq` is a total ordering (reflexive, antisymmetric, transitive,
/// strongly-connected) — the precondition of `Seq::sort_by` / `lemma_sorted_unique`.
pub proof fn lemma_str_leq_total_ordering()
    ensures vstd::relations::total_ordering(|a: String, b: String| str_leq(a, b)),
{
    axiom_string_obeys_cmp();
    axiom_string_concrete_eq();
    let leq = |a: String, b: String| str_leq(a, b);
    reveal(vstd::laws_cmp::obeys_cmp_ord);
    reveal(vstd::laws_cmp::obeys_partial_cmp_spec_properties);
    reveal(vstd::laws_eq::obeys_concrete_eq);
    // partial_cmp_spec(x, y) == Some(cmp_spec(x, y)) for all x, y.
    assert forall|x: String, y: String|
        x.partial_cmp_spec(&y) == Some(x.cmp_spec(&y)) by {}
    // reflexive: cmp_spec(x, x) is Equal (via eq_spec reflexivity).
    assert(vstd::relations::reflexive(leq)) by {
        assert forall|x: String| #[trigger] leq(x, x) by {
            assert(x.eq_spec(&x));
            assert(x.partial_cmp_spec(&x) == Some(core::cmp::Ordering::Equal));
        }
    }
    // strongly_connected: for all x, y, leq(x, y) || leq(y, x).
    assert(vstd::relations::strongly_connected(leq)) by {
        assert forall|x: String, y: String| #[trigger] leq(x, y) || #[trigger] leq(y, x) by {
            match x.cmp_spec(&y) {
                core::cmp::Ordering::Less => {},
                core::cmp::Ordering::Equal => {},
                core::cmp::Ordering::Greater => {
                    assert(x.partial_cmp_spec(&y) == Some(core::cmp::Ordering::Greater));
                    assert(y.partial_cmp_spec(&x) == Some(core::cmp::Ordering::Less));
                    assert(y.cmp_spec(&x) is Less);
                },
            }
        }
    }
    // antisymmetric: leq(x, y) && leq(y, x) ==> x == y (both non-Greater forces Equal).
    assert(vstd::relations::antisymmetric(leq)) by {
        assert forall|x: String, y: String| #[trigger] leq(x, y) && #[trigger] leq(y, x)
            implies x == y by {
            // Neither can be Less (Less on one side forces Greater on the other,
            // contradicting the other leq), so both are Equal.
            if x.cmp_spec(&y) is Less {
                assert(x.partial_cmp_spec(&y) == Some(core::cmp::Ordering::Less));
                assert(y.partial_cmp_spec(&x) == Some(core::cmp::Ordering::Greater));
                assert(y.cmp_spec(&x) is Greater);
                assert(false);
            }
            assert(x.cmp_spec(&y) is Equal);
            assert(x.partial_cmp_spec(&y) == Some(core::cmp::Ordering::Equal));
            assert(x.eq_spec(&y));
            assert(x == y);
        }
    }
    // transitive: leq(x, y) && leq(y, z) ==> leq(x, z).
    assert(vstd::relations::transitive(leq)) by {
        assert forall|x: String, y: String, z: String| #[trigger] leq(x, y) && #[trigger] leq(y, z)
            implies leq(x, z) by {
            // Reduce to partial_cmp_spec facts. leq(a, b) <==> !(b < a).
            if x.cmp_spec(&z) is Greater {
                assert(x.partial_cmp_spec(&z) == Some(core::cmp::Ordering::Greater));
                assert(z.partial_cmp_spec(&x) == Some(core::cmp::Ordering::Less));
                // z < x with x <= y and y <= z contradicts transitivity of <.
                if x.cmp_spec(&y) is Equal {
                    assert(x.eq_spec(&y));
                    // x == y, so z < x means z < y, but y <= z.
                    assert(x == y);
                    if y.cmp_spec(&z) is Equal {
                        assert(y.eq_spec(&z));
                        assert(y == z);
                        assert(false);
                    } else {
                        assert(y.partial_cmp_spec(&z) == Some(core::cmp::Ordering::Less));
                        assert(z.partial_cmp_spec(&x) == Some(core::cmp::Ordering::Less));
                        // y < z and z < x=y ==> y < y, contradiction with reflexive Equal.
                        assert(z.partial_cmp_spec(&y) == Some(core::cmp::Ordering::Less));
                        assert(y.partial_cmp_spec(&y) == Some(core::cmp::Ordering::Less));
                        assert(y.eq_spec(&y));
                        assert(false);
                    }
                } else {
                    assert(x.partial_cmp_spec(&y) == Some(core::cmp::Ordering::Less));
                    if y.cmp_spec(&z) is Equal {
                        assert(y.eq_spec(&z));
                        assert(y == z);
                        // x < y=z and z < x ==> x < x.
                        assert(z.partial_cmp_spec(&x) == Some(core::cmp::Ordering::Less));
                        assert(x.partial_cmp_spec(&x) == Some(core::cmp::Ordering::Less));
                        assert(x.eq_spec(&x));
                        assert(false);
                    } else {
                        assert(y.partial_cmp_spec(&z) == Some(core::cmp::Ordering::Less));
                        // x < y and y < z ==> x < z, contradicting z < x.
                        assert(x.partial_cmp_spec(&z) == Some(core::cmp::Ordering::Less));
                        assert(false);
                    }
                }
            }
        }
    }
}

/// Sort a key list into ascending `str_leq` order. Used to canonicalise an
/// UPDATE's assignment order so it matches the sorted `BTreeMap::iter()` walk of
/// the executable printer, independent of parse order.
pub open spec fn sorted_keys(keys: Seq<String>) -> Seq<String> {
    keys.sort_by(|a: String, b: String| str_leq(a, b))
}

/// A key sequence that is already sorted (distinct + `increasing_seq`) is a fixed
/// point of `sorted_keys`: sorting it is the identity. This is the "sort is
/// identity on already-sorted keys" idempotence used by the UPDATE roundtrip.
pub proof fn lemma_sorted_keys_idempotent(keys: Seq<String>)
    requires
        keys.no_duplicates(),
        vstd::std_specs::btree::increasing_seq(keys),
    ensures
        sorted_keys(keys) == keys,
{
    axiom_string_obeys_cmp();
    broadcast use vstd::std_specs::btree::axiom_increasing_seq_meaning;
    lemma_str_leq_total_ordering();
    let leq = |a: String, b: String| str_leq(a, b);
    // `keys` is already `sorted_by(leq)`: increasing_seq gives strict Less on i<j.
    assert(vstd::relations::sorted_by(keys, leq)) by {
        assert forall|i: int, j: int| 0 <= i < j < keys.len()
            implies #[trigger] leq(keys[i], keys[j]) by {
            assert(keys[i].cmp_spec(&keys[j]) is Less);
        }
    }
    // `sorted_keys(keys)` is sorted and a permutation of `keys` (same multiset).
    keys.lemma_sort_by_ensures(leq);
    assert(vstd::relations::sorted_by(keys.sort_by(leq), leq));
    assert(keys.to_multiset() =~= keys.sort_by(leq).to_multiset());
    // Two sorted sequences with the same multiset are equal.
    vstd::seq_lib::lemma_sorted_unique(keys, keys.sort_by(leq), leq);
}

/// Sorting a distinct key sequence yields a permutation that is still distinct,
/// covers the same set of keys, has the same length, and is `increasing_seq`
/// (strictly ascending, since distinct). These are the facts needed to prove
/// `wf_update(set, sorted_keys(order))` and to feed `printable_stmt`.
pub proof fn lemma_sorted_keys_props(keys: Seq<String>)
    requires
        keys.no_duplicates(),
    ensures
        sorted_keys(keys).len() == keys.len(),
        sorted_keys(keys).to_multiset() == keys.to_multiset(),
        sorted_keys(keys).to_set() == keys.to_set(),
        sorted_keys(keys).no_duplicates(),
        vstd::std_specs::btree::increasing_seq(sorted_keys(keys)),
{
    axiom_string_obeys_cmp();
    broadcast use vstd::std_specs::btree::axiom_increasing_seq_meaning;
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    lemma_str_leq_total_ordering();
    let leq = |a: String, b: String| str_leq(a, b);
    let s = sorted_keys(keys);
    keys.lemma_sort_by_ensures(leq);
    // Same multiset (permutation) => same length and same element set.
    assert(s.to_multiset() =~= keys.to_multiset());
    s.to_multiset_ensures();
    keys.to_multiset_ensures();
    assert(s.len() == s.to_multiset().len());
    assert(keys.len() == keys.to_multiset().len());
    assert(s.len() == keys.len());
    assert(s.to_set() =~= keys.to_set()) by {
        assert forall|k: String| s.to_set().contains(k) <==> keys.to_set().contains(k) by {
            if s.to_set().contains(k) {
                assert(s.contains(k));
                assert(s.to_multiset().count(k) > 0);
                assert(keys.to_multiset().count(k) > 0);
                assert(keys.contains(k));
            }
            if keys.to_set().contains(k) {
                assert(keys.contains(k));
                assert(keys.to_multiset().count(k) > 0);
                assert(s.to_multiset().count(k) > 0);
                assert(s.contains(k));
            }
        }
    }
    // Distinctness is preserved through the shared multiset.
    keys.lemma_multiset_has_no_duplicates();
    assert(s.no_duplicates()) by {
        s.lemma_multiset_has_no_duplicates_conv();
    }
    // sorted_by + distinct => strict Less on i<j => increasing_seq.
    assert(vstd::relations::sorted_by(s, leq));
    assert(vstd::std_specs::btree::increasing_seq(s)) by {
        assert forall|i: int, j: int| 0 <= i < j < s.len()
            implies #[trigger] s[i].cmp_spec(&s[j]) is Less by {
            assert(leq(s[i], s[j]));
            assert(s[i] != s[j]) by {
                s.lemma_multiset_has_no_duplicates();
            }
            // leq && distinct => strict Less (Equal would force eq_spec, hence ==).
            if s[i].cmp_spec(&s[j]) is Equal {
                axiom_string_concrete_eq();
                reveal(vstd::laws_cmp::obeys_cmp_ord);
                reveal(vstd::laws_eq::obeys_concrete_eq);
                assert(s[i].partial_cmp_spec(&s[j]) == Some(Ordering::Equal));
                reveal(vstd::laws_cmp::obeys_partial_cmp_spec_properties);
                assert(s[i].eq_spec(&s[j]));
                assert(s[i] == s[j]);
                assert(false);
            }
        }
    }
}

/// Two strictly-ascending (`increasing_seq`), distinct key sequences over the
/// same element set are equal. Used to identify the parser's sorted `order@` with
/// the sorted key projection of the executable printer's `BTreeMap::iter()` walk.
pub proof fn lemma_increasing_seq_eq(a: Seq<String>, b: Seq<String>)
    requires
        a.no_duplicates(),
        b.no_duplicates(),
        vstd::std_specs::btree::increasing_seq(a),
        vstd::std_specs::btree::increasing_seq(b),
        a.to_set() == b.to_set(),
    ensures
        a == b,
{
    axiom_string_obeys_cmp();
    broadcast use vstd::std_specs::btree::axiom_increasing_seq_meaning;
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    lemma_str_leq_total_ordering();
    let leq = |a1: String, b1: String| str_leq(a1, b1);
    // Both are `sorted_by(leq)` (strict Less implies leq).
    assert(vstd::relations::sorted_by(a, leq)) by {
        assert forall|i: int, j: int| 0 <= i < j < a.len() implies #[trigger] leq(a[i], a[j]) by {
            assert(a[i].cmp_spec(&a[j]) is Less);
        }
    }
    assert(vstd::relations::sorted_by(b, leq)) by {
        assert forall|i: int, j: int| 0 <= i < j < b.len() implies #[trigger] leq(b[i], b[j]) by {
            assert(b[i].cmp_spec(&b[j]) is Less);
        }
    }
    // Same set + distinct => same multiset.
    a.lemma_multiset_has_no_duplicates();
    b.lemma_multiset_has_no_duplicates();
    assert(a.to_multiset() =~= b.to_multiset()) by {
        assert forall|x: String| a.to_multiset().count(x) == b.to_multiset().count(x) by {
            a.to_multiset_ensures();
            b.to_multiset_ensures();
            if a.to_set().contains(x) {
                assert(a.contains(x));
                assert(b.contains(x));
            } else {
                assert(!a.contains(x));
                assert(!b.to_set().contains(x));
                assert(!b.contains(x));
            }
        }
    }
    vstd::seq_lib::lemma_sorted_unique(a, b, leq);
}

pub open spec fn view_opt(v: Option<ast::Expression>) -> Option<SExpr> {
    match v {
        Some(e) => Some(view_expr(e)),
        None => None,
    }
}

pub open spec fn view_assign_pairs(items: Seq<(String, Option<ast::Expression>)>)
    -> Seq<(String, Option<SExpr>)> {
    items.map_values(|kv: (String, Option<ast::Expression>)| (kv.0, view_opt(kv.1)))
}

pub proof fn view_assign_pairs_index(items: Seq<(String, Option<ast::Expression>)>)
    ensures
        view_assign_pairs(items).len() == items.len(),
        forall|i: int| 0 <= i < items.len() ==> #[trigger] view_assign_pairs(items)[i]
            == (items[i].0, view_opt(items[i].1)),
{
}

/// The keys of the parser's ghost `done` sequence.
pub open spec fn done_keys(items: Seq<(String, Option<ast::Expression>)>) -> Seq<String> {
    items.map_values(|kv: (String, Option<ast::Expression>)| kv.0)
}

/// Bijection lemma: under the parser's assignment invariants (distinct keys +
/// key set == map domain), the ghost `order = done_keys(items)` is well-formed
/// (`wf_update`) and reading the map back through `order` reproduces exactly the
/// ordered assignment sequence `view_assign_pairs(items)`.
///
/// This is the Seq <-> Map bijection on the UPDATE assignment set:
///   * soundness    — `order.no_duplicates()` and every listed key is a real
///                    assignment (`order.to_set() subset set.dom()`);
///   * completeness — every assignment is listed (`set.dom() subset
///                    order.to_set()`);
/// together giving `order.to_set() == set.dom()` and, with the value map,
/// `view_update_assigns(set, order) == view_assign_pairs(items)`.
#[verifier::spinoff_prover]
#[verifier::rlimit(60000)]
pub proof fn lemma_update_bijection(
    set: vstd::map::Map<String, Option<ast::Expression>>,
    items: Seq<(String, Option<ast::Expression>)>,
)
    requires
        set.dom().finite(),
        forall|i: int, j: int| 0 <= i < j < items.len() ==> items[i].0 != items[j].0,
        forall|i: int| 0 <= i < items.len() ==> #[trigger] set.dom().contains(items[i].0)
            && set[items[i].0] == items[i].1,
        forall|k: String| set.dom().contains(k)
            ==> exists|i: int| 0 <= i < items.len() && (#[trigger] items[i]).0 == k,
    ensures
        wf_update(set, done_keys(items)),
        view_update_assigns(set, done_keys(items)) == view_assign_pairs(items),
{
    let order = done_keys(items);
    assert(order.len() == items.len());
    assert forall|i: int| 0 <= i < order.len() implies #[trigger] order[i] == items[i].0 by {}
    // soundness: no_duplicates.
    assert(order.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < order.len() && 0 <= j < order.len()
            && i != j implies order[i] != order[j] by {
            if i < j {
                assert(items[i].0 != items[j].0);
            } else {
                assert(items[j].0 != items[i].0);
            }
        }
    }
    // order.to_set() == set.dom(), both directions.
    assert(order.to_set() =~= set.dom()) by {
        assert forall|k: String| order.to_set().contains(k) implies set.dom().contains(k) by {
            let i = choose|i: int| 0 <= i < order.len() && order[i] == k;
            assert(order[i] == items[i].0);
            assert(set.dom().contains(items[i].0));
        }
        assert forall|k: String| set.dom().contains(k) implies order.to_set().contains(k) by {
            let i = choose|i: int| 0 <= i < items.len() && items[i].0 == k;
            assert(order[i] == k);
        }
    }
    // value agreement: view_update_assigns(set, order) == view_assign_pairs(items).
    view_assign_pairs_index(items);
    assert(view_update_assigns(set, order) =~= view_assign_pairs(items)) by {
        assert(view_update_assigns(set, order).len() == items.len());
        assert(view_assign_pairs(items).len() == items.len());
        assert forall|i: int| 0 <= i < items.len() implies
            #[trigger] view_update_assigns(set, order)[i] == view_assign_pairs(items)[i] by {
            assert(view_update_assigns(set, order)[i] == (order[i], view_opt(set[order[i]])));
            assert(order[i] == items[i].0);
            assert(set.dom().contains(items[i].0) && set[items[i].0] == items[i].1);
            assert(view_assign_pairs(items)[i] == (items[i].0, view_opt(items[i].1)));
        }
    }
}

/// Boundary lemma used by the verified parser: with `order = done_keys(items)`,
/// the total `view_update_arm` equals the mirror `Update` built from the ordered
/// assignment list. No `len == 1` special case — this now covers multi-assign.
#[verifier::spinoff_prover]
#[verifier::rlimit(60000)]
#[verifier::reach_root]
pub proof fn lemma_update_view_boundary(
    table: String,
    set: vstd::map::Map<String, Option<ast::Expression>>,
    items: Seq<(String, Option<ast::Expression>)>,
    where_clause: Option<ast::Expression>,
)
    requires
        set.dom().finite(),
        forall|i: int, j: int| 0 <= i < j < items.len() ==> items[i].0 != items[j].0,
        forall|i: int| 0 <= i < items.len() ==> #[trigger] set.dom().contains(items[i].0)
            && set[items[i].0] == items[i].1,
        forall|k: String| set.dom().contains(k)
            ==> exists|i: int| 0 <= i < items.len() && (#[trigger] items[i]).0 == k,
    ensures
        view_update_arm(table, set, done_keys(items), where_clause)
            == (SStmt::Update {
                table,
                set: view_assign_pairs(items),
                where_clause: view_opt(where_clause),
            }),
{
    lemma_update_bijection(set, items);
    let order = done_keys(items);
    assert(wf_update(set, order));
    assert(view_update_arm(table, set, order, where_clause)
        == SStmt::Update {
            table,
            set: view_update_assigns(set, order),
            where_clause: view_opt(where_clause),
        });
}

} // verus!
