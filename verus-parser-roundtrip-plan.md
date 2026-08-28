# toyDB SQL parser: Verus roundtrip verification plan

Status: **E0-E4 complete; statement roundtrip S0-S5 complete (2026-08-28)**
— the full expression-grammar roundtrip is verified end to end; the statement
*mirror* roundtrip is verified for all 10 `ast::Statement` kinds (S0-S4); and the
*executable* print+parse layer (S5) is now verified for **all 10 kinds** both
directions, with end-to-end roundtrip headlines (a unified one over 8 kinds plus
standalone `print_parse_roundtrip_select` and `print_parse_roundtrip_update`), in
`src/sql/parser/verified_stmt.rs` (142 verified / 0 errors under `verify.sh`).
`Update`'s `BTreeMap` set was unblocked with a single trusted axiom,
`axiom_string_key_obeys_cmp` (`String`'s `Ord` obeys the cmp laws — analogous to
the `float_trust` assumptions). Phase 4 (production cutover) is not started.
Owner: kg (parser). Verified module opt-in via `scripts/verus/verify.sh`.

## Statement layer status (2026-08-27)

`src/sql/parser/verified_stmt.rs` (opted into `verify.sh`, 64 verified / 0 errors
under `--verify-module sql::parser::verified_stmt`) carries the `SStmt` mirror in
the same style as the expression layer, with an `SStmt::Unsupported` catch-all so
`view_stmt` stays total as the enum grows. Done:

- **S0/S1 — list-free statements.** `Begin` (READ ONLY / AS OF SYSTEM TIME),
  `Commit`, `Rollback`, `DropTable` (IF EXISTS), `Explain` (forbids nesting),
  `Delete` (optional WHERE in the verified expression domain). Mirror roundtrip
  `lemma_sparse_stmt_sprint` + `mirror_injective_stmt`.
- **S2 — CreateTable.** Full column codec (name, datatype, PRIMARY KEY,
  NULL/NOT NULL, UNIQUE, INDEX, REFERENCES, DEFAULT-last with an embedded
  expression). The 6 optional clauses use `#[verifier::opaque]` parse helpers +
  cheap per-clause "peel" lemmas to avoid a combinatorial solver blowup.
- **S3 — Insert + Select.**
  - `Insert`: optional column-name list + nested `VALUES` rows
    (`Seq<Seq<SExpr>>`, two-level comma-list lemma).
  - `Select`: select-list (exprs with optional `AS` alias, `*` unaliased),
    `FROM` join-tree list, and `WHERE`. The **FROM join tree** is the plan's
    flagged risk item: rather than fight left-recursion, `SFrom` is decomposed
    into (head table, forward join-step list) via `from_head`/`from_steps` and
    reassembled with `fold_joins`; `fold_decomp`/`sprint_decomp` prove the
    identities, and the parser reads head + forward step-list then folds.
  - **Remaining in Select:** the clauses `GROUP BY` / `HAVING` / `ORDER BY` /
    `LIMIT` / `OFFSET` are currently constrained empty/None by `printable_stmt`;
    each is one more optional clause (an expr, an expr-list, or an
    expr+Direction list) over the machinery already proven — no new obstacle.

- **S4 — Update (mirror done; multi-assignment view bridge is the residual).**
  The SET-list mirror roundtrip needs no `BTreeMap`: `SStmt::Update` carries
  `set: Seq<(String, Option<SExpr>)>` and the assignment codec (`k = expr` /
  `k = DEFAULT`, value parsed expr-first with a `DEFAULT` fallback so no
  `sprint(e)[0] != DEFAULT` fact is needed) roundtrips like any comma list.
  `view_stmt` bridges the production `BTreeMap` for the **single-assignment**
  case (`dom().len()==1`) via `dom().choose()` — no ordering. **Residual:**
  multi-assignment maps still map to `Unsupported`; the general bridge needs the
  *executable* sorted `iter()` (vstd's `increasing_seq`) and a view-level
  headline over `Map` equality (which vstd supports, unlike `BTreeMap` `==`).

All 10 statement kinds now have verified **mirror** roundtrips
(`lemma_sparse_stmt_sprint`, 72 verified / 0 errors).

**S5 — executable statement layer + headline (9/10 kinds done).**
Executable print+parse verified for **9 of 10 statement kinds**, both directions,
refining `sprint_stmt`/`sparse_stmt` at `view_stmt` (133 verified / 0 errors):
- **Begin, Commit, Rollback, DropTable, Delete, Explain** — `parse_begin_exec`,
  inline flat kinds, recursive Explain.
- **CreateTable** — `print_column_exec` (per-segment clause helpers avoid the
  6-clause solver blowup) + `print_columns_slice`/`print_createtable_exec`, and
  `parse_column_exec` (concrete keyword helpers connect the exec match to the
  opaque `sparse_column`) + `parse_columns_exec`/`parse_createtable_exec`.
- **Insert** — name-list + nested VALUES rows, both directions.
- **Select** — `print_from_exec` (recursive join tree) + from-list + select-list
  + `print_select_exec`; and `parse_from_item_exec` (a fold accumulator that
  rebuilds the left-deep tree, refining the opaque `sparse_from`) + from-list +
  select-list + `parse_select_exec`.
- **Unified dispatcher + end-to-end headline** `print_parse_roundtrip_stmt_full`
  (`print_stmt_full_exec` + `parse_stmt_full_exec`) covers the **8** list-free +
  CreateTable + Insert kinds end to end; fuel = token count, bounded by
  `full_sdepth_le_len`. Select is verified standalone both directions but not
  folded into the self-contained headline: `sdepth_stmt(Select)` over-counts
  relative to its single `SELECT` keyword of slack (e.g. `SELECT 1` has
  `sdepth 4`, print length 2), so the headline would need a doubled fuel bound
  (`sdepth_stmt(s) <= 2*sprint_stmt(s).len()`) plus a from-tree `steps_depth`
  length bound — a mechanical extension, not attempted here.

**S5 — Update (DONE, 2026-08-28).** The `BTreeMap` barrier was pinned by a
verified probe (vstd's `BTreeMap` `insert` view and `iter` spec are both gated on
`key_obeys_cmp_spec::<String>()`, which vstd does not prove for `String`) and then
unblocked with one trusted axiom, `axiom_string_key_obeys_cmp` (`String`'s `Ord`
is a genuine total order obeying the cmp laws — analogous to the `float_trust`
assumptions; grows the audited trust surface by exactly one). On top of it:
- `build_one_entry_map(k,v)` proves `m@ == Map::empty().insert(k,v)` (parse side).
- `extract_one_entry(m)` pulls the sole `(k,v)` via `iter().next()` — the `next`
  spec pops `remaining()[0]`, and for a one-entry map the `iter` spec pins it to
  the map (print side; key cloned value-exact, value borrowed to dodge the
  `Option<Expression>` deep-clone relation).
- `print_update_exec` / `parse_assign_exec` / `parse_update_exec` +
  `lemma_sparse_update_sprint` + `update_sdepth_le_len` +
  `print_parse_roundtrip_update` give the single-assignment `UPDATE` roundtrip.
  Multi-assignment (trailing comma) is outside `view_stmt`'s domain and is
  rejected as the relaxed `None` disjunct (`lemma_sparse_set_list_len`).

`stmt_injective` for the whole grammar remains outstanding (not required for the
roundtrip). The Select-into-unified-headline fuel doubling is still the one
mechanical extension left within S5 (Select is verified standalone).

**Phase 4 — production cutover** is not started, and has a hard prerequisite that
S5 does not yet satisfy. The verified executable parsers are *sound but
incomplete*: they accept only the `printable_stmt` domain (Select without
`GROUP BY`/`HAVING`/`ORDER BY`/`LIMIT`/`OFFSET`, single-assignment `Update`, no
`JOIN` types). The production SQL suite (`tests/scripts/queries`) uses `GROUP BY`
and `ORDER BY`, so a straight swap of `parser.rs`'s recursive descent for
`parse_stmt_full_exec` would make those queries fail — a regression, not a cutover.
A fast-path-with-fallback would work around it but is exactly the "digital twin"
the plan rules out (two implementations, differential behaviour).

So a sound *single-implementation* cutover is gated on first extending the
verified parser to the full production grammar:
1. **Finish Select** — the five remaining clauses (`GROUP BY` expr-list, `HAVING`
   expr, `ORDER BY` expr+Direction list, `LIMIT`/`OFFSET` expr), each one more
   optional clause over machinery already proven.
2. **Join types** — `INNER`/`LEFT`/`RIGHT`/`CROSS`/`FULL` in the FROM tree
   (currently the mirror carries the plain join; the typed variants need the
   keyword prefixes threaded through `sprint_from`/`sparse_from`).
3. **Multi-assignment Update** — the sorted-`iter()` bridge over `Map` equality
   (the general case `extract_one_entry` was built for the singleton).
4. **Byte-cursor lexer** — `verified.rs::next_token` as it stands is a **Phase 0
   toy** (its own 25-variant `Token`; single-digit integers via `b-48`,
   single-byte keywords `t`/`f`/`n`), so it cannot tokenize real SQL. Item 4 is
   therefore "build a production-capable verified byte-cursor lexer" (multi-char
   numbers, identifiers, quoted strings, the full `Keyword` set) plus the
   token-stream equivalence argument — not a retarget of the existing skeleton.

Only then does the parser swap keep the suite green. Items 1-3 are verification
work in the established mirror+exec style; item 4 is a full verified lexer.
Verified by reading the code (2026-08-28): the exec parsers accept a strict
`printable_stmt` subset, and the sole verified scanner is the Phase 0 skeleton —
so no sound single-implementation cutover is available without this work, and any
partial swap regresses `tests/scripts/queries` (which uses `GROUP BY`/`ORDER BY`).

**SMT wall cleared + GROUP BY landed end-to-end (2026-08-28).** The module-scale
wall is fixed and the first Select clause is done, both directions, 147 verified /
0 errors, full 17-module suite green:
- *Enablers:* `sprint_select_body`/`sdepth_select_body` (opaque) hold the Select
  clause structure; `sprint_column`/`sprint_columns`/`slist_depth_columns` are now
  opaque with local reveals in the six column lemmas/printers — this pulled the
  6-clause column body out of every unrelated proof's background, the root cause of
  the fragility. Grammar can now grow without tipping the CreateTable lemma.
- *`GROUP BY` mirror:* `sparse_where_group` (opaque helper + roundtrip lemma) parses
  the `[WHERE][GROUP BY]` tail; `sparse_expr_list` (boundary-terminated bare-expr
  comma-list, opaque) is its item parser; the Select roundtrip lemma composes them;
  `printable_stmt` relaxed to `all_printable_se(group_by)`.
- *`GROUP BY` exec:* `print_select_exec` emits the clause via `print_args_slice`;
  `parse_expr_list_exec` (refines `sparse_expr_list`) + `parse_where_group_exec`
  (refines `sparse_where_group`) parse it; `parse_select_exec` composes them.

**The recipe for the remaining four clauses is now proven.** `HAVING`/`LIMIT`/
`OFFSET` are single optional exprs (like the WHERE half of `sparse_where_group`);
`ORDER BY` is `sparse_expr_list` plus a per-item ASC/DESC direction. Each extends
`sprint_select_body`/`sdepth_select_body`/`sparse_where_group` (opaque, so no
column-lemma regression) + the Select lemma + the two exec parsers.

**HAVING landed (2026-08-28, 147 verified), LIMIT/OFFSET blocked by residual column
fragility.** `HAVING` went in mirror+exec on the first proof attempt — the recipe
generalises with zero new debugging. Factored the single-clause parse into a shared
`sparse_kw_expr(r, kw, fuel)` helper + `lemma_sparse_kw_expr_sprint` (one clause,
arbitrary boundary tail; used for WHERE/HAVING/LIMIT/OFFSET). The `LIMIT`+`OFFSET`
extension (5-tuple `sparse_where_group`, threading each clause's tail as the
subsequent clauses) *verified its own lemma* but re-tipped `lemma_sparse_column_sprint`
into the "expected rlimit-count" solver crash — that lemma `reveal`s the 6-clause
`sprint_column`, and the added module bulk crossed the crash threshold (unresponsive
to rlimit). **The scaling fix is `#[verifier::spinoff_prover]`, not opacity or a module split
(2026-08-28).** Ruled out col_*_toks opacity (the column lemma `reveal`s all six
regardless, so it doesn't shrink that lemma's query). The real fix for a heavy
lemma hitting the "expected rlimit-count" crash is `#[verifier::spinoff_prover]`,
which verifies it in a fresh solver instance with a minimal context — committed on
`lemma_sparse_column_sprint` (no module split needed). With that, the **entire
LIMIT/OFFSET *mirror* side verifies for all five clauses**: 5-tuple
`sparse_where_group` via the shared `sparse_kw_expr`/`kw_expr_part` helpers +
`lemma_sparse_kw_expr_sprint`, the 5-clause `lemma_sparse_where_group_sprint`
(spinoff), and — key move — the Select case of `lemma_sparse_stmt_sprint` extracted
into a spinoff'd `lemma_sparse_select_sprint` (the 5-clause `sparse_select`
composition is too big to evaluate in the main statement lemma's shared context).

**ALL FIVE Select clauses landed (2026-08-28, 151 verified).** LIMIT/OFFSET went in
via the 3+2 opaque split, confirming the scaling recipe end to end:
- `sparse_where_group` kept at 3 clauses (WHERE/GROUP/HAVING), generalised with a
  boundary `tail` param; a separate 2-clause opaque `sparse_limit_offset` parses
  LIMIT/OFFSET; `sparse_select` composes them. Each opaque parser ≤3 clauses ⟹ its
  exec refinement's one-shot `reveal` stays tractable (`parse_where_group_exec` +
  `parse_limit_offset_exec`).
- Heavy lemmas carry `#[verifier::spinoff_prover]` (fresh minimal solver context):
  `lemma_sparse_column_sprint`, `lemma_sparse_where_group_sprint`, and the Select
  roundtrip extracted into a spinoff'd `lemma_sparse_select_sprint`.
- Shared per-clause helpers `sparse_kw_expr` / `kw_expr_part` /
  `lemma_sparse_kw_expr_sprint` (one optional `KW <expr>` with an arbitrary tail).

**Reusable scaling recipe (proven):** (1) keep each opaque parser ≤3 clauses so its
exec refinement's `reveal` doesn't crash; (2) `spinoff_prover` any heavy lemma; (3)
extract a big statement-kind's roundtrip into its own spinoff'd lemma; (4) thread a
`tail` param through clause lemmas so tails compose; (5) dispatch gotcha —
`sparse_stmt` needs `fuel >= 1` (reveal `sdepth_select_body`) to pick the Select arm.

**ALL SIX Select clauses landed (2026-08-28, 165 verified).** `ORDER BY` completes
the Select grammar, mirror + exec, both directions:
- Direction + order-list codec (`sprint_order_list` / `sparse_order_list` +
  `lemma_sparse_order_list_sprint`): a boundary-terminated comma-list of
  `(expr, direction)`; the direction is *always* printed (ASC/DESC), so the printed
  form is self-delimiting and the roundtrip is exact regardless of the source default.
- A ≤3-clause opaque `sparse_order_clause` (ORDER BY only) + its lemma, threaded into
  `sparse_select` / `lemma_sparse_select_sprint` between WHERE/GROUP/HAVING and
  LIMIT/OFFSET via the boundary `tail`: where_group leaves `orderlo`, ORDER BY leaves
  `lo`, LIMIT/OFFSET finishes. No change needed to the where_group lemma (Order is not
  Where/Group/Having).
- exec: `print_order_list_slice` / `parse_order_list_exec` / `parse_order_clause_exec`.

**New scaling lever — the head/tail exec split.** Adding ORDER BY made
`print_select_exec` an 8-clause inline assembly, which crashed the solver with
`expected rlimit-count` (module-scale SMT context). `spinoff_prover` did *not* fix it
(the single function's `token_views` assembly is intrinsically large). The fix:
split the exec printer into `print_select_head_exec` (SELECT..HAVING) and
`print_select_tail_exec` (ORDER BY/LIMIT/OFFSET), each proving its own explicit
concatenation; `print_select_exec` then just `token_views_concat`s the two halves
under one `reveal(sprint_select_body)`. Generalises recipe rule (1) from opaque
*parsers* to *any* exec function that assembles many clauses.

**Remaining for the parser cutover:** multi-assignment `Update` (the sorted-`iter()`
bridge over `Map` equality). NOTE: the FROM-tree join *types* are already DONE — all
four (`Cross`/`Inner`/`Left`/`Right`, `join_kws` + `join_type_of`) roundtrip mirror +
exec (`sparse_step`/`parse_step_exec`, Cross⟹no predicate else `ON e`), landed with
the S3/S5 join-tree work. So the whole `SELECT` grammar (clauses + FROM joins) and
CreateTable/Insert/Delete are complete; only multi-`Update` grammar is left. Then the
real gates: the byte-cursor lexer (from scratch) and the ast-equivalence argument.

**Multi-`Update` — concrete design (scoped 2026-08-28; the vstd `iter()` spec makes
it tractable, and it needs NO Expression-level `==`).** `std_specs/btree.rs`'s `iter()`
postcondition pins `IteratorSpec::remaining(&it)` to be: length `= m@.dom().len()`,
each entry in `m@`, `remaining.unref().to_set() == m@.kv_pairs()`, `no_duplicates()`,
and `increasing_seq(remaining.map_values(|kv| *kv.0))` (keys sorted). So the sorted
entry seq is a *pinned function of `m@`*, even though a pure spec fn can't compute the
sort. Plan (5 pieces, each a green increment):
1. **Uniqueness lemma** (pure) — DONE (2026-08-28, 169 verified). `lemma_sorted_kv_unique`:
   two strictly-key-increasing seqs with equal `to_set()` are equal (induction on the
   min-key head). Needed a new trusted `axiom_string_obeys_cmp` (String obeys
   `laws_cmp::obeys_cmp`, distinct from `key_obeys_cmp_spec` — the `increasing_seq`
   interpretation uses the former) and `string_cmp_laws` (reflexivity + antisymmetry of
   `cmp_spec`, unpacked by revealing `obeys_cmp` / `obeys_cmp_ord` /
   `obeys_partial_cmp_spec_properties` — both sub-preds are opaque). NOTE: a later
   `view_map(m@) = m@.map_values(view_opt)` headline (Map-view equality, order-free) may
   let pieces 4-5 avoid the choose-based normal form entirely; the uniqueness lemma still
   pins iter()'s order to a canonical form and is reusable regardless.
2. **`update_normal(m@) : Seq<(String, Option<SExpr>)>`** = `choose |S|` sorted-no-dup
   with `S.to_set() == { (k, view_opt(m@[k])) }`; well-defined by (1). Note it's over
   *SExpr* values (view of each), so it depends only on keys + value-views — both
   preserved by any view-level roundtrip, which is why no Expression `==` is needed.
**Design refinement (2026-08-28): pieces 2-3 are AVOIDABLE.** Proving `total_ordering`
for the `String` `leq` (needed by `find_unique_minimal`) drags in `eq_spec <==> ==`
plumbing (`obeys_eq_spec`, `x@ == y@ <==> x == y` for `String`) — a deep chain. But
the roundtrip headline doesn't need a *sorted* normal form: state it as order-free
Map-view equality `view_map(m@) == view_map(m'@)` where
`view_map(m) = m.map_values(|v| view_opt(v))`. `view_map` is a plain spec fn (no sort),
so no `update_normal`, no `total_ordering`, no `find_unique_minimal`, no `view_stmt`
change. The uniqueness lemma (1) stays as correct infrastructure (it pins iter()'s
order) but is not on the critical path.
3. ~~view_stmt extension~~ — replaced by the `view_map` headline above.
4. **Parse-side map builder** — DONE (2026-08-28, 173 verified). `parse_set_map_exec`:
   recursive parser that reads `k = v, ...` and folds `insert` in one pass (moves parsed
   values, never clones), refining `sparse_set_list` with
   `view_map(m@) == seq_to_map(sparse_set_list(input).0.unwrap())`. Discharged via
   `lemma_view_map_insert` / `lemma_view_map_empty` + the BTreeMap insert view. Added
   `seq_to_map` (head inserted last). NOTE: parse turned out to be the *easier* half —
   it never touches `iter()`, just recursion + insert.
**Coverage lemma** — DONE (2026-08-28, 174 verified). `lemma_seq_to_map_enumerates`:
a unique-key enumeration `S` of a finite map builds exactly that map
(`seq_to_map(S) == m`). Induction peeling the head, recursing on `m.remove(head.0)`.
This is the glue that equates `parse(print(m))`'s `seq_to_map(S)` with `view_map(m@)`.

5. **Print exec** (the ONLY multi-Update piece left): loop `it.next()` accumulating a
   ghost seq `S`; invariant ties emitted tokens to `sprint_set_list(view of consumed)`
   (use `sprint_set_list_snoc` for the step) and `S ++ remaining(it) == full`. `S`
   inherits iter()'s sorted/unique/covering properties, so `lemma_seq_to_map_enumerates`
   + `lemma_sparse_set_list_sprint` + `parse_set_map_exec` close the roundtrip. Then
   relax the single-assignment restriction in the Update statement print/parse.
   - **Per-entry printer** — DONE (2026-08-28, 177 verified). `print_assign_exec` +
     `lemma_sprint_assign_view`. The reference-pattern blocker is resolved exactly as
     predicted: phrase the ensures with the `match v { Some(e) => sprint(view_expr(*e)),
     None => [Default] }` binding (matching the exec match), never a `view_opt(*v)`
     projection; `lemma_sprint_assign_view` (value-match on `o`) bridges that form to
     `sprint_assign((k, view_opt(o)))`. Borrows the value, no clone.
   - **Print `iter()` loop** — DONE (2026-08-28, 181 verified). `print_set_map_exec`: the
     prophetic accumulation loop, the hardest exec pattern in the project. Verified.
     Techniques that landed it: a counted `while count < m.len()` (NOT a bare `loop`) so
     the exit `consumed.len() == full.len()` is provable and `decreases m_len - count` is
     non-prophetic (`it.remaining().len()` is prophetic — cannot be a decreases measure);
     next() is Some every iteration so the None arm is dead (`assert(false)`);
     `lemma_all_printable_assigns_snoc` for the printable invariant step; coverage closed
     by `lemma_seq_to_map_enumerates` + `lemma_increasing_keys_distinct`;
     `spinoff_prover` on `lemma_seq_to_map_enumerates` (module-scale regression as the
     file grew).
**Multi-Update Map wall TRAVERSED END TO END (2026-08-28, 185 verified).**
`set_map_roundtrip_exec`: for a printable non-empty `BTreeMap` of assignments, parsing
its print rebuilds a map with the same `SExpr`-view — `view_map(roundtrip(m)@) ==
view_map(m@)`. Composes the print `iter()` loop + parse builder +
`lemma_sparse_set_list_sprint` + `set_list_depth_le_len_ne` (token count is a valid
fuel; the tighter no-`+1` bound needs `assign_depth(a) + 1 <= sprint_assign(a).len()`,
the `Ident =` prefix giving the slack — avoids usize overflow). The order-free `view_map`
headline is what dodged BOTH the Map-sort obstacle (no sorted normal form needed in
spec) and the Expression-`==` obstacle (only value *views* match). This was the "one
real wall" — done.

**STATEMENT GRAMMAR COMPLETE (2026-08-28, 187 verified).** Multi-`Update` wrapped in the
full statement, both cases verified: `update_set_roundtrip_exec` (`UPDATE table SET
<assignments>`) and `update_set_where_roundtrip_exec` (`.. WHERE e`). The WHERE case:
the set-list parses up to the `WHERE` keyword (a boundary, `lemma_sparse_set_list_sprint`
with a WHERE tail), then the predicate roundtrips via `parse_expr_exec` +
`lemma_sparse_sprint` (establish the expr sparse-roundtrip BEFORE `parse_expr` so its
None arm is provably dead). With this, the ENTIRE statement grammar roundtrips end to
end, verified: all six Select clauses + FROM tree with all join types, CreateTable,
Insert, Delete, single-assignment Update, and multi-assignment Update (no-WHERE + WHERE).

**Phase 4 remaining — grammar DONE, only infrastructure left:** the from-scratch
production byte-cursor lexer (the existing verified `next_token` is a Phase-0 toy — this
is the multi-week gate) and the ast-equivalence argument so the verified parser is a
sound drop-in for the hand-written one, then the actual `parser.rs`/`lexer.rs` swap run
green against the SQL suite. No grammar work remains.

**Production lexer — RUNNABLE VERIFIED TOKENIZER for byte-determined classes
(2026-08-28, L12-L17, 89 verified / 0 errors, full suite green, axiom-free).**
Beyond the L0-L11 bricks below, the lexer now tokenizes **numbers, keywords and
all symbols** end to end, both directions, culminating in a runnable executable
`Vec<u8> -> Vec<Token>` producing the *real* production `Token`:
- **L12** — full number scanner `scan_num_full_end` (int/decimal/exponent,
  matching `lexer.rs::scan_number_bytes`); roundtrip covers the two printed forms
  (Rust `f64` Display never emits scientific notation) under `num_tail_ok`.
- **L13** — keyword classification table (66 keywords). Verus does NOT auto-decide
  `seq!` literal equality, so `classify_kw` decides on `len` + indexed `byte_at`;
  the 66-arm roundtrip lemma is split into 6 `spinoff_prover` grouped helpers
  (each `requires` a keyword disjunction so its `_` arm is vacuous) to stay under
  rlimit. `classify_kw_exec` refines it.
- **L14** — ASCII case-folding + keyword-run scanner `lscan_keyword`; the keyword
  arm roundtrips axiom-free (keywords carry no `String`).
- **L15** — single-token value dispatcher `lscan_token` + `lemma_lscan_token`
  (roundtrip for every byte-determined class); symbols compose via `sym_token_of`
  delegating `lex_print_tv` to the Token-level `lscan_sym`.
- **L16** — whole-input token-LIST roundtrip `lemma_lex_all_seq_roundtrip`: a
  single **space is a universal separator** (satisfies every boundary), and
  `lex_all_seq` strips leading whitespace as a seq slice *before* each scan so all
  scans run at position 0 (only locality fact: a one-byte `skip_ws` shift).
- **L17** — scanner suffix-**locality** lemmas (every scanner: scan at `pos` ==
  scan the suffix at 0, shifted) → `lex_from` (position-based) bridged to
  `lex_all_seq`; then the executable `lex_all_exec` fuel-free loop refining
  `lex_from`, and the end-to-end `lemma_lex_all_exec_roundtrip`.

**Remaining lexer work — the `String` trust bridge (the cutover blocker).** The
only token classes left are **`Ident` (plain, non-keyword) and `String`** (quoted
`'...'`/`"..."` with `''`/`""` escapes), which carry `String` payloads. The
grammar carries these opaque, but the *lexer must build a `String` from bytes*,
which needs a minimal audited byte↔`String` (UTF-8) trust bridge — the one
planned trust-surface expansion (like `float_trust`). Plain idents also involve
unicode lowercasing (production uses `char::to_lowercase`; the ASCII case is
axiom-free, non-ASCII needs the `unicode_trust` model). Whitespace is currently
ASCII (`is_ws`) vs production's unicode `is_whitespace` — a small gap. After the
`String` bridge: ast-equivalence + the `parser.rs`/`lexer.rs` cutover.

**Production lexer STARTED (2026-08-28, `verified_lexer.rs`, in verify.sh — 18 modules).**
Same discipline as the grammar: smallest self-contained verified bricks, produces the
REAL production `Token` (not `verified.rs`'s Phase-0 toy), byte cursor over `Seq<u8>`.
- **L0 — munch-free punctuation** (`. = + - * / ^ % ? , ; ( )`): `punct1_byte` /
  `scan_punct1` / `lscan1` / `lex_print1` + `lemma_lscan1_lex_print1` (scan inverts print
  for any tail — these are never a longer token's prefix) + `scan_punct1_exec`.
- **L1 — maximal-munch operators** (`< > !` and `<= >= <> !=`): `lscan_op` looks one byte
  ahead and commits to the longest match. Introduces BYTE-level boundary reasoning
  (`op_tail_ok`): a printed `<` before `=`/`>` re-scans as `<=`/`<>`, so the single-char
  forms roundtrip only when the next byte doesn't extend them; two-char forms impose
  nothing. `lemma_lscan_op` + `scan_op_exec`.
- **L2 — whitespace skip:** `skip_ws` + `lemma_skip_ws_bounds` / `_fixpoint` / `_nonws`
  + `skip_ws_exec`. The inter-token machinery prerequisite.
- **L3 — number integer core:** `is_digit` / `all_digits` / `scan_digits_end` +
  `lemma_scan_digits_end_run` (maximal-run characterization) +
  `lemma_scan_digits_roundtrip` (digit run re-scans under a non-digit boundary) +
  `scan_digits_exec`. (`scan_number_bytes` exec already verified in `lexer.rs`.)
- **L4 — unquoted identifier char-run:** `is_ident_start`/`_cont`/`is_ident_bytes` +
  `scan_ident_end` + `lemma_scan_ident_end_run` + `lemma_scan_ident_roundtrip` +
  `scan_ident_exec`. Same maximal-munch shape as L3.
- **L5 — single-token dispatcher:** `lex_token_end` (skip_ws then classify first byte to
  number/ident/operator/punctuation) + `lemma_lex_token_end_bounds` / `_progress` (strict
  advance on a token start — the termination fact). Gotcha: establish `0 <= p` via
  `lemma_skip_ws_bounds` so the dispatcher's guard unfolds to the token arm.
- **L6 — exec dispatcher + spec token-list:** `lex_token_end_exec` (runnable, composes the
  L0-L5 exec scanners) + `lex_all_ends` (fuel-bounded spec whole-input scanner) +
  `lemma_lex_all_ends_bounded`.
- **L7 — token-list fuel stability:** `lemma_lex_all_ends_fuel_stable` (fuel >= len-pos ⟹
  more fuel changes nothing) — lets a fuel-free exec loop refine the fuel-bounded spec.
- **L8 — executable token-list loop:** `lex_all_ends_exec`, a fuel-free `while` refining
  `lex_all_ends` at fuel `len+1` (the sparse→exec loop pattern, tokenizer edition). A
  **runnable verified tokenizer skeleton** over the core token classes. Key: pin `fuel`/
  `whole` in the invariant (ghost defs don't auto-carry into the loop); `reveal_with_fuel`
  to unfold each step; realign tail fuel via L7; `ends_int` bridges `Vec<usize>`→`Seq<int>`.
- **Remaining lexer bricks:** number decimal/exponent extension; strings (quotes + escapes,
  Unicode — expands the trust surface); identifier lowercasing + keyword classification;
  quoted identifiers; line comments; wiring those arms into the dispatcher; then the
  whole-input token-LIST ROUNDTRIP (print tokens → re-lex, with inter-token separator
  canonicalisation — two adjacent `Number`s/idents need a space or they re-lex as one) and
  the executable `Vec<u8> -> Vec<Token>` top-level lexer producing real `Token`s. THEN
  ast-equivalence + cutover. Multi-week. Nine bricks done (L0-L8): the mechanically-clean
  core plus a runnable tokenizer skeleton, each reusing the token-level boundary discipline
  at the byte level and the parser's fuel/sparse→exec patterns.

**Module-scale SMT wall + the partial fix (2026-08-28).** The full `GROUP BY`
integration builds and the *mirror* verifies (sprint/sparse/printable/sdepth +
`sparse_where_group` opaque helper + roundtrip lemma + `print_select_exec`), but
it tips `slist_depth_columns_le_len` — an unrelated, pre-existing, resource-fragile
CreateTable lemma — from green to "postcondition not satisfied", and this does
**not** respond to `rlimit` (tried 8000→100000). Root cause: `verified_stmt.rs` is
~5000 lines, and every `open spec fn` body is a global SMT axiom, so growing the
grammar grows every proof's background past what that fragile lemma can discharge.

*Committed enabler:* `sprint_select_body` / `sdepth_select_body`
(`#[verifier::opaque]`) now hold the Select clause structure, so Select-grammar
growth no longer enlarges the global `sprint_stmt`/`sdepth_stmt` axioms (revealed
in the Select lemma + `print_select_exec`). This restored 144-green and is the
template for the fix. But re-applying `GROUP BY` still re-tips the column lemma:
the column codec itself (`sprint_column` — 6 optional clauses — `sprint_columns`,
`slist_depth_columns`) sits in *every* proof's background directly.

*Next linchpin (do this first, before the five clauses):* opaque-harden the column
codec the same way — make `sprint_column`/`sprint_columns`/`slist_depth_columns`
`#[verifier::opaque]` and `reveal` them locally in `lemma_sparse_column(s)_sprint`,
`slist_depth_columns_le_len`, `sdepth_column_le_len`, and `print_column(s)_exec`
(and extract the CreateTable case of `sprint_stmt`/`sdepth_stmt` into opaque
helpers, mirroring `sprint_select_body`). That removes the 6-clause bulk from the
background of every non-column proof and bounds the column lemmas' own queries.
Once green, re-apply the `GROUP BY` mirror (a solved problem) and add the exec:
`parse_expr_list_exec` (refining opaque `sparse_expr_list`) + a where+group exec
helper refining `sparse_where_group`, then the remaining four clauses reuse the
same codec/opaque-helper recipe.

The techniques that landed S0-S3 (opaque+peel for optional-clause soup;
force-evaluate a recursive `sparse_X` with an explicit `assert(sparse_X(..)==..)`;
DEFAULT/embedded-expr emitted last so its tail is always a terminator; fold
decomposition for the left-deep join tree) are recorded in the `kg` memory
`verus-stmt-roundtrip-s0-s3`.

## Completion status (2026-08-27)

The "Complete expression roundtrip — execution plan" (E0-E4) below is **done**,
landed in `src/sql/parser/verified_roundtrip.rs` (opted into `verify.sh`,
`verus focus` green, normal `cargo check` clean):

- **E0** — `SExpr` mirror of the whole `ast::Expression` grammar, `view_expr`
  bridge, `sprint` canonical printer, `sdepth` fuel measure + `sdepth_le_len`
  length bound.
- **E1+E2** — `sparse`/`sparse_args` mirror parser and the roundtrip
  `lemma_sparse_sprint` / `lemma_sparse_args_sprint` over the *entire* grammar
  (`All`, `Column`, every `Literal`, all 15 `Operator`s, and nested
  `Function`s), with `mirror_roundtrip` and `mirror_injective` corollaries. The
  `Ident (` / `Ident . Ident` / bare-`Ident` disambiguation and the extended
  boundary predicate (forbids a trailing `(` and `.`) are proved.
- **E3** — `parse_expr_exec` / `parse_args_exec`: executable parsers over
  `Vec<Token>` building real `ast::Expression` (Box children, Vec args),
  verified to refine `sparse` at the `view_expr` level. Literal payloads parse
  through the existing `verified_integer` / `float_trust` exec surface.
- **E4** — `print_expr_exec` / `print_args_slice` (executable printer,
  `token_views(result) == sprint(view_expr(e))`), the paren-wrapping
  combinators, and the headlines `roundtrip_exec`,
  `print_parse_roundtrip_exec` (fully self-contained), and
  `roundtrip_injective`.

Trust surface is unchanged: the only axioms are the three `float_trust`
assumptions. Everything else is axiom-free.

The expression headline is fuel-free: `print_expr_exec` recurses on the ghost
measure `sdepth(view_expr(*e))` (a `decreases` may be ghost even for exec code),
so `print_parse_roundtrip_exec(e)` takes only the expression and `printable_se`.
An executable `usize` fuel counter was avoided on purpose — `sdepth` is an
unbounded `nat`, so a counter would need an unprovable "AST fits in `usize`"
bound to rule out overflow.

**Remaining work** — the statement layer and the production cutover — is scoped
concretely in "Remaining work" below.

## Remaining work — statement roundtrip + cutover

The statement layer reuses the expression pieces wholesale: `parse_expr_exec` /
`print_expr_exec` for every embedded expression, `sparse` / `sprint` for the
mirror, and the `view_expr` bridge. What is new is the statement-level mirror
`SStmt` (a `Seq`-based mirror of `ast::Statement`, embedding `SExpr` for
expression children), and the keyword-driven wrappers around the expression
grammar. Same three-layer shape as E0-E4: mirror + roundtrip, then executable
refinement at a `view_stmt` level.

The wrinkles are all about the containers `Statement` carries, so the phases are
ordered by container difficulty rather than by statement kind.

- **S0 — mirror scaffold + bridge.** `SStmt`, `view_stmt: ast::Statement ->
  SStmt`, `sprint_stmt`, `sdepth_stmt`. Expression children go through the
  existing `view_expr` / `sprint`. Small, mirrors E0.

- **S1 — list-free statements.** `Begin` / `Commit` / `Rollback` / `DropTable`
  / `Explain` (recursive wrapper, forbid `Explain(Explain(_))`), and `Delete`
  with an optional `where` in the verified expression domain. The spec-level
  encodings already exist in `verified_production` (`control_tokens`,
  `drop_table_tokens`, `begin_views`, `delete_views`); port them onto `SStmt`
  and prove `sparse_stmt(sprint_stmt(s)) == (Some(s), [])`. Reuse
  `lemma_sparse_sprint` for the embedded `Delete` predicate.

- **S2 — single-level lists.** `CreateTable` columns, `Select`'s `select` (with
  `Option<String>` aliases and the `All`-only-unaliased rule via the existing
  `contains_all` predicate), `group_by`, `order_by` (with `Direction`), and
  `Insert`'s optional column-name list. Each is one comma list over an
  expression (or name), so the `sparse_args` / comma-list lemma from
  `verified_roundtrip` is the template; write one statement-list lemma and
  instantiate it per position.

- **S3 — nested lists and the join tree.** `Insert.values : Vec<Vec<Expression>>`
  is a comma list of parenthesised comma lists, so the mirror needs
  `Seq<Seq<SExpr>>` and a two-level list lemma (outer list of rows, inner list
  of values). `Select.from : Vec<From>` with `From::Join` is a left-deep
  recursive tree (right child always a table, `CROSS JOIN` alone omits its
  predicate); mirror it as a recursive `SFrom` and prove its roundtrip with the
  join-associativity direction fixed by the printer, reusing `printable_from`.

- **S4 — `Update.set : BTreeMap<String, Option<Expression>>`.** The hard one.
  A `BTreeMap` has no canonical printable order that Verus models cheaply, and
  its equality is not view-determined. Decide the representation up front:
  carry the assignments in the mirror as a `Seq<(String, Option<SExpr>)>` sorted
  by key, have `print_stmt_exec` emit them in that fixed order, and have the
  parser rebuild the `BTreeMap` — stating the roundtrip through a `view_stmt`
  that canonicalises the map to the same sorted sequence (so map equality is
  never needed, exactly as `view_expr` sidesteps `Vec` equality). If Verus's
  `BTreeMap` model is too thin to rebuild from a sequence, restrict the verified
  `Update` domain to a sorted-key normal form and document the gap.

- **S5 — executable statements + headline.** `parse_stmt_exec` / `print_stmt_exec`
  building real `ast::Statement`, refining `sparse_stmt` / `sprint_stmt` at
  `view_stmt`, delegating every expression to `parse_expr_exec` /
  `print_expr_exec`. Headlines `print_parse_roundtrip_stmt` (fuel-free, same
  ghost-measure `decreases` trick) and `stmt_injective`.

### Phase 4 — production cutover (independent of S0-S5)

Replace the two `std::iter::Peekable`s with the verified cursors so the verified
functions become the production functions (coverage numerator up, denominator
flat):

- `Lexer.chars : Peekable<Chars>` -> the byte cursor `next_token(&[u8], pos)`
  from `verified.rs`.
- `Parser.lexer : Peekable<Lexer>` -> the `TokenStream` / `PeekStream` leaf.
- Swap `parse.rs`'s recursive-descent expression/statement parsers for
  `parse_expr_exec` / `parse_stmt_exec`, and delete the std-iterator plumbing.
- Run the existing SQL suite green. Budget the ripple onto `verified_production`
  / `verified_statements` (the spec-parser-backed statement proofs) — migrate
  them onto the executable parser, then retire the spec parser.

### Phase 5 — optional refinements

Minimal-parenthesisation printer (mirror `types::ExpressionDisplay`) reproved to
roundtrip via the precedence-table argument, and the lift to string level once
the byte-cursor lexer's own roundtrip is proved (`parse(print_str(e)) == e`).

## Original plan follows

Verified module opt-in via `scripts/verus/verify.sh`.

## Objective

Prove `parse(print(e)) == e` (print-parse roundtrip, "Style B") for parser-producible
`ast::Expression`, then `ast::Statement`, while:

- keeping the parser **streaming** (single pass, O(1) token buffer, no `Vec<Token>` materialisation),
- shipping a **single implementation** (no digital twin, no differential test),
- keeping the **trusted surface tiny and audited** (one file, three float assumptions; everything else axiom-free).

This grows the verified coverage surface in the pure-logic style already proven to work in
this repo (keycode), on code entirely disjoint from `storage/mvcc.rs`.

## Why roundtrip, not grammar-completeness

The heavy verified parsers (CompCert/Menhir, CoStar in Coq) prove soundness + completeness
against a formal grammar. That needs a separate grammar formalisation and an ambiguity proof.
Roundtrip against a canonical printer is the lighter, high-leverage property (the flavour of
Narcissus/EverParse and the Dafny stdlib JSON codec), and it is exactly the keycode roundtrip
one layer up the stack. toyDB's AST has no printer yet, so we write a canonical one and control
its shape.

## What toyDB uses today (the thing being replaced)

`std::iter::Peekable`, twice, for one-element lookahead:

- Parser layer: `Parser.lexer: Peekable<Lexer<'a>>` (`parser.rs:18`), from `Lexer::new(input).peekable()`.
  The peeked iterator is toyDB's own `Lexer` (`impl Iterator<Item = Result<Token>>`, `lexer.rs:320`).
- Lexer layer: `Lexer.chars: Peekable<Chars<'a>>` (`lexer.rs:316`), from `input.chars().peekable()`.
  The peeked iterator is std's `Chars`.

Neither is verifiable as-is: the "how much input is left" quantity lives inside a std type Verus
never compiles, so there is no `decreases` measure and no spec for `next()`. The obstacle is
specifically `std::iter::Peekable`, not streaming.

## Architecture (the spine)

Streaming is preserved by making the cursor **explicit** instead of hidden in a std iterator,
packaged behind a Peekable-shaped trait so parser code keeps `peek`/`next` ergonomics.

- **Layer A, bytes -> tokens** (replaces `Peekable<Chars>`): a pure scanner
  `next_token(input: &[u8], pos: usize) -> (Result<Option<Token>>, usize)` with
  `decreases input.len() - pos`. Explicit byte cursor, no `Chars`, no std `Peekable`.
- **Interface**: a `PeekStream` trait with `spec fn view(&self) -> Seq<Token>` and `peek`/`next`
  whose `ensures` are written against `view()`. This is a *contract*, not a trusted axiom:
  every implementer must prove its body meets it; the parser assumes only the contract.
- **Leaf**: `TokenStream { input: &[u8], pos, lookahead }` implements `PeekStream` using
  `next_token`; `view()` is defined as `tokens_from(input, pos)` (a `spec fn`, not assumed).
  Because the leaf bottoms out at `&[u8]` indexing (a Verus native), the contract is discharged
  with no axiom.
- **Layer B, tokens -> AST** (replaces `Peekable<Lexer>`): the parser is generic,
  `parse_expr<S: PeekStream>(s: &mut S) -> Result<Expression>`, verified once against the trait
  with `decreases s.view().len()`.
- **Printer**: canonical `print_expr`/`print_statement` emitting `Seq<Token>`, **fully
  parenthesised** first so the roundtrip proof is structural. Minimal-parens is a later refinement.

Same `peek/next` ergonomics as today, streaming, one implementation, and the termination proof is
done once against the contract, independent of the concrete stream.

## Spec skeleton

```rust
// interface
trait PeekStream {
    spec fn view(&self) -> Seq<Token>;                 // remaining tokens (ghost)

    fn peek(&mut self) -> (r: Option<Token>)
        ensures
            r == if self.view().len() == 0 { None } else { Some(self.view()[0]) },
            self.view() == old(self).view();            // peek does not consume

    fn next(&mut self) -> (r: Option<Token>)
        ensures
            old(self).view().len() == 0 ==> r is None && self.view() == old(self).view(),
            old(self).view().len() >  0 ==> r == Some(old(self).view()[0])
                                          && self.view() == old(self).view().drop_first();
}

// leaf (verified, discharges the contract; no axiom)
struct TokenStream<'a> { input: &'a [u8], pos: usize, lookahead: Option<Token> }
impl PeekStream for TokenStream<'_> {
    spec fn view(&self) -> Seq<Token> { tokens_from(self.input, self.pos) }
    fn next(&mut self) -> Option<Token> { /* body checked against ensures */ }
    fn peek(&mut self) -> Option<Token> { /* ditto */ }
}

// parser (verified once against the contract)
fn parse_expr<S: PeekStream>(s: &mut S) -> (r: Result<Expression>)
    decreases s.view().len()
{ /* uses s.peek()/s.next(); each recursion consumes >=1 so view() shrinks */ }

// canonical printer
spec fn print_expr(e: Expression) -> Seq<Token> decreases e;

// headline
proof fn print_parse(e: Expression)
    requires parseable(e),
    ensures  parse_expr(&mut TokenStream::of(print_expr(e))) == Ok(e);   // consumes the whole view
```

## Scope decisions

1. **Work at the token layer** (`Seq<Token>`), not raw `&str`. Compose with the byte-cursor lexer's
   own roundtrip later for the full string-level statement.
2. **String / identifier payloads are opaque byte runs**: carried and compared, never inspected,
   so Verus's weak `str` support never bites.
3. **`All` (`*`) handled by a context predicate**, valid only in a select list.
4. **Single implementation**: production `parser.rs`/`lexer.rs` are switched to the verified
   functions at cutover. No twin, so no differential test.
5. **Float literals: finite-guarded trust (option 2)** — see below. AST stays `Literal::Float(f64)`,
   so nothing ripples into the planner/executor.

## Float decision (option 2: finite-guarded trust)

The roundtrip `parse(print(Float(x))) == Float(x)` unfolds to `parse_f64(display_f64(x)) == x`,
bit-exact, which needs correctly-rounded decimal<->binary conversion (Ryu/Dragonbox + Lemire) and
an IEEE model. Verus has no `f64` reasoning, so proving it is out of scope. Instead:

- Parser-produced floats are always **finite** (`NaN`/`inf` lex as identifiers, not `Number` tokens).
- For finite `x`, Rust's `Display` emits the shortest string that `FromStr` reads back bit-exactly.
  So the finite-guarded roundtrip is a **true** statement; we trust rustc's float conversion rather
  than prove it.
- The naive *un*guarded axiom `parse(display(x)) == x` is **false** under toyDB's `to_bits` equality
  (NaN payloads, signalling NaN), so the `is_finite()` guard is load-bearing, not decoration.

Well-formedness carries the guard:
```rust
spec fn parseable(e: Expression) -> bool {
    match e {
        Literal(Float(x))  => x.is_finite(),
        Literal(_)         => true,
        Operator(op)       => parseable_op(op),
        Function(_, args)  => forall|i| 0 <= i < args.len() ==> parseable(args[i]),
        // All only in select-list position; handled by a context predicate at Phase 3
        ...
    }
}
```

Trusted boundary, quarantined to one file `float_trust.rs`:
```rust
#[verifier::external_body] fn display_f64(x: f64) -> (s: Vec<u8>) ensures s@ == spec_display(x);
#[verifier::external_body] fn parse_f64(s: &[u8]) -> (r: Option<f64>) ensures r == spec_parse(s@);

#[verifier::external_body]                    // THE trusted assumption (true for finite x)
proof fn axiom_f64_finite_roundtrip(x: f64)
    requires x.is_finite(),
    ensures  spec_parse(spec_display(x)) == Some(x);
```

`f64` stays fully opaque: no arithmetic, no IEEE model. The only facts used are `is_finite`, the two
uninterpreted `spec_display`/`spec_parse`, the axiom relating them, and that `f64` spec-equality is
bit-equality (to match toyDB's `to_bits` `Literal` equality). Integer literals get a **native** exact
proof (`parse_i64(display_i64(n)) == n`), no trust.

## Trust surface (audited, small)

Exactly three assumptions, all in `float_trust.rs`:

1. `display_f64` / `parse_f64` faithfully model `<f64 as Display>` / `<f64 as FromStr>`.
2. `axiom_f64_finite_roundtrip` (true, but trusts rustc's formatter/parser instead of proving them).
3. `f64` spec-equality is bit-equality.

Everything else (the `PeekStream` contract, the `TokenStream` leaf, the parser, all
integer/string/bool/null literals, the whole roundtrip proof) is fully verified with no axioms.
Review rule: any new `PeekStream` implementer must be verified Rust; an `external_body` implementer
would silently re-introduce trust.

## Properties delivered

- **Totality**: the parser panics on no input; every token stream yields a `Result`.
- **Termination**: proved once against the `PeekStream` contract via `decreases s.view().len()`.
- **Roundtrip**: `parse(print(e)) == e` for `parseable(e)`, including finite floats.
- **Printer injectivity** on `parseable` ASTs, as a corollary.

## Phases

- **Phase 0 - spine compiles and proves trivially (2-4 days).**
  Add module `sql::parser::verified` to `scripts/verus/verify.sh`. Define Verus-side `Token`
  (plain enum, byte payloads), a minimal `next_token`/`tokens_from` with `decreases input.len()-pos`,
  the `PeekStream` trait, the `TokenStream` leaf (prove its two methods meet the contract),
  the `float_trust.rs` stub. Prove one literal roundtrip (integer native, float via the axiom).
  Wires leaf -> trait -> generic parser -> printer and the proof harness.

- **Phase 1 - minimal expression grammar, end to end (3-5 days).**
  Literals + `Column` + two binary ops + one unary. Fully-parenthesised printer,
  `parse_expr<S: PeekStream>`. Prove totality, termination, roundtrip. This is the template.

- **Phase 2 - full expression operator set (1.5-2.5 weeks).**
  All of `Operator`: `And/Or/Not`, comparisons (`= != < <= > >=`, `IS`), arithmetic
  (`+ - * / % ^`), unaries (`Negate`, `Identity`, `Factorial`, `SquareRoot`), `Like`.
  Plus `Function(name, args)` (comma-list roundtrip lemma over `Vec<Expression>`) and qualified
  `Column(Option<String>, String)`. Float literals land here via `float_trust`. Proof is structural
  induction on `Expression`; the generic termination proof from Phase 1 is reused unchanged.

- **Phase 3 - statements (1-1.5 weeks).**
  `print_statement`/`parse_statement` roundtrip for the `Statement` variants (transaction control,
  `CREATE/DROP TABLE`, `INSERT`, `UPDATE`, `DELETE`, `SELECT`). Linear keyword-driven wrappers around
  expressions; roundtrip composes over Phase 2 + list lemmas. `All` enters via the select-list predicate.

- **Phase 4 - cut over production (3-5 days).**
  Replace `Parser`'s `Peekable<Lexer>` with `TokenStream` and `Lexer`'s `Peekable<Chars>` with the
  byte cursor; delete the std-iterator plumbing. Run the existing SQL suite green. The verified
  functions become the production functions, so coverage moves properly (numerator up, denominator flat).

- **Phase 5 - optional refinements.**
  Minimal-parenthesisation printer (mirror `types::ExpressionDisplay`, `expression.rs:451`) reproved
  to roundtrip (the precedence-table = precedence-table argument). Lift to string level once the
  byte-cursor lexer's own roundtrip is proved: `parse(print_str(e)) == e`.

## Findings so far (2026-08-27)

Phase 2's `Function(name, args)` case turned out to have two separate obstacles,
only one of which the plan anticipated.

- **Termination is solved.** Recursion through `Vec<Expression>` admits a
  measure: a spec height whose list component decreases on the argument
  *sequence* (`decreases args`), not on `args.len()` (an `int`, which is
  type-incompatible with the datatype measure in the mutual-recursion group).
  Confirmed on Verus `0.2026.08.23`.

- **The real wall is Verus's `Vec` model.** `Vec` has no spec-level
  constructor, and `Vec` equality is not determined by its view, not even
  deeply (`v1@ == v2@` does not give `v1 == v2`). So a `spec fn` parser cannot
  build a `Function(name, Vec)` node, and no spec proof can recover the node
  equality the roundtrip needs. This is why the spec-parser core in
  `verified_expression.rs` is intrinsically limited to function-free
  expressions.

- **The exec-parser path works, and is validated in-repo.** An executable
  parser that builds `Vec`s at runtime, verified against a `Seq`-based mirror
  AST at the level of a structural view, closes the comma-list roundtrip for
  functions with no axioms. `src/sql/parser/verified_function_list.rs` carries
  the full pattern (spec-mirror roundtrip, `parse_exec`/`parse_args_exec`
  refining the mirror, and an end-to-end `roundtrip_demo` over real `Vec`s) and
  is opted in to `verify.sh`.

This sharpens Phase 4: the parser cutover is not only the production win, it is
the *only* way to bring functions into the roundtrip at all. Phases 2-3 should
either move to the executable-parser style throughout or accept the function-
free restriction until cutover.

## Complete expression roundtrip — execution plan

Goal: `view_expr(parse_expr_exec(print_expr(e))) == view_expr(e)` for every
`printable(e)` across the full grammar — `All`, `Column`, `Literal`, all 15
`Operator` variants, and `Function` — axiom-free apart from the existing
`float_trust` surface. Injectivity up to `view_expr` follows as the corollary.

The target equality is stated through `view_expr`, not raw `==`, because Verus
`Vec` equality is not view-determined (see Findings). `view_expr` is total and
structural, so the statement loses no information: it fixes every name, literal,
operator, nesting, and argument order/count.

### Why one unified executable parser

A `Function` can nest under any operator, and any expression can be a function
argument, so the parser is a single mutually-recursive nest. The spec parser
cannot build `Function` nodes, so the whole nest moves to executable code at
once. There is no partial spec/exec split at the expression level.

### Architecture (three layers)

- **Mirror layer (all spec).** A `Seq`-based mirror AST `SExpr` covering the
  full grammar — operator children are `Box<SExpr>`, function arguments are
  `Seq<SExpr>`. It carries the printer, fuel measure, parser, and the roundtrip
  proof. Everything here is spec-constructible and extensional, so the roundtrip
  closes with real `==` on `SExpr`.
- **Executable layer.** `parse_expr_exec` builds real `ast::Expression` (Box
  children, `Vec` arguments) and is verified to refine the mirror parser at the
  level of `view_expr`. `print_expr_exec` materialises the token vector.
- **Bridge.** `view_expr: ast::Expression -> SExpr` and the lemma
  `print_expr(e) == sprint(view_expr(e))` connect the two, so the existing spec
  printer (and the statement printers built on it) are reused unchanged.

### Components

- `SExpr` + `view_expr` / `view_args` (`ast::Expression -> SExpr`,
  `Seq<ast::Expression> -> Seq<SExpr>`).
- `sprint(se: SExpr) -> Seq<TokenView>`, the mirror printer, plus
  `print_expr(e) == sprint(view_expr(e))`.
- `sdepth(se) -> nat` / `slist_depth(args) -> nat`, the fuel measure, plus
  `sdepth(se) <= sprint(se).len()` for the fuel bound at the headline.
- `sparse(input, fuel) -> (Option<SExpr>, Seq<TokenView>)` and
  `sparse_args(...)`, the mirror parser over the full grammar.
- `lemma_sparse_sprint` / `lemma_sparse_args_sprint`, the roundtrip induction;
  mirror injectivity as its corollary.
- `parse_expr_exec` / `parse_args_exec` (executable, refine `sparse`).
- `print_expr_exec` (executable, `result@ == print_expr(e)`).
- `roundtrip` / `injective` headlines composing the above.

### Grammar deltas versus today's spec parser

- **`Ident` disambiguation.** After an `Ident`, peek: `Ident (` is a function
  call, `Ident . Ident` is a qualified column, bare `Ident` is a column.
- **Boundary predicate.** Extend `prefix_boundary(tail)` to also forbid `tail`
  opening with `OpenParen`, so a bare column is never re-read as a call. Audit
  every recursive call site — all pass `CloseParen`, `Comma`, `Is`,
  `Exclamation`, or an operator token, none of which is `OpenParen`.
- **Comma list.** `sparse_args` / `parse_args_exec` and the comma-list lemma
  come straight from `verified_function_list`.

### Phases (each ends green under `verify.sh`)

- **E0 — mirror scaffold + bridge.** `SExpr`, `view_expr`, `sprint`, and
  `print_expr(e) == sprint(view_expr(e))`; `sdepth` + the length bound. Small.
- **E1 — mirror parser + roundtrip, function-free.** Port `parse_prefix` to
  `sparse` and `lemma_parse_print_prefix` to `lemma_sparse_sprint` over `SExpr`,
  no `Function` yet. Re-establishes current coverage in the mirror; de-risks the
  port. Medium.
- **E2 — add `Function` to the mirror.** The `Ident ( args )` case, `sparse_args`,
  the comma-list lemma, and the boundary extension. The mirror roundtrip now
  covers the whole expression grammar. Medium.
- **E3 — executable parser.** `parse_expr_exec` over the full grammar, building
  `ast::Expression`, refining `sparse` at the `view_expr` level. Largest phase.
- **E4 — executable printer + headline.** `print_expr_exec` (`@ == print_expr`),
  then `roundtrip` and `injective` composing bridge + mirror roundtrip +
  refinement. Medium.

### Risks and decisions

- **Retire or keep the spec parser.** `parse_prefix` / `depth` /
  `lemma_parse_print_prefix` back the statement proofs in
  `verified_production.rs` (`delete_views`) and `verified_statements.rs`. Keep
  both paths until E3 lands, then migrate the statement proofs onto the
  executable parser and delete the spec parser. The migration is the ripple to
  budget, not the expression proof itself.
- **`TokenView` in exec.** Executable comparison needs `derive(Clone, PartialEq)`
  (or match helpers); `String` / `Ident` / `Number` payloads are carried and
  compared by value, never inspected.
- **Executable printer build order.** Building the token `Vec` with a forward
  loop fights `sprint_args`'s `drop_first` recursion (a `take`-vs-`drop_first`
  mismatch). Build by recursion over argument slices matching `drop_first`, or
  prove a prefix-extension lemma; do not stub it.
- **Fuel.** The executable parser passes `fuel = toks.len()`; `sdepth(se) <=
  sprint(se).len()` makes that a safe bound.
- **Trust surface.** Unchanged. No new axioms; `float_trust` stays the only
  trusted boundary.

### Statements follow the same shape

`Statement` carries `Vec`s too (`Insert.values`, `CreateTable.columns`,
`Select.select`/`from`, `Update.set`), so the full statement roundtrip needs the
same mirror + executable treatment, reusing the expression executable parser.
This is the original Phase 3, reframed: it cannot stay on the spec parser either.

## Risks and mitigations

- **Lexer error channel**: `next_token` returns `Result` (invalid bytes). Keep totality on arbitrary
  input; state roundtrip over the well-formed view that `print` produces, where the scan never errors.
  Fix the `PeekStream::next` signature (error state vs `Option<Result<Token>>`) in Phase 0.
- **Byte cursor vs unicode**: syntax is ASCII; UTF-8 only inside string/ident payloads, carried opaque.
  Inspecting inside a payload would be a separate verified UTF-8 step, not a `Chars` axiom.
- **Generics ceremony**: proving through `S: PeekStream` costs more annotation than a monomorphic
  function. If it drags, verify against `TokenStream` directly first (still axiom-free) and generalise
  to the trait in Phase 4; the trait's payoff is multi-implementer reuse, not soundness.

## Logistics

- Module opt-in: one line in `scripts/verus/verify.sh` (`VERIFY_MODULES`).
- Branch: `kg/parser-roundtrip-verify` per `CLAUDE.md` (initials-prefixed, never on `main`).
- Disjoint from `storage/mvcc.rs`: parallel with the MVCC work, zero merge contention.
- Rough total: a proving-out week (Phases 0-1), then ~4-5 weeks for the full expression + statement
  surface and the production cutover; Phase 5 open-ended.

## Prior art (for the colleague)

- Roundtrip/codec style: Narcissus (Coq, ICFP 2019), EverParse/LowParse (F*, USENIX Security 2019),
  Dafny stdlib JSON, AWS Encryption SDK serialisation (Dafny).
- Grammar-correctness style (heavier, not chosen): CompCert C parser via Menhir (Jourdan/Pottier/Leroy,
  ESOP 2012), CoStar (Lasser et al., PLDI 2021), TRX (Koprowski/Binsztok, ESOP 2010),
  Total Parser Combinators (Danielsson, Agda, ICFP 2010).
- Float handling: binary-format verifiers avoid it (floats are bit patterns); textual front-ends
  (CompCert) keep the literal as text and elaborate separately, leaning on Flocq for IEEE reasoning.
