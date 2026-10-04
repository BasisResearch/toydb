# inductive_loop on the Raft safety model

The acceptance run of the `inductive_loop` MCP tool (verus-tools-mcp,
`kg/inductive-loop`; plan: `verus-research/plans/inductive_loop.md`, steps 3
and 4) against this repository's Raft model: `src/raft/safety.rs` (the Verus
model and its proof) and `tla/Raft.tla` / `tla/Raft_cti.tla` (its TLA+
transliteration and the `CtiSeed` family). Nothing under `src/` or `tla/` was
changed.

`rounds/` holds every call's complete record (`NN-name.json`, the tool's
artifact) and the preview the agent sees (`NN-name.preview.txt`). Paths in
them are relative to this checkout (`src/…`, `tla/…`); `<tmp>` is the test's
temporary directory and `~` the home directory of the machine that ran it.
The run is the test `tests/inductive_loop_raft.rs` of verus-tools-mcp:

    TOYDB_DIR=<this checkout> INDUCTIVE_LOOP_EVIDENCE=<dir> RAFT_TLC_WORKERS=8 \
    VERUS_MCP_TLC_JAR=~/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar \
    VERUS_BIN=<Verus fork kg/model-tools 95e162cf>/source/target-verus/release/verus \
    cargo test --test inductive_loop_raft -- --nocapture

verus-tools-mcp `d2e54ed`, TLC fork `basis-11305b4a05`, Verus fork `95e162cf`
(cvc5), 2026-09-27, one 32-core box. Whole run 9 min 41 s. The test's
assertions below were added in verus-tools-mcp `48983c6` and pass against a
clean build of Verus `95e162cf` (rerun 2026-09-27, 7 min 28 s). The records
here come from the `d2e54ed` run, with their paths rewritten afterwards into
the repo-relative form that `48983c6` writes itself.

What the test asserts, per round: both screens ran to the end over all
597,764 states. Round `02`: no drop of either kind, one induction search
from 124 pre-states, and all 24 obligations `valid`. Round `03`:
`terms_le_1` is the only reachability drop and carries a state;
`net_within_bound` is the only induction drop, relative to all 13
conjuncts, with its pre and post state; twelve survive and all 24
obligations are `valid`. Rounds `04`–`15`: no reachability drop, the six
conjuncts below drop by induction on the action named in the table
(`inv_msgs` only on the `t_` prefix), and the other six are `screened`.
Costs, levels, fingerprints and the exact steps of round `03` are recorded,
not asserted.

## Setup

`tlc_open` on `tla/Raft_cti.tla` under `tla/Raft.cfg` (N = 3, MaxTerm = 2,
MaxLog = 2, MaxRead = 1, MaxMsgs = 7; `Raft_cti` extends `Raft` and adds
`CtiSeed`), eight workers, coverage off; `tlc_check` to exhaustion:
**597,764 distinct states**, diameter 18, every invariant
`no_violation_found`, 213 s exploring (`00`, `01`).

Every round below passes `model_session` (that session), `model_path`
(`src/raft/safety.rs`), `state_type: GState`, `typing: CtiSeed`, and the proof
bodies

    init: init_implies_inv(s);
    step: let step = choose|step: TStep| next_step(pre, post, step);
          step_preserves_inv(pre, post, step);

The candidates are the conjuncts, never the proof: the tool generates one
`init(s) ==> c(s)` and one `il_candidate_inv(pre) && next(pre, post) ==>
c(post)` proof fn per surviving conjunct, with those bodies, in a scratch
module that includes `safety.rs` through a link and is opened as its own Verus
session (verified scope: the scratch module; `safety.rs`'s lemmas are used
through their `ensures`). The scratch text is in each round's
`verus.scratch_text`.

## Step 3: the twelve `inv_*` conjuncts (`02-round-twelve`)

| | |
|---|---|
| dropped by reachability | none (all twelve hold on all 597,764 states) |
| dropped by induction | none: one search from `CtiSeed /\ c1 /\ … /\ c12`, **124** pre-states, 2,436 steps, no counterexample |
| Verus | **inductive**: 24 of 24 obligations `valid` |
| verdict | `inductive` |

Cost: 61.6 s total — reachability screen 47.6 s (597,764 states), induction
search 3.7 s, scratch session open 7.9 s, 24 `check_session` calls 2.0 s
(solver 1.8 s).

The six conjuncts that are not inductive alone (below) survive here because
they are checked as a conjunction, which is what the plan expected and what
`step_preserves_inv` states.

## Step 4: two wrong candidates beside the twelve (`03-round-twelve-plus-wrong`)

- `terms_le_1` (`forall|i| 0 <= i < s.n ==> s.hosts[i].term <= 1`): **dropped
  by reachability**. False on 546,546 stored states. The record carries the
  first violating state in the screen's scan order, at BFS level 11 with a
  10-action behaviour. It is not the shallowest: `t_bump_term` has no guard,
  so one step from `Init` already puts a host at term 2. The screen reports
  a violating state and a behaviour that reaches it (fingerprint, state and
  actions in the record), not a shortest one.
- `net_within_bound` (`s.net.len() <= 7`, the model's own `MaxMsgs` bound):
  true on every stored state, since the bound is what kept them stored, but
  **dropped by induction**: from a `CtiSeed` state with six messages,
  `t_campaign(1)` adds two, its `Campaign` message and its self-`Vote`, for
  eight. The drop records the 13-conjunct conjunction it was relative to; a
  second search over the remaining twelve finds nothing.
- Verus proves the other twelve: 24 of 24 obligations `valid`, verdict
  `inductive`.

Cost: 68.2 s — screen 48.6 s, two induction searches 9.6 s (200 pre-states,
3,894 steps), Verus open 7.7 s, 24 checks 2.1 s.

## Each conjunct alone (`04`–`15`, `screen_only`)

A `screen_only` round per conjunct (no Verus: one conjunct alone cannot use
`step_preserves_inv`). It reproduces toyDB PR #25's hand-run table exactly,
now through the tool:

| conjunct | alone | step |
|---|---|---|
| `inv_wf` | survives | |
| `inv_hosts` | survives | |
| `inv_msgs` | **dropped by induction** | `t_campaign(2)` |
| `inv_lterms` | **dropped by induction** | `t_become_leader(2)` |
| `inv_ack_persist` | **dropped by induction** | `t_send_ack(2)` |
| `inv_vote_persist` | **dropped by induction** | `t_send_ack(2)` |
| `inv_commits` | survives | |
| `inv_leader_completeness` | **dropped by induction** | `t_become_leader(2)` |
| `inv_commit_msgs` | survives | |
| `inv_host_commits` | **dropped by induction** | `t_recv_commit(2)` |
| `inv_commit_leaders` | survives | |
| `inv_reads` | survives | |

Each such round costs 14–32 s (a reachability screen of 5–21 s and one
search of up to 10,560 pre-states and 233,824 steps).

## What the verdicts rest on

- **Verus is the verdict of record.** A round says `inductive` only when
  every obligation came back `valid` from `check_session`. The model checker
  only screens, and only within `Raft.cfg`'s bounds and the `CtiSeed` family.
  A candidate it keeps can still fail in Verus. The counter test in
  verus-tools-mcp shows this with `x != -1`, which the typing never reaches
  and Verus refutes.
- **The model's lemmas are trusted in the scratch session.** It verifies
  only the obligations and uses `init_implies_inv` and `step_preserves_inv`
  through their `ensures`. That proof verifies with upstream Verus and z3:
  the `Upstream Verus gate (z3)` job for this PR's base commit `260c949a`
  (run on PR #16's merge ref, which carries the same `safety.rs`; upstream
  Verus `0.2026.08.30.b432e82`, `raft::safety` among the gated modules, job
  passed;
  [run 36170503453](https://github.com/BasisResearch/toydb/actions/runs/36170503453/job/108188594069)).
  `safety.rs` is unchanged between that commit and this PR. Under the Basis
  fork, which always uses cvc5, it does not verify:
  `model-proof-under-cvc5.txt` records a standalone run of `safety.rs` with
  the fork build the rounds used (`95e162cf`), 21 functions verified and 20
  errors. Every `*_preserves` lemma, the `recv_append_*` helpers and
  `execution_implies_inv` exceed the rlimit. So the rounds' `inductive` is
  conditional on the z3 proof in CI, not on anything this run checked.
  `verify_model: true` makes the scratch session verify the model as well,
  which under the fork would report those twenty failures, not a proof of
  the candidates.
- **Nothing is dropped silently.** Every drop carries its state or its step,
  and the conjunction it was relative to. States are TLA+ values here,
  because this session is a `tlc_open` over the hand-written transliteration.
  Over a `model_open` session the same round renders them as Verus values
  with the `t_*` step (see the counter test `a_model_session_screens_in_verus_terms`).
