# The exported model against Raft.tla

`Raft.tla` is a hand transliteration of `src/raft/safety.rs` (see
`README.md`). `export/GState_tla.tla` is what Verus's TLA+ exporter
(`verus -V tla-export`, BasisResearch/verus) writes for the same file, with no
hand edits. This document compares the two under TLC at the same bounds:
distinct states, diameter, which of the twelve `inv_*` conjuncts hold, and
the per-conjunct counterexamples to induction (CTIs) of `Raft_cti.tla`. Every
mismatch is traced below to either an exporter bug (fixed in the exporter)
or a genuine difference between `safety.rs` and the transliteration.

In short: with four exporter fixes (BasisResearch/verus#53), the export
reproduces the oracle's state space exactly. It reaches 597,764 distinct
states with diameter 18 at `Raft.cfg`'s bounds, 390,622 with diameter 20 at
`Raft_deep_lc.cfg`'s, and 10,849,481 with diameter 24 at
`Raft_deep_reads.cfg`'s. All twelve conjuncts hold in both models, and the
same six conjuncts have CTIs, produced by the same transitions. The remaining
differences come from two deliberate choices in `Raft.tla`: its (A3) action
guards and its (A5) total-map reads. Removing the (A3) guards from the oracle
reproduces the export's counts exactly.

## What is in `export/`

| file | what it is |
|---|---|
| `GState_tla.tla`, `.cfg`, `.tla.json` | the exporter's output: the module, its `.cfg` skeleton, and the report (recognised triple, holes, refusals, candidates). `export.sh` regenerates all three byte for byte. |
| `RaftExportMC.tla` | extends the export with only what the report asks for: values for the three hole constants, the one variable `Init` leaves unassigned, and `Raft.tla`'s state constraint |
| `RaftExportMC*.cfg` | `Raft.cfg`, `Raft_deep_lc.cfg`, `Raft_deep_reads.cfg` and the two witness configurations, with the same bounds |
| `RaftExportCti.tla`, `.cfg`, `cti.sh` | `Raft_cti.tla`'s seed family `CtiSeed`, restated in the export's representation, and the per-conjunct probe loop |
| `oracle.sh`, `Raft_noA3.cfg`, `Raft_deep_lc_noA3.cfg` | the oracle columns: `oracle.sh a3` runs the same probe loop on `Raft_cti.tla`; `oracle.sh noa3` deletes `Raft.tla`'s four (A3) guard lines in a temporary copy and runs `Raft.cfg` and `Raft_deep_lc.cfg` without `TypeOK` (the two `_noA3.cfg`s), then the probe loop |

The export is taken with the twelve conjuncts named:
`-V tla-export=safety:inv_wf,...,inv_reads`. Without that, the exporter's
default would check only `inv`, which calls all twelve: it treats an
invariant another invariant calls as that invariant's helper.

### What the report asked for, and what fills it

With the fixes below, the export reports 0 refusals, 3 holes, and one
variable `Init` leaves unassigned.

| report entry | value | why it loses nothing |
|---|---|---|
| hole `Dom_Option_Seq_u8_Some_v0`: the payload of `t_propose`'s `cmd: Option<Seq<u8>>` | `{<<1>>, <<2>>}` (`NCommands = 2`; 1 for the deep configurations) | this is `Raft.tla`'s (A2): `Command = {c1, c2}`. The model compares commands only for equality, so any two distinct payloads play the same role. |
| hole `Dom_TStep_LeaderCommit_q`: `t_leader_commit`'s ack map `q: Map<int, nat>` | `UNION {[Q -> 0..MaxLog] : Q \in SUBSET Nodes}` | this is `Raft.tla`'s (A4). `is_quorum(n, q.dom())` puts `q`'s domain inside the nodes, and each `q[v]` is the `mi` of an `Ack` in `net`, which `ack_msg_ok` bounds by a leader-log length, itself at most `MaxLog` under the constraint. |
| hole `Dom_TStep_BumpTerm_term`: `t_bump_term`'s `t: nat` | `1..MaxTerm` | the guard `t > h.term >= 0` gives `t >= 1`. A `t > MaxTerm` would leave the constraint. This is the oracle's `(h.term + 1)..MaxTerm`. |
| `init_unassigned: [hosts]` | `MCInit == n = N /\ hosts = [k \in 1..N \|-> init_host] /\ Init` | `init` says `s.n >= 1`, `s.hosts.len() == s.n` and `s.hosts[i] == init_host()` for every `i`, so `hosts` is determined once `n` is. Fixing `n = N` is `Raft.tla`'s (A1), and every step keeps `post.n == pre.n`. |
| (no `CONSTRAINT`) | `MCConstraint`: `Raft.tla`'s `Constraint` on the export's variables | the same bound: terms, log lengths, read sequence numbers, leader-log lengths, and `Cardinality(net) <= MaxMsgs`. |

Of the three holes, only `q` is a ghost payload. The plan's acceptance
criterion (`plans/tla_export.md`: "the holes list is empty or names only
ghost-payload quantifiers") therefore holds only in part. The command
payload and `t_bump_term`'s term are real step parameters that no guard
bounds from above: `Seq<u8>` is unbounded, and `t > h.term` is the only
guard on `t`. No exporter could bound them, and the values above are the
ones the oracle itself uses.

Everything else is exported as written, in the exporter's general
representation: `n` stays a variable, `hosts` is a sequence (node `i` at
index `i + 1`), and `Msg`, `MRole` and `Option` values are records tagged by
variant (`Raft.tla` uses a `kind` string, role strings and `Nil`). `Seq`
indices are shifted once, as `Raft.tla` does by hand.

## Results

### State space and verdicts

| configuration | | `Raft.tla` | export |
|---|---|---|---|
| `Raft.cfg` (`N=3, MaxTerm=2, MaxLog=2, MaxRead=1, MaxMsgs=7`, two commands) | distinct states | 597,764 | **597,764** |
| | diameter | 18 | **18** |
| | outdegree (avg / max / 95th pct) | 1 / 19 / 4 | 1 / 19 / 4 |
| | states generated | 7,324,630 | 8,796,586 (the oracle without its (A3) guards: 8,796,586) |
| | conjuncts violated | none of 12 | **none of 12** |
| | time on this machine | 1 min 31 s, 4 workers | 2 min 43 s, 12 workers (load average around 60) |
| `Raft_deep_lc.cfg` (`N=2, MaxLog=2, MaxMsgs=10`, one command) | distinct states / diameter | 390,622 / 20 | **390,622 / 20** |
| | states generated | 4,404,097 | 5,075,165 (the oracle without (A3): 5,075,165) |
| | conjuncts violated | none | **none** |
| `Raft_deep_lc_witness.cfg` (expected to fail) | `NoLC` violated, trace length | 13 states | **13 states** |
| `Raft_deep_reads_witness.cfg` (expected to fail) | `NoR2` violated, trace length | 14 states (see below) | **14 states** |
| `Raft_deep_reads.cfg` (`N=3, MaxLog=1, MaxMsgs=12`, one command) | distinct states / diameter | 10,849,481 / 24 | **10,849,481 / 24** (one worker; 16 workers report 25, see below) |
| | states generated | 159,660,571 | 185,460,271 |
| | conjuncts violated | none | **none** (1 h 10 min on 16 workers, load average above 100) |

The twelve conjuncts are checked separately in both models: `inv_wf`,
`inv_hosts`, `inv_msgs`, `inv_lterms`, `inv_ack_persist`, `inv_vote_persist`,
`inv_commits`, `inv_leader_completeness`, `inv_commit_msgs`,
`inv_host_commits`, `inv_commit_leaders` and `inv_reads`. All hold in every
configuration, which is what the Verus proof (`step_preserves_inv`)
predicts. The witnesses show that two of them hold non-vacuously in the deep
configurations: `NoLC` for leader completeness and `NoR2` for `inv_reads`'s
R2 clause. Both witnesses are `Raft.tla`'s definitions restated in
`RaftExportMC.tla`.

TLC's depth with several workers is an upper bound, not the breadth-first
depth: a state may first be reached through a longer path. At
`Raft_deep_reads.cfg`'s bounds the export's 16-worker run reported 25. A
one-worker run of each model gives 24 for both, with the oracle generating
159,660,571 states and the export 185,460,271. The export's one-worker run
steps with `next` rather than `Next == next /\ TypeOK'`, to cut its time,
and finds the same 10,849,481 states, so `TypeOK'` excludes nothing there.
At `Raft.cfg`'s and `Raft_deep_lc.cfg`'s bounds, one-worker runs of the
export (with `Next`, as configured) give the same diameters as the table, 18
and 20.

`README.md` gave the reads witness as a 15-state trace; it now says 14.
TLC's breadth-first search returns a shortest trace only with one worker. Run
here with one worker, the oracle's shortest witness has 14 states, and so
does the export's.

### The CTI table

Each probe seeds `CtiSeed` (the post-term-1-commit configuration of a
three-node cluster) conjoined with one conjunct, takes one step, and checks
that conjunct on the successor. The export's probe uses the same seed in the
export's representation. The seed sizes agree: 10,560 states, 1,608 under
`inv_hosts`, 966 under `inv_msgs`, and 124 under the whole invariant.

| conjunct | `Raft_cti.tla` CTIs | export CTIs | `Raft_cti.tla` without (A3) | transition |
|---|---|---|---|---|
| `inv_wf` | 0 | 0 | 0 | |
| `inv_hosts` | 0 | 0 | 0 | |
| `inv_msgs` | 162 | 432 | 432 | `t_campaign` (56 / 326 / 326), `t_send_ack` (106 / 106 / 106) |
| `inv_lterms` | 2,904 | 3,672 | 3,672 | `t_become_leader` |
| `inv_ack_persist` | 2,112 | stops at an off-domain read, after 192 CTIs (three runs) | 2,112 | `t_send_ack` |
| ↳ only acks whose term has a leader log | 384 | **384** | 384 | `t_send_ack` |
| `inv_vote_persist` | 192 | 192 | 192 | `t_send_ack` |
| `inv_commits` | 0 | 0 | 0 | |
| `inv_leader_completeness` | 2,304 | 2,304 | 2,304 | `t_become_leader` |
| `inv_commit_msgs` | 0 | 0 | 0 | |
| `inv_host_commits` | 192 | 192 | 192 | `t_recv_commit` |
| `inv_commit_leaders` | 0 | 0 | 0 | |
| `inv_reads` | 0 | 0 | 0 | |
| all twelve (`CtiInit_all`) | 0 | 0 | 0 | |

The CTI counts are violating successor states under `-continue`.
`README.md`'s table lists which conjuncts have CTIs and the transitions that
produce them; this table adds the counts. The export's transition is read
off the disjunct of `next` that TLC names (the probe's `NEXT` is `next`, not
`Next == next /\ TypeOK'`, so TLC splits it by variant).

## The mismatches

### Exporter bugs, fixed in the exporter (BasisResearch/verus#53)

The first export of `safety.rs` could not be checked at `Raft.cfg`'s bounds.
There were four gaps, each fixed generally, with a TLC-checked test in
`rust_verify_test/tests/tla_export.rs`
(`tla_export_bounds_message_fields_and_step_fields_from_their_guards`):

1. **`Set::range` was refused.** `node_ids(n)` is
   `Set::<int>::range(0, n as int)`, which lowers to the trait method
   `FiniteRange::range_set` with no body. The refusal took `inv_hosts`,
   `inv_lterms` and `inv_commits` out of the `.cfg`. Integer ranges now
   print as `lo..hi-1`.
2. **Quantifiers bound by a message in `net` were holes.**
   `forall|c, t, clog| s.net.contains(Msg::Campaign { c, term: t, clog }) ==> ...`
   left one `Dom_<type>` hole per binder: 44 across the invariants. Filled
   from the bounds, their products are too many to enumerate per state:
   `inv_msgs`'s vote-uniqueness clause alone quantifies six binders, about
   1.5 * 10^5 combinations per state at `Raft.cfg`'s bounds. A binder that is a field
   of a constructor in a membership guard now ranges over
   `{m.c : m \in {m \in net : m.tag = "Campaign"}}`. This is exactly
   `Raft.tla`'s (A6), now done by the exporter.
3. **A guarding disjunction stopped TLC.** `t_recv_append`'s
   `b == 0 || (b <= h.log.len() && h.log[b - 1].term == bt)` printed as
   `\/`. TLC branches on a disjunction inside an action, evaluated `h.log[0]`
   at `b = 0`, and stopped. `README.md` records the same trap, which the
   transliteration avoided by hand with an `IF`. The exporter now prints
   such a disjunction as `IF a THEN TRUE ELSE b` wherever neither side reads
   the post state and the operator is not one `Init` reaches.
4. **The step enum was enumerated whole.**
   `exists|step: TStep| next_step(pre, post, step)` became
   `\E step \in (union of every variant's values)`. That left 41 hole
   constants for the fields, and TLC built about 8,000 step records per
   state before evaluating any guard. The exporter now writes one `\E` per
   variant and bounds each field from the guard of the transition its match
   arm calls (`0 <= i < pre.n`, `pre.net.contains(Msg::Append { .. })`,
   `b <= e <= h.log.len()`, `c <= h.commit`, ...). That leaves 3 holes,
   the ones listed above. On this machine, at similar load, TLC went from
   about 33,000 to about 300,000 distinct states a minute.

With these fixes, nothing in the export is hand-edited.

### Genuine differences between `safety.rs` and `Raft.tla`

- **(A3): action-level bounds.** To keep TLC from type-checking successors
  one step past a bound, `Raft.tla` adds guards to `t_campaign`
  (`h.term < MaxTerm`), `t_become_leader` and `t_propose`
  (`Len(h.log) < MaxLog`) and `t_submit_read` (`h.read_seq < MaxRead`).
  `safety.rs` has no such guards, so the export takes those steps and the
  state constraint then excludes the successors. The same states are
  explored, but TLC generates more (8,796,586 against 7,324,630, and
  5,075,165 against 4,404,097). In the probes, the export also has CTIs
  that the guards remove from the oracle: `t_campaign` into term 3 for
  `inv_msgs`, and `t_become_leader` past `MaxLog` for `inv_lterms`.
  Deleting the four guards from a copy of `Raft.tla` reproduces every one
  of the export's numbers: 8,796,586 and 5,075,165 generated, 432 and
  3,672 CTIs (`export/oracle.sh noa3`). That copy has to be checked
  without `Raft.tla`'s `TypeOK`: without the guards, TLC evaluates the
  invariants on a successor one step past `MaxTerm`, `MaxLog` or `MaxRead`
  before the constraint drops it, and `TypeOK`'s bounded domains
  (`1 .. MaxTerm`, `Logs`, `1 .. MaxRead`) do not contain it. That is
  exactly what the guards are for, so `Raft_noA3.cfg` and
  `Raft_deep_lc_noA3.cfg` are `Raft.cfg` and `Raft_deep_lc.cfg` without
  `TypeOK`. The export's own invariants need no such guards, because
  they have no bounded type domains to leave.
- **(A5): Verus's `Map` is total; TLA+ functions are not.** `safety.rs`
  reads `s.leader_log[t]` in places where only a sibling conjunct
  guarantees that `t` is in the domain. Off the domain, Verus has an
  unspecified value. `Raft.tla` reads through `LL(t)`, which returns `<< >>`
  there. The export prints `leader_log[t]`, which TLC refuses to evaluate
  off the domain: it stops rather than choose a value. The exporter's rule
  is never to narrow silently, and picking `<< >>` would narrow. The
  difference shows up in one place only:
  - **In reachable states, never.** Every conjunct and every step was
    evaluated on every reachable state of every configuration above, and on
    the successors past the bound, without an evaluation error. So at these
    bounds, every map read in `safety.rs`'s invariants and transitions is
    inside its domain. The oracle cannot show this, because its `LL` hides
    such reads.
  - **In the `inv_ack_persist` probe.** From a seed where node 2 is a
    term-2 candidate with no term-2 leader, `t_send_ack(2)` emits
    `Ack(2, 2, mi)`. `ack_persist_ok` then compares node 2's log with
    `leader_log[2]`, which is off the domain. The oracle compares with
    `<< >>` and reports a CTI; the export stops. In Verus's terms the
    successor violates the conjunct for some values of `leader_log[2]` and
    not for others. A proof by induction must cover every value, so the
    oracle's CTI is a real obligation for the proof. TLC, however, cannot
    enumerate an unspecified value. The probe restricted to acks whose term
    has a leader log, `inv_ack_persist_dom` (in `RaftExportCti.tla`, and in
    `Raft_cti.tla` over the oracle's representation), gives 384 CTIs in
    both models. The other 1,728 of the oracle's 2,112 all rest on `LL`
    returning `<< >>`. Both sides seed and check it the same way: `INIT` is
    `CtiInit_ack_persist`, the seed conjoined with the *full*
    `inv_ack_persist`, and `INVARIANTS` is `inv_ack_persist_dom`, checked on
    the successors. On the seed family the two conjuncts coincide, because
    every seed ack has term 1, which is in `DOMAIN leader_log`; so the seed
    is the same 10,560 states either way, and the export can evaluate it.
    Only the check on the successor is restricted.
- **(A1), (A2), (A4), (A6)** are now choices of hole values or exporter
  behaviour, not transliteration: `n` is set by `MCInit`, and commands and
  ack maps take the values in the table above. (A6) is fix 2.
- **`TypeOK`.** `Raft.tla`'s `TypeOK` is a hand-written structural type,
  checked as a thirteenth invariant. The export's `TypeOK` keeps each
  integer field in its Rust type's range and is conjoined to `Init` and
  primed into `Next`, so it holds by construction and is not listed as an
  invariant.
- **`voter_ok` and `lterm_ok`'s `let`s.** `Raft.tla` hoists the domain
  check above `let vlog = s.elect_votes[u][x]` because "function
  application is not total". The export keeps the Rust order, which is
  sound in TLA+ because a `LET` is evaluated only where it is used, after
  the domain conjunct. No run hit it.

No other difference was found. Nothing in `safety.rs` disagrees with the
transliteration in a way TLC can observe at these bounds.

## Running it

With the exporter from BasisResearch/verus#53 (a source build runs with
`VERUS_MCP_ENABLED=1`) and the TLA+ tools:

    VERUS=<verus> tla/export/export.sh        # regenerate GState_tla.*
    cd tla/export
    java -XX:+UseParallelGC -cp <jar> tlc2.TLC -workers 4 -continue -config RaftExportMC.cfg RaftExportMC.tla
    java -XX:+UseParallelGC -cp <jar> tlc2.TLC -workers 4 -continue -config RaftExportMC_deep_lc.cfg RaftExportMC.tla
    java -XX:+UseParallelGC -cp <jar> tlc2.TLC -workers 1 -config RaftExportMC_deep_lc_witness.cfg RaftExportMC.tla
    java -XX:+UseParallelGC -cp <jar> tlc2.TLC -workers 1 -config RaftExportMC_deep_reads_witness.cfg RaftExportMC.tla
    java -XX:+UseParallelGC -cp <jar> tlc2.TLC -workers 16 -continue -config RaftExportMC_deep_reads.cfg RaftExportMC.tla
    java -XX:+UseParallelGC -cp <jar> tlc2.TLC -workers 1 -config RaftExportMC_deep_reads.cfg RaftExportMC.tla
    JAR=<jar> ./cti.sh                         # the CTI table's export column
    JAR=<jar> ./oracle.sh a3                   # its Raft_cti.tla column
    JAR=<jar> ./oracle.sh noa3                 # the "without (A3)" numbers

The witnesses run with one worker, since only then is TLC's search
breadth-first and the trace a shortest one: with four workers the reads
witness has come out at 15 states instead of 14. With several workers the
depth TLC reports is an upper bound on the diameter, not the diameter. The
16-worker `Raft_deep_reads.cfg` run gives the verdicts (and reports depth
25). The one-worker run after it gives the diameter, 24; it is much
slower. The `Raft.cfg` and `Raft_deep_lc.cfg` diameters (18 and 20) are
also the same with one worker as with four.

Verus empties its `--log-dir`, so `export.sh` exports into a temporary
directory and copies the three files. The `.cfg`s set
`CHECK_DEADLOCK FALSE`, which is the exporter's default; `-deadlock` is not
needed. The oracle's state-space and witness numbers come from the commands
in `README.md`. `oracle.sh` prints the oracle's CTI counts. With `noa3` it
also prints the state counts with the four lines marked
`\* bound, see (A3)` deleted, checked without `TypeOK` (see (A3) above).
