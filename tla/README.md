# Raft.tla

`Raft.tla` is a transliteration of `src/raft/safety.rs` — the Verus model of
the Raft protocol that `src/raft/refine.rs` proves `raft::node` refines —
into TLA+, so that TLC can enumerate concrete reachable states of the
protocol alongside the Verus proof. It is meant to be read next to the Rust:
every `t_*` transition, every `inv_*` conjunct and every spec helper
(`prefix_eq`, `splice`, `log_pinned`, `mid_compliant`, …) keeps its Rust
name and its conjunct order, and each action carries a comment naming the
`t_*` it mirrors. `GState`'s ten fields are the ten TLA+ variables; `Msg` is
a set of records discriminated by a `kind` field, carrying the ghost
payloads the model defines (`clog`, `vlog`, the commit record behind a
heartbeat) because the invariants quantify over them. Verus `Seq<AEntry>`
entry `k` models implementation index `k+1`; TLA+ sequences are 1-based, so
the TLA+ index *is* the implementation index, and every index expression is
shifted accordingly (`h.log[b - 1].term` becomes `h.log[b].term`).

`Raft_cti.tla` is the inductiveness probe: it replaces `INIT` with the
invariant and takes one step, the question Verus's `step_preserves_inv` is
asking.

## Bounds and results

`Raft.cfg` fixes a three-node cluster (`N = 3`), terms at `MaxTerm = 2`, log
length at `MaxLog = 2`, one read sequence number per term (`MaxRead = 1`),
commands from the two-element payload alphabet `{c1, c2}` plus `Nil` for the
election noop, and — the bound that actually decides the size of the model —
at most seven messages in the monotone history (`MaxMsgs = 7`). `Constraint`
states all five. Seven is the smallest message budget in which a commit is
reachable: an election costs three messages (campaign, self-vote, one
grant), the leader's self-ack a fourth, an append a fifth, the follower's
ack a sixth, and the commit announcement a seventh. At `MaxMsgs = 6` the
model exhausts in 2 min 28 s with 154,898 distinct states but never commits;
at `MaxMsgs = 8` it was still running past a million distinct states after
eight minutes.

At those bounds TLC exhausts the state space in **4 min** on four workers
(5 min 26 s with `-coverage 1`): 7,324,630 states generated, **597,764
distinct**, diameter **18**, average outdegree 1 (maximum 19), no invariant
violated. `TypeOK` and all
twelve `inv_*` conjuncts are listed separately in `INVARIANTS`, so a
violation would name the conjunct rather than the conjunction. None was
found, which is what the Verus proof predicts — every violation TLC did
report during development was a transliteration error, and the two that
mattered are recorded under "approximations" below.

All sixteen actions fire. Distinct states contributed, then invocations,
from `-coverage 1`:

    t_restart      305,483 : 1,866,084      t_send_ack      27,936 :   842,052
    t_bump_term    147,316 :   822,264      t_recv_append   25,067 :   943,797
    t_step_down     33,278 :    55,155      t_send_append   16,583 :   968,967
    t_campaign      11,681 :   625,239      t_submit_read    9,947 :   156,663
    t_confirm_read   6,366 :    70,320      t_propose        4,079 :    49,779
    t_recv_commit    2,874 :    85,338      t_grant          2,327 :   729,690
    t_collect_vote   2,032 :    66,459      t_become_leader  1,744 :     4,470
    t_leader_commit  1,050 :    28,290      t_send_commit        0 :    10,062

`t_send_commit` is enabled ten thousand times and produces no new state.
That is not dead code: it re-announces a commit index the leader already
holds, and the message it inserts, `Commit(h.term, ci, h.crec)`, is for
`ci = h.commit` the very message `t_leader_commit` already inserted into a
monotone set, so the post-state equals the pre-state; for `ci < h.commit` the
message would be new, but a commit is only reachable at exactly seven
messages, so an eighth is pruned by the bound. Raising `MaxMsgs` is what
would separate those two cases.

Two conjuncts hold only vacuously at these bounds, and it is worth being
exact about which. Checking the negated witnesses over the whole reachable
set: a commit is reachable, two elected terms are reachable, and a
crash-restart that regresses a commit index below its own witness record is
reachable (81,702 states) — but no reachable state has **both** a commit and
a strictly later elected term, so `inv_leader_completeness`'s antecedent is
never satisfied; and no read record's `born` set ever contains a commit of a
higher term, so `read_rec_ok`'s R2 clause, the linearizability core of
`inv_reads`, is never satisfied either. Both need a second election after a
commit, which costs three messages more than the budget. The rest of
`inv_reads` (`read_msg_ok`, `confirm_msg_ok`, the sequence-number bounds) and
all four commit conjuncts (`inv_commits`, `inv_commit_msgs`,
`inv_host_commits`, `inv_commit_leaders`) are exercised non-vacuously.

## Approximations

Everything the transliteration could not carry across literally is listed
as `(A1)`–`(A8)` in the module header and repeated at each site. In short:
the cluster size `n` is a constant rather than a state field (every
transition preserves it); `Option<Seq<u8>>` commands are abstracted to a
finite alphabet (the model only ever compares entries for equality);
`t_bump_term`'s term, `t_campaign`'s term bump, `t_propose`'s and
`t_become_leader`'s log growth and `t_submit_read`'s sequence number carry
their bound in the action guard as well as in `CONSTRAINT`; `t_leader_commit`
quantifies its ack map over `[Q -> 0..MaxLog]`; Verus `Map` is total, so
the two places the Rust indexes `leader_log` or `leader_of` without a local
domain guard read through `LL(t)` / `LOf(t)`, which return an empty log and
node 0 off-domain; parameters the Rust binds by `net.contains(Msg::X{..})`
are bound here by `\E m \in net : m.kind = "X"`; and `Cardinality(net)` is
bounded, which truncates behaviours and makes this a bounded check rather
than a proof.

Two of those deserve their own note, because both were found by TLC
reporting a violation that turned out to be about TLC, not about the model.
First, TLC evaluates the invariants on a successor *before* it applies the
state constraint (`ModelChecker.doNext`: the `unseen` branch runs whether or
not `inModel`), so a state one step past `MaxTerm` or `MaxLog` is
type-checked against domains that do not contain it. That is why the term
and log bounds are in the action guards and not only in `CONSTRAINT`; the
set of states TLC explores is the same either way, since a state the
constraint excludes is never enqueued. The `MaxMsgs` bound needs no such
guard, because every conjunct genuinely holds on the one-message-past states.
Second, in next-state position TLC branches on a disjunction rather than
short-circuiting it, so `t_recv_append`'s Rust guard
`b == 0 || (b <= h.log.len() && h.log[b-1].term == bt)` had to become an
`IF b = 0 THEN TRUE ELSE …`; as a disjunction TLC evaluated `h.log[b]` with
`b = 0` and died. `TypeOK` itself is written structurally (`DOMAIN` tests and
`\A` over members) rather than as membership in the constructed domains,
which are kept alongside it for the CTI probe: a membership test in
`[V -> Logs]` enumerates up to `|Logs|^|V|` functions and dominated the run
by roughly seven times before the rewrite.

## The inductiveness probe

`Raft_cti.tla` with `Raft_cti.cfg` is `tlc_cti` written out by hand: `INIT`
becomes `TypeOK /\ Inv`, `CONSTRAINT` is `TLCGet("level") < 2`, and every
`inv_*` conjunct is checked on the successor. It does not run, and it cannot
be made to run by shrinking the constants. TLC's initial-state computation
needs `var \in Set`, so `CtiTypeOK` restates the domains in that form; TLC
then refuses with "Attempted to construct a set with too many elements
(>1000000)" on `elect_votes`, and at the tightest bounds that still describe
a cluster (`N = 2`, `MaxTerm = 1`, `MaxLog = 1`, one command) with
"Overflow when computing the number of elements in `SUBSET CommitRecs`" —
the `born` field of a read record is a set of commit records, and a commit
record carries a function, so the domain is a powerset of a powerset. The
message history is the same problem: `net \in SUBSET Messages` over a
universe of about a hundred messages is `2^100` candidate states. This is
the `enumBound` refusal that `tlc_tools.md` anticipates, and for this model
it is unconditional.

What does work is seeding a small explicit family instead. `CtiSeed` is the
configuration just after term 1 elected node 0 and committed its noop, with
node 1's term, vote and commit index, node 2's entire state, and the
messages of a term-2 election left free — 10,560 states, all type-correct.
Conjoined with one `inv_*` conjunct it becomes an enumerable `INIT`, and
`CtiInit_<conjunct>` does that for each of the twelve. Six have a
counterexample to induction in that family, which is expected and is the
point: the Rust proves only the conjunction inductive.

| conjunct | action | changed |
|---|---|---|
| `inv_msgs` | `t_send_ack(2)`, `t_campaign(2)` | `net` (`hosts` too, for campaign) |
| `inv_lterms` | `t_become_leader(2)` | `leader_log`, `leader_of`, `voters`, `elect_log`, `elect_votes`, `hosts` |
| `inv_ack_persist` | `t_send_ack(2)` | `net` |
| `inv_vote_persist` | `t_send_ack(2)` | `net` |
| `inv_leader_completeness` | `t_become_leader(2)` | `leader_log`, `leader_of`, `voters`, `elect_log`, `elect_votes`, `hosts` |
| `inv_host_commits` | `t_recv_commit(2)` | `hosts` |

The `inv_ack_persist` one reads cleanly: node 2 sits at term 1 with the log
`<<[term 1, cmd]>>` while the term-1 leader log is `<<[term 1, Nil]>>`. No
ack by node 2 exists, so `inv_ack_persist` holds vacuously; `t_send_ack(2)`
then emits `Ack(2, 1, 1)` and `ack_persist_ok(2, 1, 1)` demands
`prefix_eq(hosts[2].log, leader_log[1], 1)`, which is false. The pre-state is
unreachable — `inv_hosts`'s `log_pinned` forbids it — which is exactly why
`ack_persist_ok` needs `log_pinned` next to it in the conjunction, and why a
CTI is a proof hint rather than a bug report. The `inv_lterms` and
`inv_leader_completeness` ones both fire on `t_become_leader(2)`: a fresh
term-2 leader log starting with a term-2 noop cannot contain the term-1
entry that term 1 committed, unless the up-to-date check and the vote
quorum ruled that pre-state out. `CtiInit_all`, the same family conjoined
with the whole `Inv`, leaves 124 states and finds nothing, which agrees with
`step_preserves_inv`.

The remaining six — `inv_wf`, `inv_hosts`, `inv_commits`,
`inv_commit_msgs`, `inv_commit_leaders`, `inv_reads` — produced no CTI *in
this family*. That is not a claim that they are inductive on their own; the
family is narrow.

## Running it

With the jar from the fork's build (`tlaplus/tlatools/org.lamport.tlatools/dist/tla2tools.jar`):

    cd tla
    java -XX:+UseParallelGC -cp <jar> tlc2.TLC -workers 4 -deadlock Raft.tla
    java -XX:+UseParallelGC -cp <jar> tlc2.TLC -workers 4 -deadlock -coverage 1 Raft.tla

`-deadlock` is needed because a state where every host is a follower at
`MaxTerm` with a full log has no successor, and that is not an error here.
The CTI probes want an explicit config and `-continue`, so that one run
reports every conjunct:

    java -cp <jar> tlc2.TLC -workers 2 -deadlock -continue -config Raft_cti.cfg Raft_cti.tla
    java -cp <jar> tlc2.TLC -workers 2 -deadlock -continue -config Raft_cti_small.cfg Raft_cti.tla

`Raft_cti_small.cfg` names `CtiInit_all`; edit its `INIT` to
`CtiInit_<conjunct>` and its `INVARIANTS` to that one conjunct to reproduce a
row of the table.

Through the resident checker of the TLC fork, the same run is:

    java -cp <jar> tlc2.basis.Resident

then, one JSON object per line on stdin,

    {"command":"open","spec":"Raft.tla","workers":4}
    {"command":"check","budget_ms":600000,"continue":true}
    {"command":"coverage"}
    {"command":"close"}

`check` returns a per-conjunct verdict rather than stopping at the first
violation, and `screen` evaluates candidate conjuncts over the states
already explored, which is the Houdini loop over `inv` this model exists to
feed. The `tlc_*` MCP tools drive exactly that protocol.
