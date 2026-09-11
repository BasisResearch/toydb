//! Node-local refinement of `raft::node` against the `raft::safety` model:
//! one verified *step function* per protocol input, proving that the step's
//! decision logic and state change implement (a sequence of) model
//! transitions.
//!
//! # Architecture (verified core / thin I/O shell)
//!
//! The verified state of a node is split between two types whose fields are
//! private and mutated only by verified code:
//!
//! * [`super::log::Log`]: the durable state (term, vote, entries, commit),
//!   verified against a ghost view of the stored entries (see `log.rs`).
//! * [`Abs`]: the member set ([`Members`], ranks 0..n agreed across the
//!   cluster), the volatile role state (candidate votes, leader
//!   [`Progress`]), the node's ghost abstract state (an `MHost` of the
//!   safety model), and the ghost *evidence* set of abstract messages this
//!   node has received or sent.
//!
//! `node.rs` is reduced to an I/O shell: it decodes a message, calls the one
//! step function for that message kind (`Abs::follower_heartbeat`,
//! `Abs::grant`, `Abs::leader_try_commit`, ...), and sends the messages named
//! by the returned plan. All decisions — vote grants, quorum counts, commit
//! advancement, the linearizable-read gate — and all log mutations happen
//! inside the step functions.
//!
//! # The refinement statement
//!
//! Each step function ensures [`host_refines_star`]: **from every
//! invariant-satisfying global model state consistent with this node's view
//! (its abstract state `habs`, plus its evidence being in the message
//! history), there is a sequence of model transitions that performs exactly
//! this host's state change and message emissions, ending in an
//! invariant-satisfying state.** The safety model's theorems (election
//! safety, log matching, leader completeness, state machine safety,
//! linearizable reads) hold in every invariant-satisfying state, so they
//! apply to every reachable configuration of the implementation, provided
//! the trusted assumptions below hold. The composition into a cluster-level
//! statement is itself formal: see the "Cluster composition" section
//! ([`cluster_bound`], `lemma_cluster_*`, [`thm_impl_safety`]).
//!
//! # Trusted assumptions
//!
//! 1. **Network non-forgery + angelic ghost recovery** ([`recv_msg`], the
//!    single trusted network function): every message the shell receives has
//!    an abstract counterpart in the model's message history, and `recv_msg`
//!    returns that counterpart. Its specification pins every field the
//!    concrete message carries (for an Append, the entries' terms and
//!    commands included); the payloads the concrete message only summarizes
//!    (the candidate log behind a Campaign's last_index/last_term, the
//!    commit record behind a heartbeat's commit_index) are "whatever they
//!    truly were" at the sender.
//! 2. **Storage integrity**: the engine rim in `log.rs` (see there).
//!    [`recover_host`] additionally trusts that the state recovered from the
//!    durable log at startup is the model state of this host — the initial
//!    state on a fresh start, or a `t_restart` post-state after a crash.
//! 3. **Composition**: `host_refines_star` is a per-node statement. Reading
//!    the per-node guarantees as a statement about the running cluster
//!    assumes all nodes' ghost states are simultaneously bound to one model
//!    state whose history contains every message ever sent. This binding is
//!    stated formally by [`cluster_bound`], established for a fresh cluster
//!    by `lemma_cluster_init` and maintained across every step function
//!    call and crash-restart by `lemma_cluster_step` /
//!    `lemma_cluster_restart` — the interleaving argument is machine-
//!    checked. What this assumption still asserts is that those lemmas'
//!    hypotheses track the real run: every mutation of a node's verified
//!    state is one step function call (assumption 5), nodes recover per
//!    assumption 2, and received messages' counterparts are in the bound
//!    history (assumption 1).
//! 4. **Cluster configuration**: all nodes agree on the member set (already
//!    a documented requirement of `RawNode::peers`); ranks are positions in
//!    the sorted member list, so they agree across nodes.
//! 5. **Shell discipline**, now reduced to type-enforceable obligations: the
//!    shell keeps each node's `Log`/`Abs` pair together and calls the step
//!    functions with the fields of the message it actually received, and it
//!    sends exactly the messages in the returned plans. The step functions
//!    check everything else (role, term, membership, bounds) at runtime and
//!    panic via `log::fault` on a violation.
//!
//! The model's message-receiving transitions (`t_grant`, `t_recv_append`,
//! `t_confirm_read`) also accept a higher-term message in one step; the
//! implementation always bumps the term first (`Abs::bump_term`, the model's
//! `t_bump_term`) and then handles the message at its own term, so the
//! receiving steps only cover — and only need — the equal-term case.

// The verified step functions take flat concrete-summary argument lists; the
// resulting shapes trip several style lints that don't fit this API.
#![allow(
    clippy::too_many_arguments,
    clippy::collapsible_if,
    clippy::ptr_arg,
    clippy::assign_op_pattern,
    clippy::len_zero,
    clippy::manual_unwrap_or_default,
    clippy::int_plus_one,
    clippy::single_match,
    clippy::manual_map,
    clippy::question_mark
)]

use vstd::prelude::*;

use super::log::{Entry, Fault, Index, Log, fault};
use crate::error::Result;
#[allow(unused_imports)] // several are referenced only from ghost code
use crate::raft::safety::{AEntry, CommitRec, GState, MHost, MRole, Msg, ReadRec, TStep};
use crate::raft::{NodeID, Term};
// Spec/proof items only exist under the Verus toolchain (a normal build
// erases them), so their imports are gated the same way.
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::log::{cmd_view, entries_view, entry_view};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::raft::safety::{
    init, init_host, init_implies_inv, inv, is_quorum, last_term, next, next_step, node_ids,
    prefix_eq, splice, splice_is_noop, step_preserves_inv, t_become_leader, t_bump_term,
    t_campaign, t_collect_vote, t_confirm_read, t_grant, t_leader_commit, t_propose, t_recv_append,
    t_recv_commit, t_restart, t_send_ack, t_send_append, t_send_commit, t_step_down, t_submit_read,
    thm_election_safety, thm_read_linearizable, thm_state_machine_safety, up_to_date,
};

verus! {

// ---------------------------------------------------------------------------
// The refinement statement
// ---------------------------------------------------------------------------

/// A global model state consistent with a node's local view: host `i` of an
/// `n`-node cluster has abstract state `hpre`, and the message evidence the
/// node relies on is in the history.
pub open spec fn binds(s: GState, i: int, n: u8, hpre: MHost, evid: Set<Msg>) -> bool {
    &&& 0 <= i < s.n
    &&& s.n == n as nat
    &&& s.hosts[i] == hpre
    &&& evid.subset_of(s.net)
}

/// The step from `hpre` to `hpost` emitting `sent` refines the model in one
/// transition: from every consistent global state there is a model
/// transition that performs exactly this host change and message emission.
pub open spec fn host_refines(
    i: int, n: u8, hpre: MHost, hpost: MHost, evid: Set<Msg>, sent: Set<Msg>,
) -> bool {
    forall|s: GState| #[trigger] binds(s, i, n, hpre, evid) ==> exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(sent)
    }
}

/// `s2` is reachable from `s` in exactly `k` model transitions.
pub open spec fn next_n(s: GState, s2: GState, k: nat) -> bool
    decreases k,
{
    if k == 0 {
        s2 == s
    } else {
        exists|s1: GState| #[trigger] next(s, s1) && next_n(s1, s2, (k - 1) as nat)
    }
}

/// `s2` is reachable from `s` by model transitions.
pub open spec fn reach(s: GState, s2: GState) -> bool {
    exists|k: nat| next_n(s, s2, k)
}

/// The step from `hpre` to `hpost` emitting `sent` refines the model: from
/// every invariant-satisfying global state consistent with the node's local
/// view there is a *sequence* of model transitions that performs exactly this
/// host change and message emission, ending in an invariant-satisfying state.
/// This is the per-step guarantee every step function provides.
pub open spec fn host_refines_star(
    i: int, n: u8, hpre: MHost, hpost: MHost, evid: Set<Msg>, sent: Set<Msg>,
) -> bool {
    forall|s: GState| #[trigger] binds(s, i, n, hpre, evid) && inv(s) ==> exists|s2: GState| {
        &&& #[trigger] reach(s, s2)
        &&& inv(s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(sent)
    }
}

/// The evidence set only grows, and only by the given received and sent
/// messages. Every step function ensures this about the node's ghost
/// evidence, so the evidence a later step relies on consists exclusively of
/// abstract counterparts of messages this node actually received (trusted
/// assumption 1) or itself sent (in the history after that step).
pub open spec fn evid_grows(pre: Set<Msg>, post: Set<Msg>, recv: Set<Msg>, sent: Set<Msg>) -> bool {
    &&& pre.subset_of(post)
    &&& forall|m: Msg| post.contains(m) ==> pre.contains(m) || recv.contains(m) || sent.contains(m)
}

// Transitivity of multi-step reachability.
proof fn lemma_next_n_trans(s: GState, s1: GState, s2: GState, k1: nat, k2: nat)
    requires
        next_n(s, s1, k1),
        next_n(s1, s2, k2),
    ensures
        next_n(s, s2, k1 + k2),
    decreases k1,
{
    if k1 == 0 {
        assert(s1 == s);
    } else {
        let sm = choose|sm: GState| #[trigger] next(s, sm) && next_n(sm, s1, (k1 - 1) as nat);
        lemma_next_n_trans(sm, s1, s2, (k1 - 1) as nat, k2);
        assert(next(s, sm) && next_n(sm, s2, (k1 + k2 - 1) as nat));
        assert(next_n(s, s2, k1 + k2));
    }
}

proof fn lemma_reach_trans(s: GState, s1: GState, s2: GState)
    requires
        reach(s, s1),
        reach(s1, s2),
    ensures
        reach(s, s2),
{
    let k1 = choose|k1: nat| next_n(s, s1, k1);
    let k2 = choose|k2: nat| next_n(s1, s2, k2);
    lemma_next_n_trans(s, s1, s2, k1, k2);
}

/// A single-transition refinement is a multi-step refinement: the invariant
/// is preserved by `step_preserves_inv`.
proof fn lemma_star_of_single(i: int, n: u8, hpre: MHost, hpost: MHost, evid: Set<Msg>, sent: Set<Msg>)
    requires
        host_refines(i, n, hpre, hpost, evid, sent),
    ensures
        host_refines_star(i, n, hpre, hpost, evid, sent),
{
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, evid) && inv(s) implies exists|s2: GState| {
        &&& #[trigger] reach(s, s2)
        &&& inv(s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(sent)
    } by {
        let s2 = choose|s2: GState| {
            &&& #[trigger] next(s, s2)
            &&& s2.n == s.n
            &&& s2.hosts == s.hosts.update(i, hpost)
            &&& s2.net == s.net.union(sent)
        };
        let step = choose|step: TStep| #[trigger] next_step(s, s2, step);
        step_preserves_inv(s, s2, step);
        assert(next_n(s2, s2, 0));
        assert(next_n(s, s2, 1));
        assert(reach(s, s2));
    }
}

/// The identity step refines (in zero transitions).
proof fn lemma_star_refl(i: int, n: u8, h: MHost, evid: Set<Msg>)
    ensures
        host_refines_star(i, n, h, h, evid, Set::empty()),
{
    assert forall|s: GState| #[trigger] binds(s, i, n, h, evid) && inv(s) implies exists|s2: GState| {
        &&& #[trigger] reach(s, s2)
        &&& inv(s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, h)
        &&& s2.net == s.net.union(Set::empty())
    } by {
        assert(next_n(s, s, 0));
        assert(reach(s, s));
        assert(s.hosts =~= s.hosts.update(i, h));
        assert(s.net =~= s.net.union(Set::empty()));
    }
}

/// Refinement is monotone in the evidence: relying on more of the history
/// gives a weaker (still sound) statement.
proof fn lemma_star_mono(i: int, n: u8, hpre: MHost, hpost: MHost, e1: Set<Msg>, e2: Set<Msg>, sent: Set<Msg>)
    requires
        host_refines_star(i, n, hpre, hpost, e1, sent),
        e1.subset_of(e2),
    ensures
        host_refines_star(i, n, hpre, hpost, e2, sent),
{
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, e2) && inv(s) implies exists|s2: GState| {
        &&& #[trigger] reach(s, s2)
        &&& inv(s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(sent)
    } by {
        assert(binds(s, i, n, hpre, e1));
    }
}

/// The composition lemma: extend a multi-step refinement by one more
/// transition whose evidence is covered by the accumulated evidence and the
/// messages already sent (which are in the history once sent).
proof fn lemma_star_extend(
    i: int, n: u8, h0: MHost, h1: MHost, h2: MHost, evid: Set<Msg>, sent1: Set<Msg>,
    e2: Set<Msg>, sent2: Set<Msg>,
)
    requires
        host_refines_star(i, n, h0, h1, evid, sent1),
        host_refines(i, n, h1, h2, e2, sent2),
        e2.subset_of(evid.union(sent1)),
    ensures
        host_refines_star(i, n, h0, h2, evid, sent1.union(sent2)),
{
    assert forall|s: GState| #[trigger] binds(s, i, n, h0, evid) && inv(s) implies exists|s2: GState| {
        &&& #[trigger] reach(s, s2)
        &&& inv(s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, h2)
        &&& s2.net == s.net.union(sent1.union(sent2))
    } by {
        let t1 = choose|t1: GState| {
            &&& #[trigger] reach(s, t1)
            &&& inv(t1)
            &&& t1.n == s.n
            &&& t1.hosts == s.hosts.update(i, h1)
            &&& t1.net == s.net.union(sent1)
        };
        assert(binds(t1, i, n, h1, e2)) by {
            assert(t1.hosts[i] == h1);
            assert forall|m: Msg| e2.contains(m) implies t1.net.contains(m) by {
                if sent1.contains(m) {
                } else {
                    assert(evid.contains(m));
                    assert(s.net.contains(m));
                }
            }
        }
        let t2 = choose|t2: GState| {
            &&& #[trigger] next(t1, t2)
            &&& t2.n == t1.n
            &&& t2.hosts == t1.hosts.update(i, h2)
            &&& t2.net == t1.net.union(sent2)
        };
        let step = choose|step: TStep| #[trigger] next_step(t1, t2, step);
        step_preserves_inv(t1, t2, step);
        assert(next_n(t2, t2, 0));
        assert(next_n(t1, t2, 1));
        assert(reach(t1, t2));
        lemma_reach_trans(s, t1, t2);
        assert(t2.hosts =~= s.hosts.update(i, h2));
        assert(t2.net =~= s.net.union(sent1.union(sent2)));
    }
}

// ---------------------------------------------------------------------------
// Cluster composition: the formal statement of trusted assumption 3
// ---------------------------------------------------------------------------
//
// `host_refines_star` is a per-node statement. Reading the per-node
// guarantees as a statement about the running cluster requires composing
// them: all nodes' ghost states must be simultaneously bound to one model
// state whose history contains every message ever sent, and the nodes'
// steps must interleave into one model execution from `init`. The specs and
// lemmas below state that argument formally:
//
// * `cluster_binds`/`cluster_state`/`cluster_bound` define the composition
//   invariant — a reachable, invariant-satisfying model state binding every
//   node's ghost state and evidence.
// * `lemma_cluster_init` establishes it for a fresh cluster (every node in
//   the state `Abs::recover` yields over an empty log, with no evidence).
// * `lemma_cluster_step` maintains it across any step function call, from
//   the step's `host_refines_star` and `evid_grows` postconditions plus the
//   received counterparts being in the bound history (assumption 1).
// * `lemma_cluster_restart` maintains it across a crash-restart via the
//   model's `t_restart`; `recover_host` (assumption 2) is exactly the claim
//   that the recovered ghost state is this lemma's post-state.
// * `thm_cluster_safety` and `thm_impl_safety` instantiate the model's
//   safety theorems against a bound cluster — the latter directly against
//   the verified node states and the logs' verified views, i.e. against the
//   implementation.
//
// What remains trusted is that these lemmas' hypotheses track the real run:
// every node starts fresh or recovers per `recover_host`, every mutation of
// a node's verified state is one step function call (assumption 5), and
// `recv_msg` returns counterparts in the bound history (assumption 1). The
// interleaving argument itself is machine-checked.

/// `s` binds the whole cluster: node k's ghost abstract state is `habs[k]`
/// and node k's ghost message evidence `evids[k]` is in the history.
pub open spec fn cluster_binds(s: GState, n: u8, habs: Seq<MHost>, evids: Seq<Set<Msg>>) -> bool {
    &&& s.n == n as nat
    &&& habs.len() == n as nat
    &&& evids.len() == n as nat
    &&& s.hosts == habs
    &&& forall|k: int| 0 <= k < n as int ==> (#[trigger] evids[k]).subset_of(s.net)
}

/// A reachable, invariant-satisfying model state binding every node.
pub open spec fn cluster_state(s: GState, n: u8, habs: Seq<MHost>, evids: Seq<Set<Msg>>) -> bool {
    &&& cluster_binds(s, n, habs, evids)
    &&& inv(s)
    &&& exists|s0: GState| #[trigger] init(s0) && reach(s0, s)
}

/// The composition invariant (trusted assumption 3, stated formally): some
/// model state binds the cluster.
pub open spec fn cluster_bound(n: u8, habs: Seq<MHost>, evids: Seq<Set<Msg>>) -> bool {
    exists|s: GState| #[trigger] cluster_state(s, n, habs, evids)
}

/// A fresh cluster is bound: every node in the initial host state (what
/// `Abs::recover` yields over an empty log) with no evidence.
pub proof fn lemma_cluster_init(n: u8, habs: Seq<MHost>, evids: Seq<Set<Msg>>)
    requires
        n >= 1,
        habs.len() == n as nat,
        evids.len() == n as nat,
        forall|k: int| 0 <= k < n as int ==> habs[k] == init_host(),
        forall|k: int| 0 <= k < n as int ==> evids[k] == Set::<Msg>::empty(),
    ensures
        cluster_bound(n, habs, evids),
{
    let s0 = GState {
        n: n as nat,
        hosts: habs,
        net: Set::empty(),
        leader_log: Map::empty(),
        leader_of: Map::empty(),
        voters: Map::empty(),
        elect_log: Map::empty(),
        elect_votes: Map::empty(),
        commits: Set::empty(),
        reads: Set::empty(),
        read_hwm: Map::empty(),
    };
    assert(init(s0));
    init_implies_inv(s0);
    assert(next_n(s0, s0, 0));
    assert(reach(s0, s0));
    assert(cluster_state(s0, n, habs, evids));
}

/// The composition invariant is maintained by any step function call: node
/// `i` steps from `habs[i]` to `hpost` (its `host_refines_star`
/// postcondition), its evidence grows only by the received and sent
/// messages (its `evid_grows` postcondition), and the received messages'
/// abstract counterparts are in the bound history (trusted assumption 1).
/// The bound state advances by the step's transitions; every other node
/// stays bound.
pub proof fn lemma_cluster_step(
    s: GState, n: u8, habs: Seq<MHost>, evids: Seq<Set<Msg>>, i: int,
    hpost: MHost, epost: Set<Msg>, recv: Set<Msg>, sent: Set<Msg>,
)
    requires
        cluster_state(s, n, habs, evids),
        0 <= i < n as int,
        host_refines_star(i, n, habs[i], hpost, evids[i], sent),
        evid_grows(evids[i], epost, recv, sent),
        recv.subset_of(s.net),
    ensures
        exists|s2: GState| {
            &&& cluster_state(s2, n, habs.update(i, hpost), evids.update(i, epost))
            &&& #[trigger] reach(s, s2)
        },
{
    assert(binds(s, i, n, habs[i], evids[i]));
    let s2 = choose|s2: GState| {
        &&& #[trigger] reach(s, s2)
        &&& inv(s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(sent)
    };
    let habs2 = habs.update(i, hpost);
    let evids2 = evids.update(i, epost);
    assert(s2.hosts == habs2);
    assert forall|k: int| 0 <= k < n as int implies (#[trigger] evids2[k]).subset_of(s2.net) by {
        if k == i {
            assert forall|m: Msg| epost.contains(m) implies s2.net.contains(m) by {
                if evids[i].contains(m) {
                    assert(s.net.contains(m));
                } else if recv.contains(m) {
                    assert(s.net.contains(m));
                } else {
                    assert(sent.contains(m));
                }
            }
        } else {
            assert(evids[k].subset_of(s.net));
        }
    }
    let s0 = choose|s0: GState| #[trigger] init(s0) && reach(s0, s);
    lemma_reach_trans(s0, s, s2);
    assert(cluster_state(s2, n, habs2, evids2));
}

/// The composition invariant is maintained by a crash-restart of node `i`
/// recovering commit index `c` (at most its pre-crash value; the entries,
/// term and vote are fsynced and survive): the model's `t_restart`
/// transition rebinds the recovered node. `recover_host` (trusted
/// assumption 2) is exactly the claim that the state recovered from the
/// durable log is this lemma's post-state for the node.
pub proof fn lemma_cluster_restart(
    s: GState, n: u8, habs: Seq<MHost>, evids: Seq<Set<Msg>>, i: int, c: nat,
)
    requires
        cluster_state(s, n, habs, evids),
        0 <= i < n as int,
        c <= habs[i].commit,
    ensures
        exists|s2: GState| {
            &&& cluster_state(s2, n,
                habs.update(i, MHost {
                    role: MRole::Follower,
                    commit: c,
                    votes: Set::empty(),
                    vote_logs: Map::empty(),
                    read_seq: 0,
                    ..habs[i]
                }),
                evids.update(i, Set::empty()))
            &&& #[trigger] reach(s, s2)
        },
{
    let hpost = MHost {
        role: MRole::Follower,
        commit: c,
        votes: Set::empty(),
        vote_logs: Map::empty(),
        read_seq: 0,
        ..habs[i]
    };
    let s2 = GState { hosts: s.hosts.update(i, hpost), ..s };
    assert(t_restart(s, s2, i, c));
    assert(next_step(s, s2, TStep::Restart { i, commit: c }));
    assert(next(s, s2));
    step_preserves_inv(s, s2, TStep::Restart { i, commit: c });
    assert(next_n(s2, s2, 0));
    assert(next_n(s, s2, 1));
    assert(reach(s, s2));
    let s0 = choose|s0: GState| #[trigger] init(s0) && reach(s0, s);
    lemma_reach_trans(s0, s, s2);
    assert(cluster_state(s2, n, habs.update(i, hpost), evids.update(i, Set::empty())));
}

/// The model's safety theorems instantiated for a bound cluster: election
/// safety and state machine safety hold of the nodes' ghost states.
pub proof fn thm_cluster_safety(n: u8, habs: Seq<MHost>, evids: Seq<Set<Msg>>)
    requires
        cluster_bound(n, habs, evids),
    ensures
        forall|i: int, j: int|
            #![trigger habs[i].role, habs[j].role]
            0 <= i < n as int && 0 <= j < n as int
            && habs[i].role is Leader && habs[j].role is Leader
            && habs[i].term == habs[j].term ==> i == j,
        forall|i: int, j: int, e: int|
            #![trigger habs[i].log[e], habs[j].log[e]]
            0 <= i < n as int && 0 <= j < n as int
            && 0 <= e < habs[i].commit && e < habs[j].commit ==>
            habs[i].log[e] == habs[j].log[e],
{
    let s = choose|s: GState| #[trigger] cluster_state(s, n, habs, evids);
    assert forall|i: int, j: int|
        0 <= i < n as int && 0 <= j < n as int
        && habs[i].role is Leader && habs[j].role is Leader
        && habs[i].term == habs[j].term implies i == j by {
        thm_election_safety(s, i, j);
    }
    assert forall|i: int, j: int, e: int|
        0 <= i < n as int && 0 <= j < n as int
        && 0 <= e < habs[i].commit && e < habs[j].commit implies
        habs[i].log[e] == habs[j].log[e] by {
        thm_state_machine_safety(s, i, j, e);
    }
}

/// The safety theorems instantiated against the implementation: for two
/// verified node states bound in one cluster, at most one is leader per
/// term, and the logs' verified views never disagree on a committed entry.
/// This is the end-to-end statement about the running system, modulo the
/// composition hypotheses above.
pub proof fn thm_impl_safety(
    n: u8, habs: Seq<MHost>, evids: Seq<Set<Msg>>,
    a1: &Abs, l1: &Log, a2: &Abs, l2: &Log,
)
    requires
        cluster_bound(n, habs, evids),
        a1.inv(l1),
        a2.inv(l2),
        a1.n_spec() == n,
        a2.n_spec() == n,
        habs[a1.i()] == a1.habs(),
        habs[a2.i()] == a2.habs(),
    ensures
        a1.is_leader() && a2.is_leader() && l1.term() == l2.term() ==> a1.i() == a2.i(),
        forall|e: int| 0 <= e < l1.commit_index() && e < l2.commit_index() ==>
            l1.view()[e] == l2.view()[e],
{
    let s = choose|s: GState| #[trigger] cluster_state(s, n, habs, evids);
    a1.members.lemma_rank(a1.me);
    a2.members.lemma_rank(a2.me);
    if a1.is_leader() && a2.is_leader() && l1.term() == l2.term() {
        thm_election_safety(s, a1.i(), a2.i());
    }
    assert forall|e: int| 0 <= e < l1.commit_index() && e < l2.commit_index() implies
        l1.view()[e] == l2.view()[e] by {
        thm_state_machine_safety(s, a1.i(), a2.i(), e);
    }
}

// ---------------------------------------------------------------------------
// Message abstraction
// ---------------------------------------------------------------------------

/// `m` is the abstract counterpart of a received `Message::Campaign` from the
/// candidate of rank `c`: the ghost candidate log matches the concrete
/// (last_index, last_term) summary.
pub open spec fn abstracts_campaign(m: Msg, c: int, term: nat, last_index: nat, lterm: nat) -> bool {
    &&& m matches Msg::Campaign { c: mc, term: mt, clog }
        && mc == c && mt == term && clog.len() == last_index && last_term(clog) == lterm
}

/// `m` is the abstract counterpart of a received `CampaignResponse { vote:
/// true }` from the voter of rank `v` (the ghost voter log is unconstrained:
/// the model only needs some log).
pub open spec fn abstracts_vote(m: Msg, v: int, c: int, term: nat) -> bool {
    &&& m matches Msg::Vote { v: mv, c: mc, term: mt, vlog }
        && mv == v && mc == c && mt == term
}

/// `m` is the abstract counterpart of a received heartbeat's commit_index
/// (the ghost commit record is unconstrained: it is whatever quorum evidence
/// the leader committed on).
pub open spec fn abstracts_commit(m: Msg, term: nat, ci: nat) -> bool {
    &&& m matches Msg::Commit { term: mt, ci: mci, rec } && mt == term && mci == ci
}

/// The exec summary of a received message, in abstract coordinates (sender
/// ranks computed by the verified caller from the member set). Passed to the
/// trusted `recv_msg` to recover the message's abstract counterpart.
#[allow(dead_code)] // fields are read only by ghost code, erased in a normal build
pub enum MsgSummary<'a> {
    /// `Message::Campaign` from the candidate of rank `c`.
    Campaign { c: u8, term: Term, last_index: Index, last_term: Term },
    /// `Message::CampaignResponse { vote: true }` from the voter of rank `v`.
    Vote { v: u8, c: u8, term: Term },
    /// `Message::Append`.
    Append { term: Term, base_index: Index, base_term: Term, entries: &'a Vec<Entry> },
    /// A `Message::Heartbeat`'s commit_index.
    Commit { term: Term, commit_index: Index },
    /// A `Message::{AppendResponse, HeartbeatResponse}` nonzero match index
    /// from the follower of rank `v`.
    Ack { v: u8, term: Term, match_index: Index },
    /// `Message::Read` (or a heartbeat's read_seq, which re-announces it).
    Read { term: Term, seq: u64 },
    /// A `Message::{ReadResponse, HeartbeatResponse}` nonzero read sequence
    /// confirmation from the follower of rank `v`.
    ReadConfirm { v: u8, term: Term, seq: u64 },
}

/// The abstraction relation between a model message and a summary: every
/// field the concrete message carries is pinned (for an Append, the entries'
/// terms and commands included); fields the concrete message only summarizes
/// (candidate/voter logs, commit records) are existential.
pub open spec fn summarizes(m: Msg, s: MsgSummary) -> bool {
    match s {
        MsgSummary::Campaign { c, term, last_index, last_term: lt } =>
            abstracts_campaign(m, c as int, term as nat, last_index as nat, lt as nat),
        MsgSummary::Vote { v, c, term } => abstracts_vote(m, v as int, c as int, term as nat),
        MsgSummary::Append { term, base_index, base_term, entries } => m == (Msg::Append {
            term: term as nat,
            base: base_index as nat,
            bterm: base_term as nat,
            entries: entries_view(entries@),
        }),
        MsgSummary::Commit { term, commit_index } =>
            abstracts_commit(m, term as nat, commit_index as nat),
        MsgSummary::Ack { v, term, match_index } => m == (Msg::Ack {
            v: v as int,
            term: term as nat,
            mi: match_index as nat,
        }),
        MsgSummary::Read { term, seq } => m == (Msg::Read { term: term as nat, seq: seq as nat }),
        MsgSummary::ReadConfirm { v, term, seq } => m == (Msg::ReadConfirm {
            v: v as int,
            term: term as nat,
            seq: seq as nat,
        }),
    }
}

/// TRUSTED (network non-forgery + angelic ghost recovery): every message the
/// shell receives has an abstract counterpart in the model's message
/// history; this returns that counterpart. The summarized fields are pinned;
/// ghost payloads are whatever they truly were at the sender. Sound iff the
/// returned counterpart is in the history of the model state binding the
/// cluster (`cluster_bound`; the `recv` hypothesis of
/// `lemma_cluster_step`) — trusted assumptions 1 and 3 in the module doc.
#[verifier::external_body]
fn recv_msg(s: &MsgSummary) -> (m: Ghost<Msg>)
    ensures
        summarizes(m@, *s),
{
    Ghost::assume_new()
}

// ---------------------------------------------------------------------------
// Lifting lemmas: local steps are model transitions in any consistent cluster
// ---------------------------------------------------------------------------

proof fn lemma_lift_bump(i: int, n: u8, hpre: MHost, t: nat)
    requires
        t > hpre.term,
    ensures
        host_refines(i, n, hpre,
            MHost { term: t, vote: None, role: MRole::Follower, ..hpre },
            Set::empty(), Set::empty()),
{
    let hpost = MHost { term: t, vote: None, role: MRole::Follower, ..hpre };
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, Set::empty()) implies exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(Set::empty())
    } by {
        let s2 = GState { hosts: s.hosts.update(i, hpost), ..s };
        assert(t_bump_term(s, s2, i, t));
        assert(next_step(s, s2, TStep::BumpTerm { i, term: t }));
        assert(next(s, s2));
        assert(s2.net =~= s.net.union(Set::empty()));
        assert(s2.net == s.net.union(Set::empty()));
    }
}

proof fn lemma_lift_step_down(i: int, n: u8, hpre: MHost)
    requires
        hpre.role is Candidate,
    ensures
        host_refines(i, n, hpre, MHost { role: MRole::Follower, ..hpre }, Set::empty(), Set::empty()),
{
    let hpost = MHost { role: MRole::Follower, ..hpre };
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, Set::empty()) implies exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(Set::empty())
    } by {
        let s2 = GState { hosts: s.hosts.update(i, hpost), ..s };
        assert(t_step_down(s, s2, i));
        assert(next_step(s, s2, TStep::StepDown { i }));
        assert(next(s, s2));
        assert(s2.net =~= s.net.union(Set::empty()));
        assert(s2.net == s.net.union(Set::empty()));
    }
}

proof fn lemma_lift_campaign(i: int, n: u8, hpre: MHost)
    requires
        !(hpre.role is Leader),
    ensures
        host_refines(i, n, hpre,
            MHost {
                term: (hpre.term + 1) as nat,
                vote: Some(i),
                role: MRole::Candidate,
                votes: Set::empty().insert(i),
                vote_logs: Map::empty().insert(i, hpre.log),
                ..hpre
            },
            Set::empty(),
            Set::empty()
                .insert(Msg::Campaign { c: i, term: (hpre.term + 1) as nat, clog: hpre.log })
                .insert(Msg::Vote { v: i, c: i, term: (hpre.term + 1) as nat, vlog: hpre.log })),
{
    let t = (hpre.term + 1) as nat;
    let hpost = MHost {
        term: t,
        vote: Some(i),
        role: MRole::Candidate,
        votes: Set::empty().insert(i),
        vote_logs: Map::empty().insert(i, hpre.log),
        ..hpre
    };
    let sent = Set::empty()
        .insert(Msg::Campaign { c: i, term: t, clog: hpre.log })
        .insert(Msg::Vote { v: i, c: i, term: t, vlog: hpre.log });
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, Set::empty()) implies exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(sent)
    } by {
        let s2 = GState {
            hosts: s.hosts.update(i, hpost),
            net: s.net
                .insert(Msg::Campaign { c: i, term: t, clog: hpre.log })
                .insert(Msg::Vote { v: i, c: i, term: t, vlog: hpre.log }),
            ..s
        };
        assert(t_campaign(s, s2, i));
        assert(next_step(s, s2, TStep::Campaign { i }));
        assert(next(s, s2));
        assert(s2.net =~= s.net.union(sent));
        assert(s2.net == s.net.union(sent));
    }
}

proof fn lemma_lift_grant(i: int, n: u8, hpre: MHost, c: int, clog: Seq<AEntry>)
    requires
        hpre.role is Follower,
        hpre.vote is None || hpre.vote == Some(c),
        up_to_date(clog, hpre.log),
        i != c,
    ensures
        host_refines(i, n, hpre,
            MHost { vote: Some(c), ..hpre },
            Set::empty().insert(Msg::Campaign { c, term: hpre.term, clog }),
            Set::empty().insert(Msg::Vote { v: i, c, term: hpre.term, vlog: hpre.log })),
{
    let t = hpre.term;
    let hpost = MHost { vote: Some(c), ..hpre };
    let evid = Set::empty().insert(Msg::Campaign { c, term: t, clog });
    let sent = Set::empty().insert(Msg::Vote { v: i, c, term: t, vlog: hpre.log });
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, evid) implies exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(sent)
    } by {
        let s2 = GState {
            hosts: s.hosts.update(i, hpost),
            net: s.net.insert(Msg::Vote { v: i, c, term: t, vlog: hpre.log }),
            ..s
        };
        assert(s.net.contains(Msg::Campaign { c, term: t, clog }));
        assert(hpost == MHost { term: t, vote: Some(c), role: MRole::Follower, ..hpre });
        assert(t_grant(s, s2, i, c, t, clog));
        assert(next_step(s, s2, TStep::Grant { v: i, c, term: t, clog }));
        assert(next(s, s2));
        assert(s2.net =~= s.net.union(sent));
        assert(s2.net == s.net.union(sent));
    }
}

proof fn lemma_lift_collect_vote(i: int, n: u8, hpre: MHost, v: int, vlog: Seq<AEntry>)
    requires
        hpre.role is Candidate,
    ensures
        host_refines(i, n, hpre,
            MHost { votes: hpre.votes.insert(v), vote_logs: hpre.vote_logs.insert(v, vlog), ..hpre },
            Set::empty().insert(Msg::Vote { v, c: i, term: hpre.term, vlog }),
            Set::empty()),
{
    let hpost = MHost { votes: hpre.votes.insert(v), vote_logs: hpre.vote_logs.insert(v, vlog), ..hpre };
    let evid = Set::empty().insert(Msg::Vote { v, c: i, term: hpre.term, vlog });
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, evid) implies exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(Set::empty())
    } by {
        let s2 = GState { hosts: s.hosts.update(i, hpost), ..s };
        assert(s.net.contains(Msg::Vote { v, c: i, term: hpre.term, vlog }));
        assert(t_collect_vote(s, s2, i, v, vlog));
        assert(next_step(s, s2, TStep::CollectVote { i, v, vlog }));
        assert(next(s, s2));
        assert(s2.net =~= s.net.union(Set::empty()));
        assert(s2.net == s.net.union(Set::empty()));
    }
}

proof fn lemma_lift_become_leader(i: int, n: u8, hpre: MHost)
    requires
        hpre.role is Candidate,
        is_quorum(n as nat, hpre.votes),
    ensures
        host_refines(i, n, hpre,
            MHost {
                role: MRole::Leader,
                log: hpre.log.push(AEntry { term: hpre.term, cmd: None }),
                read_seq: 0,
                ..hpre
            },
            Set::empty(), Set::empty()),
{
    let hpost = MHost {
        role: MRole::Leader,
        log: hpre.log.push(AEntry { term: hpre.term, cmd: None }),
        read_seq: 0,
        ..hpre
    };
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, Set::empty()) implies exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(Set::empty())
    } by {
        let s2 = GState {
            hosts: s.hosts.update(i, hpost),
            leader_log: s.leader_log.insert(hpre.term, hpre.log.push(AEntry { term: hpre.term, cmd: None })),
            leader_of: s.leader_of.insert(hpre.term, i),
            voters: s.voters.insert(hpre.term, hpre.votes),
            elect_log: s.elect_log.insert(hpre.term, hpre.log),
            elect_votes: s.elect_votes.insert(hpre.term, hpre.vote_logs),
            ..s
        };
        assert(t_become_leader(s, s2, i));
        assert(next_step(s, s2, TStep::BecomeLeader { i }));
        assert(next(s, s2));
        assert(s2.net =~= s.net.union(Set::empty()));
        assert(s2.net == s.net.union(Set::empty()));
    }
}

proof fn lemma_lift_propose(i: int, n: u8, hpre: MHost, cmd: Option<Seq<u8>>)
    requires
        hpre.role is Leader,
    ensures
        host_refines(i, n, hpre,
            MHost { log: hpre.log.push(AEntry { term: hpre.term, cmd }), ..hpre },
            Set::empty(), Set::empty()),
{
    let hpost = MHost { log: hpre.log.push(AEntry { term: hpre.term, cmd }), ..hpre };
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, Set::empty()) implies exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(Set::empty())
    } by {
        let s2 = GState {
            hosts: s.hosts.update(i, hpost),
            leader_log: s.leader_log.insert(hpre.term, hpre.log.push(AEntry { term: hpre.term, cmd })),
            ..s
        };
        assert(t_propose(s, s2, i, cmd));
        assert(next_step(s, s2, TStep::Propose { i, cmd }));
        assert(next(s, s2));
        assert(s2.net =~= s.net.union(Set::empty()));
        assert(s2.net == s.net.union(Set::empty()));
    }
}

proof fn lemma_lift_send_append(i: int, n: u8, hpre: MHost, b: nat, e: nat)
    requires
        hpre.role is Leader,
        b <= e <= hpre.log.len(),
    ensures
        host_refines(i, n, hpre, hpre, Set::empty(),
            Set::empty().insert(Msg::Append {
                term: hpre.term,
                base: b,
                bterm: if b == 0 { 0 } else { hpre.log[b - 1].term },
                entries: hpre.log.subrange(b as int, e as int),
            })),
{
    let m = Msg::Append {
        term: hpre.term,
        base: b,
        bterm: if b == 0 { 0 } else { hpre.log[b - 1].term },
        entries: hpre.log.subrange(b as int, e as int),
    };
    let sent = Set::empty().insert(m);
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, Set::empty()) implies exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpre)
        &&& s2.net == s.net.union(sent)
    } by {
        let s2 = GState { net: s.net.insert(m), ..s };
        assert(t_send_append(s, s2, i, b, e));
        assert(next_step(s, s2, TStep::SendAppend { i, b, e }));
        assert(next(s, s2));
        assert(s2.hosts =~= s.hosts.update(i, hpre));
        assert(s2.hosts == s.hosts.update(i, hpre));
        assert(s2.net =~= s.net.union(sent));
        assert(s2.net == s.net.union(sent));
    }
}

proof fn lemma_lift_send_ack(i: int, n: u8, hpre: MHost, mi: nat)
    requires
        1 <= mi <= hpre.log.len(),
        hpre.log[mi - 1].term == hpre.term,
    ensures
        host_refines(i, n, hpre, hpre, Set::empty(),
            Set::empty().insert(Msg::Ack { v: i, term: hpre.term, mi })),
{
    let m = Msg::Ack { v: i, term: hpre.term, mi };
    let sent = Set::empty().insert(m);
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, Set::empty()) implies exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpre)
        &&& s2.net == s.net.union(sent)
    } by {
        let s2 = GState { net: s.net.insert(m), ..s };
        assert(t_send_ack(s, s2, i, mi));
        assert(next_step(s, s2, TStep::SendAck { i, mi }));
        assert(next(s, s2));
        assert(s2.hosts =~= s.hosts.update(i, hpre));
        assert(s2.hosts == s.hosts.update(i, hpre));
        assert(s2.net =~= s.net.union(sent));
        assert(s2.net == s.net.union(sent));
    }
}

proof fn lemma_lift_recv_append(i: int, n: u8, hpre: MHost, b: nat, bt: nat, entries: Seq<AEntry>)
    requires
        hpre.role is Follower,
        b == 0 || (b <= hpre.log.len() && hpre.log[b - 1].term == bt),
    ensures
        host_refines(i, n, hpre,
            MHost { log: splice(hpre.log, b, entries), ..hpre },
            Set::empty().insert(Msg::Append { term: hpre.term, base: b, bterm: bt, entries }),
            Set::empty().insert(Msg::Ack { v: i, term: hpre.term, mi: (b + entries.len()) as nat })),
{
    let t = hpre.term;
    let hpost = MHost { log: splice(hpre.log, b, entries), ..hpre };
    let evid = Set::empty().insert(Msg::Append { term: t, base: b, bterm: bt, entries });
    let sent = Set::empty().insert(Msg::Ack { v: i, term: t, mi: (b + entries.len()) as nat });
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, evid) implies exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(sent)
    } by {
        let s2 = GState {
            hosts: s.hosts.update(i, hpost),
            net: s.net.insert(Msg::Ack { v: i, term: t, mi: (b + entries.len()) as nat }),
            ..s
        };
        assert(s.net.contains(Msg::Append { term: t, base: b, bterm: bt, entries }));
        assert(hpost == MHost {
            term: t,
            vote: hpre.vote,
            role: MRole::Follower,
            log: splice(hpre.log, b, entries),
            ..hpre
        });
        assert(t_recv_append(s, s2, i, t, b, bt, entries));
        assert(next_step(s, s2, TStep::RecvAppend { i, term: t, base: b, bterm: bt, entries }));
        assert(next(s, s2));
        assert(s2.net =~= s.net.union(sent));
        assert(s2.net == s.net.union(sent));
    }
}

proof fn lemma_lift_leader_commit(i: int, n: u8, hpre: MHost, ci: nat, q: Map<int, nat>, evid: Set<Msg>)
    requires
        hpre.role is Leader,
        1 <= ci <= hpre.log.len(),
        hpre.log[ci - 1].term == hpre.term,
        ci > hpre.commit,
        is_quorum(n as nat, q.dom()),
        forall|v: int| #[trigger] q.dom().contains(v) ==>
            q[v] >= ci && evid.contains(Msg::Ack { v, term: hpre.term, mi: q[v] }),
    ensures
        host_refines(i, n, hpre,
            MHost { commit: ci, crec: CommitRec { term: hpre.term, ci, q }, ..hpre },
            evid,
            Set::empty().insert(Msg::Commit { term: hpre.term, ci, rec: CommitRec { term: hpre.term, ci, q } })),
{
    let t = hpre.term;
    let rec = CommitRec { term: t, ci, q };
    let hpost = MHost { commit: ci, crec: rec, ..hpre };
    let sent = Set::empty().insert(Msg::Commit { term: t, ci, rec });
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, evid) implies exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(sent)
    } by {
        let s2 = GState {
            hosts: s.hosts.update(i, hpost),
            net: s.net.insert(Msg::Commit { term: t, ci, rec }),
            commits: s.commits.insert(rec),
            ..s
        };
        assert forall|v: int| q.dom().contains(v) implies
            (#[trigger] q[v]) >= ci && s.net.contains(Msg::Ack { v, term: t, mi: q[v] }) by {
            assert(evid.contains(Msg::Ack { v, term: t, mi: q[v] }));
        }
        assert(t_leader_commit(s, s2, i, ci, q));
        assert(next_step(s, s2, TStep::LeaderCommit { i, ci, q }));
        assert(next(s, s2));
        assert(s2.net =~= s.net.union(sent));
        assert(s2.net == s.net.union(sent));
    }
}

proof fn lemma_lift_recv_commit(i: int, n: u8, hpre: MHost, ci: nat, mi: nat, rec: CommitRec)
    requires
        1 <= mi <= hpre.log.len(),
        ci <= mi,
        hpre.log[mi - 1].term == hpre.term,
        ci > hpre.commit,
    ensures
        host_refines(i, n, hpre,
            MHost { commit: ci, crec: rec, ..hpre },
            Set::empty().insert(Msg::Commit { term: hpre.term, ci, rec }),
            Set::empty()),
{
    let hpost = MHost { commit: ci, crec: rec, ..hpre };
    let evid = Set::empty().insert(Msg::Commit { term: hpre.term, ci, rec });
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, evid) implies exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(Set::empty())
    } by {
        let s2 = GState { hosts: s.hosts.update(i, hpost), ..s };
        assert(s.net.contains(Msg::Commit { term: hpre.term, ci, rec }));
        assert(t_recv_commit(s, s2, i, ci, mi, rec));
        assert(next_step(s, s2, TStep::RecvCommit { i, ci, mi, rec }));
        assert(next(s, s2));
        assert(s2.net =~= s.net.union(Set::empty()));
        assert(s2.net == s.net.union(Set::empty()));
    }
}

proof fn lemma_lift_send_commit(i: int, n: u8, hpre: MHost, ci: nat)
    requires
        hpre.role is Leader,
        1 <= ci <= hpre.commit,
    ensures
        host_refines(i, n, hpre, hpre, Set::empty(),
            Set::empty().insert(Msg::Commit { term: hpre.term, ci, rec: hpre.crec })),
{
    let m = Msg::Commit { term: hpre.term, ci, rec: hpre.crec };
    let sent = Set::empty().insert(m);
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, Set::empty()) implies exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpre)
        &&& s2.net == s.net.union(sent)
    } by {
        let s2 = GState { net: s.net.insert(m), ..s };
        assert(t_send_commit(s, s2, i, ci));
        assert(next_step(s, s2, TStep::SendCommit { i, ci }));
        assert(next(s, s2));
        assert(s2.hosts =~= s.hosts.update(i, hpre));
        assert(s2.hosts == s.hosts.update(i, hpre));
        assert(s2.net =~= s.net.union(sent));
        assert(s2.net == s.net.union(sent));
    }
}

proof fn lemma_lift_submit_read(i: int, n: u8, hpre: MHost)
    requires
        hpre.role is Leader,
    ensures
        host_refines(i, n, hpre,
            MHost { read_seq: (hpre.read_seq + 1) as nat, ..hpre },
            Set::empty(),
            Set::empty()
                .insert(Msg::Read { term: hpre.term, seq: (hpre.read_seq + 1) as nat })
                .insert(Msg::ReadConfirm { v: i, term: hpre.term, seq: (hpre.read_seq + 1) as nat })),
{
    let t = hpre.term;
    let sq = (hpre.read_seq + 1) as nat;
    let hpost = MHost { read_seq: sq, ..hpre };
    let sent = Set::empty()
        .insert(Msg::Read { term: t, seq: sq })
        .insert(Msg::ReadConfirm { v: i, term: t, seq: sq });
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, Set::empty()) implies exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(sent)
    } by {
        let s2 = GState {
            hosts: s.hosts.update(i, hpost),
            net: s.net.insert(Msg::Read { term: t, seq: sq }).insert(Msg::ReadConfirm { v: i, term: t, seq: sq }),
            reads: s.reads.insert(ReadRec { term: t, seq: sq, born: s.commits }),
            read_hwm: s.read_hwm.insert(t, sq),
            ..s
        };
        assert(t_submit_read(s, s2, i));
        assert(next_step(s, s2, TStep::SubmitRead { i }));
        assert(next(s, s2));
        assert(s2.net =~= s.net.union(sent));
        assert(s2.net == s.net.union(sent));
    }
}

proof fn lemma_lift_confirm_read(i: int, n: u8, hpre: MHost, sq: nat)
    requires
        hpre.role is Follower,
    ensures
        host_refines(i, n, hpre, hpre,
            Set::empty().insert(Msg::Read { term: hpre.term, seq: sq }),
            Set::empty().insert(Msg::ReadConfirm { v: i, term: hpre.term, seq: sq })),
{
    let t = hpre.term;
    let evid = Set::empty().insert(Msg::Read { term: t, seq: sq });
    let sent = Set::empty().insert(Msg::ReadConfirm { v: i, term: t, seq: sq });
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, evid) implies exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpre)
        &&& s2.net == s.net.union(sent)
    } by {
        let s2 = GState {
            hosts: s.hosts.update(i, hpre),
            net: s.net.insert(Msg::ReadConfirm { v: i, term: t, seq: sq }),
            ..s
        };
        assert(s.net.contains(Msg::Read { term: t, seq: sq }));
        assert(hpre == MHost { term: t, vote: hpre.vote, role: MRole::Follower, ..hpre });
        assert(t_confirm_read(s, s2, i, t, sq));
        assert(next_step(s, s2, TStep::ConfirmRead { i, term: t, seq: sq }));
        assert(next(s, s2));
        assert(s2.hosts =~= s.hosts.update(i, hpre));
        assert(s2.hosts == s.hosts.update(i, hpre));
        assert(s2.net =~= s.net.union(sent));
        assert(s2.net == s.net.union(sent));
    }
}

// ---------------------------------------------------------------------------
// Members: the agreed member set, identifying hosts by rank
// ---------------------------------------------------------------------------

/// The cluster member set: the node ids, sorted. A member's *rank* — its
/// position in this list — is its host index in the safety model; the list
/// is agreed across the cluster (trusted assumption 4), so ranks agree too.
pub struct Members {
    ids: Vec<NodeID>,
}

impl Members {
    /// The member ids.
    pub closed spec fn ids_spec(&self) -> Seq<NodeID> {
        self.ids@
    }

    /// Well-formed: strictly increasing (hence distinct).
    pub open spec fn wf(&self) -> bool {
        forall|k1: int, k2: int| 0 <= k1 < k2 < self.ids_spec().len() ==>
            #[trigger] self.ids_spec()[k1] < #[trigger] self.ids_spec()[k2]
    }

    /// The cluster size.
    pub open spec fn n(&self) -> nat {
        self.ids_spec().len()
    }

    /// Membership.
    pub open spec fn is_member(&self, id: NodeID) -> bool {
        exists|k: int| 0 <= k < self.ids_spec().len() && self.ids_spec()[k] == id
    }

    /// The rank of a member (meaningful only when `is_member`).
    pub open spec fn rank_of(&self, id: NodeID) -> int {
        choose|k: int| 0 <= k < self.ids_spec().len() && self.ids_spec()[k] == id
    }

    /// A member's rank is the unique position holding its id.
    pub proof fn lemma_rank(&self, id: NodeID)
        requires
            self.wf(),
            self.is_member(id),
        ensures
            0 <= self.rank_of(id) < self.n(),
            self.ids_spec()[self.rank_of(id)] == id,
            forall|k: int| 0 <= k < self.n() && self.ids_spec()[k] == id ==> k == self.rank_of(id),
    {
        let r = self.rank_of(id);
        assert(0 <= r < self.n() && self.ids_spec()[r] == id);
        assert forall|k: int| 0 <= k < self.n() && self.ids_spec()[k] == id implies k == r by {
            if k < r {
                assert(self.ids_spec()[k] < self.ids_spec()[r]);
            } else if k > r {
                assert(self.ids_spec()[r] < self.ids_spec()[k]);
            }
        }
    }

    /// Distinct members have distinct ranks.
    pub proof fn lemma_rank_distinct(&self, id1: NodeID, id2: NodeID)
        requires
            self.wf(),
            self.is_member(id1),
            self.is_member(id2),
            id1 != id2,
        ensures
            self.rank_of(id1) != self.rank_of(id2),
    {
        self.lemma_rank(id1);
        self.lemma_rank(id2);
    }

    /// Builds a member set from a sorted id list. Returns None if the list
    /// is empty, not strictly increasing, or larger than 255 nodes.
    pub fn new(ids: Vec<NodeID>) -> (r: Option<Members>)
        ensures
            r matches Some(m) ==> m.wf() && m.ids_spec() == ids@ && 1 <= m.n() <= 255,
    {
        if ids.len() == 0 || ids.len() > 255 {
            return None;
        }
        let mut k: usize = 1;
        while k < ids.len()
            invariant
                1 <= k <= ids@.len(),
                forall|k1: int, k2: int| 0 <= k1 < k2 < k ==>
                    #[trigger] ids@[k1] < #[trigger] ids@[k2],
            decreases ids@.len() - k,
        {
            if ids[k - 1] >= ids[k] {
                return None;
            }
            proof {
                assert forall|k1: int, k2: int| 0 <= k1 < k2 < k + 1 implies
                    #[trigger] ids@[k1] < #[trigger] ids@[k2] by {
                    if k2 == k {
                        assert(ids@[k1] <= ids@[k - 1]);
                    }
                }
            }
            k += 1;
        }
        Some(Members { ids })
    }

    /// The rank of `id`, or None if it is not a member.
    fn rank(&self, id: NodeID) -> (r: Option<u8>)
        requires
            self.wf(),
            self.n() <= 255,
        ensures
            r matches Some(k) ==> self.is_member(id) && k as int == self.rank_of(id) && (k as nat) < self.n(),
            r is None ==> !self.is_member(id),
    {
        let mut k: usize = 0;
        while k < self.ids.len()
            invariant
                k <= self.ids@.len() <= 255,
                self.wf(),
                forall|j: int| 0 <= j < k ==> #[trigger] self.ids_spec()[j] != id,
            decreases self.ids@.len() - k,
        {
            if self.ids[k] == id {
                proof {
                    assert(self.ids_spec()[k as int] == id);
                    assert(self.is_member(id));
                    self.lemma_rank(id);
                }
                return Some(k as u8);
            }
            k += 1;
        }
        None
    }

    /// The cluster size.
    fn count(&self) -> (r: u8)
        requires
            self.n() <= 255,
        ensures
            r as nat == self.n(),
    {
        self.ids.len() as u8
    }
}

/// The abstract view of a durable vote: the member's rank, or -1 (an
/// impossible rank) for a vote recorded for a node outside the current
/// member set (a cluster misconfiguration; such a vote never matches any
/// candidate).
pub open spec fn vote_abs(m: &Members, vote: Option<NodeID>) -> Option<int> {
    match vote {
        None => None,
        Some(id) => if m.is_member(id) {
            Some(m.rank_of(id))
        } else {
            Some(-1)
        },
    }
}

/// The set of ranks with a granted vote.
pub open spec fn vote_set(votes: Seq<bool>) -> Set<int> {
    vstd::set_lib::set_int_range(0, votes.len() as int).filter(|k: int| votes[k])
}

// ---------------------------------------------------------------------------
// Progress: per-member replication state on the leader
// ---------------------------------------------------------------------------

/// Per-member replication progress in the leader's term, indexed by rank in
/// `Abs`. The fields are private: only the verified step functions advance
/// them, and `Abs::inv` guarantees that every nonzero match index and read
/// sequence is backed by ack/confirmation evidence in the ghost history —
/// the shell cannot advance progress without the evidence.
pub struct Progress {
    /// The next index to replicate to the member. Initialized to
    /// last_index+1, decreased when probing log mismatches. Always in the
    /// range [match_index+1, last_index+1]. Entries not yet sent are in the
    /// range [next_index, last_index]; entries not acknowledged are in the
    /// range [match_index+1, next_index).
    next_index: Index,
    /// The highest index where the member's log is known to match the
    /// leader. Initialized to 0, increases monotonically.
    match_index: Index,
    /// The last read sequence number confirmed by this member. For the
    /// leader's own rank: the last issued read sequence number.
    read_seq: u64,
}

impl Progress {
    pub closed spec fn next_index_spec(&self) -> Index {
        self.next_index
    }

    pub closed spec fn match_index_spec(&self) -> Index {
        self.match_index
    }

    pub closed spec fn read_seq_spec(&self) -> u64 {
        self.read_seq
    }
}

// ---------------------------------------------------------------------------
// Abs: the verified node state
// ---------------------------------------------------------------------------

/// The role-specific verified state.
enum AbsRole {
    Follower,
    /// A candidate's granted votes, by rank.
    Candidate { votes: Vec<bool> },
    /// A leader's per-member replication progress, by rank. The entry at the
    /// leader's own rank carries the leader's read sequence counter (its
    /// match index is unused and stays 0).
    Leader { progress: Vec<Progress> },
}

/// The verified volatile state of a node: member set, role state, and the
/// ghost abstract state and message evidence. Fields are private; every
/// mutation happens in a verified step function whose postcondition proves
/// the step refines the safety model (`host_refines_star`).
pub struct Abs {
    /// The agreed member set.
    members: Members,
    /// This node's id.
    me: NodeID,
    /// This node's rank (== members.rank_of(me)).
    rank: u8,
    /// The cluster size (== members.n()).
    n: u8,
    /// Role-specific verified state, mirroring the ghost role.
    role: AbsRole,
    /// Ghost: this node's abstract state in the safety model.
    habs: Ghost<MHost>,
    /// Ghost: the abstract counterparts of the messages this node has
    /// received or sent — trusted (via `recv_msg`) to be in the model's
    /// message history.
    evid: Ghost<Set<Msg>>,
}

impl Abs {
    /// This node's model host index (its rank).
    pub closed spec fn i(&self) -> int {
        self.rank as int
    }

    /// The cluster size.
    pub closed spec fn n_spec(&self) -> u8 {
        self.n
    }

    /// The ghost abstract state.
    pub closed spec fn habs(&self) -> MHost {
        self.habs@
    }

    /// The ghost message evidence.
    pub closed spec fn evid(&self) -> Set<Msg> {
        self.evid@
    }

    pub closed spec fn is_follower(&self) -> bool {
        self.role is Follower
    }

    pub closed spec fn is_candidate(&self) -> bool {
        self.role is Candidate
    }

    pub closed spec fn is_leader(&self) -> bool {
        self.role is Leader
    }

    /// The node identity (member set, id, rank, size) never changes.
    pub closed spec fn same_node(&self, o: &Abs) -> bool {
        &&& self.members.ids_spec() == o.members.ids_spec()
        &&& self.me == o.me
        &&& self.rank == o.rank
        &&& self.n == o.n
    }

    /// The leader's progress entry for rank `k`.
    pub closed spec fn progress_spec(&self, k: int) -> Progress {
        self.role->Leader_progress@[k]
    }

    /// The node state invariant, tying the exec state and the ghost abstract
    /// state to the (single, owned) verified log:
    ///
    /// * the member set is well-formed and this node is a member;
    /// * the ghost host state mirrors the durable log state (term, vote,
    ///   entries, commit) and the exec role;
    /// * a candidate's ghost vote set is its exec vote bitmap;
    /// * a leader's log ends in an entry of its own term, its ghost read
    ///   sequence is the counter at its own rank, and every member's
    ///   progress is within the log with evidence backing every nonzero
    ///   match index and read sequence.
    pub closed spec fn inv(&self, log: &Log) -> bool {
        let h = self.habs@;
        &&& log.inv()
        &&& self.members.wf()
        &&& 1 <= self.members.n() <= 255
        &&& self.n as nat == self.members.n()
        &&& self.members.is_member(self.me)
        &&& self.rank as int == self.members.rank_of(self.me)
        &&& h.term == log.term() as nat
        &&& h.vote == vote_abs(&self.members, log.vote())
        &&& h.log == log.view()
        &&& h.commit == log.commit_index() as nat
        &&& match self.role {
            AbsRole::Follower => h.role is Follower,
            AbsRole::Candidate { votes } => {
                &&& h.role is Candidate
                &&& votes@.len() == self.n as nat
                &&& h.votes == vote_set(votes@)
            },
            AbsRole::Leader { progress } => {
                &&& h.role is Leader
                &&& progress@.len() == self.n as nat
                &&& h.read_seq == progress@[self.rank as int].read_seq as nat
                &&& log.view().len() >= 1
                &&& log.view()[log.view().len() - 1].term == h.term
                &&& forall|k: int| 0 <= k < progress@.len() ==> {
                    let p = #[trigger] progress@[k];
                    &&& p.match_index < p.next_index
                    &&& p.match_index as nat <= log.view().len()
                    &&& p.next_index as nat <= log.view().len() + 1
                    &&& p.match_index >= 1 ==> self.evid@.contains(Msg::Ack {
                        v: k,
                        term: h.term,
                        mi: p.match_index as nat,
                    })
                    &&& p.read_seq >= 1 ==> self.evid@.contains(Msg::ReadConfirm {
                        v: k,
                        term: h.term,
                        seq: p.read_seq as nat,
                    })
                }
            },
        }
    }

    // --- Trusted recovery ----------------------------------------------

    /// TRUSTED (storage integrity + composition): the abstract state of this
    /// node recovered from its durable log at startup. On a fresh start this
    /// is the model's initial host state (`init_host`, as
    /// `lemma_cluster_init` binds it); after a crash it is the `t_restart`
    /// post-state of the pre-crash host (as `lemma_cluster_restart` rebinds
    /// it) — term, vote and log are fsynced, and the commit index (which is
    /// not) may have regressed, which `t_restart` allows. Not covered: with
    /// `Log::enable_fsync` disabled a crash can lose acknowledged entries, a
    /// state outside the model.
    #[verifier::external_body]
    fn recover_host(members: &Members, rank: u8, log: &Log) -> (h: Ghost<MHost>)
        ensures
            h@.term == log.term() as nat,
            h@.vote == vote_abs(members, log.vote()),
            h@.role is Follower,
            h@.log == log.view(),
            h@.commit == log.commit_index() as nat,
            h@.votes == Set::<int>::empty(),
            h@.read_seq == 0,
    {
        Ghost::assume_new()
    }

    /// Creates the verified node state at startup, as a follower recovered
    /// from the durable log. `ids` is the full member list (this node
    /// included), sorted; returns None if it is unsorted, empty, larger
    /// than 255 nodes, or does not contain `me`.
    pub fn recover(me: NodeID, ids: Vec<NodeID>, log: &Log) -> (r: Option<Abs>)
        requires
            log.inv(),
        ensures
            r matches Some(a) ==> {
                &&& a.inv(log)
                &&& a.is_follower()
                &&& a.evid() == Set::<Msg>::empty()
            },
    {
        let members = match Members::new(ids) {
            Some(m) => m,
            None => return None,
        };
        let n = members.count();
        let rank = match members.rank(me) {
            Some(r) => r,
            None => return None,
        };
        let habs = Self::recover_host(&members, rank, log);
        Some(Abs {
            members,
            me,
            rank,
            n,
            role: AbsRole::Follower,
            habs,
            evid: Ghost(Set::empty()),
        })
    }

    // --- Term and role transitions -------------------------------------

    /// Discovering a higher term: become a leaderless follower in it,
    /// clearing the vote (`into_follower(term, None)` on any higher-term
    /// message; the shell then re-steps the message at the equal term).
    /// Returns false (and does nothing) if the term is not higher. Refines
    /// `t_bump_term`.
    pub fn bump_term(&mut self, log: &mut Log, term: Term) -> (r: Result<bool>)
        requires
            old(self).inv(old(log)),
        ensures
            r matches Ok(b) ==> {
                &&& !b ==> *final(self) == *old(self) && *final(log) == *old(log)
                &&& b ==> {
                    &&& term > old(log).term()
                    &&& final(self).inv(final(log))
                    &&& final(self).same_node(old(self))
                    &&& final(self).is_follower()
                    &&& final(log).term() == term && final(log).vote() is None
                    &&& final(log).view() == old(log).view()
                    &&& final(log).commit_index() == old(log).commit_index()
                    &&& final(self).habs() == (MHost {
                        term: term as nat,
                        vote: None,
                        role: MRole::Follower,
                        ..old(self).habs()
                    })
                    &&& host_refines_star(old(self).i(), old(self).n_spec(), old(self).habs(),
                        final(self).habs(), old(self).evid(), Set::empty())
                    &&& final(self).evid() == old(self).evid()
                }
            },
    {
        let (cur, _) = log.get_term_vote();
        if term <= cur {
            return Ok(false);
        }
        let ghost h = self.habs@;
        log.set_term_vote(term, None)?;
        proof {
            lemma_lift_bump(self.rank as int, self.n, h, term as nat);
            lemma_star_of_single(self.rank as int, self.n, h,
                MHost { term: term as nat, vote: None, role: MRole::Follower, ..h },
                Set::empty(), Set::empty());
            lemma_star_mono(self.rank as int, self.n, h,
                MHost { term: term as nat, vote: None, role: MRole::Follower, ..h },
                Set::empty(), self.evid@, Set::empty());
        }
        self.habs = Ghost(MHost { term: term as nat, vote: None, role: MRole::Follower, ..h });
        self.role = AbsRole::Follower;
        Ok(true)
    }

    /// A candidate stepping down to follower in its own term (on discovering
    /// the election's winner). Refines `t_step_down`.
    pub fn step_down(&mut self, log: &Log)
        requires
            old(self).inv(log),
        ensures
            final(self).inv(log),
            final(self).same_node(old(self)),
            final(self).is_follower(),
            final(self).habs() == (MHost { role: MRole::Follower, ..old(self).habs() }),
            host_refines_star(old(self).i(), old(self).n_spec(), old(self).habs(),
                final(self).habs(), old(self).evid(), Set::empty()),
            final(self).evid() == old(self).evid(),
    {
        match &self.role {
            AbsRole::Candidate { .. } => {}
            _ => fault(Fault::WrongRole),
        }
        let ghost h = self.habs@;
        proof {
            lemma_lift_step_down(self.rank as int, self.n, h);
            lemma_star_of_single(self.rank as int, self.n, h,
                MHost { role: MRole::Follower, ..h }, Set::empty(), Set::empty());
            lemma_star_mono(self.rank as int, self.n, h, MHost { role: MRole::Follower, ..h },
                Set::empty(), self.evid@, Set::empty());
        }
        self.habs = Ghost(MHost { role: MRole::Follower, ..h });
        self.role = AbsRole::Follower;
    }

    /// Campaigning: bump the term, vote for self, solicit votes. Writes the
    /// new term and self-vote to the log and returns the Campaign message to
    /// broadcast. Refines `t_campaign`.
    pub fn campaign(&mut self, log: &mut Log) -> (r: Result<CampaignPlan>)
        requires
            old(self).inv(old(log)),
        ensures
            r matches Ok(p) ==> {
                let h = old(self).habs();
                let i = old(self).i();
                let t = (h.term + 1) as nat;
                let sent = Set::empty()
                    .insert(Msg::Campaign { c: i, term: t, clog: h.log })
                    .insert(Msg::Vote { v: i, c: i, term: t, vlog: h.log });
                &&& final(self).inv(final(log))
                &&& final(self).same_node(old(self))
                &&& final(self).is_candidate()
                &&& p.term as nat == t
                &&& p.last_index as nat == h.log.len()
                &&& p.last_term as nat == last_term(h.log)
                &&& final(log).view() == old(log).view()
                &&& host_refines_star(i, old(self).n_spec(), h, final(self).habs(),
                    old(self).evid(), sent)
                &&& evid_grows(old(self).evid(), final(self).evid(), Set::empty(), sent)
            },
    {
        match &self.role {
            AbsRole::Leader { .. } => fault(Fault::WrongRole),
            _ => {}
        }
        let (term, _) = log.get_term_vote();
        if term == u64::MAX {
            fault(Fault::TermOverflow);
        }
        let ghost h = self.habs@;
        let ghost i = self.rank as int;
        let ghost h2 = MHost {
            term: (term + 1) as nat,
            vote: Some(i),
            role: MRole::Candidate,
            votes: Set::empty().insert(i),
            vote_logs: Map::empty().insert(i, h.log),
            ..h
        };
        let ghost sent = Set::empty()
            .insert(Msg::Campaign { c: i, term: (term + 1) as nat, clog: h.log })
            .insert(Msg::Vote { v: i, c: i, term: (term + 1) as nat, vlog: h.log });
        log.set_term_vote(term + 1, Some(self.me))?;
        proof {
            lemma_lift_campaign(i, self.n, h);
            lemma_star_of_single(i, self.n, h, h2, Set::empty(), sent);
            lemma_star_mono(i, self.n, h, h2, Set::empty(), self.evid@, sent);
        }
        // The vote bitmap: everyone false except ourselves.
        let mut votes: Vec<bool> = Vec::new();
        let mut k: usize = 0;
        while k < self.n as usize
            invariant
                k <= self.n as usize,
                votes@.len() == k,
                forall|j: int| 0 <= j < k ==> !(#[trigger] votes@[j]),
            decreases self.n as usize - k,
        {
            votes.push(false);
            k += 1;
        }
        proof {
            self.members.lemma_rank(self.me);
        }
        let slot = &mut votes[self.rank as usize];
        *slot = true;
        proof {
            assert(vote_set(votes@) =~= Set::empty().insert(i));
        }
        self.role = AbsRole::Candidate { votes };
        self.habs = Ghost(h2);
        self.evid = Ghost(self.evid@.union(sent));
        let (last_index, lterm) = log.get_last_index();
        Ok(CampaignPlan { term: term + 1, last_index, last_term: lterm })
    }

    /// Deciding a vote request at the receiver's own term
    /// (`Message::Campaign` handling): grant only if not already committed
    /// to another candidate this term, and only if the candidate's log is at
    /// least as up-to-date (section 5.4.1) — judged, as in the
    /// implementation, on the (last_index, last_term) summaries. On a grant,
    /// writes the vote to the log and returns true; the shell sends the
    /// response either way. Refines `t_grant`.
    pub fn grant(
        &mut self, log: &mut Log, from: NodeID, term: Term, last_index: Index, lterm: Term,
    ) -> (r: Result<bool>)
        requires
            old(self).inv(old(log)),
        ensures
            r matches Ok(granted) ==> {
                let h = old(self).habs();
                let i = old(self).i();
                &&& !granted ==> *final(self) == *old(self) && *final(log) == *old(log)
                &&& granted ==> {
                    &&& final(self).inv(final(log))
                    &&& final(self).same_node(old(self))
                    &&& final(self).is_follower()
                    &&& final(log).view() == old(log).view()
                    &&& final(log).commit_index() == old(log).commit_index()
                    &&& final(log).term() == old(log).term()
                    &&& exists|m: Msg| {
                        let sent = Set::empty().insert(Msg::Vote {
                            v: i,
                            c: m->Campaign_c,
                            term: term as nat,
                            vlog: h.log,
                        });
                        &&& #[trigger] abstracts_campaign(m, m->Campaign_c, term as nat,
                            last_index as nat, lterm as nat)
                        &&& final(self).habs() == (MHost { vote: Some(m->Campaign_c), ..h })
                        &&& host_refines_star(i, old(self).n_spec(), h, final(self).habs(),
                            old(self).evid().insert(m), sent)
                        &&& evid_grows(old(self).evid(), final(self).evid(),
                            Set::empty().insert(m), sent)
                    }
                }
            },
    {
        match &self.role {
            AbsRole::Follower => {}
            _ => fault(Fault::WrongRole),
        }
        let (cur, vote) = log.get_term_vote();
        if term != cur {
            fault(Fault::WrongTerm);
        }
        // A campaign from ourselves is impossible (nodes don't send to
        // themselves); refuse rather than model it.
        if from == self.me {
            return Ok(false);
        }
        let c = match self.members.rank(from) {
            Some(c) => c,
            None => fault(Fault::UnknownNode(from)),
        };
        // Don't vote if we already voted for someone else in this term.
        if let Some(v) = vote {
            if v != from {
                return Ok(false);
            }
        }
        // Only vote if the candidate's log is at least as up-to-date as ours.
        let (log_index, log_term) = log.get_last_index();
        if log_term > lterm || (log_term == lterm && log_index > last_index) {
            return Ok(false);
        }
        let m = recv_msg(&MsgSummary::Campaign { c, term, last_index, last_term: lterm });
        let ghost h = self.habs@;
        let ghost i = self.rank as int;
        let ghost clog = m@->Campaign_clog;
        let ghost h2 = MHost { vote: Some(c as int), ..h };
        let ghost sent = Set::empty().insert(Msg::Vote { v: i, c: c as int, term: term as nat, vlog: h.log });
        proof {
            self.members.lemma_rank_distinct(self.me, from);
            self.members.lemma_rank(from);
            assert(up_to_date(clog, h.log));
            assert(h.vote is None || h.vote == Some(c as int));
            lemma_lift_grant(i, self.n, h, c as int, clog);
            lemma_star_of_single(i, self.n, h, h2, Set::empty().insert(m@), sent);
            lemma_star_mono(i, self.n, h, h2, Set::empty().insert(m@),
                self.evid@.insert(m@), sent);
        }
        log.set_term_vote(term, Some(from))?;
        self.habs = Ghost(h2);
        self.evid = Ghost(self.evid@.insert(m@).union(sent));
        Ok(true)
    }

    /// A candidate recording a granted vote (`Message::CampaignResponse`
    /// handling). Returns true when the votes now reach a quorum (the shell
    /// then transitions to leader). Refines `t_collect_vote`.
    pub fn collect_vote(&mut self, log: &Log, from: NodeID, term: Term) -> (r: bool)
        requires
            old(self).inv(log),
        ensures
            final(self).inv(log),
            final(self).same_node(old(self)),
            final(self).is_candidate(),
            exists|m: Msg| {
                &&& #[trigger] abstracts_vote(m, m->Vote_v, old(self).i(), term as nat)
                &&& final(self).habs() == (MHost {
                    votes: old(self).habs().votes.insert(m->Vote_v),
                    vote_logs: old(self).habs().vote_logs.insert(m->Vote_v, m->Vote_vlog),
                    ..old(self).habs()
                })
                &&& host_refines_star(old(self).i(), old(self).n_spec(), old(self).habs(),
                    final(self).habs(), old(self).evid().insert(m), Set::empty())
                &&& evid_grows(old(self).evid(), final(self).evid(), Set::empty().insert(m),
                    Set::empty())
            },
    {
        match &self.role {
            AbsRole::Candidate { .. } => {}
            _ => fault(Fault::WrongRole),
        }
        let (cur, _) = log.get_term_vote();
        if term != cur {
            fault(Fault::WrongTerm);
        }
        let v = match self.members.rank(from) {
            Some(v) => v,
            None => fault(Fault::UnknownNode(from)),
        };
        let m = recv_msg(&MsgSummary::Vote { v, c: self.rank, term });
        let ghost h = self.habs@;
        let ghost i = self.rank as int;
        let ghost vlog = m@->Vote_vlog;
        let ghost h2 = MHost {
            votes: h.votes.insert(v as int),
            vote_logs: h.vote_logs.insert(v as int, vlog),
            ..h
        };
        proof {
            lemma_lift_collect_vote(i, self.n, h, v as int, vlog);
            lemma_star_of_single(i, self.n, h, h2, Set::empty().insert(m@), Set::empty());
            lemma_star_mono(i, self.n, h, h2, Set::empty().insert(m@),
                self.evid@.insert(m@), Set::empty());
        }
        let votes = match &mut self.role {
            AbsRole::Candidate { votes } => votes,
            _ => fault(Fault::WrongRole),
        };
        let slot = &mut votes[v as usize];
        *slot = true;
        proof {
            assert(vote_set(self.role->Candidate_votes@) =~= h2.votes);
        }
        self.habs = Ghost(h2);
        self.evid = Ghost(self.evid@.insert(m@));
        proof {
            assert(m@->Vote_v == v as int);
            assert(abstracts_vote(m@, m@->Vote_v, old(self).i(), term as nat));
            assert(evid_grows(old(self).evid(), self.evid@, Set::empty().insert(m@), Set::empty()));
        }
        // Count the votes and report whether they reach a quorum.
        let count = self.count_votes();
        count >= self.n as usize / 2 + 1
    }

    /// Counts a candidate's granted votes: the size of the vote set.
    /// Faults when not a candidate.
    fn count_votes(&self) -> (r: usize)
        ensures
            self.is_candidate(),
            r == vote_set(self.role->Candidate_votes@).len(),
            r <= self.role->Candidate_votes@.len(),
    {
        let votes = match &self.role {
            AbsRole::Candidate { votes } => votes,
            _ => fault(Fault::WrongRole),
        };
        let mut count: usize = 0;
        let mut k: usize = 0;
        let ghost mut qids: Seq<int> = Seq::empty();
        while k < votes.len()
            invariant
                k <= votes@.len(),
                count <= k,
                count == qids.len(),
                qids.no_duplicates(),
                forall|j: int| 0 <= j < qids.len() ==> 0 <= #[trigger] qids[j] < k,
                forall|x: int| qids.to_set().contains(x) <==> (0 <= x < k && votes@[x]),
            decreases votes@.len() - k,
        {
            if votes[k] {
                proof {
                    let old_qids = qids;
                    qids = qids.push(k as int);
                    assert forall|x: int| qids.to_set().contains(x) implies
                        old_qids.to_set().contains(x) || x == k as int by {
                        let j = choose|j: int| 0 <= j < qids.len() && qids[j] == x;
                        if j < qids.len() - 1 {
                            assert(old_qids[j] == x);
                        }
                    }
                    assert forall|x: int| old_qids.to_set().contains(x) implies
                        qids.to_set().contains(x) by {
                        let j = choose|j: int| 0 <= j < old_qids.len() && old_qids[j] == x;
                        assert(qids[j] == x);
                    }
                    assert(qids.to_set().contains(k as int)) by {
                        assert(qids[qids.len() - 1] == k as int);
                    }
                }
                count += 1;
            }
            k += 1;
        }
        proof {
            qids.unique_seq_to_set();
            assert(qids.to_set() =~= vote_set(votes@));
        }
        count
    }

    /// Winning an election (`Candidate::into_leader`): checks the vote
    /// quorum — the strict-majority arithmetic of `quorum_size` — appends
    /// the leadership noop entry (section 5.4.2), and installs the leader
    /// role with fresh replication progress. Returns the noop entry's index.
    /// Refines `t_become_leader`.
    pub fn become_leader(&mut self, log: &mut Log) -> (r: Result<Index>)
        requires
            old(self).inv(old(log)),
        ensures
            r matches Ok(index) ==> {
                let h = old(self).habs();
                &&& final(self).inv(final(log))
                &&& final(self).same_node(old(self))
                &&& final(self).is_leader()
                &&& index as nat == h.log.len() + 1
                &&& final(log).view() == old(log).view().push(AEntry { term: h.term, cmd: None })
                &&& final(self).habs() == (MHost {
                    role: MRole::Leader,
                    log: final(log).view(),
                    read_seq: 0,
                    ..h
                })
                &&& host_refines_star(old(self).i(), old(self).n_spec(), h, final(self).habs(),
                    old(self).evid(), Set::empty())
                &&& final(self).evid() == old(self).evid()
            },
    {
        // Quorum check over the recorded votes.
        let count = self.count_votes();
        if count < self.n as usize / 2 + 1 {
            fault(Fault::NoVoteQuorum);
        }
        let ghost h = self.habs@;
        let ghost i = self.rank as int;
        let ghost h2 = MHost {
            role: MRole::Leader,
            log: h.log.push(AEntry { term: h.term, cmd: None }),
            read_seq: 0,
            ..h
        };
        proof {
            // The votes are ranks below n, so a strict majority of them is a
            // quorum.
            assert forall|v: int| vote_set(self.role->Candidate_votes@).contains(v) implies
                node_ids(self.n as nat).contains(v) by {
                vstd::set_lib::lemma_int_range(0, self.n as int);
                assert(node_ids(self.n as nat) == vstd::set_lib::set_int_range(0, self.n as int));
            }
            assert(is_quorum(self.n as nat, h.votes));
            lemma_lift_become_leader(i, self.n, h);
            lemma_star_of_single(i, self.n, h, h2, Set::empty(), Set::empty());
            lemma_star_mono(i, self.n, h, h2, Set::empty(), self.evid@, Set::empty());
        }
        let (last_index, _) = log.get_last_index();
        if last_index == u64::MAX {
            fault(Fault::IndexOverflow);
        }
        let index = log.append(None)?;
        // Fresh progress for every member: next at the new last index + 1
        // (the noop we just appended is index == last_index + 1).
        let mut progress: Vec<Progress> = Vec::new();
        let mut k: usize = 0;
        while k < self.n as usize
            invariant
                k <= self.n as usize,
                progress@.len() == k,
                last_index < u64::MAX,
                forall|j: int| 0 <= j < k ==> (#[trigger] progress@[j]) == (Progress {
                    next_index: (last_index + 1) as u64,
                    match_index: 0u64,
                    read_seq: 0u64,
                }),
            decreases self.n as usize - k,
        {
            progress.push(Progress { next_index: last_index + 1, match_index: 0, read_seq: 0 });
            k += 1;
        }
        self.role = AbsRole::Leader { progress };
        self.habs = Ghost(h2);
        proof {
            self.members.lemma_rank(self.me);
        }
        Ok(index)
    }

    // --- Follower message steps ----------------------------------------

    /// A follower handling a leader heartbeat at its own term: check whether
    /// our log matches the leader's last index (the ack), confirm the read
    /// sequence number, and advance the commit index if the leader's is
    /// ahead and we matched. Returns the response plan; the shell sends
    /// `HeartbeatResponse { match_index, read_seq }` and applies newly
    /// committed entries. Refines `t_send_ack` + `t_confirm_read` +
    /// `t_recv_commit`.
    pub fn follower_heartbeat(
        &mut self, log: &mut Log, term: Term, last_index: Index, commit_index: Index, read_seq: u64,
    ) -> (r: Result<HeartbeatPlan>)
        requires
            old(self).inv(old(log)),
        ensures
            r matches Ok(p) ==> {
                let h = old(self).habs();
                let i = old(self).i();
                let ack: Set<Msg> = if p.match_index != 0 {
                    Set::empty().insert(Msg::Ack { v: i, term: term as nat, mi: last_index as nat })
                } else {
                    Set::empty()
                };
                let conf: Set<Msg> = if read_seq >= 1 {
                    Set::empty().insert(Msg::ReadConfirm { v: i, term: term as nat, seq: read_seq as nat })
                } else {
                    Set::empty()
                };
                &&& final(self).inv(final(log))
                &&& final(self).same_node(old(self))
                &&& final(self).is_follower()
                &&& p.match_index == (if old(log).has_spec(last_index, term) { last_index } else { 0u64 })
                &&& final(log).view() == old(log).view()
                &&& final(log).term() == old(log).term()
                &&& final(log).vote() == old(log).vote()
                &&& p.committed ==> final(log).commit_index() == commit_index
                    && commit_index > old(log).commit_index() && p.match_index != 0
                &&& !p.committed ==> final(log).commit_index() == old(log).commit_index()
                &&& exists|cm: Msg| {
                    let recv = (if read_seq >= 1 {
                        Set::empty().insert(Msg::Read { term: term as nat, seq: read_seq as nat })
                    } else {
                        Set::empty()
                    }).union(if p.committed { Set::empty().insert(cm) } else { Set::empty() });
                    &&& #[trigger] abstracts_commit(cm, term as nat, commit_index as nat)
                    &&& host_refines_star(i, old(self).n_spec(), h, final(self).habs(),
                        old(self).evid().union(recv), ack.union(conf))
                    &&& evid_grows(old(self).evid(), final(self).evid(), recv, ack.union(conf))
                }
            },
    {
        match &self.role {
            AbsRole::Follower => {}
            _ => fault(Fault::WrongRole),
        }
        let (cur, _) = log.get_term_vote();
        if term != cur {
            fault(Fault::WrongTerm);
        }
        if commit_index > last_index {
            fault(Fault::CommitAfterLastIndex);
        }
        let ghost h = self.habs@;
        let ghost i = self.rank as int;
        let ghost n = self.n;

        // Check if our log matches the leader's log up to last_index.
        // last_index always has the leader's term, since it only appends
        // entries in its term.
        let matched = log.has(last_index, term)?;
        let match_index: Index = if matched { last_index } else { 0 };

        // The read sequence evidence: the heartbeat re-announces the
        // leader's Read message.
        let ghost read_evid: Set<Msg> = if read_seq >= 1 {
            Set::empty().insert(Msg::Read { term: term as nat, seq: read_seq as nat })
        } else {
            Set::empty()
        };
        if read_seq >= 1 {
            let rm = recv_msg(&MsgSummary::Read { term, seq: read_seq });
            self.evid = Ghost(self.evid@.insert(rm@));
        }

        // Ghost: a match acks the leader's last index (t_send_ack), and the
        // response's read_seq echo confirms the read (t_confirm_read).
        let ghost ack: Set<Msg> = if matched {
            Set::empty().insert(Msg::Ack { v: i, term: term as nat, mi: last_index as nat })
        } else {
            Set::empty()
        };
        let ghost conf: Set<Msg> = if read_seq >= 1 {
            Set::empty().insert(Msg::ReadConfirm { v: i, term: term as nat, seq: read_seq as nat })
        } else {
            Set::empty()
        };
        let ghost e0 = self.evid@;
        proof {
            lemma_star_refl(i, n, h, e0);
            if matched {
                lemma_lift_send_ack(i, n, h, last_index as nat);
                lemma_star_extend(i, n, h, h, h, e0, Set::empty(), Set::empty(), ack);
                assert(Set::empty().union(ack) =~= ack);
            }
            assert(host_refines_star(i, n, h, h, e0, ack)) by {
                if !matched {
                    assert(ack =~= Set::<Msg>::empty());
                    lemma_star_refl(i, n, h, e0);
                }
            }
            if read_seq >= 1 {
                lemma_lift_confirm_read(i, n, h, read_seq as nat);
                assert(read_evid.subset_of(e0.union(ack)));
                lemma_star_extend(i, n, h, h, h, e0, ack, read_evid, conf);
            }
            assert(host_refines_star(i, n, h, h, e0, ack.union(conf))) by {
                if !(read_seq >= 1) {
                    assert(ack.union(conf) =~= ack);
                }
            }
        }
        self.evid = Ghost(self.evid@.union(ack).union(conf));

        // Advance the commit index. We can only do this if we matched the
        // leader's last_index, which implies that the logs are identical up
        // to match_index; this also implies that the commit_index is present
        // in our log.
        let (old_commit, _) = log.get_commit_index();
        if matched && commit_index > old_commit {
            let cm = recv_msg(&MsgSummary::Commit { term, commit_index });
            let ghost rec = cm@->Commit_rec;
            let ghost h2 = MHost { commit: commit_index as nat, crec: rec, ..h };
            let ghost recv = read_evid.union(Set::empty().insert(cm@));
            proof {
                assert(abstracts_commit(cm@, term as nat, commit_index as nat));
                assert(cm@ == Msg::Commit { term: term as nat, ci: commit_index as nat, rec });
                lemma_lift_recv_commit(i, n, h, commit_index as nat, last_index as nat, rec);
                assert(Set::empty().insert(cm@).subset_of(
                    e0.insert(cm@).union(ack.union(conf))));
                lemma_star_mono(i, n, h, h, e0, e0.insert(cm@), ack.union(conf));
                lemma_star_extend(i, n, h, h, h2, e0.insert(cm@), ack.union(conf),
                    Set::empty().insert(cm@), Set::empty());
                assert((ack.union(conf)).union(Set::<Msg>::empty()) =~= ack.union(conf));
                assert(e0.insert(cm@) =~= old(self).evid@.union(recv));
                assert(host_refines_star(i, n, h, h2, old(self).evid@.union(recv),
                    ack.union(conf)));
            }
            log.commit(commit_index)?;
            self.habs = Ghost(h2);
            self.evid = Ghost(self.evid@.insert(cm@));
            proof {
                assert(evid_grows(old(self).evid@, self.evid@, recv, ack.union(conf))) by {
                    assert forall|m: Msg| self.evid@.contains(m) implies
                        old(self).evid@.contains(m) || recv.contains(m)
                        || ack.union(conf).contains(m) by {
                        if m != cm@ && !ack.contains(m) && !conf.contains(m) {
                            assert(e0.contains(m));
                            if !old(self).evid@.contains(m) {
                                assert(read_evid.contains(m));
                            }
                        }
                    }
                }
            }
            Ok(HeartbeatPlan { match_index, committed: true })
        } else {
            let ghost cmw = Msg::Commit {
                term: term as nat,
                ci: commit_index as nat,
                rec: h.crec,
            };
            let ghost recv = read_evid.union(Set::<Msg>::empty());
            proof {
                assert(abstracts_commit(cmw, term as nat, commit_index as nat));
                lemma_star_mono(i, n, h, h, e0, old(self).evid@.union(recv), ack.union(conf));
                assert(evid_grows(old(self).evid@, self.evid@, recv, ack.union(conf))) by {
                    assert forall|m: Msg| self.evid@.contains(m) implies
                        old(self).evid@.contains(m) || recv.contains(m)
                        || ack.union(conf).contains(m) by {
                        if !ack.contains(m) && !conf.contains(m) {
                            assert(e0.contains(m));
                            if !old(self).evid@.contains(m) {
                                assert(read_evid.contains(m));
                            }
                        }
                    }
                }
            }
            Ok(HeartbeatPlan { match_index, committed: false })
        }
    }

    /// A follower splicing appended entries (`Message::Append` handling at
    /// the receiver's own term): if the base entry matches our log, splice
    /// the entries (the storage-level checks and the skip-scan are verified
    /// in `Log::splice`) and ack the resulting match index; otherwise reject
    /// with a reject index capped at our log end. Refines `t_recv_append`.
    pub fn follower_append(
        &mut self, log: &mut Log, term: Term, base_index: Index, base_term: Term,
        entries: Vec<Entry>,
    ) -> (r: Result<AppendPlan>)
        requires
            old(self).inv(old(log)),
        ensures
            r matches Ok(p) ==> {
                let h = old(self).habs();
                let i = old(self).i();
                &&& final(self).inv(final(log))
                &&& final(self).same_node(old(self))
                &&& final(self).is_follower()
                &&& final(log).term() == old(log).term()
                &&& final(log).vote() == old(log).vote()
                &&& final(log).commit_index() == old(log).commit_index()
                &&& match p {
                    AppendPlan::Reject { reject_index } => {
                        &&& *final(self) == *old(self)
                        &&& *final(log) == *old(log)
                        &&& !old(log).has_spec(base_index, base_term) && base_index != 0
                        &&& reject_index as int == if base_index as int <= old(log).view().len() {
                            base_index as int
                        } else {
                            old(log).view().len() as int + 1
                        }
                    },
                    AppendPlan::Accept { match_index } => {
                        let aentries = entries_view(entries@);
                        let m = Msg::Append {
                            term: term as nat,
                            base: base_index as nat,
                            bterm: base_term as nat,
                            entries: aentries,
                        };
                        let ack = Msg::Ack {
                            v: i,
                            term: term as nat,
                            mi: (base_index + entries@.len()) as nat,
                        };
                        &&& base_index == 0 || old(log).has_spec(base_index, base_term)
                        &&& match_index as nat == base_index + entries@.len()
                        &&& final(log).view() == splice(old(log).view(), base_index as nat, aentries)
                        &&& final(self).habs() == (MHost { log: final(log).view(), ..h })
                        &&& host_refines_star(i, old(self).n_spec(), h, final(self).habs(),
                            old(self).evid().insert(m), Set::empty().insert(ack))
                        &&& evid_grows(old(self).evid(), final(self).evid(),
                            Set::empty().insert(m), Set::empty().insert(ack))
                    },
                }
            },
    {
        match &self.role {
            AbsRole::Follower => {}
            _ => fault(Fault::WrongRole),
        }
        let (cur, _) = log.get_term_vote();
        if term != cur {
            fault(Fault::WrongTerm);
        }
        // Entries must start at base_index + 1.
        if entries.len() > 0 {
            if base_index == u64::MAX || entries[0].index != base_index + 1 {
                fault(Fault::BaseIndexMismatch);
            }
        }

        // If the base entry matches our log, append the entries.
        let base_matches = base_index == 0 || log.has(base_index, base_term)?;
        if !base_matches {
            // Reject the append. If the local log is shorter than the base
            // index, lower the reject index to skip all missing entries.
            let (last_index, _) = log.get_last_index();
            let reject_index = if base_index <= last_index { base_index } else { last_index + 1 };
            return Ok(AppendPlan::Reject { reject_index });
        }

        let m = recv_msg(&MsgSummary::Append { term, base_index, base_term, entries: &entries });
        let ghost h = self.habs@;
        let ghost i = self.rank as int;
        let ghost aentries = entries_view(entries@);
        let ghost h2 = MHost { log: splice(h.log, base_index as nat, aentries), ..h };
        let ghost ackmsg = Msg::Ack { v: i, term: term as nat, mi: (base_index + aentries.len()) as nat };

        // The ack index: the last entry's index, or the base for an empty
        // probe. Provably equal to base_index + entries.len() (contiguity is
        // enforced by the splice).
        let match_index = if entries.len() == 0 {
            base_index
        } else {
            entries[entries.len() - 1].index
        };
        let ghost eseq = entries@;
        let ghost elen = entries@.len();
        log.splice(entries)?;
        proof {
            if elen > 0 {
                assert(match_index as nat == base_index + elen) by {
                    super::log::lemma_contiguous_index(eseq, elen - 1);
                }
            }
            if elen == 0 {
                // An empty batch leaves the log unchanged, as does the
                // model's splice of an empty batch at a valid base.
                assert(splice_is_noop(h.log, base_index as nat, aentries));
                assert(splice(h.log, base_index as nat, aentries) == h.log);
            }
            lemma_lift_recv_append(i, self.n, h, base_index as nat, base_term as nat, aentries);
            lemma_star_of_single(i, self.n, h, h2, Set::empty().insert(Msg::Append {
                term: term as nat,
                base: base_index as nat,
                bterm: base_term as nat,
                entries: aentries,
            }), Set::empty().insert(ackmsg));
            lemma_star_mono(i, self.n, h, h2, Set::empty().insert(Msg::Append {
                term: term as nat,
                base: base_index as nat,
                bterm: base_term as nat,
                entries: aentries,
            }), self.evid@.insert(m@), Set::empty().insert(ackmsg));
        }
        self.habs = Ghost(h2);
        self.evid = Ghost(self.evid@.insert(m@).insert(ackmsg));
        Ok(AppendPlan::Accept { match_index })
    }

    /// A follower confirming the leader's read sequence number
    /// (`Message::Read` handling at the receiver's own term). Returns the
    /// sequence number to respond with. Refines `t_confirm_read` (a zero
    /// sequence number confirms nothing).
    pub fn follower_read(&mut self, log: &Log, term: Term, seq: u64) -> (r: u64)
        requires
            old(self).inv(log),
        ensures
            final(self).inv(log),
            final(self).same_node(old(self)),
            final(self).is_follower(),
            final(self).habs() == old(self).habs(),
            r == seq,
            ({
                let i = old(self).i();
                let recv: Set<Msg> = if seq >= 1 {
                    Set::empty().insert(Msg::Read { term: term as nat, seq: seq as nat })
                } else {
                    Set::empty()
                };
                let sent: Set<Msg> = if seq >= 1 {
                    Set::empty().insert(Msg::ReadConfirm { v: i, term: term as nat, seq: seq as nat })
                } else {
                    Set::empty()
                };
                &&& host_refines_star(i, old(self).n_spec(), old(self).habs(), final(self).habs(),
                    old(self).evid().union(recv), sent)
                &&& evid_grows(old(self).evid(), final(self).evid(), recv, sent)
            }),
    {
        match &self.role {
            AbsRole::Follower => {}
            _ => fault(Fault::WrongRole),
        }
        let (cur, _) = log.get_term_vote();
        if term != cur {
            fault(Fault::WrongTerm);
        }
        let ghost h = self.habs@;
        let ghost i = self.rank as int;
        let ghost n = self.n;
        if seq >= 1 {
            let rm = recv_msg(&MsgSummary::Read { term, seq });
            let ghost conf = Set::empty().insert(Msg::ReadConfirm { v: i, term: term as nat, seq: seq as nat });
            proof {
                lemma_lift_confirm_read(i, n, h, seq as nat);
                lemma_star_of_single(i, n, h, h, Set::empty().insert(rm@), conf);
                lemma_star_mono(i, n, h, h, Set::empty().insert(rm@),
                    self.evid@.union(Set::empty().insert(rm@)), conf);
            }
            self.evid = Ghost(self.evid@.insert(rm@).union(conf));
        } else {
            proof {
                lemma_star_refl(i, n, h, self.evid@.union(Set::<Msg>::empty()));
                assert(self.evid@.union(Set::<Msg>::empty()) =~= self.evid@);
            }
        }
        seq
    }

    // --- Leader message steps ------------------------------------------

    /// A leader handling a heartbeat response: record the ack and read
    /// confirmation evidence, advance the member's read sequence and match
    /// index, and regress its next index if it did not match (the shell then
    /// probes). No model state change on the leader. The returned plan tells
    /// the shell which follow-ups to run.
    pub fn leader_heartbeat_response(
        &mut self, log: &Log, from: NodeID, term: Term, match_index: Index, read_seq: u64,
    ) -> (r: HbRespPlan)
        requires
            old(self).inv(log),
        ensures
            final(self).inv(log),
            final(self).same_node(old(self)),
            final(self).is_leader(),
            final(self).habs() == old(self).habs(),
            ({
                let recv = ack_confirm_msgs(old(self).habs().term, from, *old(self), match_index, read_seq);
                evid_grows(old(self).evid(), final(self).evid(), recv, Set::empty())
            }),
    {
        let (last_index, _) = log.get_last_index();
        if match_index > last_index {
            fault(Fault::FutureMatchIndex);
        }
        let v = self.note_response(log, from, term, match_index, read_seq);
        let own_read_seq = self.read_seq_at(self.rank);
        if read_seq > own_read_seq {
            fault(Fault::FutureReadSequence);
        }
        let progress = match &mut self.role {
            AbsRole::Leader { progress } => progress,
            _ => fault(Fault::WrongRole),
        };
        let p = &mut progress[v as usize];
        // Advance the read sequence.
        let read_advanced = if read_seq > p.read_seq {
            p.read_seq = read_seq;
            true
        } else {
            false
        };
        // If the follower didn't match our last index, an append to it must
        // have failed (or it's catching up). Move next_index back to
        // last_index so the shell probes it.
        if match_index == 0 {
            if last_index < p.next_index && p.next_index > p.match_index + 1 {
                p.next_index = if last_index > p.match_index + 1 { last_index } else { p.match_index + 1 };
            }
        }
        // Advance the match index.
        let advanced = if match_index > p.match_index {
            p.match_index = match_index;
            if p.next_index <= match_index {
                if match_index == u64::MAX {
                    fault(Fault::IndexOverflow);
                }
                p.next_index = match_index + 1;
            }
            true
        } else {
            false
        };
        HbRespPlan { read_advanced, advanced }
    }

    /// A leader recording an append response's ack: advance the member's
    /// match index. Returns whether it advanced (the shell then tries to
    /// commit).
    pub fn leader_append_response(
        &mut self, log: &Log, from: NodeID, term: Term, match_index: Index,
    ) -> (r: bool)
        requires
            old(self).inv(log),
        ensures
            final(self).inv(log),
            final(self).same_node(old(self)),
            final(self).is_leader(),
            final(self).habs() == old(self).habs(),
            ({
                let recv = ack_confirm_msgs(old(self).habs().term, from, *old(self), match_index, 0);
                evid_grows(old(self).evid(), final(self).evid(), recv, Set::empty())
            }),
    {
        let (last_index, _) = log.get_last_index();
        if match_index > last_index {
            fault(Fault::FutureMatchIndex);
        }
        let v = self.note_response(log, from, term, match_index, 0);
        let progress = match &mut self.role {
            AbsRole::Leader { progress } => progress,
            _ => fault(Fault::WrongRole),
        };
        let p = &mut progress[v as usize];
        if match_index > p.match_index {
            p.match_index = match_index;
            if p.next_index <= match_index {
                if match_index == u64::MAX {
                    fault(Fault::IndexOverflow);
                }
                p.next_index = match_index + 1;
            }
            true
        } else {
            false
        }
    }

    /// A leader recording a read response's confirmation: advance the
    /// member's read sequence. Returns whether it advanced (the shell then
    /// tries to serve reads).
    pub fn leader_read_response(&mut self, log: &Log, from: NodeID, term: Term, seq: u64) -> (r: bool)
        requires
            old(self).inv(log),
        ensures
            final(self).inv(log),
            final(self).same_node(old(self)),
            final(self).is_leader(),
            final(self).habs() == old(self).habs(),
            ({
                let recv = ack_confirm_msgs(old(self).habs().term, from, *old(self), 0, seq);
                evid_grows(old(self).evid(), final(self).evid(), recv, Set::empty())
            }),
    {
        let v = self.note_response(log, from, term, 0, seq);
        let progress = match &mut self.role {
            AbsRole::Leader { progress } => progress,
            _ => fault(Fault::WrongRole),
        };
        let p = &mut progress[v as usize];
        if seq > p.read_seq {
            p.read_seq = seq;
            true
        } else {
            false
        }
    }

    /// Records the ack / read-confirmation evidence of a follower response
    /// (heartbeat, append or read response) and returns the sender's rank.
    fn note_response(
        &mut self, log: &Log, from: NodeID, term: Term, match_index: Index, read_seq: u64,
    ) -> (v: u8)
        requires
            old(self).inv(log),
        ensures
            final(self).inv(log),
            final(self).same_node(old(self)),
            final(self).is_leader(),
            final(self).habs() == old(self).habs(),
            (v as nat) < final(self).n_spec() as nat,
            v as int == final(self).member_rank(from),
            v as int != final(self).i(),
            match_index >= 1 ==> final(self).evid().contains(Msg::Ack {
                v: v as int,
                term: old(self).habs().term,
                mi: match_index as nat,
            }),
            read_seq >= 1 ==> final(self).evid().contains(Msg::ReadConfirm {
                v: v as int,
                term: old(self).habs().term,
                seq: read_seq as nat,
            }),
            evid_grows(old(self).evid(), final(self).evid(),
                ack_confirm_msgs(old(self).habs().term, from, *old(self), match_index, read_seq),
                Set::empty()),
    {
        match &self.role {
            AbsRole::Leader { .. } => {}
            _ => fault(Fault::WrongRole),
        }
        let (cur, _) = log.get_term_vote();
        if term != cur {
            fault(Fault::WrongTerm);
        }
        // Responses come only from peers: the leader never messages itself.
        if from == self.me {
            fault(Fault::UnknownNode(from));
        }
        let v = match self.members.rank(from) {
            Some(v) => v,
            None => fault(Fault::UnknownNode(from)),
        };
        proof {
            self.members.lemma_rank(self.me);
            self.members.lemma_rank_distinct(self.me, from);
        }
        if match_index >= 1 {
            let m = recv_msg(&MsgSummary::Ack { v, term, match_index });
            self.evid = Ghost(self.evid@.insert(m@));
        }
        if read_seq >= 1 {
            let m = recv_msg(&MsgSummary::ReadConfirm { v, term, seq: read_seq });
            self.evid = Ghost(self.evid@.insert(m@));
        }
        v
    }

    /// The rank of a member (spec).
    pub closed spec fn member_rank(&self, id: NodeID) -> int {
        self.members.rank_of(id)
    }

    /// A follower rejected an append at `reject_index`: regress its next
    /// index so the shell can probe below it, unless the rejection is stale
    /// (at or below the match index) or we already probe below it. Returns
    /// whether the shell should probe.
    pub fn leader_append_reject(&mut self, log: &Log, from: NodeID, reject_index: Index) -> (r: bool)
        requires
            old(self).inv(log),
        ensures
            final(self).inv(log),
            final(self).same_node(old(self)),
            final(self).is_leader(),
            final(self).habs() == old(self).habs(),
            final(self).evid() == old(self).evid(),
    {
        match &self.role {
            AbsRole::Leader { .. } => {}
            _ => fault(Fault::WrongRole),
        }
        let (last_index, _) = log.get_last_index();
        if reject_index > last_index {
            fault(Fault::FutureRejectIndex);
        }
        if from == self.me {
            fault(Fault::UnknownNode(from));
        }
        let v = match self.members.rank(from) {
            Some(v) => v,
            None => fault(Fault::UnknownNode(from)),
        };
        proof {
            self.members.lemma_rank(self.me);
            self.members.lemma_rank_distinct(self.me, from);
        }
        let progress = match &mut self.role {
            AbsRole::Leader { progress } => progress,
            _ => fault(Fault::WrongRole),
        };
        let p = &mut progress[v as usize];
        // If the rejected base index is at or below the match index, the
        // rejection is stale and can be ignored.
        if reject_index <= p.match_index {
            return false;
        }
        // Probe below the reject index, if we haven't already moved
        // next_index below it.
        if reject_index >= p.next_index || p.next_index <= p.match_index + 1 {
            return false;
        }
        p.next_index = if reject_index > p.match_index + 1 { reject_index } else { p.match_index + 1 };
        true
    }

    /// A leader appending a client command to its log (`Leader::propose`).
    /// Returns the entry's index. Refines `t_propose`.
    pub fn propose(&mut self, log: &mut Log, command: Option<Vec<u8>>) -> (r: Result<Index>)
        requires
            old(self).inv(old(log)),
        ensures
            r matches Ok(index) ==> {
                let h = old(self).habs();
                &&& final(self).inv(final(log))
                &&& final(self).same_node(old(self))
                &&& final(self).is_leader()
                &&& index as nat == h.log.len() + 1
                &&& final(log).view() == old(log).view().push(AEntry {
                    term: h.term,
                    cmd: cmd_view(command),
                })
                &&& final(self).habs() == (MHost { log: final(log).view(), ..h })
                &&& host_refines_star(old(self).i(), old(self).n_spec(), h, final(self).habs(),
                    old(self).evid(), Set::empty())
                &&& final(self).evid() == old(self).evid()
            },
    {
        match &self.role {
            AbsRole::Leader { .. } => {}
            _ => fault(Fault::WrongRole),
        }
        let ghost h = self.habs@;
        let ghost i = self.rank as int;
        let ghost cmd = cmd_view(command);
        let ghost h2 = MHost { log: h.log.push(AEntry { term: h.term, cmd }), ..h };
        proof {
            lemma_lift_propose(i, self.n, h, cmd);
            lemma_star_of_single(i, self.n, h, h2, Set::empty(), Set::empty());
            lemma_star_mono(i, self.n, h, h2, Set::empty(), self.evid@, Set::empty());
        }
        let index = log.append(command)?;
        self.habs = Ghost(h2);
        Ok(index)
    }

    /// A leader assigning the next read sequence number (`ClientRequest::Read`
    /// handling): the shell broadcasts `Message::Read { seq }` for quorum
    /// confirmation. The leader's own confirmation is recorded here. Refines
    /// `t_submit_read`.
    pub fn submit_read(&mut self, log: &Log) -> (r: u64)
        requires
            old(self).inv(log),
        ensures
            final(self).inv(log),
            final(self).same_node(old(self)),
            final(self).is_leader(),
            r as nat == old(self).habs().read_seq + 1,
            final(self).habs() == (MHost { read_seq: r as nat, ..old(self).habs() }),
            ({
                let i = old(self).i();
                let t = old(self).habs().term;
                let sent = Set::empty()
                    .insert(Msg::Read { term: t, seq: r as nat })
                    .insert(Msg::ReadConfirm { v: i, term: t, seq: r as nat });
                &&& host_refines_star(i, old(self).n_spec(), old(self).habs(), final(self).habs(),
                    old(self).evid(), sent)
                &&& evid_grows(old(self).evid(), final(self).evid(), Set::empty(), sent)
            }),
    {
        match &self.role {
            AbsRole::Leader { .. } => {}
            _ => fault(Fault::WrongRole),
        }
        let ghost h = self.habs@;
        let ghost i = self.rank as int;
        let own = self.read_seq_at(self.rank);
        if own == u64::MAX {
            fault(Fault::ReadSequenceOverflow);
        }
        let seq = own + 1;
        let ghost h2 = MHost { read_seq: seq as nat, ..h };
        let ghost sent = Set::empty()
            .insert(Msg::Read { term: h.term, seq: seq as nat })
            .insert(Msg::ReadConfirm { v: i, term: h.term, seq: seq as nat });
        proof {
            lemma_lift_submit_read(i, self.n, h);
            lemma_star_of_single(i, self.n, h, h2, Set::empty(), sent);
            lemma_star_mono(i, self.n, h, h2, Set::empty(), self.evid@, sent);
        }
        let progress = match &mut self.role {
            AbsRole::Leader { progress } => progress,
            _ => fault(Fault::WrongRole),
        };
        let p = &mut progress[self.rank as usize];
        p.read_seq = seq;
        self.habs = Ghost(h2);
        self.evid = Ghost(self.evid@.union(sent));
        seq
    }

    /// The read sequence counter at a rank.
    fn read_seq_at(&self, rank: u8) -> (r: u64)
        requires
            self.is_leader(),
            (rank as int) < self.role->Leader_progress@.len(),
        ensures
            r == self.progress_spec(rank as int).read_seq_spec(),
    {
        let progress = match &self.role {
            AbsRole::Leader { progress } => progress,
            _ => fault(Fault::WrongRole),
        };
        progress[rank as usize].read_seq
    }

    /// A leader heartbeat (`Leader::heartbeat`): returns the heartbeat
    /// message fields. Re-announcing the commit index refines
    /// `t_send_commit` (a zero commit index announces nothing).
    pub fn leader_heartbeat(&mut self, log: &Log) -> (r: HeartbeatMsg)
        requires
            old(self).inv(log),
        ensures
            final(self).inv(log),
            final(self).same_node(old(self)),
            final(self).is_leader(),
            final(self).habs() == old(self).habs(),
            r.last_index as nat == log.view().len(),
            r.commit_index == log.commit_index(),
            r.read_seq as nat == old(self).habs().read_seq,
            ({
                let h = old(self).habs();
                let sent: Set<Msg> = if r.commit_index >= 1 {
                    Set::empty().insert(Msg::Commit {
                        term: h.term,
                        ci: r.commit_index as nat,
                        rec: h.crec,
                    })
                } else {
                    Set::empty()
                };
                &&& host_refines_star(old(self).i(), old(self).n_spec(), h, h, old(self).evid(), sent)
                &&& evid_grows(old(self).evid(), final(self).evid(), Set::empty(), sent)
            }),
    {
        match &self.role {
            AbsRole::Leader { .. } => {}
            _ => fault(Fault::WrongRole),
        }
        let (term, _) = log.get_term_vote();
        let (last_index, lterm) = log.get_last_index();
        let (commit_index, _) = log.get_commit_index();
        // The leader's last entry is always from its own term.
        if lterm != term {
            fault(Fault::LeaderLastTerm);
        }
        let read_seq = self.read_seq_at(self.rank);
        let ghost h = self.habs@;
        let ghost i = self.rank as int;
        if commit_index >= 1 {
            let ghost sent = Set::empty().insert(Msg::Commit {
                term: h.term,
                ci: commit_index as nat,
                rec: h.crec,
            });
            proof {
                lemma_lift_send_commit(i, self.n, h, commit_index as nat);
                lemma_star_of_single(i, self.n, h, h, Set::empty(), sent);
                lemma_star_mono(i, self.n, h, h, Set::empty(), self.evid@, sent);
            }
            self.evid = Ghost(self.evid@.union(sent));
        } else {
            proof {
                lemma_star_refl(i, self.n, h, self.evid@);
            }
        }
        HeartbeatMsg { last_index, commit_index, read_seq }
    }

    /// A leader sending a batch of pending log entries to a member, in the
    /// [next_index, last_index] range, limited by `max_entries`
    /// (`maybe_send_append`).
    ///
    /// If `probe` is true, we're trying to find a log index on the follower
    /// where it matches our log: an empty append with base next_index-1.
    /// The probe is skipped if the follower is up-to-date; if the probe's
    /// base has already been confirmed via match_index, actual entries are
    /// sent instead. Returns None when there is nothing to send.
    ///
    /// The returned entries are verified to be exactly the log's window
    /// above the base, and sending them refines `t_send_append`.
    pub fn leader_send_append(
        &mut self, log: &mut Log, peer: NodeID, probe: bool, max_entries: usize,
    ) -> (r: Result<Option<AppendMsg>>)
        requires
            old(self).inv(old(log)),
        ensures
            r matches Ok(ro) ==> {
                let h = old(self).habs();
                let i = old(self).i();
                &&& final(self).inv(final(log))
                &&& final(self).same_node(old(self))
                &&& final(self).is_leader()
                &&& final(self).habs() == h
                &&& *final(log) == *old(log)
                &&& match ro {
                    None => final(self).evid() == old(self).evid(),
                    Some(msg) => {
                        let b = msg.base_index as nat;
                        let aentries = entries_view(msg.entries@);
                        let m = Msg::Append {
                            term: h.term,
                            base: b,
                            bterm: msg.base_term as nat,
                            entries: aentries,
                        };
                        &&& b + aentries.len() <= h.log.len()
                        &&& aentries == h.log.subrange(b as int, b as int + aentries.len() as int)
                        &&& (b == 0 ==> msg.base_term == 0)
                        &&& (b >= 1 ==> msg.base_term as nat == h.log[b as int - 1].term)
                        &&& forall|j: int| 0 <= j < msg.entries@.len() ==>
                            (#[trigger] msg.entries@[j]).index as nat == b + 1 + j
                        &&& host_refines_star(i, old(self).n_spec(), h, h, old(self).evid(),
                            Set::empty().insert(m))
                        &&& evid_grows(old(self).evid(), final(self).evid(), Set::empty(),
                            Set::empty().insert(m))
                    },
                }
            },
    {
        match &self.role {
            AbsRole::Leader { .. } => {}
            _ => fault(Fault::WrongRole),
        }
        let (term, _) = log.get_term_vote();
        let (last_index, _) = log.get_last_index();
        let v = match self.members.rank(peer) {
            Some(v) => v,
            None => fault(Fault::UnknownNode(peer)),
        };
        let (next_index, match_index) = {
            let progress = match &self.role {
                AbsRole::Leader { progress } => progress,
                _ => fault(Fault::WrongRole),
            };
            (progress[v as usize].next_index, progress[v as usize].match_index)
        };

        // If the peer is caught up, there's no point sending an append.
        if match_index == last_index {
            return Ok(None);
        }
        // If a probe was requested, but the base_index has already been
        // confirmed via match_index, there is no point in probing. Just send
        // the entries instead.
        let probe = probe && next_index > match_index + 1;
        // If there are no pending entries, and this is not a probe, there's
        // nothing more to send until we get a response from the follower.
        if next_index > last_index && !probe {
            return Ok(None);
        }

        // Fetch the base and entries.
        let (base_index, base_term) = if next_index == 1 {
            (0, 0) // first entry, there is no base
        } else {
            match log.get(next_index - 1)? {
                Some(e) => (e.index, e.term),
                None => fault(Fault::MissingBaseEntry),
            }
        };
        let entries: Vec<Entry> = if probe {
            Vec::new()
        } else {
            log.read_range(next_index, max_entries)?
        };

        // Optimistically assume the entries will be accepted by the
        // follower, and bump next_index to avoid resending them until a
        // response.
        if entries.len() > 0 {
            let last = entries[entries.len() - 1].index;
            if last == u64::MAX {
                fault(Fault::IndexOverflow);
            }
            let progress = match &mut self.role {
                AbsRole::Leader { progress } => progress,
                _ => fault(Fault::WrongRole),
            };
            let p = &mut progress[v as usize];
            p.next_index = last + 1;
        }

        let ghost h = self.habs@;
        let ghost i = self.rank as int;
        let ghost b = base_index as nat;
        let ghost aentries = entries_view(entries@);
        let ghost m = Msg::Append { term: h.term, base: b, bterm: base_term as nat, entries: aentries };
        proof {
            assert(aentries =~= h.log.subrange(b as int, b as int + aentries.len() as int));
            lemma_lift_send_append(i, self.n, h, b, b + aentries.len());
            assert(h.log.subrange(b as int, (b + aentries.len()) as int) == aentries);
            lemma_star_of_single(i, self.n, h, h, Set::empty(), Set::empty().insert(m));
            lemma_star_mono(i, self.n, h, h, Set::empty(), self.evid@, Set::empty().insert(m));
        }
        self.evid = Ghost(self.evid@.insert(m));
        Ok(Some(AppendMsg { base_index, base_term, entries }))
    }

    /// A leader advancing the commit index (`maybe_commit_and_apply`):
    /// computes the quorum commit index — the highest index that a strict
    /// majority of members (the leader's own last index included) has
    /// matched — and commits it if it advances the current commit index and
    /// the entry there is from the leader's own term (section 5.4.2). Every
    /// counted match index is backed by ack evidence (`inv`), so the commit
    /// refines `t_send_ack` (the leader's own ack) + `t_leader_commit`.
    /// Returns the new commit index, or None if nothing advanced.
    pub fn leader_try_commit(&mut self, log: &mut Log) -> (r: Result<Option<Index>>)
        requires
            old(self).inv(old(log)),
        ensures
            r matches Ok(ro) ==> {
                let h = old(self).habs();
                let i = old(self).i();
                &&& final(self).inv(final(log))
                &&& final(self).same_node(old(self))
                &&& final(self).is_leader()
                &&& match ro {
                    None => *final(self) == *old(self) && *final(log) == *old(log),
                    Some(ci) => {
                        &&& ci > old(log).commit_index()
                        &&& ci as nat <= h.log.len()
                        &&& h.log[ci as int - 1].term == h.term
                        &&& final(log).view() == old(log).view()
                        &&& final(log).term() == old(log).term()
                        &&& final(log).commit_index() == ci
                        &&& final(self).habs().commit == ci as nat
                        &&& final(self).habs() == (MHost {
                            commit: ci as nat,
                            crec: final(self).habs().crec,
                            ..h
                        })
                        &&& final(self).habs().crec.term == h.term
                        &&& final(self).habs().crec.ci == ci as nat
                        &&& exists|sent: Set<Msg>| {
                            &&& #[trigger] sent.contains(Msg::Commit {
                                term: h.term,
                                ci: ci as nat,
                                rec: final(self).habs().crec,
                            })
                            &&& host_refines_star(i, old(self).n_spec(), h, final(self).habs(),
                                old(self).evid(), sent)
                            &&& evid_grows(old(self).evid(), final(self).evid(), Set::empty(), sent)
                        }
                    },
                }
            },
    {
        match &self.role {
            AbsRole::Leader { .. } => {}
            _ => fault(Fault::WrongRole),
        }
        let (term, _) = log.get_term_vote();
        let (last_index, _) = log.get_last_index();
        let (old_commit, _) = log.get_commit_index();
        let n = self.n as usize;
        let rank = self.rank;

        // The quorum commit index: the highest member value (match indexes,
        // with the leader's own last index at its rank) that a strict
        // majority of members reaches. Equals the quorum_size-th highest
        // member value.
        let mut ci: Index = 0;
        let mut c: usize = 0;
        while c < n
            invariant
                c <= n,
                self.is_leader(),
                n == self.n as usize,
                rank == self.rank,
                self.role->Leader_progress@.len() == n,
            decreases n - c,
        {
            let val = self.member_match(c, last_index);
            if val > ci {
                let cnt = self.count_matching(val, last_index);
                if 2 * cnt > n {
                    ci = val;
                }
            }
            c += 1;
        }

        // If the commit index doesn't advance, do nothing. The quorum value
        // may regress e.g. following a leader change where followers are
        // initialized with match index 0; that is not an error.
        if ci <= old_commit {
            return Ok(None);
        }

        // We can only safely commit an entry from our own term (section
        // 5.4.2).
        let entry = match log.get(ci)? {
            Some(entry) => entry,
            None => fault(Fault::CommitIndexMissing(ci)),
        };
        if entry.term != term {
            return Ok(None);
        }

        // Collect the quorum: every member whose match index reaches ci,
        // with its ack evidence (from `inv`; the leader's own ack of its
        // last index is sent here, refining t_send_ack).
        let ghost h = self.habs@;
        let ghost i = self.rank as int;
        let ghost selfack = Msg::Ack { v: i, term: h.term, mi: last_index as nat };
        let ghost e0 = self.evid@;
        proof {
            lemma_star_refl(i, self.n, h, e0);
            lemma_lift_send_ack(i, self.n, h, last_index as nat);
            lemma_star_extend(i, self.n, h, h, h, e0, Set::empty(), Set::empty(),
                Set::empty().insert(selfack));
            assert(Set::empty().union(Set::empty().insert(selfack)) =~= Set::empty().insert(selfack));
        }
        let ghost evid_acks = e0.insert(selfack);

        let mut count: usize = 0;
        let mut k: usize = 0;
        let ghost mut qm: Map<int, nat> = Map::empty();
        let ghost mut qids: Seq<int> = Seq::empty();
        while k < n
            invariant
                k <= n,
                count <= k,
                count == qids.len(),
                qids.no_duplicates(),
                qm.dom() == qids.to_set(),
                self.is_leader(),
                n == self.n as usize,
                rank == self.rank,
                rank < self.n,
                self.role->Leader_progress@.len() == n,
                ci >= 1,
                h == self.habs@,
                i == self.rank as int,
                evid_acks == self.evid@.insert(selfack),
                selfack == (Msg::Ack { v: i, term: h.term, mi: last_index as nat }),
                self.inv(log),
                last_index as nat == log.view().len(),
                forall|j: int| 0 <= j < qids.len() ==> 0 <= #[trigger] qids[j] < k,
                forall|v: int| #[trigger] qm.dom().contains(v) ==>
                    qm[v] >= ci as nat && evid_acks.contains(Msg::Ack { v, term: h.term, mi: qm[v] })
                        && 0 <= v < n,
            decreases n - k,
        {
            let val = self.member_match(k, last_index);
            if val >= ci {
                proof {
                    if qids.to_set().contains(k as int) {
                        let j = choose|j: int| 0 <= j < qids.len() && qids[j] == k as int;
                        assert(false);
                    }
                    let old_qids = qids;
                    qids = qids.push(k as int);
                    qm = qm.insert(k as int, val as nat);
                    assert(qm.dom() =~= qids.to_set()) by {
                        assert forall|x: int| qids.to_set().contains(x) implies
                            old_qids.to_set().contains(x) || x == k as int by {
                            let j = choose|j: int| 0 <= j < qids.len() && qids[j] == x;
                            if j < qids.len() - 1 {
                                assert(old_qids[j] == x);
                            }
                        }
                        assert forall|x: int| old_qids.to_set().contains(x) implies
                            qids.to_set().contains(x) by {
                            let j = choose|j: int| 0 <= j < old_qids.len() && old_qids[j] == x;
                            assert(qids[j] == x);
                        }
                        assert(qids.to_set().contains(k as int)) by {
                            assert(qids[qids.len() - 1] == k as int);
                        }
                    }
                    // The evidence: the leader's own ack for its rank, a
                    // member's recorded ack (inv) otherwise.
                    if k as int == i {
                        assert(evid_acks.contains(Msg::Ack { v: i, term: h.term, mi: val as nat }));
                    } else {
                        assert(self.evid@.contains(Msg::Ack { v: k as int, term: h.term, mi: val as nat }));
                    }
                }
                count += 1;
            }
            k += 1;
        }
        // Quorum: strict majority of the n-member cluster.
        proof {
            qids.unique_seq_to_set();
            assert(qm.dom().len() == count);
            assert forall|v: int| qm.dom().contains(v) implies node_ids(self.n as nat).contains(v) by {
                vstd::set_lib::lemma_int_range(0, self.n as int);
                assert(node_ids(self.n as nat) == vstd::set_lib::set_int_range(0, self.n as int));
            }
        }
        if 2 * count <= n {
            // Unreachable: ci was chosen with a strict majority reaching it.
            return Ok(None);
        }
        let ghost rec = CommitRec { term: h.term, ci: ci as nat, q: qm };
        let ghost h2 = MHost { commit: ci as nat, crec: rec, ..h };
        let ghost commitmsg = Msg::Commit { term: h.term, ci: ci as nat, rec };
        proof {
            assert(is_quorum(self.n as nat, qm.dom()));
            lemma_lift_leader_commit(i, self.n, h, ci as nat, qm, evid_acks);
            assert(evid_acks.subset_of(e0.union(Set::empty().insert(selfack))));
            lemma_star_extend(i, self.n, h, h, h2, e0, Set::empty().insert(selfack),
                evid_acks, Set::empty().insert(commitmsg));
        }
        log.commit(ci)?;
        self.habs = Ghost(h2);
        self.evid = Ghost(self.evid@.insert(selfack).insert(commitmsg));
        proof {
            let sent = Set::empty().insert(selfack).insert(commitmsg);
            assert(Set::empty().insert(selfack).union(Set::empty().insert(commitmsg)) =~= sent);
            assert(sent.contains(commitmsg));
        }
        Ok(Some(ci))
    }

    /// A member's match value for the commit quorum: its match index, or the
    /// leader's own last index at the leader's rank.
    fn member_match(&self, k: usize, last_index: Index) -> (r: Index)
        requires
            self.is_leader(),
            (k as int) < self.role->Leader_progress@.len(),
        ensures
            r == member_val(*self, k as int, last_index),
    {
        if k == self.rank as usize {
            last_index
        } else {
            let progress = match &self.role {
                AbsRole::Leader { progress } => progress,
                _ => fault(Fault::WrongRole),
            };
            progress[k].match_index
        }
    }

    /// Counts the members whose match value reaches `bound`.
    fn count_matching(&self, bound: Index, last_index: Index) -> (r: usize)
        requires
            self.is_leader(),
            self.role->Leader_progress@.len() == self.n_spec() as nat,
            self.n_spec() <= 255,
        ensures
            r <= self.n_spec() as nat,
    {
        let n = self.n as usize;
        let mut count: usize = 0;
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                count <= k,
                self.is_leader(),
                n == self.n as usize,
                self.role->Leader_progress@.len() == n,
            decreases n - k,
        {
            if self.member_match(k, last_index) >= bound {
                count += 1;
            }
            k += 1;
        }
        count
    }

    /// The linearizable-read gate (`maybe_read`): a read with sequence
    /// number `seq` may be served once (a) the leader's committed tail is
    /// from its own term, and (b) a strict majority of members (self
    /// included) have confirmed a read sequence number at or past `seq` —
    /// each confirmation backed by evidence (`inv`).
    ///
    /// When this returns true, the safety model's `thm_read_linearizable`
    /// applies (the ensures below is its conclusion): in every
    /// invariant-satisfying cluster state consistent with this node's view
    /// where this read was submitted, every write committed anywhere in the
    /// cluster at submission time is contained in this leader's committed
    /// (applied) prefix — the read is not stale.
    pub fn leader_can_serve(&self, log: &Log, seq: u64) -> (r: bool)
        requires
            self.inv(log),
        ensures
            r ==> forall|s: GState, rr: ReadRec|
                #[trigger] binds(s, self.i(), self.n_spec(), self.habs(), self.evid()) && inv(s)
                && #[trigger] s.reads.contains(rr) && rr.term == self.habs().term
                && rr.seq == seq as nat ==>
                forall|rec: CommitRec| #[trigger] rr.born.contains(rec) ==> {
                    &&& rec.term <= self.habs().term
                    &&& rec.ci <= self.habs().commit
                    &&& prefix_eq(self.habs().log, s.leader_log[rec.term], rec.ci)
                },
    {
        match &self.role {
            AbsRole::Leader { .. } => {}
            _ => fault(Fault::WrongRole),
        }
        let (term, _) = log.get_term_vote();
        let (commit_index, commit_term) = log.get_commit_index();
        // It's only safe to read if we've committed an entry from our own
        // term (the leader appends an entry when elected); otherwise a prior
        // leader may have committed entries we haven't applied.
        if commit_index == 0 || commit_term != term {
            return false;
        }
        if seq == 0 {
            return false;
        }

        // Count members that confirmed at or past seq, collecting the
        // quorum with its confirmation evidence.
        let n = self.n as usize;
        let ghost h = self.habs@;
        let ghost i = self.rank as int;
        let mut count: usize = 0;
        let mut k: usize = 0;
        let ghost mut conf: Set<int> = Set::empty();
        let ghost mut cids: Seq<int> = Seq::empty();
        while k < n
            invariant
                k <= n,
                count <= k,
                count == cids.len(),
                cids.no_duplicates(),
                conf == cids.to_set(),
                seq >= 1,
                self.is_leader(),
                n == self.n as usize,
                self.role->Leader_progress@.len() == n,
                h == self.habs@,
                self.inv(log),
                forall|j: int| 0 <= j < cids.len() ==> 0 <= #[trigger] cids[j] < k,
                forall|v: int| #[trigger] conf.contains(v) ==> {
                    &&& 0 <= v < n
                    &&& exists|sq2: nat| sq2 >= seq as nat
                        && #[trigger] self.evid@.contains(Msg::ReadConfirm { v, term: h.term, seq: sq2 })
                },
            decreases n - k,
        {
            let sq = self.read_seq_at(k as u8);
            if sq >= seq {
                proof {
                    if cids.to_set().contains(k as int) {
                        let j = choose|j: int| 0 <= j < cids.len() && cids[j] == k as int;
                        assert(false);
                    }
                    let old_cids = cids;
                    cids = cids.push(k as int);
                    conf = conf.insert(k as int);
                    assert(conf =~= cids.to_set()) by {
                        assert forall|x: int| cids.to_set().contains(x) implies
                            old_cids.to_set().contains(x) || x == k as int by {
                            let j = choose|j: int| 0 <= j < cids.len() && cids[j] == x;
                            if j < cids.len() - 1 {
                                assert(old_cids[j] == x);
                            }
                        }
                        assert forall|x: int| old_cids.to_set().contains(x) implies
                            cids.to_set().contains(x) by {
                            let j = choose|j: int| 0 <= j < old_cids.len() && old_cids[j] == x;
                            assert(cids[j] == x);
                        }
                        assert(cids.to_set().contains(k as int)) by {
                            assert(cids[cids.len() - 1] == k as int);
                        }
                    }
                    assert(exists|sq2: nat| sq2 >= seq as nat
                        && #[trigger] self.evid@.contains(Msg::ReadConfirm { v: k as int, term: h.term, seq: sq2 })) by {
                        assert(self.evid@.contains(Msg::ReadConfirm { v: k as int, term: h.term, seq: sq as nat }));
                    }
                }
                count += 1;
            }
            k += 1;
        }
        proof {
            cids.unique_seq_to_set();
            assert(conf.len() == count);
            assert forall|v: int| conf.contains(v) implies node_ids(self.n as nat).contains(v) by {
                vstd::set_lib::lemma_int_range(0, self.n as int);
                assert(node_ids(self.n as nat) == vstd::set_lib::set_int_range(0, self.n as int));
            }
            vstd::set_lib::lemma_len_subset(conf, node_ids(self.n as nat));
            vstd::set_lib::lemma_int_range(0, self.n as int);
            assert(node_ids(self.n as nat) == vstd::set_lib::set_int_range(0, self.n as int));
            assert(count <= n);
        }
        if 2 * count <= n {
            return false;
        }
        proof {
            assert(is_quorum(self.n as nat, conf));
            assert forall|s: GState, rr: ReadRec|
                #[trigger] binds(s, i, self.n, h, self.evid@) && inv(s)
                && #[trigger] s.reads.contains(rr) && rr.term == h.term && rr.seq == seq as nat implies
                forall|rec: CommitRec| #[trigger] rr.born.contains(rec) ==> {
                    &&& rec.term <= h.term
                    &&& rec.ci <= h.commit
                    &&& prefix_eq(h.log, s.leader_log[rec.term], rec.ci)
                } by {
                assert forall|z: int| #[trigger] conf.contains(z) implies
                    exists|sq2: nat| sq2 >= rr.seq
                        && #[trigger] s.net.contains(Msg::ReadConfirm { v: z, term: rr.term, seq: sq2 }) by {
                    let sq2 = choose|sq2: nat| sq2 >= seq as nat
                        && #[trigger] self.evid@.contains(Msg::ReadConfirm { v: z, term: h.term, seq: sq2 });
                    assert(s.net.contains(Msg::ReadConfirm { v: z, term: rr.term, seq: sq2 }));
                }
                assert(h.commit >= 1 && h.log[h.commit - 1].term == h.term) by {
                    assert(log.commit_index() >= 1);
                }
                thm_read_linearizable(s, i, rr, conf);
            }
        }
        true
    }

    // --- Unverified accessors for the shell's output paths --------------

    /// A member's (match_index, next_index), for status reporting (None for
    /// a non-member or when not leader).
    pub fn progress_of(&self, id: NodeID) -> Option<(Index, Index)> {
        let progress = match &self.role {
            AbsRole::Leader { progress } => progress,
            _ => return None,
        };
        let mut k: usize = 0;
        while k < self.members.ids.len()
            invariant
                k <= self.members.ids_spec().len(),
            decreases self.members.ids_spec().len() - k,
        {
            if self.members.ids[k] == id {
                if k < progress.len() {
                    return Some((progress[k].match_index, progress[k].next_index));
                }
                return None;
            }
            k += 1;
        }
        None
    }

    /// A member's match index, for status reporting.
    pub fn match_index(&self, id: NodeID) -> Option<Index> {
        match self.progress_of(id) {
            Some((mi, _)) => Some(mi),
            None => None,
        }
    }

    /// A member's next index (None for a non-member or when not leader).
    pub fn next_index(&self, id: NodeID) -> Option<Index> {
        match self.progress_of(id) {
            Some((_, next)) => Some(next),
            None => None,
        }
    }
}

/// A member's match value for the commit quorum (spec): its match index, or
/// the leader's own last index at the leader's rank.
pub open spec fn member_val(a: Abs, k: int, last_index: Index) -> Index {
    if k == a.i() {
        last_index
    } else {
        a.progress_spec(k).match_index_spec()
    }
}

/// The abstract counterparts a follower response can carry: an ack for a
/// nonzero match index and a read confirmation for a nonzero read sequence.
pub open spec fn ack_confirm_msgs(term: nat, from: NodeID, a: Abs, match_index: Index, read_seq: u64) -> Set<Msg> {
    let v = a.member_rank(from);
    (if match_index >= 1 {
        Set::empty().insert(Msg::Ack { v, term, mi: match_index as nat })
    } else {
        Set::empty()
    }).union(if read_seq >= 1 {
        Set::empty().insert(Msg::ReadConfirm { v, term, seq: read_seq as nat })
    } else {
        Set::empty()
    })
}

// ---------------------------------------------------------------------------
// Plans returned to the shell
// ---------------------------------------------------------------------------

/// The Campaign message to broadcast after `Abs::campaign`.
pub struct CampaignPlan {
    /// The new (campaigned) term.
    pub term: Term,
    /// Our last log index, sent in the Campaign message.
    pub last_index: Index,
    /// Our last log term, sent in the Campaign message.
    pub last_term: Term,
}

/// The follower's response plan for a heartbeat.
pub struct HeartbeatPlan {
    /// The heartbeat's last_index if our log matched it, else 0. Sent back
    /// in the HeartbeatResponse.
    pub match_index: Index,
    /// Whether the commit index advanced (the shell then applies).
    pub committed: bool,
}

/// The follower's response plan for an append.
pub enum AppendPlan {
    /// The entries were spliced; respond with this match index.
    Accept { match_index: Index },
    /// The base did not match; respond rejecting this index.
    Reject { reject_index: Index },
}

/// The leader's follow-ups after a heartbeat response.
pub struct HbRespPlan {
    /// The member's read sequence advanced (the shell tries to serve reads).
    pub read_advanced: bool,
    /// The member's match index advanced (the shell tries to commit).
    pub advanced: bool,
}

/// The heartbeat message fields (`Abs::leader_heartbeat`).
pub struct HeartbeatMsg {
    pub last_index: Index,
    pub commit_index: Index,
    pub read_seq: u64,
}

/// An Append message to send (`Abs::leader_send_append`).
pub struct AppendMsg {
    pub base_index: Index,
    pub base_term: Term,
    pub entries: Vec<Entry>,
}

} // verus!
