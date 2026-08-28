//! Node-local refinement of `raft::node` against the `raft::safety` model:
//! verified *step cores* proving that each step function's decision logic and
//! state change implement a model transition.
//!
//! # Architecture (verified core / trusted shell)
//!
//! The step functions in `node.rs` are restructured to route every
//! safety-relevant decision and state-change *plan* through the verified core
//! functions in this module (`core_*`). Each core takes the node's concrete
//! state summary plus its ghost abstract state (an `MHost` from the safety
//! model), and returns the plan together with the ghost post-state. Its
//! `ensures` proves `host_refines`: **in any cluster whose global state is
//! consistent with the node's local view, performing this step is a
//! transition of the safety model** — the model whose every reachable state
//! satisfies election safety, log matching, leader completeness, and state
//! machine safety.
//!
//! `node.rs` remains the trusted shell: it performs I/O, owns the collections
//! (`Log`, `Progress`, vote sets), calls the cores, and mechanically executes
//! their plans. The refinement guarantee is conditional on the explicitly
//! trusted assumptions below.
//!
//! # Trusted assumptions
//!
//! Everything marked `#[verifier::external_body]` in the TRUSTED section, plus
//! the shell discipline, is trusted rather than proven:
//!
//! 1. **Network non-forgery**: a received message was really sent by its
//!    sender, i.e. its abstract counterpart is in the ghost message history
//!    (`binds` requires `evid ⊆ s.net`). Ghost payloads behind concrete
//!    message summaries (the candidate log behind a Campaign's
//!    last_index/last_term, the commit record behind a heartbeat's
//!    commit_index) are recovered by the `recv_*` axioms.
//! 2. **Storage integrity**: the ghost log view tracks the entries actually
//!    in `Log` — `Log::has`/`get` answers agree with the view, and
//!    `Log::splice`/`append` transform the log as the model's `splice`/push
//!    do (the in-memory transition logic of splice is itself verified in
//!    `raft::log`).
//! 3. **Shell discipline**: `node.rs` calls the cores with truthful concrete
//!    summaries (they equal the ghost state's fields — each core's
//!    `requires` documents the obligation), threads the returned ghost state,
//!    and performs exactly the writes and sends in the plan. Preconditions of
//!    calls from unverified code are not machine-checked; each call site is
//!    written so the correspondence is locally auditable.
//! 4. **Cluster configuration**: all nodes agree on the member set (already a
//!    documented requirement of `RawNode::peers`).
//!
//! Under those assumptions, every safety-relevant step of a node is a
//! transition of the verified model, so the model's safety theorems carry
//! over to the implementation's reachable states.

// The verified cores take flat concrete-summary + ghost argument lists; the
// resulting shapes trip several style lints that don't fit this API.
#![allow(
    clippy::too_many_arguments,
    clippy::collapsible_if,
    clippy::ptr_arg,
    clippy::assign_op_pattern
)]

use vstd::prelude::*;

#[allow(unused_imports)] // several are referenced only from ghost code
use super::safety::{AEntry, CommitRec, GState, MHost, MRole, Msg, ReadRec, TStep};
// Spec/proof items only exist under the Verus toolchain (a normal build
// erases them), so their imports are gated the same way.
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::safety::{
    inv, is_quorum, last_term, next, next_step, node_ids, prefix_eq, splice, t_become_leader,
    t_bump_term, t_campaign, t_collect_vote, t_confirm_read, t_grant, t_leader_commit, t_propose,
    t_recv_append, t_recv_commit, t_restart, t_send_ack, t_send_append, t_send_commit, t_step_down,
    t_submit_read, thm_read_linearizable, up_to_date,
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

/// The step from `hpre` to `hpost` emitting `sent` refines the model: from
/// every consistent global state there is a model transition that performs
/// exactly this host change and message emission.
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

/// The view of a concrete vote option.
pub open spec fn vote_view(v: Option<u8>) -> Option<int> {
    match v {
        Some(id) => Some(id as int),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// TRUSTED: ghost recovery at the I/O boundary
// ---------------------------------------------------------------------------

/// TRUSTED (network non-forgery): the ghost candidate log behind a received
/// Campaign message's (last_index, last_term) summary. Sound because peers
/// only campaign through their own verified core, which puts a Campaign
/// message with their true log view into the history.
#[verifier::external_body]
pub fn recv_campaign_view(last_index: u64, lterm: u64) -> (clog: Ghost<Seq<AEntry>>)
    ensures
        clog@.len() == last_index as nat,
        last_term(clog@) == lterm as nat,
{
    Ghost::assume_new()
}

/// TRUSTED (network non-forgery): the ghost voter log behind a received
/// CampaignResponse. (No summary to pin: the model only needs some log.)
#[verifier::external_body]
pub fn recv_vote_view() -> (vlog: Ghost<Seq<AEntry>>)
{
    Ghost::assume_new()
}

/// TRUSTED (network non-forgery): the abstract entries of a received Append
/// message.
#[verifier::external_body]
pub fn recv_append_view(entries_len: usize) -> (aentries: Ghost<Seq<AEntry>>)
    ensures
        aentries@.len() == entries_len as nat,
{
    Ghost::assume_new()
}

/// TRUSTED (network non-forgery): the ghost commit record behind a received
/// heartbeat's commit_index.
#[verifier::external_body]
pub fn recv_commit_evidence() -> (rec: Ghost<CommitRec>)
{
    Ghost::assume_new()
}

/// TRUSTED (storage integrity): the abstract state of this node recovered
/// from its durable log at startup. The summaries reported by `Log` pin the
/// view's shape; its contents are whatever the disk holds.
#[verifier::external_body]
pub fn recover_abs(term: u64, vote: Option<u8>, last_index: u64, lterm: u64, commit: u64) -> (h: Ghost<MHost>)
    ensures
        h@.term == term as nat,
        h@.vote == vote_view(vote),
        h@.role is Follower,
        h@.log.len() == last_index as nat,
        last_term(h@.log) == lterm as nat,
        h@.commit == commit as nat,
        h@.votes =~= Set::<int>::empty(),
        h@.read_seq == 0,
{
    Ghost::assume_new()
}

// ---------------------------------------------------------------------------
// Ghost plumbing helpers for the (unverified) shell
// ---------------------------------------------------------------------------

/// An empty evidence set, for node startup.
pub fn empty_evidence() -> (r: Ghost<Set<Msg>>)
    ensures
        r@ == Set::<Msg>::empty(),
{
    Ghost(Set::empty())
}

/// Record a received (or self-sent) ack: `AppendResponse`/`HeartbeatResponse`
/// with a nonzero match index abstracts to an Ack in the history (trusted
/// assumption 1; for the leader's own last index, its own emission).
pub fn note_ack(Ghost(evid): Ghost<Set<Msg>>, from: u8, term: u64, mi: u64) -> (r: Ghost<Set<Msg>>)
    ensures
        r@ == evid.insert(Msg::Ack { v: from as int, term: term as nat, mi: mi as nat }),
{
    Ghost(evid.insert(Msg::Ack { v: from as int, term: term as nat, mi: mi as nat }))
}

/// Record a received (or self-sent) read confirmation
/// (`ReadResponse`/`HeartbeatResponse` read_seq).
pub fn note_read_confirm(Ghost(evid): Ghost<Set<Msg>>, from: u8, term: u64, sq: u64) -> (r: Ghost<Set<Msg>>)
    ensures
        r@ == evid.insert(Msg::ReadConfirm { v: from as int, term: term as nat, seq: sq as nat }),
{
    Ghost(evid.insert(Msg::ReadConfirm { v: from as int, term: term as nat, seq: sq as nat }))
}

/// The ghost view of a command payload.
pub fn cmd_ghost(c: &Option<Vec<u8>>) -> (r: Ghost<Option<Seq<u8>>>)
    ensures
        r@ == (match c {
            Some(v) => Some(v@),
            None => None::<Seq<u8>>,
        }),
{
    match c {
        Some(v) => Ghost(Some(v@)),
        None => Ghost(None),
    }
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

proof fn lemma_lift_restart(i: int, n: u8, hpre: MHost)
    ensures
        host_refines(i, n, hpre,
            MHost { role: MRole::Follower, votes: Set::empty(), vote_logs: Map::empty(), read_seq: 0, ..hpre },
            Set::empty(), Set::empty()),
{
    let hpost = MHost { role: MRole::Follower, votes: Set::empty(), vote_logs: Map::empty(), read_seq: 0, ..hpre };
    assert forall|s: GState| #[trigger] binds(s, i, n, hpre, Set::empty()) implies exists|s2: GState| {
        &&& #[trigger] next(s, s2)
        &&& s2.n == s.n
        &&& s2.hosts == s.hosts.update(i, hpost)
        &&& s2.net == s.net.union(Set::empty())
    } by {
        let s2 = GState { hosts: s.hosts.update(i, hpost), ..s };
        assert(t_restart(s, s2, i));
        assert(next_step(s, s2, TStep::Restart { i }));
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

// ---------------------------------------------------------------------------
// Verified step cores
// ---------------------------------------------------------------------------

/// Discovering a higher term: become a leaderless follower in it, clearing
/// the vote (`into_follower(term, None)` on any higher-term message; the
/// shell then re-steps the message at the equal term). Refines `t_bump_term`.
pub fn core_bump_term(Ghost(h): Ghost<MHost>, i: u8, n: u8, term: u64, msg_term: u64) -> (r: Ghost<MHost>)
    requires
        h.term == term as nat,
        msg_term > term,
    ensures
        r@ == (MHost { term: msg_term as nat, vote: None, role: MRole::Follower, ..h }),
        host_refines(i as int, n, h, r@, Set::empty(), Set::empty()),
{
    proof {
        lemma_lift_bump(i as int, n, h, msg_term as nat);
    }
    Ghost(MHost { term: msg_term as nat, vote: None, role: MRole::Follower, ..h })
}

/// A candidate stepping down to follower in its own term (on discovering the
/// election's winner). Refines `t_step_down`.
pub fn core_step_down(Ghost(h): Ghost<MHost>, i: u8, n: u8) -> (r: Ghost<MHost>)
    requires
        h.role is Candidate,
    ensures
        r@ == (MHost { role: MRole::Follower, ..h }),
        host_refines(i as int, n, h, r@, Set::empty(), Set::empty()),
{
    proof {
        lemma_lift_step_down(i as int, n, h);
    }
    Ghost(MHost { role: MRole::Follower, ..h })
}

/// A crash-restart: durable state survives, volatile role state resets.
/// Refines `t_restart`.
pub fn core_restart(Ghost(h): Ghost<MHost>, i: u8, n: u8) -> (r: Ghost<MHost>)
    ensures
        r@ == (MHost { role: MRole::Follower, votes: Set::empty(), vote_logs: Map::empty(), read_seq: 0, ..h }),
        host_refines(i as int, n, h, r@, Set::empty(), Set::empty()),
{
    proof {
        lemma_lift_restart(i as int, n, h);
    }
    Ghost(MHost { role: MRole::Follower, votes: Set::empty(), vote_logs: Map::empty(), read_seq: 0, ..h })
}

/// Campaigning: bump the term, vote for self, solicit votes
/// (`RawNode::<Candidate>::campaign`). Returns the new term; the shell writes
/// it with `set_term_vote(term, Some(self))` and broadcasts Campaign. Refines
/// `t_campaign`.
pub fn core_campaign(Ghost(h): Ghost<MHost>, i: u8, n: u8, term: u64) -> (r: (u64, Ghost<MHost>))
    requires
        h.term == term as nat,
        !(h.role is Leader),
        term < u64::MAX,
    ensures
        r.0 == term + 1,
        r.1@ == (MHost {
            term: (term + 1) as nat,
            vote: Some(i as int),
            role: MRole::Candidate,
            votes: Set::empty().insert(i as int),
            vote_logs: Map::empty().insert(i as int, h.log),
            ..h
        }),
        host_refines(i as int, n, h, r.1@, Set::empty(),
            Set::empty()
                .insert(Msg::Campaign { c: i as int, term: (term + 1) as nat, clog: h.log })
                .insert(Msg::Vote { v: i as int, c: i as int, term: (term + 1) as nat, vlog: h.log })),
{
    proof {
        lemma_lift_campaign(i as int, n, h);
    }
    (term + 1, Ghost(MHost {
        term: (term + 1) as nat,
        vote: Some(i as int),
        role: MRole::Candidate,
        votes: Set::empty().insert(i as int),
        vote_logs: Map::empty().insert(i as int, h.log),
        ..h
    }))
}

/// Deciding a vote request at the receiver's own term (`Message::Campaign`
/// handling): grant only if not already committed to another candidate this
/// term, and only if the candidate's log is at least as up-to-date (section
/// 5.4.1) — judged, as in the implementation, on the (last_index, last_term)
/// summaries. Returns the ghost post-state on grant; `None` rejects with no
/// state change. Refines `t_grant`.
pub fn core_grant(
    Ghost(h): Ghost<MHost>, i: u8, n: u8,
    term: u64, vote: Option<u8>,
    last_index: u64, lterm: u64,
    cand: u8, cand_last_index: u64, cand_last_term: u64,
    Ghost(clog): Ghost<Seq<AEntry>>,
) -> (r: Option<Ghost<MHost>>)
    requires
        h.term == term as nat,
        h.role is Follower,
        h.vote == vote_view(vote),
        h.log.len() == last_index as nat,
        last_term(h.log) == lterm as nat,
        clog.len() == cand_last_index as nat,
        last_term(clog) == cand_last_term as nat,
        i != cand,
    ensures
        r matches Some(h2) ==> {
            &&& h2@ == (MHost { vote: Some(cand as int), ..h })
            &&& host_refines(i as int, n, h, h2@,
                    Set::empty().insert(Msg::Campaign { c: cand as int, term: term as nat, clog }),
                    Set::empty().insert(Msg::Vote { v: i as int, c: cand as int, term: term as nat, vlog: h.log }))
        },
{
    // Don't vote if we already voted for someone else in this term.
    if let Some(v) = vote {
        if v != cand {
            return None;
        }
    }
    // Only vote if the candidate's log is at least as up-to-date as ours.
    if lterm > cand_last_term || (lterm == cand_last_term && last_index > cand_last_index) {
        return None;
    }
    proof {
        assert(up_to_date(clog, h.log));
        lemma_lift_grant(i as int, n, h, cand as int, clog);
    }
    Some(Ghost(MHost { vote: Some(cand as int), ..h }))
}

/// A candidate recording a granted vote (`Message::CampaignResponse`
/// handling). Refines `t_collect_vote`.
pub fn core_collect_vote(
    Ghost(h): Ghost<MHost>, i: u8, n: u8, term: u64, from: u8, Ghost(vlog): Ghost<Seq<AEntry>>,
) -> (r: Ghost<MHost>)
    requires
        h.term == term as nat,
        h.role is Candidate,
    ensures
        r@ == (MHost { votes: h.votes.insert(from as int), vote_logs: h.vote_logs.insert(from as int, vlog), ..h }),
        host_refines(i as int, n, h, r@,
            Set::empty().insert(Msg::Vote { v: from as int, c: i as int, term: term as nat, vlog }),
            Set::empty()),
{
    proof {
        lemma_lift_collect_vote(i as int, n, h, from as int, vlog);
    }
    Ghost(MHost { votes: h.votes.insert(from as int), vote_logs: h.vote_logs.insert(from as int, vlog), ..h })
}

/// Winning an election (`Candidate::into_leader`): checks the vote quorum —
/// the strict-majority arithmetic of `quorum_size` — and returns the leader
/// post-state, whose log ends in the new noop entry (section 5.4.2). The
/// shell performs the role change and appends the noop (`propose(None)`) as
/// one step. Returns `None` without a quorum. Refines `t_become_leader`.
pub fn core_become_leader(
    Ghost(h): Ghost<MHost>, i: u8, n: u8, term: u64, votes_count: usize,
) -> (r: Option<Ghost<MHost>>)
    requires
        h.term == term as nat,
        h.role is Candidate,
        h.votes.len() == votes_count,
        h.votes.subset_of(node_ids(n as nat)),
        n >= 1,
    ensures
        r matches Some(h2) ==> {
            &&& h2@ == (MHost {
                role: MRole::Leader,
                log: h.log.push(AEntry { term: term as nat, cmd: None }),
                read_seq: 0,
                ..h
            })
            &&& host_refines(i as int, n, h, h2@, Set::empty(), Set::empty())
        },
{
    proof {
        // |votes| <= n, so the arithmetic below cannot overflow.
        vstd::set_lib::lemma_len_subset(h.votes, node_ids(n as nat));
        vstd::set_lib::lemma_int_range(0, n as int);
        assert(node_ids(n as nat) == vstd::set_lib::set_int_range(0, n as int));
    }
    // quorum_size() == n / 2 + 1; votes_count >= n / 2 + 1 <==> 2 * count > n.
    if votes_count < (n as usize) / 2 + 1 {
        return None;
    }
    proof {
        assert(2 * h.votes.len() > n as nat);
        lemma_lift_become_leader(i as int, n, h);
    }
    Some(Ghost(MHost {
        role: MRole::Leader,
        log: h.log.push(AEntry { term: term as nat, cmd: None }),
        read_seq: 0,
        ..h
    }))
}

/// The view of a concrete command payload.
pub open spec fn cmd_view(c: Option<Seq<u8>>) -> Option<Seq<u8>> {
    c
}

/// A leader appending a client command to its log (`Leader::propose`).
/// Refines `t_propose`.
pub fn core_propose(
    Ghost(h): Ghost<MHost>, i: u8, n: u8, term: u64, Ghost(cmd): Ghost<Option<Seq<u8>>>,
) -> (r: Ghost<MHost>)
    requires
        h.term == term as nat,
        h.role is Leader,
    ensures
        r@ == (MHost { log: h.log.push(AEntry { term: term as nat, cmd }), ..h }),
        host_refines(i as int, n, h, r@, Set::empty(), Set::empty()),
{
    proof {
        lemma_lift_propose(i as int, n, h, cmd);
    }
    Ghost(MHost { log: h.log.push(AEntry { term: term as nat, cmd }), ..h })
}

/// A leader sending a window [b, e) of its log (`maybe_send_append`,
/// including empty probes). No state change; the concrete message the shell
/// sends carries the entries the leader log holds in that window. Refines
/// `t_send_append`.
pub fn core_send_append(Ghost(h): Ghost<MHost>, i: u8, n: u8, term: u64, b: u64, e: u64)
    requires
        h.term == term as nat,
        h.role is Leader,
        b <= e,
        e as nat <= h.log.len(),
    ensures
        host_refines(i as int, n, h, h, Set::empty(),
            Set::empty().insert(Msg::Append {
                term: term as nat,
                base: b as nat,
                bterm: if b == 0 { 0 } else { h.log[b as int - 1].term },
                entries: h.log.subrange(b as int, e as int),
            })),
{
    proof {
        lemma_lift_send_append(i as int, n, h, b as nat, e as nat);
    }
}

/// A host acking a match of its own-term entry at `mi` (a matching heartbeat
/// response, or the leader counting its own last index). `has_mi` is
/// `log.has(mi, term)` — trusted to agree with the ghost view. Refines
/// `t_send_ack` when the entry matches; no-op otherwise.
pub fn core_send_ack(Ghost(h): Ghost<MHost>, i: u8, n: u8, term: u64, mi: u64, has_mi: bool)
    requires
        h.term == term as nat,
        has_mi == (1 <= mi as nat <= h.log.len() && h.log[mi as int - 1].term == term as nat),
    ensures
        has_mi ==> host_refines(i as int, n, h, h, Set::empty(),
            Set::empty().insert(Msg::Ack { v: i as int, term: term as nat, mi: mi as nat })),
{
    proof {
        if has_mi {
            lemma_lift_send_ack(i as int, n, h, mi as nat);
        }
    }
}

/// A follower splicing appended entries (`Message::Append` handling at the
/// receiver's own term): `base_ok` is the `Log::has` base check — trusted to
/// agree with the ghost view. On a match, returns the ack match index and the
/// post-state with the spliced log (the splice semantics verified in
/// `raft::log`); `None` rejects with no state change. Refines
/// `t_recv_append`.
pub fn core_recv_append(
    Ghost(h): Ghost<MHost>, i: u8, n: u8, term: u64,
    base_index: u64, base_term: u64, entries_len: usize, Ghost(aentries): Ghost<Seq<AEntry>>,
    base_ok: bool,
) -> (r: Option<(u64, Ghost<MHost>)>)
    requires
        h.term == term as nat,
        h.role is Follower,
        aentries.len() == entries_len as nat,
        base_ok == (base_index == 0
            || (base_index as nat <= h.log.len() && h.log[base_index as int - 1].term == base_term as nat)),
        base_index + entries_len <= u64::MAX,
    ensures
        r matches Some((mi, h2)) ==> {
            &&& mi == base_index + entries_len as u64
            &&& h2@ == (MHost { log: splice(h.log, base_index as nat, aentries), ..h })
            &&& host_refines(i as int, n, h, h2@,
                    Set::empty().insert(Msg::Append {
                        term: term as nat, base: base_index as nat, bterm: base_term as nat, entries: aentries,
                    }),
                    Set::empty().insert(Msg::Ack {
                        v: i as int, term: term as nat, mi: (base_index + entries_len) as nat,
                    }))
        },
{
    if !base_ok {
        return None;
    }
    proof {
        // The model's Append base term is 0 exactly when the base is 0; the
        // receiving check makes both cases line up.
        if base_index == 0 {
            assert(h.log.len() >= 0);
        }
        lemma_lift_recv_append(i as int, n, h, base_index as nat, base_term as nat, aentries);
    }
    Some((base_index + entries_len as u64, Ghost(MHost { log: splice(h.log, base_index as nat, aentries), ..h })))
}

// ---------------------------------------------------------------------------
// The commit path
// ---------------------------------------------------------------------------

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

/// A leader advancing the commit index (`maybe_commit_and_apply`): validates
/// the commit index against the members' match indexes — a strict majority at
/// or past it, each backed by ack evidence — and the section 5.4.2 own-term
/// condition (`ci_term_ok`, trusted to agree with `log.get(ci)`). `members`
/// holds each member's (id, match index) with the leader's own last index
/// included; ids must be distinct and in range. Returns the post-state with
/// the new commit witness, or `None` if the commit is not justified. Refines
/// `t_leader_commit`.
pub fn core_leader_commit(
    Ghost(h): Ghost<MHost>, i: u8, n: u8, term: u64,
    ci: u64, commit_index: u64, ci_term_ok: bool,
    members: &Vec<(u8, u64)>, Ghost(evid): Ghost<Set<Msg>>,
) -> (r: Option<Ghost<MHost>>)
    requires
        h.term == term as nat,
        h.role is Leader,
        h.commit == commit_index as nat,
        ci_term_ok == (1 <= ci as nat <= h.log.len() && h.log[ci as int - 1].term == term as nat),
        forall|k1: int, k2: int| 0 <= k1 < k2 < members@.len() ==> (#[trigger] members@[k1]).0 != (#[trigger] members@[k2]).0,
        forall|k: int| 0 <= k < members@.len() ==> (#[trigger] members@[k]).0 < n,
        forall|k: int| 0 <= k < members@.len() && (#[trigger] members@[k]).1 >= 1 ==>
            evid.contains(Msg::Ack { v: members@[k].0 as int, term: term as nat, mi: members@[k].1 as nat }),
        n >= 1,
    ensures
        r matches Some(h2) ==> {
            &&& h2@.commit == ci as nat
            &&& h2@ == (MHost { commit: ci as nat, crec: h2@.crec, ..h })
            &&& h2@.crec.term == term as nat && h2@.crec.ci == ci as nat
            &&& host_refines(i as int, n, h, h2@, evid,
                    Set::empty().insert(Msg::Commit { term: term as nat, ci: ci as nat, rec: h2@.crec }))
        },
{
    if ci <= commit_index || !ci_term_ok {
        return None;
    }
    // Count members whose match index reaches ci, collecting the ghost
    // quorum map of ack evidence.
    let mut count: usize = 0;
    let mut k: usize = 0;
    let ghost mut qm: Map<int, nat> = Map::empty();
    let ghost mut qids: Seq<int> = Seq::empty();
    while k < members.len()
        invariant
            0 <= k <= members.len(),
            count <= k,
            count == qids.len(),
            qids.no_duplicates(),
            qm.dom() == qids.to_set(),
            ci >= 1,
            h.term == term as nat,
            forall|j: int| 0 <= j < qids.len() ==>
                exists|k2: int| 0 <= k2 < k && #[trigger] qids[j] == members@[k2].0 as int,
            forall|v: int| #[trigger] qm.dom().contains(v) ==>
                qm[v] >= ci as nat && evid.contains(Msg::Ack { v, term: term as nat, mi: qm[v] }) && 0 <= v < n,
            forall|k1: int, k2: int| 0 <= k1 < k2 < members@.len() ==> (#[trigger] members@[k1]).0 != (#[trigger] members@[k2]).0,
            forall|k2: int| 0 <= k2 < members@.len() ==> (#[trigger] members@[k2]).0 < n,
            forall|k2: int| 0 <= k2 < members@.len() && (#[trigger] members@[k2]).1 >= 1 ==>
                evid.contains(Msg::Ack { v: members@[k2].0 as int, term: term as nat, mi: members@[k2].1 as nat }),
        decreases members.len() - k,
    {
        let (id, val) = members[k];
        if val >= ci {
            proof {
                // The id is fresh: earlier collected ids come from earlier
                // (distinct) member entries.
                if qids.to_set().contains(id as int) {
                    let j = choose|j: int| 0 <= j < qids.len() && qids[j] == id as int;
                    let k2 = choose|k2: int| 0 <= k2 < k && qids[j] == members@[k2].0 as int;
                    assert(members@[k2].0 == members@[k as int].0);
                    assert(false);
                }
                let ghost old_qids = qids;
                qids = qids.push(id as int);
                qm = qm.insert(id as int, val as nat);
                assert(qm.dom() =~= qids.to_set()) by {
                    assert forall|x: int| qids.to_set().contains(x) implies
                        old_qids.to_set().contains(x) || x == id as int by {
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
                    assert(qids.to_set().contains(id as int)) by {
                        assert(qids[qids.len() - 1] == id as int);
                    }
                }
            }
            count = count + 1;
        }
        k = k + 1;
    }
    // Quorum: strict majority of the n-member cluster.
    proof {
        qids.unique_seq_to_set();
        assert(qm.dom().len() == count);
        assert forall|v: int| qm.dom().contains(v) implies node_ids(n as nat).contains(v) by {
            vstd::set_lib::lemma_int_range(0, n as int);
            assert(node_ids(n as nat) == vstd::set_lib::set_int_range(0, n as int));
        }
        vstd::set_lib::lemma_len_subset(qm.dom(), node_ids(n as nat));
        vstd::set_lib::lemma_int_range(0, n as int);
        assert(node_ids(n as nat) == vstd::set_lib::set_int_range(0, n as int));
        assert(count <= n as usize);
    }
    if 2 * count <= n as usize {
        return None;
    }
    proof {
        assert(is_quorum(n as nat, qm.dom()));
        lemma_lift_leader_commit(i as int, n, h, ci as nat, qm, evid);
    }
    Some(Ghost(MHost { commit: ci as nat, crec: CommitRec { term: term as nat, ci: ci as nat, q: qm }, ..h }))
}

/// A host adopting the leader's commit index from a heartbeat
/// (`Message::Heartbeat` handling): only after matching the leader's last
/// index `mi` in its own term (`match_ok`, trusted to agree with
/// `log.has(mi, term)`), and only forward. The ghost commit record is the
/// heartbeat's evidence. Returns the post-state, or `None` if nothing
/// advances. Refines `t_recv_commit`.
pub fn core_recv_commit(
    Ghost(h): Ghost<MHost>, i: u8, n: u8, term: u64,
    ci: u64, mi: u64, match_ok: bool, commit_index: u64, Ghost(rec): Ghost<CommitRec>,
) -> (r: Option<Ghost<MHost>>)
    requires
        h.term == term as nat,
        h.commit == commit_index as nat,
        match_ok == (1 <= mi as nat <= h.log.len() && h.log[mi as int - 1].term == term as nat),
        ci <= mi,
    ensures
        r matches Some(h2) ==> {
            &&& h2@ == (MHost { commit: ci as nat, crec: rec, ..h })
            &&& host_refines(i as int, n, h, h2@,
                    Set::empty().insert(Msg::Commit { term: term as nat, ci: ci as nat, rec }),
                    Set::empty())
        },
{
    if !match_ok || ci <= commit_index {
        return None;
    }
    proof {
        lemma_lift_recv_commit(i as int, n, h, ci as nat, mi as nat, rec);
    }
    Some(Ghost(MHost { commit: ci as nat, crec: rec, ..h }))
}

/// A leader re-announcing its commit index in a heartbeat
/// (`Leader::heartbeat`). No state change; a zero commit index announces
/// nothing. Refines `t_send_commit`.
pub fn core_send_commit(Ghost(h): Ghost<MHost>, i: u8, n: u8, term: u64, ci: u64)
    requires
        h.term == term as nat,
        h.role is Leader,
        h.commit == ci as nat,
    ensures
        ci >= 1 ==> host_refines(i as int, n, h, h, Set::empty(),
            Set::empty().insert(Msg::Commit { term: term as nat, ci: ci as nat, rec: h.crec })),
{
    proof {
        if ci >= 1 {
            lemma_lift_send_commit(i as int, n, h, ci as nat);
        }
    }
}

// ---------------------------------------------------------------------------
// The read path
// ---------------------------------------------------------------------------

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

/// A leader assigning the next read sequence number and broadcasting it for
/// confirmation (`ClientRequest::Read` handling). Refines `t_submit_read`.
pub fn core_submit_read(Ghost(h): Ghost<MHost>, i: u8, n: u8, term: u64, read_seq: u64) -> (r: (u64, Ghost<MHost>))
    requires
        h.term == term as nat,
        h.role is Leader,
        h.read_seq == read_seq as nat,
        read_seq < u64::MAX,
    ensures
        r.0 == read_seq + 1,
        r.1@ == (MHost { read_seq: (read_seq + 1) as nat, ..h }),
        host_refines(i as int, n, h, r.1@, Set::empty(),
            Set::empty()
                .insert(Msg::Read { term: term as nat, seq: (read_seq + 1) as nat })
                .insert(Msg::ReadConfirm { v: i as int, term: term as nat, seq: (read_seq + 1) as nat })),
{
    proof {
        lemma_lift_submit_read(i as int, n, h);
    }
    (read_seq + 1, Ghost(MHost { read_seq: (read_seq + 1) as nat, ..h }))
}

/// A follower confirming the leader's read sequence number (`Message::Read`
/// and heartbeat read_seq handling). No state change; a zero sequence number
/// confirms nothing. Refines `t_confirm_read`.
pub fn core_confirm_read(Ghost(h): Ghost<MHost>, i: u8, n: u8, term: u64, sq: u64)
    requires
        h.term == term as nat,
        h.role is Follower,
    ensures
        sq >= 1 ==> host_refines(i as int, n, h, h,
            Set::empty().insert(Msg::Read { term: term as nat, seq: sq as nat }),
            Set::empty().insert(Msg::ReadConfirm { v: i as int, term: term as nat, seq: sq as nat })),
{
    proof {
        if sq >= 1 {
            lemma_lift_confirm_read(i as int, n, h, sq as nat);
        }
    }
}

/// The linearizable-read gate (`maybe_read`): a read with sequence number
/// `seq` may be served once (a) the leader's committed tail is from its own
/// term (`commit_term_ok`, trusted to agree with `get_commit_index`), and (b)
/// a strict majority of members (self included) have confirmed a read
/// sequence number at or past `seq`, each backed by confirmation evidence.
///
/// When this returns true, the safety model's `thm_read_linearizable`
/// applies: in every invariant-satisfying cluster state consistent with this
/// node's view where this read was submitted, every write committed anywhere
/// in the cluster at submission time is contained in this leader's committed
/// (applied) prefix — the read is not stale.
pub fn core_can_serve(
    Ghost(h): Ghost<MHost>, i: u8, n: u8, term: u64,
    seq: u64, commit_index: u64, commit_term_ok: bool,
    confirms: &Vec<(u8, u64)>, Ghost(evid): Ghost<Set<Msg>>,
) -> (r: bool)
    requires
        h.term == term as nat,
        h.role is Leader,
        h.commit == commit_index as nat,
        commit_term_ok == (1 <= commit_index as nat <= h.log.len()
            && h.log[commit_index as int - 1].term == term as nat),
        seq >= 1,
        forall|k1: int, k2: int| 0 <= k1 < k2 < confirms@.len() ==> (#[trigger] confirms@[k1]).0 != (#[trigger] confirms@[k2]).0,
        forall|k: int| 0 <= k < confirms@.len() ==> (#[trigger] confirms@[k]).0 < n,
        forall|k: int| 0 <= k < confirms@.len() && (#[trigger] confirms@[k]).1 >= 1 ==>
            evid.contains(Msg::ReadConfirm { v: confirms@[k].0 as int, term: term as nat, seq: confirms@[k].1 as nat }),
        n >= 1,
    ensures
        r ==> forall|s: GState, rr: ReadRec|
            #[trigger] binds(s, i as int, n, h, evid) && inv(s)
            && #[trigger] s.reads.contains(rr) && rr.term == term as nat && rr.seq == seq as nat ==>
            forall|rec: CommitRec| #[trigger] rr.born.contains(rec) ==> {
                &&& rec.term <= term as nat
                &&& rec.ci <= h.commit
                &&& prefix_eq(h.log, s.leader_log[rec.term], rec.ci)
            },
{
    if !commit_term_ok {
        return false;
    }
    // Count members that confirmed at or past seq, collecting the quorum.
    let mut count: usize = 0;
    let mut k: usize = 0;
    let ghost mut conf: Set<int> = Set::empty();
    let ghost mut cids: Seq<int> = Seq::empty();
    while k < confirms.len()
        invariant
            0 <= k <= confirms.len(),
            count <= k,
            count == cids.len(),
            cids.no_duplicates(),
            conf == cids.to_set(),
            seq >= 1,
            h.term == term as nat,
            forall|j: int| 0 <= j < cids.len() ==>
                exists|k2: int| 0 <= k2 < k && #[trigger] cids[j] == confirms@[k2].0 as int,
            forall|v: int| #[trigger] conf.contains(v) ==> {
                &&& 0 <= v < n
                &&& exists|sq2: nat| sq2 >= seq as nat
                    && #[trigger] evid.contains(Msg::ReadConfirm { v, term: term as nat, seq: sq2 })
            },
            forall|k1: int, k2: int| 0 <= k1 < k2 < confirms@.len() ==> (#[trigger] confirms@[k1]).0 != (#[trigger] confirms@[k2]).0,
            forall|k2: int| 0 <= k2 < confirms@.len() ==> (#[trigger] confirms@[k2]).0 < n,
            forall|k2: int| 0 <= k2 < confirms@.len() && (#[trigger] confirms@[k2]).1 >= 1 ==>
                evid.contains(Msg::ReadConfirm { v: confirms@[k2].0 as int, term: term as nat, seq: confirms@[k2].1 as nat }),
        decreases confirms.len() - k,
    {
        let (id, sq) = confirms[k];
        if sq >= seq {
            proof {
                if cids.to_set().contains(id as int) {
                    let j = choose|j: int| 0 <= j < cids.len() && cids[j] == id as int;
                    let k2 = choose|k2: int| 0 <= k2 < k && cids[j] == confirms@[k2].0 as int;
                    assert(confirms@[k2].0 == confirms@[k as int].0);
                    assert(false);
                }
                let ghost old_cids = cids;
                cids = cids.push(id as int);
                conf = conf.insert(id as int);
                assert(conf =~= cids.to_set()) by {
                    assert forall|x: int| cids.to_set().contains(x) implies
                        old_cids.to_set().contains(x) || x == id as int by {
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
                    assert(cids.to_set().contains(id as int)) by {
                        assert(cids[cids.len() - 1] == id as int);
                    }
                }
                assert(exists|sq2: nat| sq2 >= seq as nat
                    && #[trigger] evid.contains(Msg::ReadConfirm { v: id as int, term: term as nat, seq: sq2 })) by {
                    assert(evid.contains(Msg::ReadConfirm { v: id as int, term: term as nat, seq: sq as nat }));
                }
            }
            count = count + 1;
        }
        k = k + 1;
    }
    proof {
        cids.unique_seq_to_set();
        assert(conf.len() == count);
        assert forall|v: int| conf.contains(v) implies node_ids(n as nat).contains(v) by {
            vstd::set_lib::lemma_int_range(0, n as int);
            assert(node_ids(n as nat) == vstd::set_lib::set_int_range(0, n as int));
        }
        vstd::set_lib::lemma_len_subset(conf, node_ids(n as nat));
        vstd::set_lib::lemma_int_range(0, n as int);
        assert(node_ids(n as nat) == vstd::set_lib::set_int_range(0, n as int));
        assert(count <= n as usize);
    }
    if 2 * count <= n as usize {
        return false;
    }
    proof {
        assert(is_quorum(n as nat, conf));
        assert forall|s: GState, rr: ReadRec|
            #[trigger] binds(s, i as int, n, h, evid) && inv(s)
            && #[trigger] s.reads.contains(rr) && rr.term == term as nat && rr.seq == seq as nat implies
            forall|rec: CommitRec| #[trigger] rr.born.contains(rec) ==> {
                &&& rec.term <= term as nat
                &&& rec.ci <= h.commit
                &&& prefix_eq(h.log, s.leader_log[rec.term], rec.ci)
            } by {
            assert forall|z: int| #[trigger] conf.contains(z) implies
                exists|sq2: nat| sq2 >= rr.seq
                    && #[trigger] s.net.contains(Msg::ReadConfirm { v: z, term: rr.term, seq: sq2 }) by {
                let sq2 = choose|sq2: nat| sq2 >= seq as nat
                    && #[trigger] evid.contains(Msg::ReadConfirm { v: z, term: term as nat, seq: sq2 });
                assert(s.net.contains(Msg::ReadConfirm { v: z, term: rr.term, seq: sq2 }));
            }
            thm_read_linearizable(s, i as int, rr, conf);
        }
    }
    true
}

} // verus!
