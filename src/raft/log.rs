// The verified code below is written in Verus's exec idiom (explicit
// `len() == 0` checks, `&Vec` parameters, verdict matches instead of `?`),
// which trips several style lints.
#![allow(
    clippy::ptr_arg,
    clippy::len_zero,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::int_plus_one,
    clippy::single_match,
    clippy::manual_map,
    clippy::question_mark
)]

use std::ops::Bound;
#[cfg(test)]
use std::ops::RangeBounds;

use serde::{Deserialize, Serialize};

use crate::encoding::{self, Key as _, Value as _, bincode};
use crate::error::{Error, Result};
use crate::raft::{NodeID, Term};
use crate::storage;

/// A log index (entry position). Starts at 1. 0 indicates no index.
pub type Index = u64;

/// A log entry containing a state machine command.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Entry {
    /// The entry index.
    ///
    /// We could omit the index in the encoded value, since it's also stored in
    /// the key, but we keep it simple.
    pub index: Index,
    /// The term in which the entry was added.
    pub term: Term,
    /// The state machine command. None (noop) commands are used during leader
    /// election to commit old entries, see section 5.4.2 in the Raft paper.
    pub command: Option<Vec<u8>>,
}

impl encoding::Value for Entry {}

/// A log storage key.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Key {
    /// A log entry, storing the term and command.
    Entry(Index),
    /// Stores the current term and vote (if any).
    TermVote,
    /// Stores the current commit index (if any).
    CommitIndex,
}

impl encoding::Key<'_> for Key {}

// --- Verus-verified Raft log ------------------------------------------------
//
// `Log` is verified against a ghost *view* of the entries the storage engine
// holds (`Log::view()`, a `Seq<AEntry>` in which entry k is impl index k+1).
// The documented log invariants (see the `Log` doc comment below) are stated
// over that view by `Log::inv` — contiguity is built into the sequence
// representation, terms are nonzero and nondecreasing and at or below the
// current term, the committed prefix is within the log and `commit_term` is
// the term of the entry at `commit_index` — and every public method carries a
// postcondition that pins its result and the new view in terms of the old
// one: `append` pushes an entry of the current term, `splice` yields exactly
// the safety model's `splice` of the batch (the "skip already-present
// entries" scan included), `commit` moves the commit index forward to an
// existing entry, and `has`/`get` answer according to the view.
//
// The precondition checks that `Log` documents as panics are kept as panics,
// raised through the single diverging function `fault`, and are proven to
// fire exactly when documented.
//
// What stays trusted is the *engine rim*: the handful of
// `#[verifier::external_body]` functions below that perform the actual
// engine I/O. Each carries an explicit specification stating what the engine
// holds afterwards in terms of the view — this is the storage-integrity
// assumption, and it is the only place it lives. `Log::open` (loading the
// durable state at startup) is likewise trusted to yield a log satisfying
// `inv`; see its comment for the fsync caveat. Serialization and the engines
// themselves are outside the verified perimeter.
//
// `verus!` erases all specs and proofs to the plain `fn` bodies under a
// normal `cargo build`.
use vstd::prelude::*;

#[allow(unused_imports)] // referenced only from ghost code
use crate::raft::safety::AEntry;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::raft::safety::{last_term, log_wf, splice, splice_is_noop, terms_le};

/// The storage engine, boxed. Wrapped so that the verified `Log` can hold it
/// as an opaque type; only the trusted engine rim below touches it.
pub struct EngineBox(pub Box<dyn storage::Engine>);

/// A `Log` precondition violation. These are the documented panics of the log
/// methods; the verified code raises them through `fault`.
#[derive(Debug)]
pub enum Fault {
    // Log faults.
    SetTermZero,
    TermRegression(Term, Term),
    VoteChange,
    AppendTermZero,
    IndexOverflow,
    CommitMissing(Index),
    CommitRegression(Index, Index),
    SpliceZeroIndexOrTerm,
    SpliceNonContiguous,
    SpliceTermRegression,
    SpliceTermBeyondCurrent(Term, Term),
    SpliceBaseTermRegression(Term, Term),
    SpliceNoTouch(Index),
    SpliceBelowCommit,
    CommandMismatch(Entry),
    CommittedEntryMissing(Index),
    // Node step faults (raised by the verified step functions in
    // `raft::refine`, mirroring the shell's former assertions).
    UnknownNode(NodeID),
    WrongRole,
    WrongTerm,
    FutureMatchIndex,
    FutureReadSequence,
    FutureRejectIndex,
    CommitAfterLastIndex,
    BaseIndexMismatch,
    NoVoteQuorum,
    TermOverflow,
    ReadSequenceOverflow,
    MissingBaseEntry,
    CommitIndexMissing(Index),
    LeaderLastTerm,
}

impl std::fmt::Display for Fault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SetTermZero => write!(f, "can't set term 0"),
            Self::TermRegression(cur, new) => write!(f, "term regression {cur} → {new}"),
            Self::VoteChange => write!(f, "can't change vote"),
            Self::AppendTermZero => write!(f, "can't append entry in term 0"),
            Self::IndexOverflow => write!(f, "log index overflow"),
            Self::CommitMissing(index) => write!(f, "commit index {index} does not exist"),
            Self::CommitRegression(cur, new) => {
                write!(f, "commit index regression {cur} → {new}")
            }
            Self::SpliceZeroIndexOrTerm => write!(f, "spliced entry has index or term 0"),
            Self::SpliceNonContiguous => write!(f, "spliced entries are not contiguous"),
            Self::SpliceTermRegression => write!(f, "spliced entries have term regression"),
            Self::SpliceTermBeyondCurrent(last, cur) => {
                write!(f, "splice term {last} beyond current {cur}")
            }
            Self::SpliceBaseTermRegression(base, first) => {
                write!(f, "splice term regression {base} → {first}")
            }
            Self::SpliceNoTouch(first) => write!(f, "first index {first} must touch existing log"),
            Self::SpliceBelowCommit => write!(f, "spliced entries below commit index"),
            Self::CommandMismatch(entry) => write!(f, "command mismatch at {entry:?}"),
            Self::CommittedEntryMissing(index) => write!(f, "committed entry {index} missing"),
            Self::UnknownNode(id) => write!(f, "unknown node {id}"),
            Self::WrongRole => write!(f, "step function called in the wrong role"),
            Self::WrongTerm => write!(f, "step function called with a message from another term"),
            Self::FutureMatchIndex => write!(f, "future match index"),
            Self::FutureReadSequence => write!(f, "future read sequence number"),
            Self::FutureRejectIndex => write!(f, "future reject index"),
            Self::CommitAfterLastIndex => write!(f, "commit_index after last_index"),
            Self::BaseIndexMismatch => write!(f, "base index mismatch"),
            Self::NoVoteQuorum => write!(f, "leadership without verified vote quorum"),
            Self::TermOverflow => write!(f, "term overflow"),
            Self::ReadSequenceOverflow => write!(f, "read sequence number overflow"),
            Self::MissingBaseEntry => write!(f, "missing base entry"),
            Self::CommitIndexMissing(index) => write!(f, "commit index {index} missing"),
            Self::LeaderLastTerm => write!(f, "leader's last_term not in current term"),
        }
    }
}

/// Loads the durable log state from the engine (unverified: deserialization
/// and engine scans). Called by the trusted `Log::open`.
fn load_state(engine: &mut Box<dyn storage::Engine>) -> Result<LogState> {
    let (term, vote) = engine
        .get(&Key::TermVote.encode())?
        .map(|v| bincode::deserialize(&v))
        .transpose()?
        .unwrap_or((0, None));
    let (last_index, last_term) = engine
        .scan_dyn((
            Bound::Included(Key::Entry(0).encode()),
            Bound::Included(Key::Entry(u64::MAX).encode()),
        ))
        .last()
        .transpose()?
        .map(|(_, v)| Entry::decode(&v))
        .transpose()?
        .map(|e| (e.index, e.term))
        .unwrap_or((0, 0));
    let (commit_index, commit_term) = engine
        .get(&Key::CommitIndex.encode())?
        .map(|v| bincode::deserialize(&v))
        .transpose()?
        .unwrap_or((0, 0));
    Ok(LogState { term, vote, last_index, last_term, commit_index, commit_term })
}

verus! {

// Types from outside the verified perimeter that the verified code handles.
// `EngineBox` and `Error` are opaque (never inspected); `Entry` and `Fault`
// are transparent (their fields are visible to the specifications).
#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)] // Verus type specification
pub struct ExEngineBox(EngineBox);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)] // Verus type specification
pub struct ExError(Error);

#[verifier::external_type_specification]
#[allow(dead_code)] // Verus type specification
pub struct ExEntry(Entry);

#[verifier::external_type_specification]
#[allow(dead_code)] // Verus type specification
pub struct ExFault(Fault);

/// Panics with the fault's message. The only way verified code panics: a
/// diverging function has a vacuous specification, so nothing is trusted
/// here beyond "it does not return".
#[verifier::external_body]
pub fn fault(f: Fault) -> ! {
    panic!("{f}")
}

/// The ghost view of a command payload.
pub open spec fn cmd_view(c: Option<Vec<u8>>) -> Option<Seq<u8>> {
    match c {
        Some(v) => Some(v@),
        None => None,
    }
}

/// The abstract (safety model) view of an entry: its term and command.
pub open spec fn entry_view(e: Entry) -> AEntry {
    AEntry { term: e.term as nat, cmd: cmd_view(e.command) }
}

/// The abstract view of a batch of entries.
pub open spec fn entries_view(es: Seq<Entry>) -> Seq<AEntry> {
    es.map_values(|e: Entry| entry_view(e))
}

/// The in-memory summary of the durable log state (term, vote, last and
/// commit index/term). Mutated only via the verified transitions below.
pub struct LogState {
    /// The current term.
    pub term: Term,
    /// Our leader vote in the current term, if any.
    pub vote: Option<NodeID>,
    /// The index of the last stored entry.
    pub last_index: Index,
    /// The term of the last stored entry.
    pub last_term: Term,
    /// The index of the last committed entry.
    pub commit_index: Index,
    /// The term of the last committed entry.
    pub commit_term: Term,
}

/// The summary's own invariant: entry terms are at or below the current term,
/// and the committed prefix is within the log. `Log::inv` extends it to the
/// ghost view of the entries.
pub open spec fn wf(st: LogState) -> bool {
    &&& st.last_term <= st.term
    &&& st.commit_index <= st.last_index
}

/// The verdict of `set_term_vote_state`.
pub enum TermVoteCheck {
    /// The term is 0, which is invalid.
    ZeroTerm,
    /// The term regresses the current term.
    TermRegression,
    /// The vote changes within the current term.
    VoteChange,
    /// The term and vote are unchanged; nothing to do.
    Noop,
    /// The term/vote change is valid; the new state.
    Update(LogState),
}

/// Option<NodeID> equality (Verus has no exec `==` for it out of the box).
fn vote_eq(a: Option<NodeID>, b: Option<NodeID>) -> (r: bool)
    ensures r == (a == b),
{
    match (a, b) {
        (None, None) => true,
        (Some(a), Some(b)) => a == b,
        _ => false,
    }
}

/// Verified term/vote transition: enforces that the term is nonzero and never
/// regresses, and that the vote can't change within a term.
pub fn set_term_vote_state(st: &LogState, term: Term, vote: Option<NodeID>) -> (r: TermVoteCheck)
    ensures match r {
        TermVoteCheck::ZeroTerm => term == 0,
        TermVoteCheck::TermRegression => 0 < term < st.term,
        TermVoteCheck::VoteChange => term == st.term && st.vote is Some && vote != st.vote,
        TermVoteCheck::Noop => term == st.term && vote == st.vote && term > 0,
        TermVoteCheck::Update(new) => {
            &&& term > 0
            &&& new.term == term && new.term >= st.term // term monotonicity
            &&& term == st.term ==> st.vote is None // votes are never changed
            &&& new.vote == vote
            &&& new.last_index == st.last_index && new.last_term == st.last_term
            &&& new.commit_index == st.commit_index && new.commit_term == st.commit_term
            &&& wf(*st) ==> wf(new)
        },
    },
{
    if term == 0 {
        return TermVoteCheck::ZeroTerm;
    }
    if term < st.term {
        return TermVoteCheck::TermRegression;
    }
    if term == st.term {
        let same_vote = vote_eq(vote, st.vote);
        if st.vote.is_some() && !same_vote {
            return TermVoteCheck::VoteChange;
        }
        if same_vote {
            return TermVoteCheck::Noop;
        }
    }
    TermVoteCheck::Update(LogState {
        term,
        vote,
        last_index: st.last_index,
        last_term: st.last_term,
        commit_index: st.commit_index,
        commit_term: st.commit_term,
    })
}

/// The verdict of `append_state`.
pub enum AppendCheck {
    /// Can't append in term 0.
    ZeroTerm,
    /// The log is full (`u64::MAX` entries); unreachable in practice.
    IndexOverflow,
    /// The append is valid: the new entry's index and the new state.
    Append(Index, LogState),
}

/// Verified append transition: the new entry is at `last_index + 1` (index
/// contiguity) in the current term, and given `wf` its term doesn't regress
/// the last entry's term (term monotonicity).
pub fn append_state(st: &LogState) -> (r: AppendCheck)
    ensures match r {
        AppendCheck::ZeroTerm => st.term == 0,
        AppendCheck::IndexOverflow => st.term > 0 && st.last_index == u64::MAX,
        AppendCheck::Append(index, new) => {
            &&& st.term > 0
            &&& index == st.last_index + 1 // index contiguity
            &&& new.last_index == index && new.last_term == st.term // current-term append
            &&& wf(*st) ==> new.last_term >= st.last_term // term monotonicity
            &&& new.term == st.term && new.vote == st.vote
            &&& new.commit_index == st.commit_index && new.commit_term == st.commit_term
            &&& wf(*st) ==> wf(new)
        },
    },
{
    if st.term == 0 {
        return AppendCheck::ZeroTerm;
    }
    if st.last_index == u64::MAX {
        return AppendCheck::IndexOverflow;
    }
    let index = st.last_index + 1;
    AppendCheck::Append(index, LogState {
        term: st.term,
        vote: st.vote,
        last_index: index,
        last_term: st.term,
        commit_index: st.commit_index,
        commit_term: st.commit_term,
    })
}

/// The verdict of `commit_state`.
pub enum CommitCheck {
    /// The index regresses the commit index.
    Regression,
    /// The index is already committed; nothing to do.
    Noop,
    /// The commit is valid; the new state.
    Commit(LogState),
}

/// Verified commit transition: the commit index never regresses. `entry_index`
/// and `entry_term` are the index and term of the log entry being committed
/// (the caller proves existence by fetching it from the log).
pub fn commit_state(st: &LogState, entry_index: Index, entry_term: Term) -> (r: CommitCheck)
    ensures match r {
        CommitCheck::Regression => entry_index < st.commit_index,
        CommitCheck::Noop => entry_index == st.commit_index,
        CommitCheck::Commit(new) => {
            &&& entry_index > st.commit_index // no commit regression
            &&& new.commit_index == entry_index && new.commit_term == entry_term
            &&& new.term == st.term && new.vote == st.vote
            &&& new.last_index == st.last_index && new.last_term == st.last_term
            &&& wf(*st) && entry_index <= st.last_index ==> wf(new)
        },
    },
{
    if entry_index < st.commit_index {
        CommitCheck::Regression
    } else if entry_index == st.commit_index {
        CommitCheck::Noop
    } else {
        CommitCheck::Commit(LogState {
            term: st.term,
            vote: st.vote,
            last_index: st.last_index,
            last_term: st.last_term,
            commit_index: entry_index,
            commit_term: entry_term,
        })
    }
}

/// A spliced batch has contiguous indexes.
pub open spec fn entries_contiguous(es: Seq<Entry>) -> bool {
    forall|i: int| #![trigger es[i]] 0 < i < es.len() ==> es[i].index == es[i - 1].index + 1
}

/// A spliced batch has equal or increasing terms.
pub open spec fn entries_terms_monotone(es: Seq<Entry>) -> bool {
    forall|i: int| #![trigger es[i]] 0 < i < es.len() ==> es[i].term >= es[i - 1].term
}

/// The verdict of `check_splice_entries`.
pub enum SpliceEntriesCheck {
    /// The batch is empty (the caller handles this before checking).
    Empty,
    /// The first entry has index or term 0.
    ZeroIndexOrTerm,
    /// The batch's indexes are not contiguous.
    NonContiguous,
    /// The batch's terms regress.
    TermRegression,
    /// The batch is well-formed.
    WellFormed,
}

/// Verified well-formedness check for a spliced batch: nonzero first index
/// and term, contiguous indexes, and monotone terms.
/// (Clippy allows: Verus wants `&Vec` and `len() == 0`, which vstd specs.)
#[allow(clippy::ptr_arg, clippy::len_zero)]
pub fn check_splice_entries(es: &Vec<Entry>) -> (r: SpliceEntriesCheck)
    ensures match r {
        SpliceEntriesCheck::Empty => es@.len() == 0,
        SpliceEntriesCheck::ZeroIndexOrTerm => {
            es@.len() > 0 && (es@[0].index == 0 || es@[0].term == 0)
        },
        SpliceEntriesCheck::NonContiguous => !entries_contiguous(es@),
        SpliceEntriesCheck::TermRegression => !entries_terms_monotone(es@),
        SpliceEntriesCheck::WellFormed => {
            &&& es@.len() > 0
            &&& es@[0].index > 0 && es@[0].term > 0
            &&& entries_contiguous(es@)
            &&& entries_terms_monotone(es@)
        },
    },
{
    if es.len() == 0 {
        return SpliceEntriesCheck::Empty;
    }
    if es[0].index == 0 || es[0].term == 0 {
        return SpliceEntriesCheck::ZeroIndexOrTerm;
    }
    let mut i: usize = 1;
    while i < es.len()
        invariant
            1 <= i <= es@.len(),
            forall|j: int| #![trigger es@[j]] 0 < j < i ==> es@[j].index == es@[j - 1].index + 1,
        decreases es@.len() - i,
    {
        // An index at u64::MAX can't have a successor, so the batch is not
        // contiguous (and computing `+ 1` would overflow).
        if es[i - 1].index == u64::MAX || es[i].index != es[i - 1].index + 1 {
            assert(es@[i as int].index != es@[i as int - 1].index + 1);
            return SpliceEntriesCheck::NonContiguous;
        }
        i += 1;
    }
    let mut i: usize = 1;
    while i < es.len()
        invariant
            1 <= i <= es@.len(),
            forall|j: int| #![trigger es@[j]] 0 < j < i ==> es@[j].term >= es@[j - 1].term,
        decreases es@.len() - i,
    {
        if es[i].term < es[i - 1].term {
            assert(es@[i as int].term < es@[i as int - 1].term);
            return SpliceEntriesCheck::TermRegression;
        }
        i += 1;
    }
    SpliceEntriesCheck::WellFormed
}

/// The verdict of `check_splice_connect`.
pub enum SpliceConnectCheck {
    /// The batch's last term is beyond the current term.
    TermBeyondCurrent,
    /// The batch's first term regresses the base entry's term.
    BaseTermRegression,
    /// The batch doesn't touch the existing log.
    NoTouch,
    /// The batch connects to the existing log.
    Connects,
}

/// Verified splice connection check: the batch must not exceed the current
/// term, and must connect to the existing log without a term regression.
/// `base_term` is the term of the log entry just before the batch's first
/// index, or None if there is no such entry.
pub fn check_splice_connect(
    st: &LogState,
    first_index: Index,
    first_term: Term,
    last_term: Term,
    base_term: Option<Term>,
) -> (r: SpliceConnectCheck)
    ensures match r {
        SpliceConnectCheck::TermBeyondCurrent => last_term > st.term,
        SpliceConnectCheck::BaseTermRegression => {
            last_term <= st.term && (base_term matches Some(bt) && first_term < bt)
        },
        SpliceConnectCheck::NoTouch => {
            last_term <= st.term && base_term is None && first_index != 1
        },
        SpliceConnectCheck::Connects => {
            &&& last_term <= st.term // term doesn't exceed the current term
            &&& match base_term {
                Some(bt) => first_term >= bt, // no term regression at the base
                None => first_index == 1, // or the batch starts the log
            }
        },
    },
{
    if last_term > st.term {
        return SpliceConnectCheck::TermBeyondCurrent;
    }
    match base_term {
        Some(bt) => {
            if first_term < bt {
                SpliceConnectCheck::BaseTermRegression
            } else {
                SpliceConnectCheck::Connects
            }
        }
        None => {
            if first_index == 1 {
                SpliceConnectCheck::Connects
            } else {
                SpliceConnectCheck::NoTouch
            }
        }
    }
}

/// Verified splice transition: refuses to write at or below the commit index
/// (committed entries are immutable), and moves the last index/term to the
/// batch's last entry. `first_index` is the first index actually written
/// (after skipping entries already in the log); `last_index`/`last_term` are
/// the batch's last entry. Returns None iff the batch writes below the commit
/// index.
pub fn splice_state(
    st: &LogState,
    first_index: Index,
    last_index: Index,
    last_term: Term,
) -> (r: Option<LogState>)
    ensures match r {
        Some(new) => {
            &&& first_index > st.commit_index // committed entries never change
            &&& new.last_index == last_index && new.last_term == last_term
            &&& new.term == st.term && new.vote == st.vote
            &&& new.commit_index == st.commit_index && new.commit_term == st.commit_term
            &&& wf(*st) && last_term <= st.term && first_index <= last_index ==> wf(new)
        },
        None => first_index <= st.commit_index,
    },
{
    if first_index <= st.commit_index {
        return None;
    }
    Some(LogState {
        term: st.term,
        vote: st.vote,
        last_index,
        last_term,
        commit_index: st.commit_index,
        commit_term: st.commit_term,
    })
}

/// Byte-vector equality.
fn bytes_eq(a: &Vec<u8>, b: &Vec<u8>) -> (r: bool)
    ensures r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            a@.len() == b@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

/// Command equality.
fn cmd_eq(a: &Option<Vec<u8>>, b: &Option<Vec<u8>>) -> (r: bool)
    ensures r == (cmd_view(*a) == cmd_view(*b)),
{
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => bytes_eq(x, y),
        _ => false,
    }
}

/// The Raft log stores a sequence of arbitrary commands (typically writes) that
/// are replicated across nodes and applied sequentially to the local state
/// machine. Each entry contains an index, command, and the term in which the
/// leader proposed it. Commands may be noops (None), which are added when a
/// leader is elected (see section 5.4.2 in the Raft paper). For example:
///
/// Index | Term | Command
/// ------|------|------------------------------------------------------
///   1   |   1  | None
///   2   |   1  | CREATE TABLE table (id INT PRIMARY KEY, value STRING)
///   3   |   1  | INSERT INTO table VALUES (1, 'foo')
///   4   |   2  | None
///   5   |   2  | UPDATE table SET value = 'bar' WHERE id = 1
///   6   |   2  | DELETE FROM table WHERE id = 1
///
/// Note that this is for illustration only, and the actual toyDB Raft commands
/// are not SQL statements but lower-level write operations.
///
/// A key/value store is used to store the log entries on disk, keyed by index,
/// along with a few other metadata keys (e.g. who we voted for in this term).
///
/// In the steady state, the log is append-only: when a client submits a
/// command, the leader appends it to its own log (via [`Log::append`]) and
/// replicates it to followers who append it to their logs (via
/// [`Log::splice`]). When an index has been replicated to a majority of nodes
/// it becomes committed, making the log immutable up to that index and
/// guaranteeing that all nodes will eventually contain it. Nodes keep track of
/// the commit index via [`Log::commit`] and apply committed commands to the
/// state machine.
///
/// However, uncommitted entries can be replaced or removed. A leader may append
/// entries to its log, but then be unable to reach consensus on them (e.g.
/// because it is unable to communicate with a majority of nodes). If a
/// different leader is elected and writes different commands to those same
/// indexes, then the uncommitted entries will be replaced with entries from the
/// new leader once the old leader (or a follower) discovers it.
///
/// The Raft log has the following invariants (the local ones are `Log::inv`,
/// verified over the ghost view of the stored entries; the cross-node ones
/// are theorems of the safety model in `raft::safety`):
///
/// * Entry indexes are contiguous starting at 1 (no index gaps).
/// * Entry terms never decrease from the previous entry.
/// * Entry terms are at or below the current term.
/// * Appended entries are durable (flushed to disk).
/// * Appended entries use the current term.
/// * Committed entries are never changed or removed (no log truncation).
/// * Committed entries will eventually be replicated to all nodes.
/// * Entries with the same index/term contain the same command.
/// * If two logs contain a matching index/term, all previous entries
///   are identical (see section 5.3 in the Raft paper).
pub struct Log {
    /// The underlying storage engine. Uses a trait object instead of generics,
    /// to allow runtime selection of the engine and avoid propagating the
    /// generic type parameters throughout Raft. Only the trusted engine rim
    /// touches it.
    engine: EngineBox,
    /// The in-memory summary of the durable state (term, vote, last and
    /// commit index/term).
    state: LogState,
    /// If true, fsync entries to disk when appended. This is mandated by Raft,
    /// but comes with a hefty performance penalty (especially since we don't
    /// optimize for it by batching entries before fsyncing). Disabling it will
    /// yield much better write performance, but may lose data on crashes, which
    /// in some scenarios can cause log entries to become "uncommitted" and
    /// state machines diverging.
    fsync: bool,
    /// Ghost (zero-sized, proof-only): the entries the engine holds, in
    /// order; entry k is the entry at index k+1. Updated only by the trusted
    /// engine rim, whose specifications state the storage-integrity
    /// assumption.
    #[allow(dead_code)] // read only by ghost code, erased in a normal build
    view: Ghost<Seq<AEntry>>,
}

impl Log {
    /// The abstract view of the stored entries.
    pub closed spec fn view(&self) -> Seq<AEntry> {
        self.view@
    }

    /// The current term.
    pub closed spec fn term(&self) -> Term {
        self.state.term
    }

    /// The vote in the current term.
    pub closed spec fn vote(&self) -> Option<NodeID> {
        self.state.vote
    }

    /// The commit index.
    pub closed spec fn commit_index(&self) -> Index {
        self.state.commit_index
    }

    /// The log holds an entry with this index and term.
    pub open spec fn has_spec(&self, index: Index, term: Term) -> bool {
        1 <= index <= self.view().len() && self.view()[index - 1].term == term as nat
    }

    /// The log invariant: the summary matches the view, the committed prefix
    /// is within the log and `commit_term` is the term of the entry at the
    /// commit index, entry terms are nonzero, nondecreasing and at or below
    /// the current term.
    pub closed spec fn inv(&self) -> bool {
        &&& self.state.last_index as nat == self.view@.len()
        &&& self.state.last_term as nat == last_term(self.view@)
        &&& self.state.commit_index as nat <= self.view@.len()
        &&& self.state.commit_index >= 1 ==>
            self.state.commit_term as nat == self.view@[self.state.commit_index - 1].term
        &&& log_wf(self.view@)
        &&& terms_le(self.view@, self.state.term as nat)
    }

    // --- TRUSTED: the engine rim ---------------------------------------
    //
    // Each function performs one kind of engine I/O and states, as its
    // postcondition, what the engine holds afterwards in terms of the ghost
    // view. These specifications are the storage-integrity assumption. On an
    // I/O error nothing is guaranteed (the error propagates and the node is
    // discarded).

    /// TRUSTED (storage integrity): opens the log over an engine, loading the
    /// durable summary. The result satisfies `inv`: the entries on disk are
    /// contiguous from 1, well-formed, and consistent with the summary
    /// (they were written by this module before the restart). Not covered:
    /// with `enable_fsync(false)` a crash can lose appended entries while
    /// keeping a commit index beyond them, a state outside the invariant.
    #[verifier::external_body]
    pub fn open(engine: EngineBox) -> (r: Result<Log>)
        ensures
            r matches Ok(log) ==> log.inv(),
    {
        let mut engine = engine;
        let state = load_state(&mut engine.0)?;
        Ok(Log { engine, state, fsync: true, view: Ghost::assume_new() })
    }

    /// TRUSTED (storage integrity): reads the entry at `index`; the engine
    /// holds exactly the entries in the view.
    #[verifier::external_body]
    fn engine_get(&mut self, index: Index) -> (r: Result<Option<Entry>>)
        ensures
            *final(self) == *old(self),
            r matches Ok(Some(e)) ==> {
                &&& 1 <= index <= old(self).view().len()
                &&& e.index == index
                &&& entry_view(e) == old(self).view()[index - 1]
            },
            r matches Ok(None) ==> !(1 <= index <= old(self).view().len()),
    {
        self.engine.0.get(&Key::Entry(index).encode())?.map(|v| Entry::decode(&v)).transpose()
    }

    /// TRUSTED (storage integrity): writes an entry at its index, which is at
    /// most one past the last; the engine then holds it there.
    #[verifier::external_body]
    fn engine_set_entry(&mut self, e: &Entry) -> (r: Result<()>)
        requires
            1 <= e.index <= old(self).view().len() + 1,
        ensures
            r is Ok ==> {
                &&& final(self).state == old(self).state
                &&& final(self).fsync == old(self).fsync
                &&& final(self).view() == (if e.index <= old(self).view().len() {
                    old(self).view().update(e.index - 1, entry_view(*e))
                } else {
                    old(self).view().push(entry_view(*e))
                })
            },
    {
        self.engine.0.set(&Key::Entry(e.index).encode(), e.encode())
    }

    /// TRUSTED (storage integrity): deletes the entries from `from` through
    /// the last index (in increasing order); the engine then holds the
    /// entries before `from`.
    #[verifier::external_body]
    fn engine_truncate(&mut self, from: Index) -> (r: Result<()>)
        requires
            1 <= from <= old(self).view().len() + 1,
            old(self).state.last_index as nat == old(self).view().len(),
        ensures
            r is Ok ==> {
                &&& final(self).state == old(self).state
                &&& final(self).fsync == old(self).fsync
                &&& final(self).view() == old(self).view().take(from - 1)
            },
    {
        let mut index = from;
        while index <= self.state.last_index {
            self.engine.0.delete(&Key::Entry(index).encode())?;
            index += 1;
        }
        Ok(())
    }

    /// TRUSTED (storage integrity): flushes the engine; entries unchanged.
    #[verifier::external_body]
    fn engine_flush(&mut self) -> (r: Result<()>)
        ensures
            r is Ok ==> *final(self) == *old(self),
    {
        self.engine.0.flush()
    }

    /// TRUSTED (storage integrity): persists the term and vote; entries
    /// unchanged.
    #[verifier::external_body]
    fn engine_set_term_vote(&mut self, term: Term, vote: Option<NodeID>) -> (r: Result<()>)
        ensures
            r is Ok ==> *final(self) == *old(self),
    {
        self.engine.0.set(&Key::TermVote.encode(), bincode::serialize(&(term, vote)))
    }

    /// TRUSTED (storage integrity): persists the commit index and term;
    /// entries unchanged.
    #[verifier::external_body]
    fn engine_set_commit(&mut self, index: Index, term: Term) -> (r: Result<()>)
        ensures
            r is Ok ==> *final(self) == *old(self),
    {
        self.engine.0.set(&Key::CommitIndex.encode(), bincode::serialize(&(index, term)))
    }

    // --- Verified methods ----------------------------------------------

    /// Controls whether to fsync writes. Disabling this may violate Raft
    /// guarantees, see comment on fsync attribute.
    pub fn enable_fsync(&mut self, fsync: bool)
        ensures
            final(self).view() == old(self).view(),
            final(self).term() == old(self).term(),
            final(self).vote() == old(self).vote(),
            final(self).commit_index() == old(self).commit_index(),
            old(self).inv() ==> final(self).inv(),
    {
        self.fsync = fsync
    }

    /// Returns the commit index and term. The term is the term of the entry
    /// at the commit index (if any).
    pub fn get_commit_index(&self) -> (r: (Index, Term))
        requires
            self.inv(),
        ensures
            r.0 == self.commit_index(),
            r.0 <= self.view().len(),
            r.0 >= 1 ==> r.1 as nat == self.view()[r.0 - 1].term,
    {
        (self.state.commit_index, self.state.commit_term)
    }

    /// Returns the last log index and term.
    pub fn get_last_index(&self) -> (r: (Index, Term))
        requires
            self.inv(),
        ensures
            r.0 as nat == self.view().len(),
            r.1 as nat == last_term(self.view()),
    {
        (self.state.last_index, self.state.last_term)
    }

    /// Returns the current term (0 if none) and vote.
    pub fn get_term_vote(&self) -> (r: (Term, Option<NodeID>))
        ensures
            r.0 == self.term(),
            r.1 == self.vote(),
    {
        (self.state.term, self.state.vote)
    }

    /// Stores the current term and cast vote (if any). Enforces that the term
    /// does not regress, and that we only vote for one node in a term. append()
    /// will use this term, and splice() can't write entries beyond it.
    ///
    /// Panics (`fault`) iff the term is 0, regresses, or the vote changes
    /// within the term.
    pub(in crate::raft::verified) fn set_term_vote(&mut self, term: Term, vote: Option<NodeID>) -> (r: Result<()>)
        requires
            old(self).inv(),
        ensures
            r is Ok ==> {
                &&& final(self).inv()
                &&& final(self).view() == old(self).view()
                &&& final(self).commit_index() == old(self).commit_index()
                &&& final(self).term() == term
                &&& final(self).vote() == vote
                &&& term >= 1 && term >= old(self).term()
                &&& term == old(self).term() ==> old(self).vote() is None || vote == old(self).vote()
            },
    {
        let state = match set_term_vote_state(&self.state, term, vote) {
            TermVoteCheck::ZeroTerm => fault(Fault::SetTermZero),
            TermVoteCheck::TermRegression => fault(Fault::TermRegression(self.state.term, term)),
            TermVoteCheck::VoteChange => fault(Fault::VoteChange),
            TermVoteCheck::Noop => return Ok(()),
            TermVoteCheck::Update(state) => state,
        };
        self.engine_set_term_vote(term, vote)?;
        // Always fsync, even with Log::fsync = false. Term changes are rare, so
        // this doesn't materially affect performance, and double voting could
        // lead to multiple leaders and split brain which is really bad.
        self.engine_flush()?;
        self.state = state;
        Ok(())
    }

    /// Appends a command to the log at the current term, and flushes it to
    /// disk, returning its index. None implies a noop command, typically after
    /// Raft leader changes.
    ///
    /// Panics (`fault`) iff the term is 0 or the log is full.
    pub(in crate::raft::verified) fn append(&mut self, command: Option<Vec<u8>>) -> (r: Result<Index>)
        requires
            old(self).inv(),
        ensures
            r matches Ok(index) ==> {
                &&& final(self).inv()
                &&& index as nat == old(self).view().len() + 1
                &&& final(self).view() == old(self).view().push(AEntry {
                    term: old(self).term() as nat,
                    cmd: cmd_view(command),
                })
                &&& final(self).term() == old(self).term()
                &&& final(self).vote() == old(self).vote()
                &&& final(self).commit_index() == old(self).commit_index()
                &&& old(self).term() >= 1
            },
    {
        let (index, state) = match append_state(&self.state) {
            AppendCheck::ZeroTerm => fault(Fault::AppendTermZero),
            AppendCheck::IndexOverflow => fault(Fault::IndexOverflow),
            AppendCheck::Append(index, state) => (index, state),
        };
        let ghost cmd = cmd_view(command);
        let entry = Entry { index, term: state.last_term, command };
        self.engine_set_entry(&entry)?;
        if self.fsync {
            self.engine_flush()?;
        }
        self.state = state;
        proof {
            let v = self.view@;
            assert(v.len() >= 1);
            assert(last_term(v) == v[v.len() - 1].term);
            assert(v[v.len() - 1] == AEntry { term: state.term as nat, cmd });
        }
        Ok(index)
    }

    /// Commits entries up to and including the given index. The index must
    /// exist and be at or after the current commit index.
    ///
    /// Panics (`fault`) iff the entry does not exist or the index regresses.
    pub(in crate::raft::verified) fn commit(&mut self, index: Index) -> (r: Result<Index>)
        requires
            old(self).inv(),
        ensures
            r matches Ok(i) ==> {
                &&& i == index
                &&& final(self).inv()
                &&& final(self).view() == old(self).view()
                &&& final(self).term() == old(self).term()
                &&& final(self).vote() == old(self).vote()
                &&& final(self).commit_index() == index
                &&& old(self).commit_index() <= index <= old(self).view().len()
            },
    {
        let entry = match self.engine_get(index)? {
            Some(entry) => entry,
            None => fault(Fault::CommitMissing(index)),
        };
        let state = match commit_state(&self.state, entry.index, entry.term) {
            CommitCheck::Regression => {
                fault(Fault::CommitRegression(self.state.commit_index, entry.index))
            }
            CommitCheck::Noop => return Ok(index),
            CommitCheck::Commit(state) => state,
        };
        self.engine_set_commit(index, entry.term)?;
        // NB: the commit index doesn't need to be fsynced, since the entries
        // are fsynced and the commit index can be recovered from the quorum.
        self.state = state;
        Ok(index)
    }

    /// Fetches an entry at an index, or None if it does not exist.
    pub fn get(&mut self, index: Index) -> (r: Result<Option<Entry>>)
        ensures
            *final(self) == *old(self),
            r matches Ok(Some(e)) ==> {
                &&& 1 <= index <= old(self).view().len()
                &&& e.index == index
                &&& entry_view(e) == old(self).view()[index - 1]
            },
            r matches Ok(None) ==> !(1 <= index <= old(self).view().len()),
    {
        self.engine_get(index)
    }

    /// Checks if the log contains an entry with the given index and term.
    pub fn has(&mut self, index: Index, term: Term) -> (r: Result<bool>)
        requires
            old(self).inv(),
        ensures
            *final(self) == *old(self),
            r matches Ok(b) ==> b == old(self).has_spec(index, term),
    {
        // Fast path: check against last_index. This is the common case when
        // followers process appends or heartbeats.
        if index == 0 || index > self.state.last_index {
            return Ok(false);
        }
        if index == self.state.last_index && term == self.state.last_term {
            return Ok(true);
        }
        match self.engine_get(index)? {
            Some(e) => Ok(e.term == term),
            None => Ok(false),
        }
    }

    /// Reads up to `max` consecutive entries starting at `from` (which must
    /// be at least 1), stopping at the end of the log: a window of the log
    /// starting at `from`.
    pub fn read_range(&mut self, from: Index, max: usize) -> (r: Result<Vec<Entry>>)
        requires
            old(self).inv(),
            from >= 1,
        ensures
            *final(self) == *old(self),
            r matches Ok(es) ==> {
                &&& es@.len() <= max
                &&& forall|j: int| 0 <= j < es@.len() ==> (#[trigger] es@[j]).index as int == from + j
                &&& from - 1 + es@.len() <= old(self).view().len()
                    || (es@.len() == 0 && from - 1 > old(self).view().len())
                &&& from - 1 <= old(self).view().len() ==> entries_view(es@)
                    == old(self).view().subrange(from - 1, from - 1 + es@.len())
            },
    {
        let mut es: Vec<Entry> = Vec::new();
        let mut off: usize = 0;
        while off < max
            invariant
                self.inv(),
                *self == *old(self),
                from >= 1,
                off == es@.len(),
                off <= max,
                off > 0 ==> from - 1 + off <= self.view().len(),
                forall|j: int| 0 <= j < es@.len() ==> (#[trigger] es@[j]).index as int == from + j,
                forall|j: int| 0 <= j < es@.len() ==>
                    entry_view(#[trigger] es@[j]) == self.view()[from - 1 + j],
            decreases max - off,
        {
            if off as u64 > u64::MAX - from {
                break;
            }
            let index = from + off as u64;
            if index > self.state.last_index {
                break;
            }
            let e = match self.engine_get(index)? {
                Some(e) => e,
                None => break,
            };
            es.push(e);
            off += 1;
        }
        proof {
            if from - 1 <= self.view().len() {
                assert(entries_view(es@) =~= self.view().subrange(from - 1, from - 1 + es@.len()));
            }
        }
        Ok(es)
    }

    /// The number of leading entries of the batch that are already in the
    /// log with the same term (and, checked at runtime, the same command).
    /// The batch is contiguous with nonzero first index.
    ///
    /// Panics (`fault`) iff an entry with matching index and term has a
    /// different command (a violation of the log-matching invariant).
    #[verifier::spinoff_prover]
    #[verifier::rlimit(240)]
    fn count_present(&mut self, es: &Vec<Entry>) -> (r: Result<usize>)
        requires
            old(self).inv(),
            es@.len() > 0,
            es@[0].index >= 1,
            entries_contiguous(es@),
        ensures
            *final(self) == *old(self),
            r matches Ok(skip) ==> {
                let b = es@[0].index - 1;
                &&& skip <= es@.len()
                &&& forall|j: int| 0 <= j < skip ==>
                    b + j < old(self).view().len() && old(self).view()[b + j] == entry_view(#[trigger] es@[j])
                &&& skip < es@.len() ==> b + skip >= old(self).view().len()
                    || old(self).view()[b + skip].term != es@[skip as int].term as nat
            },
    {
        let ghost b = es@[0].index - 1;
        let mut k: usize = 0;
        while k < es.len()
            invariant
                self.inv(),
                *self == *old(self),
                es@.len() > 0,
                es@[0].index >= 1,
                entries_contiguous(es@),
                k <= es@.len(),
                b == es@[0].index - 1,
                forall|j: int| 0 <= j < k ==>
                    b + j < self.view().len() && self.view()[b + j] == entry_view(#[trigger] es@[j]),
            decreases es@.len() - k,
        {
            proof {
                lemma_contiguous_index(es@, k as int);
            }
            let e = &es[k];
            match self.engine_get(e.index)? {
                Some(existing) => {
                    if existing.term != e.term {
                        return Ok(k);
                    }
                    if !cmd_eq(&existing.command, &e.command) {
                        fault(Fault::CommandMismatch(existing));
                    }
                    k += 1;
                }
                None => return Ok(k),
            }
        }
        Ok(k)
    }

    /// Splices a set of entries into the log and flushes it to disk. New
    /// indexes will be appended. Overlapping indexes with the same term must be
    /// equal and will be ignored. Overlapping indexes with different terms will
    /// truncate the existing log at the first conflict and then splice the new
    /// entries.
    ///
    /// The entries must have contiguous indexes and equal/increasing terms, and
    /// the first entry must be in the range [1,last_index+1] with a term at or
    /// above the previous (base) entry's term and at or below the current term;
    /// otherwise this panics (`fault`), as it does for a batch that would
    /// write at or below the commit index.
    ///
    /// The resulting view is the safety model's `splice` of the batch at its
    /// base index, i.e. the log is unchanged if the batch is already present,
    /// and otherwise equals the prefix before the batch followed by the batch.
    // The generous rlimit is headroom, not need: this query is seed-sensitive
    // (unrelated edits elsewhere in the module have flipped it at the default
    // limit), but verifies quickly when it succeeds.
    #[verifier::rlimit(600)]
    pub(in crate::raft::verified) fn splice(&mut self, entries: Vec<Entry>) -> (r: Result<Index>)
        requires
            old(self).inv(),
        ensures
            r matches Ok(last) ==> {
                &&& final(self).inv()
                &&& final(self).term() == old(self).term()
                &&& final(self).vote() == old(self).vote()
                &&& final(self).commit_index() == old(self).commit_index()
                &&& last as nat == final(self).view().len()
                &&& entries@.len() == 0 ==> final(self).view() == old(self).view()
                &&& entries@.len() > 0 ==> {
                    &&& entries_contiguous(entries@)
                    &&& entries@[0].index >= 1
                    &&& entries@[0].index - 1 <= old(self).view().len()
                    &&& final(self).view() == splice(old(self).view(), (entries@[0].index - 1) as nat, entries_view(entries@))
                }
            },
    {
        if entries.len() == 0 {
            return Ok(self.state.last_index); // empty input is noop
        }

        // Check that the entries are well-formed (nonzero first index/term,
        // contiguous indexes, monotone terms).
        match check_splice_entries(&entries) {
            SpliceEntriesCheck::Empty => fault(Fault::SpliceZeroIndexOrTerm), // unreachable
            SpliceEntriesCheck::ZeroIndexOrTerm => fault(Fault::SpliceZeroIndexOrTerm),
            SpliceEntriesCheck::NonContiguous => fault(Fault::SpliceNonContiguous),
            SpliceEntriesCheck::TermRegression => fault(Fault::SpliceTermRegression),
            SpliceEntriesCheck::WellFormed => {}
        }
        let first_index = entries[0].index;
        let first_term = entries[0].term;
        let last_index = entries[entries.len() - 1].index;
        let lterm = entries[entries.len() - 1].term;
        let ghost b = (first_index - 1) as nat;
        let ghost old_view = self.view@;
        let ghost aentries = entries_view(entries@);
        proof {
            lemma_contiguous_index(entries@, entries@.len() - 1);
            assert(aentries.len() == entries@.len());
        }

        // Check that the entries connect to the existing log (if any), and that
        // the term doesn't regress. first_index - 1 can't underflow since
        // first_index > 0.
        let base_term = match self.engine_get(first_index - 1)? {
            Some(base) => Some(base.term),
            None => None,
        };
        match check_splice_connect(&self.state, first_index, first_term, lterm, base_term) {
            SpliceConnectCheck::TermBeyondCurrent => {
                fault(Fault::SpliceTermBeyondCurrent(lterm, self.state.term))
            }
            SpliceConnectCheck::BaseTermRegression => {
                let bt = match base_term {
                    Some(bt) => bt,
                    None => 0, // unreachable
                };
                fault(Fault::SpliceBaseTermRegression(bt, first_term))
            }
            SpliceConnectCheck::NoTouch => fault(Fault::SpliceNoTouch(first_index)),
            SpliceConnectCheck::Connects => {}
        }
        assert(b <= old_view.len());

        // Skip entries that are already in the log.
        let skip = self.count_present(&entries)?;

        // If all entries already exist then we're done.
        if skip == entries.len() {
            proof {
                assert(splice_is_noop(old_view, b, aentries));
            }
            return Ok(self.state.last_index);
        }
        proof {
            lemma_contiguous_index(entries@, skip as int);
            assert(!splice_is_noop(old_view, b, aentries)) by {
                if b + aentries.len() <= old_view.len() {
                    assert(old_view[b + skip] != aentries[skip as int]);
                }
            }
        }
        let write_from = entries[skip].index;

        // The transition refuses to write below the commit index, since
        // committed entries must be immutable.
        let state = match splice_state(&self.state, write_from, last_index, lterm) {
            None => fault(Fault::SpliceBelowCommit),
            Some(state) => state,
        };

        // Write the entries that weren't already in the log.
        let mut k: usize = skip;
        while k < entries.len()
            invariant
                skip <= k <= entries@.len(),
                entries@.len() > 0,
                entries_contiguous(entries@),
                b == entries@[0].index - 1,
                b <= old_view.len(),
                aentries == entries_view(entries@),
                self.state == old(self).state,
                self.fsync == old(self).fsync,
                b + k > old_view.len() ==> self.view().len() == b + k,
                b + k <= old_view.len() ==> self.view().len() == old_view.len(),
                forall|p: int| 0 <= p < b + skip ==> #[trigger] self.view()[p] == old_view[p],
                forall|j: int| 0 <= j < skip ==> b + j < old_view.len() && old_view[b + j] == #[trigger] aentries[j],
                forall|j: int| skip <= j < k ==> self.view()[b + j] == #[trigger] aentries[j],
                forall|p: int| b + k <= p < old_view.len() ==> #[trigger] self.view()[p] == old_view[p],
            decreases entries@.len() - k,
        {
            proof {
                lemma_contiguous_index(entries@, k as int);
            }
            self.engine_set_entry(&entries[k])?;
            k += 1;
        }

        // Remove the tail of the old log if any.
        if last_index < self.state.last_index {
            self.engine_truncate(last_index + 1)?;
        }
        if self.fsync {
            self.engine_flush()?;
        }
        self.state = state;
        proof {
            let n = aentries.len();
            assert(self.view@.len() == b + n);
            assert forall|p: int| 0 <= p < b + n implies #[trigger] self.view@[p] == (old_view.subrange(0, b as int) + aentries)[p] by {
                if p < b {
                    assert(self.view@[p] == old_view[p]);
                } else {
                    assert(self.view@[p] == aentries[p - b]);
                }
            }
            assert(self.view@ =~= old_view.subrange(0, b as int) + aentries);
            assert(self.view@ == splice(old_view, b, aentries));
            // The invariant: last term, term bounds, monotonicity.
            assert(self.view@[b + n - 1].term == lterm as nat) by {
                assert(aentries[n - 1] == entry_view(entries@[n - 1]));
            }
            assert(last_term(self.view@) == lterm as nat);
            assert forall|j: int| 0 <= j < self.view@.len() implies (#[trigger] self.view@[j]).term >= 1 by {
                if j >= b {
                    lemma_monotone_terms(entries@, 0, j - b);
                }
            }
            assert forall|j1: int, j2: int| 0 <= j1 <= j2 < self.view@.len() implies
                (#[trigger] self.view@[j1]).term <= (#[trigger] self.view@[j2]).term by {
                if j1 >= b {
                    lemma_monotone_terms(entries@, j1 - b, j2 - b);
                } else if j2 >= b {
                    // j1 is in the old prefix, j2 in the batch: the base
                    // entry (if any) is at most the first term.
                    lemma_monotone_terms(entries@, 0, j2 - b);
                    if b >= 1 {
                        assert(old_view[j1].term <= old_view[b - 1].term);
                        assert(old_view[b - 1].term == base_term.unwrap() as nat);
                    }
                }
            }
            assert forall|j: int| 0 <= j < self.view@.len() implies (#[trigger] self.view@[j]).term <= self.state.term as nat by {
                if j >= b {
                    lemma_monotone_terms(entries@, j - b, n - 1);
                }
            }
        }
        Ok(last_index)
    }

    /// Reads up to `max` committed entries starting after `after` (i.e. from
    /// index `after + 1`), stopping at the commit index: the next chunk of
    /// the committed prefix of the log. Returns as many entries as are
    /// available up to `max`, so the result is empty iff `after` is at or
    /// beyond the commit index.
    ///
    /// This is the verified apply path: the returned entries are pinned to
    /// the committed prefix of the log's ghost view, so a caller that feeds
    /// them to the state machine in order applies exactly that prefix — the
    /// prefix the safety model's state machine safety theorem is about.
    ///
    /// Panics (`fault`) iff the engine contradicts the storage-integrity
    /// specification (a committed entry is missing), which the proof shows
    /// cannot happen when that trusted specification holds.
    pub fn read_committed(&mut self, after: Index, max: usize) -> (r: Result<Vec<Entry>>)
        requires
            old(self).inv(),
        ensures
            *final(self) == *old(self),
            r matches Ok(es) ==> {
                &&& es@.len() <= max
                &&& after >= old(self).commit_index() ==> es@.len() == 0
                &&& after < old(self).commit_index() ==> {
                    &&& after + es@.len() <= old(self).commit_index()
                    &&& es@.len() == max || after + es@.len() == old(self).commit_index()
                    &&& forall|j: int| 0 <= j < es@.len() ==>
                        (#[trigger] es@[j]).index as int == after + 1 + j
                    &&& entries_view(es@) == old(self).view().subrange(after as int, after + es@.len())
                }
            },
    {
        let mut es: Vec<Entry> = Vec::new();
        let commit_index = self.state.commit_index;
        if after >= commit_index {
            return Ok(es);
        }
        let avail = commit_index - after;
        let count: u64 = if (max as u64) < avail { max as u64 } else { avail };
        let mut k: u64 = 0;
        while k < count
            invariant
                self.inv(),
                *self == *old(self),
                commit_index == self.commit_index(),
                after < commit_index,
                count <= commit_index - after,
                count <= max as u64,
                k <= count,
                k == es@.len(),
                forall|j: int| 0 <= j < es@.len() ==>
                    (#[trigger] es@[j]).index as int == after + 1 + j,
                forall|j: int| 0 <= j < es@.len() ==>
                    entry_view(#[trigger] es@[j]) == self.view()[after + j],
            decreases count - k,
        {
            let index = after + 1 + k;
            let e = match self.engine_get(index)? {
                Some(e) => e,
                // Unreachable: 1 <= index <= commit_index <= view().len() by
                // `inv`, so the rim's specification puts the entry there.
                None => fault(Fault::CommittedEntryMissing(index)),
            };
            es.push(e);
            k += 1;
        }
        proof {
            assert(entries_view(es@) =~= self.view().subrange(after as int, after + es@.len()));
        }
        Ok(es)
    }
}

/// In a contiguous batch, entry k has index `first + k`.
pub proof fn lemma_contiguous_index(es: Seq<Entry>, k: int)
    requires
        entries_contiguous(es),
        0 <= k < es.len(),
    ensures
        es[k].index == es[0].index + k,
    decreases k,
{
    if k > 0 {
        lemma_contiguous_index(es, k - 1);
    }
}

/// In a term-monotone batch, terms are nondecreasing across any two positions.
proof fn lemma_monotone_terms(es: Seq<Entry>, j1: int, j2: int)
    requires
        entries_terms_monotone(es),
        0 <= j1 <= j2 < es.len(),
    ensures
        es[j1].term <= es[j2].term,
    decreases j2 - j1,
{
    if j1 < j2 {
        lemma_monotone_terms(es, j1, j2 - 1);
    }
}

} // verus!

impl Log {
    /// Initializes a log using the given storage engine.
    pub fn new(engine: Box<dyn storage::Engine>) -> Result<Self> {
        Self::open(EngineBox(engine))
    }

    /// Returns the storage engine, for tests.
    #[cfg(test)]
    pub fn engine_mut(&mut self) -> &mut Box<dyn storage::Engine> {
        &mut self.engine.0
    }

    /// Consumes the log, returning its storage engine, for tests.
    #[cfg(test)]
    pub fn into_engine(self) -> Box<dyn storage::Engine> {
        self.engine.0
    }

    /// Returns an iterator over log entries in the given index range. Tests
    /// only: the runtime apply path reads through the verified
    /// `read_committed` instead, which pins the entries to the log's
    /// verified view.
    #[cfg(test)]
    pub fn scan(&mut self, range: impl RangeBounds<Index>) -> Iterator<'_> {
        let from = match range.start_bound() {
            Bound::Excluded(&index) => Bound::Excluded(Key::Entry(index).encode()),
            Bound::Included(&index) => Bound::Included(Key::Entry(index).encode()),
            Bound::Unbounded => Bound::Included(Key::Entry(0).encode()),
        };
        let to = match range.end_bound() {
            Bound::Excluded(&index) => Bound::Excluded(Key::Entry(index).encode()),
            Bound::Included(&index) => Bound::Included(Key::Entry(index).encode()),
            Bound::Unbounded => Bound::Included(Key::Entry(Index::MAX).encode()),
        };
        Iterator::new(self.engine.0.scan_dyn((from, to)))
    }

    /// Returns an iterator over entries that are ready to apply, starting after
    /// the current applied index up to the commit index. Tests only: see
    /// `scan`.
    #[cfg(test)]
    pub fn scan_apply(&mut self, applied_index: Index) -> Iterator<'_> {
        // NB: we don't assert that commit_index >= applied_index, because the
        // local commit index is not flushed to durable storage -- if lost on
        // restart, it can be recovered from the logs of a quorum.
        if applied_index >= self.state.commit_index {
            return Iterator::new(Box::new(std::iter::empty()));
        }
        self.scan(applied_index + 1..=self.state.commit_index)
    }

    /// Returns log engine status.
    pub fn status(&mut self) -> Result<storage::Status> {
        self.engine.0.status()
    }
}
/// A log entry iterator. Tests only: see `Log::scan`.
#[cfg(test)]
pub struct Iterator<'a> {
    inner: Box<dyn storage::ScanIterator + 'a>,
}

#[cfg(test)]
impl<'a> Iterator<'a> {
    fn new(inner: Box<dyn storage::ScanIterator + 'a>) -> Self {
        Self { inner }
    }
}

#[cfg(test)]
impl std::iter::Iterator for Iterator<'_> {
    type Item = Result<Entry>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|r| r.and_then(|(_, v)| Entry::decode(&v)))
    }
}

/// Most Raft tests are Goldenscripts under src/raft/testscripts.
#[cfg(test)]
mod tests {
    use std::error::Error;
    use std::fmt::Write as _;
    use std::result::Result;
    use std::str::FromStr;

    use crossbeam::channel::Receiver;
    use regex::Regex;
    use tempfile::TempDir;
    use test_each_file::test_each_path;

    use super::*;
    use crate::encoding::format::{self, Formatter as _};
    use crate::storage::engine::test as testengine;

    // Run goldenscript tests in src/raft/testscripts/log.
    test_each_path! { in "src/raft/testscripts/log" as scripts => test_goldenscript }

    fn test_goldenscript(path: &std::path::Path) {
        goldenscript::run(&mut TestRunner::new(), path).expect("goldenscript failed")
    }

    /// Runs Raft log goldenscript tests.
    struct TestRunner {
        log: Log,
        op_rx: Receiver<testengine::Operation>,
        #[allow(dead_code)]
        tempdir: TempDir,
    }

    /// Commands accepted by the TestRunner.
    #[derive(goldenscript::Command)]
    enum Command {
        /// Appends an entry to the Raft log.
        Append(
            /// The entry command. Appending a None entry is valid, and happens
            /// on leader changes.
            Option<String>,
        ),
        /// Commits a Raft log entry.
        Commit(
            /// The index to commit.
            Index,
        ),
        /// Dumps all raw Raft storage entries.
        Dump,
        /// Fetches Raft log entries.
        Get(
            /// The indexes to fetch.
            Vec<Index>,
        ),
        /// Displays the current term and vote.
        GetTerm,
        /// Checks whether index/term pairs exist.
        Has(
            /// The index/term pairs to check.
            Vec<IndexTerm>,
        ),
        /// Reloads the Raft log from storage.
        Reload,
        /// Scans a Raft log index range.
        Scan(
            /// The index range, or the full range if omitted.
            #[arg(optional)]
            IndexRange,
        ),
        /// Scans entries to apply after an index.
        ScanApply(
            /// The last applied index.
            Index,
        ),
        /// Sets the current term and optional vote.
        SetTerm(
            /// The term to set.
            Term,
            /// The node we voted for in this term, if any.
            Option<NodeID>,
        ),
        /// Splices entries into the Raft log.
        Splice(
            /// The index/term and command entries to splice.
            #[arg(optional)]
            Vec<(IndexTerm, String)>,
        ),
        /// Displays Raft log status.
        Status {
            /// Whether to include storage engine status.
            #[arg(key, optional)]
            engine: bool,
        },
    }

    /// An index and term pair parsed from INDEX@TERM.
    struct IndexTerm(Index, Term);

    impl FromStr for IndexTerm {
        type Err = Box<dyn Error>;

        fn from_str(value: &str) -> Result<Self, Self::Err> {
            let re = Regex::new(r"^(\d+)@(\d+)$").expect("invalid regex");
            let groups = re.captures(value).ok_or_else(|| format!("invalid index/term {value}"))?;
            let index = groups.get(1).unwrap().as_str().parse()?;
            let term = groups.get(2).unwrap().as_str().parse()?;
            Ok(Self(index, term))
        }
    }

    /// An index range parsed from Rust range syntax.
    #[derive(Clone, Copy)]
    struct IndexRange(Bound<Index>, Bound<Index>);

    impl Default for IndexRange {
        fn default() -> Self {
            Self(Bound::Unbounded, Bound::Unbounded)
        }
    }

    impl FromStr for IndexRange {
        type Err = Box<dyn Error>;

        fn from_str(value: &str) -> Result<Self, Self::Err> {
            let mut range = Self::default();
            let re = Regex::new(r"^(\d+)?\.\.(=)?(\d+)?").expect("invalid regex");
            let groups = re.captures(value).ok_or_else(|| format!("invalid range {value}"))?;
            if let Some(start) = groups.get(1) {
                range.0 = Bound::Included(start.as_str().parse()?);
            }
            if let Some(end) = groups.get(3) {
                let end = end.as_str().parse()?;
                range.1 = match groups.get(2) {
                    Some(_) => Bound::Included(end),
                    None => Bound::Excluded(end),
                };
            }
            Ok(range)
        }
    }

    impl RangeBounds<Index> for IndexRange {
        fn start_bound(&self) -> Bound<&Index> {
            self.0.as_ref()
        }

        fn end_bound(&self) -> Bound<&Index> {
            self.1.as_ref()
        }
    }

    impl TestRunner {
        fn new() -> Self {
            // Use both a BitCask and a Memory engine, and mirror operations
            // across them. Emit write events to op_tx.
            let (op_tx, op_rx) = crossbeam::channel::unbounded();
            let tempdir = TempDir::with_prefix("toydb").expect("tempdir failed");
            let bitcask =
                storage::BitCask::new(tempdir.path().join("bitcask")).expect("bitcask failed");
            let memory = storage::Memory::new();
            let engine = testengine::Emit::new(testengine::Mirror::new(bitcask, memory), op_tx);
            let log = Log::new(Box::new(engine)).expect("log failed");
            Self { log, op_rx, tempdir }
        }
    }

    impl goldenscript::Runner for TestRunner {
        type Command = Command;

        fn run(
            &mut self,
            command: &Command,
            context: &goldenscript::Context,
        ) -> Result<String, Box<dyn Error>> {
            let mut output = String::new();

            match command {
                Command::Append(command) => {
                    let command = command.as_ref().map(|command| command.as_bytes().to_vec());
                    let index = self.log.append(command)?;
                    let entry = self.log.get(index)?.expect("entry not found");
                    let fmtentry = format::Raft::<format::Raw>::entry(&entry);
                    writeln!(output, "append → {fmtentry}")?;
                }

                &Command::Commit(index) => {
                    let index = self.log.commit(index)?;
                    let entry = self.log.get(index)?.expect("entry not found");
                    let fmtentry = format::Raft::<format::Raw>::entry(&entry);
                    writeln!(output, "commit → {fmtentry}")?;
                }

                Command::Dump => {
                    let range = (std::ops::Bound::Unbounded, std::ops::Bound::Unbounded);
                    let mut scan = self.log.engine_mut().scan_dyn(range);
                    while let Some((key, value)) = scan.next().transpose()? {
                        let fmtkv = format::Raft::<format::Raw>::key_value(&key, &value);
                        let rawkv = format::Raw::key_value(&key, &value);
                        writeln!(output, "{fmtkv} [{rawkv}]")?;
                    }
                }

                Command::Get(indexes) => {
                    for &index in indexes {
                        let entry = self.log.get(index)?;
                        let fmtentry = entry
                            .as_ref()
                            .map(format::Raft::<format::Raw>::entry)
                            .unwrap_or("None".to_string());
                        writeln!(output, "{fmtentry}")?;
                    }
                }

                Command::GetTerm => {
                    let (term, vote) = self.log.get_term_vote();
                    let vote = vote.map(|v| v.to_string()).unwrap_or("None".to_string());
                    writeln!(output, "term={term} vote={vote}")?;
                }

                Command::Has(indexes) => {
                    for &IndexTerm(index, term) in indexes {
                        let has = self.log.has(index, term)?;
                        writeln!(output, "{has}")?;
                    }
                }

                Command::Reload => {
                    // To get owned access to the inner engine, temporarily
                    // replace it with an empty memory engine.
                    let engine =
                        std::mem::replace(self.log.engine_mut(), Box::new(storage::Memory::new()));
                    self.log = Log::new(engine)?;
                }

                &Command::Scan(range) => {
                    let mut scan = self.log.scan(range);
                    while let Some(entry) = scan.next().transpose()? {
                        let fmtentry = format::Raft::<format::Raw>::entry(&entry);
                        writeln!(output, "{fmtentry}")?;
                    }
                }

                &Command::ScanApply(applied_index) => {
                    let mut scan = self.log.scan_apply(applied_index);
                    while let Some(entry) = scan.next().transpose()? {
                        let fmtentry = format::Raft::<format::Raw>::entry(&entry);
                        writeln!(output, "{fmtentry}")?;
                    }
                }

                &Command::SetTerm(term, vote) => {
                    self.log.set_term_vote(term, vote)?;
                }

                Command::Splice(values) => {
                    let mut entries = Vec::new();
                    for &(IndexTerm(index, term), ref value) in values {
                        let command = match value.as_str() {
                            "" => None,
                            value => Some(value.as_bytes().to_vec()),
                        };
                        entries.push(Entry { index, term, command });
                    }
                    let index = self.log.splice(entries)?;
                    let entry = self.log.get(index)?.expect("entry not found");
                    let fmtentry = format::Raft::<format::Raw>::entry(&entry);
                    writeln!(output, "splice → {fmtentry}")?;
                }

                &Command::Status { engine } => {
                    let (term, vote) = self.log.get_term_vote();
                    let (last_index, last_term) = self.log.get_last_index();
                    let (commit_index, commit_term) = self.log.get_commit_index();
                    let vote = vote.map(|id| id.to_string()).unwrap_or("None".to_string());
                    write!(
                        output,
                        "term={term} last={last_index}@{last_term} commit={commit_index}@{commit_term} vote={vote}",
                    )?;
                    if engine {
                        write!(output, " engine={:#?}", self.log.status()?)?;
                    }
                    writeln!(output)?;
                }
            }

            // If requested, output engine operations.
            let mut tags = context.tags.clone();
            if tags.remove("ops") {
                while let Ok(op) = self.op_rx.try_recv() {
                    match op {
                        testengine::Operation::Delete { key } => {
                            let fmtkey = format::Raft::<format::Raw>::key(&key);
                            let rawkey = format::Raw::key(&key);
                            writeln!(output, "engine delete {fmtkey} [{rawkey}]")?
                        }
                        testengine::Operation::Flush => writeln!(output, "engine flush")?,
                        testengine::Operation::Set { key, value } => {
                            let fmtkv = format::Raft::<format::Raw>::key_value(&key, &value);
                            let rawkv = format::Raw::key_value(&key, &value);
                            writeln!(output, "engine set {fmtkv} [{rawkv}]")?
                        }
                    }
                }
            }

            if let Some(tag) = tags.iter().next() {
                return Err(format!("unknown tag {tag}").into());
            }

            Ok(output)
        }

        fn end_command(
            &mut self,
            _: &Command,
            _: &goldenscript::Context,
        ) -> Result<String, Box<dyn Error>> {
            // Drain any remaining engine operations.
            while self.op_rx.try_recv().is_ok() {}
            Ok(String::new())
        }
    }
}
