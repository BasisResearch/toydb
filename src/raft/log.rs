use std::ops::{Bound, RangeBounds};

use serde::{Deserialize, Serialize};

use super::{NodeID, Term};
use crate::encoding::{self, Key as _, Value as _, bincode};
use crate::error::Result;
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

// --- Verus-verified core of the Raft log state machine ----------------------
//
// The documented log invariants (see the `Log` doc comment below) are enforced
// by a small set of precondition checks and in-memory state transitions:
// append always writes at `last_index + 1` in the current term, the commit
// index never regresses, and splice rejects batches that are non-contiguous,
// term-regressing, disconnected from the existing log, or below the commit
// index. The functions below are that core, extracted into pure, verified
// code over `LogState` (the mutable in-memory fields of `Log`):
//
// * Every checked precondition is proven to hold exactly when the verdict says
//   so (e.g. `CommitCheck::Regression` is returned iff the index regresses),
//   so the `Log` methods panic in precisely the documented cases.
// * Every state transition is proven to compute the new state field-by-field:
//   `append_state` yields index `last_index + 1` at term `term` (contiguity,
//   current-term append), `commit_state` yields a strictly larger commit index
//   (no commit regression), and `splice_state` refuses to touch entries at or
//   below the commit index.
// * Each transition preserves the state invariant `wf` — entry terms at or
//   below the current term, and the commit index at or below the last index —
//   where `wf` can be preserved. (`Log::new` loads state from disk, which is
//   unverified: with fsync disabled a crash can legitimately leave the commit
//   index ahead of the last index, so `wf` is preserved rather than assumed.)
//
// What stays unverified (and trusted): the storage engine, serialization, the
// on-disk log contents, and the splice scan that skips already-present
// entries. `Log` routes every in-memory state change through these functions,
// so the bookkeeping the invariants are stated over is verified even though
// disk I/O is not. `verus!` erases all specs and proofs to the plain `fn`
// bodies under a normal `cargo build`.
use vstd::prelude::*;

verus! {

/// The in-memory Raft log state: the mutable fields of `Log`. All `Log` state
/// changes go through the verified transitions below.
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

/// The state invariant: entry terms are at or below the current term, and the
/// committed prefix is within the log. Every transition preserves this (see
/// the caveat on `Log::new` in the section comment above).
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
        TermVoteCheck::Noop => term == st.term && vote == st.vote,
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

/// A spliced batch of (index, term) pairs has contiguous indexes.
pub open spec fn entries_contiguous(pairs: Seq<(Index, Term)>) -> bool {
    forall|i: int| #![trigger pairs[i]] 0 < i < pairs.len() ==> pairs[i].0 == pairs[i - 1].0 + 1
}

/// A spliced batch of (index, term) pairs has equal or increasing terms.
pub open spec fn entries_terms_monotone(pairs: Seq<(Index, Term)>) -> bool {
    forall|i: int| #![trigger pairs[i]] 0 < i < pairs.len() ==> pairs[i].1 >= pairs[i - 1].1
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

/// Verified well-formedness check for a spliced batch, as (index, term) pairs:
/// nonzero first index and term, contiguous indexes, and monotone terms.
/// (Clippy allows: Verus wants `&Vec` and `len() == 0`, which vstd specs.)
#[allow(clippy::ptr_arg, clippy::len_zero)]
pub fn check_splice_entries(pairs: &Vec<(Index, Term)>) -> (r: SpliceEntriesCheck)
    ensures match r {
        SpliceEntriesCheck::Empty => pairs@.len() == 0,
        SpliceEntriesCheck::ZeroIndexOrTerm => {
            pairs@.len() > 0 && (pairs@[0].0 == 0 || pairs@[0].1 == 0)
        },
        SpliceEntriesCheck::NonContiguous => !entries_contiguous(pairs@),
        SpliceEntriesCheck::TermRegression => !entries_terms_monotone(pairs@),
        SpliceEntriesCheck::WellFormed => {
            &&& pairs@.len() > 0
            &&& pairs@[0].0 > 0 && pairs@[0].1 > 0
            &&& entries_contiguous(pairs@)
            &&& entries_terms_monotone(pairs@)
        },
    },
{
    if pairs.len() == 0 {
        return SpliceEntriesCheck::Empty;
    }
    if pairs[0].0 == 0 || pairs[0].1 == 0 {
        return SpliceEntriesCheck::ZeroIndexOrTerm;
    }
    let mut i: usize = 1;
    while i < pairs.len()
        invariant
            1 <= i <= pairs@.len(),
            forall|j: int| #![trigger pairs@[j]] 0 < j < i ==> pairs@[j].0 == pairs@[j - 1].0 + 1,
        decreases pairs@.len() - i,
    {
        // An index at u64::MAX can't have a successor, so the batch is not
        // contiguous (and computing `+ 1` would overflow).
        if pairs[i - 1].0 == u64::MAX || pairs[i].0 != pairs[i - 1].0 + 1 {
            assert(pairs@[i as int].0 != pairs@[i as int - 1].0 + 1);
            return SpliceEntriesCheck::NonContiguous;
        }
        i += 1;
    }
    let mut i: usize = 1;
    while i < pairs.len()
        invariant
            1 <= i <= pairs@.len(),
            forall|j: int| #![trigger pairs@[j]] 0 < j < i ==> pairs@[j].1 >= pairs@[j - 1].1,
        decreases pairs@.len() - i,
    {
        if pairs[i].1 < pairs[i - 1].1 {
            assert(pairs@[i as int].1 < pairs@[i as int - 1].1);
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

} // verus!

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
/// The Raft log has the following invariants:
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
    /// generic type parameters throughout Raft.
    pub engine: Box<dyn storage::Engine>,
    /// The in-memory state (term, vote, last and commit index/term). Only
    /// mutated via the verified transitions in the `verus!` block above, which
    /// enforce the log invariants over it.
    state: LogState,
    /// If true, fsync entries to disk when appended. This is mandated by Raft,
    /// but comes with a hefty performance penalty (especially since we don't
    /// optimize for it by batching entries before fsyncing). Disabling it will
    /// yield much better write performance, but may lose data on crashes, which
    /// in some scenarios can cause log entries to become "uncommitted" and
    /// state machines diverging.
    fsync: bool,
}

impl Log {
    /// Initializes a log using the given storage engine.
    pub fn new(mut engine: Box<dyn storage::Engine>) -> Result<Self> {
        // Load some initial in-memory state from disk.
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

        let fsync = true; // fsync by default
        // NB: this state is loaded from unverified storage, so the verified
        // transitions preserve the `wf` invariant rather than assume it: with
        // fsync disabled, a crash can leave the commit index ahead of the log.
        let state = LogState { term, vote, last_index, last_term, commit_index, commit_term };
        Ok(Self { engine, state, fsync })
    }

    /// Controls whether to fsync writes. Disabling this may violate Raft
    /// guarantees, see comment on fsync attribute.
    pub fn enable_fsync(&mut self, fsync: bool) {
        self.fsync = fsync
    }

    /// Returns the commit index and term.
    pub fn get_commit_index(&self) -> (Index, Term) {
        (self.state.commit_index, self.state.commit_term)
    }

    /// Returns the last log index and term.
    pub fn get_last_index(&self) -> (Index, Term) {
        (self.state.last_index, self.state.last_term)
    }

    /// Returns the current term (0 if none) and vote.
    pub fn get_term_vote(&self) -> (Term, Option<NodeID>) {
        (self.state.term, self.state.vote)
    }

    /// Stores the current term and cast vote (if any). Enforces that the term
    /// does not regress, and that we only vote for one node in a term. append()
    /// will use this term, and splice() can't write entries beyond it.
    pub fn set_term_vote(&mut self, term: Term, vote: Option<NodeID>) -> Result<()> {
        // The verified transition enforces term/vote invariants.
        let state = match set_term_vote_state(&self.state, term, vote) {
            TermVoteCheck::ZeroTerm => panic!("can't set term 0"),
            TermVoteCheck::TermRegression => {
                panic!("term regression {} → {}", self.state.term, term)
            }
            TermVoteCheck::VoteChange => panic!("can't change vote"),
            TermVoteCheck::Noop => return Ok(()),
            TermVoteCheck::Update(state) => state,
        };
        self.engine.set(&Key::TermVote.encode(), bincode::serialize(&(term, vote)))?;
        // Always fsync, even with Log::fsync = false. Term changes are rare, so
        // this doesn't materially affect performance, and double voting could
        // lead to multiple leaders and split brain which is really bad.
        self.engine.flush()?;
        self.state = state;
        Ok(())
    }

    /// Appends a command to the log at the current term, and flushes it to
    /// disk, returning its index. None implies a noop command, typically after
    /// Raft leader changes.
    pub fn append(&mut self, command: Option<Vec<u8>>) -> Result<Index> {
        // The verified transition guarantees the entry is at last_index + 1
        // (index contiguity) in the current term (term monotonicity).
        let (index, state) = match append_state(&self.state) {
            AppendCheck::ZeroTerm => panic!("can't append entry in term 0"),
            AppendCheck::IndexOverflow => panic!("log index overflow"),
            AppendCheck::Append(index, state) => (index, state),
        };
        let entry = Entry { index, term: state.last_term, command };
        self.engine.set(&Key::Entry(entry.index).encode(), entry.encode())?;
        if self.fsync {
            self.engine.flush()?;
        }
        self.state = state;
        Ok(entry.index)
    }

    /// Commits entries up to and including the given index. The index must
    /// exist and be at or after the current commit index.
    pub fn commit(&mut self, index: Index) -> Result<Index> {
        let Some(entry) = self.get(index)? else {
            panic!("commit index {index} does not exist");
        };
        // The verified transition guarantees the commit index never regresses.
        let state = match commit_state(&self.state, entry.index, entry.term) {
            CommitCheck::Regression => {
                panic!("commit index regression {} → {}", self.state.commit_index, entry.index)
            }
            CommitCheck::Noop => return Ok(index),
            CommitCheck::Commit(state) => state,
        };
        self.engine.set(&Key::CommitIndex.encode(), bincode::serialize(&(index, entry.term)))?;
        // NB: the commit index doesn't need to be fsynced, since the entries
        // are fsynced and the commit index can be recovered from the quorum.
        self.state = state;
        Ok(index)
    }

    /// Fetches an entry at an index, or None if it does not exist.
    pub fn get(&mut self, index: Index) -> Result<Option<Entry>> {
        self.engine.get(&Key::Entry(index).encode())?.map(|v| Entry::decode(&v)).transpose()
    }

    /// Checks if the log contains an entry with the given index and term.
    pub fn has(&mut self, index: Index, term: Term) -> Result<bool> {
        // Fast path: check against last_index. This is the common case when
        // followers process appends or heartbeats.
        if index == 0 || index > self.state.last_index {
            return Ok(false);
        }
        if (index, term) == (self.state.last_index, self.state.last_term) {
            return Ok(true);
        }
        Ok(self.get(index)?.map(|e| e.term == term).unwrap_or(false))
    }

    /// Returns an iterator over log entries in the given index range.
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
        Iterator::new(self.engine.scan_dyn((from, to)))
    }

    /// Returns an iterator over entries that are ready to apply, starting after
    /// the current applied index up to the commit index.
    pub fn scan_apply(&mut self, applied_index: Index) -> Iterator<'_> {
        // NB: we don't assert that commit_index >= applied_index, because the
        // local commit index is not flushed to durable storage -- if lost on
        // restart, it can be recovered from the logs of a quorum.
        if applied_index >= self.state.commit_index {
            return Iterator::new(Box::new(std::iter::empty()));
        }
        self.scan(applied_index + 1..=self.state.commit_index)
    }

    /// Splices a set of entries into the log and flushes it to disk. New
    /// indexes will be appended. Overlapping indexes with the same term must be
    /// equal and will be ignored. Overlapping indexes with different terms will
    /// truncate the existing log at the first conflict and then splice the new
    /// entries.
    ///
    /// The entries must have contiguous indexes and equal/increasing terms, and
    /// the first entry must be in the range [1,last_index+1] with a term at or
    /// above the previous (base) entry's term and at or below the current term.
    pub fn splice(&mut self, entries: Vec<Entry>) -> Result<Index> {
        let (Some(first), Some(last)) = (entries.first(), entries.last()) else {
            return Ok(self.state.last_index); // empty input is noop
        };

        // Check that the entries are well-formed (nonzero first index/term,
        // contiguous indexes, monotone terms), using the verified checker.
        let pairs: Vec<(Index, Term)> = entries.iter().map(|e| (e.index, e.term)).collect();
        match check_splice_entries(&pairs) {
            SpliceEntriesCheck::Empty => unreachable!(), // handled above
            SpliceEntriesCheck::ZeroIndexOrTerm => panic!("spliced entry has index or term 0"),
            SpliceEntriesCheck::NonContiguous => panic!("spliced entries are not contiguous"),
            SpliceEntriesCheck::TermRegression => panic!("spliced entries have term regression"),
            SpliceEntriesCheck::WellFormed => {}
        }

        // Check that the entries connect to the existing log (if any), and that
        // the term doesn't regress, using the verified checker. The base entry
        // (just before the first spliced index) is fetched from unverified
        // storage; first.index - 1 can't underflow since first.index > 0.
        let base_term = self.get(first.index - 1)?.map(|base| base.term);
        match check_splice_connect(&self.state, first.index, first.term, last.term, base_term) {
            SpliceConnectCheck::TermBeyondCurrent => {
                panic!("splice term {} beyond current {}", last.term, self.state.term)
            }
            SpliceConnectCheck::BaseTermRegression => {
                panic!("splice term regression {} → {}", base_term.unwrap(), first.term)
            }
            SpliceConnectCheck::NoTouch => {
                panic!("first index {} must touch existing log", first.index)
            }
            SpliceConnectCheck::Connects => {}
        }

        // Skip entries that are already in the log.
        let mut entries = entries.as_slice();
        let mut scan = self.scan(first.index..=last.index);
        while let Some(entry) = scan.next().transpose()? {
            // [0] is ok, because the scan has the same size as entries.
            assert!(entry.index == entries[0].index, "index mismatch at {entry:?}");
            if entry.term != entries[0].term {
                break;
            }
            assert!(entry.command == entries[0].command, "command mismatch at {entry:?}");
            entries = &entries[1..];
        }
        drop(scan);

        // If all entries already exist then we're done.
        let Some(first) = entries.first() else {
            return Ok(self.state.last_index);
        };

        // The verified transition refuses to write below the commit index,
        // since committed entries must be immutable.
        let Some(state) = splice_state(&self.state, first.index, last.index, last.term) else {
            panic!("spliced entries below commit index");
        };

        // Write the entries that weren't already in the log, and remove the
        // tail of the old log if any.
        for entry in entries {
            self.engine.set(&Key::Entry(entry.index).encode(), entry.encode())?;
        }
        for index in last.index + 1..=self.state.last_index {
            self.engine.delete(&Key::Entry(index).encode())?;
        }
        if self.fsync {
            self.engine.flush()?;
        }

        self.state = state;
        Ok(self.state.last_index)
    }

    /// Returns log engine status.
    pub fn status(&mut self) -> Result<storage::Status> {
        self.engine.status()
    }
}

/// A log entry iterator.
pub struct Iterator<'a> {
    inner: Box<dyn storage::ScanIterator + 'a>,
}

impl<'a> Iterator<'a> {
    fn new(inner: Box<dyn storage::ScanIterator + 'a>) -> Self {
        Self { inner }
    }
}

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
                    let mut scan = self.log.engine.scan_dyn(range);
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
                        std::mem::replace(&mut self.log.engine, Box::new(storage::Memory::new()));
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
