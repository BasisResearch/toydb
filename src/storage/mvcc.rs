//! This module implements MVCC (Multi-Version Concurrency Control), a widely
//! used method for ACID transactions and concurrency control. It allows
//! multiple concurrent transactions to access and modify the same dataset,
//! isolates them from each other, detects and handles conflicts, and commits
//! their writes atomically as a single unit. It uses an underlying storage
//! engine to store raw keys and values.
//!
//! VERSIONS
//! ========
//!
//! MVCC handles concurrency control by managing multiple historical versions of
//! keys, identified by a timestamp. Every write adds a new version at a higher
//! timestamp, with deletes having a special tombstone value. For example, the
//! keys a,b,c,d may have the following values at various logical timestamps (x
//! is tombstone):
//!
//! Time
//! 5
//! 4  a4          
//! 3      b3      x
//! 2            
//! 1  a1      c1  d1
//!    a   b   c   d   Keys
//!
//! A transaction t2 that started at T=2 will see the values a=a1, c=c1, d=d1. A
//! different transaction t5 running at T=5 will see a=a4, b=b3, c=c1.
//!
//! toyDB uses logical timestamps with a sequence number stored in
//! Key::NextVersion. Each new read-write transaction takes its timestamp from
//! the current value of Key::NextVersion and then increments the value for the
//! next transaction.
//!
//! ISOLATION
//! =========
//!
//! MVCC provides an isolation level called snapshot isolation. Briefly,
//! transactions see a consistent snapshot of the database state as of their
//! start time. Writes made by concurrent or subsequent transactions are never
//! visible to it. If two concurrent transactions write to the same key they
//! will conflict and one of them must retry. A transaction's writes become
//! atomically visible to subsequent transactions only when they commit, and are
//! rolled back on failure. Read-only transactions never conflict with other
//! transactions.
//!
//! Transactions write new versions at their timestamp, storing them as
//! Key::Version(key, version) => value. If a transaction writes to a key and
//! finds a newer version, it returns an error and the client must retry.
//!
//! Active (uncommitted) read-write transactions record their version in the
//! active set, stored as Key::Active(version). When new transactions begin, they
//! take a snapshot of this active set, and any key versions that belong to a
//! transaction in the active set are considered invisible (to anyone except that
//! transaction itself). Writes to keys that already have a past version in the
//! active set will also return an error.
//!
//! To commit, a transaction simply deletes its record in the active set. This
//! will immediately (and, crucially, atomically) make all of its writes visible
//! to subsequent transactions, but not ongoing ones. If the transaction is
//! cancelled and rolled back, it maintains a record of all keys it wrote as
//! Key::TxnWrite(version, key), so that it can find the corresponding versions
//! and delete them before removing itself from the active set.
//!
//! Consider the following example, where we have two ongoing transactions at
//! time T=2 and T=5, with some writes that are not yet committed marked in
//! parentheses.
//!
//! Active set: [2, 5]
//!
//! Time
//! 5 (a5)
//! 4  a4          
//! 3      b3      x
//! 2         (x)     (e2)
//! 1  a1      c1  d1
//!    a   b   c   d   e   Keys
//!
//! Here, t2 will see a=a1, d=d1, e=e2 (it sees its own writes). t5 will see
//! a=a5, b=b3, c=c1. t2 does not see any newer versions, and t5 does not see
//! the tombstone at c@2 nor the value e=e2, because version=2 is in its active
//! set.
//!
//! If t2 tries to write b=b2, it receives an error and must retry, because a
//! newer version exists. Similarly, if t5 tries to write e=e5, it receives an
//! error and must retry, because the version e=e2 is in its active set.
//!
//! To commit, t2 can remove itself from the active set. A new transaction t6
//! starting after the commit will then see c as deleted and e=e2. t5 will still
//! not see any of t2's writes, because it's still in its local snapshot of the
//! active set at the time it began.
//!
//! READ-ONLY AND TIME TRAVEL QUERIES
//! =================================
//!
//! Since MVCC stores historical versions, it can trivially support time travel
//! queries where a transaction reads at a past timestamp and has a consistent
//! view of the database at that time.
//!
//! This is done by a transaction simply using a past version, as if it had
//! started far in the past, ignoring newer versions like any other transaction.
//! This transaction cannot write, as it does not have a unique timestamp (the
//! original read-write transaction originally owned this timestamp).
//!
//! The only wrinkle is that the time-travel query must also know what the active
//! set was at that version. Otherwise, it may see past transactions that committed
//! after that time, which were not visible to the original transaction that wrote
//! at that version. Similarly, if a time-travel query reads at a version that is
//! still active, it should not see its in-progress writes, and after it commits
//! a different time-travel query should not see those writes either, to maintain
//! version consistency.
//!
//! To achieve this, every read-write transaction stores its active set snapshot
//! in the storage engine as well, as Key::TxnActiveSnapshot, such that later
//! time-travel queries can restore its original snapshot. Furthermore, a
//! time-travel query can only see versions below the snapshot version, otherwise
//! it could see spurious in-progress or since-committed versions.
//!
//! In the following example, a time-travel query at version=3 would see a=a1,
//! c=c1, d=d1.
//!
//! Time
//! 5
//! 4  a4          
//! 3      b3      x
//! 2            
//! 1  a1      c1  d1
//!    a   b   c   d   Keys
//!
//! Read-only queries work similarly to time-travel queries, with one exception:
//! they read at the next (current) version, i.e. Key::NextVersion, and use the
//! current active set, storing the snapshot in memory only. Read-only queries
//! do not increment the version sequence number in Key::NextVersion.
//!
//! GARBAGE COLLECTION
//! ==================
//!
//! Normally, old versions would be garbage collected regularly, when they are
//! no longer needed by active transactions or time-travel queries. However,
//! toyDB does not implement garbage collection, instead keeping all history
//! forever, both out of laziness and also because it allows unlimited time
//! travel queries (it's a feature, not a bug!).

use std::borrow::Cow;
use std::collections::{BTreeSet, VecDeque};
use std::ops::{Bound, RangeBounds};
use std::sync::{Arc, Mutex};

use serde::{Deserialize, Serialize};

use super::engine::{self, Engine};
use crate::encoding::{self, Key as _, Value as _, bincode, keycode};
use crate::error::{Error, Result};
use crate::{errdata, errinput};

/// An MVCC version represents a logical timestamp. Each version belongs to a
/// separate read/write transaction. The latest version is incremented when a
/// new read-write transaction begins.
pub type Version = u64;

impl encoding::Value for Version {}

/// MVCC keys, using the Keycode encoding which preserves the ordering and
/// grouping of keys.
///
/// Cow byte slices allow encoding borrowed values and decoding owned values.
#[derive(Debug, Deserialize, Serialize)]
pub enum Key<'a> {
    /// The next available version.
    NextVersion,
    /// Active (uncommitted) transactions by version.
    TxnActive(Version),
    /// A snapshot of the active set at each version. Only written for
    /// versions where the active set is non-empty (excluding itself).
    TxnActiveSnapshot(Version),
    /// Keeps track of all keys written to by an active transaction (identified
    /// by its version), in case it needs to roll back.
    TxnWrite(
        Version,
        #[serde(with = "serde_bytes")]
        #[serde(borrow)]
        Cow<'a, [u8]>,
    ),
    /// A versioned key/value pair.
    Version(
        #[serde(with = "serde_bytes")]
        #[serde(borrow)]
        Cow<'a, [u8]>,
        Version,
    ),
    /// Unversioned non-transactional key/value pairs, mostly used for metadata.
    /// These exist separately from versioned keys, i.e. the unversioned key
    /// "foo" is entirely independent of the versioned key "foo@7".
    Unversioned(
        #[serde(with = "serde_bytes")]
        #[serde(borrow)]
        Cow<'a, [u8]>,
    ),
}

impl<'a> encoding::Key<'a> for Key<'a> {}

/// MVCC key prefixes, for prefix scans. These must match the keys above,
/// including the enum variant index.
#[derive(Debug, Deserialize, Serialize)]
enum KeyPrefix<'a> {
    NextVersion,
    TxnActive,
    TxnActiveSnapshot,
    TxnWrite(Version),
    Version(
        #[serde(with = "serde_bytes")]
        #[serde(borrow)]
        Cow<'a, [u8]>,
    ),
    Unversioned,
}

impl<'a> encoding::Key<'a> for KeyPrefix<'a> {}

/// An MVCC-based transactional key-value engine. It wraps an underlying storage
/// engine that's used for raw key/value storage.
///
/// While it supports any number of concurrent transactions, individual read or
/// write operations are executed sequentially, serialized via a mutex. There
/// are two reasons for this: the storage engine itself is not thread-safe,
/// requiring serialized access, and the Raft state machine that manages the
/// MVCC engine applies commands one at a time from the Raft log, which will
/// serialize them anyway.
pub struct MVCC<E: Engine> {
    pub engine: Arc<Mutex<E>>,
}

impl<E: Engine> MVCC<E> {
    /// Creates a new MVCC engine with the given storage engine.
    pub fn new(engine: E) -> Self {
        Self { engine: Arc::new(Mutex::new(engine)) }
    }

    /// Begins a new read-write transaction.
    pub fn begin(&self) -> Result<Transaction<E>> {
        Transaction::begin(self.engine.clone())
    }

    /// Begins a new read-only transaction at the latest version.
    pub fn begin_read_only(&self) -> Result<Transaction<E>> {
        Transaction::begin_read_only(self.engine.clone(), None)
    }

    /// Begins a new read-only transaction as of the given version.
    pub fn begin_as_of(&self, version: Version) -> Result<Transaction<E>> {
        Transaction::begin_read_only(self.engine.clone(), Some(version))
    }

    /// Resumes a transaction from the given transaction state.
    pub fn resume(&self, state: TransactionState) -> Result<Transaction<E>> {
        Transaction::resume(self.engine.clone(), state)
    }

    /// Fetches the value of an unversioned key.
    pub fn get_unversioned(&self, key: &[u8]) -> Result<Option<Vec<u8>>> {
        self.engine.lock()?.get(&Key::Unversioned(key.into()).encode())
    }

    /// Sets the value of an unversioned key.
    pub fn set_unversioned(&self, key: &[u8], value: Vec<u8>) -> Result<()> {
        self.engine.lock()?.set(&Key::Unversioned(key.into()).encode(), value)
    }

    /// Returns the status of the MVCC and storage engines.
    pub fn status(&self) -> Result<Status> {
        let mut engine = self.engine.lock()?;
        let versions = match engine.get(&Key::NextVersion.encode())? {
            Some(ref v) => Version::decode(v)? - 1,
            None => 0,
        };
        let active_txns = engine.scan_prefix(&KeyPrefix::TxnActive.encode()).count() as u64;
        Ok(Status { versions, active_txns, storage: engine.status()? })
    }
}

/// MVCC engine status.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Status {
    /// The total number of MVCC versions (i.e. read-write transactions).
    pub versions: u64,
    /// Number of currently active transactions.
    pub active_txns: u64,
    /// The storage engine.
    pub storage: super::engine::Status,
}

impl encoding::Value for Status {}

/// An MVCC transaction.
pub struct Transaction<E: Engine> {
    /// The underlying engine, shared by all transactions.
    engine: Arc<Mutex<E>>,
    /// The transaction state.
    state: TransactionState,
}

/// A Transaction's state, which determines its write version and isolation. It
/// is separate from Transaction to allow it to be passed around independently
/// of the engine. There are two main motivations for this:
///
/// * It can be exported via Transaction.state(), (de)serialized, and later used
///   to instantiate a new functionally equivalent Transaction via
///   Transaction::resume(). This allows passing the transaction between the
///   storage engine and SQL engine (potentially running on a different node)
///   across the Raft state machine boundary.
///
/// * It can be borrowed independently of Engine, allowing references to it
///   in VisibleIterator, which would otherwise result in self-references.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct TransactionState {
    /// The version this transaction is running at. Only one read-write
    /// transaction can run at a given version, since this identifies its
    /// writes.
    pub version: Version,
    /// If true, the transaction is read only.
    pub read_only: bool,
    /// The set of concurrent active (uncommitted) transactions, as of the start
    /// of this transaction. Their writes should be invisible to this
    /// transaction even if they're writing at a lower version, since they're
    /// not committed yet. Uses a BTreeSet for test determinism.
    pub active: BTreeSet<Version>,
}

impl encoding::Value for TransactionState {}

impl TransactionState {
    /// Checks whether the given version is visible to this transaction.
    ///
    /// Future versions, and versions belonging to active transactions as of
    /// the start of this transaction, are never visible.
    ///
    /// Read-write transactions see their own writes at their version.
    ///
    /// Read-only queries only see versions below the transaction's version,
    /// excluding the version itself. This is to ensure time-travel queries see
    /// a consistent version both before and after any active transaction at
    /// that version commits its writes. See the module documentation for
    /// details.
    ///
    /// Delegates to the Verus-verified `is_visible_core`, which is proven to
    /// compute `spec_is_visible` — the visibility relation of the verified
    /// snapshot-isolation model at the bottom of this file.
    fn is_visible(&self, version: Version) -> bool {
        is_visible_core(&self.active, self.version, self.read_only, version)
    }
}

impl From<TransactionState> for Cow<'_, TransactionState> {
    fn from(txn: TransactionState) -> Self {
        Cow::Owned(txn)
    }
}

impl<'a> From<&'a TransactionState> for Cow<'a, TransactionState> {
    fn from(txn: &'a TransactionState) -> Self {
        Cow::Borrowed(txn)
    }
}

impl<E: Engine> Transaction<E> {
    /// Begins a new transaction in read-write mode. This will allocate a new
    /// version that the transaction can write at, add it to the active set, and
    /// record its active snapshot for time-travel queries.
    ///
    /// Delegates to the verified `vbegin`, which is proven to refine the
    /// model `begin` transition and preserve the refinement invariant.
    fn begin(engine: Arc<Mutex<E>>) -> Result<Self> {
        let mut session = engine.lock()?;
        let (version, active) = vbegin(&mut EngineHandle::new(&mut *session))?;
        drop(session);
        Ok(Self { engine, state: TransactionState { version, read_only: false, active } })
    }

    /// Begins a new read-only transaction. If version is given it will see the
    /// state as of the beginning of that version (ignoring writes at that
    /// version). In other words, it sees the same state as the read-write
    /// transaction at that version saw when it began.
    ///
    /// Delegates to the verified `vbegin_read_only`, which is proven to
    /// produce a well-formed observer (`wf_observer`) of the current state,
    /// so the verified read-path theorems (no dirty reads, snapshot
    /// stability) apply to the resulting transaction.
    fn begin_read_only(engine: Arc<Mutex<E>>, as_of: Option<Version>) -> Result<Self> {
        let mut session = engine.lock()?;
        let (version, active) = vbegin_read_only(&mut EngineHandle::new(&mut *session), as_of)?;
        drop(session);
        Ok(Self { engine, state: TransactionState { version, read_only: true, active } })
    }

    /// Resumes a transaction from the given state.
    fn resume(engine: Arc<Mutex<E>>, s: TransactionState) -> Result<Self> {
        // For read-write transactions, verify that the transaction is still
        // active before making further writes.
        if !s.read_only && engine.lock()?.get(&Key::TxnActive(s.version).encode())?.is_none() {
            return errinput!("no active transaction at version {}", s.version);
        }
        Ok(Self { engine, state: s })
    }

    /// Returns the version the transaction is running at.
    pub fn version(&self) -> Version {
        self.state.version
    }

    /// Returns whether the transaction is read-only.
    pub fn read_only(&self) -> bool {
        self.state.read_only
    }

    /// Returns the transaction's state. This can be used to instantiate a
    /// functionally equivalent transaction via resume().
    pub fn state(&self) -> &TransactionState {
        &self.state
    }

    /// Commits the transaction, by removing it from the active set. This will
    /// immediately make its writes visible to subsequent transactions. Also
    /// removes its TxnWrite records, which are no longer needed.
    ///
    /// NB: commit does not flush writes to durable storage, since we rely on
    /// the Raft log for persistence.
    ///
    /// Delegates to the verified `vcommit`, proven to refine the model
    /// `commit` transition.
    pub fn commit(self) -> Result<()> {
        if self.state.read_only {
            return Ok(());
        }
        let mut engine = self.engine.lock()?;
        vcommit(&mut EngineHandle::new(&mut *engine), self.state.version)
    }

    /// Rolls back the transaction, by undoing all written versions and removing
    /// it from the active set. The active set snapshot is left behind, since
    /// this is needed for time travel queries at this version.
    ///
    /// Delegates to the verified `vrollback`, proven to refine the model
    /// `rollback` transition: it erases exactly the transaction's own writes.
    pub fn rollback(self) -> Result<()> {
        if self.state.read_only {
            return Ok(());
        }
        let mut engine = self.engine.lock()?;
        vrollback(&mut EngineHandle::new(&mut *engine), self.state.version)
    }

    /// Deletes a key.
    pub fn delete(&self, key: &[u8]) -> Result<()> {
        self.write_version(key, None)
    }

    /// Sets a value for a key.
    pub fn set(&self, key: &[u8], value: Vec<u8>) -> Result<()> {
        self.write_version(key, Some(value))
    }

    /// Writes a new version for a key at the transaction's version. None writes
    /// a deletion tombstone. If a write conflict is found (either a newer or
    /// uncommitted version), a serialization error is returned.  Replacing our
    /// own uncommitted write is fine.
    fn write_version(&self, key: &[u8], value: Option<Vec<u8>>) -> Result<()> {
        if self.state.read_only {
            return Err(Error::ReadOnly);
        }
        let mut engine = self.engine.lock()?;

        // Delegates to the verified `vwrite`: check for write conflicts, i.e.
        // if the latest key is invisible to us (either a newer version, or an
        // uncommitted version in our past). We can only conflict with the
        // latest key, since all transactions enforce the same invariant.
        //
        // That invariant is machine-checked: `thm_conflict_check_exact`
        // proves that under the system invariant `inv`, this
        // latest-version-only check accepts exactly when *no* version of the
        // key is invisible, `thm_inv_preserved` proves every transaction
        // operation preserves the invariant, and `vwrite` is proven to
        // perform exactly this check against the real engine and to refine
        // the model `write` transition.
        match vwrite(
            &mut EngineHandle::new(&mut *engine),
            self.state.version,
            &self.state.active,
            key,
            &value,
        ) {
            VWriteOutcome::Done => Ok(()),
            VWriteOutcome::Conflict => Err(Error::Serialization),
            VWriteOutcome::Fail(e) => Err(e),
        }
    }

    /// Fetches a key's value, or None if it does not exist.
    ///
    /// Delegates to the verified `vget`, proven to return the model read:
    /// the value at the greatest visible version of the key.
    pub fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>> {
        let mut engine = self.engine.lock()?;
        vget(
            &mut EngineHandle::new(&mut *engine),
            self.state.version,
            self.state.read_only,
            &self.state.active,
            key,
        )
    }

    /// Returns an iterator over the latest visible key/value pairs at the
    /// transaction's version.
    pub fn scan(&self, range: impl RangeBounds<Vec<u8>>) -> ScanIterator<E> {
        let start = match range.start_bound() {
            Bound::Excluded(k) => Bound::Excluded(Key::Version(k.into(), u64::MAX).encode()),
            Bound::Included(k) => Bound::Included(Key::Version(k.into(), 0).encode()),
            Bound::Unbounded => Bound::Included(Key::Version(vec![].into(), 0).encode()),
        };
        let end = match range.end_bound() {
            Bound::Excluded(k) => Bound::Excluded(Key::Version(k.into(), 0).encode()),
            Bound::Included(k) => Bound::Included(Key::Version(k.into(), u64::MAX).encode()),
            Bound::Unbounded => Bound::Excluded(KeyPrefix::Unversioned.encode()),
        };
        ScanIterator::new(self.engine.clone(), self.state().clone(), (start, end))
    }

    /// Scans keys under a given prefix.
    pub fn scan_prefix(&self, prefix: &[u8]) -> ScanIterator<E> {
        // Normally, KeyPrefix::Version will only match all versions of the
        // exact given key. We want all keys maching the prefix, so we chop off
        // the Keycode byte slice terminator 0x0000 at the end.
        let mut prefix = KeyPrefix::Version(prefix.into()).encode();
        prefix.truncate(prefix.len() - 2);
        let range = keycode::prefix_range(&prefix);
        ScanIterator::new(self.engine.clone(), self.state().clone(), range)
    }
}

/// An iterator over the latest live and visible key/value pairs for the txn.
///
/// The (single-threaded) engine is shared via mutex, and holding the mutex for
/// the lifetime of the iterator can cause deadlocks (e.g. when the local SQL
/// engine pulls from two tables concurrently during a join). Instead, we pull
/// and buffer a batch of rows at a time, and release the mutex in between.
///
/// This does not implement DoubleEndedIterator (reverse scans), since the SQL
/// layer doesn't currently need it.
pub struct ScanIterator<E: Engine> {
    /// The engine.
    engine: Arc<Mutex<E>>,
    /// The transaction state.
    txn: TransactionState,
    /// A buffer of live and visible key/value pairs to emit.
    buffer: VecDeque<(Vec<u8>, Vec<u8>)>,
    /// The remaining range after the buffer.
    remainder: Option<(Bound<Vec<u8>>, Bound<Vec<u8>>)>,
}

/// Implement [`Clone`] manually. `derive(Clone)` isn't smart enough to figure
/// out that we don't need `Engine: Clone` when it's in an [`Arc`]. See:
/// <https://github.com/rust-lang/rust/issues/26925>.
impl<E: Engine> Clone for ScanIterator<E> {
    fn clone(&self) -> Self {
        Self {
            engine: self.engine.clone(),
            txn: self.txn.clone(),
            buffer: self.buffer.clone(),
            remainder: self.remainder.clone(),
        }
    }
}

impl<E: Engine> ScanIterator<E> {
    /// The number of live key/value pairs to pull from the engine each time we
    /// lock it. Uses 2 in tests to exercise the buffering code.
    const BUFFER_SIZE: usize = if cfg!(test) { 2 } else { 32 };

    /// Creates a new scan iterator.
    fn new(
        engine: Arc<Mutex<E>>,
        txn: TransactionState,
        range: (Bound<Vec<u8>>, Bound<Vec<u8>>),
    ) -> Self {
        let buffer = VecDeque::with_capacity(Self::BUFFER_SIZE);
        Self { engine, txn, buffer, remainder: Some(range) }
    }

    /// Fills the buffer, if there's any pending items.
    fn fill_buffer(&mut self) -> Result<()> {
        // Check if there's anything to buffer.
        if self.buffer.len() >= Self::BUFFER_SIZE {
            return Ok(());
        }
        let Some(range) = self.remainder.take() else {
            return Ok(());
        };
        let range_end = range.1.clone();

        let mut engine = self.engine.lock()?;
        let mut iter = VersionIterator::new(&self.txn, engine.scan(range)).peekable();
        while let Some((key, _, value)) = iter.next().transpose()? {
            // If the next key equals this one, we're not at the latest version.
            match iter.peek() {
                Some(Ok((next, _, _))) if next == &key => continue,
                Some(Err(err)) => return Err(err.clone()),
                Some(Ok(_)) | None => {}
            }

            // Decode the value, and skip deleted keys (tombstones).
            let Some(value) = bincode::deserialize(&value)? else { continue };
            self.buffer.push_back((key, value));

            // If we filled the buffer, save the remaining range (if any) and
            // return. peek() has already buffered next(), so pull it.
            if self.buffer.len() == Self::BUFFER_SIZE {
                if let Some((next, version, _)) = iter.next().transpose()? {
                    // We have to re-encode it as a raw engine key, since we
                    // only have access to the decoded MVCC user key.
                    let range_start = Bound::Included(Key::Version(next.into(), version).encode());
                    self.remainder = Some((range_start, range_end));
                }
                return Ok(());
            }
        }
        Ok(())
    }
}

impl<E: Engine> Iterator for ScanIterator<E> {
    type Item = Result<(Vec<u8>, Vec<u8>)>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.buffer.is_empty()
            && let Err(error) = self.fill_buffer()
        {
            return Some(Err(error));
        }
        self.buffer.pop_front().map(Ok)
    }
}

/// An iterator that decodes raw engine key/value pairs into MVCC key/value
/// versions, and skips invisible versions. Helper for ScanIterator.
struct VersionIterator<'a, I: engine::ScanIterator> {
    /// The transaction the scan is running in.
    txn: &'a TransactionState,
    /// The inner engine scan iterator.
    inner: I,
}

impl<'a, I: engine::ScanIterator> VersionIterator<'a, I> {
    /// Creates a new MVCC version iterator for the given engine iterator.
    fn new(txn: &'a TransactionState, inner: I) -> Self {
        Self { txn, inner }
    }

    // Fallible next(). Returns the next visible key/version/value tuple.
    fn try_next(&mut self) -> Result<Option<(Vec<u8>, Version, Vec<u8>)>> {
        while let Some((key, value)) = self.inner.next().transpose()? {
            let Key::Version(key, version) = Key::decode(&key)? else {
                return errdata!("expected Key::Version got {key:?}");
            };
            if !self.txn.is_visible(version) {
                continue;
            }
            return Ok(Some((key.into_owned(), version, value)));
        }
        Ok(None)
    }
}

impl<I: engine::ScanIterator> Iterator for VersionIterator<'_, I> {
    type Item = Result<(Vec<u8>, Version, Vec<u8>)>;

    fn next(&mut self) -> Option<Self::Item> {
        self.try_next().transpose()
    }
}

// ---------------------------------------------------------------------------
// Verus-verified model of MVCC snapshot isolation
// ---------------------------------------------------------------------------
//
// This block builds an abstract, spec-level model of the MVCC engine above and
// proves its core isolation properties. The model state mirrors the engine's
// persistent keys one-to-one:
//
//   ModelState.next    <->  Key::NextVersion
//   ModelState.active  <->  the set of Key::TxnActive(v) records
//   ModelState.snap    <->  Key::TxnActiveSnapshot(v) (total on allocated
//                           versions; the code omits the record when the set
//                           was empty and reads a missing record as empty)
//   ModelState.store   <->  Key::Version(key, version) => value records,
//                           as a map (key, version) -> Option<value>,
//                           None modeling a deletion tombstone
//
// There is deliberately no record of *rolled-back* transactions: rollback
// erases all the transaction's writes (thm_rollback_erases), so a rolled-back
// version is observationally identical to a committed one that wrote nothing,
// and the engine keeps no such record either. `ended` (allocated, no longer
// active) is the model's notion of "this transaction is over"; an ended
// version that still owns a write in the store necessarily committed.
//
// Transitions model Transaction::begin / write_version / commit / rollback.
// Each transition is one atomic step, matching the engine mutex held across
// the corresponding operation. TxnWrite(v, key) records are modeled
// implicitly: they exist precisely to let rollback(v) find the store entries
// with version v, which the model removes directly. Read-only and time-travel
// transactions never write and are modeled as observers (`wf_observer`), not
// state. The model relies on the engine scan returning Key::Version(key, v)
// entries grouped by key and ordered by version — that is the keycode
// order-preservation property verified in `encoding::keycode`.
//
// `write` is guarded by exactly the check `write_version` performs: scan the
// versions of the key from `active.first().unwrap_or(version + 1)`
// (`is_scan_floor`) to `u64::MAX`, and error iff the *last* version in that
// range is invisible (`check_passes`). The centerpiece theorem
// `thm_conflict_check_exact` proves the comment in `write_version` ("we can
// only conflict with the latest key, since all transactions enforce the same
// invariant"): under the inductive invariant `inv`, this latest-only check
// accepts exactly when no version of the key is invisible
// (`no_write_conflict`). The invariant's load-bearing clauses are:
//
//   inv_uncommitted_latest  an uncommitted version is the latest version of
//                           its key,
//   inv_no_concurrent_writes  for any two versions of one key, the earlier
//                           writer had ended before the later writer began,
//   inv_snapshots_coherent  begin-snapshots are mutually consistent.
//
// `lemma_inv_init` and `thm_inv_preserved` prove `inv` holds initially and is
// preserved by every step — the induction the code comment appeals to.
//
// The isolation theorems map to the anomaly goldenscripts under
// src/storage/testscripts/mvcc:
//
//   anomaly_dirty_read    thm_uncommitted_invisible, thm_reads_see_only_committed
//   anomaly_dirty_write   thm_no_dirty_write
//   anomaly_fuzzy_read,
//   anomaly_read_skew,
//   anomaly_phantom_read  thm_snapshot_stability, thm_repeatable_read: a live
//                         transaction's entire visible key/value slice — and
//                         hence any point read or scan over it — is unchanged
//                         by any other transaction's begin/write/commit/rollback
//   anomaly_lost_update   thm_first_writer_wins: of two conflicting writers the
//                         later one errored unless the earlier had committed
//                         first, and then its write was visible to the later
//                         writer — an update is never blindly overwritten
//   anomaly_write_skew    intentionally NOT prevented: snapshot isolation only
//                         detects write-write conflicts, and no theorem here
//                         claims serializability
//   rollback              thm_rollback_erases, thm_rolled_back_stays_gone
//
// `verus!` erases everything below to nothing under a normal `cargo build`,
// except `is_visible_core`, which erases to the plain function body that
// `TransactionState::is_visible` calls.
use vstd::prelude::*;

verus! {

broadcast use {vstd::std_specs::btree::group_btree_axioms, vstd::laws_cmp::group_laws_cmp};

// ---- Visibility -----------------------------------------------------------

/// Spec mirror of `TransactionState::is_visible`: which versions a transaction
/// at `version` with begin-time active set `active` can see. This single
/// relation drives reads, scans, and the write-conflict check.
pub open spec fn spec_is_visible(active: Set<u64>, version: u64, read_only: bool, w: u64) -> bool {
    if active.contains(w) {
        false
    } else if read_only {
        w < version
    } else {
        w <= version
    }
}

/// Verified executable core of `TransactionState::is_visible`, proven to
/// compute `spec_is_visible` over the abstract view of the active set.
pub fn is_visible_core(active: &BTreeSet<u64>, version: u64, read_only: bool, candidate: u64) -> (r:
    bool)
    ensures
        r == spec_is_visible(active@, version, read_only, candidate),
{
    if active.contains(&candidate) {
        false
    } else if read_only {
        candidate < version
    } else {
        candidate <= version
    }
}

// ---- Model state ----------------------------------------------------------

/// The abstract MVCC state. See the block comment above for the field-by-field
/// correspondence with the engine's persistent keys.
pub struct ModelState {
    /// The next version to allocate (Key::NextVersion).
    pub next: u64,
    /// Versions of currently active (uncommitted) read-write transactions.
    pub active: Set<u64>,
    /// For every version ever allocated: the active set when it began.
    pub snap: Map<u64, Set<u64>>,
    /// Versioned writes: (key, version) -> value, None being a tombstone.
    pub store: Map<(Seq<u8>, u64), Option<Seq<u8>>>,
}

/// Whether version `v` has been allocated to some read-write transaction.
pub open spec fn allocated(s: ModelState, v: u64) -> bool {
    1 <= v < s.next
}

/// Whether the store holds a version `w` of `key`.
pub open spec fn has_version(s: ModelState, key: Seq<u8>, w: u64) -> bool {
    s.store.contains_key((key, w))
}

/// Visibility for the read-write transaction at version `v`.
pub open spec fn txn_visible(s: ModelState, v: u64, w: u64) -> bool {
    spec_is_visible(s.snap[v], v, false, w)
}

/// A version whose transaction has ended, by commit or rollback. The two are
/// deliberately indistinguishable in the state: rollback erases all the
/// transaction's writes (thm_rollback_erases), making it observationally
/// identical to a committed transaction that wrote nothing. Consequently, an
/// ended version that still has a write in the store is necessarily one that
/// committed.
pub open spec fn ended(s: ModelState, v: u64) -> bool {
    allocated(s, v) && !s.active.contains(v)
}

// ---- The inductive invariant ----------------------------------------------

/// The system invariant: holds initially and is preserved by every transition
/// (`lemma_inv_init`, `thm_inv_preserved`). The final three clauses are the
/// invariant the `write_version` comment appeals to.
pub open spec fn inv(s: ModelState) -> bool {
    // Versions start at 1.
    &&& 1 <= s.next
    // Active transactions hold allocated versions.
    &&& forall|v: u64| #[trigger] s.active.contains(v) ==> allocated(s, v)
    // Exactly the allocated versions have a begin snapshot.
    &&& forall|v: u64| #[trigger] s.snap.contains_key(v) ==> allocated(s, v)
    &&& forall|v: u64| #[trigger] allocated(s, v) ==> s.snap.contains_key(v)
    // A begin snapshot only holds older allocated versions: the transactions
    // active when v began had begun (and taken their versions) before v.
    &&& forall|v: u64, w: u64|
        s.snap.contains_key(v) && #[trigger] s.snap[v].contains(w) ==> 1 <= w < v
    // A transaction still active now, with a version below v, was already
    // active when v began — active sets only lose members over time, and new
    // members take fresh higher versions.
    &&& forall|v: u64, w: u64|
        #![trigger s.snap[v].contains(w)]
        #![trigger s.active.contains(w), s.snap.contains_key(v)]
        s.snap.contains_key(v) && s.active.contains(w) && w < v ==> s.snap[v].contains(w)
    // Versioned writes hold allocated versions.
    &&& forall|k: Seq<u8>, w: u64| #[trigger] s.store.contains_key((k, w)) ==> allocated(s, w)
    // inv_uncommitted_latest: an uncommitted version is the latest version of
    // its key. This is what makes "check only the latest version" complete:
    // an uncommitted-conflict can only sit at the top.
    &&& forall|k: Seq<u8>, w: u64, w2: u64|
        #![trigger s.store.contains_key((k, w)), s.store.contains_key((k, w2))]
        s.store.contains_key((k, w)) && s.active.contains(w) && s.store.contains_key((k, w2))
            ==> w2 <= w
    // inv_no_concurrent_writes: for any two versions of one key, the earlier
    // writer had already ended when the later writer began — no two
    // transactions that overlap in time both write the same key.
    &&& forall|k: Seq<u8>, w: u64, w2: u64|
        #![trigger s.store.contains_key((k, w)), s.store.contains_key((k, w2))]
        s.store.contains_key((k, w)) && s.store.contains_key((k, w2)) && w < w2
            ==> !s.snap[w2].contains(w)
    // inv_snapshots_coherent: begin snapshots are mutually consistent. If w
    // was still active when u began, while m (with w < m < u) had already
    // ended by then, then m's entire lifetime fell inside w's, so w was
    // active when m began.
    &&& forall|u: u64, m: u64, w: u64|
        #![trigger s.snap[u].contains(w), s.snap.contains_key(m)]
        s.snap.contains_key(u) && s.snap.contains_key(m) && s.snap[u].contains(w)
            && !s.snap[u].contains(m) && w < m && m < u ==> s.snap[m].contains(w)
}

// ---- Transitions ----------------------------------------------------------

/// The initial state: no versions allocated, everything empty.
pub open spec fn init() -> ModelState {
    ModelState {
        next: 1,
        active: Set::empty(),
        snap: Map::empty(),
        store: Map::empty(),
    }
}

/// Model artifact: the u64 version counter must not overflow. (toyDB would
/// need 2^64 - 1 transactions to get here.)
pub open spec fn can_begin(s: ModelState) -> bool {
    s.next < u64::MAX
}

/// Transaction::begin: allocate version s.next, snapshot the active set,
/// join the active set. One atomic step, like the code under the engine mutex.
pub open spec fn begin(s: ModelState) -> ModelState {
    ModelState {
        next: (s.next + 1) as u64,
        active: s.active.insert(s.next),
        snap: s.snap.insert(s.next, s.active),
        store: s.store,
    }
}

pub open spec fn can_commit(s: ModelState, v: u64) -> bool {
    s.active.contains(v)
}

/// Transaction::commit: remove the TxnActive record. The writes stay; this
/// single removal is what atomically publishes them to later transactions.
pub open spec fn commit(s: ModelState, v: u64) -> ModelState {
    ModelState {
        next: s.next,
        active: s.active.remove(v),
        snap: s.snap,
        store: s.store,
    }
}

pub open spec fn can_rollback(s: ModelState, v: u64) -> bool {
    s.active.contains(v)
}

/// Transaction::rollback: delete every store entry at version v (found via
/// the TxnWrite(v, ..) records in the code), then leave the active set. The
/// snapshot record stays behind for time-travel queries, as in the code.
pub open spec fn rollback(s: ModelState, v: u64) -> ModelState {
    ModelState {
        next: s.next,
        active: s.active.remove(v),
        snap: s.snap,
        store: s.store.remove_keys(s.store.dom().filter(|p: (Seq<u8>, u64)| p.1 == v)),
    }
}

/// The lower bound of the conflict-scan range in `write_version`:
/// `self.state.active.first().copied().unwrap_or(self.state.version + 1)`,
/// i.e. the smallest version in the begin snapshot, or version + 1 when the
/// snapshot is empty.
pub open spec fn is_scan_floor(a: Set<u64>, v: u64, lo: u64) -> bool {
    &&& forall|w: u64| #[trigger] a.contains(w) ==> lo <= w
    &&& (a.contains(lo) || (lo == v + 1 && forall|w: u64| !(#[trigger] a.contains(w))))
}

/// `m` is the greatest version of `key` in the scanned range `lo..=u64::MAX`:
/// what `engine.scan(from..=to).last()` returns in `write_version`.
pub open spec fn range_max(s: ModelState, key: Seq<u8>, lo: u64, m: u64) -> bool {
    &&& has_version(s, key, m)
    &&& lo <= m
    &&& forall|w: u64| #[trigger] has_version(s, key, w) && lo <= w ==> w <= m
}

/// The conflict check exactly as `write_version` performs it: pass iff the
/// scanned range is empty or its greatest version is visible.
pub open spec fn check_passes(s: ModelState, v: u64, key: Seq<u8>, lo: u64) -> bool {
    forall|m: u64| #[trigger] range_max(s, key, lo, m) ==> txn_visible(s, v, m)
}

/// The full (unoptimized) conflict condition: *no* version of the key,
/// anywhere in history, is invisible to the writer. `thm_conflict_check_exact`
/// proves `check_passes` equivalent to this under `inv`.
pub open spec fn no_write_conflict(s: ModelState, v: u64, key: Seq<u8>) -> bool {
    forall|w: u64| #[trigger] has_version(s, key, w) ==> txn_visible(s, v, w)
}

pub open spec fn can_write(s: ModelState, v: u64, key: Seq<u8>) -> bool {
    &&& s.active.contains(v)
    &&& exists|lo: u64|
        #[trigger] is_scan_floor(s.snap[v], v, lo) && check_passes(s, v, key, lo)
}

/// Transaction::set / delete via write_version: record the new version at the
/// writer's own version. `value` None is a deletion tombstone.
pub open spec fn write(s: ModelState, v: u64, key: Seq<u8>, value: Option<Seq<u8>>) -> ModelState {
    ModelState {
        next: s.next,
        active: s.active,
        snap: s.snap,
        store: s.store.insert((key, v), value),
    }
}

/// One step of the system, taken by the transaction at version `actor`
/// (for begin: the version being allocated).
pub open spec fn step(s: ModelState, s2: ModelState, actor: u64) -> bool {
    ||| (can_begin(s) && actor == s.next && s2 == begin(s))
    ||| (can_commit(s, actor) && s2 == commit(s, actor))
    ||| (can_rollback(s, actor) && s2 == rollback(s, actor))
    ||| exists|key: Seq<u8>, value: Option<Seq<u8>>|
        can_write(s, actor, key) && s2 == #[trigger] write(s, actor, key, value)
}

// ---- The conflict check is exact ------------------------------------------

/// `m` is the greatest version of `key` in `[lo, b)`.
spec fn range_max_below(s: ModelState, key: Seq<u8>, lo: u64, b: u64, m: u64) -> bool {
    &&& lo <= m < b
    &&& has_version(s, key, m)
    &&& forall|w: u64| lo <= w < b && #[trigger] has_version(s, key, w) ==> w <= m
}

/// Any nonempty set of versions of `key` in `[lo, b)` has a greatest element.
proof fn lemma_version_range_has_max(s: ModelState, key: Seq<u8>, lo: u64, b: u64)
    requires
        exists|w: u64| lo <= w < b && #[trigger] has_version(s, key, w),
    ensures
        exists|m: u64| #[trigger] range_max_below(s, key, lo, b, m),
    decreases b,
{
    let w0 = choose|w: u64| lo <= w < b && #[trigger] has_version(s, key, w);
    let t = (b - 1) as u64;
    if has_version(s, key, t) && lo <= t {
        assert(range_max_below(s, key, lo, b, t));
    } else {
        // The top slot b - 1 is unoccupied (lo <= t holds since lo <= w0 <= t),
        // so the witness sits in [lo, b - 1) and the max there is the max.
        assert(lo <= w0 < t && has_version(s, key, w0));
        lemma_version_range_has_max(s, key, lo, t);
        let m = choose|m: u64| #[trigger] range_max_below(s, key, lo, t, m);
        assert forall|w: u64| lo <= w < b && #[trigger] has_version(s, key, w) implies w <= m by {
            assert(w != t);
        }
        assert(range_max_below(s, key, lo, b, m));
    }
}

/// If any version of `key` is at or above `lo`, the scanned range has a
/// greatest element (all versions are below s.next by `inv`).
proof fn lemma_range_has_max(s: ModelState, key: Seq<u8>, lo: u64)
    requires
        inv(s),
        exists|w: u64| lo <= w && #[trigger] has_version(s, key, w),
    ensures
        exists|m: u64| #[trigger] range_max(s, key, lo, m),
{
    let w0 = choose|w: u64| lo <= w && #[trigger] has_version(s, key, w);
    assert(allocated(s, w0));
    lemma_version_range_has_max(s, key, lo, s.next);
    let m = choose|m: u64| #[trigger] range_max_below(s, key, lo, s.next, m);
    assert forall|w: u64| #[trigger] has_version(s, key, w) && lo <= w implies w <= m by {
        assert(allocated(s, w));
    }
    assert(range_max(s, key, lo, m));
}

/// THE CENTERPIECE: under the invariant, `write_version`'s latest-version-only
/// conflict check accepts exactly when no version of the key — latest or
/// buried — is invisible to the writer. This discharges the code comment "we
/// can only conflict with the latest key, since all transactions enforce the
/// same invariant".
///
/// Soundness (passes ==> nothing invisible) is the interesting direction:
/// * Versions below the scan floor are below every member of the begin
///   snapshot and below the writer's own version, hence visible.
/// * For a buried version w below the range's max m: w can only be invisible
///   by sitting in the writer's begin snapshot; then `inv_snapshots_coherent`
///   places w in m's begin snapshot, contradicting `inv_no_concurrent_writes`.
pub proof fn thm_conflict_check_exact(s: ModelState, v: u64, key: Seq<u8>, lo: u64)
    requires
        inv(s),
        s.active.contains(v),
        is_scan_floor(s.snap[v], v, lo),
    ensures
        check_passes(s, v, key, lo) <==> no_write_conflict(s, v, key),
{
    assert(allocated(s, v));
    assert(s.snap.contains_key(v));
    // Completeness: the range max is itself a version, so if every version is
    // visible then so is the max.
    if no_write_conflict(s, v, key) {
        assert forall|m: u64| #[trigger] range_max(s, key, lo, m) implies txn_visible(
            s,
            v,
            m,
        ) by {
            assert(has_version(s, key, m));
        }
    }
    // Soundness.
    if check_passes(s, v, key, lo) {
        assert forall|w: u64| #[trigger] has_version(s, key, w) implies txn_visible(s, v, w) by {
            if w < lo {
                // Below the floor: below every snapshot member, and below v.
                assert(!s.snap[v].contains(w));
                if s.snap[v].contains(lo) {
                    assert(lo < v);  // snapshot members precede v
                } else {
                    assert(lo == v + 1);
                }
                assert(w <= v);
            } else {
                assert(lo <= w && has_version(s, key, w));
                lemma_range_has_max(s, key, lo);
                let m = choose|m: u64| #[trigger] range_max(s, key, lo, m);
                assert(txn_visible(s, v, m));
                assert(w <= m);
                assert(m <= v);
                if w != m && s.snap[v].contains(w) {
                    // w was uncommitted when v began, yet a later version m of
                    // the same key exists: impossible.
                    if m == v {
                        // v itself wrote later: inv_no_concurrent_writes on
                        // (w, v) says w was not in v's begin snapshot.
                        assert(s.store.contains_key((key, w)) && s.store.contains_key((key, v)));
                        assert(false);
                    } else {
                        // w < m < v: coherence puts w in m's begin snapshot,
                        // conflicting with inv_no_concurrent_writes on (w, m).
                        assert(allocated(s, m));
                        assert(s.snap.contains_key(m));
                        assert(s.snap[m].contains(w));
                        assert(s.store.contains_key((key, w)) && s.store.contains_key((key, m)));
                        assert(false);
                    }
                }
                assert(!s.snap[v].contains(w));
            }
        }
    }
}

// ---- The invariant is inductive -------------------------------------------

/// The initial state satisfies the invariant.
pub proof fn lemma_inv_init()
    ensures
        inv(init()),
{
}

proof fn lemma_inv_begin(s: ModelState)
    requires
        inv(s),
        can_begin(s),
    ensures
        inv(begin(s)),
{
    let s2 = begin(s);
    let n = s.next;
    // Snapshot domain: exactly [1, next + 1).
    assert forall|v: u64| #[trigger] allocated(s2, v) implies s2.snap.contains_key(v) by {
        if v != n {
            assert(allocated(s, v));
        }
    }
    // New snapshot only holds older versions; still-active-below is inherited.
    assert forall|v: u64, w: u64|
        s2.snap.contains_key(v) && #[trigger] s2.snap[v].contains(w) implies 1 <= w < v by {
        if v == n {
            assert(s.active.contains(w));
        }
    }
    assert forall|v: u64, w: u64|
        s2.snap.contains_key(v) && s2.active.contains(w) && w < v implies #[trigger] s2.snap[v]
            .contains(w) by {
        assert(w != n);
        assert(s.active.contains(w));
        if v != n {
            assert(s.snap.contains_key(v));
        }
    }
    // The fresh version has no writes yet, so store clauses are inherited.
    assert forall|k: Seq<u8>, w: u64| #[trigger] s2.store.contains_key((k, w)) implies allocated(
        s2,
        w,
    ) by {
        assert(allocated(s, w));
    }
    assert forall|k: Seq<u8>, w: u64, w2: u64|
        #![trigger s2.store.contains_key((k, w)), s2.store.contains_key((k, w2))]
        s2.store.contains_key((k, w)) && s2.active.contains(w) && s2.store.contains_key(
            (k, w2),
        ) implies w2 <= w by {
        assert(s.store.contains_key((k, w)));
        assert(allocated(s, w));
        assert(w != n);
    }
    assert forall|k: Seq<u8>, w: u64, w2: u64|
        #![trigger s2.store.contains_key((k, w)), s2.store.contains_key((k, w2))]
        s2.store.contains_key((k, w)) && s2.store.contains_key((k, w2)) && w < w2
            implies !s2.snap[w2].contains(w) by {
        assert(allocated(s, w2));
        assert(w2 != n);
        assert(s2.snap[w2] == s.snap[w2]);
    }
    // Snapshot coherence: the only new snapshot is snap[n] == s.active, and
    // for it the claim is exactly the still-active-below clause of inv(s).
    assert forall|u: u64, m: u64, w: u64|
        #![trigger s2.snap[u].contains(w), s2.snap.contains_key(m)]
        s2.snap.contains_key(u) && s2.snap.contains_key(m) && s2.snap[u].contains(w)
            && !s2.snap[u].contains(m) && w < m && m < u implies s2.snap[m].contains(w) by {
        assert(m != n);
        assert(s2.snap[m] == s.snap[m]);
        if u == n {
            // snap[n] = s.active: w active now and w < m, so w was active
            // when m began.
            assert(s.active.contains(w));
            assert(s.snap.contains_key(m));
        } else {
            assert(s2.snap[u] == s.snap[u]);
            assert(s.snap.contains_key(u));
        }
    }
}

proof fn lemma_inv_commit(s: ModelState, v: u64)
    requires
        inv(s),
        can_commit(s, v),
    ensures
        inv(commit(s, v)),
{
    let s2 = commit(s, v);
    assert forall|x: u64| #[trigger] allocated(s2, x) implies s2.snap.contains_key(x) by {
        assert(allocated(s, x));
    }
}

proof fn lemma_inv_rollback(s: ModelState, v: u64)
    requires
        inv(s),
        can_rollback(s, v),
    ensures
        inv(rollback(s, v)),
{
    let s2 = rollback(s, v);
    assert forall|x: u64| #[trigger] allocated(s2, x) implies s2.snap.contains_key(x) by {
        assert(allocated(s, x));
    }
    assert forall|k: Seq<u8>, w: u64| #[trigger] s2.store.contains_key((k, w)) implies allocated(
        s2,
        w,
    ) by {
        assert(s.store.contains_key((k, w)));
    }
    assert forall|k: Seq<u8>, w: u64, w2: u64|
        #![trigger s2.store.contains_key((k, w)), s2.store.contains_key((k, w2))]
        s2.store.contains_key((k, w)) && s2.active.contains(w) && s2.store.contains_key(
            (k, w2),
        ) implies w2 <= w by {
        assert(s.store.contains_key((k, w)) && s.store.contains_key((k, w2)));
    }
    assert forall|k: Seq<u8>, w: u64, w2: u64|
        #![trigger s2.store.contains_key((k, w)), s2.store.contains_key((k, w2))]
        s2.store.contains_key((k, w)) && s2.store.contains_key((k, w2)) && w < w2
            implies !s2.snap[w2].contains(w) by {
        assert(s.store.contains_key((k, w)) && s.store.contains_key((k, w2)));
    }
}

proof fn lemma_inv_write(s: ModelState, v: u64, key: Seq<u8>, value: Option<Seq<u8>>)
    requires
        inv(s),
        can_write(s, v, key),
    ensures
        inv(write(s, v, key, value)),
{
    let lo = choose|lo: u64|
        #[trigger] is_scan_floor(s.snap[v], v, lo) && check_passes(s, v, key, lo);
    thm_conflict_check_exact(s, v, key, lo);
    assert(no_write_conflict(s, v, key));
    let s2 = write(s, v, key, value);
    assert(allocated(s, v));
    assert(s.snap.contains_key(v));
    assert forall|x: u64| #[trigger] allocated(s2, x) implies s2.snap.contains_key(x) by {
        assert(allocated(s, x));
    }
    assert forall|k: Seq<u8>, w: u64| #[trigger] s2.store.contains_key((k, w)) implies allocated(
        s2,
        w,
    ) by {
        if k != key || w != v {
            assert(s.store.contains_key((k, w)));
        }
    }
    // Uncommitted-is-latest: the writer's fresh version is the new maximum
    // (every prior version is visible, hence <= v), and no *other* active
    // transaction holds a version of this key (a visible version is not in
    // the begin snapshot, but any other still-active lower version would be).
    assert forall|k: Seq<u8>, w: u64, w2: u64|
        #![trigger s2.store.contains_key((k, w)), s2.store.contains_key((k, w2))]
        s2.store.contains_key((k, w)) && s2.active.contains(w) && s2.store.contains_key(
            (k, w2),
        ) implies w2 <= w by {
        if k == key {
            if w != v {
                assert(s.store.contains_key((k, w)));
                assert(has_version(s, key, w));
                assert(txn_visible(s, v, w));
                assert(w < v);
                assert(s.snap[v].contains(w));  // still-active-below
                assert(false);
            } else {
                if w2 != v {
                    assert(has_version(s, key, w2));
                    assert(txn_visible(s, v, w2));
                }
            }
        } else {
            assert(s.store.contains_key((k, w)) && s.store.contains_key((k, w2)));
        }
    }
    // No-concurrent-writes: every prior version of this key was visible, so
    // in particular outside the writer's begin snapshot.
    assert forall|k: Seq<u8>, w: u64, w2: u64|
        #![trigger s2.store.contains_key((k, w)), s2.store.contains_key((k, w2))]
        s2.store.contains_key((k, w)) && s2.store.contains_key((k, w2)) && w < w2
            implies !s2.snap[w2].contains(w) by {
        if k == key && w2 == v {
            if w != v {
                assert(has_version(s, key, w));
                assert(txn_visible(s, v, w));
            }
        } else if k == key && w == v {
            assert(s.store.contains_key((k, w2)));
            assert(has_version(s, key, w2));
            assert(txn_visible(s, v, w2));
            assert(false);  // no version above v existed
        } else {
            assert(s.store.contains_key((k, w)) && s.store.contains_key((k, w2)));
        }
    }
}

/// The invariant is preserved by every step: the induction behind the
/// `write_version` comment.
pub proof fn thm_inv_preserved(s: ModelState, s2: ModelState, actor: u64)
    requires
        inv(s),
        step(s, s2, actor),
    ensures
        inv(s2),
{
    if can_begin(s) && actor == s.next && s2 == begin(s) {
        lemma_inv_begin(s);
    } else if can_commit(s, actor) && s2 == commit(s, actor) {
        lemma_inv_commit(s, actor);
    } else if can_rollback(s, actor) && s2 == rollback(s, actor) {
        lemma_inv_rollback(s, actor);
    } else {
        let (key, value) = choose|key: Seq<u8>, value: Option<Seq<u8>>|
            can_write(s, actor, key) && s2 == #[trigger] write(s, actor, key, value);
        lemma_inv_write(s, actor, key, value);
    }
}

// ---- Observers: transactions as readers -----------------------------------

/// A well-formed reader at version `obs` using active-set snapshot `a`: every
/// transaction still active now with a version below `obs` is in `a`. This
/// holds for all three ways the code builds a `TransactionState`, per the
/// three lemmas below, and is preserved by every step
/// (`thm_snapshot_stability`).
pub open spec fn wf_observer(s: ModelState, obs: u64, a: Set<u64>, ro: bool) -> bool {
    &&& obs <= s.next
    &&& forall|w: u64|
        #![trigger s.active.contains(w)]
        #![trigger a.contains(w)]
        s.active.contains(w) && w < obs ==> a.contains(w)
}

/// A live read-write transaction reads via its begin snapshot (Transaction::begin).
pub proof fn lemma_rw_txn_is_observer(s: ModelState, u: u64)
    requires
        inv(s),
        s.active.contains(u),
    ensures
        wf_observer(s, u, s.snap[u], false),
{
    assert(allocated(s, u));
    assert(s.snap.contains_key(u));
}

/// A read-only transaction at the current version with the current active set
/// (Transaction::begin_read_only with as_of None).
pub proof fn lemma_ro_now_is_observer(s: ModelState)
    requires
        inv(s),
    ensures
        wf_observer(s, s.next, s.active, true),
{
}

/// A time-travel transaction at a past version with that version's restored
/// begin snapshot (Transaction::begin_read_only with as_of; a missing
/// TxnActiveSnapshot record decodes as the empty set it was).
pub proof fn lemma_ro_as_of_is_observer(s: ModelState, v: u64)
    requires
        inv(s),
        allocated(s, v),
    ensures
        wf_observer(s, v, s.snap[v], true),
{
    assert(s.snap.contains_key(v));
}

// ---- No dirty reads -------------------------------------------------------

/// An uncommitted transaction's version is invisible to every other reader:
/// nobody can observe in-progress writes (goldenscript anomaly_dirty_read).
pub proof fn thm_uncommitted_invisible(s: ModelState, obs: u64, a: Set<u64>, ro: bool, v: u64)
    requires
        inv(s),
        wf_observer(s, obs, a, ro),
        s.active.contains(v),
        ro || v != obs,
    ensures
        !spec_is_visible(a, obs, ro, v),
{
    if v < obs {
        assert(a.contains(v));
    }
}

/// Contrapositive on the store: every version a reader can see (other than a
/// read-write transaction's own) is committed — reads never return dirty or
/// rolled-back data.
pub proof fn thm_reads_see_only_committed(
    s: ModelState,
    obs: u64,
    a: Set<u64>,
    ro: bool,
    key: Seq<u8>,
    w: u64,
)
    requires
        inv(s),
        wf_observer(s, obs, a, ro),
        has_version(s, key, w),
        spec_is_visible(a, obs, ro, w),
        ro || w != obs,
    ensures
        ended(s, w),
{
    if s.active.contains(w) {
        thm_uncommitted_invisible(s, obs, a, ro, w);
    }
    assert(allocated(s, w));
}

// ---- No dirty writes ------------------------------------------------------

/// When the conflict check lets a write proceed, every existing version of the
/// key (other than the writer's own earlier write) is committed: a write never
/// clobbers another transaction's uncommitted data (anomaly_dirty_write).
pub proof fn thm_no_dirty_write(s: ModelState, v: u64, key: Seq<u8>, w: u64)
    requires
        inv(s),
        can_write(s, v, key),
        has_version(s, key, w),
        w != v,
    ensures
        ended(s, w),
        txn_visible(s, v, w),
{
    let lo = choose|lo: u64|
        #[trigger] is_scan_floor(s.snap[v], v, lo) && check_passes(s, v, key, lo);
    thm_conflict_check_exact(s, v, key, lo);
    assert(txn_visible(s, v, w));
    assert(allocated(s, v));
    assert(s.snap.contains_key(v));
    if s.active.contains(w) {
        assert(w < v);
        assert(s.snap[v].contains(w));  // still-active-below
        assert(false);
    }
    assert(allocated(s, w));
}

/// Restatement of the structural invariant from the `write_version` comment:
/// an uncommitted version is always the latest version of its key.
pub proof fn thm_uncommitted_is_latest(s: ModelState, key: Seq<u8>, w: u64, w2: u64)
    requires
        inv(s),
        has_version(s, key, w),
        s.active.contains(w),
        has_version(s, key, w2),
    ensures
        w2 <= w,
{
}

// ---- Repeatable reads: snapshot stability ---------------------------------

/// A reader's entire visible slice of the store — every (key, version) it can
/// see, with its value — is untouched by any other transaction's begin, write,
/// commit, or rollback, and the reader stays well-formed. Point reads, range
/// scans, and prefix scans are all functions of this slice, so none of them
/// can ever change mid-transaction: no fuzzy reads, no read skew, no phantoms
/// within a snapshot (anomaly_fuzzy_read, anomaly_read_skew,
/// anomaly_phantom_read). In particular a *commit* by another transaction
/// changes nothing either: its writes stay invisible until the reader ends.
pub proof fn thm_snapshot_stability(
    s: ModelState,
    s2: ModelState,
    actor: u64,
    obs: u64,
    a: Set<u64>,
    ro: bool,
)
    requires
        inv(s),
        step(s, s2, actor),
        wf_observer(s, obs, a, ro),
        ro || actor != obs,
    ensures
        wf_observer(s2, obs, a, ro),
        forall|key: Seq<u8>, w: u64|
            #![trigger has_version(s, key, w)]
            #![trigger has_version(s2, key, w)]
            spec_is_visible(a, obs, ro, w) ==> (has_version(s2, key, w) <==> has_version(
                s,
                key,
                w,
            )),
        forall|key: Seq<u8>, w: u64|
            spec_is_visible(a, obs, ro, w) && #[trigger] has_version(s, key, w) ==> s2.store[
                (key, w)
            ] == s.store[(key, w)],
{
    if can_begin(s) && actor == s.next && s2 == begin(s) {
        assert forall|w: u64| #[trigger] s2.active.contains(w) && w < obs implies a.contains(
            w,
        ) by {
            assert(w != s.next);
        }
    } else if can_commit(s, actor) && s2 == commit(s, actor) {
    } else if can_rollback(s, actor) && s2 == rollback(s, actor) {
        thm_uncommitted_invisible(s, obs, a, ro, actor);
        assert forall|key: Seq<u8>, w: u64|
            spec_is_visible(a, obs, ro, w) && #[trigger] has_version(s, key, w) implies s2.store[
            (key, w)
        ] == s.store[(key, w)] by {
            assert(w != actor);
        }
    } else {
        let (key0, value0) = choose|key0: Seq<u8>, value0: Option<Seq<u8>>|
            can_write(s, actor, key0) && s2 == #[trigger] write(s, actor, key0, value0);
        thm_uncommitted_invisible(s, obs, a, ro, actor);
        assert forall|key: Seq<u8>, w: u64|
            spec_is_visible(a, obs, ro, w) && #[trigger] has_version(s, key, w) implies s2.store[
            (key, w)
        ] == s.store[(key, w)] by {
            assert(w != actor);
        }
    }
}

/// The read a transaction performs — the greatest visible version of a key,
/// and its value — is identical before and after any other transaction's
/// step: reads are repeatable for the whole life of the snapshot.
pub open spec fn is_read_result(
    s: ModelState,
    obs: u64,
    a: Set<u64>,
    ro: bool,
    key: Seq<u8>,
    w: u64,
) -> bool {
    &&& has_version(s, key, w)
    &&& spec_is_visible(a, obs, ro, w)
    &&& forall|w2: u64|
        #[trigger] has_version(s, key, w2) && spec_is_visible(a, obs, ro, w2) ==> w2 <= w
}

pub proof fn thm_repeatable_read(
    s: ModelState,
    s2: ModelState,
    actor: u64,
    obs: u64,
    a: Set<u64>,
    ro: bool,
    key: Seq<u8>,
    w: u64,
)
    requires
        inv(s),
        step(s, s2, actor),
        wf_observer(s, obs, a, ro),
        ro || actor != obs,
    ensures
        is_read_result(s, obs, a, ro, key, w) <==> is_read_result(s2, obs, a, ro, key, w),
        is_read_result(s, obs, a, ro, key, w) ==> s2.store[(key, w)] == s.store[(key, w)],
{
    thm_snapshot_stability(s, s2, actor, obs, a, ro);
    if is_read_result(s, obs, a, ro, key, w) {
        assert forall|w2: u64|
            #[trigger] has_version(s2, key, w2) && spec_is_visible(a, obs, ro, w2) implies w2
            <= w by {
            assert(has_version(s, key, w2));
        }
        assert(is_read_result(s2, obs, a, ro, key, w));
    }
    if is_read_result(s2, obs, a, ro, key, w) {
        assert forall|w2: u64|
            #[trigger] has_version(s, key, w2) && spec_is_visible(a, obs, ro, w2) implies w2
            <= w by {
            assert(has_version(s2, key, w2));
        }
        assert(is_read_result(s, obs, a, ro, key, w));
    }
}

// ---- Write-write conflicts: first writer wins -----------------------------

/// For any two versions of the same key ever recorded, the earlier writer had
/// committed before the later writer began — and therefore the earlier write
/// was *visible* to the later writer. Concurrent transactions can never both
/// write a key (the later one hits Error::Serialization instead), so no
/// update is ever overwritten by a transaction that couldn't see it
/// (anomaly_lost_update, set_conflict, delete_conflict).
pub proof fn thm_first_writer_wins(s: ModelState, key: Seq<u8>, w1: u64, w2: u64)
    requires
        inv(s),
        has_version(s, key, w1),
        has_version(s, key, w2),
        w1 < w2,
    ensures
        !s.snap[w2].contains(w1),
        ended(s, w1),
        txn_visible(s, w2, w1),
{
    assert(allocated(s, w1));
    if s.active.contains(w1) {
        assert(w2 <= w1);  // uncommitted-is-latest
        assert(false);
    }
}

// ---- Rollback restores invisibility ---------------------------------------

/// Rollback removes exactly the transaction's own writes: afterwards no trace
/// of its version remains, and every other key/version survives untouched.
/// Combined with `thm_uncommitted_invisible` (nobody ever saw those writes
/// while it was active) and `thm_snapshot_stability` (the rollback step
/// changes no other reader's view), the transaction leaves no observable
/// trace whatsoever.
pub proof fn thm_rollback_erases(s: ModelState, v: u64)
    requires
        inv(s),
        can_rollback(s, v),
    ensures
        forall|key: Seq<u8>| !has_version(rollback(s, v), key, v),
        forall|key: Seq<u8>, w: u64|
            w != v ==> (#[trigger] has_version(rollback(s, v), key, w) <==> has_version(
                s,
                key,
                w,
            )),
        forall|key: Seq<u8>, w: u64|
            w != v && #[trigger] has_version(s, key, w) ==> rollback(s, v).store[(key, w)]
                == s.store[(key, w)],
{
}

/// A rolled-back version never reappears. After rollback(v), the version has
/// ended and holds no writes (thm_rollback_erases); this shows every further
/// step keeps it that way: versions are never reused (begin allocates fresh
/// ones) and writers only write at their own live version.
pub proof fn thm_rolled_back_stays_gone(s: ModelState, s2: ModelState, actor: u64, v: u64)
    requires
        inv(s),
        step(s, s2, actor),
        ended(s, v),
        forall|key: Seq<u8>| !has_version(s, key, v),
    ensures
        ended(s2, v),
        forall|key: Seq<u8>| !has_version(s2, key, v),
{
    assert forall|key: Seq<u8>| !has_version(s2, key, v) by {
        assert(!has_version(s, key, v));
        if !(can_begin(s) && actor == s.next && s2 == begin(s)) && !(can_commit(s, actor) && s2
            == commit(s, actor)) && !(can_rollback(s, actor) && s2 == rollback(s, actor)) {
            let (key0, value0) = choose|key0: Seq<u8>, value0: Option<Seq<u8>>|
                can_write(s, actor, key0) && s2 == #[trigger] write(s, actor, key0, value0);
            assert(s.active.contains(actor));
            assert(actor != v);
        }
    }
}

// ===========================================================================
// Refinement: the executable code refines the model
// ===========================================================================
//
// Everything above reasons about `ModelState`. This section closes the gap to
// the running code: the `Transaction` methods delegate to *verified*
// executable functions (`vbegin`, `vbegin_read_only`, `vget`, `vwrite`,
// `vcommit`, `vrollback`) that perform the real engine-call sequences and are
// proven to transform the engine's decoded contents by exactly the model
// transitions.
//
// The engine is abstracted as a decoded view: a spec-level map `EngView` from
// decoded MVCC keys (`KeyS`, mirroring `Key`) to decoded values (`ValS`).
// `abs: EngView -> ModelState` reads the model state off that view, and
// `view_inv` is the refinement invariant: the model invariant `inv` holds of
// `abs(view)`, and the `TxnWrite` bookkeeping records cover exactly the
// writes of live transactions (which is what makes rollback complete).
//
// The trusted boundary is the `EngineOps` facade below plus the `h_*` adapter
// functions marked `#[verifier::external_body]`: their `ensures` clauses
// axiomatize how each raw engine operation transforms the decoded view. This
// trusts (a) the storage engine to behave as a lexicographically ordered
// key/value map, and (b) the keycode/bincode codecs, whose core transforms
// are themselves verified in `encoding::keycode` (in particular, that encoded
// `Key::Version(key, version)` keys sort by key then version, which is what
// makes "last entry of the range scan" mean "greatest version"). Everything
// else — visibility, the conflict decision, version allocation, snapshot
// handling, commit/rollback bookkeeping — is verified.
//
// TOP-LEVEL GUARANTEE. `lemma_abs_empty` shows a fresh database satisfies
// `view_inv` and abstracts to `init()`. Every mutation of MVCC state goes
// through the verified operations, each of which preserves `view_inv` and
// performs exactly its model transition, while unversioned writes stay off
// the MVCC key space (`lemma_unversioned_invisible`). By induction over the
// engine's history, at every operation boundary the engine contents decode
// to a reachable model state — so every theorem above about reachable model
// states (conflict-check exactness, no dirty reads or writes, snapshot
// stability, first-writer-wins, rollback erasure) holds of the running
// system.
//
// Remaining unverified surface: `Transaction::resume` trusts the
// `TransactionState` handed to it (a documented toyDB design decision for
// crossing the Raft boundary); `ScanIterator`/`scan_prefix` use the verified
// `is_visible_core` for visibility but their batching machinery is
// unverified (`thm_snapshot_stability` covers the visible slice they draw
// from); `MVCC::status` and the unversioned get/set are direct engine
// accesses that never touch versioned state. One intentional behavior
// difference: `vget` decodes each scanned version's value eagerly, so a
// corrupt value below the visible version now errors where it previously
// went unread; and `vbegin` returns an error on u64 version-counter
// overflow where the old code would panic (both unreachable in practice).

// ---- The decoded engine view and abstraction function ---------------------

/// Decoded MVCC engine keys: the spec-level mirror of `Key`.
pub enum KeyS {
    NextVersion,
    TxnActive(u64),
    TxnActiveSnapshot(u64),
    TxnWrite(u64, Seq<u8>),
    Version(Seq<u8>, u64),
    Unversioned(Seq<u8>),
}

/// Decoded MVCC engine values, by key type: `Version::encode` for
/// NextVersion, the empty value of TxnActive/TxnWrite records,
/// `BTreeSet::encode` for snapshots, bincoded `Option<Vec<u8>>` for versioned
/// writes (None = tombstone), and raw bytes for unversioned keys.
pub enum ValS {
    U64(u64),
    Unit,
    VSet(Set<u64>),
    Bytes(Option<Seq<u8>>),
    Raw(Seq<u8>),
}

/// The engine's decoded contents.
pub type EngView = Map<KeyS, ValS>;

/// The versions `[1, n)`, i.e. all versions allocated when NextVersion is n.
pub open spec fn version_range(n: u64) -> Set<u64>
    decreases n,
{
    if n <= 1 {
        Set::empty()
    } else {
        version_range((n - 1) as u64).insert((n - 1) as u64)
    }
}

pub proof fn lemma_version_range(n: u64)
    ensures
        forall|v: u64| #[trigger] version_range(n).contains(v) <==> 1 <= v < n,
    decreases n,
{
    if n > 1 {
        lemma_version_range((n - 1) as u64);
        assert forall|v: u64| #[trigger] version_range(n).contains(v) <==> 1 <= v < n by {
            assert(version_range(n) == version_range((n - 1) as u64).insert((n - 1) as u64));
        }
    } else {
        assert(version_range(n) == Set::<u64>::empty());
    }
}

/// The next version: the decoded NextVersion record, or 1 if absent (a fresh
/// database), exactly as the code defaults.
pub open spec fn abs_next(view: EngView) -> u64 {
    if view.contains_key(KeyS::NextVersion) {
        match view[KeyS::NextVersion] {
            ValS::U64(n) => n,
            _ => 1,
        }
    } else {
        1
    }
}

/// The active set: the versions with a TxnActive record.
pub open spec fn abs_active(view: EngView) -> Set<u64> {
    view.dom().filter(|k: KeyS| k is TxnActive).map(
        |k: KeyS|
            match k {
                KeyS::TxnActive(v) => v,
                _ => 0u64,
            },
    )
}

pub proof fn lemma_abs_active(view: EngView, v: u64)
    ensures
        abs_active(view).contains(v) <==> view.contains_key(KeyS::TxnActive(v)),
{
    broadcast use vstd::set::Set::lemma_map_contains;

    if view.contains_key(KeyS::TxnActive(v)) {
        assert(view.dom().filter(|k: KeyS| k is TxnActive).contains(KeyS::TxnActive(v)));
    }
}

/// The begin snapshot recorded for version v: the decoded TxnActiveSnapshot
/// record, or empty if absent — the record is only written when the set was
/// non-empty, and the code reads a missing record as empty.
pub open spec fn abs_snap_at(view: EngView, v: u64) -> Set<u64> {
    if view.contains_key(KeyS::TxnActiveSnapshot(v)) {
        match view[KeyS::TxnActiveSnapshot(v)] {
            ValS::VSet(a) => a,
            _ => Set::empty(),
        }
    } else {
        Set::empty()
    }
}

/// The begin snapshots of all allocated versions.
pub open spec fn abs_snap(view: EngView) -> Map<u64, Set<u64>> {
    Map::new(version_range(abs_next(view)), |v: u64| abs_snap_at(view, v))
}

pub proof fn lemma_abs_snap(view: EngView, v: u64)
    ensures
        abs_snap(view).contains_key(v) <==> 1 <= v < abs_next(view),
        abs_snap(view).contains_key(v) ==> abs_snap(view)[v] == abs_snap_at(view, v),
{
    broadcast use vstd::map::lemma_map_new_domain, vstd::map::lemma_map_new_index;

    lemma_version_range(abs_next(view));
}

/// The (key, version) pairs with a Version record.
pub open spec fn abs_store_dom(view: EngView) -> Set<(Seq<u8>, u64)> {
    view.dom().filter(|k: KeyS| k is Version).map(
        |k: KeyS|
            match k {
                KeyS::Version(key, v) => (key, v),
                _ => (Seq::<u8>::empty(), 0u64),
            },
    )
}

pub proof fn lemma_abs_store_dom(view: EngView, key: Seq<u8>, v: u64)
    ensures
        abs_store_dom(view).contains((key, v)) <==> view.contains_key(KeyS::Version(key, v)),
{
    broadcast use vstd::set::Set::lemma_map_contains;

    if view.contains_key(KeyS::Version(key, v)) {
        assert(view.dom().filter(|k: KeyS| k is Version).contains(KeyS::Version(key, v)));
    }
}

/// The decoded value of a Version record (None if malformed, which
/// `view_inv`-reachable views never are for records the code reads).
pub open spec fn abs_store_at(view: EngView, p: (Seq<u8>, u64)) -> Option<Seq<u8>> {
    match view[KeyS::Version(p.0, p.1)] {
        ValS::Bytes(o) => o,
        _ => None,
    }
}

/// The versioned store.
pub open spec fn abs_store(view: EngView) -> Map<(Seq<u8>, u64), Option<Seq<u8>>> {
    Map::new(abs_store_dom(view), |p: (Seq<u8>, u64)| abs_store_at(view, p))
}

pub proof fn lemma_abs_store(view: EngView, key: Seq<u8>, v: u64)
    ensures
        abs_store(view).contains_key((key, v)) <==> view.contains_key(KeyS::Version(key, v)),
        abs_store(view).contains_key((key, v)) ==> abs_store(view)[(key, v)] == abs_store_at(
            view,
            (key, v),
        ),
{
    broadcast use vstd::map::lemma_map_new_domain, vstd::map::lemma_map_new_index;

    lemma_abs_store_dom(view, key, v);
}

/// The abstraction function: the model state an engine's decoded contents
/// represent.
pub open spec fn abs(view: EngView) -> ModelState {
    ModelState {
        next: abs_next(view),
        active: abs_active(view),
        snap: abs_snap(view),
        store: abs_store(view),
    }
}

/// The refinement invariant on engine contents:
/// * the model invariant holds of the abstracted state;
/// * TxnActive and TxnActiveSnapshot records only exist for allocated
///   versions (so scanning TxnActive recovers exactly `abs_active`, and a
///   fresh begin never finds a stale snapshot record at its new version);
/// * every write of a live transaction has its TxnWrite bookkeeping record,
///   which is what makes rollback able to find and erase all of them.
pub open spec fn view_inv(view: EngView) -> bool {
    &&& inv(abs(view))
    &&& forall|v: u64| #[trigger] view.contains_key(KeyS::TxnActive(v)) ==> 1 <= v < abs_next(view)
    &&& forall|v: u64|
        #[trigger] view.contains_key(KeyS::TxnActiveSnapshot(v)) ==> 1 <= v < abs_next(view)
    &&& forall|key: Seq<u8>, v: u64|
        #![auto]
        view.contains_key(KeyS::Version(key, v)) && view.contains_key(KeyS::TxnActive(v))
            ==> view.contains_key(KeyS::TxnWrite(v, key))
}

/// A fresh (empty) database abstracts to the initial model state and
/// satisfies the refinement invariant: the induction starts here.
pub proof fn lemma_abs_empty()
    ensures
        abs(Map::empty()) == init(),
        view_inv(Map::empty()),
{
    let view = Map::<KeyS, ValS>::empty();
    assert forall|v: u64| !(#[trigger] abs_active(view).contains(v)) by {
        lemma_abs_active(view, v);
    }
    assert(abs_active(view) =~= init().active);
    lemma_version_range(1);
    assert forall|v: u64| !(#[trigger] abs_snap(view).contains_key(v)) by {
        lemma_abs_snap(view, v);
    }
    assert(abs_snap(view) =~~= init().snap);
    assert forall|p: (Seq<u8>, u64)| !(#[trigger] abs_store(view).contains_key(p)) by {
        lemma_abs_store(view, p.0, p.1);
    }
    assert(abs_store(view) =~~= init().store);
    lemma_inv_init();
}

/// Unversioned keys are invisible to the abstraction: the unversioned
/// get/set operations (and any other engine traffic that stays off the MVCC
/// key space) preserve the refinement invariant and the abstract state.
pub proof fn lemma_unversioned_invisible(view: EngView, key: Seq<u8>, value: Seq<u8>)
    ensures
        abs(view.insert(KeyS::Unversioned(key), ValS::Raw(value))) == abs(view),
        view_inv(view) ==> view_inv(view.insert(KeyS::Unversioned(key), ValS::Raw(value))),
{
    let view2 = view.insert(KeyS::Unversioned(key), ValS::Raw(value));
    assert(abs_next(view2) == abs_next(view));
    assert forall|v: u64| #[trigger] abs_active(view2).contains(v) <==> abs_active(view).contains(
        v,
    ) by {
        lemma_abs_active(view2, v);
        lemma_abs_active(view, v);
    }
    assert(abs_active(view2) =~= abs_active(view));
    assert forall|v: u64|
        #[trigger] abs_snap(view2).contains_key(v) <==> abs_snap(view).contains_key(v) by {
        lemma_abs_snap(view2, v);
        lemma_abs_snap(view, v);
    }
    assert forall|v: u64| #[trigger] abs_snap(view2).contains_key(v) implies abs_snap(view2)[v]
        == abs_snap(view)[v] by {
        lemma_abs_snap(view2, v);
        lemma_abs_snap(view, v);
    }
    assert(abs_snap(view2) =~~= abs_snap(view));
    assert forall|p: (Seq<u8>, u64)|
        #[trigger] abs_store(view2).contains_key(p) <==> abs_store(view).contains_key(p) by {
        lemma_abs_store(view2, p.0, p.1);
        lemma_abs_store(view, p.0, p.1);
    }
    assert forall|p: (Seq<u8>, u64)| #[trigger] abs_store(view2).contains_key(p) implies abs_store(
        view2,
    )[p] == abs_store(view)[p] by {
        lemma_abs_store(view2, p.0, p.1);
        lemma_abs_store(view, p.0, p.1);
    }
    assert(abs_store(view2) =~~= abs_store(view));
}

// ---- The trusted engine boundary ------------------------------------------
//
// `hview` is the uninterpreted "decoded contents" of the engine behind a
// handle. The `h_*` functions below are the ONLY way the verified core
// touches the engine; each is `external_body` with an `ensures` contract
// axiomatizing (TRUSTED) what the underlying engine operation and codec do
// to the decoded view. Read operations leave the view unchanged. On `Err`,
// write operations promise nothing (a failed engine write may leave
// arbitrary state) and the transaction aborts with the error.

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExError(Error);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExEngineHandle<'a>(EngineHandle<'a>);

/// std Result with toyDB's Error, spelled explicitly because the crate's
/// single-parameter `Result` alias shadows the std form in this module.
pub type EResult<T> = core::result::Result<T, Error>;

/// The decoded contents of the engine behind the handle.
pub uninterp spec fn hview(h: EngineHandle<'_>) -> EngView;

/// TRUSTED: NextVersion holds the next version as a `Version::encode` value,
/// defaulting to 1 when absent.
#[verifier::external_body]
fn h_get_next_version(h: &mut EngineHandle<'_>) -> (r: EResult<u64>)
    ensures
        hview(*final(h)) == hview(*old(h)),
        match r {
            Ok(n) => n == abs_next(hview(*final(h))),
            Err(_) => true,
        },
{
    match h.inner.get_raw(&Key::NextVersion.encode())? {
        Some(ref v) => Version::decode(v),
        None => Ok(1),
    }
}

/// TRUSTED: writing NextVersion updates exactly that record.
#[verifier::external_body]
fn h_set_next_version(h: &mut EngineHandle<'_>, n: u64) -> (r: EResult<()>)
    ensures
        r is Ok ==> hview(*final(h)) == hview(*old(h)).insert(KeyS::NextVersion, ValS::U64(n)),
{
    h.inner.set_raw(&Key::NextVersion.encode(), n.encode())
}

/// TRUSTED: scanning the TxnActive prefix yields exactly the versions with a
/// TxnActive record.
#[verifier::external_body]
fn h_scan_active(h: &mut EngineHandle<'_>) -> (r: EResult<Vec<u64>>)
    ensures
        hview(*final(h)) == hview(*old(h)),
        match r {
            Ok(vs) => forall|v: u64|
                #[trigger] vs@.contains(v) <==> hview(*final(h)).contains_key(KeyS::TxnActive(v)),
            Err(_) => true,
        },
{
    h.inner.scan_active_versions()
}

/// TRUSTED: reading a TxnActiveSnapshot record decodes the recorded set.
#[verifier::external_body]
fn h_get_txn_active_snapshot(h: &mut EngineHandle<'_>, v: u64) -> (r: EResult<
    Option<BTreeSet<u64>>,
>)
    ensures
        hview(*final(h)) == hview(*old(h)),
        match r {
            Ok(Some(b)) => hview(*final(h)).contains_key(KeyS::TxnActiveSnapshot(v)) && hview(*final(h))[
                KeyS::TxnActiveSnapshot(v)
            ] == ValS::VSet(b@),
            Ok(None) => !hview(*final(h)).contains_key(KeyS::TxnActiveSnapshot(v)),
            Err(_) => true,
        },
{
    match h.inner.get_raw(&Key::TxnActiveSnapshot(v).encode())? {
        Some(ref value) => Ok(Some(BTreeSet::<Version>::decode(value)?)),
        None => Ok(None),
    }
}

/// TRUSTED: writing a TxnActiveSnapshot record stores the encoded set.
#[verifier::external_body]
fn h_set_txn_active_snapshot(h: &mut EngineHandle<'_>, v: u64, set: &BTreeSet<u64>) -> (r: EResult<
    (),
>)
    ensures
        r is Ok ==> hview(*final(h)) == hview(*old(h)).insert(
            KeyS::TxnActiveSnapshot(v),
            ValS::VSet(set@),
        ),
{
    h.inner.set_raw(&Key::TxnActiveSnapshot(v).encode(), set.encode())
}

/// TRUSTED: registering a transaction writes its TxnActive record.
#[verifier::external_body]
fn h_set_txn_active(h: &mut EngineHandle<'_>, v: u64) -> (r: EResult<()>)
    ensures
        r is Ok ==> hview(*final(h)) == hview(*old(h)).insert(KeyS::TxnActive(v), ValS::Unit),
{
    h.inner.set_raw(&Key::TxnActive(v).encode(), vec![])
}

/// TRUSTED: unregistering a transaction deletes its TxnActive record.
#[verifier::external_body]
fn h_delete_txn_active(h: &mut EngineHandle<'_>, v: u64) -> (r: EResult<()>)
    ensures
        r is Ok ==> hview(*final(h)) == hview(*old(h)).remove(KeyS::TxnActive(v)),
{
    h.inner.delete_raw(&Key::TxnActive(v).encode())
}

/// TRUSTED: the write-conflict scan. Scanning Version(key, lo)..=Version(key,
/// u64::MAX) and taking the last entry yields the greatest version of `key`
/// at or above `lo`, by the keycode ordering of Version keys (key first,
/// version second — see `encoding::keycode`).
#[verifier::external_body]
fn h_scan_last_version_in_range(h: &mut EngineHandle<'_>, key: &[u8], lo: u64) -> (r: EResult<
    Option<u64>,
>)
    ensures
        hview(*final(h)) == hview(*old(h)),
        match r {
            Ok(Some(m)) => hview(*final(h)).contains_key(KeyS::Version(key@, m)) && lo <= m && forall|
                w: u64,
            |
                #![auto]
                hview(*final(h)).contains_key(KeyS::Version(key@, w)) && lo <= w ==> w <= m,
            Ok(None) => forall|w: u64|
                #![auto]
                lo <= w ==> !hview(*final(h)).contains_key(KeyS::Version(key@, w)),
            Err(_) => true,
        },
{
    h.inner.scan_last_version_in_range(key, lo)
}

/// TRUSTED: recording a write's TxnWrite bookkeeping record.
#[verifier::external_body]
fn h_set_txn_write(h: &mut EngineHandle<'_>, v: u64, key: &[u8]) -> (r: EResult<()>)
    ensures
        r is Ok ==> hview(*final(h)) == hview(*old(h)).insert(KeyS::TxnWrite(v, key@), ValS::Unit),
{
    h.inner.set_raw(&Key::TxnWrite(v, key.into()).encode(), vec![])
}

/// TRUSTED: writing a versioned value stores its bincoded Option (None being
/// a deletion tombstone).
#[verifier::external_body]
fn h_set_version(h: &mut EngineHandle<'_>, key: &[u8], v: u64, value: &Option<Vec<u8>>) -> (r:
    EResult<()>)
    ensures
        r is Ok ==> hview(*final(h)) == hview(*old(h)).insert(
            KeyS::Version(key@, v),
            ValS::Bytes(value.deep_view()),
        ),
{
    h.inner.set_raw(&Key::Version(key.into(), v).encode(), bincode::serialize(value))
}

/// TRUSTED: deleting a TxnWrite record removes exactly it.
#[verifier::external_body]
fn h_delete_txn_write(h: &mut EngineHandle<'_>, v: u64, key: &[u8]) -> (r: EResult<()>)
    ensures
        r is Ok ==> hview(*final(h)) == hview(*old(h)).remove(KeyS::TxnWrite(v, key@)),
{
    h.inner.delete_raw(&Key::TxnWrite(v, key.into()).encode())
}

/// TRUSTED: deleting a versioned record removes exactly it.
#[verifier::external_body]
fn h_delete_version(h: &mut EngineHandle<'_>, key: &[u8], v: u64) -> (r: EResult<()>)
    ensures
        r is Ok ==> hview(*final(h)) == hview(*old(h)).remove(KeyS::Version(key@, v)),
{
    h.inner.delete_raw(&Key::Version(key.into(), v).encode())
}

/// TRUSTED: scanning the TxnWrite(version) prefix yields exactly the user
/// keys the transaction has written.
#[verifier::external_body]
fn h_scan_txn_write_keys(h: &mut EngineHandle<'_>, v: u64) -> (r: EResult<Vec<Vec<u8>>>)
    ensures
        hview(*final(h)) == hview(*old(h)),
        match r {
            Ok(ks) => (forall|i: int|
                0 <= i < ks@.len() ==> hview(*final(h)).contains_key(
                    KeyS::TxnWrite(v, #[trigger] ks@[i]@),
                )) && (forall|key: Seq<u8>|
                #[trigger] hview(*final(h)).contains_key(KeyS::TxnWrite(v, key)) ==> exists|i: int| #![auto] 0 <= i < ks@.len() && ks@[i]@ == key),
            Err(_) => true,
        },
{
    h.inner.scan_txn_write_keys(v)
}

/// TRUSTED: the read scan. Scanning Version(key, 0)..=Version(key, hi) in
/// reverse yields all versions of `key` up to `hi`, latest first, with their
/// decoded values.
#[verifier::external_body]
fn h_scan_versions_desc(h: &mut EngineHandle<'_>, key: &[u8], hi: u64) -> (r: EResult<
    Vec<(u64, Option<Vec<u8>>)>,
>)
    ensures
        hview(*final(h)) == hview(*old(h)),
        match r {
            Ok(es) => (forall|i: int|
                0 <= i < es@.len() ==> (#[trigger] es@[i]).0 <= hi && hview(*final(h)).contains_key(
                    KeyS::Version(key@, es@[i].0),
                ) && hview(*final(h))[KeyS::Version(key@, es@[i].0)] == ValS::Bytes(es@[i].1.deep_view()))
                && (forall|i: int, j: int| #![auto] 0 <= i < j < es@.len() ==> es@[i].0 > es@[j].0) && (
            forall|w: u64|
                w <= hi && #[trigger] hview(*final(h)).contains_key(KeyS::Version(key@, w))
                    ==> exists|i: int| #![auto] 0 <= i < es@.len() && es@[i].0 == w),
            Err(_) => true,
        },
{
    h.inner.scan_versions_desc(key, hi)
}

/// TRUSTED: constructs the version-overflow error (the u64 version counter
/// would wrap; unreachable in practice).
#[verifier::external_body]
fn err_version_overflow() -> Error {
    Error::InvalidData("version number overflow".to_string())
}

/// TRUSTED: constructs the begin_as_of error for a nonexistent version, with
/// the same message the code has always produced.
#[verifier::external_body]
fn err_version_does_not_exist(v: u64) -> Error {
    Error::InvalidInput(format!("version {v} does not exist"))
}

// ---- Verified transaction operations --------------------------------------

/// The abstraction reads only the NextVersion, TxnActive, TxnActiveSnapshot
/// and Version records: two views that agree on those abstract identically.
/// (In particular, TxnWrite bookkeeping and unversioned keys are invisible.)
proof fn lemma_abs_depends(view: EngView, view2: EngView)
    requires
        view2.contains_key(KeyS::NextVersion) == view.contains_key(KeyS::NextVersion),
        view.contains_key(KeyS::NextVersion) ==> view2[KeyS::NextVersion]
            == view[KeyS::NextVersion],
        forall|v: u64|
            #[trigger] view2.contains_key(KeyS::TxnActive(v)) <==> view.contains_key(
                KeyS::TxnActive(v),
            ),
        forall|v: u64|
            (#[trigger] view2.contains_key(KeyS::TxnActiveSnapshot(v)) <==> view.contains_key(
                KeyS::TxnActiveSnapshot(v),
            )) && (view.contains_key(KeyS::TxnActiveSnapshot(v)) ==> view2[
                KeyS::TxnActiveSnapshot(v)
            ] == view[KeyS::TxnActiveSnapshot(v)]),
        forall|key: Seq<u8>, v: u64|
            (#[trigger] view2.contains_key(KeyS::Version(key, v)) <==> view.contains_key(
                KeyS::Version(key, v),
            )) && (view.contains_key(KeyS::Version(key, v)) ==> view2[KeyS::Version(key, v)]
                == view[KeyS::Version(key, v)]),
    ensures
        abs(view2) == abs(view),
{
    assert(abs_next(view2) == abs_next(view));
    assert forall|v: u64| #[trigger] abs_active(view2).contains(v) <==> abs_active(view).contains(
        v,
    ) by {
        lemma_abs_active(view2, v);
        lemma_abs_active(view, v);
    }
    assert(abs_active(view2) =~= abs_active(view));
    assert forall|v: u64|
        #[trigger] abs_snap(view2).contains_key(v) <==> abs_snap(view).contains_key(v) by {
        lemma_abs_snap(view2, v);
        lemma_abs_snap(view, v);
    }
    assert forall|v: u64| #[trigger] abs_snap(view2).contains_key(v) implies abs_snap(view2)[v]
        == abs_snap(view)[v] by {
        lemma_abs_snap(view2, v);
        lemma_abs_snap(view, v);
        assert(view2.contains_key(KeyS::TxnActiveSnapshot(v)) == view.contains_key(
            KeyS::TxnActiveSnapshot(v),
        ));
        assert(abs_snap_at(view2, v) == abs_snap_at(view, v));
    }
    assert(abs_snap(view2) =~~= abs_snap(view));
    assert forall|p: (Seq<u8>, u64)|
        #[trigger] abs_store(view2).contains_key(p) <==> abs_store(view).contains_key(p) by {
        lemma_abs_store(view2, p.0, p.1);
        lemma_abs_store(view, p.0, p.1);
    }
    assert forall|p: (Seq<u8>, u64)| #[trigger] abs_store(view2).contains_key(p) implies abs_store(
        view2,
    )[p] == abs_store(view)[p] by {
        lemma_abs_store(view2, p.0, p.1);
        lemma_abs_store(view, p.0, p.1);
        assert(view2.contains_key(KeyS::Version(p.0, p.1)) == view.contains_key(
            KeyS::Version(p.0, p.1),
        ));
        assert(abs_store_at(view2, p) == abs_store_at(view, p));
    }
    assert(abs_store(view2) =~~= abs_store(view));
}

/// Verified core of `Transaction::commit` (read-write): delete the
/// transaction's TxnWrite records (no longer needed once it can no longer
/// roll back), then delete its TxnActive record — the single step that
/// atomically publishes its writes. Refines the model `commit` transition.
#[allow(clippy::question_mark)]
fn vcommit(h: &mut EngineHandle<'_>, version: u64) -> (r: EResult<()>)
    requires
        view_inv(hview(*old(h))),
        abs(hview(*old(h))).active.contains(version),
    ensures
        r is Ok ==> view_inv(hview(*final(h))) && abs(hview(*final(h))) == commit(
            abs(hview(*old(h))),
            version,
        ),
{
    let keys = match h_scan_txn_write_keys(h, version) {
        Ok(ks) => ks,
        Err(e) => return Err(e),
    };
    let ghost view0 = hview(*h);
    let mut i: usize = 0;
    while i < keys.len()
        invariant
            i <= keys.len(),
            // Everything the abstraction and the invariant read is untouched,
            // as are other transactions' TxnWrite records.
            hview(*h).contains_key(KeyS::NextVersion) == view0.contains_key(KeyS::NextVersion),
            view0.contains_key(KeyS::NextVersion) ==> hview(*h)[KeyS::NextVersion] == view0[
                KeyS::NextVersion
            ],
            forall|v: u64|
                #[trigger] hview(*h).contains_key(KeyS::TxnActive(v)) <==> view0.contains_key(
                    KeyS::TxnActive(v),
                ),
            forall|v: u64|
                (#[trigger] hview(*h).contains_key(KeyS::TxnActiveSnapshot(v))
                    <==> view0.contains_key(KeyS::TxnActiveSnapshot(v))) && (view0.contains_key(
                    KeyS::TxnActiveSnapshot(v),
                ) ==> hview(*h)[KeyS::TxnActiveSnapshot(v)] == view0[KeyS::TxnActiveSnapshot(v)]),
            forall|key: Seq<u8>, v: u64|
                (#[trigger] hview(*h).contains_key(KeyS::Version(key, v)) <==> view0.contains_key(
                    KeyS::Version(key, v),
                )) && (view0.contains_key(KeyS::Version(key, v)) ==> hview(*h)[
                    KeyS::Version(key, v)
                ] == view0[KeyS::Version(key, v)]),
            forall|v2: u64, key: Seq<u8>|
                v2 != version ==> (#[trigger] hview(*h).contains_key(KeyS::TxnWrite(v2, key))
                    <==> view0.contains_key(KeyS::TxnWrite(v2, key))),
            // Our TxnWrite records only disappear, and the first i are gone.
            forall|key: Seq<u8>|
                #[trigger] hview(*h).contains_key(KeyS::TxnWrite(version, key))
                    ==> view0.contains_key(KeyS::TxnWrite(version, key)),
            forall|j: int|
                0 <= j < i ==> !hview(*h).contains_key(KeyS::TxnWrite(version, #[trigger] keys@[j]@)),
            // The scan listed every TxnWrite record of this transaction.
            forall|key: Seq<u8>|
                #[trigger] view0.contains_key(KeyS::TxnWrite(version, key)) ==> exists|j: int| #![auto] 0 <= j < keys@.len() && keys@[j]@ == key,
        decreases keys.len() - i,
    {
        match h_delete_txn_write(h, version, keys[i].as_slice()) {
            Ok(_) => {},
            Err(e) => return Err(e),
        }
        i += 1;
    }
    proof {
        lemma_abs_depends(view0, hview(*h));
    }
    let ghost view_l = hview(*h);
    match h_delete_txn_active(h, version) {
        Ok(_) => {},
        Err(e) => return Err(e),
    }
    proof {
        let s0 = abs(view0);
        let view_f = hview(*h);
        // No TxnWrite record of this transaction survived the loop.
        assert forall|key: Seq<u8>| !(#[trigger] view_f.contains_key(
            KeyS::TxnWrite(version, key),
        )) by {
            if view_l.contains_key(KeyS::TxnWrite(version, key)) {
                let j = choose|j: int| #![auto] 0 <= j < keys@.len() && keys@[j]@ == key;
                assert(!view_l.contains_key(KeyS::TxnWrite(version, keys@[j]@)));
            }
        }
        // The abstraction: only the active set changes, dropping version.
        assert(abs_next(view_f) == abs_next(view_l));
        assert forall|v: u64|
            #[trigger] abs_active(view_f).contains(v) <==> abs_active(view_l).remove(
                version,
            ).contains(v) by {
            lemma_abs_active(view_f, v);
            lemma_abs_active(view_l, v);
        }
        assert(abs_active(view_f) =~= abs_active(view_l).remove(version));
        assert forall|v: u64|
            #[trigger] abs_snap(view_f).contains_key(v) <==> abs_snap(view_l).contains_key(v) by {
            lemma_abs_snap(view_f, v);
            lemma_abs_snap(view_l, v);
        }
        assert forall|v: u64| #[trigger] abs_snap(view_f).contains_key(v) implies abs_snap(view_f)[v]
            == abs_snap(view_l)[v] by {
            lemma_abs_snap(view_f, v);
            lemma_abs_snap(view_l, v);
        }
        assert(abs_snap(view_f) =~~= abs_snap(view_l));
        assert forall|p: (Seq<u8>, u64)|
            #[trigger] abs_store(view_f).contains_key(p) <==> abs_store(view_l).contains_key(p) by {
            lemma_abs_store(view_f, p.0, p.1);
            lemma_abs_store(view_l, p.0, p.1);
        }
        assert forall|p: (Seq<u8>, u64)| #[trigger] abs_store(view_f).contains_key(p) implies
            abs_store(view_f)[p] == abs_store(view_l)[p] by {
            lemma_abs_store(view_f, p.0, p.1);
            lemma_abs_store(view_l, p.0, p.1);
        }
        assert(abs_store(view_f) =~~= abs_store(view_l));
        assert(abs(view_f) == commit(s0, version));
        // The refinement invariant.
        lemma_inv_commit(s0, version);
        assert forall|v: u64| #[trigger] view_f.contains_key(KeyS::TxnActive(v)) implies 1 <= v
            < abs_next(view_f) by {
            assert(view0.contains_key(KeyS::TxnActive(v)));
        }
        assert forall|v: u64| #[trigger] view_f.contains_key(KeyS::TxnActiveSnapshot(v)) implies 1
            <= v < abs_next(view_f) by {
            assert(view0.contains_key(KeyS::TxnActiveSnapshot(v)));
        }
        assert forall|key: Seq<u8>, v: u64|
            #![auto]
            view_f.contains_key(KeyS::Version(key, v)) && view_f.contains_key(
                KeyS::TxnActive(v),
            ) implies view_f.contains_key(KeyS::TxnWrite(v, key)) by {
            assert(v != version);
            assert(view0.contains_key(KeyS::Version(key, v)));
            assert(view0.contains_key(KeyS::TxnActive(v)));
        }
        assert(view_inv(view_f));
    }
    Ok(())
}

/// Verified core of `Transaction::rollback` (read-write): use the TxnWrite
/// records to find and delete every version the transaction wrote (the
/// refinement invariant guarantees they cover all of them — this is why the
/// bookkeeping exists), then delete its TxnActive record. The snapshot record
/// stays behind for time-travel queries. Refines the model `rollback`
/// transition.
#[allow(clippy::question_mark)]
fn vrollback(h: &mut EngineHandle<'_>, version: u64) -> (r: EResult<()>)
    requires
        view_inv(hview(*old(h))),
        abs(hview(*old(h))).active.contains(version),
    ensures
        r is Ok ==> view_inv(hview(*final(h))) && abs(hview(*final(h))) == rollback(
            abs(hview(*old(h))),
            version,
        ),
{
    let keys = match h_scan_txn_write_keys(h, version) {
        Ok(ks) => ks,
        Err(e) => return Err(e),
    };
    let ghost view0 = hview(*h);
    proof {
        // The transaction is active, so the refinement invariant's TxnWrite
        // coverage applies to every one of its writes.
        lemma_abs_active(view0, version);
        assert(view0.contains_key(KeyS::TxnActive(version)));
    }
    let mut i: usize = 0;
    while i < keys.len()
        invariant
            i <= keys.len(),
            // Records the abstraction reads, other than this transaction's
            // versioned writes, are untouched; so are other TxnWrites.
            hview(*h).contains_key(KeyS::NextVersion) == view0.contains_key(KeyS::NextVersion),
            view0.contains_key(KeyS::NextVersion) ==> hview(*h)[KeyS::NextVersion] == view0[
                KeyS::NextVersion
            ],
            forall|v: u64|
                #[trigger] hview(*h).contains_key(KeyS::TxnActive(v)) <==> view0.contains_key(
                    KeyS::TxnActive(v),
                ),
            forall|v: u64|
                (#[trigger] hview(*h).contains_key(KeyS::TxnActiveSnapshot(v))
                    <==> view0.contains_key(KeyS::TxnActiveSnapshot(v))) && (view0.contains_key(
                    KeyS::TxnActiveSnapshot(v),
                ) ==> hview(*h)[KeyS::TxnActiveSnapshot(v)] == view0[KeyS::TxnActiveSnapshot(v)]),
            forall|v2: u64, key: Seq<u8>|
                v2 != version ==> (#[trigger] hview(*h).contains_key(KeyS::TxnWrite(v2, key))
                    <==> view0.contains_key(KeyS::TxnWrite(v2, key))),
            // Other versions' writes are untouched.
            forall|key: Seq<u8>, v2: u64|
                v2 != version ==> (#[trigger] hview(*h).contains_key(KeyS::Version(key, v2))
                    <==> view0.contains_key(KeyS::Version(key, v2))) && (view0.contains_key(
                    KeyS::Version(key, v2),
                ) ==> hview(*h)[KeyS::Version(key, v2)] == view0[KeyS::Version(key, v2)]),
            // This transaction's writes and TxnWrites only disappear, and the
            // first i of each are gone.
            forall|key: Seq<u8>|
                #[trigger] hview(*h).contains_key(KeyS::Version(key, version))
                    ==> view0.contains_key(KeyS::Version(key, version)),
            forall|key: Seq<u8>|
                #[trigger] hview(*h).contains_key(KeyS::TxnWrite(version, key))
                    ==> view0.contains_key(KeyS::TxnWrite(version, key)),
            forall|j: int|
                0 <= j < i ==> !hview(*h).contains_key(
                    KeyS::Version(#[trigger] keys@[j]@, version),
                ) && !hview(*h).contains_key(KeyS::TxnWrite(version, keys@[j]@)),
            // The scan listed every TxnWrite record of this transaction, and
            // the refinement invariant made those cover every write.
            forall|key: Seq<u8>|
                #[trigger] view0.contains_key(KeyS::TxnWrite(version, key)) ==> exists|j: int| #![auto] 0 <= j < keys@.len() && keys@[j]@ == key,
            forall|key: Seq<u8>|
                #[trigger] view0.contains_key(KeyS::Version(key, version)) ==> view0.contains_key(
                    KeyS::TxnWrite(version, key),
                ),
        decreases keys.len() - i,
    {
        match h_delete_version(h, keys[i].as_slice(), version) {
            Ok(_) => {},
            Err(e) => return Err(e),
        }
        match h_delete_txn_write(h, version, keys[i].as_slice()) {
            Ok(_) => {},
            Err(e) => return Err(e),
        }
        i += 1;
    }
    let ghost view_l = hview(*h);
    match h_delete_txn_active(h, version) {
        Ok(_) => {},
        Err(e) => return Err(e),
    }
    proof {
        let s0 = abs(view0);
        let view_f = hview(*h);
        // Nothing of the transaction survived: not its writes (coverage +
        // scan completeness + the loop), not its TxnWrite records.
        assert forall|key: Seq<u8>|
            !(#[trigger] view_f.contains_key(KeyS::Version(key, version))) && !(
            #[trigger] view_f.contains_key(KeyS::TxnWrite(version, key))) by {
            if view_l.contains_key(KeyS::Version(key, version)) || view_l.contains_key(
                KeyS::TxnWrite(version, key),
            ) {
                assert(view0.contains_key(KeyS::TxnWrite(version, key)));
                let j = choose|j: int| #![auto] 0 <= j < keys@.len() && keys@[j]@ == key;
                assert(!view_l.contains_key(KeyS::Version(keys@[j]@, version)));
                assert(!view_l.contains_key(KeyS::TxnWrite(version, keys@[j]@)));
            }
        }
        // The abstraction: the active set drops version, and the store loses
        // exactly the pairs at version.
        let s2 = rollback(s0, version);
        assert(abs_next(view_f) == abs_next(view0));
        assert forall|v: u64| #[trigger] abs_active(view_f).contains(v) <==> s2.active.contains(
            v,
        ) by {
            lemma_abs_active(view_f, v);
            lemma_abs_active(view0, v);
        }
        assert(abs_active(view_f) =~= s2.active);
        assert forall|v: u64|
            #[trigger] abs_snap(view_f).contains_key(v) <==> s2.snap.contains_key(v) by {
            lemma_abs_snap(view_f, v);
            lemma_abs_snap(view0, v);
        }
        assert forall|v: u64| #[trigger] abs_snap(view_f).contains_key(v) implies abs_snap(view_f)[v]
            == s2.snap[v] by {
            lemma_abs_snap(view_f, v);
            lemma_abs_snap(view0, v);
            assert(view_f.contains_key(KeyS::TxnActiveSnapshot(v)) == view0.contains_key(
                KeyS::TxnActiveSnapshot(v),
            ));
            assert(abs_snap_at(view_f, v) == abs_snap_at(view0, v));
        }
        assert(abs_snap(view_f) =~~= s2.snap);
        assert forall|p: (Seq<u8>, u64)|
            #[trigger] abs_store(view_f).contains_key(p) <==> s2.store.contains_key(p) by {
            lemma_abs_store(view_f, p.0, p.1);
            lemma_abs_store(view0, p.0, p.1);
        }
        assert forall|p: (Seq<u8>, u64)| #[trigger] abs_store(view_f).contains_key(p) implies
            abs_store(view_f)[p] == s2.store[p] by {
            lemma_abs_store(view_f, p.0, p.1);
            lemma_abs_store(view0, p.0, p.1);
            assert(p.1 != version);
            assert(abs_store_at(view_f, p) == abs_store_at(view0, p));
        }
        assert(abs_store(view_f) =~~= s2.store);
        assert(abs(view_f) == s2);
        // The refinement invariant.
        lemma_inv_rollback(s0, version);
        assert forall|v: u64| #[trigger] view_f.contains_key(KeyS::TxnActive(v)) implies 1 <= v
            < abs_next(view_f) by {
            assert(view0.contains_key(KeyS::TxnActive(v)));
        }
        assert forall|v: u64| #[trigger] view_f.contains_key(KeyS::TxnActiveSnapshot(v)) implies 1
            <= v < abs_next(view_f) by {
            assert(view0.contains_key(KeyS::TxnActiveSnapshot(v)));
        }
        assert forall|key: Seq<u8>, v: u64|
            #![auto]
            view_f.contains_key(KeyS::Version(key, v)) && view_f.contains_key(
                KeyS::TxnActive(v),
            ) implies view_f.contains_key(KeyS::TxnWrite(v, key)) by {
            assert(v != version);
            assert(view0.contains_key(KeyS::Version(key, v)));
            assert(view0.contains_key(KeyS::TxnActive(v)));
        }
        assert(view_inv(view_f));
    }
    Ok(())
}

/// Collects scanned versions into the in-memory active set.
fn versions_to_set(versions: &[u64]) -> (r: BTreeSet<u64>)
    ensures
        forall|v: u64| #[trigger] r@.contains(v) <==> versions@.contains(v),
{
    let mut set = BTreeSet::new();
    let mut i: usize = 0;
    while i < versions.len()
        invariant
            i <= versions.len(),
            forall|v: u64|
                #[trigger] set@.contains(v) <==> exists|j: int| 0 <= j < i && versions@[j] == v,
        decreases versions.len() - i,
    {
        set.insert(versions[i]);
        assert forall|v: u64| #[trigger] set@.contains(v) implies exists|j: int|
            0 <= j < i + 1 && versions@[j] == v by {
            if v == versions@[i as int] {
                assert(0 <= i < i + 1 && versions@[i as int] == v);
            } else {
                let j = choose|j: int| 0 <= j < i && versions@[j] == v;
                assert(0 <= j < i + 1 && versions@[j] == v);
            }
        }
        i += 1;
    }
    set
}

/// Verified core of `Transaction::begin`: allocate the next version, bump
/// NextVersion, snapshot the active set (persisting it only when non-empty,
/// exactly as the code always has), and register the transaction as active.
/// Refines the model `begin` transition and returns the transaction state
/// (its version and active-set snapshot) that `begin` produces in the model.
#[allow(clippy::question_mark)]
fn vbegin(h: &mut EngineHandle<'_>) -> (r: EResult<(u64, BTreeSet<u64>)>)
    requires
        view_inv(hview(*old(h))),
    ensures
        match r {
            Ok((version, active)) => {
                &&& can_begin(abs(hview(*old(h))))
                &&& version == abs(hview(*old(h))).next
                &&& active@ == abs(hview(*old(h))).active
                &&& view_inv(hview(*final(h)))
                &&& abs(hview(*final(h))) == begin(abs(hview(*old(h))))
            },
            Err(_) => true,
        },
{
    let ghost view0 = hview(*h);
    let ghost s0 = abs(view0);
    // Allocate a new version to write at.
    let version = match h_get_next_version(h) {
        Ok(n) => n,
        Err(e) => return Err(e),
    };
    if version == u64::MAX {
        // The u64 version counter would wrap: refuse. (Unreachable in
        // practice; the historical code would panic here instead.)
        return Err(err_version_overflow());
    }
    match h_set_next_version(h, version + 1) {
        Ok(_) => {},
        Err(e) => return Err(e),
    }
    let ghost view1 = hview(*h);
    // Fetch the current set of active transactions, persist it for
    // time-travel queries if non-empty, then add this txn to it.
    let versions = match h_scan_active(h) {
        Ok(vs) => vs,
        Err(e) => return Err(e),
    };
    let active = versions_to_set(versions.as_slice());
    proof {
        assert forall|v: u64| #[trigger] active@.contains(v) <==> s0.active.contains(v) by {
            lemma_abs_active(view0, v);
        }
        assert(active@ =~= s0.active);
    }
    if !active.is_empty() {
        match h_set_txn_active_snapshot(h, version, &active) {
            Ok(_) => {},
            Err(e) => return Err(e),
        }
    }
    let ghost view2 = hview(*h);
    match h_set_txn_active(h, version) {
        Ok(_) => {},
        Err(e) => return Err(e),
    }
    proof {
        let view_f = hview(*h);
        let s2 = begin(s0);
        // In the empty case no snapshot record is written; there was no stale
        // record at the fresh version either (view_inv), so the absent record
        // reads back as the empty set the active set was.
        assert(!view0.contains_key(KeyS::TxnActiveSnapshot(version)));
        assert(abs_next(view_f) == s2.next);
        assert forall|v: u64| #[trigger] abs_active(view_f).contains(v) <==> s2.active.contains(
            v,
        ) by {
            lemma_abs_active(view_f, v);
            lemma_abs_active(view0, v);
        }
        assert(abs_active(view_f) =~= s2.active);
        assert forall|v: u64|
            #[trigger] abs_snap(view_f).contains_key(v) <==> s2.snap.contains_key(v) by {
            lemma_abs_snap(view_f, v);
            lemma_abs_snap(view0, v);
        }
        assert forall|v: u64| #[trigger] abs_snap(view_f).contains_key(v) implies abs_snap(view_f)[v]
            == s2.snap[v] by {
            lemma_abs_snap(view_f, v);
            lemma_abs_snap(view0, v);
            if v == version {
                if active@.is_empty() {
                    assert(!view_f.contains_key(KeyS::TxnActiveSnapshot(version)));
                    assert(abs_snap_at(view_f, version) =~= s0.active);
                } else {
                    assert(view_f[KeyS::TxnActiveSnapshot(version)] == ValS::VSet(active@));
                    assert(abs_snap_at(view_f, version) == active@);
                }
            } else {
                assert(view_f.contains_key(KeyS::TxnActiveSnapshot(v)) == view0.contains_key(
                    KeyS::TxnActiveSnapshot(v),
                ));
                assert(abs_snap_at(view_f, v) == abs_snap_at(view0, v));
            }
        }
        assert(abs_snap(view_f) =~~= s2.snap);
        assert forall|p: (Seq<u8>, u64)|
            #[trigger] abs_store(view_f).contains_key(p) <==> s2.store.contains_key(p) by {
            lemma_abs_store(view_f, p.0, p.1);
            lemma_abs_store(view0, p.0, p.1);
        }
        assert forall|p: (Seq<u8>, u64)| #[trigger] abs_store(view_f).contains_key(p) implies
            abs_store(view_f)[p] == s2.store[p] by {
            lemma_abs_store(view_f, p.0, p.1);
            lemma_abs_store(view0, p.0, p.1);
            assert(abs_store_at(view_f, p) == abs_store_at(view0, p));
        }
        assert(abs_store(view_f) =~~= s2.store);
        assert(abs(view_f) == s2);
        // The refinement invariant.
        lemma_inv_begin(s0);
        assert forall|v: u64| #[trigger] view_f.contains_key(KeyS::TxnActive(v)) implies 1 <= v
            < abs_next(view_f) by {
            if v != version {
                assert(view0.contains_key(KeyS::TxnActive(v)));
            }
        }
        assert forall|v: u64| #[trigger] view_f.contains_key(KeyS::TxnActiveSnapshot(v)) implies 1
            <= v < abs_next(view_f) by {
            if v != version {
                assert(view0.contains_key(KeyS::TxnActiveSnapshot(v)));
            }
        }
        assert forall|key: Seq<u8>, v: u64|
            #![auto]
            view_f.contains_key(KeyS::Version(key, v)) && view_f.contains_key(
                KeyS::TxnActive(v),
            ) implies view_f.contains_key(KeyS::TxnWrite(v, key)) by {
            assert(view0.contains_key(KeyS::Version(key, v)));
            lemma_abs_store(view0, key, v);
            assert(s0.store.contains_key((key, v)));
            assert(allocated(s0, v));
            assert(v != version);
            assert(view0.contains_key(KeyS::TxnActive(v)));
        }
        assert(view_inv(view_f));
    }
    Ok((version, active))
}

/// TRUSTED: `BTreeSet::first` returns the smallest element, if any.
#[verifier::external_body]
fn btree_set_first(s: &BTreeSet<u64>) -> (r: Option<u64>)
    ensures
        match r {
            Some(m) => s@.contains(m) && forall|w: u64| #[trigger] s@.contains(w) ==> m <= w,
            None => forall|w: u64| !(#[trigger] s@.contains(w)),
        },
{
    s.first().copied()
}

/// The outcome of a versioned write: done, a serialization conflict (the
/// caller returns `Error::Serialization`), or an engine/decode failure.
pub enum VWriteOutcome {
    Done,
    Conflict,
    Fail(Error),
}

/// Verified core of `Transaction::write_version`: the conflict check and
/// write. Scans the versions of `key` from the smallest version in the begin
/// snapshot (or version + 1 if none) and errors iff the latest one is
/// invisible — and by `thm_conflict_check_exact` that latest-only check
/// conflicts exactly when *any* version of the key is invisible. On success,
/// writes the TxnWrite bookkeeping record and the new version, refining the
/// model `write` transition.
#[allow(clippy::question_mark, clippy::collapsible_if)]
#[allow(clippy::needless_return)]
fn vwrite(
    h: &mut EngineHandle<'_>,
    version: u64,
    active: &BTreeSet<u64>,
    key: &[u8],
    value: &Option<Vec<u8>>,
) -> (r: VWriteOutcome)
    requires
        view_inv(hview(*old(h))),
        abs(hview(*old(h))).active.contains(version),
        active@ == abs(hview(*old(h))).snap[version],
    ensures
        match r {
            VWriteOutcome::Done => {
                &&& can_write(abs(hview(*old(h))), version, key@)
                &&& view_inv(hview(*final(h)))
                &&& abs(hview(*final(h))) == write(
                    abs(hview(*old(h))),
                    version,
                    key@,
                    value.deep_view(),
                )
            },
            VWriteOutcome::Conflict => !no_write_conflict(abs(hview(*old(h))), version, key@)
                && hview(*final(h)) == hview(*old(h)),
            VWriteOutcome::Fail(_) => true,
        },
{
    let ghost view0 = hview(*h);
    let ghost s0 = abs(view0);
    proof {
        assert(allocated(s0, version));  // version is active, so version < next <= u64::MAX
    }
    // The scan floor: the smallest version in our begin snapshot, or the
    // version after ours — everything below is visible to us.
    let lo = match btree_set_first(active) {
        Some(m) => m,
        None => version + 1,
    };
    proof {
        assert(is_scan_floor(s0.snap[version], version, lo));
    }
    // Check for write conflicts: find the latest version of the key in the
    // scanned range and test its visibility.
    let latest = match h_scan_last_version_in_range(h, key, lo) {
        Ok(l) => l,
        Err(e) => return VWriteOutcome::Fail(e),
    };
    // Relate the view-level scan result to the model-level range maximum.
    proof {
        match latest {
            Some(m) => {
                lemma_abs_store(view0, key@, m);
                assert(has_version(s0, key@, m));
                assert forall|w: u64| #[trigger] has_version(s0, key@, w) && lo <= w implies w
                    <= m by {
                    lemma_abs_store(view0, key@, w);
                }
                assert(range_max(s0, key@, lo, m));
            },
            None => {
                assert forall|m2: u64| !(#[trigger] range_max(s0, key@, lo, m2)) by {
                    if range_max(s0, key@, lo, m2) {
                        lemma_abs_store(view0, key@, m2);
                    }
                }
            },
        }
    }
    if let Some(m) = latest {
        if !is_visible_core(active, version, false, m) {
            proof {
                // The latest version is invisible: by exactness of the check,
                // some version of the key genuinely conflicts.
                assert(!check_passes(s0, version, key@, lo));
                thm_conflict_check_exact(s0, version, key@, lo);
            }
            return VWriteOutcome::Conflict;
        }
    }
    proof {
        // The check passed: only the range maximum needed testing.
        assert forall|m2: u64| #[trigger] range_max(s0, key@, lo, m2) implies txn_visible(
            s0,
            version,
            m2,
        ) by {
            match latest {
                Some(m) => {
                    assert(m2 == m);
                },
                None => {},
            }
        }
        assert(check_passes(s0, version, key@, lo));
        assert(can_write(s0, version, key@));
    }
    // Write the new version and its write record.
    match h_set_txn_write(h, version, key) {
        Ok(_) => {},
        Err(e) => return VWriteOutcome::Fail(e),
    }
    match h_set_version(h, key, version, value) {
        Ok(_) => {},
        Err(e) => return VWriteOutcome::Fail(e),
    }
    proof {
        let view_f = hview(*h);
        let s2 = write(s0, version, key@, value.deep_view());
        assert(abs_next(view_f) == s2.next);
        assert forall|v: u64| #[trigger] abs_active(view_f).contains(v) <==> s2.active.contains(
            v,
        ) by {
            lemma_abs_active(view_f, v);
            lemma_abs_active(view0, v);
        }
        assert(abs_active(view_f) =~= s2.active);
        assert forall|v: u64|
            #[trigger] abs_snap(view_f).contains_key(v) <==> s2.snap.contains_key(v) by {
            lemma_abs_snap(view_f, v);
            lemma_abs_snap(view0, v);
        }
        assert forall|v: u64| #[trigger] abs_snap(view_f).contains_key(v) implies abs_snap(view_f)[v]
            == s2.snap[v] by {
            lemma_abs_snap(view_f, v);
            lemma_abs_snap(view0, v);
            assert(view_f.contains_key(KeyS::TxnActiveSnapshot(v)) == view0.contains_key(
                KeyS::TxnActiveSnapshot(v),
            ));
            assert(abs_snap_at(view_f, v) == abs_snap_at(view0, v));
        }
        assert(abs_snap(view_f) =~~= s2.snap);
        assert forall|p: (Seq<u8>, u64)|
            #[trigger] abs_store(view_f).contains_key(p) <==> s2.store.contains_key(p) by {
            lemma_abs_store(view_f, p.0, p.1);
            lemma_abs_store(view0, p.0, p.1);
        }
        assert forall|p: (Seq<u8>, u64)| #[trigger] abs_store(view_f).contains_key(p) implies
            abs_store(view_f)[p] == s2.store[p] by {
            lemma_abs_store(view_f, p.0, p.1);
            lemma_abs_store(view0, p.0, p.1);
            if p == (key@, version) {
                assert(view_f[KeyS::Version(key@, version)] == ValS::Bytes(value.deep_view()));
            } else {
                assert(abs_store_at(view_f, p) == abs_store_at(view0, p));
            }
        }
        assert(abs_store(view_f) =~~= s2.store);
        assert(abs(view_f) == s2);
        // The refinement invariant.
        lemma_inv_write(s0, version, key@, value.deep_view());
        assert forall|v: u64| #[trigger] view_f.contains_key(KeyS::TxnActive(v)) implies 1 <= v
            < abs_next(view_f) by {
            assert(view0.contains_key(KeyS::TxnActive(v)));
        }
        assert forall|v: u64| #[trigger] view_f.contains_key(KeyS::TxnActiveSnapshot(v)) implies 1
            <= v < abs_next(view_f) by {
            assert(view0.contains_key(KeyS::TxnActiveSnapshot(v)));
        }
        assert forall|k2: Seq<u8>, v: u64|
            #![auto]
            view_f.contains_key(KeyS::Version(k2, v)) && view_f.contains_key(
                KeyS::TxnActive(v),
            ) implies view_f.contains_key(KeyS::TxnWrite(v, k2)) by {
            if k2 != key@ || v != version {
                assert(view0.contains_key(KeyS::Version(k2, v)));
                assert(view0.contains_key(KeyS::TxnActive(v)));
            }
        }
        assert(view_inv(view_f));
    }
    VWriteOutcome::Done
}

/// Verified core of `Transaction::get`: scan the key's versions from the
/// transaction's version downwards and return the first visible one — proven
/// to be the model read (`is_read_result`): the value at the greatest visible
/// version, or None if no version is visible.
#[allow(clippy::question_mark)]
fn vget(
    h: &mut EngineHandle<'_>,
    version: u64,
    read_only: bool,
    active: &BTreeSet<u64>,
    key: &[u8],
) -> (r: EResult<Option<Vec<u8>>>)
    requires
        view_inv(hview(*old(h))),
    ensures
        hview(*final(h)) == hview(*old(h)),
        match r {
            Ok(res) => ({
                let s = abs(hview(*old(h)));
                ||| exists|w: u64|
                    #[trigger] is_read_result(s, version, active@, read_only, key@, w)
                        && res.deep_view() == s.store[(key@, w)]
                ||| ((forall|w: u64|
                    #[trigger] has_version(s, key@, w) ==> !spec_is_visible(
                        active@,
                        version,
                        read_only,
                        w,
                    )) && res is None)
            }),
            Err(_) => true,
        },
{
    let ghost view0 = hview(*h);
    let ghost s0 = abs(view0);
    let mut entries = match h_scan_versions_desc(h, key, version) {
        Ok(es) => es,
        Err(e) => return Err(e),
    };
    let ghost es = entries@;
    proof {
        // Every version of the key is below NextVersion and, if visible, at
        // or below the transaction's version — so the scan to `version`
        // covered every visible version.
        assert forall|w: u64|
            #[trigger] has_version(s0, key@, w) && spec_is_visible(active@, version, read_only, w)
                implies exists|i: int| #![auto] 0 <= i < es.len() && es[i].0 == w by {
            lemma_abs_store(view0, key@, w);
        }
    }
    let mut i: usize = 0;
    while i < entries.len()
        invariant
            i <= entries.len(),
            entries@ == es,
            view0 == hview(*old(h)),
            hview(*h) == view0,
            view_inv(view0),
            s0 == abs(view0),
            // Scan facts (restated from the adapter contract).
            forall|j: int|
                0 <= j < es.len() ==> (#[trigger] es[j]).0 <= version && view0.contains_key(
                    KeyS::Version(key@, es[j].0),
                ) && view0[KeyS::Version(key@, es[j].0)] == ValS::Bytes(es[j].1.deep_view()),
            forall|j: int, j2: int| #![auto] 0 <= j < j2 < es.len() ==> es[j].0 > es[j2].0,
            forall|w: u64|
                #[trigger] has_version(s0, key@, w) && spec_is_visible(
                    active@,
                    version,
                    read_only,
                    w,
                ) ==> exists|j: int| #![auto] 0 <= j < es.len() && es[j].0 == w,
            // Everything we have walked past is invisible.
            forall|j: int|
                0 <= j < i ==> !spec_is_visible(active@, version, read_only, (#[trigger] es[j]).0),
        decreases entries.len() - i,
    {
        if is_visible_core(active, version, read_only, entries[i].0) {
            let entry = entries.remove(i);
            let ghost w = entry.0;
            let val = entry.1;
            proof {
                // w is visible with a version record: it is the model read,
                // since any visible version appears in the scan, and entries
                // before ours are invisible while entries after are smaller.
                lemma_abs_store(view0, key@, w);
                assert(has_version(s0, key@, w));
                assert forall|w2: u64|
                    #[trigger] has_version(s0, key@, w2) && spec_is_visible(
                        active@,
                        version,
                        read_only,
                        w2,
                    ) implies w2 <= w by {
                    let j2 = choose|j2: int| #![auto] 0 <= j2 < es.len() && es[j2].0 == w2;
                    if j2 < i {
                        assert(!spec_is_visible(active@, version, read_only, es[j2].0));
                    } else if j2 > i {
                        assert(es[i as int].0 > es[j2].0);
                    }
                }
                assert(is_read_result(s0, version, active@, read_only, key@, w));
                assert(s0.store[(key@, w)] == abs_store_at(view0, (key@, w)));
                assert(s0.store[(key@, w)] == val.deep_view());
            }
            return Ok(val);
        }
        i += 1;
    }
    proof {
        // No entry was visible, and every visible version is an entry.
        assert forall|w: u64| #[trigger] has_version(s0, key@, w) implies !spec_is_visible(
            active@,
            version,
            read_only,
            w,
        ) by {
            if spec_is_visible(active@, version, read_only, w) {
                let j = choose|j: int| #![auto] 0 <= j < es.len() && es[j].0 == w;
                assert(!spec_is_visible(active@, version, read_only, es[j].0));
            }
        }
    }
    Ok(None)
}

/// Verified core of `Transaction::begin_read_only`: read the current version
/// and either take a live snapshot of the active set (as_of None) or restore
/// the persisted snapshot of a past version (time travel). Either way the
/// result is a well-formed observer (`wf_observer`) of the current state, so
/// all the read-path theorems (no dirty reads, snapshot stability) apply to
/// it. Does not modify the engine.
#[allow(clippy::question_mark)]
fn vbegin_read_only(h: &mut EngineHandle<'_>, as_of: Option<u64>) -> (r: EResult<
    (u64, BTreeSet<u64>),
>)
    requires
        view_inv(hview(*old(h))),
    ensures
        hview(*final(h)) == hview(*old(h)),
        match r {
            Ok((version, active)) => {
                &&& wf_observer(abs(hview(*old(h))), version, active@, true)
                &&& match as_of {
                    Some(v) => version == v && v < abs(hview(*old(h))).next,
                    None => version == abs(hview(*old(h))).next && active@ == abs(
                        hview(*old(h)),
                    ).active,
                }
            },
            Err(_) => true,
        },
{
    let ghost view0 = hview(*h);
    let ghost s0 = abs(view0);
    // Fetch the latest version.
    let mut version = match h_get_next_version(h) {
        Ok(n) => n,
        Err(e) => return Err(e),
    };
    let active: BTreeSet<u64>;
    if let Some(v) = as_of {
        // Create the transaction as of a past version, restoring the active
        // snapshot as of the beginning of that version.
        if v >= version {
            return Err(err_version_does_not_exist(v));
        }
        version = v;
        active = match h_get_txn_active_snapshot(h, v) {
            Ok(Some(set)) => set,
            Ok(None) => BTreeSet::new(),
            Err(e) => return Err(e),
        };
        proof {
            // The observer property: any still-active transaction below v was
            // active when v began, hence in the snapshot we restored (which,
            // if absent, was empty — and then nothing below v is still
            // active). Mirrors lemma_ro_as_of_is_observer against the view.
            assert forall|w: u64| s0.active.contains(w) && w < v implies active@.contains(w) by {
                lemma_abs_active(view0, w);
                if view0.contains_key(KeyS::TxnActiveSnapshot(v)) {
                    lemma_abs_snap(view0, v);
                    assert(s0.snap.contains_key(v));
                    assert(s0.snap[v].contains(w));
                    assert(active@ == abs_snap_at(view0, v));
                } else {
                    // No snapshot record: the active set at v's begin was
                    // empty. If w were still active with w < v, the model
                    // invariant would place it in v's (empty) snapshot.
                    assert(abs_snap_at(view0, v) =~= Set::<u64>::empty());
                    if 1 <= v {
                        lemma_abs_snap(view0, v);
                        assert(s0.snap.contains_key(v));
                        assert(s0.snap[v].contains(w));
                        assert(false);
                    }
                }
            }
        }
    } else {
        // Use the latest version and the current, real-time active set.
        let versions = match h_scan_active(h) {
            Ok(vs) => vs,
            Err(e) => return Err(e),
        };
        active = versions_to_set(versions.as_slice());
        proof {
            assert forall|w: u64| #[trigger] active@.contains(w) <==> s0.active.contains(w) by {
                lemma_abs_active(view0, w);
            }
            assert(active@ =~= s0.active);
        }
    }
    Ok((version, active))
}

} // verus!

/// The object-safe engine facade used by the verified MVCC core. TRUSTED:
/// together with the `h_*` adapter functions in the `verus!` block above,
/// this forms the trusted boundary between the verified transaction logic
/// and the raw storage engine. Each method mirrors an engine access pattern
/// the transaction code historically performed inline; the adapter contracts
/// state what each is trusted to do in terms of the decoded view `hview`.
pub trait EngineOps {
    fn get_raw(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>>;
    fn set_raw(&mut self, key: &[u8], value: Vec<u8>) -> Result<()>;
    fn delete_raw(&mut self, key: &[u8]) -> Result<()>;
    /// The versions of all TxnActive records.
    fn scan_active_versions(&mut self) -> Result<Vec<u64>>;
    /// The greatest version of `key` in `lo..=u64::MAX`: the write conflict
    /// scan. Relies on the keycode encoding ordering Version keys by (key,
    /// version), so the last entry of the range scan is the greatest version.
    fn scan_last_version_in_range(&mut self, key: &[u8], lo: u64) -> Result<Option<u64>>;
    /// All (version, value) pairs of `key` with version <= hi, latest first,
    /// with values decoded: the read scan.
    fn scan_versions_desc(&mut self, key: &[u8], hi: u64) -> Result<Vec<(u64, Option<Vec<u8>>)>>;
    /// The user keys of all TxnWrite records of `version`, in key order.
    fn scan_txn_write_keys(&mut self, version: u64) -> Result<Vec<Vec<u8>>>;
}

impl<E: Engine> EngineOps for E {
    fn get_raw(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>> {
        self.get(key)
    }

    fn set_raw(&mut self, key: &[u8], value: Vec<u8>) -> Result<()> {
        self.set(key, value)
    }

    fn delete_raw(&mut self, key: &[u8]) -> Result<()> {
        self.delete(key)
    }

    fn scan_active_versions(&mut self) -> Result<Vec<u64>> {
        let mut versions = Vec::new();
        let mut scan = self.scan_prefix(&KeyPrefix::TxnActive.encode());
        while let Some((key, _)) = scan.next().transpose()? {
            match Key::decode(&key)? {
                Key::TxnActive(version) => versions.push(version),
                key => return errdata!("expected TxnActive key, got {key:?}"),
            }
        }
        Ok(versions)
    }

    fn scan_last_version_in_range(&mut self, key: &[u8], lo: u64) -> Result<Option<u64>> {
        let from = Key::Version(key.into(), lo).encode();
        let to = Key::Version(key.into(), u64::MAX).encode();
        match self.scan(from..=to).last().transpose()? {
            Some((key, _)) => match Key::decode(&key)? {
                Key::Version(_, version) => Ok(Some(version)),
                key => errdata!("expected Key::Version got {key:?}"),
            },
            None => Ok(None),
        }
    }

    fn scan_versions_desc(&mut self, key: &[u8], hi: u64) -> Result<Vec<(u64, Option<Vec<u8>>)>> {
        let from = Key::Version(key.into(), 0).encode();
        let to = Key::Version(key.into(), hi).encode();
        let mut entries = Vec::new();
        let mut scan = self.scan(from..=to).rev();
        while let Some((key, value)) = scan.next().transpose()? {
            match Key::decode(&key)? {
                Key::Version(_, version) => entries.push((version, bincode::deserialize(&value)?)),
                key => return errdata!("expected Key::Version got {key:?}"),
            }
        }
        Ok(entries)
    }

    fn scan_txn_write_keys(&mut self, version: u64) -> Result<Vec<Vec<u8>>> {
        let mut keys = Vec::new();
        let mut scan = self.scan_prefix(&KeyPrefix::TxnWrite(version).encode());
        while let Some((key, _)) = scan.next().transpose()? {
            match Key::decode(&key)? {
                Key::TxnWrite(_, key) => keys.push(key.into_owned()),
                key => return errdata!("expected TxnWrite, got {key:?}"),
            }
        }
        Ok(keys)
    }
}

/// A dyn-erased handle to the engine, passed to the verified core. Erasing
/// the `Engine` type parameter keeps generic trait bounds out of the
/// verified functions' signatures.
pub struct EngineHandle<'a> {
    inner: &'a mut dyn EngineOps,
}

impl<'a> EngineHandle<'a> {
    fn new(inner: &'a mut dyn EngineOps) -> Self {
        Self { inner }
    }
}

/// Most storage tests are Goldenscripts under src/storage/testscripts.
#[cfg(test)]
pub mod tests {
    use std::collections::HashMap;
    use std::error::Error;
    use std::fmt::Write as _;
    use std::path::Path;
    use std::result::Result;

    use crossbeam::channel::Receiver;
    use itertools::Itertools as _;
    use tempfile::TempDir;
    use test_case::test_case;
    use test_each_file::test_each_path;

    use super::*;
    use crate::encoding::format::{self, Formatter as _};
    use crate::storage::engine::test::{BinaryString, Emit, KeyRange, Mirror, Operation};
    use crate::storage::{BitCask, Memory};

    // Run goldenscript tests in src/storage/testscripts/mvcc.
    test_each_path! { in "src/storage/testscripts/mvcc" as scripts => test_goldenscript }

    fn test_goldenscript(path: &Path) {
        goldenscript::run(&mut MVCCRunner::new(), path).expect("goldenscript failed")
    }

    /// Tests that key prefixes are actually prefixes of keys.
    #[test_case(KeyPrefix::NextVersion, Key::NextVersion; "NextVersion")]
    #[test_case(KeyPrefix::TxnActive, Key::TxnActive(1); "TxnActive")]
    #[test_case(KeyPrefix::TxnActiveSnapshot, Key::TxnActiveSnapshot(1); "TxnActiveSnapshot")]
    #[test_case(KeyPrefix::TxnWrite(1), Key::TxnWrite(1, b"foo".as_slice().into()); "TxnWrite")]
    #[test_case(KeyPrefix::Version(b"foo".as_slice().into()), Key::Version(b"foo".as_slice().into(), 1); "Version")]
    #[test_case(KeyPrefix::Unversioned, Key::Unversioned(b"foo".as_slice().into()); "Unversioned")]
    fn key_prefix(prefix: KeyPrefix, key: Key) {
        let prefix = prefix.encode();
        let key = key.encode();
        assert_eq!(prefix, key[..prefix.len()])
    }

    /// Runs MVCC goldenscript tests.
    pub struct MVCCRunner {
        mvcc: MVCC<TestEngine>,
        txns: HashMap<String, Transaction<TestEngine>>,
        op_rx: Receiver<Operation>,
        _tempdir: TempDir,
    }

    type TestEngine = Emit<Mirror<BitCask, Memory>>;

    /// Commands accepted by the MVCC Goldenscript runner.
    #[derive(goldenscript::Command)]
    pub enum Command {
        /// Begins a transaction selected by the command prefix.
        Begin {
            /// The optional `readonly` transaction mode.
            readonly: Option<String>,
            /// The historical version for a read-only transaction.
            #[arg(key)]
            as_of: Option<Version>,
        },
        /// Commits the transaction selected by the command prefix.
        Commit,
        /// Deletes keys in the selected transaction.
        Delete(
            /// The keys to delete.
            Vec<BinaryString>,
        ),
        /// Dumps all raw MVCC storage entries.
        Dump,
        /// Fetches keys from the selected transaction.
        Get(
            /// The keys to fetch.
            Vec<BinaryString>,
        ),
        /// Fetches unversioned keys.
        GetUnversioned(
            /// The unversioned keys to fetch.
            Vec<BinaryString>,
        ),
        /// Imports key/value pairs at an optional version.
        Import {
            /// The version to import at.
            version: Option<Version>,
            /// The key/value pairs to import.
            entries: Vec<(BinaryString, BinaryString)>,
        },
        /// Resumes a transaction from serialized state.
        Resume(String),
        /// Rolls back the transaction selected by the command prefix.
        Rollback,
        /// Scans a key range in the selected transaction.
        Scan(
            /// The key range, or the full range if omitted.
            #[arg(optional)]
            KeyRange,
        ),
        /// Scans keys with a prefix in the selected transaction.
        ScanPrefix(BinaryString),
        /// Sets key/value pairs in the selected transaction.
        Set(Vec<(BinaryString, BinaryString)>),
        /// Sets unversioned key/value pairs.
        SetUnversioned(Vec<(BinaryString, BinaryString)>),
        /// Displays the selected transaction state.
        State,
        /// Displays MVCC status.
        Status,
    }

    impl MVCCRunner {
        fn new() -> Self {
            // Use both a BitCask and a Memory engine, and mirror operations
            // across them. Emit engine operations to op_rx.
            let (op_tx, op_rx) = crossbeam::channel::unbounded();
            let tempdir = TempDir::with_prefix("toydb").expect("tempdir failed");
            let bitcask = BitCask::new(tempdir.path().join("bitcask")).expect("bitcask failed");
            let memory = Memory::new();
            let engine = Emit::new(Mirror::new(bitcask, memory), op_tx);
            let mvcc = MVCC::new(engine);
            Self { mvcc, op_rx, txns: HashMap::new(), _tempdir: tempdir }
        }

        /// Fetches the named transaction from a command prefix.
        fn get_txn(
            &mut self,
            prefix: &Option<String>,
        ) -> Result<&'_ mut Transaction<TestEngine>, Box<dyn Error>> {
            let name = Self::txn_name(prefix)?;
            self.txns.get_mut(name).ok_or(format!("unknown txn {name}").into())
        }

        /// Fetches the txn name from a command prefix, or errors.
        fn txn_name(prefix: &Option<String>) -> Result<&str, Box<dyn Error>> {
            prefix.as_deref().ok_or("no txn name".into())
        }

        /// Errors if a txn prefix is given.
        fn no_txn(name: &str, context: &goldenscript::Context) -> Result<(), Box<dyn Error>> {
            if let Some(prefix) = &context.prefix {
                return Err(format!("can't run {name} with txn {prefix}").into());
            }
            Ok(())
        }
    }

    impl goldenscript::Runner for MVCCRunner {
        type Command = Command;

        fn run(
            &mut self,
            command: &Command,
            context: &goldenscript::Context,
        ) -> Result<String, Box<dyn Error>> {
            let mut output = String::new();
            let mut tags = context.tags.clone();

            match command {
                &Command::Begin { ref readonly, as_of } => {
                    let name = Self::txn_name(&context.prefix)?;
                    if self.txns.contains_key(name) {
                        return Err(format!("txn {name} already exists").into());
                    }
                    let readonly = match readonly.as_deref() {
                        Some("readonly") => true,
                        None => false,
                        Some(v) => return Err(format!("invalid argument {v}").into()),
                    };
                    let txn = match (readonly, as_of) {
                        (false, None) => self.mvcc.begin()?,
                        (true, None) => self.mvcc.begin_read_only()?,
                        (true, Some(v)) => self.mvcc.begin_as_of(v)?,
                        (false, Some(_)) => return Err("as_of only valid for read-only txn".into()),
                    };
                    self.txns.insert(name.to_string(), txn);
                }

                Command::Commit => {
                    let name = Self::txn_name(&context.prefix)?;
                    let txn = self.txns.remove(name).ok_or(format!("unknown txn {name}"))?;
                    txn.commit()?;
                }

                Command::Delete(keys) => {
                    let txn = self.get_txn(&context.prefix)?;
                    for key in keys {
                        txn.delete(key)?;
                    }
                }

                Command::Dump => {
                    let mut engine = self.mvcc.engine.lock().unwrap();
                    let mut scan = engine.scan(..);
                    while let Some((key, value)) = scan.next().transpose()? {
                        let fmtkv = format::MVCC::<format::Raw>::key_value(&key, &value);
                        let rawkv = format::Raw::key_value(&key, &value);
                        writeln!(output, "{fmtkv} [{rawkv}]")?;
                    }
                }

                Command::Get(keys) => {
                    let txn = self.get_txn(&context.prefix)?;
                    for key in keys {
                        let value = txn.get(key)?;
                        let fmtkv = format::Raw::key_maybe_value(key, value.as_deref());
                        writeln!(output, "{fmtkv}")?;
                    }
                }

                Command::GetUnversioned(keys) => {
                    Self::no_txn("get_unversioned", context)?;
                    for key in keys {
                        let value = self.mvcc.get_unversioned(key)?;
                        let fmtkv = format::Raw::key_maybe_value(key, value.as_deref());
                        writeln!(output, "{fmtkv}")?;
                    }
                }

                &Command::Import { version, ref entries } => {
                    Self::no_txn("import", context)?;
                    let mut txn = self.mvcc.begin()?;
                    if let Some(version) = version {
                        if txn.version() > version {
                            return Err(format!("version {version} already used").into());
                        }
                        while txn.version() < version {
                            txn = self.mvcc.begin()?;
                        }
                    }
                    for (key, value) in entries {
                        if value.is_empty() {
                            txn.delete(key)?;
                        } else {
                            txn.set(key, value.to_vec())?;
                        }
                    }
                    txn.commit()?;
                }

                Command::Resume(raw) => {
                    let name = Self::txn_name(&context.prefix)?;
                    let state: TransactionState = serde_json::from_str(raw)?;
                    let txn = self.mvcc.resume(state)?;
                    self.txns.insert(name.to_string(), txn);
                }

                Command::Rollback => {
                    let name = Self::txn_name(&context.prefix)?;
                    let txn = self.txns.remove(name).ok_or(format!("unknown txn {name}"))?;
                    txn.rollback()?;
                }

                Command::Scan(range) => {
                    let txn = self.get_txn(&context.prefix)?;

                    let kvs: Vec<_> = txn.scan(range).try_collect()?;
                    for (key, value) in kvs {
                        writeln!(output, "{}", format::Raw::key_value(&key, &value))?;
                    }
                }

                Command::ScanPrefix(prefix) => {
                    let txn = self.get_txn(&context.prefix)?;

                    let kvs: Vec<_> = txn.scan_prefix(prefix).try_collect()?;
                    for (key, value) in kvs {
                        writeln!(output, "{}", format::Raw::key_value(&key, &value))?;
                    }
                }

                Command::Set(entries) => {
                    let txn = self.get_txn(&context.prefix)?;
                    for (key, value) in entries {
                        txn.set(key, value.to_vec())?;
                    }
                }

                Command::SetUnversioned(entries) => {
                    Self::no_txn("set_unversioned", context)?;
                    for (key, value) in entries {
                        self.mvcc.set_unversioned(key, value.to_vec())?;
                    }
                }

                Command::State => {
                    let txn = self.get_txn(&context.prefix)?;
                    let state = txn.state();
                    write!(
                        output,
                        "v{} {} active={{{}}}",
                        state.version,
                        if state.read_only { "ro" } else { "rw" },
                        state.active.iter().sorted().join(",")
                    )?;
                }

                Command::Status => writeln!(output, "{:#?}", self.mvcc.status()?)?,
            }

            // If requested, output engine operations.
            if tags.remove("ops") {
                while let Ok(op) = self.op_rx.try_recv() {
                    match op {
                        Operation::Delete { key } => {
                            let fmtkey = format::MVCC::<format::Raw>::key(&key);
                            let rawkey = format::Raw::key(&key);
                            writeln!(output, "engine delete {fmtkey} [{rawkey}]")?
                        }
                        Operation::Flush => writeln!(output, "engine flush")?,
                        Operation::Set { key, value } => {
                            let fmtkv = format::MVCC::<format::Raw>::key_value(&key, &value);
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

        // Drain unhandled engine operations.
        fn end_command(
            &mut self,
            _: &Command,
            _: &goldenscript::Context,
        ) -> Result<String, Box<dyn Error>> {
            while self.op_rx.try_recv().is_ok() {}
            Ok(String::new())
        }
    }
}
