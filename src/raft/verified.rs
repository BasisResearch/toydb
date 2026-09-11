//! The verified core of Raft: the durable log (`log`) and the node-local
//! refinement layer (`refine`).
//!
//! The two live under this shared parent module so that `Log`'s mutating
//! methods (`set_term_vote`, `append`, `commit`, `splice`) can be scoped to
//! it with `pub(in crate::raft::verified)`: every log mutation must go
//! through a verified step function in `refine`, whose postconditions keep
//! the ghost abstract state (`refine::Abs`) in sync with the log's ghost
//! view. The unverified I/O shell (`super::node`) gets read access only, so
//! it cannot mutate the log behind the refinement layer's back and silently
//! invalidate `Abs::inv` (and with it the refinement proof).

// The files stay at their original `src/raft/` paths (hence the explicit
// `#[path]`); only the module tree nests them under `verified`.

#[path = "log.rs"]
pub mod log;
// A normal build erases the ghost code, leaving the parameters that only
// feed ghost state unused.
#[allow(unused_variables)]
#[path = "refine.rs"]
pub mod refine;
