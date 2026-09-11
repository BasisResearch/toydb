// Fixture: a module with a verus! block mixing exec/spec/proof functions and
// plain (external-by-default) functions outside the block. Line numbers are
// load-bearing for the span-join tests, so do not reformat casually.
//
// Layout (1-based lines):
//   1-13  header comment
//   14    fn outside_block()      -- NOT verified (outside verus!)
//   16    verus! {
//   17    pub fn reached_exec()   -- exec, executed in cov fixture
//   21    pub fn dead_exec()      -- exec, NOT executed in cov fixture -> FLAG
//   25    pub spec fn a_spec()    -- ghost, never flagged
//   28    proof fn a_proof()      -- ghost, never flagged
//   32    } // verus!
fn outside_block() -> u32 {
    99
}
verus! {
pub fn reached_exec(x: u32) -> u32 {
    x + 1
}

pub fn dead_exec(x: u32) -> u32 {
    x + 2
}

pub open spec fn a_spec(x: u32) -> u32 {
    x
}

proof fn a_proof(x: u32)
    ensures x == x
{
}
} // verus!
