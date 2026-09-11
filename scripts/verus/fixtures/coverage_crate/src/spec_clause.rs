// Fixture: exercises the span computation across Verus spec clauses whose
// expressions contain braces (`ensures ({ ... })`) and a body brace on its own
// line at base indent. Regression guard for the truncated-span bug where the
// naive "first {" heuristic stopped inside the ensures clause. Line numbers are
// load-bearing.
//
//   9    verus! {
//   10   pub fn clause_body()   -- exec; body spans past the ensures braces
//   22   } // verus!
verus! {
pub fn clause_body(x: u32) -> (r: u32)
    requires x < 100,
    ensures ({
        let doubled = x + x;
        r == doubled
    }),
{
    let y = x + x;
    y
}
} // verus!
