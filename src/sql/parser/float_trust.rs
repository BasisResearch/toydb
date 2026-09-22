//! Narrow, audited trust boundary for textual finite-f64 round trips.
//!
//! `canonical_nan` deliberately promises only `r == spec_canonical_nan()`, not
//! a bit pattern. It used to also ensure `to_bits_spec() == 0x7ff8...` for a
//! body returning `f64::NAN`, which Rust does not guarantee: on a target where
//! that differs, an `external_body` postcondition asserting it would be false,
//! and a false assumption makes every obligation in the parser's NaN arms
//! vacuous rather than failing loudly. Nothing consumed the claim, so it was
//! pure downside and is gone.

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use vstd::float::FloatBitsProperties;
use vstd::prelude::*;

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::verified_integer;

verus! {

/// Mathematical formatter/parser symbols for the canonical runtime encoding.
/// The formatter uses Rust's `Debug` representation because, unlike `Display`,
/// it preserves the decimal point in values such as `1.0`.
pub uninterp spec fn spec_format(x: f64) -> Seq<u8>;
pub uninterp spec fn spec_parse(s: Seq<u8>) -> Option<f64>;
pub uninterp spec fn spec_canonical_nan() -> f64;
pub uninterp spec fn spec_infinity() -> f64;

/// Models the production f64 formatter and parser without exposing their
/// implementation to the verified parser.
#[verifier::external_body]
pub fn format_f64(x: f64) -> (r: Vec<u8>)
    ensures
        r@ == spec_format(x),
        !verified_integer::all_digits(r@),
{
    format!("{x:?}").into_bytes()
}

#[verifier::external_body]
pub fn parse_f64(s: &[u8]) -> (r: Option<f64>)
    ensures r == spec_parse(s@),
{
    match std::str::from_utf8(s) {
        Ok(text) => text.parse::<f64>().ok(),
        Err(_) => None,
    }
}

/// Constructs the exact NaN payload used by the production parser.
#[verifier::external_body]
pub fn canonical_nan() -> (r: f64)
    ensures
        r == spec_canonical_nan(),
{
    f64::NAN
}

#[verifier::external_body]
pub fn infinity() -> (r: f64)
    ensures r == spec_infinity(),
{
    f64::INFINITY
}

/// The sole semantic assumption: finite values survive the canonical
/// formatter and `FromStr` exactly. Non-finite values are outside the domain.
#[verifier::external_body]
pub proof fn axiom_f64_finite_roundtrip(x: f64)
    requires x.is_finite_spec(),
    ensures
        spec_parse(spec_format(x)) == Some(x),
        !verified_integer::all_digits(spec_format(x)),
{
}

} // verus!
