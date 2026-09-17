//! Narrow, audited trust boundary for textual finite-f64 round trips.

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use vstd::float::FloatBitsProperties;
use vstd::prelude::*;

#[allow(unused_imports)] // Used by Verus; erased from normal Rust builds.
use super::verified_integer;

verus! {

/// Raw bits of Rust's canonical quiet NaN value.
pub const CANONICAL_NAN_BITS: u64 = 0x7ff8_0000_0000_0000;

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
        r.to_bits_spec() == CANONICAL_NAN_BITS,
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
