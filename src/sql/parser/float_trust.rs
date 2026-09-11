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

/// Runtime classifications used by the canonical printer.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FloatClass {
    Printable,
    CanonicalNan,
    Other,
}

/// Models both the finite/nonnegative literal guard and the exact NaN payload
/// accepted after `IS`.
#[verifier::external_body]
pub fn classify_f64(x: f64) -> (r: FloatClass)
    ensures r == if x.is_finite_spec() && !x.is_sign_negative_spec() {
        FloatClass::Printable
    } else if x.to_bits_spec() == CANONICAL_NAN_BITS {
        FloatClass::CanonicalNan
    } else {
        FloatClass::Other
    },
{
    if x.is_finite() && x.is_sign_positive() {
        FloatClass::Printable
    } else if x.to_bits() == CANONICAL_NAN_BITS {
        FloatClass::CanonicalNan
    } else {
        FloatClass::Other
    }
}

pub fn is_printable_f64(x: f64) -> (r: bool)
    ensures r == (x.is_finite_spec() && !x.is_sign_negative_spec()),
{
    matches!(classify_f64(x), FloatClass::Printable)
}

pub fn is_canonical_nan(x: f64) -> (r: bool)
    ensures r == (x.to_bits_spec() == CANONICAL_NAN_BITS),
{
    matches!(classify_f64(x), FloatClass::CanonicalNan)
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

/// Connects bit equality to Verus equality for the one NaN payload admitted
/// by the canonical `IS NAN` syntax.
#[verifier::external_body]
pub proof fn axiom_canonical_nan(value: f64)
    requires value.to_bits_spec() == CANONICAL_NAN_BITS,
    ensures
        value == spec_canonical_nan(),
        spec_canonical_nan().to_bits_spec() == CANONICAL_NAN_BITS,
{
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
