//! Audited trust boundary for Rust's Unicode character operations.

use vstd::prelude::*;

verus! {

/// Mathematical models of the Rust Unicode operations used by the lexer.
pub uninterp spec fn spec_is_alphabetic(c: char) -> bool;
pub uninterp spec fn spec_is_alphanumeric(c: char) -> bool;
pub uninterp spec fn spec_lowercase(c: char) -> Seq<char>;

#[verifier::external_body]
pub fn is_alphabetic(c: char) -> (r: bool)
    ensures r == spec_is_alphabetic(c),
{
    c.is_alphabetic()
}

#[verifier::external_body]
pub fn is_alphanumeric(c: char) -> (r: bool)
    ensures r == spec_is_alphanumeric(c),
{
    c.is_alphanumeric()
}

#[verifier::external_body]
pub fn lowercase(c: char) -> (r: Vec<char>)
    ensures r@ == spec_lowercase(c),
{
    c.to_lowercase().collect()
}

} // verus!
