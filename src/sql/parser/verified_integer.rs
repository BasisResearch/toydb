//! Axiom-free decimal model for `u64` and non-negative `i64` integers.

#![allow(dead_code)]
#![allow(clippy::manual_range_contains)]

use vstd::prelude::*;

verus! {

pub const U64_MAX: u64 = 18_446_744_073_709_551_615u64;
pub const I64_MAX: u64 = 9_223_372_036_854_775_807u64;

pub open spec fn decimal_digits(n: u64) -> Seq<u8>
    decreases n,
{
    if n < 10 {
        seq![(48u64 + n) as u8]
    } else {
        decimal_digits(n / 10) + seq![(48u64 + n % 10) as u8]
    }
}

pub fn print_u64(n: u64) -> (r: Vec<u8>)
    ensures r@ == decimal_digits(n),
    decreases n,
{
    if n < 10 {
        vec![(48u64 + n) as u8]
    } else {
        let mut out = print_u64(n / 10);
        let ghost before = out@;
        out.push((48u64 + n % 10) as u8);
        proof {
            assert(n / 10 < n);
            assert(decimal_digits(n) == decimal_digits(n / 10)
                + seq![(48u64 + n % 10) as u8]);
            assert(before == decimal_digits(n / 10));
        }
        out
    }
}

pub fn print_i64(n: i64) -> (r: Vec<u8>)
    requires 0 <= n,
    ensures r@ == decimal_digits(n as u64),
{
    print_u64(n as u64)
}

pub open spec fn parse_digits_spec(input: Seq<u8>) -> Option<u64>
    decreases input.len(),
{
    if input.len() == 0 {
        None
    } else {
        let b = input[input.len() - 1];
        if 48u8 <= b && b <= 57u8 {
            let digit = (b - 48u8) as u64;
            if input.len() == 1 {
                Some(digit)
            } else {
                match parse_digits_spec(input.drop_last()) {
                    Some(prefix) if prefix <= (U64_MAX - digit) / 10 =>
                        Some((prefix * 10 + digit) as u64),
                    _ => None,
                }
            }
        } else {
            None
        }
    }
}

pub open spec fn all_digits(input: Seq<u8>) -> bool
    decreases input.len(),
{
    input.len() == 0 || (48u8 <= input[input.len() - 1] && input[input.len() - 1] <= 57u8
        && all_digits(input.drop_last()))
}

pub open spec fn parse_i64_spec(input: Seq<u8>) -> Option<i64> {
    match parse_digits_spec(input) {
        Some(value) if value <= I64_MAX => Some(value as i64),
        _ => None,
    }
}

pub fn parse_digits(input: &[u8]) -> (r: Option<u64>)
    ensures r == parse_digits_spec(input@),
    decreases input.len(),
{
    if input.is_empty() {
        None
    } else {
        let b = input[input.len() - 1];
        if 48u8 <= b && b <= 57u8 {
            let digit = (b - 48u8) as u64;
            if input.len() == 1 {
                Some(digit)
            } else {
                let prefix_input = vstd::slice::slice_subrange(input, 0, input.len() - 1);
                match parse_digits(prefix_input) {
                    Some(prefix) if prefix <= (U64_MAX - digit) / 10 => {
                        Some(prefix * 10 + digit)
                    }
                    _ => None,
                }
            }
        } else {
            None
        }
    }
}

pub fn parse_i64(input: &[u8]) -> (r: Option<i64>)
    ensures r == parse_i64_spec(input@),
{
    match parse_digits(input) {
        Some(value) if value <= I64_MAX => Some(value as i64),
        Some(_) => None,
        None => None,
    }
}

pub fn parse_u64(input: &[u8]) -> (r: Option<u64>)
    ensures r == parse_digits_spec(input@),
{
    parse_digits(input)
}

pub open spec fn print_i64_spec(n: i64) -> Seq<u8>
    recommends 0 <= n,
{
    decimal_digits(n as u64)
}

proof fn lemma_parse_decimal_digits(n: u64)
    ensures parse_digits_spec(decimal_digits(n)) == Some(n),
    decreases n,
{
    reveal(decimal_digits);
    reveal(parse_digits_spec);
    if n < 10 {
        assert(decimal_digits(n) == seq![(48u64 + n) as u8]);
        assert(parse_digits_spec(decimal_digits(n)) == Some(n));
    } else {
        assert(n / 10 < n);
        lemma_parse_decimal_digits(n / 10);
        assert(decimal_digits(n) == decimal_digits(n / 10)
            + seq![(48u64 + n % 10) as u8]);
        assert(decimal_digits(n).drop_last() == decimal_digits(n / 10)) by {
            Seq::drop_last_distributes_over_add(
                decimal_digits(n / 10),
                seq![(48u64 + n % 10) as u8],
            );
        }
        assert(parse_digits_spec(decimal_digits(n).drop_last()) == Some(n / 10));
        assert(n / 10 <= (U64_MAX - n % 10) / 10) by (nonlinear_arith);
        assert((n / 10) * 10 + n % 10 == n) by (nonlinear_arith);
        assert(parse_digits_spec(decimal_digits(n)) == Some(n));
    }
}

pub proof fn decimal_digits_are_digits(n: u64)
    ensures all_digits(decimal_digits(n)),
    decreases n,
{
    reveal(decimal_digits);
    reveal_with_fuel(all_digits, 2);
    if n >= 10 {
        decimal_digits_are_digits(n / 10);
        assert(all_digits(decimal_digits(n / 10)));
        assert(decimal_digits(n).drop_last() == decimal_digits(n / 10)) by {
            Seq::drop_last_distributes_over_add(
                decimal_digits(n / 10),
                seq![(48u64 + n % 10) as u8],
            );
        }
        assert(all_digits(decimal_digits(n).drop_last()));
        assert(decimal_digits(n)[decimal_digits(n).len() - 1]
            == (48u64 + n % 10) as u8);
        assert(all_digits(decimal_digits(n)));
    }
}

pub proof fn print_parse_u64_roundtrip(n: u64)
    ensures parse_digits_spec(decimal_digits(n)) == Some(n),
{
    lemma_parse_decimal_digits(n);
}

pub proof fn print_parse_roundtrip(n: i64)
    requires 0 <= n,
    ensures parse_digits_spec(print_i64_spec(n)) == Some(n as u64),
{
    let value = n as u64;
    lemma_parse_decimal_digits(value);
    assert(parse_digits_spec(print_i64_spec(n)) == Some(value));
}

} // verus!
