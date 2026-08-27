//! Keycode is a lexicographical order-preserving binary encoding for use with
//! keys in key/value stores. It is designed for simplicity, not efficiency
//! (i.e. it does not use varints or other compression methods).
//!
//! Ordering is important because it allows limited scans across specific parts
//! of the keyspace, e.g. scanning an individual table or using an index range
//! predicate like `WHERE id < 100`. It also avoids sorting in some cases where
//! the keys are already in the desired order, e.g. in the Raft log.
//!
//! The encoding is not self-describing: the caller must provide a concrete type
//! to decode into, and the binary key must conform to its structure.
//!
//! Keycode supports a subset of primitive data types, encoded as follows:
//!
//! * [`bool`]: `0x00` for `false`, `0x01` for `true`.
//! * [`u64`]: big-endian binary representation.
//! * [`i64`]: big-endian binary, sign bit flipped.
//! * [`f64`]: big-endian binary, sign bit flipped, all flipped if negative.
//! * [`Vec<u8>`]: `0x00` escaped as `0x00ff`, terminated with `0x0000`.
//! * [`String`]: like [`Vec<u8>`].
//! * Sequences: concatenation of contained elements, with no other structure.
//! * Enum: the variant's index as [`u8`], then the content sequence.
//! * [`crate::sql::types::Value`]: like any other enum.
//!
//! The canonical key representation is an enum. For example:
//!
//! ```
//! #[derive(Debug, Deserialize, Serialize)]
//! enum Key {
//!     Foo,
//!     Bar(String),
//!     Baz(bool, u64, #[serde(with = "serde_bytes")] Vec<u8>),
//! }
//! ```
//!
//! Unfortunately, byte strings such as `Vec<u8>` must be wrapped with
//! [`serde_bytes::ByteBuf`] or use the `#[serde(with="serde_bytes")]`
//! attribute. See <https://github.com/serde-rs/bytes>.

use std::ops::Bound;

use serde::de::{
    Deserialize, DeserializeSeed, EnumAccess, IntoDeserializer as _, SeqAccess, VariantAccess,
    Visitor,
};
use serde::ser::{Impossible, Serialize, SerializeSeq, SerializeTuple, SerializeTupleVariant};

use crate::errdata;
use crate::error::{Error, Result};

// --- Verus-verified core of the i64 key encoding ---------------------------
//
// An i64 is stored as its big-endian bytes with the sign bit flipped, so that
// the unsigned lexicographic byte order of encoded keys matches the signed
// order of the values (see `serialize_i64` below). Flipping the sign bit of the
// big-endian bytes is exactly `x ^ (1 << 63)` on the u64 view of those bytes.
//
// The functions below are the executable encoder/decoder that
// `serialize_i64` / `deserialize_i64` call. Verus proves they are mutual
// inverses (`i64_key_roundtrip`) and order-preserving (`i64_key_order`), which
// are the two correctness properties keycode relies on. Everything else in this
// file is external-by-default and unverified. `verus!` erases all of this to
// the two plain `fn` bodies under a normal `cargo build`.
use vstd::prelude::*;

verus! {

/// The order-preserving u64 key for an i64 value: flip the sign bit.
pub open spec fn i64_key(v: i64) -> u64 {
    (v as u64) ^ (1u64 << 63)
}

/// The encoding is reversible: flipping the sign bit twice is the identity.
pub proof fn i64_key_roundtrip(v: i64)
    ensures (i64_key(v) ^ (1u64 << 63)) as i64 == v,
{
    assert((((v as u64) ^ (1u64 << 63)) ^ (1u64 << 63)) as i64 == v) by (bit_vector);
}

/// The encoding is order-preserving: signed `<=` on values matches unsigned
/// `<=` on keys, which is what makes lexicographic key scans correct.
pub proof fn i64_key_order(a: i64, b: i64)
    ensures a <= b <==> i64_key(a) <= i64_key(b),
{
    assert(a <= b <==> ((a as u64) ^ (1u64 << 63)) <= ((b as u64) ^ (1u64 << 63)))
        by (bit_vector);
}

/// Executable encoder, proven to compute `i64_key`.
pub fn encode_i64_key(v: i64) -> (r: u64)
    ensures r == i64_key(v),
{
    (v as u64) ^ (1u64 << 63)
}

/// Executable decoder, proven to invert the encoding: `i64_key(decode(k)) == k`.
pub fn decode_i64_key(k: u64) -> (r: i64)
    ensures i64_key(r) == k,
{
    assert(((((k ^ (1u64 << 63)) as i64) as u64) ^ (1u64 << 63)) == k) by (bit_vector);
    (k ^ (1u64 << 63)) as i64
}

// --- Verus-verified core of the f64 key encoding ---------------------------
//
// An f64 is stored as its big-endian IEEE-754 bytes, transformed so unsigned
// lexicographic byte order matches float order: a positive float (sign bit
// clear) gets its sign bit set, and a negative float (sign bit set) gets all
// bits flipped (see `serialize_f64` below). On the u64 `to_bits` view that is
// `bits ^ (1 << 63)` for positives and `!bits` for negatives. Unlike i64 this
// transform branches on the sign, so encode and decode invert each other via a
// two-case bit-vector argument (`f64_key_roundtrip`).
//
// We verify the round trip (no bit pattern — NaN payloads included — is lost),
// which is what `serialize_f64` / `deserialize_f64` rely on for correctness.
// Order preservation is deliberately out of scope here: it is a property of
// IEEE-754 float ordering, which Verus does not model, so it cannot be stated
// as an honest `f64 <= f64` spec.

/// The order-preserving u64 key for an f64's raw IEEE-754 bits: a positive
/// float (sign bit clear) gets its sign bit set; a negative float (sign bit
/// set) gets all bits flipped.
pub open spec fn f64_key(bits: u64) -> u64 {
    if bits & (1u64 << 63) == 0 {
        bits ^ (1u64 << 63)
    } else {
        !bits
    }
}

/// The inverse transform: if the key's top bit is set the input was positive
/// (undo the sign-bit flip), otherwise it was negative (undo the full flip).
pub open spec fn f64_unkey(key: u64) -> u64 {
    if key & (1u64 << 63) != 0 {
        key ^ (1u64 << 63)
    } else {
        !key
    }
}

/// The encoding is reversible on every bit pattern, so a serialize/deserialize
/// round trip preserves the exact f64 (including NaN payloads).
pub proof fn f64_key_roundtrip(bits: u64)
    ensures f64_unkey(f64_key(bits)) == bits,
{
    assert(f64_unkey(f64_key(bits)) == bits) by (bit_vector);
}

/// Executable encoder, proven to compute `f64_key`.
pub fn encode_f64_key(bits: u64) -> (r: u64)
    ensures r == f64_key(bits),
{
    if bits & (1u64 << 63) == 0 {
        bits ^ (1u64 << 63)
    } else {
        !bits
    }
}

/// Executable decoder, proven to compute `f64_unkey` (the inverse of
/// `encode_f64_key`, per `f64_key_roundtrip`).
pub fn decode_f64_key(key: u64) -> (r: u64)
    ensures r == f64_unkey(key),
{
    if key & (1u64 << 63) != 0 {
        key ^ (1u64 << 63)
    } else {
        !key
    }
}

// --- Verus-verified core of the bool key encoding --------------------------
//
// A bool is stored as a single byte: 0x01 for true, 0x00 for false (see
// `serialize_bool` / `deserialize_bool`). The round trip is trivial but we
// state it so the encoder/decoder are pinned to the same byte convention.

/// The single-byte key for a bool: 1 for true, 0 for false.
pub open spec fn bool_key(b: bool) -> u8 {
    if b { 1u8 } else { 0u8 }
}

/// Executable encoder, proven to compute `bool_key`.
pub fn encode_bool_key(b: bool) -> (r: u8)
    ensures r == bool_key(b),
{
    if b { 1u8 } else { 0u8 }
}

/// Executable decoder, proven to invert the encoding for the two valid bytes.
pub fn decode_bool_key(byte: u8) -> (r: bool)
    requires byte == 0u8 || byte == 1u8,
    ensures bool_key(r) == byte,
{
    byte == 1u8
}

// --- Verus-verified core of the byte-string key encoding -------------------
//
// A byte slice is encoded by escaping each 0x00 as the pair `0x00 0xff` and
// appending a `0x00 0x00` terminator (see `serialize_bytes` /
// `decode_next_bytes` below). This makes the encoding self-terminating and,
// because the terminator `0x00 0x00` is <= any escaped continuation, order-
// preserving so that a prefix orders before a longer string.
//
// `bytes_enc` is the mathematical encoding; `bytes_dec` is its parser, returning
// the decoded content together with the bytes that follow the terminator.
// `bytes_roundtrip` proves they are inverse on every input, which is exactly the
// property keycode relies on to deserialize a key unambiguously.

/// The escaped bytes of `v` *without* the terminator: each `0x00` becomes the
/// pair `0x00 0xff`, every other byte is copied verbatim.
pub open spec fn esc_all(v: Seq<u8>) -> Seq<u8>
    decreases v.len(),
{
    if v.len() == 0 {
        Seq::empty()
    } else {
        let esc = if v[0] == 0u8 { seq![0u8, 255u8] } else { seq![v[0]] };
        esc + esc_all(v.subrange(1, v.len() as int))
    }
}

/// The full escaped encoding of a byte string: escaped body then the
/// `0x00 0x00` terminator.
pub open spec fn bytes_enc(v: Seq<u8>) -> Seq<u8> {
    esc_all(v) + seq![0u8, 0u8]
}

/// The parser: given an encoded stream, returns the decoded byte string and the
/// bytes remaining after the terminator. On malformed input it returns empty
/// sequences (never reached for `bytes_enc` output, per `bytes_roundtrip`).
pub open spec fn bytes_dec(s: Seq<u8>) -> (Seq<u8>, Seq<u8>)
    decreases s.len(),
{
    if s.len() < 2 {
        (Seq::<u8>::empty(), Seq::<u8>::empty())
    } else if s[0] == 0u8 {
        if s[1] == 0u8 {
            // terminator
            (Seq::<u8>::empty(), s.subrange(2, s.len() as int))
        } else if s[1] == 255u8 {
            // escaped 0x00
            let rest = bytes_dec(s.subrange(2, s.len() as int));
            (seq![0u8] + rest.0, rest.1)
        } else {
            (Seq::<u8>::empty(), Seq::<u8>::empty())
        }
    } else {
        // literal byte
        let rest = bytes_dec(s.subrange(1, s.len() as int));
        (seq![s[0]] + rest.0, rest.1)
    }
}

/// Encoding then parsing recovers the original byte string and leaves any
/// trailing bytes untouched: `bytes_dec(bytes_enc(v) + suffix) == (v, suffix)`.
/// Taking `suffix == []` gives the plain round trip `bytes_dec(bytes_enc(v)).0
/// == v`.
pub proof fn bytes_roundtrip(v: Seq<u8>, suffix: Seq<u8>)
    ensures bytes_dec(bytes_enc(v) + suffix) == (v, suffix),
    decreases v.len(),
{
    let s = bytes_enc(v) + suffix;
    if v.len() == 0 {
        assert(esc_all(v) == Seq::<u8>::empty());
        assert(bytes_enc(v) =~= seq![0u8, 0u8]);
        assert(s =~= seq![0u8, 0u8] + suffix);
        assert(s.len() >= 2);
        assert(s[0] == 0u8 && s[1] == 0u8);
        assert(s.subrange(2, s.len() as int) =~= suffix);
    } else {
        let tail = v.subrange(1, v.len() as int);
        bytes_roundtrip(tail, suffix);
        // enc(v) = esc(v[0]) + esc_all(tail) + [0,0]; regroup so the suffix
        // rides along with the tail's full encoding.
        assert(bytes_enc(tail) + suffix =~= esc_all(tail) + seq![0u8, 0u8] + suffix);
        if v[0] == 0u8 {
            assert(esc_all(v) =~= seq![0u8, 255u8] + esc_all(tail));
            assert(s =~= seq![0u8, 255u8] + (bytes_enc(tail) + suffix));
            assert(s.len() >= 2);
            assert(s[0] == 0u8 && s[1] == 255u8);
            assert(s.subrange(2, s.len() as int) =~= bytes_enc(tail) + suffix);
            assert(v =~= seq![0u8] + tail);
        } else {
            assert(esc_all(v) =~= seq![v[0]] + esc_all(tail));
            assert(s =~= seq![v[0]] + (bytes_enc(tail) + suffix));
            assert(s.len() >= 2);
            assert(s[0] == v[0] && s[0] != 0u8);
            assert(s.subrange(1, s.len() as int) =~= bytes_enc(tail) + suffix);
            assert(v =~= seq![v[0]] + tail);
        }
    }
}

/// `esc_all` is a homomorphism from concatenation to concatenation: escaping a
/// concatenation is the concatenation of the escapes. This is what lets the
/// executable encoder build the result one byte at a time.
pub proof fn esc_all_concat(a: Seq<u8>, b: Seq<u8>)
    ensures esc_all(a + b) == esc_all(a) + esc_all(b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
        assert(esc_all(a) =~= Seq::<u8>::empty());
    } else {
        let a0 = a.subrange(1, a.len() as int);
        esc_all_concat(a0, b);
        assert((a + b).len() > 0);
        assert((a + b)[0] == a[0]);
        assert((a + b).subrange(1, (a + b).len() as int) =~= a0 + b);
    }
}

/// The escape of a single byte, matching `esc_all` on a one-element sequence.
pub proof fn esc_all_single(b: u8)
    ensures
        esc_all(seq![b]) == (if b == 0u8 { seq![0u8, 255u8] } else { seq![b] }),
{
    assert(seq![b].subrange(1, 1) =~= Seq::<u8>::empty());
    assert(esc_all(Seq::<u8>::empty()) =~= Seq::<u8>::empty());
}

/// Executable encoder, proven to compute `bytes_enc(v)`: escape each `0x00` as
/// `0x00 0xff` and append the `0x00 0x00` terminator. This is the verified core
/// that `serialize_bytes` calls.
pub fn encode_bytes(v: &[u8]) -> (r: Vec<u8>)
    ensures r@ == bytes_enc(v@),
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            out@ == esc_all(v@.subrange(0, i as int)),
        decreases v.len() - i,
    {
        let b = v[i];
        proof {
            esc_all_concat(v@.subrange(0, i as int), seq![b]);
            esc_all_single(b);
            assert(v@.subrange(0, i as int + 1) =~= v@.subrange(0, i as int) + seq![b]);
        }
        if b == 0u8 {
            out.push(0u8);
            out.push(255u8);
        } else {
            out.push(b);
        }
        i += 1;
    }
    proof {
        assert(v@.subrange(0, v.len() as int) =~= v@);
    }
    out.push(0u8);
    out.push(0u8);
    assert(out@ =~= esc_all(v@) + seq![0u8, 0u8]);
    out
}

/// The outcome of `decode_bytes`: either the decoded byte string with the
/// number of input bytes consumed, or one of the two malformed-input cases,
/// mirroring the diagnostics `decode_next_bytes` reports.
pub enum DecodeBytes {
    /// `Decoded(bytes, taken)`: the parsed content and the number of input
    /// bytes consumed (up to and including the `0x00 0x00` terminator).
    Decoded(Vec<u8>, usize),
    /// A `0x00` was not followed by `0x00` (terminator) or `0xff` (escape).
    InvalidEscape,
    /// The input ran out at an element boundary with no terminator.
    UnexpectedEnd,
}

/// Executable decoder, proven to compute `bytes_dec(s)` on success: it returns
/// `Decoded(decoded, taken)` where `decoded` is the parsed byte string and
/// `taken` is the number of input bytes consumed (up to and including the
/// terminator). Malformed input yields `InvalidEscape` or `UnexpectedEnd`,
/// matching the two cases `decode_next_bytes` distinguishes. This is the
/// verified core that `decode_next_bytes` calls.
pub fn decode_bytes(s: &[u8]) -> (r: DecodeBytes)
    ensures
        match r {
            DecodeBytes::Decoded(d, n) => {
                &&& n <= s@.len()
                &&& d@ == bytes_dec(s@).0
                &&& n as int == s@.len() - bytes_dec(s@).1.len()
                &&& s@.subrange(n as int, s@.len() as int) == bytes_dec(s@).1
            }
            _ => true,
        },
{
    let ghost full = s@;
    let mut decoded: Vec<u8> = Vec::new();
    let mut pos: usize = 0;
    assert(full.subrange(0, full.len() as int) =~= full);
    assert(decoded@ + bytes_dec(full).0 =~= bytes_dec(full).0);
    loop
        invariant
            pos <= s@.len(),
            s@ == full,
            bytes_dec(full).0 == decoded@ + bytes_dec(
                full.subrange(pos as int, full.len() as int),
            ).0,
            bytes_dec(full).1 == bytes_dec(full.subrange(pos as int, full.len() as int)).1,
        decreases s@.len() - pos,
    {
        let ghost suf = full.subrange(pos as int, full.len() as int);
        if s.len() - pos < 2 {
            // Fewer than two bytes remain: no room for a terminator. A lone
            // trailing 0x00 is a truncated escape; anything else is a missing
            // terminator (matching decode_next_bytes' two error paths).
            if pos < s.len() && s[pos] == 0 {
                return DecodeBytes::InvalidEscape;
            } else {
                return DecodeBytes::UnexpectedEnd;
            }
        }
        let b0 = s[pos];
        let b1 = s[pos + 1];
        assert(suf.len() >= 2);
        assert(suf[0] == b0 && suf[1] == b1);
        if b0 == 0 {
            if b1 == 0 {
                // Terminator: the decoded bytes so far are the full result.
                assert(bytes_dec(suf).0 =~= Seq::<u8>::empty());
                assert(bytes_dec(suf).1 =~= full.subrange(pos as int + 2, full.len() as int));
                assert(decoded@ =~= bytes_dec(full).0);
                return DecodeBytes::Decoded(decoded, pos + 2);
            } else if b1 == 255 {
                // Escaped 0x00.
                let ghost suf2 = full.subrange(pos as int + 2, full.len() as int);
                assert(suf.subrange(2, suf.len() as int) =~= suf2);
                assert(bytes_dec(suf).0 =~= seq![0u8] + bytes_dec(suf2).0);
                assert(bytes_dec(suf).1 == bytes_dec(suf2).1);
                decoded.push(0);
                pos += 2;
                assert(decoded@ + bytes_dec(suf2).0 =~= bytes_dec(full).0);
            } else {
                // Invalid escape sequence.
                return DecodeBytes::InvalidEscape;
            }
        } else {
            // Literal byte.
            let ghost suf1 = full.subrange(pos as int + 1, full.len() as int);
            assert(suf.subrange(1, suf.len() as int) =~= suf1);
            assert(bytes_dec(suf).0 =~= seq![b0] + bytes_dec(suf1).0);
            assert(bytes_dec(suf).1 == bytes_dec(suf1).1);
            decoded.push(b0);
            pos += 1;
            assert(decoded@ + bytes_dec(suf1).0 =~= bytes_dec(full).0);
        }
    }
}

} // verus!

/// Serializes a key to a binary Keycode representation.
///
/// In the common case, the encoded key is borrowed for a storage engine call
/// and then thrown away. We could avoid a bunch of allocations by taking a
/// reusable byte vector to encode into and return a reference to it, but we
/// keep it simple.
pub fn serialize<T: Serialize>(key: &T) -> Vec<u8> {
    let mut serializer = Serializer { output: Vec::new() };
    // Panic on failure, as this is a problem with the data structure.
    key.serialize(&mut serializer).expect("key must be serializable");
    serializer.output
}

/// Deserializes a key from a binary Keycode representation.
pub fn deserialize<'a, T: Deserialize<'a>>(input: &'a [u8]) -> Result<T> {
    let mut deserializer = Deserializer::from_bytes(input);
    let t = T::deserialize(&mut deserializer)?;
    if !deserializer.input.is_empty() {
        return errdata!(
            "unexpected trailing bytes {:x?} at end of key {input:x?}",
            deserializer.input,
        );
    }
    Ok(t)
}

// --- Verus-verified core of prefix range scans -----------------------------
//
// `prefix_range` turns a key prefix into a `[start, end)` byte range such that
// scanning that range visits exactly the keys that begin with the prefix. This
// is what makes prefix scans correct — e.g. scanning one SQL table (whose rows
// share a key prefix) or the tail of the Raft log. The verified core
// `prefix_end` computes the exclusive upper bound (a `None` result means the
// scan runs to the end of the keyspace), proven against the lexicographic byte
// order that the storage engine maintains.
verus! {

/// Strict lexicographic order on byte strings: compare byte by byte, and a
/// proper prefix orders before its extensions. This is the order the storage
/// engine keeps keys in.
pub open spec fn lex_lt(a: Seq<u8>, b: Seq<u8>) -> bool
    decreases a.len(),
{
    if a.len() == 0 {
        b.len() > 0
    } else if b.len() == 0 {
        false
    } else if a[0] != b[0] {
        a[0] < b[0]
    } else {
        lex_lt(a.subrange(1, a.len() as int), b.subrange(1, b.len() as int))
    }
}

/// Non-strict lexicographic order.
pub open spec fn lex_le(a: Seq<u8>, b: Seq<u8>) -> bool {
    a == b || lex_lt(a, b)
}

/// `p` is a prefix of `k`: `k` starts with all of `p`'s bytes.
pub open spec fn is_prefix(p: Seq<u8>, k: Seq<u8>) -> bool {
    p.len() <= k.len() && k.subrange(0, p.len() as int) == p
}

/// A prefix orders at-or-before any key it prefixes.
pub proof fn lemma_prefix_implies_le(p: Seq<u8>, k: Seq<u8>)
    requires is_prefix(p, k),
    ensures lex_le(p, k),
    decreases p.len(),
{
    if p.len() == 0 {
        // Empty prefix: p == k (k has length >= 0 and k[0..0] == p == []) or p < k.
        if k.len() == 0 {
            assert(p =~= k);
        } else {
            assert(lex_lt(p, k));
        }
    } else {
        // p[0] == k[0]; the tails are still in the prefix relation.
        assert(k[0] == p[0]) by {
            assert(k.subrange(0, p.len() as int)[0] == p[0]);
        }
        assert(k.len() > 0);
        let p1 = p.subrange(1, p.len() as int);
        let k1 = k.subrange(1, k.len() as int);
        assert(is_prefix(p1, k1)) by {
            assert(k1.subrange(0, p1.len() as int) =~= p1);
        }
        lemma_prefix_implies_le(p1, k1);
        // Fold the tail comparison back up to the full strings.
        if p == k {
            assert(lex_le(p, k));
        } else {
            // p != k with equal heads forces the tails to differ, so the IH
            // gives a strict order on the tails, which lifts to p < k.
            assert(p1 != k1) by {
                if p1 =~= k1 {
                    assert(p =~= k);
                }
            }
            assert(lex_lt(p1, k1));
            assert(lex_lt(p, k));
        }
    }
}

/// Build `lex_lt(a, b)` from a first point of difference: `a` and `b` agree on
/// `[0, m)` and `a[m] < b[m]`.
pub proof fn lemma_lex_lt_at(a: Seq<u8>, b: Seq<u8>, m: int)
    requires
        0 <= m < a.len(),
        m < b.len(),
        forall|j: int| 0 <= j < m ==> a[j] == b[j],
        a[m] < b[m],
    ensures
        lex_lt(a, b),
    decreases m,
{
    if m == 0 {
        // a[0] != b[0] with a[0] < b[0]: lex_lt reduces to the head comparison.
    } else {
        assert(a[0] == b[0]);
        let a1 = a.subrange(1, a.len() as int);
        let b1 = b.subrange(1, b.len() as int);
        assert forall|j: int| 0 <= j < m - 1 implies a1[j] == b1[j] by {
            assert(a1[j] == a[j + 1]);
            assert(b1[j] == b[j + 1]);
        }
        assert(a1[m - 1] == a[m] && b1[m - 1] == b[m]);
        lemma_lex_lt_at(a1, b1, m - 1);
    }
}

/// From strict order, the heads are ordered `<=`.
pub proof fn lemma_head_le_from_lt(a: Seq<u8>, b: Seq<u8>)
    requires
        lex_lt(a, b),
        a.len() > 0,
        b.len() > 0,
    ensures
        a[0] <= b[0],
{
}

/// From strict order with equal heads, the tails are strictly ordered.
pub proof fn lemma_tail_lt_from_lt(a: Seq<u8>, b: Seq<u8>)
    requires
        lex_lt(a, b),
        a.len() > 0,
        b.len() > 0,
        a[0] == b[0],
    ensures
        lex_lt(a.subrange(1, a.len() as int), b.subrange(1, b.len() as int)),
{
}

/// From non-strict order with equal heads, the tails are non-strictly ordered.
pub proof fn lemma_le_tail(a: Seq<u8>, b: Seq<u8>)
    requires
        lex_le(a, b),
        a.len() > 0,
        b.len() > 0,
        a[0] == b[0],
    ensures
        lex_le(a.subrange(1, a.len() as int), b.subrange(1, b.len() as int)),
{
    if a =~= b {
        assert(a.subrange(1, a.len() as int) =~= b.subrange(1, b.len() as int));
    } else {
        lemma_tail_lt_from_lt(a, b);
    }
}

/// Lift `is_prefix` over a shared head byte.
pub proof fn lemma_prefix_lift(p: Seq<u8>, k: Seq<u8>)
    requires
        p.len() > 0,
        k.len() > 0,
        p[0] == k[0],
        is_prefix(p.subrange(1, p.len() as int), k.subrange(1, k.len() as int)),
    ensures
        is_prefix(p, k),
{
    let p1 = p.subrange(1, p.len() as int);
    let k1 = k.subrange(1, k.len() as int);
    assert(k1.subrange(0, p1.len() as int) =~= p1);
    assert(k.subrange(0, p.len() as int) =~= p) by {
        assert forall|j: int| #![auto] 0 <= j < p.len() implies k.subrange(0, p.len() as int)[j] == p[j] by {
            if j >= 1 {
                assert(k1[j - 1] == k[j]);
                assert(p1[j - 1] == p[j]);
                assert(k1.subrange(0, p1.len() as int)[j - 1] == p1[j - 1]);
            }
        }
    }
}

/// When the prefix is all `0xff`, being `>=` the prefix already implies being
/// prefixed by it: no byte can exceed `0xff`, so a key can only be `>=` an
/// all-`0xff` prefix by extending it.
pub proof fn lemma_allff(p: Seq<u8>, k: Seq<u8>)
    requires
        forall|j: int| 0 <= j < p.len() ==> p[j] == 255,
        lex_le(p, k),
    ensures
        is_prefix(p, k),
    decreases p.len(),
{
    if p.len() == 0 {
        assert(k.subrange(0, 0) =~= p);
    } else if p =~= k {
        assert(k.subrange(0, p.len() as int) =~= p);
    } else {
        assert(lex_lt(p, k));
        assert(k.len() > 0);
        lemma_head_le_from_lt(p, k);
        assert(p[0] == 255);
        assert(k[0] == 255);
        let p1 = p.subrange(1, p.len() as int);
        let k1 = k.subrange(1, k.len() as int);
        lemma_le_tail(p, k);
        assert forall|j: int| 0 <= j < p1.len() implies p1[j] == 255 by {
            assert(p1[j] == p[j + 1]);
        }
        lemma_allff(p1, k1);
        lemma_prefix_lift(p, k);
    }
}

/// From non-strict order, the heads are ordered `<=`.
pub proof fn lemma_head_le_from_le(a: Seq<u8>, b: Seq<u8>)
    requires
        lex_le(a, b),
        a.len() > 0,
        b.len() > 0,
    ensures
        a[0] <= b[0],
{
    if a =~= b {
    } else {
        lemma_head_le_from_lt(a, b);
    }
}

/// Forward direction of prefix-range correctness: every key prefixed by `p`
/// lies in `[p, end)`, where `end` is `p` truncated after its last non-`0xff`
/// byte `i`, with that byte incremented.
pub proof fn lemma_prefix_end_fwd(p: Seq<u8>, i: int, e: Seq<u8>, k: Seq<u8>)
    requires
        0 <= i < p.len(),
        p[i] != 255,
        e == p.subrange(0, i) + seq![((p[i] + 1) as u8)],
        is_prefix(p, k),
    ensures
        lex_le(p, k),
        lex_lt(k, e),
{
    lemma_prefix_implies_le(p, k);
    assert(e.len() == i + 1);
    assert(i < k.len());
    assert forall|j: int| 0 <= j < i implies k[j] == e[j] by {
        assert(k.subrange(0, p.len() as int)[j] == p[j]);
        assert(e[j] == p[j]);
    }
    assert(k[i] == p[i]) by {
        assert(k.subrange(0, p.len() as int)[i] == p[i]);
    }
    assert(e[i] == (p[i] + 1) as u8);
    assert(k[i] < e[i]);
    lemma_lex_lt_at(k, e, i);
}

/// Backward direction of prefix-range correctness: every key in `[p, end)` is
/// prefixed by `p`. Together with the forward direction this makes the range
/// exact. Proved by induction on `i`, peeling one shared head byte at a time.
pub proof fn lemma_prefix_end_bwd(p: Seq<u8>, i: int, e: Seq<u8>, k: Seq<u8>)
    requires
        0 <= i < p.len(),
        p[i] != 255,
        forall|j: int| i < j < p.len() ==> p[j] == 255,
        e == p.subrange(0, i) + seq![((p[i] + 1) as u8)],
        lex_le(p, k),
        lex_lt(k, e),
    ensures
        is_prefix(p, k),
    decreases i,
{
    assert(e.len() == i + 1);
    assert(k.len() > 0);
    lemma_head_le_from_le(p, k);
    lemma_head_le_from_lt(k, e);
    let p1 = p.subrange(1, p.len() as int);
    let k1 = k.subrange(1, k.len() as int);
    if i == 0 {
        // end == [p[0]+1]. k[0] can only be p[0] (p[0]+1 would force k >= end).
        assert(e[0] == (p[0] + 1) as u8);
        if k[0] == e[0] {
            lemma_tail_lt_from_lt(k, e);
            assert(e.subrange(1, e.len() as int).len() == 0);
            assert(false);
        }
        assert(k[0] == p[0]);
        lemma_le_tail(p, k);
        assert forall|j: int| 0 <= j < p1.len() implies p1[j] == 255 by {
            assert(p1[j] == p[j + 1]);
        }
        lemma_allff(p1, k1);
        lemma_prefix_lift(p, k);
    } else {
        // e[0] == p[0]; the head must match and we recurse on the tails.
        assert(e[0] == p[0]);
        assert(k[0] == p[0]);
        lemma_le_tail(p, k);
        lemma_tail_lt_from_lt(k, e);
        let e1 = e.subrange(1, e.len() as int);
        assert(e1 == p1.subrange(0, i - 1) + seq![((p1[i - 1] + 1) as u8)]) by {
            assert(p1[i - 1] == p[i]);
            assert forall|m: int| 0 <= m < i implies e1[m] == (p1.subrange(0, i - 1) + seq![
                ((p1[i - 1] + 1) as u8),
            ])[m] by {
                assert(e1[m] == e[m + 1]);
                if m < i - 1 {
                    assert(p1.subrange(0, i - 1)[m] == p1[m]);
                    assert(p1[m] == p[m + 1]);
                    assert(e[m + 1] == p[m + 1]);
                }
            }
        }
        assert forall|j: int| i - 1 < j < p1.len() implies p1[j] == 255 by {
            assert(p1[j] == p[j + 1]);
        }
        lemma_prefix_end_bwd(p1, i - 1, e1, k1);
        lemma_prefix_lift(p, k);
    }
}

/// Executable core of `prefix_range`: computes the exclusive upper bound key for
/// a prefix scan, or `None` (scan to the end of the keyspace) when the prefix is
/// empty or all `0xff`. Proven correct: the returned bound makes the range
/// `[prefix, end)` contain *exactly* the keys prefixed by `prefix`.
pub fn prefix_end(prefix: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        match r {
            Option::None => forall|k: Seq<u8>|
                #![trigger is_prefix(prefix@, k)]
                is_prefix(prefix@, k) <==> lex_le(prefix@, k),
            Option::Some(e) => forall|k: Seq<u8>|
                #![trigger is_prefix(prefix@, k)]
                is_prefix(prefix@, k) <==> (lex_le(prefix@, k) && lex_lt(k, e@)),
        },
{
    let n = prefix.len();
    let mut i = n;
    while i > 0
        invariant
            i <= n,
            n == prefix.len(),
            forall|j: int| i <= j < n ==> prefix@[j] == 255,
        decreases i,
    {
        if prefix[i - 1] != 255 {
            let idx = i - 1;
            assert(prefix@[idx as int] != 255);
            assert(forall|j: int| idx < j < n ==> prefix@[j] == 255);
            // Build e = prefix[0..idx] ++ [prefix[idx] + 1].
            let mut e: Vec<u8> = Vec::new();
            let mut m: usize = 0;
            while m < idx
                invariant
                    m <= idx,
                    idx < n,
                    n == prefix.len(),
                    e@ == prefix@.subrange(0, m as int),
                decreases idx - m,
            {
                e.push(prefix[m]);
                assert(prefix@.subrange(0, m as int + 1) =~= prefix@.subrange(0, m as int)
                    + seq![prefix@[m as int]]);
                m += 1;
            }
            assert(prefix@[idx as int] < 255);
            let last = prefix[idx] + 1;
            e.push(last);
            assert(e@ =~= prefix@.subrange(0, idx as int) + seq![((prefix@[idx as int] + 1) as u8)]);
            proof {
                assert forall|k: Seq<u8>|
                    #![trigger is_prefix(prefix@, k)]
                    is_prefix(prefix@, k) <==> (lex_le(prefix@, k) && lex_lt(k, e@)) by {
                    if is_prefix(prefix@, k) {
                        lemma_prefix_end_fwd(prefix@, idx as int, e@, k);
                    }
                    if lex_le(prefix@, k) && lex_lt(k, e@) {
                        lemma_prefix_end_bwd(prefix@, idx as int, e@, k);
                    }
                }
            }
            return Some(e);
        }
        i -= 1;
    }
    // i == 0: every byte is 0xff (or the prefix is empty), so the scan has no
    // upper bound.
    assert(forall|j: int| 0 <= j < n ==> prefix@[j] == 255);
    proof {
        assert forall|k: Seq<u8>|
            #![trigger is_prefix(prefix@, k)]
            is_prefix(prefix@, k) <==> lex_le(prefix@, k) by {
            if is_prefix(prefix@, k) {
                lemma_prefix_implies_le(prefix@, k);
            }
            if lex_le(prefix@, k) {
                lemma_allff(prefix@, k);
            }
        }
    }
    None
}

} // verus!

/// Generates a key range for a key prefix, used e.g. for prefix scans.
///
/// The exclusive end bound is generated by adding 1 to the value of the last
/// byte. If the last byte(s) is 0xff (so adding 1 would overflow), we instead
/// find the latest non-0xff byte, increment that, and truncate the rest. If all
/// bytes are 0xff, we scan to the end of the range, since there can't be other
/// prefixes after it.
pub fn prefix_range(prefix: &[u8]) -> (Bound<Vec<u8>>, Bound<Vec<u8>>) {
    let start = Bound::Included(prefix.to_vec());
    // `prefix_end` is the Verus-verified core: it computes the exclusive upper
    // bound (`Some`) or signals an unbounded scan (`None`), proven to make
    // `[prefix, end)` cover exactly the keys prefixed by `prefix`. See the
    // `verus!` block above.
    let end = match prefix_end(prefix) {
        Some(e) => Bound::Excluded(e),
        None => Bound::Unbounded,
    };
    (start, end)
}

/// Serializes keys as binary byte vectors.
struct Serializer {
    output: Vec<u8>,
}

impl serde::ser::Serializer for &mut Serializer {
    type Ok = ();
    type Error = Error;

    type SerializeSeq = Self;
    type SerializeTuple = Self;
    type SerializeTupleVariant = Self;
    type SerializeTupleStruct = Impossible<(), Error>;
    type SerializeMap = Impossible<(), Error>;
    type SerializeStruct = Impossible<(), Error>;
    type SerializeStructVariant = Impossible<(), Error>;

    /// bool simply uses 1 for true and 0 for false.
    fn serialize_bool(self, v: bool) -> Result<()> {
        self.output.push(if v { 1 } else { 0 });
        Ok(())
    }

    fn serialize_i8(self, _: i8) -> Result<()> {
        unimplemented!()
    }

    fn serialize_i16(self, _: i16) -> Result<()> {
        unimplemented!()
    }

    fn serialize_i32(self, _: i32) -> Result<()> {
        unimplemented!()
    }

    /// i64 uses the big-endian two's complement encoding, but flips the
    /// left-most sign bit such that negative numbers are ordered before
    /// positive numbers.
    ///
    /// The relative ordering of the remaining bits is already correct: -1, the
    /// largest negative integer, is encoded as 01111111...11111111, ordered
    /// after all other negative integers but before positive integers.
    fn serialize_i64(self, v: i64) -> Result<()> {
        // Verified encoder: big-endian bytes with the sign bit flipped.
        self.output.extend(encode_i64_key(v).to_be_bytes());
        Ok(())
    }

    fn serialize_u8(self, _: u8) -> Result<()> {
        unimplemented!()
    }

    fn serialize_u16(self, _: u16) -> Result<()> {
        unimplemented!()
    }

    fn serialize_u32(self, _: u32) -> Result<()> {
        unimplemented!()
    }

    /// u64 simply uses the big-endian encoding.
    fn serialize_u64(self, v: u64) -> Result<()> {
        self.output.extend(v.to_be_bytes());
        Ok(())
    }

    fn serialize_f32(self, _: f32) -> Result<()> {
        unimplemented!()
    }

    /// f64 is encoded in big-endian IEEE 754 form, but it flips the sign bit to
    /// order positive numbers after negative numbers, and also flips all other
    /// bits for negative numbers to order them from smallest to largest. NaN is
    /// ordered at the end.
    fn serialize_f64(self, v: f64) -> Result<()> {
        // Verified encoder: the sign-dependent bit flip on the IEEE-754 bits,
        // stored big-endian. `to_bits` gives the same bytes as `to_be_bytes`.
        self.output.extend(encode_f64_key(v.to_bits()).to_be_bytes());
        Ok(())
    }

    fn serialize_char(self, _: char) -> Result<()> {
        unimplemented!()
    }

    // Strings are encoded like bytes.
    fn serialize_str(self, v: &str) -> Result<()> {
        self.serialize_bytes(v.as_bytes())
    }

    // Byte slices are terminated by 0x0000, escaping 0x00 as 0x00ff. This
    // ensures that we can detect the end, and that for two overlapping slices,
    // the shorter one orders before the longer one.
    //
    // We can't use e.g. length prefix encoding, since it doesn't sort correctly.
    fn serialize_bytes(self, v: &[u8]) -> Result<()> {
        // `encode_bytes` is the Verus-verified core, proven to compute
        // `bytes_enc` (escape each 0x00 as 0x00ff, append the 0x0000
        // terminator). See the `verus!` block above.
        self.output.extend(encode_bytes(v));
        Ok(())
    }

    fn serialize_none(self) -> Result<()> {
        unimplemented!()
    }

    fn serialize_some<T: Serialize + ?Sized>(self, _: &T) -> Result<()> {
        unimplemented!()
    }

    fn serialize_unit(self) -> Result<()> {
        unimplemented!()
    }

    fn serialize_unit_struct(self, _: &'static str) -> Result<()> {
        unimplemented!()
    }

    /// Enum variants are serialized using their index, as a single byte.
    fn serialize_unit_variant(self, _: &'static str, index: u32, _: &'static str) -> Result<()> {
        self.output.push(index.try_into()?);
        Ok(())
    }

    fn serialize_newtype_struct<T: Serialize + ?Sized>(self, _: &'static str, _: &T) -> Result<()> {
        unimplemented!()
    }

    /// Newtype variants are serialized using the variant index and inner type.
    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        name: &'static str,
        index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<()> {
        self.serialize_unit_variant(name, index, variant)?;
        value.serialize(self)
    }

    /// Sequences are serialized as the concatenation of the serialized elements.
    fn serialize_seq(self, _: Option<usize>) -> Result<Self::SerializeSeq> {
        Ok(self)
    }

    /// Tuples are serialized as the concatenation of the serialized elements.
    fn serialize_tuple(self, _: usize) -> Result<Self::SerializeTuple> {
        Ok(self)
    }

    fn serialize_tuple_struct(
        self,
        _: &'static str,
        _: usize,
    ) -> Result<Self::SerializeTupleStruct> {
        unimplemented!()
    }

    /// Tuple variants are serialized using the variant index and the
    /// concatenation of the serialized elements.
    fn serialize_tuple_variant(
        self,
        name: &'static str,
        index: u32,
        variant: &'static str,
        _: usize,
    ) -> Result<Self::SerializeTupleVariant> {
        self.serialize_unit_variant(name, index, variant)?;
        Ok(self)
    }

    fn serialize_map(self, _: Option<usize>) -> Result<Self::SerializeMap> {
        unimplemented!()
    }

    fn serialize_struct(self, _: &'static str, _: usize) -> Result<Self::SerializeStruct> {
        unimplemented!()
    }

    fn serialize_struct_variant(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self::SerializeStructVariant> {
        unimplemented!()
    }
}

/// Sequences simply concatenate the serialized elements, with no external structure.
impl SerializeSeq for &mut Serializer {
    type Ok = ();
    type Error = Error;

    fn serialize_element<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<()> {
        value.serialize(&mut **self)
    }

    fn end(self) -> Result<()> {
        Ok(())
    }
}

/// Tuples, like sequences, simply concatenate the serialized elements.
impl SerializeTuple for &mut Serializer {
    type Ok = ();
    type Error = Error;

    fn serialize_element<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<()> {
        value.serialize(&mut **self)
    }

    fn end(self) -> Result<()> {
        Ok(())
    }
}

/// Tuples, like sequences, simply concatenate the serialized elements.
impl SerializeTupleVariant for &mut Serializer {
    type Ok = ();
    type Error = Error;

    fn serialize_field<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<()> {
        value.serialize(&mut **self)
    }

    fn end(self) -> Result<()> {
        Ok(())
    }
}

/// Deserializes keys from byte slices into a given type. The format is not
/// self-describing, so the caller must provide a concrete type to deserialize
/// into.
pub struct Deserializer<'de> {
    input: &'de [u8],
}

impl<'de> Deserializer<'de> {
    /// Creates a deserializer for a byte slice.
    pub fn from_bytes(input: &'de [u8]) -> Self {
        Deserializer { input }
    }

    /// Chops off and returns the next len bytes of the byte slice, or errors if
    /// there aren't enough bytes left.
    fn take_bytes(&mut self, len: usize) -> Result<&[u8]> {
        if self.input.len() < len {
            return errdata!("insufficient bytes, expected {len} bytes for {:x?}", self.input);
        }
        let bytes = &self.input[..len];
        self.input = &self.input[len..];
        Ok(bytes)
    }

    /// Decodes and chops off the next encoded byte slice.
    ///
    /// The parse itself is delegated to `decode_bytes`, the Verus-verified core
    /// proven to compute `bytes_dec` (see the `verus!` block above); this
    /// wrapper just advances `self.input` and maps the two malformed-input
    /// cases to the diagnostics this function has always reported.
    fn decode_next_bytes(&mut self) -> Result<Vec<u8>> {
        match decode_bytes(self.input) {
            DecodeBytes::Decoded(decoded, taken) => {
                self.input = &self.input[taken..];
                Ok(decoded)
            }
            DecodeBytes::InvalidEscape => errdata!("invalid escape sequence"),
            DecodeBytes::UnexpectedEnd => errdata!("unexpected end of input"),
        }
    }
}

/// For details on serialization formats, see Serializer.
impl<'de> serde::de::Deserializer<'de> for &mut Deserializer<'de> {
    type Error = Error;

    fn deserialize_any<V: Visitor<'de>>(self, _: V) -> Result<V::Value> {
        panic!("must provide type, Keycode is not self-describing")
    }

    fn deserialize_bool<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_bool(match self.take_bytes(1)?[0] {
            0x00 => false,
            0x01 => true,
            b => return errdata!("invalid boolean value {b}"),
        })
    }

    fn deserialize_i8<V: Visitor<'de>>(self, _: V) -> Result<V::Value> {
        unimplemented!()
    }

    fn deserialize_i16<V: Visitor<'de>>(self, _: V) -> Result<V::Value> {
        unimplemented!()
    }

    fn deserialize_i32<V: Visitor<'de>>(self, _: V) -> Result<V::Value> {
        unimplemented!()
    }

    fn deserialize_i64<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        // Verified decoder, the inverse of `serialize_i64`.
        let key = u64::from_be_bytes(self.take_bytes(8)?.try_into()?);
        visitor.visit_i64(decode_i64_key(key))
    }

    fn deserialize_u8<V: Visitor<'de>>(self, _: V) -> Result<V::Value> {
        unimplemented!()
    }

    fn deserialize_u16<V: Visitor<'de>>(self, _: V) -> Result<V::Value> {
        unimplemented!()
    }

    fn deserialize_u32<V: Visitor<'de>>(self, _: V) -> Result<V::Value> {
        unimplemented!()
    }

    fn deserialize_u64<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_u64(u64::from_be_bytes(self.take_bytes(8)?.try_into()?))
    }

    fn deserialize_f32<V: Visitor<'de>>(self, _: V) -> Result<V::Value> {
        unimplemented!()
    }

    fn deserialize_f64<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        // Verified decoder, the inverse of `serialize_f64`.
        let key = u64::from_be_bytes(self.take_bytes(8)?.try_into()?);
        visitor.visit_f64(f64::from_bits(decode_f64_key(key)))
    }

    fn deserialize_char<V: Visitor<'de>>(self, _: V) -> Result<V::Value> {
        unimplemented!()
    }

    fn deserialize_str<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        let bytes = self.decode_next_bytes()?;
        visitor.visit_str(&String::from_utf8(bytes)?)
    }

    fn deserialize_string<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        let bytes = self.decode_next_bytes()?;
        visitor.visit_string(String::from_utf8(bytes)?)
    }

    fn deserialize_bytes<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        let bytes = self.decode_next_bytes()?;
        visitor.visit_bytes(&bytes)
    }

    fn deserialize_byte_buf<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        let bytes = self.decode_next_bytes()?;
        visitor.visit_byte_buf(bytes)
    }

    fn deserialize_option<V: Visitor<'de>>(self, _: V) -> Result<V::Value> {
        unimplemented!()
    }

    fn deserialize_unit<V: Visitor<'de>>(self, _: V) -> Result<V::Value> {
        unimplemented!()
    }

    fn deserialize_unit_struct<V: Visitor<'de>>(self, _: &'static str, _: V) -> Result<V::Value> {
        unimplemented!()
    }

    fn deserialize_newtype_struct<V: Visitor<'de>>(
        self,
        _: &'static str,
        _: V,
    ) -> Result<V::Value> {
        unimplemented!()
    }

    fn deserialize_seq<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_seq(self)
    }

    fn deserialize_tuple<V: Visitor<'de>>(self, _: usize, visitor: V) -> Result<V::Value> {
        visitor.visit_seq(self)
    }

    fn deserialize_tuple_struct<V: Visitor<'de>>(
        self,
        _: &'static str,
        _: usize,
        _: V,
    ) -> Result<V::Value> {
        unimplemented!()
    }

    fn deserialize_map<V: Visitor<'de>>(self, _: V) -> Result<V::Value> {
        unimplemented!()
    }

    fn deserialize_struct<V: Visitor<'de>>(
        self,
        _: &'static str,
        _: &'static [&'static str],
        _: V,
    ) -> Result<V::Value> {
        unimplemented!()
    }

    fn deserialize_enum<V: Visitor<'de>>(
        self,
        _: &'static str,
        _: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value> {
        visitor.visit_enum(self)
    }

    fn deserialize_identifier<V: Visitor<'de>>(self, _: V) -> Result<V::Value> {
        unimplemented!()
    }

    fn deserialize_ignored_any<V: Visitor<'de>>(self, _: V) -> Result<V::Value> {
        unimplemented!()
    }
}

/// Sequences are simply deserialized until the byte slice is exhausted.
impl<'de> SeqAccess<'de> for Deserializer<'de> {
    type Error = Error;

    fn next_element_seed<T: DeserializeSeed<'de>>(&mut self, seed: T) -> Result<Option<T::Value>> {
        if self.input.is_empty() {
            return Ok(None);
        }
        seed.deserialize(self).map(Some)
    }
}

/// Enum variants are deserialized by their index.
impl<'de> EnumAccess<'de> for &mut Deserializer<'de> {
    type Error = Error;
    type Variant = Self;

    fn variant_seed<V: DeserializeSeed<'de>>(self, seed: V) -> Result<(V::Value, Self::Variant)> {
        let index = self.take_bytes(1)?[0] as u32;
        let value: Result<_> = seed.deserialize(index.into_deserializer());
        Ok((value?, self))
    }
}

/// Enum variant contents are deserialized as sequences.
impl<'de> VariantAccess<'de> for &mut Deserializer<'de> {
    type Error = Error;

    fn unit_variant(self) -> Result<()> {
        Ok(())
    }

    fn newtype_variant_seed<T: DeserializeSeed<'de>>(self, seed: T) -> Result<T::Value> {
        seed.deserialize(&mut *self)
    }

    fn tuple_variant<V: Visitor<'de>>(self, _: usize, visitor: V) -> Result<V::Value> {
        visitor.visit_seq(self)
    }

    fn struct_variant<V: Visitor<'de>>(self, _: &'static [&'static str], _: V) -> Result<V::Value> {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;
    use std::f64::consts::PI;

    use paste::paste;
    use serde::{Deserialize, Serialize};
    use serde_bytes::ByteBuf;

    use super::*;
    use crate::sql::types::Value;

    #[derive(Debug, Deserialize, Serialize, PartialEq)]
    enum Key<'a> {
        Unit,
        NewType(String),
        Tuple(bool, #[serde(with = "serde_bytes")] Vec<u8>, u64),
        Cow(
            #[serde(with = "serde_bytes")]
            #[serde(borrow)]
            Cow<'a, [u8]>,
            bool,
            #[serde(borrow)] Cow<'a, str>,
        ),
    }

    /// Assert that serializing a value yields the expected byte sequence (as a
    /// hex-encoded string), and that deserializing it yields the original value.
    macro_rules! test_serialize_deserialize {
        ( $( $name:ident: $input:expr => $expect:literal, )* ) => {
        $(
            #[test]
            fn $name() -> Result<()> {
                let mut input = $input;
                let expect = $expect;
                let output = serialize(&input);
                assert_eq!(hex::encode(&output), expect, "encode failed");

                let expect = input;
                input = deserialize(&output)?; // reuse input variable for proper type
                assert_eq!(input, expect, "decode failed");
                Ok(())
            }
        )*
        };
    }

    /// Assert that deserializing invalid inputs results in errors. Takes byte
    /// slices (as hex-encoded strings) and the type to deserialize into.
    macro_rules! test_deserialize_error {
        ( $( $name:ident: $input:literal as $type:ty, )* ) => {
        paste! {
        $(
            #[test]
            #[should_panic]
            fn [< $name _deserialize_error >]() {
                let bytes = hex::decode($input).unwrap();
                deserialize::<$type>(&bytes).unwrap();
            }
        )*
        }
        };
    }

    // Assert that serializing a value results in an error.
    macro_rules! test_serialize_error {
        ( $( $name:ident: $input:expr, )* ) => {
        paste! {
        $(
            #[test]
            #[should_panic]
            fn [< $name _serialize_error >]() {
                let input = $input;
                serialize(&input);
            }
        )*
        }
        };
    }

    test_serialize_deserialize! {
        bool_false: false => "00",
        bool_true: true => "01",

        f64_min: f64::MIN => "0010000000000000",
        f64_neg_inf: f64::NEG_INFINITY => "000fffffffffffff",
        f64_neg_pi: -PI => "3ff6de04abbbd2e7",
        f64_neg_zero: -0f64 => "7fffffffffffffff",
        f64_zero: 0f64 => "8000000000000000",
        f64_pi: PI => "c00921fb54442d18",
        f64_max: f64::MAX => "ffefffffffffffff",
        f64_inf: f64::INFINITY => "fff0000000000000",
        // We don't test NAN here, since NAN != NAN.

        i64_min: i64::MIN => "0000000000000000",
        i64_neg_65535: -65535i64 => "7fffffffffff0001",
        i64_neg_1: -1i64 => "7fffffffffffffff",
        i64_0: 0i64 => "8000000000000000",
        i64_1: 1i64 => "8000000000000001",
        i64_65535: 65535i64 => "800000000000ffff",
        i64_max: i64::MAX => "ffffffffffffffff",

        u64_min: u64::MIN => "0000000000000000",
        u64_1: 1_u64 => "0000000000000001",
        u64_65535: 65535_u64 => "000000000000ffff",
        u64_max: u64::MAX => "ffffffffffffffff",

        bytes: ByteBuf::from(vec![0x01, 0xff]) => "01ff0000",
        bytes_empty: ByteBuf::new() => "0000",
        bytes_escape: ByteBuf::from(vec![0x00, 0x01, 0x02]) => "00ff01020000",

        string: "foo".to_string() => "666f6f0000",
        string_empty: "".to_string() => "0000",
        string_escape: "foo\x00bar".to_string() => "666f6f00ff6261720000",
        string_utf8: "👋".to_string() => "f09f918b0000",

        tuple: (true, u64::MAX, ByteBuf::from(vec![0x00, 0x01])) => "01ffffffffffffffff00ff010000",
        array_bool: [false, true, false] => "000100",
        vec_bool: vec![false, true, false] => "000100",
        vec_u64: vec![u64::MIN, u64::MAX, 65535_u64] => "0000000000000000ffffffffffffffff000000000000ffff",

        enum_unit: Key::Unit => "00",
        enum_newtype: Key::NewType("foo".to_string()) => "01666f6f0000",
        enum_tuple: Key::Tuple(false, vec![0x00, 0x01], u64::MAX) => "020000ff010000ffffffffffffffff",
        enum_cow: Key::Cow(vec![0x00, 0x01].into(), false, String::from("foo").into()) => "0300ff01000000666f6f0000",
        enum_cow_borrow: Key::Cow([0x00, 0x01].as_slice().into(), false, "foo".into()) => "0300ff01000000666f6f0000",

        value_null: Value::Null => "00",
        value_bool: Value::Boolean(true) => "0101",
        value_int: Value::Integer(-1) => "027fffffffffffffff",
        value_float: Value::Float(PI) => "03c00921fb54442d18",
        value_string: Value::String("foo".to_string()) => "04666f6f0000",
    }

    test_serialize_error! {
        char: 'a',
        f32: 0f32,
        i8: 0i8,
        i16: 0i16,
        i32: 0i32,
        i128: 0i128,
        u8: 0u8,
        u16: 0u16,
        u32: 0u32,
        u128: 0u128,
        some: Some(true),
        none: Option::<bool>::None,
        vec_u8: vec![0u8],
    }

    test_deserialize_error! {
        bool_empty: "" as bool,
        bool_2: "02" as bool,
        char: "61" as char,
        f32: "00000000" as f32,
        i8: "00" as i8,
        i16: "0000" as i16,
        i32: "00000000" as i32,
        i128: "00000000000000000000000000000000" as i128,
        u16: "0000" as u16,
        u32: "00000000" as u32,
        u64_partial: "0000" as u64,
        u128: "00000000000000000000000000000000" as u128,
        option: "00" as Option::<bool>,
        string_utf8_invalid: "c0" as String,
        tuple_partial: "0001" as (bool, bool, bool),
        vec_u8: "0000" as Vec<u8>,
    }
}
