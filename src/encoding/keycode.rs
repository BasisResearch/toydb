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

use itertools::Either;
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

/// Generates a key range for a key prefix, used e.g. for prefix scans.
///
/// The exclusive end bound is generated by adding 1 to the value of the last
/// byte. If the last byte(s) is 0xff (so adding 1 would overflow), we instead
/// find the latest non-0xff byte, increment that, and truncate the rest. If all
/// bytes are 0xff, we scan to the end of the range, since there can't be other
/// prefixes after it.
pub fn prefix_range(prefix: &[u8]) -> (Bound<Vec<u8>>, Bound<Vec<u8>>) {
    let start = Bound::Included(prefix.to_vec());
    let end = match prefix.iter().rposition(|&b| b != 0xff) {
        Some(i) => Bound::Excluded(
            prefix.iter().take(i).copied().chain(std::iter::once(prefix[i] + 1)).collect(),
        ),
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
        let bytes = v
            .iter()
            .flat_map(|&byte| match byte {
                0x00 => Either::Left([0x00, 0xff].into_iter()),
                byte => Either::Right([byte].into_iter()),
            })
            .chain([0x00, 0x00]);
        self.output.extend(bytes);
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
    fn decode_next_bytes(&mut self) -> Result<Vec<u8>> {
        let mut decoded = Vec::new();
        let mut iter = self.input.iter().enumerate();
        let taken = loop {
            match iter.next() {
                Some((_, 0x00)) => match iter.next() {
                    Some((i, 0x00)) => break i + 1,        // terminator
                    Some((_, 0xff)) => decoded.push(0x00), // escaped 0x00
                    _ => return errdata!("invalid escape sequence"),
                },
                Some((_, b)) => decoded.push(*b),
                None => return errdata!("unexpected end of input"),
            }
        };
        self.input = &self.input[taken..];
        Ok(decoded)
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
