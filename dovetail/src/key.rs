//! Exact content-derived keys for e-node deduplication and N-best tiebreaking.
//!
//! The deduplication key for an e-node MUST be an exact content byte-stream, NOT
//! a 64-bit hash. A 64-bit-hash dedup is proven unsound in this project
//! (`hash_only_pair_dedup_can_drop_distinct_keys`): two observationally-distinct
//! terms can collide on the same 64-bit value, and one would be silently
//! dropped — losing a valid alternative, which the engine forbids.
//!
//! [`ContentKey`] is the exact byte-stream. Equality is byte equality (so
//! distinct content *always* yields distinct keys — no collisions), and its
//! total [`Ord`] gives the content-derived tiebreak the N-best extractor uses to
//! keep equal-weight distinct alternatives both alive, in a deterministic order.

use std::fmt;

/// Write a length-framed byte segment: a `u64`-LE length prefix followed by the
/// bytes. Framing makes concatenations unambiguous — `[b"ab", b"c"]` and
/// `[b"a", b"bc"]` produce different streams despite the same concatenation —
/// which is required for [`SemanticHash`] to be injective over composites.
#[inline]
pub fn write_framed(out: &mut Vec<u8>, segment: &[u8]) {
    out.extend_from_slice(&(segment.len() as u64).to_le_bytes());
    out.extend_from_slice(segment);
}

/// Write an order-preserving, prefix-free byte segment.
///
/// This is used for derivation-tree tiebreak keys. Unlike [`write_framed`], the
/// payload bytes are compared before the segment terminator, so lexicographic
/// order of child keys is preserved when child keys are embedded in parent keys.
/// Each payload byte is encoded as `0x01, byte`; the segment terminator is
/// `0x00`. Because no payload element begins with `0x00`, the encoding is
/// prefix-free, and because every payload element begins with the same marker,
/// bytewise payload order is preserved.
#[inline]
pub fn write_ordered_framed(out: &mut Vec<u8>, segment: &[u8]) {
    for &byte in segment {
        out.push(1);
        out.push(byte);
    }
    out.push(0);
}

/// An exact, content-derived key: the canonical byte serialization of a value.
///
/// Equality and ordering are over the exact bytes, so distinct content always
/// yields distinct keys (collision-free, unlike a 64-bit hash). [`Ord`] provides
/// the total tiebreak the N-best extractor relies on to keep equal-weight
/// distinct alternatives both alive in a deterministic order.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ContentKey(Box<[u8]>);

impl ContentKey {
    /// Wrap an exact byte buffer as a key.
    #[inline]
    pub fn from_bytes(bytes: Vec<u8>) -> Self {
        ContentKey(bytes.into_boxed_slice())
    }

    /// The exact key bytes (the identity of the key).
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Number of key bytes.
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Whether the key is empty (zero content bytes).
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl fmt::Debug for ContentKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Hex rendering for compactness; the exact bytes are the identity.
        write!(f, "ContentKey(")?;
        for b in self.0.iter() {
            write!(f, "{:02x}", b)?;
        }
        write!(f, ")")
    }
}

/// A value that can serialize its canonical content into an exact byte buffer.
///
/// Mirrors the macro-generated `semantic_hash` write-stream, but writes into an
/// exact `Vec<u8>` rather than a 64-bit `Hasher` — so the resulting
/// [`ContentKey`] is collision-free.
///
/// ## Contract
///
/// # Safety
///
/// `write_content` must be **injective up to observational equivalence**: two
/// values write the same bytes **iff** they are observationally equal. It must
/// also agree with `Eq`/`Hash`: values that compare equal must write identical
/// bytes. Composite implementors MUST length-frame their parts (see
/// [`write_framed`]) so that distinct structural decompositions cannot alias.
pub unsafe trait SemanticHash {
    /// Append this value's canonical content bytes to `out`.
    fn write_content(&self, out: &mut Vec<u8>);

    /// Materialize the exact [`ContentKey`] for this value.
    #[inline]
    fn content_key(&self) -> ContentKey {
        let mut out = Vec::new();
        self.write_content(&mut out);
        ContentKey::from_bytes(out)
    }
}

// --- Primitive implementations ---------------------------------------------
//
// Fixed-width integers serialize as little-endian bytes (fixed size ⇒ no
// framing needed). `bool` is a single discriminant byte. Variable-length types
// (`str`, byte slices) are length-framed.

macro_rules! impl_semantic_hash_le {
    ($($t:ty),* $(,)?) => {$(
        unsafe impl SemanticHash for $t {
            #[inline]
            fn write_content(&self, out: &mut Vec<u8>) {
                out.extend_from_slice(&self.to_le_bytes());
            }
        }
    )*};
}
impl_semantic_hash_le!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

unsafe impl SemanticHash for bool {
    #[inline]
    fn write_content(&self, out: &mut Vec<u8>) {
        out.push(*self as u8);
    }
}

unsafe impl SemanticHash for str {
    #[inline]
    fn write_content(&self, out: &mut Vec<u8>) {
        write_framed(out, self.as_bytes());
    }
}

unsafe impl SemanticHash for String {
    #[inline]
    fn write_content(&self, out: &mut Vec<u8>) {
        write_framed(out, self.as_bytes());
    }
}

unsafe impl SemanticHash for [u8] {
    #[inline]
    fn write_content(&self, out: &mut Vec<u8>) {
        write_framed(out, self);
    }
}

unsafe impl<T: SemanticHash + ?Sized> SemanticHash for &T {
    #[inline]
    fn write_content(&self, out: &mut Vec<u8>) {
        (**self).write_content(out);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    #[test]
    fn content_key_is_deterministic() {
        assert_eq!("hello".content_key(), "hello".content_key());
        assert_eq!(42u64.content_key(), 42u64.content_key());
    }

    #[test]
    fn distinct_values_yield_distinct_keys() {
        assert_ne!("hello".content_key(), "world".content_key());
        assert_ne!(3u64.content_key(), 4u64.content_key());
        assert_ne!(true.content_key(), false.content_key());
    }

    #[test]
    fn framing_prevents_concatenation_collision() {
        // ("ab","c") vs ("a","bc"): same concatenation, but framing must
        // disambiguate them — the structural decomposition is part of identity.
        let mut k1 = Vec::new();
        write_framed(&mut k1, b"ab");
        write_framed(&mut k1, b"c");
        let mut k2 = Vec::new();
        write_framed(&mut k2, b"a");
        write_framed(&mut k2, b"bc");
        assert_ne!(ContentKey::from_bytes(k1), ContentKey::from_bytes(k2));
    }

    #[test]
    fn ordered_framing_preserves_segment_order() {
        let segments: [&[u8]; 7] = [b"", b"\0", b"\0\0", b"\0a", b"a", b"a\0", b"aa"];

        for left in segments {
            for right in segments {
                let mut left_encoded = Vec::new();
                let mut right_encoded = Vec::new();
                write_ordered_framed(&mut left_encoded, left);
                write_ordered_framed(&mut right_encoded, right);

                assert_eq!(
                    left.cmp(right),
                    left_encoded.cmp(&right_encoded),
                    "ordered framing must preserve segment order for {left:?} vs {right:?}"
                );
            }
        }
    }

    #[test]
    fn ordered_framing_prevents_prefix_collision() {
        let mut k1 = Vec::new();
        write_ordered_framed(&mut k1, b"ab");
        write_ordered_framed(&mut k1, b"c");

        let mut k2 = Vec::new();
        write_ordered_framed(&mut k2, b"a");
        write_ordered_framed(&mut k2, b"bc");

        assert_ne!(ContentKey::from_bytes(k1), ContentKey::from_bytes(k2));
    }

    #[test]
    fn ord_is_a_total_content_order() {
        let mut keys = vec!["b".content_key(), "a".content_key(), "c".content_key()];
        keys.sort();
        assert_eq!(keys, vec!["a".content_key(), "b".content_key(), "c".content_key()]);
    }

    #[test]
    fn distinct_keys_are_never_collapsed_in_a_set() {
        // Rust-level analogue of `exact_key_pair_dedup_preserves_distinct_keys`:
        // exact-key dedup keeps every distinct key; only true repeats merge.
        let mut s = BTreeSet::new();
        s.insert("x".content_key());
        s.insert("y".content_key());
        s.insert("x".content_key()); // exact repeat of the first
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn key_roundtrips_through_bytes() {
        let k = "roundtrip".content_key();
        let k2 = ContentKey::from_bytes(k.as_bytes().to_vec());
        assert_eq!(k, k2);
        assert!(!k.is_empty());
        assert_eq!(k.len(), k.as_bytes().len());
    }
}
