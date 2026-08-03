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

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, OnceLock};

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

const FINGERPRINT_BASE: u128 = 0x0000_0001_0000_01b3;

enum ContentKeyKind {
    Flat(Box<[u8]>),
    Tree {
        header: Box<[u8]>,
        children: Box<[ContentKey]>,
    },
}

struct ContentKeyInner {
    kind: ContentKeyKind,
    len: usize,
    fingerprint: u128,
    flattened: OnceLock<Box<[u8]>>,
}

/// An exact, content-derived key with persistent structural sharing.
///
/// Equality and ordering remain byte-exact. Tree keys retain their children as
/// shared nodes and materialize the canonical byte stream only when
/// [`ContentKey::as_bytes`] is requested. This makes parent-key construction
/// proportional to the node's arity instead of copying and re-escaping the
/// complete key of every descendant at every level.
#[derive(Clone)]
pub struct ContentKey(Option<Arc<ContentKeyInner>>);

enum ByteFrame<'a> {
    Key(&'a ContentKey),
    Slice { bytes: &'a [u8], index: usize },
}

struct ContentKeyBytes<'a> {
    stack: Vec<ByteFrame<'a>>,
}

impl<'a> ContentKeyBytes<'a> {
    fn new(key: &'a ContentKey) -> Self {
        ContentKeyBytes { stack: vec![ByteFrame::Key(key)] }
    }
}

impl Iterator for ContentKeyBytes<'_> {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(frame) = self.stack.pop() {
            match frame {
                ByteFrame::Key(key) => match &key.inner().kind {
                    ContentKeyKind::Flat(bytes) => {
                        self.stack.push(ByteFrame::Slice { bytes, index: 0 });
                    },
                    ContentKeyKind::Tree { header, children } => {
                        for child in children.iter().rev() {
                            self.stack.push(ByteFrame::Key(child));
                        }
                        self.stack
                            .push(ByteFrame::Slice { bytes: header, index: 0 });
                    },
                },
                ByteFrame::Slice { bytes, index } if index < bytes.len() => {
                    self.stack
                        .push(ByteFrame::Slice { bytes, index: index + 1 });
                    return Some(bytes[index]);
                },
                ByteFrame::Slice { .. } => {},
            }
        }
        None
    }
}

fn fingerprint_bytes(bytes: &[u8]) -> u128 {
    bytes.iter().fold(0u128, |state, byte| {
        state
            .wrapping_mul(FINGERPRINT_BASE)
            .wrapping_add(u128::from(*byte) + 1)
    })
}

fn wrapping_pow(mut base: u128, mut exponent: usize) -> u128 {
    let mut result = 1u128;
    while exponent != 0 {
        if exponent & 1 == 1 {
            result = result.wrapping_mul(base);
        }
        base = base.wrapping_mul(base);
        exponent >>= 1;
    }
    result
}

fn concatenate_fingerprint(prefix: u128, suffix: u128, suffix_len: usize) -> u128 {
    prefix
        .wrapping_mul(wrapping_pow(FINGERPRINT_BASE, suffix_len))
        .wrapping_add(suffix)
}

impl ContentKey {
    /// Wrap an exact byte buffer as a key.
    #[inline]
    pub fn from_bytes(bytes: Vec<u8>) -> Self {
        let len = bytes.len();
        let fingerprint = fingerprint_bytes(&bytes);
        ContentKey(Some(Arc::new(ContentKeyInner {
            kind: ContentKeyKind::Flat(bytes.into_boxed_slice()),
            len,
            fingerprint,
            flattened: OnceLock::new(),
        })))
    }

    /// Build the exact prefix-coded key of one derivation node. The operator is
    /// order-preserving framed once, the fixed-width arity makes the recursive
    /// grammar self-delimiting, and child keys are structurally shared.
    pub(crate) fn tree<L: SemanticHash>(op: &L, children: Vec<ContentKey>) -> Self {
        let mut op_bytes = Vec::new();
        op.write_content(&mut op_bytes);
        let mut header = Vec::with_capacity(op_bytes.len().saturating_mul(2).saturating_add(9));
        write_ordered_framed(&mut header, &op_bytes);
        header.extend_from_slice(&(children.len() as u64).to_be_bytes());

        let mut len = header.len();
        let mut fingerprint = fingerprint_bytes(&header);
        for child in &children {
            len = len
                .checked_add(child.len())
                .expect("content key length overflow");
            fingerprint =
                concatenate_fingerprint(fingerprint, child.inner().fingerprint, child.len());
        }
        ContentKey(Some(Arc::new(ContentKeyInner {
            kind: ContentKeyKind::Tree {
                header: header.into_boxed_slice(),
                children: children.into_boxed_slice(),
            },
            len,
            fingerprint,
            flattened: OnceLock::new(),
        })))
    }

    /// The exact key bytes (the identity of the key).
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        match &self.inner().kind {
            ContentKeyKind::Flat(bytes) => bytes,
            ContentKeyKind::Tree { .. } => self
                .inner()
                .flattened
                .get_or_init(|| {
                    let mut bytes = Vec::with_capacity(self.len());
                    bytes.extend(self.bytes());
                    bytes.into_boxed_slice()
                })
                .as_ref(),
        }
    }

    /// Number of key bytes.
    #[inline]
    pub fn len(&self) -> usize {
        self.inner().len
    }

    /// Whether the key is empty (zero content bytes).
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner().len == 0
    }

    fn bytes(&self) -> ContentKeyBytes<'_> {
        ContentKeyBytes::new(self)
    }

    fn inner(&self) -> &ContentKeyInner {
        self.0
            .as_deref()
            .expect("live content key must retain its shared node")
    }
}

impl PartialEq for ContentKey {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(self.0.as_ref().expect("live key"), other.0.as_ref().expect("live key"))
            || (self.inner().len == other.inner().len
                && self.inner().fingerprint == other.inner().fingerprint
                && self.bytes().eq(other.bytes()))
    }
}

impl Eq for ContentKey {}

impl Hash for ContentKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.inner().len);
        state.write_u128(self.inner().fingerprint);
    }
}

impl Ord for ContentKey {
    fn cmp(&self, other: &Self) -> Ordering {
        if Arc::ptr_eq(self.0.as_ref().expect("live key"), other.0.as_ref().expect("live key")) {
            Ordering::Equal
        } else {
            self.bytes().cmp(other.bytes())
        }
    }
}

impl PartialOrd for ContentKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Drop for ContentKey {
    fn drop(&mut self) {
        let Some(root) = self.0.take() else {
            return;
        };
        let mut pending = vec![root];
        while let Some(node) = pending.pop() {
            let Ok(mut inner) = Arc::try_unwrap(node) else {
                continue;
            };
            let kind = std::mem::replace(&mut inner.kind, ContentKeyKind::Flat(Box::new([])));
            if let ContentKeyKind::Tree { children, .. } = kind {
                for mut child in Vec::from(children) {
                    if let Some(child_node) = child.0.take() {
                        pending.push(child_node);
                    }
                }
            }
        }
    }
}

impl fmt::Debug for ContentKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Hex rendering for compactness; the exact bytes are the identity.
        write!(f, "ContentKey(")?;
        for b in self.bytes() {
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

    #[test]
    fn tree_key_flattening_is_exact_and_hash_compatible() {
        use std::collections::HashSet;

        let left = ContentKey::tree(&"left", Vec::new());
        let right = ContentKey::tree(&"right", Vec::new());
        let tree = ContentKey::tree(&"pair", vec![left, right]);
        let flat = ContentKey::from_bytes(tree.as_bytes().to_vec());

        assert_eq!(tree, flat);
        let mut keys = HashSet::new();
        keys.insert(tree);
        keys.insert(flat);
        assert_eq!(keys.len(), 1);
    }

    #[test]
    fn tree_key_growth_is_linear_under_deep_nesting() {
        let leaf = ContentKey::tree(&0u8, Vec::new());
        let one_level = ContentKey::tree(&1u8, vec![leaf.clone(), leaf.clone()]);
        let bytes_per_level = one_level.len() - leaf.len() * 2;
        let depth = 16_384usize;
        let mut key = leaf.clone();
        for _ in 0..depth {
            key = ContentKey::tree(&1u8, vec![key, leaf.clone()]);
        }

        assert_eq!(key.len(), leaf.len() * (depth + 1) + bytes_per_level * depth);
        assert!(key.inner().flattened.get().is_none());
    }

    #[test]
    fn tree_key_order_tracks_the_first_differing_child() {
        let a = ContentKey::tree(&"a", Vec::new());
        let b = ContentKey::tree(&"b", Vec::new());
        let left = ContentKey::tree(&"pair", vec![a.clone(), b.clone()]);
        let right = ContentKey::tree(&"pair", vec![b, a]);
        assert_eq!(left.cmp(&right), left.as_bytes().cmp(right.as_bytes()));
        assert_eq!(left.cmp(&right), Ordering::Less);
    }
}
