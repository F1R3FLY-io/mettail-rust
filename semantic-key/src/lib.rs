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

use rustc_hash::FxHashMap as HashMap;
use std::any::{Any, TypeId};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, OnceLock};

/// Process-local identity of one live immutable node allocation.
///
/// The type component prevents equal addresses in distinct generated
/// categories from aliasing. This value is only a cache index; exact
/// ContentKey equality remains semantic identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ContentKeyNodeIdentity {
    type_id: TypeId,
    address: usize,
}

impl ContentKeyNodeIdentity {
    pub fn of_arc<T: Any + Send + Sync>(owner: &Arc<T>) -> Self {
        Self {
            type_id: TypeId::of::<T>(),
            address: Arc::as_ptr(owner).cast::<()>() as usize,
        }
    }

    pub fn of_ref<T: Any + Send + Sync>(node: &T) -> Self {
        Self {
            type_id: TypeId::of::<T>(),
            address: std::ptr::from_ref(node).cast::<()>() as usize,
        }
    }
}

struct CachedNode {
    // Keeping the allocation alive makes its address a stable identity for the
    // complete cache lifetime and prevents allocator-address reuse.
    _owner: Option<Arc<dyn Any + Send + Sync>>,
    key: ContentKey,
}

/// Failure to stage or atomically commit a semantic-key cache transaction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContentKeyCacheError {
    /// One live immutable allocation was assigned two different exact keys.
    /// This is a generator/codec contract violation, never a hash collision.
    IdentityConflict,
    /// A generated traversal failed to produce exactly one balanced root key.
    ConstructionInvariant,
    /// Publishing the complete transaction would exceed the configured number
    /// of retained node witnesses. No staged entry is published on failure.
    ResourceExhausted { limit: usize, requested: usize },
    /// One exact semantic stream would exceed the configured logical byte
    /// bound. Persistent sharing does not weaken this bound: it is measured on
    /// the complete flattened stream that defines semantic identity.
    KeyBytesExhausted { limit: usize, requested: usize },
}

impl fmt::Display for ContentKeyCacheError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IdentityConflict => {
                formatter.write_str("one immutable node produced conflicting semantic keys")
            },
            Self::ConstructionInvariant => {
                formatter.write_str("semantic-key construction did not produce one balanced root")
            },
            Self::ResourceExhausted { limit, requested } => write!(
                formatter,
                "semantic-key cache entry limit {limit} exceeded (requested {requested})",
            ),
            Self::KeyBytesExhausted { limit, requested } => write!(
                formatter,
                "semantic-key logical byte limit {limit} exceeded (requested {requested})",
            ),
        }
    }
}

impl std::error::Error for ContentKeyCacheError {}

/// Session-scoped cache of persistent exact keys by immutable allocation.
///
/// The cache retains either the indexed allocation itself or an immutable root
/// that transitively owns every indexed descendant, preventing allocator reuse
/// from turning pointer identity into a stale cache hit.
/// Construction uses [`ContentKeyCacheTransaction`], so resource exhaustion
/// cannot publish a proper subset of one root's node keys.
pub struct ContentKeyCache {
    entries: HashMap<ContentKeyNodeIdentity, CachedNode>,
    retained_roots: Vec<Arc<dyn Any + Send + Sync>>,
    max_entries: usize,
    max_key_bytes: usize,
}

impl Default for ContentKeyCache {
    fn default() -> Self {
        Self::with_max_entries(usize::MAX)
    }
}

impl ContentKeyCache {
    pub fn with_max_entries(max_entries: usize) -> Self {
        Self::with_limits(max_entries, usize::MAX)
    }

    /// Construct a cache with independent retained-node and logical-key-byte
    /// limits. Both limits are checked before a transaction is published.
    pub fn with_limits(max_entries: usize, max_key_bytes: usize) -> Self {
        Self {
            entries: HashMap::default(),
            retained_roots: Vec::new(),
            max_entries,
            max_key_bytes,
        }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn max_entries(&self) -> usize {
        self.max_entries
    }

    pub fn max_key_bytes(&self) -> usize {
        self.max_key_bytes
    }

    pub fn transaction(&mut self) -> ContentKeyCacheTransaction<'_> {
        ContentKeyCacheTransaction {
            cache: self,
            root_owner: None,
            staged: HashMap::default(),
        }
    }

    /// Begin one atomic traversal transaction over an immutable owned graph.
    ///
    /// The committed cache retains the root owner, so addresses of every
    /// descendant allocation borrowed from that graph remain live until the
    /// cache is dropped.
    pub fn transaction_for_root<T>(&mut self, root_owner: Arc<T>) -> ContentKeyCacheTransaction<'_>
    where
        T: Any + Send + Sync,
    {
        ContentKeyCacheTransaction {
            cache: self,
            root_owner: Some(root_owner),
            staged: HashMap::default(),
        }
    }
}

/// Atomic staging area for all persistent keys discovered while constructing
/// one semantic root.
pub struct ContentKeyCacheTransaction<'a> {
    cache: &'a mut ContentKeyCache,
    root_owner: Option<Arc<dyn Any + Send + Sync>>,
    staged: HashMap<ContentKeyNodeIdentity, CachedNode>,
}

impl ContentKeyCacheTransaction<'_> {
    pub fn max_key_bytes(&self) -> usize {
        self.cache.max_key_bytes
    }

    fn check_key_bytes(&self, key: &ContentKey) -> Result<(), ContentKeyCacheError> {
        if key.len() > self.cache.max_key_bytes {
            Err(ContentKeyCacheError::KeyBytesExhausted {
                limit: self.cache.max_key_bytes,
                requested: key.len(),
            })
        } else {
            Ok(())
        }
    }

    pub fn get<T: Any + Send + Sync>(&self, owner: &Arc<T>) -> Option<ContentKey> {
        let identity = ContentKeyNodeIdentity::of_arc(owner);
        self.staged
            .get(&identity)
            .or_else(|| self.cache.entries.get(&identity))
            .map(|entry| entry.key.clone())
    }

    pub fn stage<T: Any + Send + Sync>(
        &mut self,
        owner: Arc<T>,
        key: ContentKey,
    ) -> Result<ContentKey, ContentKeyCacheError> {
        self.check_key_bytes(&key)?;
        let identity = ContentKeyNodeIdentity::of_arc(&owner);
        if let Some(existing) = self
            .staged
            .get(&identity)
            .or_else(|| self.cache.entries.get(&identity))
        {
            return if existing.key == key {
                Ok(existing.key.clone())
            } else {
                Err(ContentKeyCacheError::IdentityConflict)
            };
        }
        self.staged
            .insert(identity, CachedNode { _owner: Some(owner), key: key.clone() });
        Ok(key)
    }

    /// Look up a node borrowed from the immutable root graph of this
    /// transaction.
    pub fn get_borrowed<T: Any + Send + Sync>(&self, node: &T) -> Option<ContentKey> {
        let identity = ContentKeyNodeIdentity::of_ref(node);
        self.get_identity(identity)
    }

    /// Look up a process-local node identity retained by this cache.
    pub fn get_identity(&self, identity: ContentKeyNodeIdentity) -> Option<ContentKey> {
        self.staged
            .get(&identity)
            .or_else(|| self.cache.entries.get(&identity))
            .map(|entry| entry.key.clone())
    }

    /// Stage a key for a node borrowed from the transaction's retained root.
    ///
    /// # Safety
    ///
    /// The node must be reachable through immutable ownership from the Arc
    /// supplied to ContentKeyCache::transaction_for_root. Generated MeTTaIL AST
    /// traversal satisfies this by visiting only fields of that root and
    /// temporary canonical nodes are deliberately not staged.
    pub unsafe fn stage_borrowed<T: Any + Send + Sync>(
        &mut self,
        node: &T,
        key: ContentKey,
    ) -> Result<ContentKey, ContentKeyCacheError> {
        let identity = ContentKeyNodeIdentity::of_ref(node);
        // SAFETY: forwarded from this method's root-ownership contract.
        unsafe { self.stage_identity(identity, key) }
    }

    /// Stage an exact key under a node identity borrowed from the retained
    /// immutable root.
    ///
    /// # Safety
    ///
    /// The identity must have been derived from a node reachable through
    /// immutable ownership from this transaction's retained root.
    pub unsafe fn stage_identity(
        &mut self,
        identity: ContentKeyNodeIdentity,
        key: ContentKey,
    ) -> Result<ContentKey, ContentKeyCacheError> {
        self.check_key_bytes(&key)?;
        if self.root_owner.is_none() {
            return Err(ContentKeyCacheError::IdentityConflict);
        }
        if let Some(existing) = self
            .staged
            .get(&identity)
            .or_else(|| self.cache.entries.get(&identity))
        {
            return if existing.key == key {
                Ok(existing.key.clone())
            } else {
                Err(ContentKeyCacheError::IdentityConflict)
            };
        }
        self.staged
            .insert(identity, CachedNode { _owner: None, key: key.clone() });
        Ok(key)
    }

    pub fn commit(self) -> Result<usize, ContentKeyCacheError> {
        let requested = self
            .cache
            .entries
            .len()
            .checked_add(self.staged.len())
            .ok_or(ContentKeyCacheError::ResourceExhausted {
                limit: self.cache.max_entries,
                requested: usize::MAX,
            })?;
        if requested > self.cache.max_entries {
            return Err(ContentKeyCacheError::ResourceExhausted {
                limit: self.cache.max_entries,
                requested,
            });
        }
        let added = self.staged.len();
        self.cache.entries.extend(self.staged);
        if added != 0 {
            if let Some(root_owner) = self.root_owner {
                self.cache.retained_roots.push(root_owner);
            }
        }
        Ok(added)
    }
}

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

/// Source-neutral operator whose exact identity uses the same framed encoding
/// as generated MeTTaIL Dovetail operators: one stable `u32` discriminant,
/// followed by zero or more canonical payload segments.
///
/// Reader-facing labels live in the checked projection/report layer rather
/// than this identity object. Keeping them separate makes the `Eq`, `Hash`,
/// [`SemanticHash`], and `Display` observations agree for every constructible
/// value while preserving legacy semantic-key bytes.
#[derive(Clone, Debug)]
pub struct FramedSemanticOperator {
    stable_discriminant: u32,
    payload_segments: Vec<Vec<u8>>,
}

impl FramedSemanticOperator {
    pub fn new(stable_discriminant: u32, payload_segments: Vec<Vec<u8>>) -> Self {
        Self { stable_discriminant, payload_segments }
    }

    pub fn stable_discriminant(&self) -> u32 {
        self.stable_discriminant
    }

    pub fn payload_segments(&self) -> &[Vec<u8>] {
        &self.payload_segments
    }
}

impl PartialEq for FramedSemanticOperator {
    fn eq(&self, other: &Self) -> bool {
        self.stable_discriminant == other.stable_discriminant
            && self.payload_segments == other.payload_segments
    }
}

impl Eq for FramedSemanticOperator {}

impl Hash for FramedSemanticOperator {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.stable_discriminant.hash(state);
        self.payload_segments.hash(state);
    }
}

impl fmt::Display for FramedSemanticOperator {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "op#{}", self.stable_discriminant)
    }
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
    #[doc(hidden)]
    pub fn tree<L: SemanticHash>(op: &L, children: Vec<ContentKey>) -> Self {
        let mut op_bytes = Vec::new();
        op.write_content(&mut op_bytes);
        let mut header = Vec::with_capacity(op_bytes.len().saturating_mul(2).saturating_add(9));
        write_ordered_framed(&mut header, &op_bytes);
        header.extend_from_slice(&(children.len() as u64).to_be_bytes());

        Self::from_parts(header, children)
    }

    /// Concatenate one local exact byte segment with structurally shared child
    /// keys without changing the resulting byte stream.
    ///
    /// Unlike [`Self::tree`], this function adds no framing. It is the neutral
    /// rope operation used when an existing semantic-key ABI already defines
    /// the local bytes and child order. Flattening the result is exactly
    /// `local` followed by each child's bytes in order.
    pub fn concat(local: Vec<u8>, children: Vec<ContentKey>) -> Self {
        Self::from_parts(local, children)
    }

    /// Concatenate exact key fragments without flattening any fragment.
    ///
    /// This is the general rope operation used when local byte writes and
    /// recursively cached child keys are interleaved. The result has exactly
    /// the bytes obtained by flattening each fragment in order.
    pub fn concat_keys(mut fragments: Vec<ContentKey>) -> Self {
        match fragments.len() {
            0 => Self::from_bytes(Vec::new()),
            1 => match fragments.pop() {
                Some(fragment) => fragment,
                None => Self::from_bytes(Vec::new()),
            },
            _ => Self::from_parts(Vec::new(), fragments),
        }
    }

    fn try_concat_keys(
        mut fragments: Vec<ContentKey>,
        max_key_bytes: usize,
    ) -> Result<Self, ContentKeyCacheError> {
        match fragments.len() {
            0 => Ok(Self::from_bytes(Vec::new())),
            1 => match fragments.pop() {
                Some(fragment) if fragment.len() <= max_key_bytes => Ok(fragment),
                Some(fragment) => Err(ContentKeyCacheError::KeyBytesExhausted {
                    limit: max_key_bytes,
                    requested: fragment.len(),
                }),
                None => Ok(Self::from_bytes(Vec::new())),
            },
            _ => Self::try_from_parts(Vec::new(), fragments, max_key_bytes),
        }
    }

    fn try_from_parts(
        header: Vec<u8>,
        children: Vec<ContentKey>,
        max_key_bytes: usize,
    ) -> Result<Self, ContentKeyCacheError> {
        if children.is_empty() {
            return if header.len() <= max_key_bytes {
                Ok(Self::from_bytes(header))
            } else {
                Err(ContentKeyCacheError::KeyBytesExhausted {
                    limit: max_key_bytes,
                    requested: header.len(),
                })
            };
        }

        let mut len = header.len();
        let mut fingerprint = fingerprint_bytes(&header);
        for child in &children {
            len = len
                .checked_add(child.len())
                .ok_or(ContentKeyCacheError::KeyBytesExhausted {
                    limit: max_key_bytes,
                    requested: usize::MAX,
                })?;
            if len > max_key_bytes {
                return Err(ContentKeyCacheError::KeyBytesExhausted {
                    limit: max_key_bytes,
                    requested: len,
                });
            }
            fingerprint =
                concatenate_fingerprint(fingerprint, child.inner().fingerprint, child.len());
        }
        Ok(ContentKey(Some(Arc::new(ContentKeyInner {
            kind: ContentKeyKind::Tree {
                header: header.into_boxed_slice(),
                children: children.into_boxed_slice(),
            },
            len,
            fingerprint,
            flattened: OnceLock::new(),
        }))))
    }

    fn from_parts(header: Vec<u8>, children: Vec<ContentKey>) -> Self {
        if children.is_empty() {
            return Self::from_bytes(header);
        }

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

    fn accelerator(&self) -> ContentKeyAccelerator {
        ContentKeyAccelerator {
            len: self.inner().len,
            fingerprint: self.inner().fingerprint,
        }
    }

    fn inner(&self) -> &ContentKeyInner {
        self.0
            .as_deref()
            .expect("live content key must retain its shared node")
    }
}

/// Stack-safe builder for the generated semantic-fingerprint byte protocol.
///
/// Ordinary Hasher writes are accumulated as local exact bytes. A cached child
/// ContentKey can be spliced between those writes with Self::push_key,
/// preserving the byte stream while retaining structural sharing.
pub struct SemanticKeyBuilder {
    fragments: Vec<ContentKey>,
    local: Vec<u8>,
    logical_bytes: usize,
    max_key_bytes: usize,
    error: Option<ContentKeyCacheError>,
}

impl Default for SemanticKeyBuilder {
    fn default() -> Self {
        Self::with_max_bytes(usize::MAX)
    }
}

impl SemanticKeyBuilder {
    pub fn with_max_bytes(max_key_bytes: usize) -> Self {
        Self {
            fragments: Vec::new(),
            local: Vec::new(),
            logical_bytes: 0,
            max_key_bytes,
            error: None,
        }
    }

    pub fn max_key_bytes(&self) -> usize {
        self.max_key_bytes
    }

    fn reserve_logical(&mut self, additional: usize) -> bool {
        if self.error.is_some() {
            return false;
        }
        let Some(requested) = self.logical_bytes.checked_add(additional) else {
            self.error = Some(ContentKeyCacheError::KeyBytesExhausted {
                limit: self.max_key_bytes,
                requested: usize::MAX,
            });
            return false;
        };
        if requested > self.max_key_bytes {
            self.error = Some(ContentKeyCacheError::KeyBytesExhausted {
                limit: self.max_key_bytes,
                requested,
            });
            return false;
        }
        self.logical_bytes = requested;
        true
    }

    fn push_raw(&mut self, tag: u8, payload: &[u8]) {
        let Some(additional) = payload.len().checked_add(9) else {
            self.error = Some(ContentKeyCacheError::KeyBytesExhausted {
                limit: self.max_key_bytes,
                requested: usize::MAX,
            });
            return;
        };
        if !self.reserve_logical(additional) {
            return;
        }
        self.local.push(tag);
        self.local
            .extend_from_slice(&(payload.len() as u64).to_le_bytes());
        self.local.extend_from_slice(payload);
    }

    fn push_fixed(&mut self, tag: u8, payload: &[u8]) {
        let Some(additional) = payload.len().checked_add(1) else {
            self.error = Some(ContentKeyCacheError::KeyBytesExhausted {
                limit: self.max_key_bytes,
                requested: usize::MAX,
            });
            return;
        };
        if !self.reserve_logical(additional) {
            return;
        }
        self.local.push(tag);
        self.local.extend_from_slice(payload);
    }

    fn flush_local(&mut self) {
        if !self.local.is_empty() {
            self.fragments
                .push(ContentKey::from_bytes(std::mem::take(&mut self.local)));
        }
    }

    /// Splice an already-built exact child key at the current stream position.
    pub fn push_key(&mut self, key: ContentKey) {
        if !self.reserve_logical(key.len()) {
            return;
        }
        self.flush_local();
        self.fragments.push(key);
    }

    /// Append one child as an exact `Hasher::write` segment without flattening
    /// its persistent rope. The resulting bytes are the ordinary raw-write tag,
    /// the `u64` little-endian child length, and the complete child key.
    pub fn push_framed_key(&mut self, key: ContentKey) {
        let Some(additional) = key.len().checked_add(9) else {
            self.error = Some(ContentKeyCacheError::KeyBytesExhausted {
                limit: self.max_key_bytes,
                requested: usize::MAX,
            });
            return;
        };
        if !self.reserve_logical(additional) {
            return;
        }
        self.local.push(0);
        self.local
            .extend_from_slice(&(key.len() as u64).to_le_bytes());
        self.flush_local();
        self.fragments.push(key);
    }

    /// Finish the persistent exact key without flattening child fragments.
    pub fn into_key(mut self) -> Result<ContentKey, ContentKeyCacheError> {
        if let Some(error) = self.error.take() {
            return Err(error);
        }
        self.flush_local();
        ContentKey::try_concat_keys(self.fragments, self.max_key_bytes)
    }
}

impl Hasher for SemanticKeyBuilder {
    fn finish(&self) -> u64 {
        if self.error.is_some() {
            return 0;
        }
        let mut fingerprint = 0u128;
        for fragment in &self.fragments {
            fingerprint =
                concatenate_fingerprint(fingerprint, fragment.inner().fingerprint, fragment.len());
        }
        let local_fingerprint = fingerprint_bytes(&self.local);
        fingerprint = concatenate_fingerprint(fingerprint, local_fingerprint, self.local.len());
        fingerprint as u64
    }

    fn write(&mut self, bytes: &[u8]) {
        self.push_raw(0, bytes);
    }

    fn write_u8(&mut self, value: u8) {
        self.push_fixed(1, &[value]);
    }

    fn write_u16(&mut self, value: u16) {
        self.push_fixed(2, &value.to_le_bytes());
    }

    fn write_u32(&mut self, value: u32) {
        self.push_fixed(3, &value.to_le_bytes());
    }

    fn write_u64(&mut self, value: u64) {
        self.push_fixed(4, &value.to_le_bytes());
    }

    fn write_u128(&mut self, value: u128) {
        self.push_fixed(5, &value.to_le_bytes());
    }

    fn write_usize(&mut self, value: usize) {
        self.push_fixed(6, &(value as u128).to_le_bytes());
    }

    fn write_i8(&mut self, value: i8) {
        self.push_fixed(7, &value.to_le_bytes());
    }

    fn write_i16(&mut self, value: i16) {
        self.push_fixed(8, &value.to_le_bytes());
    }

    fn write_i32(&mut self, value: i32) {
        self.push_fixed(9, &value.to_le_bytes());
    }

    fn write_i64(&mut self, value: i64) {
        self.push_fixed(10, &value.to_le_bytes());
    }

    fn write_i128(&mut self, value: i128) {
        self.push_fixed(11, &value.to_le_bytes());
    }

    fn write_isize(&mut self, value: isize) {
        self.push_fixed(12, &(value as i128).to_le_bytes());
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ContentKeyAccelerator {
    len: usize,
    fingerprint: u128,
}

/// Collision-safe index for lazy [`ContentKey`] values.
///
/// The immutable length/fingerprint pair selects a bucket only. Every lookup
/// performs exact `ContentKey` equality inside that bucket, so an accelerator
/// collision cannot conflate distinct semantic terms. Keeping keys in bucket
/// values also avoids using the lazily flattened key as a mutable map key.
pub struct ContentKeyMap<V> {
    buckets: HashMap<ContentKeyAccelerator, Vec<(ContentKey, V)>>,
    len: usize,
}

impl<V> Default for ContentKeyMap<V> {
    fn default() -> Self {
        Self { buckets: HashMap::default(), len: 0 }
    }
}

impl<V> ContentKeyMap<V> {
    /// Borrow the value whose key is byte-exactly equal to `key`.
    pub fn get(&self, key: &ContentKey) -> Option<&V> {
        self.buckets
            .get(&key.accelerator())
            .and_then(|bucket| find_exact(bucket, key).map(|index| &bucket[index].1))
    }

    /// Mutably borrow the value whose key is byte-exactly equal to `key`.
    ///
    /// The immutable accelerator selects only a bucket. Exact key equality is
    /// still checked before exposing the value, and the lazily materialized
    /// [`ContentKey`] remains a bucket value rather than a hash-map key.
    pub fn get_mut(&mut self, key: &ContentKey) -> Option<&mut V> {
        self.buckets
            .get_mut(&key.accelerator())
            .and_then(|bucket| find_exact(bucket, key).map(|index| &mut bucket[index].1))
    }

    /// Insert a value, replacing and returning only an exact-key match.
    pub fn insert(&mut self, key: ContentKey, value: V) -> Option<V> {
        let bucket = self.buckets.entry(key.accelerator()).or_default();
        if let Some(index) = find_exact(bucket, &key) {
            return Some(std::mem::replace(&mut bucket[index].1, value));
        }
        bucket.push((key, value));
        self.len += 1;
        None
    }

    /// Number of exact keys in the map.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether the map contains no exact keys.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Iterate over exact key/value pairs in unspecified bucket order.
    pub fn iter(&self) -> impl Iterator<Item = (&ContentKey, &V)> {
        self.buckets
            .values()
            .flat_map(|bucket| bucket.iter().map(|(key, value)| (key, value)))
    }

    /// Consume the map and iterate over its values in unspecified bucket order.
    pub fn into_values(self) -> impl Iterator<Item = V> {
        self.buckets
            .into_values()
            .flat_map(|bucket| bucket.into_iter().map(|(_, value)| value))
    }
}

fn find_exact<V>(bucket: &[(ContentKey, V)], key: &ContentKey) -> Option<usize> {
    bucket.iter().position(|(candidate, _)| candidate == key)
}

#[derive(Default)]
pub struct ContentKeySet {
    entries: ContentKeyMap<()>,
}

impl ContentKeySet {
    /// Insert an exact key, returning whether it was not already present.
    pub fn insert(&mut self, key: ContentKey) -> bool {
        self.entries.insert(key, ()).is_none()
    }

    /// Test membership by byte-exact key equality.
    pub fn contains(&self, key: &ContentKey) -> bool {
        self.entries.get(key).is_some()
    }

    /// Number of exact keys in the set.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the set contains no exact keys.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Iterate over exact keys in unspecified bucket order.
    pub fn iter(&self) -> impl Iterator<Item = &ContentKey> {
        self.entries.iter().map(|(key, ())| key)
    }

    /// Iterate over keys present in `self` but absent from `other`.
    pub fn difference<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = &'a ContentKey> {
        self.iter().filter(|key| !other.contains(key))
    }

    /// Iterate over keys present in both sets.
    pub fn intersection<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = &'a ContentKey> {
        self.iter().filter(|key| other.contains(key))
    }
}

impl FromIterator<ContentKey> for ContentKeySet {
    fn from_iter<T: IntoIterator<Item = ContentKey>>(iter: T) -> Self {
        let mut set = Self::default();
        for key in iter {
            set.insert(key);
        }
        set
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

// SAFETY: equality and hashing compare exactly the stable discriminant and the
// ordered payload segments written below. Every component is length-framed, so
// distinct segment decompositions cannot alias. The observation-only label is
// excluded consistently from both equality and the semantic byte stream.
unsafe impl SemanticHash for FramedSemanticOperator {
    fn write_content(&self, out: &mut Vec<u8>) {
        write_framed(out, &self.stable_discriminant.to_le_bytes());
        for segment in &self.payload_segments {
            write_framed(out, segment);
        }
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
    use std::collections::hash_map::DefaultHasher;

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
    fn framed_operator_matches_generated_discriminant_and_payload_encoding() {
        let operator =
            FramedSemanticOperator::new(17, vec![b"fixed".to_vec(), b"dynamic".to_vec()]);
        let mut expected = Vec::new();
        write_framed(&mut expected, &17u32.to_le_bytes());
        write_framed(&mut expected, b"fixed");
        write_framed(&mut expected, b"dynamic");
        assert_eq!(operator.content_key(), ContentKey::from_bytes(expected));
    }

    #[test]
    fn framed_operator_equality_and_display_follow_semantic_identity() {
        let left = FramedSemanticOperator::new(3, vec![b"value".to_vec()]);
        let right = FramedSemanticOperator::new(3, vec![b"value".to_vec()]);
        assert_eq!(left, right);
        assert_eq!(left.content_key(), right.content_key());
        assert_eq!(left.to_string(), right.to_string());
    }

    #[test]
    fn accelerator_bucket_collision_uses_exact_key_fallback() {
        let left = ContentKey::from_bytes(b"left".to_vec());
        let right = ContentKey::from_bytes(b"right".to_vec());
        // A single forced bucket models an arbitrary accelerator collision.
        let bucket = vec![(left.clone(), 1usize), (right.clone(), 2usize)];
        assert_eq!(find_exact(&bucket, &left), Some(0));
        assert_eq!(find_exact(&bucket, &right), Some(1));
        assert_eq!(find_exact(&bucket, &ContentKey::from_bytes(b"absent".to_vec())), None);
    }

    #[test]
    fn content_key_bucket_map_replaces_only_exact_matches() {
        let left = ContentKey::from_bytes(b"left".to_vec());
        let right = ContentKey::from_bytes(b"right".to_vec());
        let mut map = ContentKeyMap::default();
        assert_eq!(map.insert(left.clone(), 1usize), None);
        assert_eq!(map.insert(right.clone(), 2usize), None);
        assert_eq!(map.insert(left.clone(), 3usize), Some(1));
        assert_eq!(map.len(), 2);
        assert_eq!(map.get(&left), Some(&3));
        assert_eq!(map.get(&right), Some(&2));

        *map.get_mut(&left).expect("exact left key is present") = 4;
        assert_eq!(map.get(&left), Some(&4));
        assert_eq!(map.get(&right), Some(&2));
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
        let mut s = ContentKeySet::default();
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
        let left = ContentKey::tree(&"left", Vec::new());
        let right = ContentKey::tree(&"right", Vec::new());
        let tree = ContentKey::tree(&"pair", vec![left, right]);
        let flat = ContentKey::from_bytes(tree.as_bytes().to_vec());

        assert_eq!(tree, flat);
        let mut tree_hasher = DefaultHasher::new();
        tree.hash(&mut tree_hasher);
        let mut flat_hasher = DefaultHasher::new();
        flat.hash(&mut flat_hasher);
        assert_eq!(tree_hasher.finish(), flat_hasher.finish());
    }

    #[test]
    fn raw_concatenation_preserves_the_existing_exact_stream() {
        let left = ContentKey::from_bytes(vec![1, 2, 3]);
        let right = ContentKey::from_bytes(vec![4, 5]);
        let key = ContentKey::concat(vec![9, 8], vec![left, right]);
        assert_eq!(key.as_bytes(), &[9, 8, 1, 2, 3, 4, 5]);
        assert_eq!(key, ContentKey::from_bytes(vec![9, 8, 1, 2, 3, 4, 5]));
    }

    #[test]
    fn nested_concatenation_is_representation_independent() {
        let leaf = ContentKey::from_bytes(vec![3, 4]);
        let nested = ContentKey::concat(vec![1], vec![ContentKey::concat(vec![2], vec![leaf])]);
        let flat = ContentKey::from_bytes(vec![1, 2, 3, 4]);
        assert_eq!(nested, flat);
        let mut nested_hasher = DefaultHasher::new();
        let mut flat_hasher = DefaultHasher::new();
        nested.hash(&mut nested_hasher);
        flat.hash(&mut flat_hasher);
        assert_eq!(nested_hasher.finish(), flat_hasher.finish());
    }

    #[test]
    fn semantic_key_builder_splices_cached_children_without_changing_bytes() {
        let mut child_builder = SemanticKeyBuilder::default();
        child_builder.write_u16(0x1234);
        child_builder.write(b"child");
        let child = child_builder.into_key().expect("child key fits");

        let mut composed = SemanticKeyBuilder::default();
        composed.write_u8(7);
        composed.push_key(child);
        composed.write_i64(-9);
        let composed = composed.into_key().expect("composed key fits");

        let mut reference = SemanticKeyBuilder::default();
        reference.write_u8(7);
        reference.write_u16(0x1234);
        reference.write(b"child");
        reference.write_i64(-9);
        let reference = reference.into_key().expect("reference key fits");

        assert_eq!(composed, reference);
        assert_eq!(composed.as_bytes(), reference.as_bytes());
    }

    #[test]
    fn semantic_key_builder_frames_cached_children_like_hasher_write() {
        let mut child_builder = SemanticKeyBuilder::default();
        child_builder.write_u16(0x1234);
        child_builder.write(b"child");
        let child = child_builder.into_key().expect("child key fits");

        let mut composed = SemanticKeyBuilder::default();
        composed.write_u8(7);
        composed.push_framed_key(child.clone());
        composed.write_i64(-9);

        let mut reference = SemanticKeyBuilder::default();
        reference.write_u8(7);
        reference.write(child.as_bytes());
        reference.write_i64(-9);

        assert_eq!(composed.finish(), reference.finish());
        assert_eq!(
            composed.into_key().expect("composed key fits"),
            reference.into_key().expect("reference key fits"),
        );
    }

    #[test]
    fn semantic_key_builder_finish_is_representation_independent() {
        let mut child_builder = SemanticKeyBuilder::default();
        child_builder.write_u32(41);
        let child = child_builder.into_key().expect("child key fits");

        let mut composed = SemanticKeyBuilder::default();
        composed.write_usize(3);
        composed.push_key(child);
        composed.write_i128(-17);

        let mut flat = SemanticKeyBuilder::default();
        flat.write_usize(3);
        flat.write_u32(41);
        flat.write_i128(-17);

        assert_eq!(composed.finish(), flat.finish());
        assert_eq!(
            composed.into_key().expect("composed key fits"),
            flat.into_key().expect("flat key fits"),
        );
    }

    #[test]
    fn cache_transaction_reuses_live_pointer_identity() {
        let node = Arc::new(String::from("node"));
        let key = ContentKey::from_bytes(vec![1, 2, 3]);
        let mut cache = ContentKeyCache::with_max_entries(4);
        {
            let mut transaction = cache.transaction();
            assert!(transaction.get(&node).is_none());
            assert_eq!(transaction.stage(node.clone(), key.clone()), Ok(key.clone()));
            assert_eq!(transaction.get(&node), Some(key.clone()));
            assert_eq!(transaction.commit(), Ok(1));
        }
        let transaction = cache.transaction();
        assert_eq!(transaction.get(&node), Some(key));
    }

    #[test]
    fn cache_exhaustion_publishes_no_partial_transaction() {
        let first = Arc::new(1u64);
        let second = Arc::new(2u64);
        let mut cache = ContentKeyCache::with_max_entries(1);
        let mut transaction = cache.transaction();
        transaction
            .stage(first, ContentKey::from_bytes(vec![1]))
            .expect("first staged key");
        transaction
            .stage(second, ContentKey::from_bytes(vec![2]))
            .expect("second staged key");
        assert_eq!(
            transaction.commit(),
            Err(ContentKeyCacheError::ResourceExhausted { limit: 1, requested: 2 })
        );
        assert!(cache.is_empty());
    }

    #[test]
    fn semantic_key_builder_enforces_logical_byte_limit_atomically() {
        let mut builder = SemanticKeyBuilder::with_max_bytes(2);
        builder.write_u8(7);
        builder.write_u8(8);
        assert_eq!(
            builder.into_key(),
            Err(ContentKeyCacheError::KeyBytesExhausted { limit: 2, requested: 4 }),
        );
    }

    #[test]
    fn framed_child_length_counts_toward_logical_byte_limit() {
        let child = ContentKey::from_bytes(vec![1, 2, 3]);
        let mut builder = SemanticKeyBuilder::with_max_bytes(11);
        builder.push_framed_key(child);
        assert_eq!(
            builder.into_key(),
            Err(ContentKeyCacheError::KeyBytesExhausted { limit: 11, requested: 12 }),
        );
    }

    #[test]
    fn cache_rejects_overlong_key_before_staging_or_commit() {
        let node = Arc::new(3u8);
        let mut cache = ContentKeyCache::with_limits(4, 2);
        let mut transaction = cache.transaction();
        assert_eq!(transaction.max_key_bytes(), 2);
        assert_eq!(
            transaction.stage(node, ContentKey::from_bytes(vec![1, 2, 3])),
            Err(ContentKeyCacheError::KeyBytesExhausted { limit: 2, requested: 3 }),
        );
        assert_eq!(transaction.commit(), Ok(0));
        assert!(cache.is_empty());
    }

    #[test]
    fn one_live_allocation_cannot_change_exact_identity() {
        let node = Arc::new(7u64);
        let mut cache = ContentKeyCache::default();
        let mut transaction = cache.transaction();
        transaction
            .stage(node.clone(), ContentKey::from_bytes(vec![1]))
            .expect("first identity");
        assert_eq!(
            transaction.stage(node, ContentKey::from_bytes(vec![2])),
            Err(ContentKeyCacheError::IdentityConflict)
        );
    }

    #[test]
    fn graph_cache_retains_the_root_that_owns_borrowed_node_addresses() {
        #[derive(Debug)]
        struct Root {
            child: Box<u64>,
        }

        let root = Arc::new(Root { child: Box::new(17) });
        let weak = Arc::downgrade(&root);
        let key = 17u64.content_key();
        let mut cache = ContentKeyCache::with_max_entries(4);
        {
            let mut transaction = cache.transaction_for_root(root.clone());
            // SAFETY: child is owned by the retained immutable root.
            unsafe {
                transaction
                    .stage_borrowed(root.child.as_ref(), key.clone())
                    .expect("borrowed node has one exact identity");
            }
            assert_eq!(transaction.get_borrowed(root.child.as_ref()), Some(key.clone()));
            assert_eq!(transaction.commit(), Ok(1));
        }

        drop(root);
        let retained = weak
            .upgrade()
            .expect("committed graph cache must retain its root owner");
        let transaction = cache.transaction_for_root(retained.clone());
        assert_eq!(transaction.get_borrowed(retained.child.as_ref()), Some(key));
    }

    #[test]
    fn graph_cache_exhaustion_publishes_no_root_or_node() {
        let root = Arc::new(Box::new(29u64));
        let weak = Arc::downgrade(&root);
        let mut cache = ContentKeyCache::with_max_entries(0);
        let mut transaction = cache.transaction_for_root(root.clone());
        // SAFETY: the value is owned by the retained immutable root.
        unsafe {
            transaction
                .stage_borrowed(root.as_ref().as_ref(), 29u64.content_key())
                .expect("staging remains provisional");
        }
        assert_eq!(
            transaction.commit(),
            Err(ContentKeyCacheError::ResourceExhausted { limit: 0, requested: 1 })
        );
        assert!(cache.is_empty());
        assert!(cache.retained_roots.is_empty());
        drop(root);
        assert!(weak.upgrade().is_none());
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
