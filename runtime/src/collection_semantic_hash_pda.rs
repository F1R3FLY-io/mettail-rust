use mettail_semantic_key::{ContentKey, ContentKeyCacheError, SemanticKeyBuilder};

/// Structural collection-key ABI emitted by this machine.
///
/// Version 1 reduced recursive children to finite `u64` digests before sorting
/// or combining them. Version 2 carries complete exact child keys through the
/// collection PDA and uses the digest embedded in [`ContentKey`] only as an
/// accelerator with mandatory exact fallback.
pub const COLLECTION_SEMANTIC_KEY_ABI_V2: u8 = 2;

/// Exact per-element sink used while a collection PDA is suspended.
///
/// Generated term drivers borrow this builder through a stable raw pointer.
/// The builder is boxed by [`CollectionSemanticHashPda`], so moving the PDA
/// frame never invalidates that pointer.
pub type CollectionSemanticHasher = SemanticKeyBuilder;

#[derive(Clone, Copy, Debug)]
pub struct CollectionSemanticHashItem {
    primary: *const (),
    secondary: Option<*const ()>,
    repetitions: usize,
}

impl CollectionSemanticHashItem {
    #[inline]
    pub fn unary<T>(value: &T) -> Self {
        Self {
            primary: value as *const T as *const (),
            secondary: None,
            repetitions: 1,
        }
    }

    #[inline]
    pub fn pair<K, V>(primary: &K, secondary: &V) -> Self {
        Self {
            primary: primary as *const K as *const (),
            secondary: Some(secondary as *const V as *const ()),
            repetitions: 1,
        }
    }

    #[inline]
    pub fn key_only<T>(key: &T) -> Self {
        Self::unary(key)
    }

    #[inline]
    pub fn repeated<T>(value: &T, repetitions: usize) -> Self {
        Self {
            primary: value as *const T as *const (),
            secondary: None,
            repetitions,
        }
    }
}

#[derive(Debug)]
pub enum CollectionSemanticHashStep {
    /// Write one child into the supplied exact scratch builder, then resume.
    Hash {
        role: CollectionSemanticHashRole,
        value: *const (),
        state: *mut CollectionSemanticHasher,
    },
    WriteU8(u8),
    WriteUsize(usize),
    /// Write a length-framed exact child key at this structural position.
    WriteKey(ContentKey),
    Error(ContentKeyCacheError),
    Done,
}

/// Structural role requested by a suspended collection-key PDA.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CollectionSemanticHashRole {
    Primary,
    Secondary,
}

/// Resumable exact semantic-key construction for recursive collections.
///
/// The machine emits the following versioned structural streams:
///
/// - set: ABI, kind, entry count, sorted exact element keys;
/// - map: ABI, kind, entry count, sorted exact key/value pairs;
/// - bag: ABI, kind, total count, distinct-entry count, sorted exact
///   element-key/multiplicity pairs;
/// - PathMap: ABI, PathMap kind, explicit Empty/Set/Map mode, entry count,
///   then mode-correct exact entries.
///
/// Sorting compares complete [`ContentKey`] values. Its fixed-width rolling
/// fingerprint can accelerate equality buckets, but never establishes
/// identity or order on its own. All traversal remains on the generated
/// explicit work stack.
pub struct CollectionSemanticHashPda {
    kind: Kind,
    phase: Phase,
    items: Vec<CollectionSemanticHashItem>,
    item_index: usize,
    emit_index: usize,
    pending_key: Option<ContentKey>,
    scratch: Box<CollectionSemanticHasher>,
    waiting: bool,
    unary_keys: Vec<ContentKey>,
    pair_keys: Vec<(ContentKey, ContentKey)>,
    counted_keys: Vec<(ContentKey, usize)>,
    error: Option<ContentKeyCacheError>,
    max_key_bytes: usize,
}

impl CollectionSemanticHashPda {
    pub fn set(items: Vec<CollectionSemanticHashItem>) -> Self {
        Self::set_with_max_bytes(items, usize::MAX)
    }

    pub fn set_with_max_bytes(
        items: Vec<CollectionSemanticHashItem>,
        max_key_bytes: usize,
    ) -> Self {
        Self::new(Kind::Set, items, max_key_bytes)
    }

    pub fn map(items: Vec<CollectionSemanticHashItem>) -> Self {
        Self::map_with_max_bytes(items, usize::MAX)
    }

    pub fn map_with_max_bytes(
        items: Vec<CollectionSemanticHashItem>,
        max_key_bytes: usize,
    ) -> Self {
        Self::new(Kind::Map, items, max_key_bytes)
    }

    pub fn bag(total_count: usize, items: Vec<CollectionSemanticHashItem>) -> Self {
        Self::bag_with_max_bytes(total_count, items, usize::MAX)
    }

    pub fn bag_with_max_bytes(
        total_count: usize,
        items: Vec<CollectionSemanticHashItem>,
        max_key_bytes: usize,
    ) -> Self {
        Self::new(Kind::Bag { total_count }, items, max_key_bytes)
    }

    pub fn path_neutral() -> Self {
        Self::path_neutral_with_max_bytes(usize::MAX)
    }

    pub fn path_neutral_with_max_bytes(max_key_bytes: usize) -> Self {
        Self::new(Kind::PathNeutral, Vec::new(), max_key_bytes)
    }

    pub fn path_set(items: Vec<CollectionSemanticHashItem>) -> Self {
        Self::path_set_with_max_bytes(items, usize::MAX)
    }

    pub fn path_set_with_max_bytes(
        items: Vec<CollectionSemanticHashItem>,
        max_key_bytes: usize,
    ) -> Self {
        Self::new(Kind::PathSet, items, max_key_bytes)
    }

    pub fn path_map(items: Vec<CollectionSemanticHashItem>) -> Self {
        Self::path_map_with_max_bytes(items, usize::MAX)
    }

    pub fn path_map_with_max_bytes(
        items: Vec<CollectionSemanticHashItem>,
        max_key_bytes: usize,
    ) -> Self {
        Self::new(Kind::PathMap, items, max_key_bytes)
    }

    fn new(kind: Kind, items: Vec<CollectionSemanticHashItem>, max_key_bytes: usize) -> Self {
        let capacity = items.len();
        let error = (!kind.accepts(&items)).then_some(ContentKeyCacheError::ConstructionInvariant);
        Self {
            kind,
            phase: Phase::Abi,
            items,
            item_index: 0,
            emit_index: 0,
            pending_key: None,
            scratch: Box::new(CollectionSemanticHasher::with_max_bytes(max_key_bytes)),
            waiting: false,
            unary_keys: Vec::with_capacity(capacity),
            pair_keys: Vec::with_capacity(capacity),
            counted_keys: Vec::with_capacity(capacity),
            error,
            max_key_bytes,
        }
    }

    pub fn resume(&mut self) -> CollectionSemanticHashStep {
        if let Some(error) = self.error.take() {
            self.phase = Phase::Done;
            return CollectionSemanticHashStep::Error(error);
        }
        if self.waiting {
            if let Err(error) = self.accept_hash() {
                self.phase = Phase::Done;
                return CollectionSemanticHashStep::Error(error);
            }
        }

        loop {
            match self.phase {
                Phase::Abi => {
                    self.phase = Phase::Kind;
                    return CollectionSemanticHashStep::WriteU8(COLLECTION_SEMANTIC_KEY_ABI_V2);
                },
                Phase::Kind => {
                    self.phase = if self.kind.path_mode().is_some() {
                        Phase::PathMode
                    } else {
                        Phase::Prefix0
                    };
                    return CollectionSemanticHashStep::WriteU8(self.kind.tag());
                },
                Phase::PathMode => {
                    let Some(mode) = self.kind.path_mode() else {
                        self.phase = Phase::Done;
                        return CollectionSemanticHashStep::Error(
                            ContentKeyCacheError::ConstructionInvariant,
                        );
                    };
                    self.phase = Phase::Prefix0;
                    return CollectionSemanticHashStep::WriteU8(mode);
                },
                Phase::Prefix0 => {
                    let prefix = match self.kind {
                        Kind::Bag { total_count } => total_count,
                        Kind::Set
                        | Kind::Map
                        | Kind::PathNeutral
                        | Kind::PathSet
                        | Kind::PathMap => self.items.len(),
                    };
                    self.phase = if matches!(self.kind, Kind::Bag { .. }) {
                        Phase::Prefix1
                    } else {
                        Phase::Items
                    };
                    return CollectionSemanticHashStep::WriteUsize(prefix);
                },
                Phase::Prefix1 => {
                    self.phase = Phase::Items;
                    return CollectionSemanticHashStep::WriteUsize(self.items.len());
                },
                Phase::Items => {
                    if self.item_index == self.items.len() {
                        self.unary_keys.sort();
                        self.pair_keys.sort();
                        self.counted_keys.sort();
                        self.phase = Phase::Emit;
                        continue;
                    }
                    let item = self.items[self.item_index];
                    let pending = match self.kind {
                        Kind::Set | Kind::PathSet => PendingHash::Unary,
                        Kind::Map | Kind::PathMap => PendingHash::MapKey,
                        Kind::Bag { .. } => PendingHash::BagElement,
                        Kind::PathNeutral => {
                            self.phase = Phase::Emit;
                            continue;
                        },
                    };
                    return self.request_hash(
                        item.primary,
                        CollectionSemanticHashRole::Primary,
                        pending,
                    );
                },
                Phase::MapValue => {
                    let Some(value) = self
                        .items
                        .get(self.item_index)
                        .and_then(|item| item.secondary)
                    else {
                        self.phase = Phase::Done;
                        return CollectionSemanticHashStep::Error(
                            ContentKeyCacheError::ConstructionInvariant,
                        );
                    };
                    return self.request_hash(
                        value,
                        CollectionSemanticHashRole::Secondary,
                        PendingHash::MapValue,
                    );
                },
                Phase::Emit => match self.kind {
                    Kind::Set | Kind::PathSet => {
                        let Some(key) = self.unary_keys.get(self.emit_index).cloned() else {
                            self.phase = Phase::Done;
                            continue;
                        };
                        self.emit_index += 1;
                        return CollectionSemanticHashStep::WriteKey(key);
                    },
                    Kind::Map | Kind::PathMap => {
                        let flat_index = self.emit_index;
                        let Some((key, value)) = self.pair_keys.get(flat_index / 2) else {
                            self.phase = Phase::Done;
                            continue;
                        };
                        self.emit_index += 1;
                        return CollectionSemanticHashStep::WriteKey(if flat_index % 2 == 0 {
                            key.clone()
                        } else {
                            value.clone()
                        });
                    },
                    Kind::Bag { .. } => {
                        let flat_index = self.emit_index;
                        let Some((key, count)) = self.counted_keys.get(flat_index / 2) else {
                            self.phase = Phase::Done;
                            continue;
                        };
                        self.emit_index += 1;
                        return if flat_index % 2 == 0 {
                            CollectionSemanticHashStep::WriteKey(key.clone())
                        } else {
                            CollectionSemanticHashStep::WriteUsize(*count)
                        };
                    },
                    Kind::PathNeutral => {
                        self.phase = Phase::Done;
                        continue;
                    },
                },
                Phase::PendingUnary
                | Phase::PendingMapKey
                | Phase::PendingMapValue
                | Phase::PendingBagElement => {
                    self.phase = Phase::Done;
                    return CollectionSemanticHashStep::Error(
                        ContentKeyCacheError::ConstructionInvariant,
                    );
                },
                Phase::Done => return CollectionSemanticHashStep::Done,
            }
        }
    }

    fn request_hash(
        &mut self,
        value: *const (),
        role: CollectionSemanticHashRole,
        pending: PendingHash,
    ) -> CollectionSemanticHashStep {
        *self.scratch = CollectionSemanticHasher::with_max_bytes(self.max_key_bytes);
        self.phase = pending.phase();
        self.waiting = true;
        CollectionSemanticHashStep::Hash { role, value, state: &mut *self.scratch }
    }

    fn accept_hash(&mut self) -> Result<(), ContentKeyCacheError> {
        self.waiting = false;
        let key = std::mem::take(&mut *self.scratch).into_key()?;
        match self.phase {
            Phase::PendingUnary => {
                self.unary_keys.push(key);
                self.item_index += 1;
                self.phase = Phase::Items;
                Ok(())
            },
            Phase::PendingMapKey => {
                self.pending_key = Some(key);
                self.phase = Phase::MapValue;
                Ok(())
            },
            Phase::PendingMapValue => {
                let Some(primary) = self.pending_key.take() else {
                    return Err(ContentKeyCacheError::ConstructionInvariant);
                };
                self.pair_keys.push((primary, key));
                self.item_index += 1;
                self.phase = Phase::Items;
                Ok(())
            },
            Phase::PendingBagElement => {
                let Some(count) = self.items.get(self.item_index).map(|item| item.repetitions)
                else {
                    return Err(ContentKeyCacheError::ConstructionInvariant);
                };
                self.counted_keys.push((key, count));
                self.item_index += 1;
                self.phase = Phase::Items;
                Ok(())
            },
            _ => Err(ContentKeyCacheError::ConstructionInvariant),
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Kind {
    Set,
    Map,
    Bag { total_count: usize },
    PathNeutral,
    PathSet,
    PathMap,
}

impl Kind {
    fn accepts(self, items: &[CollectionSemanticHashItem]) -> bool {
        match self {
            Self::Set | Self::PathSet => items
                .iter()
                .all(|item| item.secondary.is_none() && item.repetitions == 1),
            Self::Map | Self::PathMap => items
                .iter()
                .all(|item| item.secondary.is_some() && item.repetitions == 1),
            Self::Bag { total_count } => {
                let count = items.iter().try_fold(0usize, |sum, item| {
                    (item.secondary.is_none() && item.repetitions > 0)
                        .then(|| sum.checked_add(item.repetitions))
                        .flatten()
                });
                count == Some(total_count)
            },
            Self::PathNeutral => items.is_empty(),
        }
    }

    fn tag(self) -> u8 {
        match self {
            Self::Set => 0,
            Self::Map => 1,
            Self::Bag { .. } => 2,
            Self::PathNeutral | Self::PathSet | Self::PathMap => 3,
        }
    }

    fn path_mode(self) -> Option<u8> {
        match self {
            Self::PathNeutral => Some(0),
            Self::PathSet => Some(1),
            Self::PathMap => Some(2),
            Self::Set | Self::Map | Self::Bag { .. } => None,
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum PendingHash {
    Unary,
    MapKey,
    MapValue,
    BagElement,
}

impl PendingHash {
    fn phase(self) -> Phase {
        match self {
            Self::Unary => Phase::PendingUnary,
            Self::MapKey => Phase::PendingMapKey,
            Self::MapValue => Phase::PendingMapValue,
            Self::BagElement => Phase::PendingBagElement,
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Phase {
    Abi,
    Kind,
    PathMode,
    Prefix0,
    Prefix1,
    Items,
    MapValue,
    PendingUnary,
    PendingMapKey,
    PendingMapValue,
    PendingBagElement,
    Emit,
    Done,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{HashBag, HashMapLit, HashSetLit};
    use std::hash::Hash;

    #[derive(Debug, PartialEq, Eq)]
    enum TraceWrite {
        U8(u8),
        Usize(usize),
        Key(Vec<u8>),
    }

    fn exact_key<T: Hash>(value: &T) -> ContentKey {
        let mut builder = SemanticKeyBuilder::default();
        value.hash(&mut builder);
        builder.into_key().expect("test key fits")
    }

    fn run(mut pda: CollectionSemanticHashPda) -> Vec<TraceWrite> {
        let mut output = Vec::new();
        loop {
            match pda.resume() {
                CollectionSemanticHashStep::Hash { value, state, .. } => unsafe {
                    (*(value.cast::<i32>())).hash(&mut *state);
                },
                CollectionSemanticHashStep::WriteU8(value) => {
                    output.push(TraceWrite::U8(value));
                },
                CollectionSemanticHashStep::WriteUsize(value) => {
                    output.push(TraceWrite::Usize(value));
                },
                CollectionSemanticHashStep::WriteKey(value) => {
                    output.push(TraceWrite::Key(value.as_bytes().to_vec()));
                },
                CollectionSemanticHashStep::Error(error) => {
                    panic!("valid collection-key machine failed: {error}");
                },
                CollectionSemanticHashStep::Done => return output,
            }
        }
    }

    #[test]
    fn set_stream_retains_sorted_exact_children() {
        let set: HashSetLit<i32> = [7, -3, 11, 7].into_iter().collect();
        let items = set.iter().map(CollectionSemanticHashItem::unary).collect();
        let actual = run(CollectionSemanticHashPda::set(items));
        let mut keys: Vec<_> = set.iter().map(exact_key).collect();
        keys.sort();
        let mut expected = vec![
            TraceWrite::U8(COLLECTION_SEMANTIC_KEY_ABI_V2),
            TraceWrite::U8(0),
            TraceWrite::Usize(keys.len()),
        ];
        expected.extend(
            keys.into_iter()
                .map(|key| TraceWrite::Key(key.as_bytes().to_vec())),
        );
        assert_eq!(actual, expected);
    }

    #[test]
    fn map_stream_retains_exact_pair_boundaries() {
        let map: HashMapLit<i32, i32> = [(7, 9), (-3, 4), (11, -8)].into_iter().collect();
        let items = map
            .iter()
            .map(|(key, value)| CollectionSemanticHashItem::pair(key, value))
            .collect();
        let actual = run(CollectionSemanticHashPda::map(items));
        let mut pairs: Vec<_> = map
            .iter()
            .map(|(key, value)| (exact_key(key), exact_key(value)))
            .collect();
        pairs.sort();
        let mut expected = vec![
            TraceWrite::U8(COLLECTION_SEMANTIC_KEY_ABI_V2),
            TraceWrite::U8(1),
            TraceWrite::Usize(pairs.len()),
        ];
        for (key, value) in pairs {
            expected.push(TraceWrite::Key(key.as_bytes().to_vec()));
            expected.push(TraceWrite::Key(value.as_bytes().to_vec()));
        }
        assert_eq!(actual, expected);
    }

    #[test]
    fn bag_stream_retains_exact_multiplicities() {
        let bag: HashBag<i32> = [7, -3, 7, 11, -3, 7].into_iter().collect();
        let items = bag
            .iter()
            .map(|(value, count)| CollectionSemanticHashItem::repeated(value, count))
            .collect();
        let actual = run(CollectionSemanticHashPda::bag(bag.len(), items));
        let mut entries: Vec<_> = bag
            .iter()
            .map(|(value, count)| (exact_key(value), count))
            .collect();
        entries.sort();
        let mut expected = vec![
            TraceWrite::U8(COLLECTION_SEMANTIC_KEY_ABI_V2),
            TraceWrite::U8(2),
            TraceWrite::Usize(bag.len()),
            TraceWrite::Usize(entries.len()),
        ];
        for (key, count) in entries {
            expected.push(TraceWrite::Key(key.as_bytes().to_vec()));
            expected.push(TraceWrite::Usize(count));
        }
        assert_eq!(actual, expected);
    }

    #[test]
    fn pathmap_empty_set_and_map_modes_are_distinct() {
        let neutral = run(CollectionSemanticHashPda::path_neutral());
        let set = run(CollectionSemanticHashPda::path_set(Vec::new()));
        let map = run(CollectionSemanticHashPda::path_map(Vec::new()));
        assert_ne!(neutral, set);
        assert_ne!(neutral, map);
        assert_ne!(set, map);
    }

    #[test]
    fn distinct_child_streams_remain_distinct_exact_keys() {
        let left = 1i32;
        let right = 2i32;
        let left_stream =
            run(CollectionSemanticHashPda::set(vec![CollectionSemanticHashItem::unary(&left)]));
        let right_stream =
            run(CollectionSemanticHashPda::set(vec![CollectionSemanticHashItem::unary(&right)]));
        assert_ne!(left_stream, right_stream);
    }

    #[test]
    fn malformed_collection_shapes_fail_closed_without_panicking() {
        let key = 1i32;
        let value = 2i32;
        let malformed = [
            CollectionSemanticHashPda::set(vec![CollectionSemanticHashItem::pair(&key, &value)]),
            CollectionSemanticHashPda::map(vec![CollectionSemanticHashItem::unary(&key)]),
            CollectionSemanticHashPda::bag(1, vec![CollectionSemanticHashItem::repeated(&key, 0)]),
            CollectionSemanticHashPda::path_set(vec![CollectionSemanticHashItem::pair(
                &key, &value,
            )]),
            CollectionSemanticHashPda::path_map(vec![CollectionSemanticHashItem::unary(&key)]),
        ];

        for mut pda in malformed {
            assert!(matches!(
                pda.resume(),
                CollectionSemanticHashStep::Error(ContentKeyCacheError::ConstructionInvariant)
            ));
            assert!(matches!(pda.resume(), CollectionSemanticHashStep::Done));
        }
    }

    #[test]
    fn collection_child_key_byte_exhaustion_is_explicit() {
        let value = 17i32;
        let mut pda = CollectionSemanticHashPda::set_with_max_bytes(
            vec![CollectionSemanticHashItem::unary(&value)],
            1,
        );

        loop {
            match pda.resume() {
                CollectionSemanticHashStep::Hash { value, state, .. } => unsafe {
                    (*(value.cast::<i32>())).hash(&mut *state);
                },
                CollectionSemanticHashStep::Error(ContentKeyCacheError::KeyBytesExhausted {
                    limit,
                    requested,
                }) => {
                    assert_eq!(limit, 1);
                    assert!(requested > limit);
                    break;
                },
                CollectionSemanticHashStep::Error(error) => {
                    panic!("unexpected collection-key error: {error}");
                },
                CollectionSemanticHashStep::Done => {
                    panic!("overlong child key was accepted");
                },
                CollectionSemanticHashStep::WriteU8(_)
                | CollectionSemanticHashStep::WriteUsize(_)
                | CollectionSemanticHashStep::WriteKey(_) => {},
            }
        }
    }
}
