use rustc_hash::FxHasher;
use std::hash::{Hash, Hasher};

/// The exact per-element hasher used by the collection semantic-hash contract.
///
/// Generated term drivers borrow this state through a stable raw pointer while
/// a [`CollectionSemanticHashPda`] is suspended on their explicit work stack.
/// The pointer remains valid because the hasher is boxed and the box allocation
/// does not move when the surrounding PDA frame moves.
pub type CollectionSemanticHasher = FxHasher;

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
    pub fn pair<T>(primary: &T, secondary: &T) -> Self {
        Self {
            primary: primary as *const T as *const (),
            secondary: Some(secondary as *const T as *const ()),
            repetitions: 1,
        }
    }

    /// A map entry whose value callback intentionally writes no bytes.
    ///
    /// Homogeneous set-mode `PathMapLit` uses precisely this representation:
    /// its wrapper delegates to `HashMapLit::semantic_hash_into`, hashing each
    /// key normally and each unit value with an empty callback. The resulting
    /// value digest is therefore `FxHasher::default().finish()`.
    #[inline]
    pub fn key_only<T>(key: &T) -> Self {
        Self::unary(key)
    }

    #[inline]
    pub fn repeated<T>(value: &T, repetitions: usize) -> Self {
        assert!(repetitions > 0, "semantic hash bag entries must be present");
        Self {
            primary: value as *const T as *const (),
            secondary: None,
            repetitions,
        }
    }
}

#[derive(Debug)]
pub enum CollectionSemanticHashStep {
    /// Hash `value` into the supplied stable scratch state, then resume the PDA.
    Hash {
        value: *const (),
        state: *mut CollectionSemanticHasher,
    },
    WriteUsize(usize),
    WriteU64(u64),
    Done,
}

/// Resumable semantic hashing for unordered recursive collections.
///
/// The machine reproduces the existing wrapper contracts without invoking a
/// recursive term callback:
///
/// - set: length, sorted semantic element digests;
/// - map: length, sorted `(key_digest, value_digest)` pairs;
/// - bag: total count, distinct count, and the four commutative lanes;
/// - set-mode PathMap: the map machine with an empty unit-value callback.
///
/// The generated driver owns this PDA in a continuation task. A `Hash` step is
/// answered by pushing the requested term onto the same driver stack with the
/// returned scratch state as its target. Consequently arbitrary nesting adds
/// heap frames, never native call frames.
pub struct CollectionSemanticHashPda {
    kind: Kind,
    phase: Phase,
    items: Vec<CollectionSemanticHashItem>,
    item_index: usize,
    emit_index: usize,
    pending_key_digest: u64,
    scratch: Box<CollectionSemanticHasher>,
    waiting: bool,
    unary_digests: Vec<u64>,
    pair_digests: Vec<(u64, u64)>,
    sum_a: u64,
    sum_b: u64,
    xor_a: u64,
    xor_b: u64,
}

impl CollectionSemanticHashPda {
    pub fn set(items: Vec<CollectionSemanticHashItem>) -> Self {
        assert!(
            items.iter().all(|item| item.secondary.is_none()),
            "set semantic hash items must be unary",
        );
        Self::new(Kind::Set, items)
    }

    pub fn map(items: Vec<CollectionSemanticHashItem>) -> Self {
        Self::new(Kind::Map, items)
    }

    pub fn bag(total_count: usize, items: Vec<CollectionSemanticHashItem>) -> Self {
        assert!(
            items.iter().all(|item| item.secondary.is_none()),
            "bag semantic hash items must be unary",
        );
        assert_eq!(
            items.iter().map(|item| item.repetitions).sum::<usize>(),
            total_count,
            "bag semantic hash total must equal the sum of multiplicities",
        );
        Self::new(Kind::Bag { total_count }, items)
    }

    fn new(kind: Kind, items: Vec<CollectionSemanticHashItem>) -> Self {
        let capacity = items.len();
        Self {
            kind,
            phase: Phase::Prefix0,
            items,
            item_index: 0,
            emit_index: 0,
            pending_key_digest: 0,
            scratch: Box::new(CollectionSemanticHasher::default()),
            waiting: false,
            unary_digests: Vec::with_capacity(capacity),
            pair_digests: Vec::with_capacity(capacity),
            sum_a: 0,
            sum_b: 0,
            xor_a: 0,
            xor_b: 0,
        }
    }

    pub fn resume(&mut self) -> CollectionSemanticHashStep {
        if self.waiting {
            self.accept_hash();
        }

        loop {
            match self.phase {
                Phase::Prefix0 => {
                    self.phase = match self.kind {
                        Kind::Set | Kind::Map => Phase::Items,
                        Kind::Bag { .. } => Phase::Prefix1,
                    };
                    return CollectionSemanticHashStep::WriteUsize(match self.kind {
                        Kind::Set | Kind::Map => self.items.len(),
                        Kind::Bag { total_count } => total_count,
                    });
                },
                Phase::Prefix1 => {
                    self.phase = Phase::Items;
                    return CollectionSemanticHashStep::WriteUsize(self.items.len());
                },
                Phase::Items => match self.kind {
                    Kind::Set => {
                        if self.item_index == self.items.len() {
                            self.unary_digests.sort_unstable();
                            self.phase = Phase::Emit;
                            continue;
                        }
                        return self.request_hash(
                            self.items[self.item_index].primary,
                            PendingHash::SetElement,
                            CollectionSemanticHasher::default(),
                        );
                    },
                    Kind::Map => {
                        if self.item_index == self.items.len() {
                            self.pair_digests.sort_unstable();
                            self.phase = Phase::Emit;
                            continue;
                        }
                        return self.request_hash(
                            self.items[self.item_index].primary,
                            PendingHash::MapKey,
                            CollectionSemanticHasher::default(),
                        );
                    },
                    Kind::Bag { .. } => {
                        if self.item_index == self.items.len() {
                            self.phase = Phase::Emit;
                            continue;
                        }
                        return self.request_hash(
                            self.items[self.item_index].primary,
                            PendingHash::BagA,
                            CollectionSemanticHasher::with_seed(0),
                        );
                    },
                },
                Phase::MapValue => {
                    let item = self.items[self.item_index];
                    if let Some(value) = item.secondary {
                        return self.request_hash(
                            value,
                            PendingHash::MapValue,
                            CollectionSemanticHasher::default(),
                        );
                    }
                    let empty_digest = CollectionSemanticHasher::default().finish();
                    self.pair_digests
                        .push((self.pending_key_digest, empty_digest));
                    self.item_index += 1;
                    self.phase = Phase::Items;
                },
                Phase::BagB => {
                    let item = self.items[self.item_index];
                    let mut state = CollectionSemanticHasher::with_seed(0x9e37_79b9_7f4a_7c15usize);
                    item.repetitions.hash(&mut state);
                    return self.request_hash(item.primary, PendingHash::BagB, state);
                },
                Phase::Emit => match self.kind {
                    Kind::Set => {
                        let Some(&digest) = self.unary_digests.get(self.emit_index) else {
                            self.phase = Phase::Done;
                            continue;
                        };
                        self.emit_index += 1;
                        return CollectionSemanticHashStep::WriteU64(digest);
                    },
                    Kind::Map => {
                        let flat_index = self.emit_index;
                        let Some(&(key, value)) = self.pair_digests.get(flat_index / 2) else {
                            self.phase = Phase::Done;
                            continue;
                        };
                        self.emit_index += 1;
                        return CollectionSemanticHashStep::WriteU64(if flat_index % 2 == 0 {
                            key
                        } else {
                            value
                        });
                    },
                    Kind::Bag { .. } => {
                        let lanes = [self.sum_a, self.sum_b, self.xor_a, self.xor_b];
                        let Some(&lane) = lanes.get(self.emit_index) else {
                            self.phase = Phase::Done;
                            continue;
                        };
                        self.emit_index += 1;
                        return CollectionSemanticHashStep::WriteU64(lane);
                    },
                },
                Phase::PendingSetElement
                | Phase::PendingMapKey
                | Phase::PendingMapValue
                | Phase::PendingBagA
                | Phase::PendingBagB => {
                    panic!("collection semantic hash PDA advanced before its requested hash")
                },
                Phase::Done => return CollectionSemanticHashStep::Done,
            }
        }
    }

    fn request_hash(
        &mut self,
        value: *const (),
        pending: PendingHash,
        state: CollectionSemanticHasher,
    ) -> CollectionSemanticHashStep {
        *self.scratch = state;
        self.phase = pending.phase();
        self.waiting = true;
        CollectionSemanticHashStep::Hash { value, state: &mut *self.scratch }
    }

    fn accept_hash(&mut self) {
        self.waiting = false;
        match self.phase {
            Phase::PendingSetElement => {
                self.unary_digests.push(self.scratch.finish());
                self.item_index += 1;
                self.phase = Phase::Items;
            },
            Phase::PendingMapKey => {
                self.pending_key_digest = self.scratch.finish();
                self.phase = Phase::MapValue;
            },
            Phase::PendingMapValue => {
                self.pair_digests
                    .push((self.pending_key_digest, self.scratch.finish()));
                self.item_index += 1;
                self.phase = Phase::Items;
            },
            Phase::PendingBagA => {
                let count = self.items[self.item_index].repetitions;
                count.hash(&mut *self.scratch);
                let a = mix_hashbag_lane(self.scratch.finish());
                self.pending_key_digest = a;
                self.phase = Phase::BagB;
            },
            Phase::PendingBagB => {
                let a = self.pending_key_digest;
                let b = mix_hashbag_lane(self.scratch.finish());
                self.sum_a = self.sum_a.wrapping_add(a);
                self.sum_b = self.sum_b.wrapping_add(b);
                self.xor_a ^= a.rotate_left((b & 63) as u32);
                self.xor_b ^= b.rotate_left((a & 63) as u32);
                self.item_index += 1;
                self.phase = Phase::Items;
            },
            _ => panic!("collection semantic hash PDA resumed without a pending hash"),
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Kind {
    Set,
    Map,
    Bag { total_count: usize },
}

#[derive(Clone, Copy, Debug)]
enum PendingHash {
    SetElement,
    MapKey,
    MapValue,
    BagA,
    BagB,
}

impl PendingHash {
    fn phase(self) -> Phase {
        match self {
            Self::SetElement => Phase::PendingSetElement,
            Self::MapKey => Phase::PendingMapKey,
            Self::MapValue => Phase::PendingMapValue,
            Self::BagA => Phase::PendingBagA,
            Self::BagB => Phase::PendingBagB,
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Phase {
    Prefix0,
    Prefix1,
    Items,
    MapValue,
    BagB,
    PendingSetElement,
    PendingMapKey,
    PendingMapValue,
    PendingBagA,
    PendingBagB,
    Emit,
    Done,
}

#[inline]
fn mix_hashbag_lane(mut x: u64) -> u64 {
    x ^= x >> 30;
    x = x.wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x ^= x >> 27;
    x = x.wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{HashBag, HashMapLit, HashSetLit};

    #[derive(Default)]
    struct TraceHasher(Vec<TraceWrite>);

    #[derive(Debug, PartialEq, Eq)]
    enum TraceWrite {
        Usize(usize),
        U64(u64),
    }

    impl Hasher for TraceHasher {
        fn finish(&self) -> u64 {
            0
        }

        fn write(&mut self, _bytes: &[u8]) {
            panic!("collection semantic hash oracle unexpectedly used write(bytes)")
        }

        fn write_usize(&mut self, value: usize) {
            self.0.push(TraceWrite::Usize(value));
        }

        fn write_u64(&mut self, value: u64) {
            self.0.push(TraceWrite::U64(value));
        }
    }

    fn run(mut pda: CollectionSemanticHashPda) -> TraceHasher {
        let mut output = TraceHasher::default();
        loop {
            match pda.resume() {
                CollectionSemanticHashStep::Hash { value, state } => unsafe {
                    (*(value.cast::<i32>())).hash(&mut *state);
                },
                CollectionSemanticHashStep::WriteUsize(value) => output.write_usize(value),
                CollectionSemanticHashStep::WriteU64(value) => output.write_u64(value),
                CollectionSemanticHashStep::Done => return output,
            }
        }
    }

    #[test]
    fn set_stream_matches_existing_wrapper_oracle() {
        let set: HashSetLit<i32> = [7, -3, 11, 7].into_iter().collect();
        let items = set.iter().map(CollectionSemanticHashItem::unary).collect();
        let actual = run(CollectionSemanticHashPda::set(items));
        let mut expected = TraceHasher::default();
        set.semantic_hash_into(&mut expected, Hash::hash);
        assert_eq!(actual.0, expected.0);
    }

    #[test]
    fn map_stream_matches_existing_wrapper_oracle() {
        let map: HashMapLit<i32, i32> = [(7, 9), (-3, 4), (11, -8)].into_iter().collect();
        let items = map
            .iter()
            .map(|(key, value)| CollectionSemanticHashItem::pair(key, value))
            .collect();
        let actual = run(CollectionSemanticHashPda::map(items));
        let mut expected = TraceHasher::default();
        map.semantic_hash_into(&mut expected, Hash::hash, Hash::hash);
        assert_eq!(actual.0, expected.0);
    }

    #[test]
    fn key_only_map_stream_matches_empty_value_callback() {
        let map: HashMapLit<i32, ()> = [(7, ()), (-3, ()), (11, ())].into_iter().collect();
        let items = map
            .keys()
            .map(CollectionSemanticHashItem::key_only)
            .collect();
        let actual = run(CollectionSemanticHashPda::map(items));
        let mut expected = TraceHasher::default();
        map.semantic_hash_into(&mut expected, Hash::hash, |_unit, _state| {});
        assert_eq!(actual.0, expected.0);
    }

    #[test]
    fn bag_stream_matches_existing_wrapper_oracle() {
        let bag: HashBag<i32> = [7, -3, 7, 11, -3, 7].into_iter().collect();
        let items = bag
            .iter()
            .map(|(value, count)| CollectionSemanticHashItem::repeated(value, count))
            .collect();
        let actual = run(CollectionSemanticHashPda::bag(bag.len(), items));
        let mut expected = TraceHasher::default();
        bag.semantic_hash_into(&mut expected, Hash::hash);
        assert_eq!(actual.0, expected.0);
    }
}
