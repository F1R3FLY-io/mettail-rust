use super::*;
use crate::OrdVar;
use moniker::{Binder, BinderIndex, BoundVar, FreeVar, ScopeOffset};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct CollisionKey(usize);

impl Hash for CollisionKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        0usize.hash(state);
    }
}

fn observe<T: Clone + Hash + Eq>(bag: &HashBag<T>, expected: &mut usize) {
    *expected = (*expected).max(bag.counts.capacity());
    assert_eq!(bag.historical_capacity(), *expected);
}

#[test]
fn history_tracks_observed_growth_not_multiplicity() {
    let mut bag = HashBag::new();
    let mut expected = 0;
    observe(&bag, &mut expected);
    bag.insert_n(0usize, 0);
    observe(&bag, &mut expected);
    assert_eq!(bag.counts.capacity(), 0);
    for key in 0..96 {
        if key % 2 == 0 {
            bag.insert(key);
        } else {
            bag.insert_n(key, 2);
        }
        observe(&bag, &mut expected);
    }
    let before = expected;
    bag.insert_n(0, 10_000);
    observe(&bag, &mut expected);
    assert_eq!(expected, before);
    assert!(!bag.remove(&999));
    observe(&bag, &mut expected);
    assert!(bag.remove(&0));
    observe(&bag, &mut expected);
}

#[test]
fn binding_found_after_reserve_records_growth_without_a_new_key() {
    let mut bag = HashBag::new();
    let mut expected = 0;
    bag.insert_binding_entry(0usize, 1);
    observe(&bag, &mut expected);
    let initial_capacity = bag.counts.capacity();
    for key in 1..initial_capacity {
        bag.insert_binding_entry(key, 1);
        observe(&bag, &mut expected);
    }
    let width = bag.counts.len();
    assert_eq!(width, initial_capacity);
    bag.insert_binding_entry(0, 9);
    observe(&bag, &mut expected);
    assert_eq!(bag.counts.len(), width);
    assert_eq!(bag.counts.get(&0), Some(&9));
    assert!(bag.counts.capacity() > initial_capacity);
}

#[test]
fn collisions_and_tombstones_do_not_erase_history_or_clone_allocation() {
    let mut bag = HashBag::new();
    let mut expected = 0;
    for key in 0..128 {
        bag.insert(CollisionKey(key));
        observe(&bag, &mut expected);
    }
    let high = expected;
    let mut saw_capacity_decrease = false;
    for key in 0..128 {
        let before = bag.counts.capacity();
        assert!(bag.remove(&CollisionKey(key)));
        saw_capacity_decrease |= bag.counts.capacity() < before;
        observe(&bag, &mut expected);
        assert_eq!(expected, high);
        if key == 63 || key == 127 {
            let cloned = bag.clone();
            assert_eq!(cloned, bag);
            assert_eq!(cloned.counts.capacity(), bag.counts.capacity());
            assert_eq!(cloned.historical_capacity(), high);
        }
    }
    assert!(saw_capacity_decrease, "collision fixture must create tombstones");
    assert!(bag.counts.is_empty());
    assert!(bag.counts.capacity() > 0, "empty allocation is not the singleton");
    let fresh: HashBag<CollisionKey> = HashBag::new();
    assert_eq!(fresh.clone().historical_capacity(), 0);
}

#[test]
fn binding_rebuild_resets_history_but_preserves_first_key_last_count_and_total() {
    let first: FreeVar<String> = FreeVar::fresh_named("first");
    let mut last = first.clone();
    last.pretty_name = Some("last".to_owned());
    let first = OrdVar(Var::Free(first));
    let last = OrdVar(Var::Free(last));
    let mut source = HashBag::new();
    source.insert_n(first.clone(), 7);
    let extras: Vec<_> = (0..64)
        .map(|_| OrdVar(Var::Free(FreeVar::fresh_named("extra"))))
        .collect();
    for key in &extras {
        source.insert(key.clone());
    }
    for key in &extras {
        assert!(source.remove(key));
    }
    let old_history = source.historical_capacity();
    for final_count in [0, 5] {
        let entries = [(first.clone(), 2), (last.clone(), final_count)];
        let mut native = HashMap::<_, usize, BuildHasherDefault<FxHasher>>::default();
        let mut expected_history = 0;
        for (key, count) in entries.clone() {
            native.insert(key, count);
            expected_history = expected_history.max(native.capacity());
        }
        let rebuilt = source.rebuild_binding_entries(entries);
        assert_eq!(rebuilt.counts, native);
        assert_eq!(rebuilt.len(), 7);
        assert_eq!(rebuilt.distinct_len(), 1);
        assert_eq!(rebuilt.historical_capacity(), expected_history);
        assert!(rebuilt.historical_capacity() < old_history);
        let (key, count) = rebuilt.iter().next().expect("zero counts remain stored");
        assert_eq!(count, final_count);
        match &key.0 {
            Var::Free(value) => assert_eq!(value.pretty_name.as_deref(), Some("first")),
            Var::Bound(_) => panic!("binding recipe does not transform the supplied free key"),
        }
    }
    let empty = source.rebuild_binding_entries(std::iter::empty());
    assert_eq!(empty.historical_capacity(), 0);
    assert_eq!(empty.len(), 7);
    assert_eq!(source.historical_capacity(), old_history);
}

#[test]
fn all_bound_term_replacements_reset_large_and_empty_backing_tables() {
    for operation in 0..3 {
        let variables: Vec<FreeVar<String>> =
            (0..64).map(|_| FreeVar::fresh_named("entry")).collect();
        let binders: Vec<_> = variables.iter().cloned().map(Binder).collect();
        let keys: Vec<_> = variables
            .iter()
            .enumerate()
            .map(|(index, variable)| {
                if operation == 1 {
                    OrdVar(Var::Bound(BoundVar {
                        scope: ScopeOffset(0),
                        binder: BinderIndex(index as u32),
                        pretty_name: Some("bound".to_owned()),
                    }))
                } else {
                    OrdVar(Var::Free(variable.clone()))
                }
            })
            .collect();
        let mut bag: HashBag<_> = keys.iter().cloned().collect();
        for key in &keys[1..] {
            assert!(bag.remove(key));
        }
        let old_history = bag.historical_capacity();
        for empty in [false, true] {
            if empty {
                let remaining = bag
                    .iter()
                    .next()
                    .expect("one retained key before emptying")
                    .0
                    .clone();
                assert!(bag.remove(&remaining));
                assert!(bag.counts.capacity() > 0);
            }
            match operation {
                0 => bag.close_term(ScopeState::new(), &binders),
                1 => bag.open_term(ScopeState::new(), &binders),
                _ => bag.visit_mut_vars(&mut |_| {}),
            }
            assert_eq!(bag.distinct_len(), usize::from(!empty));
            assert_eq!(bag.historical_capacity(), bag.counts.capacity());
            assert!(bag.historical_capacity() < old_history);
            if empty {
                assert_eq!(bag.historical_capacity(), 0);
            }
        }
    }
}

#[test]
fn variable_identity_collapse_retains_native_last_count_with_fresh_history() {
    let mut bag = HashBag::new();
    for count in 1..=64 {
        bag.insert_n(OrdVar(Var::Free(FreeVar::fresh_named("input"))), count);
    }
    let old_history = bag.historical_capacity();
    let original_total = bag.len();
    let last_count = bag
        .iter()
        .last()
        .expect("nonempty source before identity collapse")
        .1;
    let replacement = Var::Free(FreeVar::fresh_named("collapsed"));
    bag.visit_mut_vars(&mut |variable| *variable = replacement.clone());
    assert_eq!(bag.distinct_len(), 1);
    assert_eq!(bag.len(), original_total);
    assert_eq!(bag.iter().next().expect("one retained collapsed key").1, last_count);
    assert_eq!(bag.historical_capacity(), bag.counts.capacity());
    assert!(bag.historical_capacity() < old_history);
}

#[derive(Default)]
struct HashStream(Vec<u8>);

impl Hasher for HashStream {
    fn finish(&self) -> u64 {
        0
    }

    fn write(&mut self, bytes: &[u8]) {
        self.0.extend_from_slice(bytes);
    }
}

#[test]
fn equal_bags_with_different_real_histories_keep_native_hash_eq_and_order() {
    let mut large = HashBag::new();
    for key in 0..64 {
        large.insert(CollisionKey(key));
    }
    for key in 1..64 {
        assert!(large.remove(&CollisionKey(key)));
    }
    let small: HashBag<_> = [CollisionKey(0)].into_iter().collect();
    assert!(large.historical_capacity() > small.historical_capacity());
    assert_eq!(large, small);
    assert_eq!(large.cmp(&small), Ordering::Equal);
    let mut large_stream = HashStream::default();
    let mut small_stream = HashStream::default();
    large.hash(&mut large_stream);
    small.hash(&mut small_stream);
    assert_eq!(large_stream.0, small_stream.0);
    assert_eq!(large_stream.0.len(), 2 * std::mem::size_of::<usize>() + 4 * 8);
}
