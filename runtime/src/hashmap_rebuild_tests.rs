use super::*;
use crate::{binding_receipt::BindingCharge, BindingFailure};
use std::cell::Cell;
use std::rc::Rc;

#[derive(Clone, Debug)]
struct Key {
    identity: usize,
    diagnostic: usize,
    hashes: Rc<Cell<usize>>,
    comparisons: Rc<Cell<usize>>,
}

impl PartialEq for Key {
    fn eq(&self, other: &Self) -> bool {
        self.comparisons.set(self.comparisons.get() + 1);
        self.identity == other.identity
    }
}
impl Eq for Key {}
impl Hash for Key {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hashes.set(self.hashes.get() + 1);
        0usize.hash(state);
    }
}

fn fixture(
    width: usize,
) -> (HashMapLit<Key, usize>, Vec<(Key, usize)>, Rc<Cell<usize>>, Rc<Cell<usize>>) {
    let hashes = Rc::new(Cell::new(0));
    let comparisons = Rc::new(Cell::new(0));
    let mut source = HashMapLit::new();
    let mut entries = Vec::new();
    for index in 0..width {
        let key = Key {
            identity: index,
            diagnostic: index,
            hashes: Rc::clone(&hashes),
            comparisons: Rc::clone(&comparisons),
        };
        source.insert(key.clone(), index);
        entries.push((Key { identity: index % 3, ..key }, 100 + index));
    }
    hashes.set(0);
    comparisons.set(0);
    (source, entries, hashes, comparisons)
}

fn rebuild<E, R: FnMut(usize, usize) -> Result<(), E>>(
    source: &HashMapLit<Key, usize>,
    entries: Vec<(Key, usize)>,
    reserve: &mut R,
) -> Result<HashMapLit<Key, usize>, BindingFailure<E>> {
    source.try_rebuild_entries_with(
        entries,
        reserve,
        |_, reserve| {
            crate::reserve_binding_parts(1, 0, 0, reserve)?;
            Ok(BindingCharge::new(7, 1, 3).expect("test hash receipt"))
        },
        |_, _, reserve| {
            crate::reserve_binding_parts(1, 0, 0, reserve)?;
            Ok(BindingCharge::new(5, 1, 2).expect("test equality receipt"))
        },
    )
}

fn pairs(map: &HashMapLit<Key, usize>) -> Vec<(usize, usize, usize)> {
    map.iter()
        .map(|(key, value)| (key.identity, key.diagnostic, *value))
        .collect()
}

#[test]
fn ordered_rebuild_retains_first_key_last_value_without_structural_rehash() {
    if !crate::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
        return;
    }
    for width in [0, 1, 3, 4, 7, 8, 14, 15, 28, 29] {
        let (source, entries, hashes, comparisons) = fixture(width);
        let mut expected = HashMapLit::new();
        for (key, value) in entries.clone() {
            expected.insert(key, value);
        }
        let expected = pairs(&expected);
        hashes.set(0);
        comparisons.set(0);
        let actual = rebuild(&source, entries, &mut |_, _| Ok::<_, ()>(())).expect("admitted map");
        assert_eq!(pairs(&actual), expected);
        assert_eq!(hashes.get(), width, "only one incoming hash per insertion, no retained rehash");
        assert_eq!(source.len(), width);
        assert_eq!(
            source
                .iter()
                .map(|(key, _)| key.diagnostic)
                .collect::<Vec<_>>(),
            (0..width).collect::<Vec<_>>()
        );
    }
}

#[test]
fn every_refused_admission_stops_before_the_next_native_operation() {
    if !crate::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
        return;
    }
    let (source, entries, hashes, comparisons) = fixture(7);
    let mut trace = Vec::new();
    rebuild(&source, entries.clone(), &mut |work, units| {
        trace.push((work, units, hashes.get(), comparisons.get()));
        Ok::<_, usize>(())
    })
    .expect("baseline");
    for cut in 0..trace.len() {
        hashes.set(0);
        comparisons.set(0);
        let mut seen = Vec::new();
        let result = rebuild(&source, entries.clone(), &mut |work, units| {
            let index = seen.len();
            seen.push((work, units, hashes.get(), comparisons.get()));
            if index == cut {
                Err(cut)
            } else {
                Ok(())
            }
        });
        assert!(matches!(result, Err(BindingFailure::Reservation(index)) if index == cut));
        assert_eq!(seen, trace[..=cut]);
        assert_eq!((hashes.get(), comparisons.get()), (trace[cut].2, trace[cut].3));
        assert_eq!(source.len(), 7);
    }
}

#[test]
fn exact_and_one_under_work_or_storage_are_atomic_and_width_mismatch_rejects() {
    if !crate::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
        return;
    }
    let (source, entries, hashes, _) = fixture(4);
    let mut total = (0, 0);
    rebuild(&source, entries.clone(), &mut |work, units| {
        total.0 += work;
        total.1 += units;
        Ok::<_, ()>(())
    })
    .expect("baseline");
    for (work_limit, unit_limit, succeeds) in [
        (total.0, total.1, true),
        (total.0 - 1, total.1, false),
        (total.0, total.1 - 1, false),
        (0, total.1, false),
    ] {
        let mut used = (0, 0);
        let result = rebuild(&source, entries.clone(), &mut |work, units| {
            if work > work_limit - used.0 || units > unit_limit - used.1 {
                return Err(());
            }
            used.0 += work;
            used.1 += units;
            Ok(())
        });
        assert_eq!(result.is_ok(), succeeds);
        assert!(used.0 <= work_limit && used.1 <= unit_limit);
    }
    hashes.set(0);
    assert!(matches!(
        rebuild(&source, Vec::new(), &mut |_, _| Ok::<_, ()>(())),
        Err(BindingFailure::InvalidCollectionInput(_))
    ));
    assert_eq!(hashes.get(), 0);
}
