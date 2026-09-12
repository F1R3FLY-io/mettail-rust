//! Native leaf hashing under the existing binding reservation callback.
//!
//! This is the concrete Fx2.1.3 leaf interpretation in
//! `AdmittedKeyHashExecution.v`, not another hashing algorithm. The original
//! `Hash::hash` receives the original `FxHasher`, including its seed and current
//! state. Only audited leaf types implement the sealed interface.

use crate::{Binder, BindingFailure, FltNode, FltTemplatePiece, OrdVar, Var};
use rustc_hash::FxHasher;
use std::hash::Hash;
use std::sync::Arc;

/// Failure before the native hash call; earlier inspection charges remain spent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KeyHashFailure<E> {
    UnsupportedProfile,
    Admission(BindingFailure<E>),
}

/// Whether this build matches the initial compiler/target profile.
///
/// The profile assumes the trusted standard, prebuilt core library. Custom
/// sysroots, rebuilt core and compiler wrappers are outside this contract;
/// this flag is not a toolchain attestation. Ordinary hashing is unaffected.
pub const CHECKED_FX_PROFILE_AVAILABLE: bool = cfg!(mettail_checked_fx_profile);

mod sealed {
    pub trait Leaf {
        // Called only after the constant-size inspection/arithmetic group is paid.
        fn execution_work<E>(
            &self,
            reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
        ) -> Result<usize, super::BindingFailure<E>>;
    }
}

/// Resource admission for audited fixed, String, binder and structural FLT leaves.
///
/// Successful execution returns the native call's logical work allowance,
/// excluding separately consumed inspection charges. Fixed/String/binder leaves
/// consume one inspection unit; FLTs consume three plus their hole and piece
/// counts, with admission before every iterator advance. The result is an
/// accounting value, not authority to execute another value or profile.
/// A caller retaining or reusing it must admit that storage and a separate
/// execution, against unchanged borrowed input. Hasher creation and `finish`
/// are caller operations and are not included.
///
/// Native execution borrows bytes and allocates no owned payload. These work
/// units count documented bounded source groups and byte reads, not CPU
/// instructions, semantic gas, allocator bytes or physical memory.
pub trait CheckedFxHashLeaf: Hash + sealed::Leaf {
    fn try_hash_fx<E>(
        &self,
        state: &mut FxHasher,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, KeyHashFailure<E>> {
        hash_leaf(self, state, reserve, CHECKED_FX_PROFILE_AVAILABLE)
    }
}

fn hash_leaf<T: Hash + sealed::Leaf + ?Sized, E>(
    value: &T,
    state: &mut FxHasher,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    supported: bool,
) -> Result<usize, KeyHashFailure<E>> {
    if !supported {
        return Err(KeyHashFailure::UnsupportedProfile);
    }
    reserve(1, 0).map_err(|error| KeyHashFailure::Admission(BindingFailure::Reservation(error)))?;
    let work = value
        .execution_work(reserve)
        .map_err(KeyHashFailure::Admission)?;
    reserve(work, 0)
        .map_err(|error| KeyHashFailure::Admission(BindingFailure::Reservation(error)))?;
    value.hash(state);
    Ok(work)
}

macro_rules! fixed_leaf {
    ($ty:ty, $work:expr) => {
        impl sealed::Leaf for $ty {
            fn execution_work<E>(
                &self,
                _: &mut impl FnMut(usize, usize) -> Result<(), E>,
            ) -> Result<usize, BindingFailure<E>> {
                Ok($work)
            }
        }
        impl CheckedFxHashLeaf for $ty {}
    };
}

// Leaf dispatch + accumulator, with one extra signed forwarding group for i64.
fixed_leaf!(i64, 3);
fixed_leaf!(bool, 2);
fixed_leaf!(u8, 2);
fixed_leaf!(usize, 2);

/// Fx2.1.3's byte loads include repeated short-input loads and an overlapping
/// final suffix. Each bulk iteration accounts separately for its probe, fixed
/// decode/update group and mix. The ten fixed groups cover leaf/String-to-str
/// dispatch, write_str, write(bytes), setup, terminal probe, short/suffix group,
/// final mix, accumulator, optional sentinel accumulator and final length xor.
/// Charging the sentinel and short-path probe covers both dependency feature
/// profiles without changing either profile's native hash stream.
fn string_execution_work(bytes: usize) -> Option<usize> {
    let (chunks, loads) = match bytes {
        0 => (0usize, 0usize),
        1..=3 => (0, 3),
        4..=7 => (0, 8),
        8..=16 => (0, 16),
        _ => {
            let chunks = bytes.checked_sub(1)? / 16;
            (chunks, chunks.checked_mul(16)?.checked_add(16)?)
        },
    };
    10usize
        .checked_add(chunks.checked_mul(3)?)?
        .checked_add(loads)
}

impl sealed::Leaf for String {
    fn execution_work<E>(
        &self,
        _: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, BindingFailure<E>> {
        string_execution_work(self.len()).ok_or(BindingFailure::SizeOverflow)
    }
}
impl CheckedFxHashLeaf for String {}

// AdmittedStructuralKeyHash.v: Moniker 0.5.0 hashes identities, not pretty names.
fn ordvar_execution_work(value: &OrdVar) -> usize {
    match &value.0 {
        Var::Free(_) => 14,
        Var::Bound(_) => 19,
    }
}

impl sealed::Leaf for OrdVar {
    fn execution_work<E>(
        &self,
        _: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, BindingFailure<E>> {
        Ok(ordvar_execution_work(self))
    }
}
impl CheckedFxHashLeaf for OrdVar {}
fixed_leaf!(Binder<String>, 8);

fn binder_vector_execution_work(width: usize) -> Option<usize> {
    width.checked_mul(10)?.checked_add(7)
}

impl sealed::Leaf for Vec<Binder<String>> {
    fn execution_work<E>(
        &self,
        _: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, BindingFailure<E>> {
        binder_vector_execution_work(self.len()).ok_or(BindingFailure::SizeOverflow)
    }
}
impl CheckedFxHashLeaf for Vec<Binder<String>> {}

fn add_work<E>(total: usize, more: usize) -> Result<usize, BindingFailure<E>> {
    total.checked_add(more).ok_or(BindingFailure::SizeOverflow)
}

fn string_work<E>(value: &str) -> Result<usize, BindingFailure<E>> {
    string_execution_work(value.len()).ok_or(BindingFailure::SizeOverflow)
}

// Borrow metadata only. The initial paid group covers this fixed-size root
// projection; each subsequent group covers next + fixed item metadata + checked
// accumulation. Actual native Hash remains the single whole call in hash_leaf.
fn flt_execution_work<E>(
    node: &FltNode,
    forwarding: usize,
    reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
) -> Result<usize, BindingFailure<E>> {
    let mut total = add_work(43, forwarding)?;
    total = add_work(total, ordvar_execution_work(&node.selector))?;
    total = add_work(total, string_work(&node.selector_name)?)?;
    total = add_work(total, string_work(&node.category)?)?;
    total = add_work(total, string_work(&node.open_src)?)?;
    total = add_work(total, string_work(&node.body_src)?)?;
    total = add_work(total, string_work(&node.close_src)?)?;
    let mut holes = node.holes.iter();
    loop {
        reserve(1, 0).map_err(BindingFailure::Reservation)?;
        let Some(hole) = holes.next() else { break };
        let category = match &hole.category {
            None => 5,
            Some(category) => add_work(6, string_work(category)?)?,
        };
        let item = add_work(add_work(18, string_work(&hole.name)?)?, category)?;
        total = add_work(total, item)?;
    }
    let mut pieces = node.pieces.iter();
    loop {
        reserve(1, 0).map_err(BindingFailure::Reservation)?;
        let Some(piece) = pieces.next() else { break };
        let item = match piece {
            FltTemplatePiece::Text { text, .. } => add_work(16, string_work(text)?)?,
            FltTemplatePiece::Hole { .. } => 20,
        };
        total = add_work(total, item)?;
    }
    Ok(total)
}

impl sealed::Leaf for FltNode {
    fn execution_work<E>(
        &self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, BindingFailure<E>> {
        flt_execution_work(self, 0, reserve)
    }
}
impl CheckedFxHashLeaf for FltNode {}

impl sealed::Leaf for Arc<FltNode> {
    fn execution_work<E>(
        &self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, BindingFailure<E>> {
        flt_execution_work(self.as_ref(), 2, reserve)
    }
}
impl CheckedFxHashLeaf for Arc<FltNode> {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::hash::Hasher;

    fn check<T: CheckedFxHashLeaf>(value: T, expected_work: usize) {
        check_inspections(value, expected_work, 1);
    }

    fn check_inspections<T: CheckedFxHashLeaf>(value: T, expected_work: usize, inspections: usize) {
        assert!(
            CHECKED_FX_PROFILE_AVAILABLE,
            "this correspondence gate requires the audited build profile"
        );
        for seed in [0, 1, usize::MAX] {
            let mut expected = FxHasher::with_seed(seed);
            // Nonempty initial state tests composition, not just standalone digest.
            29u8.hash(&mut expected);
            let initial = expected.clone();
            value.hash(&mut expected);
            let mut actual = initial.clone();
            let mut charges = Vec::new();
            let receipt = value
                .try_hash_fx(&mut actual, &mut |work, units| {
                    charges.push((work, units));
                    Ok::<_, usize>(())
                })
                .expect("admitted native hash");
            assert_eq!(receipt, expected_work);
            let mut expected_charges = vec![(1, 0); inspections];
            expected_charges.push((expected_work, 0));
            assert_eq!(charges, expected_charges);
            assert_eq!(actual.finish(), expected.finish());
            for stop in 0..=inspections {
                let mut actual = initial.clone();
                let mut seen = 0;
                let mut spent = 0;
                let failed = value.try_hash_fx(&mut actual, &mut |work, units| {
                    let current = seen;
                    seen += 1;
                    assert_eq!((work, units), expected_charges[current]);
                    if current == stop {
                        Err(stop)
                    } else {
                        spent += work;
                        Ok(())
                    }
                });
                assert_eq!(
                    failed,
                    Err(KeyHashFailure::Admission(BindingFailure::Reservation(stop)))
                );
                assert_eq!(seen, stop + 1);
                assert_eq!(spent, stop);
                assert_eq!(actual.finish(), initial.finish());
            }
            let exact = expected_work + inspections;
            for limit in [exact - 1, exact] {
                let mut actual = initial.clone();
                let mut remaining = limit;
                let result = value.try_hash_fx(&mut actual, &mut |work, units| {
                    assert_eq!(units, 0);
                    remaining = remaining.checked_sub(work).ok_or("budget")?;
                    Ok(())
                });
                if limit == exact - 1 {
                    assert_eq!(
                        result,
                        Err(KeyHashFailure::Admission(BindingFailure::Reservation("budget")))
                    );
                    assert_eq!(remaining, expected_work - 1);
                    assert_eq!(actual.finish(), initial.finish());
                } else {
                    assert_eq!(result, Ok(expected_work));
                    assert_eq!(remaining, 0);
                    assert_eq!(actual.finish(), expected.finish());
                }
            }
        }
    }

    #[test]
    #[cfg(mettail_checked_fx_profile)]
    fn fixed_and_string_calls_preserve_hashes_and_refuse_before_execution() {
        check(i64::MIN, 3);
        check(i64::MAX, 3);
        check(false, 2);
        check(true, 2);
        check(255u8, 2);
        check(usize::MAX, 2);
        for (bytes, work) in [
            (0, 10),
            (1, 13),
            (3, 13),
            (4, 18),
            (7, 18),
            (8, 26),
            (16, 26),
            (17, 45),
            (32, 45),
            (33, 64),
        ] {
            check("x".repeat(bytes), work);
        }
        check("λ".to_owned(), 13);
        check(
            "x".repeat(1_000_000),
            string_execution_work(1_000_000).expect("finite test envelope"),
        );
    }

    #[test]
    fn unknown_profile_has_no_charge_or_state_change() {
        let mut hasher = FxHasher::with_seed(91);
        let before = hasher.finish();
        let mut called = false;
        let result = hash_leaf(
            &37i64,
            &mut hasher,
            &mut |_, _| {
                called = true;
                Ok::<_, ()>(())
            },
            false,
        );
        assert_eq!(result, Err(KeyHashFailure::UnsupportedProfile));
        assert!(!called);
        assert_eq!(hasher.finish(), before);
    }

    #[test]
    fn string_envelope_arithmetic_never_wraps() {
        assert_eq!(string_execution_work(usize::MAX), None);
        assert_eq!(string_execution_work(usize::MAX - 15), None);
        for bytes in 0..4096 {
            let chunks = if bytes <= 16 { 0 } else { (bytes - 1) / 16 };
            let loads = if bytes == 0 {
                0
            } else if bytes < 4 {
                3
            } else if bytes < 8 {
                8
            } else if bytes <= 16 {
                16
            } else {
                16 * chunks + 16
            };
            assert_eq!(string_execution_work(bytes), Some(10 + 3 * chunks + loads));
        }
    }

    #[test]
    #[cfg(mettail_checked_fx_profile)]
    fn identities_ignore_hints_and_binder_vectors_admit_each_native_visit() {
        let mut free = crate::FreeVar::fresh_named("x".to_owned());
        for hint in [None, Some("λ".repeat(500_000))] {
            free.pretty_name = hint.clone();
            check(OrdVar(Var::Free(free.clone())), 14);
            check(
                OrdVar(Var::Bound(crate::BoundVar {
                    scope: moniker::ScopeOffset(u32::MAX),
                    binder: moniker::BinderIndex(u32::MAX),
                    pretty_name: hint,
                })),
                19,
            );
            check(Binder(free.clone()), 8);
        }
        let binder = Binder(crate::FreeVar::fresh_named("v".to_owned()));
        for width in [0, 1, 2, 1000] {
            check(vec![binder.clone(); width], 7 + 10 * width);
        }
        check(vec![binder, Binder(free)], 27);
    }

    fn empty_flt() -> FltNode {
        FltNode {
            selector: OrdVar(Var::Free(crate::FreeVar::fresh_named("s".to_owned()))),
            selector_name: String::new(),
            category: String::new(),
            open_src: String::new(),
            body_src: String::new(),
            holes: Vec::new(),
            pieces: Vec::new(),
            close_src: String::new(),
            bounds: crate::FltTemplateBounds::default(),
            position: 0,
        }
    }

    #[test]
    #[cfg(mettail_checked_fx_profile)]
    fn structural_flts_admit_every_metadata_step_before_original_hash() {
        // Raw carrier tests intentionally bypass template validation: claimed
        // bounds cannot replace actual strings/vectors in a native hash budget.
        check_inspections(empty_flt(), 107, 3);
        for index in 0..5 {
            let mut node = empty_flt();
            let fields = [
                &mut node.selector_name,
                &mut node.category,
                &mut node.open_src,
                &mut node.body_src,
                &mut node.close_src,
            ];
            *fields.into_iter().nth(index).expect("five string fields") = "x".repeat(33);
            check_inspections(node, 161, 3); // Replace S(0)=10 by S(33)=64.
        }
        let mut node = empty_flt();
        node.selector = OrdVar(Var::Bound(crate::BoundVar {
            scope: moniker::ScopeOffset(u32::MAX),
            binder: moniker::BinderIndex(u32::MAX),
            pretty_name: Some("ignored".repeat(10_000)),
        }));
        node.selector_name = "a".to_owned();
        node.category = "xxxx".to_owned();
        node.open_src = "x".repeat(8);
        node.body_src = "x".repeat(17);
        node.close_src = "λ".to_owned();
        let range = crate::FltSourceRange::new(usize::MAX, usize::MAX);
        node.holes = vec![
            crate::FltHole {
                id: crate::FltHoleId(u32::MAX),
                name: "".to_owned(),
                category: None,
                first_occurrence: range,
            },
            crate::FltHole {
                id: crate::FltHoleId(0),
                name: "λ".to_owned(),
                category: Some("xxxx".to_owned()),
                first_occurrence: range,
            },
        ];
        node.pieces = vec![
            FltTemplatePiece::Text { text: "x".repeat(33), range },
            FltTemplatePiece::Hole { id: crate::FltHoleId(u32::MAX), range },
        ];
        node.bounds = crate::FltTemplateBounds {
            source_bytes: usize::MAX,
            body_bytes: usize::MAX,
            piece_count: usize::MAX,
            hole_declarations: usize::MAX,
            hole_occurrences: usize::MAX,
        };
        node.position = usize::MAX;
        // Root=177; hole entries=33+55; piece entries=80+20.
        check_inspections(node.clone(), 365, 7);
        let shared = Arc::new(node);
        check_inspections(shared.clone(), 367, 7);
        assert_eq!(Arc::strong_count(&shared), 1);
        let mut state = FxHasher::default();
        shared
            .try_hash_fx(&mut state, &mut |_, _| {
                assert_eq!(Arc::strong_count(&shared), 1);
                Ok::<_, ()>(())
            })
            .expect("borrow-only Arc forwarding");
    }

    #[test]
    fn structural_cost_arithmetic_never_wraps() {
        assert_eq!(binder_vector_execution_work(0), Some(7));
        assert_eq!(binder_vector_execution_work(usize::MAX), None);
        let maximum_width = (usize::MAX - 7) / 10;
        assert!(binder_vector_execution_work(maximum_width).is_some());
        assert_eq!(binder_vector_execution_work(maximum_width + 1), None);
        assert_eq!(add_work::<()>(usize::MAX, 1), Err(BindingFailure::SizeOverflow));
        assert_eq!(add_work::<()>(usize::MAX, 0), Ok(usize::MAX));
    }
}
