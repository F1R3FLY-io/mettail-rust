//! Native fixed/String hashing under the existing binding reservation callback.
//!
//! This is the concrete Fx2.1.3 leaf interpretation in
//! `AdmittedKeyHashExecution.v`, not another hashing algorithm. The original
//! `Hash::hash` receives the original `FxHasher`, including its seed and current
//! state. Only audited leaf types implement the sealed interface.

use crate::BindingFailure;
use rustc_hash::FxHasher;
use std::hash::Hash;

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
        fn execution_work(&self) -> Option<usize>;
    }
}

/// Resource admission for the five audited fixed/String native leaf types.
///
/// Successful execution returns the native call's logical work allowance,
/// excluding the separately consumed one-unit inspection charge. It is an
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
        .execution_work()
        .ok_or(KeyHashFailure::Admission(BindingFailure::SizeOverflow))?;
    reserve(work, 0)
        .map_err(|error| KeyHashFailure::Admission(BindingFailure::Reservation(error)))?;
    value.hash(state);
    Ok(work)
}

macro_rules! fixed_leaf {
    ($ty:ty, $work:expr) => {
        impl sealed::Leaf for $ty {
            fn execution_work(&self) -> Option<usize> {
                Some($work)
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
    fn execution_work(&self) -> Option<usize> {
        string_execution_work(self.len())
    }
}
impl CheckedFxHashLeaf for String {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::hash::Hasher;

    fn check<T: CheckedFxHashLeaf>(value: T, expected_work: usize) {
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
            assert_eq!(charges, [(1, 0), (expected_work, 0)]);
            assert_eq!(actual.finish(), expected.finish());
            for stop in 0..2 {
                let mut actual = initial.clone();
                let mut seen = 0;
                let failed = value.try_hash_fx(&mut actual, &mut |_, _| {
                    let current = seen;
                    seen += 1;
                    if current == stop {
                        Err(stop)
                    } else {
                        Ok(())
                    }
                });
                assert_eq!(
                    failed,
                    Err(KeyHashFailure::Admission(BindingFailure::Reservation(stop)))
                );
                assert_eq!(seen, stop + 1);
                assert_eq!(actual.finish(), initial.finish());
            }
            for limit in [expected_work, expected_work + 1] {
                let mut actual = initial.clone();
                let mut remaining = limit;
                let result = value.try_hash_fx(&mut actual, &mut |work, units| {
                    assert_eq!(units, 0);
                    remaining = remaining.checked_sub(work).ok_or("budget")?;
                    Ok(())
                });
                if limit == expected_work {
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
}
