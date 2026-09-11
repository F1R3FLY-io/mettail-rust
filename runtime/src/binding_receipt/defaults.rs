//! Source-backed default contracts for the runtime's native carriers.
//!
//! `NativeWork` counts a bounded native construction/cleanup call, not CPU
//! instructions. `NativeRecord` counts one selected payload record, plus any
//! separately retained allocation. Records are logical retention units, not
//! allocator bytes. `OwnedByte` counts separately handled dynamic byte payload;
//! zero bytes does not mean zero allocated memory.
//!
//! Empty collections construct no elements and invoke no element callbacks.
//! The numeric defaults use the pinned num-bigint zero/one inline forms and
//! retain an outer Box. Their Copy handles do not free that allocation.
//! Extraction/iteration/replacement costs belong to the generated field site.

use super::{BindingDefaultReceipt, Counts, DefaultReceipt, Event, ReceiptOverflow};
use crate::{
    CanonicalBigInt, CanonicalBigRat, CanonicalFixedPoint, CanonicalFloat32, CanonicalFloat64,
    HashBag, HashMapLit, HashSetLit, PathMapLit, ReadZipperLit, WriteZipperLit,
};
use std::hash::Hash;
use std::sync::Arc;

const INLINE_VALUE: DefaultReceipt = DefaultReceipt {
    construction: native_construction(1),
    field_glue: Counts::ZERO,
};

const EMPTY_CONTAINER: DefaultReceipt = DefaultReceipt {
    construction: native_construction(1),
    field_glue: Counts::singleton(Event::NativeWork, 1),
};

// One payload record and one separately retained Box. No dynamic digit buffer
// is needed by the pinned zero/one values. The handle itself has no Drop glue.
const RETAINED_NUMERIC: DefaultReceipt = DefaultReceipt {
    construction: native_construction(2),
    field_glue: Counts::ZERO,
};

const fn native_construction(records: usize) -> Counts {
    let mut counts = Counts::ZERO;
    counts.0[Event::NativeWork as usize] = 1;
    counts.0[Event::NativeRecord as usize] = records;
    counts
}

macro_rules! inline_defaults {
    ($($ty:ty),+ $(,)?) => {$(
        impl BindingDefaultReceipt for $ty {
            const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow> = Ok(INLINE_VALUE);
        }
    )+};
}

inline_defaults!(
    (),
    bool,
    char,
    i8,
    i16,
    i32,
    i64,
    i128,
    isize,
    u8,
    u16,
    u32,
    u64,
    u128,
    usize,
    f32,
    f64,
    CanonicalFloat32,
    CanonicalFloat64,
);

impl BindingDefaultReceipt for String {
    const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow> = Ok(EMPTY_CONTAINER);
}

impl<T> BindingDefaultReceipt for Vec<T> {
    const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow> = Ok(EMPTY_CONTAINER);
}

impl<T> BindingDefaultReceipt for Option<T> {
    const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow> = Ok(EMPTY_CONTAINER);
}

impl<T: Clone + Hash + Eq> BindingDefaultReceipt for HashBag<T> {
    const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow> = Ok(EMPTY_CONTAINER);
}

impl<T> BindingDefaultReceipt for HashSetLit<T> {
    const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow> = Ok(EMPTY_CONTAINER);
}

impl<K, V> BindingDefaultReceipt for HashMapLit<K, V> {
    const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow> = Ok(EMPTY_CONTAINER);
}

impl<K, V> BindingDefaultReceipt for PathMapLit<K, V> {
    const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow> = Ok(EMPTY_CONTAINER);
}

impl BindingDefaultReceipt for CanonicalBigInt {
    const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow> = Ok(RETAINED_NUMERIC);
}

impl BindingDefaultReceipt for CanonicalBigRat {
    const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow> = Ok(RETAINED_NUMERIC);
}

impl BindingDefaultReceipt for CanonicalFixedPoint {
    // canonical_fixed_point::default constructs a BigInt default and then the
    // fixed pair. Both handles are Copy; neither introduces deallocation glue.
    const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow> =
        RETAINED_NUMERIC.checked_add(INLINE_VALUE);
}

const fn zipper_default() -> Result<DefaultReceipt, ReceiptOverflow> {
    // zipper_lit::default constructs PathMapLit::Empty, an empty focus Vec,
    // then their product. This creates no key/value defaults.
    let fields = match EMPTY_CONTAINER.checked_add(EMPTY_CONTAINER) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    fields.checked_add(INLINE_VALUE)
}

impl<K, V> BindingDefaultReceipt for ReadZipperLit<K, V> {
    const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow> = zipper_default();
}

impl<K, V> BindingDefaultReceipt for WriteZipperLit<K, V> {
    const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow> = zipper_default();
}

const fn arc_default(
    inner: Result<DefaultReceipt, ReceiptOverflow>,
) -> Result<DefaultReceipt, ReceiptOverflow> {
    let inner = match inner {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    // AllocateArc supplies the wrapper's construction/record event. A fresh
    // default Arc is the sole strong owner. CheckArcOwner here denotes Arc's
    // last-strong-owner check during Drop, not a call to Arc::into_inner.
    let construction = match inner
        .construction
        .checked_add(Counts::singleton(Event::AllocateArc, 1))
    {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let field_glue = match inner.field_glue.checked_add(Counts::ARC_RELEASE) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok(DefaultReceipt { construction, field_glue })
}

impl<T: BindingDefaultReceipt> BindingDefaultReceipt for Arc<T> {
    const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow> =
        arc_default(T::DEFAULT_RECEIPT);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binding_receipt::{default_field_local, default_local_for, LocalReceipt};

    // No Default/Clone/Hash/Drop behavior may be required from empty elements.
    struct NoDefault;

    #[test]
    fn empty_carriers_need_no_element_default() {
        fn receipt<T: BindingDefaultReceipt>() -> DefaultReceipt {
            T::DEFAULT_RECEIPT.expect("empty native receipt")
        }
        assert_eq!(receipt::<Vec<NoDefault>>(), EMPTY_CONTAINER);
        assert_eq!(receipt::<Option<NoDefault>>(), EMPTY_CONTAINER);
        assert_eq!(receipt::<HashSetLit<NoDefault>>(), EMPTY_CONTAINER);
        assert_eq!(receipt::<HashMapLit<NoDefault, NoDefault>>(), EMPTY_CONTAINER);
        assert_eq!(receipt::<PathMapLit<NoDefault, NoDefault>>(), EMPTY_CONTAINER);
        assert_eq!(
            receipt::<ReadZipperLit<NoDefault, NoDefault>>(),
            zipper_default().expect("zipper receipt")
        );
        assert_eq!(
            receipt::<WriteZipperLit<NoDefault, NoDefault>>(),
            zipper_default().expect("zipper receipt")
        );
        assert!(Vec::<NoDefault>::default().is_empty());
        assert!(Option::<NoDefault>::default().is_none());
        assert!(HashSetLit::<NoDefault>::default().is_empty());
        assert!(HashMapLit::<NoDefault, NoDefault>::default().is_empty());
        assert_eq!(PathMapLit::<NoDefault, NoDefault>::default().mode(), crate::PathMapMode::Empty);
    }

    #[test]
    fn scalar_and_numeric_defaults_preserve_their_actual_values() {
        assert_eq!(i64::DEFAULT_RECEIPT, Ok(INLINE_VALUE));
        assert_eq!(CanonicalFloat32::DEFAULT_RECEIPT, Ok(INLINE_VALUE));
        assert_eq!(CanonicalFloat64::DEFAULT_RECEIPT, Ok(INLINE_VALUE));
        assert_eq!(CanonicalBigInt::DEFAULT_RECEIPT, Ok(RETAINED_NUMERIC));
        assert_eq!(CanonicalBigRat::DEFAULT_RECEIPT, Ok(RETAINED_NUMERIC));
        let fixed = CanonicalFixedPoint::DEFAULT_RECEIPT.expect("fixed default receipt");
        assert_eq!(fixed.construction.get(Event::NativeRecord), 3);
        assert_eq!(fixed.construction.get(Event::NativeWork), 2);
        assert_eq!(fixed.field_glue, Counts::ZERO);
        assert_eq!(CanonicalBigInt::default().get(), &num_bigint::BigInt::from(0));
        let rational = CanonicalBigRat::default();
        assert_eq!(rational.get().numer(), &num_bigint::BigInt::from(0));
        assert_eq!(rational.get().denom(), &num_bigint::BigInt::from(1));
        let fixed = CanonicalFixedPoint::default();
        assert_eq!(fixed.unscaled(), &num_bigint::BigInt::from(0));
        assert_eq!(fixed.places(), 0);
        for receipt in [INLINE_VALUE, RETAINED_NUMERIC, EMPTY_CONTAINER] {
            assert_eq!(receipt.construction.get(Event::OwnedByte), 0);
        }
    }

    // The spelling is deliberately misleading. Only the implemented Rust trait
    // determines its cost, never a suffix classification.
    struct ForeignBigInt;
    impl Default for ForeignBigInt {
        fn default() -> Self {
            panic!("receipt inference must not call Default")
        }
    }
    impl BindingDefaultReceipt for ForeignBigInt {
        const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow> = Ok(DefaultReceipt {
            construction: Counts::singleton(Event::NativeRecord, 7),
            field_glue: Counts::ZERO,
        });
    }
    enum InferenceFixture {
        Payload(ForeignBigInt),
        Pair(ForeignBigInt, Vec<NoDefault>),
    }
    const INFERRED: Result<LocalReceipt, ReceiptOverflow> =
        default_local_for(InferenceFixture::Payload);
    const FIELD: Result<LocalReceipt, ReceiptOverflow> =
        default_field_local(|value: &InferenceFixture| match value {
            InferenceFixture::Pair(_, field) => field,
            InferenceFixture::Payload(_) => panic!("projection must not execute"),
        });

    #[test]
    fn type_inference_uses_nonexecuted_constructors_and_projections() {
        assert_eq!(
            INFERRED
                .expect("actual payload contract")
                .construction
                .get(Event::NativeRecord),
            7
        );
        assert_eq!(FIELD, Ok(EMPTY_CONTAINER.into_local()));
        let value = InferenceFixture::Pair(ForeignBigInt, Vec::new());
        assert!(matches!(value, InferenceFixture::Pair(_, _)));
    }

    struct OverflowingDefault;
    impl Default for OverflowingDefault {
        fn default() -> Self {
            panic!("overflow must propagate without construction")
        }
    }
    impl BindingDefaultReceipt for OverflowingDefault {
        const DEFAULT_RECEIPT: Result<DefaultReceipt, ReceiptOverflow> = Ok(DefaultReceipt {
            construction: Counts::singleton(Event::AllocateArc, usize::MAX),
            field_glue: Counts::ZERO,
        });
    }

    #[test]
    fn arc_defaults_compose_once_and_preserve_overflow() {
        let receipt = Arc::<String>::DEFAULT_RECEIPT.expect("native Arc default receipt");
        assert_eq!(receipt.construction.get(Event::NativeWork), 1);
        assert_eq!(receipt.construction.get(Event::AllocateArc), 1);
        assert_eq!(receipt.field_glue.get(Event::NativeWork), 1);
        assert_eq!(receipt.field_glue.get(Event::ReleaseFieldArc), 1);
        assert_eq!(receipt.field_glue.get(Event::CheckArcOwner), 1);
        assert_eq!(
            Arc::<OverflowingDefault>::DEFAULT_RECEIPT,
            Err(ReceiptOverflow { event: Event::AllocateArc })
        );
        let overflow = DefaultReceipt {
            construction: Counts::ZERO,
            field_glue: Counts::singleton(Event::NativeWork, usize::MAX),
        };
        assert_eq!(
            overflow.checked_add(EMPTY_CONTAINER),
            Err(ReceiptOverflow { event: Event::NativeWork })
        );
    }
}
