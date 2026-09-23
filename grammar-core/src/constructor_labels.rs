//! Original implicit constructor-label selection, with frontend observations
//! and label construction supplied at the existing lazy call sites.
//!
//! No type parsing, Unicode table, or constructor validation is introduced.
//! ConstructorLabelProjection.v covers the scoped observation/callback boundary.

use crate::NativeType;

/// Apply the original first-scalar uppercase rule, then construct the Var label.
/// The constructor receives the complete uppercase prefix, without truncation.
pub fn generate_var_label<Label>(category: &str, construct: impl FnOnce(String) -> Label) -> Label {
    let first_letter = category
        .chars()
        .next()
        .unwrap_or('V')
        .to_uppercase()
        .collect::<String>();
    construct(first_letter)
}

/// Select the original literal label without eagerly observing the native type.
/// Byte vectors bypass native classification; only the chosen label is built.
pub fn generate_literal_label<Label>(
    is_byte_vector: impl FnOnce() -> bool,
    native_type: impl FnOnce() -> NativeType,
    construct: impl FnOnce(&'static str) -> Label,
) -> Label {
    // ★ The BYTE carrier is asked FIRST, because `NativeType` cannot see it.
    // `NativeType::from_syn_type` classifies by the last path segment, so `Vec<u8>` and
    // `Vec<Proc>` are both `VecCollection` and would both be labelled `ListLit`. A `Vec<u8>` is
    // not a collection of terms (see `native::is_byte_vector` for the full argument): its
    // surface is ONE literal, `b"deadbeef"`, and `u8` is not a category. Labelling it `ListLit`
    // put a scalar value into the collection Display path, which wrapped it in the EMPTY
    // delimiters a non-`as List` category declares — the measured `Bytes::…(vec![])` ⇒ `""`.
    if is_byte_vector() {
        return construct("BytesLit");
    }
    let nt = native_type();
    // Group integer-like (including `CanonicalBigInt`) before narrower classifiers
    // so `is_integer()` correctly covers arbitrary-precision ints.
    if nt.is_integer() {
        return construct("NumLit");
    }
    match nt {
        NativeType::Float32 | NativeType::Float64 => construct("FloatLit"),
        NativeType::Bool => construct("BoolLit"),
        NativeType::Str => construct("StringLit"),
        NativeType::CanonicalBigRat => construct("RatLit"),
        NativeType::CanonicalFixedPoint => construct("FixedLit"),
        // Collection wrappers: the variant label matches the collection's
        // surface kind. `Vec` is the list backing, `HashBag` the bag backing,
        // `HashMap`/`HashMapLit` the map backing.
        NativeType::VecCollection => construct("ListLit"),
        NativeType::HashBagCollection | NativeType::HashSetCollection => construct("BagLit"),
        NativeType::HashMapLitCollection | NativeType::HashMapCollection => construct("MapLit"),
        // Rholang 1.4 (main) collection wrappers — distinct surface kinds whose
        // variant labels must match enums.rs (CollectionCategory::Set/Pathmap →
        // "SetLit"/"PathmapLit"). These wrappers parse as `NativeType::Other`.
        NativeType::Other(ref s) if s == "HashSetLit" => construct("SetLit"),
        NativeType::Other(ref s) if s == "PathMapLit" => construct("PathmapLit"),
        NativeType::Other(_) => construct("Lit"), // Generic fallback
        // Unreachable: `is_integer()` above already returned for these.
        NativeType::Int8
        | NativeType::Int16
        | NativeType::Int32
        | NativeType::Int64
        | NativeType::Int128
        | NativeType::Isize
        | NativeType::UInt8
        | NativeType::UInt16
        | NativeType::UInt32
        | NativeType::UInt64
        | NativeType::UInt128
        | NativeType::Usize
        | NativeType::CanonicalBigInt => construct("NumLit"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    #[test]
    fn shared_constructor_label_byte_probe_suppresses_native_callback() {
        let trace = RefCell::new(Vec::new());
        let label = generate_literal_label(
            || {
                trace.borrow_mut().push("byte");
                true
            },
            || {
                trace.borrow_mut().push("native");
                panic!("byte carrier must skip native classification")
            },
            |label| {
                trace.borrow_mut().push("construct");
                label.to_string()
            },
        );
        assert_eq!(label, "BytesLit");
        assert_eq!(*trace.borrow(), ["byte", "construct"]);
    }

    #[test]
    fn shared_constructor_label_nonbyte_callbacks_keep_order_and_failure() {
        let trace = RefCell::new(Vec::new());
        let result = generate_literal_label(
            || {
                trace.borrow_mut().push("byte");
                false
            },
            || {
                trace.borrow_mut().push("native");
                NativeType::Other("HashSetLit".into())
            },
            |label| {
                trace.borrow_mut().push("construct");
                Err::<(), _>(label)
            },
        );
        assert_eq!(result, Err("SetLit"));
        assert_eq!(*trace.borrow(), ["byte", "native", "construct"]);
    }

    #[test]
    fn shared_constructor_label_integer_uses_one_selected_constructor() {
        let trace = RefCell::new(Vec::new());
        let label = generate_literal_label(
            || {
                trace.borrow_mut().push("byte");
                false
            },
            || {
                trace.borrow_mut().push("native");
                NativeType::CanonicalBigInt
            },
            |label| {
                trace.borrow_mut().push(label);
                label
            },
        );
        assert_eq!(label, "NumLit");
        assert_eq!(*trace.borrow(), ["byte", "native", "NumLit"]);
    }

    #[test]
    fn shared_constructor_label_var_keeps_unicode_expansion_and_empty_fallback() {
        for (source, expected) in [
            ("", "VVar"),
            ("ßuffix", "SSVar"),
            ("éclair", "ÉVar"),
            ("δelta", "ΔVar"),
            ("r#type", "RVar"),
        ] {
            let calls = std::cell::Cell::new(0);
            let label = generate_var_label(source, |prefix| {
                calls.set(calls.get() + 1);
                format!("{prefix}Var")
            });
            assert_eq!(label, expected, "{source}");
            assert_eq!(calls.get(), 1);
        }
    }
}
