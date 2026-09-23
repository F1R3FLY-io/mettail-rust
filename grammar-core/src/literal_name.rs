//! Original literal token-name selection over borrowed declarations.
//!
//! Equality is the source name's equality, not its rendered spelling. Constructors
//! receive the original literal occurrence, so frontend-specific identity/span
//! behavior stays with the frontend. Runtime alias admission is a separate policy.

use crate::NativeKind;

/// Select the original parser's standard token name, or clone its original name.
///
/// The first equal declaration wins even when it has no native type. Native
/// classification and constructors are lazy at their original iterator sites.
/// This is the selector modeled by `LiteralNameProjection`; it does not validate
/// declarations or change the caller's token metadata/order.
pub fn normalize_literal_name<'a, C, Name, Native, Output>(
    original: &Name,
    categories: &'a [C],
    mut category_name: impl FnMut(&'a C) -> &'a Name,
    mut native_type: impl FnMut(&'a C) -> Option<&'a Native>,
    mut native_kind: impl FnMut(&'a Native) -> NativeKind,
    construct_standard: impl FnOnce(&'static str, &Name) -> Output,
    clone_original: impl FnOnce(&Name) -> Output,
) -> Output
where
    Name: PartialEq + ?Sized + 'a,
    Native: ?Sized + 'a,
{
    categories
        .iter()
        .find(|category| category_name(category) == original)
        .and_then(|category| native_type(category))
        .and_then(|native| native_kind(native).standard_token_variant())
        .map(|variant| construct_standard(variant, original))
        .unwrap_or_else(|| clone_original(original))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    #[derive(Clone, Debug)]
    struct Name {
        class: u32,
        spelling: &'static str,
        span: usize,
    }

    impl PartialEq for Name {
        fn eq(&self, other: &Self) -> bool {
            self.class == other.class
        }
    }

    struct Category {
        id: usize,
        name: Name,
        native: Option<NativeKind>,
    }

    fn select(original: &Name, categories: &[Category]) -> (Name, Vec<String>) {
        let trace = RefCell::new(Vec::new());
        let expected_original = original;
        let selected = normalize_literal_name(
            original,
            categories,
            |category| {
                trace.borrow_mut().push(format!("name:{}", category.id));
                &category.name
            },
            |category| {
                trace.borrow_mut().push(format!("native:{}", category.id));
                category.native.as_ref()
            },
            |kind| {
                trace.borrow_mut().push(format!("kind:{kind:?}"));
                *kind
            },
            |variant, original| {
                trace.borrow_mut().push(format!("construct:{variant}"));
                assert!(std::ptr::eq(original, expected_original));
                Name {
                    class: original.class,
                    spelling: variant,
                    span: original.span,
                }
            },
            |original| {
                trace.borrow_mut().push("clone".to_owned());
                assert!(std::ptr::eq(original, expected_original));
                original.clone()
            },
        );
        (selected, trace.into_inner())
    }

    #[test]
    fn literal_name_neutral_uses_source_equality_and_original_occurrence() {
        let original = Name { class: 7, spelling: "r#Wanted", span: 90 };
        let categories = [
            Category {
                id: 0,
                name: Name { class: 8, spelling: "r#Wanted", span: 10 },
                native: Some(NativeKind::Float64),
            },
            Category {
                id: 1,
                name: Name {
                    class: 7,
                    spelling: "Different",
                    span: 20,
                },
                native: Some(NativeKind::Int32),
            },
            Category {
                id: 2,
                name: original.clone(),
                native: Some(NativeKind::Bool),
            },
        ];
        let (selected, trace) = select(&original, &categories);
        assert_eq!(selected.spelling, "Integer");
        assert_eq!(selected.span, 90);
        assert_eq!(trace, ["name:0", "name:1", "native:1", "kind:Int32", "construct:Integer"]);
    }

    #[test]
    fn literal_name_neutral_first_match_and_fallback_gates_are_lazy() {
        let original = Name {
            class: 7,
            spelling: "r#Original",
            span: 90,
        };
        let (missing, missing_trace) = select(&original, &[]);
        assert_eq!(missing.spelling, original.spelling);
        assert_eq!(missing.span, original.span);
        assert_eq!(missing_trace, ["clone"]);
        for native in [None, Some(NativeKind::Other), Some(NativeKind::CanonicalBigInt)] {
            let categories = [
                Category { id: 0, name: original.clone(), native },
                Category {
                    id: 1,
                    name: original.clone(),
                    native: Some(NativeKind::Int32),
                },
            ];
            let (selected, trace) = select(&original, &categories);
            assert_eq!(selected.spelling, original.spelling);
            assert_eq!(selected.span, original.span);
            let mut expected = vec!["name:0".to_owned(), "native:0".to_owned()];
            if let Some(kind) = native {
                expected.push(format!("kind:{kind:?}"));
            }
            expected.push("clone".to_owned());
            assert_eq!(trace, expected);
        }
    }
}
