//! Original category-local AST variant assembly, shared with macro term ops.
//!
//! Source classifiers remain callbacks at their original observation sites.
//! Neither WPDA rule coordinates nor semantic operator IDs are variant tags.
//! `OwnedSemanticVisitor` records the callback/order correspondence.

pub fn complete_category_variants<V>(
    mut variants: Vec<V>,
    is_var: impl FnMut(&V) -> bool,
    implicit_var: impl FnOnce() -> bool,
    make_var: impl FnOnce() -> V,
    native_literal: impl FnOnce(&mut Vec<V>),
    hol_variants: impl FnOnce(&mut Vec<V>),
) -> Vec<V> {
    let has_var = variants.iter().any(is_var);
    if !has_var && implicit_var() {
        variants.push(make_var());
    }
    native_literal(&mut variants);
    hol_variants(&mut variants);
    variants
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    #[test]
    fn original_roster_keeps_authored_var_literal_hol_order_and_callback_state() {
        let trace = RefCell::new(Vec::new());
        let actual = complete_category_variants(
            vec!["second", "first"],
            |variant| {
                trace.borrow_mut().push(*variant);
                *variant == "var"
            },
            || {
                trace.borrow_mut().push("implicit");
                true
            },
            || {
                trace.borrow_mut().push("make_var");
                "var"
            },
            |variants| {
                assert_eq!(variants, &["second", "first", "var"]);
                trace.borrow_mut().push("native");
                variants.push("literal");
            },
            |variants| {
                assert_eq!(variants, &["second", "first", "var", "literal"]);
                trace.borrow_mut().push("hol");
                variants.extend(["lambda", "apply"]);
            },
        );
        assert_eq!(actual, ["second", "first", "var", "literal", "lambda", "apply"]);
        assert_eq!(*trace.borrow(), ["second", "first", "implicit", "make_var", "native", "hol"]);
    }

    #[test]
    fn explicit_var_short_circuits_scan_and_never_probes_implicit_authority() {
        let trace = RefCell::new(Vec::new());
        let actual = complete_category_variants(
            vec!["var", "literal"],
            |variant| {
                trace.borrow_mut().push(*variant);
                *variant == "var"
            },
            || panic!("explicit Var skips implicit permission"),
            || panic!("explicit Var skips constructor creation"),
            |variants| {
                trace.borrow_mut().push("native");
                assert_eq!(variants, &["var", "literal"]);
            },
            |_| trace.borrow_mut().push("hol"),
        );
        assert_eq!(actual, ["var", "literal"]);
        assert_eq!(*trace.borrow(), ["var", "native", "hol"]);
    }
}
