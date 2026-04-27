//! Phase 7: refinement-type predicate evaluation.
//!
//! Per the predicated-types design, a refinement type
//! `RefInt = { x: Int | x > 0 }` declares a predicate that must hold for
//! any value to inhabit the refined category. The macro pipeline lowers
//! the refinement predicate to a closure registered via
//! `register_refinement_predicate`. Generated rule-action codegen calls
//! `evaluate_refinement_predicate(name, value)` after constructing a
//! candidate term; on failure, the action emits an RT01 diagnostic and
//! pushes the category's `Err` variant (or returns empty).
//!
//! The registry is a thread-local `HashMap<String, Predicate>` so each
//! evaluator thread sees its own bindings — important for proptests and
//! parallel rewriting.

use std::any::Any;
use std::cell::RefCell;
use std::collections::HashMap;

/// A refinement predicate: a function taking a `&dyn Any` value (the
/// constructed candidate term) and returning `true` if it inhabits the
/// refined category. The predicate is responsible for downcasting to the
/// expected concrete type.
pub type RefinementPredicate = std::sync::Arc<dyn Fn(&dyn Any) -> bool + Send + Sync>;

thread_local! {
    static REFINEMENT_REGISTRY: RefCell<HashMap<String, RefinementPredicate>> =
        RefCell::new(HashMap::new());
}

/// Register a refinement predicate by name. Called by the generated
/// language-init function for each `RefinementTypeDef` in the grammar.
pub fn register_refinement_predicate(name: &str, pred: RefinementPredicate) {
    REFINEMENT_REGISTRY.with(|reg| {
        reg.borrow_mut().insert(name.to_string(), pred);
    });
}

/// Clear all registered refinement predicates. Called by test setup /
/// teardown.
pub fn clear_refinement_registry() {
    REFINEMENT_REGISTRY.with(|reg| reg.borrow_mut().clear());
}

/// Evaluate the refinement predicate for the named refinement type
/// against `value`. Returns `true` if the predicate holds (or if no
/// predicate is registered — conservative).
pub fn evaluate_refinement_predicate(name: &str, value: &dyn Any) -> bool {
    REFINEMENT_REGISTRY.with(|reg| {
        let reg = reg.borrow();
        match reg.get(name) {
            Some(pred) => pred(value),
            // No predicate registered → default true. Languages without
            // refinement types pay nothing; test grammars with synthetic
            // refinements register their predicates explicitly.
            None => true,
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unregistered_predicate_returns_true() {
        clear_refinement_registry();
        let v: i32 = 5;
        assert!(evaluate_refinement_predicate("PositiveInt", &v));
    }

    #[test]
    fn registered_predicate_filters_values() {
        clear_refinement_registry();
        register_refinement_predicate(
            "PositiveInt",
            std::sync::Arc::new(|val: &dyn Any| {
                if let Some(&n) = val.downcast_ref::<i32>() {
                    n > 0
                } else {
                    false
                }
            }),
        );
        let v_pos: i32 = 5;
        let v_neg: i32 = -3;
        assert!(evaluate_refinement_predicate("PositiveInt", &v_pos));
        assert!(!evaluate_refinement_predicate("PositiveInt", &v_neg));
        clear_refinement_registry();
    }

    #[test]
    fn predicate_for_unrelated_type_returns_false() {
        clear_refinement_registry();
        register_refinement_predicate(
            "PositiveInt",
            std::sync::Arc::new(|val: &dyn Any| {
                val.downcast_ref::<i32>().map(|n| *n > 0).unwrap_or(false)
            }),
        );
        let s: String = "5".to_string();
        // Predicate is for i32; passing &String should return false (no downcast match).
        assert!(!evaluate_refinement_predicate("PositiveInt", &s));
        clear_refinement_registry();
    }
}
