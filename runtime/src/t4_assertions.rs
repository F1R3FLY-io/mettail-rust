//! T4 user assertion registry.
//!
//! Phase 7C (predicated types): T4 undecidable guard predicates
//! cannot be evaluated automatically — the user must supply a closure
//! that provides the answer. This module hosts the runtime registry
//! that maps rule labels to user-registered assertion closures.
//!
//! ## Lifecycle
//!
//! 1. The macro emits a T4 codegen path (per
//!    `macros::gen::runtime::guard_codegen::generate_guard_function`)
//!    that calls `t4_assertion_lookup(rule_label)` and dispatches to
//!    the registered closure if one exists.
//! 2. User code (or generated `cert:` validation) calls
//!    `register_t4_assertion(rule_label, |env| ...)` to install the
//!    assertion before the first `run_ascent()`.
//! 3. If no assertion is registered when the rule fires, the guard
//!    safely-fails to `false` (the spec's safe default for
//!    undecidable predicates).
//!
//! ## Thread-local vs global
//!
//! The registry is thread-local because each `run_ascent()` call may
//! install different assertions for testing or simulation. A global
//! registry would race between concurrent simulators.
//!
//! ## Why no `unregister`
//!
//! Re-registering with the same key overwrites the prior closure.
//! `clear_t4_assertions()` clears the entire table for the current
//! thread.

use std::cell::RefCell;
use std::collections::HashMap;

/// A user-supplied T4 assertion closure.
///
/// Receives a borrow of the variable bindings collected from the rule
/// match. Returns `true` iff the user vouches that the undecidable
/// predicate holds for those bindings.
pub type T4Assertion = Box<dyn Fn(&HashMap<String, String>) -> bool + Send + 'static>;

thread_local! {
    static T4_ASSERTION_TABLE: RefCell<HashMap<String, T4Assertion>> =
        RefCell::new(HashMap::new());
}

/// Install a T4 assertion for the named rule on the current thread.
///
/// Subsequent T4 codegen paths for that rule will dispatch through
/// this closure. Re-registering replaces any prior closure.
pub fn register_t4_assertion<F>(rule_label: &str, assertion: F)
where
    F: Fn(&HashMap<String, String>) -> bool + Send + 'static,
{
    T4_ASSERTION_TABLE.with(|table| {
        table
            .borrow_mut()
            .insert(rule_label.to_string(), Box::new(assertion));
    });
}

/// Look up a T4 assertion for the named rule.
///
/// Returns a clone-equivalent dispatch handle. Because closures are
/// not `Clone`, the returned handle is a small wrapper that internally
/// re-acquires the thread-local borrow each time it's invoked.
pub fn t4_assertion_lookup(rule_label: &str) -> Option<T4AssertionHandle> {
    T4_ASSERTION_TABLE.with(|table| {
        if table.borrow().contains_key(rule_label) {
            Some(T4AssertionHandle { rule_label: rule_label.to_string() })
        } else {
            None
        }
    })
}

/// A small handle that, when called, dispatches to the
/// thread-local-installed assertion for its rule label. The handle
/// is `Send` so it can be returned from `t4_assertion_lookup` and
/// invoked in a Rust closure context that doesn't directly own the
/// table.
pub struct T4AssertionHandle {
    rule_label: String,
}

impl T4AssertionHandle {
    /// Invoke the registered assertion. Panics if the table entry has
    /// been removed between lookup and invocation (a race only
    /// possible if user code calls `clear_t4_assertions` mid-rule).
    pub fn call(&self, env: &HashMap<String, String>) -> bool {
        T4_ASSERTION_TABLE.with(|table| {
            let table = table.borrow();
            let assertion = table
                .get(&self.rule_label)
                .expect("T4 assertion removed between lookup and call");
            assertion(env)
        })
    }
}

/// Clear the entire T4 assertion table for the current thread.
///
/// Used by tests and simulators to reset between runs.
pub fn clear_t4_assertions() {
    T4_ASSERTION_TABLE.with(|table| table.borrow_mut().clear());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn register_and_lookup_returns_some() {
        clear_t4_assertions();
        register_t4_assertion("MyRule", |_env| true);
        let handle = t4_assertion_lookup("MyRule");
        assert!(handle.is_some());
    }

    #[test]
    fn lookup_unregistered_returns_none() {
        clear_t4_assertions();
        let handle = t4_assertion_lookup("NotRegistered");
        assert!(handle.is_none());
    }

    #[test]
    fn registered_assertion_is_invoked() {
        clear_t4_assertions();
        register_t4_assertion("ReturnsTrue", |_env| true);
        register_t4_assertion("ReturnsFalse", |_env| false);
        let env = HashMap::new();
        assert!(t4_assertion_lookup("ReturnsTrue").unwrap().call(&env));
        assert!(!t4_assertion_lookup("ReturnsFalse").unwrap().call(&env));
    }

    #[test]
    fn assertion_can_inspect_env() {
        clear_t4_assertions();
        register_t4_assertion("CheckX", |env| {
            env.get("x").map(|v| v == "expected").unwrap_or(false)
        });
        let mut env = HashMap::new();
        env.insert("x".to_string(), "expected".to_string());
        assert!(t4_assertion_lookup("CheckX").unwrap().call(&env));
        env.insert("x".to_string(), "wrong".to_string());
        assert!(!t4_assertion_lookup("CheckX").unwrap().call(&env));
    }

    #[test]
    fn re_registration_replaces_prior_closure() {
        clear_t4_assertions();
        register_t4_assertion("Replace", |_env| false);
        register_t4_assertion("Replace", |_env| true);
        let env = HashMap::new();
        assert!(t4_assertion_lookup("Replace").unwrap().call(&env));
    }

    #[test]
    fn clear_removes_all_entries() {
        register_t4_assertion("A", |_env| true);
        register_t4_assertion("B", |_env| true);
        clear_t4_assertions();
        assert!(t4_assertion_lookup("A").is_none());
        assert!(t4_assertion_lookup("B").is_none());
    }
}
