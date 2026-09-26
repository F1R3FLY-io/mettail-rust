//! The original runtime variable cache, shared by generated and owned actions.
//! These identities are native/session-local, not a canonical wire encoding.

use moniker::FreeVar;
use std::cell::RefCell;
use std::collections::HashMap;

// Thread-local variable cache for consistent variable identity within a parsing session.
// Uses thread_local + RefCell instead of Mutex since parsing is single-threaded.
// Each thread gets its own independent cache, eliminating lock overhead (~15-25ns per call).
thread_local! {
    static VAR_CACHE: RefCell<HashMap<String, FreeVar<String>>> =
        RefCell::new(HashMap::new());
}

/// Get or create a variable from the cache.
///
/// This ensures that parsing the same variable name twice produces
/// the same FreeVar instance, which is critical for correct variable
/// identity in alpha-equivalence checking.
pub fn get_or_create_var(name: impl Into<String>) -> FreeVar<String> {
    let name = name.into();
    VAR_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        cache
            .entry(name.clone())
            .or_insert_with(|| FreeVar::fresh_named(name))
            .clone()
    })
}

/// Clear the variable cache.
///
/// Call this before parsing a new term to ensure variables from
/// different terms don't accidentally share identity.
pub fn clear_var_cache() {
    VAR_CACHE.with(|cache| cache.borrow_mut().clear());
}

/// Get the current size of the variable cache.
pub fn var_cache_size() -> usize {
    VAR_CACHE.with(|cache| cache.borrow().len())
}

/// Get or insert a FreeVar into the cache.
///
/// Unlike `get_or_create_var`, this uses an existing FreeVar if not in cache
/// (rather than creating a fresh one). This is used for unifying FreeVar IDs
/// after environment substitution.
pub fn get_or_insert_var(var: &FreeVar<String>) -> FreeVar<String> {
    if let Some(name) = &var.pretty_name {
        VAR_CACHE.with(|cache| {
            let mut cache = cache.borrow_mut();
            cache
                .entry(name.clone())
                .or_insert_with(|| var.clone())
                .clone()
        })
    } else {
        var.clone()
    }
}
