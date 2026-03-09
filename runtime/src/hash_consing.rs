//! Hash-consing infrastructure for recursive term types (A-RT01).
//!
//! Provides thread-local interning tables that store `Rc<T>` references keyed
//! by structural hash. When the same term structure is constructed multiple
//! times, hash-consing returns the existing `Rc` instead of allocating a new
//! one. This enables:
//!
//! - **O(1) equality**: `Rc::ptr_eq` instead of O(depth) structural comparison
//! - **Sharing**: identical subterms share a single allocation
//! - **Cache locality**: fewer distinct allocations improve cache behavior
//!
//! ## Usage
//!
//! Generated code (when ART01 gate is enabled) wraps recursive fields in
//! `Rc<T>` and calls `intern()` after construction:
//!
//! ```rust,ignore
//! let term = Proc::PPar(intern(left), intern(right));
//! ```
//!
//! The interning table is epoch-scoped: it is cleared at the start of each
//! Ascent evaluation (alongside the BCG05 epoch bump) to prevent unbounded
//! growth across evaluations.

use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

// Thread-local interning tables, one per type. Each maps structural hash → Rc<T>.
// The epoch tracks when the table was last cleared; on epoch mismatch with the
// BCG05 epoch (bumped at each run_ascent_typed), the table is cleared.
thread_local! {
    static INTERN_EPOCH: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// A thread-local interning table for a specific term type `T`.
///
/// Uses structural hashing (via `Hash`) to detect duplicates and returns
/// shared `Rc<T>` references for structurally identical terms.
pub struct InternTable<T: Hash + Eq + Clone> {
    epoch: u64,
    map: HashMap<u64, Vec<Rc<T>>>,
}

impl<T: Hash + Eq + Clone> InternTable<T> {
    /// Create an empty interning table.
    pub fn new() -> Self {
        Self {
            epoch: 0,
            map: HashMap::new(),
        }
    }

    /// Clear the table if the epoch has advanced.
    fn check_epoch(&mut self) {
        let current = INTERN_EPOCH.with(|e| e.get());
        if self.epoch != current {
            self.epoch = current;
            self.map.clear();
        }
    }

    /// Intern a value, returning a shared `Rc<T>`.
    ///
    /// If a structurally equal value already exists in the table, returns
    /// a clone of the existing `Rc`. Otherwise, wraps the value in a new
    /// `Rc` and inserts it.
    pub fn intern(&mut self, value: T) -> Rc<T> {
        self.check_epoch();

        let hash = {
            let mut h = std::hash::DefaultHasher::new();
            value.hash(&mut h);
            h.finish()
        };

        let bucket = self.map.entry(hash).or_default();

        // Check for structural equality (handles hash collisions)
        for existing in bucket.iter() {
            if **existing == value {
                return Rc::clone(existing);
            }
        }

        let rc = Rc::new(value);
        bucket.push(Rc::clone(&rc));
        rc
    }

    /// Number of interned entries.
    pub fn len(&self) -> usize {
        self.map.values().map(|v| v.len()).sum()
    }

    /// Whether the table is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

impl<T: Hash + Eq + Clone> Default for InternTable<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Bump the intern epoch, causing all `InternTable`s to clear on next access.
///
/// Called alongside `bump_bcg05_epoch()` at the start of each Ascent evaluation.
pub fn bump_intern_epoch() {
    INTERN_EPOCH.with(|e| e.set(e.get().wrapping_add(1)));
}

/// Get the current intern epoch.
pub fn intern_epoch() -> u64 {
    INTERN_EPOCH.with(|e| e.get())
}

/// Convenience macro for defining a thread-local `InternTable<T>` and
/// an intern function.
///
/// Usage in generated code:
/// ```rust,ignore
/// mettail_runtime::define_intern_table!(INTERN_PROC, intern_proc, Proc);
/// // Generates:
/// // thread_local! { static INTERN_PROC: RefCell<InternTable<Proc>> = ... }
/// // fn intern_proc(value: Proc) -> Rc<Proc> { ... }
/// ```
#[macro_export]
macro_rules! define_intern_table {
    ($table_name:ident, $fn_name:ident, $type_name:ty) => {
        thread_local! {
            static $table_name: std::cell::RefCell<$crate::InternTable<$type_name>> =
                std::cell::RefCell::new($crate::InternTable::new());
        }

        /// Intern a term, returning a shared `Rc` reference.
        #[allow(dead_code)]
        fn $fn_name(value: $type_name) -> std::rc::Rc<$type_name> {
            $table_name.with(|table| table.borrow_mut().intern(value))
        }
    };
}

/// Analysis result for hash-consing applicability.
///
/// Reports which categories in a language would benefit from hash-consing
/// based on recursive structure depth and sharing patterns.
#[derive(Debug, Clone)]
pub struct HashConsingAnalysis {
    /// Categories with recursive fields (self-referencing via Box<Self>).
    pub recursive_categories: Vec<String>,
    /// Estimated sharing ratio (0.0 = no sharing, 1.0 = all shared).
    pub estimated_sharing: f64,
    /// Whether hash-consing is recommended for this grammar.
    pub recommended: bool,
}

impl HashConsingAnalysis {
    /// Create an analysis result.
    pub fn new(recursive_categories: Vec<String>, estimated_sharing: f64) -> Self {
        let recommended = !recursive_categories.is_empty() && estimated_sharing > 0.1;
        Self {
            recursive_categories,
            estimated_sharing,
            recommended,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_intern_table_dedup() {
        let mut table = InternTable::<String>::new();
        let a1 = table.intern("hello".to_string());
        let a2 = table.intern("hello".to_string());
        let b = table.intern("world".to_string());

        // Same structure → same Rc
        assert!(Rc::ptr_eq(&a1, &a2));
        // Different structure → different Rc
        assert!(!Rc::ptr_eq(&a1, &b));
        assert_eq!(table.len(), 2);
    }

    #[test]
    fn test_intern_table_epoch_clear() {
        let mut table = InternTable::<i32>::new();
        let a = table.intern(42);
        assert_eq!(table.len(), 1);

        // Bump epoch
        bump_intern_epoch();

        // After epoch bump, table should clear on next access
        let b = table.intern(42);
        assert_eq!(table.len(), 1);
        // But the Rc is different (table was cleared)
        assert!(!Rc::ptr_eq(&a, &b));
    }

    #[test]
    fn test_intern_table_hash_collision_handling() {
        // Two values that might have the same hash but are not equal
        let mut table = InternTable::<(i32, i32)>::new();
        let a = table.intern((1, 2));
        let b = table.intern((2, 1));
        let a2 = table.intern((1, 2));

        assert!(Rc::ptr_eq(&a, &a2));
        assert!(!Rc::ptr_eq(&a, &b));
        assert_eq!(table.len(), 2);
    }

    #[test]
    fn test_intern_table_empty() {
        let table = InternTable::<String>::new();
        assert!(table.is_empty());
        assert_eq!(table.len(), 0);
    }

    #[test]
    fn test_intern_epoch_counter() {
        let e1 = intern_epoch();
        bump_intern_epoch();
        let e2 = intern_epoch();
        assert_eq!(e2, e1.wrapping_add(1));
    }

    #[test]
    fn test_hash_consing_analysis() {
        let analysis = HashConsingAnalysis::new(
            vec!["Proc".to_string(), "Name".to_string()],
            0.35,
        );
        assert!(analysis.recommended);
        assert_eq!(analysis.recursive_categories.len(), 2);

        let no_recursive = HashConsingAnalysis::new(vec![], 0.0);
        assert!(!no_recursive.recommended);

        let low_sharing = HashConsingAnalysis::new(
            vec!["Proc".to_string()],
            0.05,
        );
        assert!(!low_sharing.recommended);
    }

    // =========================================================================
    // 16. proptest: intern(x) twice always returns Rc::ptr_eq
    // =========================================================================
    proptest::proptest! {
        #![proptest_config(proptest::prelude::ProptestConfig::with_cases(300))]
        #[test]
        fn prop_intern_dedup_invariant(s in "[a-zA-Z0-9]{0,20}") {
            let mut table = InternTable::<String>::new();
            let rc1 = table.intern(s.clone());
            let rc2 = table.intern(s);
            proptest::prop_assert!(
                Rc::ptr_eq(&rc1, &rc2),
                "interning the same value twice must return Rc::ptr_eq references"
            );
        }
    }

    // =========================================================================
    // 17. proptest: x != y implies not Rc::ptr_eq
    // =========================================================================
    proptest::proptest! {
        #![proptest_config(proptest::prelude::ProptestConfig::with_cases(300))]
        #[test]
        fn prop_intern_distinct_values_distinct(
            x in "[a-zA-Z0-9]{0,20}",
            y in "[a-zA-Z0-9]{0,20}"
        ) {
            proptest::prop_assume!(x != y);
            let mut table = InternTable::<String>::new();
            let rc_x = table.intern(x);
            let rc_y = table.intern(y);
            proptest::prop_assert!(
                !Rc::ptr_eq(&rc_x, &rc_y),
                "distinct values must produce distinct Rc allocations"
            );
        }
    }
}
