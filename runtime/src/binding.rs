//! Variable binding support using moniker
//!
//! This module provides wrappers around moniker types that add
//! Hash and Ord implementations needed for MeTTaIL's use in
//! Ascent (which requires Hash for relations) and term generation
//! (which requires Ord for enumeration).

use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};

// Re-export moniker types
pub use moniker::{Binder, BoundPattern, BoundTerm, BoundVar, FreeVar, Var};

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

//=============================================================================
// TERM EQUALITY CACHE (Sprint B: R1)
//=============================================================================

// Thread-local cache for `Scope::term_eq()` results.
//
// Keyed by `(hash_a, hash_b)` where each hash is a 64-bit structural hash of
// a `Scope`'s `unsafe_pattern` and `unsafe_body`. The key pair is canonicalized
// (smaller hash first) so that `(a, b)` and `(b, a)` share the same cache entry.
//
// Uses `Cell<HashMap>` with take/set pattern for zero-overhead thread-local access
// (no borrow tracking at runtime, same pattern as pipeline TLS buffer pools).
//
// Collision probability for N distinct terms: ≈ N²/2⁶⁴. For N = 10,000: ≈ 5.4 × 10⁻¹².
thread_local! {
    static TERM_EQ_CACHE: Cell<HashMap<(u64, u64), bool>> =
        Cell::new(HashMap::new());
}

// BCG05 epoch counter: incremented at the start of each Ascent evaluation
// so that BCG05 normalize-on-insert dedup guards detect the new epoch and
// clear their HashSets. Without this, hashes from a prior run persist and
// cause the dedup guard to skip rule firings for previously-seen terms,
// leading to incorrect results on repeated evaluations (e.g., REPL `exec`).
thread_local! {
    static BCG05_EPOCH: Cell<u64> = const { Cell::new(0) };
}

/// Increment the BCG05 dedup epoch counter.
///
/// Call at the start of each `run_ascent_typed()` invocation. BCG05 dedup
/// guards in generated Ascent rules compare their local epoch against
/// this counter and clear their HashSet when a mismatch is detected.
pub fn bump_bcg05_epoch() {
    BCG05_EPOCH.with(|e| e.set(e.get().wrapping_add(1)));
}

/// Get the current BCG05 epoch value.
///
/// Called from generated BCG05 dedup guards in Ascent rules to check
/// whether the current epoch matches their cached epoch.
pub fn bcg05_epoch() -> u64 {
    BCG05_EPOCH.with(|e| e.get())
}

/// Clear the term equality cache.
///
/// Call this at the start of each Ascent evaluation (`run_ascent_typed()`) to
/// prevent stale entries from a previous evaluation affecting correctness.
/// The cache is only valid within a single fixpoint computation because
/// term identity (via moniker's unique IDs) is session-scoped.
pub fn clear_term_eq_cache() {
    TERM_EQ_CACHE.with(|cache| {
        let mut map = cache.take();
        map.clear();
        cache.set(map);
    });
}

/// Get the current size of the term equality cache.
pub fn term_eq_cache_size() -> usize {
    TERM_EQ_CACHE.with(|cache| {
        let map = cache.take();
        let size = map.len();
        cache.set(map);
        size
    })
}

/// Compute a structural hash for cache key generation.
///
/// Hashes both `unsafe_pattern` and `unsafe_body` fields of a moniker `Scope`.
/// This produces a hash consistent with alpha-equivalence: two α-equivalent
/// scopes hash identically because `close_term` normalizes bound variable
/// structure into identical `unsafe_*` fields.
fn structural_scope_hash<P: Hash, T: Hash>(scope: &moniker::Scope<P, T>) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    scope.unsafe_pattern.hash(&mut h);
    scope.unsafe_body.hash(&mut h);
    h.finish()
}

/// Cached term equality check for `Scope` types.
///
/// Looks up the `(hash_self, hash_other)` pair in the TLS cache. On miss,
/// delegates to `moniker::Scope::term_eq()` (which performs `unbind2` + recursive
/// comparison) and stores the result. On hit, returns the cached value in O(1).
///
/// The cache key is canonicalized: `min(h1, h2), max(h1, h2)` so that
/// `term_eq(a, b)` and `term_eq(b, a)` share the same entry.
fn cached_term_eq<P, T>(this: &moniker::Scope<P, T>, other: &moniker::Scope<P, T>) -> bool
where
    P: Hash + BoundPattern<String> + Clone + PartialEq,
    T: Hash + BoundTerm<String> + Clone + PartialEq,
{
    let h_self = structural_scope_hash(this);
    let h_other = structural_scope_hash(other);

    // Canonical key ordering to ensure (a,b) and (b,a) share a cache entry
    let key = if h_self <= h_other {
        (h_self, h_other)
    } else {
        (h_other, h_self)
    };

    TERM_EQ_CACHE.with(|cache| {
        let mut map = cache.take();
        let result = if let Some(&cached) = map.get(&key) {
            cached
        } else {
            let eq = this.term_eq(other);
            map.insert(key, eq);
            eq
        };
        cache.set(map);
        result
    })
}

//=============================================================================
// SCOPE WRAPPER
//=============================================================================

/// Wrapper around moniker::Scope that adds Hash and Ord implementations.
///
/// The official moniker crate doesn't implement Hash or Ord for Scope,
/// but we need these for:
/// - Using Scopes in HashMap-based data structures (Ascent relations)
/// - Generating terms in canonical order
///
/// The Hash implementation hashes both pattern and body, which is safe
/// because Scope's PartialEq already compares these fields alpha-equivalently.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scope<P, T> {
    inner: moniker::Scope<P, T>,
}

impl<P: Hash, T: Hash> Hash for Scope<P, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash the pattern and body directly
        // This is safe because Scope's PartialEq ensures
        // that equal scopes have equal patterns and bodies (alpha-equivalently)
        self.inner.unsafe_pattern.hash(state);
        self.inner.unsafe_body.hash(state);
    }
}

impl<P, T> PartialOrd for Scope<P, T>
where
    P: Clone + PartialEq + Eq + BoundPattern<String> + fmt::Debug + Hash,
    T: Clone + PartialEq + Eq + BoundTerm<String> + fmt::Debug + Ord,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<P, T> Ord for Scope<P, T>
where
    P: Clone + PartialEq + Eq + BoundPattern<String> + fmt::Debug + Hash,
    T: Clone + PartialEq + Eq + BoundTerm<String> + fmt::Debug + Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        // Zero-allocation comparison using unsafe accessors (no clone/unbind).
        //
        // Pattern: Compare by deterministic hash (FreeVar hashes by unique_id only).
        // This is imperfect for Ord (hash collisions could make non-equal patterns
        // compare as Equal) but since PartialEq is correct and this ordering is only
        // used for collection ordering (not semantic equality), it's acceptable.
        //
        // Body: Compare directly using T's Ord implementation.
        let hash_pat = |p: &P| -> u64 {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            p.hash(&mut h);
            h.finish()
        };
        hash_pat(&self.inner.unsafe_pattern)
            .cmp(&hash_pat(&other.inner.unsafe_pattern))
            .then_with(|| self.inner.unsafe_body.cmp(&other.inner.unsafe_body))
    }
}

impl<P, T> Scope<P, T> {
    /// Create a new scope by binding a term with the given pattern
    pub fn new<N>(pattern: P, body: T) -> Scope<P, T>
    where
        N: Clone + PartialEq,
        P: BoundPattern<N>,
        T: BoundTerm<N>,
    {
        Scope {
            inner: moniker::Scope::new(pattern, body),
        }
    }

    /// Unbind a term, returning the freshened pattern and body
    pub fn unbind<N>(self) -> (P, T)
    where
        N: Clone + Eq + Hash,
        P: BoundPattern<N>,
        T: BoundTerm<N>,
    {
        self.inner.unbind()
    }

    /// Simultaneously unbind two terms
    pub fn unbind2<N, P2, T2>(self, other: Scope<P2, T2>) -> (P, T, P2, T2)
    where
        N: Clone + Eq + Hash,
        P: BoundPattern<N>,
        T: BoundTerm<N>,
        P2: BoundPattern<N>,
        T2: BoundTerm<N>,
    {
        self.inner.unbind2(other.inner)
    }

    /// Access to the underlying moniker Scope (for advanced use)
    pub fn inner(&self) -> &moniker::Scope<P, T> {
        &self.inner
    }

    /// Direct access to the pattern (unsafe - preserves bound variables)
    ///
    /// Use this instead of unbind() when you need stable variable identity
    /// for equations or pattern matching.
    pub fn unsafe_pattern(&self) -> &P {
        &self.inner.unsafe_pattern
    }

    /// Direct access to the body (unsafe - preserves bound variables)
    ///
    /// Use this instead of unbind() when you need stable variable identity
    /// for equations or pattern matching.
    pub fn unsafe_body(&self) -> &T {
        &self.inner.unsafe_body
    }

    /// Construct a Scope from pattern and body directly (unsafe - no closing)
    ///
    /// This assumes the body already has the correct bound variable structure.
    /// Used in generated Ascent code for reconstructing terms.
    pub fn from_parts_unsafe(pattern: P, body: T) -> Scope<P, T> {
        Scope {
            inner: moniker::Scope {
                unsafe_pattern: pattern,
                unsafe_body: body,
            },
        }
    }
}

// Implement BoundTerm<String> with cached term_eq (Sprint B: R1).
//
// MeTTaIL always uses String as the name type. The cached_term_eq function
// requires Hash bounds on P and T (for structural hashing), which are satisfied
// by all MeTTaIL term types but not by arbitrary N. A blanket impl for generic N
// is provided below for non-String name types (without caching).
impl<P, T> BoundTerm<String> for Scope<P, T>
where
    P: BoundPattern<String> + Clone + PartialEq + Hash,
    T: BoundTerm<String> + Clone + PartialEq + Hash,
{
    fn term_eq(&self, other: &Scope<P, T>) -> bool {
        cached_term_eq(&self.inner, &other.inner)
    }

    fn close_term(&mut self, state: moniker::ScopeState, on_free: &impl moniker::OnFreeFn<String>) {
        self.inner.close_term(state, on_free)
    }

    fn open_term(&mut self, state: moniker::ScopeState, on_bound: &impl moniker::OnBoundFn<String>) {
        self.inner.open_term(state, on_bound)
    }

    fn visit_vars(&self, on_var: &mut impl FnMut(&Var<String>)) {
        self.inner.visit_vars(on_var)
    }

    fn visit_mut_vars(&mut self, on_var: &mut impl FnMut(&mut Var<String>)) {
        self.inner.visit_mut_vars(on_var)
    }
}

// Allow conversion from moniker::Scope
impl<P: Clone, T: Clone> From<moniker::Scope<P, T>> for Scope<P, T> {
    fn from(scope: moniker::Scope<P, T>) -> Self {
        Scope { inner: scope }
    }
}

//=============================================================================
// ORDVAR WRAPPER
//=============================================================================

/// Wrapper around moniker::Var that adds Ord implementation.
///
/// The official moniker crate doesn't implement Ord for Var,
/// but we need it for:
/// - Sorting terms for enumeration
/// - Using terms as keys in BTree collections
/// - Canonical term ordering
///
/// The Ord implementation compares variables by their pretty-printed names,
/// providing a total order (NOT alpha-equivalence respecting).
/// This is intentional - we want a total order for enumeration.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct OrdVar(pub Var<String>);

impl PartialOrd for OrdVar {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OrdVar {
    fn cmp(&self, other: &Self) -> Ordering {
        // Zero-allocation comparison by variant discriminant, then structural fields.
        // FreeVar: compare by unique_id (the only field used for PartialEq/Hash).
        // BoundVar: compare by (scope, binder) — both derive Ord.
        match (&self.0, &other.0) {
            (Var::Free(_), Var::Bound(_)) => Ordering::Less,
            (Var::Bound(_), Var::Free(_)) => Ordering::Greater,
            (Var::Free(a), Var::Free(b)) => {
                // UniqueId wraps a u32 but doesn't expose it or derive Ord.
                // Use deterministic hashing (DefaultHasher) for a total ordering.
                // DefaultHasher is deterministic within a process — hash(a) == hash(b)
                // iff a == b for u32-sized types (no collisions in practice).
                let hash_uid = |uid: &moniker::UniqueId| -> u64 {
                    let mut h = std::collections::hash_map::DefaultHasher::new();
                    uid.hash(&mut h);
                    h.finish()
                };
                hash_uid(&a.unique_id).cmp(&hash_uid(&b.unique_id))
            },
            (Var::Bound(a), Var::Bound(b)) => a.scope.cmp(&b.scope).then(a.binder.cmp(&b.binder)),
        }
    }
}

// Forward BoundTerm implementation to inner Var
impl BoundTerm<String> for OrdVar {
    fn term_eq(&self, other: &Self) -> bool {
        self.0.term_eq(&other.0)
    }

    fn close_term(&mut self, state: moniker::ScopeState, on_free: &impl moniker::OnFreeFn<String>) {
        self.0.close_term(state, on_free)
    }

    fn open_term(
        &mut self,
        state: moniker::ScopeState,
        on_bound: &impl moniker::OnBoundFn<String>,
    ) {
        self.0.open_term(state, on_bound)
    }

    fn visit_vars(&self, on_var: &mut impl FnMut(&Var<String>)) {
        self.0.visit_vars(on_var)
    }

    fn visit_mut_vars(&mut self, on_var: &mut impl FnMut(&mut Var<String>)) {
        self.0.visit_mut_vars(on_var)
    }
}

// Conversion from Var to OrdVar
impl From<Var<String>> for OrdVar {
    fn from(var: Var<String>) -> Self {
        OrdVar(var)
    }
}

// Conversion from OrdVar to Var
impl From<OrdVar> for Var<String> {
    fn from(ord_var: OrdVar) -> Self {
        ord_var.0
    }
}

// Display formatting
impl fmt::Display for OrdVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;

    // =========================================================================
    // 1. get_or_create_var: same name returns same FreeVar
    // =========================================================================
    #[test]
    fn test_get_or_create_var_same_instance() {
        clear_var_cache();
        let v1 = get_or_create_var("alpha");
        let v2 = get_or_create_var("alpha");
        assert_eq!(v1.pretty_name, v2.pretty_name, "pretty_name must match");
        assert_eq!(v1.unique_id, v2.unique_id, "unique_id must match for same name");
    }

    // =========================================================================
    // 2. get_or_create_var: different names produce different FreeVars
    // =========================================================================
    #[test]
    fn test_get_or_create_var_different_names() {
        clear_var_cache();
        let v1 = get_or_create_var("alpha");
        let v2 = get_or_create_var("beta");
        assert_ne!(
            v1.unique_id, v2.unique_id,
            "different names must yield different unique_ids"
        );
    }

    // =========================================================================
    // 3. clear_var_cache: clearing then recreating yields a NEW FreeVar
    // =========================================================================
    #[test]
    fn test_clear_var_cache_resets() {
        clear_var_cache();
        let v1 = get_or_create_var("gamma");
        let uid1 = v1.unique_id;
        clear_var_cache();
        let v2 = get_or_create_var("gamma");
        assert_ne!(
            uid1, v2.unique_id,
            "after clear, same name must produce a fresh unique_id"
        );
    }

    // =========================================================================
    // 4. var_cache_size tracks inserts and clears
    // =========================================================================
    #[test]
    fn test_var_cache_size() {
        clear_var_cache();
        assert_eq!(var_cache_size(), 0, "cache should be empty after clear");

        get_or_create_var("a");
        assert_eq!(var_cache_size(), 1);

        get_or_create_var("b");
        assert_eq!(var_cache_size(), 2);

        // Duplicate does not increase size
        get_or_create_var("a");
        assert_eq!(var_cache_size(), 2);

        clear_var_cache();
        assert_eq!(var_cache_size(), 0, "cache should be empty after second clear");
    }

    // =========================================================================
    // 5. get_or_insert_var preserves existing cached var
    // =========================================================================
    #[test]
    fn test_get_or_insert_var_preserves_existing() {
        clear_var_cache();
        // Seed the cache with a var for "delta"
        let cached = get_or_create_var("delta");

        // Create a fresh FreeVar with the same pretty_name but a different unique_id
        let fresh = FreeVar::fresh_named("delta");
        assert_ne!(
            cached.unique_id, fresh.unique_id,
            "fresh var should have a different unique_id than cached"
        );

        // get_or_insert_var should return the *cached* one, not the fresh one
        let result = get_or_insert_var(&fresh);
        assert_eq!(
            result.unique_id, cached.unique_id,
            "get_or_insert_var must return the previously cached var"
        );
    }

    // =========================================================================
    // 6. OrdVar ordering: Free < Bound
    // =========================================================================
    #[test]
    fn test_ordvar_ordering_free_before_bound() {
        clear_var_cache();
        let free_var = OrdVar(Var::Free(FreeVar::fresh_named("x")));
        let bound_var = OrdVar(Var::Bound(BoundVar {
            scope: moniker::ScopeOffset(0),
            binder: moniker::BinderIndex(0),
            pretty_name: Some("x".to_string()),
        }));

        assert!(
            free_var < bound_var,
            "OrdVar(Free) must be less than OrdVar(Bound)"
        );
        assert!(
            bound_var > free_var,
            "OrdVar(Bound) must be greater than OrdVar(Free)"
        );
    }

    // =========================================================================
    // 7. OrdVar display works without panic
    // =========================================================================
    #[test]
    fn test_ordvar_display() {
        clear_var_cache();
        let free_var = OrdVar(Var::Free(FreeVar::fresh_named("x")));
        let bound_var = OrdVar(Var::Bound(BoundVar {
            scope: moniker::ScopeOffset(0),
            binder: moniker::BinderIndex(0),
            pretty_name: Some("y".to_string()),
        }));

        // Just verify Display doesn't panic and produces non-empty output
        let s1 = format!("{}", free_var);
        let s2 = format!("{}", bound_var);
        assert!(!s1.is_empty(), "Display for free OrdVar must produce output");
        assert!(!s2.is_empty(), "Display for bound OrdVar must produce output");
    }

    // =========================================================================
    // 8. OrdVar::from / Var::from roundtrip
    // =========================================================================
    #[test]
    fn test_ordvar_from_var_roundtrip() {
        clear_var_cache();
        let original_var: Var<String> = Var::Free(FreeVar::fresh_named("z"));
        let ord = OrdVar::from(original_var.clone());
        let back: Var<String> = Var::from(ord);
        assert_eq!(original_var, back, "OrdVar::from / Var::from must roundtrip");
    }

    // =========================================================================
    // 9. Scope: equal scopes produce equal hashes
    // =========================================================================
    #[test]
    fn test_scope_hash_consistent_with_eq() {
        clear_var_cache();
        let v = get_or_create_var("w");
        let binder1 = Binder(v.clone());
        let body1 = OrdVar(Var::Free(v.clone()));

        let binder2 = Binder(v.clone());
        let body2 = OrdVar(Var::Free(v.clone()));

        let scope1 = Scope::<Binder<String>, OrdVar>::new::<String>(binder1, body1);
        let scope2 = Scope::<Binder<String>, OrdVar>::new::<String>(binder2, body2);

        assert_eq!(scope1, scope2, "scopes with same binder/body must be equal");

        let hash_of = |s: &Scope<Binder<String>, OrdVar>| -> u64 {
            let mut h = DefaultHasher::new();
            s.hash(&mut h);
            h.finish()
        };

        assert_eq!(
            hash_of(&scope1),
            hash_of(&scope2),
            "equal scopes must have equal hashes"
        );
    }

    // =========================================================================
    // 10. Scope: Ord transitivity (a < b, b < c => a < c)
    // =========================================================================
    #[test]
    fn test_scope_ord_transitivity() {
        clear_var_cache();

        // Create three distinct bound vars with increasing (scope, binder) indices
        // to give a predictable ordering via the body's Ord impl.
        let body_a = OrdVar(Var::Bound(BoundVar {
            scope: moniker::ScopeOffset(0),
            binder: moniker::BinderIndex(0),
            pretty_name: None,
        }));
        let body_b = OrdVar(Var::Bound(BoundVar {
            scope: moniker::ScopeOffset(0),
            binder: moniker::BinderIndex(1),
            pretty_name: None,
        }));
        let body_c = OrdVar(Var::Bound(BoundVar {
            scope: moniker::ScopeOffset(1),
            binder: moniker::BinderIndex(0),
            pretty_name: None,
        }));

        // Use the same binder for all three so the hash-based pattern comparison
        // is Equal and the ordering depends entirely on body comparison.
        let v = FreeVar::fresh_named("t");

        let scope_a = Scope::<Binder<String>, OrdVar>::new::<String>(
            Binder(v.clone()),
            body_a,
        );
        let scope_b = Scope::<Binder<String>, OrdVar>::new::<String>(
            Binder(v.clone()),
            body_b,
        );
        let scope_c = Scope::<Binder<String>, OrdVar>::new::<String>(
            Binder(v.clone()),
            body_c,
        );

        // Verify a < b, b < c
        assert!(
            scope_a < scope_b,
            "scope_a must be less than scope_b"
        );
        assert!(
            scope_b < scope_c,
            "scope_b must be less than scope_c"
        );
        // Transitivity: a < c
        assert!(
            scope_a < scope_c,
            "transitivity: scope_a must be less than scope_c"
        );
    }

    // =========================================================================
    // 11. proptest: var cache idempotent
    // =========================================================================
    proptest::proptest! {
        #![proptest_config(proptest::prelude::ProptestConfig::with_cases(200))]
        #[test]
        fn prop_var_cache_idempotent(name in "[a-z]{1,10}") {
            clear_var_cache();
            let v1 = get_or_create_var(&name);
            let v2 = get_or_create_var(&name);
            proptest::prop_assert_eq!(v1.pretty_name, v2.pretty_name);
            proptest::prop_assert_eq!(v1.unique_id, v2.unique_id);
        }
    }

    // =========================================================================
    // 12. bump_bcg05_epoch increments by 1
    // =========================================================================
    #[test]
    fn test_bump_bcg05_epoch_increments() {
        let before = bcg05_epoch();
        bump_bcg05_epoch();
        let after = bcg05_epoch();
        assert_eq!(
            after,
            before.wrapping_add(1),
            "bump_bcg05_epoch must increment by exactly 1"
        );
    }

    // =========================================================================
    // 13. bcg05_epoch: bumping increases relative to current
    // =========================================================================
    #[test]
    fn test_bcg05_epoch_relative_increment() {
        // Since tests may share TLS, we just verify relative behavior
        let e1 = bcg05_epoch();
        bump_bcg05_epoch();
        bump_bcg05_epoch();
        let e3 = bcg05_epoch();
        assert_eq!(
            e3,
            e1.wrapping_add(2),
            "two bumps must advance epoch by 2"
        );
    }

    // =========================================================================
    // 14-15. term_eq cache: clear + size work correctly
    // =========================================================================
    #[test]
    fn test_clear_term_eq_cache_and_size() {
        clear_var_cache();
        clear_term_eq_cache();
        assert_eq!(term_eq_cache_size(), 0, "cache should be empty after clear");

        // Populate the cache by comparing two Scopes
        let v1 = FreeVar::fresh_named("p");
        let v2 = FreeVar::fresh_named("q");

        let scope1 = Scope::<Binder<String>, OrdVar>::new::<String>(
            Binder(v1.clone()),
            OrdVar(Var::Free(v1)),
        );
        let scope2 = Scope::<Binder<String>, OrdVar>::new::<String>(
            Binder(v2.clone()),
            OrdVar(Var::Free(v2)),
        );

        // term_eq populates the cache
        let _eq = scope1.term_eq(&scope2);
        assert!(
            term_eq_cache_size() > 0,
            "cache must have at least one entry after term_eq"
        );

        clear_term_eq_cache();
        assert_eq!(
            term_eq_cache_size(),
            0,
            "cache should be empty after clearing"
        );
    }
}
