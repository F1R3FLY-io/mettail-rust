//! Shared runtime infrastructure for iterative (trampolined) tree
//! traversals emitted by the `language!` macro.
//!
//! ## Motivation (Option B, HOL memory reduction)
//!
//! The `language!` macro emits seven iterative traversal engines per
//! language — Clone, PartialEq/Ord, Hash, Drop, Display, Debug, and
//! pattern-match. Each is a stack-based walk with a per-op Task enum,
//! a thread-local `Cell<Vec<Task>>` pool for zero-allocation reuse, a
//! `try_with` / `take` / `set` fallback dance for thread-shutdown
//! safety, and per-variant match arms.
//!
//! Pre-consolidation, the seven engine loops + pool plumbing were
//! written seven times per language (roughly 60–120 lines of shared
//! scaffold, emitted seven times into the `target/generated/<lang>/`
//! spill). This module factors the *scaffold* out so each per-op
//! generator emits only the per-variant handler body.
//!
//! ## Scope of this module
//!
//! - [`with_pool_or_fallback`] — thread-local pool access that falls
//!   back to a fresh heap-allocated `Vec` when TLS is unavailable
//!   (e.g., during thread shutdown). Every iterative traversal uses
//!   exactly this pattern; centralising it removes the `try_with` /
//!   `take` / `set` / fallback boilerplate from every emitter.
//! - [`PoolGuard`] — RAII-backed take/restore pattern that guarantees
//!   the pool is returned even on panic. Current generators hand-roll
//!   this and one of them ([`macros/src/gen/term_ops/iterative_drop.rs`])
//!   has a known landmine: `DROP_ACTIVE` is a bare flag with no panic
//!   guard, so a panic inside a variant arm leaves the flag set and
//!   wedges every subsequent drop on the same thread.
//!
//! The per-op `Task` enums, `impl Drop`/`impl Clone`/etc. shells, and
//! per-variant match arms remain per-language generator output — those
//! cannot be generic because the constructor set is grammar-dependent.
//!
//! ## Non-goals
//!
//! - This module does NOT provide the full generic `Visit<State>` +
//!   `run_visit` trait machinery that was originally scoped for Option
//!   B. That refactor would require reshaping all seven emitters to
//!   emit trait impls instead of free-function engines, which is a
//!   multi-day effort. The helpers here are a subset — the minimum
//!   common denominator that reduces emitted-code duplication without
//!   requiring the emitters to be restructured.
//!
//! ## Safety and re-entrancy
//!
//! These helpers are re-entrancy-safe: a nested call (e.g., Display
//! formatting a `HashBag<Proc>` that calls `HashBag::fmt` → `Proc::fmt`)
//! takes the pool, leaves an empty `Vec` in its place, and restores on
//! exit. An inner call sees the empty pool, allocates locally, and
//! returns its allocation to the pool on exit — same semantics as the
//! pre-consolidation hand-rolled code.

use std::cell::Cell;
use std::thread::LocalKey;

/// Run `f` with exclusive access to a thread-local `Vec` pool,
/// falling back to a fresh heap-allocated `Vec` when TLS is not
/// available (e.g., during thread shutdown).
///
/// The borrowed `Vec` is returned to the pool on successful exit via
/// [`Drop`] of [`PoolGuard`]. Even on panic the pool is restored,
/// preventing the "thread-local wedged" class of bugs that afflicts
/// bespoke implementations of this pattern.
///
/// # Example (generated-code shape, no user should call this directly)
///
/// ```ignore
/// thread_local! {
///     static DROP_POOL: Cell<Vec<DropTask>> = const { Cell::new(Vec::new()) };
/// }
///
/// fn drop_iter(root: DropTask) {
///     mettail_runtime::visitor::with_pool_or_fallback(&DROP_POOL, |stack| {
///         stack.push(root);
///         while let Some(task) = stack.pop() {
///             match task { /* per-variant */ }
///         }
///     });
/// }
/// ```
pub fn with_pool_or_fallback<T, F, R>(pool: &'static LocalKey<Cell<Vec<T>>>, f: F) -> R
where
    F: FnOnce(&mut Vec<T>) -> R,
{
    match pool.try_with(|cell| cell.take()) {
        Ok(mut stack) => {
            let result = std::panic::AssertUnwindSafe(|| f(&mut stack));
            let outcome = std::panic::catch_unwind(result);
            // Return the vec to the pool whether or not the closure
            // panicked. Clearing first so the next user sees an empty
            // pool rather than leftover state from a partial run.
            stack.clear();
            let _ = pool.try_with(|cell| cell.set(stack));
            match outcome {
                Ok(r) => r,
                Err(panic) => std::panic::resume_unwind(panic),
            }
        },
        Err(_) => {
            // TLS unavailable (thread shutdown). Fall back to local Vec.
            let mut stack: Vec<T> = Vec::new();
            f(&mut stack)
        },
    }
}

/// Run `f` with exclusive access to *two* thread-local `Vec` pools in
/// lock-step. Used by the two-phase Clone traversal which needs a
/// `CloneTask` stack AND a `Vec<Option<AnyClonedTerm>>` result buffer.
///
/// Same panic-safety guarantee as [`with_pool_or_fallback`].
pub fn with_two_pools_or_fallback<T, U, F, R>(
    task_pool: &'static LocalKey<Cell<Vec<T>>>,
    result_pool: &'static LocalKey<Cell<Vec<U>>>,
    f: F,
) -> R
where
    F: FnOnce(&mut Vec<T>, &mut Vec<U>) -> R,
{
    match (
        task_pool.try_with(|cell| cell.take()),
        result_pool.try_with(|cell| cell.take()),
    ) {
        (Ok(mut tasks), Ok(mut results)) => {
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                f(&mut tasks, &mut results)
            }));
            tasks.clear();
            results.clear();
            let _ = task_pool.try_with(|cell| cell.set(tasks));
            let _ = result_pool.try_with(|cell| cell.set(results));
            match outcome {
                Ok(r) => r,
                Err(panic) => std::panic::resume_unwind(panic),
            }
        },
        _ => {
            // TLS shutdown: fall back to local vecs.
            let mut tasks: Vec<T> = Vec::new();
            let mut results: Vec<U> = Vec::new();
            f(&mut tasks, &mut results)
        },
    }
}

/// RAII guard that sets a thread-local `Cell<bool>` flag on
/// construction and clears it on drop (including on panic unwind).
///
/// Used by generators that need a re-entrancy guard — specifically
/// the iterative Drop engine, where an inner `Drop::drop` call that
/// fires during dummy-value teardown must bail out of the iterative
/// loop to avoid re-entering it. The guard pattern ensures the flag
/// is cleared even if a variant arm panics.
pub struct FlagGuard {
    flag: &'static LocalKey<Cell<bool>>,
}

impl FlagGuard {
    /// Set the flag. Returns `Some(FlagGuard)` when the flag was previously
    /// unset (the caller is the outermost entry); returns `None` when the
    /// flag was already set (re-entrant call; caller should return early).
    pub fn try_enter(flag: &'static LocalKey<Cell<bool>>) -> Option<Self> {
        match flag.try_with(|cell| {
            if cell.get() {
                false
            } else {
                cell.set(true);
                true
            }
        }) {
            Ok(true) => Some(FlagGuard { flag }),
            _ => None,
        }
    }
}

impl Drop for FlagGuard {
    fn drop(&mut self) {
        let _ = self.flag.try_with(|cell| cell.set(false));
    }
}
