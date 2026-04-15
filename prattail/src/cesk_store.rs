//! CESK Store: Address-based indirection for mutable state.
//!
//! The CESK machine (Felleisen, 1986) extends the CEK machine with an explicit
//! **Store** component that introduces address-based indirection:
//!
//! - Environment maps variables to addresses: `env[var] → addr`
//! - Store maps addresses to values: `store[addr] → value`
//!
//! This enables mutation (`set!`), aliasing, closures with shared state, and
//! proper Rholang tuplespace semantics where names are shared through a global
//! namespace.
//!
//! ## Two-Tier Store Architecture
//!
//! ```text
//! ┌────────────────────────────────────────────────────────────────────┐
//! │                    Global Store (Tier 2)                           │
//! │  DashMap<u64, StoreValue>  — lock-free, shared across all threads │
//! │  Arc<AtomicU64> global_next_addr  — monotonic allocation          │
//! │  • Channel refs (StoreValue::ChannelRef(ChannelId))               │
//! │  • Names created by `new` (shared across P | Q)                   │
//! │  • GC: async mark-and-sweep (snapshot at coordinator idle)        │
//! ├──────────────────────────┬─────────────────────────────────────────┤
//! │     Green Thread 0       │      Green Thread 1                    │
//! │  ┌────────────────────┐  │  ┌────────────────────┐                │
//! │  │ Local Store (Tier 1)│  │  │ Local Store (Tier 1)│               │
//! │  │ im::HashMap (CoW)  │  │  │ im::HashMap (CoW)  │               │
//! │  │ • let bindings      │  │  │ • let bindings      │               │
//! │  │ • pattern match     │  │  │ • pattern match     │               │
//! │  │ • closure envs      │  │  │ • closure envs      │               │
//! │  │ AtomicU64 local_id  │  │  │ AtomicU64 local_id  │               │
//! │  │ GC: refcount (async)│  │  │ GC: refcount (async)│               │
//! │  └────────────────────┘  │  └────────────────────┘                │
//! └──────────────────────────┴─────────────────────────────────────────┘
//! ```
//!
//! ## Feature Gates
//!
//! - `cek-runtime`: Core types (`StoreAddr`, `StoreValue`, `LocalCeskStore`)
//! - `green-threads`: Concurrent types (`GlobalCeskStore`, `PersistentLocalStore`,
//!   `StoreValue::ChannelRef`)
//!
//! ## References
//!
//! - Felleisen, M. & Friedman, D. P. (1986). Control operators, the SECD-machine,
//!   and the λ-calculus.
//! - Van Horn, D. & Might, M. (2010). Abstracting Abstract Machines. *ICFP 2010*.
//! - Might, M. CESK machines tutorial.

use std::collections::HashMap;
use std::fmt;

use std::sync::atomic::{AtomicU64, Ordering};

use dashmap::DashMap;

use crate::channel::ChannelId;

// ══════════════════════════════════════════════════════════════════════════════
// StoreAddr — Tagged store address
// ══════════════════════════════════════════════════════════════════════════════

/// Tagged store address — dispatches lookups to the correct store tier.
///
/// The CESK environment maps variables to `StoreAddr` values. On lookup,
/// the variant determines which store tier to query:
///
/// - `Local(id)` → per-thread store (`LocalCeskStore` or `PersistentLocalStore`)
/// - `Global(id)` → shared store (`GlobalCeskStore` via `DashMap`)
///
/// Addresses are monotonically allocated within each tier (no reuse),
/// which simplifies GC epoch-based TOCTOU prevention.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum StoreAddr {
    /// Per-thread store address. Resolved in `LocalCeskStore` (standalone) or
    /// `PersistentLocalStore` (green threads). Single-writer — only the owning
    /// thread can read/write.
    Local(u64),
    /// Shared store address. Resolved in `GlobalCeskStore` (`DashMap`).
    /// Lock-free concurrent access from any thread.
    Global(u64),
}

impl StoreAddr {
    /// Extract the raw address id, regardless of tier.
    #[inline]
    pub fn id(&self) -> u64 {
        match self {
            StoreAddr::Local(id) | StoreAddr::Global(id) => *id,
        }
    }

    /// Whether this address points to the local store.
    #[inline]
    pub fn is_local(&self) -> bool {
        matches!(self, StoreAddr::Local(_))
    }

    /// Whether this address points to the global store.
    #[inline]
    pub fn is_global(&self) -> bool {
        matches!(self, StoreAddr::Global(_))
    }

    /// Extract the local id, returning an error if this is a global address.
    #[inline]
    pub fn local_id(&self) -> Result<u64, String> {
        match self {
            StoreAddr::Local(id) => Ok(*id),
            StoreAddr::Global(_) => Err("expected Local address, got Global".to_string()),
        }
    }

    /// Extract the global id, returning an error if this is a local address.
    #[inline]
    pub fn global_id(&self) -> Result<u64, String> {
        match self {
            StoreAddr::Global(id) => Ok(*id),
            StoreAddr::Local(_) => Err("expected Global address, got Local".to_string()),
        }
    }
}

impl fmt::Display for StoreAddr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StoreAddr::Local(id) => write!(f, "L#{}", id),
            StoreAddr::Global(id) => write!(f, "G#{}", id),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// StoreValue — Values stored in the CESK store
// ══════════════════════════════════════════════════════════════════════════════

/// A value stored in the CESK store.
///
/// The store maps addresses (`u64`) to these values. Each variant represents
/// a different kind of storable datum:
///
/// | Variant | Created By | Used For |
/// |---------|-----------|----------|
/// | `Simple` | `let x = v` | Scalar/string values |
/// | `Closure` | Lambda capture | Functions with captured env |
/// | `ChannelRef` | `new ch` | Channel lifecycle tracking |
/// | `Void` | `set!` result | Unit/void values |
///
/// Additional variants (`Relation`, `Constraint`, `RewriteRule`, `EClass`)
/// are added by later sprints (CESK-8 through CESK-11).
#[derive(Debug, Clone, PartialEq)]
pub enum StoreValue {
    /// A simple string value (numbers, identifiers, etc. in display form).
    Simple(String),

    /// A closure: a function body paired with a captured environment snapshot.
    ///
    /// The `env_snapshot` maps variable names to `StoreAddr` values that were
    /// in scope at the point of closure creation. When the closure is applied,
    /// the snapshot is restored as the evaluation environment.
    Closure {
        /// Captured variable bindings at closure creation time.
        env_snapshot: HashMap<String, StoreAddr>,
        /// The function body (display form).
        body: String,
    },

    /// A reference to a channel in the `ChannelMap`.
    ///
    /// The store tracks the channel's lifecycle: when the last `StoreAddr`
    /// pointing to a `ChannelRef` is garbage collected, `ChannelMap.dec_ref(ch_id)`
    /// is called, and at zero refs the channel entry is removed.
    ///
    /// Only available with the `green-threads` feature (channels require the
    /// concurrent runtime).
    ChannelRef(ChannelId),

    /// The void/unit value, produced by mutation operations (`set!`).
    Void,

    // ── CESK-8: Ascent Datalog bridge ───────────────────────────────────

    /// An Ascent-derived relation stored in the CESK store.
    ///
    /// After Ascent fixpoint completes, key relations (`rw_*`, `eq_*`, `fold_*`)
    /// are serialized into `Relation` entries. The evaluator's `Reducing` state
    /// can consult store-resident relations before falling back to full Ascent
    /// re-computation.
    Relation {
        /// Relation name (e.g., "rw_proc", "eq_name").
        name: String,
        /// (lhs, rhs) display pairs for this relation.
        tuples: Vec<(String, String)>,
    },

    // ── CESK-9: Type system constraint store ────────────────────────────

    /// A refinement type constraint stored alongside a variable's value.
    ///
    /// When a refinement-typed variable is bound, the constraint is stored
    /// in the CESK store. Subsequent access can check constraint satisfaction
    /// lazily. Constraints compose: binding `x: {v: Int | v > 0}` then
    /// `y = x + 1` propagates `{v: Int | v > 1}` to y's constraint entry.
    Constraint {
        /// ConstraintDomain name (e.g., "NonNeg", "Bounded").
        domain: String,
        /// Display form of the constraint predicate.
        predicate: String,
        /// Variables bound by the constraint.
        bindings: Vec<String>,
    },

    // ── CESK-10: Meta-level rewriting ───────────────────────────────────

    /// A first-class rewrite rule stored in the CESK store.
    ///
    /// Makes rewrite rules first-class store values, enabling MeTTa-style
    /// meta-programming where programs can inspect and modify their own
    /// rewrite rules at runtime.
    RewriteRule {
        /// Rule identifier.
        name: String,
        /// LHS pattern (display form).
        lhs_pattern: String,
        /// RHS template (display form).
        rhs_template: String,
        /// Rule priority (lower = higher priority).
        priority: u32,
        /// Whether the rule is currently active (can be dynamically toggled).
        active: bool,
    },

    // ── CESK-11: E-graph bridge ─────────────────────────────────────────

    /// An e-graph equivalence class exposed to the evaluator.
    ///
    /// After equality saturation completes, e-classes are exported to the
    /// global store. The evaluator can substitute the cost leader during
    /// reduction for equality-preserving optimization.
    EClass {
        /// E-class identifier.
        class_id: u64,
        /// Display forms of equivalent terms in this class.
        members: Vec<String>,
        /// Cheapest member by extraction cost.
        cost_leader: String,
    },
}

impl StoreValue {
    /// Whether this is a `Simple` value.
    #[inline]
    pub fn is_simple(&self) -> bool {
        matches!(self, StoreValue::Simple(_))
    }

    /// Whether this is a `Closure`.
    #[inline]
    pub fn is_closure(&self) -> bool {
        matches!(self, StoreValue::Closure { .. })
    }

    /// Whether this is a `ChannelRef`.
    #[inline]
    pub fn is_channel_ref(&self) -> bool {
        {
            matches!(self, StoreValue::ChannelRef(_))
        }
    }

    /// Whether this is `Void`.
    #[inline]
    pub fn is_void(&self) -> bool {
        matches!(self, StoreValue::Void)
    }

    /// Extract the string value from a `Simple`, or `None`.
    pub fn as_simple(&self) -> Option<&str> {
        match self {
            StoreValue::Simple(s) => Some(s),
            _ => None,
        }
    }

    /// Extract the closure components, or `None`.
    pub fn as_closure(&self) -> Option<(&HashMap<String, StoreAddr>, &str)> {
        match self {
            StoreValue::Closure { env_snapshot, body } => Some((env_snapshot, body)),
            _ => None,
        }
    }

    /// Extract the `ChannelId` from a `ChannelRef`, or `None`.
    pub fn as_channel_ref(&self) -> Option<ChannelId> {
        match self {
            StoreValue::ChannelRef(id) => Some(*id),
            _ => None,
        }
    }

    /// Whether this is a `Relation`.
    #[inline]
    pub fn is_relation(&self) -> bool {
        matches!(self, StoreValue::Relation { .. })
    }

    /// Extract the relation tuples, or `None`.
    pub fn as_relation(&self) -> Option<(&str, &[(String, String)])> {
        match self {
            StoreValue::Relation { name, tuples } => Some((name, tuples)),
            _ => None,
        }
    }

    /// Whether this is a `Constraint`.
    #[inline]
    pub fn is_constraint(&self) -> bool {
        matches!(self, StoreValue::Constraint { .. })
    }

    /// Extract the constraint components, or `None`.
    pub fn as_constraint(&self) -> Option<(&str, &str, &[String])> {
        match self {
            StoreValue::Constraint {
                domain,
                predicate,
                bindings,
            } => Some((domain, predicate, bindings)),
            _ => None,
        }
    }

    /// Whether this is a `RewriteRule`.
    #[inline]
    pub fn is_rewrite_rule(&self) -> bool {
        matches!(self, StoreValue::RewriteRule { .. })
    }

    /// Extract the rewrite rule components, or `None`.
    pub fn as_rewrite_rule(&self) -> Option<(&str, &str, &str, u32, bool)> {
        match self {
            StoreValue::RewriteRule {
                name,
                lhs_pattern,
                rhs_template,
                priority,
                active,
            } => Some((name, lhs_pattern, rhs_template, *priority, *active)),
            _ => None,
        }
    }

    /// Whether this is an `EClass`.
    #[inline]
    pub fn is_eclass(&self) -> bool {
        matches!(self, StoreValue::EClass { .. })
    }

    /// Extract the e-class components, or `None`.
    pub fn as_eclass(&self) -> Option<(u64, &[String], &str)> {
        match self {
            StoreValue::EClass {
                class_id,
                members,
                cost_leader,
            } => Some((*class_id, members, cost_leader)),
            _ => None,
        }
    }
}

impl fmt::Display for StoreValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StoreValue::Simple(s) => write!(f, "{}", s),
            StoreValue::Closure { body, env_snapshot } => {
                write!(f, "<closure({} bindings) {}>", env_snapshot.len(), body)
            }
            StoreValue::ChannelRef(ch_id) => write!(f, "<channel-ref {}>", ch_id),
            StoreValue::Void => write!(f, "void"),
            StoreValue::Relation { name, tuples } => {
                write!(f, "<relation {} ({} tuples)>", name, tuples.len())
            }
            StoreValue::Constraint {
                domain, predicate, ..
            } => write!(f, "<constraint {}:{}>", domain, predicate),
            StoreValue::RewriteRule {
                name,
                active,
                priority,
                ..
            } => write!(
                f,
                "<rule {} p={} {}>",
                name,
                priority,
                if *active { "on" } else { "off" }
            ),
            StoreValue::EClass {
                class_id,
                members,
                cost_leader,
            } => write!(
                f,
                "<eclass #{} ({} members, leader={})>",
                class_id,
                members.len(),
                cost_leader
            ),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// LocalCeskStore — Single-writer per-evaluator store (HashMap-based)
// ══════════════════════════════════════════════════════════════════════════════

/// Local CESK store — single-writer, per-evaluator or per-green-thread.
///
/// Used by the standalone `CekEvaluator` (REPL, tests, single-threaded eval).
/// Backed by a standard `HashMap<u64, StoreValue>` with monotonically increasing
/// address allocation.
///
/// ## Thread Safety
///
/// Not `Sync` — only the owning evaluator reads/writes. This is intentional:
/// the local store is for bindings that never cross thread boundaries (let-bindings,
/// pattern-match results, closure environments).
///
/// ## Allocation
///
/// Addresses are allocated by bumping `next_addr`. Allocation never reuses
/// addresses, which simplifies GC: a freed address is simply removed from
/// the `cells` map, and any future alloc gets a strictly larger address.
#[derive(Debug, Clone)]
pub struct LocalCeskStore {
    /// Store cells: addr → value.
    cells: HashMap<u64, StoreValue>,
    /// Next address to allocate (monotonically increasing).
    next_addr: u64,
}

impl LocalCeskStore {
    /// Create an empty local store.
    pub fn new() -> Self {
        Self {
            cells: HashMap::new(),
            next_addr: 0,
        }
    }

    /// Create a local store with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            cells: HashMap::with_capacity(capacity),
            next_addr: 0,
        }
    }

    /// Allocate a fresh address without storing a value.
    ///
    /// The address is reserved (bumped) but no value is stored. The caller
    /// must subsequently call `set()` to populate it.
    pub fn alloc(&mut self) -> u64 {
        let addr = self.next_addr;
        self.next_addr += 1;
        addr
    }

    /// Allocate a fresh address and store a value in one step.
    ///
    /// Returns the allocated address.
    pub fn alloc_with(&mut self, value: StoreValue) -> u64 {
        let addr = self.alloc();
        self.cells.insert(addr, value);
        addr
    }

    /// Look up a value by address.
    pub fn get(&self, addr: u64) -> Option<&StoreValue> {
        self.cells.get(&addr)
    }

    /// Look up a value by address, returning a clone.
    ///
    /// Useful when the caller needs an owned value (e.g., for trait-based
    /// resolution where the return type must be `Option<StoreValue>`).
    pub fn get_cloned(&self, addr: u64) -> Option<StoreValue> {
        self.cells.get(&addr).cloned()
    }

    /// Set (overwrite) the value at an existing address.
    ///
    /// Used for mutation (`set!`). The address must have been previously
    /// allocated. No-op if the address does not exist.
    pub fn set(&mut self, addr: u64, value: StoreValue) {
        if self.cells.contains_key(&addr) {
            self.cells.insert(addr, value);
        }
    }

    /// Remove a value from the store, returning it if present.
    ///
    /// Used by GC when an address becomes unreachable.
    pub fn remove(&mut self, addr: u64) -> Option<StoreValue> {
        self.cells.remove(&addr)
    }

    /// Number of values currently stored.
    #[inline]
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    /// Whether the store is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// Whether the store contains a value at the given address.
    #[inline]
    pub fn contains(&self, addr: u64) -> bool {
        self.cells.contains_key(&addr)
    }

    /// The next address that will be allocated.
    ///
    /// Useful for diagnostics and testing.
    #[inline]
    pub fn next_addr(&self) -> u64 {
        self.next_addr
    }

    /// Iterate over all (addr, value) pairs.
    pub fn iter(&self) -> impl Iterator<Item = (&u64, &StoreValue)> {
        self.cells.iter()
    }

    /// Collect all addresses currently in the store.
    pub fn addresses(&self) -> Vec<u64> {
        self.cells.keys().copied().collect()
    }

    /// Clear all cells but preserve the address counter.
    ///
    /// After clearing, previously allocated addresses are still "consumed"
    /// — new allocations continue from `next_addr`, not from 0.
    pub fn clear(&mut self) {
        self.cells.clear();
    }

    /// Reset the store completely (clear cells AND reset address counter).
    ///
    /// Only appropriate for full evaluator reset.
    pub fn reset(&mut self) {
        self.cells.clear();
        self.next_addr = 0;
    }
}

impl Default for LocalCeskStore {
    fn default() -> Self {
        Self::new()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// GlobalCeskStore — Lock-free concurrent shared store (DashMap-based)
// ══════════════════════════════════════════════════════════════════════════════

/// Global CESK store — shared, lock-free concurrent access via `DashMap`.
///
/// Used for values that must be accessible across green threads:
/// - Channel references (`StoreValue::ChannelRef`)
/// - Names created by Rholang's `new` (shared across `P | Q`)
///
/// ## Allocation
///
/// Uses `AtomicU64` for lock-free monotonic address allocation. Multiple
/// threads can allocate concurrently without contention (each gets a unique
/// address via `fetch_add`).
///
/// ## Epoch Tracking
///
/// Maintains an `epoch` counter incremented on each allocation. The GC
/// snapshot captures the current epoch; any address allocated after the
/// snapshot epoch is exempt from collection (TOCTOU prevention).
///
/// ## Feature Gate
///
/// Requires `green-threads` (which transitively enables `cek-runtime`).
#[derive(Debug)]
pub struct GlobalCeskStore {
    /// Store cells: addr → value (lock-free sharded map).
    cells: DashMap<u64, StoreValue>,
    /// Next address to allocate (atomic, monotonically increasing).
    next_addr: AtomicU64,
    /// Epoch counter for GC TOCTOU prevention. Incremented on each alloc.
    epoch: AtomicU64,
}

impl GlobalCeskStore {
    /// Create an empty global store.
    pub fn new() -> Self {
        Self {
            cells: DashMap::new(),
            next_addr: AtomicU64::new(0),
            epoch: AtomicU64::new(0),
        }
    }

    /// Create a global store with pre-allocated shard capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            cells: DashMap::with_capacity(capacity),
            next_addr: AtomicU64::new(0),
            epoch: AtomicU64::new(0),
        }
    }

    /// Allocate a fresh address without storing a value.
    ///
    /// Thread-safe: uses `fetch_add` for lock-free monotonic allocation.
    /// Increments the epoch counter.
    pub fn alloc(&self) -> u64 {
        self.epoch.fetch_add(1, Ordering::Relaxed);
        self.next_addr.fetch_add(1, Ordering::Relaxed)
    }

    /// Allocate a fresh address and store a value atomically.
    ///
    /// Thread-safe: the address is allocated via `fetch_add`, then the
    /// value is inserted into the `DashMap`.
    pub fn alloc_with(&self, value: StoreValue) -> u64 {
        let addr = self.alloc();
        self.cells.insert(addr, value);
        addr
    }

    /// Look up a value by address, returning a clone.
    ///
    /// Returns `None` if the address is not present. The value is cloned
    /// out of the `DashMap` guard because `DashMap::Ref` has a limited
    /// lifetime tied to the internal shard lock.
    pub fn get(&self, addr: u64) -> Option<StoreValue> {
        self.cells.get(&addr).map(|entry| entry.value().clone())
    }

    /// Set (overwrite) the value at an existing address.
    ///
    /// Thread-safe via `DashMap`'s internal sharded locking.
    /// No-op if the address does not exist.
    pub fn set(&self, addr: u64, value: StoreValue) {
        if let Some(mut entry) = self.cells.get_mut(&addr) {
            *entry.value_mut() = value;
        }
    }

    /// Remove a value from the store, returning it if present.
    ///
    /// Thread-safe. Used by GC sweep phase.
    pub fn remove(&self, addr: u64) -> Option<StoreValue> {
        self.cells.remove(&addr).map(|(_, v)| v)
    }

    /// Number of values currently stored.
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    /// Whether the store is empty.
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// Whether the store contains a value at the given address.
    pub fn contains(&self, addr: u64) -> bool {
        self.cells.contains_key(&addr)
    }

    /// The current epoch (number of allocations performed).
    ///
    /// Used by GC to determine which addresses were allocated after a
    /// snapshot was taken (those are exempt from collection).
    pub fn current_epoch(&self) -> u64 {
        self.epoch.load(Ordering::Acquire)
    }

    /// The next address that will be allocated.
    pub fn next_addr(&self) -> u64 {
        self.next_addr.load(Ordering::Acquire)
    }

    /// Collect all addresses currently in the store.
    ///
    /// Used by GC for constructing root sets and sweep targets.
    /// Iterates the entire `DashMap` — O(n) but only called during GC.
    pub fn addresses(&self) -> Vec<u64> {
        self.cells.iter().map(|entry| *entry.key()).collect()
    }

    /// Remove multiple addresses in bulk.
    ///
    /// Used by GC sweep phase to remove dead addresses efficiently.
    /// Returns the number of addresses actually removed.
    pub fn remove_bulk(&self, addrs: &[u64]) -> usize {
        let mut removed = 0;
        for &addr in addrs {
            if self.cells.remove(&addr).is_some() {
                removed += 1;
            }
        }
        removed
    }
}

impl Default for GlobalCeskStore {
    fn default() -> Self {
        Self::new()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// PersistentLocalStore — O(1) fork via im::HashMap (green threads)
// ══════════════════════════════════════════════════════════════════════════════

/// Persistent local store for green threads — O(1) fork via `im::HashMap`.
///
/// Each green thread owns a `PersistentLocalStore` for its local bindings
/// (let-bindings, pattern-match results, closure environments). When a
/// thread forks via `P | Q`, the child receives a structural-sharing clone
/// of the parent's store in O(1) time. Subsequent mutations on either
/// parent or child diverge via copy-on-write at the affected tree nodes.
///
/// ## Why `im::HashMap` Instead of `HashMap`?
///
/// Standard `HashMap::clone()` is O(n) — it copies all entries. For Rholang's
/// heavily-forking `P | Q` pattern, this would be prohibitively expensive.
/// `im::HashMap` uses a Hash Array Mapped Trie (HAMT) with reference-counted
/// nodes, giving O(1) clone and O(log₃₂ n) read/write.
///
/// ## Feature Gate
///
/// Requires `green-threads`.
#[derive(Debug, Clone)]
pub struct PersistentLocalStore {
    /// Store cells: addr → value (persistent HAMT).
    cells: im::HashMap<u64, StoreValue>,
    /// Next address to allocate. Per-thread — not shared (local addrs
    /// are thread-local, so there's no contention).
    next_addr: u64,
}

impl PersistentLocalStore {
    /// Create an empty persistent local store.
    pub fn new() -> Self {
        Self {
            cells: im::HashMap::new(),
            next_addr: 0,
        }
    }

    /// Allocate a fresh address without storing a value.
    pub fn alloc(&mut self) -> u64 {
        let addr = self.next_addr;
        self.next_addr += 1;
        addr
    }

    /// Allocate a fresh address and store a value.
    pub fn alloc_with(&mut self, value: StoreValue) -> u64 {
        let addr = self.alloc();
        self.cells.insert(addr, value);
        addr
    }

    /// Look up a value by address.
    pub fn get(&self, addr: u64) -> Option<&StoreValue> {
        self.cells.get(&addr)
    }

    /// Look up a value by address, returning a clone.
    pub fn get_cloned(&self, addr: u64) -> Option<StoreValue> {
        self.cells.get(&addr).cloned()
    }

    /// Set (overwrite) the value at an existing address.
    ///
    /// Uses `im::HashMap::insert` which creates a new path from root to
    /// the modified node — O(log₃₂ n). Other threads sharing the old
    /// tree structure are unaffected (copy-on-write).
    pub fn set(&mut self, addr: u64, value: StoreValue) {
        if self.cells.contains_key(&addr) {
            self.cells.insert(addr, value);
        }
    }

    /// Remove a value from the store.
    pub fn remove(&mut self, addr: u64) -> Option<StoreValue> {
        self.cells.remove(&addr)
    }

    /// Number of values currently stored.
    #[inline]
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    /// Whether the store is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// Whether the store contains a value at the given address.
    #[inline]
    pub fn contains(&self, addr: u64) -> bool {
        self.cells.contains_key(&addr)
    }

    /// The next address that will be allocated.
    #[inline]
    pub fn next_addr(&self) -> u64 {
        self.next_addr
    }

    /// O(1) fork: create a child store sharing the parent's data.
    ///
    /// The child receives a structural-sharing clone of all cells.
    /// Subsequent mutations on either parent or child are isolated
    /// via copy-on-write. The child's `next_addr` continues from the
    /// parent's current value, so address spaces don't overlap.
    ///
    /// This is the key operation enabling efficient `P | Q` forking
    /// in the green thread runtime.
    pub fn fork(&self) -> PersistentLocalStore {
        PersistentLocalStore {
            cells: self.cells.clone(), // O(1) — structural sharing via Arc
            next_addr: self.next_addr,
        }
    }

    /// Collect all addresses currently in the store.
    pub fn addresses(&self) -> Vec<u64> {
        self.cells.keys().copied().collect()
    }

    /// Iterate over all (addr, value) pairs.
    pub fn iter(&self) -> impl Iterator<Item = (&u64, &StoreValue)> {
        self.cells.iter()
    }

    /// Collect all `StoreAddr::Global` addresses reachable from values in this store.
    ///
    /// Used by GC root set construction: the global store's mark-and-sweep GC
    /// needs to know which global addresses are reachable from each thread's
    /// local store (e.g., closures capturing global channel refs).
    pub fn collect_global_roots(&self) -> Vec<u64> {
        let mut roots = Vec::new();
        for (_, value) in self.cells.iter() {
            Self::collect_global_addrs_from_value(value, &mut roots);
        }
        roots
    }

    /// Recursively collect global addresses from a store value.
    fn collect_global_addrs_from_value(value: &StoreValue, roots: &mut Vec<u64>) {
        match value {
            StoreValue::Closure { env_snapshot, .. } => {
                for addr in env_snapshot.values() {
                    if let StoreAddr::Global(id) = addr {
                        roots.push(*id);
                    }
                }
            }
            // These variants don't contain store address references
            StoreValue::Simple(_)
            | StoreValue::Void
            | StoreValue::Relation { .. }
            | StoreValue::Constraint { .. }
            | StoreValue::RewriteRule { .. }
            | StoreValue::EClass { .. } => {}
            // ChannelRef is already in global store (no nested addrs)
            StoreValue::ChannelRef(_) => {}
        }
    }
}

impl Default for PersistentLocalStore {
    fn default() -> Self {
        Self::new()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// StoreResolver — Unified resolution trait
// ══════════════════════════════════════════════════════════════════════════════

/// Trait for resolving store addresses to values.
///
/// Provides a uniform interface for address resolution regardless of
/// the backing store implementation. Returns owned (`StoreValue`) values
/// because `DashMap` lookups cannot return plain references (they return
/// guard objects with limited lifetimes).
///
/// ## Implementors
///
/// - `LocalCeskStore`: Resolves `Local` addresses; panics on `Global`.
/// - Combined resolver (in green thread runtime): Dispatches to local
///   or global store based on the `StoreAddr` variant.
pub trait StoreResolver {
    /// Resolve a store address to its value.
    ///
    /// Returns `None` if the address is not present in the appropriate store.
    fn resolve(&self, addr: StoreAddr) -> Option<StoreValue>;

    /// Allocate a new local address and store a value.
    ///
    /// Returns the allocated `StoreAddr::Local(id)`.
    fn alloc_local(&mut self, val: StoreValue) -> StoreAddr;
}

impl StoreResolver for LocalCeskStore {
    fn resolve(&self, addr: StoreAddr) -> Option<StoreValue> {
        match addr {
            StoreAddr::Local(id) => self.get_cloned(id),
            StoreAddr::Global(_) => None, // Standalone evaluator has no global store
        }
    }

    fn alloc_local(&mut self, val: StoreValue) -> StoreAddr {
        StoreAddr::Local(self.alloc_with(val))
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// GcSnapshot — Frozen store state for mark-and-sweep GC
// ══════════════════════════════════════════════════════════════════════════════

/// A frozen snapshot of the global store for mark-and-sweep GC.
///
/// Constructed by the coordinator at `ParkIdle` (when all green threads
/// have yielded). The GC worker thread operates on this snapshot without
/// touching the live store, avoiding data races.
///
/// ## Epoch-Based TOCTOU Prevention
///
/// The `epoch` field records the global store's allocation epoch at snapshot
/// time. Any address allocated after this epoch is exempt from collection
/// — it was created after the snapshot and therefore wasn't considered
/// during the mark phase.
#[derive(Debug, Clone)]
pub struct GcSnapshot {
    /// Root set: global addresses reachable from all threads' environments.
    pub roots: Vec<u64>,
    /// Frozen copy of the global store's cells.
    pub store_cells: HashMap<u64, StoreValue>,
    /// Global store epoch at snapshot time (for TOCTOU filtering).
    pub epoch: u64,
}

impl GcSnapshot {
    /// Create a new GC snapshot.
    pub fn new(roots: Vec<u64>, store_cells: HashMap<u64, StoreValue>, epoch: u64) -> Self {
        Self {
            roots,
            store_cells,
            epoch,
        }
    }

    /// Number of roots in this snapshot.
    #[inline]
    pub fn root_count(&self) -> usize {
        self.roots.len()
    }

    /// Number of store cells in this snapshot.
    #[inline]
    pub fn cell_count(&self) -> usize {
        self.store_cells.len()
    }
}

/// Response from a completed mark-and-sweep GC cycle.
///
/// Contains the addresses determined to be unreachable (dead) and the
/// epoch at which the snapshot was taken. The coordinator filters by
/// epoch before applying removals.
#[derive(Debug, Clone)]
pub struct GcResponse {
    /// Addresses in the global store that are unreachable.
    pub dead_addrs: Vec<u64>,
    /// Channel IDs that should be decremented (from dead `ChannelRef` values).
    pub dead_channel_refs: Vec<ChannelId>,
    /// Epoch of the snapshot that produced this response.
    pub snapshot_epoch: u64,
}

// ══════════════════════════════════════════════════════════════════════════════
// CESK-12: Parameterized Allocation (AAM tick/alloc)
// ══════════════════════════════════════════════════════════════════════════════

/// Machine configuration for parameterized allocation strategies.
///
/// Contains the state information needed by `AllocStrategy::alloc()` to
/// decide which address to return. The fields mirror the CESK_t machine:
/// `(e, ρ, σ, κ, t)` — expression, environment, store, continuation, time.
#[derive(Debug, Clone)]
pub struct CeskConfig {
    /// Current control expression (display form).
    pub control: String,
    /// Number of environment bindings.
    pub env_size: usize,
    /// Number of store cells.
    pub store_size: usize,
    /// Continuation stack depth.
    pub stack_depth: usize,
}

/// Parameterized allocation strategy for the CESK_t machine.
///
/// Following Van Horn & Might's "Abstracting Abstract Machines" (ICFP 2010, §2.4),
/// the CESK machine is parameterized by two functions:
///
/// - `tick(Σ) → Time` — advances the time component
/// - `alloc(var, Σ) → Addr` — chooses addresses based on computation state
///
/// This is the knob for tuning **polyvariance and context-sensitivity**:
///
/// | Analysis | Addr | alloc(v, ĉ) |
/// |----------|------|-------------|
/// | Concrete | `u64` | Monotonic counter (default) |
/// | 0CFA | `Var` | `hash(v)` — monovariant |
/// | 1CFA | `Var × Exp` | `hash(v, e)` — context-sensitive |
/// | k-CFA | `Var × Exp^k` | `hash(v, ⟨e₁,...,eₖ⟩)` |
pub trait AllocStrategy: Send + Sync + std::fmt::Debug {
    /// Advance the time component of the machine (no-op for concrete execution).
    fn tick(&self, _config: &CeskConfig) {}

    /// Allocate an address for a variable given the current machine state.
    ///
    /// For concrete execution, returns a fresh monotonic address.
    /// For abstract interpretation, may return an address based on the
    /// variable name and/or call-site context.
    fn alloc(&self, var: &str, config: &CeskConfig) -> u64;

    /// Human-readable name of this strategy (for diagnostics).
    fn name(&self) -> &'static str;
}

/// Concrete monotonic allocation (default).
///
/// Each `alloc()` returns a fresh, strictly increasing address. This is
/// the standard concrete execution behavior: infinite address space,
/// every binding gets a unique cell.
#[derive(Debug)]
pub struct MonotonicAlloc {
    /// Monotonically increasing counter (atomic for Send+Sync).
    next: std::sync::atomic::AtomicU64,
}

impl MonotonicAlloc {
    /// Create a new monotonic allocator starting from 0.
    pub fn new() -> Self {
        Self {
            next: std::sync::atomic::AtomicU64::new(0),
        }
    }

    /// Create a new monotonic allocator starting from a given address.
    pub fn from(start: u64) -> Self {
        Self {
            next: std::sync::atomic::AtomicU64::new(start),
        }
    }
}

impl Default for MonotonicAlloc {
    fn default() -> Self {
        Self::new()
    }
}

impl AllocStrategy for MonotonicAlloc {
    fn alloc(&self, _var: &str, _config: &CeskConfig) -> u64 {
        self.next.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    }

    fn name(&self) -> &'static str {
        "MonotonicAlloc"
    }
}

/// 0CFA (monovariant) allocation: `Addr = hash(Var)`.
///
/// Every binding of the same variable name gets the same address.
/// This collapses all flows through a variable into one abstract cell,
/// making the state space finite (enables fixpoint computation).
#[derive(Debug, Clone, Default)]
pub struct ZeroCfaAlloc;

impl AllocStrategy for ZeroCfaAlloc {
    fn alloc(&self, var: &str, _config: &CeskConfig) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        var.hash(&mut hasher);
        hasher.finish()
    }

    fn name(&self) -> &'static str {
        "0CFA"
    }
}

/// 1CFA (context-sensitive) allocation: `Addr = hash(Var, Exp)`.
///
/// Each binding gets an address that depends on both the variable name
/// and the current control expression. Different call sites produce
/// different addresses for the same variable.
#[derive(Debug, Clone, Default)]
pub struct OneCfaAlloc;

impl AllocStrategy for OneCfaAlloc {
    fn alloc(&self, var: &str, config: &CeskConfig) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        var.hash(&mut hasher);
        config.control.hash(&mut hasher);
        hasher.finish()
    }

    fn name(&self) -> &'static str {
        "1CFA"
    }
}

/// k-CFA allocation: `Addr = hash(Var, Exp^k)`.
///
/// Generalizes 1CFA to use the last `k` expressions as context.
/// Higher `k` gives more precision but exponentially larger state space.
#[derive(Debug)]
pub struct KCfaAlloc {
    /// Context depth (number of expressions to track).
    pub k: usize,
    /// Ring buffer of the last `k` control expressions (Mutex for Send+Sync).
    context: std::sync::Mutex<Vec<String>>,
}

impl KCfaAlloc {
    /// Create a k-CFA allocator with the given context depth.
    pub fn new(k: usize) -> Self {
        Self {
            k,
            context: std::sync::Mutex::new(Vec::with_capacity(k)),
        }
    }
}

impl AllocStrategy for KCfaAlloc {
    fn tick(&self, config: &CeskConfig) {
        let mut ctx = self.context.lock().expect("KCfaAlloc context lock poisoned");
        if ctx.len() >= self.k {
            ctx.remove(0);
        }
        ctx.push(config.control.clone());
    }

    fn alloc(&self, var: &str, _config: &CeskConfig) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        var.hash(&mut hasher);
        let ctx = self.context.lock().expect("KCfaAlloc context lock poisoned");
        for expr in ctx.iter() {
            expr.hash(&mut hasher);
        }
        hasher.finish()
    }

    fn name(&self) -> &'static str {
        "k-CFA"
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    // ── StoreAddr tests ─────────────────────────────────────────────────

    #[test]
    fn store_addr_local_properties() {
        let addr = StoreAddr::Local(42);
        assert!(addr.is_local());
        assert!(!addr.is_global());
        assert_eq!(addr.id(), 42);
        assert_eq!(addr.local_id().expect("should be Local"), 42);
        assert_eq!(format!("{}", addr), "L#42");
    }

    #[test]
    fn store_addr_global_properties() {
        let addr = StoreAddr::Global(99);
        assert!(addr.is_global());
        assert!(!addr.is_local());
        assert_eq!(addr.id(), 99);
        assert_eq!(addr.global_id().expect("should be Global"), 99);
        assert_eq!(format!("{}", addr), "G#99");
    }

    #[test]
    fn store_addr_local_id_panics_on_global() {
        let err = StoreAddr::Global(0).local_id().unwrap_err();
        assert!(err.contains("expected Local address, got Global"), "{err}");
    }

    #[test]
    fn store_addr_global_id_panics_on_local() {
        let err = StoreAddr::Local(0).global_id().unwrap_err();
        assert!(err.contains("expected Global address, got Local"), "{err}");
    }

    #[test]
    fn store_addr_ordering() {
        // Local < Global for same id (enum variant order)
        assert!(StoreAddr::Local(0) < StoreAddr::Global(0));
        // Within same variant, ordered by id
        assert!(StoreAddr::Local(1) < StoreAddr::Local(2));
        assert!(StoreAddr::Global(5) < StoreAddr::Global(10));
    }

    // ── StoreValue tests ────────────────────────────────────────────────

    #[test]
    fn store_value_simple() {
        let val = StoreValue::Simple("42".to_string());
        assert!(val.is_simple());
        assert!(!val.is_closure());
        assert!(!val.is_void());
        assert_eq!(val.as_simple(), Some("42"));
        assert_eq!(format!("{}", val), "42");
    }

    #[test]
    fn store_value_closure() {
        let mut env = HashMap::new();
        env.insert("x".to_string(), StoreAddr::Local(0));
        let val = StoreValue::Closure {
            env_snapshot: env.clone(),
            body: "(+ x 1)".to_string(),
        };
        assert!(val.is_closure());
        let (snap, body) = val.as_closure().expect("should be closure");
        assert_eq!(snap.len(), 1);
        assert_eq!(body, "(+ x 1)");
        assert!(format!("{}", val).contains("closure"));
    }

    #[test]
    fn store_value_void() {
        let val = StoreValue::Void;
        assert!(val.is_void());
        assert_eq!(format!("{}", val), "void");
    }

    // ── LocalCeskStore tests ────────────────────────────────────────────

    #[test]
    fn local_store_new_is_empty() {
        let store = LocalCeskStore::new();
        assert!(store.is_empty());
        assert_eq!(store.len(), 0);
        assert_eq!(store.next_addr(), 0);
    }

    #[test]
    fn local_store_alloc_monotonic() {
        let mut store = LocalCeskStore::new();
        let a0 = store.alloc();
        let a1 = store.alloc();
        let a2 = store.alloc();
        assert_eq!(a0, 0);
        assert_eq!(a1, 1);
        assert_eq!(a2, 2);
        assert_eq!(store.next_addr(), 3);
    }

    #[test]
    fn local_store_alloc_with_and_get() {
        let mut store = LocalCeskStore::new();
        let addr = store.alloc_with(StoreValue::Simple("hello".to_string()));
        assert_eq!(addr, 0);
        assert_eq!(store.len(), 1);
        assert!(store.contains(addr));
        let val = store.get(addr).expect("should be present");
        assert_eq!(val.as_simple(), Some("hello"));
    }

    #[test]
    fn local_store_set_overwrites() {
        let mut store = LocalCeskStore::new();
        let addr = store.alloc_with(StoreValue::Simple("old".to_string()));
        store.set(addr, StoreValue::Simple("new".to_string()));
        assert_eq!(store.get(addr).unwrap().as_simple(), Some("new"));
    }

    #[test]
    fn local_store_set_noop_for_missing() {
        let mut store = LocalCeskStore::new();
        // Set on a non-existent address is a no-op
        store.set(999, StoreValue::Simple("ghost".to_string()));
        assert!(!store.contains(999));
    }

    #[test]
    fn local_store_remove() {
        let mut store = LocalCeskStore::new();
        let addr = store.alloc_with(StoreValue::Simple("temp".to_string()));
        let removed = store.remove(addr);
        assert_eq!(removed.unwrap().as_simple(), Some("temp"));
        assert!(!store.contains(addr));
        assert_eq!(store.len(), 0);
        // Address counter not reset — next alloc is still monotonic
        assert_eq!(store.next_addr(), 1);
    }

    #[test]
    fn local_store_clear_preserves_counter() {
        let mut store = LocalCeskStore::new();
        store.alloc_with(StoreValue::Void);
        store.alloc_with(StoreValue::Void);
        store.clear();
        assert!(store.is_empty());
        assert_eq!(store.next_addr(), 2); // Counter preserved
    }

    #[test]
    fn local_store_reset_resets_counter() {
        let mut store = LocalCeskStore::new();
        store.alloc_with(StoreValue::Void);
        store.reset();
        assert!(store.is_empty());
        assert_eq!(store.next_addr(), 0); // Counter reset
    }

    #[test]
    fn local_store_multiple_values() {
        let mut store = LocalCeskStore::new();
        let a0 = store.alloc_with(StoreValue::Simple("zero".to_string()));
        let a1 = store.alloc_with(StoreValue::Simple("one".to_string()));
        let a2 = store.alloc_with(StoreValue::Void);
        assert_eq!(store.len(), 3);
        assert_eq!(store.get(a0).unwrap().as_simple(), Some("zero"));
        assert_eq!(store.get(a1).unwrap().as_simple(), Some("one"));
        assert!(store.get(a2).unwrap().is_void());
    }

    #[test]
    fn local_store_addresses_and_iter() {
        let mut store = LocalCeskStore::new();
        store.alloc_with(StoreValue::Simple("a".to_string()));
        store.alloc_with(StoreValue::Simple("b".to_string()));
        let mut addrs = store.addresses();
        addrs.sort();
        assert_eq!(addrs, vec![0, 1]);
        assert_eq!(store.iter().count(), 2);
    }

    // ── StoreResolver for LocalCeskStore ────────────────────────────────

    #[test]
    fn store_resolver_local_resolve() {
        let mut store = LocalCeskStore::new();
        let addr = store.alloc_local(StoreValue::Simple("resolved".to_string()));
        assert!(addr.is_local());
        let val = store.resolve(addr).expect("should resolve");
        assert_eq!(val.as_simple(), Some("resolved"));
    }

    #[test]
    fn store_resolver_global_returns_none_for_local_store() {
        let store = LocalCeskStore::new();
        assert!(store.resolve(StoreAddr::Global(0)).is_none());
    }

    // ── Property-based tests ────────────────────────────────────────────

    #[test]
    fn prop_alloc_monotonicity() {
        // Verify that alloc returns strictly increasing addresses
        let mut store = LocalCeskStore::new();
        let mut prev = None;
        for _ in 0..100 {
            let addr = store.alloc();
            if let Some(p) = prev {
                assert!(addr > p, "alloc must return strictly increasing addrs");
            }
            prev = Some(addr);
        }
    }

    #[test]
    fn prop_get_after_set() {
        // For all (addr, val): set(addr, val); get(addr) == Some(val)
        let mut store = LocalCeskStore::new();
        let values = vec![
            StoreValue::Simple("a".to_string()),
            StoreValue::Simple("b".to_string()),
            StoreValue::Void,
            StoreValue::Closure {
                env_snapshot: HashMap::new(),
                body: "body".to_string(),
            },
        ];
        for val in &values {
            let addr = store.alloc_with(val.clone());
            assert_eq!(store.get(addr).unwrap(), val);
        }
        // Now overwrite each one and verify
        let addrs: Vec<u64> = (0..values.len() as u64).collect();
        for (i, addr) in addrs.iter().enumerate() {
            let new_val = StoreValue::Simple(format!("new_{}", i));
            store.set(*addr, new_val.clone());
            assert_eq!(store.get(*addr).unwrap(), &new_val);
        }
    }

    #[test]
    fn prop_remove_then_get_none() {
        // For all addr: remove(addr); get(addr) == None
        let mut store = LocalCeskStore::new();
        let addrs: Vec<u64> = (0..10)
            .map(|i| store.alloc_with(StoreValue::Simple(format!("{}", i))))
            .collect();
        for addr in addrs {
            store.remove(addr);
            assert!(store.get(addr).is_none());
        }
    }

    // ── GlobalCeskStore tests (green-threads) ───────────────────────────

    mod global_store_tests {
        use super::*;

        #[test]
        fn global_store_new_is_empty() {
            let store = GlobalCeskStore::new();
            assert!(store.is_empty());
            assert_eq!(store.len(), 0);
            assert_eq!(store.current_epoch(), 0);
        }

        #[test]
        fn global_store_alloc_monotonic() {
            let store = GlobalCeskStore::new();
            let a0 = store.alloc();
            let a1 = store.alloc();
            let a2 = store.alloc();
            assert_eq!(a0, 0);
            assert_eq!(a1, 1);
            assert_eq!(a2, 2);
            assert_eq!(store.current_epoch(), 3);
        }

        #[test]
        fn global_store_alloc_with_and_get() {
            let store = GlobalCeskStore::new();
            let addr = store.alloc_with(StoreValue::Simple("global_val".to_string()));
            assert_eq!(store.len(), 1);
            assert!(store.contains(addr));
            let val = store.get(addr).expect("should be present");
            assert_eq!(val.as_simple(), Some("global_val"));
        }

        #[test]
        fn global_store_set_overwrites() {
            let store = GlobalCeskStore::new();
            let addr = store.alloc_with(StoreValue::Simple("old".to_string()));
            store.set(addr, StoreValue::Simple("new".to_string()));
            assert_eq!(store.get(addr).unwrap().as_simple(), Some("new"));
        }

        #[test]
        fn global_store_remove() {
            let store = GlobalCeskStore::new();
            let addr = store.alloc_with(StoreValue::Simple("temp".to_string()));
            let removed = store.remove(addr);
            assert_eq!(removed.unwrap().as_simple(), Some("temp"));
            assert!(!store.contains(addr));
        }

        #[test]
        fn global_store_epoch_tracks_allocs() {
            let store = GlobalCeskStore::new();
            assert_eq!(store.current_epoch(), 0);
            store.alloc();
            assert_eq!(store.current_epoch(), 1);
            store.alloc_with(StoreValue::Void);
            assert_eq!(store.current_epoch(), 2);
        }

        #[test]
        fn global_store_remove_bulk() {
            let store = GlobalCeskStore::new();
            let a0 = store.alloc_with(StoreValue::Void);
            let a1 = store.alloc_with(StoreValue::Void);
            let a2 = store.alloc_with(StoreValue::Void);
            let removed = store.remove_bulk(&[a0, a2, 999]); // 999 doesn't exist
            assert_eq!(removed, 2);
            assert!(!store.contains(a0));
            assert!(store.contains(a1));
            assert!(!store.contains(a2));
        }

        #[test]
        fn global_store_concurrent_alloc() {
            use std::sync::Arc;
            use std::thread;

            let store = Arc::new(GlobalCeskStore::new());
            let threads: Vec<_> = (0..4)
                .map(|_| {
                    let store = Arc::clone(&store);
                    thread::spawn(move || {
                        let mut addrs = Vec::new();
                        for _ in 0..100 {
                            let addr =
                                store.alloc_with(StoreValue::Simple("val".to_string()));
                            addrs.push(addr);
                        }
                        addrs
                    })
                })
                .collect();

            let mut all_addrs = Vec::new();
            for handle in threads {
                all_addrs.extend(handle.join().expect("thread should not panic"));
            }

            // All 400 addresses should be unique
            all_addrs.sort();
            all_addrs.dedup();
            assert_eq!(all_addrs.len(), 400);
            assert_eq!(store.len(), 400);
            assert_eq!(store.current_epoch(), 400);
        }
    }

    // ── PersistentLocalStore tests (green-threads) ──────────────────────

    mod persistent_store_tests {
        use super::*;

        #[test]
        fn persistent_store_new_is_empty() {
            let store = PersistentLocalStore::new();
            assert!(store.is_empty());
            assert_eq!(store.len(), 0);
        }

        #[test]
        fn persistent_store_alloc_and_get() {
            let mut store = PersistentLocalStore::new();
            let addr = store.alloc_with(StoreValue::Simple("persistent".to_string()));
            assert_eq!(store.get(addr).unwrap().as_simple(), Some("persistent"));
        }

        #[test]
        fn persistent_store_fork_isolation() {
            let mut parent = PersistentLocalStore::new();
            let addr = parent.alloc_with(StoreValue::Simple("shared".to_string()));

            // Fork child
            let mut child = parent.fork();

            // Both see the original value
            assert_eq!(parent.get(addr).unwrap().as_simple(), Some("shared"));
            assert_eq!(child.get(addr).unwrap().as_simple(), Some("shared"));

            // Mutate in child
            child.set(addr, StoreValue::Simple("child_only".to_string()));

            // Parent unchanged (copy-on-write isolation)
            assert_eq!(parent.get(addr).unwrap().as_simple(), Some("shared"));
            assert_eq!(child.get(addr).unwrap().as_simple(), Some("child_only"));
        }

        #[test]
        fn persistent_store_fork_addr_continuity() {
            let mut parent = PersistentLocalStore::new();
            parent.alloc_with(StoreValue::Void); // addr 0
            parent.alloc_with(StoreValue::Void); // addr 1

            let mut child = parent.fork();
            let child_addr = child.alloc_with(StoreValue::Simple("new".to_string()));

            // Child's new alloc continues from parent's next_addr
            assert_eq!(child_addr, 2);
            // Parent's counter is unaffected
            assert_eq!(parent.next_addr(), 2);
        }

        #[test]
        fn persistent_store_fork_child_alloc_invisible_to_parent() {
            let parent = PersistentLocalStore::new();
            let mut child = parent.fork();

            let child_addr = child.alloc_with(StoreValue::Simple("child_data".to_string()));
            assert!(child.contains(child_addr));
            assert!(!parent.contains(child_addr));
        }

        #[test]
        fn persistent_store_collect_global_roots() {
            let mut store = PersistentLocalStore::new();

            // A simple value — no global roots
            store.alloc_with(StoreValue::Simple("local".to_string()));

            // A closure capturing a global address
            let mut env = HashMap::new();
            env.insert("ch".to_string(), StoreAddr::Global(42));
            env.insert("x".to_string(), StoreAddr::Local(0));
            store.alloc_with(StoreValue::Closure {
                env_snapshot: env,
                body: "body".to_string(),
            });

            let roots = store.collect_global_roots();
            assert_eq!(roots, vec![42]);
        }

        #[test]
        fn persistent_store_fork_deep_isolation() {
            // Test that multi-level forks maintain isolation
            let mut grandparent = PersistentLocalStore::new();
            let addr = grandparent.alloc_with(StoreValue::Simple("gp".to_string()));

            let mut parent = grandparent.fork();
            parent.set(addr, StoreValue::Simple("p".to_string()));

            let mut child = parent.fork();
            child.set(addr, StoreValue::Simple("c".to_string()));

            assert_eq!(grandparent.get(addr).unwrap().as_simple(), Some("gp"));
            assert_eq!(parent.get(addr).unwrap().as_simple(), Some("p"));
            assert_eq!(child.get(addr).unwrap().as_simple(), Some("c"));
        }
    }

    // ── GcSnapshot tests (green-threads) ────────────────────────────────

    mod gc_snapshot_tests {
        use super::*;

        #[test]
        fn gc_snapshot_construction() {
            let roots = vec![0, 1, 2];
            let mut cells = HashMap::new();
            cells.insert(0, StoreValue::Simple("a".to_string()));
            cells.insert(1, StoreValue::Void);
            let snapshot = GcSnapshot::new(roots, cells, 42);
            assert_eq!(snapshot.root_count(), 3);
            assert_eq!(snapshot.cell_count(), 2);
            assert_eq!(snapshot.epoch, 42);
        }
    }
}
