# PathMap Integration -- Constraint Theory Data Layer

**Status:** DESIGN PROPOSAL -- not yet implemented
**Depends on:** `logict`, `unification`, `lattice-theory`, `presburger`
**External dependency:** `pathmap` crate (already used by `decision_tree.rs`)

---

## 1. Intuition: Why PathMap for Constraint Theory Stores

PraTTaIL's constraint theories (`UnificationTheory`, `LatticeTheory`,
`PresburgerTheory`) each maintain a *constraint store* -- a data structure
holding accumulated constraints and derived facts. Today, each store is
implemented as a bespoke Rust struct with `HashMap`s, `HashSet`s, and
`Vec`s. This works, but misses opportunities that arise from a unified
data layer:

1. **Copy-on-write forking.** Constraint propagation is speculative: when
   exploring alternative branches (via LogicT's `interleave`), the solver
   forks the store, tries a branch, and potentially backtracks. With
   `HashMap`-based stores, forking requires a full `clone()` -- O(n) in
   store size. PathMap provides O(1) structural sharing via persistent
   tries, making fork-heavy search dramatically cheaper.

2. **Cross-theory queries.** A guard like `x + y <= 100 /\ App(f, Var(x))`
   spans both Presburger and Unification theories. Today, cross-theory
   queries require manually extracting data from one store and feeding it
   to another. With PathMap-backed stores sharing a common key space,
   cross-theory queries compose naturally via path-prefix joins.

3. **Consistent encoding.** PathMap's byte-path addressing provides a
   universal term encoding that all theories can share. A term like
   `App("f", [Var(0), Const("a")])` encodes to a byte path; the same
   encoding serves as a unification store key, a lattice node address,
   and a Presburger variable reference.

4. **Integration with decision trees.** The `decision_tree.rs` module
   already uses `PathMap<DecisionAction>` for parse dispatch tries (with
   byte-encoded token prefixes in the range `0x00..0xC1`). Using PathMap
   for constraint stores unifies the data layer across both parsing and
   constraint solving, enabling shared infrastructure for trie traversal,
   prefix matching, and structural operations.

5. **Structural deduplication.** When multiple search branches converge to
   equivalent stores, PathMap's hash consing detects this automatically,
   avoiding redundant constraint propagation work.

---

## 2. Complementary Layers

PathMap serves as the *data layer* in a three-layer architecture where
each layer has a distinct role:

```
╔════════════════════════════════════════════════════════════════════════╗
║                                                                        ║
║  Layer C: Runtime Engine (in MeTTaTron -- NOT a PraTTaIL dependency)   ║
║  ┌──────────────────────────────────────────────────────────────────┐  ║
║  │  MORK / MM2                                                      │  ║
║  │                                                                  │  ║
║  │  Runtime constraint evaluation, incremental re-propagation,      │  ║
║  │  concurrent constraint store access. Operates on PathMap         │  ║
║  │  stores serialized from compile-time analysis.                   │  ║
║  │                                                                  │  ║
║  │  Note: This layer is shown for architectural completeness.       │  ║
║  │  PraTTaIL has NO dependency on MORK/MM2.                        │  ║
║  └──────────────────────────────────────────────────────────────────┘  ║
║                         ▲                                              ║
║                         │ serialized PathMap stores                     ║
║                         │                                              ║
╠════════════════════════════════════════════════════════════════════════╣
║                                                                        ║
║  Layer B: Reasoning Engine (compile-time)                              ║
║  ┌──────────────────────────────────────────────────────────────────┐  ║
║  │  Ascent (Datalog) ────────── fixpoint derivation                 │  ║
║  │  LogicT ─────────────────── fair backtracking search             │  ║
║  │  TheoryAlgebra<T> ────────── BooleanAlgebra bridge               │  ║
║  │                                                                  │  ║
║  │  Reads/writes PathMap stores via ConstraintTheory trait methods:  │  ║
║  │    propagate() ──▶ insert bindings, check consistency            │  ║
║  │    label() ───────▶ enumerate search alternatives                │  ║
║  │    witness() ─────▶ extract concrete assignment                  │  ║
║  │    evaluate() ────▶ check constraint against assignment          │  ║
║  └──────────────────────────────────────────────────────────────────┘  ║
║                         ▲                                              ║
║                         │ ConstraintTheory trait                        ║
║                         │                                              ║
╠════════════════════════════════════════════════════════════════════════╣
║                                                                        ║
║  Layer A: Data Layer                                                   ║
║  ┌──────────────────────────────────────────────────────────────────┐  ║
║  │  PathMap<V>                                                      │  ║
║  │                                                                  │  ║
║  │  Persistent trie with byte-path keys                             │  ║
║  │  O(k) lookup by key path (k = key length in bytes)               │  ║
║  │  O(1) CoW fork (Arc-based structural sharing)                    │  ║
║  │  Hash-consing for O(1) equality checks                           │  ║
║  │  Algebraic operations (Lattice, DistributiveLattice, Ring)       │  ║
║  │                                                                  │  ║
║  │  Stores:                                                         │  ║
║  │    UnificationStore ── variable bindings + pending equations      │  ║
║  │    LatticeStore ────── subtype edges + closure + LUB/GLB cache   │  ║
║  │    PresburgerStore ─── variable bounds + constraint set           │  ║
║  │    ComposedStore ───── cross-theory prefix-partitioned data       │  ║
║  │    MultiplicityStore ─ resource usage counts                     │  ║
║  └──────────────────────────────────────────────────────────────────┘  ║
║                                                                        ║
╚════════════════════════════════════════════════════════════════════════╝
```

**Key separation of concerns:**

| Layer | Responsibility | Mutability | Sharing |
|-------|---------------|------------|---------|
| A (PathMap) | Store, index, fork, merge constraint data | Persistent (CoW) | Structural sharing across forks |
| B (Ascent/LogicT) | Derive new facts, search, propagate constraints | Via Layer A's CoW interface | Immutable snapshots between derivation rounds |
| C (MORK/MM2) | Execute at runtime, incremental updates | Mutable (runtime owned) | Serialized from Layer A; independent lifecycle |

---

## 3. PathMap-Backed Stores

### 3.1 UnificationStore

The unification store holds variable bindings (substitution sigma) and pending
equations. In the PathMap-backed design, term structure is encoded as byte
sequences (Section 5), and substitution bindings are stored as PathMap entries:

```rust
use pathmap::PathMap;

/// PathMap-backed unification store with O(1) CoW forking.
///
/// Key encoding: variable index as big-endian 4-byte path.
/// Value: byte-encoded term (see Section 5 for encoding scheme).
pub struct UnificationStore {
    /// Substitution sigma: var_index -> encoded term.
    bindings: PathMap<TermBytes>,

    /// Pending equations not yet processed by Martelli-Montanari.
    /// Keyed by equation index (big-endian u32).
    pending: PathMap<EquationPair>,

    /// Next equation index for pending queue.
    next_eq_idx: u32,
}

/// Compact byte-encoded term for PathMap storage.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TermBytes(Vec<u8>);

/// A pending equation: two terms to be unified.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct EquationPair {
    pub lhs: TermBytes,
    pub rhs: TermBytes,
}

impl UnificationStore {
    /// Create an empty store.
    pub fn new() -> Self {
        UnificationStore {
            bindings: PathMap::new(),
            pending: PathMap::new(),
            next_eq_idx: 0,
        }
    }

    /// O(1) fork: structural sharing via PathMap's persistent trie.
    ///
    /// Both the original and the fork share all existing data.
    /// Mutations to either copy are independent (copy-on-write).
    pub fn fork(&self) -> Self {
        UnificationStore {
            bindings: self.bindings.clone(), // O(1) Arc clone
            pending: self.pending.clone(),   // O(1) Arc clone
            next_eq_idx: self.next_eq_idx,
        }
    }

    /// Look up a variable's binding.  O(k) where k = 4 (key length).
    pub fn lookup(&self, var: usize) -> Option<&TermBytes> {
        let key = encode_var_key(var);
        self.bindings.get(&key)
    }

    /// Bind a variable to a term.  O(k) where k = 4.
    pub fn bind(&mut self, var: usize, term: TermBytes) {
        let key = encode_var_key(var);
        self.bindings.insert(&key, term);
    }

    /// Add a pending equation to the work queue.
    pub fn add_equation(&mut self, lhs: TermBytes, rhs: TermBytes) {
        let key = encode_u32_key(self.next_eq_idx);
        self.pending.insert(&key, EquationPair { lhs, rhs });
        self.next_eq_idx += 1;
    }

    /// Check whether all equations have been processed.
    pub fn is_solved(&self) -> bool {
        self.pending.is_empty()
    }
}

fn encode_var_key(var: usize) -> [u8; 4] {
    (var as u32).to_be_bytes()
}

fn encode_u32_key(idx: u32) -> [u8; 4] {
    idx.to_be_bytes()
}
```

### 3.2 LatticeStore

The lattice store holds subtype edges and transitive closure data. With
PathMap, edges are stored as 2-byte keys (sub, sup pair) and the closure
is a second PathMap sharing the same key encoding:

```rust
/// PathMap-backed lattice store with O(1) fork and prefix iteration.
///
/// Key encoding for edges/closure: [sub_id, sup_id] as 2-byte path.
/// Key encoding for caches: [a, b] normalized (a <= b) as 2-byte path.
pub struct LatticeStore {
    /// Direct subtype edges: key = [sub, sup], value = ().
    edges: PathMap<()>,

    /// Transitive closure (computed lazily via Warshall's algorithm).
    closure: PathMap<()>,

    /// LUB cache: key = [a, b] normalized, value = Option<TypeId>.
    lub_cache: PathMap<Option<u8>>,

    /// GLB cache: key = [a, b] normalized, value = Option<TypeId>.
    glb_cache: PathMap<Option<u8>>,

    /// Whether closure needs recomputation after edge additions.
    closure_dirty: bool,
}

impl LatticeStore {
    /// O(1) fork via PathMap structural sharing.
    ///
    /// The fork shares all edge, closure, and cache data with the
    /// original. Only mutations to either copy are allocated fresh.
    pub fn fork(&self) -> Self {
        LatticeStore {
            edges: self.edges.clone(),
            closure: self.closure.clone(),
            lub_cache: self.lub_cache.clone(),
            glb_cache: self.glb_cache.clone(),
            closure_dirty: self.closure_dirty,
        }
    }

    /// Add a subtype edge and mark closure as dirty.
    pub fn add_edge(&mut self, sub: u8, sup: u8) {
        self.edges.insert(&[sub, sup], ());
        self.closure_dirty = true;
        self.lub_cache = PathMap::new();
        self.glb_cache = PathMap::new();
    }

    /// Check if sub <= sup holds in the transitive closure.
    pub fn is_subtype(&self, sub: u8, sup: u8) -> bool {
        if sub == sup { return true; } // reflexive
        self.closure.get(&[sub, sup]).is_some()
    }

    /// Enumerate all subtypes of a given type (via prefix iteration).
    ///
    /// Uses PathMap's prefix iteration: all keys [*, sup] where
    /// the second byte is `sup` are subtypes of `sup`.
    ///
    /// Note: this requires iterating the full closure and filtering,
    /// since PathMap prefixes match on the first byte. For production
    /// use, maintain a reverse index PathMap keyed by [sup, sub].
    pub fn subtypes_of(&self, sup: u8) -> Vec<u8> {
        self.closure.iter()
            .filter_map(|(key, _)| {
                if key.len() == 2 && key[1] == sup {
                    Some(key[0])
                } else {
                    None
                }
            })
            .collect()
    }
}
```

### 3.3 PresburgerStore

```rust
/// PathMap-backed Presburger constraint store.
///
/// Stores variable bounds and accumulated linear constraints.
/// Key encoding for bounds: [var_index] as 1-byte path.
/// Key encoding for constraints: [constraint_index] as 4-byte path.
pub struct PresburgerStore {
    /// Per-variable bounds: var_index -> (lower, upper).
    bounds: PathMap<(i64, i64)>,

    /// Accumulated linear constraints (indexed for iteration).
    constraints: PathMap<LinearConstraint>,

    /// Next constraint index.
    next_constraint_idx: u32,
}

impl PresburgerStore {
    /// O(1) fork via PathMap structural sharing.
    pub fn fork(&self) -> Self {
        PresburgerStore {
            bounds: self.bounds.clone(),
            constraints: self.constraints.clone(),
            next_constraint_idx: self.next_constraint_idx,
        }
    }

    /// Narrow the bounds for a variable.
    ///
    /// Returns false if the narrowed bounds are empty (lower > upper).
    pub fn narrow_bounds(&mut self, var: u8, new_lower: i64, new_upper: i64) -> bool {
        let key = [var];
        let (lower, upper) = self.bounds.get(&key)
            .copied()
            .unwrap_or((i64::MIN, i64::MAX));
        let refined_lower = lower.max(new_lower);
        let refined_upper = upper.min(new_upper);
        if refined_lower > refined_upper {
            return false; // empty interval: inconsistent
        }
        self.bounds.insert(&key, (refined_lower, refined_upper));
        true
    }

    /// Add a linear constraint to the store.
    pub fn add_constraint(&mut self, constraint: LinearConstraint) {
        let key = encode_u32_key(self.next_constraint_idx);
        self.constraints.insert(&key, constraint);
        self.next_constraint_idx += 1;
    }
}
```

---

## 4. Martelli-Montanari Unification via PathMap propagate()

The core unification algorithm (Martelli & Montanari, 1982) maps directly
onto PathMap operations. The `propagate()` method implements the full
algorithm using PathMap's `insert`, `get`, and iteration:

```rust
impl ConstraintTheory for PathMapUnificationTheory {
    type Constraint = UnificationEquation;
    type Assignment = Substitution;
    type Store = UnificationStore;

    /// Martelli-Montanari unification via PathMap-backed store.
    ///
    /// Adds the new equation to the store and runs the unification
    /// algorithm to completion.  Returns None if the system is
    /// unsatisfiable (constructor clash, arity mismatch, occurs check).
    ///
    /// The store is forked (O(1) CoW) before any mutations, so the
    /// caller's original store is never modified.
    fn propagate(
        &self,
        store: &UnificationStore,
        eq: &UnificationEquation,
    ) -> Option<UnificationStore> {
        // Step 0: Fork the store -- O(1) via PathMap CoW.
        let mut new_store = store.fork();

        // Step 1: Encode and add the new equation.
        let lhs_bytes = encode_term(&eq.lhs);
        let rhs_bytes = encode_term(&eq.rhs);
        new_store.add_equation(lhs_bytes, rhs_bytes);

        // Step 2: Drain pending equations into an explicit work stack.
        //
        // We use a Vec work stack (not PathMap iteration) because
        // new equations may be generated during decomposition.
        let mut work: Vec<(TermBytes, TermBytes)> = Vec::new();
        for (_key, eq_pair) in new_store.pending.iter() {
            work.push((eq_pair.lhs.clone(), eq_pair.rhs.clone()));
        }
        new_store.pending = PathMap::new();
        new_store.next_eq_idx = 0;

        // Step 3: Martelli-Montanari work loop.
        while let Some((s_bytes, t_bytes)) = work.pop() {
            // Apply current substitution to both sides.
            let s = apply_subst_bytes(&new_store.bindings, &s_bytes);
            let t = apply_subst_bytes(&new_store.bindings, &t_bytes);

            match (decode_tag(&s), decode_tag(&t)) {
                // ── Var(x) = Var(x): trivial identity ───────────────
                (Tag::Var(x), Tag::Var(y)) if x == y => {
                    continue;
                }

                // ── Var(x) = t: bind x to t (with occurs check) ────
                (Tag::Var(x), _) => {
                    if occurs_in_bytes(x, &t) {
                        return None; // infinite term: x occurs in t
                    }
                    new_store.bind(x, t.clone());
                    update_all_bindings(&mut new_store.bindings, x, &t);
                }

                // ── t = Var(y): orient variable to left ─────────────
                (_, Tag::Var(y)) => {
                    if occurs_in_bytes(y, &s) {
                        return None; // infinite term: y occurs in s
                    }
                    new_store.bind(y, s.clone());
                    update_all_bindings(&mut new_store.bindings, y, &s);
                }

                // ── App(f, args_s) = App(f, args_t): decompose ──────
                (Tag::App(f1, arity1), Tag::App(f2, arity2)) => {
                    if f1 != f2 {
                        return None; // constructor clash: f1 != f2
                    }
                    if arity1 != arity2 {
                        return None; // arity mismatch
                    }
                    let args_s = extract_args_bytes(&s, arity1);
                    let args_t = extract_args_bytes(&t, arity2);
                    for (arg_s, arg_t) in args_s.into_iter().zip(args_t) {
                        work.push((arg_s, arg_t));
                    }
                }

                // ── Const(a) = Const(a): identity ───────────────────
                (Tag::Const(a), Tag::Const(b)) if a == b => {
                    continue;
                }

                // ── Const(a) = Const(b): constant clash ─────────────
                (Tag::Const(_), Tag::Const(_)) => {
                    return None;
                }

                // ── Kind clash (Const vs App, etc.) ─────────────────
                _ => {
                    return None;
                }
            }
        }

        Some(new_store)
    }

    fn is_consistent(&self, store: &UnificationStore) -> bool {
        store.is_solved()
    }

    fn witness(&self, store: &UnificationStore) -> Option<Substitution> {
        if !self.is_consistent(store) { return None; }
        let mut bindings = HashMap::new();
        for (key, term_bytes) in store.bindings.iter() {
            let var = u32::from_be_bytes([key[0], key[1], key[2], key[3]]) as usize;
            let term = decode_term(term_bytes);
            bindings.insert(var, term);
        }
        Some(Substitution { bindings })
    }

    fn label(&self, _store: &UnificationStore) -> LogicStream<UnificationEquation> {
        LogicStream::empty() // decidable: no labeling needed
    }

    fn evaluate(
        &self,
        eq: &UnificationEquation,
        subst: &Substitution,
    ) -> bool {
        let lhs = subst.apply(&eq.lhs);
        let rhs = subst.apply(&eq.rhs);
        lhs == rhs
    }
}
```

### Substitution Application via PathMap

```rust
/// Apply substitution to a byte-encoded term by following variable
/// bindings transitively in the PathMap store.
///
/// Complexity: O(n * d) where n = term size and d = max binding chain depth.
/// In practice d is small because Martelli-Montanari produces flat
/// substitutions (no chains longer than 1 after update_all_bindings).
fn apply_subst_bytes(
    bindings: &PathMap<TermBytes>,
    term: &TermBytes,
) -> TermBytes {
    match decode_tag(term) {
        Tag::Var(x) => {
            let key = encode_var_key(x);
            match bindings.get(&key) {
                Some(bound) => apply_subst_bytes(bindings, bound),
                None => term.clone(), // unbound variable
            }
        }
        Tag::Const(_) => term.clone(),
        Tag::App(head, arity) => {
            let args = extract_args_bytes(term, arity);
            let new_args: Vec<TermBytes> = args.into_iter()
                .map(|a| apply_subst_bytes(bindings, &a))
                .collect();
            encode_app(&head, &new_args)
        }
    }
}

/// Update all existing bindings by applying {var -> term}.
///
/// For each (key, value) in the PathMap, if value mentions var,
/// replace var with term.  Uses PathMap iteration + targeted re-insertion.
///
/// Complexity: O(n * t) where n = number of bindings and t = avg term size.
fn update_all_bindings(
    bindings: &mut PathMap<TermBytes>,
    var: usize,
    term: &TermBytes,
) {
    let updates: Vec<(Vec<u8>, TermBytes)> = bindings.iter()
        .filter_map(|(key, value)| {
            if mentions_var_bytes(value, var) {
                let new_value = substitute_var_bytes(value, var, term);
                Some((key.to_vec(), new_value))
            } else {
                None
            }
        })
        .collect();

    for (key, new_value) in updates {
        bindings.insert(&key, new_value);
    }
}
```

### Key Properties of PathMap-Backed Unification

- **O(1) fork.** `store.fork()` is a reference count increment on PathMap's
  internal `Arc`, not a deep copy. When LogicT's `interleave` forks a store
  to explore an alternative branch, the cost is constant regardless of the
  number of bindings.

- **Amortized O(k) bind.** Inserting a binding costs O(k) where k = 4 bytes
  (the variable key length). CoW path copying means only the trie nodes along
  the insertion path are freshly allocated; all other nodes are shared.

- **Structural sharing during search.** When LogicT explores n branches from
  a common ancestor store, all n forks share the ancestor's bindings. Only
  the per-branch delta (new bindings, modified bindings) is allocated fresh.

---

## 5. Term Byte Encoding

Terms are encoded as compact byte sequences for PathMap-native storage.
The encoding is self-delimiting (each term's length can be determined from
its prefix), enabling PathMap's trie structure to index terms structurally:

```
┌──────────────────────────────────────────────────────────────────────┐
│  Tag Byte    │  Payload                                              │
├──────────────┼──────────────────────────────────────────────────────┤
│  0x00        │  Var: 4 bytes (u32 big-endian variable index)         │
│  0x01        │  Const: 2 bytes (u16 string table index, big-endian)  │
│  0x02        │  App: 2 bytes (u16 head index, big-endian) +          │
│              │       1 byte (u8 arity) +                             │
│              │       arity * encoded child terms (recursive)         │
│  0x03        │  Wildcard: 0 bytes (matches anything)                 │
└──────────────┴──────────────────────────────────────────────────────┘
```

### Encoding Examples

```
Term: Var(0)
Bytes: [0x00, 0x00, 0x00, 0x00, 0x00]     5 bytes (tag + u32 index)

Term: Var(42)
Bytes: [0x00, 0x00, 0x00, 0x00, 0x2A]     5 bytes

Term: Const("a")  (string table index 7)
Bytes: [0x01, 0x00, 0x07]                 3 bytes (tag + u16 index)

Term: App("f", [Var(0), Const("a")])
  head "f" = string table index 3, arity = 2
Bytes: [0x02, 0x00, 0x03, 0x02,           4 bytes: tag + head + arity
        0x00, 0x00, 0x00, 0x00, 0x00,     5 bytes: child 0 = Var(0)
        0x01, 0x00, 0x07]                 3 bytes: child 1 = Const("a")
Total: 12 bytes

Term: Wildcard
Bytes: [0x03]                             1 byte
```

### String Table

Constructor names and constant names are interned into a shared string
table (`Vec<String>` or `HashMap<String, u16>`). The 2-byte index supports
up to 65,536 distinct names. The string table is shared across all stores
in a given analysis context and is constructed once during grammar
classification.

### Encoding Properties

| Property | Guarantee |
|----------|-----------|
| **Self-delimiting** | Each term's byte length is determinable from its tag + payload structure |
| **Deterministic** | Same term always produces the same byte sequence |
| **Compact** | Var: 5 bytes, Const: 3 bytes, App: 4 + sum(children) bytes |
| **Ordered** | Tag byte ordering: Var(0x00) < Const(0x01) < App(0x02) < Wildcard(0x03) |
| **PathMap-compatible** | Byte sequences serve as PathMap keys directly |

---

## 6. Coreferential Matching: Shared-Variable Guard Dispatch

When multiple guard predicates share variables -- e.g., `f(x, x)` where
the same variable appears in two positions -- the constraint system must
ensure that both positions bind to the same value. This is *coreferential
matching* (Peyton Jones & Graf, 2023), and PathMap's persistent trie
structure supports it efficiently.

### The Problem

Consider a guard pattern `App("pair", [Var(0), Var(0)])` -- a pair where
both elements must be equal. Matching against
`App("pair", [Const("a"), Const("b")])` should fail (a != b), while
matching against `App("pair", [Const("a"), Const("a")])` should succeed
with the substitution `{x0 -> Const("a")}`.

### PathMap-Based Solution

The first occurrence of `Var(0)` creates a binding in the PathMap store.
The second occurrence triggers a *lookup* rather than a bind. If the
lookup finds a binding, the matched value must equal the existing binding:

```rust
/// Match a pattern against a concrete term, accumulating bindings in
/// the PathMap-backed store.  Handles coreferential variables (same
/// variable appearing multiple times) via lookup-before-bind.
///
/// Returns true if the match succeeds; the store contains all bindings.
/// Returns false if the match fails; the store is left in an
/// indeterminate state (caller should discard it).
fn match_coreferential(
    store: &mut UnificationStore,
    pattern: &TermBytes,
    target: &TermBytes,
) -> bool {
    match decode_tag(pattern) {
        Tag::Var(x) => {
            match store.lookup(x) {
                Some(existing) => {
                    // Coreference: variable already bound.
                    // The target must equal the existing binding.
                    *existing == *target
                }
                None => {
                    // First occurrence: bind variable to target.
                    store.bind(x, target.clone());
                    true
                }
            }
        }
        Tag::App(head_p, arity_p) => {
            match decode_tag(target) {
                Tag::App(head_t, arity_t)
                    if head_p == head_t && arity_p == arity_t =>
                {
                    let args_p = extract_args_bytes(pattern, arity_p);
                    let args_t = extract_args_bytes(target, arity_t);
                    args_p.iter().zip(args_t.iter())
                        .all(|(p, t)| match_coreferential(store, p, t))
                }
                _ => false, // constructor or arity mismatch
            }
        }
        Tag::Const(c_p) => {
            match decode_tag(target) {
                Tag::Const(c_t) => c_p == c_t,
                _ => false, // kind mismatch
            }
        }
        Tag::Wildcard => true, // matches anything
    }
}
```

The O(k) PathMap lookup for `store.lookup(x)` (k = 4 bytes) makes the
coreference check nearly as fast as a fresh binding. Because PathMap is
persistent, the bindings are automatically "rolled back" if the match
fails and the store is discarded -- the original store is unchanged
(no explicit undo needed).

### Guard Dispatch Code Generation

For guards with shared variables, the codegen emits a dispatch sequence
that uses the PathMap store as a one-pass binding accumulator:

```rust
// Generated code for guard: pair(x, x)
fn match_guard_pair_xx(input: &Term) -> Option<Substitution> {
    let mut store = UnificationStore::new();
    match input {
        Term::App { head, args } if head == "pair" && args.len() == 2 => {
            // First occurrence of x: bind
            store.bind(0, encode_term(&args[0]));
            // Second occurrence of x: coreference check
            let existing = store.lookup(0).expect("just bound x0");
            if *existing == encode_term(&args[1]) {
                Some(store.to_substitution())
            } else {
                None // coreference failure: args[0] != args[1]
            }
        }
        _ => None, // pattern mismatch
    }
}
```

---

## 7. Composed PathMap Queries: Cross-Theory Constraint Checking

When a guard predicate spans multiple theories -- for example,
`x + y <= 100 /\ App(f, Var(x))` involves both Presburger (arithmetic
bound) and Unification (structural pattern) -- the pipeline needs to
check cross-theory consistency. PathMap's trie structure supports this
via a single shared store with prefix-partitioned theory data:

```
┌──────────────────────────────────────────────────────────────────────────┐
│  Shared PathMap key space (ComposedStore)                                │
│                                                                          │
│  Prefix 0x00: Unification bindings                                       │
│    [0x00, var_hi, var_lo, var_3, var_4] -> TermBytes                    │
│                                                                          │
│  Prefix 0x01: Lattice edges and closure                                  │
│    [0x01, sub, sup] -> ()                                                │
│                                                                          │
│  Prefix 0x02: Presburger bounds                                          │
│    [0x02, var] -> (lower: i64, upper: i64)                               │
│                                                                          │
│  Prefix 0x03+: User-defined theory data                                  │
│    [0x03, ...] -> theory-specific values                                 │
│                                                                          │
│  Cross-theory query example:                                             │
│    "Is var x0 bound to a term whose head type is a subtype of Number?"   │
│    Step 1: lookup [0x00, 0,0,0,0] -> term t (Unification prefix)        │
│    Step 2: extract type of head(t) -> TypeId                             │
│    Step 3: lookup [0x01, TypeId, Number] (Lattice prefix) -> subtype?    │
│                                                                          │
│  All steps are O(k) PathMap traversals with no data copying.             │
└──────────────────────────────────────────────────────────────────────────┘
```

### ComposedStore Implementation

```rust
/// A composed constraint store spanning multiple theories.
///
/// Each theory's data occupies a distinct prefix in the shared PathMap.
/// Cross-theory queries compose via sequential prefix lookups.
/// O(1) fork via PathMap structural sharing.
pub struct ComposedStore {
    /// Shared PathMap with prefix-partitioned theory data.
    data: PathMap<StoreValue>,
}

/// A tagged value in the composed store.
#[derive(Clone, Debug, PartialEq)]
pub enum StoreValue {
    /// Unification binding: variable index -> encoded term.
    UnifBinding(TermBytes),
    /// Lattice edge marker: (sub, sup) edge present.
    LatticeEdge,
    /// Presburger bounds: variable -> (lower, upper).
    PresburgerBound(i64, i64),
    /// User-defined theory value.
    UserDefined(Vec<u8>),
}

impl ComposedStore {
    const UNIF_PREFIX: u8 = 0x00;
    const LATTICE_PREFIX: u8 = 0x01;
    const PRESB_PREFIX: u8 = 0x02;
    const USER_PREFIX: u8 = 0x03;

    /// O(1) fork via PathMap structural sharing.
    pub fn fork(&self) -> Self {
        ComposedStore { data: self.data.clone() }
    }

    /// Bind a unification variable.
    pub fn unif_bind(&mut self, var: usize, term: TermBytes) {
        let mut key = vec![Self::UNIF_PREFIX];
        key.extend_from_slice(&encode_var_key(var));
        self.data.insert(&key, StoreValue::UnifBinding(term));
    }

    /// Look up a unification variable's binding.
    pub fn unif_lookup(&self, var: usize) -> Option<&TermBytes> {
        let mut key = vec![Self::UNIF_PREFIX];
        key.extend_from_slice(&encode_var_key(var));
        match self.data.get(&key) {
            Some(StoreValue::UnifBinding(t)) => Some(t),
            _ => None,
        }
    }

    /// Add a subtype edge to the lattice partition.
    pub fn lattice_add_edge(&mut self, sub: u8, sup: u8) {
        self.data.insert(
            &[Self::LATTICE_PREFIX, sub, sup],
            StoreValue::LatticeEdge,
        );
    }

    /// Check subtype relationship in the lattice partition.
    pub fn lattice_is_subtype(&self, sub: u8, sup: u8) -> bool {
        if sub == sup { return true; }
        self.data.get(&[Self::LATTICE_PREFIX, sub, sup]).is_some()
    }

    /// Cross-theory query: check if a unification variable is bound to
    /// a term whose type is a subtype of the given target type.
    ///
    /// Requires a type extraction function that maps terms to TypeIds.
    pub fn var_has_subtype(
        &self,
        var: usize,
        target_type: u8,
        extract_type: impl Fn(&TermBytes) -> Option<u8>,
    ) -> bool {
        // Step 1: Look up the unification binding.
        let bound_term = match self.unif_lookup(var) {
            Some(t) => t,
            None => return false, // unbound variable
        };

        // Step 2: Extract the type of the bound term.
        let term_type = match extract_type(bound_term) {
            Some(ty) => ty,
            None => return false, // term has no extractable type
        };

        // Step 3: Check subtype relationship.
        self.lattice_is_subtype(term_type, target_type)
    }

    /// Narrow a Presburger variable's bounds.
    pub fn presb_narrow(
        &mut self,
        var: u8,
        new_lower: i64,
        new_upper: i64,
    ) -> bool {
        let key = [Self::PRESB_PREFIX, var];
        let (lower, upper) = match self.data.get(&key) {
            Some(StoreValue::PresburgerBound(lo, hi)) => (*lo, *hi),
            _ => (i64::MIN, i64::MAX),
        };
        let refined_lower = lower.max(new_lower);
        let refined_upper = upper.min(new_upper);
        if refined_lower > refined_upper {
            return false; // empty interval
        }
        self.data.insert(&key, StoreValue::PresburgerBound(refined_lower, refined_upper));
        true
    }
}
```

---

## 8. PathMap NFA Transitions: Sparse Storage for Presburger

The Presburger NFA construction (see `presburger-algebra.md`, Section 3)
generates transition tables indexed by `(state, symbol)` pairs. For k
variables, the alphabet is `{0,1}^k` with `2^k` symbols. When k >= 3,
the transition table becomes sparse -- many `(state, symbol)` pairs have
no transition -- and PathMap provides efficient sparse storage:

```rust
/// PathMap-backed sparse NFA transition table.
///
/// Key encoding: [state_hi, state_lo, symbol] (3 bytes).
/// Value: set of target states (Vec<u16> for NFA nondeterminism).
///
/// For k >= 3 variables (alphabet size >= 8), the transition table
/// is typically 30--60% sparse.  PathMap's trie structure avoids
/// allocating entries for missing transitions while supporting
/// efficient prefix iteration for "all transitions from state s".
pub struct SparseNfaTransitions {
    transitions: PathMap<Vec<u16>>,
}

impl SparseNfaTransitions {
    pub fn new() -> Self {
        SparseNfaTransitions { transitions: PathMap::new() }
    }

    /// Add a transition: source --[symbol]--> target.
    pub fn add(&mut self, source: u16, symbol: u32, target: u16) {
        let key = [
            (source >> 8) as u8,
            (source & 0xFF) as u8,
            symbol as u8,
        ];
        match self.transitions.get_mut(&key) {
            Some(targets) => {
                if !targets.contains(&target) {
                    targets.push(target);
                }
            }
            None => {
                self.transitions.insert(&key, vec![target]);
            }
        }
    }

    /// Look up all target states for a given (source, symbol) pair.
    pub fn get(&self, source: u16, symbol: u32) -> &[u16] {
        let key = [
            (source >> 8) as u8,
            (source & 0xFF) as u8,
            symbol as u8,
        ];
        self.transitions.get(&key)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Iterate all transitions from a given source state.
    ///
    /// Uses PathMap prefix iteration: all keys starting with
    /// [state_hi, state_lo] are transitions from that state.
    pub fn transitions_from(&self, source: u16) -> Vec<(u32, Vec<u16>)> {
        let prefix = [
            (source >> 8) as u8,
            (source & 0xFF) as u8,
        ];
        self.transitions.iter_prefix(&prefix)
            .map(|(key_suffix, targets)| {
                let symbol = key_suffix[0] as u32;
                (symbol, targets.clone())
            })
            .collect()
    }

    /// O(1) fork for NFA state sharing during Boolean operations.
    ///
    /// When computing intersection (product construction), both
    /// component NFAs can share their transition tables via fork.
    pub fn fork(&self) -> Self {
        SparseNfaTransitions {
            transitions: self.transitions.clone(),
        }
    }
}
```

### Space Analysis for k >= 3

| k (variables) | Alphabet size 2^k | Dense table entries (S * 2^k) | Typical sparsity | PathMap memory savings |
|---------------|-------------------|-------------------------------|------------------|----------------------|
| 2 | 4 | 4S | ~10% sparse | Negligible |
| 3 | 8 | 8S | ~35% sparse | ~30% |
| 4 | 16 | 16S | ~55% sparse | ~50% |
| 5 | 32 | 32S | ~70% sparse | ~65% |

where S = number of NFA states.

For grammar-level analysis (k <= 4), the absolute space savings are modest
because the NFAs are small. The primary benefit for Presburger is
structural sharing when forking NFA states during Boolean operations
(intersection, complement), where the product construction creates many
intermediate NFAs that share most of their transition structure.

---

## 9. Multiplicity Tracking: Resource-Aware Stores

Rholang's linear types require tracking how many times each channel or
resource is used. A resource-aware constraint theory extends the PathMap
data layer with multiplicity counts and enforcement:

```rust
/// Resource-aware store tracking usage multiplicities.
///
/// Each resource (channel, capability) has a count and a constraint.
/// Linear resources require count == 1; affine resources require
/// count <= 1; relevant resources require count >= 1.
///
/// PathMap key: resource_id as big-endian u16 (2 bytes).
/// PathMap value: (current_count, constraint).
pub struct MultiplicityStore {
    counts: PathMap<(u32, MultiplicityConstraint)>,
}

/// Multiplicity constraint kinds (substructural type modalities).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MultiplicityConstraint {
    /// Linear: resource used exactly once.
    /// Corresponds to Rholang's standard channel semantics.
    Linear,       // count == 1

    /// Affine: resource used at most once (may be dropped).
    /// Corresponds to Rholang's optional receive patterns.
    Affine,       // count <= 1

    /// Relevant: resource used at least once (cannot be dropped).
    /// Corresponds to Rholang's persistent channels.
    Relevant,     // count >= 1

    /// Unrestricted: no usage constraint.
    /// Corresponds to standard (non-linear) values.
    Unrestricted, // count >= 0
}

#[derive(Debug)]
pub struct MultiplicityViolation {
    pub resource_id: u16,
    pub expected: MultiplicityConstraint,
    pub actual_count: u32,
}

impl MultiplicityStore {
    pub fn new() -> Self {
        MultiplicityStore { counts: PathMap::new() }
    }

    /// Record a usage of the given resource.
    ///
    /// Returns None if the usage violates the resource's constraint.
    pub fn use_resource(
        &mut self,
        resource_id: u16,
        constraint: MultiplicityConstraint,
    ) -> Option<()> {
        let key = resource_id.to_be_bytes();
        let (count, existing_constraint) = self.counts.get(&key)
            .cloned()
            .unwrap_or((0, constraint.clone()));

        let new_count = count + 1;

        // Check eagerly: affine and linear resources fail on second use.
        match &existing_constraint {
            MultiplicityConstraint::Linear if new_count > 1 => return None,
            MultiplicityConstraint::Affine if new_count > 1 => return None,
            _ => {}
        }

        self.counts.insert(&key, (new_count, existing_constraint));
        Some(())
    }

    /// Check that all resources satisfy their end-of-scope constraints.
    ///
    /// Linear resources must have count == 1.
    /// Relevant resources must have count >= 1.
    pub fn check_completeness(&self) -> Vec<MultiplicityViolation> {
        let mut violations = Vec::new();
        for (key, (count, constraint)) in self.counts.iter() {
            let resource_id = u16::from_be_bytes([key[0], key[1]]);
            let violated = match constraint {
                MultiplicityConstraint::Linear => *count != 1,
                MultiplicityConstraint::Relevant => *count == 0,
                _ => false,
            };
            if violated {
                violations.push(MultiplicityViolation {
                    resource_id,
                    expected: constraint.clone(),
                    actual_count: *count,
                });
            }
        }
        violations
    }

    /// O(1) fork for speculative constraint checking.
    pub fn fork(&self) -> Self {
        MultiplicityStore { counts: self.counts.clone() }
    }
}
```

### Integration with LogicT Search

When the runtime explores alternative comm events (which channel to
receive from), each branch forks the multiplicity store to track
independent resource usage:

```
                   MultiplicityStore (initial)
                  /                            \
       fork() for branch A              fork() for branch B
      /                                        \
use_resource(ch1, Linear)            use_resource(ch2, Linear)
use_resource(ch2, Linear)            use_resource(ch1, Linear)
      |                                        |
check_completeness()                 check_completeness()
      |                                        |
  Both ch1, ch2 used once:           Both ch1, ch2 used once:
  OK (linear constraint satisfied)   OK (linear constraint satisfied)
```

PathMap's O(1) fork ensures that exploring n alternative comm events
costs O(n * delta) rather than O(n * store_size) memory, where delta
is the number of resource usages per branch.

---

## 10. Performance Characteristics

### Per-Operation Complexity

| Operation | PathMap-Backed | HashMap-Backed | Analysis |
|-----------|---------------|---------------|----------|
| **Fork (clone)** | O(1) -- Arc ref increment | O(n) -- deep copy | PathMap wins by factor n |
| **Lookup** | O(k) -- k = key bytes | O(1) amortized | HashMap faster per-lookup |
| **Insert** | O(k) -- k = key bytes | O(1) amortized | HashMap faster per-insert |
| **Prefix iteration** | O(m) -- m = matches | O(n) -- full scan | PathMap faster for prefix queries |
| **Equality check** | O(1) -- hash consing | O(n) -- element-wise | PathMap wins for convergence detection |

Where n = store size, k = key length (typically 2--5 bytes), m = prefix matches.

### Memory Under Branching Search

For a search tree with branching factor b, depth d, initial store size S,
and per-branch delta delta:

```
HashMap memory:   O(b^d * S)
PathMap memory:   O(S + b^d * delta)

Sharing ratio:    (b^d * S) / (S + b^d * delta) = b^d * S / (S + b^d * delta)

For S >> delta (large store, small changes per branch):
  Ratio approaches b^d (number of branches)
```

### Numerical Example

```
Parameters: S = 500 bindings, b = 3, d = 4, delta = 3 bindings/branch

HashMap:  3^4 * 500 = 40,500 binding copies
PathMap:  500 + 81 * 3 = 743 binding nodes

Memory ratio: 40,500 / 743 = 54.5x reduction
```

### When PathMap Is Preferred

PathMap-backed stores are strictly better when:
- The search tree has high branching factor (LogicT `interleave` with many alternatives).
- The store is large relative to the per-branch delta.
- Cross-theory queries require prefix-based data partitioning.
- Convergence detection (two branches reaching the same store) is valuable.

### When HashMap Is Preferred

HashMap-backed stores are faster when:
- Fork operations are rare (decidable theories with no LogicT search).
- Store size is small (fewer than ~20 entries).
- Random-access lookups dominate (no prefix queries, no iteration).

### Design Recommendation

PathMap-backed stores should be an *option*, not a requirement. The
`ConstraintTheory` trait is store-agnostic -- any type satisfying
`Clone + Debug + Send + Sync + 'static` works as a `Store`. Theory
implementors choose the backing store based on their search characteristics:

- **Decidable theories** (Presburger, Lattice, base Unification): use
  `HashMap`-based stores. Fork cost is paid rarely or never.
- **Search-heavy theories** (extended Unification with AC-matching, region
  inference, type class resolution): use `PathMap`-backed stores. Fork
  cost dominates runtime in LogicT search.

---

## 11. Citations

- Peyton Jones, S. & Graf, S. (2023). "Lower Your Guards: A Compositional
  Pattern-Match Coverage Checker." *Journal of Functional Programming*, 33,
  e3. DOI: [10.1017/S0956796823000072](https://doi.org/10.1017/S0956796823000072)
  -- Compositional pattern matching with constraint-based coverage checking;
  motivates the coreferential matching and exhaustiveness analysis design
  in Section 6.

- Martelli, A. & Montanari, U. (1982). "An Efficient Unification Algorithm."
  *ACM Transactions on Programming Languages and Systems*, 4(2), 258--282.
  DOI: [10.1145/357162.357169](https://doi.org/10.1145/357162.357169) --
  The reference unification algorithm implemented via PathMap in Section 4.

- Bagwell, P. (2001). "Ideal Hash Trees." Technical Report, EPFL. -- The
  Hash Array Mapped Trie (HAMT) data structure that PathMap builds upon
  for persistent structural sharing with O(1) fork semantics.

- Okasaki, C. (1999). *Purely Functional Data Structures*. Cambridge
  University Press. -- Foundational work on persistent data structures
  with amortized O(1) operations, underpinning PathMap's CoW fork
  semantics.

- Kiselyov, O., Shan, C., Friedman, D. P. & Sabry, A. (2005). "Backtracking,
  Interleaving, and Terminating Monad Transformers." *ICFP 2005*. ACM,
  pp. 192--203. DOI: [10.1145/1086365.1086390](https://doi.org/10.1145/1086365.1086390)
  -- The LogicT framework that drives the fork-heavy search patterns
  motivating PathMap-backed stores.

- Buchi, J. R. (1960). "Weak second-order arithmetic and finite automata."
  *Zeitschrift fur mathematische Logik und Grundlagen der Mathematik*, 6,
  66--92. -- Presburger NFA construction whose sparse transition tables
  benefit from PathMap storage (Section 8).

- Gay, S. & Vasconcelos, V. T. (2010). "Linear Type Theory for Asynchronous
  Session Types." *Journal of Functional Programming*, 20(1), 19--50. DOI:
  [10.1017/S0956796809990268](https://doi.org/10.1017/S0956796809990268)
  -- Substructural type modalities (linear, affine, relevant) motivating
  multiplicity tracking in Section 9.
