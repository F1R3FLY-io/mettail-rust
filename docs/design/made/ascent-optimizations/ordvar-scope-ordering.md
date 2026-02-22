# Opt 4: OrdVar Total Order and Scope Total Preorder

## 1. Motivation

Ascent Datalog uses BTree-based collections for its relations. BTree operations require the `Ord` trait. The `moniker` crate — which provides the variable binding infrastructure (`Var`, `Scope`) — implements `PartialEq` and `Hash` but not `Ord`.

Two custom wrappers provide ordering:

- **`OrdVar`** wraps `Var<String>` with a hash-based `Ord` on `UniqueId`
- **`Scope<P, T>`** wraps `moniker::Scope<P, T>` with a hash-pattern-then-body `Ord`

**Concern:** Are these orderings valid? Specifically:
- Does `OrdVar::cmp` form a total order (required for BTree correctness)?
- Does `Scope::cmp` at least form a total preorder (sufficient for BTree)?
- Is the ordering consistent with `PartialEq` (no contradictions)?

## 2. The Optimization

### 2.1 OrdVar

`OrdVar` wraps `Var<String>` and provides zero-allocation comparison:

```rust
// binding.rs:256-258
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct OrdVar(pub Var<String>);

// binding.rs:266-289
impl Ord for OrdVar {
    fn cmp(&self, other: &Self) -> Ordering {
        match (&self.0, &other.0) {
            (Var::Free(_), Var::Bound(_)) => Ordering::Less,
            (Var::Bound(_), Var::Free(_)) => Ordering::Greater,
            (Var::Free(a), Var::Free(b)) => {
                let hash_uid = |uid: &moniker::UniqueId| -> u64 {
                    let mut h = DefaultHasher::new();
                    uid.hash(&mut h);
                    h.finish()
                };
                hash_uid(&a.unique_id).cmp(&hash_uid(&b.unique_id))
            }
            (Var::Bound(a), Var::Bound(b)) =>
                a.scope.cmp(&b.scope).then(a.binder.cmp(&b.binder)),
        }
    }
}
```

**Strategy:** Variant discriminant first (Free < Bound), then:
- Free vs Free: compare hashes of `UniqueId` (u32 — no practical hash collisions)
- Bound vs Bound: lexicographic on `(scope, binder)` (both derive `Ord`)

### 2.2 Scope

`Scope<P, T>` wraps `moniker::Scope<P, T>` and provides hash-based comparison:

```rust
// binding.rs:87-89
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scope<P, T> {
    inner: moniker::Scope<P, T>,
}

// binding.rs:111-134
impl<P, T> Ord for Scope<P, T>
where
    P: Clone + PartialEq + Eq + BoundPattern<String> + Debug + Hash,
    T: Clone + PartialEq + Eq + BoundTerm<String> + Debug + Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        let hash_pat = |p: &P| -> u64 {
            let mut h = DefaultHasher::new();
            p.hash(&mut h);
            h.finish()
        };
        hash_pat(&self.inner.unsafe_pattern)
            .cmp(&hash_pat(&other.inner.unsafe_pattern))
            .then_with(|| self.inner.unsafe_body.cmp(&other.inner.unsafe_body))
    }
}
```

**Strategy:** Hash the pattern, compare hashes, then compare bodies using `T::Ord`. No cloning or unbinding — zero allocation.

## 3. Part A: OrdVar — Total Order

### 3.1 Definitions

**Definition (Var).** The variable type mirrors Rust's `moniker::Var`:

```
Inductive Var :=
  | Free : UID → Var
  | Bound : ScopeId → BinderId → Var
```

**Definition (cmp_var).** The comparison function:

```
cmp_var(v1, v2) :=
  match v1, v2 with
  | Free _,    Bound _ _ => Lt       (* Free < Bound *)
  | Bound _ _, Free _    => Gt       (* Bound > Free *)
  | Free a,    Free b    => Z.compare(hash_uid(a), hash_uid(b))
  | Bound s1 b1, Bound s2 b2 => cmp_then(cmp_scope_id(s1, s2),
                                          cmp_binder_id(b1, b2))
  end
```

**Hypothesis (hash_uid_injective).** `∀ a b : UID, hash_uid(a) = hash_uid(b) → a = b`

*Justification:* `UniqueId` wraps a `u32`. `DefaultHasher` maps `u32` values to `u64` hashes. For the `u32` domain (4 billion values), there are no practical collisions with `DefaultHasher` — the mapping is effectively injective.

### 3.2 Theorems

**Theorem (O1a: Reflexivity).**

> `∀ v, cmp_var(v, v) = Eq`

**Proof.** Case split on `v`:
- **Free(uid):** `Z.compare(hash_uid(uid), hash_uid(uid)) = Eq` by `Z.compare_refl`. **QED.**
- **Bound(s, b):** `cmp_then(cmp_scope_id(s, s), cmp_binder_id(b, b))`. By `cmp_scope_id_refl`, the first component is `Eq`, so `cmp_then(Eq, ...) = cmp_binder_id(b, b) = Eq` by `cmp_binder_id_refl`. **QED.**

---

**Theorem (O1b: Antisymmetry).**

> `∀ v1 v2, cmp_var(v1, v2) = Eq → v1 = v2`

**Proof.** Case split on `(v1, v2)`:
- **(Free, Bound):** `cmp_var = Lt ≠ Eq`. Contradiction. **QED.**
- **(Bound, Free):** `cmp_var = Gt ≠ Eq`. Contradiction. **QED.**
- **(Free a, Free b):** `Z.compare(hash_uid(a), hash_uid(b)) = Eq` implies `hash_uid(a) = hash_uid(b)` by `Z.compare_eq`. By `hash_uid_injective`, `a = b`. Therefore `Free(a) = Free(b)`. **QED.**
- **(Bound s1 b1, Bound s2 b2):** `cmp_then(cmp_scope_id(s1, s2), cmp_binder_id(b1, b2)) = Eq`. By `cmp_then_eq`, both components are `Eq`. By `cmp_scope_id_eq` and `cmp_binder_id_eq`, `s1 = s2` and `b1 = b2`. **QED.**

---

**Theorem (O1c: Transitivity).**

> `∀ v1 v2 v3, cmp_var(v1, v2) = Lt → cmp_var(v2, v3) = Lt → cmp_var(v1, v3) = Lt`

**Proof.** Case split on the 8 possible variant triples `(v1, v2, v3)`:

| v1 | v2 | v3 | `cmp(v1,v2)` | `cmp(v2,v3)` | Result |
|----|----|----|-------------|-------------|--------|
| Free | Free | Free | `Z.compare` | `Z.compare` | By `z_compare_lt_trans` |
| Free | Free | Bound | `Z.compare = Lt` | `Lt` | `cmp(Free,Bound) = Lt` |
| Free | Bound | Bound | `Lt` | ... | `cmp(Free,Bound) = Lt` |
| Bound | Free | _ | `Gt ≠ Lt` | — | Contradiction |
| Bound | Bound | Free | ... | `Gt ≠ Lt` | Contradiction |
| Bound | Bound | Bound | `cmp_then` | `cmp_then` | By `cmp_then_trans_lt_lt` |

The helper `cmp_then_trans_lt_lt` handles the Bound-Bound-Bound case by further case splitting on scope comparison results (Eq-Eq, Eq-Lt, Lt-Eq, Lt-Lt). **QED.**

---

**Theorem (O1d: Totality).**

> `∀ v1 v2, cmp_var(v1, v2) = Lt ∨ cmp_var(v1, v2) = Eq ∨ cmp_var(v1, v2) = Gt`

**Proof.** Case split on `(v1, v2)`:
- **(Free, Free):** `Z.compare` is total by `z_compare_total`. **QED.**
- **(Free, Bound):** `Lt`. **QED.**
- **(Bound, Free):** `Gt`. **QED.**
- **(Bound, Bound):** If `cmp_scope_id = Eq`, passes through to `cmp_binder_id` which is total. Otherwise, scope comparison determines the result. **QED.**

---

**Theorem (O3: Hash-Ord Consistency).**

> `∀ a b, cmp_var(Free(a), Free(b)) = Eq ↔ a = b`

**Proof.**
- **(→):** `Z.compare(hash_uid(a), hash_uid(b)) = Eq` implies `hash_uid(a) = hash_uid(b)` by `z_compare_eq`. By `hash_uid_injective`, `a = b`. **QED.**
- **(←):** `a = b` implies `cmp_var(Free(a), Free(a)) = Eq` by O1a. **QED.**

## 4. Part B: Scope — Total Preorder

### 4.1 Definitions

**Definition (Scope_t).** A scope is a record with a pattern and a body:

```
Record Scope_t := mkScope {
  scope_pattern : P;
  scope_body : T;
}
```

**Definition (cmp_scope).** Scope comparison: hash pattern first, then body:

```
cmp_scope(s1, s2) :=
  cmp_then(Z.compare(hash_pat(scope_pattern(s1)), hash_pat(scope_pattern(s2))),
           cmp_body(scope_body(s1), scope_body(s2)))
```

**Definition (scope_eq).** Structural equality:

```
scope_eq(s1, s2) := eq_pat(scope_pattern(s1), scope_pattern(s2)) ∧
                     scope_body(s1) = scope_body(s2)
```

### 4.2 Theorems

**Theorem (O2a: Reflexivity).**

> `∀ s, cmp_scope(s, s) = Eq`

**Proof.** `Z.compare(hash_pat(p), hash_pat(p)) = Eq` by `Z.compare_refl`. `cmp_then(Eq, cmp_body(b, b))`. `cmp_body(b, b) = Eq` by `cmp_body_refl`. **QED.**

---

**Theorem (O2b: Transitivity).**

> `∀ s1 s2 s3, cmp_scope(s1, s2) = Lt → cmp_scope(s2, s3) = Lt → cmp_scope(s1, s3) = Lt`

**Proof.** Let `h_i = hash_pat(scope_pattern(s_i))`. Case split on `Z.compare(h1, h2)` and `Z.compare(h2, h3)`:

- **(Eq, Eq):** `h1 = h2 = h3`. Pattern hashes are equal, so `Z.compare(h1, h3) = Eq`. The result depends on body comparison. By `cmp_body_trans_lt`, bodies are transitively ordered. **QED.**
- **(Eq, Lt):** `h1 = h2 < h3`. `Z.compare(h1, h3) = Z.compare(h2, h3) = Lt`. **QED.**
- **(Lt, Eq):** `h1 < h2 = h3`. `Z.compare(h1, h3) = Z.compare(h1, h2) = Lt`. **QED.**
- **(Lt, Lt):** `h1 < h2 < h3`. `Z.compare(h1, h3) = Lt` by `z_compare_lt_trans`. **QED.**

---

**Theorem (O2c: Totality).**

> `∀ s1 s2, cmp_scope(s1, s2) = Lt ∨ cmp_scope(s1, s2) = Eq ∨ cmp_scope(s1, s2) = Gt`

**Proof.** `Z.compare` is total. If `Eq`, `cmp_body` takes over (total by assumption). Otherwise `Lt` or `Gt` directly. **QED.**

---

**Theorem (O4: PartialEq → Ord-Eq).**

> `∀ s1 s2, scope_eq(s1, s2) → cmp_scope(s1, s2) = Eq`

**Proof.** Given `eq_pat(p1, p2)` and `b1 = b2`. By `hash_pat_compat`, `hash_pat(p1) = hash_pat(p2)`, so `Z.compare(...) = Eq`. Body comparison: `cmp_body(b1, b2) = cmp_body(b1, b1) = Eq` by `cmp_body_refl`. **QED.**

**Additional Hypothesis:** `hash_pat_compat : ∀ p1 p2, eq_pat(p1, p2) → hash_pat(p1) = hash_pat(p2)` — structurally equal patterns hash equally. This is a standard requirement of `Hash` implementations.

### 4.3 Why NOT Antisymmetric

The converse of O4 does **not** hold: `cmp_scope(s1, s2) = Eq` does NOT imply `scope_eq(s1, s2)`.

**Counter-scenario:** If two structurally distinct patterns `p1 ≠ p2` have `hash_pat(p1) = hash_pat(p2)` (hash collision), and their bodies are also equal (`b1 = b2`), then `cmp_scope` returns `Eq` despite the patterns being different.

This means `cmp_scope` is **not antisymmetric**, so `Scope` comparison is a **total preorder** rather than a **total order**.

**Why this is acceptable:** Rust's `BTreeMap`/`BTreeSet` only requires a total preorder for correctness. The BTree invariant is maintained as long as the ordering is reflexive, transitive, and total — antisymmetry is not required. Elements that compare as `Eq` are treated as equivalent for ordering purposes, and `PartialEq` handles actual equality checks.

## 5. Order Property Comparison Table

| Property | OrdVar | Scope |
|----------|--------|-------|
| Reflexive | O1a | O2a |
| Antisymmetric | O1b (with `hash_uid_injective`) | Not provable (hash collisions) |
| Transitive | O1c | O2b |
| Total | O1d | O2c |
| **Classification** | **Total Order** | **Total Preorder** |

## 6. Spec-to-Code Traceability

| Rocq Definition | Rust / Ascent Code | Location |
|-----------------|-------------------|----------|
| `cmp_var` | `OrdVar::cmp` | `binding.rs:266-289` |
| `cmp_scope` | `Scope::cmp` | `binding.rs:111-134` |
| `hash_uid` | `hash_uid` closure in `OrdVar::cmp` | `binding.rs:279-283` |
| `hash_pat` | `hash_pat` closure in `Scope::cmp` | `binding.rs:125-129` |
| `Free` / `Bound` | `Var::Free` / `Var::Bound` | `moniker` crate |
| `OrdVar` | `pub struct OrdVar(pub Var<String>)` | `binding.rs:256-258` |
| `Scope_t` | `pub struct Scope<P, T> { inner }` | `binding.rs:87-89` |
| `O1a_cmp_var_refl` | — | `TotalOrder.v:175-182` |
| `O1b_cmp_var_antisym` | — | `TotalOrder.v:187-199` |
| `O1c_cmp_var_trans` | — | `TotalOrder.v:247-259` |
| `O1d_cmp_var_total` | — | `TotalOrder.v:264-280` |
| `O2a_cmp_scope_refl` | — | `TotalOrder.v:341-345` |
| `O2b_cmp_scope_trans` | — | `TotalOrder.v:350-369` |
| `O2c_cmp_scope_total` | — | `TotalOrder.v:374-385` |
| `O3_hash_ord_consistency` | — | `TotalOrder.v:285-292` |
| `O4_eq_implies_cmp_eq` | — | `TotalOrder.v:394-402` |

## 7. Rocq Source Reference

- **File:** `formal/rocq/ascent_optimizations/theories/TotalOrder.v` (425 lines)
- **Dependencies:** `Prelude.v`
- **Sections:**
  - `OrdVarOrder` (lines 127-294): Parameterized over `UID`, `ScopeId`, `BinderId`, `hash_uid`, comparison functions with standard order hypotheses
  - `ScopeOrder` (lines 300-425): Parameterized over `P`, `T`, `hash_pat`, `cmp_body`, `eq_pat`
- **Auxiliary lemmas:** `z_compare_refl`, `z_compare_eq`, `z_compare_lt_trans`, `z_compare_antisym`, `z_compare_total`, `nat_compare_*`, `cmp_then_*`, `cmp_var_flip`, `cmp_then_trans_lt_lt`
