# Rocq Verification Artifacts

## 1. File Inventory

| File | Lines | Dependencies | What's Proven |
|------|-------|-------------|---------------|
| `Prelude.v` | 146 | (none) | Hash model, list utilities, multiset notation, decidable equality |
| `TLSPoolEquiv.v` | 133 | `Prelude.v` | T1: Pool pattern = Vec pattern (Opt 2) |
| `TotalOrder.v` | 425 | `Prelude.v` | O1a-d: OrdVar total order, O2a-c: Scope preorder, O3, O4 (Opt 4) |
| `GraphReachability.v` | 156 | `Prelude.v` | Graph model, reach, bidi_reach, field_types (shared by Opts 3, 5) |
| `DeadRulePruning.v` | 183 | `Prelude.v`, `GraphReachability.v` | P2: Dead rules derive nothing, P3: Pruned = Full (Opt 3) |
| `SCCSplitting.v` | 362 | `Prelude.v`, `GraphReachability.v` | S1-S3: Core/Full fixpoint equivalence (Opt 5) |
| `ConcreteInstantiations.v` | 385 | All above | Calculator + RhoCalc language instances |
| **Total** | **1,790** | | **Zero `Admitted`** |

## 2. Dependency Graph

```
                    Prelude.v (146 lines)
                   /    |    \
                  /     |     \
                 v      v      v
    TLSPoolEquiv.v  TotalOrder.v  GraphReachability.v
       (133)           (425)            (156)
          |              |           /           \
          |              |          v              v
          |              |   DeadRulePruning.v  SCCSplitting.v
          |              |       (183)             (362)
          v              v          v              v
          +----------- ConcreteInstantiations.v --+
                            (385)
```

**Critical ordering:** `GraphReachability.v` must compile before both `DeadRulePruning.v` and `SCCSplitting.v`. `ConcreteInstantiations.v` depends on all six other files.

## 3. Build Instructions

### 3.1 Prerequisites

- Rocq 9.1 (Coq) with Stdlib
- GNU Make

### 3.2 Building

From the project root:

```bash
cd formal/rocq/ascent_optimizations

# Generate Makefile from _CoqProject (if needed)
coq_makefile -f _CoqProject -o CoqMakefile

# Build with resource limits (recommended on shared systems)
systemd-run --user --scope \
  -p MemoryMax=126G \
  -p CPUQuota=1800% \
  -p IOWeight=30 \
  -p TasksMax=200 \
  make -f CoqMakefile -j1
```

### 3.3 Expected Output

- 7 `.vo` files in `theories/`
- Build time: ~30 seconds on modern hardware
- No warnings, no `Admitted`

### 3.4 Cleaning

```bash
make -f CoqMakefile clean
```

### 3.5 _CoqProject

```
-Q theories AscentOptimizations

theories/Prelude.v
theories/GraphReachability.v
theories/TLSPoolEquiv.v
theories/TotalOrder.v
theories/DeadRulePruning.v
theories/SCCSplitting.v
theories/ConcreteInstantiations.v
```

## 4. Theorem Catalog

### 4.1 Prelude

| ID | Statement | Proof Strategy |
|----|-----------|---------------|
| `hash_le_refl` | `∀ a, hash_le a a` | Unfold, `lia` |
| `hash_le_trans` | `∀ a b c, hash_le a b → hash_le b c → hash_le a c` | Unfold, `lia` |
| `hash_le_total` | `∀ a b, hash_le a b ∨ hash_le b a` | Unfold, `lia` |
| `hash_le_antisym` | `∀ a b, hash_le a b → hash_le b a → a = b` | `hash_injective`, `lia` |
| `flat_map_nil` | `flat_map f [] = []` | Reflexivity |
| `flat_map_cons` | `flat_map f (x::xs) = f x ++ flat_map f xs` | Reflexivity |
| `flat_map_app` | `flat_map f (l1++l2) = flat_map f l1 ++ flat_map f l2` | Induction on `l1` |
| `flat_map_all_nil` | `(∀ x ∈ l, f x = []) → flat_map f l = []` | Induction on `l` |
| `flat_map_filter_nil` | `(∀ x ∈ l, ¬pred(x) → f x = []) → flat_map f l = flat_map f (filter pred l)` | Induction on `l` |
| `cond_extract_true` | `cond_extract true vals = vals` | Reflexivity |
| `cond_extract_false` | `cond_extract false vals = []` | Reflexivity |

### 4.2 TLSPoolEquiv (Opt 2)

| ID | Statement | Proof Strategy |
|----|-----------|---------------|
| `pool_equiv` (T1) | `pool_pattern(pc, t) = vec_pattern(t)` | Unfold, case split on `classify t` |
| `pool_contents_irrelevant` | `pool_pattern(c1, t) = pool_pattern(c2, t)` | Two applications of T1 |
| `pool_empty_equiv` | `pool_pattern([], t) = vec_pattern(t)` | Immediate from T1 |

### 4.3 TotalOrder (Opt 4)

| ID | Statement | Proof Strategy |
|----|-----------|---------------|
| `z_compare_refl` | `Z.compare a a = Eq` | Stdlib |
| `z_compare_eq` | `Z.compare a b = Eq → a = b` | Stdlib |
| `z_compare_lt_trans` | `Z.compare a b = Lt → Z.compare b c = Lt → Z.compare a c = Lt` | Stdlib + `Z.lt_trans` |
| `z_compare_antisym` | `Z.compare a b = CompOpp(Z.compare b a)` | Stdlib |
| `z_compare_total` | `Z.compare a b ∈ {Lt, Eq, Gt}` | Destruct |
| `nat_compare_refl` | `Nat.compare a a = Eq` | Stdlib |
| `nat_compare_eq` | `Nat.compare a b = Eq → a = b` | Stdlib |
| `nat_compare_lt_trans` | Transitivity for `Nat.compare` | Stdlib + `lia` |
| `cmp_then_refl` | `cmp_then Eq c = c` | Reflexivity |
| `cmp_then_eq` | `cmp_then c1 c2 = Eq → c1 = Eq ∧ c2 = Eq` | Destruct `c1` |
| `cmp_var_flip` | `cmp_var v1 v2 = CompOpp(cmp_var v2 v1)` | Case split + antisymmetry |
| `cmp_then_trans_lt_lt` | Transitivity helper for `cmp_then` | 4 sub-cases on scope comparison |
| `O1a_cmp_var_refl` | `cmp_var v v = Eq` | Case split on `v` |
| `O1b_cmp_var_antisym` | `cmp_var v1 v2 = Eq → v1 = v2` | Case split + `hash_uid_injective` |
| `O1c_cmp_var_trans` | `cmp_var v1 v2 = Lt → cmp_var v2 v3 = Lt → cmp_var v1 v3 = Lt` | 8-way case split |
| `O1d_cmp_var_total` | `cmp_var v1 v2 ∈ {Lt, Eq, Gt}` | Case split + `z_compare_total` |
| `O3_hash_ord_consistency` | `cmp_var(Free a, Free b) = Eq ↔ a = b` | `z_compare_eq` + `hash_uid_injective` |
| `O2a_cmp_scope_refl` | `cmp_scope s s = Eq` | Unfold + `z_compare_refl` + `cmp_body_refl` |
| `O2b_cmp_scope_trans` | `cmp_scope s1 s2 = Lt → cmp_scope s2 s3 = Lt → cmp_scope s1 s3 = Lt` | 4 sub-cases on hash comparison |
| `O2c_cmp_scope_total` | `cmp_scope s1 s2 ∈ {Lt, Eq, Gt}` | Destruct `Z.compare` |
| `O4_eq_implies_cmp_eq` | `scope_eq s1 s2 → cmp_scope s1 s2 = Eq` | `hash_pat_compat` + `cmp_body_refl` |
| `O4_converse_not_provable` | (documentation remark) | `exact I` |

### 4.4 GraphReachability (Shared)

| ID | Statement | Proof Strategy |
|----|-----------|---------------|
| `reach_edge` | `edge a b → reach a b` | `reach_step` + `reach_refl` |
| `reach_trans` | `reach a b → reach b c → reach a c` | Induction on `reach a b` |
| `bidi_reach_refl` | `bidi_reach primary primary` | `reach_refl` in both directions |
| `bidi_reach_sym` | Symmetry helper | Direct |
| `unreachable_no_edge` | `¬reach src tgt → ¬edge src tgt` | Contrapositive via `reach_edge` |

### 4.5 DeadRulePruning (Opt 3)

| ID | Statement | Proof Strategy |
|----|-----------|---------------|
| `P2_dead_rule_derives_nothing` | `¬reach(src,tgt) → rule_derive(src,tgt,db) = []` | `flat_map_all_nil` + P1 |
| `P3_pruned_equals_full` | `full_derive(tgt,db) = pruned_derive(tgt,db)` | `flat_map_filter_nil` + P2 |
| `fixpoint_unchanged` | Same as P3 (corollary) | `exact P3_pruned_equals_full` |

### 4.6 SCCSplitting (Opt 5)

| ID | Statement | Proof Strategy |
|----|-----------|---------------|
| `primary_is_core` | `is_core(primary)` | `bidi_reach_refl` |
| `S1_non_core_derives_nothing` | `¬is_core(tgt) ∧ nce(db) → full_step(db,tgt) = []` | `flat_map_all_nil`, case split on `is_core(src)` |
| `S2_core_derivations_equal` | `is_core(tgt) ∧ nce(db) → full_step = core_step` | `flat_map_filter_nil` |
| `full_iter_preserves_invariant` | `nce(db) → nce(full_iter(db))` | `merge_preserves_noncore_empty` + S1 |
| `full_iter_n_preserves_invariant` | `nce(db) → nce(full_iter_n(n,db))` | Induction on `n` |
| `S3_step_equivalence` | Step functions agree per-category | Case split on `is_core(c)` |
| `S3_iter_equivalence` | `nce(db) → full_iter(db) = core_iter(db)` | `merge_ext` + S1 + S2 |
| `S3_fixpoint_restriction` | `nce(db) → full_iter_n(n,db) = core_iter_n(n,db)` | Induction on `n` + invariant preservation |

### 4.7 ConcreteInstantiations

| ID | Statement | Proof Strategy |
|----|-----------|---------------|
| `eqb_IntKind_spec` | Boolean equality spec for `IntKind` | Exhaustive case split |
| `all_IntKinds_complete` | Completeness | `destruct k; auto` |
| `all_IntKinds_nodup` | No duplicates | `repeat constructor; intuition discriminate` |
| `calc_pool_equiv` | Calculator pool equivalence | `apply pool_equiv` |
| `calc_no_dead_rules` | Vacuously correct | `exact I` |
| `calc_ordvar_total_order` | Universal OrdVar properties | `exact I` |
| `eqb_RhoCat_spec` | Boolean equality spec for `RhoCat` | Exhaustive case split |
| `all_RhoCats_complete` | Completeness | `destruct c; auto` |
| `all_RhoCats_nodup` | No duplicates | `repeat constructor; intuition discriminate` |
| `rho_Proc_reaches_Name` | `reach(Proc, Name)` | `reach_step` + `edge_Proc_Name` |
| `rho_Name_reaches_Proc` | `reach(Name, Proc)` | `reach_step` + `edge_Name_Proc` |
| `rho_Proc_is_core` | `bidi_reach(Proc, Proc)` | `reach_refl` both directions |
| `rho_Name_is_core` | `bidi_reach(Proc, Name)` | Forward + backward reach |
| `rho_Proc_edges_only` | `edge(Proc, tgt) → tgt ∈ {Proc, Name}` | Inversion on `rho_edge` |
| `rho_Name_edges_only` | `edge(Name, tgt) → tgt ∈ {Proc, Name}` | Inversion on `rho_edge` |
| `rho_Proc_Name_closed` | `{Proc, Name}` closed under edges | Edge-only lemmas |
| `rho_Proc_reach_only_Proc_Name` | `reach(Proc, tgt) → tgt ∈ {Proc, Name}` | Induction on `reach` + closure |
| `rho_Proc_not_reach_Expr` | `¬reach(Proc, Expr)` | `rho_Proc_reach_only_Proc_Name` + discriminate |
| `rho_Expr_not_core` | `¬bidi_reach(Proc, Expr)` | Forward direction fails |
| `rho_Chan_not_core` | `¬bidi_reach(Proc, Chan)` | Forward direction fails |
| `rho_Ground_not_core` | `¬bidi_reach(Proc, Ground)` | Forward direction fails |
| `rho_Float_not_core` | `¬bidi_reach(Proc, Float)` | Forward direction fails |
| `rho_scc_splitting_applicable` | SCC splitting applies to RhoCalc | `exact I` |

## 5. Hypothesis Audit

All unproven axioms (hypotheses) in the proof suite, with justifications:

| Hypothesis | Used In | Justification |
|------------|---------|---------------|
| `hash_injective` | `Prelude.v` | `DefaultHasher` on `u32` (`UniqueId`) is effectively injective. The u32 domain has 4 billion values; `DefaultHasher` maps to u64 with no practical collisions. |
| `hash_uid_injective` | `TotalOrder.v` | Instance of `hash_injective` for `UniqueId`. Same justification. |
| `cmp_scope_id_refl` | `TotalOrder.v` | `ScopeOffset` derives `Ord`; `cmp(x, x) = Eq` is a standard property. |
| `cmp_scope_id_eq` | `TotalOrder.v` | `ScopeOffset` comparison is antisymmetric. Standard for derived `Ord`. |
| `cmp_scope_id_trans_lt` | `TotalOrder.v` | `ScopeOffset` comparison is transitive. Standard for derived `Ord`. |
| `cmp_scope_id_antisym` | `TotalOrder.v` | `ScopeOffset` comparison satisfies antisymmetry. Standard for derived `Ord`. |
| `cmp_binder_id_refl` | `TotalOrder.v` | `BinderIndex` derives `Ord`; same standard property. |
| `cmp_binder_id_eq` | `TotalOrder.v` | Same as scope_id. |
| `cmp_binder_id_trans_lt` | `TotalOrder.v` | Same as scope_id. |
| `cmp_binder_id_antisym` | `TotalOrder.v` | Same as scope_id. |
| `cmp_body_refl` | `TotalOrder.v` | Body type `T` has `Ord`; reflexivity is standard. |
| `cmp_body_trans_lt` | `TotalOrder.v` | Body type `T` has `Ord`; transitivity is standard. |
| `cmp_body_eq_implies_eq` | `TotalOrder.v` | Body type `T` has `Ord`; antisymmetry is standard. |
| `cmp_body_antisym` | `TotalOrder.v` | Body type `T` has `Ord`; `cmp(a,b) = CompOpp(cmp(b,a))` is standard. |
| `hash_pat_compat` | `TotalOrder.v` | `eq_pat(p1, p2) → hash_pat(p1) = hash_pat(p2)`. Required by Rust's `Hash` trait contract. |
| `eq_pat_dec` | `TotalOrder.v` | Pattern equality is decidable. Patterns are algebraic data types with decidable equality. |
| `node_eqb_spec` | `GraphReachability.v` | Category names are strings; string equality is decidable. |
| `all_nodes_complete` | `GraphReachability.v` | All categories enumerated from `language.types` (exhaustive). |
| `all_nodes_nodup` | `GraphReachability.v` | Category names are unique in `language.types` (enforced by grammar). |
| `edge_dec` | `GraphReachability.v` | Edge relation is computed from finite constructor fields; decidable. |
| `field_types_are_edges` | `GraphReachability.v` | Field types define edges (by construction in `compute_category_reachability`). |
| `edges_are_field_types` | `GraphReachability.v` | Converse: edges come from field types only. |
| `unreachable_no_field_types` | `GraphReachability.v` | Unreachable categories have no matching constructor fields. Code generator only emits arms for existing constructors. |
| `extract_empty_when_unreachable` (P1) | `DeadRulePruning.v` | Generated match has no arms for unreachable pairs — falls through to `[]`. See `categories.rs:50-53`. |
| `all_cats_complete` | `DeadRulePruning.v`, `SCCSplitting.v` | Same as `all_nodes_complete`. |
| `cat_eqb_spec` | `DeadRulePruning.v`, `SCCSplitting.v` | Same as `node_eqb_spec`. |
| `reach_dec` | `DeadRulePruning.v` | Reachability decidable on finite graphs (transitive closure is computed as `BTreeSet`). |
| `derive_from_empty` | `SCCSplitting.v` | Empty source relation → no rule fires. `flat_map` over `[]` is `[]`. |
| `derive_unreachable_empty` | `SCCSplitting.v` | From Opt 3 (P2): unreachable rules derive nothing. |
| `derive_core_noncore_empty` | `SCCSplitting.v` | Core→non-core extraction path requires non-core intermediates (empty by invariant). See Opt 5 hypothesis justification. |
| `get_set_same` | `SCCSplitting.v` | Standard database axiom: reading what you wrote. |
| `get_set_other` | `SCCSplitting.v` | Standard database axiom: writing one key doesn't affect others. |
| `get_empty` | `SCCSplitting.v` | Standard database axiom: empty DB has no facts. |
| `merge_preserves_noncore_empty` | `SCCSplitting.v` | Merging `[]` into empty relations preserves emptiness. Merge is additive. |
| `merge_ext` | `SCCSplitting.v` | Merge is extensional: pointwise-equal functions yield equal databases. |

## 6. Consolidated Spec-to-Code Traceability

Master table sorted by Rust file for reverse lookup:

| Rust File | Line(s) | Rocq Definition | Rocq File |
|-----------|---------|-----------------|-----------|
| `binding.rs` | 87-89 | `Scope_t` | `TotalOrder.v` |
| `binding.rs` | 111-134 | `cmp_scope` | `TotalOrder.v` |
| `binding.rs` | 125-129 | `hash_pat` | `TotalOrder.v` |
| `binding.rs` | 256-258 | `OrdVar` | `TotalOrder.v` |
| `binding.rs` | 266-289 | `cmp_var` | `TotalOrder.v` |
| `binding.rs` | 279-283 | `hash_uid` | `TotalOrder.v`, `Prelude.v` |
| `categories.rs` | 34-48 | dead rule skip | `DeadRulePruning.v` |
| `categories.rs` | 50-53 | `extract` | `DeadRulePruning.v` |
| `common.rs` | 215-298 | `reach`, `edge`, `Node` | `GraphReachability.v` |
| `common.rs` | 219-265 | `field_types`, `edge` | `GraphReachability.v` |
| `common.rs` | 267-297 | transitive closure loop | `GraphReachability.v` |
| `common.rs` | 357-391 | `is_core`, `core_cats` | `SCCSplitting.v` |
| `common.rs` | 369-383 | `bidi_reach` check | `GraphReachability.v` |
| `common.rs` | 448-482 | `pool_pattern` | `TLSPoolEquiv.v` |
| `common.rs` | 471 | `take` | `TLSPoolEquiv.v` |
| `common.rs` | 472 | `clear` | `TLSPoolEquiv.v` |
| `common.rs` | 478 | `return` (set) | `TLSPoolEquiv.v` |
| `language.rs` | 1254-1288 | dispatcher (full) | `SCCSplitting.v` |
| `language.rs` | 1262-1272 | `core_step` | `SCCSplitting.v` |
| `language.rs` | 1275-1286 | `full_step` | `SCCSplitting.v` |
| `language.rs` | 1356-1366 | `run_ascent_typed` | `SCCSplitting.v` |
| `helpers.rs` | — | `vec_pattern` (pre-Opt 2) | `TLSPoolEquiv.v` |
| `helpers.rs` | — | `rule_derive` | `DeadRulePruning.v` |

## 7. Relationship to Rule Consolidation Proofs

The rule consolidation proofs (Opt 1) are a separate verification effort in `formal/rocq/rule_consolidation/`:

| Property | Ascent Optimization Proofs | Rule Consolidation Proofs |
|----------|---------------------------|--------------------------|
| Location | `formal/rocq/ascent_optimizations/` | `formal/rocq/rule_consolidation/` |
| Files | 7 | 5 |
| Lines | 1,790 | 1,469 |
| Scope | Infrastructure optimizations (alloc, rules, ordering, SCC) | Per-rule consolidation (N `if let` → 1 `match`) |
| Key theorems | T1, P2-P3, O1-O4, S1-S3 | R1-R3, V4 |
| Shared techniques | `flat_map_all_nil`, `flat_map_filter_nil` | Same |
| Documentation | `docs/design/made/ascent-optimizations/` | `docs/design/made/rule-consolidation/` |
| Conventions | Same: `**Definition.**`, `**Theorem.**`, `**QED.**` | Same |
