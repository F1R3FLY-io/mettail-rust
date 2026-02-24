# Rocq Verification Artifacts

## 1. File Inventory

| File                    | Lines     | Dependencies | What's Proven                                                   |
|-------------------------|-----------|--------------|-----------------------------------------------------------------|
| `Prelude.v`             | 183       | (none)       | Multiset equivalence, flat_map lemmas, cond_extract, option_eqb |
| `DisjointPatterns.v`    | 192       | `Prelude.v`  | D1-D3: classify uniqueness, match_extract, per_kind_extract     |
| `RuleConsolidation.v`   | 400       | `Prelude.v`  | R1: for_match_equiv, R2: if_match_equiv, R3: pair_match_equiv   |
| `VariantIndexRebuild.v` | 266       | `Prelude.v`  | V4: variant_index_extract_equiv, variant_index_congruence_equiv |
| `AreaProofs.v`          | 428       | All above    | 6 area instantiations for Calculator IntKind                    |
| **Total**               | **1,469** |              | **Zero `Admitted`**                                             |

## 2. Dependency Graph

```
                Prelude.v (183 lines)
               /         \
              v           v
DisjointPatterns.v   RuleConsolidation.v
     (192)                (400)
              \         /     \
               v       v       v
         AreaProofs.v    VariantIndexRebuild.v
            (428)              (266)
```

**Critical ordering:** `Prelude.v` must compile before all others. `AreaProofs.v` depends on `RuleConsolidation.v` and `VariantIndexRebuild.v`. Both `DisjointPatterns.v` and `RuleConsolidation.v` depend only on `Prelude.v`.

## 3. Build Instructions

### 3.1 Prerequisites

- Rocq 9.0+ (tested with 9.1.0)
- Standard library (included with Rocq)
- GNU Make

### 3.2 Building

From the project root:

```bash
cd formal/rocq/rule_consolidation

# Generate Makefile from _CoqProject (if needed)
coq_makefile -f _CoqProject -o CoqMakefile

# Build with resource limits (recommended on shared systems)
systemd-run --user --scope \
  -p MemoryMax=16G \
  -p CPUQuota=400% \
  make -f CoqMakefile -j1
```

### 3.3 Expected Output

- 5 `.vo` files in `theories/`
- Build time: ~15 seconds on modern hardware
- No warnings, no `Admitted`

### 3.4 Cleaning

```bash
make -f CoqMakefile clean
```

### 3.5 _CoqProject

```
-Q theories RuleConsolidation

theories/Prelude.v
theories/DisjointPatterns.v
theories/RuleConsolidation.v
theories/VariantIndexRebuild.v
theories/AreaProofs.v
```

## 4. Theorem Catalog

### 4.1 Prelude.v

| ID                       | Statement                                                                        | Proof Strategy                       |
|--------------------------|----------------------------------------------------------------------------------|--------------------------------------|
| `flat_map_nil`           | `flat_map f [] = []`                                                             | Reflexivity                          |
| `flat_map_cons`          | `flat_map f (x::xs) = f x ++ flat_map f xs`                                      | Reflexivity                          |
| `flat_map_app`           | `flat_map f (l1++l2) = flat_map f l1 ++ flat_map f l2`                           | Induction on `l1`                    |
| `flat_map_singleton`     | `flat_map f [x] = f x`                                                           | Simpl + `app_nil_r`                  |
| `flat_map_all_nil`       | `(∀ k ∈ ks, f k = []) → flat_map f ks = []`                                      | Induction on `ks`                    |
| `flat_map_single_hit`    | `NoDup ks → k0 ∈ ks → (∀ k ∈ ks, k ≠ k0 → f k = []) → flat_map f ks ≡ₘ f k0`     | Induction on `ks`, `NoDup` inversion |
| `option_eqb_spec`        | `(∀ a b, eqb_A a b = true ↔ a = b) → ∀ x y, option_eqb eqb_A x y = true ↔ x = y` | Case split on `x`, `y`               |
| `cond_extract_hit`       | `cond_extract eqb_K (Some k) k extract = extract k`                              | Unfold + `eqb_K_spec` reflexivity    |
| `cond_extract_miss_diff` | `k' ≠ k → cond_extract eqb_K (Some k') k extract = []`                           | Unfold + `eqb_K_spec` contradiction  |
| `cond_extract_miss_none` | `cond_extract eqb_K None k extract = []`                                         | Reflexivity                          |

### 4.2 DisjointPatterns.v

| ID                        | Statement                                                   | Proof Strategy                      |
|---------------------------|-------------------------------------------------------------|-------------------------------------|
| `match_extract_some` (D2) | `classify t = Some k → match_extract t = extract k t`       | Unfold + rewrite `Hcl`              |
| `match_extract_none` (D3) | `classify t = None → match_extract t = []`                  | Unfold + rewrite `Hcl`              |
| `classify_unique` (D1)    | `classify t = Some k1 → classify t = Some k2 → k1 = k2`     | Rewrite + inversion                 |
| `per_kind_extract_hit`    | `classify t = Some k → per_kind_extract k t = extract k t`  | Unfold + `eqb_K_spec`               |
| `per_kind_extract_miss`   | `classify t = Some k' → k ≠ k' → per_kind_extract k t = []` | Unfold + `eqb_K_spec` contradiction |
| `per_kind_extract_none`   | `classify t = None → per_kind_extract k t = []`             | Unfold + rewrite                    |

### 4.3 RuleConsolidation.v

**R1 Section (ForMatchEquiv):**

| ID                     | Statement                                           | Proof Strategy                                                                                |
|------------------------|-----------------------------------------------------|-----------------------------------------------------------------------------------------------|
| `per_kind_hit`         | `classify t = Some k → per_kind k t = extract k t`  | Unfold + `eqb_K_spec`                                                                         |
| `per_kind_miss`        | `classify t = Some k' → k ≠ k' → per_kind k t = []` | Unfold + `eqb_K_spec` contradiction                                                           |
| `per_kind_none`        | `classify t = None → per_kind k t = []`             | Unfold + rewrite                                                                              |
| `for_match_equiv` (R1) | `all_rules t ≡ₘ consolidated_extract t`             | Case split on `classify t`; `flat_map_single_hit` for `Some k`, `flat_map_all_nil` for `None` |

**R2 Section (IfMatchEquiv):**

| ID                    | Statement                                                                                        | Proof Strategy                                           |
|-----------------------|--------------------------------------------------------------------------------------------------|----------------------------------------------------------|
| `if_match_equiv` (R2) | `(∃ k, In k trigger_kinds ∧ if_let_matches k t = true) ↔ match_predicate trigger_kinds t = true` | Split; `existsb_exists` in both directions               |
| `if_match_bool_equiv` | `existsb (fun k => if_let_matches k t) trigger_kinds = match_predicate trigger_kinds t`          | Case split on `classify t`; induction on `trigger_kinds` |

**R3 Section (PairMatchEquiv):**

| ID                      | Statement                                                                              | Proof Strategy                                                                                                            |
|-------------------------|----------------------------------------------------------------------------------------|---------------------------------------------------------------------------------------------------------------------------|
| `per_kind_pair_hit`     | `classify s = Some k → classify t = Some k → per_kind_pair k s t = extract_pair k s t` | Unfold + `eqb_K_spec`                                                                                                     |
| `per_kind_pair_miss_s`  | `classify s = Some k' → k ≠ k' → per_kind_pair k s t = []`                             | Unfold + `eqb_K_spec` contradiction                                                                                       |
| `per_kind_pair_miss_t`  | `classify s = Some ks → classify t = Some kt → ks ≠ kt → per_kind_pair k s t = []`     | Unfold + `eqb_K_spec` case analysis                                                                                       |
| `per_kind_pair_none_s`  | `classify s = None → per_kind_pair k s t = []`                                         | Unfold + rewrite                                                                                                          |
| `per_kind_pair_none_t`  | `classify s = Some ks → classify t = None → per_kind_pair k s t = []`                  | Unfold + rewrite                                                                                                          |
| `pair_match_equiv` (R3) | `original_pair_rules s t ≡ₘ pair_match_extract s t`                                    | 4-way case split on `(classify s, classify t)`; `flat_map_single_hit` for same-constructor, `flat_map_all_nil` for others |

### 4.4 VariantIndexRebuild.v

| ID                                 | Statement                                                                                                     | Proof Strategy                                                                                |
|------------------------------------|---------------------------------------------------------------------------------------------------------------|-----------------------------------------------------------------------------------------------|
| `vi_arm_miss`                      | `classify t = Some k' → k ≠ k' → (arm for k) = []`                                                            | Rewrite + `eqb_K_spec` contradiction                                                          |
| `vi_arm_none`                      | `classify t = None → (arm for k) = []`                                                                        | Rewrite                                                                                       |
| `vi_per_kind_hit`                  | `classify t = Some k → vi_per_kind t k = combine (extract_fields k t) (map (vi_of k) (seq 0 (num_fields k)))` | Unfold + `eqb_K_spec`                                                                         |
| `vi_per_kind_miss`                 | `classify t = Some k' → k ≠ k' → vi_per_kind t k = []`                                                        | Unfold + `eqb_K_spec` contradiction                                                           |
| `vi_per_kind_none`                 | `classify t = None → vi_per_kind t k = []`                                                                    | Unfold + rewrite                                                                              |
| `original_vi_extract_eq`           | `original_vi_extract t = flat_map (vi_per_kind t) all_kinds`                                                  | Reflexivity                                                                                   |
| `variant_index_extract_equiv` (V4) | `original_vi_extract t ≡ₘ vi_extract t`                                                                       | Case split on `classify t`; `flat_map_single_hit` for `Some k`, `flat_map_all_nil` for `None` |
| `variant_index_congruence_equiv`   | `map rw_fn (original_vi_extract t) ≡ₘ map rw_fn (vi_extract t)`                                               | `Permutation_map` + V4                                                                        |

### 4.5 AreaProofs.v

| ID                                     | Statement                                                                                  | Proof Strategy                                                  |
|----------------------------------------|--------------------------------------------------------------------------------------------|-----------------------------------------------------------------|
| `eqb_IntKind_spec`                     | `eqb_IntKind a b = true ↔ a = b`                                                           | Exhaustive case split (8 x 8)                                   |
| `all_IntKinds_nodup`                   | `NoDup all_IntKinds`                                                                       | `repeat constructor; intuition discriminate`                    |
| `area1_subterm_extraction`             | `all_rules t ≡ₘ consolidated_extract t` (for Int)                                          | `apply for_match_equiv` with IntKind infrastructure             |
| `area2_auto_variant_lam_congruence`    | `all_rules t ≡ₘ consolidated_extract t` (for AutoKind)                                     | `apply for_match_equiv` with AutoKind infrastructure            |
| `area3_equation_congruence`            | `original_pair_rules s t ≡ₘ pair_match_extract s t` (for Int)                              | `apply pair_match_equiv` with IntKind infrastructure            |
| `area4_explicit_congruence_extraction` | `original_vi_extract t ≡ₘ vi_extract_int t`                                                | `apply variant_index_extract_equiv` with IntKind infrastructure |
| `area4_explicit_congruence`            | `map rw_fn (original_vi_extract t) ≡ₘ map rw_fn (vi_extract_int t)`                        | `Permutation_map` + extraction theorem                          |
| `area5_fold_triggers`                  | `(∃ k ∈ fold_trigger_kinds, if_let_matches k t) ↔ match_predicate fold_trigger_kinds t`    | `apply if_match_equiv` with `eqb_IntKind_spec`                  |
| `area5_fold_triggers_bool`             | `existsb (if_let_matches · t) fold_trigger_kinds = match_predicate fold_trigger_kinds t`   | `apply if_match_bool_equiv`                                     |
| `area6_fold_identities`                | `(∃ k ∈ fold_identity_kinds, if_let_matches k t) ↔ match_predicate fold_identity_kinds t`  | `apply if_match_equiv` with `eqb_IntKind_spec`                  |
| `area6_fold_identities_bool`           | `existsb (if_let_matches · t) fold_identity_kinds = match_predicate fold_identity_kinds t` | `apply if_match_bool_equiv`                                     |

## 5. Hypothesis Audit

All hypotheses from Section parameters in the 5 Rocq files, with justifications:

| Hypothesis                  | Used In                                                                               | Justification                                                                                                                                                                                                                                                                    |
|-----------------------------|---------------------------------------------------------------------------------------|----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `eqb_K_spec`                | `DisjointPatterns.v`, `RuleConsolidation.v` (all 3 sections), `VariantIndexRebuild.v` | Rust `enum` types derive `PartialEq`; boolean equality reflects propositional equality. Instantiated as `eqb_IntKind_spec` in `AreaProofs.v`.                                                                                                                                    |
| `all_kinds_complete`        | `DisjointPatterns.v`, `RuleConsolidation.v` (R1, R3), `VariantIndexRebuild.v`         | Finite `enum` — `all_kinds` lists every constructor. Enforced by code generator iterating `language.terms`.                                                                                                                                                                      |
| `all_kinds_nodup`           | `DisjointPatterns.v`, `RuleConsolidation.v` (R1, R3), `VariantIndexRebuild.v`         | Distinct constructors in `enum`. Instantiated as `all_IntKinds_nodup` (proven by `repeat constructor; intuition discriminate`).                                                                                                                                                  |
| `vi_of_injective` (V1)      | `VariantIndexRebuild.v`                                                               | Sequential assignment in codegen: variant indices are assigned by enumerating constructors and their field positions in order. See `congruence.rs:414`.                                                                                                                          |
| `rebuild_identity` (V2)     | `VariantIndexRebuild.v`                                                               | Round-trip property: rebuilding a term with its original field value at the same variant index recovers the original term. Standard property of pattern matching on algebraic data types.                                                                                        |
| `rebuild_replaces` (V3)     | `VariantIndexRebuild.v`                                                               | Constructor-preserving field replacement: rebuilding preserves the constructor kind and replaces exactly the target field. Follows from the structure of the generated `match (lhs, vi)` expression.                                                                             |
| `vi_extract_spec`           | `VariantIndexRebuild.v`                                                               | Extraction matches the `combine`/`map`/`seq` pattern: for a term with constructor kind `k`, the extraction produces `(field_i, vi_of(k, i))` pairs for all field positions. Directly corresponds to the generated `match lhs { Cat::A(x0, x1) => vec![(x0, 0), (x1, 1)], ... }`. |
| `vi_extract_none`           | `VariantIndexRebuild.v`                                                               | Empty extraction for unclassified terms: when `classify(t) = None`, the generated match falls through to `_ => vec![]`.                                                                                                                                                          |
| `extract_fields_length`     | `VariantIndexRebuild.v`                                                               | Field count consistency: `length(extract_fields(k, t)) = num_fields(k)`. The number of fields extracted from a term equals the constructor's arity. Holds by construction of the generated match arms.                                                                           |
| `classify_complete`         | `AreaProofs.v` (Areas 1, 3, 4)                                                        | Instance of `all_kinds_complete` for `Int` with `all_IntKinds`.                                                                                                                                                                                                                  |
| `eqb_AK_spec`               | `AreaProofs.v` (Area 2)                                                               | Instance of `eqb_K_spec` for the auto-variant `AutoKind` type.                                                                                                                                                                                                                   |
| `all_AK_complete`           | `AreaProofs.v` (Area 2)                                                               | Instance of `all_kinds_complete` for `AutoKind`.                                                                                                                                                                                                                                 |
| `all_AK_nodup`              | `AreaProofs.v` (Area 2)                                                               | Instance of `all_kinds_nodup` for `AutoKind`.                                                                                                                                                                                                                                    |
| `vi_of_int_injective`       | `AreaProofs.v` (Area 4)                                                               | Instance of `vi_of_injective` for `Int`.                                                                                                                                                                                                                                         |
| `vi_extract_int_spec`       | `AreaProofs.v` (Area 4)                                                               | Instance of `vi_extract_spec` for `Int`.                                                                                                                                                                                                                                         |
| `vi_extract_int_none`       | `AreaProofs.v` (Area 4)                                                               | Instance of `vi_extract_none` for `Int`.                                                                                                                                                                                                                                         |
| `extract_fields_int_length` | `AreaProofs.v` (Area 4)                                                               | Instance of `extract_fields_length` for `Int`.                                                                                                                                                                                                                                   |

## 6. Consolidated Spec-to-Code Traceability

Master table sorted by Rust file for reverse lookup:

| Rust File       | Line(s) | Rocq Definition                                                        | Rocq File               |
|-----------------|---------|------------------------------------------------------------------------|-------------------------|
| `helpers.rs`    | 52      | `generate_consolidated_deconstruction_rules` → `consolidated_extract`  | `RuleConsolidation.v`   |
| `helpers.rs`    | 295     | `generate_consolidated_congruence_rules` → `for_match_equiv` (R1)      | `RuleConsolidation.v`   |
| `equations.rs`  | 78      | `generate_congruence_rules` → `pair_match_extract`                     | `RuleConsolidation.v`   |
| `congruence.rs` | 429     | `generate_consolidated_simple_congruence` → `vi_extract`, `vi_rebuild` | `VariantIndexRebuild.v` |
| `mod.rs`        | 452     | `generate_fold_big_step_rules` → `match_predicate`                     | `RuleConsolidation.v`   |
| `rules.rs`      | 75      | `generate_rule_clause_with_category`                                   | (not formally modeled)  |

### Traceability for Abstract Functions

| Rocq Abstraction     | Rust/Ascent Pattern                                 | Generated Location   |
|----------------------|-----------------------------------------------------|----------------------|
| `classify`           | `match t { Cat::Ctor(..) => Some(k), ... }`         | helpers.rs:68        |
| `extract`            | Match arm body: `vec![f0.clone(), ...]`             | helpers.rs:83        |
| `match_extract`      | `(match t { ... }).into_iter()`                     | helpers.rs:45        |
| `per_kind_extract`   | `if let Cat::Ctor(..) = t` (original N rules)       | (pre-consolidation)  |
| `match_predicate`    | `if (match t { ... => true, _ => false })`          | mod.rs fold triggers |
| `pair_match_extract` | `(match (s, t) { ... }).into_iter()`                | equations.rs         |
| `vi_extract`         | `for (field_val, vi) in (match lhs { ... })`        | congruence.rs:434    |
| `vi_rebuild`         | `match (lhs, vi) { (Cat::A(..), 0) => ... }`        | congruence.rs:474    |
| `all_kinds`          | All constructors in `language.terms` for a category | helpers.rs:70        |

## 7. Relationship to Ascent Optimization Proofs

The ascent optimization proofs (Opts 2-5) are a separate verification effort in `formal/rocq/ascent_optimizations/`:

| Property          | Rule Consolidation Proofs                       | Ascent Optimization Proofs                                 |
|-------------------|-------------------------------------------------|------------------------------------------------------------|
| Location          | `formal/rocq/rule_consolidation/`               | `formal/rocq/ascent_optimizations/`                        |
| Files             | 5                                               | 7                                                          |
| Lines             | 1,469                                           | 1,790                                                      |
| Scope             | Per-rule consolidation (N `if let` → 1 `match`) | Infrastructure optimizations (alloc, rules, ordering, SCC) |
| Key theorems      | R1-R3, V4                                       | T1, P2-P3, O1-O4, S1-S3                                    |
| Shared techniques | `flat_map_all_nil`, `flat_map_single_hit`       | Same                                                       |
| Documentation     | `docs/design/made/rule-consolidation/`          | `docs/design/made/ascent-optimizations/`                   |
| Conventions       | `**Definition.**`, `**Theorem.**`, `**QED.**`   | Same                                                       |
