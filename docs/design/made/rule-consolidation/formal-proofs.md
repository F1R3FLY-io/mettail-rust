# Formal Proofs of Rule Consolidation Semantic Equivalence

This document presents the formal proofs that the Ascent rule consolidation (replacing N per-constructor rules with 1 consolidated rule) preserves the **semantics** of the Datalog program: the consolidated rule derives exactly the same set of facts as the original N rules.

## 1. Definitions

### 1.1 Type System

Let **T** be a type with disjoint constructors (a Rust `enum`). Each constructor has a *kind* drawn from a finite set **K** = {k_1, ..., k_n}.

**Definition (Classifier).** The function

    classify : T -> K ∪ {⊥}

assigns each term its constructor kind, or ⊥ if the term does not match any tracked constructor.

**Key property:** Since `classify` is a function (deterministic pattern matching), for any term t there is *at most one* k such that classify(t) = k.

**Definition (Extractor).** The function

    extract : K x T -> P(V)

returns the set of values extracted from a term when its constructor kind matches. For example, `extract(KAdd, Add(a, b)) = {a, b}`.

**Definition (Consolidated Match).** The function

    match_extract(t) = { extract(k, t)  if classify(t) = k
                       { {}              if classify(t) = ⊥

models the Rust `match t { Cat::A(..) => vec![..], ..., _ => vec![] }`.

### 1.2 Preconditions

| ID | Precondition | Justification |
|----|-------------|---------------|
| P1 | classify is total and deterministic | Rust pattern matching on enums |
| P2 | all_kinds enumerates every K that classify can return | Finite enum |
| P3 | all_kinds has no duplicates | Distinct constructors |

These hold for any Rust enum type.

### 1.3 What "Semantic Equivalence" Means

A Datalog rule `H <-- B1, ..., Bn` is a function from database state to derived facts. Two rules are **semantically equivalent** if, for every database state, they derive the same set of new facts.

For the consolidation transform, we prove that for every input term t (bound by `cat(t)`), the set of values produced by the `for`/`if` clause is identical between the original N rules and the consolidated rule. Since the rest of the rule body (relation lookups, head construction) depends only on these values, identical extracted values imply identical derived facts.

---

## 2. Core Theorem: For-Match Equivalence (R1)

**Theorem (R1).** For all t in T:

    U_{k in K} { extract(k, t) | classify(t) = k }  =  match_extract(t)

where the left side models the union of facts derived by N separate `if let` rules, and the right side models the single consolidated `match` rule.

**Proof.** Case split on classify(t).

**Case 1: classify(t) = k for some k in K.**
- *Left side:* The union iterates over all k' in K. For k' = k, the guard `classify(t) = k` holds, contributing extract(k, t). For k' != k, the guard fails (by determinism of classify), contributing nothing. So the union equals extract(k, t).
- *Right side:* match_extract(t) = extract(k, t) by definition.
- *Conclusion:* Both sides equal extract(k, t). **QED.**

**Case 2: classify(t) = ⊥.**
- *Left side:* For every k' in K, the guard `classify(t) = k'` fails, so the union is empty.
- *Right side:* match_extract(t) = {} by definition.
- *Conclusion:* Both sides are empty. **QED.**

**Rocq theorem:** `for_match_equiv` in `RuleConsolidation.v`.

**Applies to:** Area 1 (Subterm Extraction), Area 2 (Auto-Variant Congruence).

---

## 3. If-Match Equivalence (R2)

**Theorem (R2).** For a set of trigger kinds S subset K and any term t:

    (exists k in S. classify(t) = k)  <=>  match_predicate_S(t) = true

where match_predicate_S models `match t { Cat::A(_) => true, ..., _ => false }`.

**Proof.**
- *Forward:* If classify(t) = k and k in S, then the match on t returns true for the arm matching k.
- *Backward:* If match_predicate returns true, then classify(t) = k for some k, and the existsb check found k in S.

**Corollary (Boolean form).** The disjunction `any(k in S, if_let_matches(k, t))` equals `match_predicate_S(t)`.

**Rocq theorem:** `if_match_equiv`, `if_match_bool_equiv` in `RuleConsolidation.v`.

**Applies to:** Area 5 (Fold Triggers), Area 6 (Fold Identities).

---

## 4. Pair-Match Equivalence (R3)

**Theorem (R3).** For terms s, t in T:

    U_{k in K} { extract_pair(k, s, t) | classify(s) = k AND classify(t) = k }
    =
    pair_match_extract(s, t)

where pair_match_extract matches (s, t) simultaneously and extracts paired fields only when both terms have the same constructor.

**Proof.** Case split on (classify(s), classify(t)).

**Case (k, k) — same constructor:**
- The union contributes only extract_pair(k, s, t).
- pair_match_extract(s, t) returns extract_pair(k, s, t).
- Both sides equal. **QED.**

**Case (k1, k2) where k1 != k2 — different constructors:**
- For each k' in K, the double guard fails (can't have classify(s) = k' AND classify(t) = k' simultaneously when s and t have different constructors).
- pair_match_extract returns empty (the eqb check fails).
- Both sides empty. **QED.**

**Case (⊥, _) or (_, ⊥):**
- Both sides trivially empty. **QED.**

**Rocq theorem:** `pair_match_equiv` in `RuleConsolidation.v`.

**Applies to:** Area 3 (Equation Congruence).

---

## 5. Variant-Index Rebuild (V4)

For explicit rewrite congruence (Area 4), each (constructor, field_position) pair is assigned a unique **variant index** vi. The consolidated rule uses vi to:
1. **Extract:** produce (field_value, vi) pairs from the source term
2. **Rebuild:** given (original_term, vi, new_value), reconstruct the term with the field at vi replaced

### 5.1 Definitions

**Definition (Variant Index Assignment).**

    vi_of : K x N -> N

maps (constructor kind, field position within that constructor) to a globally unique natural number.

**Precondition (V1 — Injectivity):** vi_of(k1, i1) = vi_of(k2, i2) implies k1 = k2 and i1 = i2.

This holds because the Rust codegen assigns variant indices sequentially.

**Definition (VI Extract).**

    vi_extract(t) = { (field_i(t), vi_of(k, i)) | classify(t) = k, i in fields(k) }

**Definition (VI Rebuild).**

    vi_rebuild(t, vi, v') = term with field at vi replaced by v'

**Precondition (V2 — Round-trip):** vi_rebuild(t, vi_of(k, i), field_i(t)) = t.

**Precondition (V3 — Correctness):** vi_rebuild preserves the constructor kind and replaces exactly the target field.

### 5.2 Theorem

**Theorem (V4).** For all t in T:

    U_{k in K, i in fields(k)} { (field_i(t), vi_of(k, i)) | classify(t) = k }
    =
    vi_extract(t)

**Proof.** Direct application of R1 with V = (field_value, vi) pairs. The classifier selects the constructor, the extractor produces (field, vi) pairs for each field position. By disjointness, only the matching constructor contributes. **QED.**

**Corollary.** The derived rw_cat facts are identical:

    { (t, vi_rebuild(t, vi, rw(v))) | (v, vi) in original_extract(t) }
    =
    { (t, vi_rebuild(t, vi, rw(v))) | (v, vi) in vi_extract(t) }

since the map function is applied to permutation-equivalent lists.

**Rocq theorem:** `variant_index_extract_equiv`, `variant_index_congruence_equiv` in `VariantIndexRebuild.v`.

**Applies to:** Area 4 (Explicit Rewrite Congruence).

---

## 6. Area Applications

Each consolidation area is an instance of the core theorems:

| Area | Name | Core Theorem | What's Preserved |
|------|------|-------------|------------------|
| 1 | Subterm Extraction | R1 | Set of subterms added to target category |
| 2 | Auto-Variant Congruence | R1 | Set of lam fields fed to rw_cat |
| 3 | Equation Congruence | R3 | Set of paired fields checked for equality |
| 4 | Explicit Rewrite Congruence | V4 (uses R1) | Set of (field, vi) pairs for rebuild |
| 5 | Fold Triggers | R2 | Set of terms triggering fold evaluation |
| 6 | Fold Identities | R2 | Set of terms receiving identity folds |

### Area 1: Subterm Extraction

- **Original:** N rules, one per constructor. Each rule fires when its `if let` matches, extracting fields of the target category.
- **Consolidated:** 1 rule per (source_cat, target_cat) pair. A single `match` extracts all relevant subterms.
- **Proof:** Direct instance of R1 with T = source type, K = constructor kinds, V = target type.
- **Rocq:** `area1_subterm_extraction` in `AreaProofs.v`
- **proptest:** `prop_subterm_extraction_equiv`

### Area 2: Auto-Variant Congruence

- **Original:** 2C rules (Apply + MApply per domain). Each extracts the lam field.
- **Consolidated:** 1 rule extracts lam from all Apply/MApply variants.
- **Proof:** Instance of R1 with K = {ApplyDom1, MApplyDom1, ApplyDom2, ...}.
- **Rocq:** `area2_auto_variant_lam_congruence` in `AreaProofs.v`

### Area 3: Equation Congruence

- **Original:** N rules per constructor. Each matches (s, t) with the same constructor and checks per-field equality.
- **Consolidated:** 1 rule per field-type signature. `match (s, t)` extracts paired fields.
- **Proof:** Direct instance of R3.
- **Rocq:** `area3_equation_congruence` in `AreaProofs.v`
- **proptest:** `prop_pair_match_equiv`

### Area 4: Explicit Rewrite Congruence

- **Original:** N rules (one per constructor x field). Each extracts one field, checks rewrite, rebuilds.
- **Consolidated:** 1 rule per (source_cat, field_cat). Variant indices identify which field to rebuild.
- **Proof:** Direct instance of V4. Injectivity of vi ensures no collisions.
- **Rocq:** `area4_explicit_congruence_extraction`, `area4_explicit_congruence` in `AreaProofs.v`
- **proptest:** `prop_rebuild_roundtrip`, `prop_extraction_completeness`, `test_variant_index_injectivity`

### Area 5: Fold Triggers

- **Original:** N rules (one per fold-mode constructor). `rw_cat(s, t) <-- cat(s), if let Cat::FoldCtor(..) = s, fold_cat(s, t)`.
- **Consolidated:** 1 rule with `if (match s { ... => true, _ => false })`.
- **Proof:** Direct instance of R2 with trigger_kinds = fold-mode constructors.
- **Rocq:** `area5_fold_triggers` in `AreaProofs.v`
- **proptest:** `prop_fold_trigger_equiv`

### Area 6: Fold Identities

- **Original:** N rules (one per non-fold constructor). `fold_cat(t, t) <-- cat(t), if let Cat::NonFold(..) = t`.
- **Consolidated:** 1 rule with `if (match t { ... => true, _ => false })`.
- **Proof:** Direct instance of R2 with trigger_kinds = non-fold constructors.
- **Rocq:** `area6_fold_identities` in `AreaProofs.v`

---

## 7. Fixpoint Equivalence

The Datalog program computes a fixpoint via the **immediate consequence operator** T_P: given a database state I, T_P(I) adds all facts derivable by one application of any rule. The fixpoint is the least I such that T_P(I) = I.

Since each consolidated rule derives exactly the same facts as the original N rules it replaces (proven above), the immediate consequence operator is unchanged:

    T_P_consolidated(I) = T_P_original(I)  for all I

Therefore the fixpoints are identical, and the consolidated program computes the same result as the original.

---

## 8. Verification Artifacts

| Artifact | Location | Status |
|----------|----------|--------|
| Rocq proofs (5 files) | `formal/rocq/rule_consolidation/theories/` | All compile (verified) |
| proptest suite (9 tests) | `languages/tests/consolidation_tests.rs` | All pass |
| Full test suite (229+ tests) | `cargo test --workspace` | All pass |

### Spec-to-Code Traceability

| Rocq Definition | Rust/Ascent Code | Location |
|----------------|------------------|----------|
| `classify` | `match t { Cat::Ctor(..) => ...` | helpers.rs:68-81 |
| `extract` | Match arm body `vec![f0.clone(), ...]` | helpers.rs:83-110 |
| `match_extract` | `(match t { ... }).into_iter()` | helpers.rs:45-65 |
| `match_predicate` | `if (match t { ... => true, _ => false })` | mod.rs fold triggers |
| `pair_match_extract` | `(match (s,t) { ... }).into_iter()` | equations.rs |
| `vi_extract` | `for (field_val, vi) in (match lhs { ... })` | congruence.rs:434-471 |
| `vi_rebuild` | `match (lhs, vi) { (Cat::A(..), 0) => ... }` | congruence.rs:474-512 |
| `all_kinds` | All constructors in language.terms for a category | helpers.rs:70 |
