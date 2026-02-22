# Formal Proofs of Rule Consolidation Semantic Equivalence

This document presents the formal proofs that the Ascent rule consolidation (replacing N per-constructor rules with 1 consolidated rule) preserves the **semantics** of the Datalog program: the consolidated rule derives exactly the same set of facts as the original N rules.

All proofs have been mechanically verified in Rocq (Coq 9.1). For the complete theorem catalog, build instructions, and hypothesis audit, see [rocq-artifacts.md](rocq-artifacts.md).

---

## 1. Definitions

### 1.1 Type System

Let **T** be a type with disjoint constructors (a Rust `enum`). Each constructor has a *kind* drawn from a finite set **K** = {k_1, ..., k_n}.

The Rocq formalization parameterizes over these types in a `Section`:

```coq
Variable T : Type.        (* Term type, e.g., Int *)
Variable K : Type.        (* Constructor kind type, e.g., IntKind *)
Variable V : Type.        (* Extracted value type, e.g., Int for subterms *)
```

**Definition (Classifier).** The function

    classify : T → K ∪ {⊥}

assigns each term its constructor kind, or ⊥ if the term does not match any tracked constructor. In Rocq, this is modeled as `classify : T → option K`.

**Key property:** Since `classify` is a function (deterministic pattern matching), for any term t there is *at most one* k such that classify(t) = Some k. This is D1 (`classify_unique`) in `DisjointPatterns.v`.

**Definition (Extractor).** The function

    extract : K × T → list V

returns the list of values extracted from a term when its constructor kind matches. For example, `extract(KAdd, Add(a, b)) = [a, b]`.

**Definition (Consolidated Match).** The function

    match_extract(t) = { extract(k, t)  if classify(t) = Some k
                       { []             if classify(t) = None

models the Rust `match t { Cat::A(..) => vec![..], ..., _ => vec![] }`. In Rocq:

```coq
Definition match_extract (t : T) : list V :=
  match classify t with
  | Some k => extract k t
  | None   => []
  end.
```

This is D2 (`match_extract_some`) and D3 (`match_extract_none`) in `DisjointPatterns.v`.

**Definition (Per-Kind Conditional Extraction).** The function

    per_kind_extract(k, t) = { extract(k, t)  if classify(t) = Some k
                             { []             otherwise

models an individual `if let Cat::k(..) = t` rule. In Rocq:

```coq
Definition per_kind_extract (k : K) (t : T) : list V :=
  cond_extract eqb_K (classify t) k (fun k' => extract k' t).
```

Three helper lemmas characterize its behavior:

- `per_kind_extract_hit`: classify(t) = Some k ⟹ per_kind_extract(k, t) = extract(k, t)
- `per_kind_extract_miss`: classify(t) = Some k', k ≠ k' ⟹ per_kind_extract(k, t) = []
- `per_kind_extract_none`: classify(t) = None ⟹ per_kind_extract(k, t) = []

**Definition (Original Rules).** The original N per-constructor rules are modeled as:

    original_rules(t) = flat_map (λk. per_kind_extract(k, t)) all_kinds

This computes the union of extractions across all constructor kinds, exactly modeling the N separate Ascent rules.

### 1.2 Preconditions

| ID | Precondition | Justification | Rocq Hypothesis |
|----|-------------|---------------|-----------------|
| P1 | classify is total and deterministic | Rust pattern matching on enums | Built into the type: `classify : T → option K` is a function |
| P2 | all_kinds enumerates every K that classify can return | Finite enum, code generator iterates `language.terms` | `all_kinds_complete` |
| P3 | eqb_K reflects propositional equality | Rust `enum` derives `PartialEq` | `eqb_K_spec` |
| P4 | all_kinds has no duplicates | Distinct constructors | `all_kinds_nodup` |

These hold for any Rust enum type. P4 is required by `flat_map_single_hit` (from `Prelude.v`), which is the key workhorse lemma: given a list with no duplicates where exactly one element produces a non-nil result, `flat_map` over that list is permutation-equivalent to just that one element's contribution.

### 1.3 What "Semantic Equivalence" Means

A Datalog rule `H <-- B1, ..., Bn` is a function from database state to derived facts. Two rules are **semantically equivalent** if, for every database state, they derive the same set of new facts.

For the consolidation transform, we prove that for every input term t (bound by `cat(t)`), the set of values produced by the `for`/`if` clause is identical between the original N rules and the consolidated rule. Since the rest of the rule body (relation lookups, head construction) depends only on these values, identical extracted values imply identical derived facts.

We use multiset equivalence (Rocq `Permutation`, notation `≡ₘ`) rather than strict list equality because:

- Datalog relations are unordered sets
- The order in which match arms appear does not affect the set of derived facts
- `Permutation` is an equivalence relation with congruence under `map`, `flat_map`, etc.

---

## 2. Core Theorem: For-Match Equivalence (R1)

**Theorem (R1: `for_match_equiv`).** For all t in T:

    flat_map (λk. per_kind(k, t)) all_kinds  ≡ₘ  consolidated_extract(t)

where the left side models the union of facts derived by N separate `if let` rules, and the right side models the single consolidated `match` rule. In Rocq:

```coq
Theorem for_match_equiv :
  forall (t : T),
    all_rules t ≡ₘ consolidated_extract t.
```

### Helper Lemmas

Three lemmas characterize the per-kind function (from `RuleConsolidation.v:97-118`):

**Lemma (`per_kind_hit`).** If classify(t) = Some k, then per_kind(k, t) = extract(k, t).

**Lemma (`per_kind_miss`).** If classify(t) = Some k' and k ≠ k', then per_kind(k, t) = [].

**Lemma (`per_kind_none`).** If classify(t) = None, then per_kind(k, t) = [].

### Proof

Case split on classify(t).

**Case 1: classify(t) = Some k for some k ∈ K.**

```
all_rules t
  = flat_map per_kind all_kinds                   (by definition)
  ≡ₘ per_kind k t                                 (by flat_map_single_hit:
                                                     NoDup all_kinds   [P4]
                                                     k ∈ all_kinds     [P2, via all_kinds_complete]
                                                     ∀ k' ≠ k, per_kind k' t = []  [per_kind_miss])
  = extract k t                                    (by per_kind_hit)
  = consolidated_extract t                         (by definition, since classify t = Some k)
```

The key step is `flat_map_single_hit`: since `all_kinds` has no duplicates (P4), k is in `all_kinds` (P2), and every other kind k' produces `[]` (by `per_kind_miss` and the determinism of `classify`), the entire `flat_map` is permutation-equivalent to just `per_kind k t`.

**Case 2: classify(t) = None.**

```
all_rules t
  = flat_map per_kind all_kinds                   (by definition)
  = []                                             (by flat_map_all_nil:
                                                     ∀ k ∈ all_kinds, per_kind k t = []  [per_kind_none])
  = consolidated_extract t                         (by definition, since classify t = None)
```

Both sides are empty. **QED.**

**Rocq source:** `RuleConsolidation.v:122-143` (`for_match_equiv`).

**Applies to:** Area 1 (Subterm Extraction), Area 2 (Auto-Variant Congruence).

---

## 3. If-Match Equivalence (R2)

For boolean predicates (fold triggers and identities), the consolidation replaces N `if let` guards with a single `if (match ... { ... })` boolean predicate.

**Definition (`match_predicate`).** For a set of trigger kinds S ⊆ K and term t:

```coq
Definition match_predicate (trigger_kinds : list K) (t : T) : bool :=
  match classify t with
  | Some k => existsb (eqb_K k) trigger_kinds
  | None   => false
  end.
```

This models the Rust `if (match t { Cat::A(_) => true, Cat::B(_,_) => true, _ => false })`.

**Definition (`if_let_matches`).** The individual `if let` guard for kind k:

```coq
Definition if_let_matches (k : K) (t : T) : bool :=
  match classify t with
  | Some k' => eqb_K k' k
  | None    => false
  end.
```

**Theorem (R2: `if_match_equiv`).** For trigger kinds S ⊆ K and any term t:

    (∃ k ∈ S, if_let_matches(k, t) = true)  ⟺  match_predicate(S, t) = true

### Proof

Split into forward and backward directions.

**Forward (→):** Suppose there exists k ∈ S such that `if_let_matches(k, t) = true`. Then `classify(t) = Some k'` for some k' (otherwise `if_let_matches` would return `false`). By `existsb_exists`, `existsb (eqb_K k') trigger_kinds = true`, so `match_predicate(S, t) = true`.

**Backward (←):** Suppose `match_predicate(S, t) = true`. Then `classify(t) = Some k'` (otherwise the predicate returns `false`). By `existsb_exists`, there exists k ∈ S such that `eqb_K k' k = true`, i.e., `if_let_matches(k, t) = true`. **QED.**

**Corollary (`if_match_bool_equiv`).** The boolean form directly captures the codegen pattern:

    existsb (λk. if_let_matches(k, t)) trigger_kinds = match_predicate(trigger_kinds, t)

Proof by case split on `classify(t)`: when `Some k'`, both sides reduce to `existsb (eqb_K k') trigger_kinds`; when `None`, both sides reduce to `false` (by induction on `trigger_kinds`).

**Rocq source:** `RuleConsolidation.v:192-239`.

**Applies to:** Area 5 (Fold Triggers), Area 6 (Fold Identities).

---

## 4. Pair-Match Equivalence (R3)

For equation congruence (Area 3), two terms s and t are matched simultaneously. The consolidated rule uses `match (s, t)` to extract paired field values only when both terms have the same constructor.

**Definition (`pair_match_extract`).** The consolidated pair-match expression:

```coq
Definition pair_match_extract (s t : T) : list V :=
  match classify s, classify t with
  | Some ks, Some kt =>
      if eqb_K ks kt then extract_pair ks s t
      else []
  | _, _ => []
  end.
```

**Definition (`per_kind_pair`).** The per-kind pair extraction for original rules:

```coq
Definition per_kind_pair (k : K) (s t : T) : list V :=
  match classify s, classify t with
  | Some ks, Some kt =>
      if eqb_K ks k then
        if eqb_K kt k then extract_pair k s t
        else []
      else []
  | _, _ => []
  end.
```

**Definition (`original_pair_rules`).** The original N per-constructor pair rules:

    original_pair_rules(s, t) = flat_map (λk. per_kind_pair(k, s, t)) all_kinds

**Theorem (R3: `pair_match_equiv`).** For all s, t in T:

    original_pair_rules(s, t) ≡ₘ pair_match_extract(s, t)

### Helper Lemmas

Five lemmas characterize `per_kind_pair` (from `RuleConsolidation.v:310-354`):

- `per_kind_pair_hit`: classify(s) = Some k ∧ classify(t) = Some k ⟹ per_kind_pair(k, s, t) = extract_pair(k, s, t)
- `per_kind_pair_miss_s`: classify(s) = Some k', k ≠ k' ⟹ per_kind_pair(k, s, t) = []
- `per_kind_pair_miss_t`: classify(s) = Some ks, classify(t) = Some kt, ks ≠ kt ⟹ per_kind_pair(k, s, t) = []
- `per_kind_pair_none_s`: classify(s) = None ⟹ per_kind_pair(k, s, t) = []
- `per_kind_pair_none_t`: classify(s) = Some ks, classify(t) = None ⟹ per_kind_pair(k, s, t) = []

### Proof

Four-way case split on (classify(s), classify(t)).

**Case (Some ks, Some kt) with ks = kt (same constructor):**

```
original_pair_rules s t
  = flat_map (λk. per_kind_pair k s t) all_kinds
  ≡ₘ per_kind_pair ks s t                         (by flat_map_single_hit:
                                                     NoDup all_kinds    [P4]
                                                     ks ∈ all_kinds     [P2]
                                                     ∀ k' ≠ ks, per_kind_pair k' s t = []
                                                       [per_kind_pair_miss_s])
  = extract_pair ks s t                            (by per_kind_pair_hit, using kt = ks)
  = pair_match_extract s t                         (eqb_K ks ks = true, by P3)
```

**Case (Some ks, Some kt) with ks ≠ kt (different constructors):**

Every kind k in `all_kinds` produces `[]`: if `eqb_K ks k = true` then ks = k, but then `eqb_K kt k = eqb_K kt ks`, which is `false` since ks ≠ kt (by `per_kind_pair_miss_t`). By `flat_map_all_nil`, the left side is `[]`. The right side is also `[]` since `eqb_K ks kt = false`.

**Case (Some ks, None):**

Every arm produces `[]` by `per_kind_pair_none_t`. The right side is `[]` by definition.

**Case (None, _):**

Every arm produces `[]` by `per_kind_pair_none_s`. The right side is `[]` by definition.

All four cases match. **QED.**

**Rocq source:** `RuleConsolidation.v:358-398`.

**Applies to:** Area 3 (Equation Congruence).

---

## 5. Variant-Index Rebuild (V4)

For explicit rewrite congruence (Area 4), each (constructor, field_position) pair is assigned a unique **variant index** (vi). The consolidated rule uses vi to:
1. **Extract:** produce (field_value, vi) pairs from the source term
2. **Rebuild:** given (original_term, vi, new_value), reconstruct the term with the field at vi replaced

### 5.1 Definitions

**Definition (Variant Index Assignment).**

    vi_of : K × ℕ → ℕ

maps (constructor kind, field position within that constructor) to a globally unique natural number. In the Rust codegen, these are assigned sequentially:

```text
Int::Add(x0, x1) => vec![(x0.clone(), 0usize), (x1.clone(), 1usize)],
Int::Neg(x0)     => vec![(x0.clone(), 2usize)],
Int::Sub(x0, x1) => vec![(x0.clone(), 3usize), (x1.clone(), 4usize)],
```

**Definition (`vi_per_kind`).** The per-kind extraction with variant indices:

```coq
Definition vi_per_kind (t : T) (k : K) : list (V * nat) :=
  match classify t with
  | Some k' =>
      if eqb_K k' k then
        combine (extract_fields k t) (map (vi_of k) (seq 0 (num_fields k)))
      else []
  | None => []
  end.
```

**Definition (`original_vi_extract`).** The original N per-constructor rules:

    original_vi_extract(t) = flat_map (λk. vi_per_kind(t, k)) all_kinds

### 5.2 Preconditions

| ID | Precondition | Justification | Rocq Hypothesis |
|----|-------------|---------------|-----------------|
| V1 | vi_of is injective | Sequential assignment in codegen | `vi_of_injective` |
| V2 | Rebuilding with the original value recovers the original term | Round-trip property of pattern matching | `rebuild_identity` |
| V3 | Rebuild preserves constructor and replaces exactly the target field | Constructor-preserving field replacement | `rebuild_replaces` |

Additionally, the vi_extract function is specified by two hypotheses:
- `vi_extract_spec`: for classify(t) = Some k, vi_extract(t) = combine(extract_fields(k, t), map(vi_of(k), seq(0, num_fields(k))))
- `vi_extract_none`: for classify(t) = None, vi_extract(t) = []

### 5.3 Helper Lemmas

Three lemmas characterize `vi_per_kind`:

- `vi_per_kind_hit`: classify(t) = Some k ⟹ vi_per_kind(t, k) = combine(extract_fields(k, t), map(vi_of(k), seq(0, num_fields(k))))
- `vi_per_kind_miss`: classify(t) = Some k', k ≠ k' ⟹ vi_per_kind(t, k) = []
- `vi_per_kind_none`: classify(t) = None ⟹ vi_per_kind(t, k) = []

### 5.4 Theorem

**Theorem (V4: `variant_index_extract_equiv`).** For all t in T:

    original_vi_extract(t) ≡ₘ vi_extract(t)

### Proof

Case split on classify(t).

**Case: classify(t) = Some k.**

```
original_vi_extract t
  = flat_map (vi_per_kind t) all_kinds             (by original_vi_extract_eq)
  ≡ₘ vi_per_kind t k                               (by flat_map_single_hit:
                                                      NoDup all_kinds    [P4]
                                                      k ∈ all_kinds      [P2]
                                                      ∀ k' ≠ k, vi_per_kind t k' = []
                                                        [vi_per_kind_miss])
  = combine (extract_fields k t)
            (map (vi_of k) (seq 0 (num_fields k))) (by vi_per_kind_hit)
  = vi_extract t                                    (by vi_extract_spec, since classify t = Some k)
```

**Case: classify(t) = None.**

```
original_vi_extract t
  = flat_map (vi_per_kind t) all_kinds
  = []                                              (by flat_map_all_nil + vi_per_kind_none)
  = vi_extract t                                    (by vi_extract_none)
```

**QED.**

**Corollary (`variant_index_congruence_equiv`).** The derived rw_cat facts are identical:

    map (λ(v, vi). (t, vi_rebuild(t, vi, rw(v)))) (original_vi_extract t)
    ≡ₘ
    map (λ(v, vi). (t, vi_rebuild(t, vi, rw(v)))) (vi_extract t)

Proof by `Permutation_map` applied to V4: since `original_vi_extract t ≡ₘ vi_extract t`, mapping any function over both preserves the permutation equivalence.

**Rocq source:** `VariantIndexRebuild.v:230-264`.

**Applies to:** Area 4 (Explicit Rewrite Congruence).

---

## 6. Area Applications

Each consolidation area is an instance of the core theorems. All instantiations use the Calculator language's `IntKind` type:

```coq
Inductive IntKind : Type :=
  | KAdd | KSub | KNeg | KPow | KFact | KTern | KCustomOp | KNumLit.
```

The infrastructure supporting instantiation:

- `eqb_IntKind_spec`: decidable equality — proven by exhaustive case split (8 × 8 constructors)
- `all_IntKinds_complete`: every kind returned by `classify` is in `all_IntKinds`
- `all_IntKinds_nodup`: `NoDup all_IntKinds` — proven by `repeat constructor; intuition discriminate`

These three properties hold for any Rust `enum` type, since:
1. Rust enums have finitely many constructors
2. Pattern matching is exhaustive and deterministic
3. Constructor names are unique

### Summary Table

| Area | Name | Core Theorem | Instantiation | What's Preserved |
|------|------|-------------|---------------|------------------|
| 1 | Subterm Extraction | R1 | `area1_subterm_extraction` | Set of subterms added to target category |
| 2 | Auto-Variant Congruence | R1 | `area2_auto_variant_lam_congruence` | Set of lam fields fed to rw_cat |
| 3 | Equation Congruence | R3 | `area3_equation_congruence` | Set of paired fields checked for equality |
| 4 | Explicit Rewrite Congruence | V4 | `area4_explicit_congruence_extraction` | Set of (field, vi) pairs for rebuild |
| 5 | Fold Triggers | R2 | `area5_fold_triggers` | Set of terms triggering fold evaluation |
| 6 | Fold Identities | R2 | `area6_fold_identities` | Set of terms receiving identity folds |

### Area 1: Subterm Extraction

- **Original:** N rules, one per constructor. Each rule fires when its `if let` matches, extracting fields of the target category.
- **Consolidated:** 1 rule per (source_cat, target_cat) pair. A single `match` extracts all relevant subterms.
- **Instantiation:** T = Int, K = IntKind, V = Int. `classify` = constructor kind of Int terms. `extract` = subterm extraction per constructor.
- **Proof:** Direct instance of R1:

```coq
Theorem area1_subterm_extraction :
  forall (t : Int),
    all_rules Int IntKind Int classify_int extract_int all_IntKinds eqb_IntKind t
    ≡ₘ
    consolidated_extract Int IntKind Int classify_int extract_int t.
Proof.
  apply for_match_equiv.
  - exact eqb_IntKind_spec.
  - exact classify_complete.
  - exact all_IntKinds_nodup.
Qed.
```

- **Rocq:** `area1_subterm_extraction` in `AreaProofs.v`
- **proptest:** `prop_subterm_extraction_equiv`

### Area 2: Auto-Variant Congruence

- **Original:** 2C rules (Apply + MApply per domain). Each extracts the lam field.
- **Consolidated:** 1 rule extracts lam from all Apply/MApply variants.
- **Instantiation:** T = source category type, K = AutoKind (one per Apply/MApply variant), V = T (lam field type). Uses a separate `eqb_AK_spec`, `all_AK_complete`, `all_AK_nodup` for the auto-variant kind type.
- **Proof:** Instance of R1 with auto-variant kind type.

```coq
Theorem area2_auto_variant_lam_congruence :
  forall (t : T),
    all_rules T AutoKind T classify_auto extract_lam all_auto_kinds eqb_AK t
    ≡ₘ
    consolidated_extract T AutoKind T classify_auto extract_lam t.
Proof.
  apply for_match_equiv.
  - exact eqb_AK_spec.
  - exact all_AK_complete.
  - exact all_AK_nodup.
Qed.
```

- **Rocq:** `area2_auto_variant_lam_congruence` in `AreaProofs.v`
- **Note:** Area 2 also uses R1+V4 for the rebuild side (the variant index identifies which Apply/MApply variant to reconstruct).

### Area 3: Equation Congruence

- **Original:** N rules per constructor. Each matches (s, t) with the same constructor and checks per-field equality.
- **Consolidated:** 1 rule per field-type signature. `match (s, t)` extracts paired fields.
- **Instantiation:** T = Int, K = IntKind, V = (Int × Int) (paired field values). `classify` = constructor kind. `extract_pair` = corresponding field pairs.
- **Proof:** Direct instance of R3:

```coq
Theorem area3_equation_congruence :
  forall (s t : Int),
    original_pair_rules Int IntKind (Int * Int) classify_int
      extract_pair_int all_IntKinds eqb_IntKind s t
    ≡ₘ
    pair_match_extract Int IntKind (Int * Int) classify_int
      extract_pair_int eqb_IntKind s t.
Proof.
  apply pair_match_equiv.
  - exact eqb_IntKind_spec.
  - exact classify_complete.
  - exact all_IntKinds_nodup.
Qed.
```

- **Rocq:** `area3_equation_congruence` in `AreaProofs.v`
- **proptest:** `prop_pair_match_equiv`

### Area 4: Explicit Rewrite Congruence

- **Original:** N rules (one per constructor × field). Each extracts one field, checks rewrite, rebuilds.
- **Consolidated:** 1 rule per (source_cat, field_cat). Variant indices identify which field to rebuild.
- **Instantiation:** T = Int, K = IntKind, V = Int (field value type). Additional parameters: `vi_extract_int`, `vi_rebuild_int`, `extract_fields_int`, `vi_of_int`, `num_fields_int`, plus hypotheses for V1-V3 and the vi_extract specification.
- **Proof (extraction):** Direct instance of V4. **Proof (rebuild corollary):** `Permutation_map` over the extraction equivalence.

```coq
Theorem area4_explicit_congruence_extraction :
  forall (t : Int),
    original_vi_extract Int IntKind Int classify_int eqb_IntKind
      all_IntKinds extract_fields_int vi_of_int num_fields_int t
    ≡ₘ
    vi_extract_int t.
Proof.
  apply variant_index_extract_equiv.
  - exact eqb_IntKind_spec.
  - exact classify_complete.
  - exact all_IntKinds_nodup.
  - exact vi_extract_int_spec.
  - exact vi_extract_int_none.
Qed.

Corollary area4_explicit_congruence :
  forall (t : Int) (rw : Int -> Int),
    map (fun '(v, vi) => (t, vi_rebuild_int t vi (rw v)))
        (original_vi_extract ...) ≡ₘ
    map (fun '(v, vi) => (t, vi_rebuild_int t vi (rw v)))
        (vi_extract_int t).
Proof.
  intros t rw. apply Permutation_map.
  apply area4_explicit_congruence_extraction.
Qed.
```

- **Rocq:** `area4_explicit_congruence_extraction`, `area4_explicit_congruence` in `AreaProofs.v`
- **proptest:** `prop_rebuild_roundtrip`, `prop_extraction_completeness`, `test_variant_index_injectivity`

### Area 5: Fold Triggers

- **Original:** N rules (one per fold-mode constructor). `rw_cat(s, t) <-- cat(s), if let Cat::FoldCtor(...) = s, fold_cat(s, t)`.
- **Consolidated:** 1 rule with `if (match s { ... => true, _ => false })`.
- **Instantiation:** T = Int, K = IntKind. `fold_trigger_kinds = [KNeg; KSub; KCustomOp]` — the constructors with fold-mode evaluation rules.
- **Proof:** Direct instance of R2:

```coq
Definition fold_trigger_kinds : list IntKind := [KNeg; KSub; KCustomOp].

Theorem area5_fold_triggers :
  forall (t : Int),
    (exists k, In k fold_trigger_kinds /\
               if_let_matches Int IntKind classify_int eqb_IntKind k t = true)
    <->
    match_predicate Int IntKind classify_int eqb_IntKind fold_trigger_kinds t = true.
Proof.
  apply (if_match_equiv Int IntKind classify_int eqb_IntKind).
Qed.
```

- **Rocq:** `area5_fold_triggers`, `area5_fold_triggers_bool` in `AreaProofs.v`
- **proptest:** `prop_fold_trigger_equiv`

### Area 6: Fold Identities

- **Original:** N rules (one per non-fold constructor). `fold_cat(t, t) <-- cat(t), if let Cat::NonFold(..) = t`.
- **Consolidated:** 1 rule with `if (match t { ... => true, _ => false })`.
- **Instantiation:** T = Int, K = IntKind. `fold_identity_kinds = [KAdd; KPow; KFact; KTern; KNumLit]` — the constructors that are NOT fold-mode (i.e., they keep their value under fold evaluation).
- **Proof:** Direct instance of R2, identical structure to Area 5 with `fold_identity_kinds` instead of `fold_trigger_kinds`:

```coq
Definition fold_identity_kinds : list IntKind :=
  [KAdd; KPow; KFact; KTern; KNumLit].

Theorem area6_fold_identities :
  forall (t : Int),
    (exists k, In k fold_identity_kinds /\
               if_let_matches Int IntKind classify_int eqb_IntKind k t = true)
    <->
    match_predicate Int IntKind classify_int eqb_IntKind fold_identity_kinds t = true.
Proof.
  apply (if_match_equiv Int IntKind classify_int eqb_IntKind).
Qed.
```

- **Rocq:** `area6_fold_identities`, `area6_fold_identities_bool` in `AreaProofs.v`

---

## 7. Fixpoint Equivalence

The Datalog program computes a fixpoint via the **immediate consequence operator** T_P: given a database state I, T_P(I) adds all facts derivable by one application of any rule. The fixpoint is the least I such that T_P(I) = I.

Since each consolidated rule derives exactly the same facts as the original N rules it replaces (proven above for all 6 areas), the immediate consequence operator is unchanged:

    T_P_consolidated(I) = T_P_original(I)  for all I

**Formal statement:** Let P_orig be the original Datalog program with N per-constructor rules, and P_cons be the consolidated program. For any database state I:

    T_{P_cons}(I) = T_{P_orig}(I)

Since T_P is a monotone operator on a complete lattice (the power set of ground atoms), both programs have the same least fixpoint by the Knaster-Tarski theorem. Therefore the consolidated program computes the same result as the original.

This argument does not require a separate Rocq proof — it follows directly from the per-rule equivalence theorems (R1, R2, R3, V4) and the standard theory of Datalog fixpoints.

---

## 8. Verification Artifacts

| Artifact | Location | Status |
|----------|----------|--------|
| Rocq proofs (5 files) | `formal/rocq/rule_consolidation/theories/` | All compile, zero `Admitted` |
| proptest suite (9 tests) | `languages/tests/consolidation_tests.rs` | All pass |
| Full test suite (306+ tests) | `cargo test --workspace` | All pass |

For the complete theorem catalog, build instructions, and hypothesis audit, see [rocq-artifacts.md](rocq-artifacts.md).
