# Composition Semantics

**Date:** 2026-03-03

This document provides a formal treatment of merge-based grammar composition
in PraTTaIL.  It defines the merge operation M(A, B) on `LanguageDef` values,
establishes its algebraic properties, and states the invariants preserved by
merge.  For WFST-level composition theorems (union completeness, soundness,
weight preservation, dispatch determinism), see
[composition-correctness.md](composition-correctness.md).

---

## Table of Contents

1. [Definitions](#1-definitions)
2. [The Merge Operation](#2-the-merge-operation)
3. [Algebraic Properties](#3-algebraic-properties)
4. [Invariants Preserved by Merge](#4-invariants-preserved-by-merge)
5. [Strategy-Specific Semantics](#5-strategy-specific-semantics)
6. [Relation to WFST Composition](#6-relation-to-wfst-composition)
7. [References](#7-references)

---

## 1. Definitions

### 1.1 LanguageDef

A `LanguageDef` is a tuple L = (N, T, R, E, W, G, O) where:

- **N** = {(n, τ) | n is a category name, τ ∈ Option(RustType)} — named categories
  with optional native types
- **T** = {(l, c, s) | l is a label, c ∈ names(N), s is a syntax pattern} — term
  rules mapping labels to categories with syntax
- **E** = {(l, lhs, rhs) | l is a label, lhs and rhs are patterns} — equational
  axioms
- **W** = {(l, premise, lhs, rhs)} — rewrite rules with optional premises
- **G** = {(rel, params, content)} — logic (Ascent Datalog) relations and rules
- **O** = {(k, v)} — key-value option pairs

We write names(N) = {n | (n, τ) ∈ N} for the set of category names, and
labels(T) = {l | (l, c, s) ∈ T} for the set of term labels.

### 1.2 DuplicateStrategy

The merge operation is parameterized by a duplicate strategy σ ∈ {Error, Override}:

- **Error**: if labels(T_A) ∩ labels(T_B) ≠ ∅, the merge fails with
  `DuplicateRuleLabel` errors for each shared label.
- **Override**: for shared labels, B's definition replaces A's.  Formally,
  T_merged = (T_A \ {(l, c, s) ∈ T_A | l ∈ labels(T_B)}) ∪ T_B.

### 1.3 Composition Clauses

| Clause      | Strategy | Components Merged |
|-------------|----------|-------------------|
| `extends:`  | Error    | N, T, E, W, G, O  |
| `includes:` | Override | N, T only         |
| `mixins:`   | Override | N, T only         |

---

## 2. The Merge Operation

### 2.1 Definition

The merge operation M_σ : LanguageDef × LanguageDef → Result(LanguageDef, Error)
is defined componentwise.

**Category merge** (M_N):

    M_N(N_A, N_B) = N_A ∪ {(n, τ) ∈ N_B | n ∉ names(N_A)}

    Precondition: ∀ (n, τ_A) ∈ N_A, (n, τ_B) ∈ N_B : τ_A = τ_B
    (native type consistency; violation → CategoryNativeTypeMismatch error)

Categories from A appear first in the merged list; B categories are appended
in their original order, skipping names already present from A.

**Term merge** (M_T):

    M_T^Error(T_A, T_B)    = T_A ∪ T_B          if labels(T_A) ∩ labels(T_B) = ∅
                            = Error(shared)      otherwise

    M_T^Override(T_A, T_B) = {(l,c,s) ∈ T_A | l ∉ labels(T_B)} ∪ T_B

**Equation merge** (M_E): same as M_T with respective strategy.

**Rewrite merge** (M_W): same as M_T with respective strategy.

**Logic merge** (M_G):

    M_G(G_A, G_B):
      Relations unioned by name; conflicting parameter types → error.
      Rule content (TokenStream) concatenated.

**Option merge** (M_O):

    M_O(O_A, O_B) = O_A ∪ {(k, v) ∈ O_B | k ∉ keys(O_A)}

B's options fill in keys not present in A; A's values take precedence.

### 2.2 Full Merge

For `extends:` (σ = Error):

    M_Error(A, B) = (M_N(N_A, N_B), M_T^Error(T_A, T_B),
                     M_E^Error(E_A, E_B), M_W^Error(W_A, W_B),
                     M_G(G_A, G_B), M_O(O_A, O_B))

For `includes:` and `mixins:` (σ = Override):

    M_Override(A, B) = (M_N(N_A, N_B), M_T^Override(T_A, T_B),
                        E_B, W_B, G_B, O_B)

Note: equations (E_A), rewrites (W_A), and logic (G_A) from the base are
**discarded** under `includes:`/`mixins:`.  Only B's semantics survive.

---

## 3. Algebraic Properties

### 3.1 Non-Commutativity

**Theorem**: M_σ(A, B) ≠ M_σ(B, A) in general.

**Proof**: The primary category is determined by positional priority — the first
category with `is_primary = true` across A then B becomes primary in the merged
grammar.  If both A and B declare a primary category, M_σ(A, B) uses A's
primary while M_σ(B, A) uses B's primary.

Additionally, under Override strategy, M_T^Override(T_A, T_B) keeps B's
definitions for shared labels, while M_T^Override(T_B, T_A) keeps A's
definitions.  Since the kept definitions may differ, the results differ.

Concretely, let A define rule `Add: a "+" b : Int ![a + b]` and B define
`Add: a "+" b : Int ![a.wrapping_add(b)]`.  Then:

    M_Override(A, B) contains B's Add (wrapping)
    M_Override(B, A) contains A's Add (standard)

These produce different evaluation semantics.  ∎

### 3.2 Associativity under Error Strategy

**Theorem**: If all pairwise merges succeed, then
M_Error(M_Error(A, B), C) = M_Error(A, M_Error(B, C)).

**Proof sketch**: Under Error strategy, all shared labels cause failure.
If M_Error(A, B) succeeds, labels(T_A) ∩ labels(T_B) = ∅.  If
M_Error(AB, C) succeeds, (labels(T_A) ∪ labels(T_B)) ∩ labels(T_C) = ∅.
This implies labels(T_B) ∩ labels(T_C) = ∅ and labels(T_A) ∩ labels(T_C) = ∅,
so M_Error(B, C) and M_Error(A, BC) both succeed.

Category merge is associative because it is a name-prioritized union:
categories from A appear first regardless of grouping.  The positional
ordering of A < B < C categories is preserved under both groupings because
A's categories always precede B's, which always precede C's.

Term merge under Error is set union (since no overlaps exist), which is
associative.  Equations and rewrites follow the same argument.  Option merge
is first-writer-wins, which is associative when keys don't overlap across
all three grammars (guaranteed when Error succeeds at each step).  ∎

**Note**: Associativity does NOT hold under Override strategy in general,
because Override is last-writer-wins and the grouping determines which
writer is "last" for three-way overlaps.

### 3.3 Override is Last-Writer-Wins

**Theorem**: Under Override strategy, for any label l ∈ labels(T_A) ∩ labels(T_B),
M_T^Override(T_A, T_B) contains B's definition of l.

**Proof**: By definition, M_T^Override filters out A's rules with labels in
labels(T_B), then unions with all of T_B.  For label l present in both,
A's (l, c_A, s_A) is removed and B's (l, c_B, s_B) is included.  ∎

### 3.4 Identity Element

**Theorem**: The empty LanguageDef ε = (∅, ∅, ∅, ∅, ∅, ∅) is a right
identity for M_σ: M_σ(A, ε) = A for both strategies.

**Proof**: M_N(N_A, ∅) = N_A.  M_T^σ(T_A, ∅) = T_A (no overlaps, no
additions).  Similarly for E, W, G, O.  ∎

ε is also a left identity: M_σ(ε, A) = A (A's categories and rules are
appended to the empty set).

---

## 4. Invariants Preserved by Merge

The merge operation preserves the following invariants, which are required
by the downstream pipeline:

### 4.1 Category Name Uniqueness

**Invariant**: names(N_merged) has no duplicates.

**Proof**: M_N unions by name, skipping B categories whose names already
appear in A.  Since N_A has unique names (precondition of well-formed
LanguageDef) and B duplicates are skipped, the result has unique names.  ∎

### 4.2 Rule Label Uniqueness

**Invariant (Error)**: labels(T_merged) has no duplicates.

**Proof**: M_T^Error succeeds only when labels(T_A) ∩ labels(T_B) = ∅.
Since T_A and T_B individually have unique labels, the union has unique
labels.  ∎

**Invariant (Override)**: labels(T_merged) has no duplicates.

**Proof**: M_T^Override removes from T_A all rules whose labels appear in
T_B, then unions with T_B.  The resulting set has labels =
(labels(T_A) \ labels(T_B)) ∪ labels(T_B).  Since T_B has unique labels
and the subtracted set removes all conflicts from T_A, no duplicates
remain.  ∎

### 4.3 Native Type Consistency

**Invariant**: For all (n, τ) ∈ N_merged, τ is well-defined (no conflicts).

**Proof**: The precondition of M_N requires τ_A = τ_B for shared category
names.  Violation produces `CategoryNativeTypeMismatch` error and the merge
does not succeed.  ∎

### 4.4 Primary Category Uniqueness

**Invariant**: At most one category in N_merged has `is_primary = true`.

**Proof**: M_N uses a `seen_primary` sentinel.  The first category with
`is_primary = true` (scanning A first, then B) keeps the flag; all
subsequent primaries are demoted to `is_primary = false`.  ∎

---

## 5. Strategy-Specific Semantics

### 5.1 Error Strategy (`extends:`)

Error strategy enforces **strict additivity**: the extension can only add
new definitions, never shadow existing ones.  This is the strongest
guarantee — the merged grammar's behavior for any input accepted by A is
identical to A's behavior for that input, because all of A's rules,
equations, and rewrites are preserved unchanged.

**Monotonicity**: If A parses input I to term t, then M_Error(A, B) also
parses I to t (assuming the merge succeeds).  New rules from B can only
accept additional inputs, never change existing parses.

### 5.2 Override Strategy (`includes:`, `mixins:`)

Override strategy enables **selective replacement**: the consuming language
can redefine rules from the source.  This trades monotonicity for
flexibility — a redefined rule may produce a different AST or have
different evaluation semantics.

**Semantic independence**: Since equations, rewrites, and logic from the
source are discarded, the consuming language has full control over
operational semantics.  The source grammar contributes only syntax.

---

## 6. Relation to WFST Composition

The merge operation M_σ operates on `LanguageDef` (the raw, denormalized AST).
After merge, the result flows through `project_to_language_spec()` into the
PraTTaIL pipeline, where WFST construction, dead-rule detection, and codegen
occur.

The LanguageSpec-level `compose_languages()` function (`prattail/src/compose.rs`)
operates on already-classified specifications and performs a structurally similar
merge.  The formal theorems in [composition-correctness.md](composition-correctness.md)
apply to LanguageSpec-level composition:

- **Union completeness**: merged grammar accepts inputs from either source
- **Soundness**: merged grammar rejects inputs rejected by both sources
- **Weight preservation**: WFST weights from source grammars are maintained
- **Dispatch determinism**: dispatch tables are deterministic after merge

These properties hold for LanguageDef-level merge as well, because the merged
LanguageDef produces a LanguageSpec through the same pipeline that LanguageSpec
composition feeds into.

---

## 7. References

- `macros/src/ast/merge.rs` — Implementation of `merge_language_defs()`
- `prattail/src/compose.rs` — LanguageSpec-level composition
- [composition-correctness.md](composition-correctness.md) — WFST union
  completeness, soundness, and weight preservation theorems
- [../../usage/language/unification/00-overview.md](../../usage/language/unification/00-overview.md) —
  Pedagogical unification guide
- [../../design/wfst/grammar-composition.md](../../design/wfst/grammar-composition.md) —
  LanguageSpec composition design doc
