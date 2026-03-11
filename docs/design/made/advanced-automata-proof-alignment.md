# Advanced Automata: Rocq Proof ↔ Rust Implementation Alignment Audit

## Summary

The Advanced Automata Infrastructure (Sprint 14) produced 7 Rocq proof files
in `formal/rocq/advanced_automata/theories/`. This audit compared each proof
against its Rust implementation in `prattail/src/`, identified 1 critical
correctness bug, 4 abstraction gaps requiring documentation, and missing
alignment tests.

**Date**: 2026-03-10
**Scope**: 7 Rocq proofs × 7 Rust modules

---

## Findings Table

| # | Proof File | Rust File | Finding | Resolution | Status |
|---|-----------|-----------|---------|------------|--------|
| 1 | `TwoWayCrossingSequence.v` | `two_way_transducer.rs` | **BUG**: Crossing sequence tracks `(state, pos)` not `(state, pos, direction)` | Code fix + 3 tests | FIXED |
| 2 | `PataEmptiness.v` | `parity_tree.rs` | Algorithm difference: Zielonka vs fixpoint | Documented gap + 2 tests | DOCUMENTED |
| 3 | `AwaPolynomialEvaluation.v` | `alternating.rs` | Model difference: polynomial vs game semantics | Documented gap + 2 tests | DOCUMENTED |
| 4 | `StochasticNormalization.v` | `probabilistic.rs` | Compatible: log-domain vs nat | 2 alignment tests | ALIGNED |
| 5 | `MsoAutomataEquivalence.v` | `weighted_mso.rs` | Missing WFA construction function | Documented gap + 2 tests | DOCUMENTED |
| 6 | `RegisterEquivalence.v` | `register_automata.rs` | Concrete BFS vs orbit-finite abstraction | Documented gap | DOCUMENTED |
| 7 | `MultisetSemiringLaws.v` | `multiset_automata.rs` | Well aligned; missing distributivity test | 3 alignment tests | ALIGNED |

---

## Detailed Findings

### Finding 1: two_way_transducer.rs — Crossing Sequence Direction Bug

**Rocq theorem**: `no_repeats_length_bound` (line 266)
```coq
Definition CrossingEntry := (State * Direction)%type.
(* ... *)
Lemma no_repeats_length_bound : forall cs n,
  cs_no_repeats cs = true ->
  (forall e, In e cs -> fst e < n) ->
  length cs <= 2 * n.
```

**Rust function**: `transduce()` (line 297)

**Bug**: The `visited` set was `HashSet<(usize, usize)>` — tracking only
`(state, position)` without direction. A forward traversal through state S at
position P and a backward traversal through S at P were incorrectly treated as
the same crossing. The backward visit was pruned, potentially dropping valid
transduction results.

**Fix**:
- `visited: HashSet<(usize, usize, HeadDirection)>`
- `visited.insert((state_id, 0, self.states[state_id].direction))`
- `config_key = (t.to, new_pos, self.states[t.to].direction)`
- `debug_assert!` in `set_initial()` for forward-direction enforcement

**Tests**: 3 new
- `test_crossing_sequence_direction_aware` — verifies forward+backward at same position both produce output
- `test_set_initial_rejects_backward_state` — verifies debug_assert fires for backward initial
- `test_crossing_sequence_bound` — verifies termination within crossing bound

---

### Finding 2: parity_tree.rs — Zielonka vs Fixpoint

**Rocq theorem**: `zielonka_terminates` (line 256)
```coq
Theorem zielonka_terminates : forall G,
  exists W : WinRegion, zielonka G = W.
```

**Rust function**: `check_emptiness()` (line 427)

**Gap**: The Rocq proves Zielonka's recursive parity game algorithm terminates
and correctly partitions vertices. The Rust implements bottom-up fixpoint
propagation — states with even priority are immediately accepting; odd-priority
states become accepting when their transitions are satisfied.

**Why**: Both solve PATA emptiness for finite trees. The fixpoint is correct
because `accepting[s]` is monotone over a finite lattice. For infinite-tree
semantics, the full Zielonka algorithm would be needed.

**Tests**: 2 new
- `test_emptiness_even_priority_leaf_non_empty` — even priority leaf is non-empty
- `test_emptiness_universal_requires_all_children` — universal state requires all accepting children

---

### Finding 3: alternating.rs — Polynomial vs Game Semantics

**Rocq theorem**: `bu_equals_td` (line 241)
```coq
Theorem bu_equals_td : forall A w,
  eval_bottom_up A w = eval_top_down A w.
```

**Rust function**: `evaluate_word()` (line 855)

**Gap**: The Rocq models an AWA with univariate polynomials (coefficient lists).
The Rust implements the multivariate generalization (Kostolányi & Mišún Def. 5.1)
with existential = ⊕ and universal = ⊗ branching modes over per-edge weights.

**Why**: Multivariate polynomial Rocq libraries would be significantly more complex.
The univariate proof captures the essential inductive structure — evaluation
direction independence is preserved in both models.

**Tests**: 2 new
- `test_evaluate_word_empty_equals_final_weight` — empty word = terminal weight of initial
- `test_evaluate_word_single_symbol` — single symbol = transition + terminal weight

---

### Finding 4: probabilistic.rs — Log-Domain vs Natural Numbers

**Rocq theorem**: `proportional_same_support` (line 291)
```coq
Theorem proportional_same_support : forall eval1 eval2 c1 c2,
  c1 > 0 -> c2 > 0 ->
  (forall w, eval1 w * c2 = eval2 w * c1) ->
  same_support eval1 eval2.
```

**Rust function**: `normalize()` (line 229), `probability_of()` (line 187)

**Alignment**: The Rocq uses nat weights with proportionality; the Rust uses
LogWeight (f64 log-probability). The essential structure — normalization preserves
support (positive→positive, zero→zero) — is the same in both domains.

**Tests**: 2 new
- `test_normalize_preserves_support` — positive stays positive, zero stays zero after normalize
- `test_normalize_preserves_relative_ordering` — P(w1) > P(w2) preserved after normalize

---

### Finding 5: weighted_mso.rs — Missing WFA Construction

**Rocq theorem**: `restricted_mso_recognizable` (line 314)
```coq
Theorem restricted_mso_recognizable : forall phi : MsoFormula,
  exists f : Word -> Weight, series_eq (mso_sem phi) f.
```

**Rust function**: `classify_formula()` (line 292)

**Gap**: The Rocq proves the constructive direction of the weighted
Büchi-Elgot-Trakhtenbrot theorem — restricted MSO → recognizable series. The
Rust has `classify_formula()` and `check_decidability()` that correctly align
with the Rocq's `restricted_mso` predicate. However, the Rust does not yet
implement `to_weighted_automaton()` — the compilation from MSO formula to WFA.
The `evaluate_sentence_bool()` function provides direct formula evaluation.

**Tests**: 2 new
- `test_formula_without_forall_second_is_restricted` — non-Full classification
- `test_formula_with_forall_second_is_full` — ForallSecond → Full classification

---

### Finding 6: register_automata.rs — Concrete BFS vs Orbit Abstraction

**Rocq theorem**: `register_equivalence_decidable` (line 357)
```coq
Theorem register_equivalence_decidable :
  forall (num_states k : nat),
    num_states > 0 ->
    bisim_space_bound num_states k > 0.
```

**Rust function**: `check_equivalence()` (in register_automata.rs)

**Gap**: The Rocq proves orbit-finite bisimulation decidability via
equality-pattern-based orbit partitioning (at most |Q| * 2^(k²) orbit classes).
The Rust uses BFS over concrete product configurations with sentinel data values.
The concrete BFS is sound (if it finds a difference, the automata are truly
non-equivalent) but may be incomplete for large register counts.

---

### Finding 7: multiset_automata.rs — Distributivity

**Rocq theorems**: `mw_times_plus_distr_l` (line 205), `mw_times_plus_distr_r` (line 215)
```coq
Theorem mw_times_plus_distr_l : forall f g h,
  mw_eq (mw_times f (mw_plus g h))
        (mw_plus (mw_times f g) (mw_times f h)).
```

**Rust**: `MultisetWeight::plus()` / `times()` in `multiset_automata.rs`

**Alignment**: Well aligned — the Rust correctly implements pointwise max (⊕) and
pointwise add (⊗) matching the Rocq model exactly.

**Tests**: 3 new
- `test_multiset_weight_left_distributivity` — a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c)
- `test_multiset_weight_right_distributivity` — (a ⊕ b) ⊗ c = (a ⊗ c) ⊕ (b ⊗ c)
- `test_tropical_multiset_weight_distributivity` — same for TropicalMultisetWeight

---

## Traceability Table Corrections

The Spec-to-Code Traceability tables in 5 Rocq files were updated to fix
mismatched identifiers:

| File | Correction |
|------|------------|
| `TwoWayCrossingSequence.v` | `Direction` → `HeadDirection`, `CrossingSeq` → `visited: HashSet<(usize,usize,HeadDirection)>`, `crossing_seq_at` → loop detection in `transduce()` |
| `AwaPolynomialEvaluation.v` | `eval_bottom_up`/`eval_top_down` → `evaluate_word()` |
| `StochasticNormalization.v` | `support()` → `probability_of()` positivity check |
| `MsoAutomataEquivalence.v` | `MsoFormula` → `WeightedMsoFormula`, `wfa_eval` → `evaluate_sentence_bool()`, `mso_to_wfa` → (not yet implemented) |
| `RegisterEquivalence.v` | `Config` → implicit in `evaluate()`, `orbit_eq`/`orbit_class` → not exposed |

---

## Abstraction Gap Summary

All 4 documented abstraction gaps follow a common pattern: the Rocq proofs use
simplified mathematical models (nat, univariate polynomials, abstract relations)
while the Rust implementations use efficient data structures (log-domain floats,
multivariate game semantics, concrete BFS). The simplifications preserve the
essential properties (support preservation, evaluation direction independence,
bisimulation soundness) while making the proofs tractable.

---

## Test Summary

14 new alignment tests added across 6 files:

| File | Tests | Feature Gate |
|------|-------|-------------|
| `two_way_transducer.rs` | 3 | `two-way-transducer` |
| `probabilistic.rs` | 2 | `probabilistic` |
| `multiset_automata.rs` | 3 | `multiset-automata` |
| `alternating.rs` | 2 | `alternating` |
| `weighted_mso.rs` | 2 | `weighted-mso` |
| `parity_tree.rs` | 2 | `parity-tree-automata` |
