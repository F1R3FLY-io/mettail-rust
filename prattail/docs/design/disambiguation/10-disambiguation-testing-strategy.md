# Disambiguation Testing Strategy

## 1. Why Property-Based Testing

The integration of 11 analysis modules into disambiguation, recovery, and dispatch
generates a combinatorial explosion of input configurations. Manual test cases can
cover representative paths but cannot enumerate:

- Arbitrary category counts (1 to 20+)
- Arbitrary rules per category (0 to 10+)
- All combinations of syntax item types (Terminal, NonTerminal, IdentCapture,
  Binder, BinderCollection, Collection, Optional, Sep, Map, Zip)
- All feature gate combinations (default, `omega`, `symbolic-automata`,
  `probabilistic`, `register-automata`, `multi-tape`, `all-features`)

Property-based testing replaces manual enumeration with **invariant-based
verification**: generate arbitrary grammars via `proptest`, run the analysis,
and assert that mathematical invariants hold universally. A single property
replaces hundreds of hand-written examples.

## 2. Arbitrary Grammar Generation

The `arb_grammar` strategy (in `test_generators.rs`) produces syntactically valid
grammars with controlled complexity:

```
arb_grammar(num_cats: Range<usize>, rules_per_cat: Range<usize>)
  │
  ├─ Step 1: Sample num_cats category names (without replacement)
  │           from a fixed pool of 20 names
  │
  ├─ Step 2: For each category, generate rules_per_cat rules:
  │   ├─ Rule label: "<Category>::R<index>"
  │   ├─ Each rule has 1..5 syntax items drawn from:
  │   │   ├─ Terminal("x") / Terminal("+") / Terminal("(") / ...
  │   │   ├─ NonTerminal(<random category from this grammar>)
  │   │   ├─ IdentCapture
  │   │   ├─ Binder
  │   │   ├─ BinderCollection
  │   │   ├─ Collection(<random category>)
  │   │   └─ Optional { inner: <recursive item> }
  │   └─ First category always has is_primary: true
  │
  └─ Output: (Vec<CategoryInfo>, Vec<(String, String, Vec<SyntaxItemSpec>)>)
```

### Companion Generators

| Generator | Module | Purpose |
|-----------|--------|---------|
| `arb_small_grammar()` | `test_generators.rs` | 2--4 categories, 1--3 rules each |
| `arb_grammar(2..6, 1..4)` | `test_generators.rs` | General-purpose |
| `arb_category_name()` | `test_generators.rs` | Single valid category name |
| `arb_category_pair()` | `pipeline.rs` | Two distinct category names |
| `arb_category_names(min, max)` | `pipeline.rs` | Vec of distinct category names |
| `arb_category()` | `predicate_dispatch.rs` | Category name for dispatch tests |
| `arb_grammar_rule()` | `predicate_dispatch.rs` | Single (category, label, items) triple |
| `arb_grammar()` | `predicate_dispatch.rs` | Vec of grammar rules for dispatch |
| `arb_signature()` | `predicate_dispatch.rs` | Random `PredicateSignature` bitfield |

## 3. Property Catalog

The 60 proptest properties are organized by sprint. Each property asserts a
mathematical invariant that must hold for all generated inputs.

### Phase A Properties (pipeline.rs, recovery.rs)

| # | Sprint | Property Name | Mathematical Invariant | Module |
|---|--------|--------------|----------------------|--------|
| 1 | A3 | `prop_bisimilar_discount_lexicographic_second` | For bisimilar (C_a, C_b) with C_a < C_b: only C_b receives +0.5 penalty | pipeline.rs |
| 2 | A3 | `prop_non_bisimilar_no_discount` | All pairs in non_bisimilar_pairs receive 0 penalty | pipeline.rs |
| 3 | A3 | `prop_bisimilar_discount_is_0_5` | Penalty magnitude is exactly TropicalWeight(0.5) | pipeline.rs |
| 4 | A1 | `prop_depth_exceeds_ceiling_multiplier_below_one` | d > c implies skip multiplier in (0, 1) | recovery.rs |
| 5 | A1 | `prop_depth_within_ceiling_no_extra_factor` | d <= c implies skip multiplier = 1.0 | recovery.rs |
| 6 | A1 | `prop_ceiling_none_idempotent` | No ceiling implies multiplier = 1.0 for all depths | recovery.rs |
| 7 | A1 | `prop_ceiling_monotone` | Multiplier is non-increasing in depth beyond ceiling | recovery.rs |
| 8 | A2 | `prop_penalty_in_one_or_two` | Bracket penalty is in {1.0, 2.0} | recovery.rs |
| 9 | A2 | `prop_penalty_2_iff_in_set` | penalty = 2.0 iff token in bracket_mismatch_ids | recovery.rs |
| 10 | A2 | `prop_empty_mismatch_all_one` | Empty mismatch set implies all penalties = 1.0 | recovery.rs |
| 11 | A2 | `prop_superset_includes_subset_penalties` | B_1 subset B_2 implies penalties(B_2) >= penalties(B_1) pointwise | recovery.rs |
| 12 | C2 | `prop_recursive_flag_round_trip` | set_recursive(b); is_recursive() == b | recovery.rs |
| 13 | C2 | `prop_default_not_recursive` | Default RecoveryWfst has recursive_category = false | recovery.rs |
| 14 | C2 | `prop_recursive_insert_le_nonrecursive` | In recursive context, insert cost <= non-recursive insert cost | recovery.rs |
| 15 | C2 | `prop_recursive_skip_ge_nonrecursive` | In recursive context, skip cost >= non-recursive skip cost | recovery.rs |

### Phase B Properties

#### B1: Symbolic Guard Analysis (symbolic.rs)

| # | Property Name | Mathematical Invariant |
|---|--------------|----------------------|
| 16 | `prop_disjoint_terminals_no_overlap` | forall c in cats: (forall r_1, r_2 in rules(c): G(r_1) intersection G(r_2) = emptyset) implies overlapping_guards = emptyset |
| 17 | `prop_unsatisfiable_subset_all_rules` | unsatisfiable_guards subset rule_labels |
| 18 | `prop_terminal_start_always_satisfiable` | A rule starting with Terminal(t) is never unsatisfiable |
| 19 | `prop_nonterminal_start_always_satisfiable` | A rule starting with NonTerminal(C) is never unsatisfiable |
| 20 | `prop_overlap_only_within_category` | (r_1, r_2) in overlapping_guards implies category(r_1) = category(r_2) |
| 21 | `prop_subsumed_implies_strict_subset` | (r_sub, r_super) in subsumed_guards implies G(r_sub) proper-subset G(r_super) |
| 22 | `prop_guard_count_equals_rule_count` | |guards| = |rules| (every rule has a guard set) |

#### B2: Buchi SCC Analysis (buchi.rs)

| # | Property Name | Mathematical Invariant |
|---|--------------|----------------------|
| 23 | `prop_scc_names_are_category_names` | forall s in flatten(accepting_sccs): s in category_names |
| 24 | `prop_scc_sorted_within` | Each SCC is sorted lexicographically |
| 25 | `prop_scc_count_le_category_count` | |accepting_sccs| <= |categories| |
| 26 | `prop_accepting_scc_has_cycle` | forall S in accepting_sccs: |S| >= 2 or S has self-loop |
| 27 | `prop_no_self_ref_singleton_not_accepting` | Singleton without self-loop is not an accepting SCC |
| 28 | `prop_has_accepting_cycle_iff_nonempty_sccs` | has_accepting_cycle iff accepting_sccs is non-empty |
| 29 | `prop_num_states_equals_category_count` | num_states = |categories| |

#### B3: Probabilistic Entropy (probabilistic.rs)

| # | Property Name | Mathematical Invariant |
|---|--------------|----------------------|
| 30 | `prop_entropy_non_negative` | H(grammar) >= 0 |
| 31 | `prop_single_rule_selectivity_one` | Single-rule category: selectivity = 1.0 |
| 32 | `prop_simpler_rule_higher_weight` | |items(r_1)| < |items(r_2)| implies weight(r_1) > weight(r_2) |
| 33 | `prop_is_normalized_always_true` | analyze_from_bundle() always produces is_normalized = true |
| 34 | `prop_total_selectivity_positive` | For non-empty grammar: sum(selectivities) > 0 |
| 35 | `prop_rule_selectivities_count_equals_rules` | |rule_selectivities| = |rules| |
| 36 | `prop_uniform_rules_max_entropy` | n uniform rules: H = ln(n) (maximum entropy) |

#### B4: Register Dead Detection (register_automata.rs)

| # | Property Name | Mathematical Invariant |
|---|--------------|----------------------|
| 37 | `prop_dead_registers_subset_all` | dead_registers subset categories |
| 38 | `prop_dead_implies_store_no_test` | C in dead_registers implies has_store(C) and not has_test(C) |
| 39 | `prop_no_binders_no_dead` | No IdentCapture/Binder/BinderCollection items implies dead_registers = emptyset |
| 40 | `prop_referenced_category_not_dead` | NonTerminal(C) in some rule implies C not in dead_registers |
| 41 | `prop_num_registers_equals_categories` | |registers| = |categories| |

#### B5: Multi-Tape Independence (multi_tape.rs)

| # | Property Name | Mathematical Invariant |
|---|--------------|----------------------|
| 42 | `prop_disconnected_no_cross_references` | C in independent implies no NonTerminal references to C from other categories |
| 43 | `prop_connected_not_disconnected` | Categories in same connected component are not both independent |
| 44 | `prop_disconnected_subset_all_tapes` | independent_categories subset categories |
| 45 | `prop_all_terminal_all_disconnected` | Grammar with only Terminal items: all categories are independent |
| 46 | `prop_overlapping_tapes_subset_all` | overlapping_tapes pairs both in categories |
| 47 | `prop_disconnected_count_le_categories` | |independent_categories| <= |categories| |

### Phase C Properties

#### C1: Guard Disambiguation (pipeline.rs)

| # | Property Name | Mathematical Invariant |
|---|--------------|----------------------|
| 48 | `prop_disambiguated_subset_subsumed_labels` | guard_disambiguated_tokens subset { labels from subsumed_guards } |
| 49 | `prop_no_subsumption_no_disambiguation` | subsumed_guards = emptyset implies guard_disambiguated_tokens = emptyset |
| 50 | `prop_all_subsumed_all_disambiguated` | All labels in subsumed_guards appear in guard_disambiguated_tokens |

#### C3: Per-Category Entropy (pipeline.rs)

| # | Property Name | Mathematical Invariant |
|---|--------------|----------------------|
| 51 | `prop_entropy_non_negative_all` | forall (C, H) in per_category_entropy: H >= 0 |
| 52 | `prop_single_rule_zero_entropy` | Single-rule category: H(C) = 0 |
| 53 | `prop_uniform_max_entropy` | n uniform rules: H(C) = ln(n) |
| 54 | `prop_more_rules_higher_entropy` | More rules with equal weights implies higher entropy |

#### C4: Predicate Dispatch Ordering (predicate_dispatch.rs)

| # | Property Name | Mathematical Invariant |
|---|--------------|----------------------|
| 55 | `prop_specificity_preserves_all_labels` | order_by_specificity(L) is a permutation of L |
| 56 | `prop_no_subsumption_preserves_order` | Empty subsumed_guards preserves grammar order |
| 57 | `prop_subsumed_before_subsumer` | (r_sub, r_super) in subsumed implies index(r_sub) < index(r_super) |
| 58 | `prop_transitivity_ordering` | If r_1 subsumed r_2 subsumed r_3, then index(r_1) < index(r_2) < index(r_3) |
| 59 | `prop_specificity_score_monotone` | Specificity score is non-decreasing with subsumption count |

### Predicate Dispatch Module Properties (predicate_dispatch.rs)

| # | Property Name | Mathematical Invariant |
|---|--------------|----------------------|
| P1 | `prop_extract_always_includes_base` | extract(formula).raw() & BASE = BASE |
| P2 | `prop_extract_mso_always_includes_base` | extract_from_mso(formula).raw() & BASE = BASE |
| P3 | `prop_signature_union_idempotent` | s union s = s |
| P4 | `prop_signature_union_commutative` | a union b = b union a |
| P5 | `prop_signature_union_associative` | (a union b) union c = a union (b union c) |
| P6 | `prop_signature_count_is_popcount` | count() = popcount(raw()) |
| P7 | `prop_signature_contains_consistent` | contains(bit) iff raw() & bit != 0 |
| P8 | `prop_signature_set_monotonic` | s.set(bit); s.raw() >= old_raw |
| P9 | `prop_sfa_accepts_nonzero` | SFA accepts any non-zero signature |
| P10 | `prop_sfa_rejects_zero` | SFA rejects signature 0 |
| P11 | `prop_algebra_has_bit_eval` | evaluate(bit_pred, sigma_with_bit) = true |
| P12 | `prop_algebra_witness_satisfies` | witness(bit_pred) is Some and satisfies bit_pred |
| P13 | `prop_plan_requires_consistent` | plan_requires(sig) includes all set bits |
| P14 | `prop_extract_monotonic_and` | extract(a AND b) >= extract(a) union extract(b) (monotone) |
| P15 | `prop_signature_intersection_idempotent` | s intersection s = s |
| P16 | `prop_union_with_base_includes_base` | (s union BASE).raw() & BASE = BASE |
| P17 | `prop_classify_grammar_always_includes_base` | classify_grammar(g) & BASE = BASE |
| P18 | `prop_classify_grammar_monotonic` | More rules implies superset-or-equal signature |
| P19 | `prop_recursive_implies_buchi` | Self-recursive category implies M2 Buchi bit set |
| P20 | `prop_brackets_implies_vpa` | Bracket pairs implies M4 VPA bit set |
| P21 | `prop_binder_implies_register` | Binder items implies M6 Register bit set |
| P22 | `prop_ambiguity_implies_probabilistic` | Shared FIRST tokens implies M7 Probabilistic bit set |
| P23 | `prop_schedule_ordered_by_cost` | Schedule is sorted by ascending cost |
| P24 | `prop_classify_grammar_deterministic` | Two calls on same grammar give same result |
| P25 | `prop_grammar_superset_of_predicate` | Grammar signature >= individual predicate signature |
| P26 | `prop_fixpoint_activates_vpa_parity` | Fixpoint formula activates M4 + M5 |
| P27 | `prop_non_fixpoint_no_vpa` | Non-fixpoint, non-bracket formula does not require M4 |
| P28 | `prop_specificity_preserves_all_labels` | order_by_specificity output is a permutation |

**Total: 60 proptest properties** (15 Phase A + 29 Phase B + 9 Phase C + 7 Phase C4/P-series from predicate_dispatch)

## 4. Feature Gate Matrix

Properties are gated by the feature flags of their respective modules. The
table below shows which `--features` flag enables each property group.

```
                    default  omega  symbolic  probabilistic  register  multi-tape  all-features
                    ═══════  ═════  ════════  ═════════════  ════════  ══════════  ════════════
Phase A
  A1 (recovery)      x                                                               x
  A2 (recovery)      x                                                               x
  A3 (pipeline)                                                                      x

Phase B
  B1 (symbolic)                       x                                              x
  B2 (buchi)                  x                                                      x
  B3 (probabilistic)                             x                                   x
  B4 (register)                                              x                       x
  B5 (multi-tape)                                                        x           x

Phase C
  C1 (pipeline)                       x                                              x
  C2 (recovery)               x                                                      x
  C3 (pipeline)                                  x                                   x
  C4 (pred. dispatch)                 x                                              x

Predicate dispatch   ──────── always active (symbolic-automata is a dependency) ──────
```

### Running Tests by Feature

```bash
# Default features only (A1, A2 properties)
cargo test --workspace

# Individual module tests
cargo test --workspace --features symbolic-automata   # B1, C1, C4
cargo test --workspace --features omega               # B2, C2
cargo test --workspace --features probabilistic        # B3, C3
cargo test --workspace --features register-automata    # B4
cargo test --workspace --features multi-tape           # B5

# Full suite (all 60 properties)
cargo test --workspace --all-features
```

## 5. Edge Cases

Each sprint includes boundary conditions that test degenerate inputs.

### Empty Grammar

| Sprint | Edge Case | Expected Behavior |
|--------|-----------|-------------------|
| B1 | Zero rules | overlapping_guards = emptyset, subsumed_guards = emptyset |
| B2 | Zero categories | accepting_sccs = [], has_accepting_cycle = false |
| B3 | Zero rules | entropy = 0, rule_selectivities = [] |
| B4 | Zero rules | dead_registers = emptyset |
| B5 | Zero categories | independent_categories = [], overlapping_tapes = [] |
| C1 | No symbolic analysis | guard_disambiguated_tokens = emptyset |
| C3 | No probabilistic analysis | per_category_entropy = emptyset |

### Single Category

| Sprint | Edge Case | Expected Behavior |
|--------|-----------|-------------------|
| B1 | One rule in one category | No overlap possible, no subsumption |
| B2 | No self-loop | Not an accepting SCC (singleton, no cycle) |
| B2 | Self-loop | Accepting SCC of size 1 |
| B3 | One rule | selectivity = 1.0, entropy = 0.0 |
| B4 | Only Terminal items | dead_registers = emptyset |
| B5 | One category | independent (trivially) |
| C4 | One label | order_by_specificity returns [label] |

### Zero Ceiling / None

| Sprint | Edge Case | Expected Behavior |
|--------|-----------|-------------------|
| A1 | vpa_nesting_ceiling = None | No depth modulation, all depths neutral |
| A1 | vpa_nesting_ceiling = Some(0) | All non-zero depths exceed ceiling |
| A2 | bracket_mismatch_ids = emptyset | All insert penalties = 1.0 |
| C2 | recursive_scc_categories = emptyset | All categories non-recursive |

### Maximum Cardinality

| Sprint | Edge Case | Expected Behavior |
|--------|-----------|-------------------|
| B1 | All rules share one terminal | All pairs overlap |
| B2 | All categories mutually recursive | One accepting SCC of size |categories| |
| B3 | All rules identical length | Uniform weights, max entropy |
| B5 | Complete dependency graph | One connected component, no independent categories |
| C4 | Total order of subsumption | Output reverses the subsumption chain |

## 6. Test Isolation and Reproducibility

### proptest Configuration

All proptest blocks use a fixed case count to balance coverage with CI speed:

```rust
proptest! {
    #![proptest_config(ProptestConfig::with_cases(30))]
    // ...
}
```

This produces 30 random grammars per property per CI run. The `proptest-regressions`
files in each module's test directory capture any previously-failing seeds for
deterministic replay.

### Deterministic Helpers

In addition to property-based tests, each sprint includes deterministic unit tests
that pin specific known-interesting configurations:

| Sprint | Deterministic Tests | Purpose |
|--------|--------------------|---------|
| A1 | `test_vpa_nesting_depth_modulation` | Verify exact 0.3x multiplier |
| A2 | `test_vpa_bracket_mismatch_tokens_populated` | Verify dual-role bracket detection |
| B1 | `test_symbolic_overlapping_guards` | Two rules sharing "+" terminal |
| B2 | `test_buchi_mutual_recursion_scc` | Expr <-> Stmt mutual recursion |
| B3 | `test_probabilistic_structure_weights` | Verify 1/(1+len) formula |
| B4 | `test_register_dead_binder` | Binder without NonTerminal reference |
| B5 | `test_multi_tape_disconnected_categories` | Terminal-only categories |
| C1 | `guard_disambiguated_tokens_from_subsumption` | Subsumption populates guard set |
| C2 | `test_recursive_category_recovery_discount` | Verify 0.7x/1.3x modifiers |
| C3 | `per_category_entropy_two_rules` | Verify Shannon formula |
| C4 | `order_by_specificity_linear_chain` | Linear subsumption chain |

## 7. Composition Testing

Beyond individual sprint properties, three integration-level properties verify
cross-module composition:

| Property | Invariant | Modules Involved |
|----------|-----------|-----------------|
| `prop_disambiguated_subset_subsumed_labels` | C1 output is a subset of B1 output | B1 + C1 |
| `prop_recursive_insert_le_nonrecursive` | C2 modifier amplifies B2's SCC detection | B2 + C2 |
| `prop_more_rules_higher_entropy` | C3 entropy increases with B3's rule count | B3 + C3 |

These properties test the data-flow integrity of the Phase B -> Phase C pipeline:
enhanced analysis (B) must produce results that compose correctly with the
integration logic (C).

## 8. Cross-References

- **Architecture document**: [09-automata-disambiguation-integration.md](09-automata-disambiguation-integration.md)
- **Theory documents**: [../../theory/disambiguation/](../../theory/disambiguation/)
- **Test generators**: `prattail/src/test_generators.rs` (`arb_grammar`, `arb_small_grammar`)
- **Predicate dispatch generators**: `prattail/src/predicate_dispatch.rs` (`arb_category`, `arb_grammar`)
- **Grammar expression generators**: `prattail/src/grammar_gen.rs` (expression-level strategies)
- **Integration record**: [automata-disambiguation-integration.md](../../../docs/design/made/automata-disambiguation-integration.md)
