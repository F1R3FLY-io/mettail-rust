# Auto-Generated Test Framework for `language!` Specs

## Context

MeTTaIL's `language!` macro defines formal languages declaratively — types, terms (grammar rules with constructors, binding structure, HOL evaluation), equations (algebraic axioms), rewrites (reduction rules), and custom Ascent logic. The macro already generates exhaustive and random term generators, parsers, display, substitution, normalization, and Ascent datalog rules. However, testing is currently hand-written and incomplete: a single `roundtrip_tests.rs` for Calculator's `Int` category, plus scattered in-source prattail tests.

**Goal**: Make testing a first-class citizen by auto-generating comprehensive `#[test]` and `proptest!` tests from `language!` specs, leveraging the analytical layers (CESK, WPDS, confluence, etc.) for intelligent test generation and dead-code pruning. Tests integrate natively with `cargo test` and `cargo nextest run`.

**Design Principles**: Inspired by Clojure's `test.check` but going further — exhaustive where feasible, analytically guided, and fully integrated with the language specification rather than being a separate afterthought. Each language defined via `language!` automatically gets a complete, zero-effort test suite.

**Key Decisions**:
- **Cargo-native only**: All tests are `#[test]` / `proptest!` functions discoverable by `cargo test` and `cargo nextest run`. No standalone binary.
- **Library crate**: `testkit` is a reusable library providing property assertion functions, strategy helpers, and analytical integrations. Any crate using `language!` can depend on it.
- **Generated test files**: The `language!` macro writes `languages/tests/generated/{name}_tests.rs` as a side effect (same pattern as `*-datalog.rs` and `*-blocks.ts`). These are checked into version control.
- **TRS strictness**: Confluence and termination check failures default to hard errors. Configurable per-language via `options { }` to `error` (default), `warn`, or `disable`.
- **Parallelism + isolation**: `cargo nextest` provides per-test process isolation. Each test clears thread-local state (`clear_var_cache()`) and has no shared mutable state.

---

## Architecture Overview

Two layers:

```
┌─────────────────────────────────────────────────────┐
│  Generated test files (languages/tests/generated/)  │
│  #[test], proptest!, #[ignore] for dead rules       │
│  Discovered by cargo test / cargo nextest run       │
├─────────────────────────────────────────────────────┤
│  testkit crate (testkit/)                   │
│  Library: property assertions, strategy helpers,    │
│  analytical integrations (confluence, termination)  │
├─────────────────────────────────────────────────────┤
│  Macro layer (macros/src/gen/test_gen/)              │
│  Compile-time: generates proptest strategies,       │
│  #[test] functions, writes test files               │
└─────────────────────────────────────────────────────┘
```

---

## 1. New Crate: `testkit`

**Path**: `testkit/`

A pure library crate providing reusable property assertion functions and analytical test drivers. No binary, no test runner, no CLI — just functions that generated `#[test]` code calls.

### 1.1 Property Assertion Functions

#### Structural (`testkit/src/properties/structural.rs`)

```rust
/// Assert parse(display(term)).term_eq(term) — uses alpha-equivalence
pub fn assert_roundtrip<T: Display + Term + Parse>(term: &T) -> Result<(), TestCaseError> { ... }

/// Assert display(parse(display(term))) == display(term) — string equality
pub fn assert_display_idempotence<T: Display + Parse>(term: &T) -> Result<(), TestCaseError> { ... }

/// Assert parse(input) succeeds
pub fn assert_parses<T: Parse>(input: &str) -> Result<T, String> { ... }

/// Assert parse(input) fails
pub fn assert_parse_fails<T: Parse>(input: &str) -> Result<(), String> { ... }
```

#### Semantic (`testkit/src/properties/semantic.rs`)

```rust
/// Assert normalize(normalize(t)).term_eq(normalize(t))
pub fn assert_normalization_idempotence<T: Normalize + Term>(term: &T) -> Result<(), TestCaseError> { ... }

/// Assert eval(t) == eval(t) — deterministic evaluation
pub fn assert_eval_determinism(lang: &dyn Language, term: &dyn Term) -> Result<(), String> { ... }

/// Assert is_ground(t) => try_direct_eval(t).is_some()
pub fn assert_ground_eval_completeness(lang: &dyn Language, term: &dyn Term) -> Result<(), String> { ... }
```

#### Algebraic (`testkit/src/properties/algebraic.rs`)

```rust
/// Run Ascent on lhs, verify rhs in equivalence class (and vice versa)
pub fn assert_equation_symmetry(lang: &dyn Language, lhs: &str, rhs: &str) -> Result<(), String> { ... }

/// Run Ascent on term, verify at least one rewrite fires
pub fn assert_rewrite_fires(lang: &dyn Language, input: &str) -> Result<(), String> { ... }

/// Run Ascent, verify rewrite reaches expected result
pub fn assert_rewrites_to(lang: &dyn Language, input: &str, expected: &str) -> Result<(), String> { ... }

/// Verify term is in normal form (no rewrites apply)
pub fn assert_normal_form(lang: &dyn Language, input: &str) -> Result<(), String> { ... }

/// Verify eval(parse(input)) displays as expected
pub fn assert_evals_to(lang: &dyn Language, input: &str, expected: &str) -> Result<(), String> { ... }
```

### 1.2 Program Test Suite Builder (`testkit/src/program.rs`)

```rust
/// Builder for auto-generating tests for a program written in a MeTTaIL language.
pub struct ProgramTestSuite<'a> {
    language: &'a dyn Language,
    source: String,
    parsed: Option<Box<dyn Term>>,
}

impl<'a> ProgramTestSuite<'a> {
    pub fn new(language: &'a dyn Language) -> Self { ... }
    pub fn source(self, src: &str) -> Self { ... }

    // Structural
    pub fn expect_parses(self) -> Self { ... }
    pub fn expect_roundtrip(self) -> Self { ... }

    // Semantic
    pub fn expect_terminates(self, max_steps: usize) -> Self { ... }
    pub fn expect_normalizes_to(self, expected: &str) -> Self { ... }
    pub fn expect_rewrite(self, input: &str, expected: &str) -> Self { ... }

    // Concurrency (feature-gated)
    pub fn expect_no_deadlock(self) -> Self { ... }

    // Temporal (feature-gated)
    pub fn expect_ltl(self, formula: &str) -> Self { ... }

    // Property-based
    pub fn with_proptest<F>(self, cases: u32, property: F) -> Self
    where F: Fn(&dyn Term) -> Result<(), TestCaseError> + Send + Sync + 'static { ... }

    /// Run all configured tests. Returns Ok on all pass, Err with details on failure.
    pub fn run(self) -> Result<(), String> { ... }
}
```

### 1.3 Analytical Drivers

#### Confluence Checking (`testkit/src/analytical/confluence.rs`, feature-gated: `trs-analysis`)

```rust
/// Check confluence of rewrite rules. Returns critical pairs with joinability status.
pub fn check_language_confluence(metadata: &dyn LanguageMetadata) -> ConfluenceResult { ... }

pub struct ConfluenceResult {
    pub critical_pairs: Vec<CriticalPair>,
    pub all_joinable: bool,
}
```

Called from a generated `#[test]` function per language.

#### Termination Checking (`testkit/src/analytical/termination.rs`, feature-gated: `trs-analysis`)

```rust
/// Check termination of rewrite rules via dependency pairs.
pub fn check_language_termination(metadata: &dyn LanguageMetadata) -> TerminationResult { ... }
```

#### CESK State Coverage (`testkit/src/analytical/cesk_coverage.rs`, feature-gated: `cek-runtime`)

```rust
/// Build DSG and report reachable configuration coverage.
pub fn cesk_state_coverage(metadata: &dyn LanguageMetadata) -> CoverageReport { ... }
```

### 1.4 Strategy Helpers (`testkit/src/strategies.rs`)

Shared utilities used by the macro-generated `arb_strategy()` methods:

```rust
/// Strategy for generating fresh variable names
pub fn arb_var_name() -> impl Strategy<Value = String> { ... }

/// Strategy for native type values with interesting edge cases
pub fn arb_i32_interesting() -> impl Strategy<Value = i32> { ... }
pub fn arb_f64_interesting() -> impl Strategy<Value = f64> { ... }
pub fn arb_bool() -> impl Strategy<Value = bool> { ... }
pub fn arb_string_short() -> impl Strategy<Value = String> { ... }
```

### 1.5 Alpha-Equivalence Utilities (`testkit/src/alpha.rs`)

```rust
/// Assert two terms are alpha-equivalent (via moniker BoundTerm::term_eq)
pub fn assert_alpha_eq(left: &dyn Term, right: &dyn Term) -> Result<(), String> { ... }
```

---

## 2. Macro Layer: `macros/src/gen/test_gen/`

### 2.1 Module Structure

```
macros/src/gen/test_gen/
  mod.rs              — generate_test_file() entry point + write_test_file()
  strategies.rs       — Per-category proptest strategy generation (arb_strategy)
  unit_tests.rs       — Constructor roundtrip #[test] functions
  equation_tests.rs   — Equation-derived #[test] functions
  rewrite_tests.rs    — Rewrite-derived #[test] functions
  analytical_tests.rs — Confluence, termination, CESK #[test] functions
  user_tests.rs       — User-specified test codegen from tests { } block
  program_tests.rs    — Application-level program { } block codegen
```

### 2.2 Strategy Generation (`strategies.rs`)

For each category `Cat`, generate an `arb_strategy()` method emitted into the `language!` expansion:

```rust
impl Cat {
    pub fn arb_strategy(max_depth: u32) -> proptest::strategy::BoxedStrategy<Cat> {
        use proptest::prelude::*;
        let leaf = prop_oneof![
            // Native type literals (e.g., i32 for NumLit)
            mettail_testkit::strategies::arb_i32_interesting()
                .prop_map(|n| Cat::NumLit(n)),
            // Nullary constructors
            Just(Cat::PZero),
        ];
        leaf.prop_recursive(max_depth, 256, 4, |inner| {
            prop_oneof![
                // Binary constructors
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| Cat::AddInt(Box::new(a), Box::new(b))),
                // Binder constructors
                (mettail_testkit::strategies::arb_var_name(), inner.clone())
                    .prop_map(|(x, body)| Cat::Lam(/* Scope::new(...) */)),
                // Collection constructors
                proptest::collection::vec(inner.clone(), 0..4)
                    .prop_map(|elems| Cat::Par(elems)),
                // Cross-category references
                (OtherCat::arb_strategy(max_depth.saturating_sub(1)), inner.clone())
                    .prop_map(|(n, p)| Cat::Input(Box::new(n), Box::new(p))),
            ]
        }).boxed()
    }
}
```

Mirrors `macros/src/gen/term_gen/random.rs` structure but targets proptest's `Strategy` trait.

### 2.3 Generated Test File (`mod.rs` → `write_test_file()`)

The macro writes a complete Rust test file per language. Following the existing pattern of `write_ascent_source()` and `write_blockly_blocks()`:

```rust
pub fn write_test_file(language: &LanguageDef, pipeline: &PipelineAnalysis) {
    let test_code = generate_test_file(language, pipeline);
    let path = format!("tests/generated/{}_tests.rs", language.name.to_string().to_lowercase());
    // Write file (same mechanism as write_ascent_source)
}
```

The generated file contains:

1. **Unit tests** — one `#[test]` per constructor (roundtrip with concrete values)
2. **Equation tests** — one `#[test]` per equation (symmetry via Ascent)
3. **Rewrite tests** — one `#[test]` per rewrite rule (fires + result matches)
4. **Property tests** — `proptest!` block per category (roundtrip, display idempotence, normalization idempotence, eval determinism, ground eval completeness)
5. **Analytical tests** — `#[test]` for confluence check, termination check (feature-gated via `#[cfg(feature = "...")]`; behavior controlled by `options { confluence_check, termination_check, egraph_joinability }`)
6. **User tests** — `#[test]` per spec-level entry in `tests { }` block
7. **Program tests** — `mod program_{name} { }` per `program { }` entry in `tests { }` block (structural, semantic, rewrite, concurrency, temporal tests)
8. **Dead-rule tests** — annotated with `#[ignore = "dead rule per WFST analysis (Tier N: reason)"]`

### 2.4 Unit Test Generation (`unit_tests.rs`)

For each constructor in `terms`:
- Constructs a concrete instance using small representative values
- Displays, parses, asserts alpha-equivalence via `mettail_testkit::assert_roundtrip()`
- Nullary: just construct and roundtrip
- Native types: use representative values (0, 1, -1, 42)
- Binder constructors: use named variables ("x", "y"), verify alpha-eq
- Dead rules: emit with `#[ignore]`

#### Sole collection carriers and bag frames

A sole collection field retains its declared element category and carrier semantics.
The flatten helper accepts the constructor's own category as its element type.
The generator therefore emits and calls this helper only for a matching element category and a supported multiset carrier.
Other element categories use direct insertion.
A sole set field uses `HashSetLit`, which provides the traits required by the generated syntax tree.

A bag stores one entry per distinct value and a multiplicity for that entry.
The fused normalization frame reserves one result slot per stored entry with `distinct_len()`.
The visit loop fills those slots, and assembly restores each entry's multiplicity.
Using `len()` reserved extra slots when a value repeated, which caused the assembly cursor check to fail.
Sequences retain `len()` because each sequence position has its own result slot.

The models are [BinderFloatCanonicalization](../../formal/rocq/rho_bridge/theories/BinderFloatCanonicalization.v) and [TaggedNormalizationMachine](../../formal/rocq/runtime_grammar/theories/TaggedNormalizationMachine.v).
Their implementation checks use the existing generator tests and the compiled collection fixture.

| Model invariant | Implementation check |
|---|---|
| Helper calls have an emitted, well-typed helper | `flatten_helper_is_emitted_only_for_the_owner_element`, cross-category normalization checks, and `a_cross_category_bag_fold_fires` |
| Same-category helper behavior remains unchanged | `each_sole_carrier_keeps_its_own_semantics` and the nested-bag property |
| Direct insertion preserves atoms and bag flatness | `arbitrary_bags_keep_distinct_entries_and_multiplicities` checks exact normalized structure |
| Visits fill exactly the reserved result slots | `fused_bag_frames_reserve_one_slot_per_stored_entry` and both bag properties complete without assembly failure |
| Assembly preserves total multiplicity | Both bag properties compare the complete result or its repeated-element count |
| Bags without repeats retain their behavior | The arbitrary-bag property includes zero and one multiplicities |

The arbitrary-bag property varies distinct entries, multiplicities, empty bags, and nested bags.
A surrounding sequence also exercises frames after previously reserved result slots.
The existing repeated-element property checks display and parse readback for both same-category and cross-category bags.
The model retains the old repeated-element failure as a negative control.

Test-hosted language definitions do not need removed library feature flags.
For example, the InOutDemo report target uses `dovetail-codegen`, which supplies the report methods that its tests execute.

#### Election rank comparison

An election rank records lateness, weight, and an ordered sequence of decision events.
Each event contains a token position, nesting depth, and emission ordinal.
The comparator first checks lateness, then weight, then the decision sequence.
Packing index and child coordinates resolve remaining ties.

The decision projection sorts events by ascending position and descending depth.
Stable sorting preserves emission order when both coordinates match.
The comparator treats a missing ordinal as `u16::MAX`.
Thus, an empty sequence and a sequence containing only maximum ordinals compare equally.
Ordinary vector comparison would change this rule.

The heap previously called the strict comparison in both directions.
Each call could copy and sort both decision sequences.
The comparator now returns one `Ordering` and projects each operand at most once.
It retains the forward and reverse weight checks because generic weights need their existing selection rule.
No sorted projection survives the comparison.

```text
compare(left, right):
    if lateness differs: return lateness order
    if weights differ:
        if the forward weight choice selects left: return Less
        if the reverse weight choice selects right: return Greater
        return Equal
    project each event sequence once with stable sorting
    compare projected ordinals with maximum-ordinal padding
    return Equal if every padded ordinal agrees
```

The [occurrence model](../../formal/rocq/prattail_wpda_runtime/theories/SelectedOccurrencePlan.v)
contains the comparison proof in `ElectionComparisonReuse`.
The model parameterizes the padding value and uses enough fuel to examine both finite words.
The Rust comparator uses the maximum word length as that bound.
The proof preserves the existing projection and does not prove the standard library sorting implementation.

| Model invariant | Implementation property |
|---|---|
| `padded_ordinal_compare_reverse` and `one_ordinal_comparison_replaces_two_strict_tests` | `election_comparison_preserves_two_direction_order_and_projection_bound` checks both directions against an independent event-order oracle. |
| `rank_comparison_preserves_forward_then_reverse` | The same property varies lateness, weights, rules, signed zero, and infinite cost. |
| `equal_rank_keeps_packing_then_coordinates` and `unequal_rank_ignores_secondary_coordinates` | The same property checks complete candidate comparison with packing and coordinate ties. |
| `one_comparison_needs_at_most_two_projections` | A test-only counter checks zero projections before the ordinal stage and exactly two at that stage. |
| `padding_is_not_a_new_decision` and `trailing_padding_preserves_rank` | `election_comparison_preserves_stable_ties_and_maximum_padding` checks empty words and arbitrary trailing padding. |
| Stable projection preserves equal-coordinate emission order. | The padding property checks exact projection of arbitrary ordinals with identical position and depth. |

Both properties run 128 generated cases.
The reference projection sorts explicit encounter indices to provide an independent check of stable ties.

```sh
cargo test --locked --offline -p prattail --lib election_comparison
cd formal/rocq/prattail_wpda_runtime
coqc -Q theories PrattailWpdaRuntime theories/SelectedOccurrencePlan.v
coqchk -Q theories PrattailWpdaRuntime PrattailWpdaRuntime.SelectedOccurrencePlan
```

The application profile identified both vector assembly and repeated sorting costs.
This repair removes duplicate sorting only.
Application tests must establish completion separately from the local equivalence proof.

##### Typed unary publication

The full Regex application exposed an incompatible unary packing in the canonical parser.
The reduction published a completed `Proc` Symbol as the input of `CostSigGround`, which requires `Name`.
Every selected input then failed the generated action's downcast.
The extractor continued to enumerate descendants because the published parent still requested a result.
One descendant frontier contained 41,034 candidates with 209 coordinates each.

The full allocation trace used the temporary shared-sequence representation, which the repair removes.
The full allocation trace measured 31.95 GiB of resident memory before termination at the 32 GiB limit.
Semantic-key allocations held 17.28 GiB, and election allocations held 5.36 GiB.
Allocator metadata and alignment required at least 6.48 GiB across 439 million live allocations.
This accounting explains 97.18 percent of resident memory.
The remaining 0.90 GiB has no precise attribution.
These observations establish retained allocation growth, rather than a proof of a memory leak.

Semantic keys can have owners in both the cache and result indexes.
A complete smaller snapshot found approximately 377 MiB of key payload shared by those owners.
Only 50,176 bytes of key payload belonged exclusively to the cache in that snapshot.
This ownership result excludes cache management storage and does not describe ownership at the final memory peak.
Reducing the cache entry limit cannot release keys that result indexes still own.

The repair checks the existing action signature before D1 publication.
D1 denotes a frame that produces a fresh constituent without consuming an external left operand.
The check applies to `Return`, `RuleAt`, and `MixfixMarker` frames with committed, non-spine rules.
It reads the category of a direct completed Symbol without flattening an ambiguous spine.
It rejects only a concrete mismatch against exactly one declared unary input.
It preserves unknown metadata, wildcard inputs, structural bodies, other arities, and other frame classes.

```text
reduce(descriptor):
    if descriptor is an eligible D1 firing frame:
        actual = direct completed Symbol category, if available
        expected = concrete unary action input, if fully specified
        if actual and expected exist and differ:
            return success without publication
    execute the existing reduction
```

The check precedes seed statistics, forest allocation, recorded pops, and caller resumption.
An invalid attempt cannot create an accepting root or add a packing to an existing Symbol.
Valid attempts retain their original body identities, positions, weights, and publication order.
Explicit coercions remain grammar productions.
The check does not infer conversions from category reachability.

The [publication model](../../formal/rocq/prattail_wpda_runtime/theories/TypedUnaryPublication.v) defines the exact rejection certificate and publication boundary.
Its dynamic driver permits subsequent requests to depend on the complete current state.
Its finite execution index introduces no implementation limit.
The replay proof reuses the existing `PurePackingPreservation` edge/pop product and uniqueness theorems.
All 36 exported laws passed compilation, independent kernel checking, and assumption inspection before the Rust implementation changed.

Typed-value preservation requires truthful Symbol categories and actions that reject incompatible concrete inputs.
The generated downcast and owned-provider category checks establish the relevant implementation contracts.
The model does not establish those contracts for an arbitrary engine with false metadata.
The model also does not prove the complete Rust recognizer or extractor.

Election preservation uses an independently constructed typed reference forest.
It does not assert election parity with the malformed forest.
An invalid parent can otherwise set a shared descendant's first-demand depth and change equal-position decision ordering.
The property compares complete election observations and child demand against the typed reference.

The [walker properties](../../prattail/src/wpda_walker/typed_unary_publication_tests.rs) use the actual reduction, replay, and extraction paths.
Each property runs 96 generated cases.
The [provider property](../../macros/tests/support/owned_engine_parity.rs) runs 64 cases through the existing generated and owned actions.
The following mapping includes every exported model law.

| Model laws | Implementation property |
|---|---|
| `reject_exact_certificate`, `unary_input_exact_metadata`, `matching_input_is_not_rejected`, `mismatching_input_is_rejected`, `request_rejection_exact` | `typed_unary_publication_classifier_and_reduce_preserve_conservative_cases` checks declared categories and actual publication. |
| `unknown_metadata_is_not_rejected`, `unknown_body_is_not_rejected`, `uncertified_signature_is_not_rejected`, `wildcard_is_not_rejected` | The classifier property varies missing and malformed signatures, wildcard inputs, and structural body shapes. |
| `d2_is_ineligible`, `structural_pop_is_ineligible`, `spine_rule_is_ineligible`, `ineligible_request_is_unchanged` | The classifier property checks frame classes, firing kinds, and synthetic spine rules. |
| `unary_input_renamed`, `category_renaming_preserves_rejection` | The classifier property repeats fixtures with an injective category renaming that preserves the wildcard. |
| `certified_mismatch_rejects_every_typed_value`, `rejected_values_have_no_success`, `rejection_preserves_typed_successes` | `typed_unary_publication_generated_and_owned_input_contract` executes both action providers with matching and incompatible terms. |
| `publication_matches_typed_reference`, `rejected_publication_preserves_all_state`, `retained_publication_is_exact`, `retained_error_is_exact` | The classifier property checks state preservation. `typed_unary_publication_retains_exact_payload_and_errors` checks values, spans, costs, and actual resource/action errors. |
| `ordered_typed_reference`, `valid_siblings_are_retained`, `rejection_is_idempotent`, `dynamic_driver_is_a_typed_reference_run`, `dynamic_typed_reference_determines_exact_trace_and_state` | `typed_unary_publication_replay_preserves_valid_siblings` interleaves repeated invalid and valid attempts around caller creation and existing output Symbols. |
| `rejected_request_has_no_pop`, `retained_request_has_exact_pop`, `edge_operation_in_iff`, `pop_operation_in_iff`, `typed_replay_is_exact_edge_pop_product`, `typed_replay_resumes_each_pair_once`, `typed_replay_is_order_independent` | The replay property checks both creation orders, repeated operations, exact pop counts, and unique caller resumptions. |
| `typed_reference_preserves_election_observation`, `dynamic_typed_reference_preserves_election` | `typed_unary_publication_election_matches_typed_forest_without_invalid_demand` checks shared descendants, equal-position decisions, representative values, weights, and extraction counters. |

```sh
cargo test --locked --offline -p prattail --lib wpda_walker
cargo test --locked --offline -p macros --test owned_engine_parity
coqc -Q formal/rocq/prattail_wpda_runtime/theories PrattailWpdaRuntime formal/rocq/prattail_wpda_runtime/theories/TypedUnaryPublication.v
coqchk -Q formal/rocq/prattail_wpda_runtime/theories PrattailWpdaRuntime PrattailWpdaRuntime.TypedUnaryPublication
```

The unchanged application checks passed after this repair.
Both checks used release builds with the `lambda-runtime` and `calculator-runtime` features, a 32 GiB limit, and no swap.
Resident set size, abbreviated RSS, measures resident process pages.

| Application check | Passed tests | Test time | Peak process RSS |
|---|---:|---:|---:|
| Full `inline_ddl_demo` suite, including the complete Regex fixture | 8 | 1.26 seconds | 150.82 MiB |
| `practical_regex_gslt_application_contains_the_checked_declaration_and_parses_once` | 1 | 0.37 seconds | 126.32 MiB |

The inline suite previously stopped at the 32 GiB limit during its Regex check.
These successful runs retain the default cache capacity and the original `im::Vector` election storage.
The measurements therefore establish the effect of the typed publication repair without a cache-capacity reduction or the discarded storage experiment.

The `KBEST-STATE` diagnostic retains its logical counts and omits the former `seen_witness_bytes` estimate.
That estimate ignored retained key payloads, sharing, and container capacity.
Use allocation traces and process memory measurements for byte accounting.


#### Bounded semantic-key memoization

The parser uses exact semantic keys to group equivalent candidates and select representatives.
The cache avoids repeated key construction for the same immutable allocation.
Its identity combines the node type and memory address.
Equivalent nodes in separate allocations can therefore occupy separate entries.

The cache uses least-recently-used eviction, abbreviated LRU.
A valid hit becomes the most recent entry.
Insertion at capacity removes the least-recent entry, even when its syntax node remains live.
Node liveness never pins an entry.
A miss uses the existing generated or owned visitor to compute the same exact key.
Capacity zero disables retention without changing parsing results.

The default walker capacity is 1,048,576 entries.
`with_semantic_key_cache_entries` changes this retention capacity.
The separate default logical key-byte limit is 64 MiB per constructed key.
That limit applies to cached and uncached construction.
An entry count is not a complete heap-byte bound.
Shared key ropes and weak allocation witnesses have different physical costs from flattened key bytes.

The implementation uses `lru` 0.18.5 with the existing fast hasher.
It initializes storage without reserving every configured entry.
LRU replaces old observations with recent observations after saturation.
This policy is a practical baseline, not a proof of optimal performance for every grammar.

Each entry holds a weak owner witness.
A lookup must validate that witness before it accepts an address match.
An expired witness removes the entry and produces a miss.
Weak ownership permits the syntax value to be destroyed while the cache remains alive.
The weak allocation itself can remain allocated until its last weak reference is removed.
See the [Rust ownership contract](https://doc.rust-lang.org/std/sync/struct.Weak.html).

The current traversal retains its root strongly while it borrows descendants.
After the transaction ends, the cache does not retain that strong ownership.
A shared child can outlive the owner recorded by its entry.
That expired witness causes a conservative miss, and the existing visitor recomputes the key.
Returned keys own their representation and survive cache eviction or syntax-owner destruction.

One LRU table holds both committed and provisional entries.
A transaction-local set identifies surviving provisional entries.
Both entry populations share the configured capacity, and the marker count cannot exceed the entry count.
The exclusive mutable cache borrow prevents other callers from observing provisional entries.

```text
Lookup an identity.
    Remove an expired witness and report a miss.
    Promote a valid hit and return its exact key.
On a miss, compute the exact key with the existing visitor.
    Check construction limits and valid identity conflicts.
    If capacity is positive, insert the key and evict the LRU entry when necessary.
    Track surviving provisional identities only.
    Return the computed key at every cache capacity.
On commit, clear the provisional markers.
On abort, remove the surviving provisional entries.
```

An abort can leave earlier entries evicted or change their recency.
These optimization details do not require rollback.
An abort retains none of its surviving provisional entries.
Actual construction errors still prevent publication of parser candidates.
The cache-entry exhaustion error no longer exists.
Key-byte errors, invalid key construction, and valid identity conflicts remain distinct failures.

The formal model is [KbestCompositionalSemanticKey.v](../../formal/rocq/runtime_grammar/theories/KbestCompositionalSemanticKey.v).
[OwnedSemanticVisitor.v](../../formal/rocq/runtime_grammar/theories/OwnedSemanticVisitor.v) applies the construction boundary to the owned visitor.
The lifetime premise requires immutable ownership of each borrowed node.
Rust ownership and the weak-witness properties connect that premise to the implementation.

| Model laws | Implementation property or additional control |
|---|---|
| `eviction_preserves_soundness`, `admission_preserves_soundness`, `lookup_preserves_soundness` | `cache_transactions_follow_bounded_lru` checks generated histories against an independent recency sequence. Generated-key parity checks the returned bytes. |
| `admission_bounds_all_entries`, `zero_capacity_retains_nothing`, `admission_does_not_inspect_liveness` | The transaction property checks capacity after every operation while every syntax owner remains live. |
| `lookup_preserves_entry_bound`, `valid_hit_promotes_to_most_recent` | The transaction property compares the complete LRU order after hits, insertions, and evictions. |
| `valid_hit_returns_exact_stream`, `cache_capacity_cannot_change_key`, `arbitrary_eviction_preserves_observations` | `generated_exact_keys_are_independent_of_cache_capacity` compares the actual generated visitor with its original uncached stream. |
| `expired_owner_is_a_miss` | `expired_owners_and_shared_children_are_cache_misses` covers expired roots, shared live children, and an expired witness at a current identity. |
| `provisional_metadata_is_bounded`, `abort_removes_every_provisional_entry`, `abort_preserves_soundness`, `commit_keeps_entries_and_clears_markers` | The transaction property compares commit and abort histories. `real_key_failures_abort_provisional_entries` injects construction failures after live-entry eviction. |
| `construction_success_publishes_all_candidates`, `construction_failure_publishes_no_candidates` | `persistent_cache_capacity_preserves_class_representatives` compares complete class representatives. `key_construction_failure_never_publishes_a_candidate_prefix` checks the failure boundary with generated candidate streams. |
| `successful_key_construction_publishes_candidates`, `failed_key_construction_cannot_publish_candidates` | Generated/owned source parity runs at capacities zero, one, and 64. The installed Regex control distinguishes disabled retention from an actual key-byte failure. |
| `compose_key_exact`, `accelerator_composes`, `collision_safe_equal_iff_exact` | `persistent_composition_preserves_exact_stream_and_limits` compares composed keys with flat keys and their exact streams. |
| `accelerator_collision_cannot_merge` | The representative property also forces legacy digest collisions and compares every class with an independent exact-value oracle. |
| `empty_cache_sound`, `inserted_key_is_found`, `sound_cache_insert`, `cache_hit_returns_exact_stream` | The transaction property covers empty caches, insertion, valid hits, and recomputation after eviction. |
| `bounded_key_success_is_exact_and_within_limit`, `bounded_key_exhaustion_reports_exact_request`, `byte_exhaustion_exposes_no_partial_key` | The composition property checks exact bytes and the complete attempted key length. The failure property checks typed refusal and transaction cleanup. |
| `chain_restream_work_is_triangular`, `chain_compositional_work_is_linear`, `retained_cache_witnesses_are_linear` | `persistent_chain_shares_linear_local_storage` counts actual local bytes, shared child references, and byte visits when complete prefixes are read. |

The chain laws describe key representation costs, not total parser runtime or total heap use.
The capacity properties vary live allocations, repeated values, weights, commit decisions, abort decisions, and access order.
The representative property checks both realization paths, strict minimum weights, first-on-tie identity, and k-best provenance.
The generated property includes shared subtrees and separately allocated equivalent nodes.

Focused checks use the existing process memory limits:

```sh
cargo test --locked --offline -p mettail-semantic-key --lib
cargo test --locked --offline -p prattail --lib wpda_walker::tests::
cargo test --locked --offline -p prattail --lib wpda_owned::semantic_keys
cargo test --locked --offline -p prattail --test parse_error_lifecycle
cargo test --locked --offline -p macros --test owned_engine_parity
coqc -Q formal/rocq/runtime_grammar/theories RuntimeGrammar formal/rocq/runtime_grammar/theories/KbestCompositionalSemanticKey.v
coqc -Q formal/rocq/prattail_wpda_runtime/theories PrattailWpdaRuntime -Q formal/rocq/runtime_grammar/theories RuntimeGrammar formal/rocq/runtime_grammar/theories/OwnedSemanticVisitor.v
coqchk -silent -Q formal/rocq/prattail_wpda_runtime/theories PrattailWpdaRuntime -Q formal/rocq/runtime_grammar/theories RuntimeGrammar RuntimeGrammar.KbestCompositionalSemanticKey RuntimeGrammar.OwnedSemanticVisitor
```


#### Query request argument boundaries

The Rholang query expansion must preserve the same argument vector as an ordinary send.
Its private return channel is the first argument.
Each authored query argument then occupies one message field.
An explicit list remains one argument.

`languages/src/rholang/runtime.rs::mk_output` constructs the existing empty, monadic, or polyadic send variant from that vector.
The helper previously packed multiple arguments into one list-valued field.
That field could not match a responder with separate receive patterns.
The checked preparation path already schedules separate send arguments.
The repair makes the original expansion preserve those boundaries too.

The existing [surface-arity model](../../formal/rocq/rho_bridge/theories/RholangSurfaceArity.v) supplies the applicable laws.
`query_expansion_preserves_argument_boundaries` runs 64 cases for each declared query form.
Each case compares the complete encoded result with an explicit request-and-reply expansion.
The property also checks request and receive field counts directly.
Arguments include scalars and explicit lists, including requests with no authored arguments.

| Applicable model law | Implementation check |
|---|---|
| `surface_send_preserves_every_argument` | The property compares complete bytes and requires the return field plus every argument |
| `preparation_preserves_send_arity` | The property preserves argument boundaries through expansion and lowering |
| `preparation_does_not_pack_polyadic_arguments`, `explicit_list_send_is_not_polyadic` | Generated explicit-list arguments retain their own field boundaries |
| `surface_bind_preserves_every_pattern`, `zero_one_and_polyadic_arities_are_distinct` | The property checks empty, plain, and quoted reply patterns |

The existing query integration suite tests real replies, private return channels, nested receives, joins, and unanswered services.
The demo suite checks the shipped programs and their documented output.
The model's install-service laws concern the separate installation protocol and are unchanged by this helper repair.

#### Collections of data categories

A `data` category contains structural syntax without generic substitution or normalization semantics.
A collection of data values therefore forms one preserved payload in an object constructor.
The generated matcher compares that payload for exact structural equality.
An embedded object term inside the data payload does not become a substitution target or pattern variable.
Adjacent object fields still receive the requested semantic operation.

For example, `PMetas . ms:HashBag(Meta) |- "metas" "{" ms.*sep(",") "}" : Proc;` declares such a payload when `Meta` is `data`.
The declaration does not require a `VisitMeta` task or a `Meta::match_pattern` method.
The generator selects the existing data-category predicate before it emits collection traversal.
Normalization and substitution clone the declared carrier and preserve the constructor.
Matching compares the carriers directly.
Object-category collections retain their existing traversal and assembly paths.

This repair changes the sole-collection paths in `normalize.rs`, `subst.rs`, and `match_pattern.rs`.
The legacy multiple-field, binder-field, and nested-type `std::collections::HashSet` sites in `types/enums.rs` are separate paths.
The test-only `generate_collection_assemble_arm` oracle remains unchanged.

The [capability model](../../formal/rocq/runtime_grammar/theories/DataCategoryCapabilities.v) states this rule for an arbitrary carrier type.
The carrier parameter includes sequence order, bag multiplicity, and set membership.
The model uses the existing `semantic_field_plan` distinction between recursive object work and preserved data.

| Formal invariant | Implementation property in `collection_fold_carriers.rs` |
|---|---|
| `data_collection_preserves_exact_carrier` | `normalization_preserves_data_and_transforms_object_children` and `substitution_preserves_data_identity_and_composition` |
| `object_collection_keeps_recursive_transform` | The same properties require changes in adjacent object fields |
| `semantic_collection_map_identity` | Identity substitution preserves the complete constructor |
| `semantic_collection_map_composition` | Two substitutions compose while the data payload remains unchanged |
| `generic_semantics_cannot_cross_a_data_boundary` | `matching_compares_data_exactly_and_keeps_object_bindings` rejects a variable match inside data |
| `every_declared_field_edge_remains_structurally_traversable` | `all_data_carriers_parse_display_and_read_back` checks complete parsed structure |

The properties cover judgment and BNF declarations for bags, sets, and sequences.
The fixture includes empty collections, repeated values, distinct values, and data values that contain object terms.
The object controls distinguish preservation of a data payload from accidental omission of the parent traversal.

Run the focused suite with:

```sh
cargo test --locked -p languages --no-default-features --features walker-trace,dovetail-codegen --test collection_fold_carriers
```

#### Collection display and opener checks

Collection display preserves lexical boundaries around word delimiters.
For example, `bnames n, n end` must not print as `bnamesn, nend`.
The empty collection requires separation between `bnames` and `end` too.
The display generator uses the existing delimiter boundary policy for both cases.
Bracket delimiters retain their previous spacing.

`WpdaDispatchPartition.v` proves the boundary policy and the unchanged bracket case.
`delimited_collections_space_word_delimiters_from_their_items` checks the emitted boundary choices.
`word_delimited_collections_of_any_size_read_back` checks generated parser behavior for bags, sets, and sequences.
The collection integration suite also checks empty and nonempty examples.

A lexical fork must retain collection openers alongside ordinary readings.
The shared transition preserves each opener's rule, category, lexical target, weight, and required parenthesis.
The owned parser uses the same metadata and admits the standalone collection action.
The repair uses the existing transition and action classifier.

| Formal invariant | Implementation check |
|---|---|
| `LexForkKeywordReservation.CollectionOpenFork` retention, order, marker, edge, and parenthesis laws | `collection_routes_preserve_evidence` in `prattail/src/wpda_transitions/lexical_fork.rs` |
| Primary-only dispatch remains available | `sole_primary_collection_retains_normal_dispatch` |
| `OwnedCollectionAction` standalone input, carrier, and priority laws | Generated/owned parser parity in `macros/tests/prefix_opener_union.rs` |
| Cross-category fold syntax remains executable | `a_cross_category_bag_fold_fires` in `languages/tests/collection_fold_carriers.rs` |

The parity suite checks exact weighted readings, randomized collection inputs, ordinary fallback, and rejection of a missing required parenthesis.

#### Prefix operand display

A prefix constructor can return a different category from its operand.
For example, `Mark . body:Value |- "#" body : Envelope prefix(220);` parses its `Value` operand with threshold 220.
If that operand contains a weaker infix operation, display must group the complete operand.
Otherwise, `#z + z` leaves `+ z` outside the prefix operand and can fail to parse as `Envelope`.

The display lookup uses the parser's existing `CrossCatPrefixUnary` classifier.
It calls the same `compute_prefix_bp` function with the operand category and the declaration's optional threshold.
An explicit threshold takes priority.
Without an explicit threshold, the operand category determines the threshold.
The result category's operator levels do not determine this threshold.
Existing same-category prefix lookup remains unchanged.

`WpdaDispatchPartition.v`, section `CrossCategoryPrefixDisplay`, proves the threshold and grouping obligations.
The model describes the binding-power boundary rather than the complete parser.
Compiled roundtrip properties check the connection to emitted display code and actual parser behavior.

| Formal invariant | Implementation property |
|---|---|
| Display and parser use the same operand threshold | `cross_category_prefix_uses_source_binding_power` |
| Explicit thresholds retain their declared value | The same property varies the optional threshold across the byte domain |
| Default thresholds use the source category | The same property varies source and result operator counts independently |
| Same-category prefixes retain their threshold | The same property checks a local prefix beside the foreign prefix |
| Grouping preserves an operand that would escape its prefix | `foreign_prefix_roundtrips_infix_operands` constructs mixed infix trees and compares the complete parsed value |
| A missing threshold can lose an infix tail | The model's counterexample and the recorded failing integration run precede the repair |

The integration fixture uses both an explicit `#` prefix and an inferred `tag` prefix.
It uses the generator's transparent grouping, so the property can compare complete syntax trees without an extra authored grouping constructor.
It contains no Rholang or F1r3lang syntax.

#### Adjacent frame operands

The projection frame matcher must separate adjacent operands without a delimiter between them.
For example, `(pair {} {})` contains two complete operands before the final parenthesis.
The old matcher scanned forward to that parenthesis and assigned the full region to the first operand.
The second operand then had no input.
The independent `AdjacentFrames` fixture reproduces this failure while the existing main parser accepts the same source.

The repair extends the existing matcher and source layout.
The lexer graph supplies token starts and ends as byte offsets.
The source layout stores those offsets in sorted order without duplicates and checks each UTF-8 boundary.
When the next slot is another operand, the matcher tries each token boundary within the remaining span.
Each choice continues through the existing skeleton matcher, operand parser, and reading selection.
Literal-delimited operands retain their existing matching path.

The matcher does not split at arbitrary character positions.
For example, `(pair zz)` cannot become two operands when the lexer supplies one identifier token.
Quoted text remains one token even when the text contains spaces or brackets.
A repeated operand can be empty, so a boundary at the current position remains a valid candidate.
The existing operand parser determines whether that empty span satisfies the declared field.

`ProjectionIsolation.v`, section `AdjacentOperandBoundaries`, models ordered candidate splits over supplied lexer boundaries.
Its eight laws prove candidate coverage, source-boundary membership, range order, operand count, and empty-span support.
The model does not prove the lexer or the complete parser.
Compiled properties connect these obligations to the generated implementation.

| Formal invariant | Implementation property in `macros/tests/adjacent_frame_operands.rs` |
|---|---|
| Candidate cuts are exactly the supplied boundaries within the span | Complete nested-tree readback and rejection of splits inside one token |
| Enumeration retains every valid ordered split | `adjacent_operands_preserve_the_complete_tree` covers nested pairs and triples |
| Every split retains the declared operand count | The same property compares the complete syntax tree |
| Every cut comes from the source lexer | `adjacent_boundaries_never_split_one_token` varies identifiers and quoted text |
| Operand ranges remain in source order | Complete tree equality preserves each ordered field |
| An empty repeated operand remains admissible | `adjacent_lists_preserve_empty_and_nonempty_operands` always tests an empty list and varies nonempty lists |
| Interior cuts remain available before the final delimiter | Nested pairs and triples require those cuts |
| The old final-delimiter choice loses valid operands | The formal counterexample and the saved failing independent fixture precede the repair |

The Rholang integration controls also test substitution with variables, empty collections, and nested constructor applications.
Those controls compare failures with the existing main parser to separate frame matching from core parser defects.

#### Leading operand category goals

A rule can start with an operand from another category.
For example, `Application . head:Head, arguments:Vec(Value) |- head "(" arguments.*sep(",") ")" : Value;` starts with a `Head` operand.
That operand must return a `Head` before the application rule consumes its parentheses.
Previously, its unrestricted entry could consume the application suffix and return a `Value` to the waiting application rule.
The parent then waited for a parenthesis that the child had already consumed.

Leading operands now use the existing `StackSymbolV2::category_entry_goal` constructor.
Ordinary rule operands already use this constructor.
The shared infix dispatcher reads its goal and checks the declared category reachability relation.
An extension remains available when its result can reach the required operand category.
An extension cannot consume the parent's suffix when its result cannot reach that category.

The repair covers the singleton entry, fork entry, and nested child entry.
It preserves the source category, token position, binding powers, caller continuation, and authored weight.
The unrestricted entry for cross-category left-side discovery remains unchanged.
Both the generated parser and owned parser use the shared transition implementation.

`LeadingCategoryContinuation.v`, module `LeadingOperandGoal`, proves eight entry and admission laws.
The model takes category reachability as an input and does not prove the whole parser or the reachability computation.
The properties execute the production transitions and the existing infix, postfix, and mixfix admission paths.

| Formal invariant | Implementation property |
|---|---|
| `leading_entry_preserves_source` | `leading_route_is_frame_structural_and_preserves_authored_weight` compares every entry field after removing the goal |
| `leading_entry_requires_its_declared_category` | The same property checks the nested, singleton, and fork child goals |
| `leading_entry_preserves_control` | The same property varies positions, both binding powers, rule/category indices, and seven caller kinds |
| `leading_goal_admission_is_exact` | `leading_operand_goal_preserves_exact_reachable_extensions` checks the actual dispatcher against arbitrary reachability results |
| `leading_goal_refuses_unreachable_results` | Each case rejects an unreachable result in all three operator paths |
| `leading_goal_retains_reachable_results` | Each case retains a reachable foreign result in all three operator paths |
| `unrestricted_entry_admission_is_unchanged` | Each case checks an unrestricted entry with the same operator and reachability result |
| `unrestricted_child_can_leave_its_declared_category` | Each case compares strict and unrestricted admission for a distinct result category |

The independent `ApplicationOperand` fixture contains no Rholang or F1r3lang declarations.
Its fixed controls check `A()`, `empty - A()`, grouping, and a surrounding prefix constructor.
Its 64-case property varies application names, empty and nonempty argument lists, nested applications, and infix expressions.
Both the main parser and facade must preserve the complete expected tree.

Run the focused checks with:

```sh
cargo test --locked -p prattail --lib wpda_transitions::prefix::explicit_floor_tests
cargo test --locked -p macros --test cross_category_application_operand
```

#### Prefix operands with operator tails

A closing literal does not make an operator tail independent of precedence.
For example, `Inspect . receiver:Value, payload:Value |- receiver "[" payload "]" : Value;` is a local Pratt operator.
Under a prefix with binding power 220, the surface `@() [empty]` stops before the bracket postfix.
The complete operand requires grouping, as in `@(() [empty])`.

The display generator now uses the parser's existing `classify_rule_public` result.
A classified operator whose source and result categories are equal cannot inherit its receiver's primary status.
This rule applies to infix, postfix, and mixfix operators without testing names or operator spellings.
Other frames retain the existing wrapping decision.
A closing frame with a foreign source category can still follow its leading operand.
An unclassified frame also retains that behavior.

The independent fixture includes a captured-token method, a bracket postfix, two prefix symbols, and an enclosing send.
The parser classifies the bracket postfix as a Pratt operator.
The captured-token method uses the existing complex rule path.
The fixture checks those paths separately and retains the enclosing-send regression for independent diagnosis.

`WpdaDispatchPartition.v`, module `SigilOperandTail`, models the wrapping decision and its precedence boundary.
It uses the previous model's prefix-preservation predicate.
The model does not prove the parser classifier or all prefix/frame combinations.
The classification property checks emitted code, and the compiled fixture checks complete tree readback.

| Formal invariant | Implementation property |
|---|---|
| `local_operator_never_inherits_primary` | `sigil_wrap_preserves_parser_operator_boundaries` requires unconditional grouping for local operators |
| `local_operator_always_groups` | The same property varies open and closed operator tails |
| `unclassified_frame_preserves_old_wrap` | The same property checks the captured-token method's unchanged emitted decision |
| `foreign_operator_preserves_old_wrap` | The same property varies category names and checks foreign-source operators |
| `open_tail_always_groups` | The same property checks the open foreign-source tail |
| `closed_unclassified_tail_follows_primary` | The classification property checks the emitted call and the compiled fixture varies keyword and punctuation receivers |
| `local_operator_grouping_preserves_prefix_operand` | `prefix_roundtrip_preserves_complete_postfix_trees` compares complete parsed trees under both prefix symbols |
| `closed_literal_does_not_protect_a_local_tail` | Each recursive property case also rejects the ungrouped local tail |

The recursive property varies receivers, payloads, method names, and empty or nonempty argument lists.
It compares the main parser's readings and the facade result with the constructed tree.

#### Merge verification measurements

The 2026-10-21 macro census covers 57 reconstructed languages.
The census excludes the same three composed languages that require the macro registry.

The unit-test refusal count changes from 128 to 162 for two measured reasons:

- `SoleCollectionCarrierDemo` contributes 11 collection constructors.
- `PrefixOpenerUnion` contributes 10 collection constructors.
- Correct leaf classification exposes 13 Rholang constructors without a static field value.

The two fixtures have explicit integration and property tests.
Their collection constructors use the existing `CollectionElementSetup` refusal in the static unit-test generator.
This refusal does not remove the fixture tests.

The 13 Rholang constructors require values from categories whose former apparent leaf had a capture field.
The former leaf expression omitted that field and could not construct a valid Rust value.
The corrected classifier reports these cases instead of emitting that invalid expression.

The 2026-10-22 data-collection fixture adds six `CollectionElementSetup` entries.
They are `PMetas`, `PMetaSet`, `PMetaSeq`, `PMetaBagBnf`, `PMetaSetBnf`, and `PMetaSeqBnf`.
These declarations increase the unit-test count from 162 to 168.
The non-nullary `Meta::MProc` declaration adds one `ClosedDataCategory` entry to each depth generator.
Those counts increase from 100 to 101.
The nullary `MLit` and `MOther` declarations belong to the existing depth-zero domain.
The three intersection counts remain 75, 20, and 45.
The 57-language corpus and all generator classification rules remain the same.

| Category | Constructors newly reported by the unit-test generator |
|---|---|
| `DdlTheoryExpr` | `DdlTheoryFree`, `DdlTheoryApply`, `DdlTheoryRef` |
| `DdlImports` | `DdlImportsNonEmpty` |
| `DdlFreshnesses` | `DdlFreshnessOne` |
| `DdlPremises` | `DdlPremiseOne` |
| `DdlProjectionRule` | `DdlProjectionRuleDirect` |
| `DdlRuleAst` | `DdlRuleAstRemainderOnly`, `DdlRuleAstCollectionRemainder`, `DdlRuleAstTypedCollectionEmpty`, `DdlRuleAstTypedRemainderOnly`, `DdlRuleAstTypedCollectionRemainder` |
| `DdlRuleAstRemainderTail` | `DdlRuleAstTailMore` |

All 13 cases already have the `ClosedDataCategory` refusal in the random-term generator.
Thus, the unit-test and random-term intersection changes from 32 to 45.
The complete measured tuple is `(79, 162, 100, 75, 20, 45)`.
The tuple contains tape, unit-test, and random-term totals, followed by their pairwise intersections.

The factoring tests also use measurements from the merged Rholang grammar:

| Quantity | Measured value |
|---|---|
| `Name` category index | 6 |
| Unary, empty, and polyadic send indices | 6, 8, 10 |
| Persistent send indices | 7, 9, 11 |
| `@` prefix groups | 3 groups with 6, 3, and 6 members |
| `for` prefix group | `PForUser` and `PForCostSigned`, indices 29 and 30 |
| Send mixfix spine identifiers | 63492 and 63493 |

The tests retain checks for rule labels, branch order, binding powers, commit positions, and generated table contents.
The shift probe now selects the fourth `Proc` rule within that category.
A global term position could select a different category after the merge.

#### Grouped-send constructor evidence

The October 2026 opener investigation found valid interpretations beyond two historical parser counts.
The generated Rholang grammar permits transparent grouping and the explicit `NParen` constructor.
A channel with `d` groups therefore has constructor depths from zero through `d`.
These forms remain distinct parser results even when later lowering gives the same executable name.

For `bitnot ((a))!(false)`, the complete set contains channel depths zero, one, and two.
The route probe isolated the Proc opener at token position one.
Special branch 2, the Name grouping marker, produced depths zero and one.
Ordinary branch 22, the Name source entry, also produced depth two.
Ordinary branch 25, the leading unary send rule, produced depths zero and one.
The proposed source-category filter would remove a valid declared constructor combination.
The generator and owned engine therefore retain their existing route union.

The source `@Nil!()` has three retained forms:

- `POutputNilEmpty`.
- `POutputShortEmpty(PZero)`.
- `POutputEmpty(NQuoteNil)`.

The payload `@Nil!() / @Nil!()` has all nine ordered pairs of these forms.
Adding the two channel forms for `(a)` gives eighteen results for `bitnot (a)!(@Nil!() / @Nil!())`.
The tests construct the expected abstract syntax trees directly and compare complete structural sets.
They also reject duplicate results.
The expected set does not depend on the current parser's enumeration order.

The existing `PrefixOpenerUnion.v` model now includes this grammar fragment.
The model proves the constructor-depth bounds, completeness, uniqueness, and product counts.
The measured route lists provide a checked counterexample to pruning by source-category overlap alone.
They do not establish general equivalence or completeness for every parser route.

| Model obligations | Implementation evidence |
|---|---|
| `grouped_name_depth_sound`, `grouped_name_depth_complete`, `grouped_name_readings_exact` | `grouped_send_constructor_combinations_match_the_grammar` compares every generated constructor combination with the complete parser result set. |
| `grouped_name_readings_count`, `grouped_name_readings_unique`, `all_explicit_groups_are_retained` | The same property checks the exact cardinality, rejects duplicates, and includes the fully wrapped channel. |
| `measured_union_retains_all_two_group_forms`, `source_category_overlap_does_not_justify_removal` | `bitnot_nested_grouped_send_preserves_each_name_form` requires depths zero, one, and two. The retained route probe records their origins. |
| `grouped_send_combinations_exact`, `grouped_send_combinations_count`, `single_group_divided_send_has_eighteen_forms` | The property checks ordered payload pairs. `bitnot_grouped_send_payload_preserves_declared_combinations` checks the eighteen-form witness. |

The property varies the channel identifier, nesting depth from zero through six, and both payload families across 64 cases.
The model covers arbitrary finite nesting depth.
The implementation tests provide bounded correspondence evidence through the existing generated parser.
The separate cast-representative investigation remains applicable to the Boolean payload.

Run the focused checks with the existing resource limits:

```sh
coqc -Q formal/rocq/runtime_grammar/theories RuntimeGrammar formal/rocq/runtime_grammar/theories/PrefixOpenerUnion.v
coqchk -silent -Q formal/rocq/runtime_grammar/theories RuntimeGrammar RuntimeGrammar.PrefixOpenerUnion
cargo test --locked -p languages --no-default-features --features rholang,rho-codegen,dovetail-codegen,walker-trace --test rholang_tests flip_blocker_prefix_grouped_send -- --nocapture --test-threads=1
```

#### Semantic-class representatives

The all-results parser groups constructed terms by the generated semantic key.
A key defines a parser class. It does not prove that every class member has the same native value.
For example, `CastBool(BoolLit(false))` and `CastUInt32(BoolToUInt32(BoolLit(false)))` share a key.
Their native values have different types.

The old all-results fold retained the member with the smallest lexicographic weight.
When earlier weight fields are equal, rule 39, `CastUInt32`, precedes rule 40, `CastBool`.
The defect model isolates that ordering case. The source regression records the retained numeric constructor.
Single-result parsing elected the Boolean constructor instead.
The baseline reproduced this difference for `false`, `not false`, `true and true`, and `int(false, 64)`.

The corrected interfaces share `WpdaWalker::elect_root_to_term_with_weight`.
This method contains the existing descending probe sequence, from 128 through one, with the existing single-result election mode.
The single-result facade retains its driver and selection behavior.

The all-results facade first completes its existing enumeration and semantic-class fold.
It then collects each root's elected term and orders these terms by their existing weights.
`align_semantic_class_representatives` selects the first elected member with a matching key for each retained class.
A class without a matching election retains its current member.
Alignment preserves class order, class count, keys, and the minimum weight already recorded for each class.
The final weight sort remains unchanged.

Both complete-input and trailing-input branches use this alignment.
An election or reconstruction error returns the existing structured failure before the facade publishes a result.
The correction does not change the key schema or the bounded-prefix facade.
The ranked-prefix work has its own outstanding verification obligations.

| Formal obligation | Implementation evidence |
|---|---|
| `align_preserves_count`, `align_preserves_weights`, `align_preserves_keys` | The 256-case `alignment_preserves_classes_weights_and_first_elected_members` property checks every class position and weight. |
| `aligned_representative_is_elected`, `alignment_preserves_unmatched_class`, `alignment_uses_first_matching_election` | The same property checks first-match priority, absent keys, duplicate keys, empty inputs, and repeated alignment. |
| `key_eqb_spec`, `cast_cohort_key_collision`, `cast_cohort_eval_differs` | `transparent_casts_share_a_key_but_keep_distinct_native_values` checks both Boolean values through generated keys and native evaluators. |
| `g1_fold_keeps_cast_u32`, `g1_fold_drops_elected_term`, `g1_consumer_value` | The baseline regression records the wrong constructor. The key, native-value, rule-index, and weight-order checks bind the defect model to the generated implementation. |
| `g1_aligned_rep_is_elected`, `g1_aligned_value` | The four source regressions and the 64-case Boolean-expression property compare exact constructor trees with the existing single-result parser. |

`aligned_boolean_class_retains_its_minimum_weight` compares the retained weight with the minimum from raw walker enumeration for the same generated key.
It also checks rule 39 and the elected Boolean constructor.
The test oracle requires each small forest to finish enumeration within its explicit limit.
`trailing_input_uses_the_same_elected_representative` applies the same check to the trailing-input branch.
The ambiguity control preserves all four measured classes for `@((a)!(0))!()` and checks their distinct generated keys.

`facade_class_election.rs` uses the existing independent LedTest language definition.
Its examples and 64-case property cover Boolean and numeric categories, operators, grouping, distinct same-surface productions, and trailing input.
The tests compare all class keys and exact minimum weights with raw enumeration. They also compare the selected constructor with single-result parsing.
The shared production correction contains no language name, category name, literal, or rule index from either fixture.

The Boolean class has primary weight `0.025`, which the standard debug formatter displays as `0.0`.
The exact comparison retains all weight fields and the primary value bits. It does not use rounded debug text.
The affected REPL guard regression also passes: the vacuous implication permits communication, and the false implication prevents communication.

The models are `FacadeDriverFallThrough.v` and `OwnedSemanticVisitor.v`.
Their election premises describe the existing policy. They do not prove equality between the demand driver's roots and the exhaustive driver's roots.
Alignment only substitutes an elected member whose key already belongs to a retained class.
The cast counterexample uses finite, zero-cost weights. The alignment laws preserve weight records without evaluating their numeric fields.

Run the focused checks with the existing resource limits:

```sh
cargo test --locked -p prattail --test semantic_class_election
cargo test --locked -p languages --no-default-features --features rholang,rho-codegen,dovetail-codegen,walker-trace --test rholang_facade_election --test facade_class_election -- --nocapture --test-threads=1
coqc -Q formal/rocq/prattail_wpda_runtime/theories PrattailWpdaRuntime formal/rocq/prattail_wpda_runtime/theories/FacadeDriverFallThrough.v
coqc -Q formal/rocq/prattail_wpda_runtime/theories PrattailWpdaRuntime -Q formal/rocq/runtime_grammar/theories RuntimeGrammar formal/rocq/runtime_grammar/theories/OwnedSemanticVisitor.v
coqchk -silent -Q formal/rocq/prattail_wpda_runtime/theories PrattailWpdaRuntime -Q formal/rocq/runtime_grammar/theories RuntimeGrammar PrattailWpdaRuntime.FacadeDriverFallThrough RuntimeGrammar.OwnedSemanticVisitor
```

#### Ranked prefix parsing

The [ranked-prefix design](ranked-prefix-parsing.md) defines the generated ranked parser API, evidence retention, bounds, and formal-to-property mapping.

#### Parser expectation evidence

Parser expectations follow the declared grammar and measured constructor results.
The October 2026 checks retain both live internal keywords, `__comm_where` and `__guard_then`, under their generated hexadecimal token identifiers.
The deleted `__ppar` keyword remains absent.

The grammar explicitly lists `PPar` as contextual.
Its bare form remains a variable. Its complete predicate form selects `SpatialPPar`.
The semantic-predicate suite checks both forms and the neighboring identifier and call forms.

The projection comparison corpus now records 159 folds and zero comparator differences.
The probe contract permits zero differences when folds occur.
The test requires actual folds, the measured zero-difference result, and the existing exact constructor readings.
It does not claim comparator equivalence outside that corpus.

Native collection literals expose category-valued elements to the e-graph.
The bound-string fold witness therefore requires the concatenated value.
Its runtime-reducer error control remains active and records the existing semantic divergence.
These expectation corrections do not change parser or runtime behavior.

#### Static leaf selection

A static leaf is a constructor value that requires no recursively generated child.
The unit-test generator selects native literals first, then nullary constructors, then an admitted variable constructor.
The generator returns no static leaf when none of these choices applies.

The canonical `rule_to_variant_kind` classifier determines whether a constructor is nullary.
An empty legacy item list or term context does not establish this property.
For example, `value@Ident` creates a field even when the rule has no category-valued parameter.
The generator must skip that rule when it needs a nullary value.
Among eligible nullary constructors, the generator selects the first declaration in the requested category.

Collection fields use the empty value of their generated carrier.
An optional field uses `None` before the generator considers its carrier.

| Declared carrier | Empty Rust expression |
|---|---|
| `Vec` | `vec![]` |
| `HashBag` | `mettail_runtime::HashBag::new()` |
| `HashSet` | `mettail_runtime::HashSetLit::new()` |
| `PathMap` | `mettail_runtime::HashBag::new()` |
| Key/value `HashMap` | `mettail_runtime::HashMapLit::default()` |

The PathMap expression follows the generated field type.
It does not imply that a map and a bag have identical language semantics.
Correct carrier types also do not establish display and parse roundtrip behavior.
The finite witness generator therefore keeps its separate admission checks.

The [finite constructor model](../../formal/rocq/rho_bridge/theories/FiniteConstructorWitnessAdapter.v) defines `leaf_nullary`, `first_nullary_leaf`, and `empty_carrier_expression`.
The [generator tests](../../macros/src/gen/test_gen/unit_tests.rs) exercise the implementation with generated grammars and field metadata.

| Model invariant | Implementation property or regression |
|---|---|
| Capture fields prevent nullary classification | `captured_token_is_not_a_nullary_leaf`, `first_nullary_leaf_matches_model` |
| Selected rules belong to the requested category and have no fields | `first_nullary_leaf_matches_model` |
| Every eligible declaration yields a leaf | `first_nullary_leaf_matches_model` |
| Declaration order selects the first eligible rule | `first_nullary_leaf_matches_model` |
| Empty expressions match the declared carrier | `empty_carrier_matches_model` |
| Optional fields use `None` | `empty_carrier_matches_model` |

Run the focused generator tests with this command:

```sh
cargo test --locked -p macros --lib gen::test_gen::unit_tests::tests
```

The model proves selection and representation properties.
Generated-language compilation and roundtrip tests check the emitted Rust and its parser behavior.

### 2.5 Equation Test Generation (`equation_tests.rs`)

For each equation:
1. Parse LHS and RHS from `EquationDef` metadata strings
2. Run Ascent on LHS, verify RHS in equivalence class
3. Run Ascent on RHS, verify LHS in equivalence class (symmetry)
4. For freshness conditions: test violation does NOT produce equivalence

### 2.6 Rewrite Test Generation (`rewrite_tests.rs`)

For each rewrite rule:
1. Parse LHS from `RewriteDef` metadata
2. Run Ascent, verify at least one rewrite fires
3. Verify result matches RHS pattern
4. For congruence rules: construct outer context + inner redex, verify propagation

### 2.7 Analytical Test Generation (`analytical_tests.rs`)

Generate per-language:

```rust
#[test]
#[cfg(feature = "trs-analysis")]
fn analytical_confluence_check() {
    let lang = CalculatorLanguage;
    let result = mettail_testkit::analytical::check_language_confluence(lang.metadata());
    assert!(result.all_joinable,
        "Non-joinable critical pairs found:\n{}", result.format_failures());
}

#[test]
#[cfg(feature = "trs-analysis")]
fn analytical_termination_check() {
    let lang = CalculatorLanguage;
    let result = mettail_testkit::analytical::check_language_termination(lang.metadata());
    assert!(result.terminates,
        "Non-terminating SCCs found:\n{}", result.format_failures());
}
```

### 2.8 User Test Codegen (`user_tests.rs`)

Parse `tests { }` block, generate one `#[test]` per entry:

```rust
#[test]
fn user_eval_1_plus_2() {
    let lang = CalculatorLanguage;
    mettail_testkit::assert_evals_to(&lang, "1 + 2", "3")
        .expect("user test: eval \"1 + 2\" => \"3\"");
}
```

---

## 3. `tests { }` Block in `language!`

### 3.1 Syntax

```
language! {
    name: Calculator,
    types { ... },
    terms { ... },
    rewrites { ... },
    tests {
        // Spec-level tests
        parse "1 + 2" : Int;
        parse_fail "1 +" : Int;
        eval "1 + 2" => "3" : Int;
        eval "3 * (4 + 1)" => "15" : Int;
        rewrite "0{}" => normal_form : Proc;
        rewrite "for(0){x.{*x}}" => "*0" : Proc;
        roundtrip "lam x. x" : Term;

        // Application-level tests (see §5B for full syntax)
        program "double" {
            source: "lam x. x + x";
            eval "double(5)" => "10" : Int;
            property terminates;
        }
    },
}
```

### 3.2 AST Extension

Add to `LanguageDef` in `macros/src/ast/language.rs`:

```rust
pub tests: Option<TestBlock>,

pub struct TestBlock { pub cases: Vec<UserTest> }

pub enum UserTest {
    // Spec-level tests
    Parse { input: String, category: Ident },
    ParseFail { input: String, category: Ident },
    Eval { input: String, expected: String, category: Ident },
    Rewrite { input: String, expected: RewriteExpectation, category: Ident },
    Roundtrip { input: String, category: Ident },
    // Application-level tests
    Program { name: Ident, source: String, directives: Vec<ProgramDirective> },
}

pub enum RewriteExpectation { NormalForm, Term(String) }

pub enum ProgramDirective {
    Input { input: String, expected: String },        // concrete I/O test
    Property(ProgramProperty),                        // behavioral property
    Proptest { cases: u32, body: TokenStream },       // custom property test
}

pub enum ProgramProperty {
    Terminates,                          // F(normal_form)
    NoDeadlock,                          // G(!deadlock) via Petri
    Eventually(String),                  // F(predicate)
    Always(String),                      // G(predicate)
    Custom(String),                      // LTL formula string
}
```

### 3.3 TRS Check Configuration via `options { }`

The `options { }` block in `language!` already accepts key-value pairs (`HashMap<String, AttributeValue>`). We add three new recognized keys:

```
language! {
    name: Rholang,
    options {
        // TRS check behavior: "error" (default) | "warn" | "disable"
        confluence_check: "error",    // default: hard error on non-confluence
        termination_check: "warn",    // downgrade to warning for process calculi
        egraph_joinability: "error",  // default: hard error on non-joinability
    },
    // ...
}
```

**Semantics**:
- `"error"` (default): Non-confluence / non-termination is a `#[test]` that `assert!`s — hard failure
- `"warn"`: Non-confluence / non-termination is a `#[test]` that prints a warning but does **not** fail. Uses `eprintln!` with structured output. The test passes but the diagnostic is visible in `cargo test -- --nocapture`
- `"disable"`: The test is not generated at all (no `#[test]` function emitted)

The macro reads these from `language.options` during `generate_test_file()` and emits the appropriate test function:

```rust
// options { confluence_check: "error" } → default
#[test]
#[cfg(feature = "trs-analysis")]
fn analytical_confluence_check() {
    let result = mettail_testkit::analytical::check_language_confluence(...);
    assert!(result.all_joinable, "Non-joinable critical pairs:\n{}", result.format_failures());
}

// options { confluence_check: "warn" }
#[test]
#[cfg(feature = "trs-analysis")]
fn analytical_confluence_check() {
    let result = mettail_testkit::analytical::check_language_confluence(...);
    if !result.all_joinable {
        eprintln!("[WARN] Non-joinable critical pairs:\n{}", result.format_failures());
    }
}

// options { confluence_check: "disable" } → no test generated
```

### 3.4 Future Extension Point: Predicated Types

The design deliberately does **not** couple with predicated type syntax. When predicated types stabilize, they will feed into test generation via:
- Generating terms satisfying/violating refinement predicates
- Using `RefinementTypeSystem` from `type_system.rs` to guide strategies

---

## 4. Analytical Integration — Full Automata Map

Every module below has `analyze_from_bundle()` accepting grammar categories/syntax, making integration uniform. Each produces tests as `#[test]` functions in generated files, feature-gated where noted. Organized by tier: **always active**, **core analysis**, **advanced analysis**, and **new automata to add**.

### Tier 0: Always Active (No Feature Gate)

**4.0.1 WPDS Dead-Rule Pruning** (`prattail/src/wpds.rs`)
- `PipelineAnalysis.dead_rule_labels` already computed at macro expansion
- Tests for dead rules emitted with `#[ignore = "dead rule per WFST analysis"]`
- `PipelineAnalysis.constructor_weights` used to order tests by tropical weight (most-dispatched first)

**4.0.2 Forward-Backward Coverage Guidance** (`prattail/src/forward_backward.rs`)
- `forward_scores()` / `backward_scores()` identify hot paths through grammar
- `edge_occupancy()` reveals under-tested dispatch edges
- `hot_path_analysis()` identifies heavily-weighted paths → generate extra tests for these
- `critical_path()` identifies the single most important execution path → ensure full coverage

**4.0.3 Cost-Benefit Test Prioritization** (`prattail/src/cost_benefit.rs`)
- `build_grammar_profile()` produces `GrammarProfile` with ambiguity metrics
- `analyze_ambiguity_targets()` identifies ambiguous tokens → generate disambiguation tests
- `recommended_optimizations()` scores grammar properties → test-priority ranking

### Tier 1: Core Analysis (Feature: `trs-analysis`)

**4.1.1 Confluence Checking** (`prattail/src/confluence.rs`)
- `detect_critical_pairs(rules)` → for each critical pair, generate a `#[test]` asserting joinability
- `check_confluence(rules, max_steps)` → overall confluence certificate → one `#[test]`
- `suggest_confluence_repairs()` → diagnostic output on failure
- Behavior controlled by `options { confluence_check: "error" | "warn" | "disable" }` (default: `"error"`)

**4.1.2 Termination Checking** (`prattail/src/termination.rs`)
- `extract_dependency_pairs(rules)` → identify potential non-termination cycles
- `build_dependency_graph(pairs)` → SCC decomposition
- `check_termination(rules)` → `TerminationResult` → one `#[test]` per language
- Behavior controlled by `options { termination_check: "error" | "warn" | "disable" }` (default: `"error"`)

**4.1.3 E-Graph Equality Saturation** (`prattail/src/egraph.rs`)
- `analyze_trs(rules, terms)` → discover unexpected equalities between terms
- `check_joinability_egraph(t1, t2)` → verify terms join via equality saturation (stronger than TRS confluence)
- Each discovered equality becomes a regression `#[test]`
- `simplify_term(term, rules, config)` → verify simplification produces valid terms

**4.1.4 Theory Morphism Verification** (`prattail/src/morphism.rs`)
- For composed languages (`extends`, `includes`, `mixins`): verify translation preservation
- `detect_gaps(morphism)` → identify missing translations → test for each gap
- `verify_preservation(morphism)` → one `#[test]` per composition relationship

### Tier 2: Semantic Analysis (Feature: `cek-runtime`)

**4.2.1 Abstract CESK State Coverage** (`prattail/src/abstract_cesk.rs`)
- Build `DyckStateGraph` for reduction semantics with chosen allocation strategy (`ZeroCfaAlloc`, `OneCfaAlloc`)
- Enumerate reachable `EvalControlState` configurations via BFS
- `is_reachable()` checks → generate tests targeting unreached configurations
- `abstract_gc()` → verify GC preserves live locations
- `abstract_live_locations()` → coverage metric: fraction of reachable states exercised

**4.2.2 CEGAR Counterexample Generation** (`prattail/src/cegar.rs`)
- `cegar_verify(property, config)` → iterative refinement (Boolean → Counting → Tropical)
- Concrete counterexamples become `#[test]` functions with witness terms
- Spurious counterexamples (refined away) logged as diagnostics
- `adaptive_dead_rule_elimination()` → cross-validate with WPDS dead-rule results

**4.2.3 Green Thread Interleaving** (`prattail/src/green_thread.rs`)
- `QuantumResult` state machine (Ready → Running → Completed/Suspended/Failed/Forked)
- Generate tests that exercise fork/join patterns, suspension/resume cycles
- Verify deterministic scheduling: same seed → same execution trace
- Test checkpoint/restore: O(1) fork via structural sharing (im::HashMap)

### Tier 3: Structure Analysis (Feature: `structure-analysis`)

**4.3.1 Tree Automaton Coverage** (`prattail/src/tree_automaton.rs`)
- `analyze_from_bundle()` → extract WTA from grammar categories
- `bottom_up_evaluate(automaton, term)` → verify every generated term is accepted by its category's WTA
- Hot-path specialization: `HotPathReport` identifies most-weighted derivations → prioritize tests
- `validate_token_tree(tree, automaton)` → validate parse trees against structural invariants
- Generate terms from WTA: walk the automaton top-down, selecting transitions → systematic term construction

**4.3.2 VPA Nesting Verification** (`prattail/src/vpa.rs`)
- `analyze_from_bundle()` → extract VPA from balanced grammar structure
- `check_equivalence(a, b)` → verify grammar transformations preserve nesting
- `is_language_empty(vpa)` → detect unreachable nesting configurations
- Generate balanced test cases: walk VPA with matching call/return pairs
- `complement()` + `intersect()` → generate negative tests (strings that should NOT parse)

**4.3.3 Parity Tree Automata — mu-Calculus** (`prattail/src/parity_tree.rs`)
- `mu_calculus_to_pata(formula)` → compile modal specifications to tree automata
- `check_emptiness()` → verify specifications are satisfiable
- `evaluate_term(automaton, term, state)` → test ASTs against fixed-point properties
- `check_inclusion(a, b)` → verify one specification implies another

**4.3.4 Nominal Automata — Name-Binding** (`prattail/src/nominal.rs`)
- `check_freshness(automaton, state, name)` → verify freshness conditions in equation premises
- Generate name permutations to test alpha-equivalence: `term_eq()` must be invariant under name swaps
- `ScopeNarrowingResult` → verify scope analysis for binder-containing terms
- Orbit decomposition → systematic coverage of name configurations

### Tier 4: Concurrency Analysis (Feature: `process-analysis`)

**4.4.1 Petri Net Reachability** (`prattail/src/petri.rs`)
- Model concurrent language constructs (PPar, channels) as Petri net places/transitions
- Coverability analysis → detect potential deadlocks in concurrent terms
- Generate concurrent interleavings: different firing sequences for same initial marking
- Livelock detection → verify progress properties

**4.4.2 Multi-Tape Synchronization** (`prattail/src/multi_tape.rs`)
- `build_synced_stream_automaton()` → model multi-channel communication
- `validate_sync_constraints()` → verify stream synchronization invariants
- Generate test cases exercising all synchronization points
- Cross-channel data dependency → test data flow between concurrent processes

**4.4.3 Two-Way Transducer — Join Patterns** (`prattail/src/two_way_transducer.rs`)
- `analyze_join_pattern()` → identify join patterns in concurrent languages
- `detect_deadlock()` → hard test failure for potential deadlocks
- `prune_join_patterns()` → verify pruning preserves semantics

### Tier 5: Symbolic & Predicate Analysis (Feature: `symbolic-analysis`)

**4.5.1 Symbolic Finite Automata (SFA)** (`prattail/src/symbolic.rs`)
- `BooleanAlgebra` trait: `is_satisfiable()`, `witness()` → generate satisfying test inputs
- Guard overlap detection: for overlapping predicates, generate inputs that fall in the overlap
- `classify_decidability()` → verify all guard predicates have decidable checking
- Minterm partitioning → exhaustive partition of input space, one test per minterm

**4.5.2 Symbolic Finite Transducers (SFT)** (`prattail/src/sft.rs`)
- `compose_chain(transducers)` → verify composition preserves semantics
- `case_fold_sft()` / `whitespace_normalize_sft()` → test normalization invariants
- Generate inputs via predicate witnesses → verify transduction output matches expected

**4.5.3 Presburger Arithmetic** (`prattail/src/presburger.rs`)
- `is_satisfiable_nfa(pred, bit_width)` → verify numeric guard satisfiability
- `witness_nfa(nfa)` → generate satisfying integer assignments for test inputs
- `complement_nfa()` + `is_empty_nfa()` → verify guard completeness (no uncovered cases)
- `extract_numeric_guard()` → automatically extract testable constraints from guard expressions

**4.5.4 Register Automata** (`prattail/src/register_automata.rs`)
- `analyze()` → data-equality analysis over name/channel values
- Generate inputs exercising each register operation (test, assign, update)
- Verify register bounds: finite register count handles unbounded name domains

**4.5.5 KAT — Kleene Algebra with Tests** (`prattail/src/kat.rs`)
- `check_equivalence(a, b)` → verify program fragment equivalences
- `verify_hoare_triple({pre} prog {post})` → auto-generated correctness tests from equations/rewrites
- Each equation `l = r` becomes a KAT equivalence check → one `#[test]`
- Bounded equivalence for complex programs: `check_equivalence_bounded(a, b, depth)`

### Tier 6: Quantitative Analysis (Feature: `quantitative-analysis`)

**4.6.1 Cost Register Automata (CRA)** (`prattail/src/cra.rs`)
- `evaluate_stream(cra, input_stream)` → verify resource cost of term evaluation
- `cra_check_equivalence(a, b)` → verify cost-equivalent transformations
- Generate bounded-resource test inputs → verify evaluation stays within bounds

**4.6.2 Probabilistic Analysis** (`prattail/src/probabilistic.rs`)
- `estimate_channel_load()` → predict concurrent channel utilization
- Generate test inputs biased toward high-probability paths (likelihood-guided testing)
- Verify coverage of low-probability but critical paths

**4.6.3 Provenance Tracking** (`prattail/src/provenance.rs`)
- `track_from_bundle()` → identify which derivation paths each test exercises
- Coverage report: what fraction of provenance paths have at least one test
- Generate tests targeting uncovered provenance paths

**4.6.4 Weighted MSO** (`prattail/src/weighted_mso.rs`)
- `classify_formula()` → verify decidability of language properties
- `evaluate_sentence_bool()` → test closed formulas against concrete structures
- Auto-translate LTL/CTL specifications to WMSO → verify satisfaction

**4.6.5 Affine Relation Analysis (ARA)** (`prattail/src/ara.rs`)
- `analyze_from_bundle()` → discover affine invariants between grammar variables
- Each invariant becomes a proptest property: verify all generated terms satisfy the invariant

### Tier 7: Temporal & Infinite Behavior (Feature: `temporal-analysis`)

**4.7.1 LTL Temporal Logic** (`prattail/src/ltl.rs`)
- `parse_ltl(formula)` → specify behavioral properties as LTL formulas
- `check_ltl_property(property, trace)` → verify traces satisfy temporal properties
- Generate traces from reduction sequences → check against LTL specs
- Auto-derive LTL properties from rewrite rules: "eventually normal form", "always well-typed"

**4.7.2 Buchi Automata** (`prattail/src/buchi.rs`)
- `ltl_to_buchi(formula)` → compile LTL to omega-automaton
- `check_emptiness(buchi)` → verify property is satisfiable
- `buchi_intersect(system, negated_property)` → model checking (empty = property holds)
- `total_accepting_weight()` → quantitative measure of property satisfaction

**4.7.3 Alternating Automata** (`prattail/src/alternating.rs`)
- `evaluate_word(automaton, word)` → verify word under universal/existential branching
- `bisimulation_game(a, b)` → verify bisimulation equivalence of language constructs
- `analyze_fork_join_cost()` → parallelization cost model for concurrent terms

### Tier 8: Algebraic & Path Analysis (Feature: `algebraic-analysis`)

**4.8.1 Algebraic Path Expressions** (`prattail/src/algebraic.rs`)
- `build_cfg(wpds)` → extract control flow from WPDS
- `path_expression(cfg)` → compute regex-like path closure
- `all_pairs_analysis(cfg)` → all-pairs shortest paths → verify every reachable pair is tested
- `interprocedural_analyze(icfg)` → cross-category analysis

**4.8.2 Relational Heap Analysis** (`prattail/src/relational.rs`)
- `HeapWpds` → model store mutations as relational transitions
- Verify heap invariants: store operations preserve well-formedness
- Generate heap test sequences: allocate, mutate, GC, verify

**4.8.3 EWPDS — Extended WPDS** (`prattail/src/ewpds.rs`)
- `ewpds_poststar()` → reachability with custom merge functions
- Verify merge semantics: `OverrideMerge` produces expected results
- Test local variable handling across category boundaries

**4.8.4 Lattice Theory** (`prattail/src/lattice_theory.rs`)
- `analyze_from_bundle()` → extract type lattice from grammar
- Verify subtype transitivity: if A <: B and B <: C then A <: C
- Verify join/meet properties: commutativity, associativity, absorption

### 4.9 New Automata Worth Adding

These do not currently exist in prattail but would enrich test generation:

| New Automaton | Purpose | Test Generation Value |
|---|---|---|
| **Bounded model checker** | Explicit-state k-bounded verification | Exhaustively verify properties up to depth k; find shortest counterexamples |
| **Antichain-based inclusion checker** | Efficient language inclusion using antichains | Verify grammar refinements preserve inclusion; test that composed languages don't lose behaviors |
| **Interpolation engine** | Craig interpolation for abstraction | Generate minimal predicates separating good/bad states; guided strategy generation |
| **Symbolic execution engine** | Concrete-symbolic hybrid execution | Path-sensitive test generation; explore all feasible paths through guard conditions |
| **Mutation testing automaton** | Systematic term mutation (operator swap, constant change, binder rename) | Verify test suite detects mutations; mutation score as quality metric |
| **Grammar coverage automaton** | Track which grammar rules are exercised by test inputs | Coverage metric: fraction of rules exercised; generate inputs targeting uncovered rules |
| **Counterexample minimizer** | Delta-debugging style minimization over ASTs | Shrink failing test cases to minimal reproducer; better than proptest's linear shrinking for tree-structured terms |

---

## 5. Property Test Specifications

For each language, generate these per-category:

### 5.1 Structural Properties (Always Generated)

| Property | Formula | Scope |
|---|---|---|
| Roundtrip | `parse(display(t)).term_eq(t)` | Every category |
| Display idempotence | `display(parse(display(t))) == display(t)` | Every category |
| Parse determinism | `parse(s)` twice → same result | Every category |

Alpha-equivalence via `Term::term_eq()` (moniker `BoundTerm`) used universally.

### 5.2 Semantic Properties (Always Generated)

| Property | Formula | Scope |
|---|---|---|
| Eval determinism | `eval(t) == eval(t)` | Categories with native types |
| Normalization idempotence | `normalize(normalize(t)) == normalize(t)` | All categories |
| Substitution well-formedness | `is_ground(v) => parse(display(subst(t, x, v)))` succeeds | Categories with binders |
| Ground eval completeness | `is_ground(t) => try_direct_eval(t).is_some()` | Categories with native types |

### 5.3 Algebraic Properties (Always Generated)

| Property | Formula | Scope |
|---|---|---|
| Equation symmetry | Ascent: `eq(l, r)` and `eq(r, l)` | Each equation |
| Rewrite progress | `run_ascent(t).rewrites.len() > 0` | Each base rewrite |
| Rewrite determinism | Same input → same rewrite result | Each rewrite |

### 5.4 TRS Properties (Feature: `trs-analysis`)

| Property | Formula | Scope |
|---|---|---|
| Confluence | Critical pair normal forms coincide | Default error; configurable via `options { confluence_check }` |
| Termination | Rewrite chains terminate within N steps | Default error; configurable via `options { termination_check }` |
| E-graph joinability | `check_joinability_egraph(t1, t2)` for critical pairs | Default error; configurable via `options { egraph_joinability }` |

### 5.5 Structural Invariants (Feature: `structure-analysis`)

| Property | Formula | Scope |
|---|---|---|
| WTA acceptance | Every generated term accepted by its category's WTA | All categories |
| VPA balance | Every generated term parses to balanced token tree | All categories |
| Nominal freshness | Freshness conditions in equations verified | Each equation with `x # P` |

### 5.6 Semantic Invariants (Feature: `cek-runtime`)

| Property | Formula | Scope |
|---|---|---|
| CESK reachability | Generated terms reach expected abstract states | Per-category |
| GC safety | `abstract_gc()` preserves live locations | Per-category |
| Green thread determinism | Same seed → same scheduling trace | Concurrent categories |

### 5.7 Symbolic Properties (Feature: `symbolic-analysis`)

| Property | Formula | Scope |
|---|---|---|
| Guard decidability | All guards classified T1-T3 (no T4) | Per-guard |
| Presburger satisfiability | Numeric guards have satisfying assignment | Per-numeric-guard |
| KAT Hoare triples | `{pre} rule {post}` verified | Per-equation/rewrite |

---

## 5A. Predicated Types — Future Test Generation (Decoupled)

When predicated types are fully implemented, the following test generation capabilities become available. The testkit design provides extension points but does **not** couple with current predicated type syntax.

### 5A.1 Guard Classification Tests

For each guard `phi` in the language:
- Verify decidability tier assignment (T1/T2/T3/T4) is correct
- **T1 guards**: verify compile-time evaluation matches runtime evaluation
- **T2 guards**: verify SFA/Ascent-compiled guard matches naive evaluation
- **T3 guards**: verify bounded checker finds same result as unbounded (for small domains)
- **T4 guards**: verify user assertion wrapper is correctly emitted

### 5A.2 Refinement Type Tests

For each refinement type `R = { x: Base | phi(x) }`:
- **Positive**: generate terms satisfying `phi` → verify `is_refined_R(term)` holds in Ascent
- **Negative**: generate terms violating `phi` → verify `is_refined_R(term)` does NOT hold
- **Boundary**: generate terms at the boundary of `phi` → verify classification is correct
- **Inhabitedness**: verify `is_inhabited(env, R)` matches whether witness generation succeeds
- Use `RefinementTypeSystem<S, T>` from `type_system.rs` to guide strategy generation

### 5A.3 Guard Interaction Tests

- **Overlap detection**: for guards on the same channel, verify SFA overlap analysis
- **Subsumption**: if refinement type `R` entails guard `phi`, verify communication always succeeds for R-typed values
- **Dead receive rules**: verify SYM01 lint catches genuinely dead receives
- **Priority ordering**: verify entropy-based guard ordering doesn't change semantics

### 5A.4 Constraint Theory Tests

For each theory registered in `guards { theories { ... } }`:
- **Presburger**: generate integer assignments → verify `evaluate_presburger(pred, assignment)` matches expected
- **Unification**: generate terms → verify `propagate(store, constraint)` produces correct substitution
- **Lattice**: verify subtype relationships hold after propagation
- **Cross-theory**: for guards spanning multiple theories, verify composition is sound

### 5A.5 Multi-Channel Coordination Tests

For languages with `channels { }` configuration:
- **Join patterns**: verify multi-channel receives fire only when all channels have matching values
- **Deadlock detection**: TW01 lint → verify Petri net analysis catches actual deadlocks
- **Backward propagation**: verify M8/M11 analysis correctly constrains upstream channels

### 5A.6 Pipeline Stage Tests

For each guard through the 5-stage pipeline:
- **Stage 1** (Parsing): verify guard syntax parses correctly, variable categories inferred
- **Stage 2** (Classification): verify tier assignment matches expected
- **Stage 3** (Analysis): verify module activation (M1-M15) is correct
- **Stage 4** (Compilation): verify compiled guard accepts same inputs as interpreted guard
- **Stage 5** (Codegen): verify generated Rust code compiles and produces correct results

### 5A.7 Lint Completeness Tests

For each of the 24+ lint categories:
- Generate a term that should trigger the lint → verify it fires
- Generate a term that should NOT trigger the lint → verify it doesn't
- Lint categories: SYM01-SYM03, MSO01-MSO03, PT01-PT03, RA01-RA03, MT01-MT03, TW01-TW03, PR01, PB01-PB03, UN01-UN03, SL01-SL02, LT01-LT03

### 5A.8 Predicated Types + Application Testing

Predicated types dramatically improve application-level testing (§5B):

**Type-directed fuzzing**: Instead of generating arbitrary terms, `arb_strategy()` is filtered by the guard predicate. For `(chan ? {x: PosInt}).{body}`, only positive integers are generated. This uses:
- `RefinementTypeSystem::is_inhabited()` to verify the strategy can produce terms
- `PresburgerAlgebra::witness_nfa()` for integer constraint solving
- `BooleanAlgebra::witness()` for symbolic predicate satisfaction
- `LogicStream` fair backtracking for quantified predicates

**Guard-as-specification**: Each guard becomes a testable specification:
- `(n ? phi).{c}` ≡ "c executes only when phi holds on input"
- Auto-generate `{phi(input)} → c[input/x] terminates` (Hoare triple)
- Auto-generate `{¬phi(input)} → c does not execute` (negative test)
- Use KAT `verify_hoare_triple()` for decidable verification
- Use CEGAR for counterexample-guided falsification

**Compositional contracts**: For `P | Q`:
- P's output type must refine Q's input guard: `type(P_output) ⊆ guard(Q_input)`
- Verified via `is_subtype()` in `RefinementTypeSystem`
- Failures become hard test errors with witness terms

**Decidability-aware test selection**: The tier classification (T1-T4) determines test strategy:
- T1 (compile-time): test exhaustively (small finite domain)
- T2 (runtime decidable): test via SFA acceptance + proptest
- T3 (semi-decidable): test with bounded depth, flag as partial coverage
- T4 (undecidable): trust user assertion, generate smoke tests only

### 5A.9 Extension Points in Current Design

The current testkit design provides these hooks for future predicated type integration:
- `AnalyticalConfig.enable_guard_analysis: bool` — gate guard-related tests
- Generated test files include `#[cfg(feature = "predicated-types")]` sections (empty initially)
- `testkit/src/analytical/guards.rs` — placeholder module for guard test drivers
- Strategy generation respects refinement types: when `arb_strategy()` generates terms for a refined category, it filters by predicate (once available)
- `ProgramTestSuite::with_guard_coverage()` — generate inputs exercising each guard branch
- `testkit/src/properties/guard_properties.rs` — placeholder for guard-specific property assertions

---

## 5B. Application-Level Testing — Programs Written in MeTTaIL Languages

Beyond testing language specifications, the framework auto-generates tests for **applications** (programs) written in MeTTaIL-defined languages. A user writes a program in e.g. Rholang or Calculator, and the framework generates tests for that program using the language's semantics.

### 5B.1 Architecture

Programs are provided as source text (`.rho`, `.calc`, etc.) or as terms constructed in Rust. The testkit provides a `ProgramTestSuite` builder that takes a program, its language, and optional user annotations, and generates `#[test]` functions.

Two modes:
1. **Inline in `language!`**: Programs in the `tests { }` block with `program` keyword
2. **Standalone test files**: Rust test files that use testkit's `ProgramTestSuite` API

### 5B.2 Inline Mode — `tests { }` Extension

```
language! {
    name: Rholang,
    // ...
    tests {
        // Spec-level tests (existing)
        eval "1 + 2" => "3" : Int;

        // Application-level tests (new)
        program "echo" {
            source: "for(x <- chan){chan!(*x)}";
            // Auto-generated: parse, roundtrip, type-check, normalize, rewrite
            // Auto-generated: deadlock analysis, termination bound, CESK coverage
            input chan!("hello") => chan!("hello");  // concrete I/O test
            property terminates;                     // LTL: eventually normal form
            property no_deadlock;                    // Petri net analysis
        }

        program "counter" {
            source: "new count in { count!(0) | for(n <- count){count!(*n + 1)} }";
            property eventually(count_gt(5));  // bounded liveness
        }
    },
}
```

### 5B.3 Standalone API Mode

```rust
// In a test file:
use mettail_testkit::program::ProgramTestSuite;
use mettail_languages::rholang::RholangLanguage;

#[test]
fn test_echo_program() {
    let suite = ProgramTestSuite::new(&RholangLanguage)
        .source("for(x <- chan){chan!(*x)}")
        .expect_parses()
        .expect_terminates(1000)           // bounded step count
        .expect_no_deadlock()              // Petri net
        .expect_rewrite("chan!(hello)", "chan!(hello)")  // concrete I/O
        .with_proptest(500, |term| {       // property: arbitrary input preserved
            // Auto-generated: term is a random Name-typed value
            // Verify: sending term on chan yields receiving term on chan
        });
    suite.run().expect("echo program tests");
}
```

### 5B.4 Auto-Generated Application Tests

Given a program `P` in language `L`, automatically generate:

**Structural**:
- Parse `P` succeeds
- Roundtrip: `parse(display(parse(P))) == parse(P)`
- All subterms are well-formed (WTA acceptance)

**Semantic**:
- Normalize `P` → verify normalization is idempotent
- If `P` has native-type subterms: eval produces values
- Substitution: for each free variable in `P`, substitute concrete values → verify well-formedness

**Rewrite**:
- Run Ascent on `P` → verify at least one rewrite fires (if `P` is not normal form)
- Rewrite to normal form → verify it's actually in normal form (no further rewrites)
- If multiple rewrite paths exist: verify confluence (same normal form)

**Concurrency** (for process calculi like Rholang):
- Petri net deadlock analysis → hard error if deadlock detected
- Multi-tape synchronization → verify all channels can communicate
- Green thread interleaving → verify all scheduling orders produce same normal form

**Abstract interpretation**:
- CESK: enumerate reachable states → verify no stuck states (except intended halting)
- CEGAR: search for property violations → counterexamples become failing tests

**Temporal**:
- Auto-derive LTL properties:
  - `F(normal_form)` — eventually reaches normal form (termination)
  - `G(well_typed)` — always well-typed (type preservation)
  - `G(!deadlock)` — always not deadlocked (liveness)
- Compile to Büchi → model check against execution traces

**Input generation** (property-based):
- For each free variable/channel in `P`: generate inputs using `arb_strategy()`
- For each input: substitute into `P`, run Ascent, verify properties hold
- This is the key connection: the language's term generators become the program's input generators

### 5B.5 Predicated Types + Application Testing (Future)

When predicated types are implemented, application testing gains:

**Type-directed input generation**:
- For `(chan ? {x: PosInt}).{body}`: generate only positive integer inputs
- Use `RefinementTypeSystem` to filter `arb_strategy()` to satisfying terms
- Presburger witness generation (`witness_nfa()`) produces satisfying integer inputs
- SFA witness generation (`BooleanAlgebra::witness()`) produces satisfying predicate inputs

**Guard coverage**:
- For each guarded receive in `P`: generate inputs that match AND inputs that don't match
- Verify guard selectivity: matching inputs proceed, non-matching inputs block
- Multi-guard coverage: for overlapping guards, test the overlap region

**Behavioral specification testing**:
- Guards as specifications: `(chan ? phi).{body}` means "`body` only executes when `phi` holds"
- Auto-generate positive tests: inputs satisfying `phi` → verify `body` executes
- Auto-generate negative tests: inputs violating `phi` → verify `body` does NOT execute
- Boundary tests: inputs at the boundary of `phi` → verify correct classification

**Contract testing** (Hoare triples from guards):
- Each guarded communication `{ n!(q) | (n ? phi).{body} }` implies `{phi(q)} body {post}`
- Auto-extract `post` from the normal form of `body[q/x]`
- Use KAT to verify the Hoare triple
- Use CEGAR to find counterexamples

**Compositional testing**:
- For composed programs `P | Q`: verify P's outputs satisfy Q's input guards
- Type refinement subsumption: if P sends type `R` and Q expects guard `phi`, verify `R ⊆ phi`
- Deadlock freedom: Petri net analysis of the composed system

### 5B.6 Integration with `cargo test`

Application-level tests from the `tests { program ... }` block are generated as `#[test]` functions in the same generated test file:

```rust
// Generated in languages/tests/generated/rholang_tests.rs

mod program_echo {
    use super::*;

    #[test]
    fn parse() { ... }

    #[test]
    fn roundtrip() { ... }

    #[test]
    fn terminates() { ... }

    #[test]
    #[cfg(feature = "process-analysis")]
    fn no_deadlock() { ... }

    #[test]
    fn io_chan_hello() { ... }

    proptest! {
        #[test]
        fn prop_input_preservation(input in Name::arb_strategy(2)) {
            // Verify: sending input on chan yields receiving input on chan
        }
    }
}
```

---

## 6. `cargo test` / `cargo nextest run` Integration

### 6.1 Generated Test Files

The `language!` macro writes test files at `languages/tests/generated/{name}_tests.rs` as a side effect during expansion (same pattern as `write_ascent_source()` and `write_blockly_blocks()`). These are checked into version control.

### 6.2 Usage

```bash
# Run all generated tests for all languages
cargo test -p languages

# Run only Calculator tests
cargo test -p languages calculator

# Run only roundtrip property tests
cargo test -p languages prop_roundtrip

# Run with nextest for per-test process isolation
cargo nextest run -p languages

# Run specific test
cargo nextest run -p languages -E 'test(prop_int_roundtrip)'

# Include dead-rule tests (normally ignored)
cargo test -p languages -- --ignored

# Run with TRS analysis
cargo test -p languages --features trs-analysis
```

### 6.3 Nextest Compatibility

Fully nextest-compatible:
- Each test calls `mettail_runtime::clear_var_cache()` at the start
- No shared mutable state between tests
- No test ordering dependencies
- proptest tests use deterministic seeds (regression files track failures)

### 6.4 Dead-Rule Handling

Dead rules per WFST analysis get `#[ignore]`:

```rust
#[test]
#[ignore = "dead rule per WFST analysis (Tier 1: LiteralNoNativeType)"]
fn unit_deadrule_roundtrip() { ... }
```

---

## 7. Module & File Map

### New Files

| File | Purpose |
|---|---|
| `testkit/Cargo.toml` | Crate manifest (deps: proptest, runtime, prattail) |
| `testkit/src/lib.rs` | Re-exports |
| `testkit/src/properties/mod.rs` | Property module |
| `testkit/src/properties/structural.rs` | Roundtrip, display idempotence assertions |
| `testkit/src/properties/semantic.rs` | Eval determinism, normalization idempotence, subst, ground eval |
| `testkit/src/properties/algebraic.rs` | Equation symmetry, rewrite progress, eval-to, normal-form |
| `testkit/src/analytical/mod.rs` | Analytical module |
| `testkit/src/analytical/confluence.rs` | Tier 1: Confluence checking |
| `testkit/src/analytical/termination.rs` | Tier 1: Termination checking |
| `testkit/src/analytical/egraph_tests.rs` | Tier 1: E-graph joinability |
| `testkit/src/analytical/morphism_tests.rs` | Tier 1: Theory morphism verification |
| `testkit/src/analytical/cesk_coverage.rs` | Tier 2: CESK state coverage |
| `testkit/src/analytical/cegar_tests.rs` | Tier 2: CEGAR counterexample generation |
| `testkit/src/analytical/green_thread_tests.rs` | Tier 2: Green thread interleaving |
| `testkit/src/analytical/tree_automaton_tests.rs` | Tier 3: WTA coverage |
| `testkit/src/analytical/vpa_tests.rs` | Tier 3: VPA nesting |
| `testkit/src/analytical/nominal_tests.rs` | Tier 3: Nominal freshness |
| `testkit/src/analytical/parity_tree_tests.rs` | Tier 3: Parity tree / mu-calculus |
| `testkit/src/analytical/petri_tests.rs` | Tier 4: Petri net deadlock |
| `testkit/src/analytical/multi_tape_tests.rs` | Tier 4: Multi-tape sync |
| `testkit/src/analytical/sfa_tests.rs` | Tier 5: SFA guard analysis |
| `testkit/src/analytical/presburger_tests.rs` | Tier 5: Presburger numeric guards |
| `testkit/src/analytical/kat_tests.rs` | Tier 5: KAT Hoare triples |
| `testkit/src/analytical/provenance_tests.rs` | Tier 6: Derivation path coverage |
| `testkit/src/analytical/ltl_buchi_tests.rs` | Tier 7: LTL temporal properties |
| `testkit/src/analytical/guards.rs` | Future: Predicated type guard analysis stubs |
| `testkit/src/properties/guard_properties.rs` | Future: Guard-specific property assertions |
| `testkit/src/mutation.rs` | New: Mutation testing automaton |
| `testkit/src/coverage.rs` | New: Grammar coverage automaton |
| `testkit/src/minimizer.rs` | New: AST-aware counterexample minimizer |
| `testkit/src/strategies.rs` | Shared proptest strategy helpers (var names, interesting values) |
| `testkit/src/alpha.rs` | Alpha-equivalence assertion helpers |
| `testkit/src/program.rs` | `ProgramTestSuite` builder for application-level testing |
| `macros/src/gen/test_gen/mod.rs` | `generate_test_file()` + `write_test_file()` entry point |
| `macros/src/gen/test_gen/strategies.rs` | Per-category `arb_strategy()` codegen |
| `macros/src/gen/test_gen/unit_tests.rs` | Constructor unit test codegen |
| `macros/src/gen/test_gen/equation_tests.rs` | Equation test codegen |
| `macros/src/gen/test_gen/rewrite_tests.rs` | Rewrite test codegen |
| `macros/src/gen/test_gen/analytical_tests.rs` | Analytical test codegen |
| `macros/src/gen/test_gen/user_tests.rs` | User `tests {}` block codegen |
| `macros/src/gen/test_gen/program_tests.rs` | Application-level `program {}` block codegen |
| `languages/tests/generated/calculator_tests.rs` | Auto-generated test file for Calculator |
| `languages/tests/generated/lambda_tests.rs` | Auto-generated test file for Lambda |
| `languages/tests/generated/rholang_tests.rs` | Auto-generated test file for Rholang |
| `languages/tests/generated/ambient_tests.rs` | Auto-generated test file for Ambient |
| `docs/design/test_framework.md` | Design documentation |

### Modified Files

| File | Change |
|---|---|
| `Cargo.toml` (workspace root) | Add `testkit` to workspace members |
| `macros/src/gen/mod.rs` | Add `pub mod test_gen;` |
| `macros/src/lib.rs` | Call `write_test_file()` in `language()` alongside `write_ascent_source()` |
| `macros/src/ast/language.rs` | Add optional `tests: Option<TestBlock>` to `LanguageDef`, parse `tests { }` |
| `languages/Cargo.toml` | Add `testkit` as dev-dependency |

### Existing Files to Reuse (Not Modify)

| File | Reuse |
|---|---|
| `macros/src/gen/term_gen/random.rs` | Pattern for strategy generation |
| `macros/src/gen/term_gen/exhaustive.rs` | `GenerationContext` memoization pattern |
| `macros/src/gen/runtime/language.rs` | Pattern for `generate_language_impl()` |
| `runtime/src/language.rs` | `Language`, `Term`, `AscentResults` traits |
| `runtime/src/metadata.rs` | `LanguageMetadata`, `TermDef`, `EquationDef`, `RewriteDef` |
| `prattail/src/lib.rs` | `PipelineAnalysis` (dead_rule_labels, constructor_weights) |
| `prattail/src/confluence.rs` | Confluence checking |
| `prattail/src/termination.rs` | Termination checking |
| `prattail/src/abstract_cesk.rs` | DSG construction |
| `prattail/src/cegar.rs` | CEGAR refinement |

---

## 8. Dependency Graph

```
testkit (library)
 ├── runtime (Language, Term, AscentResults, LanguageMetadata)
 ├── prattail [optional: confluence, termination, abstract_cesk, cegar]
 └── proptest

languages (dev-dependencies for tests)
 ├── testkit
 └── proptest

macros (proc macro, no new deps — generates code referencing testkit)
```

### Feature Gating (`testkit/Cargo.toml`)

```toml
[features]
default = []
# Tier 1: Confluence, termination, e-graph, morphism
trs-analysis = ["prattail/confluence", "prattail/termination", "prattail/egraph"]
# Tier 2: Abstract CESK, CEGAR, green threads
cek-runtime = ["prattail/cek-runtime", "prattail/green-threads"]
# Tier 3: Tree automata, VPA, parity tree, nominal
structure-analysis = ["prattail/tree-automaton", "prattail/vpa", "prattail/nominal"]
# Tier 4: Petri nets, multi-tape, two-way transducers
process-analysis = ["prattail/petri", "prattail/multi-tape", "prattail/process-algebra"]
# Tier 5: SFA, SFT, Presburger, register automata, KAT
symbolic-analysis = ["prattail/symbolic-automata", "prattail/predicate-dispatch", "prattail/kat"]
# Tier 6: CRA, probabilistic, provenance, WMSO, ARA
quantitative-analysis = ["prattail/cra", "prattail/probabilistic", "prattail/provenance"]
# Tier 7: LTL, Büchi, alternating automata
temporal-analysis = ["prattail/ltl", "prattail/buchi", "prattail/alternating"]
# Tier 8: Algebraic paths, relational, EWPDS, lattice
algebraic-analysis = ["prattail/analysis"]
# Future: predicated types
predicated-types = []
# Everything
full-analysis = ["trs-analysis", "cek-runtime", "structure-analysis", "process-analysis",
                 "symbolic-analysis", "quantitative-analysis", "temporal-analysis", "algebraic-analysis"]
```

---

## 9. Implementation Phases

### Phase 1: Foundation
- Create `testkit/` crate with `Cargo.toml`, `lib.rs`, property modules (stubs)
- Create `macros/src/gen/test_gen/mod.rs` with `write_test_file()` stub
- Wire into `macros/src/lib.rs` alongside `write_ascent_source()`
- Implement basic structural assertions (`assert_roundtrip`, `assert_display_idempotence`)
- Implement strategy helpers (`arb_var_name`, `arb_i32_interesting`, etc.)
- **Verify**: `cargo build -p languages` compiles with empty generated test files

### Phase 2: Proptest Strategy Generation + Cargo Test Files
- Implement `macros/src/gen/test_gen/strategies.rs` — auto-generate `arb_strategy()` per category
- Handle all constructor variants: nullary, unary, binary, n-ary, binder, multi-binder, collection, cross-category
- Handle native type leaves: `i32`, `f64`, `bool`, `String`
- Implement generated test file writing (following `write_ascent_source()` pattern)
- Generate structural property tests (`proptest!` blocks) in test files
- **Verify**: `cargo test -p languages` runs roundtrip + display idempotence for all categories; `cargo nextest run` works

### Phase 3: Unit Tests + Semantic Properties
- Implement unit test generation (one `#[test]` per constructor)
- Implement semantic assertions (eval determinism, normalization idempotence, subst, ground eval)
- Generate semantic property tests in test files
- **Verify**: `cargo test -p languages` runs unit + structural + semantic tests

### Phase 4: Equation + Rewrite Tests
- Implement equation test generation (symmetry via Ascent)
- Implement rewrite test generation (fires + result matches)
- Implement algebraic assertions
- **Verify**: `cargo test -p languages` includes equation + rewrite tests

### Phase 5: `tests { }` Block
- Add `TestBlock` to `LanguageDef`, parse `tests { }` in `language.rs`
- Implement user test codegen
- Add example `tests { }` blocks to Calculator and Rholang
- **Verify**: `cargo test -p languages user_` runs user-specified tests

### Phase 6: Tier 0 — Always-Active Analytics
- Implement WPDS dead-rule `#[ignore]` annotations from `PipelineAnalysis`
- Implement forward-backward coverage guidance (hot path tests)
- Implement cost-benefit test prioritization (ambiguity target tests)
- **Verify**: `cargo test -p languages` shows dead rules as ignored, hot-path tests present

### Phase 7: Tier 1 — TRS Analysis
- Implement confluence checking integration (`confluence.rs`)
- Implement termination checking integration (`termination.rs`)
- Implement e-graph joinability tests (`egraph.rs`)
- Implement theory morphism verification for composed languages (`morphism.rs`)
- **Verify**: `cargo test -p languages --features trs-analysis`

### Phase 8: Tier 2 — CEK Runtime Analysis
- Implement abstract CESK state coverage (`abstract_cesk.rs`)
- Implement CEGAR counterexample generation (`cegar.rs`)
- Implement green thread interleaving tests (`green_thread.rs`)
- **Verify**: `cargo test -p languages --features cek-runtime`

### Phase 9: Tier 3 — Structure Analysis
- Implement tree automaton coverage (WTA acceptance, hot-path)
- Implement VPA nesting verification (balance, negative tests)
- Implement nominal automata freshness tests
- Implement parity tree automata (mu-calculus model checking)
- **Verify**: `cargo test -p languages --features structure-analysis`

### Phase 10: Tier 4 — Process/Concurrency Analysis
- Implement Petri net reachability (deadlock detection)
- Implement multi-tape synchronization tests
- Implement two-way transducer join pattern analysis
- **Verify**: `cargo test -p languages --features process-analysis`

### Phase 11: Tier 5 — Symbolic Analysis
- Implement SFA guard analysis (satisfiability, overlap, minterm coverage)
- Implement SFT composition tests
- Implement Presburger arithmetic (numeric guard tests)
- Implement register automata (data-equality tests)
- Implement KAT Hoare triple verification
- **Verify**: `cargo test -p languages --features symbolic-analysis`

### Phase 12: Tiers 6-8 — Quantitative, Temporal, Algebraic
- Implement CRA resource bound tests
- Implement probabilistic likelihood-guided testing
- Implement provenance path coverage
- Implement LTL/Büchi temporal property tests
- Implement algebraic path analysis
- Implement lattice theory invariant tests
- **Verify**: `cargo test -p languages --features full-analysis`

### Phase 13: Application-Level Testing
- Implement `ProgramTestSuite` builder in `testkit/src/program.rs`
- Implement `program {}` block parsing in `tests {}` AST extension
- Implement `macros/src/gen/test_gen/program_tests.rs` codegen
- Auto-generate structural/semantic/rewrite tests from program source
- Integrate with Petri net (deadlock), LTL/Büchi (temporal), CESK (reachability)
- Add example `program {}` blocks to Rholang and Calculator `tests {}`
- **Verify**: `cargo test -p languages program_` runs application-level tests

### Phase 14: New Automata
- Implement mutation testing automaton (mutation score metric)
- Implement grammar coverage automaton (rule coverage metric)
- Implement counterexample minimizer (AST-aware delta debugging)
- **Verify**: Mutation score and coverage metrics reported in test output

### Phase 15: Predicated Types Stubs (Future)
- Add empty `#[cfg(feature = "predicated-types")]` sections to generated test files
- Add `testkit/src/analytical/guards.rs` placeholder
- Add `testkit/src/properties/guard_properties.rs` placeholder
- Add `AnalyticalConfig.enable_guard_analysis` field
- Add `ProgramTestSuite::with_guard_coverage()` stub
- **Verify**: Compiles with and without `predicated-types` feature

---

## 10. Verification Plan

### Per-Phase
Each phase has a concrete verification step (see above).

### End-to-End
1. `cargo build -p languages` — compiles cleanly
2. `cargo test -p languages` — all generated `#[test]` functions pass (Tier 0 + always-on)
3. `cargo nextest run -p languages` — all tests pass with per-test process isolation
4. `cargo test -p languages calculator` — filters to Calculator tests only
5. `cargo test -p languages prop_roundtrip` — runs only roundtrip property tests
6. `cargo test -p languages -- --ignored` — runs dead-rule tests
7. `cargo test -p languages --features trs-analysis` — Tier 1: confluence + termination + e-graph
8. `cargo test -p languages --features cek-runtime` — Tier 2: CESK + CEGAR + green threads
9. `cargo test -p languages --features structure-analysis` — Tier 3: WTA + VPA + nominal + parity
10. `cargo test -p languages --features process-analysis` — Tier 4: Petri + multi-tape
11. `cargo test -p languages --features symbolic-analysis` — Tier 5: SFA + Presburger + KAT
12. `cargo test -p languages --features full-analysis` — all tiers
13. Compare auto-generated roundtrip coverage against hand-written `roundtrip_tests.rs` — auto should cover all categories, not just `Int`
14. Verify adding a new `language!` automatically gets a full test suite with zero manual writing
15. `cargo test -p testkit` — testkit's own unit tests pass
16. `cargo nextest run -p languages --retries 0` — no flaky tests (deterministic seeds)
17. `cargo test -p languages program_` — application-level program tests pass
18. Verify `ProgramTestSuite` API works from standalone test files (not just `tests { }` block)
19. Verify mutation testing score ≥ 80% for Calculator language
20. Verify grammar coverage ≥ 95% rule exercise rate for all languages
21. Verify `options { termination_check: "warn" }` produces warning output instead of failure
22. Verify `options { confluence_check: "disable" }` omits the test entirely


### Surface filler admission

Surface samples use the same variable-admission predicate as the existing generated unit tests and property strategies.
The sampler selects a variable only when the category receives a parseable automatic variable rule.
Otherwise, the sampler keeps the category's declared ground sample.
A category without either option contributes no invented sample.

The previous sampler checked only the presence of a native type.
This check replaced the empty constructor of a `noadmit` category with an invalid bare identifier.
The repair calls `category_emits_parseable_auto_var` and leaves the sample builders unchanged.
It applies to every declared category.

`SourceRoleVariableAuthority.SurfaceFillerAdmission` defines sample selection and proves five results.
The model and independent kernel checks pass without axioms or unsafe features.
The property `surface_fillers_follow_declared_variable_admission` covers all five results with 64 generated cases.
Each case checks open, `noadmit`, and `data` categories, with or without a declared ground sample.

| Model result | Property observation |
|---|---|
| `admitted_variable_keeps_nonground_sample` | An open category receives the existing variable spelling |
| `denied_variable_preserves_declared_ground` | Closed categories retain their declared constructor spelling |
| `denied_variable_without_ground_is_not_invented` | A closed category without a ground sample has no filler |
| `variable_replacement_requires_admission` | Only the open category replaces its ground sample |
| `native_presence_does_not_imply_variable_authority` | The `noadmit` and `data` cases have no native type but cannot receive a variable |

The generated syntax-wrapping suite checks these samples through the actual Rholang parser.
Its existing coverage checks and failure assertions remain required.

### Compound delimiter returns

The [lexical infix return design](lexical-infix-return.md) maps nine formal results to transition and parser properties.
The tests preserve complete operator trees at compound delimiters and reject malformed frames.


### Isolated prefix operand precedence

Projection isolation parses a declared operand as a separate source span.
The operand must retain its declared binding-power floor, which excludes operators with lower binding power.
An explicit group permits a complete operator expression inside that operand.

The previous projection path parsed every isolated operand with floor zero.
Its later constructor filter recognized simple binary and unary rules but missed method and postfix rules with longer syntax.
Consequently, the facade accepted some sources that the main parser correctly rejected.
For example, a quote declared with `prefix(220)` must reject `@*a.call(empty)` when the method binds below 220.
The complete quoted method requires `@(*a.call(empty))`.

The repair derives the floor from the existing prefix classifier and binding-power table.
A cross-category prefix uses the operand category's operator table.
An explicit `prefix(...)` annotation takes precedence over the inferred floor.
Closed operand frames retain their existing parsing path.

The generated single-result and weighted-result entries share their existing lexer and parser bodies with a bounded entry.
Both token-slice and lexical-graph paths pass the floor to the existing parser.
Their existing complete-input checks reject an unconsumed suffix.
The implementation adds no parser generator or language-specific operator list.

The operand entry uses the existing category-reachability relation from the parser's goal gate.
This relation includes operators and transparent projections that extend an already constructed term.
It excludes prefix edges, which require their token before the operand.
An operator can restrict an operand only when its result can reach the operand category through this relation.

The first bounded-entry repair selected the main parser for every positive floor.
That selection changed quote representatives even when the floor excluded no operator that could return the required category.
The independent `InactivePrefixFloor` grammar reproduces this defect with aliases, transparent groups, a foreign-result operator, and an eligible prefix cohort.
Before the repair, its prefix changed `Group(Quote(Atom("A")))` into `Quote(Atom("A"))`.
The operator-admission check now preserves the existing facade when its precedence behavior is sufficient.

The operand entry follows this procedure:

1. Classify the declared prefix with the existing parser classifier.
2. Derive its operand floor from the explicit annotation or source-category operator table.
3. Select operators whose result can reach the operand category through the existing goal-gate relation.
4. If no selected operator lies below the floor, use the existing facade entry.
5. Otherwise, use the shared main-parser entry with the declared floor.
6. Preserve the returned terms and weights after the existing complete-input check.

`ProjectionIsolation.OperandPrecedence` proves nineteen results about entry selection, payload preservation, complete spans, category admission, and operator admission.
The model abstracts the parser result as an arbitrary payload, which can include terms and weights.
It abstracts category reachability as an admission predicate and does not prove the complete generated parser correct.
The implementation reuses the generator's existing category-reachability computation for both the goal gate and operand selection.

`macros/tests/cross_category_prefix_frame.rs` supplies three properties with 64 generated cases each.
`isolated_prefix_preserves_floor_payload_and_span` varies identifiers, method chains, receivers, and restrictive floors.
`local_prefix_keeps_postfix_outside_its_operand` checks local prefix association through both public parser entries.
`inactive_floor_preserves_isolated_operand_selection` checks exact operand selection, required readings, and ordered weighted results at inactive floors.

| Formal result | Implementation observation |
|---|---|
| `no_operator_excluded_at_zero` | The generator property includes explicit floor zero with both empty and populated operator tables |
| `restriction_has_lower_operator` | Generated prefix metadata requires an admitted operator strictly below the declared floor |
| `admitted_lower_operator_restricts` | A foreign-result operator requires bounded entry when transparent projections return its result to the operand category |
| `rejected_operator_does_not_change_restriction` | The same operator does not require bounded entry without that return path |
| `inactive_floor_admits_every_operator` | The generator property varies both category tables and explicitly includes the minimum operator floor |
| `equal_binding_power_is_admitted` | Floor two retains the lowest operator and exact weighted readings in the independent grammar |
| `zero_floor_preserves_existing_entry` | The bounded zero-floor entry equals the original weighted entry; a declared zero-floor prefix accepts the complete method |
| `empty_table_keeps_existing_entry` | Categories with no admitted operators keep the facade, including positive inferred and explicit floors |
| `inactive_floor_preserves_existing_entry` | The independent prefix preserves the exact isolated operand and its specific grouped reading |
| `restrictive_floor_uses_declared_context` | Both bounded entries and the quote facade reject the ungrouped lower-precedence method |
| `restrictive_floor_preserves_result` | Grouped operands preserve the complete expected tree through bounded and facade entries |
| `restrictive_floor_ignores_unrestricted_result` | Unrestricted success does not make a restrictive prefix accept the same ungrouped source |
| `complete_entry_preserves_payload` | Grouped results preserve the complete ordered terms and weights from the zero-floor entry |
| `incomplete_entry_rejects` | Both bounded entries reject a valid grouped operand followed by an extra identifier |
| `accepted_entry_consumes_the_span` | Complete operands succeed, while corresponding sources with an unconsumed suffix fail |
| `lower_operator_requires_grouping` | Ungrouped method chains fail under the restrictive quote floor |
| `grouping_preserves_operator_reading` | Explicit groups preserve method chains and permit a local prefix to contain a complete method |
| `inactive_floor_preserves_operator_readings` | Floors zero through two preserve exact ordered terms and weights for the independent expression grammar |
| `unrestricted_operand_can_violate_a_prefix_floor` | The zero-floor control accepts the method that the restrictive-floor control rejects |

The generator properties each check 64 additional cases.
`projection_operand_floor_matches_parser_classification` varies category names, precedence ladders, and explicit annotations across the full byte range.
It checks local prefixes, cross-category prefixes, closed frames, empty tables, and floors zero, one, and two.
`operand_floor_uses_existing_result_reachability` varies names, floors, and a two-edge transparent return path for a foreign-result operator.

Rholang regression tests retain the original ungrouped quoted-channel witnesses as required rejections.
Grouped positive controls must preserve the enclosing send and produce a stable canonical surface.
The method-quote control compares complete payloads while admitting the grammar's declared quote aliases.
The existing numeral-carrier and query-desugaring assertions remain unchanged.


### Explicit lexer entry context

A lexer mode selects the declared token patterns for the current source position.
A token can push a nested mode or pop back to its caller.
The default mode applies to complete source input.
A fragment inside a named mode requires that mode as its entry context.

The category method `parse_via_wpda_in_lexer_mode(input, mode)` accepts an explicit entry context.
Use `None` for the existing default entry.
Use `Some(name)` for an exact declared mode name.
The method `parse_via_wpda_all_with_weights_in_lexer_mode` retains all results and their weights under the same context.
An unknown mode name is an error.

Named entries reuse the generated lexer tables, lexical graph, and main parser.
They do not add named-mode tokens to the default lexer.
The existing `compute_mode_map` delegates to `compute_mode_map_from` with entry zero.
The generalized scan starts with the selected entry mode and requires that same stack at input end.
A fragment cannot pop its entry mode or leave an unclosed nested mode.
Raw modes retain whitespace as token content.

For example, the independent fixture declares a `body` mode with a text token and a nested character-class mode.
Its `Piece` category can parse a NUL text fragment through `Some("body")`.
The same fragment must fail through the default entry.
A complete document supplies its own opener and closer and uses the default entry.

The scan follows this procedure:

1. Resolve the declared mode name to its existing lexer table identifier.
2. Initialize the mode stack with that identifier.
3. Scan each token with the current mode's existing transition table.
4. Apply the token's declared push or pop action after its source span.
5. Reject a pop that would remove the entry context.
6. Require the original entry context at input end.
7. Pass the resulting lexical graph to the existing parser and complete-input check.

`LexerModeOwnership.EntryContext` proves sixteen laws about the mode stack and layout policy.
The proofs cover entry-context transitions, not arbitrary regular-expression compilation or the entire parser.
Compilation and independent kernel verification pass without axioms or unsafe features.

The runtime property `explicit_mode_entry_preserves_context_and_token_ownership` checks 128 generated cases.
It varies the entry mode, text bytes, Unicode text, whitespace, and nesting depth.
It checks the actual mode map and weighted token scanner.
The macro fixture `modal_fragment_entry` checks the generated lexer and category entries with 64 additional cases.

| Formal result | Implementation observation |
|---|---|
| `initial_mode_is_active` | Every fragment byte receives its selected entry mode |
| `empty_fragment_preserves_entry` | Empty input yields an empty mode map without losing its context |
| `ordinary_token_keeps_context` | Text tokens leave the mode map in the selected mode |
| `nested_region_restores_context` | Balanced nested regions return to the entry context |
| `fragment_cannot_pop_entry` | A closer before or after a text fragment fails |
| `failed_transition_cannot_recover` | Text after an unmatched closer cannot make the scan succeed |
| `completion_requires_original_context` | Balanced fragments pass and incomplete nested fragments fail |
| `unclosed_region_rejects` | An extra unmatched opener fails at input end |
| `raw_mode_preserves_layout` | Raw token ranges retain leading spaces, tabs, and newlines |
| `ordinary_mode_skips_layout` | Whitespace-only input in an ordinary mode produces no tokens |
| `token_ownership_is_independent_of_entry` | Named entries retain their existing token kinds; the default entry still rejects a raw NUL fragment |

Generated round-trip tests must retain the lexical context for every parse of a fragment.
They must require a valid declared context and stable canonical output within that context.
Removing NUL from a strategy or accepting named-mode tokens globally would violate this contract.


Raw collection display uses the same declared mode ownership.
The display generator checks the mode after the preceding captured token and the owner of the following captured token.
When both identify the same raw mode, the repetition retains its exact declared separator and adds no boundary spaces.
The generator also avoids adding grouping parentheses inside that raw payload.
Ordinary-mode collections retain their existing layout.
The generator property `raw_region_spacing_follows_declared_mode_ownership` varies mode names, token names, and the raw flag across 64 cases.
It also rejects mismatched mode boundaries and a preceding pop token as evidence for a raw region.

The independent modal fixture checks multiple text elements with a nested character class between them.
Its byte-for-byte source comparison detects added separator spaces, boundary spaces, or lost whitespace.
The fixture also checks ordinary-mode collections with multiple elements through `ordinary_mode_keeps_collection_boundaries_and_declared_layout`.
This 64-case property preserves the declared constructor, element order, boundary spaces, separator spaces, and complete forest membership.

| Additional formal result | Implementation observation |
|---|---|
| `raw_boundary_adds_no_bytes` | A raw collection adds no spaces beside its opener or closer |
| `ordinary_boundary_preserves_request` | The ordinary-mode collection property retains both requested boundary spaces |
| `raw_separator_preserves_declared_bytes` | Multiple raw elements retain the declared empty separator |
| `ordinary_separator_preserves_layout` | The ordinary-mode collection property retains the existing separator spaces between every pair of elements |
| `raw_frame_preserves_payload` | A complete displayed raw document equals its original source, including Unicode, NUL, and whitespace |

Both generated modal lexer loops consult the declared raw flag before skipping whitespace.
The linear token path and retained-stream path therefore use the same layout policy as the lexical graph.


### Checked traversal stack probes

The runtime stack gate classifies every file in the generated Rholang directory.
The current directory contains 47 files.
The source and binding workers require separate depth probes because ordinary comparison and substitution do not invoke those checked workers.

`ast_checked_binding` closes a variable at the deepest position of a nested list.
An independent loop checks every list wrapper, its arity, and the resulting bound variable's scope, binder index, and name.
The probe then opens the term and checks complete equality with the original term.
Its reservation counter must show work beyond the requested depth.

`ast_checked_source` checks the same nested-list shape with the production source profile.
A second policy delegates every decision to that profile except its refusal of the numeric leaf.
The probe requires that refusal at the exact source ordinal, after all list wrappers.
This control detects a checker that returns success without visiting the complete source.

Both subjects join the existing flat-stack classification and depth ladder.
The gate checks depths 4 through 4,096 and independently classifies the subjects at depth 32,768.
The classifier retains its recursive control and its existing stack limits.
The subject count is 42, including that control.

`iterative_cmp_hash.rs` contains only includes for the separately classified clone, comparison, hash, and checked-binding files.
It has no traversal body and retains an explicit inert census entry.
The census rejects any unclassified file, missing declared file, invalid entry point, or unresolved probe subject.

These additions extend the existing acceptance instrument.
They do not change the generated workers or their established formal contracts and property tests.
