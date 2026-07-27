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
