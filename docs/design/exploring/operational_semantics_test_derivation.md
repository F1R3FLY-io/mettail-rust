# Automata-Driven Operational Semantics Test Derivation

## Context

The structural test framework is complete (482 tests pass — unit, equation, rewrite, proptest roundtrip/display/debug/clone, precedence, analytical). But zero tests exercise the **operational semantics** — the actual evaluation behavior specified by HOL `![...]` code blocks, equations, and rewrites in `language!` specs.

The hand-written `calculator.rs` tests demonstrate the pattern (`parse → run_ascent → check normal form`), but they're manual. We need to auto-derive these from the specs using the automata infrastructure, with zero hard-coded assumptions about syntax or semantics.

## Design Principles

1. **Everything derived from the spec** — no hard-coded values, semantics, or syntax assumptions
2. **Full pipeline testing** — expression strings → parse → evaluate → verify (not just AST construction)
3. **Automata-driven** — WPDS, WFST, tree automaton, type system, forward-backward analysis guide generation
4. **Exhaustive and creative** — nested expressions, mixed built-in/non-built-in, edge cases, algebraic properties
5. **Proptest-inspired strategies** — exhaustive small-depth enumeration (SmallCheck), coverage-guided targeting, metamorphic testing, boundary value analysis, equivalence partitioning
6. **Trampolined** — all recursive operations use iterative work-stacks

---

## What's Available at Macro Expansion Time

From `GrammarRule`:
- `label` — constructor name
- `category` — result type
- `rust_code: Option<RustCodeBlock>` — HOL evaluation code (the `syn::Expr` AST)
- `eval_mode: Option<EvalMode>` — `Fold` (constant folding) or `Step` (congruence only)
- `term_context: Option<Vec<TermParam>>` — typed parameters (name + category)
- `syntax_pattern: Option<Vec<SyntaxExpr>>` — concrete user syntax
- `is_right_assoc: bool`

From `LanguageDef`:
- `types` — categories with optional `native_type` (i32, i64, f64, bool, str)
- `terms` — all constructors with above data
- `equations` — algebraic axioms (LHS = RHS with premises)
- `rewrites` — reduction rules (LHS ~> RHS with premises)

From `PipelineAnalysis` (to be extended):
- `dead_rule_labels`, `constructor_weights`, `category_weights`
- **New**: WPDS call graph, depth bounds, cycle classification, reachable rules
- **New**: WFST dispatch coverage (per-token actions and ambiguity flags)
- **New**: Binding power table reference

---

## Architecture

```
macros/src/gen/test_gen/
  mod.rs                              — orchestrator (existing)
  operational_tests/
    mod.rs                            — entry: generate_operational_tests()
    ground_term_enum.rs               — enumerate ground terms per rule from spec
    symbolic_eval.rs                  — mini symbolic evaluator for syn::Expr at macro time
    expr_string_gen.rs                — generate parse→eval→verify test code
    nested_expr_gen.rs                — compose nested/mixed expressions
    cross_category_tests.rs           — cross-category cast and mixed-type tests
    edge_case_gen.rs                  — boundary values, overflow, division-by-zero
    algebraic_property_tests.rs       — derive properties from equations block
    wpds_guided.rs                    — WPDS-guided evaluation path coverage
    wfst_guided.rs                    — WFST-guided parser dispatch verification
    precedence_assoc_tests.rs         — operator precedence + associativity from BP table
    type_preservation.rs              — type preservation across evaluation
```

---

## Module Design

### A. Ground Term Enumeration (`ground_term_enum.rs`)

For each rule with `rust_code`, systematically generate ground (no free variables) input terms.

**Algorithm** (iterative work-stack, not recursive):
1. Build a **leaf bank** per category from the spec:
   - `native_type` → representative values derived from type: `i32` → `[0, 1, -1, 2, 42, i32::MAX, i32::MIN]`; `f64` → `[0.0, 1.0, -1.0, 0.5, 2.5, f64::INFINITY, f64::NEG_INFINITY]`; `bool` → `[true, false]`; `str` → `["", "a", "hello"]`
   - Nullary constructors → included as leaves (e.g., `PZero`, `Err`)
   - **All values derived from the `native_type` declaration in the spec**, not hard-coded per language
2. **Depth-0 terms**: Leaf values for each category
3. **Depth-1 terms**: For each rule with `rust_code`, cross-product of leaf values for each parameter (capped per rule)
4. **Depth-2 terms**: Nest depth-1 results as operands — e.g., `(1 + 2) * 3`, `sin(1.0 + 2.0)`
5. Use **tree automaton** `bottom_up_evaluate()` to verify generated terms are structurally valid
6. Use **WPDS** `compute_depth_bounds()` to cap nesting depth per category

**Output**: `Vec<GroundTerm>` per rule, where:
```rust
struct GroundTerm {
    rule_label: String,
    construction_code: String,  // Rust AST construction (e.g., "Int::AddInt(Box::new(Int::NumLit(1)), ...)")
    param_values: Vec<(String, SymValue)>,  // parameter name → concrete value
    depth: u32,
}
```

### B. Symbolic Evaluator (`symbolic_eval.rs`)

A mini evaluator that interprets `syn::Expr` at macro expansion time to compute expected results.

**Handles** (derived from the actual `rust_code` AST, not hard-coded):
- Binary ops: `+`, `-`, `*`, `/`, `%`, `&&`, `||`, `==`, `!=`, `<`, `>`, `<=`, `>=`
- Unary ops: `-`, `!`
- Method calls: `.pow()`, `.sin()`, `.cos()`, `.exp()`, `.ln()`, `.powf()`, `.len()`, `.concat()`, `.parse()`, `.to_string()`, `.abs()`
- Blocks: `{ expr }`, `{ if cond { then } else { else } }`
- Match expressions: Pattern match on constructors (for cross-category ops)
- Casts: `as u32`, `as f64`, `as i64`

**Uses iterative work-stack** (trampolined):
```rust
enum EvalTask {
    EvalExpr { expr_idx: usize, result_slot: usize },
    ApplyBinOp { op: BinOp, left_slot: usize, right_slot: usize, result_slot: usize },
    ApplyUnaryOp { op: UnOp, operand_slot: usize, result_slot: usize },
    ApplyMethodCall { method: String, receiver_slot: usize, args_slots: Vec<usize>, result_slot: usize },
}
```

**When symbolic evaluation fails** (complex match, unknown method, etc.): falls back to **smoke test** that verifies evaluation completes without panic.

### C. Expression String Generation (`expr_string_gen.rs`)

For each ground term, generate a test that goes through the full pipeline:

```rust
#[test]
fn eval_{lang}_{rule}_{params}() {
    mettail_runtime::clear_var_cache();
    // Construct the term from the spec-derived ground values
    let input_term = {construction_code};
    // Get the expression string via Display (uses the actual parser syntax)
    let input_str = format!("{}", input_term);
    // Parse → Evaluate → Verify
    let lang = {Lang}Language;
    let parsed = lang.parse_term(&input_str).expect("parse should succeed");
    let results = lang.run_ascent(parsed.as_ref()).expect("eval should succeed");
    let nfs: Vec<String> = results.normal_forms().iter().map(|nf| nf.display.clone()).collect();
    assert!(nfs.iter().any(|d| d == "{expected_display}"),
        "{} should evaluate to {}, got {:?}", input_str, "{expected_display}", nfs);
}
```

When symbolic eval produces a known result → assert exact match.
When symbolic eval fails → assert at least one normal form exists (smoke test).

### D. Nested Expression Generation (`nested_expr_gen.rs`)

Go beyond depth-1 — compose expressions that test the evaluation pipeline under nesting:

1. **Homogeneous nesting**: `(1 + 2) + 3`, `((1 + 2) * 3) - 4` — same operator at multiple depths
2. **Heterogeneous nesting**: `sin(1.0 + 2.0)`, `len(concat("a", "b"))`, `int(3.14) + 1` — different operators mixed
3. **Built-in mixed with non-built-in**: `fold`-mode ops nested inside `step`-mode ops and vice versa
4. **Cross-category nesting**: `int(float(1))`, `bool(1 + 2 == 3)` — type casts at multiple levels
5. **Precedence-critical nesting**: `2 + 3 * 4` (= 14, not 20), `2 ^ 3 ^ 2` (= 512, not 64)

**Algorithm**: For each pair of rules where the output category of one matches an input category of another, compose them. The tree automaton validates the composition is well-typed.

### E. Cross-Category Tests (`cross_category_tests.rs`)

Derived from the spec by scanning for:
1. **Cast rules**: Where a parameter's category differs from the result category and there's no `rust_code` (pure embedding)
2. **Cross-category operations**: Where `rust_code` pattern-matches on cast constructors (detected by inspecting `syn::Expr::Match` arms)

Generate:
- Cast roundtrip: `"42"` parsed as Proc → displays as `"42"` → parses back
- Cast + operation: `"42 + 10"` as Proc → evaluates to `"52"`
- Nested casts: `"int(float(42))"` → evaluates to `"42"`
- Mixed-type expressions: `"1 + 2 == 3"` → evaluates to `"true"` (Int arithmetic → Bool comparison)

### F. Edge Case Generation (`edge_case_gen.rs`)

Derived from the spec's `native_type` and `rust_code`:

1. **Boundary values per native type** (derived from type, not hard-coded per language):
   - `i32`/`i64`: `0`, `1`, `-1`, `MAX`, `MIN`, `MAX-1`, `MIN+1`
   - `f64`: `0.0`, `1.0`, `-1.0`, `INFINITY`, `NEG_INFINITY`, `MIN_POSITIVE`, `EPSILON`
   - `bool`: `true`, `false` (exhaustive)
   - `str`: `""`, `"a"`, `" "` (empty, single char, whitespace)

2. **Operation-specific edge cases** (derived by analyzing `rust_code`):
   - Division ops (detected by `/` or `%` in `syn::Expr`): test with denominator `0` — expect either `Err` result or panic-safety
   - Power ops (detected by `.pow()` in method calls): test with exponent `0` (any^0 = 1) and base `0` (0^n = 0)
   - Factorial (detected by factorial pattern in code): test with `0` (0! = 1), `1`, negative (if applicable)
   - Trig functions (detected by `.sin()`, `.cos()` etc.): test with `0.0`, `PI/2`, `PI`
   - String length (detected by `.len()`): test with empty string
   - Type casts: test with values at type boundaries (e.g., `float(i32::MAX)`, `int(NaN)`)

3. **Commutative operations** (derived from equations block or by detecting `a op b` and `b op a` in rewrites): test `a op b == b op a`

### G. Algebraic Property Tests (`algebraic_property_tests.rs`)

**Derive properties from the `equations` and `rewrites` blocks** — these ARE the algebraic axioms:

1. **From equations** (`language.equations`): Each equation `lhs = rhs` with premises defines a testable property. For ground instances:
   - Parse LHS and RHS
   - Evaluate both via `run_ascent`
   - Verify they reach the same normal form (equivalence)

2. **Metamorphic properties** (derived from equation structure):
   - If `a + b = b + a` (commutativity detected): proptest `forall a, b: eval(a+b) == eval(b+a)`
   - If `(a + b) + c = a + (b + c)` (associativity detected): proptest `forall a, b, c: eval((a+b)+c) == eval(a+(b+c))`
   - If `a + 0 = a` (identity detected): proptest `forall a: eval(a+0) == eval(a)`
   - If `a * 0 = 0` (annihilation detected): proptest `forall a: eval(a*0) == eval(0)`

3. **Detection algorithm**: Pattern-match on equation LHS/RHS structure:
   - Commutativity: `f(a, b) = f(b, a)` where same constructor, args swapped
   - Associativity: `f(f(a, b), c) = f(a, f(b, c))` where same constructor nested
   - Identity: `f(a, e) = a` where `e` is a literal/nullary
   - Idempotence: `f(a, a) = a` or `f(f(a)) = f(a)`

4. **From rewrites** (`language.rewrites`): Each rewrite `lhs ~> rhs` is a testable reduction. For ground instances of the LHS, verify the RHS is reachable.

5. **Confluence from rewrite pairs**: For any term with multiple applicable rewrites, verify they reach the same normal form. Use the **e-graph** `check_joinability_egraph()` for this.

### H. WPDS-Guided Evaluation Path Coverage (`wpds_guided.rs`)

**Extend `PipelineAnalysis`** with WPDS-derived data:
- `call_graph_edges: Vec<(String, String)>` — cross-category evaluation edges
- `depth_bounds: HashMap<String, u32>` — max safe test depth per category
- `cycle_categories: Vec<Vec<String>>` — SCCs with evaluation cycles
- `reachable_rules_wpds: HashSet<String>` — truly reachable rules (more precise than WFST)

**Test generation**:
1. For each edge in the call graph, ensure at least one test exercises it
2. Use depth bounds to cap nesting depth (avoid non-termination)
3. For cyclic categories, generate bounded-depth tests with a comment
4. Skip truly unreachable rules (WPDS-verified dead)

### I. WFST-Guided Parser Dispatch Testing (`wfst_guided.rs`)

**Extend `PipelineAnalysis`** with dispatch coverage data:
- `dispatch_entries: HashMap<String, Vec<DispatchEntry>>` — per category, per token: which rules dispatch

**Test generation**:
1. For each unambiguous dispatch: generate an expression starting with that token, verify correct constructor
2. For each ambiguous dispatch: generate expressions that disambiguate via context
3. For each two-token lookahead case: generate expressions exercising the lookahead

### J. Precedence and Associativity Tests (`precedence_assoc_tests.rs`)

**Derived from `BindingPowerTable`** (already computed for Display):

1. **Precedence pairs**: For each pair of operators at different bp levels:
   - `"a low_op b high_op c"` → verify `high_op` binds tighter
   - `"a high_op b low_op c"` → verify `low_op` is the root
   - With concrete values: `"2 + 3 * 4"` → evaluate → verify `14` (not `20`)

2. **Associativity**: For each operator:
   - Left-assoc: `"a op b op c"` → verify `(a op b) op c` structure
   - Right-assoc: `"a op b op c"` → verify `a op (b op c)` structure
   - With concrete values: `"2 ^ 3 ^ 2"` → evaluate → verify `512` (right-assoc: 2^(3^2)=2^9)

3. **Parenthesization override**: `"(2 + 3) * 4"` → verify `20` (parens override precedence)

### K. Type Preservation Tests (`type_preservation.rs`)

For every rule with `rust_code`:
1. Generate a well-typed ground term
2. Evaluate it
3. Verify the result is in the same category
4. For native types: verify `try_eval()` returns `Some`

---

## Proptest-Inspired Strategies

Beyond concrete test cases, generate proptest properties:

1. **SmallCheck-style exhaustive enumeration**: For each category with finite leaf domain (e.g., Bool with `[true, false]`), enumerate ALL terms up to depth 2 and verify ALL evaluate correctly

2. **Coverage-guided generation**: Use `parser-coverage` feature to track which dispatch paths are exercised, bias proptest toward uncovered paths

3. **Metamorphic relations**: From detected algebraic properties, generate proptest:
   ```rust
   proptest! {
       fn prop_addint_commutative(a in arb_int(1), b in arb_int(1)) {
           let lang = CalculatorLanguage;
           let ab = format!("{} + {}", a, b);
           let ba = format!("{} + {}", b, a);
           // Both should evaluate to the same normal form
       }
   }
   ```

4. **Shrinking**: Proptest's built-in shrinking finds minimal failing cases via the tape-based strategy

---

## Test Volume Control

- Per-rule cap: max 10 concrete eval tests (configurable)
- Per-language total cap: max 500 operational tests
- Priority by constructor weight (from `PipelineAnalysis.constructor_weights`)
- Hot-path bias from forward-backward analysis
- Deduplication by expression string

## Implementation Phases

1. **Phase 1**: Ground term enumeration + symbolic evaluator + basic eval tests (A + B + C)
2. **Phase 2**: Nested expressions + edge cases (D + F)
3. **Phase 3**: Cross-category + algebraic properties (E + G)
4. **Phase 4**: WFST dispatch + precedence/associativity (I + J)
5. **Phase 5**: WPDS path coverage + type preservation (H + K)
6. **Phase 6**: Proptest metamorphic relations

## Verification

1. `cargo test -p languages` — all existing 482 tests + new operational tests pass
2. Deliberately break a HOL `![...]` block → verify new test catches it
3. Verify Calculator gets eval tests for every arithmetic op
4. Verify RhoCalc gets cross-category cast tests
5. Verify precedence tests catch `2 + 3 * 4 = 14`
6. Verify edge case tests cover division by zero, empty string length, etc.

## Key Files

### New
- `macros/src/gen/test_gen/operational_tests/mod.rs`
- `macros/src/gen/test_gen/operational_tests/ground_term_enum.rs`
- `macros/src/gen/test_gen/operational_tests/symbolic_eval.rs`
- `macros/src/gen/test_gen/operational_tests/expr_string_gen.rs`
- `macros/src/gen/test_gen/operational_tests/nested_expr_gen.rs`
- `macros/src/gen/test_gen/operational_tests/cross_category_tests.rs`
- `macros/src/gen/test_gen/operational_tests/edge_case_gen.rs`
- `macros/src/gen/test_gen/operational_tests/algebraic_property_tests.rs`
- `macros/src/gen/test_gen/operational_tests/wpds_guided.rs`
- `macros/src/gen/test_gen/operational_tests/wfst_guided.rs`
- `macros/src/gen/test_gen/operational_tests/precedence_assoc_tests.rs`
- `macros/src/gen/test_gen/operational_tests/type_preservation.rs`

### Modified
- `macros/src/gen/test_gen/mod.rs` — add `pub mod operational_tests;`, call from `generate_test_file()`
- `prattail/src/lib.rs` — extend `PipelineAnalysis` with WPDS/WFST test guidance fields
- `macros/src/gen/syntax/parser/prattail_bridge.rs` — populate new PipelineAnalysis fields

### Reference (read, don't modify)
- `macros/src/ast/grammar.rs` — GrammarRule, RustCodeBlock, EvalMode
- `macros/src/gen/native/eval.rs` — how HOL code generates eval methods
- `macros/src/gen/term_ops/subst.rs` — `collect_category_variants()`, `VariantKind`
- `languages/tests/calculator.rs` — hand-written eval tests (reference pattern)
- `languages/src/calculator.rs` — Calculator spec
- `languages/src/rhocalc.rs` — RhoCalc spec
- `prattail/src/wpds.rs` — WPDS infrastructure
- `prattail/src/wfst.rs` — WFST prediction
- `prattail/src/tree_automaton.rs` — tree automaton
- `prattail/src/forward_backward.rs` — hot path analysis
- `prattail/src/binding_power.rs` — BindingPowerTable
