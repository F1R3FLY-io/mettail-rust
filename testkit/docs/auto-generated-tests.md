# Automatically Generated Test Suites from `language!` Specifications

> *"Testing as a first-class citizen: every `language!` specification automatically
> receives a comprehensive test suite with zero manual effort."*

**Source files:** `macros/src/gen/test_gen/` (all modules)

---

## Table of Contents

1. [Overview](#1-overview)
2. [Test Categories](#2-test-categories)
3. [Tape-Based Term Generation](#3-tape-based-term-generation)
4. [Operational Semantics Derivation](#4-operational-semantics-derivation)
5. [Algebraic Property Detection](#5-algebraic-property-detection)
6. [WFST-Guided Verification](#6-wfst-guided-verification)

---

## 1 Overview

### 1.1 What Is It?

The MeTTaIL test framework is a **compile-time test synthesis engine** embedded
within the `language!` procedural macro. When a language designer writes a
`language!` specification -- defining syntactic categories, grammar rules,
equations, rewrite rules, and operational semantics blocks -- the macro
expansion automatically derives a complete, multi-category test suite alongside
the language implementation. The tests are generated as Rust source code,
spliced directly into the build tree, and compiled by `cargo test`.

### 1.2 What Does It Do?

For a given `language!` specification, the framework generates:

```
    ┌──────────────────────────────────────────────────────────┐
    │                  language! { ... }                       │
    └────────────────────────┬─────────────────────────────────┘
                             │ macro expansion
    ┌────────────────────────▼─────────────────────────────────┐
    │   ┌───────────────┐  ┌──────────────┐  ┌──────────────┐  │
    │   │  Unit tests   │  │ Equation     │  │ Rewrite      │  │
    │   │  (roundtrip)  │  │ tests        │  │ tests        │  │
    │   └───────────────┘  └──────────────┘  └──────────────┘  │
    │   ┌───────────────┐  ┌──────────────┐  ┌──────────────┐  │
    │   │  Proptest     │  │ Operational  │  │ Precedence   │  │
    │   │  strategies   │  │ semantics    │  │ & assoc.     │  │
    │   └───────────────┘  └──────────────┘  └──────────────┘  │
    │   ┌───────────────┐  ┌──────────────┐  ┌──────────────┐  │
    │   │  Cross-cat    │  │ Edge cases   │  │ WFST/WPDS    │  │
    │   │  coercions    │  │ (boundary)   │  │ guided       │  │
    │   └───────────────┘  └──────────────┘  └──────────────┘  │
    │   ┌───────────────┐  ┌──────────────┐                    │
    │   │  Algebraic    │  │ Type         │                    │
    │   │  properties   │  │ preservation │                    │
    │   └───────────────┘  └──────────────┘                    │
    └──────────────────────────────────────────────────────────┘
```

### 1.3 Why Was This Design Chosen?

The design draws on several principles:

**Specification-as-oracle.** The `language!` spec is the single source of truth.
By deriving tests from it, we guarantee that tests faithfully reflect the
intended semantics rather than the programmer's ad-hoc understanding. This
eliminates the "testing the tests" problem where hand-written tests drift out of
sync with the implementation.

**Zero-effort coverage.** Language designers should focus on semantics, not on
writing test boilerplate. Every new constructor, equation, or rewrite rule
automatically receives test coverage. The marginal cost of adding a language
feature includes testing for free.

**Multi-phase architecture.** The generated tests span six phases of increasing
sophistication, from simple roundtrip tests (Phase 1) through
WFST/WPDS-guided path-coverage tests (Phase 5). This stratified approach
ensures that fundamental properties (parsing, display) are verified before
more complex semantic properties (evaluation, algebraic laws).

**Compile-time verification.** Because test generation happens at macro
expansion time, many classes of errors -- dead rules, ambiguous syntax patterns,
unreachable categories -- are detected before a single test runs.

### 1.4 How Does It Work?

The test generation pipeline proceeds as follows:

```
    LanguageDef ──┬── PipelineAnalysis ──┐
                  │                      │
                  ▼                      ▼
    ┌─────────────────────────────────────────────┐
    │          Test Generation Phases             │
    │                                             │
    │   Phase 1: Unit + ground term eval          │
    │   Phase 2: Nested expressions + edge cases  │
    │   Phase 3: Cross-category + algebraic       │
    │   Phase 4: WFST dispatch + precedence       │
    │   Phase 5: WPDS path coverage + type pres.  │
    │   Phase 6: Proptest metamorphic relations   │
    └───────────────────┬─────────────────────────┘
                        │
                        ▼
            Rust source code (#[test] functions)
```

The `PipelineAnalysis` structure carries information derived from the WFST
(Weighted Finite State Transducer) and WPDS (Weighted Pushdown System) analyses
of the grammar, including constructor weights, dead rule labels, category
weights, and unreachable categories. This information guides test prioritization
and coverage allocation.

---

## 2 Test Categories

### 2.1 Unit Tests (Per-Constructor Roundtrip)

**Source:** `macros/src/gen/test_gen/unit_tests.rs`

**What:** One `#[test]` per constructor that verifies the display-parse
roundtrip property: `∀ t : Cat, parse(display(t)) = t` (up to display
equivalence).

**Why:** The roundtrip property is the most fundamental correctness criterion
for any language with a concrete syntax. If `Display` and `Parse` disagree on
the representation of a term, every downstream operation (evaluation, rewriting,
serialization) is suspect.

**How:**

```
    PROCEDURE generate_unit_test(rule, language):
        variant ← classify_variant(rule, language)
        MATCH variant:
            Nullary{label}:
                term ← Cat::label
            Literal{label}:
                term ← Cat::label(default_for_native_type(type))
            Var{label}:
                term ← Cat::label(OrdVar(Var::Free("x")))
            Regular{label, fields}:
                FOR EACH field ∈ fields:
                    child ← construct_leaf_for_category(field.category)
                term ← Cat::label(Box(child₁), ..., Box(childₙ))
            Binder{label, pre_scope, body_cat}:
                body ← construct_leaf_for_category(body_cat)
                term ← Cat::label(pre_scope..., Scope::new(Binder("x"), body))
            Collection{..} | MultiBinder{..}:
                SKIP  -- too complex for static construction

        displayed ← format!("{}", term)
        ASSERT displayed ≠ ""
        IF parse(displayed) succeeds as parsed:
            re_displayed ← format!("{}", parsed)
            ASSERT displayed = re_displayed
```

The leaf-value construction strategy follows a priority ordering:

1. **Literal** -- if the category has a `native_type`, use the type's default
   value (0 for integers, 0.0 for floats, `false` for booleans, `""` for strings)
2. **Nullary** -- if a zero-argument constructor exists, use it
3. **Variable** -- fall back to `OrdVar(Var::Free("x"))`

Dead rules (identified by WFST analysis in `pipeline.dead_rule_labels`) receive
`#[ignore]` annotations. Auto-generated `Var` and `Literal` variants that are
not explicitly defined in the grammar also receive unit tests.

### 2.2 Equation Tests (Symmetry via Ascent)

**Source:** `macros/src/gen/test_gen/equation_tests.rs`

**What:** One `#[test]` per equation declared in the `language!` spec. Verifies
that equation metadata (LHS, RHS strings) is present and well-formed in the
language's metadata table.

**Why:** Equations define the equational theory of the language. While full
equational reasoning is exercised by the Ascent evaluator, these tests serve as
a compile-time sanity check that the equation declarations have been correctly
translated into runtime metadata.

**How:**

```
    PROCEDURE generate_equation_test(equation, i, language):
        IF equation has complex premises (Freshness, ForAll, BehavioralGuard, RelationQuery):
            -- Metadata presence test only; cannot instantiate statically
            EMIT test:
                lang ← LanguageStruct
                -- equation requires complex conditions
        ELSE:
            EMIT test:
                meta ← lang.metadata()
                equations ← meta.equations()
                ASSERT equations.length > i
                eq ← equations[i]
                ASSERT eq.lhs ≠ ""
                ASSERT eq.rhs ≠ ""
```

**Important note:** Equation LHS/RHS strings contain meta-variables (e.g., `N`,
`P`, `Q`, `...rest`) and are *not* concrete terms. The tests deliberately avoid
parsing these strings, as they may cause stack overflow in the parser due to
deeply nested pattern representations.

### 2.3 Rewrite Tests (Rule Firing Verification)

**Source:** `macros/src/gen/test_gen/rewrite_tests.rs`

**What:** One `#[test]` per rewrite rule. Verifies that rewrite metadata is
present, correctly named, and has non-empty LHS/RHS patterns.

**Why:** Rewrite rules drive the evaluation semantics. These tests verify the
structural integrity of the rewrite rule database.

**How:** Congruence rules (those with `S ~> T` premises) are marked with
explanatory comments, since they require a triggering context to fire. Dead
rules identified by WFST analysis are similarly annotated.

```
    PROCEDURE generate_rewrite_test(rewrite, i, pipeline, language):
        IF rewrite.is_congruence_rule():
            EMIT test:
                -- congruence rules require triggering context
                lang ← LanguageStruct
        ELSE:
            EMIT test:
                meta ← lang.metadata()
                rewrites ← meta.rewrites()
                ASSERT rewrites.length > i
                rw ← rewrites[i]
                ASSERT rw.name = rewrite.name
                ASSERT rw.lhs ≠ ""
                ASSERT rw.rhs ≠ ""
```

### 2.4 Proptest Strategies (Tape-Based Term Generation)

**Source:** `macros/src/gen/test_gen/strategies.rs`

This category is documented in full in [Section 3](#3-tape-based-term-generation).

**What:** Proptest (Claessen & Hughes, 2000) strategies that generate random
well-typed terms of each syntactic category. These strategies are used by
algebraic property tests (Phase 3b/6) to verify metamorphic relations like
commutativity and associativity over randomly generated inputs.

**Why:** Concrete ground-instance tests cover a small portion of the input space.
Property-based testing exercises the algebraic laws of the language across a
diverse range of term shapes, providing much stronger assurance.

### 2.5 Operational Semantics Tests (Parse → Eval → Verify)

**Source:** `macros/src/gen/test_gen/operational_tests/`

**What:** For each rule with a `rust_code` block (the HOL operational semantics
specification), the framework generates tests that:

1. Construct a ground term from the spec
2. Display it to a string
3. Parse the string back
4. Evaluate via Ascent (the Datalog-based evaluator)
5. Assert the result matches the symbolically evaluated expected value

**Why:** The operational semantics tests close the loop between the declarative
specification (`rust_code` blocks) and the actual evaluation pipeline. They
verify not just that parsing and display work, but that the entire
`construct → display → parse → eval` pipeline produces correct results.

**How:** The generation proceeds in six phases:

| Phase | Name                 | Count Cap | Description                              |
|-------|----------------------|-----------|------------------------------------------|
| 1     | Ground term eval     | ∞         | Basic `construct → eval → verify`        |
| 2a    | Nested expressions   | 50        | Depth-2 compositions (e.g., `1 + 2 * 3`) |
| 2b    | Edge cases           | 80        | Boundary values, boolean exhaustion      |
| 3a    | Cross-category       | 200       | Cast chains, mixed-type expressions      |
| 3b    | Algebraic properties | 30        | Commutativity, associativity, identity   |
| 4a    | WFST dispatch        | 60        | Weight-prioritized pipeline tests        |
| 4b    | Precedence/assoc.    | 40        | Binding power verification               |
| 5a    | WPDS path coverage   | 40        | Category-proportional path tests         |
| 5b    | Type preservation    | 50        | `eval(t) : Cat` for all rules            |

Test names are deduplicated: if two phases produce a test with the same name,
a numeric suffix (e.g., `_2`, `_3`) is appended.

### 2.6 Precedence and Associativity Tests

**Source:** `macros/src/gen/test_gen/operational_tests/precedence_assoc_tests.rs`

**What:** Tests derived from the `BindingPowerTable` that verify:
- Higher-precedence operators bind tighter (e.g., `2 + 3 * 4 = 14` not `20`)
- Left-associative chaining (e.g., `10 - 3 - 2 = 5` not `9`)
- Right-associative chaining (e.g., `2 ^ 3 ^ 2 = 512` not `64`)
- Parenthesization overrides (e.g., `(2 + 3) * 4 = 20`)

**Why:** Binding power assignment is one of the most error-prone aspects of
parser generation. These tests verify that the Pratt parser's binding power
table (computed by `analyze_binding_powers()`) correctly implements the
precedence and associativity declared in the spec.

**How:**

```
    PROCEDURE generate_precedence_tests(language):
        spec ← language_def_to_spec(language)
        bp_table ← analyze_binding_powers(spec)
        ops_by_cat ← collect_infix_ops(bp_table, language)

        FOR EACH category, ops ∈ ops_by_cat:
            (a, b, c) ← get_three_values(category)
            FOR EACH pair (low_op, high_op) WHERE low_op.bp < high_op.bp:
                -- Precedence test: "a low_op b high_op c"
                -- high_op should bind tighter → eval as a low_op (b high_op c)
                expected ← symbolic_eval(low_op(a, high_op(b, c)))
                EMIT test: parse("a low b high c") → expected

                -- Parenthesization override: "(a low_op b) high_op c"
                expected ← symbolic_eval(high_op(low_op(a, b), c))
                EMIT test: parse("(a low b) high c") → expected

            FOR EACH op:
                -- Associativity test: "a op b op c"
                IF op.is_right_assoc:
                    expected ← symbolic_eval(op(a, op(b, c)))
                ELSE:
                    expected ← symbolic_eval(op(op(a, b), c))
                EMIT test: parse("a op b op c") → expected
```

Power/exponentiation operators are excluded from precedence tests because
the combination of two operations (e.g., `a + b ^ c`) easily causes integer
overflow. Results exceeding |1,000,000| are also filtered out as a safety
guard.

### 2.7 Cross-Category Coercion Tests (Cast Chains)

**Source:** `macros/src/gen/test_gen/operational_tests/cross_category_tests.rs`

**What:** Tests verifying that cross-category operations (casts, type
conversions, mixed-type expressions) work correctly through the full pipeline.

**Why:** Languages with multiple syntactic categories (e.g., `Int`, `Float`,
`Bool`, `Proc`) require coercion rules to move values between categories. These
rules form a directed graph, and the tests verify that:
- Single-hop casts work (A → B)
- Roundtrip casts produce valid terms (A → B → A)
- Multi-hop chains compose correctly (A → B → C)
- Cast values interoperate with native operations (`sin(float(42))`)

**How:** The cast graph is constructed by scanning the grammar for rules where
a parameter's category differs from the result category:

```
    ┌─────┐  IntToFloat   ┌───────┐
    │ Int │──────────────▶│ Float │
    └─────┘               └───────┘
       ▲    FloatToInt      │
       └────────────────────┘
```

Five sub-strategies are generated:

1. **1A-i: Single-hop casts** -- one test per cast edge
2. **1A-ii: Roundtrip casts** -- for each (A→B, B→A) pair
3. **1A-iii: Multi-hop chains** -- length-2 paths via BFS
4. **1B: Cast-op composites** -- `eval_rule(cast(leaf))`
5. **1C: Mixed-type nested** -- `binary_op(cast(leafA), leafB)` and vice-versa

### 2.8 Edge Case Generation (Boundary Values from Native Types)

**Source:** `macros/src/gen/test_gen/operational_tests/edge_case_gen.rs`

**What:** For each rule with `rust_code`, the framework analyzes the
`syn::Expr` AST at macro time to detect dangerous or boundary patterns, then
generates targeted edge-case tests.

**Why:** Arithmetic operations have well-known edge cases (division by zero,
exponent zero, boolean exhaustion, empty strings, integer MIN/MAX). By detecting
these patterns from the code itself, the framework generates tests that exercise
precisely the dangerous paths.

**Detected Patterns:**

| Pattern          | Detection Criterion                             | Generated Test                     |
|------------------|-------------------------------------------------|------------------------------------|
| `PowerEdge`      | `.pow()` or `.powf()` in expression             | Exponent = 0 (should give 1)       |
| `BoolExhaustive` | `&&`, `\|\|`, `&`, `\|`, `^`, `!` in expression | All 2^n boolean combinations       |
| `EmptyString`    | `.len()`, `.trim()`, `.contains()`, etc.        | String params = `""`               |
| `IntBoundary`    | Integer parameters present                      | `i32::MAX`, `i32::MIN` (when safe) |

**Note:** Division by zero (`DivByZero`) tests are *not* generated because
Rust's integer division by zero causes a panic that aborts the test runner.
Integer boundary tests are only generated for rules without overflow risk
(checked by scanning for `pow`, `product`, `checked_mul`, multiplication, and
bit-shift operations).

The edge pattern detector walks the `syn::Expr` AST using an iterative
work-stack:

```
    PROCEDURE detect_edge_patterns(expr):
        stack ← [expr]
        flags ← {div: false, pow: false, bool: false, string: false}

        WHILE stack is non-empty:
            e ← stack.pop()
            MATCH e:
                Binary(op, left, right):
                    IF op ∈ {Div, Rem}: flags.div ← true
                    IF op ∈ {And, Or, BitAnd, BitOr, BitXor}: flags.bool ← true
                    stack.push(left); stack.push(right)
                MethodCall(method, receiver, args):
                    IF method ∈ {"pow", "powf", "powi"}: flags.pow ← true
                    IF method ∈ {"len", "trim", "contains", ...}: flags.string ← true
                    stack.push(receiver); stack.push_all(args)
                Paren(inner) | Group(inner) | Unary(_, inner) | Cast(inner, _):
                    stack.push(inner)
                Block(stmts):
                    FOR EACH Expr stmt ∈ stmts: stack.push(stmt)
                If(cond, then, else):
                    stack.push(cond)
                    FOR EACH Expr stmt ∈ then: stack.push(stmt)
                    IF else exists: stack.push(else)
                _: CONTINUE

        RETURN detected patterns from flags
```

### 2.9 Analytical Tests (Confluence, Termination)

While full confluence and termination analysis is not yet implemented in the
test generator, the framework lays the groundwork:

- **Dead rule detection** (via WFST analysis) identifies rules that can never
  fire, which is a necessary condition for local confluence analysis.
- **Constructor weight ordering** provides a natural measure function for
  termination arguments -- if every rewrite step reduces the total weight of
  the term, termination is guaranteed.
- **Type preservation tests** (Phase 5b) verify that evaluation preserves
  the syntactic category, which is a key invariant for subject reduction proofs.

---

## 3 Tape-Based Term Generation

**Source:** `macros/src/gen/test_gen/strategies.rs`

### 3.1 What Is It?

A stack-safe alternative to proptest's `prop_recursive` combinator for
generating random well-typed terms of arbitrary depth.

### 3.2 What Does It Do?

It produces a `BoxedStrategy<Cat>` for each syntactic category `Cat`. When
proptest samples a test case, it generates a flat `Vec<u8>` "instruction tape"
and interprets it iteratively to build a term.

### 3.3 Why Was It Chosen?

The standard approach for recursive types in proptest is `prop_recursive`:

```rust
// This causes stack overflow for deeply nested terms!
fn arb_int() -> BoxedStrategy<Int> {
    prop_oneof![
        Just(Int::Zero),
        any::<i32>().prop_map(Int::Lit),
    ].prop_recursive(8, 256, 16, |inner| {
        (inner.clone(), inner.clone())
            .prop_map(|(a, b)| Int::Add(Box::new(a), Box::new(b)))
    }).boxed()
}
```

This creates recursive strategy chains that overflow the call stack on deeply
nested terms. The tape-based approach eliminates all recursion:

- **No recursive function calls** -- cross-category references push tasks onto
  the same work-stack
- **Proptest shrinking works naturally** -- a shorter tape produces a simpler
  term (Claessen & Hughes, 2000)
- **Bounded depth** -- the `max_depth` parameter controls maximum nesting

### 3.4 How Does It Work?

The pipeline has three stages:

```
    ┌───────────────┐     ┌───────────────┐     ┌──────────────┐
    │ TapeReader    │────▶│ BuildTask     │────▶│ AnyTerm      │
    │ (Vec<u8>)     │     │ work-stack    │     │ slots        │
    └───────────────┘     └───────────────┘     └──────────────┘
```

#### 3.4.1 The TapeReader

The `TapeReader` is a cursor over the raw byte tape:

```
    STRUCTURE TapeReader:
        tape: byte array
        pos: integer (initially 0)

        PROCEDURE next_byte() → byte:
            IF tape is empty: RETURN 0
            b ← tape[pos MOD tape.length]
            pos ← pos + 1
            RETURN b

        PROCEDURE next_u32() → u32:
            RETURN next_byte()
                 | (next_byte() << 8)
                 | (next_byte() << 16)
                 | (next_byte() << 24)

        PROCEDURE next_i32() → i32: RETURN next_u32() as i32
        PROCEDURE next_i64() → i64: RETURN next_u32() | (next_u32() << 32)

        PROCEDURE next_f64() → f64:
            bits ← next_i64() as u64
            val ← f64::from_bits(bits)
            IF val is NaN or Inf: RETURN 0.0
            ELSE: RETURN val

        PROCEDURE next_bool() → bool: RETURN next_byte() & 1 = 1

        PROCEDURE next_string() → String:
            len ← next_byte() MOD 8
            RETURN string of `len` chars from 'a' + (next_byte() MOD 26)
```

The tape wraps around when exhausted, ensuring that any tape length produces a
valid term. NaN and infinity values are mapped to 0.0 to avoid issues with
`Eq`/`Ord` implementations.

#### 3.4.2 The Heterogeneous Term Wrapper

```
    ENUM AnyTerm:
        WrapInt(Int)
        WrapFloat(Float)
        WrapBool(Bool)
        ...  -- one variant per category

    -- Typed unwrap helpers:
    AnyTerm.unwrap_int()   → Int   (panics on wrong variant)
    AnyTerm.unwrap_float() → Float
    ...
```

#### 3.4.3 The BuildTask Work-Stack

```
    ENUM BuildTask:
        BuildInt  { depth: u32, slot: usize }
        BuildFloat{ depth: u32, slot: usize }
        BuildBool { depth: u32, slot: usize }
        ...  -- one variant per category
```

#### 3.4.4 The Iterative Builder

```
    PROCEDURE build_from_tape(reader: TapeReader, max_depth: u32) → Cat:
        slots ← [None, None, ...]  -- Vec<Option<AnyTerm>>, preallocated
        next_slot ← 0
        stack ← [BuildCat{depth: max_depth, slot: 0}]
        next_slot ← 1

        WHILE stack is non-empty:
            task ← stack.pop()
            MATCH task:
                BuildCat{depth, slot}:
                    IF depth = 0:
                        -- Must choose a leaf constructor
                        choice ← reader.next_byte() MOD leaf_count
                        MATCH choice:
                            0 → slots[slot] ← AnyTerm::WrapCat(Cat::Lit(reader.next_i32()))
                            1 → slots[slot] ← AnyTerm::WrapCat(Cat::Zero)
                            ...
                    ELSE:
                        -- May choose leaf or recursive constructor
                        choice ← reader.next_byte() MOD (leaf_count + recursive_count)
                        IF choice < leaf_count:
                            -- same as depth = 0
                        ELSE:
                            -- Recursive constructor: allocate child slots
                            child_slot_a ← next_slot; next_slot ← next_slot + 1
                            child_slot_b ← next_slot; next_slot ← next_slot + 1
                            -- Push assembly instruction first (LIFO: runs last)
                            -- (encoded in the result extraction below)
                            -- Push child tasks (LIFO: children built before parent)
                            stack.push(BuildCatA{depth: depth-1, slot: child_slot_a})
                            stack.push(BuildCatB{depth: depth-1, slot: child_slot_b})
                            -- After children are built, assemble parent:
                            slots[slot] ← assemble(constructor, child_slots)

        RETURN slots[0].unwrap_cat()
```

**Key insight:** because the stack is LIFO, pushing child tasks *after* the
assembly instruction ensures children are fully built before the parent reads
their slots. Cross-category references (e.g., an `Int` field inside a `Bool`
constructor) push a `BuildInt{...}` task onto the same work-stack -- no
recursive function calls.

#### 3.4.5 Variant Classification

Each category's constructors are classified into **leaves** and **recursive**:

| Variant Kind | Leaf? | Build Code |
|-------------|-------|------------|
| Nullary | Yes | Direct construction |
| Literal | Yes | Read from tape via `next_T()` |
| Var | Yes | Choose from `["a","b","c","x","y","z"]` |
| Regular | Recursive | Allocate slots for fields, push child tasks |
| Collection | Recursive | Read element count from tape, push element tasks |
| Binder | Recursive | Allocate body slot, push body task |
| MultiBinder | Recursive | Like Binder with `Vec<Binder>` |

If a category has no natural leaves (no nullary constructors, no native type),
a variable leaf is fabricated as a fallback.

#### 3.4.6 Why Shrinking Works

Proptest generates the tape as `proptest::collection::vec(any::<u8>(), 1..max_size)`.
When a test fails, proptest shrinks the tape by:

1. Reducing the tape length (fewer bytes → fewer constructor choices)
2. Reducing individual byte values (smaller bytes → earlier constructors,
   typically leaves)

Both operations produce simpler terms, converging toward a minimal failing
example. This is exactly the property described by Claessen & Hughes (2000):
generators that map from a flat representation inherit the shrinking behavior
of that representation.

#### 3.4.7 The Proptest Blocks

The generated proptest blocks use the tape strategies for metamorphic testing:

```
    proptest! {
        #[test]
        fn roundtrip_int(term in arb_int(5)) {
            let displayed = format!("{}", term);
            if let Ok(parsed) = Int::parse(&displayed) {
                let re_displayed = format!("{}", parsed);
                prop_assert_eq!(displayed, re_displayed);
            }
        }
    }
```

For categories with binders (where variable identity may differ after a
display-parse roundtrip), the strategy falls back to display-string comparison
rather than structural `PartialEq`.

---

## 4 Operational Semantics Derivation

**Source:** `macros/src/gen/test_gen/operational_tests/symbolic_eval.rs`,
`ground_term_enum.rs`, `expr_string_gen.rs`

### 4.1 What Is It?

A compile-time symbolic evaluator that interprets `syn::Expr` AST nodes from
the `rust_code` blocks of grammar rules to compute expected values for tests.

### 4.2 What Does It Do?

Given a grammar rule like:

```rust
AddInt(a: Int, b: Int) -> Int ![a + b]
```

and ground values `a = 2, b = 3`, the symbolic evaluator computes the expected
result `5` at macro expansion time, enabling the test framework to generate
assertion-based tests rather than mere smoke tests.

### 4.3 Why Was It Chosen?

**Smoke tests vs. assertion tests.** A smoke test verifies only that evaluation
produces *some* result. An assertion test verifies the result is *correct*.
The symbolic evaluator upgrades smoke tests to assertion tests whenever possible.

**Graceful degradation.** When the expression is too complex for macro-time
evaluation (match expressions, closures, iterator chains), the evaluator
returns `None` and the test generator falls back to a smoke test. This ensures
the framework never generates incorrect expected values.

### 4.4 How Does It Work?

The evaluator uses a **continuation-passing trampoline** with two stacks:

```
    PROCEDURE symbolic_eval(expr, env) → Option<SymValue>:
        work_stack ← [Eval(expr)]
        value_stack ← []

        WHILE work_stack is non-empty:
            item ← work_stack.pop()
            MATCH item:
                Eval(expr):
                    MATCH expr:
                        Lit(literal):
                            value_stack.push(eval_lit(literal))
                        Path(ident):
                            value_stack.push(env.lookup(ident))
                        Binary(op, left, right):
                            work_stack.push(ApplyBinary(op))
                            work_stack.push(Eval(left))
                            work_stack.push(Eval(right))
                        Unary(op, operand):
                            work_stack.push(ApplyUnary(op))
                            work_stack.push(Eval(operand))
                        MethodCall(method, receiver, args):
                            work_stack.push(ApplyMethodCall(method, |args|))
                            work_stack.push(Eval(receiver))
                            FOR arg ∈ args IN REVERSE:
                                work_stack.push(Eval(arg))
                        Cast(inner, target_type):
                            work_stack.push(ApplyCast(target_type))
                            work_stack.push(Eval(inner))
                        If(cond, then, else):
                            cond_val ← symbolic_eval(cond, env)  -- nested call
                            IF cond_val = Some(Bool(true)): work_stack.push(Eval(then))
                            ELIF cond_val = Some(Bool(false)): work_stack.push(Eval(else))
                            ELSE: value_stack.push(None)
                        Match | Closure | Call | Index | Field | Tuple | Array:
                            value_stack.push(None)  -- too complex

                ApplyBinary(op):
                    left ← value_stack.pop()
                    right ← value_stack.pop()
                    value_stack.push(apply_binary(op, left, right))

                ApplyUnary(op):
                    operand ← value_stack.pop()
                    value_stack.push(apply_unary(op, operand))

                ApplyMethodCall(method, arg_count):
                    receiver ← value_stack.pop()
                    args ← pop arg_count values from value_stack
                    value_stack.push(apply_method(method, receiver, args))

                ApplyCast(target_type):
                    val ← value_stack.pop()
                    value_stack.push(apply_cast(val, target_type))

        RETURN value_stack.pop()
```

The `SymValue` domain:

```
    ENUM SymValue:
        Int(i64)       -- all integer types widened to i64
        Float(f64)     -- all float types widened to f64
        Bool(bool)
        Str(String)
        Unknown        -- cannot be determined
```

**Supported operations:**

| Category   | Operations                                                                                                         |
|------------|--------------------------------------------------------------------------------------------------------------------|
| Arithmetic | `+`, `-`, `*`, `/`, `%` (wrapping semantics for integers)                                                          |
| Comparison | `==`, `!=`, `<`, `>`, `<=`, `>=`                                                                                   |
| Logical    | `&&`, `\|\|`, `&`, `\|`, `^`, `!`                                                                                  |
| Bitwise    | `&`, `\|`, `^`, `<<`, `>>`                                                                                         |
| Methods    | `pow`, `powf`, `sin`, `cos`, `exp`, `ln`, `sqrt`, `abs`, `len`, `max`, `min`, `clone`, `get`, `to_string`, `parse` |
| Casts      | All numeric type conversions (`i32 as f64`, `f64 as i32`, etc.)                                                    |

### 4.5 Ground Term Enumeration

**Source:** `ground_term_enum.rs`

Ground terms are enumerated by building a **leaf bank** -- a map from category
names to representative values -- then computing cross-products:

```
    PROCEDURE enumerate_ground_terms(language) → Vec<GroundTerm>:
        leaf_bank ← build_leaf_bank(language)
        terms ← []

        FOR EACH rule WITH rust_code:
            params ← extract_simple_params(rule)
            IF params is empty:
                terms.push(GroundTerm{rule.label, Cat::Label})
                CONTINUE

            param_leaves ← FOR EACH (name, cat) ∈ params:
                leaf_bank[cat]  -- list of LeafValue

            IF any param has no leaves: SKIP

            -- Cross-product (capped: 5 leaves/param, 20 terms/rule)
            FOR EACH combination ∈ cross_product(param_leaves):
                construction ← Cat::Label(Box(leaf₁), ..., Box(leafₙ))
                terms.push(GroundTerm{rule.label, construction, ...})

        RETURN terms
```

Representative values are derived from the native type:

| Type     | Values                                        |
|----------|-----------------------------------------------|
| `i32`    | 0, 1, 2, 5 (and -1 if prefix negation exists) |
| `f64`    | 0.0, 1.0, 0.5, 2.0, 2.5                       |
| `bool`   | true, false                                   |
| `String` | `""`, `"a"`, `"hello"`                        |

### 4.6 The Fallback: Smoke Tests

When symbolic evaluation returns `None`, the test degrades to a smoke test:

```
    #[test]
    fn eval_calculator_factorial_5_smoke() {
        let input_term = Int::Factorial(Box::new(Int::NumLit(5)));
        let input_str = format!("{}", input_term);
        let lang = CalculatorLanguage;
        let parsed = lang.parse_term(&input_str).expect("parse should succeed");
        let results = lang.run_ascent(parsed.as_ref()).expect("eval should succeed");
        assert!(!results.normal_forms().is_empty(),
            "{} should evaluate to at least one normal form", input_str);
    }
```

This verifies the full pipeline without asserting a specific value -- useful for
complex operations (iterators, pattern matching, closures) that the symbolic
evaluator cannot handle.

---

## 5 Algebraic Property Detection

**Source:** `macros/src/gen/test_gen/operational_tests/algebraic_property_tests.rs`

### 5.1 What Is It?

A pattern-matching algorithm that scans the `equations` section of a
`language!` specification to detect algebraic properties: commutativity,
associativity, and identity elements.

### 5.2 What Does It Do?

For each detected property, the framework generates:
- **Concrete ground-instance tests** verifying the property for specific values
- **Proptest metamorphic blocks** verifying the property for randomly generated
  terms

### 5.3 Why Was It Chosen?

Algebraic properties are the fundamental laws governing term equivalence. If
`AddInt` is declared commutative but the evaluator does not respect this, the
language's equational theory is broken. Detecting these properties from the
equation declarations (rather than hard-coding them) ensures that the tests
track the specification.

### 5.4 How Does It Work?

#### 5.4.1 The Pattern AST

Equations are represented as `Pattern` trees with `PatternTerm` nodes:

```
    ENUM Pattern:
        Term(PatternTerm)
        ...

    ENUM PatternTerm:
        Apply { constructor: Ident, args: Vec<Pattern> }
        Var(Ident)
        ...
```

#### 5.4.2 Commutativity Detection

**Definition:** A binary constructor `f` is commutative if the equation
`f(a, b) = f(b, a)` exists, where `a ≠ b` and both are pattern variables.

```
    PROCEDURE detect_commutativity(equation) → Option<AlgebraicProperty>:
        (lhs_ctor, lhs_args) ← extract_apply(equation.left)?
        (rhs_ctor, rhs_args) ← extract_apply(equation.right)?

        IF lhs_ctor ≠ rhs_ctor: RETURN None
        IF |lhs_args| ≠ 2 OR |rhs_args| ≠ 2: RETURN None

        la ← extract_var_name(lhs_args[0])?
        lb ← extract_var_name(lhs_args[1])?
        ra ← extract_var_name(rhs_args[0])?
        rb ← extract_var_name(rhs_args[1])?

        -- Commutativity: f(a,b) = f(b,a)
        IF la = rb AND lb = ra AND la ≠ lb:
            RETURN Some(Commutativity{equation.name, lhs_ctor, la, lb})
        RETURN None
```

#### 5.4.3 Associativity Detection

**Definition:** A binary constructor `f` is associative if the equation
`f(f(a, b), c) = f(a, f(b, c))` exists.

```
    PROCEDURE detect_associativity(equation) → Option<AlgebraicProperty>:
        (lhs_ctor, lhs_args) ← extract_apply(equation.left)?
        (rhs_ctor, rhs_args) ← extract_apply(equation.right)?

        IF lhs_ctor ≠ rhs_ctor OR |lhs_args| ≠ 2 OR |rhs_args| ≠ 2:
            RETURN None

        -- LHS must be f(f(a,b), c)
        (inner_ctor, inner_args) ← extract_apply(lhs_args[0])?
        IF inner_ctor ≠ lhs_ctor OR |inner_args| ≠ 2: RETURN None
        a ← extract_var_name(inner_args[0])?
        b ← extract_var_name(inner_args[1])?
        c ← extract_var_name(lhs_args[1])?

        -- RHS must be f(a, f(b,c))
        ra ← extract_var_name(rhs_args[0])?
        (rhs_inner_ctor, rhs_inner_args) ← extract_apply(rhs_args[1])?
        IF rhs_inner_ctor ≠ rhs_ctor OR |rhs_inner_args| ≠ 2: RETURN None
        rb ← extract_var_name(rhs_inner_args[0])?
        rc ← extract_var_name(rhs_inner_args[1])?

        IF a = ra AND b = rb AND c = rc:
            RETURN Some(Associativity{equation.name, lhs_ctor, a, b, c})
        RETURN None
```

#### 5.4.4 Identity Detection

**Definition:** A binary constructor `f` has identity element `e` if
`f(a, e) = a` or `f(e, a) = a`, where `e` is a nullary constructor or literal.

```
    PROCEDURE detect_identity(equation) → Option<AlgebraicProperty>:
        (lhs_ctor, lhs_args) ← extract_apply(equation.left)?
        IF |lhs_args| ≠ 2: RETURN None
        rhs_var ← extract_var_name(equation.right)?

        -- Case 1: f(a, e) = a
        IF extract_var_name(lhs_args[0]) = rhs_var:
            identity ← extract_nullary_or_literal(lhs_args[1])?
            RETURN Some(Identity{equation.name, lhs_ctor, rhs_var, identity})

        -- Case 2: f(e, a) = a
        IF extract_var_name(lhs_args[1]) = rhs_var:
            identity ← extract_nullary_or_literal(lhs_args[0])?
            RETURN Some(Identity{equation.name, lhs_ctor, rhs_var, identity})

        RETURN None
```

#### 5.4.5 Generated Tests

For each detected property, two kinds of tests are generated:

**Concrete tests** use specific ground values:

```
    -- Commutativity of AddInt: eval(2 + 5) should overlap with eval(5 + 2)
    lhs_nfs ← eval(AddInt(2, 5)).normal_forms()
    rhs_nfs ← eval(AddInt(5, 2)).normal_forms()
    ASSERT lhs_nfs ∩ rhs_nfs ≠ ∅
```

**Proptest metamorphic blocks** use randomly generated terms:

```
    proptest! {
        #[test]
        fn comm_addint_proptest(a in arb_int(3), b in arb_int(3)) {
            let lhs = Int::AddInt(Box::new(a.clone()), Box::new(b.clone()));
            let rhs = Int::AddInt(Box::new(b), Box::new(a));
            // eval(lhs) ∩ eval(rhs) ≠ ∅
        }
    }
```

---

## 6 WFST-Guided Verification

**Source:** `macros/src/gen/test_gen/operational_tests/wfst_guided.rs`,
`wpds_guided.rs`

### 6.1 What Is It?

A test prioritization and coverage allocation strategy guided by the WFST
(Weighted Finite State Transducer) and WPDS (Weighted Pushdown System) analyses
of the grammar.

### 6.2 What Does It Do?

- **WFST-guided tests (Phase 4a):** Sort rules by constructor weight (lower
  weight = more frequently used = higher priority). Generate full-pipeline
  smoke tests for the most important constructors first. Also generate
  **disambiguation tests** for rules that share a leading keyword prefix.

- **WPDS-guided tests (Phase 5a):** Allocate test budgets proportionally
  across categories based on category weights. Within each category, prioritize
  constructors by weight.

### 6.3 Why Was It Chosen?

In a language with hundreds of constructors, uniform test allocation wastes
budget on rarely-used rules. WFST/WPDS weights provide a principled,
specification-derived measure of constructor importance. The weights are
computed during the grammar analysis pipeline, so they reflect the actual
structure of the language, not a human's intuition about what is "important."

### 6.4 How Does It Work?

#### 6.4.1 WFST-Guided Dispatch Tests

```
    PROCEDURE generate_wfst_guided_tests(language, pipeline):
        -- Step 1: Filter eligible rules
        eligible ← rules WITH rust_code
                    AND NOT IN dead_rule_labels
                    AND NOT IN ambiguous_prefix_rules

        -- Step 2: Sort by weight (ascending)
        sort eligible BY pipeline.constructor_weights[label]

        -- Step 3: Generate tests in priority order
        FOR EACH rule ∈ eligible (up to 60):
            gt ← first safe ground term for this rule
            EMIT smoke test: construct → display → parse → eval

        -- Step 4: Disambiguation tests
        groups ← group rules BY (category, first_syntax_literal)
        FOR EACH group WITH |members| > 1:
            FOR EACH member:
                EMIT roundtrip smoke test
```

The generated test file includes a **coverage plan comment** showing the
weight ordering:

```
    // WFST-derived test coverage plan
    // Dead rules (skipped):
    //   - UnusedRule
    // Constructor weights (lower = more frequent):
    //   AddInt               weight: 0.1234
    //   MulInt               weight: 0.2345
    //   ...
```

#### 6.4.2 WPDS-Guided Path Coverage

```
    PROCEDURE generate_wpds_guided_tests(language, pipeline):
        -- Step 1: Compute per-category budgets
        FOR EACH category (excluding unreachable):
            score ← 1.0 / category_weight    -- inverse weight
        budgets ← proportional allocation of 40 tests by score

        -- Step 2: Within each category, sort ground terms by constructor weight
        -- Step 3: Take up to `budget` tests per category
```

#### 6.4.3 WFST Compile-Time Verification

Beyond test generation, the WFST data is used for compile-time verification:

- **Dead rule labels** cause unit tests to be annotated with `#[ignore]`,
  signaling to the developer that a grammar rule is unreachable
- **Constructor weights** guide the proptest configuration (more tests for
  high-weight constructors)
- **Category weights** influence the Display implementation's choice of
  parenthesization thresholds

### 6.5 Type Preservation Tests (Phase 5b)

**Source:** `type_preservation.rs`

These tests verify a key property: **evaluation preserves the syntactic
category**. For each rule with `rust_code`:

```
    PROCEDURE generate_type_preservation_test(rule, gt):
        term ← construct(gt)
        displayed ← format("{}", term)
        parsed ← lang.parse_term(displayed)
        results ← lang.run_ascent(parsed)
        ASSERT results.normal_forms() ≠ ∅
        FOR EACH nf ∈ results.normal_forms():
            re_parsed ← lang.parse_term(nf.display)
            ASSERT re_parsed succeeds  -- same category accepts the result
```

This is the runtime analogue of the **subject reduction** property from type
theory: if `t : Cat` and `t →* v`, then `v : Cat`.

---

## References

- Claessen, K. & Hughes, J. (2000). *QuickCheck: A Lightweight Tool for Random
  Testing of Haskell Programs.* Proceedings of the 5th ACM SIGPLAN
  International Conference on Functional Programming (ICFP '00).

- Reps, T., Schwoon, S., Jha, S., & Melski, D. (2005). *Weighted Pushdown
  Systems and their Application to Interprocedural Dataflow Analysis.*
  Science of Computer Programming, 58(1-2), 206-263.

- Mohri, M. (2009). *Weighted Automata Algorithms.* In: Droste, M., Kuich, W.,
  Vogler, H. (eds) Handbook of Weighted Automata. Springer.

- Pratt, V. R. (1973). *Top Down Operator Precedence.* Proceedings of the 1st
  Annual ACM SIGACT-SIGPLAN Symposium on Principles of Programming Languages.
