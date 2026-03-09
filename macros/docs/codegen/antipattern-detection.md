# Codegen Antipattern Detection

**Source**: [`macros/src/logic/antipattern.rs`](../../src/logic/antipattern.rs)

## 1. Overview / Purpose

The antipattern detection module runs five compile-time lint detectors during
macro expansion. These detectors analyze user-defined `logic {}` blocks,
grammar constructors, and equation/rewrite rules to identify common Ascent
Datalog performance antipatterns that would cause quadratic, cubic, or
unbounded runtime behavior.

Each detector fires independently and produces an `AntipatternWarning` with
a diagnostic code, message, and remediation hint. Warnings are collected by
`detect_antipatterns()` and emitted as grouped lint diagnostics by
`emit_antipattern_lints()` in `mod.rs`.

## 2. Architecture and Data Flow

```
 LanguageDef
     |
     v
 detect_antipatterns(lang)
     |
     +---> detect_cubic_transitivity(lang)       --> C-AP01
     +---> detect_extension_along_equality(lang)  --> C-AP02
     +---> detect_deep_congruence_chains(lang)    --> C-AP03
     +---> detect_unbounded_rewrite_growth(lang)  --> C-AP04
     +---> detect_clone_storm(lang)               --> C-AP05
     |
     v
 Vec<AntipatternWarning>
     |
     v
 emit_antipattern_lints()  -->  LintDiagnostic emissions
```

## 3. Key Types and Functions

### `AntipatternWarning`

```rust
pub struct AntipatternWarning {
    pub code: &'static str,    // "C-AP01" .. "C-AP05"
    pub message: String,       // Human-readable diagnostic
    pub hint: Option<String>,  // Remediation suggestion
}
```

### Public API

| Function               | Returns                   | Purpose                           |
|------------------------|---------------------------|-----------------------------------|
| `detect_antipatterns`  | `Vec<AntipatternWarning>` | Run all 5 detectors on a language |

### Internal Detectors

| Function                           | Antipattern |
|------------------------------------|-------------|
| `detect_cubic_transitivity`        | C-AP01      |
| `detect_extension_along_equality`  | C-AP02      |
| `detect_deep_congruence_chains`    | C-AP03      |
| `detect_unbounded_rewrite_growth`  | C-AP04      |
| `detect_clone_storm`               | C-AP05      |

## 4. Algorithm Description

### C-AP01: Cubic Transitivity Blowup

**Pattern**: `R(x, z) <-- R(x, y), R(y, z)` in user `logic {}` blocks.

**Detection algorithm**:

```
for each rule in parsed_logic_program:
    extract head_clauses: [(relation_name, [arg_exprs])]
    extract body_clauses: [(relation_name, [arg_exprs])]
    for each (head_rel, head_args) in head_clauses:
        if head_args.len() < 2: continue
        same_rel_body = body_clauses filtered by rel == head_rel
        if same_rel_body.len() < 2: continue
        for each pair (b1, b2) in same_rel_body x same_rel_body where b1 != b2:
            if b1[1] == b2[0]          // chain variable
               AND b1[0] == head[0]    // source propagated
               AND b2[1] == head[1]:   // target propagated
                emit C-AP01 warning
                break  // one warning per head clause
```

**Complexity**: The join `R(x,y), R(y,z)` produces O(|R|^3) intermediate
tuples in the worst case. Ascent's semi-naive evaluation cannot avoid this
because the chain variable `y` ranges over the entire domain of R.

**Resolution**: Use `#[ds(crate::eqrel)]` on equivalence relations, or a
transitive-closure operator instead of manual transitivity rules.

### C-AP02: Quadratic Extension-Along-Equality

**Pattern**: `eq_cat(x, y), some_rel(y, z)` in user `logic {}` blocks.

**Detection algorithm**:

```
eq_rels = { "eq_<cat>" for each category } UNION
          { user relations with #[ds(...eqrel...)] attribute }

for each rule in parsed_logic_program:
    body_clauses = extract body clause (relation, args) pairs
    for each pair (clause_a, clause_b) where a != b:
        if clause_a.rel IN eq_rels AND clause_a.args.len() == 2:
            eq_output = clause_a.args[1]
            if eq_output IN clause_b.args AND clause_b.rel NOT IN eq_rels:
                emit C-AP02 warning
```

**Complexity**: For each x, the join iterates over the entire equivalence
class of x to find matching y values, producing O(|class| * |some_rel|)
intermediate tuples.

**Resolution**: Use a canonical representative or inline the equivalence test.

### C-AP03: Deep Congruence Chains

**Pattern**: Self-recursive or deeply nested constructor field graphs.

**Detection algorithm**:

```
1. Build field_graph: category -> set of categories referenced via fields
   (scanning GrammarItem::NonTerminal, Collection, Binder, and term_context)

2. Check for self-loops:
   for each (cat, refs) in field_graph:
       if cat IN refs:
           emit C-AP03 "unbounded depth" warning

3. Compute max chain depth via DFS with cycle detection:
   compute_chain_depth(cat, field_graph, max_depths, visited, on_stack):
       if cat in max_depths: return cached
       if cat in on_stack: return MAX (cycle)
       mark on_stack
       depth = 1 + max(compute_chain_depth(child) for child in refs - {cat})
       unmark on_stack, cache result

4. For categories with depth > 10 (threshold):
   emit C-AP03 warning (unless already warned for self-recursion)
```

**Complexity**: Congruence rules apply recursively at every nesting level,
producing rule application chains exponential in depth.

**Resolution**: Flatten the category hierarchy or bound the rewrite depth.

### C-AP04: Unbounded Term Growth via Rewrite Feedback

**Pattern**: Rewrite rules whose RHS is deeper than LHS (positive depth delta).

**Detection algorithm**:

```
for each rewrite rule:
    lhs_depth = pattern_depth(rewrite.left)
    rhs_depth = pattern_depth(rewrite.right)
    delta = rhs_depth - lhs_depth
    if delta > 0:
        check if any other rewrite has complementary negative delta
        if no complementary rule:
            emit C-AP04 warning
```

This is more targeted than ART05/A01: it specifically flags *rewrite* rules
(not equations) and checks for missing complementary depth-reducing rules.

**Resolution**: Add a complementary depth-reducing rewrite or enable the
runtime depth bound (ART05).

### C-AP05: Clone Storm on Large ASTs

**Pattern**: Constructors with collection fields (Vec, HashBag) that cause
expensive deep clones during congruence rule evaluation.

**Detection algorithm**:

```
for each grammar rule:
    if rule has Collection items:
        estimate clone cost based on:
            - collection nesting depth
            - element type complexity
            - number of collection fields
        if clone_cost > threshold:
            emit C-AP05 warning
```

**Resolution**: Consider structural sharing (e.g., persistent data structures)
or limit congruence propagation through collection constructors.

## 5. Generated Code Patterns

This module does not generate code -- it is purely an analysis and diagnostic
pass. The warnings inform users about patterns in their grammar or logic blocks
that will cause performance problems in the *generated* Ascent code.

### Before (user grammar/logic causing C-AP01):

```
logic {
    reaches(x, z) <-- reaches(x, y), reaches(y, z);
}
```

### After (user applies remediation):

```
logic {
    #[ds(crate::eqrel)]
    relation reaches(Node, Node);
    // ... use built-in transitive closure
}
```

## 6. Integration with Pipeline

The antipattern detectors are invoked from `mod.rs::generate_ascent_source()`
at step 5 of the pipeline, after cancellation pair detection and depth delta
analysis but before code generation begins:

```rust
// C-AP01 through C-AP05: Ascent antipattern detection.
emit_antipattern_lints(language, &grammar_name);
```

The `emit_antipattern_lints()` function in `mod.rs` maps each `AntipatternWarning`
to a `LintDiagnostic` with appropriate severity:

| Code   | Severity | Rationale                             |
|--------|----------|---------------------------------------|
| C-AP01 | Warning  | Cubic blowup, serious performance hit |
| C-AP02 | Warning  | Quadratic blowup                      |
| C-AP03 | Note     | Informational, may be intentional     |
| C-AP04 | Warning  | Potential non-convergence             |
| C-AP05 | Note     | Informational, clone cost awareness   |

## 7. Diagnostic Emissions

| Lint ID | Name                                 | Severity | Trigger                               |
|---------|--------------------------------------|----------|---------------------------------------|
| C-AP01  | `cubic-transitivity-blowup`          | Warning  | Transitivity chain in logic block     |
| C-AP02  | `quadratic-extension-along-equality` | Warning  | Eq-relation join in logic block       |
| C-AP03  | `deep-congruence-chain`              | Note     | Self-recursive or deep category graph |
| C-AP04  | `unbounded-rewrite-growth`           | Warning  | Positive depth delta without complement |
| C-AP05  | `clone-storm-collection-field`       | Note     | Collection field clone cost           |

Diagnostics are collected by `detect_antipatterns()` and emitted in batch
via `emit_collected_diagnostics()` for grouping support.

## 8. Test Coverage

The antipattern detection module is tested indirectly through the full
integration test suite -- when grammars with known antipatterns are compiled,
the diagnostics appear in the build output. Direct unit tests for the
individual detectors would require constructing `LanguageDef` instances
with specific patterns.

The detection algorithms rely on `ascent_syntax_export::parse_ascent_program_tokens`
for C-AP01 and C-AP02 (parsing user logic blocks), and on the `LanguageDef`
grammar structure for C-AP03, C-AP04, and C-AP05.

## 9. Source References

- **Primary source**: [`macros/src/logic/antipattern.rs`](../../src/logic/antipattern.rs) (~490 lines)
- **Invocation site**: [`macros/src/logic/mod.rs`](../../src/logic/mod.rs), `emit_antipattern_lints()`
- **Lint infrastructure**: [`prattail/src/lint.rs`](../../../prattail/src/lint.rs)

## 10. Cross-References

- [equation-system.md](equation-system.md) -- C-AP03 relates to congruence chain depth
- [rule-generation.md](rule-generation.md) -- C-AP04 relates to depth delta analysis (ART05)
- [congruence-closure.md](congruence-closure.md) -- C-AP05 relates to collection congruence cloning
- [`docs/design/codegen-optimization-catalog.md`](../../../docs/design/codegen-optimization-catalog.md) -- catalog entry
