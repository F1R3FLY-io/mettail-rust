# Three-Tier Dead-Rule Detection

**Date:** 2026-03-01

Dead-rule detection identifies grammar rules that can never fire during
parsing and reports them as compile-time warnings.  This document describes
PraTTaIL's three-tier detection architecture, its integration with the
unified lint layer, correctness properties, and practical results.

---

## Table of Contents

1. [Introduction & Motivation](#1-introduction--motivation)
2. [Three-Tier Architecture](#2-three-tier-architecture)
3. [Integration with Unified Lint Layer](#3-integration-with-unified-lint-layer)
4. [Correctness Properties](#4-correctness-properties)
5. [Dead Rules Detected in Practice](#5-dead-rules-detected-in-practice)
6. [Algorithm Complexity](#6-algorithm-complexity)
7. [References](#7-references)

---

## 1. Introduction & Motivation

### Why dead-rule detection matters

Every rule in a parser grammar has a cost: it complicates the dispatch
tables, increases generated code volume, and misleads the grammar author
into believing certain parses are possible when they are not.  Detecting
dead rules at compile time has three benefits:

1. **Correctness feedback** — a rule the author intended to be reachable
   may be shadowed by a higher-priority alternative or rendered unreachable
   by the FIRST-set topology.  The warning reveals the problem.

2. **Code hygiene** — dead rules left over from grammar refactors are
   silent technical debt.  Flagging them prompts cleanup.

3. **Smaller generated code** — although dead rules are *not* automatically
   removed (they may be intentionally present for documentation or future
   use), the warnings help the author decide whether to keep or discard
   them.

### False positives vs false negatives

PraTTaIL's detection is **conservative**: it may miss some dead rules
(false negatives), but it will never flag a live rule as dead (no false
positives).  This design choice mirrors Rust's `#[warn(dead_code)]` lint,
where the compiler accepts silent dead code over noisy false alarms.  The
three-tier structure progressively widens coverage while maintaining this
conservatism.

### Relation to compiler warnings

The dead-rule warning is analogous to Rust's `#[warn(dead_code)]`:

| Rust compiler | PraTTaIL |
|---------------|----------|
| Function never called | Rule never dispatched via any FIRST-set token |
| Struct field never read | Literal rule in category without `native_type` |
| Dead arm in match | Infix rule in category with no reachable prefix |

---

## 2. Three-Tier Architecture

### Decision flow

Every rule in the grammar enters the detection pipeline and is classified
by exactly one tier.  The tiers execute in order; once a rule is handled by
a tier, it does not proceed to subsequent tiers.

```
  Rule
   │
   ▼
  ┌────────────────────────────────┐
  │ Tier 1: Literal rule?          │
  │ (rule_info.is_literal == true) │
  └────────┬───────────────────────┘
           │
     ┌─────┴─────┐
     │yes        │no
     ▼            ▼
  ┌──────────┐  ┌────────────────────────────────────────────┐
  │ Check:   │  │ Tier 2: Same-category infix/var?           │
  │ category │  │ (is_infix && !is_cross_category) || is_var │
  │ has      │  └────────┬───────────────────────────────────┘
  │ native_  │           │
  │ type?    │     ┌─────┴─────┐
  └────┬─────┘     │yes        │no
       │           ▼            ▼
  ┌────┴────┐  ┌──────────┐  ┌──────────────────────────┐
  │no →DEAD │  │ Check:   │  │ Tier 3: WFST reachable?  │
  │yes→LIVE │  │ category │  │ (prefix, cast, cross-cat)│
  └─────────┘  │ reachable│  └────────┬─────────────────┘
               │ ?        │           │
               └────┬─────┘     ┌─────┴─────┐
                    │           │yes        │no
               ┌────┴────┐     ▼            ▼
               │no →DEAD │  ┌──────┐    ┌──────┐
               │yes→LIVE │  │ LIVE │    │ DEAD │
               └─────────┘  └──────┘    └──────┘
```

### Tier 1 — Literal rules (structural check)

**Condition**: `rule_info.is_literal == true`

A literal rule (e.g., `NumLit` mapping `Token::Integer` to an AST node)
is dead if its category has no `native_type`.  Without a `native_type`,
the generated code has no match arm for the literal token, so the rule
can never fire.

**Pseudocode** (from `pipeline.rs:152–165`):

```
for rule_info in rule_infos:
    if rule_info.is_literal:
        has_native = categories
            .any(c → c.name == rule_info.category && c.native_type.is_some())
        if not has_native:
            warn LiteralNoNativeType { rule_info.label, rule_info.category }
        continue   // literal rules do not proceed to tier 2 or 3
```

**Example**:

| Rule | Category | `native_type` | Result |
|------|----------|---------------|--------|
| `NumLit` | `Int` | `Some("i32")` | Live — match arm generated |
| `NumLit` | `Expr` | `None` | Dead — no match arm for `Token::Integer` |

### Tier 2 — Same-category infix/var rules (graph reachability)

**Condition**: `(rule_info.is_infix && !rule_info.is_cross_category) || rule_info.is_var`

An infix rule like `Add: Int + Int` requires that a prefix rule has
already parsed the left operand.  If no prefix rule can start a parse in
that category, the infix rule can never fire.  Likewise, a `var` rule
requires that the category is reachable for identifiers to bind.

The "reachable" check is a fixed-point computation over categories:

**Graph model**: Categories are nodes.  Cross-category and cast rules are
directed edges from source to target.

**Formal definition**:

    R = μX. { C | FIRST(C) ≠ ∅ } ∪ { C | ∃ rule r : r.source ∈ X ∧ r.target = C }

where `r.source` is the first NonTerminal in the rule's syntax items and
`r.target` is `r.category`.

**Pseudocode** (from `pipeline.rs:117–150`):

```
// Seed: categories with non-empty FIRST sets
reachable = { cat | FIRST(cat).tokens ≠ ∅ }

// Fixed-point: propagate via cross-category/cast edges
changed = true
while changed:
    changed = false
    for rule in rule_infos:
        if rule.is_cross_category or rule.is_cast:
            source = first NonTerminal in rule.first_items
            if source ∈ reachable and rule.category ∉ reachable:
                reachable ← reachable ∪ { rule.category }
                changed = true

// Check: infix/var rules in unreachable categories
for rule_info in rule_infos:
    if (rule_info.is_infix && !rule_info.is_cross_category) || rule_info.is_var:
        if rule_info.category ∉ reachable:
            warn UnreachableCategory { rule_info.label, rule_info.category }
        continue   // does not proceed to tier 3
```

**Why infix/var rules are category-dependent**: The Pratt infix loop only
runs after a prefix rule produces a left operand.  If no prefix rule is
reachable in the category, the infix loop never starts.

**Example diagram** — transitive reachability via cast chain:

```
  Int ──cast──→ Float ──cast──→ Str
  ─────
  FIRST(Int) = { Integer }          ← seed: Int reachable
  FIRST(Float) = { Integer }        ← Float reachable via IntToFloat cast
  FIRST(Str) = { Integer, "\"" }    ← Str reachable via FloatToStr cast

  Result: FAdd (infix in Float) is LIVE
          SConcat (infix in Str) is LIVE
```

### Tier 3 — Prefix/cast/cross-category rules (WFST reachability)

**Condition**: all remaining rules (not literal, not same-category
infix/var)

For prefix, cast, and cross-category rules, the detection queries the
prediction WFST directly: is there any token in the category's FIRST set
that dispatches to this rule?

**Pseudocode** (from `pipeline.rs:183–203`):

```
for rule_info in rule_infos:  // (continued from tiers 1 and 2)
    wfst = prediction_wfsts[rule_info.category]
    reachable = FIRST(rule_info.category).tokens
        .any(tok → wfst.predict(tok)
            .any(action → action.rule_label() == rule_info.label))
    if not reachable:
        warn WfstUnreachable { rule_info.label, rule_info.category }
```

This is an **implicit boolean projection**: the predicate
`∨_{T ∈ FIRST(C)} [wfst.predict(T) routes to R]` is equivalent to
projecting each WFST transition weight onto `BooleanWeight` via
`w → BooleanWeight(w ≠ zero)` and computing `plus` (disjunction) across
all transitions.  See `theory/wfst/semirings/boolean-weight.md` for the
formal connection.

**Example**: Cast rule `FloatToStr` in the `Str` category is dead if
the WFST routes every FIRST token to higher-priority alternatives (e.g.,
`StrLit` for `"..."` and `IntToStr` for `Integer`).

---

## 3. Integration with Unified Lint Layer

Dead-rule detection was migrated from inline `eprintln!` calls in
`pipeline.rs` to the unified lint layer in `lint.rs`.  The data flow is:

```
  pipeline.rs: generate_parser_code()
       │
       ▼
  ┌──────────────────────────────────────────────┐
  │ lint::LintContext                             │
  │ { categories, rules, first_sets,             │
  │   prediction_wfsts, ... }                    │
  └──────────────────┬───────────────────────────┘
                     │
                     ▼
  lint::run_lints(&ctx)
       │
       ├─ G01..G10  (grammar structure)
       ├─ W01       (dead-rule) ◄── this lint
       ├─ W02..W06  (WFST-specific)
       ├─ R01..R07  (recovery)
       ├─ C01..C04  (cross-category)
       └─ P02..P04  (performance)
       │
       ▼
  Vec<LintDiagnostic>
       │
       ▼
  lint::emit_diagnostics()  →  stderr
```

### LintDiagnostic structure

```rust
pub struct LintDiagnostic {
    pub id: &'static str,       // "W01"
    pub name: &'static str,     // "dead-rule"
    pub severity: LintSeverity, // Warning
    pub category: Option<String>,
    pub rule: Option<String>,
    pub message: String,
    pub hint: Option<String>,
}
```

### W01 wrapper: `lint_w01_dead_rule()`

The W01 lint function (`lint.rs:786–832`) calls `detect_dead_rules()` and
maps each `DeadRuleWarning` variant to a `LintDiagnostic` with a
variant-specific hint:

| Variant | Hint |
|---------|------|
| `LiteralNoNativeType` | "add a native_type to the category or remove the literal rule" |
| `UnreachableCategory` | "add a prefix rule to make the category reachable" |
| `WfstUnreachable` | "remove the rule or add a unique dispatch token" |

### Diagnostic display format

Output follows Rust compiler conventions:

```text
warning[W01]: literal rule NumLit in category Expr is unreachable (dead code) — category has no native_type
  = hint: add a native_type to the category or remove the literal rule

warning[W01]: rule Add in category Ghost is unreachable (dead code) — category Ghost has no reachable prefix rules
  = hint: add a prefix rule to make the category reachable

warning[W01]: rule FloatToStr in category Str is unreachable (dead code) — no token in FIRST(Str) dispatches to it via prediction WFST
  = hint: remove the rule or add a unique dispatch token
```

---

## 4. Correctness Properties

### No false positives

Each tier uses **necessary conditions** for liveness.  A rule flagged as
dead is provably unreachable:

- **Tier 1**: A literal rule without `native_type` has no generated match
  arm.  This is a definitional property of the codegen — there is no code
  path that can produce the AST node.

- **Tier 2**: The reachable set is a least fixed-point.  It starts with
  all categories that have FIRST tokens (the seed is complete) and closes
  under all cross-category and cast edges (the propagation is
  exhaustive).  If a category is not in the fixed-point, no sequence of
  dispatch actions can enter it.

- **Tier 3**: The FIRST-set scan is exhaustive — every token that can
  begin a parse in the category is checked.  If no token routes to the
  rule, no prefix dispatch can reach it.

### Permitted false negatives

The analysis is intentionally conservative.  Known sources of false
negatives (dead rules not flagged):

- **Infix rules with unreachable operators**: An infix rule `+` in a
  reachable category is classified as live, even if the `+` token is
  never produced by the lexer in practice.  The lexer guarantees all
  operators are lexable, so this is a semantic rather than structural
  property.

- **Rules reachable only via error recovery**: A rule that fires only
  during error recovery (e.g., after token insertion) is not considered
  dead.  Error recovery is best-effort and its paths are not modeled by
  the prediction WFST.

### Monotonicity

Adding rules to the grammar never makes existing live rules dead.
Formally, if rule R is live in grammar G, then R is live in G ∪ {R'} for
any new rule R'.

**Proof sketch**: WFST weights are additive — adding a new rule can only
create new transitions or increase existing transition weights, never
remove transitions.  Category reachability is a least fixed-point, so
adding cast/cross-category edges can only enlarge the reachable set.
Literal liveness depends only on `native_type`, which is a category
property independent of other rules.

---

## 5. Dead Rules Detected in Practice

### By language

| Language | Dead Rules | Tier 1 | Tier 2 | Tier 3 |
|----------|-----------|--------|--------|--------|
| Calculator | 8 | 0 | 0 | 8 |
| RhoCalc | 36 | 0 | 0 | 36 |

### Calculator dead rules (8)

| Rule | Category | Tier | Reason |
|------|----------|------|--------|
| FloatToStr | Str | 3 | Cast shadowed by higher-priority alternatives |
| FloatToBool | Bool | 3 | Cast shadowed by higher-priority alternatives |
| StrToBool | Bool | 3 | Cast shadowed by higher-priority alternatives |
| IntId | Int | 3 | Identity rule shadowed by direct parse |
| FloatId | Float | 3 | Identity rule shadowed by direct parse |
| BoolId | Bool | 3 | Identity rule shadowed by direct parse |
| StrId | Str | 3 | Identity rule shadowed by direct parse |
| POutput | Proc | 3 | Output rule unreachable via prefix dispatch |

### RhoCalc dead rules (36)

The RhoCalc grammar has 36 dead rules, all detected by Tier 3.  These
arise from cross-category comparison operators (e.g., `IntGt`, `FloatGt`,
`IntEq`, etc.) and cast rules where higher-priority direct alternatives
shadow the cross-category path.

### Test coverage

13 unit tests in `tests/warning_tests.rs::dead_rule_tests`:

| Test | Tier | Validates |
|------|------|-----------|
| `test_literal_rule_without_native_type_is_dead` | 1 | Literal in category without `native_type` flagged |
| `test_literal_rule_with_native_type_is_not_dead` | 1 | Literal with `native_type` not flagged |
| `test_infix_rule_in_unreachable_category_is_dead` | 2 | Infix in empty-FIRST category flagged |
| `test_var_rule_in_unreachable_category_is_dead` | 2 | Var in empty-FIRST category flagged |
| `test_infix_rule_in_reachable_category_is_not_dead` | 2 | Infix in reachable category not flagged |
| `test_var_rule_in_reachable_category_is_not_dead` | 2 | Var in reachable category not flagged |
| `test_cross_category_infix_goes_through_wfst_check` | 3 | Cross-cat infix uses WFST (not tier 2) |
| `test_reachable_cross_category_not_flagged` | 3 | Reachable cross-cat rule not flagged |
| `test_dead_cast_rule_flagged` | 3 | Unreachable cast rule flagged |
| `test_reachable_cast_rule_not_flagged` | 3 | Reachable cast rule not flagged |
| `test_category_reachable_transitively_via_cast` | 2 | Transitive cast chain makes category reachable |
| `test_dead_rule_warning_display` | — | Display formatting for all 3 variants |
| `test_mixed_grammar_dead_rules` | 1,2 | Mixed scenario: 3 dead rules across tiers |

---

## 6. Algorithm Complexity

| Tier | Complexity | Description |
|------|-----------|-------------|
| 1 | O(\|rules\|) | Single pass, constant-time check per rule |
| 2 (reachable set) | O(\|rules\| × \|categories\|) | Fixed-point with at most \|categories\| iterations |
| 2 (rule check) | O(\|rules\|) | Set membership test per rule |
| 3 | O(\|rules\| × \|FIRST\| × \|WFST_actions\|) | Bounded by grammar size |

The total cost is dominated by Tier 3, which is O(|rules| × |FIRST| ×
|WFST_actions|).  In practice this is negligible compared to WFST
construction itself: the prediction WFST build involves DFA subset
construction and Hopcroft minimization, both of which are significantly
more expensive than the linear scans in dead-rule detection.

**Empirical**: For the RhoCalc grammar (~120 rules, ~10 categories),
dead-rule detection completes in under 1 ms, compared to ~50 ms for WFST
construction.

---

## 7. References

- Mohri, M. (2009). *Weighted Automata Algorithms.* In: Handbook of
  Weighted Automata. Springer. — Reachability as boolean projection of
  weighted automata.

- [BooleanWeight: Theory](../../theory/wfst/semirings/boolean-weight.md)
  — Formal definition of the boolean semiring and reachability proofs.

- [BooleanWeight: Design](../semirings/boolean-weight.md) — Design
  decisions and implicit boolean projection rationale.

- [Pipeline Integration §5f](../../architecture/wfst/pipeline-integration.md#5-data-bundles-annotated)
  — Data flow showing `detect_dead_rules()` in the pipeline sequence.

---

## Source Locations

| Component | File | Lines |
|-----------|------|-------|
| `DeadRuleWarning` enum | `pipeline.rs` | 48–96 |
| `detect_dead_rules()` | `pipeline.rs` | 106–207 |
| `lint_w01_dead_rule()` | `lint.rs` | 786–832 |
| `run_lints()` entry point | `lint.rs` | 136–176 |
| `LintDiagnostic` struct | `lint.rs` | 68–84 |
| `LintContext` struct | `lint.rs` | 97–126 |
| `emit_diagnostics()` | `lint.rs` | 179–183 |
| Unit tests | `tests/warning_tests.rs` | 355–920 |
