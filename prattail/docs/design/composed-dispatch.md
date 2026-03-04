# Phase 6C: WFST-Composed Dispatch Table Computation

**Date:** 2026-02-26

---

## Table of Contents

1. [Formal Problem Statement](#1-formal-problem-statement)
2. [Complete Pseudocode](#2-complete-pseudocode)
3. [Composition Diagram](#3-composition-diagram)
4. [Rule Specificity Weight Assignment](#4-rule-specificity-weight-assignment)
5. [Worked Example: RhoCalc `error` Keyword Ambiguity](#5-worked-example-rhocalc-error-keyword-ambiguity)
6. [Counting Semiring Pass (Ambiguity Detection)](#6-counting-semiring-pass-ambiguity-detection)
7. [Semiring Polymorphism](#7-semiring-polymorphism)
8. [Complexity Analysis](#8-complexity-analysis)
9. [Source References](#9-source-references)

---

## 1. Formal Problem Statement

The composed dispatch algorithm solves the following problem: when the lexer
DFA reaches an accepting state that recognizes multiple token kinds
simultaneously (a **multi-accept state**), the parser must determine which
token interpretation to use.  This decision depends on the **parse context**
-- specifically, which grammar category is currently being parsed.

### Inputs

**Multi-accept DFA states.** The lexer DFA analysis produces a set of
ambiguous accepting states.  Each state maps to the alternative token kinds
it can accept, each carrying a tropical weight derived from token priority:

```
AmbiguousStates : { (S, [(tokᵢ, wᵢ)]) }

    where  S    : StateId  (DFA state identifier, u32)
           tokᵢ : TokenKind  (e.g., Fixed("error"), Ident, Integer)
           wᵢ   : TropicalWeight  (lower = higher priority)
```

These are extracted by `analyze_ambiguity()` in `codegen.rs`, which inspects
every accepting DFA state for multiple `TokenKind` assignments.  The weight
`wᵢ` is computed via `TropicalWeight::from_priority(p)` where
`p = TokenKind::priority()`.  Fixed keywords have priority 10 (weight 0.0);
identifiers have priority 1 (weight 9.0).

**PredictionWfst entries.** For each grammar category, the prediction engine
maps tokens to parse rules.  Given a category C and a token variant name,
the FIRST set and rule specificity analysis produce candidate rules:

```
Predict(C, tok) : [(rule, w_rule)]

    where  C       : String  (category name, e.g., "Proc", "Int")
           tok     : String  (token variant name, e.g., "KwError", "Ident")
           rule    : String  (rule label, e.g., "CompareProc", "VarProc")
           w_rule  : f64     (specificity weight, lower = more specific)
```

Rule weights are derived from structural specificity (see Section 4).
Tokens not in `FIRST(C)` produce an empty candidate list.

### Output

The composed dispatch table maps each (category, DFA state) pair to a
weight-ranked list of resolution candidates:

```
TABLE[(C, S)] : [(tokᵢ, rule, w_composed)]

    where  w_composed = wᵢ ⊗ w_rule    (tropical times = f64 addition)
```

Entries are sorted by `w_composed` ascending.  The entry at index 0 is the
tropical shortest-path winner -- the token interpretation and parse rule
that the generated parser will try first.

### Formal Signature

Let:
- S = { s₁, ..., sₘ }  be the set of ambiguous DFA states
- C = { c₁, ..., cₙ }  be the set of grammar categories
- A(s) = { (tok₁, w₁), ..., (tokₖ, wₖ) }  be the alternatives at state s
- P(c, tok) = { (r₁, w₁), ..., (rⱼ, wⱼ) }  be the prediction entries
- FIRST(c) be the FIRST set of category c

Then the composed dispatch table is:

```
TABLE : (C × S) → [(TokenKind × Rule × TropicalWeight)]

TABLE(c, s) = sort_asc(
    { (tokᵢ, rⱼ, wᵢ + w_rⱼ)
      | (tokᵢ, wᵢ) ∈ A(s),
        variant(tokᵢ) ∈ FIRST(c),
        (rⱼ, w_rⱼ) ∈ P(c, variant(tokᵢ)) }
)
```

---

## 2. Complete Pseudocode

```
function compute_composed_dispatch(
    ambiguous_states : [(StateId, [(TokenKind, TropicalWeight)])],
    categories       : [String],
    first_sets       : Map<String, FirstSet>,
    variant_map      : TokenVariantMap,
    rule_infos       : [RuleInfo],
) → Map<(String, u32), [ComposedEntry]>:

    table ← empty map

    for each (state_id, alts) in ambiguous_states:
        for each category in categories:
            first_set ← first_sets[category]
            if first_set is None: continue

            candidates ← empty list

            for each (tok_kind, lexer_weight) in alts:
                variant_name ← token_kind_to_variant_name(tok_kind)

                ── FIRST-set membership filter ──
                if variant_name ∉ first_set:
                    continue

                ── Find matching rules via specificity analysis ──
                matching_rules ← find_rules_for_token(
                    rule_infos, category, variant_name
                )

                if matching_rules is empty:
                    ── Variable fallback: no specific rule found ──
                    tok_id ← variant_map.kind_to_id(tok_kind)
                    candidates.append(ComposedEntry {
                        token_kind_id:      tok_id,
                        token_variant_name: variant_name,
                        rule_label:         "Var" + category,
                        weight:             lexer_weight + 2.0,
                    })
                else:
                    for each (rule_label, specificity) in matching_rules:
                        rule_weight ← specificity_weight(specificity)
                            ── i.e., 1.0 / (1.0 + specificity) ──

                        composed_weight ← lexer_weight ⊗ rule_weight
                            ── tropical times = addition ──
                            ── i.e., lexer_weight.value() + rule_weight ──

                        tok_id ← variant_map.kind_to_id(tok_kind)
                        candidates.append(ComposedEntry {
                            token_kind_id:      tok_id,
                            token_variant_name: variant_name,
                            rule_label:         rule_label,
                            weight:             composed_weight,
                        })

            if candidates is not empty:
                ── Sort by composed weight ascending (best first) ──
                sort candidates by weight ascending

                ── Emit codegen-time ambiguity warning if count > 1 ──
                if candidates.len() > 1:
                    emit_ambiguity_warning(category, state_id, candidates)

                table[(category, state_id)] ← candidates

    return table
```

### Helper: `find_rules_for_token`

```
function find_rules_for_token(
    rule_infos    : [RuleInfo],
    category      : String,
    variant_name  : String,
) → [(String, f64)]:

    matches ← empty list

    for each rule in rule_infos:
        if rule.category ≠ category: continue
        if rule.is_infix: continue

        first_matches ← match rule.first_items[0]:
            Terminal(t)       → terminal_to_variant_name(t) = variant_name
            NonTerminal(_)    → variant_name = "Ident"
            Ident             → variant_name = "Ident"

        if first_matches:
            specificity ← compute_rule_specificity(rule)
            matches.append((rule.label, specificity))

    return matches
```

### Helper: `compute_rule_specificity`

```
function compute_rule_specificity(rule : RuleInfo) → f64:
    terminals ← 0.0
    nonterminals ← 0.0
    for each item in rule.first_items:
        match item:
            Terminal(_)    → terminals += 1.0
            NonTerminal(_) → nonterminals += 1.0
            Ident          → nonterminals += 0.5
    return terminals + 0.5 × nonterminals
```

---

## 3. Composition Diagram

The composed dispatch table is computed by a pointwise composition of two
weighted structures: the lexer's multi-accept alternatives and the grammar's
prediction entries.  This is not a full WFST product construction -- it is
an eager, table-driven join over only the ambiguous states.

### Conceptual Data Flow

```
    ┌─────────────────────────────────────────────────────────────┐
    │                   Lexer DFA Analysis                        │
    │                                                             │
    │  State 7 (multi-accept):                                    │
    │    Fixed("error")  w = 0.0   (keyword, priority 10)         │
    │    Ident           w = 9.0   (identifier, priority 1)       │
    └────────────────────────┬────────────────────────────────────┘
                             │
                             │  for each (tokᵢ, wᵢ)
                             ▼
    ┌─────────────────────────────────────────────────────────────┐
    │                FIRST Set Membership Filter                  │
    │                                                             │
    │  Category "Proc":                                           │
    │    FIRST(Proc) = { KwError, Ident, Star, LBrace, ... }      │
    │                                                             │
    │    KwError ∈ FIRST(Proc)?  ✓  →  pass through               │
    │    Ident   ∈ FIRST(Proc)?  ✓  →  pass through               │
    └────────────────────────┬────────────────────────────────────┘
                             │
                             │  for each surviving (tokᵢ, wᵢ)
                             ▼
    ┌─────────────────────────────────────────────────────────────┐
    │              Rule Specificity Lookup                        │
    │                                                             │
    │  Predict(Proc, KwError):                                    │
    │    CompareProc   specificity = 1.0   w_rule = 0.50          │
    │                                                             │
    │  Predict(Proc, Ident):                                      │
    │    VarProc       specificity = 0.25  w_rule = 0.80          │
    └────────────────────────┬────────────────────────────────────┘
                             │
                             │  composed_weight = wᵢ + w_rule
                             ▼
    ┌─────────────────────────────────────────────────────────────┐
    │            Composed Dispatch Table                          │
    │                                                             │
    │  TABLE[(Proc, 7)]:                                          │
    │    ┌──────────────┬──────────────┬───────────────┐          │
    │    │ Token        │ Rule         │ Weight        │          │
    │    ├──────────────┼──────────────┼───────────────┤          │
    │    │ KwError      │ CompareProc  │ 0.0 + 0.50    │          │
    │    │              │              │     = 0.50    │ ← best   │
    │    ├──────────────┼──────────────┼───────────────┤          │
    │    │ Ident        │ VarProc      │ 9.0 + 0.80    │          │
    │    │              │              │     = 9.80    │          │
    │    └──────────────┴──────────────┴───────────────┘          │
    │                                                             │
    │  Tropical shortest path → CompareProc (weight 0.50)         │
    └─────────────────────────────────────────────────────────────┘
```

### Pointwise Composition Detail

The composition is computed as a three-way join at each ambiguous state.
The vertical axis enumerates lexer alternatives; the horizontal axis
enumerates grammar rules that accept each token.

```
                              Grammar Rules for Category C
                    ┌───────────────┬───────────────┬───────────────┐
                    │  Rule R₁      │  Rule R₂      │  Rule R₃      │
                    │  (w_r₁)       │  (w_r₂)       │  (w_r₃)       │
    ┌───────────────┼───────────────┼───────────────┼───────────────┤
    │ tok₁ (w₁)     │  w₁ + w_r₁    │      ──       │      ──       │
    │ ∈ FIRST(C)?   │  ✓ compose    │  tok₁ ∉ R₂    │  tok₁ ∉ R₃    │
    ├───────────────┼───────────────┼───────────────┼───────────────┤
    │ tok₂ (w₂)     │      ──       │  w₂ + w_r₂    │  w₂ + w_r₃    │
    │ ∈ FIRST(C)?   │  tok₂ ∉ R₁    │  ✓ compose    │  ✓ compose    │
    ├───────────────┼───────────────┼───────────────┼───────────────┤
    │ tok₃ (w₃)     │      ──       │      ──       │      ──       │
    │ ∈ FIRST(C)?   │  tok₃ ∉ R₁    │  tok₃ ∉ R₂    │  tok₃ ∉ R₃    │
    │  ✗ filtered   │               │               │               │
    └───────────────┴───────────────┴───────────────┴───────────────┘

    Composed entries = { (tok₁, R₁, w₁ + w_r₁),
                         (tok₂, R₂, w₂ + w_r₂),
                         (tok₂, R₃, w₂ + w_r₃) }

    After sorting by weight:
    TABLE[(C, S)] = [ entry with min weight, ..., entry with max weight ]
```

Where `──` denotes that the token is not in the rule's FIRST set (filtered
out by the FIRST-set membership check), and the `✗` row shows a token that
is not in `FIRST(C)` at all and is discarded before rule lookup.

---

## 4. Rule Specificity Weight Assignment

### Formula

The specificity weight for a grammar rule is computed from its syntactic
structure:

```
    specificity(R) = terminals(R) + 0.5 × nonterminals(R)

    weight(R) = 1 / (1 + specificity(R))
```

Where:
- `terminals(R)` counts fixed terminal tokens in the rule's first items
  (each contributes 1.0)
- `nonterminals(R)` counts nonterminal references (each contributes 1.0
  to the raw count, then scaled by 0.5)
- `Ident` captures count as 0.5 nonterminal (they constrain the input
  more than a free nonterminal but less than a fixed terminal)

### Rationale

More specific rules -- those with more structural constraints (terminals
and nonterminals) -- should be preferred over less specific rules.  The
weight formula maps higher specificity to lower weight, which the tropical
semiring's `min` operation selects as the best path.

The 0.5 scaling for nonterminals reflects that a nonterminal reference
constrains the parse (it must be a valid expression of that category) but
less tightly than a fixed terminal token (which must match exactly one
string).

### Examples

| Rule                  | Structure                  | Terminals  | NTs         | Specificity     | Weight            |
|-----------------------|----------------------------|------------|-------------|-----------------|-------------------|
| `Compare(E, "==", E)` | `E "==" E`                 | 1 (`"=="`) | 1 (`E`)     | 1.0 + 0.5 = 1.5 | 1/(1+1.5) = 0.40  |
| `IfThenElse(b, t, f)` | `"if" b "then" t "else" f` | 3          | 3           | 3.0 + 1.5 = 4.5 | 1/(1+4.5) = 0.18  |
| `Err`                 | `"error"`                  | 1          | 0           | 1.0             | 1/(1+1.0) = 0.50  |
| `Var(x)`              | `x:Ident`                  | 0          | 0.5 (Ident) | 0.25            | 1/(1+0.25) = 0.80 |
| `Unit`                | `"()"`                     | 1          | 0           | 1.0             | 1/(1+1.0) = 0.50  |

### Interpretation

- **`IfThenElse` (weight 0.18):** Highly specific -- three terminal keywords
  plus three nonterminal positions.  Strongly preferred when `"if"` is seen.
- **`Compare` (weight 0.40):** Moderately specific -- one operator terminal
  and one nonterminal.
- **`Err` (weight 0.50):** Single terminal keyword.  Preferred over `Var`
  when the keyword `"error"` matches.
- **`Var` (weight 0.80):** Least specific -- just an identifier capture.
  This is the fallback rule.

The variable fallback penalty (`+2.0`) applied when no specific rule is
found (see pseudocode) pushes generic variable rules even further down the
ranking, ensuring structural rules are always tried first.

---

## 5. Worked Example: RhoCalc `error` Keyword Ambiguity

### Grammar Context

The RhoCalc grammar (defined in `languages/src/rhocalc.rs`) includes:

```
Err . |- "error" : Proc;       // "error" is a keyword for the Err rule
PVar . x:Name |- x : Proc;     // variables, where Name includes identifiers
```

The string `error` is lexed by the DFA as either:
- `Fixed("error")` with priority 10 → `TropicalWeight(0.0)` (keyword)
- `Ident` with priority 1 → `TropicalWeight(9.0)` (identifier)

This creates a multi-accept DFA state (state 7 in this example).

### Step 1: Identify Ambiguous State

```
analyze_ambiguity(dfa) yields:

    State 7:
      alternatives = [
          (Fixed("error"), TropicalWeight(0.0)),
          (Ident,          TropicalWeight(9.0)),
      ]
```

### Step 2: Map TokenKind to Variant Names

```
token_kind_to_variant_name(Fixed("error")) = "KwError"
token_kind_to_variant_name(Ident)          = "Ident"
```

### Step 3: FIRST Set Filter for Category "Proc"

```
FIRST(Proc) = { KwError, Ident, Star, LBrace, EmptyBraces, Caret, At, ... }

    KwError ∈ FIRST(Proc)?  ✓
    Ident   ∈ FIRST(Proc)?  ✓
```

Both alternatives survive the filter.

### Step 4: Rule Lookup and Specificity

For `KwError`:
```
find_rules_for_token(rule_infos, "Proc", "KwError"):
    Rule "Err": first_items = [Terminal("error")]
        terminal_to_variant_name("error") = "KwError" = "KwError"  ✓
        specificity = 1.0 (1 terminal + 0 NTs)
    → [("Err", 1.0)]
```

For `Ident`:
```
find_rules_for_token(rule_infos, "Proc", "Ident"):
    Rule "PVar": first_items = [Ident]
        Ident matches "Ident"  ✓
        specificity = 0.25 (0.5 × 0.5 for Ident)
    → [("PVar", 0.25)]
```

### Step 5: Weight Composition (Tropical Times)

```
For (KwError → Err):
    lexer_weight = 0.0      (keyword priority)
    rule_weight  = specificity_weight(1.0) = 1/(1+1.0) = 0.50
    composed     = 0.0 + 0.50 = 0.50

For (Ident → PVar):
    lexer_weight = 9.0      (identifier priority)
    rule_weight  = specificity_weight(0.25) = 1/(1+0.25) = 0.80
    composed     = 9.0 + 0.80 = 9.80
```

### Step 6: Sort and Emit

```
TABLE[(Proc, 7)] = [
    ComposedEntry { token: KwError, rule: Err,  weight: 0.50 },   ← tropical best
    ComposedEntry { token: Ident,  rule: PVar, weight: 9.80 },
]
```

The generated parser, upon reaching DFA state 7 while parsing category
`Proc`, will interpret the input as the `error` keyword and dispatch to the
`Err` rule.  The identifier interpretation (`PVar`) is available as a
fallback if the keyword interpretation fails.

### Generated Code

The composed dispatch table is emitted as a static lookup:

```rust
const CATEGORY_ID_PROC: u8 = 0;
const CATEGORY_ID_INT: u8 = 1;

fn composed_dispatch(
    category_id: u8,
    dfa_state: u32,
) -> &'static [(u8, &'static str, f64)] {
    match (category_id, dfa_state) {
        (0, 7) => &[
            (3, "Err",  0.500000),    // KwError → Err
            (1, "PVar", 9.800000),    // Ident   → PVar
        ],
        _ => &[]
    }
}
```

---

## 6. Counting Semiring Pass (Ambiguity Detection)

### Purpose

The counting semiring pass performs the same composition as the tropical
pass, but instead of computing optimal weights, it counts the number of
alternative resolutions per (category, state) pair.  This serves as a
**compile-time diagnostic** to alert grammar authors to ambiguous dispatch
points.

### Algorithm

The counting semiring N = (N, +, x, 0, 1) uses:
- Carrier: natural numbers N
- Plus (parallel combination): addition (+)
- Times (sequential composition): multiplication (x)
- Zero: 0
- One: 1

For each (category, state) pair, the count is the number of
`ComposedEntry`s produced by the composition:

```
function count_ambiguities(
    table : Map<(String, u32), [ComposedEntry]>,
) → Map<(String, u32), usize>:

    counts ← empty map
    for each ((category, state), entries) in table:
        counts[(category, state)] ← entries.len()
    return counts
```

### Warning Emission

When `count > 1` for any (category, state) pair, a codegen-time warning
is emitted.  This happens inside `compute_composed_dispatch()` after
the entries are sorted:

```
if entries.len() > 1:
    ── Build human-readable description ──
    alts_desc ← for each entry in entries:
        format("  - Token::{} → rule {} (weight {:.2})",
               entry.token_variant_name,
               entry.rule_label,
               entry.weight)

    eprintln(
        "warning: {}-way ambiguity at ({}, DFA state {}):\n{}\n"
        "  Resolved by tropical shortest path → {}",
        entries.len(),
        category,
        state_id,
        join(alts_desc, "\n"),
        entries[0].rule_label,
    )
```

### Example Warning Output

For the RhoCalc `error` ambiguity at state 7:

```
warning: 2-way ambiguity at (Proc, DFA state 7):
  - Token::KwError → rule Err (weight 0.50)
  - Token::Ident → rule PVar (weight 9.80)
  Resolved by tropical shortest path → Err
```

### Zero Runtime Overhead

The counting pass executes entirely at codegen time (during `language! {}`
macro expansion).  The `eprintln!` warnings appear during compilation.
No counting semiring code is embedded in the generated parser -- the
diagnostic is complete before any runtime code is produced.

---

## 7. Semiring Polymorphism

> **Mode 1 — Re-Interpretation:** The `CountingWeight` usage below (§7.3) is a
> Mode 1 re-interpretation: `entries.len()` projects the set of tropical-weighted
> alternatives onto a single counting value.  See
> [`semiring-composition.md`](../theory/wfst/semiring-composition.md) §2 for
> the formal definition and
> [`semiring-orchestration.md`](../architecture/wfst/semiring-orchestration.md) §3.2
> for source-level detail.

The composed dispatch table format is semiring-agnostic.  The same
structure `TABLE[(C, S)] → [(tok, rule, weight)]` supports different
weight interpretations depending on the semiring used for composition.

### Tropical Semiring (Always-On Default)

```
Semiring:   (R⁺ ∪ {+∞}, min, +, +∞, 0.0)
    plus  = min(a, b)     (select best alternative)
    times = a + b          (accumulate costs along path)
    zero  = +∞             (unreachable)
    one   = 0.0            (zero cost)
```

**Usage:** The always-on dispatch strategy.  All grammars use
WFST-weighted dispatch -- the `wfst` feature was removed and this
is now the default (and only) dispatch path.  `TABLE[(C, S)][0]`
is the single best resolution (tropical shortest path).  Runtime
cost: O(1) index into the sorted slice.

**Idempotent:** `min(a, a) = a`.  The tropical semiring is a
bounded lattice.

### Log Semiring (Feature `wfst-log` Only)

```
Semiring:   (R⁺ ∪ {+∞}, log-sum-exp, +, +∞, 0.0)
    plus  = -ln(exp(-a) + exp(-b))   (combine probabilities)
    times = a + b                      (multiply probabilities in log space)
    zero  = +∞                         (probability 0)
    one   = 0.0                        (probability 1)
```

**Usage:** Requires the `wfst-log` feature gate (the only remaining
WFST-related feature gate).  When trained weights from `TrainedModel`
are available, the same table carries log-probability weights.  This
enables beam search: instead of selecting only `TABLE[(C, S)][0]`, the
parser can explore multiple alternatives within a beam width threshold.

**Non-idempotent:** `plus(a, a) = a - ln(2) ≠ a`.  The log semiring
correctly accounts for multiple derivation paths contributing to the
same result.

### Counting Semiring (Diagnostic, Always-On)

```
Semiring:   (N, +, ×, 0, 1)
    plus  = a + b     (count parallel alternatives)
    times = a × b     (count sequential compositions)
    zero  = 0         (no alternatives)
    one   = 1         (one way)
```

**Usage:** Always-on codegen-time diagnostic.  Counts the number of
alternative resolutions per (category, state) pair.  Count > 1 triggers
a warning.  Zero runtime overhead -- no counting semiring code is embedded
in the generated parser.

### Boolean Semiring (Dead-Rule Detection, Always-On)

```
Semiring:   ({0, 1}, ∨, ∧, 0, 1)
    plus  = OR(a, b)   (reachable from either path)
    times = AND(a, b)  (reachable through both steps)
    zero  = false      (unreachable)
    one   = true       (reachable)
```

**Usage:** Always-on codegen-time diagnostic.  After WFST construction,
a boolean semiring projection identifies rules that are unreachable
(dead rules) in the grammar.  These are reported as compile-time
warnings.  Zero runtime overhead.

### Edit Semiring (Recovery Costs, Always-On)

```
Semiring:   (N, min, +, ∞, 0)
    plus  = min(a, b)  (select cheapest repair)
    times = a + b      (accumulate edit costs)
    zero  = ∞          (impossible repair)
    one   = 0          (free operation)
```

**Usage:** Always-on error recovery costing via `RepairAction::edit_cost()`.
Ranks repair strategies (skip, insert, substitute, delete) by edit
distance.  Used by `recovery.rs` to select the lowest-cost repair action.

### Product Semiring (Multi-Metric Composition, Always-On)

```
Semiring:   (A × B, (⊕_A, ⊕_B), (⊗_A, ⊗_B), (0_A, 0_B), (1_A, 1_B))
```

**Usage:** Always-on lexicographic product of two semirings (left
component compared first, then right).  Enables multi-metric optimization,
e.g., `ProductWeight<TropicalWeight, EditWeight>` for jointly optimizing
dispatch likelihood and recovery cost.

### Unified Table Format

All three semirings produce the same table structure:

```
    TABLE[(C, S)] → [(tok_kind_id: u8, rule_label: &str, weight: f64)]
```

The interpretation of `weight` changes with the semiring:

| Semiring | Weight Meaning           | Best =          | Runtime Access        | Feature Gate |
|----------|--------------------------|-----------------|-----------------------|--------------|
| Tropical | Accumulated cost         | `min` (index 0) | O(1)                  | Always-on    |
| Counting | Number of alternatives   | Diagnostic      | Compile-time only     | Always-on    |
| Boolean  | Reachability             | OR              | Compile-time only     | Always-on    |
| Edit     | Edit distance            | `min`           | O(k) repair choices   | Always-on    |
| Product  | Multi-metric             | Lexicographic   | Depends on components | Always-on    |
| Log      | Negative log probability | Beam search     | O(beam width)         | `wfst-log`   |

---

## 8. Complexity Analysis

### Worst-Case Bound

```
T(composed) = O(|S_amb| × |C| × |A_max| × |R_max|)
```

Where:
- `|S_amb|` = number of ambiguous DFA states
- `|C|` = number of grammar categories
- `|A_max|` = maximum number of alternatives per ambiguous state
- `|R_max|` = maximum number of rules matching a single token in a category

### Practical Bounds

In typical PraTTaIL grammars:

| Parameter   | Typical Value | Bound                                 |
|-------------|---------------|---------------------------------------|
| `\|S_amb\|` | 2--5          | Keywords overlapping with identifiers |
| `\|C\|`     | 2--6          | Proc, Name, Int, Bool, Str, ...       |
| `\|A_max\|` | 2--3          | Usually keyword vs. identifier        |
| `\|R_max\|` | 1--3          | Rules starting with the same token    |

Total composed entries: typically < 100.  For the RhoCalc grammar with 4
categories and 3 ambiguous states, the algorithm produces ~20 entries.

### Per-Phase Cost

| Phase                   | Operation                   | Cost                               |
|-------------------------|-----------------------------|------------------------------------|
| FIRST-set filter        | Set membership lookup       | O(log \|FIRST(C)\|) per token      |
| Rule lookup             | Linear scan of `rule_infos` | O(\|rules\|) per (category, token) |
| Specificity computation | Count first items           | O(\|first_items\|) per rule        |
| Weight composition      | Addition                    | O(1) per entry                     |
| Sort                    | Sort entries per (C, S)     | O(k log k) where k = entries       |
| Warning emission        | String formatting           | O(k) per ambiguous pair            |

### Codegen-Time Guarantee

**All composition is computed at codegen time** during the `language! {}`
macro expansion.  The generated parser embeds the composed table as static
data:

```rust
fn composed_dispatch(
    category_id: u8,
    dfa_state: u32,
) -> &'static [(u8, &'static str, f64)]
```

Runtime dispatch is a single `match` on `(category_id, dfa_state)` that
returns a static slice.  The runtime cost is O(1) for tropical (read
`slice[0]`) or O(beam_width) for log semiring beam search.

---

## 9. Source References

All source code is in the `prattail/src/` directory.

### Core Algorithm

| Function                         | File            | Description                              |
|----------------------------------|-----------------|------------------------------------------|
| `compute_composed_dispatch()`    | `prediction.rs` | Main composition algorithm               |
| `find_rules_for_token()`         | `prediction.rs` | Rule lookup by FIRST token match         |
| `compute_rule_specificity()`     | `prediction.rs` | Structural specificity scoring           |
| `specificity_weight()`           | `prediction.rs` | Specificity → tropical weight conversion |
| `token_kind_to_variant_name()`   | `prediction.rs` | TokenKind → variant name mapping         |
| `emit_composed_dispatch_table()` | `prediction.rs` | Codegen: emit static dispatch table      |

### Supporting Infrastructure

| Function / Type        | File                  | Description                             |
|------------------------|-----------------------|-----------------------------------------|
| `ComposedEntry`        | `prediction.rs`       | Single entry in composed table          |
| `RuleInfo`             | `prediction.rs`       | Rule metadata for FIRST set computation |
| `FirstSet`             | `prediction.rs`       | Token set with nullable flag            |
| `compute_first_sets()` | `prediction.rs`       | Fixed-point FIRST set computation       |
| `analyze_ambiguity()`  | `automata/codegen.rs` | DFA multi-accept state detection        |
| `LexerAmbiguityInfo`   | `automata/codegen.rs` | Ambiguous state data structure          |
| `TokenVariantMap`      | `automata/codegen.rs` | Token name ↔ compact ID mapping         |

### Semiring Definitions

| Type                  | File                   | Description                                                      |
|-----------------------|------------------------|------------------------------------------------------------------|
| `Semiring` trait      | `automata/semiring.rs` | Generic `(K, +, *, 0, 1)` interface                              |
| `TropicalWeight`      | `automata/semiring.rs` | `(R⁺ ∪ {+∞}, min, +, +∞, 0.0)` (always-on)                       |
| `CountingWeight`      | `automata/semiring.rs` | `(N, +, ×, 0, 1)` (always-on, diagnostic)                        |
| `BooleanWeight`       | `automata/semiring.rs` | `({0, 1}, ∨, ∧, 0, 1)` (always-on, dead-rule detection)          |
| `EditWeight`          | `automata/semiring.rs` | `(N, min, +, ∞, 0)` (always-on, recovery costs)                  |
| `ProductWeight<A, B>` | `automata/semiring.rs` | Lexicographic product (always-on)                                |
| `LogWeight`           | `automata/semiring.rs` | `(R⁺ ∪ {+∞}, log-sum-exp, +, +∞, 0.0)` (feature `wfst-log` only) |

### WFST Prediction Layer

| Function / Type                | File      | Description                               |
|--------------------------------|-----------|-------------------------------------------|
| `PredictionWfst`               | `wfst.rs` | Per-category prediction WFST              |
| `PredictionWfstBuilder`        | `wfst.rs` | Builder for constructing prediction WFSTs |
| `build_prediction_wfsts()`     | `wfst.rs` | Build WFSTs from FIRST sets and overlaps  |
| `compute_action_weight()`      | `wfst.rs` | Dispatch action → tropical weight         |
| `generate_weighted_dispatch()` | `wfst.rs` | Weight-ordered dispatch codegen           |
| `WeightedAction`               | `wfst.rs` | Action + weight pair                      |
| `WeightedTransition`           | `wfst.rs` | WFST state transition                     |

### Pipeline Integration

| Function                             | File            | Description                                     |
|--------------------------------------|-----------------|-------------------------------------------------|
| `generate_parser_code()`             | `pipeline.rs`   | Pipeline orchestrator (calls WFST construction) |
| `build_dispatch_action_tables()`     | `prediction.rs` | Structured dispatch tables for WFST builder     |
| `write_category_dispatch_weighted()` | `dispatch.rs`   | WFST-ordered dispatch codegen                   |
| `emit_prediction_wfst_static()`      | `pipeline.rs`   | CSR-format static WFST embedding                |

### Tests

| Test                                             | File            | Description                                   |
|--------------------------------------------------|-----------------|-----------------------------------------------|
| `test_composed_dispatch_basic`                   | `prediction.rs` | End-to-end composition with `error` ambiguity |
| `test_composed_dispatch_empty_when_no_ambiguity` | `prediction.rs` | Empty table for unambiguous grammars          |
| `test_specificity_weight`                        | `prediction.rs` | Higher specificity → lower weight             |
| `test_compute_rule_specificity`                  | `prediction.rs` | Structural scoring of terminals/NTs           |
| `test_emit_composed_dispatch_table`              | `prediction.rs` | Generated code parses as valid Rust           |
