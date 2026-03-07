# D09: conflict-resolution-guide

**Date:** 2026-03-06
**Updated:** 2026-03-06
**Severity:** Note
**Category:** Decision Tree

## 1 Description

For each genuine conflict (ambiguous dispatch point) in the PathMap decision
trie, provides a comprehensive menu of resolution strategies. Unlike D08, which
targets a single best-fit suggestion per ambiguity pattern, D09 enumerates **all
four** canonical resolution strategies so the grammar author can choose the most
appropriate one for their use case.

This diagnostic is **informational** (Note severity). It does not indicate a
bug -- the parser handles ambiguous dispatch correctly via NFA try-all at
runtime. D09 exists as a reference guide that accompanies each conflict,
ensuring the grammar author is aware of all available options.

## 2 Trigger Conditions

A D09 diagnostic is emitted when **any** `Ambiguous` action exists in any
segment of the category's decision trie:

1. The function iterates all segments in `tree.segments`.
2. For each `(path, DecisionAction::Ambiguous { candidates })` entry, a D09
   diagnostic is emitted.
3. The diagnostic lists all candidate rule labels and presents the four
   resolution strategies.

One D09 diagnostic is emitted per ambiguous node. Categories with no ambiguity
produce no D09 diagnostics.

## 3 The Four Resolution Strategies

D09 presents the following strategies in its hint text:

### 3.1 Strategy 1: Add Distinguishing Terminal

Insert a unique keyword or symbol at or before the point where the competing
rules diverge. This creates a deterministic split in the trie.

**When to use:** The grammar can tolerate a syntax change, and the ambiguity
involves two rules with a short shared prefix.

**Example:**

Before:
```
FloatId    = "float" "(" <ident> ")";
IntToFloat = "float" "(" Float  ")";
```

After:
```
FloatId    = "float" "(" <ident> ")";
IntToFloat = "float" "(" "int" Float ")";
```

The added `"int"` keyword splits the trie at depth 3.

### 3.2 Strategy 2: Reorder via WFST Weights

Assign distinct weights to the competing rules in the WFST model. The runtime
try-all dispatcher evaluates candidates in weight order, so the most common rule
is tried first. This does not eliminate the ambiguity but reduces the expected
number of backtracking attempts.

**When to use:** The ambiguity is intentional (overloaded syntax) and one
alternative is far more common than others.

**Example:**

```
// In WFST training data or weight annotations:
FloatId    weight=0.8  // tried first (80% of inputs)
IntToFloat weight=0.2  // tried second (20% of inputs)
```

### 3.3 Strategy 3: Factor Grammar

Extract the common prefix into a helper rule and use nonterminal boundary
dispatch. If the continuation tokens after the helper rule have disjoint FIRST
sets, the trie resolves deterministically at the nonterminal boundary.

**When to use:** Multiple rules (3+) share a long common prefix, and their
continuations have distinct leading tokens.

**Example:**

Before:
```
NewChannel  = "new" <ident> "in" Proc;
NewContract = "new" "contract" <ident> Proc;
NewBundle   = "new" "bundle" Proc;
```

After:
```
NewOpen     = "new";
NewChannel  = NewOpen <ident> "in" Proc;
NewContract = NewOpen "contract" <ident> Proc;
NewBundle   = NewOpen "bundle" Proc;
```

### 3.4 Strategy 4: Accept Ambiguity

If the grammar intentionally allows overlapping syntax and the performance cost
is acceptable, no change is needed. The NFA try-all dispatcher handles the
ambiguity correctly at runtime. This is the right choice when:

- The grammar is a faithful encoding of a language specification that requires
  overlapping productions.
- The ambiguity is rare in practice (few inputs hit the ambiguous path).
- The candidate count is small (2-3 rules) and backtracking cost is negligible.

## 4 Output Format

### 4.1 Message Structure

```
note[D09] (GrammarName): genuine conflict between [<label_1>, <label_2>, ...] — resolution strategies:
  = hint: 1. Add distinguishing terminal before the nonterminal
          2. Reorder rules via WFST weights
          3. Factor grammar: extract common prefix
          4. Accept ambiguity with #[allow(ambiguous)]
```

### 4.2 Example: Two-Rule Conflict

```
note[D09] (MyLang): genuine conflict between [FloatId, IntToFloat] — resolution strategies:
  = hint: 1. Add distinguishing terminal before the nonterminal
          2. Reorder rules via WFST weights
          3. Factor grammar: extract common prefix
          4. Accept ambiguity with #[allow(ambiguous)]
```

### 4.3 Example: Multi-Rule Conflict

```
note[D09] (Rho): genuine conflict between [NewChannel, NewContract, NewBundle] — resolution strategies:
  = hint: 1. Add distinguishing terminal before the nonterminal
          2. Reorder rules via WFST weights
          3. Factor grammar: extract common prefix
          4. Accept ambiguity with #[allow(ambiguous)]
```

### 4.4 Example: Multiple Conflicts in One Category

```
note[D09] (Rho): genuine conflict between [Send, SendAsync] — resolution strategies:
  = hint: 1. Add distinguishing terminal before the nonterminal
          2. Reorder rules via WFST weights
          3. Factor grammar: extract common prefix
          4. Accept ambiguity with #[allow(ambiguous)]

note[D09] (Rho): genuine conflict between [MatchInt, MatchFloat, MatchStr] — resolution strategies:
  = hint: 1. Add distinguishing terminal before the nonterminal
          2. Reorder rules via WFST weights
          3. Factor grammar: extract common prefix
          4. Accept ambiguity with #[allow(ambiguous)]
```

## 5 Decision Framework

The following decision tree helps select the appropriate strategy:

```
    Is the ambiguity intentional?
     │
     ├── Yes ──▶ Is one alternative much more common?
     │            │
     │            ├── Yes ──▶ Strategy 2 (WFST weights)
     │            │
     │            └── No ───▶ Strategy 4 (accept ambiguity)
     │
     └── No ───▶ How many rules share the prefix?
                  │
                  ├── 2 ────▶ Strategy 1 (distinguishing terminal)
                  │
                  └── 3+ ──▶ Strategy 3 (factor grammar)
```

### 5.1 Strategy Comparison

| Strategy                   | Eliminates ambiguity?        | Requires grammar change? | Runtime cost |
|----------------------------|------------------------------|--------------------------|--------------|
| 1. Distinguishing terminal | Yes                          | Yes (syntax change)      | None         |
| 2. WFST weights            | No (reduces cost)            | No (weight annotation)   | Reduced avg  |
| 3. Factor grammar          | Yes (if FIRST sets disjoint) | Yes (structural)         | None         |
| 4. Accept ambiguity        | No                           | No                       | Full try-all |

## 6 Source

**Function:** `conflict_resolution_guidance()` in
`prattail/src/decision_tree.rs`

```rust
pub fn conflict_resolution_guidance(tree: &CategoryDecisionTree) -> Vec<TreeDiagnostic>
```

The function:
1. Iterates all segments in the tree.
2. For each `Ambiguous` action, collects the candidate `rule_label` values.
3. Constructs a `TreeDiagnostic` with lint ID `"D09"`, severity `Note`, a
   message listing the conflicting labels, and a hint enumerating the four
   resolution strategies.
4. Returns all collected diagnostics.

**Pipeline call site:** `prattail/src/pipeline.rs`, inside the decision tree
construction block:

```rust
// D09: Conflict resolution guidance
for cat_name in &category_names {
    if let Some(tree) = dt_builder.get_tree(cat_name) {
        for diag in crate::decision_tree::conflict_resolution_guidance(tree) {
            pipeline_diagnostic(
                &bundle.grammar_name, diag.lint_id, "conflict-resolution-guide",
                diag.severity,
                diag.message,
                diag.hint,
            );
        }
    }
}
```

## 7 Relationship to D08

D08 and D09 both fire for ambiguous nodes but serve different purposes:

| Aspect            | D08                           | D09                    |
|-------------------|-------------------------------|------------------------|
| Focus             | Single best suggestion        | All four strategies    |
| 2-candidate hint  | "Add distinguishing terminal" | Full strategy menu     |
| 3+ candidate hint | "Factor common prefix"        | Full strategy menu     |
| Actionability     | Targeted recommendation       | Reference guide        |
| When to read      | To quickly fix one ambiguity  | To evaluate trade-offs |

Both D08 and D09 fire for each ambiguous node. Grammar authors who want a quick
fix should follow D08; those who want to evaluate trade-offs should consult D09.

## 8 Related Lints

- [D01](D01-precision-ambiguity.md) -- Precision ambiguity detail; D09 provides
  resolution guidance for the same ambiguous nodes reported by D01.
- [D02](D02-unresolvable-ambiguity.md) -- Unresolvable ambiguity; D09's
  strategies are especially important for D02 nodes where the conflict is
  inherent and cannot be resolved by deeper lookahead.
- [D04](D04-min-lookahead-depth.md) -- Minimum lookahead depth; applying D09
  strategies 1 or 3 reduces `min_lookahead` toward 1 (LL(1)).
- [D08](D08-optimization-suggestion.md) -- Targeted optimization suggestion;
  D08 provides a single best-fit recommendation, while D09 enumerates all
  options.
- [D06](D06-wfst-trie-inconsistency.md) -- WFST/trie consistency; strategy 2
  (WFST weights) requires the WFST to be in sync with the trie, which D06
  validates.
