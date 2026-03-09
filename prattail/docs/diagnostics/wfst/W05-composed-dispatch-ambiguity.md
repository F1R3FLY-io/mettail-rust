# W05: composed-dispatch-ambiguity

**Severity:** Warning
**Category:** WFST-Specific
**Feature Gate:** none (always active)

## Description

Detects **N-way ambiguities** in the composed dispatch table where multiple
rules within a category share the same first token at a given DFA state.
When the prediction WFST composes category-level dispatch transducers into a
unified dispatch table, some DFA states may have multiple outgoing transitions
for the same input token, each leading to a different rule.  This ambiguity
is resolved at compile time using the **tropical semiring shortest-path**
algorithm: the rule with the lowest (best) WFST weight wins.

```
  DFA state 5, category "Expr":
  ┌──────────────────────────────────────┐
  │  Token::Ident                        │
  │    ├── rule FnCall   (weight 1.00)   │ <-- winner
  │    └── rule VarRef   (weight 5.00)   │
  │                                      │
  │  Resolved by tropical shortest path: │
  │    min(1.00, 5.00) = 1.00 -> FnCall  │
  └──────────────────────────────────────┘
```

The `CountingWeight` semiring tracks the number of derivations per
(category, token) pair.  When `count > 1`, the ambiguity is detected and
W05 fires.  The diagnostic includes:

- The **N-way** ambiguity degree (number of competing rules).
- The **DFA state** where the ambiguity occurs.
- The **per-rule weights** showing the competition.
- The **winner** selected by tropical shortest path.

W05 is a compile-time resolution -- the generated parser will always use the
winner.  The warning exists to alert the grammar author that the resolution
is implicit and weight-dependent, which may produce unexpected behavior if
rule weights change.

## Trigger Conditions

All of the following must hold:

- The composed dispatch table has been constructed (at least one category
  with WFST-based dispatch).
- A DFA state has **two or more** dispatch entries for the same input token
  leading to different rules.
- The ambiguity is resolved by tropical shortest-path weight comparison.

One diagnostic is emitted per ambiguous (state, token) pair.  The grouper
consolidates multiple W05 diagnostics into a per-category summary:

```
warning[W05] (GrammarName): 8 ambiguities resolved by tropical shortest path
  Float: -> FnFloat (vs Ident); -> MulFloat (vs DivFloat)
  Int: -> IntCast (vs Ident)
```

## Example

### Grammar

```rust
language! {
    name: MixedLang,
    types { ![f64] as Float, ![i64] as Int },
    terms {
        FnFloat  . |- "fn" <ident> "(" Float ")" : Float;
        Ident    . |- <ident>                     : Float;
        IntCast  . |- "int" "(" Float ")"         : Int;
        IntIdent . |- <ident>                     : Int;
    },
}
```

### Output

```
warning[W05] (MixedLang): 2-way ambiguity at DFA state 0: 2 derivations
  - Token::Ident -> rule Ident (weight 1.00)
  - Token::Ident -> rule FnFloat (weight 5.00)
  Resolved by tropical shortest path -> Ident
  = hint: WFST weights are auto-assigned by rule specificity and declaration order; restructure rules to have distinct first tokens, or reorder rule declarations to change priority
```

## Resolution

1. **Give rules distinct first tokens.**  The most robust fix is to ensure
   that each rule in a category begins with a unique terminal token.
   Refactoring `FnFloat` to `"fn" "(" Float ")"` removes the shared
   `<ident>` prefix and eliminates the ambiguity entirely.

2. **Reorder rule declarations.**  WFST weights are auto-assigned by rule
   specificity (more specific rules get lower weights) and declaration order
   (earlier rules get lower weights among equally specific rules).  Moving
   the desired winner earlier in the grammar gives it priority.

3. **Accept the resolution.**  If the tropical shortest-path winner is the
   correct choice, the warning is informational.  The generated parser will
   always dispatch to the winner at this state.  Suppress by setting
   `PRATTAIL_LINT_LEVEL=error` if the implicit resolution is acceptable.

4. **Use explicit weight annotations.**  If supported, annotate rules with
   explicit weights to make the priority ordering explicit and
   self-documenting.

## Hint Explanation

The hint **"WFST weights are auto-assigned by rule specificity and declaration
order; restructure rules to have distinct first tokens, or reorder rule
declarations to change priority"** explains the weight assignment mechanism:

- **Rule specificity:** Rules with more terminals and more specific patterns
  receive lower (better) weights.  A rule like `"fn" <ident> "(" ... ")"`
  is more specific than bare `<ident>`.

- **Declaration order:** Among equally specific rules, earlier declarations
  win.  This provides a deterministic tiebreaker but can be fragile (grammar
  refactoring may change declaration order).

- **Restructuring** makes the dispatch deterministic without relying on
  weights, which is the most maintainable solution.

## Related Lints

- [W01](W01-dead-rule.md) -- If a rule consistently loses all its
  ambiguities, it may become effectively dead (unreachable via any token
  dispatch), which W01 would detect.
- [W03](W03-high-ambiguity-token.md) -- Detects tokens that cause ambiguity
  across many rules in a category; W05 is the per-state instance-level
  version.
- [W06](W06-weight-inversion.md) -- Detects weight inversions where a less
  specific rule has a better weight than a more specific one, which can cause
  W05 resolutions to produce counterintuitive winners.
- [D01](../decision-tree/D01-precision-ambiguity.md) -- The decision tree's
  own ambiguity analysis; complements W05's WFST-level analysis.
