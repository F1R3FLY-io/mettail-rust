# W03: high-ambiguity-token

**Severity:** Warning
**Category:** WFST-Specific

## Description

Detects tokens with a high branching factor in the prediction WFST. When a single token in a category's FIRST set dispatches to 3 or more rules, parsing that token requires the parser to consider multiple alternatives, each of which may involve speculative parsing with save/restore of parser state. This directly impacts parse performance: each additional alternative adds a potential backtracking point.

The lint uses `predict_with_confidence()` on the prediction WFST, which annotates each prediction with a `CountingWeight` -- a semiring that counts the number of distinct derivations reachable from the token. When the count reaches 3 or higher, the branching factor is significant enough to warrant a warning.

While ambiguity at the 2-rule level is common and usually well-handled by NFA spillover (see W02), a branching factor of 3+ suggests that the grammar could benefit from structural disambiguation: adding unique leading tokens, factoring out common prefixes, or consolidating related rules.

## Trigger Conditions

A W03 diagnostic fires when **all** of the following hold:

1. The category `cat` has a prediction WFST in `prediction_wfsts`.

2. The category has a FIRST set in `first_sets`.

3. For a token `t` in `first_set.sorted_tokens()`, calling `wfst.predict_with_confidence(t)` returns predictions where the `CountingWeight`'s `count()` is >= 3.

4. The diagnostic lists all rule labels that the token dispatches to, regardless of their individual weights.

## Example

### Grammar

```
language! {
    name: ExprLang;
    primary: Proc;

    category Int {
        native_type: Integer;

        IntLit     = <int>;
        IntNeg     = "-" Int;
        IntAdd     = Int "+" Int;
        IntMul     = Int "*" Int;
    }

    category Bool {
        native_type: Boolean;

        BoolLit    = <bool>;
        BoolEq     = Int "==" Int;
        BoolNot    = "!" Bool;
    }

    category Proc {
        // All four rules start with identifier — high ambiguity
        PAssign    = Identifier "=" Int;
        PCall      = Identifier "(" Int ")";
        PField     = Identifier "." Identifier;
        PSend      = Identifier "!" "(" Int ")";

        POutput    = "stdout" "!" "(" Int ")";
        PNil       = "Nil";

        // Casts
        CastInt    = Int;
        CastBool   = Bool;
    }
}
```

### Output

```
warning[W03]: token `Identifier` dispatches to 4 rules in category `Proc`: [PAssign, PCall, PField, PSend]
  = in category `Proc`
  = hint: high branching factor — consider adding unique dispatch tokens to reduce ambiguity
```

## Resolution

Reduce the number of rules that share the same leading token. The following strategies are ordered from most effective to most conservative:

1. **Add unique leading keywords.** Give each rule a distinct first terminal so the dispatch table can route directly:
   ```
   PAssign = "let" Identifier "=" Int;
   PCall   = "call" Identifier "(" Int ")";
   PField  = "get" Identifier "." Identifier;
   PSend   = "send" Identifier "!" "(" Int ")";
   ```

2. **Left-factor the common prefix.** If all rules share `Identifier` as their prefix, introduce an intermediate category that parses the identifier and then dispatches on the second token:
   ```
   category ProcSuffix {
       SAssign = "=" Int;
       SCall   = "(" Int ")";
       SField  = "." Identifier;
       SSend   = "!" "(" Int ")";
   }

   category Proc {
       PExpr   = Identifier ProcSuffix;
       POutput = "stdout" "!" "(" Int ")";
       PNil    = "Nil";
   }
   ```
   This reduces branching from 4 to 1 for the `Identifier` token in `Proc`, pushing disambiguation to `ProcSuffix` where the second token (`=`, `(`, `.`, `!`) is unique per rule.

3. **Consolidate into a single rule with postfix dispatch.** If the rules represent variations of the same concept, unify them into one rule that matches the common prefix and then branches internally.

4. **Accept the ambiguity.** If the grammar requires all four forms and structural changes are undesirable, the WFST-ordered NFA spillover mechanism will handle it correctly -- the warning simply notes the performance cost of 4-way speculative parsing.

## Hint Explanation

**"high branching factor -- consider adding unique dispatch tokens to reduce ambiguity"** -- The "branching factor" is the number of rules that the parser must speculatively attempt when it encounters the ambiguous token. Each branch involves saving the parser state (cursor position, partial AST), attempting a parse, and either committing (on success) or restoring state and trying the next branch (on failure). With 3+ branches, the worst-case cost is 3+ full parse attempts per occurrence of that token. Adding unique dispatch tokens converts this from O(branches) speculative parsing to O(1) direct dispatch via the DFA transition table.

The `CountingWeight` semiring underlying this lint uses the `(+, x)` semiring over natural numbers. The `+` operation (addition) counts total derivation paths, and the `x` operation (multiplication) composes through sequential WFST transitions. The count thus reflects the true number of distinct parse paths reachable from the token, accounting for the full WFST structure rather than a simple rule-count heuristic.

## Related Lints

- [W02](W02-nfa-ambiguous-prefix.md) -- Fires at the 2-rule threshold for NFA spillover categories; W03 is a higher-severity version that fires at 3+ rules across all categories
- [P04](../performance/P04-many-alternatives.md) -- The performance-focused counterpart that fires when a token dispatches to > 4 rules; focuses on save/restore overhead rather than WFST prediction structure
