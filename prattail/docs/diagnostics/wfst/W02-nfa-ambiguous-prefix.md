# W02: nfa-ambiguous-prefix

**Severity:** Warning
**Category:** WFST-Specific

## Description

Detects ambiguous prefix dispatch in categories that require NFA spillover. When a category is in `nfa_spillover_categories`, it means the deterministic DFA dispatch table cannot uniquely assign a single rule to every leading token -- some tokens map to multiple rules, and the parser must use NFA-style backtracking (with spillover buffers) to resolve the ambiguity at parse time.

This lint fires when multiple recursive-descent (RD) rules within such a category share the same dispatch token. The prediction WFST is queried via `nfa_alternative_order()` to determine the ordering of alternatives by their tropical weights. If all alternatives have equal weights (difference < 1e-12), the lint notes that resolution is deferred to semantic disambiguation, meaning the parser will try each alternative in declaration order until one succeeds.

Ambiguous prefix dispatch has two concrete costs: (1) wasted parse attempts when early alternatives fail, and (2) harder-to-predict parser behavior for grammar authors. Assigning distinct WFST weights or adding distinguishing leading tokens eliminates both costs.

## Trigger Conditions

A W02 diagnostic fires when **all** of the following hold:

1. The category `cat` is a member of `nfa_spillover_categories` (it has NFA-level ambiguity that requires spillover buffers).

2. `group_rd_by_dispatch_token_pub(rd_rules, cat)` returns a dispatch group where a single token maps to 2 or more RD rules.

3. The category has a prediction WFST in `prediction_wfsts`.

4. For each ambiguous token, `wfst.nfa_alternative_order(token, &labels)` returns the weight-ordered alternatives. If all weights are within 1e-12 of each other, the message includes the "equal weight / deferred resolution" annotation.

## Example

### Grammar

```
language! {
    name: MiniLang;
    primary: Proc;

    category Int {
        native_type: Integer;

        IntLit    = <int>;
        IntNeg    = "-" Int;
        IntAdd    = Int "+" Int;
    }

    category Bool {
        native_type: Boolean;

        BoolLit   = <bool>;
        BoolNot   = "!" Bool;
        BoolAnd   = Bool "&&" Bool;
    }

    category Proc {
        // Both rules start with identifier token — ambiguous prefix
        PNew      = "new" Identifier "in" Proc;
        PNewRho   = "new" Identifier "," Identifier "in" Proc;

        // Both rules start with "for" — ambiguous prefix
        PFor      = "for" "(" Identifier "<-" Int ")" Proc;
        PForAll   = "for" "(" Identifier "<-" Int ";" Bool ")" Proc;

        POutput   = "stdout" "!" "(" Int ")";
        PNil      = "Nil";
        CastInt   = Int;
    }
}
```

### Output

```
warning[W02]: ambiguous prefix dispatch for token `new` in category `Proc`: rules [PNew, PNewRho] all match — all 2 alternatives have equal weight (0.5); resolution deferred to semantic disambiguation
  = in category `Proc`
  = hint: add distinguishing syntax or assign different WFST weights to resolve the ambiguity

warning[W02]: ambiguous prefix dispatch for token `for` in category `Proc`: rules [PFor, PForAll] all match — all 2 alternatives have equal weight (0.5); resolution deferred to semantic disambiguation
  = in category `Proc`
  = hint: add distinguishing syntax or assign different WFST weights to resolve the ambiguity
```

## Resolution

There are three main strategies to resolve an NFA ambiguous prefix:

1. **Add distinguishing leading tokens.** Redesign the grammar so that each rule has a unique first terminal. For example, rename `PForAll` to use `"forall"` as its keyword instead of reusing `"for"`:
   ```
   PForAll = "forall" "(" Identifier "<-" Int ";" Bool ")" Proc;
   ```

2. **Assign distinct WFST weights.** If the ambiguous prefix is intentional (e.g., the grammar genuinely needs both forms), assign different weights so the WFST orders them deterministically. The parser will try the lower-weight (preferred) alternative first. If it fails, the spillover mechanism falls back to the higher-weight alternative.

3. **Merge into a single rule with optional syntax.** If the two forms are minor variations, combine them using an optional group:
   ```
   PNew = "new" Identifier ["," Identifier] "in" Proc;
   ```
   This eliminates the ambiguity entirely because there is only one rule to dispatch to.

## Hint Explanation

**"add distinguishing syntax or assign different WFST weights to resolve the ambiguity"** -- The two strategies address different use cases. Adding distinguishing syntax (a unique leading token for each rule) eliminates the ambiguity structurally: the DFA dispatch table can then assign each token to exactly one rule without spillover. Assigning different WFST weights preserves the shared prefix but gives the parser a deterministic preference order: the lower-weight alternative is tried first, and the spillover mechanism handles fallback to the higher-weight alternative. The choice depends on whether the shared prefix is a design constraint (use weights) or an accidental collision (add distinguishing syntax).

When the lint reports "all alternatives have equal weight ... resolution deferred to semantic disambiguation," it means the WFST cannot break the tie, and the parser falls back to declaration order. This is functional but fragile: reordering rules in the grammar silently changes parse behavior.

## Related Lints

- [G03](../grammar/G03-ambiguous-prefix.md) -- The structural (non-WFST) counterpart; detects ambiguous prefixes using FIRST-set overlap without considering NFA spillover or WFST weights
- [W03](W03-high-ambiguity-token.md) -- Fires when a token dispatches to 3 or more rules (W02 fires at 2+); W03 focuses on the branching factor cost rather than the NFA spillover mechanism
