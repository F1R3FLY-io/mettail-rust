# W04: weight-gap-anomaly

**Severity:** Note
**Category:** WFST-Specific

## Description

Detects tokens where the prediction WFST assigns two or more rules but the weight gap between the best (lowest) and second-best rule exceeds 5.0 on the tropical semiring scale. A large weight gap indicates that the parser is treating the token as ambiguous (allocating NFA spillover, generating multiple dispatch paths) when in practice the second-best alternative is so heavily penalized that it will almost never be chosen.

This lint is informational rather than actionable: it highlights places where the grammar is effectively deterministic despite the formal ambiguity. Grammar authors can use this information to either:

- Restructure the grammar to make the determinism explicit (eliminating the overhead of speculative parsing for this token).
- Confirm that the WFST weight assignment correctly reflects their intent, and accept the minor overhead.

The tropical semiring `(min, +)` assigns lower weights to preferred alternatives. A gap of 5.0 means the second-best path costs at least 5 additional units, which in probability terms (when weights represent negative log-probabilities) corresponds to the second alternative being roughly e^(-5) ~ 0.007x as likely as the best.

## Trigger Conditions

A W04 diagnostic fires when **all** of the following hold:

1. The category `cat` has a prediction WFST in `prediction_wfsts`.

2. The category has a FIRST set in `first_sets`.

3. For a token `t` in `first_set.sorted_tokens()`, calling `wfst.predict(t)` returns at least 2 `WeightedAction` entries (sorted by ascending weight).

4. The gap `actions[1].weight.value() - actions[0].weight.value()` is strictly greater than 5.0.

## Example

### Grammar

```
language! {
    name: RhoPiSubset;
    primary: Proc;

    category Int {
        native_type: Integer;

        IntLit     = <int>;
        IntNeg     = "-" Int;
        IntAdd     = Int "+" Int;
        IntMul     = Int "*" Int;
        IntSub     = Int "-" Int;
    }

    category Bool {
        native_type: Boolean;

        BoolLit    = <bool>;
        BoolEq     = Int "==" Int;
        BoolNot    = "!" Bool;
        BoolAnd    = Bool "&&" Bool;
    }

    category Proc {
        POutput    = "stdout" "!" "(" Int ")";
        PInput     = "stdin" "?" "(" Identifier ")" Proc;
        PIf        = "if" Bool "then" Proc "else" Proc;

        // Both match starting from Int; prediction WFST assigns very
        // different weights because PEval has a much more specific
        // context path through the grammar
        PEval      = "eval" "(" Int ")";
        PEvalDebug = "eval" "(" Int "," Bool ")";

        PNil       = "Nil";
        CastInt    = Int;
        CastBool   = Bool;
    }
}
```

In this grammar, both `PEval` and `PEvalDebug` share the dispatch token `"eval"`. Suppose the WFST training or static weight assignment gives `PEval` a weight of 0.3 (very common pattern) and `PEvalDebug` a weight of 7.1 (rare debug-mode variant). The gap is 6.8, which exceeds the 5.0 threshold.

### Output

```
note[W04]: token `eval` in category `Proc`: gap of 6.8 between best rule `PEval` (weight 0.3) and second-best `PEvalDebug` (weight 7.1) — near-deterministic treated as ambiguous
  = in category `Proc`
  = hint: the large weight gap suggests this token is effectively unambiguous — the second alternative is very unlikely
```

## Resolution

This is an informational diagnostic (severity: Note). No action is required, but the following options are available:

1. **Make the determinism explicit.** If `PEvalDebug` is truly a rare variant, give it a distinct leading token to remove the formal ambiguity:
   ```
   PEvalDebug = "eval_debug" "(" Int "," Bool ")";
   ```
   This eliminates the NFA spillover overhead for the `"eval"` token entirely.

2. **Accept the note.** The WFST-ordered dispatch will correctly prefer `PEval` in virtually all cases. The spillover mechanism will fall back to `PEvalDebug` only when `PEval` fails to parse (e.g., when the debug-mode `, Bool` suffix is present). The performance cost is minimal since the first alternative almost always succeeds.

3. **Adjust weights to narrow the gap.** If the gap is artificially large due to weight initialization rather than genuine frequency data, adjust the WFST weights so they more accurately reflect the expected frequency of each form.

## Hint Explanation

**"the large weight gap suggests this token is effectively unambiguous -- the second alternative is very unlikely"** -- In the tropical semiring, weights represent costs (lower is better). When the prediction WFST sorts alternatives by weight, a gap of > 5.0 means the second-best alternative is at least 5 cost units worse than the best. If weights are calibrated as negative log-probabilities, this corresponds to the second alternative being approximately 150x less likely than the first (e^5 ~ 148.4).

Despite this extreme asymmetry, the parser still treats the token as formally ambiguous: it allocates spillover buffers, generates NFA backtracking paths, and maintains save/restore points for the unlikely alternative. The note informs grammar authors that this overhead -- while functionally correct -- could be eliminated by restructuring the grammar to remove the formal ambiguity.

The 5.0 threshold was chosen empirically: gaps below 5.0 represent genuinely competitive alternatives where the parser's speculative behavior adds value, while gaps above 5.0 indicate near-certainty about which rule will succeed.

## Related Lints

- [W02](W02-nfa-ambiguous-prefix.md) -- Fires when multiple NFA spillover rules share a dispatch token; W04 identifies cases where that ambiguity is practically irrelevant due to weight asymmetry
- [W06](W06-weight-inversion.md) -- Detects cases where weight ordering contradicts specificity ordering; W04 detects cases where weight ordering is correct but excessively decisive
