# W11: context-weight-narrowing

**Severity:** Note
**Category:** WFST-Specific / Context Analysis
**Feature Gate:** none (always active)

## Description

Detects dispatch points where the decision tree uses **NfaTryAll** (try every
candidate rule sequentially) but the WFST's **ContextWeight** analysis proves
that the dispatch is actually **deterministic** -- the powerset of candidate
rules narrows to a single winner when considering the ContextWeight labels.

This represents a missed optimization opportunity: the generated parser is
using the expensive NfaTryAll strategy when it could use the much cheaper
Commit strategy (dispatch directly to the single winning rule).

```
  Category "Proc", token "ident":
  ┌──────────────────────────────────────────────────┐
  │  Decision tree strategy:  NfaTryAll              │
  │    Candidates: [PApp, PVar, PRef]                │
  │                                                    │
  │  ContextWeight analysis:                          │
  │    is_deterministic_context(["ident"]) = PVar    │
  │                                                    │
  │  The NfaTryAll could be replaced with:            │
  │    Commit(PVar) for this token                    │
  └──────────────────────────────────────────────────┘
```

The **ContextWeight** powerset tracks which rules remain viable after
considering the token sequence context.  When the powerset narrows to a
singleton for a given token, the dispatch is deterministic and NfaTryAll is
unnecessary.  W11 reports these opportunities so that future optimizations
(or grammar restructuring) can upgrade the dispatch strategy.

W11 differs from [W10](W10-multi-token-lookahead.md) in its detection
mechanism: W10 checks whether *multi-token lookahead* resolves NFA spillover,
while W11 checks whether the *ContextWeight powerset* resolves NfaTryAll to
a singleton.  Both may fire for the same token -- W10 identifies that
lookahead helps, W11 identifies that the WFST already has the resolution.

## Trigger Conditions

All of the following must hold:

- The category has a decision tree AND a prediction WFST with non-empty
  `context_labels`.
- The category has a FIRST set with at least one token.
- For a specific token, the decision tree returns an `NfaTryAll` strategy
  (multiple candidate rules).
- The WFST's `is_deterministic_context(&[token])` returns `Some(label)`,
  proving singleton resolution.

One diagnostic is emitted per (category, token) pair where ContextWeight
resolves the NfaTryAll.

## Example

### Grammar

```rust
language! {
    name: ExprLang,
    types { ![i32] as Expr },
    terms {
        FnCall . f:Expr, a:Expr |- f "(" a ")" : Expr;
        VarRef . |- <ident>                    : Expr;
        NumLit . |- <int>                      : Expr;
    },
}
```

### Output

```
note[W11] (ExprLang): NfaTryAll for token `ident` in `Expr` (2 candidates) is deterministic via ContextWeight — resolves to `VarRef`
  = hint: the NFA try-all could be replaced with direct Commit dispatch for this token
```

## Resolution

1. **Restructure for distinct first tokens.**  Adding a unique leading
   terminal to each rule eliminates the NfaTryAll condition entirely.
   For instance, making `FnCall` start with a keyword (`"call" f "(" a ")"`)
   gives it a distinct dispatch token.

2. **Wait for automatic optimization.**  Future PraTTaIL versions may
   automatically promote NfaTryAll to Commit when W11 confirms determinism.
   The diagnostic documents the opportunity for the optimization pass.

3. **Accept the note.**  NfaTryAll is correct and the performance difference
   may be negligible for small candidate sets.  W11 is informational -- it
   identifies an optimization opportunity, not a correctness issue.

## Hint Explanation

The hint **"the NFA try-all could be replaced with direct Commit dispatch for
this token"** identifies the specific optimization:

- **NFA try-all** iterates through candidate rules, attempting each parse
  until one succeeds.  This is O(k) in the number of candidates.
- **Commit dispatch** directly jumps to the winning rule.  This is O(1).
- The ContextWeight analysis *proves* that the Commit result is correct,
  so the optimization is safe.

## Related Lints

- [W10](W10-multi-token-lookahead.md) -- Detects cases where multi-token
  lookahead narrows or resolves NFA spillover.  W10 and W11 may both fire
  for the same token but report different analysis paths.
- [W02](W02-nfa-ambiguous-prefix.md) -- The original NFA ambiguity
  diagnostic; W11 provides the resolution analysis.
- [W05](W05-composed-dispatch-ambiguity.md) -- Composed-level ambiguity
  resolution; W11 is the per-category ContextWeight-based version.
- [D01](../decision-tree/D01-precision-ambiguity.md) -- The decision tree's
  precision analysis, which produces the NfaTryAll strategy that W11 evaluates.
