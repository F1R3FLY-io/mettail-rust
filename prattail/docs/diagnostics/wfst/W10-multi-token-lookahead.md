# W10: multi-token-lookahead

**Severity:** Note
**Category:** WFST-Specific / NFA Spillover
**Feature Gate:** none (always active)

## Description

Detects NFA spillover situations where **single-token dispatch** is
insufficient to resolve which rule to parse, but **multi-token lookahead**
(typically 2-token) can narrow or fully resolve the ambiguity.  NFA spillover
occurs when the decision tree's dispatch for a given token falls back to
`NfaTryAll` -- trying every candidate rule sequentially until one succeeds.
W10 identifies cases where this expensive try-all could be replaced by
deterministic or narrowed dispatch with additional lookahead.

The lint has two sub-variants:

**Variant 1: Fully deterministic.**  The WFST's `is_deterministic_context()`
confirms that 1-token lookahead resolves the spillover to a single rule.

```
  Category "Proc", token "kw_new":
  ┌──────────────────────────────────────────────┐
  │  Single-token dispatch:   NfaTryAll           │
  │    Candidates: [PNew, PNewName, PNewChan]     │
  │                                                │
  │  1-token lookahead (WFST context):            │
  │    "kw_new" + next_token -> PNew (unique)     │
  │                                                │
  │  Result: spillover could be eliminated         │
  └──────────────────────────────────────────────┘
```

**Variant 2: Narrowed but not deterministic.**  The WFST's
`context_narrowing()` reduces the candidate set but does not eliminate
ambiguity completely.

```
  Category "Proc", token "kw_for":
  ┌──────────────────────────────────────────────┐
  │  Single-token dispatch:   NfaTryAll           │
  │    Candidates: [PFor, PForEach, PForAll]      │
  │                                                │
  │  ContextWeight analysis narrows:              │
  │    3 candidates -> 1 candidate                │
  │                                                │
  │  Result: ambiguity reduced but not eliminated  │
  └──────────────────────────────────────────────┘
```

When multiple W10 diagnostics are emitted for a grammar, the grouper
consolidates them into a per-category summary:

```
note[W10] (RhoCalc): 2 categories could eliminate NFA spillover with k-token lookahead: Proc, Name
```

## Trigger Conditions

For each category that has NFA spillover, the lint checks each dispatch
token:

- **Variant 1:** The token group has more than one candidate rule AND
  `wfst.is_deterministic_context(&[token])` returns `Some(label)`, meaning
  1-token lookahead fully resolves the group.

- **Variant 2:** The token group has more than one candidate rule AND
  `wfst.context_narrowing(&[token])` returns a narrowed count that is
  both greater than zero and less than the original candidate count.

One diagnostic is emitted per (category, token) pair.

## Example

### Grammar

```rust
language! {
    name: ProcLang,
    types { ![String] as Proc, ![String] as Name },
    terms {
        PNew     . n:Name, p:Proc |- "new" n "in" p : Proc;
        PNewName . n:Name         |- "new" n        : Proc;
        NVar     . |- <ident>     : Name;
    },
}
```

### Output (Variant 1)

```
note[W10] (ProcLang): NFA spillover for token `kw_new` in `Proc` could be eliminated with 1-token lookahead (resolves to `PNew`)
  = hint: two-token WFST disambiguation resolves this group deterministically
```

### Output (Variant 2)

```
note[W10] (ProcLang): NFA spillover for token `kw_for` in `Proc` narrows from 3 to 1 candidates with ContextWeight analysis
  = hint: consider extending lookahead depth to further reduce ambiguity
```

## Resolution

1. **Restructure rules for distinct prefixes.**  The most robust fix is to
   give each rule a unique leading token sequence.  If `PNew` and `PNewName`
   both start with `"new"`, adding a distinguishing keyword
   (e.g., `"new" "name"` vs `"new" "chan"`) eliminates the spillover entirely.

2. **Leverage the information.**  W10 confirms that the WFST already *can*
   resolve the ambiguity with lookahead.  Future PraTTaIL versions may
   automatically upgrade NfaTryAll to lookahead dispatch when W10 fires.
   For now, the note documents the opportunity.

3. **Accept the spillover.**  NFA try-all is correct -- it just tries each
   candidate sequentially.  For small candidate sets (2-3 rules), the
   performance cost is negligible.  W10 is informational.

## Hint Explanation

The two hint variants correspond to the two detection modes:

- **"two-token WFST disambiguation resolves this group deterministically"**
  (Variant 1): The WFST analysis proves that the first two tokens uniquely
  determine which rule to parse.  The NFA try-all is doing unnecessary work.

- **"consider extending lookahead depth to further reduce ambiguity"**
  (Variant 2): The 2-token analysis narrows but does not eliminate the
  ambiguity.  Extending to 3-token or deeper lookahead may achieve full
  determinism.

## Related Lints

- [W02](W02-nfa-ambiguous-prefix.md) -- Detects the NFA ambiguity itself
  (multiple rules share a first token).  W10 extends the analysis by checking
  whether lookahead resolves the ambiguity.
- [W11](W11-context-weight-narrowing.md) -- Detects cases where ContextWeight
  analysis narrows NfaTryAll dispatch to a singleton, a complementary
  analysis to W10.
- [W05](W05-composed-dispatch-ambiguity.md) -- Detects ambiguities at the
  composed dispatch level; W10 operates at the per-category NFA level.
- [D01](../decision-tree/D01-precision-ambiguity.md) -- The decision tree's
  own ambiguity analysis, which may already incorporate lookahead information.
