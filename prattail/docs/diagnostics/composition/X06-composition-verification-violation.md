# X06: composition-verification-violation

**Severity:** Warning (CVT property violation) / Note (common sublanguage report)
**Category:** composition
**Feature Gate:** None (always enabled when grammar composition is used)

## Description

Reports violations detected by the Composition Verification Table (CVT) during
grammar composition, and also reports common sublanguage structure between the
two source grammars. X06 serves a dual role:

### CVT Property Violations (Warning)

When two grammars are composed via `compose()`, the merged WFST is verified
against four correctness properties:

1. **LanguageContainment**: Every (token, action) pair in each source WFST must
   exist in the merged WFST. A violation means the composition lost a valid
   parse path.

2. **NoSpuriousActions**: The merged WFST must not contain (token, action) pairs
   that do not exist in either source. A violation means the composition
   introduced phantom parse paths.

3. **WeightConsistency**: For shared (token, action) pairs, the merged WFST's
   weight must be the tropical minimum of the two source weights. A violation
   means weight resolution is incorrect.

4. **DispatchDeterminismPreservation**: Tokens that are deterministic (single
   action) in both source WFSTs must remain bounded in the merged WFST. A
   violation means the composition introduced new ambiguity.

```
  CVT verification matrix:

  ┌────────────────────────────────────┬────────────┬──────────┐
  │ Property                           │ Source     │ Merged   │
  ├────────────────────────────────────┼────────────┼──────────┤
  │ LanguageContainment                │ A ∪ B ⊆ M │ verified │
  │ NoSpuriousActions                  │ M ⊆ A ∪ B │ verified │
  │ WeightConsistency                  │ w(M) =    │ verified │
  │                                    │ min(A, B) │          │
  │ DispatchDeterminismPreservation    │ det(A) ∩   │ verified │
  │                                    │ det(B)⊆det│          │
  └────────────────────────────────────┴────────────┴──────────┘
```

### Common Sublanguage Report (Note)

After CVT verification, X06 also performs a decision tree composition analysis
that compares the dispatch tries of the two source grammars for shared
categories. It reports the number of common dispatch paths (the sublanguage
shared by both grammars), paths unique to each source, and any new ambiguities
introduced by the composition.

## Trigger Conditions

### CVT Violations

- Two grammars are composed via `compose()`.
- The CVT verification (`composition_verify::verify_composition()`) reports at
  least one property where `holds == false`.
- One diagnostic is emitted per violation string within each failed property.

### Common Sublanguage

- Two grammars are composed and both have decision trees for at least one
  shared category.
- `composition_trie_analysis()` reports `common_rules > 0` for at least one
  shared category.
- One diagnostic is emitted per shared category with common rules.

## Example

### CVT Violation Output

```
warning[X06] (AmbientCalc): composition verification [WeightConsistency]: token `+` has weight 1.5 in merged but min(2.0, 1.0) = 1.0 in sources
  = hint: review the composed grammar for property violations
```

### Common Sublanguage Output

```
note[X06] (AmbientCalc): composition: 5 common dispatch paths, 3 unique to A, 7 unique to B
  = in category `Expr`
```

### New Ambiguity Output (X07)

```
warning[X07] (AmbientCalc): composition introduces 2 new ambiguous dispatch point(s) not present in either source
  = in category `Proc`
```

## Resolution

### For CVT Violations

1. **Review the grammar composition.** Ensure that the two source grammars are
   compatible for composition. Check that shared categories use consistent
   token vocabularies and action semantics.

2. **Fix weight inconsistencies.** If WeightConsistency fails, ensure that
   the weight resolution policy (tropical minimum) is appropriate for the
   composed grammar's semantics.

3. **Resolve spurious actions.** If NoSpuriousActions fails, examine the
   merged WFST for (token, action) pairs that should not exist. This usually
   indicates a bug in the composition algorithm.

4. **Restore determinism.** If DispatchDeterminismPreservation fails, the
   composition introduced ambiguity. Left-factor the conflicting rules or
   add priority annotations to restore deterministic dispatch.

### For Common Sublanguage Reports

No action required. The common sublanguage report is informational, showing
the structural overlap between the two source grammars.

## Hint Explanation

The hint **"review the composed grammar for property violations"** directs the
user to examine the composed grammar specification. CVT violations indicate
that the composition algorithm produced a WFST that does not faithfully
represent the union of the two source languages. The four properties
(containment, no spurious actions, weight consistency, determinism
preservation) are the minimal correctness criteria for a sound composition.

## Related Lints

- [X01](X01-composition-ambiguity-introduction.md) -- Composition ambiguity
  introduction. Detects when composition creates new ambiguous dispatch points.
- [X02](X02-composition-priority-shadowing.md) -- Composition priority
  shadowing. Detects when one grammar's priorities shadow another's.
- [X03](X03-composition-dead-rule-creation.md) -- Composition dead rule
  creation. Detects when composition makes previously live rules unreachable.
- [X07](X07-composition-introduced-ambiguity.md) -- Composition introduced
  ambiguity. The per-category counterpart to X06's new ambiguity detection.
