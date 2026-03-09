# Repair Suggestion Engine

| Property       | Value                                  |
|----------------|----------------------------------------|
| Feature gate   | always-on (no feature gate)            |
| Source file    | `prattail/src/repair.rs` (~1152 lines) |
| Pipeline phase | Post-analysis diagnostic enrichment    |
| Lint codes     | W01, G03, M01, T01 (enrichment)        |

## Rationale

Analysis modules detect problems (non-confluence, scope violations, dead rules) but do not prescribe fixes. The repair engine bridges this gap: it transforms analysis diagnostics into ranked, actionable repair suggestions. By leveraging semiring-derived metrics (confidence from FuzzyWeight, edit cost from EditWeight, alternatives from CountingWeight), the engine presents repairs ordered by feasibility and impact. This closes the diagnostic-to-fix loop that makes PraTTaIL's static analysis actionable for grammar authors.

## Theoretical Foundations

**Definition (Repair Suggestion).** A repair suggestion `r = (kind, desc, conf, cost, alts, action)` consists of:
- `kind in RepairKind` -- the class of fix (add rule, fix confluence, etc.)
- `desc` -- human-readable description
- `conf in [0, 1]` -- confidence that the fix is correct
- `cost in N` -- minimum edit cost to apply
- `alts in N` -- number of alternative fixes
- `action` -- concrete code/rule change

**Definition (Multi-Criteria Ranking).** The score of a suggestion is:

    score(r) = conf(r) / (cost(r) + 1)

Higher scores indicate better suggestions (high confidence, low cost).

**Theorem (Repair Completeness for Grammar Completion).** For a grammar category `C` with FIRST set `F(C)` and a set of uncovered tokens `U = F(other categories) \ F(C)`, the function `suggest_missing_rules(C, U)` produces exactly `|U|` suggestions, each covering one uncovered token.

**Definition (Congruence Repair).** For a constructor `c` of arity `n` lacking congruence rules, `suggest_congruence_rules(c, cat, n)` produces `n` suggestions, one per argument position `i in {0, ..., n-1}`, each generating a rule that rewrites argument `i` while preserving the rest.

### References

1. Bodik, R. & Jobstmann, B. (2013). "Algorithmic program synthesis: Introduction." *STTT*, 15(5-6).
2. Le Goues, C. et al. (2012). "GenProg: A generic method for automatic software repair." *IEEE TSE*, 38(1).
3. Green, T.J., Karvounarakis, G., & Tannen, V. (2007). "Provenance semirings." *PODS*.

## Algorithm Pseudocode

### 1. Semiring-Ranked Repair Ordering

```
FUNCTION rank_multi_criteria(repair_set):
    ranked := []
    FOR EACH suggestion s in repair_set:
        score := s.confidence / (s.edit_cost + 1)
        ranked.append((s, score))
    SORT ranked BY score DESCENDING
    RETURN ranked
```

### 2. Grammar Completion Suggestion

```
FUNCTION suggest_missing_rules(category, missing_tokens):
    set := new RepairSet
    FOR EACH token in missing_tokens:
        skeleton := "NewRule . {category} ::= \"{token}\" ... ;"
        suggestion := RepairSuggestion(
            kind = AddRule,
            description = "Add rule to {category} for '{token}'",
            action = AddRuleToCategory(category, skeleton),
            confidence = 0.7,
            edit_cost = 2
        )
        set.add(suggestion)
    RETURN set
```

### 3. Diagnostic Enrichment Pipeline

```
FUNCTION enrich_diagnostics_with_repairs(diagnostics, confluence_result):
    IF confluence_result is None OR is_confluent THEN RETURN
    repairs := suggest_confluence_repairs(confluence_result)
    IF repairs is empty THEN RETURN

    FOR EACH diag in diagnostics WHERE diag.id == "T01":
        repair_text := join(repairs.suggestions, "; ")
        diag.hint.append("[repair: {repair_text}]")
```

## Complexity Analysis

| Operation                       | Time         | Space       |
|---------------------------------|--------------|-------------|
| `suggest_missing_rules(n)`      | O(n)         | O(n)        |
| `suggest_congruence_rules(k)`   | O(k^2)       | O(k)        |
| `suggest_cross_category_ref(r)` | O(r)         | O(r)        |
| `sort_by_confidence`            | O(n log n)   | O(1)        |
| `rank_multi_criteria`           | O(n log n)   | O(n)        |
| `filter_by_confidence(t)`       | O(n)         | O(n)        |
| `merge(other)`                  | O(m + n)     | O(m)        |
| `enrich_diagnostics_with_repairs` | O(D . R)   | O(R)        |

Where n = suggestions, k = constructor arity, r = reachable categories, D = diagnostics, R = repair text size, m = other set size.

## Architecture Diagram

```
  ┌─────────────────────────────────────────────────────────────┐
  │                    Analysis Results                          │
  │                                                             │
  │  ConfluenceAnalysis ─┐    MorphismCheck ─┐    WpdsAnalysis  │
  │                      ▼                   ▼         │        │
  │            enrich_diagnostics    enrich_morphism    │        │
  │            _with_repairs()       _repairs()         │        │
  │                      │                   │         ▼        │
  │                      └───────┬───────────┘   verify_from    │
  │                              ▼               _bundle()      │
  │                     LintDiagnostic[]                         │
  │                      (hint enriched)                        │
  │                              │                              │
  │  ┌───────────────────────────┘                              │
  │  │                                                          │
  │  ▼                                                          │
  │  RepairDiagnostic ──▶ RepairSet ──▶ rank_multi_criteria()  │
  │       │                    │                                │
  │       ▼                    ▼                                │
  │  lint_code + severity   sorted suggestions                  │
  └─────────────────────────────────────────────────────────────┘
```

## PraTTaIL Integration

### Pipeline Bridge Functions

- **`enrich_diagnostics_with_repairs(diagnostics, confluence, syntax)`** (feature `trs-analysis`) -- Scans T01 diagnostics and appends confluence repair hints.
- **`enrich_diagnostics_with_morphism_repairs(diagnostics, morphism)`** (feature `morphisms`) -- Scans M01 diagnostics and appends morphism gap repair hints.

### Lint Enrichment

Repair suggestions are attached to existing lint codes rather than emitting new ones:

- **W01** (dead rule): Cross-category reference suggestions via `RepairDiagnostic::dead_rule()`
- **G03** (incomplete category): Missing rule and congruence suggestions via `RepairDiagnostic::missing_rule()` and `missing_congruence()`
- **T01** (non-joinable critical pair): Confluence repair hints
- **M01** (morphism gap): Morphism completion hints

### Context-Sensitive Codegen (Phase 5B.3)

`analyze_context_dispatch()` identifies categories where different callers enable different rule subsets, producing `ContextDispatchHint` records for caller-specific code generation.

### Congruence Fusion (Phase 5B.4)

`analyze_congruence_fusion()` groups congruence rules by constructor and identifies cases where multiple single-argument rules can be fused into a single multi-argument match arm.

## Rust Implementation Notes

| Type                   | Role                                                     |
|------------------------|----------------------------------------------------------|
| `RepairSuggestion`     | Single repair: kind, description, confidence, cost, action |
| `RepairKind`           | Enum: AddRule, AddCrossRef, Disambiguate, FixConfluence, etc. |
| `RepairAction`         | Concrete change: AddRuleToCategory, AddEquation, Description |
| `RepairSet`            | Collection with sort/filter/merge/ranking operations     |
| `RepairDiagnostic`     | Lint code + severity + RepairSet (structured diagnostic) |
| `DiagnosticSeverity`   | Note, Warning, Error                                     |
| `ContextDispatchHint`  | Per-caller rule subset narrowing recommendation          |
| `CongruenceFusionHint` | Multi-argument congruence fusion recommendation          |

## Worked Example

A grammar has constructor `Add` in category `Expr` with arity 2 but no congruence rules.

**Step 1: Detect.** The pipeline identifies that `Add` has no congruence rules.

**Step 2: Suggest.** `suggest_congruence_rules("Add", "Expr", 2)` produces:

```
Suggestion 1: Add congruence rule for Add at argument position 0
  Action: AddCong0 . |- S ~> T |- (Add S X1) ~> (Add T X1) ;
  Confidence: 0.95, Edit cost: 1

Suggestion 2: Add congruence rule for Add at argument position 1
  Action: AddCong1 . |- S ~> T |- (Add X0 S) ~> (Add X0 T) ;
  Confidence: 0.95, Edit cost: 1
```

**Step 3: Rank.** `rank_multi_criteria()` scores both at `0.95 / 2 = 0.475`.

**Step 4: Emit.** `RepairDiagnostic::missing_congruence("Add", "Expr", 2)` produces:

```
[G03-note] constructor 'Add' in 'Expr' has no congruence rules
  Suggestions:
    1. Add congruence rule for Add at position 0 (confidence: 95%, cost: 1)
    2. Add congruence rule for Add at position 1 (confidence: 95%, cost: 1)
```

## References

1. Bodik, R. & Jobstmann, B. (2013). "Algorithmic program synthesis." *STTT*, 15(5-6).
2. Le Goues, C. et al. (2012). "GenProg: A generic method for automatic software repair." *IEEE TSE*, 38(1).
3. Green, T.J., Karvounarakis, G., & Tannen, V. (2007). "Provenance semirings." *PODS*.
4. Knuth, D.E. & Bendix, P.B. (1970). "Simple word problems in universal algebras." *Computational Problems in Abstract Algebra*.
5. Baader, F. & Nipkow, T. (1998). *Term Rewriting and All That.* Cambridge University Press.
