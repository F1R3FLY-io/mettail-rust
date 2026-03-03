# PraTTaIL Lint Layer

## Overview

The lint layer (`prattail/src/lint.rs`) provides unified compile-time diagnostics for PraTTaIL grammars. It consolidates previously scattered `eprintln!` warnings into a single structured system with 23 lints across 5 categories.

For detailed per-lint documentation with examples and resolution guidance, see the
[Diagnostic Reference](../diagnostics/README.md).

## Architecture

```text
generate_parser_code()
  1. FIRST/FOLLOW set computation
  2. Cross-category overlap analysis
  3. Build prediction WFSTs + beam width
  4. Build recovery WFSTs
  ─── 5. lint::run_lints(&ctx) → Vec<LintDiagnostic> ───
  6. WFST static embedding
  7. RD handlers + trampoline + dispatch codegen
  8. Error recovery codegen
```

All lint data is borrowed from existing pipeline computations via `LintContext` — no separate analysis passes. Lints run after WFST construction but before codegen.

## Types

```rust
pub enum LintSeverity { Note, Warning, Error }

pub struct SourceLocation { pub line: u32, pub column: u32 }

pub struct LintDiagnostic {
    pub id: &'static str,                      // "G04", "W01", "C01"
    pub name: &'static str,                    // "dead-rule", "cast-cycle"
    pub severity: LintSeverity,
    pub category: Option<String>,
    pub rule: Option<String>,
    pub message: String,
    pub hint: Option<String>,
    pub grammar_name: Option<String>,          // e.g., "RhoPi"
    pub source_location: Option<SourceLocation>, // proc-macro span data
}

pub struct LintContext<'a> {
    pub grammar_name: &'a str,
    pub rule_locations: &'a HashMap<(String, String), SourceLocation>,
    /* + borrows all pipeline data */
}
```

## Display Format

Rust-compiler-style diagnostics to stderr. Diagnostics are grouped under a grammar-name header:

```
  linting grammar `RhoPi`
warning[G09]: rule `PIn` in category `Proc` has unbalanced delimiters: 0 `(` vs 1 `)`
  --> <macro>:42:9
  = in category `Proc`, rule `PIn`
  = hint: add the missing `(` delimiter

error[C01]: cast cycle detected: Int -> Proc -> Int
  = hint: break the cycle by removing one cast direction

warning[W01]: rule `FloatToStr` in category `Str` is unreachable (dead code)
  = in category `Str`, rule `FloatToStr`
  = hint: remove the rule or add a unique dispatch token

note[R07]: 36 operator pair(s) differ by 1 character (SwapTokens repair candidates): `!`↔`*`, `!`↔`+`, ... (28 more)
  = hint: the error recovery system can detect and fix common typos between these operators via SwapTokens
```

- Source location line (`-->`) shown when `line > 0` (real proc-macro span data available)
- Category/rule context line shown when category and/or rule are present
- Pipeline info messages (E1, D1, A5) are prefixed with grammar name: `info[RhoPi]: D1 ...`

## Semiring Selection

| Lint Category | Semiring | Rationale |
|---------------|----------|-----------|
| Reachability (dead rules, cast chains) | **BooleanWeight** | `(∨, ∧)` — canonical for reachability |
| Ambiguity counting | **CountingWeight** | `(+, ×)` — counts distinct derivations |
| Weight analysis (gaps, inversions) | **TropicalWeight** | `(min, +)` — on all WFST actions |
| Recovery cost analysis | **TropicalWeight + EditWeight** | Recovery costs are tropical |
| Structural checks | None | Pattern matching on `ParserBundle` data |

## Lint Catalog (23 lints)

### Grammar Structure (G01–G10)

| ID | Name | Severity | Description |
|----|------|----------|-------------|
| G01 | `left-recursion` | Warning | Rule starts with same-category NT |
| G02 | `unused-category` | Warning | Declared but never referenced |
| G03 | `ambiguous-prefix` | Warning | Multiple rules share dispatch token |
| G04 | `duplicate-rule-label` | Error | Two rules share constructor label |
| G05 | `empty-category` | Warning | Category has zero rules |
| G06 | `shadowed-operator` | Note | Same terminal as both infix and prefix |
| G07 | `identical-rules` | Warning | Two rules with identical syntax sequences |
| G08 | `missing-cast-to-root` | Warning | No cast path to primary category |
| G09 | `unbalanced-delimiters` | Warning | Opening delimiter without matching close |
| G10 | `ambiguous-associativity` | Warning | Same-precedence ops with different assoc |

### WFST-Specific (W01–W06)

| ID | Name | Severity | Description |
|----|------|----------|-------------|
| W01 | `dead-rule` | Warning | No FIRST-set token dispatches to rule |
| W02 | `nfa-ambiguous-prefix` | Warning | Multiple rules share dispatch token with equal weight |
| W03 | `high-ambiguity-token` | Warning | Token dispatches to 3+ rules |
| W04 | `weight-gap-anomaly` | Note | Gap > 5.0 between best and second-best |
| W06 | `weight-inversion` | Note | Less-specific rule has lower weight |

### Recovery (R01–R07)

| ID | Name | Severity | Description |
|----|------|----------|-------------|
| R01 | `empty-sync-set` | Warning | No sync tokens — recovery skips to EOF |
| R02 | `sparse-recovery` | Note | < 2 sync tokens |
| R05 | `missing-bracket-sync` | Warning | Bracket delimiters without closing in sync set |
| R06 | `inverted-recovery-costs` | Warning | Costs violate hierarchy |
| R07 | `transposition-candidate` | Note | Operators differing by 1 char |

### Cross-Category (C01–C04)

| ID | Name | Severity | Description |
|----|------|----------|-------------|
| C01 | `cast-cycle` | Error | Circular cast chain |
| C02 | `transitive-cast-redundancy` | Note | Direct cast alongside transitive path |
| C04 | `wide-cross-overlap` | Note | ≥ 80% FIRST set overlap |

### Performance (P02–P04)

| ID | Name | Severity | Description |
|----|------|----------|-------------|
| P02 | `high-nfa-spillover` | Note | > 3 categories need spillover buffers |
| P03 | `deep-cast-nesting` | Note | Cast chain depth > 3 |
| P04 | `many-alternatives` | Note | Token dispatches to > 4 rules |

## Recovery Synergies

| Recovery Feature | Lint Synergy |
|-----------------|-------------|
| RecoveryConfig (19 fields) | R06: validates cost hierarchy |
| Sync tokens (FOLLOW + structural) | R01, R02, R05: sync set quality |
| Transposition (SwapTokens) | R07: detects commonly-confused operator pairs |
| Bracket tracking | R05: bracket-aware recovery validation |

## Files

| File | Role |
|------|------|
| `prattail/src/lint.rs` | All 23 lint functions, types, Display, `run_lints()` |
| `prattail/src/lib.rs` | `pub mod lint;` + re-exports |
| `prattail/src/pipeline.rs` | `LintContext` construction + `run_lints()` call |

## Migration from Ad-Hoc Warnings

| Former Location | Former Function | New Lint |
|----------------|-----------------|----------|
| `prediction.rs` | `detect_grammar_warnings()` → `LeftRecursion` | G01 |
| `prediction.rs` | `detect_grammar_warnings()` → `UnusedCategory` | G02 |
| `prediction.rs` | `detect_grammar_warnings()` → `AmbiguousPrefix` | G03 |
| `pipeline.rs:725-733` | `detect_dead_rules()` + `eprintln!` | W01 |
| `pipeline.rs:945-977` | NFA ambiguity `eprintln!` block | W02 |

The original `detect_grammar_warnings()` and `detect_dead_rules()` functions are preserved for backward compatibility but are no longer called directly from the pipeline — the lint layer delegates to them internally.
