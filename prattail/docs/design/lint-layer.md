# PraTTaIL Lint Layer

## Overview

The lint layer (`prattail/src/lint.rs`) provides unified compile-time diagnostics for PraTTaIL grammars. It consolidates all diagnostic output into a single structured system with ANSI-colorized, Rust-compiler-style formatting. All pipeline info messages, warnings, and errors now route through `LintDiagnostic` structs and `format_diagnostic_colored()` for consistent output.

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
  5b. Decision tree analysis (D01–D09)
  6. WFST static embedding
  7. RD handlers + trampoline + dispatch codegen
  8. Error recovery codegen
```

All lint data is borrowed from existing pipeline computations via `LintContext` — no separate analysis passes. Lints run after WFST construction but before codegen.

## Types

```rust
pub enum LintSeverity { Info, Note, Warning, Error }

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
- Grammar name shown in dim parentheses after `[ID]` when present: `info[I01] (RhoPi): transducer cascade: ...`
- All pipeline info messages, EBNF dumps, env overrides, and composition verification now route through the lint system

## Semiring Selection

| Lint Category | Semiring | Rationale |
|---------------|----------|-----------|
| Reachability (dead rules, cast chains) | **BooleanWeight** | `(∨, ∧)` — canonical for reachability |
| Ambiguity counting | **CountingWeight** | `(+, ×)` — counts distinct derivations |
| Weight analysis (gaps, inversions) | **TropicalWeight** | `(min, +)` — on all WFST actions |
| Recovery cost analysis | **TropicalWeight + EditWeight** | Recovery costs are tropical |
| Structural checks | None | Pattern matching on `ParserBundle` data |
| Safety verification (prestar) | **BooleanWeight** | `(∨, ∧)` — reachability to bad states |
| CEGAR refinement ladder | **Boolean → Counting → Tropical** | Progressive precision for abstraction refinement |
| Provenance tracking | **ProvenanceWeight** | N[X] polynomial — tracks derivation source |
| KAT decision | None (algebraic structure) | Automata-based PSPACE decision |
| Repair ranking | **FuzzyWeight + EditWeight + CountingWeight** | Multi-criteria suggestion scoring |

## Severity Levels

| Level | Color | Description |
|-------|-------|-------------|
| `Info` | Bold cyan | Infrastructure progress messages — pipeline status |
| `Note` | Bold cyan | Informational — no action required |
| `Warning` | Bold yellow | Possible issue — review recommended |
| `Error` | Bold red | Correctness bug — compilation may fail |

Ordering: `Info < Note < Warning < Error`

## Lint Catalog

### Grammar Structure (G01–G10, G24–G31)

| ID  | Name                            | Severity | Description                               |
|-----|---------------------------------|----------|-------------------------------------------|
| G01 | `left-recursion`                | Warning  | Rule starts with same-category NT         |
| G02 | `unused-category`               | Warning  | Declared but never referenced             |
| G03 | `ambiguous-prefix`              | Warning  | Multiple rules share dispatch token       |
| G04 | `duplicate-rule-label`          | Error    | Two rules share constructor label         |
| G05 | `empty-category`                | Warning  | Category has zero rules                   |
| G06 | `shadowed-operator`             | Note     | Same terminal as both infix and prefix    |
| G07 | `identical-rules`               | Warning  | Two rules with identical syntax sequences |
| G08 | `missing-cast-to-root`          | Warning  | No cast path to primary category          |
| G09 | `unbalanced-delimiters`         | Warning  | Opening delimiter without matching close  |
| G10 | `ambiguous-associativity`       | Warning  | Same-precedence ops with different assoc  |
| G24 | `alpha-equivalent-rules`        | Note     | Rules with identical De Bruijn structure  |
| G25 | `cancellation-pair-detected`    | Note     | Equation `Outer(Inner(X)) = X` suppressed |
| G26 | `equation-subsumed`             | Note     | Equation eliminated by subsumption        |
| G27 | `rule-subsumption-candidate`    | Warning  | Rule may be subsumed by more general rule |
| G28 | `alpha-equivalent-groups`       | Note     | Alpha-equivalent LHS pattern groups       |
| G29 | `dependency-groups`             | Note     | Fine-grained dependency groups            |
| G30 | `isomorphic-wfst-groups`        | Note     | Isomorphic WFST dispatch topology         |
| G31 | `subsumed-equations-eliminated` | Note     | N equations eliminated from codegen       |

### WFST-Specific (W01–W09)

| ID  | Name                                | Severity | Description                                           |
|-----|-------------------------------------|----------|-------------------------------------------------------|
| W01 | `dead-rule`                         | Warning  | No FIRST-set token dispatches to rule                 |
| W02 | `nfa-ambiguous-prefix`              | Warning  | Multiple rules share dispatch token with equal weight |
| W03 | `high-ambiguity-token`              | Warning  | Token dispatches to 3+ rules                          |
| W04 | `weight-gap-anomaly`                | Note     | Gap > 5.0 between best and second-best                |
| W05 | `composed-dispatch-ambiguity`       | Warning  | N-way ambiguity in composed dispatch table            |
| W06 | `weight-inversion`                  | Note     | Less-specific rule has lower weight                   |
| W09 | `cancellation-pair-missing-rewrite` | Warning  | Suppressed equation has no corresponding rewrite      |

### Recovery (R01–R07)

| ID  | Name                      | Severity | Description                                    |
|-----|---------------------------|----------|------------------------------------------------|
| R01 | `empty-sync-set`          | Warning  | No sync tokens — recovery skips to EOF         |
| R02 | `sparse-recovery`         | Note     | < 2 sync tokens                                |
| R05 | `missing-bracket-sync`    | Warning  | Bracket delimiters without closing in sync set |
| R06 | `inverted-recovery-costs` | Warning  | Costs violate hierarchy                        |
| R07 | `transposition-candidate` | Note     | Operators differing by 1 char                  |

### Cross-Category (C01–C04)

| ID  | Name                         | Severity | Description                           |
|-----|------------------------------|----------|---------------------------------------|
| C01 | `cast-cycle`                 | Error    | Circular cast chain                   |
| C02 | `transitive-cast-redundancy` | Note     | Direct cast alongside transitive path |
| C04 | `wide-cross-overlap`         | Note     | ≥ 80% FIRST set overlap               |

### Composition (X06)

| ID  | Name                              | Severity | Description                          |
|-----|-----------------------------------|----------|--------------------------------------|
| X06 | `composition-verification-violation` | Warning | CVT property violation              |

### Decision Tree (D01–D09)

| ID  | Name                        | Severity | Description                                               |
|-----|-----------------------------|----------|-----------------------------------------------------------|
| D01 | `precision-ambiguity`       | Note     | Token path with conflicting rules and overlap tokens      |
| D02 | `unresolvable-ambiguity`    | Warning  | No finite lookahead resolves -- inherent grammar conflict |
| D03 | `trie-unreachable-rule`     | Warning  | Rule shadowed by higher-priority path in PathMap trie     |
| D04 | `min-lookahead-depth`       | Note     | Per-category minimum lookahead tokens                     |
| D05 | `decision-tree-summary`     | Note     | States, deterministic/ambiguous ratio, depth, savings     |
| D06 | `wfst-trie-inconsistency`   | Warning  | WFST prediction vs trie reachability mismatch             |
| D07 | `path-coverage-report`      | Note     | Untested trie paths (opt-in `PRATTAIL_COVERAGE=1`)        |
| D08 | `optimization-suggestion`   | Note     | Grammar modifications to resolve PathMap ambiguity        |
| D09 | `conflict-resolution-guide` | Note     | Strategies for genuine conflicts in PathMap trie          |

### TRS Analysis (T01–T04)

| ID  | Name                           | Severity | Feature Gate    | Description                                           |
|-----|--------------------------------|----------|-----------------|-------------------------------------------------------|
| T01 | `non-joinable-critical-pair`   | Warning  | `trs-analysis`  | Critical pair not joinable — confluence failure       |
| T02 | `confluence-verified`          | Note     | `trs-analysis`  | All critical pairs joinable — system is confluent     |
| T03 | `non-terminating-cycle`        | Warning  | `trs-analysis`  | Dependency pair SCC with non-decreasing cycle         |
| T04 | `termination-verified`         | Note     | `trs-analysis`  | All SCCs have decreasing measures — system terminates |

### Automata Analysis (V01–V04)

| ID  | Name                     | Severity | Feature Gate     | Description                                              |
|-----|--------------------------|----------|------------------|----------------------------------------------------------|
| V01 | `vpa-determinizable`     | Note     | `vpa`            | Grammar admits zero-backtracking VPA                     |
| V02 | `vpa-alphabet-mismatch`  | Warning  | `vpa`            | Delimiter classified as both call and return              |
| V03 | `wta-unrecognized-term`  | Warning  | `tree-automata`  | Term pattern not in regular tree language                |
| V04 | `wta-hot-path`           | Note     | `tree-automata`  | High-frequency term pattern — specialization candidate   |

### Safety & Verification (S01–S06)

| ID  | Name                  | Severity | Feature Gate     | Description                                  |
|-----|-----------------------|----------|------------------|----------------------------------------------|
| S01 | `safety-violation`    | Warning  | always-on        | Bad state reachable via WPDS prestar         |
| S02 | `safety-verified`     | Note     | always-on        | No bad states reachable — safety verified    |
| S03 | `cegar-refinement`    | Note     | always-on        | CEGAR refinement step count and verdict      |
| S04 | `ewpds-merge-site`    | Note     | `wpds-extended`  | EWPDS merge function attachment points       |
| S05 | `ara-invariant`       | Note     | `wpds-ara`       | ARA affine-relation invariants discovered    |
| S06 | `algebraic-summary`   | Note     | always-on        | Tarjan SCC path expression summary           |

### Concurrency (N01–N05)

| ID  | Name                 | Severity | Feature Gate   | Description                                           |
|-----|----------------------|----------|----------------|-------------------------------------------------------|
| N01 | `deadlock-risk`      | Warning  | `petri`        | Petri net coverability detects potential deadlock      |
| N02 | `unbounded-channel`  | Warning  | `petri`        | Place has unbounded token capacity                    |
| N03 | `scope-violation`    | Warning  | `nominal`      | Name used outside its binding scope                   |
| N04 | `scope-narrowing`    | Note     | `nominal`      | PNew scope can be tightened                           |
| N05 | `non-bisimilar`      | Warning  | `alternating`  | Categories not bisimilar — attacker wins game         |

### Temporal (L01–L02)

| ID  | Name            | Severity | Feature Gate | Description                                      |
|-----|-----------------|----------|--------------|--------------------------------------------------|
| L01 | `ltl-violated`  | Warning  | `ltl`        | LTL property violated — Buchi product non-empty  |
| L02 | `ltl-verified`  | Note     | `ltl`        | LTL properties satisfied                         |

### Extension (E01–E02)

| ID  | Name                 | Severity | Feature Gate   | Description                                      |
|-----|----------------------|----------|----------------|--------------------------------------------------|
| E01 | `provenance-trace`   | Note     | `provenance`   | How-provenance polynomial tracking summary       |
| E02 | `cra-cost-anomaly`   | Warning  | `cra`          | CRA register value exceeds threshold             |

### Morphism (M01–M02)

| ID  | Name                             | Severity | Feature Gate | Description                                     |
|-----|----------------------------------|----------|--------------|-------------------------------------------------|
| M01 | `morphism-gap`                   | Warning  | `morphisms`  | Theory morphism missing sort/operation mapping  |
| M02 | `morphism-preservation-failure`  | Warning  | `morphisms`  | Axiom not preserved under morphism              |

### KAT (K01–K02)

| ID  | Name               | Severity | Feature Gate | Description                      |
|-----|---------------------|----------|--------------|----------------------------------|
| K01 | `hoare-failure`     | Warning  | `kat`        | Hoare triple {p} e {q} fails    |
| K02 | `kat-equivalence`   | Note     | `kat`        | KAT expression equivalence result |

### Performance (P02–P06)

| ID  | Name                    | Severity | Description                                   |
|-----|-------------------------|----------|-----------------------------------------------|
| P02 | `high-nfa-spillover`    | Note     | > 3 categories need spillover buffers         |
| P03 | `deep-cast-nesting`     | Note     | Cast chain depth > 3                          |
| P04 | `many-alternatives`     | Note     | Token dispatches to > 4 rules                 |
| P05 | `wpds-pipeline-cost`    | Info     | WPDS analysis wall-clock time and sizes       |
| P06 | `analysis-pipeline-cost`| Note     | Mathematical analysis phase wall-clock time   |

### Infrastructure (I01–I12)

| ID  | Name                       | Severity | Source File       | Description                           |
|-----|----------------------------|----------|-------------------|---------------------------------------|
| I01 | `transducer-cascade`       | Info     | pipeline.rs       | E1 cascade summary                    |
| I02 | `cascade-skipped`          | Info     | pipeline.rs       | B3 trivial grammar skips cascade      |
| I03 | `adaptive-beam`            | Info     | pipeline.rs       | A7 entropy-based beam width           |
| I04 | `beam-feature-required`    | Warning  | pipeline.rs       | Auto beam needs `wfst-log`            |
| I05 | `cost-benefit-recommendations` | Info | pipeline.rs       | D1 optimization recommendations       |
| I06 | `enhanced-dce-active`      | Info     | pipeline.rs       | A4 dead rule suppression              |
| I07 | `ambiguity-targeting`      | Info     | pipeline.rs       | A5 ambiguity analysis                 |
| I08 | `env-override-active`      | Warning  | cost_benefit.rs   | PRATTAIL_AUTO_OPTIMIZE active         |
| I09 | `env-override-parse-error` | Error    | cost_benefit.rs   | PRATTAIL_AUTO_OPTIMIZE parse fail     |
| I10 | `ascent-file-write-failed` | Warning  | macros logic/mod.rs | Ascent Datalog file I/O error       |
| I11 | `ebnf-dump-failed`         | Warning  | ebnf.rs           | EBNF dump I/O failure                 |
| I12 | `ebnf-dump-success`        | Info     | ebnf.rs           | EBNF dump written                     |

## Recovery Synergies

| Recovery Feature                  | Lint Synergy                                  |
|-----------------------------------|-----------------------------------------------|
| RecoveryConfig (19 fields)        | R06: validates cost hierarchy                 |
| Sync tokens (FOLLOW + structural) | R01, R02, R05: sync set quality               |
| Transposition (SwapTokens)        | R07: detects commonly-confused operator pairs |
| Bracket tracking                  | R05: bracket-aware recovery validation        |

## Files

| File                           | Role                                                                               |
|--------------------------------|------------------------------------------------------------------------------------|
| `prattail/src/lint.rs`         | Core lint types, `run_lints()`, `emit_diagnostic()`, `format_diagnostic_colored()` |
| `prattail/src/lib.rs`          | `pub mod lint;` + re-exports                                                       |
| `prattail/src/pipeline.rs`     | `LintContext` construction + `run_lints()` + I01–I07 emissions                     |
| `prattail/src/prediction.rs`   | W05 composed dispatch ambiguity warning                                            |
| `prattail/src/cost_benefit.rs` | I08, I09 env override diagnostics                                                  |
| `prattail/src/compose.rs`      | X06 composition verification violations                                            |
| `prattail/src/ebnf.rs`         | I11, I12 EBNF dump diagnostics                                                     |
| `macros/src/logic/mod.rs`      | G25–G31, W09, I10 macro-phase diagnostics                                          |
| `prattail/src/verify.rs` | S01-S02 safety verification results |
| `prattail/src/cegar.rs` | S03 CEGAR refinement log |
| `prattail/src/ewpds.rs` | S04 EWPDS merge site detection |
| `prattail/src/ara.rs` | S05 ARA invariant discovery |
| `prattail/src/algebraic.rs` | S06 Tarjan path expression summary |
| `prattail/src/confluence.rs` | T01-T02 confluence analysis |
| `prattail/src/termination.rs` | T03-T04 termination analysis |
| `prattail/src/vpa.rs` | V01-V02 VPA analysis |
| `prattail/src/tree_automaton.rs` | V03-V04 WTA analysis |
| `prattail/src/petri.rs` | N01-N02 Petri net analysis |
| `prattail/src/nominal.rs` | N03-N04 nominal scope analysis |
| `prattail/src/alternating.rs` | N05 alternating bisimulation |
| `prattail/src/ltl.rs` | L01-L02 LTL model checking |
| `prattail/src/provenance.rs` | E01 provenance tracking |
| `prattail/src/cra.rs` | E02 CRA cost analysis |
| `prattail/src/morphism.rs` | M01-M02 morphism checking |
| `prattail/src/kat.rs` | K01-K02 KAT verification |
| `prattail/src/repair.rs` | Repair suggestion engine integration |

## Migration from Ad-Hoc Warnings

| Former Location       | Former Function                                 | New Lint |
|-----------------------|-------------------------------------------------|----------|
| `prediction.rs`       | `detect_grammar_warnings()` → `LeftRecursion`   | G01      |
| `prediction.rs`       | `detect_grammar_warnings()` → `UnusedCategory`  | G02      |
| `prediction.rs`       | `detect_grammar_warnings()` → `AmbiguousPrefix` | G03      |
| `pipeline.rs:725-733` | `detect_dead_rules()` + `eprintln!`             | W01      |
| `pipeline.rs:945-977` | NFA ambiguity `eprintln!` block                 | W02      |

The original `detect_grammar_warnings()` and `detect_dead_rules()` functions are preserved for backward compatibility but are no longer called directly from the pipeline — the lint layer delegates to them internally.

## Diagnostic Grouping

Larger grammars can produce many diagnostics with the same lint ID — for example, Calculator emits ~25 individual W01 dead-rule warnings. The grouping system collapses repeated lint IDs into compact summaries while preserving all information.

### Grouped IDs

| ID  | Group Key                    | Sub-Group | Grouped Output                                                            |
|-----|------------------------------|-----------|---------------------------------------------------------------------------|
| W01 | hint text (= dead-rule tier) | category  | `"N rules are unreachable...\n  Cat1: R1, R2\n  Cat2: R3"`                |
| W02 | (single group)               | category  | `"N ambiguous NFA prefix dispatch in M categories\n  Cat: msg"`           |
| W03 | (single group)               | category  | `"N high-ambiguity tokens in M categories\n  Cat: msg"`                   |
| W05 | (single group)               | category  | `"N ambiguities resolved by tropical shortest path\n  Cat: details"`      |
| W07 | (single group)               | category  | `"N rules on nearly-dead paths\n  Cat: R1, R2"`                           |
| G03 | (single group)               | category  | `"N ambiguous prefix dispatch in M categories\n  Cat: msg"`               |
| G08 | (single group)               | —         | `"N categories have no cast path to primary\n  isolated: Cat1, Cat2"`     |
| G27 | general rule name            | —         | `"N rules may be subsumed by general rule \`Gen\`\n  candidates: R1, R2"` |

All other lint IDs pass through unchanged. Single-item groups always pass through unchanged.

### Before/After Example

**Before (verbose):**
```
warning[W01] (Calculator): rule `FloatToStr` in category `Str` is unreachable (dead code)
  = in category `Str`, rule `FloatToStr`
  = hint: remove the rule or add a unique dispatch token
warning[W01] (Calculator): rule `BoolToStr` in category `Str` is unreachable (dead code)
  = in category `Str`, rule `BoolToStr`
  = hint: remove the rule or add a unique dispatch token
warning[W01] (Calculator): rule `IntToBool` in category `Bool` is unreachable (dead code)
  = in category `Bool`, rule `IntToBool`
  = hint: remove the rule or add a unique dispatch token
```

**After (grouped, default):**
```
warning[W01] (Calculator): 3 rules are unreachable (dead code)
  Bool: IntToBool
  Str: FloatToStr, BoolToStr
  = hint: remove the rule or add a unique dispatch token
```

### `PRATTAIL_LINT_VERBOSE` Environment Variable

Set `PRATTAIL_LINT_VERBOSE=1` to disable grouping and emit individual diagnostics (the pre-grouping behavior). Useful for CI pipelines that filter on specific rule names or categories:

```bash
PRATTAIL_LINT_VERBOSE=1 cargo build -p mettail-languages
```

### Implementation

- **Pipeline phase:** `lint::emit_diagnostics_for_grammar()` checks `PRATTAIL_LINT_VERBOSE` and calls `group_diagnostics()` when unset
- **Macro phase:** `emit_collected_diagnostics()` in `macros/src/logic/mod.rs` applies the same grouping
- **Core function:** `lint::group_diagnostics(Vec<LintDiagnostic>) -> Vec<LintDiagnostic>`
  - Partitions by lint ID; delegates to per-ID groupers for known groupable IDs
  - Preserves relative ordering: grouped result replaces first-occurrence position
  - Per-ID groupers: `group_w01()`, `group_w02()`, `group_w03()`, `group_w05()`, `group_w07()`, `group_g03()`, `group_g08()`, `group_g27()`
  - Shared helper: `group_ambiguity_by_category()` for W02, W03, G03
