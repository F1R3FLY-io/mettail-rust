# PraTTaIL Diagnostic Reference

Comprehensive reference for all compile-time lint diagnostics and runtime error messages
produced by the PraTTaIL parser generator.

## Severity Levels

| Level   | Label         | Color       | Meaning                                           |
|---------|---------------|-------------|---------------------------------------------------|
| Info    | `info[ID]`    | Bold cyan   | Infrastructure progress — pipeline status         |
| Note    | `note[ID]`    | Bold cyan   | Informational — no action required                |
| Warning | `warning[ID]` | Bold yellow | Possible issue — review recommended               |
| Error   | `error[ID]`   | Bold red    | Correctness bug — must be fixed for valid codegen |

Ordering: `Info < Note < Warning < Error`

## Quick Reference

### Grammar Structure (G01–G10, G24–G31)

| ID                                            | Name                    | Severity | Description                                             |
|-----------------------------------------------|-------------------------|----------|---------------------------------------------------------|
| [G01](grammar/G01-left-recursion.md)          | left-recursion          | Warning  | Left-recursive rule (same-category leading NonTerminal) |
| [G02](grammar/G02-unused-category.md)         | unused-category         | Warning  | Category declared but never referenced                  |
| [G03](grammar/G03-ambiguous-prefix.md)        | ambiguous-prefix        | Warning  | Multiple prefix rules share the same first terminal     |
| [G04](grammar/G04-duplicate-rule-label.md)    | duplicate-rule-label    | Error    | Duplicate rule label within a category                  |
| [G05](grammar/G05-empty-category.md)          | empty-category          | Warning  | Category with zero rules                                |
| [G06](grammar/G06-shadowed-operator.md)       | shadowed-operator       | Note     | Operator used as both infix and prefix                  |
| [G07](grammar/G07-identical-rules.md)         | identical-rules         | Warning  | Structurally identical rules in same category           |
| [G08](grammar/G08-missing-cast-to-root.md)    | missing-cast-to-root    | Warning  | No cast path from category to primary                   |
| [G09](grammar/G09-unbalanced-delimiters.md)   | unbalanced-delimiters   | Warning  | Mismatched open/close brackets in rule syntax           |
| [G10](grammar/G10-ambiguous-associativity.md) | ambiguous-associativity | Warning  | Same-precedence operators with mixed associativity      |
| G24 | alpha-equivalent-rules | Note | Rules with identical De Bruijn structure |
| G25 | cancellation-pair-detected | Note | Equation `Outer(Inner(X)) = X` suppressed from eqrel |
| G26 | equation-subsumed | Note | Equation eliminated by subsumption |
| G27 | rule-subsumption-candidate | Warning | Rule may be subsumed by more general rule |
| G28 | alpha-equivalent-groups | Note | Alpha-equivalent LHS pattern groups |
| G29 | dependency-groups | Note | Fine-grained dependency groups |
| G30 | isomorphic-wfst-groups | Note | Isomorphic WFST dispatch topology |
| G31 | subsumed-equations-eliminated | Note | N equations eliminated from codegen |

### WFST-Specific (W01–W09)

| ID                                      | Name                 | Severity | Description                                             |
|-----------------------------------------|----------------------|----------|---------------------------------------------------------|
| [W01](wfst/W01-dead-rule.md)            | dead-rule            | Warning  | Rule unreachable via prediction WFST                    |
| [W02](wfst/W02-nfa-ambiguous-prefix.md) | nfa-ambiguous-prefix | Warning  | Ambiguous NFA prefix dispatch                           |
| [W03](wfst/W03-high-ambiguity-token.md) | high-ambiguity-token | Warning  | Token dispatches to 3+ rules                            |
| [W04](wfst/W04-weight-gap-anomaly.md)   | weight-gap-anomaly   | Note     | Large weight gap suggests effective determinism         |
| W05 | composed-dispatch-ambiguity | Warning | N-way ambiguity in composed dispatch table |
| [W06](wfst/W06-weight-inversion.md)     | weight-inversion     | Note     | Less-specific rule has better weight than more-specific |
| W09 | cancellation-pair-missing-rewrite | Warning | Suppressed equation has no corresponding rewrite |

### Recovery (R01–R07)

| ID                                             | Name                    | Severity | Description                                        |
|------------------------------------------------|-------------------------|----------|----------------------------------------------------|
| [R01](recovery/R01-empty-sync-set.md)          | empty-sync-set          | Warning  | Category has no sync tokens for recovery           |
| [R02](recovery/R02-sparse-recovery.md)         | sparse-recovery         | Note     | Category has only 1 sync token                     |
| [R05](recovery/R05-missing-bracket-sync.md)    | missing-bracket-sync    | Warning  | Opening bracket without matching close in sync set |
| [R06](recovery/R06-inverted-recovery-costs.md) | inverted-recovery-costs | Warning  | Recovery cost hierarchy violated                   |
| [R07](recovery/R07-transposition-candidate.md) | transposition-candidate | Note     | Operator pairs with edit distance 1                |

### Cross-Category (C01–C04)

| ID                                                      | Name                       | Severity | Description                                |
|---------------------------------------------------------|----------------------------|----------|--------------------------------------------|
| [C01](cross-category/C01-cast-cycle.md)                 | cast-cycle                 | Error    | Cycle detected in cast rule graph          |
| [C02](cross-category/C02-transitive-cast-redundancy.md) | transitive-cast-redundancy | Note     | Direct cast redundant with transitive path |
| [C04](cross-category/C04-wide-cross-overlap.md)         | wide-cross-overlap         | Note     | High FIRST-set overlap between categories  |

### Composition (X06)

| ID  | Name | Severity | Description |
|-----|------|----------|-------------|
| X06 | composition-verification-violation | Warning | CVT property violation in composed grammar |

### Performance (P02–P04)

| ID                                           | Name               | Severity | Description                                   |
|----------------------------------------------|--------------------|----------|-----------------------------------------------|
| [P02](performance/P02-high-nfa-spillover.md) | high-nfa-spillover | Note     | Many categories need NFA spillover buffers    |
| [P03](performance/P03-deep-cast-nesting.md)  | deep-cast-nesting  | Note     | Deep cast chain adds Box wrapper overhead     |
| [P04](performance/P04-many-alternatives.md)  | many-alternatives  | Note     | Token dispatches to many rules (save/restore) |

### Infrastructure (I01–I12)

| ID  | Name | Severity | Description |
|-----|------|----------|-------------|
| I01 | transducer-cascade | Info | E1 transducer cascade summary |
| I02 | cascade-skipped | Info | B3 trivial grammar skips cascade |
| I03 | adaptive-beam | Info | A7 entropy-based beam width |
| I04 | beam-feature-required | Warning | Auto beam needs `wfst-log` |
| I05 | cost-benefit-recommendations | Info | D1 optimization recommendations |
| I06 | enhanced-dce-active | Info | A4 dead rule suppression |
| I07 | ambiguity-targeting | Info | A5 ambiguity analysis |
| I08 | env-override-active | Warning | PRATTAIL_AUTO_OPTIMIZE active |
| I09 | env-override-parse-error | Error | PRATTAIL_AUTO_OPTIMIZE parse fail |
| I10 | ascent-file-write-failed | Warning | Ascent Datalog file I/O error |
| I11 | ebnf-dump-failed | Warning | EBNF dump I/O failure |
| I12 | ebnf-dump-success | Info | EBNF dump written |

### Runtime Errors

| Document                                | Description                                         |
|-----------------------------------------|-----------------------------------------------------|
| [Parse Errors](runtime/parse-errors.md) | All 5 ParseError variants, triggers, and resolution |
| [Lex Errors](runtime/lex-errors.md)     | Lexer errors, common causes, and resolution         |

## Diagnostic Output Format

PraTTaIL diagnostics follow Rust-compiler-style formatting with ANSI colors:

```
error[C01]: cast cycle detected: Int -> Proc -> Int
  --> <macro>:42:8
  = in category `Proc`, rule `CastInt`
  = hint: break the cycle by removing one cast direction

warning[W01]: rule `FloatToStr` in category `Str` is unreachable (dead code)
  --> <macro>:15:8
  = in category `Str`, rule `FloatToStr`
  = hint: remove the rule or add a unique dispatch token
```

### Color Scheme

| Element                     | Color       |
|-----------------------------|-------------|
| `error[ID]`                 | Bold red    |
| `warning[ID]`               | Bold yellow |
| `note[ID]` / `info[ID]`    | Bold cyan   |
| `(GrammarName)`             | Dim         |
| `-->` location              | Bold blue   |
| `= in category/rule`        | Dim         |
| `= hint:`                   | Green       |
| Backtick-quoted identifiers | Bold        |

## Implementation

All diagnostic output routes through `LintDiagnostic` structs and `format_diagnostic_colored()`
in [`prattail/src/lint.rs`](../../src/lint.rs). The public API includes:
- `emit_diagnostic()` — emit a single colorized diagnostic to stderr
- `format_diagnostic_colored()` — format without emitting (for custom output)
- `colorize_backtick_spans()` — backtick highlighting helper
- `ansi` module — ANSI color constants

Grammar-level lints (G/W/R/C/P) run during the Generate phase via `run_lints()`. Pipeline
info messages (I01–I12) are emitted inline. Macro-phase lints (G25–G31, W09, I10) are
emitted by the macros crate via `emit_diagnostic()`.
