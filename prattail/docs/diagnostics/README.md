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

### Grammar Structure (G01–G10, G24–G32)

| ID                                            | Name                          | Severity | Description                                             |
|-----------------------------------------------|-------------------------------|----------|---------------------------------------------------------|
| [G01](grammar/G01-left-recursion.md)          | left-recursion                | Warning  | Left-recursive rule (same-category leading NonTerminal) |
| [G02](grammar/G02-unused-category.md)         | unused-category               | Warning  | Category declared but never referenced                  |
| [G03](grammar/G03-ambiguous-prefix.md)        | ambiguous-prefix              | Warning  | Multiple prefix rules share the same first terminal     |
| [G04](grammar/G04-duplicate-rule-label.md)    | duplicate-rule-label          | Error    | Duplicate rule label within a category                  |
| [G05](grammar/G05-empty-category.md)          | empty-category                | Warning  | Category with zero rules                                |
| [G06](grammar/G06-shadowed-operator.md)       | shadowed-operator             | Note     | Operator used as both infix and prefix                  |
| [G07](grammar/G07-identical-rules.md)         | identical-rules               | Warning  | Structurally identical rules in same category           |
| [G08](grammar/G08-missing-cast-to-root.md)    | missing-cast-to-root          | Warning  | No cast path from category to primary                   |
| [G09](grammar/G09-unbalanced-delimiters.md)   | unbalanced-delimiters         | Warning  | Mismatched open/close brackets in rule syntax           |
| [G10](grammar/G10-ambiguous-associativity.md) | ambiguous-associativity       | Warning  | Same-precedence operators with mixed associativity      |
| G24                                           | alpha-equivalent-rules        | Note     | Rules with identical De Bruijn structure                |
| G25                                           | cancellation-pair-detected    | Note     | Equation `Outer(Inner(X)) = X` suppressed from eqrel   |
| G26                                           | equation-subsumed             | Note     | Equation eliminated by subsumption                      |
| G27                                           | rule-subsumption-candidate    | Warning  | Rule may be subsumed by more general rule               |
| G28                                           | alpha-equivalent-groups       | Note     | Alpha-equivalent LHS pattern groups                     |
| G29                                           | dependency-groups             | Note     | Fine-grained dependency groups                          |
| G30                                           | isomorphic-wfst-groups        | Note     | Isomorphic WFST dispatch topology                       |
| G31                                           | subsumed-equations-eliminated | Note     | N equations eliminated from codegen                     |
| G32                                           | prefix-isomorphism            | Note     | Categories with structurally identical dispatch tries   |

### WFST-Specific (W01–W16)

| ID                                                       | Name                             | Severity | Description                                               |
|----------------------------------------------------------|----------------------------------|----------|-----------------------------------------------------------|
| [W01](wfst/W01-dead-rule.md)                             | dead-rule                        | Warning  | Rule unreachable via prediction WFST                      |
| [W02](wfst/W02-nfa-ambiguous-prefix.md)                  | nfa-ambiguous-prefix             | Warning  | Ambiguous NFA prefix dispatch                             |
| [W03](wfst/W03-high-ambiguity-token.md)                  | high-ambiguity-token             | Warning  | Token dispatches to 3+ rules                              |
| [W04](wfst/W04-weight-gap-anomaly.md)                    | weight-gap-anomaly               | Note     | Large weight gap suggests effective determinism           |
| W05                                                       | composed-dispatch-ambiguity      | Warning  | N-way ambiguity in composed dispatch table                |
| [W06](wfst/W06-weight-inversion.md)                      | weight-inversion                 | Note     | Less-specific rule has better weight than more-specific   |
| W07                                                       | nearly-dead-path                 | Note     | Rule nearly dead -- high weight but still reachable       |
| W09                                                       | cancellation-pair-missing-rewrite| Warning  | Suppressed equation has no corresponding rewrite          |
| W10                                                       | multi-token-lookahead-required   | Warning  | Single-token dispatch insufficient for disambiguation     |
| W11                                                       | context-weight-narrowing         | Note     | ContextWeight powerset narrowed by 2-token lookahead      |
| W12                                                       | forward-backward-recovery        | Note     | Forward-backward analysis improved recovery weights       |
| [W13](wfst/W13-wpds-unreachable.md)                      | wpds-unreachable                 | Warning  | Rule unreachable via WPDS stack-aware analysis            |
| [W14](wfst/W14-wpds-confirmed-ambiguity.md)              | wpds-confirmed-ambiguity         | Warning  | WPDS confirms pushdown-level ambiguity                    |
| [W16](wfst/W16-wpds-weight-inversion.md)                 | wpds-weight-inversion            | Warning  | WFST vs WPDS weight order disagrees                       |

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

### Composition (X01–X06)

| ID                                                                     | Name                                | Severity | Description                                              |
|------------------------------------------------------------------------|-------------------------------------|----------|----------------------------------------------------------|
| [X01](composition/X01-composition-ambiguity-introduction.md)           | composition-ambiguity-introduction  | Warning  | Composition introduces new FIRST set tokens              |
| [X02](composition/X02-composition-priority-shadowing.md)               | composition-priority-shadowing      | Warning  | Rule from grammar A shadowed by grammar B                |
| [X03](composition/X03-composition-dead-rule-creation.md)               | composition-dead-rule-creation      | Warning  | Live rule became dead after composition                  |
| X04                                                                     | composition-cast-chain-break        | Error    | Cast chain broken after composition                      |
| X05                                                                     | composition-terminal-collision      | Warning  | Terminal has different semantic roles across grammars     |
| X06                                                                     | composition-verification-violation  | Warning  | CVT property violation in composed grammar               |

### Decision Tree (D01–D10, D13)

| ID                                                                              | Name                      | Severity | Description                                               |
|---------------------------------------------------------------------------------|---------------------------|----------|-----------------------------------------------------------|
| [D01](decision-tree/D01-precision-ambiguity.md)       | precision-ambiguity       | Note     | Token path with conflicting rules and overlap tokens      |
| [D02](decision-tree/D02-unresolvable-ambiguity.md)    | unresolvable-ambiguity    | Warning  | No finite lookahead resolves -- inherent grammar conflict |
| [D03](decision-tree/D03-trie-unreachable-rule.md)     | trie-unreachable-rule     | Warning  | Rule shadowed by higher-priority path in PathMap trie     |
| [D04](decision-tree/D04-min-lookahead-depth.md)       | min-lookahead-depth       | Note     | Per-category minimum lookahead tokens                     |
| [D05](decision-tree/D05-decision-tree-summary.md)     | decision-tree-summary     | Note     | States, deterministic/ambiguous ratio, depth, savings     |
| [D06](decision-tree/D06-wfst-trie-inconsistency.md)   | wfst-trie-inconsistency   | Warning  | WFST prediction vs trie reachability mismatch             |
| [D07](decision-tree/D07-path-coverage-report.md)      | path-coverage-report      | Note     | Untested trie paths (opt-in `PRATTAIL_COVERAGE=1`)        |
| [D08](decision-tree/D08-optimization-suggestion.md)   | optimization-suggestion   | Note     | Grammar modifications to resolve PathMap ambiguity        |
| [D09](decision-tree/D09-conflict-resolution-guide.md) | conflict-resolution-guide | Note     | Strategies for genuine conflicts in PathMap trie          |
| D10                                                     | lookahead-waste           | Note     | Generated lookahead deeper than necessary                 |
| D13                                                     | ascent-trie-correlation   | Note     | Parsed-but-never-rewritten constructors                   |

### WPDS (D14–D15, COMP-08)

| ID | Name | Severity | Description |
|---|---|---|---|
| [D14](wpds/D14-wpds-complexity-report.md) | wpds-complexity-report | Info | WPDS analysis size: |Γ|, |Δ|, SCCs, depth bounds |
| [D15](wpds/D15-wpds-witness-trace.md) | wpds-witness-trace | Info | BFS shortest path witness for W13 dead rules |
| [COMP-08](wpds/COMP-08-refactoring-suggestion.md) | wpds-refactoring-suggestion | Note | Grammar restructuring suggestions from WPDS analysis |

### TRS Analysis (T01–T04)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [T01](analysis/trs/T01-non-joinable-critical-pair.md) | non-joinable-critical-pair | Warning | `trs-analysis` | Critical pair not joinable — confluence failure |
| [T02](analysis/trs/T02-confluence-verified.md) | confluence-verified | Note | `trs-analysis` | All critical pairs joinable — system is confluent |
| [T03](analysis/trs/T03-non-terminating-cycle.md) | non-terminating-cycle | Warning | `trs-analysis` | Dependency pair SCC with non-decreasing cycle |
| [T04](analysis/trs/T04-termination-verified.md) | termination-verified | Note | `trs-analysis` | All SCCs have decreasing measures — system terminates |

### Automata Analysis (V01–V04)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [V01](analysis/automata/V01-vpa-determinizable.md) | vpa-determinizable | Note | `vpa` | Grammar admits zero-backtracking VPA |
| [V02](analysis/automata/V02-vpa-alphabet-mismatch.md) | vpa-alphabet-mismatch | Warning | `vpa` | Delimiter classified as both call and return |
| [V03](analysis/automata/V03-wta-unrecognized-term.md) | wta-unrecognized-term | Warning | `tree-automata` | Term pattern not in regular tree language |
| [V04](analysis/automata/V04-wta-hot-path.md) | wta-hot-path | Note | `tree-automata` | High-frequency term pattern — specialization candidate |

### Safety & Verification (S01–S06)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [S01](analysis/safety/S01-safety-violation.md) | safety-violation | Warning | always-on | Bad state reachable via WPDS prestar |
| [S02](analysis/safety/S02-safety-verified.md) | safety-verified | Note | always-on | No bad states reachable — safety verified |
| [S03](analysis/safety/S03-cegar-refinement.md) | cegar-refinement | Note | always-on | CEGAR refinement step count and verdict |
| [S04](analysis/safety/S04-ewpds-merge-site.md) | ewpds-merge-site | Note | `wpds-extended` | EWPDS merge function attachment points |
| [S05](analysis/safety/S05-ara-invariant.md) | ara-invariant | Note | `wpds-ara` | ARA affine-relation invariants discovered |
| [S06](analysis/safety/S06-algebraic-summary.md) | algebraic-summary | Note | always-on | Tarjan SCC path expression summary |

### Concurrency (N01–N05)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [N01](analysis/concurrency/N01-deadlock-risk.md) | deadlock-risk | Warning | `petri` | Petri net coverability detects potential deadlock |
| [N02](analysis/concurrency/N02-unbounded-channel.md) | unbounded-channel | Warning | `petri` | Place has unbounded token capacity |
| [N03](analysis/concurrency/N03-scope-violation.md) | scope-violation | Warning | `nominal` | Name used outside its binding scope |
| [N04](analysis/concurrency/N04-scope-narrowing.md) | scope-narrowing | Note | `nominal` | PNew scope can be tightened |
| [N05](analysis/concurrency/N05-non-bisimilar.md) | non-bisimilar | Warning | `alternating` | Categories not bisimilar — attacker wins game |

### Temporal (L01–L02)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [L01](analysis/temporal/L01-ltl-violated.md) | ltl-violated | Warning | `ltl` | LTL property violated — Buchi product non-empty |
| [L02](analysis/temporal/L02-ltl-verified.md) | ltl-verified | Note | `ltl` | LTL properties satisfied |

### Extension (E01–E02)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [E01](analysis/extension/E01-provenance-trace.md) | provenance-trace | Note | `provenance` | How-provenance polynomial tracking summary |
| [E02](analysis/extension/E02-cra-cost-anomaly.md) | cra-cost-anomaly | Warning | `cra` | CRA register value exceeds threshold |

### Morphism (M01–M02)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [M01](analysis/morphism/M01-morphism-gap.md) | morphism-gap | Warning | `morphisms` | Theory morphism missing sort/operation mapping |
| [M02](analysis/morphism/M02-morphism-preservation-failure.md) | morphism-preservation-failure | Warning | `morphisms` | Axiom not preserved under morphism |

### KAT (K01–K02)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [K01](analysis/kat/K01-hoare-failure.md) | hoare-failure | Warning | `kat` | Hoare triple {p} e {q} fails |
| [K02](analysis/kat/K02-kat-equivalence.md) | kat-equivalence | Note | `kat` | KAT expression equivalence result |

### Performance (P02–P06)

| ID                                           | Name               | Severity | Description                                   |
|----------------------------------------------|--------------------|----------|-----------------------------------------------|
| [P02](performance/P02-high-nfa-spillover.md) | high-nfa-spillover | Note     | Many categories need NFA spillover buffers    |
| [P03](performance/P03-deep-cast-nesting.md)  | deep-cast-nesting  | Note     | Deep cast chain adds Box wrapper overhead     |
| [P04](performance/P04-many-alternatives.md)  | many-alternatives  | Note     | Token dispatches to many rules (save/restore) |
| [P05](performance/P05-wpds-pipeline-cost.md) | wpds-pipeline-cost | Info     | WPDS analysis wall-clock time and sizes       |
| [P06](analysis/P06-analysis-pipeline-cost.md) | analysis-pipeline-cost | Note | Mathematical analysis phase wall-clock time   |

### Ascent (A01–A10)

| ID                                                       | Name                           | Severity | Description                                                      |
|----------------------------------------------------------|--------------------------------|----------|------------------------------------------------------------------|
| [A01](ascent/A01-fixpoint-non-convergence.md)            | fixpoint-non-convergence       | Warning  | Potential unbounded term growth in fixpoint computation           |
| [A02](ascent/A02-redundant-congruence.md)                | redundant-congruence           | Note     | Congruence declared for category with no rewrites                |
| [A03](ascent/A03-eq-rw-category-mismatch.md)             | eq-rw-category-mismatch        | Note     | Category has parsing rules but no equations/rewrites             |
| A04                                                       | large-equivalence-class        | Warning  | Constructor in many dependency groups -- equivalence explosion   |
| A05                                                       | self-referential-equation      | Warning  | Trivial identity rule (single self-referential nonterminal)      |
| A06                                                       | missing-equation-congruence    | Note     | Equation constructor field category lacks equation participants  |
| A07                                                       | fixpoint-iteration-anomaly     | Warning  | Grammar complexity suggests slow fixpoint convergence            |
| A08                                                       | equation-subsumes-rewrite      | Note     | Constructor in multiple dependency groups -- equation may subsume|
| A09                                                       | ascent-struct-size             | Warning  | Large Ascent struct may slow compilation                         |
| A10                                                       | unreachable-equation-variable  | Note     | Variable captured but may not be referenced in RHS               |

### Dispatch (DIS01–DIS05)

| ID                                                       | Name                              | Severity | Description                                                     |
|----------------------------------------------------------|-----------------------------------|----------|-----------------------------------------------------------------|
| [DIS01](dispatch/DIS01-hot-path-misalignment.md)         | hot-path-misalignment             | Note     | WFST action table not weight-ordered (CD01 compensates)         |
| [DIS02](dispatch/DIS02-cold-arm-ratio.md)                | cold-arm-ratio                    | Note     | >80% of dispatch arms are cold (weight >= 1.0)                  |
| DIS03                                                     | decision-tree-depth               | Warning  | Decision tree max_depth exceeds threshold of 8                  |
| DIS04                                                     | backtrack-elimination-coverage    | Note     | Committed vs save/restore arms after G1 analysis                |
| DIS05                                                     | nfa-try-all-set-size              | Warning  | NFA-ambiguous candidate set exceeds 5 -- poor disambiguation    |

### Lexer (LEX01–LEX05)

| ID    | Name                         | Severity | Description                                                  |
|-------|------------------------------|----------|--------------------------------------------------------------|
| LEX01 | overlapping-token-defs       | Note     | Same terminal with different semantic meaning across categories |
| LEX02 | unreachable-token-pattern    | Note     | Terminal is prefix of another -- longest-match semantics apply |
| LEX03 | excessive-equiv-classes      | Note     | Unusually diverse character set increases DFA table size     |
| LEX04 | dfa-state-explosion          | Note     | Many terminals -- monitor DFA state count                    |
| LEX05 | float-integer-ambiguity      | Note     | Both integer and float types present -- `123` lexes as integer|

### Parser (PAR01–PAR05)

| ID    | Name                             | Severity | Description                                                     |
|-------|----------------------------------|----------|-----------------------------------------------------------------|
| PAR01 | deep-rd-chain                    | Warning  | Cross-category RD call chain depth exceeds 5                    |
| PAR02 | unused-bp-level                  | Note     | BP range has many unused levels -- wider than necessary          |
| PAR03 | postfix-prefix-collision         | Warning  | Same token is both prefix and postfix in same category           |
| PAR04 | mixfix-ambiguous-delimiter       | Warning  | Mixfix middle delimiter also used as infix operator              |
| PAR05 | trampoline-frame-variant-count   | Note     | Category has many trampoline frame variants (large frame size)   |

### Codegen Antipattern (C-AP01–C-AP05)

| ID     | Name                                | Severity | Description                                                |
|--------|-------------------------------------|----------|------------------------------------------------------------|
| C-AP01 | cubic-transitivity-blowup           | Warning  | Cubic term growth from transitive equation chains          |
| C-AP02 | quadratic-extension-along-equality  | Warning  | Quadratic blowup from extension along equality             |
| C-AP03 | deep-congruence-chain               | Note     | Deep congruence propagation chain                          |
| C-AP04 | unbounded-rewrite-growth            | Warning  | Rewrite rules may cause unbounded term growth              |
| C-AP05 | clone-storm-collection-field        | Note     | Collection field cloning in generated congruence rules     |

### Infrastructure (I01–I19)

| ID  | Name                         | Severity | Description                       |
|-----|------------------------------|----------|-----------------------------------|
| I01 | transducer-cascade           | Info     | E1 transducer cascade summary     |
| I02 | cascade-skipped              | Info     | B3 trivial grammar skips cascade  |
| I03 | adaptive-beam                | Info     | A7 entropy-based beam width       |
| I04 | beam-feature-required        | Warning  | Auto beam needs `wfst-log`        |
| I05 | cost-benefit-recommendations | Info     | D1 optimization recommendations   |
| I06 | enhanced-dce-active          | Info     | A4 dead rule suppression          |
| I07 | ambiguity-targeting          | Info     | A5 ambiguity analysis             |
| I08 | env-override-active          | Warning  | PRATTAIL_AUTO_OPTIMIZE active     |
| I09 | env-override-parse-error     | Error    | PRATTAIL_AUTO_OPTIMIZE parse fail |
| I10 | ascent-file-write-failed     | Warning  | Ascent Datalog file I/O error     |
| I11 | ebnf-dump-failed             | Warning  | EBNF dump I/O failure             |
| I12 | ebnf-dump-success            | Info     | EBNF dump written                 |
| I13 | lazy-analysis-skip           | Info     | Lazy analysis skipped (unchanged) |
| I14 | lazy-analysis-skip           | Info     | Lazy analysis phase skipped       |
| I15 | lazy-analysis-skip           | Info     | Lazy analysis layer skipped       |
| I16 | hybrid-lexer-active          | Info     | AL02 hybrid lexer activation      |
| I17 | computed-goto-dispatch       | Info     | CD03 computed goto dispatch       |
| I18 | lint-cache-hit               | Info     | DB04 lint cache hit (hash-based)  |
| I19 | parallel-analysis            | Info     | Parallel analysis execution       |

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
| `note[ID]` / `info[ID]`     | Bold cyan   |
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

Grammar-level lints (G/W/R/C/D/P) run during the Generate phase via `run_lints()`.
Ascent lints (A01--A10), dispatch lints (DIS01--DIS05), lexer lints (LEX01--LEX05),
and parser lints (PAR01--PAR05) also run in `run_lints()`. Composition lints
(X01--X06) run during `compose_languages!` via `run_composition_lints()`. Pipeline
info messages (I01--I19) are emitted inline. Macro-phase lints (G25--G31, W09, I10,
C-AP01--C-AP05) are emitted by the macros crate via `emit_diagnostic()`.
Mathematical analysis lints (T/V/S/N/L/E/M/K) run in the same phase, with results
provided by the 6-phase analysis pipeline (feature-gated).
