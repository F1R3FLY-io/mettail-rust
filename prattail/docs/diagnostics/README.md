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

## About the Feature Gate Column

Many lint tables below carry a **Feature Gate** column (for example `` `trs-analysis` ``,
`` `kat` ``, `` `type-system` ``, `` `egraph` ``, `` `symbolic-automata` ``, `` `vpa` ``).
These entries name the **analysis category / lint namespace** that owns each lint. They are
**grouping labels, not `cargo --features` toggles.**

> [!IMPORTANT]
> Do **not** run `cargo build --features type-system` (nor `kat`, `egraph`, `presburger`,
> `unification`, `sft`, `trs-analysis`, `symbolic-automata`, `tree-automata`, `ltl`, `petri`,
> `nominal`, `provenance`, `cra`, `morphisms`, `wpds-extended`, `wpds-ara`, `omega`,
> `weighted-mso`, `lattice-theory`, `logict`, `predicate-dispatch`). None of these is a
> declared Cargo feature, and **none gates parser compilation through `#[cfg(feature = "…")]`**.
> Whether one of these mathematical-analysis lints can fire is decided at grammar-analysis time
> by the analysis pipeline (predicate dispatch over the grammar's guards; see **PD01–PD04**),
> independent of any Cargo feature.

Two special values appear in the column:

- **`always-on`** — the lint runs unconditionally (no gate of any kind).
- **Advanced-automata labels are runtime-dispatched, not Cargo features.** The values
  `alternating`, `vpa`, `parity-tree-automata`, `register-automata`, `probabilistic`,
  `multi-tape`, `multiset-automata`, `two-way-transducer`, and `buchi` name the
  advanced-automata analyses. Like every other value in this column they are
  **analysis-category labels, not `cargo --features` toggles**: the compilers they name
  (`BuchiCompiler`, `AlternatingCompiler`, `VpaCompiler`, …) are **always compiled** and
  dispatched at grammar-analysis time by the `predicate_dispatch/signature.rs` runtime registry.
  (They were previously *also* declared as inert `= []` placeholder Cargo features in
  [`prattail/Cargo.toml`](../../Cargo.toml); those declarations gated **nothing** and were
  **removed**, and the predicate-dispatch conformance test
  (`prattail/src/predicate_dispatch/tests.rs`) now runs **unconditionally**.)

For the flags that genuinely change the build — instrumentation, tracing, the SMT/rendering
back ends, and language selection — see
[Optional Cargo Features](#optional-cargo-features) and
[Environment Variables](#environment-variables) at the end of this document. (The **OSLF
analysis substrate** is no longer among them: its precise engines are always compiled and
always run — see [OSLF analysis substrate](#oslf-analysis-substrate-prattail-always-on--no-longer-cargo-features).)

## Quick Reference

### Grammar Structure (G01–G10, G24, G32)

| ID                                            | Name                          | Severity | Description                                             |
|-----------------------------------------------|-------------------------------|----------|---------------------------------------------------------|
| [G01](grammar/G01-left-recursion.md)          | left-recursion                | Warning  | Left-recursive rule (same-category leading NonTerminal) |
| [G02](grammar/G02-unused-category.md)         | unused-category               | Warning  | Category declared but never referenced                  |
| [G03](grammar/G03-ambiguous-prefix.md)        | ambiguous-prefix              | Warning  | Multiple prefix rules share the same first terminal     |
| [G04](grammar/G04-duplicate-rule-label.md)    | duplicate-rule-label          | Error    | Duplicate rule label within a category                  |
| [G05](grammar/G05-empty-category.md)          | empty-category                | Warning  | Category with zero rules                                |
| [G06](grammar/G06-shadowed-operator.md)       | shadowed-operator             | Note     | Operator used as both infix and prefix                  |
| [G07](grammar/G07-identical-rules.md)         | identical-rules               | Warning  | Structurally identical rules in same category           |
| [G08](grammar/G08-missing-cast-to-root.md)    | missing-cast-to-root          | Warning  | No value-flow path from category to primary             |
| [G09](grammar/G09-unbalanced-delimiters.md)   | unbalanced-delimiters         | Warning  | Mismatched open/close brackets in rule syntax           |
| [G10](grammar/G10-ambiguous-associativity.md) | ambiguous-associativity       | Warning  | Same-precedence operators with mixed associativity      |
| G24                                           | alpha-equivalent-rules        | Note     | Rules with identical De Bruijn structure                |
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
| W12                                                       | forward-backward-recovery        | Note     | Forward-backward analysis improved recovery weights       |
| [W13](wfst/W13-wpds-unreachable.md)                      | wpds-unreachable                 | Warning  | Rule unreachable via WPDS stack-aware analysis            |
| [W14](wfst/W14-walker-fork-tight-margin.md)              | walker-fork-tight-margin         | Note     | Top-2 prediction weights within ε; Walker lex-min Fork resolution will be src_idx/rule_idx-dependent |
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
| [D13](decision-tree/D13-parsed-but-unrewritten.md)      | parsed-but-unrewritten    | Note     | Parsed-but-never-rewritten constructors                   |

### WPDS (D14–D15, COMP-08)

| ID | Name | Severity | Description |
|---|---|---|---|
| [D14](wpds/D14-wpds-complexity-report.md) | wpds-complexity-report | Info | WPDS analysis size: \|Γ\|, \|Δ\|, SCCs, depth bounds |
| [D15](wpds/D15-wpds-witness-trace.md) | wpds-witness-trace | Info | BFS shortest path witness for W13 dead rules |
| [COMP-08](wpds/COMP-08-refactoring-suggestion.md) | wpds-refactoring-suggestion | Note | Grammar restructuring suggestions from WPDS analysis |

### TRS Analysis (T01–T04)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [T01](analysis/trs/T01-non-joinable-critical-pair.md) | non-joinable-critical-pair | Warning | `trs-analysis` | Critical pair not joinable — confluence failure |
| [T02](analysis/trs/T02-confluence-verified.md) | confluence-verified | Note | `trs-analysis` | All critical pairs joinable — system is confluent |
| [T03](analysis/trs/T03-non-terminating-cycle.md) | non-terminating-cycle | Warning | `trs-analysis` | Dependency pair SCC with non-decreasing cycle |
| [T04](analysis/trs/T04-termination-verified.md) | termination-verified | Note | `trs-analysis` | All SCCs have decreasing measures — system terminates |

### Automata Analysis (V01–V06)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [V01](analysis/automata/V01-vpa-determinizable.md) | vpa-determinizable | Note | `vpa` | Grammar admits zero-backtracking VPA |
| [V02](analysis/automata/V02-vpa-alphabet-mismatch.md) | vpa-alphabet-mismatch | Warning | `vpa` | Delimiter classified as both call and return |
| [V03](analysis/automata/V03-wta-unrecognized-term.md) | wta-unrecognized-term | Warning | `tree-automata` | Term pattern not in regular tree language |
| [V04](analysis/automata/V04-wta-hot-path.md) | wta-hot-path | Note | `tree-automata` | High-frequency term pattern — specialization candidate |

*See also V05–V06 in the [Weighted VPA](#weighted-vpa-v05v06) section below.*

### Safety & Verification (S01–S06)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [S01](analysis/safety/S01-safety-violation.md) | safety-violation | Warning | always-on | Bad state reachable via WPDS prestar |
| [S02](analysis/safety/S02-safety-verified.md) | safety-verified | Note | always-on | No bad states reachable — safety verified |
| [S03](analysis/safety/S03-cegar-refinement.md) | cegar-refinement | Note | always-on | CEGAR refinement step count and verdict |
| [S04](analysis/safety/S04-ewpds-merge-site.md) | ewpds-merge-site | Note | `wpds-extended` | EWPDS merge function attachment points |
| [S05](analysis/safety/S05-ara-invariant.md) | ara-invariant | Note | `wpds-ara` | ARA affine-relation invariants discovered |
| [S06](analysis/safety/S06-algebraic-summary.md) | algebraic-summary | Note | always-on | Tarjan SCC path expression summary |

### Concurrency (N01–N07)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [N01](analysis/concurrency/N01-deadlock-risk.md) | deadlock-risk | Warning | `petri` | Petri net coverability detects potential deadlock |
| [N02](analysis/concurrency/N02-unbounded-channel.md) | unbounded-channel | Warning | `petri` | Place has unbounded token capacity |
| [N03](analysis/concurrency/N03-scope-violation.md) | scope-violation | Warning | `nominal` | Name used outside its binding scope |
| [N04](analysis/concurrency/N04-scope-narrowing.md) | scope-narrowing | Note | `nominal` | PNew scope can be tightened |
| [N05](analysis/concurrency/N05-non-bisimilar.md) | non-bisimilar | Warning | `alternating` | Categories not bisimilar — attacker wins game |

*See also N06–N07 in the [Weighted Alternating](#weighted-alternating-n06n07) section below.*

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

### Symbolic Automata (SYM01–SYM04)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| SYM01 | unsatisfiable-guard | Warning | `symbolic-automata` | Receive guard is BOT (dead receive) — SFA emptiness check confirms no satisfying value exists |
| SYM02 | overlapping-guards | Warning | `symbolic-automata` | Two guards on same channel overlap — SFA intersection is non-empty, causing ambiguous dispatch |
| SYM03 | subsumed-guard | Note | `symbolic-automata` | Guard A ⊇ Guard B (redundant) — subsumption check via complement ∩ intersection emptiness |
| SYM04 | non-minimal-guards | Note | `symbolic-automata` | SFA has mergeable states — symbolic Hopcroft minimization can reduce guard automaton |

### Weighted Buchi (O01–O02)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| O01 | weighted-buchi-non-convergent | Warning | `omega` | Accepting cycle weight computation did not converge — Tarjan SCC + `matrix_star()` exceeded iteration limit |
| O02 | weighted-buchi-heavy-cycle | Note | `omega` | Accepting cycle weight exceeds threshold — potential liveness concern or very expensive accepting run |

### Weighted Alternating (N06–N07)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| N06 | weighted-parity-non-convergent | Warning | `alternating` | Parity game value computation did not converge — Jurdzinski small progress measures exceeded limit |
| N07 | weighted-branching-imbalance | Note | `alternating` | Universal successor weights differ by >10x — one branch dominates product, potential design issue |

### Weighted VPA (V05–V06)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [V05](vpa/V05.md) | weighted-vpa-non-determinizable (compatibility name) | Warning | `vpa` | Visible-alphabet partition conflict; exact VPA decisions reject the malformed model |
| [V06](vpa/V06.md) | weighted-vpa-inclusion-failure (compatibility name) | Warning | `vpa` | Large invalid model cannot enter the exact Boolean decision path; no inclusion verdict has run |

### Parity Tree Automata (PT01–PT03)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| PT01 | pata-emptiness-violation | Warning | `parity-tree-automata` | Predicate unsatisfiable — Zielonka's recursive parity game confirms no AST can match the mu-calculus formula |
| PT02 | pata-subsumption | Note | `parity-tree-automata` | Predicate A subsumes predicate B — redundant guard check detected via PATA inclusion |
| PT03 | pata-high-priority | Note | `parity-tree-automata` | Parity priority depth exceeds 4 — exponential blowup warning for emptiness/inclusion algorithms |

### Register Automata (RA01–RA03)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| RA01 | unbound-data-reference | Warning | `register-automata` | Data value referenced (TestEq/TestNeq) but never stored — register is always uninitialized at test point |
| RA02 | redundant-register | Note | `register-automata` | Register written (Store) but never tested — dead register can be eliminated by `normalize()` |
| RA03 | register-equivalence | Note | `register-automata` | Two registers always hold the same value — orbit-finite bisimulation confirms equivalence, one can be eliminated |

### Probabilistic Automata (PR01–PR04)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| PR01 | low-selectivity-rule | Warning | `probabilistic` | Rule handles <1% of expected inputs — guard has extremely low selectivity against corpus distribution |
| PR02 | non-stochastic-state | Warning | `probabilistic` | Outgoing probabilities do not sum to 1 — per-state log-sum-exp normalization violated |
| PR03 | high-entropy-category | Note | `probabilistic` | Category has high Shannon entropy — many equally-likely alternatives suggest poor disambiguation |
| PR04 | expected-depth-anomaly | Note | `probabilistic` | Expected recursion depth exceeds threshold — forward-backward analysis detects deep expected nesting |

### Multi-Tape Automata (MT01–MT02)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| MT01 | multi-channel-overlap | Warning | `multi-tape` | Two tapes constrained to identical patterns — redundant channel in multi-tape automaton |
| MT02 | multi-tape-disconnected | Note | `multi-tape` | Tape has no auto-intersection constraints with other tapes — independent channel can be analyzed separately |

### Multiset Automata (MS01–MS02)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| MS01 | unsatisfiable-cardinality | Warning | `multiset-automata` | Cardinality constraint impossible given multiset structure — e.g., `count(f) >= k` when max multiplicity < k |
| MS02 | redundant-feature-check | Note | `multiset-automata` | Feature multiplicity always >= threshold (tautological guard) — constraint is always satisfied |

### Weighted MSO (MSO01–MSO03)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| MSO01 | unrestricted-universal-set | Warning | `weighted-mso` | Formula uses ∀X (second-order universal set quantification) — not in restricted MSO, classified T3/T4 |
| MSO02 | non-recognizable-step | Warning | `weighted-mso` | ∀x.φ where φ is not a recognizable step function — violates restricted MSO constraint (Def. 3.6) |
| MSO03 | equivalent-formulas | Note | `weighted-mso` | Two guard formulas have identical semantics — decidable equivalence check (Cor. 6.5) detects redundancy |

### Two-Way Transducers (TW01–TW03)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| TW01 | circular-channel-dependency | Warning | `two-way-transducer` | Bidirectional reachability detects deadlock cycle among channels — circular constraint propagation |
| TW02 | one-way-sufficient | Note | `two-way-transducer` | W2T analysis determines backward pass is unnecessary — one-way transducer suffices for this pattern |
| TW03 | constraint-propagation-divergent | Warning | `two-way-transducer` | Backward constraint propagation does not converge — infinite constraint refinement detected |

### Symbolic Finite Transducers (SFT01–SFT04)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [SFT01](sft/SFT01.md) | empty-sft-domain | Warning | `sft` | SFT has empty domain — dead transduction that can never fire |
| [SFT02](sft/SFT02.md) | constant-sft-output | Note | `sft` | SFT always produces same output — simplifiable to constant |
| [SFT03](sft/SFT03.md) | nondeterministic-sft | Note | `sft` | SFT is not single-valued (nondeterministic output) |
| [SFT04](sft/SFT04.md) | equivalent-sft-pair | Note | `sft` | Two functional SFTs produce identical input-output behavior |

### Predicate Dispatch (PD01–PD04)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [PD01](predicate-dispatch/PD01.md) | degenerate-predicate | Warning | `predicate-dispatch` | Predicate activates no specialized module beyond base (M1+M10) |
| [PD02](predicate-dispatch/PD02.md) | all-modules-activated | Note | `predicate-dispatch` | Predicate activates all 11 modules (no dispatch benefit) |
| [PD03](predicate-dispatch/PD03.md) | dispatch-savings | Info | `predicate-dispatch` | Reports number of module invocations skipped by dispatch |
| [PD04](predicate-dispatch/PD04.md) | missing-feature-gate | Warning | `predicate-dispatch` | Cross-channel predicate but required module feature not enabled |

### Presburger Arithmetic (PB01–PB03)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [PB01](presburger/PB01.md) | unsatisfiable-arithmetic-guard | Warning | `presburger` | Linear arithmetic guard is provably unsatisfiable via Presburger NFA emptiness — dead rule |
| [PB02](presburger/PB02.md) | tautological-arithmetic-guard | Note | `presburger` | Arithmetic guard accepts all valid inputs (NFA complement is empty) — redundant guard |
| [PB03](presburger/PB03.md) | subsumed-arithmetic-guard | Note | `presburger` | One guard's satisfying set ⊆ another's — subsumed guard is redundant on same channel |

### Unification (UN01–UN03)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [UN01](unification/UN01.md) | unsatisfiable-unification-guard | Warning | `unification` | Structural pattern guard fails unification (constructor clash or occurs check) — dead rule |
| [UN02](unification/UN02.md) | tautological-unification-guard | Note | `unification` | Unification guard trivially satisfiable — any substitution satisfies it |
| [UN03](unification/UN03.md) | subsumed-unification-guard | Note | `unification` | One pattern guard strictly more general than another — subsumed guard is redundant |

### Subtype Lattice (SL01–SL02)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [SL01](subtype-lattice/SL01.md) | unsatisfiable-subtype-constraint | Warning | `lattice-theory` | Subtype constraint set contradicts declared type hierarchy — no valid assignment |
| [SL02](subtype-lattice/SL02.md) | redundant-subtype-constraint | Note | `lattice-theory` | Subtype constraint already implied by transitive closure of existing edges |

### Refinement Types (RT01–RT06)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [RT01](refinement/RT01.md) | unsatisfiable-refinement-predicate | Warning | `type-system` | Refinement predicate has no satisfying value — empty type |
| [RT02](refinement/RT02.md) | tautological-refinement-predicate | Note | `type-system` | Refinement predicate is always true — equivalent to base type |
| [RT03](refinement/RT03.md) | empty-refinement-intersection | Warning | `type-system` | Two refinement types have provably empty intersection |
| [RT04](refinement/RT04.md) | refinement-subtype-detected | Note | `type-system` | One refinement type is a subtype of another |
| [RT05](refinement/RT05.md) | refinement-decidability-tier | Note | `type-system` | Refinement predicate decidability classification (T1–T4) |
| [RT06](refinement/RT06.md) | refinement-type-shadows-base | Warning | `type-system` | Refinement type name shadows a base type category |

### LogicT (LT01)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [LT01](logict/LT01.md) | logict-search-bound-exceeded | Warning | `logict` | Fair interleaving search hit configured depth limit — result is Unknown, not Unsat |

### Performance (P03–P06)

| ID                                           | Name               | Severity | Description                                   |
|----------------------------------------------|--------------------|----------|-----------------------------------------------|
| [P03](performance/P03-deep-cast-nesting.md)  | deep-cast-nesting  | Note     | Deep cast chain adds Box wrapper overhead     |
| [P04](performance/P04-many-alternatives.md)  | many-alternatives  | Note     | Token dispatches to many rules (save/restore) |
| [P05](performance/P05-wpds-pipeline-cost.md) | wpds-pipeline-cost | Info     | WPDS analysis wall-clock time and sizes       |
| [P06](analysis/P06-analysis-pipeline-cost.md) | analysis-pipeline-cost | Note | Mathematical analysis phase wall-clock time   |

### Equation/rewrite network (historical A01–A10 IDs)

| ID                                                       | Name                           | Severity | Description                                                      |
|----------------------------------------------------------|--------------------------------|----------|------------------------------------------------------------------|
| [A01](ascent/A01-fixpoint-non-convergence.md)            | fixpoint-non-convergence       | Warning  | Potential unbounded term growth under repeated rewriting          |
| [A02](ascent/A02-redundant-congruence.md)                | redundant-congruence           | Note     | Congruence declared for category with no rewrites                |
| [A03](ascent/A03-eq-rw-category-mismatch.md)             | eq-rw-category-mismatch        | Note     | Category has parsing rules but no equations/rewrites             |
| [A04](ascent/A04-large-equivalence-class.md)              | large-equivalence-class        | Warning  | Constructor in many dependency groups -- equivalence explosion   |
| A05                                                       | self-referential-equation      | Warning  | Trivial identity rule (single self-referential nonterminal)      |
| A06                                                       | missing-equation-congruence    | Note     | Equation constructor field category lacks equation participants  |
| [A07](ascent/A07-fixpoint-iteration-anomaly.md)           | fixpoint-iteration-anomaly     | Warning  | Dependency topology suggests excessive rewrite propagation       |
| A08                                                       | equation-subsumes-rewrite      | Note     | Constructor in multiple dependency groups -- equation may subsume|
| [A09](ascent/A09-generated-rewrite-network-size.md)       | generated-rewrite-network-size | Warning  | Large generated Dovetail/Rho network may slow compilation        |
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

### Historical Codegen Antipattern IDs (C-AP01–C-AP05)

These Ascent-era diagnostics have no production emitter in the current
Dovetail/Rho pipeline. Their pages remain an explicitly historical record.

| ID     | Name                                | Severity | Description                                                |
|--------|-------------------------------------|----------|------------------------------------------------------------|
| C-AP01 | cubic-transitivity-blowup           | Retired  | Cubic term growth from transitive equation chains          |
| C-AP02 | quadratic-extension-along-equality  | Retired  | Quadratic blowup from extension along equality             |
| C-AP03 | deep-congruence-chain               | Retired  | Deep congruence propagation chain                          |
| C-AP04 | unbounded-rewrite-growth            | Retired  | Rewrite rules may cause unbounded term growth              |
| C-AP05 | clone-storm-collection-field        | Retired  | Collection field cloning in generated congruence rules     |

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
| I10 | ascent-file-write-failed     | Retired  | Historical Ascent artifact; no production emitter |
| I11 | ebnf-dump-failed             | Warning  | EBNF dump I/O failure             |
| I12 | ebnf-dump-success            | Info     | EBNF dump written                 |
| I13 | lazy-analysis-skip           | Info     | Lazy analysis skipped (unchanged) |
| I14 | lazy-analysis-skip           | Info     | Lazy analysis phase skipped       |
| I15 | lazy-analysis-skip           | Info     | Lazy analysis layer skipped       |
| I16 | hybrid-lexer-active          | Info     | AL02 hybrid lexer activation      |
| I17 | computed-goto-dispatch       | Info     | CD03 computed goto dispatch       |
| I18 | lint-cache-hit               | Info     | DB04 lint cache hit (hash-based)  |
| I19 | parallel-analysis            | Info     | Parallel analysis execution       |

### E-Graph Equality Saturation (EG01–EG04)

| ID | Name | Severity | Feature Gate | Description |
|---|---|---|---|---|
| [EG01](egraph/EG01.md) | discovered-equivalence | Note | `egraph` | E-graph saturation discovered non-trivial term equivalence |
| [EG02](egraph/EG02.md) | simplifiable-guard | Note | `egraph` | Guard expression simplifiable to lower-cost equivalent via equality saturation |
| [EG03](egraph/EG03.md) | saturation-non-convergence | Warning | `egraph` | Equality saturation did not converge within configured resource limits |
| [EG04](egraph/EG04.md) | joinability-witness | Note | `egraph` | E-graph found joinability witness for critical pair (suppresses T01) |

### Runtime Errors

| Document                                | Description                                         |
|-----------------------------------------|-----------------------------------------------------|
| [Parse Errors](runtime/parse-errors.md) | All 5 ParseError variants, triggers, and resolution |
| [Lex Errors](runtime/lex-errors.md)     | Lexer errors, common causes, and resolution         |

## Optional Cargo Features

Every feature listed here is **off by default**. The **default build is the production
surface**: no instrumentation, no tracing, no solver, no analysis substrate — just the parser
generator. Enable a feature with `cargo build --features <name>` (or the crate-qualified form,
e.g. `--features mettail-prattail/walker-trace`). The `prattail` crate declares **no** default
features of its own; the default surface comes from the workspace crates that depend on it.

Unless noted otherwise, an "Enables / deps" cell of *(none)* means the feature pulls in no
extra crates — it is a pure compile-time switch.

### Instrumentation and tracing (`prattail`, `macros`)

| Feature | Enables / deps | Default | Purpose |
|---------|----------------|:------:|---------|
| `walker-trace` | *(none)* | off | Compile **in** the parser's per-diagnostic stderr trace/dump statements — the `PRATTAIL_CGLL_*`, `PRATTAIL_GRP_*`, `PRATTAIL_CANONICAL_GLL_STATS`, `PRATTAIL_DISPATCH_TRACE`, `PRATTAIL_ENTROPY`, `PRATTAIL_DUMP_EBNF`/`PRATTAIL_DUMP_PARSER`, `PRATTAIL_RD_U1_DIAG`, and `PRATTAIL_MACRO_TRACE` families. Off ⇒ each gated site (including the `std::env::var*` read) is compiled out entirely via `trace_diag!` / `#[cfg(feature = "walker-trace")]` (`prattail/src/trace.rs`): zero hot-path cost. Under the feature each diagnostic is still selected individually at runtime by its own env var. Works in any profile (debug or release). |
| `walker-stats` | *(none)* | off | Compile in 19 `u64` walker counters (`apply_action_to_cursor` calls, cursor-proliferation peaks, `merge_equivalent_cursors` collapse ratios, cursor lifecycle sources/sinks, Fork composition by kind). Per-walker scope, no atomics. Output is triggered at parse end by `PRATTAIL_WALKER_STATS=1`. |
| `hang-dump` | `dep:signal-hook`, `dep:parking_lot` | off | SIGUSR1 handler that snapshots walker state for debugging hangs. Armed at runtime by `PRATTAIL_HANG_DUMP` (+ `PRATTAIL_HANG_DUMP_PATH`, `PRATTAIL_HANG_WATCHDOG`); JSON is hand-formatted. |

The `mettail-languages` and `mettail-macros` crates re-expose `walker-trace` and `walker-stats`
as pass-throughs (`mettail-languages/walker-trace` turns on both the `prattail` runtime gate and
the `mettail-macros` codegen-time gate for `PRATTAIL_MACRO_TRACE`).

### Solver and rendering (`prattail`)

| Feature | Enables / deps | Default | Purpose |
|---------|----------------|:------:|---------|
| `smt` | `dep:z3` | off | SMT-backed `ConstraintTheory` via in-process Z3 (`prattail/src/logict_smt.rs`), reachable only through three-valued `is_satisfiable_3v` / `checked_witness` (`unknown → Sat3::DontKnow`, never collapsed). Secondary gap-filler where the verified deciders return `DontKnow`. The default build links no libz3 and is byte-identical. |
| `railroad-diagrams` | *(none)* | off | Optional hand-emitted **SVG** railroad-diagram output (`render_grammar_railroad_svg`). Text/ASCII railroad rendering (`render_grammar_railroad_text`) is **always** available and needs no feature. |

### OSLF analysis substrate (`prattail`, always-on — no longer Cargo features)

The seven OSLF analysis engines below are **not** Cargo features. They were once gated behind
the default-off `any-algebra-carrier`, `sym-tree-structural`, `oslf-bisimulation`,
`oslf-transducer`, `oslf-letprop`, `oslf-hindley-milner`, and `oslf-behavioral-lowering`
features; those features — and the string-heuristic fallbacks they used to guard — were
**deleted** (commit `2ec8316e`). The precise engines are now the **sole, always-on** analysis
path: always compiled, always run, with no opt-in and no opt-out. Correctness by construction
is a primary purpose of the crate, so the analysis substrate must not ship an unsound /
under-enforcing heuristic mode — the two deleted fallbacks (`category_is_scalar_by_string`,
which misclassified scalar sorts by string-matching a type-name segment, and the silent
heuristic `analyze_refinement_dispatch`, which under-enforced RT03) were genuine
correctness-by-construction violations. `mettail-ast` is now a normal (non-optional)
dependency. (OSLF = the Order-Sorted Logical-Framework analysis tower.)

Their lints — **RT03**, **RT07**, **LP01**, **HM01** — therefore fire **unconditionally**. All
four are **inert on the current grammar corpus** (0 firings across every bundled grammar), but
they are always active: any future grammar that exhibits the defect they detect will trip them.

| Engine (module) | Decides / provides | Lint fired |
|---|---|---|
| `AnyAlgebra` carrier (`any_algebra.rs`) | Sole route for `symbolic::analyze_from_bundle` through the uniform guard-predicate carrier; the real `NativeKind` scalar-sort resolution the other engines reuse. Byte-for-byte agreement with the retained `analyze_from_bundle_string_set` oracle is pinned by `guard_carrier_snapshot`. | — |
| structural dispatch (`sym_tree`, `structural_types`) | Structural refinement-type dispatch via `SymbolicTreeAutomaton<AnyAlgebra>`; decides disjointness / subtype precisely (conservative `Overlapping` on parse failure — never worse than the status quo). | **RT03** empty-refinement-intersection |
| symbolic tree transducer (`sym_tree_transducer.rs`) | Bottom-up symbolic tree transducer for cast totality / cast reachability (pre-image ∩ source category). | **RT07** dead-cast |
| bisimulation LTS (`bisimulation.rs`) | Coarsest bisimulation by partition refinement; supersedes the weaker `alternating` behavioral-iso check (**N06-ISO**); agreement-gated against `alternating::analyze_from_bundle`. | — |
| letprop→PATA (`letprop.rs` → `parity_tree.rs`) | Recursive-predicate → modal-μ → Parity Alternating Tree Automaton emptiness. Inert on every current grammar (no recursive-predicate **surface syntax** yet — a tracked `ast/` follow-up). | **LP01** dead-behavioral-type |
| Hindley–Milner sort pass (`hindley_milner.rs`) | Base-sort consistency: checks each constructor's principal arrow type unifies with its declared category. | **HM01** sort-mismatch |
| behavioral lowering (`behavioral_pred` → `behavioral_algebra`) | Lowers the runtime `BehavioralPred` carrier into the `BehavioralFormula` relational decider; the eval path is untouched. | — |

### Predicate-dispatch capability labels (`prattail`, not Cargo features)

The advanced-automata capability labels — `buchi`, `alternating`, `vpa`, `parity-tree-automata`,
`register-automata`, `probabilistic`, `multi-tape`, `multiset-automata`, and `two-way-transducer`
— are **not** Cargo features. The automata compilers they name are always compiled and dispatched
at grammar-analysis time by the `predicate_dispatch/signature.rs` runtime registry, never by a
Cargo feature. They were formerly declared as inert `= []` placeholder features (present only to
keep `cargo check --all-targets` *check-cfg-clean* and to gate the predicate-dispatch conformance
test); those declarations gated **nothing** and were **removed**, and the conformance test
(`prattail/src/predicate_dispatch/tests.rs`) now runs **unconditionally**. See
[About the Feature Gate Column](#about-the-feature-gate-column).

The bench-only toggles `wfst-log` and `set-theoretic-types` **do** remain declared as real `= []`
Cargo features (to keep `cargo check --all-targets` check-cfg-clean); they are consumed only by
the criterion **benchmarks** (`bench_wfst`, `bench_type_system`) — `wfst-log` selects the
log-semiring training path there (see [WFST Feature Gates](../usage/wfst/feature-gates.md)).
Neither affects the default parser build.

### Language selection and runtime backends (`languages`, `repl`, `rholang-runtime`)

These belong to sibling crates, not `prattail`; they select which generated languages and
runtime backends are compiled. `mettail-languages` defaults to
`["all-languages", "rho-codegen", "dovetail-codegen"]`.

| Feature (crate) | Enables / deps | Default | Purpose |
|-----------------|----------------|:------:|---------|
| `all-languages` (`languages`) | the per-language set below | **on** | Umbrella over every bundled language. |
| per-language (`languages`) | *(none, except `composition`)* | via `all-languages` | `ambient`, `appsubst`, `calculator`, `class2hashmapsmoke`, `class2multi`, `class2optsmoke`, `class2smoke`, `class3multi`, `class3opt`, `composition` (= `calculator` + `lambda`), `fortran_model`, `reserved_model`, `guarded-rho`, `lambda`, `led-test`, `optsmoke`, `refinementsmoke`, `rholang`. `guardoptsmoke` exists but is **not** in `all-languages` (opt-in site-2 smoke). |
| `rho-codegen` (`languages`) | `dep:mettail-rholang-codegen` | **on** | Macro-generated AST-first Rho scalar invocation descriptions. |
| `dovetail-codegen` (`languages`) | `dep:dovetail`, `dep:mettail-dovetail-runtime`, `dep:rigail` | **on** | Macro-generated AST-first Dovetail report compiler (general-purpose runtime backend). |
| `strategies` (`languages`) | `dep:proptest` | off | Public `arb_{cat}` proptest strategies; required by the `simulate_*` CLI binaries. |
| `mimalloc` (`languages`) | `dep:mimalloc` | off | mimalloc global allocator for the `trampoline_tests` binary. |
| `rho-languages` (`repl`) | `bundled-languages`, `dep:mettail-rholang-runtime`, `dep:mettail-rholang-codegen` | **on** | Full `exec` surface (Rholang/Calculator two-stage Dovetail+Rholang). A Dovetail-only REPL builds `--no-default-features --features bundled-languages`. |
| `rholang-runtime` (`rholang-runtime`) | `runtime-report`, `dep:mettail-ast`, `dep:mettail-languages`, `dep:syn`, `mettail-languages/{rholang,dovetail-codegen}` | **on** | Production AST-first Rholang-to-Rho wrapper (values are `rhoapi::Par`, never reparsed source). |
| `source-oracle` (`rholang-runtime`) | *(none)* | **on** | Hand-authored Rholang source-evaluation helpers used only by source-oracle regression tests. |

## Environment Variables

PraTTaIL reads a small set of `PRATTAIL_*` environment variables. They fall into three
categories, distinguished by **when the read is compiled** and **what enables the effect**:

- **Config / limits** — *always* compiled and read (no feature required). They tune codegen or
  bound the walker.
- **Diagnostics (walker-trace-gated)** — stderr trace/dump selectors. The read itself is
  **compiled out of the default build**; it exists only under `--features walker-trace`. When
  compiled in, each variable independently selects its diagnostic at runtime. Zero cost by
  default (see [Optional Cargo Features](#optional-cargo-features)).
- **Instrumentation (feature-paired)** — read at runtime, but the effect only materialises in a
  build that also includes the paired feature (`walker-stats` or `hang-dump`).

```
                       PRATTAIL_* diagnostic env vars
                                    │
          ┌─────────────────────────┴─────────────────────────┐
      default build                          cargo build --features walker-trace
   (production surface)                          (trace build, any profile)
          │                                                    │
  trace_diag!{…} / #[cfg] gate                     trace_diag!{…} / #[cfg] gate
  expands to NOTHING                               expands the env read + dump IN
          │                                                    │
  env var is never read                          each var (e.g. PRATTAIL_CGLL_FENCE_DIAG=1)
  → no branch, zero hot-path cost                 selects its diagnostic at runtime
```

### Config / limits (always live)

| Variable | Category | Effect |
|----------|----------|--------|
| `PRATTAIL_AUTO_OPTIMIZE` | config | `all` / `none` / (case-insensitive other) — force-on, force-off, or auto-threshold the incremental FIRST/FOLLOW + cost-benefit optimization gates during codegen. Surfaced by lints **I08** (active) / **I09** (parse error). |
| `PRATTAIL_CGLL_BUDGET` | limit | Step budget for the canonical-GLL pure run. Default `20_000_000`. |
| `PRATTAIL_MAX_STEPS` | limit | Max walker steps for the end-of-input drivers. Default = the caller's `default_max_steps`. |
| `PRATTAIL_COVERAGE` | config | If set, emit runtime trie-path coverage instrumentation into the generated parser (drives lint **D07**). |
| `PRATTAIL_LINT_LEVEL` | config | Minimum lint severity printed: `error`, `note`, or `info` (`all` is an alias for `info`). Default = `warning`. |
| `PRATTAIL_LINT_VERBOSE` | config | If set, emit individual per-grammar lints, not just the per-grammar summary. |

### Diagnostics (compiled only under `--features walker-trace`)

Each variable is read only when the crate is built `--features walker-trace`; the read is
otherwise removed before type-checking. When compiled in, setting the variable (any value, or
`=1` where noted) enables that one diagnostic. `PRATTAIL_MACRO_TRACE` is a **codegen-time**
(`language!`-expansion) tracer and is additionally gated in `mettail-macros`.

| Variable | Category | Effect |
|----------|----------|--------|
| `PRATTAIL_CANONICAL_GLL_STATS` | diagnostic | Canonical-GLL per-run statistics dump. |
| `PRATTAIL_CGLL_DIAG` | diagnostic | `CGLL-DIAG` accept trace (`classic_root → bin_root`, span). |
| `PRATTAIL_CGLL_EVENT_DIAG` | diagnostic | `CGLL-EVENTS` GSS event/winner trace. |
| `PRATTAIL_CGLL_FENCE_DIAG` | diagnostic | `CGLL-FENCE` replay-adjacency / reconnection-refute trace. |
| `PRATTAIL_CGLL_REALIZE_DIAG` | diagnostic | SPPF realization / ancestor-chain trace. |
| `PRATTAIL_CGLL_PURE_TRACE` | diagnostic | Capped canonical-GLL protocol trace; `=<n>` steps (non-numeric ⇒ 400). |
| `PRATTAIL_CGLL_PURE_COLLDIAG` | diagnostic | Canonical-GLL collection-close trace. |
| `PRATTAIL_CGLL_PURE_FOLDTRAP` | diagnostic | Canonical-GLL fold-trap trace. |
| `PRATTAIL_CGLL_PURE_WFCHECK` | diagnostic | Canonical-GLL well-formedness check dump. |
| `PRATTAIL_CGLL_PURE_FDUMP` | diagnostic | Canonical-GLL frontier dump. |
| `PRATTAIL_GRP_FIRE_DIAG` | diagnostic | `GRP-FIRE` guarded-reconnect fire trace. |
| `PRATTAIL_GRP_GUARD_DIAG` | diagnostic | `GRP-PROJ-SUPPRESS-PURE` guarded-reconnect projection-suppress trace. |
| `PRATTAIL_RD_U1_DIAG` | diagnostic | RD-U1 post-window recovery probe. |
| `PRATTAIL_DISPATCH_TRACE` | diagnostic | `DISPATCH-DROP` dispatch-table shadowing trace. |
| `PRATTAIL_ENTROPY` | diagnostic | Per-category dispatch-entropy report (codegen). |
| `PRATTAIL_DUMP_EBNF` | diagnostic | Write the grammar's EBNF (codegen). Value is the output dir/target. |
| `PRATTAIL_DUMP_PARSER` | diagnostic | Write the generated parser source (codegen). `=1` ⇒ current dir, else the given dir. |
| `PRATTAIL_MACRO_TRACE` | diagnostic | `language!` macro + lexer pipeline stage tracer (codegen; also gated in `mettail-macros`). |

### Instrumentation (feature-paired)

| Variable | Category | Paired feature | Effect |
|----------|----------|----------------|--------|
| `PRATTAIL_WALKER_STATS` | instrumentation | `walker-stats` | `=1` ⇒ print the walker counter summary to stderr at parse end. |
| `PRATTAIL_HANG_DUMP` | instrumentation | `hang-dump` | If set, install the SIGUSR1 walker-state snapshot handler. |
| `PRATTAIL_HANG_DUMP_PATH` | instrumentation | `hang-dump` | Destination file for the snapshot (default: stderr). |
| `PRATTAIL_HANG_WATCHDOG` | instrumentation | `hang-dump` | Watchdog interval in seconds; auto-dumps when the step counter stops advancing. |

### Removed A/B levers

The single-engine re-platform collapsed the parser's former A/B kill-switches and isolation
levers to their **shipped defaults**; the following variables **no longer exist** as live reads
(a few survive only inside explanatory comments, and are documented here so readers do not go
looking for them):

- **`PRATTAIL_NO_*` isolation family** — `PRATTAIL_NO_CANONICAL_GLL`,
  `PRATTAIL_NO_CHANNEL_FIRST_RECONNECT`, `PRATTAIL_NO_SEND_SUGAR_CANON`.
- **Other kill-switches / levers** — `PRATTAIL_SEP_RECONVERGE`,
  `PRATTAIL_PROJ_CACHE_POS_QUOTIENT`, `PRATTAIL_FP_LAZY`, `PRATTAIL_REALIZE_DEDUP`,
  `PRATTAIL_REALIZE_TRACE`, `PRATTAIL_SR_SUBSUME`, `PRATTAIL_CGLL_HYBRID`,
  `PRATTAIL_CGLL_BINARIZE`, `PRATTAIL_CGLL_RETSLOT`, `PRATTAIL_EP_P1` / `PRATTAIL_EP_P2` /
  `PRATTAIL_EP_P4_DEMOTE`, `PRATTAIL_TRACE` / `PRATTAIL_TRACE_STRICT`.
- **Reserved-but-never-wired** — `PRATTAIL_CACHE_DIR` (an incremental-cache convention kept for
  a future implementation; reads no value today).

Canonical-GLL parsing, first-token reconnection, send-sugar canonicalization, lazy
fingerprinting, and realization dedup are now the **unconditional** shipped behavior.

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
in [`prattail/src/lint/`](../../src/lint/). The public API includes:
- `emit_diagnostic()` — emit a single colorized diagnostic to stderr
- `format_diagnostic_colored()` — format without emitting (for custom output)
- `colorize_backtick_spans()` — backtick highlighting helper
- `ansi` module — ANSI color constants

Grammar-level lints (G/W/R/C/D/P) run during the Generate phase via `run_lints()`.
Equation/rewrite-network lints with historical A01--A10 identifiers, dispatch
lints (DIS01--DIS05), lexer lints (LEX01--LEX05),
and parser lints (PAR01--PAR05) also run in `run_lints()`. Composition lints
(X01--X06) run during `compose_languages!` via `run_composition_lints()`. Pipeline
info messages are emitted inline. Historical Ascent macro-phase identifiers
G25--G31, G35, G38, G41--G42, W09, C-AP01--C-AP05, and I10 have no production
emitter in the current Dovetail/Rho pipeline; their pages are retained only as
an architecture record.
Mathematical analysis lints (T/V/S/N/L/E/M/K) run in the same phase, with results
provided by the 6-phase analysis pipeline. Advanced automata lints
(SYM/O/N06-07/V05-06/PT/RA/PR/MT/MS/MSO/TW), predicated type lints (PB/UN/SL/LT),
refinement type lints (RT01–RT06), symbolic finite transducer lints (SFT01–SFT04),
and e-graph equality saturation lints (EG01–EG04) all run in the same parallel
analysis phase; their results are collected into `MathAnalysisResults` fields and
fed to `LintContext` for emission. EG04 interacts with TRS confluence analysis to
suppress T01 when joinability witnesses are found.

Each such lint is grouped under an **analysis-category label** — the value shown in
the **Feature Gate** column of the tables above (e.g. `trs-analysis`, `symbolic-automata`,
`presburger`, `unification`, `lattice-theory`, `logict`, `type-system`, `sft`, `egraph`).
These labels are lint namespaces, **not** `cargo --features` toggles: whether a given lint
fires is decided at grammar-analysis time by predicate dispatch over the grammar's guards, not
by a Cargo feature. See [About the Feature Gate Column](#about-the-feature-gate-column) for the
full explanation (including the advanced-automata capability labels — `buchi`, `alternating`,
`vpa`, etc. — which name always-compiled compilers dispatched by the `predicate_dispatch`
runtime registry rather than Cargo features). See
[advanced-automata-overview.md](../design/advanced-automata-overview.md) for the full module
architecture.
