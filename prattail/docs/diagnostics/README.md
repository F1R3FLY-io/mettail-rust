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
| V05 | weighted-vpa-non-determinizable | Warning | `vpa` | Non-idempotent semiring weights combined with ambiguous transitions — weighted subset construction may diverge |
| V06 | weighted-vpa-inclusion-failure | Warning | `vpa` | Recovery automaton accepts inputs with cost exceeding threshold — stack-bounded repair too expensive |

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
Advanced automata lints (SYM/O/N06-07/V05-06/PT/RA/PR/MT/MS/MSO/TW) run in the
same parallel analysis phase, each gated by its respective feature flag. Results
are collected into `MathAnalysisResults` fields and fed to `LintContext` for
emission. Predicated type lints (PB/UN/SL/LT) run in the same phase, gated by
their respective feature flags (`presburger`, `unification`, `lattice-theory`,
`logict`). Refinement type lints (RT01–RT06) run in the same phase, gated by
the `type-system` feature flag. Symbolic finite transducer lints (SFT01–SFT04)
run in the same phase, gated by the `sft` feature flag. E-graph equality
saturation lints (EG01–EG04) run in the same phase, gated by the `egraph`
feature flag; EG04 interacts with TRS confluence analysis to suppress T01
when joinability witnesses are found. See [advanced-automata-overview.md](../design/advanced-automata-overview.md)
for the full module architecture.
