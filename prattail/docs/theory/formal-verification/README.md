# Formal Verification: Rocq Proofs for PraTTaIL Mathematical Analyses

## Why Formal Verification

PraTTaIL's mathematical analysis pipeline makes strong correctness claims:
semiring arithmetic underpins provenance tracking and weighted analysis;
WPDS poststar/prestar must accept exactly the right set of configurations;
VPA closure properties enable grammar equivalence checking; KAT encodings
reduce Hoare reasoning to equational algebra; and Buchi-WPDS products
must faithfully capture liveness properties. A bug in any of these would
silently produce wrong analysis results -- false positives, missed
dead rules, or unsound verification verdicts.

These are not the kind of bugs that unit tests reliably catch. The
correctness arguments involve universally quantified invariants over
infinite configuration spaces. Machine-checked proofs in Rocq (Coq 9.1)
provide the strongest possible assurance: every theorem is verified by
the Rocq kernel, and every axiom is explicit.

The five proof files together contain **3,474 lines** of Rocq with
**zero `Admitted`** stubs -- every proof obligation is fully discharged.


## Proof Files

| # | File | Lines | Subject | Doc |
|---|------|------:|---------|-----|
| 6.1 | `SemiringLaws.v` | 877 | Semiring axioms for Provenance, Relational, and KAT weight domains | [semiring-laws.md](semiring-laws.md) |
| 6.2 | `WpdsCorrectness.v` | 950 | Poststar/prestar soundness, saturation convergence, MOVP fixpoint | [wpds-correctness.md](wpds-correctness.md) |
| 6.3 | `VpaClosureProperties.v` | 518 | VPA complement, intersection, decidable equivalence | [vpa-closure.md](vpa-closure.md) |
| 6.4 | `KatSoundness.v` | 494 | KAT denotational semantics, Hoare triple soundness & completeness | [kat-soundness.md](kat-soundness.md) |
| 6.5 | `BuchiWpdsProduct.v` | 635 | Buchi x WPDS product construction, SCC-based emptiness | [buchi-wpds-product.md](buchi-wpds-product.md) |

All proofs reside in:

```
formal/rocq/mathematical_analyses/theories/
```


## Dependency Order

```
   SemiringLaws.v ────────────> KatSoundness.v
        (6.1)          depends on      (6.4)

   WpdsCorrectness.v ────────> BuchiWpdsProduct.v
        (6.2)          depends on      (6.5)

   VpaClosureProperties.v
        (6.3)              standalone
```

KatSoundness imports the semiring type class from SemiringLaws.
BuchiWpdsProduct builds on the WPDS model from WpdsCorrectness.
VpaClosureProperties is self-contained.


## Proof Traceability Table

Every Rocq definition maps to a specific Rust construct. This table
consolidates the traceability from all five proof files.

### SemiringLaws.v

| Rocq Definition | Rust Code | Location |
|----------------|-----------|----------|
| `Semiring` (class) | `trait Semiring` | `automata/semiring.rs:36` |
| `prov_plus` | `ProvenanceWeight::plus` | `provenance.rs:180` |
| `prov_times` | `ProvenanceWeight::times` | `provenance.rs:193` |
| `prov_zero` | `ProvenanceWeight::zero` | `provenance.rs:149` |
| `prov_one` | `ProvenanceWeight::one` | `provenance.rs:155` |
| `rel_plus` | `HeapSemiring::plus` for Relational | `relational.rs:155` |
| `rel_times` | `HeapSemiring::times` for Relational | `relational.rs:165` |
| `rel_zero` | `RelationalWeight::empty` | `relational.rs:75` |
| `rel_one` | `RelationalWeight::identity` | `relational.rs:83` |
| `kat_zero` / `kat_one` | `KatExpr::Zero` / `KatExpr::One` | `kat.rs:134-135` |
| `kat_seq` / `kat_alt` | `KatExpr::Seq` / `KatExpr::Alt` | `kat.rs:143-145` |
| `kat_star` | `KatExpr::Star` | `kat.rs:147` |
| `kat_test` | `KatExpr::Test` | `kat.rs:139` |
| `verify_hoare_triple` | `verify_hoare_triple` | `kat.rs:568` |

### WpdsCorrectness.v

| Rocq Definition | Rust Code | Location |
|----------------|-----------|----------|
| `symbol` | `StackSymbol { category, rule, pos }` | `wpds.rs:62-69` |
| `sl_rule` (Pop/Replace/Push) | `WpdsRule<W>` enum | `wpds.rs:104-133` |
| `sl_step` | one-step PDS execution | `wpds.rs:101-103` |
| `sl_reachable` | reflexive-transitive closure of step | `wpds.rs:689-706` |
| `pa_reads` | path through P-automaton transitions | `wpds.rs:248-254` |
| `sl_accepts` | `PAutomaton` acceptance | `wpds.rs:314-324` |
| `poststar` | `poststar()` saturation loop | `wpds.rs:707-840` |
| `prestar` | `prestar()` saturation loop | `wpds.rs:855-1005` |
| `sat_step` | worklist pop + rule match | `wpds.rs:735-836` |
| `existing` (transition map) | `HashMap<(from,sym,to), W>` | `wpds.rs:724-729` |
| `embed_p` | `p_state` (= 0) | `wpds.rs:709` |

### VpaClosureProperties.v

| Rocq Definition | Rust Code | Location |
|----------------|-----------|----------|
| `symbol_kind` | `SymbolKind` | `vpa.rs:100-110` |
| `classify` | `VpaAlphabet::classify()` | `vpa.rs:75-86` |
| `step` / `run` / `accepts` | VPA run simulation | `vpa.rs:130-175` |
| `complement_is_final` | `complement()` | `vpa.rs` |
| `prod_step` / `prod_run` | `intersect()` | `vpa.rs` |
| `vpa_equivalence_decidable` | `check_vpa_equivalence()` | `vpa.rs` |

### KatSoundness.v

| Rocq Definition | Rust Code | Location |
|----------------|-----------|----------|
| `bool_test` | `BooleanTest` | `kat.rs:56-69` |
| `kat_expr` | `KatExpr` | `kat.rs:131-147` |
| `test_denote` | `eval_test()` | `kat.rs:421-430` |
| `denote` | symbolic bisimulation semantics | `kat.rs:312-382` |
| `hoare_valid` | `verify_hoare_triple()` | `kat.rs:568-578` |
| `hoare_condition` | `KatExpr::hoare_condition()` | `kat.rs:179-184` |
| `kat_simplify` | `simplify()` | `kat.rs:516-553` |

### BuchiWpdsProduct.v

| Rocq Definition | Rust Code | Location |
|----------------|-----------|----------|
| `wpds_config` | `StackSymbol` + `WpdsRule` | `wpds.rs:62-133` |
| `wpds_step` | poststar saturation | `wpds.rs` (poststar fn) |
| `buchi_state` | `BuchiState` | `buchi.rs:58-69` |
| `buchi_transition` | `BuchiTransition` | `buchi.rs:112-131` |
| `buchi_intersect` | `buchi_intersect()` | `buchi.rs:277-385` |
| `check_emptiness` | `check_emptiness()` | `buchi.rs:402-578` |
| `product_config` | product construction in pipeline | `pipeline.rs` |
| `scc_has_accepting` | Tarjan SCC + accepting check | `buchi.rs:462-575` |


## Build Instructions

All proofs require Rocq 9.1 with the `coq-hammer-tactics` and
`coq-equations` packages installed.

### Standard Build

```bash
cd formal/rocq/mathematical_analyses
make
```

### Resource-Limited Build (recommended)

To prevent the proof checker from consuming excessive system resources,
use `systemd-run` with resource limits:

```bash
cd formal/rocq/mathematical_analyses
systemd-run --user --scope \
  -p MemoryMax=126G \
  -p CPUQuota=1800% \
  -p IOWeight=30 \
  -p TasksMax=200 \
  make -j1
```

The `-j1` flag ensures serial compilation, which is important for
memory-intensive modular proofs. The memory cap of 126 GB is 50% of the
development machine's 252 GB RAM, and 1800% CPU quota allows up to 18
cores.

### Clean

```bash
make clean
```

This removes all generated `.vo`, `.vok`, `.vos`, `.glob` files and the
auto-generated `CoqMakefile`.


## External Dependencies

| Dependency | Use |
|-----------|-----|
| `coq-hammer-tactics` | `hauto`, `sauto`, `firstorder` automation used in relational and SCC proofs |
| `coq-equations` | `Equations` plugin used in KatSoundness for structural recursion |
| Stdlib modules | `List`, `Bool`, `Arith`, `PeanoNat`, `Lia`, `Relations`, `ZArith`, `Classical`, `Decidable`, `Permutation`, `SetoidList`, `Setoid` |


## Summary Statistics

| Metric | Value |
|--------|------:|
| Total files | 5 |
| Total lines | 3,474 |
| `Admitted` stubs | 0 |
| Theorem/Lemma count | ~75 |
| Semiring instances | 3 (Provenance, Relational, KAT) |
| Classical logic use | WpdsCorrectness only (MOVP convergence) |
| Rocq version | 9.1 |
