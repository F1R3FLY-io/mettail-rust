# References

Last updated: 2026-06-23

This page collects the external literature, the repository-local source files, and
the mechanized proofs that the suite cites. External works link to a DOI where a
valid one exists. Repository-local paths are checked by
[`validate.sh`](validate.sh) to resolve from the repository root.

## External literature

### dantoni-veanes-2017

L. D'Antoni and M. Veanes. *The Power of Symbolic Automata and Transducers
(Invited Tutorial).* Computer Aided Verification (CAV) 2017, LNCS 10426, pp. 47–67.
The foundational survey of effective Boolean algebras, symbolic automata, symbolic
(tree) transducers, their composition algorithms, and closure properties.
DOI: [10.1007/978-3-319-63387-9_3](https://doi.org/10.1007/978-3-319-63387-9_3).

### dantoni-veanes-2014

L. D'Antoni and M. Veanes. *Minimization of Symbolic Automata.* Principles of
Programming Languages (POPL) 2014, pp. 541–553. Minterm-based determinization and
minimization of symbolic automata.
DOI: [10.1145/2535838.2535849](https://doi.org/10.1145/2535838.2535849).

### dantoni-veanes-2013

L. D'Antoni and M. Veanes. *Static Analysis of String Encoders and Decoders.*
Verification, Model Checking, and Abstract Interpretation (VMCAI) 2013, LNCS 7737,
pp. 209–228. The pre-image / post-image static analysis of symbolic transducers.
DOI: [10.1007/978-3-642-35873-9_14](https://doi.org/10.1007/978-3-642-35873-9_14).

### veanes-popl-2012

M. Veanes, P. Hooimeijer, B. Livshits, D. Molnar, and N. Bjørner. *Symbolic Finite
State Transducers: Algorithms and Applications.* Principles of Programming Languages
(POPL) 2012, pp. 137–150. The symbolic-finite-transducer model — predicate-guarded
edges with output functions, composition, and functionality — realized by
`prattail/src/sft.rs`.
DOI: [10.1145/2103656.2103674](https://doi.org/10.1145/2103656.2103674).

### buchi-1960

J. R. Büchi. *Weak Second-Order Arithmetic and Finite Automata.* Zeitschrift für
mathematische Logik und Grundlagen der Mathematik, 6(1–6):66–92, 1960. The
automata-theoretic characterization of Presburger-definable sets that underlies the
`PresburgerAlgebra` decision procedure.
DOI: [10.1002/malq.19600060105](https://doi.org/10.1002/malq.19600060105).

### bartzis-bultan-2003

C. Bartzis and T. Bultan. *Efficient Symbolic Representations for Arithmetic
Constraints in Verification.* International Journal of Foundations of Computer
Science, 14(4):605–624, 2003. The binary-encoded remainder-NFA construction for
linear-integer (Presburger) constraints that `presburger.rs` implements. (No
resolvable DOI; cited by venue.)

### nelson-oppen-1979

G. Nelson and D. C. Oppen. *Simplification by Cooperating Decision Procedures.* ACM
Transactions on Programming Languages and Systems, 1(2):245–257, 1979. The
cooperating-decision-procedures method whose base case `TheoryCombination.v`
mechanizes for combining two decidable theories.
DOI: [10.1145/357073.357079](https://doi.org/10.1145/357073.357079).

### stay-meredith-2016

M. Stay and L. G. Meredith. *Logic as a Distributive Law.* arXiv:1610.02247, 2016.
The OSLF (Ordered Linear-Substructural Funding) resource-logic reading of a
calculus that [09 — OSLF Composition](09-oslf-composition.md) composes the predicate
algebra with. Available at
[arxiv.org/abs/1610.02247](https://arxiv.org/abs/1610.02247).

### tata

H. Comon, M. Dauchet, R. Gilleron, F. Jacquemard, D. Lugiez, S. Tison, and M.
Tommasi. *Tree Automata Techniques and Applications (TATA).* 2007. The classical
tree-automaton and tree-transducer background for the tree closure
([05 §7](05-algebra-pyramid-and-decidability.md)) and the symbolic tree transducer
([04 §8](04-symbolic-transducers-sft-stft.md)). Available at
[inria.hal.science/hal-03367725](https://inria.hal.science/hal-03367725).

## Intuitionistic logic, topology, and behavioral equivalence

These ground the Heyting-algebra treatment of behavioral constraints
([12 — Heyting Behavioral Logic](12-heyting-behavioral-logic.md)) as theory; per the
suite's citation discipline none corresponds to a mechanized lemma.

### heyting-1930

A. Heyting. *Die formalen Regeln der intuitionistischen Logik.* Sitzungsberichte der
Preußischen Akademie der Wissenschaften, 1930. The formal intuitionistic calculus
whose algebraization is the Heyting algebra. (No resolvable DOI; cited by venue.)

### troelstra-vandalen-1988

A. S. Troelstra and D. van Dalen. *Constructivism in Mathematics: An Introduction.*
North-Holland, 1988. The Brouwer–Heyting–Kolmogorov interpretation — the
evidence/provability reading of the connectives used to argue that behavioral logic
is intuitionistic. (Cited by venue.)

### johnstone-1982

P. T. Johnstone. *Stone Spaces.* Cambridge University Press, 1982. Frames and locales
(lattices of opens as Heyting algebras) — the topological model of intuitionistic
logic and the "negation as interior" picture. (Cited by venue.)

### esakia-2019

L. Esakia. *Heyting Algebras: Duality Theory* (G. Bezhanishvili and W. Holliday,
eds.). Trends in Logic 50, Springer, 2019. Esakia duality — Heyting algebras are dual
to Esakia spaces, the Heyting analog of Stone duality.
DOI: [10.1007/978-3-030-12096-2](https://doi.org/10.1007/978-3-030-12096-2).

### maclane-moerdijk-1992

S. Mac Lane and I. Moerdijk. *Sheaves in Geometry and Logic: A First Introduction to
Topos Theory.* Springer, 1992. The subobject classifier of an elementary topos as a
Heyting algebra — the topos-theoretic provenance of intuitionistic logic.
DOI: [10.1007/978-1-4612-0927-0](https://doi.org/10.1007/978-1-4612-0927-0).

### hennessy-milner-1985

M. Hennessy and R. Milner. *Algebraic Laws for Nondeterminism and Concurrency.*
Journal of the ACM, 32(1):137–161, 1985. The Hennessy–Milner theorem: over an
image-finite LTS, two states satisfy the same modal formulas iff they are bisimilar —
the basis for bisimulation-invariance of behavioral predicates
([12 §4](12-heyting-behavioral-logic.md)).
DOI: [10.1145/2455.2460](https://doi.org/10.1145/2455.2460).

### van-benthem-1983

J. van Benthem. *Modal Logic and Classical Logic.* Bibliopolis, 1983. The van Benthem
characterization: modal logic is exactly the bisimulation-invariant fragment of
first-order logic. (Cited by venue.)

## The constraint-theory engine (LogicT)

These ground the backtracking logic-monad engine
([13 — The Constraint-Theory Engine](13-constraint-theory-engine.md)).

### kiselyov-2005

O. Kiselyov, C. Shan, D. P. Friedman, and A. Sabry. *Backtracking, Interleaving, and
Terminating Monad Transformers (Functional Pearl).* International Conference on
Functional Programming (ICFP) 2005, pp. 192–203. The LogicT monad and its fair
operators (`msplit`, `interleave`, `fair_conjoin`, `ifte`, `once`) that
`prattail/src/logict.rs` realizes.
DOI: [10.1145/1086365.1086390](https://doi.org/10.1145/1086365.1086390).

### hemann-friedman-2013

J. Hemann and D. P. Friedman. *μKanren: A Minimal Functional Core for Relational
Programming.* Scheme and Functional Programming Workshop, 2013. The minimal
relational-programming core in the lineage of the constraint-theory search. (No
resolvable DOI; cited by venue.)

## Temporal logic and the modal μ-calculus

Ground the modal/temporal fixpoint logic of the behavioral Heyting algebra
([15 — The Modal μ-Calculus](15-mu-calculus.md)).

### kozen-1983

D. Kozen. *Results on the Propositional μ-Calculus.* Theoretical Computer Science
27(3), 1983, pp. 333–354. The propositional modal μ-calculus: syntax with least (`μX`)
and greatest (`νX`) fixpoint binders over the modalities, its fixpoint semantics, and
axiomatization.
DOI: [10.1016/0304-3975(82)90125-6](https://doi.org/10.1016/0304-3975%2882%2990125-6).

### tarski-1955

A. Tarski. *A Lattice-Theoretical Fixpoint Theorem and Its Applications.* Pacific
Journal of Mathematics 5(2), 1955, pp. 285–309. The Knaster–Tarski theorem: a monotone
map on a complete lattice has a least and a greatest fixpoint — the existence guarantee
behind `μX`/`νX`.
DOI: [10.2140/pjm.1955.5.285](https://doi.org/10.2140/pjm.1955.5.285).

### emerson-clarke-1980

E. A. Emerson and E. M. Clarke. *Characterizing Correctness Properties of Parallel
Programs Using Fixpoints.* International Colloquium on Automata, Languages and
Programming (ICALP) 1980, LNCS 85, pp. 169–181. The fixpoint characterization of
branching-time (CTL) temporal properties — the basis of the CTL-to-μ encoding. (The
linear-time alternation-free model-checking refinement is E. A. Emerson and C.-L. Lei,
*Efficient Model Checking in Fragments of the Propositional μ-Calculus,* LICS 1986,
pp. 267–278; cited by venue.)
DOI: [10.1007/3-540-10003-2_69](https://doi.org/10.1007/3-540-10003-2_69).

### bradfield-stirling-2001

J. Bradfield and C. Stirling. *Modal Logics and mu-Calculi: An Introduction.* Handbook
of Process Algebra, Elsevier, 2001, pp. 293–330. The standard survey of the modal
μ-calculus, its expressiveness, and model checking.
DOI: [10.1016/b978-044482830-9/50022-9](https://doi.org/10.1016/b978-044482830-9/50022-9).

## Decision procedures: arithmetic, unification, order

Ground the shipped decidable constraint theories cataloged in
[13 §2.2](13-constraint-theory-engine.md) and the leaf-algebra decision procedures
of [02 §5](02-effective-boolean-algebra.md). (The Büchi / Bartzis–Bultan
automata constructions for Presburger arithmetic are cited above under
[buchi-1960](#buchi-1960) and [bartzis-bultan-2003](#bartzis-bultan-2003).)

### presburger-1929

M. Presburger. *Über die Vollständigkeit eines gewissen Systems der Arithmetik ganzer
Zahlen, in welchem die Addition als einzige Operation hervortritt.* Comptes Rendus du I
Congrès de Mathématiciens des Pays Slaves, Warsaw, 1929, pp. 92–101. The decidability of
the first-order theory of `⟨ℤ, +, ≤⟩` — the classical backing for the `PresburgerTheory`
decision procedure. (English translation by Stansifer, 1984; cited by venue.)

### robinson-1965

J. A. Robinson. *A Machine-Oriented Logic Based on the Resolution Principle.* Journal of
the ACM 12(1), 1965, pp. 23–41. The existence and computability of the most general
unifier of a set of term equations.
DOI: [10.1145/321250.321253](https://doi.org/10.1145/321250.321253).

### martelli-montanari-1982

A. Martelli and U. Montanari. *An Efficient Unification Algorithm.* ACM Transactions on
Programming Languages and Systems 4(2), 1982, pp. 258–282. The transformation system
(delete / decompose / eliminate-with-occurs-check / conflict) that `UnificationTheory`
implements.
DOI: [10.1145/357162.357169](https://doi.org/10.1145/357162.357169).

### warshall-1962

S. Warshall. *A Theorem on Boolean Matrices.* Journal of the ACM 9(1), 1962, pp. 11–12.
The `O(n³)` transitive-closure algorithm that `LatticeTheory` uses to decide the finite
subtype order.
DOI: [10.1145/321105.321107](https://doi.org/10.1145/321105.321107).

### pierce-tapl-2002

B. C. Pierce. *Types and Programming Languages.* MIT Press, 2002 (ISBN 0-262-16209-1).
Chapter 15 (Subtyping) — the finite-lattice subtype order `LatticeTheory` realizes.
(Textbook; cited by ISBN.)

## Relational databases and quantification

Grounds the closed-world / active-domain semantics of relational quantifiers
([14 — Quantification](14-quantification.md)).

### abiteboul-hull-vianu-1995

S. Abiteboul, R. Hull, and V. Vianu. *Foundations of Databases.* Addison-Wesley, 1995
(ISBN 0-201-53771-0). The active-domain (closed-world) semantics of relational
calculus — the finite universe of constants over which a safe / domain-independent
quantifier ranges — that makes a relational `∀`/`∃` decidable. Freely available at
[webdam.inria.fr/Alice](http://webdam.inria.fr/Alice/).

## Repository-local source files

The substrate (the `prattail` crate):

- `prattail/src/symbolic.rs`
- `prattail/src/sft.rs`
- `prattail/src/sym_tree_transducer.rs`
- `prattail/src/algebra_tower.rs`
- `prattail/src/any_algebra.rs`
- `prattail/src/collection_algebra.rs`
- `prattail/src/product_nary.rs`
- `prattail/src/sym_tree.rs`
- `prattail/src/presburger.rs`
- `prattail/src/behavioral_algebra.rs`
- `prattail/src/behavioral_pred.rs`
- `prattail/src/bisimulation.rs`
- `prattail/src/string_algebra.rs`
- `prattail/src/regex_sfa.rs`
- `prattail/src/ordered_field.rs`
- `prattail/src/unification.rs`
- `prattail/src/lattice_theory.rs`
- `prattail/src/logict.rs`
- `prattail/src/logict_smt.rs`
- `prattail/src/letprop.rs`
- `prattail/src/parity_tree.rs`
- `prattail/src/hindley_milner.rs`
- `prattail/src/parser/predicate_pratt.rs`

The declaration surface (the `ast` crate) and the consumer (`rholang-codegen`):

- `ast/src/language/model.rs`
- `ast/src/language/parse.rs`
- `ast/src/grammar.rs`
- `rholang-codegen/src/backend.rs`
- `rholang-codegen/src/guard_quality.rs`
- `rholang-codegen/src/flip.rs`

The example language and its tests:

- `languages/src/guarded_rho.rs`
- `languages/tests/guarded_rho_rho_backend.rs`
- `rholang-runtime/tests/rho_guard_oracle.rs`

## Repository-local mechanized proofs (zero-admission)

Symbolic algebra (`make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-symbolic-algebra`):

- `formal/rocq/symbolic_algebra/theories/EffectiveBooleanAlgebra.v`
- `formal/rocq/symbolic_algebra/theories/ProductAlgebraClosure.v`
- `formal/rocq/symbolic_algebra/theories/SumAlgebraClosure.v`
- `formal/rocq/symbolic_algebra/theories/CollectionAlgebraClosure.v`
- `formal/rocq/symbolic_algebra/theories/TreeAlgebraClosure.v`
- `formal/rocq/symbolic_algebra/theories/TheoryCombination.v`
- `formal/rocq/symbolic_algebra/theories/HeytingAlgebra.v`
- `formal/rocq/symbolic_algebra/theories/GuardTierCertificate.v`
- `formal/rocq/symbolic_algebra/theories/BehavioralNegation.v`
- `formal/rocq/symbolic_algebra/theories/AnyAlgebraProjectionSound.v`
- `formal/rocq/symbolic_algebra/theories/GuardTierClassificationSound.v`
- `formal/rocq/symbolic_algebra/theories/SymTreeWiringSound.v`
- `formal/rocq/symbolic_algebra/theories/BehavioralTierClassificationSound.v`
- `formal/rocq/symbolic_algebra/theories/BehavioralLoweringSound.v`
- `formal/rocq/symbolic_algebra/theories/Z3WitnessChecked.v`

Symbolic transducers (`FORMAL_CAPPED_TARGET=rocq-sft`):

- `formal/rocq/sft/theories/OutputTermAlgebra.v`
- `formal/rocq/sft/theories/SftComposition.v`
- `formal/rocq/sft/theories/SftFunctionality.v`
- `formal/rocq/sft/theories/StftComposition.v`
- `formal/rocq/sft/theories/StftFunctionality.v`
- `formal/rocq/sft/theories/StftWiringSound.v`

Presburger and dispatch (`FORMAL_CAPPED_TARGET=rocq-presburger` / `rocq-predicate-dispatch`):

- `formal/rocq/presburger/theories/PresburgerBooleanAlgebra.v`
- `formal/rocq/predicate_dispatch/theories/DispatchCompleteness.v`

Advanced automata (`FORMAL_CAPPED_TARGET=rocq-advanced-automata`):

- `formal/rocq/advanced_automata/theories/RegisterEquivalence.v`
- `formal/rocq/advanced_automata/theories/BisimulationWiringSound.v`
- `formal/rocq/advanced_automata/theories/LetpropPataWiringSound.v`
- `formal/rocq/advanced_automata/theories/TraceLtlCheckSound.v`
- `formal/rocq/advanced_automata/theories/HindleyMilnerWiringSound.v`

Algebra-to-COMM bridges (`FORMAL_CAPPED_TARGET=rocq-rho-bridge`):

- `formal/rocq/rho_bridge/theories/RhoGuardedCommSoundness.v`
- `formal/rocq/rho_bridge/theories/GuardedCommSoundness.v`
- `formal/rocq/rho_bridge/theories/RhoBackendFlipGate.v`
- `formal/rocq/rho_bridge/theories/MettaOslfLawsConformance.v`
- `formal/rocq/rho_bridge/theories/MettaGsltPresentation.v`

The zero-admission gate (`FORMAL_CAPPED_TARGET=rocq-critical-zero-admission`):

- `formal/scripts/check_rocq_zero_admission.py`

## Related design documents

- `docs/design/predicated-types.md` — the predicated-type design of record.
- `docs/design/guards-block.md` — the `guards { }` block design.
- `prattail/docs/design/symbolic-substrate/any-algebra-substrate.md` — the
  `AnyAlgebra` substrate generalization.
- `prattail/docs/theory/symbolic/boolean-algebra.md` — the EBA / SFA theory note.
- `docs/design/dovetail-engine/oslf-gslt-native-fold-reduction.md` — the OSLF/GSLT
  engine treatment.
- `docs/papers/plan.md` — the GSLT/MeTTaIL paper plan, including the Hennessy–Milner
  correspondence ("processes are bisimilar iff they satisfy the same formulae").
