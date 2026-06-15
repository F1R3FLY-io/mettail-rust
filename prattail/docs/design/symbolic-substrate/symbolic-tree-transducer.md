# Symbolic Tree Automata & Transducers — the structural axis

**Status:** IMPLEMENTED (2026-06-15). Companion to
[any-algebra-substrate.md](any-algebra-substrate.md). Records the design of the
structural (tree) generalization of the word SFA/SFT machinery so it can be
reconstructed from scratch.

---

## 1. From words to trees

A symbolic **word** automaton/transducer runs left-to-right over `list A`,
each step guarded by a predicate of an effective Boolean algebra `A`. The
structural axis lifts this to **ranked trees** `SymTerm<D>` (a constructor + a
payload + a list of children), processed **bottom-up**: each node's transition
is guarded by a payload predicate over `A`, and the result depends on the node's
constructor and the (already-computed) states of its children.

The lift reuses the word machinery's *shape*; only the step changes
(word-step → tree bottom-up step). The Coq proofs are the word proofs with the
induction principle changed from `list` to a hand-rolled `tree_ind'`.

## 2. `SymbolicTreeAutomaton<A>` (`sym_tree.rs`)

- `SymTerm<D>`: a ranked term — constructor label, payload `D`, children
  `Vec<SymTerm<D>>`.
- `TreePred<P>`: a tree predicate — "constructor `c` ∧ payload ⊨ φ (a `P`) ∧
  child_i ⊨ φ_i", with `Var` wildcards.
- `TreeAlgebra<A>`: the EBA whose domain is `SymTerm<A::Domain>` and whose
  predicates are `TreePred<A::Predicate>`. Operations: `run`/`accepts`/`is_empty`/
  `witness`/`intersect`/`union`/`determinize`/`complement`.
- Boolean closure is by **tree-automaton product/union/complement**. Complement
  needs a deterministic complete automaton; determinization classifies payloads
  by **minterms** over the payload predicates (the same minterm helper the
  collection algebras use — `collection_algebra::minterms`). `SetTheoreticTypeSystem`
  (`type_system.rs`) is the payload-free special case (`elem = unit`) that
  delegates to the generic ops (single source of truth, no RT3 regression).

`bottom_up_evaluate` (`tree_automaton.rs`) is the engine; `parity_tree.rs`
(μ-calculus → parity alternating tree automata) backs the modal decisions.

### Decidable emptiness + witness (the closure theorem)

`TreeAlgebraClosure.v` proves `tree_eba_laws : EBA_Laws tree_eba` —
zero-admission. The Coq model is a **deterministic complete bottom-up tree
automaton** (a `DFTA` record carrying its finite state set, transition, and final
predicate) over a finite payload-class partition (the satisfiable minterms,
abstracted as `Sigma`/`letter`/`pick`). Because the automaton is deterministic
and complete:

- **`conj`/`disj`** are the deterministic product (`run_tprod` proves
  `run (product M N) t = (run M t, run N t)`); no determinization is needed.
- **`neg`** is the final-flip (`run_tneg`/`teval_tneg`) — exact complement.
- **SAT/WIT** are decided by a bottom-up **saturation** (`sat_pairs`) that carries
  a *witness tree per reachable state* (the `PairInv` invariant: every recorded
  `(q, t)` satisfies `run M t = q`), driven by a generic finite-universe
  chain-stabilization fixpoint (`Section Stabilization`: an extensive, monotone,
  `q_enum`-bounded operator stabilizes within `|q_enum|` steps). `tsat`/`twit`
  soundness+completeness follow.

The only abstraction is the documented payload-minterm partition (its finiteness
and inhabitation are verified in `CollectionAlgebraClosure.v`); the structural
automaton content is fully proved with no axioms.

## 3. `SymbolicTreeTransducer<A,B>` (`sym_tree_transducer.rs`)

Generalizes `sft.rs` from words (`list`) to ranked trees: bottom-up guarded
transitions, a per-node `OutputBuilder`/`PayloadOut`, and the operations
`transduce` / `compose_transduce` / `domain_sta` / `is_total` / `is_functional`.
The control structure is copied from `sft.rs`; the word-step is swapped for the
tree bottom-up step (`tree_automaton::bottom_up_evaluate`).

### Coq: the tree analogs of the word proofs (`rocq-sft`)

Both files define ranked trees `Tree X := tnode : X -> list (Tree X) -> Tree X`
with a hand-rolled strong induction principle `tree_ind'` (an axiom-free
`Fixpoint`; Coq's auto-generated principle is too weak through the
`list (Tree X)` nesting).

- **`StftComposition.v`** — (a) the bottom-up relabeling homomorphism `thom`:
  `thom_id`, `thom_fusion` (the forest-fusion tree analog of
  `flat_map_flat_map`), `thom_compose_assoc`, `tcount_thom` (node-count
  preservation — the tree analog of word length); (b) the forest-transducer
  monoid `ft_compose`/`ft_identity`: left/right identity + associativity.
- **`StftFunctionality.v`** — `functional f := ∀ t, length (f t) ≤ 1`;
  identity/constant/epsilon functional, `compose_preserves_functional`,
  `domain_characterization`, `thom_preserves_tcount` (genuinely tree-recursive
  via `tree_ind'`).

These reuse the same `flat_map` theorems (`app`/`singleton`/`flat_map`) that back
the word `SftComposition.v`, so the tree and word transducer monoids share one
foundation.

## 4. `OutputTerm` — the first-class output-function algebra (`sft.rs §8`)

The opaque `OutputFunction::Map`/`FlatMap` closures are the *provability hole*:
`SymbolicFiniteTransducer::compose` must go conservative on them (an opaque
`FlatMap` over-approximation). `OutputTerm<A,B> {Eps, Id, Const, Concat}` replaces
them wherever the output is structural — a finite, fully-inspectable term so that
composition is a **precise symbolic term** (`then`), never a black box.

`OutputTerm` carries two compatible structures, both proven in
`OutputTermAlgebra.v` up to denotational equivalence:

- a **monoid** `(Concat, Eps)` — output concatenation, associative with unit
  `Eps` (`oconcat_assoc`/`oconcat_eps_{l,r}`);
- a **category** `(then, Id)` — sequential composition `A→B then B→C`,
  associative with unit `Id` (`othen_assoc`/`othen_id_{l,r}`);

plus the β compose-correctness law
`othen_correct : oapply (othen s t) x = oapply_all t (oapply s x)` — exactly the
Rust contract `(self.then(next)).apply(i) = next.apply_all(self.apply(i))`. The
precise composition `then` (`Eps∘_=Eps`, `Const∘t=Const(apply_all t v)`,
`Id∘t=t`, `Concat` distributes) produces no closure, upgrading the conservative
compose path. `From<OutputTerm> for OutputFunction` lowers a term for the runtime
while keeping the term as the static-analysis source of truth.

## 5. Concept → code → proof

| Concept | Rust | Zero-admission Coq |
|---|---|---|
| Symbolic tree automaton + Boolean closure | `sym_tree::TreeAlgebra` | `TreeAlgebraClosure.v` `tree_eba_laws` |
| Symbolic tree transducer | `sym_tree_transducer::SymbolicTreeTransducer` | `Stft{Composition,Functionality}.v` |
| Tree relabel homomorphism + fusion | (analysis layer) | `StftComposition.v` `thom_fusion`/`tcount_thom` |
| Functionality preservation | `is_functional` | `StftFunctionality.v` `compose_preserves_functional` |
| Output-term algebra (precise compose) | `sft::OutputTerm` (`then`) | `OutputTermAlgebra.v` `othen_correct`/`othen_assoc`/`oconcat_assoc` |

Build: `make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-sft` (the `sft`
theory dir is in the zero-admission `DEFAULT_ROOTS`). Rust:
`cargo test -p mettail-prattail --lib sft` / `sym_tree`.

## 6. Why this matters

Structural guards gain the *same* dead-code / overlap / satisfiability lints that
numeric guards have today: `p1 ∩ p2` unSAT ⇒ the two patterns are disjoint;
`p1 implies p2` ⇒ `p1` subsumes `p2`; `is_satisfiable` ⇒ the pattern is
inhabited, with `witness` producing a sample matched term. The runtime matcher is
untouched; only the compile-time analysis re-targets onto `TreeAlgebra`, and the
precise `OutputTerm` composition makes transducer pipelines (e.g. desugaring +
lowering chains) analyzable end-to-end instead of bottoming out in a closure.
