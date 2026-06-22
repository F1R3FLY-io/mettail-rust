# Symbolic Transducers (SFT / STFT)

Last updated: 2026-06-22

All symbols are defined in [Concepts and Glossary](01-concepts-and-glossary.md).
This document is the transduction layer. Where a symbolic finite automaton (SFA,
[03](03-symbolic-automata-sfa.md)) *recognizes* a language over an infinite
alphabet, a **symbolic finite transducer** (SFT) *transforms* one — each edge
carries an output function as well as a guard, so the machine maps inputs to
outputs symbolically. The page covers the word transducer (`SFT`), its
first-class analyzable output algebra (`OutputTerm`), composition, pre-/post-image,
single-valuedness (functionality), and the ranked-tree analog (`STFT`), and ties
every operation to its Rust entry point and its zero-admission Coq theorem.

## 1. What an SFT is

An SFA labels each edge with a predicate `φ` of an effective Boolean algebra
(EBA) and fires when the input element satisfies it. An **SFT promotes that edge
to a rule**: it additionally attaches an *output function* `f` that maps the
consumed input element to a (possibly empty) sequence of output elements drawn
from a *second* algebra. A transition is drawn

```text
q --[ φ / f ]--> q′
```

and reads: "in state `q`, on an input element `e` with `e ⊨ φ`, emit the output
sequence `f(e)` and move to `q′`." The input guard lives in an input algebra
`𝓐ᵢₙ`; the output elements live in an output algebra `𝓐ₒᵤₜ`. The two algebras may
differ (case-folding maps `char → char`; an encoder maps `char → byte`), which is
why an SFT is parameterized by *two* EBAs rather than one
([D'Antoni & Veanes, 2017](references.md#dantoni-veanes-2017)).

> **Definition 1.1 (Symbolic Finite Transducer).** A symbolic finite transducer
> is a tuple `T = (Q, 𝓐ᵢₙ, 𝓐ₒᵤₜ, Δ, q₀, F)` where:
> - `Q` is a finite set of states, `q₀ ∈ Q` the initial state (a *set* of initial
>   states in the NFA-style realization), and `F ⊆ Q` the accepting states;
> - `𝓐ᵢₙ` is the input EBA and `𝓐ₒᵤₜ` the output EBA;
> - `Δ ⊆ Q × Φ(𝓐ᵢₙ) × (Dᵢₙ → Dₒᵤₜ*) × Q` is the transition relation: each edge
>   pairs an input guard `φ ∈ Φ(𝓐ᵢₙ)` with an *output function* `f : Dᵢₙ → Dₒᵤₜ*`
>   producing a finite output word.
>
> `T` transduces an input word `w = e₁ … eₙ ∈ Dᵢₙ*` by walking a path
> `q₀ →^{φ₁/f₁} q₁ → … →^{φₙ/fₙ} qₙ` with `qₙ ∈ F` and `eᵢ ⊨ φᵢ` for every step;
> the produced output word is the concatenation `f₁(e₁) · … · fₙ(eₙ)`. The
> *relation* computed by `T` is the set of all `(w, out)` over all accepting
> paths. `T` is **functional** when that relation is a partial function (each `w`
> has at most one output).

The Rust realization is `prattail/src/sft.rs::SymbolicFiniteTransducer<A, B>`,
whose fields mirror the tuple exactly: `input_algebra: A`, `output_algebra: B`,
`states`, `transitions`, `initial_states`, `accepting_states`. A single transition
is `SftTransition<A, B> { from, to, guard: A::Predicate, output: OutputFunction<A, B> }`.
The output function is a *closed enum* rather than a bare closure so that it can be
`Clone`, `Debug`, and — crucially — *inspected* by the analyses:

```rust
pub enum OutputFunction<A: BooleanAlgebra, B: BooleanAlgebra> {
    Epsilon,                 // ε — produce nothing
    Constant(Vec<B::Domain>),// fixed output, ignores the input
    Identity,                // pass the consumed element through (Dᵢₙ ≈ Dₒᵤₜ)
    Map(Arc<dyn Fn(&A::Domain) -> B::Domain + Send + Sync>),      // one computed element
    FlatMap(Arc<dyn Fn(&A::Domain) -> Vec<B::Domain> + Send + Sync>), // many computed elements
}
```

`Epsilon`, `Constant`, and `Identity` cover the overwhelming majority of practical
edges with **no closure at all**, and are exactly the cases the static analyses can
reason about precisely; `Map`/`FlatMap` are the escape hatch for arbitrary
computed output, and are treated conservatively wherever a structural decision is
required.

## 2. Reading the transduction figure

![SFT transduction: input-predicate / output-term transitions](figures/04-sft-transduction.svg)

PlantUML source: [figures/04-sft-transduction.puml](figures/04-sft-transduction.puml).

The figure is a transducer state diagram. Each edge is labeled `φ / f` — the input
guard before the slash, the output function after it — using the suite's violet
`#EDE9FE` for the transducer. The illustration is the shipped `case_fold_sft`
factory: a single accepting state `q0` with two self-loops. The first edge
`[A‑Z] / Map(c ↦ c+32)` fires on an uppercase letter and emits its lowercase
counterpart; the second edge `¬[A‑Z] / Identity` fires on every other character
and passes it through unchanged. Because the two guards are complementary (their
conjunction is unsatisfiable), exactly one edge fires per input element — the
diagram is *visibly functional*, which is the property §7 decides mechanically.
The key reading is that an SFT edge carries **two** annotations where an SFA edge
carries one: the guard decides *whether* the edge fires, the output function
decides *what is emitted* when it does.

## 3. The `transduce` algorithm

Transduction is an NFA-style frontier simulation. The configuration is a set of
`(state, output-so-far)` pairs; each input element advances every pair along every
enabled edge, extending the accumulated output by that edge's emission. At
end-of-input the outputs of the pairs sitting in accepting states are collected.

> **Algorithm `Transduce` — run an SFT over an input word.**
> *Input:* an SFT `T = (Q, 𝓐ᵢₙ, 𝓐ₒᵤₜ, Δ, I, F)` and a word `w = e₁ … eₙ`.
> *Output:* the set of output words over all accepting paths.
>
> ```text
> Transduce(T, w):
>   if I = ∅: return ∅                       ▷ no start state ⇒ empty relation
>   frontier ← { (q, ε) | q ∈ I }            ▷ each start state, empty output
>   for e in w:                              ▷ consume one input element
>     next ← ∅
>     for (q, acc) in frontier:
>       for (q --[φ / f]--> q′) in Δ with q = from:
>         if 𝓐ᵢₙ.evaluate(φ, e):             ▷ guard fires on this element
>           next ← next ∪ { (q′, acc · f(e)) }   ▷ extend the accumulated output
>     frontier ← next
>   return { acc | (q, acc) ∈ frontier, q ∈ F }  ▷ outputs in accepting states
> ```
>
> The Rust entry point is `SymbolicFiniteTransducer::transduce` (`sft.rs`). Its
> time complexity is `O(|w| · |Q| · |Δ|)`: each of the `|w|` steps re-scans the
> frontier (bounded by `|Q|` distinct states, though the accumulator multiplicity
> grows with nondeterminism) against every transition. A *functional* SFT keeps a
> single output per step, so the accumulator count stays at one and the simulation
> is linear in the word length (the mechanized bound `functional_output_bounded`
> in [`SftFunctionality.v`](#9-references) certifies `|out| ≤ |w|`).

`domain_sfa` projects an SFT onto an SFA over `𝓐ᵢₙ` by dropping every output
function and keeping only the guards; the resulting automaton accepts exactly the
inputs for which `T` produces at least one output (`is_empty` is then an emptiness
check on that projection). This is the operational meaning of "domain of the
transduction" and is the bridge to the recognition algorithms in
[03](03-symbolic-automata-sfa.md).

## 4. `OutputTerm`: a first-class, analyzable output algebra

`OutputFunction::Map`/`FlatMap` are opaque: an `Arc<dyn Fn>` is a black box that
can only be *applied*, never *inspected*. That is fine for `transduce`, but it
defeats *composition* — when two SFTs are chained, an opaque output cannot be
folded into the downstream guard analysis, so the conservative arm of `compose`
must wrap it in a fresh `FlatMap` (over-approximating the product, §5). The fix is
to make the structural output a **finite term** instead of a closure:

```rust
pub enum OutputTerm<A: BooleanAlgebra, B: BooleanAlgebra> {
    Eps,                                                  // ε — produce nothing
    Id,                                                   // pass the consumed element through
    Const(Vec<B::Domain>),                                // fixed output
    Concat(Box<OutputTerm<A, B>>, Box<OutputTerm<A, B>>), // emit both sub-terms in order
    // _Input — a never-constructed marker tying the output-only term to `A`.
}
```

Every node is inspectable, so composition over `OutputTerm`s is a *precise symbolic
operation* (`then`) that yields another `OutputTerm` — never a closure. `OutputTerm`
carries **two compatible algebraic structures**, both proven up to denotational
equivalence `oeq s t ≝ ∀x. ⟦s⟧(x) = ⟦t⟧(x)` in
`formal/rocq/sft/theories/OutputTermAlgebra.v`. Write `⟦t⟧` for the denotation
`OutputTerm::apply : Dᵢₙ → Dₒᵤₜ*` and `⟦t⟧*` for its sequence lift
`OutputTerm::apply_all` (the per-element `flat_map`).

**(a) A monoid `(Concat, Eps)` — output concatenation.** Concatenation is
associative with the empty output `Eps` as a two-sided unit:

| Law | Statement | Coq theorem |
|---|---|---|
| associativity | `Concat(Concat(a, b), c) ≈ Concat(a, Concat(b, c))` | `oconcat_assoc` |
| left unit | `Concat(Eps, a) ≈ a` | `oconcat_eps_l` |
| right unit | `Concat(a, Eps) ≈ a` | `oconcat_eps_r` |

The smart constructor `OutputTerm::concat` performs the unit normalization
directly — `(Eps, t)` and `(t, Eps)` collapse to `t` — so monoid identities never
accumulate in a built term.

**(b) A category `(then, Id)` — sequential composition.** `self.then(next)`
composes `self : A→B*` with `next : B→C*` into a term `A→C*`. Its defining law is
the β / compose-correctness equation: composing then applying equals applying then
re-applying.

| Law | Statement | Coq theorem |
|---|---|---|
| β (compose-correctness) | `⟦self.then(next)⟧(i) = ⟦next⟧*(⟦self⟧(i))` | `othen_correct` |
| left unit (η) | `Id.then(t) ≈ t` | `othen_id_l` |
| right unit (η) | `t.then(Id) ≈ t` | `othen_id_r` |
| associativity | `(s.then(t)).then(u) ≈ s.then(t.then(u))` | `othen_assoc` |
| absorbing `Eps` | `Eps.then(t) ≈ Eps` | `othen_eps_l` |

`then` is *structural*, not closure-building: `Eps.then(_) = Eps`,
`Const(v).then(next) = Const(⟦next⟧*(v))` (the constant is pushed through eagerly),
`Id.then(next) = next` (re-typed to the new input algebra by `retype_input`, sound
because every generator either ignores the input or is a pure structural marker),
and `Concat(x, y).then(next) = Concat(x.then(next), y.then(next))` (composition
distributes over the monoid product). The result is always a concrete
`OutputTerm`, which is the whole point: **the term stays the source of truth for
static analysis even after composition.**

`From<OutputTerm<A, B>> for OutputFunction<A, B>` lowers an analyzable term to the
runtime function when an SFT must actually *run*: `Eps`/`Id`/a single `Const` map
to their direct `OutputFunction` counterparts, and a richer `Concat` lowers to a
`FlatMap` that evaluates the term. The lowering is one-directional on purpose —
analysis and composition happen on the term; only execution drops to the closure.

> **Why a term, not a closure.** The opaque `Map`/`FlatMap` arm of `compose`
> cannot statically tell which downstream guards a computed output can satisfy, so
> it connects to *every* satisfiable successor and re-wraps the output as a fresh
> `FlatMap` — a sound but lossy over-approximation. Replacing the structural cases
> with `OutputTerm` makes their composition *exact*: `othen_correct` guarantees the
> composed term denotes precisely the function-composition of the two stages, with
> no spurious product edges and no nested closures. `Concat` is the genuinely new
> expressive power beyond `Epsilon`/`Constant`/`Identity`.

## 5. Composition

Composition chains two transducers: `self : A → B*` followed by `other : B → C*`
yields `self ∘ other : A → C*`, computed by a product construction over the two
state spaces ([D'Antoni & Veanes, 2017](references.md#dantoni-veanes-2017), §4).

> **Algorithm `Compose` — chain two SFTs.**
> *Input:* `T₁ = (Q₁, A, B, Δ₁, I₁, F₁)` and `T₂ = (Q₂, B, C, Δ₂, I₂, F₂)`.
> *Output:* `T = (Q₁ × Q₂, A, C, Δ, I₁ × I₂, F₁ × F₂)`.
>
> ```text
> Compose(T₁, T₂):
>   create product start states I₁ × I₂; mark (q₁, q₂) accepting iff q₁∈F₁ ∧ q₂∈F₂
>   worklist ← I₁ × I₂
>   while (q₁, q₂) ← worklist.pop():
>     for t₁ = (q₁ --[φ₁ / f₁]--> q₁′) in Δ₁:
>       match f₁:
>         Epsilon   → add (q₁,q₂) --[φ₁ / Epsilon]--> (q₁′, q₂)     ▷ advance T₁ only
>         Constant(v) → feed v through T₂ from q₂ (fixed-length run);
>                        if feasible, add edge to (q₁′, q₂_after) emitting the
>                        accumulated C-output
>         Identity  → for each t₂ = (q₂ --[φ₂/f₂]--> q₂′) with φ₁ satisfiable:
>                        add (q₁,q₂) --[φ₁ / (input ↦ f₂(input))]--> (q₁′, q₂′)
>         Map | FlatMap → for each satisfiable t₂ from q₂:           ▷ conservative
>                        add (q₁,q₂) --[φ₁ / compose(f₁, f₂)]--> (q₁′, q₂′)
>   return the accumulated product transducer
> ```
>
> The Rust entry point is `SymbolicFiniteTransducer::compose::<C>` (`sft.rs`); the
> structural arms (`Epsilon`, `Constant`, `Identity`) are exact, while the
> computed-output arm is the conservative over-approximation that `OutputTerm::then`
> (§4) replaces with a precise term wherever the output is structural.
> `compose_chain` folds a slice of same-algebra SFTs into one pipeline by repeated
> `compose`, and `restrict_domain` intersects an SFT's domain with an input SFA
> (product with the guards, outputs retained) so that only inputs in the SFA's
> language are transduced.

![SFT composition pipeline](figures/04-sft-composition.svg)

PlantUML source: [figures/04-sft-composition.puml](figures/04-sft-composition.puml).

The composition figure is a left-to-right pipeline: an input word over `A` enters
`T₁` (violet), whose intermediate `B*` output streams into `T₂` (violet), whose
`C*` output exits — with the product `T₁ ∘ T₂` drawn beneath as the single
transducer the construction yields. It makes the type discipline visible: the
output algebra of the first stage *is* the input algebra of the second
(`A → B*` then `B → C*`), which is exactly why composability requires the middle
algebra `B` to match.

**Composition is a monoid.** Modeling each SFT abstractly as a list-lifted
per-element function `f : A → list B` (the `flat_map` lift to words), composition
`sft_compose f g ≝ λa. flat_map g (f a)` forms a monoid under the identity
transducer. The laws are proven in `formal/rocq/sft/theories/SftComposition.v`:

| Law | Statement | Coq theorem |
|---|---|---|
| left identity | `id ∘ T ≈ T` | `sft_compose_left_identity` |
| right identity | `T ∘ id ≈ T` | `sft_compose_right_identity` |
| associativity | `(T₁ ∘ T₂) ∘ T₃ ≈ T₁ ∘ (T₂ ∘ T₃)` | `sft_compose_assoc` |

The same three `flat_map` lemmas (`flat_map_app`, `flat_map_singleton`,
`flat_map_flat_map`) that close these also close the `OutputTerm` category laws in
`OutputTermAlgebra.v` — the output-term algebra and the transducer-composition
monoid rest on **one shared foundation**, so `then` (§4) and `compose` agree by
construction.

## 6. Pre-image and post-image

The two image operators turn a transducer plus an automaton on *one* side into an
automaton on the *other* side — the analytic core of static reasoning about a
transformation.

- **Pre-image** `pre_image(Aᵦ)`: given an SFA `Aᵦ` over the *output* algebra `B`,
  produce an SFA over the *input* algebra `A` accepting exactly those inputs whose
  transduction lands in `L(Aᵦ)`. Construction: the product of the SFT with `Aᵦ`,
  simulating `Aᵦ` forward over each edge's output (for `Epsilon` the acceptor state
  is unchanged; for `Constant` it is advanced by running `Aᵦ` on the constant word;
  for `Identity` the acceptor's `B`-guard is converted to an `A`-guard and
  intersected with the SFT guard; computed outputs connect conservatively). Its use:
  **answering "which inputs produce an output with property P?"** by setting
  `Aᵦ = ` the SFA for `P` and reading off the resulting input SFA — *without ever
  enumerating inputs*. The Rust entry point is `SymbolicFiniteTransducer::pre_image`.

- **Post-image** `post_image(Aₐ)`: given an SFA `Aₐ` over the *input* algebra `A`,
  produce an SFA over the *output* algebra `B` accepting exactly the outputs
  reachable from inputs in `L(Aₐ)`. Construction: the product `Aₐ × T` over
  compatible input guards (`φ_Aₐ ∧ φ_T` satisfiable), projecting each SFT edge's
  output to an output-side guard (exact for `Epsilon`; conservative `⊤` for
  `Identity`/`Constant`/computed). Its use: **bounding the reachable output
  language** of a transformation — what an encoder, normalizer, or rewriter can
  possibly emit.

Together they make a transformation *analyzable in both directions*: pre-image
pulls an output property back to an input property; post-image pushes an input
language forward to an output language. Both are pure SFA constructions, so every
downstream operation in [03](03-symbolic-automata-sfa.md) — emptiness,
intersection, equivalence — applies to the result unchanged.

## 7. Functionality (single-valuedness)

An SFT is **functional** when it is single-valued: every input word has at most
one output word. Functionality is what lets a transducer stand in for a *function*
(a normalizer, an encoder) rather than a one-to-many *relation*, and it is the
precondition for deciding equivalence.

`SymbolicFiniteTransducer::is_functional` (`sft.rs`) decides it by a structural
self-product check: for every pair of transitions leaving a common state, if their
guards overlap (`𝓐ᵢₙ.is_satisfiable(φᵢ ∧ φⱼ)`), then they must agree — same target
and structurally identical output (`output_structurally_equal`, which compares
`Epsilon`/`Identity`/`Const` precisely and conservatively treats `Map`/`FlatMap` as
unequal). Any overlapping-but-disagreeing pair witnesses nondeterminism and returns
`false`. Building on it:

- `is_equivalent_functional` decides `T₁ ≡ T₂` for functional `T₁`, `T₂`: it
  returns `Err(SftError::NotFunctional)` if either is nondeterministic, then checks
  domain equality (`domain_sfa().is_equivalent`) and a DFS over the reachable
  state-pairs confirming the outputs agree on every overlapping guard.
- `is_total` checks the domain SFA is universal (its complement is empty); `is_injective`
  is a conservative distinctness check on constant outputs.

The mechanized model (`formal/rocq/sft/theories/SftFunctionality.v`) abstracts an
SFT as `f : A → list B` and defines `functional f ≝ ∀a. length (f a) ≤ 1` — the
per-element bound that forces per-word single-valuedness:

| Property | Statement | Coq theorem |
|---|---|---|
| identity is functional | `functional sft_identity` | `identity_functional` |
| constant is functional | `∀c. functional (sft_constant c)` | `constant_functional` |
| **composition preserves it** | `functional f → functional g → functional (f ∘ g)` | `compose_preserves_functional` |
| decidability hook | `functional f ↔ ∀a. length (f a) ≤ 1` | `functional_iff_all_le1` |
| domain characterization | `in_domain f w ↔ ∃a ∈ w. f a ≠ []` | `domain_characterization` |
| output bound | `functional f → length (transduce f w) ≤ length w` | `functional_output_bounded` |

`compose_preserves_functional` is the load-bearing result: it certifies that
chaining single-valued transducers (the `compose`/`then` of §4–§5) never
introduces ambiguity, so a pipeline of functions is itself a function. The single
step is `flat_map_functional_le1` — feeding a `≤ 1`-length intermediate through a
functional second stage stays `≤ 1`.

## 8. Symbolic tree transducers (STFT)

The word transducer reads a sequence; the **symbolic tree transducer** reads a
*ranked tree* and rebuilds it bottom-up. Its realization is
`prattail/src/sym_tree_transducer.rs::SymbolicTreeTransducer<A, B>`. Where an SFT
edge matches one input element, an STFT *rule* matches a node — its constructor,
its payload (against an input guard), and the states its already-transduced
children occupy — and an **output builder** assembles the output node:

```rust
pub struct TransducerRule<A: BooleanAlgebra, B: BooleanAlgebra> {
    pub constructor: String,                 // input head constructor
    pub payload_guard: Option<A::Predicate>, // input payload guard (None ⇒ structural node)
    pub child_states: Vec<usize>,            // required state of each input child
    pub target: usize,                       // resulting state
    pub output: OutputBuilder<A, B>,         // how to build the output node
}

pub enum OutputBuilder<A: BooleanAlgebra, B: BooleanAlgebra> {
    Build { constructor: String, payload: PayloadOut<A, B>, children: Vec<usize> },
    Project(usize),  // emit the i-th transduced child directly (delete this node)
}

pub enum PayloadOut<A: BooleanAlgebra, B: BooleanAlgebra> {
    Structural,                                          // output node has no payload
    Const(B::Domain),                                    // fixed output payload
    Map(Arc<dyn Fn(&A::Domain) -> B::Domain + Send + Sync>), // payload computed from input payload
}
```

`transduce` runs bottom-up (`run_outputs`): it recursively computes, for each
child, the set of output terms producible in each state; for every rule whose
constructor, child-state vector, and payload guard match the node, it forms the
cartesian product of one chosen output per child (`cartesian_terms`, hence the
*set* of outputs under nondeterminism) and applies the builder. `Build` reorders
and selects children by index (`children: Vec<usize>` is a permutation/selection
into the input's children) and sets the payload from `Structural`/`Const`/`Map`;
`Project(i)` emits a child directly, deleting the current node. The accepting
(root) states' outputs are the transduction. `domain_sta` drops the builders to
recover the underlying symbolic tree automaton; `is_total` complements that domain
and checks emptiness. Sequential composition of two transductions is
`compose_transduce(t1, t2, input) = t1.transduce(input).flat_map(|mid| t2.transduce(mid))`
— transduce with the first, then each intermediate with the second.

These rules realize **structural rewriting / pattern-output over ranked trees**:
a `Build` that reuses the input shape and selects children in order is exactly a
bottom-up *relabeling homomorphism* (rename each head, keep the structure), and a
`Project` is node deletion — the building blocks of a tree-to-tree transformation.

**Two algebraic layers, both zero-admission.** `StftComposition.v` and
`StftFunctionality.v` model ranked trees `Tree X ≝ tnode : X → list (Tree X) → Tree X`
with a hand-rolled strong induction principle `tree_ind'` (a plain `Fixpoint`,
hence axiom-free, because Coq's generated principle is too weak through the
`list (Tree X)` nesting). They establish:

*(a) the deterministic relabeling homomorphism* `thom g` (rebuild every node,
relabel the head by `g`):

| Property | Statement | Coq theorem |
|---|---|---|
| identity relabel | `thom (λa.a) t = t` | `thom_id` |
| forest fusion | `thom g₂ (thom g₁ t) = thom (λa. g₂ (g₁ a)) t` | `thom_fusion` |
| associativity | `thom g₃ (thom g₂ (thom g₁ t)) = thom (λa. g₃ (g₂ (g₁ a))) t` | `thom_compose_assoc` |
| node-count preserved | `tcount (thom g t) = tcount t` | `tcount_thom` / `thom_preserves_tcount` |

*(b) the forest transducer monoid* `ft` modeling the full nondeterministic
transduction `f : Tree A → list (Tree B)`, with `ft_compose f g ≝ λt. flat_map g (f t)`
and unit `ft_identity t ≝ [t]`:

| Property | Statement | Coq theorem |
|---|---|---|
| left identity | `id ; g ≈ g` | `ft_compose_left_identity` |
| right identity | `f ; id ≈ f` | `ft_compose_right_identity` |
| **associativity** | `(f ; g) ; h ≈ f ; (g ; h)` | `ft_compose_assoc` |
| composition preserves functionality | `functional f → functional g → functional (f ; g)` | `compose_preserves_functional` (STFT) |
| relabel is single-valued | `functional (λt. [thom g t])` | `thom_singleton_functional` |
| domain characterization | `in_domain (f ; g) t ↔ ∃s ∈ f(t). g(s) ≠ []` | `domain_characterization` (STFT) |

The bridge corollary `ft_compose_thom_singleton` shows the deterministic relabels
form a *sub-monoid* of the forest transducer monoid whose composition is precisely
homomorphism fusion — so the structural-rewrite layer and the general transduction
layer are one algebra. Layer (b) reuses the **same** `flat_map` lemmas as the word
proofs in `SftComposition.v`, so word and tree transducers share their composition
foundation; `tcount` (node count) plays the role the word `length` plays in
`SftFunctionality.v` (e.g. `thom_preserves_tcount` is the tree analog of
`identity_preserves_length`).

## 9. Where SFTs sit in the integration

The substrate's job ends at the compile-time boundary: it classifies a guard and
emits *evidence + quality*, never an automaton or transducer into generated
Rholang (the classify-only boundary, [01](01-concepts-and-glossary.md)). An SFT is
the disposition the substrate records when a guard obligation is best discharged by
a *symbolic transduction* — the `RhoGuardDispositionKind::SymbolicFiniteTransducer`
case classified in the language-to-Rholang flow. Concretely, the input-normalizing
and encoder/decoder transformations (`case_fold_sft`, `whitespace_normalize_sft`,
and grammar-derived structural rewrites) are the family of guards whose coverage is
witnessed by an SFT/STFT: functionality (§7) is the evidence that the
transformation is a well-defined function, and pre-/post-image (§6) bound what it
reads and writes. How that disposition is collected, quality-graded, and gated into
a fail-closed flip decision is the subject of
[07 — Language-to-Rholang Integration](07-language-to-rholang-integration.md); the
run-time enforcement of the *surviving* predicate (never the SFT itself) is
[08 — Runtime COMM Enforcement](08-runtime-comm-enforcement.md).

## 10. References

Primary sources for the symbolic-transducer theory (full bibliographic detail and
the local Rocq/Rust anchors in [References](references.md)):

- Veanes, M., Hooimeijer, P., Livshits, B., Molnar, D., Björner, N. (2012).
  *Symbolic Finite State Transducers: Algorithms and Applications.* POPL 2012,
  137–150. DOI [10.1145/2103656.2103674](https://doi.org/10.1145/2103656.2103674).
  The foundational SFT model — predicate-guarded edges with output functions,
  composition, and functionality — that `sft.rs` realizes
  ([references.md#veanes-popl-2012](references.md#veanes-popl-2012)).
- D'Antoni, L., Veanes, M. (2013). *Static Analysis of String Encoders and
  Decoders.* VMCAI 2013, LNCS 7737, 209–228.
  DOI [10.1007/978-3-642-35873-9_14](https://doi.org/10.1007/978-3-642-35873-9_14).
  The pre-image/post-image static-analysis use of SFTs over encoders and decoders
  ([references.md#dantoni-veanes-2013](references.md#dantoni-veanes-2013)).
- D'Antoni, L., Veanes, M. (2017). *The Power of Symbolic Automata and Transducers
  (Invited Tutorial).* CAV 2017, LNCS 10426, 47–67.
  DOI [10.1007/978-3-319-63387-9_3](https://doi.org/10.1007/978-3-319-63387-9_3).
  The survey covering composition algorithms and **symbolic tree transducers**
  ([references.md#dantoni-veanes-2017](references.md#dantoni-veanes-2017)).
- Comon, H., Dauchet, M., Gilleron, R., Jacquemard, F., Lugiez, D., Tison, S.,
  Tommasi, M. *Tree Automata Techniques and Applications (TATA)*, Ch. 6 (tree
  transducers, homomorphisms, composition) — the classical tree-transducer
  background for §8 ([references.md#tata](references.md#tata)).

Local zero-admission Coq theories (`formal/rocq/sft/theories/`), each closing with
a `Print Assumptions` audit and built by
`make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-sft`:

- `OutputTermAlgebra.v` — `OutputTerm` is a monoid (`oconcat_assoc`,
  `oconcat_eps_l`, `oconcat_eps_r`) and a category (`othen_correct` the β-law,
  `othen_id_l`, `othen_id_r`, `othen_assoc`).
- `SftComposition.v` — the composition monoid (`sft_compose_left_identity`,
  `sft_compose_right_identity`, `sft_compose_assoc`).
- `SftFunctionality.v` — `compose_preserves_functional`, `functional_iff_all_le1`,
  `domain_characterization`, `functional_output_bounded`.
- `StftComposition.v` — the tree layer (`thom_id`, `thom_fusion`,
  `thom_compose_assoc`, `tcount_thom`, `ft_compose_assoc`).
- `StftFunctionality.v` — the tree single-valuedness layer
  (`compose_preserves_functional`, `thom_preserves_tcount`,
  `thom_singleton_functional`, `domain_characterization`).

The Rust substrate lives in `prattail/src/sft.rs` (word transducer + `OutputTerm`)
and `prattail/src/sym_tree_transducer.rs` (tree transducer). Continue to
[05 — Algebra Pyramid and Decidability](05-algebra-pyramid-and-decidability.md) for
the tower the input/output algebras live in, or to
[References](references.md) for the complete bibliography.
