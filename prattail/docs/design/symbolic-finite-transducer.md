# Symbolic Finite Transducers -- Output-Producing Transductions over Infinite Domains

## Quick Start

Symbolic Finite Transducers (SFTs) extend Symbolic Finite Automata (SFAs) with
output functions: where SFAs accept or reject inputs, SFTs transform inputs to
outputs.  Each transition is guarded by a predicate from an effective Boolean
algebra and annotated with an output function that maps the consumed input
element to a sequence of output elements.

```rust
use prattail::symbolic::{IntervalAlgebra, IntervalPred};
use prattail::sft::{SymbolicFiniteTransducer, OutputFunction};
use std::sync::Arc;

let alg = IntervalAlgebra::new(0, 100);
let mut sft = SymbolicFiniteTransducer::new(alg.clone(), alg);

// Single self-loop state accepting all inputs.
let q0 = sft.add_state(true, Some("q0".to_string()));
sft.set_initial(q0);

// Double every input in [0, 100).
sft.add_transition(
    q0,
    q0,
    IntervalPred::True,
    OutputFunction::Map(Arc::new(|x: &i64| x * 2)),
);

let results = sft.transduce(&[3, 5, 7]);
assert_eq!(results.len(), 1);
assert_eq!(results[0], vec![6, 10, 14]);
```

The module provides the core `SymbolicFiniteTransducer<A, B>` type (parameterized
over input algebra `A` and output algebra `B`), five `OutputFunction` variants,
composition, pre-image, post-image, functionality/totality/injectivity checks,
four factory functions, and a pipeline analysis bridge.

## SFA vs SFT

Symbolic Finite Automata (SFAs) and Symbolic Finite Transducers (SFTs) share the
same predicate-guarded transition framework, but serve fundamentally different
purposes.

| Aspect          | SFA                              | SFT                                         |
|-----------------|----------------------------------|----------------------------------------------|
| Purpose         | Accept / reject                  | Transform input to output                    |
| Transition      | `(q, guard, q')`                 | `(q, guard, output_fn, q')`                  |
| Algebras        | One algebra `A`                  | Two algebras `A` (input) and `B` (output)    |
| Result          | `bool`                           | `Vec<Vec<B::Domain>>`                        |
| Closure         | Union, intersection, complement  | Composition, pre-image, post-image           |
| Equivalence     | Decidable (symmetric difference) | Decidable for functional SFTs                |
| Key operation   | `accepts(word) -> bool`          | `transduce(word) -> Vec<Vec<B::Domain>>`     |

An SFA is a degenerate SFT where every transition has `OutputFunction::Epsilon`
and the only question is reachability of an accepting state.  The `domain_sfa()`
method on any SFT extracts exactly this underlying SFA.

```
SFA:  q0 ──[x in [0,100)]──> q1 (accept)
      Answer: is the word accepted?

SFT:  q0 ──[x in [0,100), out: x*2]──> q1 (accept)
      Answer: what output does the word produce?
```

## Formal Definitions

The following definitions follow D'Antoni & Veanes (POPL 2012).

**Definition 1 (Effective Boolean Algebra).** An effective Boolean algebra is a
tuple `(D, Psi, bot, top, and, or, not, SAT, WIT, EVAL)` where `D` is the
(possibly infinite) domain, `Psi` is a decidable set of predicates over `D`,
`bot` and `top` are the falsity and truth predicates, `and`, `or`, `not` are
Boolean connectives, `SAT: Psi -> {true, false}` decides satisfiability,
`WIT: Psi -> D union {bot}` generates a witness, and `EVAL: Psi x D -> {true, false}`
evaluates a predicate on a concrete element.

**Definition 2 (Symbolic Finite Transducer).** An SFT over input algebra `A`
and output algebra `B` is a tuple `T = (Q, A, B, delta, q_0, F)` where:
- `Q` is a finite set of states
- `A = (D_A, Psi_A, ...)` is the input Boolean algebra
- `B = (D_B, Psi_B, ...)` is the output Boolean algebra
- `delta subset Q x Psi_A x (D_A -> D_B*) x Q` is the guarded output transition relation
- `q_0 subset Q` is the set of initial states
- `F subset Q` is the set of accepting (final) states

A transition `(q, phi, f, q')` fires when the current input element `d`
satisfies `EVAL(phi, d) = true`, producing output sequence `f(d)` and moving
to state `q'`.

**Definition 3 (Transduction).** Given input word `w = d_1 d_2 ... d_n in D_A*`,
the transduction `T(w)` is the set of all output words `o_1 o_2 ... o_m` such
that there exists a run `q_0 --[phi_1, f_1]--> q_1 --[phi_2, f_2]--> ... --[phi_n, f_n]--> q_n`
with `q_0 in q_0`, `q_n in F`, `EVAL(phi_i, d_i) = true` for all `i`, and the
output is the concatenation `f_1(d_1) . f_2(d_2) . ... . f_n(d_n)`.

**Definition 4 (Functionality).** An SFT is functional (single-valued) if
`|T(w)| <= 1` for every `w in D_A*`.  Equivalently, for every reachable state,
no two outgoing transitions with overlapping guards lead to states that can
produce different output suffixes.

**Definition 5 (Totality).** An SFT is total if `|T(w)| >= 1` for every
`w in D_A*`.  Equivalently, the domain SFA is universal (accepts all words).

## Architecture Diagram

```
┌──────────────────────────────────────────────────────────────────────────┐
│                          PraTTaIL Pipeline                               │
│                                                                          │
│  language! { ... }                                                       │
│       │                                                                  │
│       ▼                                                                  │
│  Grammar Rules ──▶ WFST + Decision Tree (finite dispatch)               │
│       │                                                                  │
│       │    ┌────────────────────────────────────────────────────────┐    │
│       └───▶│         Symbolic Modules (symbolic.rs + sft.rs)        │    │
│            │                                                        │    │
│            │  BooleanAlgebra (trait)                                 │    │
│            │    ├── IntervalAlgebra       (numeric ranges, i64)      │    │
│            │    ├── CharClassAlgebra      (Unicode chars)            │    │
│            │    └── KatBooleanAlgebra     (propositional tests)      │    │
│            │           │                                            │    │
│            │           │  extends                                   │    │
│            │           ▼                                            │    │
│            │  ┌──────────────────────────────────────┐              │    │
│            │  │  SymbolicAutomaton<A>     (SFA)       │              │    │
│            │  │    ├── accepts()                      │              │    │
│            │  │    ├── is_empty()                     │              │    │
│            │  │    ├── intersect()                    │              │    │
│            │  │    ├── complement()                   │              │    │
│            │  │    ├── determinize()                  │              │    │
│            │  │    └── is_equivalent()                │              │    │
│            │  └──────────────────────────────────────┘              │    │
│            │           │                                            │    │
│            │           │  extends (adds output functions)           │    │
│            │           ▼                                            │    │
│            │  ┌──────────────────────────────────────┐              │    │
│            │  │  SymbolicFiniteTransducer<A,B>  (SFT) │              │    │
│            │  │    ├── transduce()                    │              │    │
│            │  │    ├── compose()                      │              │    │
│            │  │    ├── pre_image()                    │              │    │
│            │  │    ├── post_image()                   │              │    │
│            │  │    ├── restrict_domain()              │              │    │
│            │  │    ├── domain_sfa()                   │              │    │
│            │  │    ├── is_functional()                │              │    │
│            │  │    ├── is_equivalent_functional()     │              │    │
│            │  │    ├── is_total()                     │              │    │
│            │  │    ├── is_injective()                 │              │    │
│            │  │    └── is_empty()                     │              │    │
│            │  └──────────────────────────────────────┘              │    │
│            │                                                        │    │
│            │  OutputFunction<A,B>                                   │    │
│            │    ├── Epsilon                                         │    │
│            │    ├── Constant(Vec<B::Domain>)                        │    │
│            │    ├── Identity                                        │    │
│            │    ├── Map(Arc<dyn Fn>)                                │    │
│            │    └── FlatMap(Arc<dyn Fn>)                            │    │
│            │                                                        │    │
│            │  Factory functions                                     │    │
│            │    ├── case_fold_sft()                                 │    │
│            │    ├── whitespace_normalize_sft()                      │    │
│            │    ├── guard_transform_sft()                           │    │
│            │    └── compose_chain()                                 │    │
│            │                                                        │    │
│            │  SftAnalysis ──▶ MathAnalysisResults                   │    │
│            └────────────────────────────────────────────────────────┘    │
│                                                                          │
│  Pipeline Integration                                                    │
│    ├── MathAnalysisResults.sft_result     (analysis data)                │
│    ├── LintContext.sft_result             (lint wiring)                  │
│    ├── Optimization::SftAnalysis          (cost-benefit gate)            │
│    └── ModuleId::Sft (M15)               (predicate dispatch)           │
└──────────────────────────────────────────────────────────────────────────┘
```

## API Reference

### Core Types

#### `OutputFunction<A: BooleanAlgebra, B: BooleanAlgebra>`

Closed enum representing the output function on a transition.  Using an enum
rather than a trait object enables `Clone`, `Debug`, and compile-time composition
without dynamic dispatch.  `Identity`, `Constant`, and `Epsilon` cover over 90%
of practical cases without requiring closures.

| Variant              | Semantics                      | Output for input `d`        |
|----------------------|--------------------------------|-----------------------------|
| `Epsilon`            | Produce nothing                | `[]`                        |
| `Constant(Vec<B>)`   | Ignore input, emit fixed seq   | `[c_1, c_2, ...]`          |
| `Identity`           | Pass through unchanged         | `[d]` (via `Into<B>`)       |
| `Map(Arc<dyn Fn>)`   | Single-element computed output | `[f(d)]`                    |
| `FlatMap(Arc<dyn Fn>)`| Multi-element computed output | `f(d)` (returns `Vec`)      |

Methods:
- `apply(&self, input: &A::Domain) -> Vec<B::Domain>` -- apply to one element
- `apply_all(&self, inputs: &[A::Domain]) -> Vec<B::Domain>` -- apply to a sequence, concatenating
- `is_epsilon() -> bool`, `is_constant() -> bool`, `is_identity() -> bool` -- variant queries

#### `SftTransition<A: BooleanAlgebra, B: BooleanAlgebra>`

A single transition in the transducer.

| Field    | Type                  | Description                                |
|----------|-----------------------|--------------------------------------------|
| `from`   | `usize`               | Source state ID                            |
| `to`     | `usize`               | Target state ID                            |
| `guard`  | `A::Predicate`        | Guard predicate over the input algebra     |
| `output` | `OutputFunction<A,B>` | Output function applied when guard fires   |

#### `SftState`

State representation, reusing the same structure as `SymbolicState` in the SFA module.

| Field          | Type             | Description                         |
|----------------|------------------|-------------------------------------|
| `id`           | `usize`          | Unique state identifier             |
| `is_accepting` | `bool`           | Whether this is a final state       |
| `label`        | `Option<String>` | Optional human-readable label       |

#### `SymbolicFiniteTransducer<A: BooleanAlgebra, B: BooleanAlgebra>`

The core SFT type.  Parameterized over input algebra `A` and output algebra `B`,
both implementing `BooleanAlgebra`.

| Field              | Type                         | Description                        |
|--------------------|------------------------------|------------------------------------|
| `input_algebra`    | `A`                          | Input Boolean algebra instance     |
| `output_algebra`   | `B`                          | Output Boolean algebra instance    |
| `states`           | `Vec<SftState>`              | All states                         |
| `transitions`      | `Vec<SftTransition<A, B>>`   | All transitions                    |
| `initial_states`   | `HashSet<usize>`             | Initial state IDs                  |
| `accepting_states` | `HashSet<usize>`             | Accepting state IDs                |

#### `SftError`

Error type for operations that may fail.

| Variant           | Meaning                                                 |
|-------------------|---------------------------------------------------------|
| `NotFunctional`   | Operation requires a functional SFT but input is not    |
| `AlgebraMismatch` | Input/output algebras of two SFTs are incompatible      |

#### `SftAnalysis`

Pipeline analysis result, produced by `analyze_from_bundle()`.

| Field                   | Type                     | Description                          |
|-------------------------|--------------------------|--------------------------------------|
| `num_transducers`       | `usize`                  | Number of SFTs constructed           |
| `functional_count`      | `usize`                  | Number that are single-valued        |
| `total_count`           | `usize`                  | Number that accept all inputs        |
| `equivalent_pairs`      | `Vec<(String, String)>`  | Pairs of semantically equivalent SFTs|
| `empty_domain_labels`   | `Vec<String>`            | Labels of SFTs with empty domains    |
| `constant_output_labels`| `Vec<String>`            | Labels of SFTs with constant output  |

### Construction API

```rust
// Create an empty SFT with given input and output algebras.
fn new(input_algebra: A, output_algebra: B) -> Self;

// Add a state, returning its ID.  Accepting states are automatically
// registered in the accepting_states set.
fn add_state(&mut self, is_accepting: bool, label: Option<String>) -> usize;

// Mark an existing state as initial.  Panics if state_id is out of range.
fn set_initial(&mut self, state_id: usize);

// Add a guarded transition with output function.
// Panics if from or to are out of range.
fn add_transition(
    &mut self,
    from: usize,
    to: usize,
    guard: A::Predicate,
    output: OutputFunction<A, B>,
);

// Accessors.
fn num_states(&self) -> usize;
fn num_transitions(&self) -> usize;
```

### Transduction

```rust
// NFA-style simulation: maintains (state, accumulated_output) frontier.
// Returns all possible output sequences reaching accepting states.
fn transduce(&self, word: &[A::Domain]) -> Vec<Vec<B::Domain>>
where
    A::Domain: Clone + Into<B::Domain>;
```

For each input element `d_i`, every frontier entry `(q, acc)` is expanded by
checking each transition `(q, phi, f, q')` with `EVAL(phi, d_i) = true`,
appending `f(d_i)` to `acc`, and advancing to `q'`.  After processing the
entire word, outputs from accepting states are collected.  If the SFT is
functional, the result contains at most one element.

### Analysis Operations

```rust
// Extract domain SFA: drop outputs, keep guards.
fn domain_sfa(&self) -> SymbolicAutomaton<A>;

// Empty domain check (delegates to domain_sfa().is_empty()).
fn is_empty(&self) -> bool;

// Functionality: each input produces at most one output.
// Checks all pairs of outgoing transitions from each state
// for overlapping guards with structurally different outputs.
fn is_functional(&self) -> bool;

// Equivalence for functional SFTs.
// Err(NotFunctional) if either SFT is nondeterministic.
fn is_equivalent_functional(&self, other: &Self) -> Result<bool, SftError>;

// Totality: domain SFA accepts all words.
fn is_total(&self) -> bool;

// Injectivity (conservative): different inputs -> different outputs.
fn is_injective(&self) -> bool;
```

### Composition and Image Operations

```rust
// Compose: self (A -> B) followed by other (B -> C) = (A -> C).
// Product construction over (Q1 x Q2) state space.
fn compose<C: BooleanAlgebra>(
    &self,
    other: &SymbolicFiniteTransducer<B, C>,
) -> SymbolicFiniteTransducer<A, C>
where
    A::Domain: Clone + Into<B::Domain>,
    B::Domain: Clone + Into<C::Domain>;

// Pre-image: given SFA over B, compute SFA over A accepting exactly
// those inputs whose transduction is accepted by the SFA.
fn pre_image(&self, acceptor: &SymbolicAutomaton<B>) -> SymbolicAutomaton<A>
where
    A::Domain: Clone + Into<B::Domain>;

// Post-image: given SFA over A, compute SFA over B accepting exactly
// the outputs produced from inputs in L(input_lang).
fn post_image(&self, input_lang: &SymbolicAutomaton<A>) -> SymbolicAutomaton<B>
where
    A::Domain: Clone + Into<B::Domain>;

// Restrict domain to intersection with given SFA.
fn restrict_domain(&self, input_lang: &SymbolicAutomaton<A>) -> Self
where
    A::Domain: Clone + Into<B::Domain>;
```

### Factory Functions

```rust
// Case-fold: A-Z -> a-z, all other characters pass through unchanged.
fn case_fold_sft() -> SymbolicFiniteTransducer<CharClassAlgebra, CharClassAlgebra>;

// Whitespace normalize: tab, CR, FF, VT -> ASCII space; others unchanged.
fn whitespace_normalize_sft() -> SymbolicFiniteTransducer<CharClassAlgebra, CharClassAlgebra>;

// Build SFT from guarded rules: each (guard, output) pair becomes a
// self-loop transition from the single state.  Disjoint guards yield
// a functional SFT; overlapping guards yield a nondeterministic one.
fn guard_transform_sft<A: BooleanAlgebra>(
    rules: &[(A::Predicate, OutputFunction<A, A>)],
    algebra: &A,
) -> SymbolicFiniteTransducer<A, A>;

// Compose a chain of same-algebra SFTs: T_1 ; T_2 ; ... ; T_n.
// Left-folds compose().  Panics if the chain is empty.
fn compose_chain<A: BooleanAlgebra>(
    chain: &[SymbolicFiniteTransducer<A, A>],
) -> SymbolicFiniteTransducer<A, A>
where
    A::Domain: Clone + Into<A::Domain> + Send + Sync + 'static;
```

## Algorithm Descriptions

### Composition (D'Antoni & Veanes, Section 4)

Given `T1: A -> B` and `T2: B -> C`, the composed SFT `T1 ; T2 : A -> C` is
constructed by a product-state BFS:

```
Input:  T1 = (Q1, A, B, delta1, I1, F1)
        T2 = (Q2, B, C, delta2, I2, F2)
Output: T  = (Q, A, C, delta, I, F) where L(T) = L(T1) ; L(T2)

1. I = I1 x I2
2. worklist <- I; state_map <- { (i1, i2) -> pid }
3. While worklist not empty:
   a. (q1, q2) <- pop(worklist)
   b. For each transition t1 = (q1, phi1, f1, q1') in delta1:
      Case f1:
        Epsilon:
          Add (pid, phi1, Epsilon, pid') where pid' = map(q1', q2)
        Constant(vals):
          Simulate vals through T2 from q2; if feasible at q2_final:
          Add (pid, phi1, Constant(composed_outputs), map(q1', q2_final))
        Identity:
          For each t2 = (q2, phi2, f2, q2') in delta2:
            If SAT(phi1) and SAT(phi2):
              Add (pid, phi1, f2, map(q1', q2'))
        Map/FlatMap:
          For each t2 = (q2, phi2, f2, q2') in delta2:
            If SAT(phi2):
              Add (pid, phi1, compose(f1, f2), map(q1', q2'))
4. F = { pid | (q1, q2) maps to pid, q1 in F1, q2 in F2 }
```

The output function composition `compose(f1, f2)` handles algebraic
simplifications: `epsilon ; f = epsilon`, `f ; epsilon = epsilon`,
`id ; id = id`, `const(c) ; id = const(c as C)`, and falls back to
`FlatMap` for general cases.

### Pre-Image

Given SFT `T: A -> B` and SFA `M` over `B`, the pre-image
`T^{-1}(L(M)) = { w in D_A* | T(w) intersect L(M) != emptyset }` is computed
by a product construction `T x M`:

```
1. Product states: (q_sft, q_sfa)
2. For each SFT transition (q_sft, phi, f, q_sft'):
   Case f:
     Epsilon:   SFA state unchanged; add (pid, phi, pid')
     Constant:  Simulate SFA on constant; advance SFA to final state
     Identity:  For each SFA transition from q_sfa, add (pid, phi, pid')
     Map/FlatMap: Conservative -- connect to all reachable SFA successors
3. Accepting: (q_sft, q_sfa) where q_sft in F_sft and q_sfa in F_sfa
```

### Post-Image

Given SFT `T: A -> B` and SFA `M` over `A`, the post-image
`T(L(M)) = { T(w) | w in L(M) }` is computed by a product construction `M x T`,
projecting to output:

```
1. Product states: (q_sfa, q_sft)
2. For each pair (t_sfa from q_sfa, t_sft from q_sft):
   combined_guard = t_sfa.guard AND t_sft.guard
   If SAT(combined_guard):
     Output guard = project SFT output (TRUE for computed, exact for constant)
     Add transition in result SFA over B
3. Accepting: both component states accepting
```

### Functionality Check

```
1. For each state q in Q:
   Collect all outgoing transitions T_q
2. For each pair (t_i, t_j) in T_q x T_q, i < j:
   If SAT(guard_i AND guard_j):
     If t_i.to != t_j.to OR outputs structurally differ:
       Return false
3. Return true
```

Structural output comparison covers `Epsilon == Epsilon`,
`Identity == Identity`, and `Constant(a) == Constant(b)` via debug
representation (since `B::Domain` does not require `Eq` in general).
`Map`/`FlatMap` closures are conservatively treated as always unequal.

## Complexity Analysis

| Operation                       | Time Complexity                          | Space                      |
|---------------------------------|------------------------------------------|----------------------------|
| `new()`                         | O(1)                                     | O(1)                       |
| `add_state()`                   | O(1) amortized                           | O(1)                       |
| `add_transition()`              | O(1) amortized                           | O(1)                       |
| `transduce(word)`               | O(\|w\| * \|Q\| * \|delta\|)             | O(\|Q\| * \|w\|)           |
| `domain_sfa()`                  | O(\|Q\| + \|delta\|)                     | O(\|Q\| + \|delta\|)       |
| `is_empty()`                    | O(\|Q\| + \|delta\| * SAT)              | O(\|Q\|)                   |
| `is_functional()`               | O(\|Q\| * \|delta\|^2 * SAT)            | O(\|delta\|)               |
| `is_total()`                    | O(2^\|Q\| * SAT)                         | O(2^\|Q\|)                 |
| `is_injective()`                | O(\|Q\| * \|delta\|^2 * SAT)            | O(\|delta\|)               |
| `is_equivalent_functional()`    | O(\|Q1\| * \|Q2\| * \|delta\|^2 * SAT)  | O(\|Q1\| * \|Q2\|)        |
| `compose(other)`                | O(\|Q1\| * \|Q2\| * \|delta1\| * \|delta2\|) | O(\|Q1\| * \|Q2\|)   |
| `pre_image(sfa)`                | O(\|Q_sft\| * \|Q_sfa\| * \|delta\|^2)  | O(\|Q_sft\| * \|Q_sfa\|)  |
| `post_image(sfa)`               | O(\|Q_sfa\| * \|Q_sft\| * \|delta\|^2 * SAT) | O(\|Q_sfa\| * \|Q_sft\|) |
| `restrict_domain(sfa)`          | O(\|Q_sfa\| * \|Q_sft\| * \|delta\|^2 * SAT) | O(\|Q_sfa\| * \|Q_sft\|) |
| `case_fold_sft()`               | O(1)                                     | O(1) (2 transitions)       |
| `whitespace_normalize_sft()`    | O(1)                                     | O(1) (2 transitions)       |
| `guard_transform_sft(rules)`    | O(\|rules\|)                             | O(\|rules\|)               |
| `compose_chain(sfts)`           | O(n * compose_cost)                      | O(product states)          |

`SAT` denotes the cost of a single satisfiability query on the Boolean algebra.
For `IntervalAlgebra` and `CharClassAlgebra`, `SAT` is O(k) where k is the
number of intervals.  For `KatBooleanAlgebra`, `SAT` is O(2^n) where n is the
number of propositional atoms.

## Compile-Time vs Runtime

All SFT operations in PraTTaIL execute during macro expansion
(`language! { ... }` invocation).  The pipeline constructs SFTs from grammar
data, analyzes them (functionality, emptiness, equivalence), emits lint
diagnostics, and discards the transducers.  No SFT data structures survive into
the compiled binary.

```
┌─────────────────────────────────────────────────────────────────┐
│                      Compile Time (proc-macro)                   │
│                                                                  │
│  language! { ... }                                               │
│       │                                                          │
│       ▼                                                          │
│  Pipeline::analyze()                                             │
│       │                                                          │
│       ├──▶ SFT construction from grammar rules                  │
│       ├──▶ is_functional(), is_total(), is_empty() checks        │
│       ├──▶ SftAnalysis populated                                 │
│       ├──▶ Lint SFT01-SFT04 emitted                             │
│       └──▶ SFTs dropped (zero runtime footprint)                │
│                                                                  │
│  Generated code: parse/eval functions (no SFT references)        │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│                      Runtime                                     │
│                                                                  │
│  Zero SFT overhead.  Generated parser operates directly on      │
│  token streams via Pratt parsing and recursive descent.          │
└─────────────────────────────────────────────────────────────────┘
```

## Pipeline Integration

### MathAnalysisResults

The `MathAnalysisResults` struct in `pipeline.rs` carries the `sft_result` field,
populated by a dedicated thread during the mathematical analysis phase:

```rust
#[cfg(feature = "sft")]
pub sft_result: Option<crate::sft::SftAnalysis>,
```

The analysis thread is spawned alongside other module threads
(WPDS, Buchi, VPA, etc.) and gated by predicate dispatch:

```rust
#[cfg(feature = "sft")]
let h_sft = s.spawn(|| {
    #[cfg(feature = "predicate-dispatch")]
    if !dispatch_plan.requires(crate::predicate_dispatch::ModuleId::Sft) {
        return None;
    }
    Some(crate::sft::analyze_from_bundle(all_syntax, categories))
});
```

### LintContext Wiring

`LintContext` carries `sft_result: Option<&'a SftAnalysis>`, populated from
`MathAnalysisResults` when constructing the lint context in the pipeline's
diagnostic phase.  The four SFT lint functions read from this field.

### Cost-Benefit Gate

`Optimization::SftAnalysis` is registered in the cost-benefit framework with
status `OptimizationStatus::Diagnostic` (analysis-only, no code transformation).
The gate identifier is `"SFT01"`.  When the cost-benefit analysis determines
the gate is not worthwhile (grammar too small, no transduction patterns), the
SFT analysis thread is skipped entirely.

### Predicate Dispatch

Module `M15` (`ModuleId::Sft`) in the predicate dispatch automaton classifies
grammar predicates that require SFT analysis.  The dispatch signature bit is
`ModuleSig::M15_SFT = 1 << 14`.  When no grammar predicate activates M15, the
SFT analysis thread returns `None` immediately, avoiding unnecessary work.

The dispatch pipeline feature name mapping is `Sft -> "sft"`, which corresponds
to the Cargo feature gate.

## Lint Diagnostics

Four lint rules target SFT analysis results.  All are gated behind `#[cfg(feature = "sft")]`.

| Code   | Name                          | Severity | Trigger                                        |
|--------|-------------------------------|----------|------------------------------------------------|
| SFT01  | `empty-domain-transduction`   | Warning  | SFT has empty domain (dead transduction)       |
| SFT02  | `constant-output-transduction`| Note     | SFT always produces constant output            |
| SFT03  | `nondeterministic-transduction`| Note    | SFT is not functional (multiple outputs)       |
| SFT04  | `equivalent-transductions`    | Note     | Two SFTs produce identical behavior            |

**SFT01** fires for each label in `SftAnalysis.empty_domain_labels`.  An empty
domain means no input word ever triggers the transduction -- the SFT is dead
code.  Hint: remove the dead transduction or fix its guard predicates.

**SFT02** fires for each label in `SftAnalysis.constant_output_labels`.  A
transduction that always emits the same constant can be replaced by a direct
constant mapping, reducing transducer complexity.

**SFT03** fires when `num_transducers - functional_count > 0`.  Nondeterministic
SFTs produce multiple outputs for some inputs, which may indicate overlapping
guard predicates that should be made disjoint.

**SFT04** fires for each pair in `SftAnalysis.equivalent_pairs`.  Two SFTs with
identical input-output behavior represent a deduplication opportunity.

## Feature Gate

```toml
sft = ["symbolic-automata"]
```

The `sft` feature depends on `symbolic-automata`, which provides the
`BooleanAlgebra` trait, `SymbolicAutomaton<A>`, and the concrete algebras
(`IntervalAlgebra`, `CharClassAlgebra`, `KatBooleanAlgebra`).  Enabling `sft`
makes the `prattail::sft` module available and activates the SFT01-SFT04 lint
functions, the `SftAnalysis` cost-benefit gate, and the M15 predicate dispatch
classification.

The `sft` feature is included in both the `all-features` and `all-analyses`
convenience groups defined in `Cargo.toml`.

## References

1. D'Antoni, L. & Veanes, M. (2012). "Symbolic Finite State Transducers:
   Algorithms and Applications." *POPL 2012*. The foundational paper defining
   SFTs with effective Boolean algebras and establishing algorithms for
   composition, pre-image, and functionality checking.

2. D'Antoni, L. & Veanes, M. (2017). "The Power of Symbolic Automata and
   Transducers." *CAV 2017*. Extended treatment covering minterm-based
   determinization, minimization, and practical applications of symbolic
   automata and transducers.

3. Feng, C. & Maletti, A. (2022). "Two-Way Transducers and Their Weighted
   Extensions." Provides the theoretical framework for bidirectional
   transductions that complements the one-way SFT model.

4. Veanes, M., de Halleux, P., & Tillmann, N. (2010). "Rex: Symbolic Regular
   Expression Explorer." *ICST 2010*. Demonstrates practical symbolic execution
   of regular expressions using effective Boolean algebras.

5. D'Antoni, L. & Veanes, M. (2014). "Minimization of Symbolic Automata."
   *POPL 2014*. Efficient minimization techniques applicable to the domain SFA
   extracted from SFTs via `domain_sfa()`.
