# Symbolic Automata -- Predicate-Guarded Transitions over Infinite Domains

## Quick Start

Symbolic Finite Automata (SFA) replace finite alphabet labels on transitions with predicates from an effective Boolean algebra, enabling automata over infinite domains. Instead of enumerating every possible character or integer as a separate transition, an SFA uses a single guard predicate like `[0, 100)` or `[a-z]` to compactly represent an entire equivalence class of inputs. This makes SFAs indispensable for PraTTaIL's handling of predicated types, numeric ranges, and Unicode character classes.

The module provides three concrete Boolean algebras -- `IntervalAlgebra` for integer ranges, `CharClassAlgebra` for Unicode characters, and `KatBooleanAlgebra` for propositional tests from the KAT module -- plus the generic `SymbolicAutomaton<A>` that works over any `BooleanAlgebra` implementation. A decidability classifier (`DecidabilityTier`) categorizes predicate expressions into four tiers (T1--T4) to determine whether they can be resolved at compile time, at runtime, semi-decidably, or not at all.

**Motivating example**: Consider a MeTTaIL receive pattern `for (@x : [0, 1000) <- ch)`. The predicate `x in [0, 1000)` cannot be finitely enumerated in a classical automaton, but an SFA guard `IntervalPred::Range(0, 1000)` captures it in a single transition.

```
┌─────────────────────────────────────────────────────────┐
│                PraTTaIL Pipeline                        │
│                                                        │
│  Grammar rules                                         │
│       │                                                │
│       ▼                                                │
│  WFST + Decision Tree (finite-alphabet dispatch)       │
│       │                                                │
│       │    ┌─────────────────────────────────────┐     │
│       └───▶│  Symbolic Automata Module            │     │
│            │                                     │     │
│            │  BooleanAlgebra (trait)              │     │
│            │    ├── IntervalAlgebra (numeric)     │     │
│            │    ├── CharClassAlgebra (Unicode)    │     │
│            │    └── KatBooleanAlgebra (KAT)       │     │
│            │                                     │     │
│            │  SymbolicAutomaton<A>                │     │
│            │  DecidabilityClassifier              │     │
│            └─────────────────────────────────────┘     │
│                                                        │
│  KAT module ◄──── KatBooleanAlgebra adapter            │
└────────────────────────────────────────────────────────┘
```

## Intuition

Think of a classical DFA as a museum guard with a checklist of allowed badge numbers: for each door (transition), the guard checks whether the visitor's badge appears on a finite list. An SFA guard replaces the checklist with a rule: "badge numbers between 100 and 200 may pass." The set of badge numbers is infinite, but the rule is compact and decidable.

**Before this module**: PraTTaIL dispatch relied on finite-alphabet WFST and PathMap tries. Predicates over numeric ranges or character classes had to be manually expanded or handled outside the automata framework.

**After this module**: Guard predicates participate directly in automata algorithms -- emptiness, intersection, complement, determinization, and equivalence -- all without enumerating the domain.

**Key insight**: The `BooleanAlgebra` trait isolates the three operations (satisfiability, witness generation, evaluation) that are necessary and sufficient for all standard automata constructions to work symbolically. Any domain with a decidable Boolean algebra can be plugged in.

## Theoretical Foundations

**Definition 1.1 (Effective Boolean Algebra).** An effective Boolean algebra is a tuple `(D, Psi, ⊥, ⊤, ∧, ∨, ¬, SAT, WIT, EVAL)` where:
- `D` is a (possibly infinite) domain
- `Psi` is a set of predicates over `D`
- `⊥, ⊤ in Psi` are the falsity and truth predicates
- `∧, ∨: Psi x Psi -> Psi` and `¬: Psi -> Psi` are Boolean connectives
- `SAT: Psi -> {true, false}` decides satisfiability
- `WIT: Psi -> D ∪ {⊥}` returns a witness element if satisfiable
- `EVAL: Psi x D -> {true, false}` evaluates a predicate on a concrete element

**Definition 1.2 (Symbolic Finite Automaton).** An SFA over a Boolean algebra `A` is a tuple `M = (Q, q₀, F, delta)` where:
- `Q` is a finite set of states
- `q₀ ⊆ Q` are initial states
- `F ⊆ Q` are accepting states
- `delta ⊆ Q x Psi x Q` is the predicate-guarded transition relation

A word `w = d₁ d₂ ... dₙ in D*` is accepted iff there exists a run `q₀ --[phi₁]--> q₁ --[phi₂]--> q₂ ... --[phiₙ]--> qₙ` with `q₀ in q₀`, `qₙ in F`, and `EVAL(phiᵢ, dᵢ) = true` for all `i`.

**Definition 1.3 (Minterm).** Given predicates `{phi₁, ..., phiₖ}`, a minterm is a maximal satisfiable conjunction `sigma₁(phi₁) ∧ sigma₂(phi₂) ∧ ... ∧ sigmaₖ(phiₖ)` where `sigmaᵢ in {id, ¬}`. Minterms partition the domain `D` into equivalence classes where all elements trigger exactly the same set of transitions.

**Theorem 1.1 (Minterm-Based Determinization, D'Antoni & Veanes 2017).** Every SFA can be determinized via minterm-based subset construction. Given an SFA with `n` states and `k` distinct guard predicates on outgoing transitions from a subset state, the determinized SFA has at most `2ⁿ` states and uses at most `2ᵏ` minterms per subset state. In practice, many minterms are unsatisfiable and pruned.

**Theorem 1.2 (Closure Properties).** SFAs are closed under union (complement+intersection), intersection (product construction with guard conjunction), complement (determinize then flip acceptance), and concatenation. Emptiness, universality, and equivalence are decidable.

**Decidability Classification (Tiers T1--T4):**
| Tier | Name | Description | Example |
|------|------|-------------|---------|
| T1 | Compile-time decidable | Propositional, finite-domain quantification | `x > 0 /\ x < 100` |
| T2 | Runtime decidable | Ascent relation lookups, dynamic queries | `rel(x, y)` |
| T3 | Semi-decidable | Bounded infinite-domain quantification | `Bounded(ForallInfinite(...), 1000)` |
| T4 | Undecidable | Unbounded infinite-domain quantification | `ForallInfinite(x, ...)` |

## Design

### Trait hierarchy

```
BooleanAlgebra (trait)
├── Predicate (assoc type)
├── Domain (assoc type)
├── true_pred() -> Predicate
├── false_pred() -> Predicate
├── and(a, b) -> Predicate
├── or(a, b) -> Predicate
├── not(a) -> Predicate
├── is_satisfiable(a) -> bool
├── witness(a) -> Option<Domain>
├── evaluate(pred, elem) -> bool
├── implies(a, b) -> bool          [default: !SAT(a ∧ ¬b)]
├── equivalent(a, b) -> bool       [default: implies(a,b) ∧ implies(b,a)]
├── is_tautology(a) -> bool        [default: !SAT(¬a)]
└── overlaps(a, b) -> bool         [default: SAT(a ∧ b)]
```

### Concrete algebras

| Algebra | Predicate type | Domain | Satisfiability method |
|---------|---------------|--------|----------------------|
| `IntervalAlgebra` | `IntervalPred` | `i64` | Range normalization (linear) |
| `CharClassAlgebra` | `CharClassPred` | `char` | Unicode range normalization |
| `KatBooleanAlgebra` | `BooleanTest` | `HashMap<String, bool>` | Exhaustive 2ⁿ search |

### Key types

- `SymbolicAutomaton<A: BooleanAlgebra>` -- the generic SFA
- `SymbolicState` -- state with `id`, `is_accepting`, optional `label`
- `SymbolicTransition<A>` -- guarded transition `(from, to, guard: A::Predicate)`
- `SymbolicAnalysis` -- pipeline bridge summary
- `DecidabilityTier` -- T1/T2/T3/T4 classification
- `PredicateExpr` -- rich predicate language for decidability analysis

## Algorithms

### Emptiness Check

```
Input:  SFA M = (Q, q₀, F, delta, algebra)
Output: true if L(M) = emptyset

1. Build adjacency list adj[q] = {q' | (q, phi, q') in delta, SAT(phi)}
2. BFS from q₀ through adj
3. Return true iff no state in F is reached
```

**Complexity**: O(|Q| + |delta| * SAT_cost)

### Determinization (Minterm-Based Subset Construction)

```
Input:  SFA M = (Q, q₀, F, delta, algebra)
Output: Deterministic SFA M'

1. worklist <- {q₀}; state_map <- {q₀ -> 0}
2. While worklist not empty:
   a. S <- pop(worklist)
   b. Collect guards = {phi | (q, phi, q') in delta, q in S}
   c. minterms <- compute_minterms(algebra, guards)
   d. For each minterm m:
      i.   T <- {q' | (q, phi, q') in delta, q in S, overlaps(m, phi)}
      ii.  If T not in state_map: add to worklist
      iii. Add transition S --[m]--> T
3. Accepting states of M': those containing an original accepting state
```

**Complexity**: O(2^|Q| * 2^k * SAT_cost) worst case; typically much smaller.

### Complement

1. Determinize the SFA
2. Flip accepting and non-accepting states
3. Add sink state for unmatched inputs (complement of covered guards)

### Equivalence

Reduces to emptiness of symmetric difference: `L(A) = L(B)` iff `(L(A) ∩ L(B)^c) ∪ (L(A)^c ∩ L(B)) = emptyset`.

## Integration

- **Pipeline** (`pipeline.rs`): `SymbolicAnalysis` provides guard satisfiability, overlap, and subsumption data for lint diagnostics.
- **KAT module** (`kat.rs`): `KatBooleanAlgebra` wraps `BooleanTest` predicates, enabling symbolic operations over propositional Hoare logic tests.
- **Decision tree** (`decision_tree.rs`): Symbolic guards model dispatch over predicate-guarded paths.
- **WFST** (`wfst.rs`): Symbolic guards generalize WFST input labels from finite tokens to predicate-guarded transitions.

## Diagnostics

No module-specific lint codes. Guard analysis feeds existing pipeline diagnostics via `SymbolicAnalysis`:
- `guard_satisfiability`: identifies unsatisfiable guards (dead transitions)
- `overlapping_guards`: non-disjoint guards indicate potential ambiguity
- `subsumed_guards`: one guard implies another, indicating redundancy

## Examples

### Example 1: Integer range acceptance

```rust
let algebra = IntervalAlgebra::new(0, 1000);
let mut sfa = SymbolicAutomaton::new(algebra.clone());
let q0 = sfa.add_state(false, Some("start".into()));
let q1 = sfa.add_state(true, Some("accept".into()));
sfa.set_initial(q0);
sfa.add_transition(q0, q1, IntervalPred::Range(10, 50));

assert!(!sfa.is_empty());
assert!(sfa.accepts(&[25]));    // 25 in [10, 50)
assert!(!sfa.accepts(&[100]));  // 100 not in [10, 50)
```

### Example 2: Character class intersection

```rust
let algebra = CharClassAlgebra::new();
let mut a = SymbolicAutomaton::new(algebra.clone());
// SFA accepting [a-z]
let q0a = a.add_state(false, None); a.set_initial(q0a);
let q1a = a.add_state(true, None);
a.add_transition(q0a, q1a, CharClassPred::Range('a', 'z'));

let mut b = SymbolicAutomaton::new(algebra.clone());
// SFA accepting [m-z]
let q0b = b.add_state(false, None); b.set_initial(q0b);
let q1b = b.add_state(true, None);
b.add_transition(q0b, q1b, CharClassPred::Range('m', 'z'));

let c = a.intersect(&b);
assert!(c.accepts(&['p']));    // 'p' in [a-z] ∩ [m-z]
assert!(!c.accepts(&['b']));   // 'b' in [a-z] but not [m-z]
```

## Advanced Topics

**Edge cases**: `KatBooleanAlgebra` satisfiability is exponential in the number of atoms (2ⁿ truth assignments). For PraTTaIL grammars with fewer than ~10 atoms, this is tractable.

**Interaction with other modules**: The symbolic module is a foundation for Modules 10 (Weighted MSO) and 6 (Register Automata), which both require predicate-guarded reasoning.

**Performance**: Range operations (normalize, intersect, complement) are linear in the number of intervals. Minterm computation is exponential in the number of distinct guards but is pruned aggressively by unsatisfiability checks.

## Reference

### API Table

| Function | Input | Output | Complexity |
|----------|-------|--------|------------|
| `is_empty()` | `&self` | `bool` | O(\|Q\| + \|delta\| * SAT) |
| `accepts(word)` | `&[Domain]` | `bool` | O(\|w\| * \|Q\| * \|delta\|) |
| `intersect(other)` | `&Self` | `Self` | O(\|Q₁\|\|Q₂\|\|delta₁\|\|delta₂\| * AND) |
| `complement()` | `&self` | `Self` | O(2^\|Q\|) worst case |
| `determinize()` | `&self` | `Self` | O(2^\|Q\| * 2^k * SAT) |
| `is_equivalent(other)` | `&Self` | `bool` | O(complement + intersect) |
| `analyze()` | `&self` | `SymbolicAnalysis` | O(\|delta\|^2 * SAT) |
| `classify_decidability(expr)` | `&PredicateExpr` | `DecidabilityTier` | O(\|expr\|) |
| `compute_minterms(preds)` | `&[Predicate]` | `Vec<Predicate>` | O(2^k * SAT) |

### Feature gate

`symbolic-automata`

### Citations

- D'Antoni, L. & Veanes, M. (2017). "The power of symbolic automata and transducers." *CAV 2017*.
- Veanes, M., de Halleux, P., & Tillmann, N. (2010). "Rex: Symbolic regular expression explorer." *ICST 2010*.
- D'Antoni, L. & Veanes, M. (2014). "Minimization of symbolic automata." *POPL 2014*.
