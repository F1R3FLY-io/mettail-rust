# Dispatch SFA Model — Self-Referential Verification

## Motivation

The feature extraction function `extract_features()` is the runtime dispatcher.
The SFA (Symbolic Finite Automaton) is a formal *model* that verifies the
dispatch is complete and consistent. This is self-referential: it uses M1's
`BooleanAlgebra` trait to verify the dispatch of M1–M11.

## Definitions

**Definition 3.1** (Dispatch Alphabet). The **dispatch alphabet** is the set of
all possible `PredicateSignature` values, represented as u16 bitfields:
D = { σ ∈ {0,...,2¹¹-1} }. Each element σ encodes a subset of {M1,...,M11}.

**Definition 3.2** (Dispatch Boolean Algebra). The **DispatchAlgebra** is an
effective Boolean algebra (D, Ψ, ⟦·⟧, ⊥, ⊤, ∧, ∨, ¬, SAT) where:

- D = PredicateSignature (u16 bitfields)
- Ψ = SignaturePred (bit-membership predicates)
- ⟦HasBit(i)⟧ = { σ ∈ D : σ.bit(i) = 1 }
- ⊤ = True (all signatures satisfy)
- ⊥ = False (no signature satisfies)
- ∧ = And(p, q) (conjunction of predicates)
- ∨ = Or(p, q) (disjunction of predicates)
- ¬ = Not(p) (complement)
- SAT(HasBit(i)) = true for all i ∈ {0,...,10}

*Intuition*: The algebra asks "does this signature have bit i set?" Each predicate
is a module-membership test. The algebra is effective because satisfiability is
decidable (in constant time, via bitwise operations on u16).

*In PraTTaIL*: `DispatchAlgebra` implements `BooleanAlgebra` from `symbolic.rs`,
reusing the same trait that `IntervalAlgebra` and `FiniteAlgebra` implement.

**Definition 3.3** (Dispatch SFA). The **Dispatch SFA** A_D = (DispatchAlgebra, Q, q₀, F, δ) where:
- Q = {q₀, q_M1, q_M2, ..., q_M11, q_⊥}  (13 states)
- q₀ is the initial state
- F = {q_M1, ..., q_M11}  (all module states are accepting)
- δ(q₀, HasBit(i)) = q_Mᵢ  for each i ∈ {0,...,10}
- δ(q₀, ¬(HasBit(0) ∨ ... ∨ HasBit(10))) = q_⊥

## State Diagram

```
                         HasBit(0)
                   ┌──────────────────→ ◉ q_M1  (Symbolic)
                   │    HasBit(1)
                   ├──────────────────→ ◉ q_M2  (Büchi)
                   │    HasBit(2)
                   ├──────────────────→ ◉ q_M3  (AWA)
                   │    HasBit(3)
                   ├──────────────────→ ◉ q_M4  (VPA)
                   │    HasBit(4)
      ┌───┐        ├──────────────────→ ◉ q_M5  (Parity Tree)
      │q₀ │────────┤    HasBit(5)
      └───┘        ├──────────────────→ ◉ q_M6  (Register)
                   │    HasBit(6)
                   ├──────────────────→ ◉ q_M7  (Probabilistic)
                   │    HasBit(7)
                   ├──────────────────→ ◉ q_M8  (Multi-Tape)
                   │    HasBit(8)
                   ├──────────────────→ ◉ q_M9  (Multiset)
                   │    HasBit(9)
                   ├──────────────────→ ◉ q_M10 (W. MSO)
                   │    HasBit(10)
                   └──────────────────→ ◉ q_M11 (Two-Way)

      ¬(HasBit(0) ∨ ... ∨ HasBit(10))
      ────────────────────────────────→ ○ q_⊥   (reject)

Legend: ◉ = accepting state, ○ = non-accepting state
```

The SFA is nondeterministic in the sense that a single input signature σ may
trigger multiple transitions (one for each set bit). The `accepts(σ)` function
checks whether *any* transition from q₀ leads to an accepting state.

## Verification Properties

**Theorem 3.1** (Completeness). For every σ ∈ D with σ ≠ 0: A_D accepts σ.

*Proof*: σ ≠ 0 implies ∃i ∈ {0,...,10} such that σ.bit(i) = 1.
Then the transition δ(q₀, HasBit(i)) = q_Mᵢ is enabled, and q_Mᵢ ∈ F.
Therefore A_D accepts σ. ∎

**Theorem 3.2** (Zero Rejection). A_D rejects the zero signature σ = 0.

*Proof*: For σ = 0, no bit is set, so ∀i: HasBit(i) evaluates to false.
No transition to any q_Mᵢ is enabled. The only enabled transition leads to q_⊥,
which is not in F. Therefore A_D rejects σ = 0. ∎

**Theorem 3.3** (Base Module Invariant). For every σ produced by
`extract_features()`: σ.bit(0) = 1 ∧ σ.bit(9) = 1.

*Proof*: `extract_features()` initializes σ = PredicateSignature::BASE
= M1_SYMBOLIC | M10_MSO = (1 << 0) | (1 << 9). No match arm in the traversal
clears bits (all operations are `sig.set(...)` which performs bitwise OR).
Therefore bits 0 and 9 remain set throughout the traversal. ∎

**Corollary 3.1** (Non-Degeneracy). PD01 (degenerate guard) can only fire for
user-constructed `PredicateSignature` values, never for `extract_features()` output.

*Proof*: By Theorem 3.3, every `extract_features()` output has M1 and M10 set,
which is strictly more than "no specialized module." PD01 checks for
`signature.is_base_only()`, which is true iff only M1 and M10 are set —
meaning no *specialized* module was activated, not that *no* module was
activated. ∎

## Connection to M1 Implementation

`DispatchAlgebra` reuses the `BooleanAlgebra` trait from `symbolic.rs`:

```rust
// In symbolic.rs:
pub trait BooleanAlgebra {
    type Predicate;
    type Domain;
    fn true_pred(&self) -> Self::Predicate;
    fn false_pred(&self) -> Self::Predicate;
    fn and(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate;
    fn or(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate;
    fn not(&self, a: &Self::Predicate) -> Self::Predicate;
    fn is_satisfiable(&self, pred: &Self::Predicate) -> bool;
    fn witness(&self, pred: &Self::Predicate) -> Option<Self::Domain>;
    fn evaluate(&self, pred: &Self::Predicate, value: &Self::Domain) -> bool;
}

// In predicate_dispatch.rs:
impl BooleanAlgebra for DispatchAlgebra {
    type Predicate = SignaturePred;       // HasBit(i), And, Or, Not, True, False
    type Domain = PredicateSignature;     // u16 bitfield
    // ... implementations using bitwise operations
}
```

Side-by-side with `IntervalAlgebra`:
- `IntervalAlgebra::Domain = u32` (character ranges)
- `DispatchAlgebra::Domain = PredicateSignature` (module bitfields)
- Both use the same trait, enabling `SymbolicAutomaton<DispatchAlgebra>` to
  verify dispatch completeness using the same SFA infrastructure that M1 uses
  for guard analysis.

## Overlap Analysis

`dispatch_overlap_pairs()` identifies module pairs that are always co-activated:

- (M1, M10): Always co-active (both in BASE)
- (M2, M3): ForallInfinite activates both
- (M8, M11): Cross-channel references activate both
- (M4, M5): Recursive predicates / letprop activate both

This information is used for analysis planning: co-activated modules can share
intermediate results.

## References

- D'Antoni, L. & Veanes, M. (2017). The power of symbolic automata and transducers. *CAV 2017*.
- Veanes, M. et al. (2010). Symbolic finite automata. *ACM SIGPLAN Notices* 45(1).
