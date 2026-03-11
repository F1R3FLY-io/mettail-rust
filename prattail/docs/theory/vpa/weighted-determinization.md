# Weighted Visibly Pushdown Automata — Determinization and Inclusion Theory

## Motivation

Context-free languages are not closed under complement or intersection, and equivalence is undecidable. **Visibly pushdown automata** (VPA) restrict pushdown automata so that the stack discipline is determined entirely by the input — call symbols push, return symbols pop, internal symbols are stack-neutral. This "visible" stack discipline yields a language class (**visibly pushdown languages**, VPL) that is closed under all Boolean operations with decidable equivalence and inclusion, while still capturing nested structure (matched parentheses, XML, recursive function calls).

**Core question**: How can we verify structural equivalence and inclusion of grammars with nested constructs (brackets, blocks, function calls) in a decidable framework, and extend this to quantitative analysis with semiring weights?

**Historical context**: Alur & Madhusudan (2004) introduced VPAs and proved their remarkable closure and decidability properties. The key insight is that when the input determines the stack behavior, the subset construction for determinization remains well-defined despite the stack. Alur, Kumar, Madhusudan & Viswanathan (2005) established a Myhill-Nerode theorem for VPLs, enabling minimization.

**Connection to the Chomsky hierarchy**: VPLs sit strictly between regular and context-free languages. They properly contain all regular languages and are properly contained in the deterministic context-free languages (DCFL). Unlike general CFLs, VPLs are closed under complement and intersection.

```
Regular ⊂ VPL ⊂ DCFL ⊂ CFL ⊂ CSL
  (FA)    (VPA)  (DPDA)  (PDA)  (LBA)
```

## Definitions

**Definition 4.1** (Visibly Pushdown Alphabet). A **visibly pushdown alphabet** is a triple Σ̃ = (Σ_c, Σ_r, Σ_int) where:
- Σ_c is the set of **call** symbols (push onto stack)
- Σ_r is the set of **return** symbols (pop from stack)
- Σ_int is the set of **internal** symbols (stack-neutral)
- Σ = Σ_c ∪ Σ_r ∪ Σ_int and all three sets are pairwise disjoint

*Intuition*: The alphabet partition determines the stack behavior. When reading a call symbol, the automaton must push; when reading a return symbol, it must pop. The automaton has no choice in its stack operations — only in its state transitions.

*Example*: For PraTTaIL bracket matching: Σ_c = {(, {, [}, Σ_r = {), }, ]}, Σ_int = {+, -, id, if, ...}.

**Definition 4.2** (Nondeterministic Visibly Pushdown Automaton). An **NVPA** over Σ̃ is a tuple M = (Q, Σ̃, Γ, δ, Q₀, Z₀, F) where:
- Q is a finite set of states
- Γ is the stack alphabet
- δ = (δ_c, δ_r, δ_int) is the transition function:
  - δ_c : Q × Σ_c → 2^{Q × Γ} — call transitions (push γ)
  - δ_r : Q × Σ_r × Γ → 2^Q — return transitions (pop γ)
  - δ_int : Q × Σ_int → 2^Q — internal transitions (stack unchanged)
- Q₀ ⊆ Q is the set of initial states
- Z₀ ∈ Γ is the initial stack symbol
- F ⊆ Q is the set of accepting states

*Intuition*: The crucial restriction: the type of stack operation (push/pop/neutral) is determined by the input symbol, not by the automaton's choice. This makes the stack height a function of the input word alone.

**Definition 4.3** (Weighted VPA). A **weighted VPA** over semiring (K, ⊕, ⊗, 0̄, 1̄) is an NVPA where each transition carries a weight from K:
- δ_c : Q × Σ_c → 2^{Q × Γ × K} — call transitions with weight
- δ_r : Q × Σ_r × Γ → 2^{Q × K} — return transitions with weight
- δ_int : Q × Σ_int → 2^{Q × K} — internal transitions with weight

The weight of a run is the semiring product (⊗) of transition weights along the path. The total weight of a word is the semiring sum (⊕) over all accepting runs.

*Example*: In MeTTaIL, `WeightedVpa<W>` parameterizes over semiring W. `Vpa = WeightedVpa<BooleanWeight>` is the classical unweighted case. `WeightedVpa<TropicalWeight>` computes shortest-path parsing cost.

**Definition 4.4** (Macro-State). In the determinization of an NVPA, a **macro-state** S ⊆ Q is a set of micro-states from the original automaton. The key insight of VPA determinization is that the stack contents at any point in the computation are determined by the input word (not by nondeterministic choices), so macro-states need only track state sets, not stack configurations.

## Key Theorems

**Theorem 4.1** (VPA Determinization; Alur & Madhusudan, 2004, Theorem 1):
For every NVPA M with n states, there exists an equivalent deterministic VPA (DVPA) with at most 2^{n²+n} states.

*Intuition*: The determinization uses a subset construction adapted for the visible stack discipline. Internal transitions use standard powerset construction. Call transitions push the current macro-state (as a stack symbol) and compute the successor macro-state. Return transitions pop the caller macro-state and combine return targets appropriately. The n² factor (rather than 2^n) comes from tracking summary information across matched call-return pairs.

*Proof sketch*:
1. **Internal transitions**: For macro-state S and internal symbol a, compute S' = ⋃_{q∈S} δ_int(q, a). This is the standard powerset construction.
2. **Call transitions**: For macro-state S and call symbol c, push S onto the stack (encoded as a stack symbol), then compute S' = ⋃_{q∈S} {q' : (q', γ) ∈ δ_c(q, c)}.
3. **Return transitions**: For macro-state S, return symbol r, and popped stack symbol S_caller, compute S' = ⋃_{q∈S, p∈S_caller} {q' : q' ∈ δ_r(q, r, γ) where (·, γ) was pushed by p on the matching call}.
4. **Acceptance**: Macro-state S is accepting iff S ∩ F ≠ ∅.

*Consequence for MeTTaIL*: The `WeightedVpa::determinize()` method implements this algorithm. The resulting DVPA is **total** — every (macro-state, symbol) pair has exactly one successor, with missing transitions routed to a dead/sink state.

*Reference*: Alur, R. & Madhusudan, P. (2004). "Visibly Pushdown Languages." *STOC*, pp. 202–211. ACM.

**Theorem 4.2** (VPL Closure Properties; Alur & Madhusudan, 2004, Theorem 2):
Visibly pushdown languages are effectively closed under:
1. **Union**: O(n₁ + n₂) states (disjoint union with new initial state)
2. **Intersection**: O(n₁ · n₂) states (product construction)
3. **Complement**: determinize (2^{O(n²)} states) then flip accepting states
4. **Concatenation**: O(n₁ · n₂) states
5. **Kleene star**: O(n²) states

*Consequence for MeTTaIL*: Complementation enables inclusion checking: L(A) ⊆ L(B) iff L(A) ∩ L(B)^c = ∅. The `weighted_inclusion()` method uses this approach with weight comparison at accepting configurations.

*Reference*: Alur, R. & Madhusudan, P. (2004). "Visibly Pushdown Languages." *STOC*, pp. 202–211. ACM. Theorem 2.

**Theorem 4.3** (VPL Decidability; Alur & Madhusudan, 2009, Theorem 5):
The following problems are decidable for VPAs:
1. **Emptiness**: NLOGSPACE-complete (graph reachability)
2. **Universality**: EXPTIME-complete (determinize + complement + empty)
3. **Inclusion**: EXPTIME-complete (complement + intersect + empty)
4. **Equivalence**: EXPTIME-complete (double inclusion)

*Intuition*: These are the same decidability results as for regular languages, despite VPLs being strictly more expressive. The visible stack discipline ensures that the subset construction (the source of complexity) remains finite.

*Consequence for MeTTaIL*: All these operations are T1 (compile-time decidable). The `is_deterministic()`, `reachable_states()`, `trim()`, and `weighted_inclusion()` methods enable complete structural verification of grammar transformations at compile time.

*Reference*: Alur, R. & Madhusudan, P. (2009). "Adding Nesting Structure to Words." *J. ACM*, 56(3), Article 16.

**Theorem 4.4** (Myhill-Nerode for VPLs; Alur, Kumar, Madhusudan & Viswanathan, 2005):
For every VPL L, there exists a unique minimal DVPA recognizing L (up to isomorphism). The minimal DVPA can be computed in polynomial time from any DVPA for L using a congruence-based construction analogous to the classical Myhill-Nerode theorem.

*Consequence for MeTTaIL*: The `trim()` method removes unreachable states as a first step toward minimization. Full minimization via the VPL congruence is a future extension.

*Reference*: Alur, R., Kumar, V., Madhusudan, P. & Viswanathan, M. (2005). "Congruences for Visibly Pushdown Languages." *ICALP*, LNCS 3580, pp. 1102–1114. Springer.

## Algorithms

### Algorithm 1: VPA Determinization (Subset Construction)

```
PROCEDURE VPA-DETERMINIZE(M = (Q, Σ̃, Γ, δ, Q₀, Z₀, F))
  INPUT:  NVPA M
  OUTPUT: Equivalent DVPA M'

  1. Dead state: S_dead = ∅ (sink for missing transitions)
  2. Initial macro-state: S₀ = Q₀
  3. Worklist ← {S₀, S_dead}; macro_states ← {S₀ → id₀, S_dead → id_dead}
  4. While Worklist ≠ ∅:
       S ← pop from Worklist
       For each internal symbol a ∈ Σ_int:
         S' ← ⋃_{q∈S} δ_int(q, a)
         Register S' → add transition S --a--> S'
       For each call symbol c ∈ Σ_c:
         S' ← ⋃_{q∈S} {q' : (q', γ) ∈ δ_c(q, c)}
         stack_sym ← encode(S)  // push caller macro-state identity
         Register S' → add call transition S --c/push(stack_sym)--> S'
       For each return symbol r ∈ Σ_r:
         For each known caller macro-state S_caller:
           stack_sym ← encode(S_caller)
           S' ← ⋃_{q∈S, p∈S_caller, (·,γ)∈δ_c(p,·)} δ_r(q, r, γ)
           Register S' → add return transition S --r/pop(stack_sym)--> S'
  5. F' ← {S : S ∩ F ≠ ∅}
  6. Return M' = (macro_states, Σ̃, stack_syms, transitions, {S₀}, encode(S_dead), F')

  COMPLEXITY: O(2^{n²+n} · |Σ|) worst case
```

### Algorithm 2: Weighted VPA Run Simulation

```
PROCEDURE WEIGHTED-RUN(M, word)
  INPUT:  Weighted VPA M, input word w₁w₂...wₙ
  OUTPUT: Total acceptance weight ∈ K

  1. configs ← {(q₀, [Z₀]) → w₀ : q₀ ∈ Q₀, w₀ = initial_weight(q₀)}
  2. For each symbol wᵢ:
     next_configs ← ∅
     For each ((q, stack), w) ∈ configs:
       Case classify(wᵢ):
         Internal: for (q', tw) ∈ δ_int(q, wᵢ):
           next_configs[(q', stack)] ⊕← w ⊗ tw
         Call: for (q', γ, tw) ∈ δ_c(q, wᵢ):
           next_configs[(q', stack·γ)] ⊕← w ⊗ tw
         Return: if |stack| > 1, top = stack.last():
           for (q', tw) ∈ δ_r(q, wᵢ, top):
             next_configs[(q', stack[0..-1])] ⊕← w ⊗ tw
     configs ← next_configs
  3. total ← 0̄
     For each ((q, _), w) ∈ configs where q ∈ F:
       total ⊕← w ⊗ accepting_weight(q)
  4. Return total

  COMPLEXITY: O(|w| · |Q|^k · |δ|) where k depends on stack depth
```

## Decidability Analysis

| Property | Complexity | Tier |
|----------|-----------|------|
| Emptiness | NLOGSPACE-complete | T1 |
| Membership | O(\|w\| · \|Q\|) | T1 |
| Determinization | EXPTIME (2^{O(n²)}) | T1 |
| Equivalence | EXPTIME-complete | T1 |
| Inclusion L(A) ⊆ L(B) | EXPTIME-complete | T1 |
| Weighted inclusion (idempotent K) | EXPTIME | T1 |
| Minimization | PTIME (from DVPA) | T1 |

**Boundary cases**: If the alphabet partition were not fixed (i.e., the automaton could choose whether a symbol pushes or pops), we would recover general pushdown automata, and equivalence/inclusion become undecidable. The visible stack discipline is the exact boundary between decidability and undecidability for these problems.

## Diagrams

### VPA Alphabet Partition

```
Input alphabet Σ = Σ_c ∪ Σ_r ∪ Σ_int

  ┌──────────────────────────────────────────────┐
  │                    Σ                         │
  │  ┌──────────┐ ┌──────────┐ ┌──────────────┐ │
  │  │  Σ_c     │ │  Σ_r     │ │  Σ_int       │ │
  │  │  (call)  │ │ (return) │ │ (internal)   │ │
  │  │          │ │          │ │              │ │
  │  │  ( { [   │ │  ) } ]   │ │ + - id if    │ │
  │  │  PUSH    │ │  POP     │ │ NO-OP       │ │
  │  └──────────┘ └──────────┘ └──────────────┘ │
  └──────────────────────────────────────────────┘
```

### VPA Determinization: Macro-State Construction

```
Original NVPA with states {q₀, q₁, q₂}:

   q₀ ──(──▶ q₁    q₀ ──(──▶ q₂    (nondeterministic call)
   q₁ ──)──▶ q₀    q₂ ──)──▶ q₀    (return transitions)

Determinized DVPA:

   {q₀} ──(/ push M{q₀}──▶ {q₁,q₂}
   {q₁,q₂} ──)/ pop M{q₀}──▶ {q₀}

   Macro-state {q₁,q₂} tracks both possibilities
   Stack symbol M{q₀} remembers the caller macro-state
```

### VPL Position in the Language Hierarchy

```
  ┌────────────────────────────────────────────────┐
  │  Context-Sensitive Languages (CSL)             │
  │  ┌──────────────────────────────────────────┐  │
  │  │  Context-Free Languages (CFL)            │  │
  │  │  ┌────────────────────────────────────┐  │  │
  │  │  │  DCFL (Deterministic CFL)          │  │  │
  │  │  │  ┌──────────────────────────────┐  │  │  │
  │  │  │  │  VPL (Visibly Pushdown)      │  │  │  │
  │  │  │  │  ┌────────────────────────┐  │  │  │  │
  │  │  │  │  │  Regular Languages     │  │  │  │  │
  │  │  │  │  │  (no stack needed)     │  │  │  │  │
  │  │  │  │  └────────────────────────┘  │  │  │  │
  │  │  │  │  Closed under ∪,∩,¬,·,*     │  │  │  │
  │  │  │  │  Decidable: =,⊆,∅          │  │  │  │
  │  │  │  └──────────────────────────────┘  │  │  │
  │  │  │  Closed under ∪,∩,¬               │  │  │
  │  │  └────────────────────────────────────┘  │  │
  │  │  NOT closed under ∩ or ¬                 │  │
  │  └──────────────────────────────────────────┘  │
  └────────────────────────────────────────────────┘
```

## Connections

**To Module 2 (Buchi)**: VPA-Buchi automata combine visible stack discipline with Buchi acceptance for ω-regular properties of infinite recursive computations. The `from_wpds()` bridge in `buchi.rs` converts WPDS call graphs to Buchi automata, which could be extended to VPA-Buchi for stack-aware liveness analysis.

**To Module 3 (Alternating)**: Alternating VPAs combine the visible stack with existential/universal branching. This would model "all possible parsings of nested input must satisfy a property" (universal) or "some parsing suffices" (existential).

**To WPDS module**: VPAs and weighted pushdown systems (WPDS) are closely related. A VPA can be viewed as a WPDS where the push/pop discipline is determined by the input rather than by the system's choice. The `wpds.rs` module's `poststar`/`prestar` algorithms apply to VPAs with the additional constraint of input-determined stack operations.

**Open problems**:
1. **Weighted VPA minimization**: Extend the Myhill-Nerode congruence for VPLs to weighted VPAs over arbitrary semirings.
2. **Symbolic VPA**: Combine VPAs with symbolic guards (Module 1) for infinite-alphabet nested structures.
3. **VPA learning**: Extend Angluin's L* algorithm to learn VPAs from membership and equivalence queries.

## Bibliography

1. Alur, R. & Madhusudan, P. (2004). "Visibly Pushdown Languages." *STOC*, pp. 202–211. ACM.

2. Alur, R. & Madhusudan, P. (2009). "Adding Nesting Structure to Words." *J. ACM*, 56(3), Article 16.

3. Alur, R., Kumar, V., Madhusudan, P. & Viswanathan, M. (2005). "Congruences for Visibly Pushdown Languages." *ICALP*, LNCS 3580, pp. 1102–1114. Springer.

4. Alur, R. & Madhusudan, P. (2006). "Visibly Pushdown Languages." *STOC 2004 Extended Version*, available as technical report.

5. von Braunmuhl, B. & Verbeek, R. (1983). "Input-Driven Languages are Recognized in log n Space." *Annals of Discrete Mathematics*, 24, pp. 1–19.
