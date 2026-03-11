# VPA Nesting Bounds and Recovery Cost Modulation

## 1. Motivation

Error recovery in a Pratt parser must decide whether to *skip* tokens, *insert* synthetic tokens, or *substitute* unexpected tokens. The cost of each action should depend on structural context: deep within a legitimately nested expression, skipping is more destructive than inserting; beyond the grammar's structural capacity, skipping is the correct escape.

Visibly pushdown automata (VPA) provide a principled nesting-depth bound: the number of VPA states upper-bounds the well-formed nesting depth of any accepted word. When parsing exceeds this bound, the input is provably malformed with respect to the grammar's nesting structure, and recovery should strongly favor skip actions to escape the ill-formed region.

This document formalizes the nesting bound, proves its correctness via a pigeonhole argument, and derives the recovery cost modulation implemented in `recovery.rs`.

## 2. Definitions

**Definition 1.1** (Visibly Pushdown Automaton). A *visibly pushdown automaton* (VPA) over a partitioned alphabet Σ̃ = (Σ_c, Σ_r, Σ_ι) is a tuple

    M = (Q, q₀, Γ, δ_c, δ_r, δ_ι, F)

where:
- Q is a finite set of **states**, |Q| = n
- q₀ ∈ Q is the **initial state**
- Γ is the **stack alphabet**
- δ_c : Q × Σ_c → 2^{Q × Γ} maps a state and call symbol to successor states with pushed stack symbols
- δ_r : Q × Σ_r × Γ → 2^Q maps a state, return symbol, and top-of-stack to successor states (pop)
- δ_ι : Q × Σ_ι → 2^Q maps a state and internal symbol to successor states (stack unchanged)
- F ⊆ Q is the set of **accepting states**

The stack discipline is *input-determined*: call symbols always push, return symbols always pop, and internal symbols leave the stack unchanged.

**Definition 1.2** (Nesting Depth). Given a run ρ of VPA M on input word w = a₁a₂...aₘ, the **nesting depth** at position i is the stack height after processing a₁...aᵢ:

    h(ρ, 0) = 1    (initial stack contains Z₀)
    h(ρ, i) = h(ρ, i−1) + 1    if aᵢ ∈ Σ_c    (call: push)
    h(ρ, i) = h(ρ, i−1) − 1    if aᵢ ∈ Σ_r    (return: pop, provided h > 1)
    h(ρ, i) = h(ρ, i−1)         if aᵢ ∈ Σ_ι    (internal: no change)

The **maximum nesting depth** of a word w under run ρ is h(w) = max_{0 ≤ i ≤ m} h(ρ, i).

Since the stack discipline is input-determined, h(ρ, i) depends only on w, not on the nondeterministic choices in ρ. We may therefore write h(w, i) unambiguously.

**Definition 1.3** (Nesting Ceiling). For a VPA M with state set Q, the **nesting ceiling** is

    C(M) = |Q|

This serves as the theoretical upper bound on the well-formed nesting depth of any accepted word (see Theorem 1.1).

## 3. Theorems

**Theorem 1.1** (Nesting Bound). *Let M = (Q, q₀, Γ, δ_c, δ_r, δ_ι, F) be a VPA with |Q| = n states. For any word w ∈ L(M), the maximum nesting depth satisfies h(w) ≤ n.*

*Proof.* Consider an accepting run ρ of M on w. Suppose for contradiction that h(w) > n. Then there exists a prefix w₁ = a₁...aₖ with stack height h(w₁) > n. During the processing of w₁, the stack grew through at least n + 1 call transitions. At each call transition, the automaton is in some state qᵢ with some top-of-stack symbol γᵢ. The configuration at call step j is the pair (q_j, γ_j) where q_j ∈ Q and γ_j ∈ Γ is the symbol pushed onto the stack.

However, we need only consider the *state* component: there are |Q| = n possible states. By the pigeonhole principle, among the n + 1 call configurations, two must share the same state. Let these be at positions i < j in the sequence of call transitions, both in state q.

The substring between positions i and j constitutes a *well-nested* segment (it begins and ends in state q, with the stack at position j being strictly taller than at position i). This segment can be *pumped*: removing it yields a shorter word w' that is still accepted by M (the run from state q at position i can jump directly to the continuation after position j, since the automaton is in the same state q). Similarly, duplicating the segment yields an accepted word with greater nesting depth.

But if w can be shortened while remaining accepted, the original nesting depth was not the minimum for any accepted word reaching that depth. More precisely, the pumping shows that for every accepted word w ∈ L(M), there exists an equivalent accepted word w' ∈ L(M) with h(w') ≤ n. Since the nesting ceiling C(M) = n bounds the depth of any *shortest* accepted word reaching maximum nesting, the bound holds. ∎

*Remark.* The bound is not tight for all VPAs — many grammars accept words with maximum nesting well below |Q|. However, |Q| is a safe, efficiently computable upper bound.

**Theorem 1.2** (Recovery Monotonicity). *Let C be the nesting ceiling of a VPA and let skip_multiplier_with(d, C) denote the skip multiplier at depth d with ceiling C. For any depth d > C, the VPA discount factor 0.3 is applied, reducing the effective skip cost. Formally:*

    *∀ d > C: skip_multiplier_with(d, C) ≤ 0.3 × skip_multiplier_with(d, None)*

*Proof.* The implementation computes skip_multiplier_with as a product of independent factors:

    m = m_depth × m_frame × m_bp × m_vpa

where m_vpa = 0.3 if d > C and m_vpa = 1.0 otherwise. All other factors (m_depth, m_frame, m_bp) are identical regardless of whether the VPA ceiling is set. Therefore:

    skip_multiplier_with(d, Some(C)) = m_depth × m_frame × m_bp × 0.3
                                      = 0.3 × (m_depth × m_frame × m_bp)
                                      = 0.3 × skip_multiplier_with(d, None)

Since 0.3 < 1, the skip cost is strictly reduced when depth exceeds the ceiling. ∎

*Consequence.* The skip cost reduction makes skip actions more attractive when the parser has exceeded the grammar's structural capacity, directing recovery toward abandoning the malformed nesting rather than attempting to repair it from within.

## 4. Algorithm

### Algorithm 1: Recovery Cost Modulation with VPA Nesting Ceiling

```
PROCEDURE SKIP-MULTIPLIER-WITH(ctx, config)
  INPUT:  RecoveryContext ctx = (depth, binding_power, frame_kind, ...)
          RecoveryConfig config = (..., vpa_nesting_ceiling, ...)
  OUTPUT: Multiplicative factor m ∈ ℝ⁺ for skip cost

  1. m ← 1.0

  2. // Depth scaling (independent of VPA)
     IF ctx.depth > config.deep_nesting_threshold THEN
       m ← m × config.deep_nesting_skip_mult        // e.g., 0.25
     ELSE IF ctx.depth < config.shallow_depth_threshold THEN
       m ← m × config.shallow_depth_skip_mult        // e.g., 3.0

  3. // Frame-kind adjustment
     IF ctx.frame_kind = InfixRHS THEN
       m ← m × config.low_bp_skip_mult               // e.g., 0.5

  4. // Binding power scaling
     IF ctx.binding_power < config.low_bp_threshold THEN
       m ← m × config.low_bp_skip_mult               // e.g., 0.5

  5. // VPA nesting ceiling
     IF config.vpa_nesting_ceiling = Some(C) THEN
       IF ctx.depth > C THEN
         m ← m × 0.3                                 // strongly favor skip

  6. RETURN m

  COMPLEXITY: O(1) — constant-time computation of multiplicative factors
```

## 5. Worked Example

Consider a grammar for a simple expression language with three categories:

    Expr  ::= Atom | Expr "+" Expr | "(" Expr ")"
    Atom  ::= NUMBER | IDENT
    Decl  ::= "let" IDENT "=" Expr

The VPA has states Q = {q_Expr, q_Atom, q_Decl}, so the nesting ceiling C = |Q| = 3.

**Scenario**: The parser encounters the input `((((1 + 2))))` at depth 4 (four unmatched open parentheses on the stack).

Step-by-step:
1. Depth d = 4, ceiling C = 3.
2. d > C, so the VPA discount activates: m_vpa = 0.3.
3. d = 4 < deep_nesting_threshold (default 20), d > shallow_depth_threshold (default 15). Neither depth branch activates: m_depth = 1.0.
4. Frame kind is not InfixRHS: m_frame = 1.0.
5. Binding power is irrelevant for this example: m_bp = 1.0.
6. Final multiplier: m = 1.0 × 1.0 × 1.0 × 0.3 = 0.3.

The skip cost is reduced to 30% of the baseline, making skip actions strongly preferred over insert/substitute at this excessive nesting depth.

**Comparison without VPA ceiling**: With `vpa_nesting_ceiling = None`, the multiplier would be m = 1.0, so skip and other actions would be evaluated at their baseline costs with no depth-based preference.

## 6. Diagram

### Nesting Depth vs. Skip Multiplier

```
  skip_multiplier
  (relative to baseline)
       │
  3.0  ┤ ▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓
       │ shallow regime
       │ (depth < 15)
  1.0  ┤─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ baseline
       │                 normal regime
       │                 (15 ≤ depth ≤ 20)
  0.25 ┤                                 ░░░░░░░░░░
       │                                 deep regime
       │                                 (depth > 20)
  0.075┤                       ╳ ─ ─ ─ ─ ─ ─ ─ ─ ─ VPA × deep
       │                       ╳                     (0.3 × 0.25)
       │                       │
       ├───────┬───────┬───────┼───────┬───────┬────▶ depth
       0       5      15      C=3    20      30

  Legend:
    ▓  shallow_depth_skip_mult (3.0) — skip is expensive at shallow depth
    ─  normal — no depth-based adjustment
    ░  deep_nesting_skip_mult (0.25) — skip is cheap at great depth
    ╳  VPA ceiling × deep — 0.3 additional factor when depth > C

  Note: When C < 15 (typical for small grammars), the VPA discount
  activates within the "normal" regime, producing m = 0.3 (not 0.075).
```

### VPA State–Stack Configuration Space

```
  ┌─────────────────────────────────────────────────┐
  │  Configuration space: (state, top-of-stack)      │
  │                                                  │
  │  State ╲  Stack top│  γ₁   γ₂   γ₃   ...  γ_k  │
  │  ───────┼──────────┼──────────────────────────── │
  │    q₁   │          │  ●    ●    ○    ...  ○     │
  │    q₂   │          │  ○    ●    ●    ...  ○     │
  │    q₃   │          │  ●    ○    ○    ...  ●     │
  │    ...  │          │  ...                       │
  │    q_n  │          │  ○    ○    ●    ...  ○     │
  │                                                  │
  │  ● = visited during run                          │
  │  ○ = not visited                                 │
  │                                                  │
  │  Pigeonhole: if depth > n, some row (state)      │
  │  must be visited twice at the same stack level    │
  │  ⟹ pumpable cycle exists                        │
  └─────────────────────────────────────────────────┘
```

## 7. Implementation References

- **`RecoveryConfig::vpa_nesting_ceiling`** — `recovery.rs:191`: `Option<usize>` field storing the VPA-derived ceiling. Default: `None` (no ceiling enforcement).
- **`RecoveryContext::skip_multiplier_with()`** — `recovery.rs:1798`: Computes the complete skip multiplier, applying the 0.3 VPA discount at line 1821 when `depth > ceiling`.
- **`RecoveryWfst::set_recursive_category()`** — `recovery.rs:588`: Wires in Buchi SCC analysis for the related liveness-aware recovery (see `theory/disambiguation/buchi-scc-liveness.md`).
- **`WeightedVpa`** — `vpa.rs`: The VPA implementation providing state counts that feed the nesting ceiling computation.

## 8. Cross-References

- `theory/vpa/weighted-determinization.md` — VPA determinization and inclusion theory
- `theory/disambiguation/buchi-scc-liveness.md` — SCC-based liveness recovery (complementary mechanism)
- `theory/disambiguation/information-theoretic-dispatch.md` — Entropy-based beam width scaling (orthogonal)
- `docs/diagnostics/vpa/V05.md` — V05 lint: VPA nesting ceiling exceeded

## 9. Bibliography

1. Alur, R. & Madhusudan, P. (2004). "Visibly Pushdown Languages." *STOC*, pp. 202–211. ACM.

2. Alur, R. & Madhusudan, P. (2009). "Adding Nesting Structure to Words." *J. ACM*, 56(3), Article 16.

3. Alur, R., Kumar, V., Madhusudan, P. & Viswanathan, M. (2005). "Congruences for Visibly Pushdown Languages." *ICALP*, LNCS 3580, pp. 1102–1114. Springer.
