# VpaClosureProperties.v -- VPA Closure and Decidable Equivalence

**File:** `formal/rocq/mathematical_analyses/theories/VpaClosureProperties.v`
**Lines:** 518
**Admitted:** 0
**Dependencies:** Standalone (no imports from other proof files)


## Intuition

A Visibly Pushdown Automaton (VPA) is a pushdown automaton where the
stack operation -- push, pop, or no-op -- is determined entirely by the
input symbol, not by the automaton's state. This "input-driven" stack
discipline is exactly what PraTTaIL's grammar categories exhibit:
parentheses and brackets are always call/return symbols regardless of
parsing state.

This seemingly minor restriction has profound consequences. General
pushdown automata cannot be determinized, cannot be complemented, and
have undecidable equivalence. VPAs can do *all three*. This proof file
establishes these closure properties, which PraTTaIL uses for grammar
equivalence checking and inclusion testing between VPA models of
grammar categories.


## What It Proves

### Part 1: Closure Under Complement

```
Theorem complement_correctness : forall w,
  complement_accepts w = true <->
  (accepts w = false /\
   match snd (run initial_config w) with [] => True | _ => False end).
```

The complement VPA accepts exactly those well-matched words that the
original VPA rejects. The construction simply swaps the acceptance
predicate: `complement_is_final q = negb (is_final q)`.

```
Theorem complement_involution : forall w,
  double_comp_accepts = accepts w.
```

Complementing twice recovers the original language.

### Part 2: Closure Under Intersection

```
Theorem intersection_correctness : forall w,
  prod_accepts w = true <-> (accepts w = true /\ accepts2 w = true).
```

The product VPA accepts exactly the intersection of the two component
languages. The construction runs both VPAs in lockstep.

### Part 3: Decidable Equivalence

```
Theorem vpa_equivalence_decidable :
  (forall P : list Symbol -> bool,
    (exists w, P w = true) \/ (forall w, P w = false)) ->
  (forall w, accepts w = accepts2 w) \/
  (exists w, accepts w <> accepts2 w).
```

Given a decidable emptiness oracle for Boolean predicates on words,
VPA language equivalence is decidable. The proof reduces equivalence to
two emptiness checks on symmetric difference languages.


## Why It Matters

```
  ┌─────────────────────────────────────────────────────────────┐
  │  Grammar Equivalence Checking                               │
  │  (are two grammar versions equivalent?)                     │
  ├─────────────────────────────────────────────────────────────┤
  │  VPA Intersection  +  VPA Complement  +  Emptiness Check    │ <-- THIS
  ├─────────────────────────────────────────────────────────────┤
  │  VPA Model of Grammar Categories                            │
  │  (call = open bracket, return = close bracket)              │
  └─────────────────────────────────────────────────────────────┘
```

PraTTaIL models grammar categories as VPAs (`vpa.rs`). The alphabet
partition maps grammar symbols to call/return/internal based on their
role in the grammar's delimiter structure. The closure properties enable:

- **Grammar refinement checking:** is the new grammar a subset of the old?
  (complement + intersection + emptiness)
- **Ambiguity detection:** do two categories overlap?
  (intersection + emptiness)
- **Equivalence after optimization:** did an optimization preserve the
  language? (full equivalence check)

Without these closure properties, these questions would be undecidable.


## Proof Strategy

### Complement: Determinism Is the Key

The complement construction is trivial for deterministic automata: swap
accepting and non-accepting states. The entire proof reduces to:

```
rewrite Bool.negb_true_iff.   (* complement correctness *)
rewrite Bool.negb_involutive.  (* involution *)
```

The subtlety is in the well-matchedness condition. The complement only
applies to words where the stack is empty at the end (well-matched
words). For non-well-matched words, neither the original nor the
complement accepts:

```
  ┌─────────────────────────────────────────────────────┐
  │ Word class          │ accepts │ complement_accepts │
  ├─────────────────────┼─────────┼────────────────────┤
  │ Well-matched, final │  true   │  false             │
  │ Well-matched, !final│  false  │  true              │
  │ Not well-matched    │  false  │  false             │
  └─────────────────────┴─────────┴────────────────────┘
```

### Intersection: Product Construction

The product construction runs two VPAs in parallel on the same input.
The key insight is that because both VPAs share the *same* alphabet
partition (same `classify` function), their stacks push and pop in
lockstep. This means the product stack can use paired symbols:

```
  Product state:     (State1 x State2)
  Product stack sym: (StackSym1 x StackSym2)

  On call symbol a:
    VPA1: (q1, stk1) -> (q1', g1 :: stk1)
    VPA2: (q2, stk2) -> (q2', g2 :: stk2)
    Product: ((q1,q2), stk) -> ((q1',q2'), (g1,g2) :: stk)

  On return symbol a:
    Both pop simultaneously -- stacks stay synchronized.

  On internal symbol a:
    Both update state only -- stacks unchanged.
```

The correctness proof uses **projection lemmas** that show the product
run decomposes cleanly into individual runs:

```
Lemma prod_run_proj1 : forall w c,
  proj1_config (prod_run c w) = run (proj1_config c) w.

Lemma prod_run_proj2 : forall w c,
  proj2_config (prod_run c w) = run2 (proj2_config c) w.
```

These are proven by induction on the word `w`, with the step case using
`prod_step_proj1` / `prod_step_proj2` (case analysis on `classify a`).

### Determinization Diagram

General PDAs cannot be determinized because the stack operation depends
on the current state, making the subset construction blow up. VPAs avoid
this because the stack operation is fixed by the input symbol:

```
  General PDA:                    VPA (Input-Driven):

  State determines               Input symbol determines
  push/pop/noop                   push/pop/noop
       │                                │
       v                                v
  ┌──────────┐                   ┌──────────┐
  │ State q1 │──push──>          │ Symbol a │──push──>  (always)
  │ State q2 │──pop───>          │ Symbol b │──pop───>  (always)
  │ State q3 │──noop──>          │ Symbol c │──noop──>  (always)
  └──────────┘                   └──────────┘
       │                                │
  Cannot determinize             Subset construction works:
  (different states do           all states in the powerset
   different stack ops           do the SAME stack op
   on the same input)            on the same input
```

This is why VPAs have the same closure properties as finite automata
but strictly more expressive power.

### Decidable Equivalence: Symmetric Difference

The equivalence decision procedure decomposes into two inclusion checks:

```
L(A1) = L(A2)
  <-> L(A1) \ L(A2) = empty  AND  L(A2) \ L(A1) = empty
  <-> L(A1) cap complement(L(A2)) = empty
      AND  complement(L(A1)) cap L(A2) = empty
```

Each check uses:
1. **Complement** (swap is_final to negb is_final) -- proven sound
2. **Intersection** (product construction) -- proven sound
3. **Emptiness** (reachability on finite state space) -- assumed as oracle

The proof uses the decidable emptiness oracle `Hempty_dec` to check
both symmetric difference directions. If either direction has a witness,
the languages differ. If both are empty, the languages are equal.


## Rust Code Traceability

| Rocq Definition | Rust Counterpart | File |
|----------------|-----------------|------|
| `symbol_kind` (Call/Return/Internal) | `SymbolKind` enum | `vpa.rs:100-110` |
| `classify` | `VpaAlphabet::classify()` | `vpa.rs:75-86` |
| `step` | Single-step VPA transition | `vpa.rs:130-175` |
| `run` | VPA run (fold over word) | `vpa.rs` |
| `accepts` | VPA acceptance predicate | `vpa.rs` |
| `complement_is_final` | `complement()` function | `vpa.rs` |
| `prod_step` / `prod_run` | `intersect()` function | `vpa.rs` |
| `vpa_equivalence_decidable` | `check_vpa_equivalence()` | `vpa.rs` |


## Theoretical References

- Alur, R. & Madhusudan, P. (2004). "Visibly pushdown languages."
  STOC 2004. Introduced VPAs and proved closure under Boolean operations.
- Alur, R. & Madhusudan, P. (2009). "Adding nesting structure to words."
  Extended journal version with additional decidability results.
