# Extended Automata Models

**Source files:** `vpa.rs`, `tree_automaton.rs`, `buchi.rs`, `alternating.rs`
**Pipeline phases:** 2 (VPA, WTA), 4 (Alternating), 5 (Buchi)
**Feature gates:** `vpa`, `tree-automata`, `omega`, `alternating`

## Rationale

Classical finite automata operate on flat strings.  PraTTaIL grammars
produce structured output -- nested delimiters, tree-shaped ASTs, and
potentially infinite execution traces.  Each of these structures requires a
matching automaton model:

- **VPA** (Visibly Pushdown Automata) capture delimiter nesting with
  decidable equivalence and inclusion.
- **WTA** (Weighted Tree Automata) assign semiring-weighted states to AST
  nodes bottom-up, enabling ranked term enumeration.
- **Buchi automata** recognise infinite words, serving as the property
  specification formalism for liveness and fairness.
- **Alternating automata** add universal (conjunctive) branching for
  game-theoretic analysis and CTL model checking.

---

## 1. Visibly Pushdown Automata (`vpa.rs`)

### 1.1 Intuition

A VPA is a pushdown automaton whose stack discipline is determined entirely
by the input.  The input alphabet is partitioned into three disjoint sets:

```
  Sigma = Sigma_call  union  Sigma_return  union  Sigma_internal
```

Call symbols push, return symbols pop, internal symbols leave the stack
unchanged.  This restriction -- the stack height is a function of the input
prefix alone -- yields a class closed under all Boolean operations with
decidable equivalence and inclusion (in polynomial time).

PraTTaIL's structural delimiters `(`, `)`, `{`, `}`, `[`, `]` are natural
call/return symbols.  Keywords and operators are internal symbols.

### 1.2 Formal Definition

A VPA is `A = (Q, Sigma, Gamma, delta, Q0, Qf, gamma_bot)` where:

- `Q` -- finite set of states
- `Sigma = Sigma_c union Sigma_r union Sigma_i` -- partitioned alphabet
- `Gamma` -- stack alphabet (includes bottom-of-stack marker `gamma_bot`)
- `delta = delta_c union delta_r union delta_i`:
  - `delta_c: Q x Sigma_c -> 2^{Q x Gamma}` (push)
  - `delta_r: Q x Sigma_r x Gamma -> 2^Q` (pop)
  - `delta_i: Q x Sigma_i -> 2^Q` (no stack change)
- `Q0 subset Q` -- initial states
- `Qf subset Q` -- final states

### 1.3 Determinization

Unlike general PDA, VPA can always be determinised.  The key construction
uses *summary edges* that compress matched call-return pairs:

```
function determinize_vpa(nfa_vpa) -> det_vpa:
    // States of the DFA are subsets of Q (powerset construction)
    // Stack symbols of the DFA are pairs (source_state_set, pushed_symbol)
    initial_set := epsilon_closure(nfa_vpa.Q0)
    worklist := [initial_set]
    visited := {initial_set}
    det_transitions := {}

    while worklist is non-empty:
        S := worklist.pop()
        for each symbol a in Sigma:
            if a in Sigma_call:
                T := union { delta_c(q, a).states | q in S }
                stack_sym := (S, union { delta_c(q, a).gamma | q in S })
                det_transitions.add_push(S, a, T, stack_sym)
            else if a in Sigma_return:
                // For each possible stack top (S', gamma):
                for each (S', gamma) seen as stack symbol:
                    T := union { delta_r(q, a, gamma) | q in S }
                    det_transitions.add_pop(S, a, (S', gamma), T)
            else:  // internal
                T := union { delta_i(q, a) | q in S }
                det_transitions.add_internal(S, a, T)

            if T not in visited:
                visited.add(T); worklist.push(T)

    return det_vpa
```

### 1.4 Closure Properties

| Property        | VPA      | General PDA |
|-----------------|----------|-------------|
| Union           | Closed   | Closed      |
| Intersection    | Closed   | Not closed  |
| Complement      | Closed   | Not closed  |
| Determinization | Always   | Impossible  |
| Equivalence     | Decidable (PTIME) | Undecidable |
| Inclusion       | Decidable (PTIME) | Undecidable |

### 1.5 Diagram: VPA Stack Discipline

```
  Input:    (   a   (   b   )   c   )
            ▼       ▼       ▼       ▼
  Stack:   [Z]    [Z,A]  [Z,A,B]  [Z,A]  [Z]
            │       │       │       │       │
            push    int     push    pop     pop
            A               B       B       A

  Stack height follows the nesting structure exactly:
  h(w) = #calls(w) - #returns(w) >= 0 at every prefix.
```

### 1.6 Pipeline Bridge

```rust
pub fn analyze_from_bundle(
    categories: &[CategoryInfo],
    all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
) -> Option<VpaAnalysis>
```

Constructs a VPA from the grammar's delimiter structure, performs
determinization, and checks inclusion against a reference VPA derived
from the grammar's category hierarchy.

---

## 2. Weighted Tree Automata (`tree_automaton.rs`)

### 2.1 Intuition

Tree automata generalise finite automata from words (sequences) to trees
(terms).  A bottom-up tree automaton processes a term from leaves to root,
assigning a state to each subterm.  A weighted tree automaton additionally
assigns a semiring weight to each transition, enabling ranked term
enumeration and probabilistic parsing.

### 2.2 Formal Definition

A bottom-up WTA is `A = (Q, F, Sigma, delta, w)` where:

- `Q` -- finite set of states
- `F subset Q` -- final (accepting) states
- `Sigma` -- ranked alphabet (each symbol has a fixed arity)
- `delta` -- transition rules: `f(q1, ..., qn) -> q` for `f` of arity `n`
- `w: delta -> W` -- weight function from a semiring `W`

A run assigns a state to each node bottom-up.  The weight of a run is the
product of all transition weights.  The weight of a term is the sum (over
all accepting runs) of their weights.

### 2.3 Bottom-Up Evaluation

```
function bottom_up_evaluate(term, wta) -> Map<Node, (State, Weight)>:
    assignment := {}
    for each node v in term (post-order traversal):
        if v is a leaf (arity 0):
            for each rule f() -> q with weight w in delta:
                if v.symbol == f:
                    assignment[v] := (q, w)
        else:  // v = f(c1, ..., cn)
            child_states := [assignment[ci].state for ci in children(v)]
            for each rule f(q1,...,qn) -> q with weight w in delta:
                if child_states == [q1,...,qn]:
                    total_weight := w * product(assignment[ci].weight for ci)
                    assignment[v] := (q, total_weight)
    return assignment
```

### 2.4 Myhill-Nerode Minimization

Two states `q1`, `q2` are equivalent if they accept the same set of
contexts (terms with a hole).  The Myhill-Nerode equivalence classes define
the minimal WTA:

```
function minimize_wta(wta) -> minimal_wta:
    // Partition states by finality
    partition := [F, Q \ F]
    changed := true
    while changed:
        changed := false
        new_partition := []
        for each block B in partition:
            // Split B by transition behavior w.r.t. current partition
            signatures := { q -> [block_of(delta(q, ...)) for each context] | q in B }
            sub_blocks := group_by(signatures)
            if |sub_blocks| > 1:
                changed := true
            new_partition.extend(sub_blocks)
        partition := new_partition
    // Build minimal automaton from equivalence classes
    return build_from_partition(wta, partition)
```

### 2.5 Diagram: WTA Bottom-Up State Assignment

```
  Term:            Add
                  ╱    ╲
               Mul      Num(3)
              ╱    ╲
          Num(1)  Num(2)

  Bottom-up evaluation (states q_val, q_expr):

  Step 1: Num(1) -> q_val [w=1.0]
  Step 2: Num(2) -> q_val [w=1.0]
  Step 3: Num(3) -> q_val [w=1.0]
  Step 4: Mul(q_val, q_val) -> q_expr [w=0.8]
  Step 5: Add(q_expr, q_val) -> q_expr [w=0.9]

  Total weight = 1.0 * 1.0 * 1.0 * 0.8 * 0.9 = 0.72
```

---

## 3. Buchi Automata (`buchi.rs`)

### 3.1 Intuition

Buchi automata extend finite automata to infinite words.  A run over an
infinite word `w = a0 a1 a2 ...` is accepting if it visits some accepting
state infinitely often.  This captures liveness properties: "something
good happens infinitely often."

### 3.2 Formal Definition

A nondeterministic Buchi automaton (NBA) is `A = (Q, Sigma, delta, Q0, F)`
where:

- `Q` -- finite set of states
- `Sigma` -- input alphabet
- `delta: Q x Sigma -> 2^Q` -- nondeterministic transition function
- `Q0 subset Q` -- initial states
- `F subset Q` -- accepting states

A run `rho = q0 q1 q2 ...` on infinite word `w = a0 a1 a2 ...` is
accepting iff `inf(rho) intersect F != emptyset`, where `inf(rho)` is the
set of states appearing infinitely often.

### 3.3 Product Construction (Intersection)

To check `L(A) intersect L(B) != emptyset`, construct the product automaton
using the 3-counter construction:

Product state = `(q1, q2, phase)` where `phase in {0, 1, 2}`:

```
  Phase 0: waiting for A to accept (scanning for q1 in F_A)
  Phase 1: A accepted, now waiting for B (scanning for q2 in F_B)
  Phase 2: both accepted -- this is the accepting phase; reset to 0

  Transition (q1, q2, c) --a--> (q1', q2', c'):
    q1 --a--> q1' in A,  q2 --a--> q2' in B, and:
      c == 0 and q1 in F_A  =>  c' = 1
      c == 1 and q2 in F_B  =>  c' = 2
      c == 2               =>  c' = 0
      otherwise            =>  c' = c

  Product accepts in phase-2 states.
  Size: |Q_A| * |Q_B| * 3
```

### 3.4 Emptiness Check via SCC

A Buchi automaton is non-empty iff there exists a reachable SCC containing
at least one accepting state and at least one edge (guaranteeing infinite
repetition):

```
function check_emptiness(buchi) -> bool:
    reachable := BFS from initial_states
    adj := adjacency list restricted to reachable states
    sccs := tarjan_scc(adj)
    for each scc in sccs:
        has_cycle := |scc| > 1 or (|scc| == 1 and has_self_loop(scc[0]))
        has_accepting := any(s in scc where s in F)
        if has_cycle and has_accepting:
            return false  // non-empty
    return true  // empty
```

### 3.5 Diagram: Buchi Product Construction

```
  Automaton A:              Automaton B:
  q0 --a--> q1* --b--> q0  q0 --a--> q1 --b--> q0*

  Product (3-counter):
  (q0,q0,0) --a--> (q1,q1,0)    // q0 not in F_A, stay phase 0
  (q1,q1,0) --b--> (q0,q0,1)    // q1 in F_A, advance to phase 1
  (q0,q0,1) --a--> (q1,q1,1)    // q0 not in F_B, stay phase 1
  (q1,q1,1) --b--> (q0,q0,2)    // q0 in F_B, advance to phase 2 (accepting)
  (q0,q0,2) --a--> (q1,q1,0)    // phase 2 -> reset to 0

  SCC: {(q0,q0,0), (q1,q1,0), (q0,q0,1), (q1,q1,1), (q0,q0,2), (q1,q1,0)}
  Contains accepting state (q0,q0,2) -> NON-EMPTY
  -> L(A) intersect L(B) != emptyset
```

### 3.6 Pipeline Bridge

`from_wpds` converts the WPDS call graph into a Buchi automaton:

- Each category becomes a state
- Call-graph edges become transitions
- Primary categories (zero fan-in) are accepting states and initial states

This enables liveness checking: "every recursive grammar category is
entered infinitely often in any infinite parse."

---

## 4. Alternating Automata (`alternating.rs`)

### 4.1 Intuition

Standard NFA transitions are existential: "there exists a successor that
accepts."  Alternating automata add universal transitions: "all successors
must accept."  This duality models game semantics -- an existential state
is controlled by the "system" (trying to accept), a universal state by the
"environment" (trying to reject).

### 4.2 Formal Definition

An alternating parity automaton is `A = (Q, Sigma, delta, q0, Omega)`:

- `Q = Q_E union Q_A` -- existential and universal states
- `delta: Q x Sigma -> 2^Q` -- transition function
- `q0` -- initial state
- `Omega: Q -> N` -- priority function (even = accepting, odd = rejecting)

A run is a tree (not a sequence).  At existential states, the run branches
to one successor set.  At universal states, it branches to all successor
sets.  Acceptance uses the parity condition: a branch is accepting iff the
minimum priority visited infinitely often is even.

### 4.3 Emptiness via Fixpoint

For finite-word semantics, emptiness reduces to a backward fixpoint:

```
function check_emptiness(automaton) -> bool:
    accepting := [false; num_states]
    // Initialize leaves: even priority with no transitions -> accepting
    for s in 0..num_states:
        if no_transitions_from(s):
            accepting[s] := (priority(s) % 2 == 0)
    // Fixpoint propagation
    changed := true
    while changed:
        changed := false
        for s in 0..num_states:
            if accepting[s]: continue
            match branching(s):
                Existential =>
                    // At least one transition leads to all-accepting successors
                    new := any(t in transitions(s) where
                               all(succ in t.successors where accepting[succ]))
                Universal =>
                    // ALL transitions lead to all-accepting successors
                    new := all(t in transitions(s) where
                               all(succ in t.successors where accepting[succ]))
            if new and not accepting[s]:
                accepting[s] := true; changed := true
    return not accepting[initial_state]
```

### 4.4 Bisimulation Game

Two alternating automata are language-equivalent iff the Defender wins the
bisimulation game from the initial position `(q0_A, q0_B)`:

```
  Game position: (state_in_A, state_in_B)

  Attacker moves:
    1. Pick a transition in A (or B) on some label
    2. Defender must match it with a transition on the same label in B (or A)
    3. If Defender cannot match: Attacker wins (not bisimilar)
    4. If the game continues forever: Defender wins (bisimilar)
```

The implementation uses attractor computation:

```
function bisimulation_game(A, B) -> bool:
    attacker_wins := [false; |Q_A| * |Q_B|]
    // Phase 1: immediate Attacker wins (unmatched labels)
    for (pa, pb) in Q_A x Q_B:
        a_labels := labels_from(A, pa)
        b_labels := labels_from(B, pb)
        if a_labels \ b_labels != emptyset or b_labels \ a_labels != emptyset:
            attacker_wins[pa, pb] := true
    // Phase 2: backward propagation until fixpoint
    propagate_attacker_wins(attacker_wins, A, B)
    return not attacker_wins[init_A, init_B]
```

### 4.5 Diagram: Alternating Automaton

```
  q0 [E, p=0]                     E = Existential (player picks one)
     │                             A = Universal (all must work)
     ├──a──▶ {q1, q2}
     │
  q1 [A, p=1]                     Universal: BOTH successors must accept
     │
     ├──b──▶ {q3}
     ├──c──▶ {q4}
     │
  q2 [E, p=0]                     Existential: EITHER successor suffices
     │
     └──d──▶ {q3}

  q3 [E, p=0]  (leaf, even priority -> accepting)
  q4 [E, p=1]  (leaf, odd priority -> rejecting)

  q1 is universal: needs BOTH b->q3 and c->q4 to accept.
  But q4 is rejecting, so q1 does NOT accept.
  q0 needs q1 AND q2 to accept (transition to {q1,q2}).
  Since q1 does not accept, the language is EMPTY.
```

### 4.6 Pipeline Bridge

`analyze_from_bundle` builds one alternating automaton per grammar category:

- Root state: existential (parser tries alternative rules)
- Per-rule state: universal (all syntax items must match)
- Per-item state: existential (leaf)

Then runs pairwise bisimulation checks to identify non-bisimilar category
pairs, surfaced as N05 lint diagnostics.

---

## 5. References

- R. Alur & P. Madhusudan (2004). "Visibly pushdown languages." *STOC
  2004*, pp. 202--211.
- R. Alur & P. Madhusudan (2009). "Adding nesting structure to words."
  *JACM*, 56(3).
- J.W. Thatcher & J.B. Wright (1968). "Generalized finite automata theory
  with an application to a decision problem of second-order logic."
  *Mathematical Systems Theory*, 2(1).
- H. Comon, M. Dauchet, R. Gilleron, C. Loding, F. Jacquemard,
  D. Lugiez, S. Tison & M. Tommasi (2007). *Tree Automata Techniques and
  Applications* (TATA).
- J.R. Buchi (1962). "On a decision method in restricted second order
  arithmetic." *Proc. Internat. Congr. Logic, Method. and Philos. Sci.*
- M.Y. Vardi & P. Wolper (1994). "Reasoning about infinite computations."
  *Information and Computation*, 115(1).
- A.K. Chandra, D.C. Kozen & L.J. Stockmeyer (1981). "Alternation."
  *JACM*, 28(1), pp. 114--133.
- O. Kupferman & M.Y. Vardi (2001). "Weak alternating automata are not
  that weak." *ACM Trans. Comp. Logic*, 2(3).
- M. Jurdzinski (2000). "Small progress measures for solving parity
  games." *STACS 2000*, LNCS 1770.
