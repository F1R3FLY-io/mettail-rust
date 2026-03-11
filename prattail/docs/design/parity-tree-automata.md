# Parity Alternating Tree Automata -- Mu-Calculus Model Checking over Parse Trees

## Quick Start

Parity Alternating Tree Automata (PATA) extend alternating automata from words to trees (terms). A PATA processes a term from root to leaves, using existential (disjunctive) and universal (conjunctive) branching to navigate child subtrees. The parity acceptance condition generalizes Buchi acceptance: a run is accepting iff the minimum priority visited infinitely often along every path is even. This module provides `ParityAlternatingTreeAutomaton<W>`, a mu-calculus formula compiler `mu_calculus_to_pata()`, emptiness checking via parity game reduction, term evaluation, and inclusion checking via complement + product + emptiness.

**Motivating example**: In PraTTaIL, the property "every function application has a well-typed argument in some child position" is a mu-calculus formula: `nu X. (Atom("apply") => Diamond{1, typed}) /\ Box{0, X} /\ Box{1, X}`. This formula compiles to a PATA that can be checked against concrete parse trees via `evaluate_term()` or verified structurally via `check_emptiness()`.

```
Mu-calculus formula
      |
      v
mu_calculus_to_pata()
      |
      v
ParityAlternatingTreeAutomaton<W>
      |
      +---> check_emptiness()     (parity game reduction)
      +---> evaluate_term()       (bottom-up evaluation on concrete terms)
      +---> check_inclusion()     (complement + product + emptiness)
```

## Intuition

Think of a PATA as a team of inspectors auditing a corporate hierarchy chart (a tree). At each department (node), the chief inspector (universal state) demands that *all* sub-departments pass inspection, while the assistant inspector (existential state) is satisfied if *at least one* sub-department passes. The priority system tracks how deeply nested the inspection is -- even priorities mark satisfactory checkpoints, odd priorities flag issues that must eventually resolve. The mu-calculus formulas encode which inspections to perform at which positions.

**Before this module**: Tree-structured properties of parse trees were checked by ad-hoc recursive visitors without formal semantics or compositional reasoning.

**After this module**: Tree properties are expressed as mu-calculus formulas and compiled to PATAs with formal parity acceptance, enabling systematic emptiness checking, term evaluation, and inclusion verification.

**Key insight**: The mu-calculus is equi-expressive with alternating tree automata with parity acceptance (Emerson & Jutla 1991). Every mu-calculus formula can be compiled to a PATA and vice versa, providing both a logical specification language and an automata-theoretic verification engine.

## Theoretical Foundations

**Definition 5.1 (Parity Alternating Tree Automaton).** A PATA is a tuple `A = (Q_E, Q_A, Sigma, delta, q_0, Omega, k)` where:
- `Q = Q_E ∪ Q_A` partitions states into existential and universal
- `Sigma` is the ranked alphabet (each symbol has an arity)
- `delta: Q x Sigma -> B+(Dir x Q)` maps states and symbols to positive Boolean combinations of direction-state pairs
- `q_0` is the initial state
- `Omega: Q -> N` is the priority function (even = accepting, odd = rejecting)
- `k` is the maximum arity (branching factor)

**Definition 5.2 (Term).** A term (tree) over ranked alphabet `Sigma` is a labeled, ranked tree. Each node has a symbol `f in Sigma` and `arity(f)` children. Leaves have arity 0.

**Definition 5.3 (Mu-Calculus Formula).** The modal mu-calculus extends propositional logic with:
- Modal operators: `Diamond{k, phi}` ("some k-th child satisfies phi"), `Box{k, phi}` ("all k-th children satisfy phi")
- Fixpoint operators: `Mu{X, phi}` (least fixpoint -- liveness), `Nu{X, phi}` (greatest fixpoint -- safety)

Semantics over tree `T` and environment `rho`:
- `[[True]]_rho` = all nodes
- `[[Atom(a)]]_rho` = {nodes labeled `a`}
- `[[Diamond{k, phi}]]_rho` = {nodes whose k-th child is in `[[phi]]_rho`}
- `[[Box{k, phi}]]_rho` = {nodes whose all k-th children are in `[[phi]]_rho`}
- `[[Mu{X, phi}]]_rho` = least fixpoint of `S -> [[phi]]_rho[X:=S]`
- `[[Nu{X, phi}]]_rho` = greatest fixpoint of `S -> [[phi]]_rho[X:=S]`

**Theorem 5.1 (Emerson & Jutla 1991).** The modal mu-calculus and alternating tree automata with parity acceptance are equi-expressive. Model checking a mu-calculus formula against a finite tree is decidable in time polynomial in the tree and exponential in the alternation depth.

**Theorem 5.2 (Complementation via Duality).** For alternating automata, complementation is obtained by:
1. Swapping existential and universal branching modes
2. Incrementing all priorities by 1 (flipping even/odd parity)

This exploits the duality of alternation (Emerson & Jutla 1991).

## Activation: Recursive + Branching → M5

M5 (Parity Tree) is activated by predicate dispatch when the grammar or its
predicates indicate ranked tree structure requiring mu-calculus fixpoint analysis.

```
Grammar Rules                     Predicate Expressions
      │                                 │
      ▼                                 ▼
classify_grammar()               extract_features() / walk_mso()
      │                                 │
      ▼                                 ▼
DirectRecursion(C)               is_fixpoint_relation()
    AND                            with has_recursive = true
HighBranching(≥3)
      │                                 │
      └──────────┬──────────────────────┘
                 ▼
        M5_PARITY_TREE bit set
```

**Grammar heuristic**: Both direct recursion AND high branching (≥3 non-terminals)
must be present in the grammar. Recursion alone gives linear chains (→ M2 Büchi);
branching alone gives flat structures (→ M3 AWA). Only their combination creates
the ranked tree structure that parity tree automata are designed to analyze.

**Predicate trigger**: Fixpoint relations (`mu`, `nu`, `fixpoint`, `letrec`, etc.)
combined with the `has_recursive_predicate` flag.

**Example grammar rule triggering M5**:
```
("TreeNode", "Tree", [NT("Tree","left"), NT("Tree","mid"), NT("Tree","right")])
   ↑ recursive (Tree→Tree) + branching (3 NTs) → M5 activated
```

**Theoretical justification**: Recursive categories with branching children form
ranked trees. Properties over these trees (mu-calculus formulas like `μX. φ(X)`)
require parity acceptance conditions on infinite branches through the tree —
precisely what PATA provides. Linear recursion (Büchi) and flat branching (AWA)
are insufficient for the interplay of both dimensions.

## Design

### Core types

```rust
pub struct ParityTreeState {
    pub id: usize,
    pub branching: BranchingMode,   // Existential or Universal
    pub priority: u32,              // even = accepting, odd = rejecting
    pub label: Option<String>,
}

pub struct ParityTreeTransition<W: Semiring> {
    pub from: usize,
    pub symbol: String,
    pub directions: Vec<(usize, usize, W)>,  // (child_index, target_state, weight)
}

pub struct Term {
    pub symbol: String,
    pub children: Vec<Term>,
}

pub struct ParityAlternatingTreeAutomaton<W: Semiring> {
    pub states: Vec<ParityTreeState>,
    pub alphabet: HashSet<String>,
    pub transitions: Vec<ParityTreeTransition<W>>,
    pub initial_state: Option<usize>,
    pub max_arity: usize,
}

pub enum MuCalculusFormula {
    Var(String),
    True,
    False,
    Atom(String),
    Not(Box<MuCalculusFormula>),
    And(Box<MuCalculusFormula>, Box<MuCalculusFormula>),
    Or(Box<MuCalculusFormula>, Box<MuCalculusFormula>),
    Diamond { child_idx: usize, body: Box<MuCalculusFormula> },
    Box { child_idx: usize, body: Box<MuCalculusFormula> },
    Mu { var: String, body: Box<MuCalculusFormula> },
    Nu { var: String, body: Box<MuCalculusFormula> },
}
```

### Formula-to-automaton compilation diagram

```
  MuCalculusFormula            ParityAlternatingTreeAutomaton
  +-------------+              +---------------------------+
  | mu X.       |    compile   | q0 [E, p=1] (mu:X)       |
  |   Atom("f") | ----------> | q1 [E, p=0] (atom:f)     |
  |   /\ Box{0, |              | q2 [A, p=0] (box:0:q3)   |
  |       X}    |              |   q0 --_mu_X--> q1        |
  +-------------+              |   q2 --_box_0--> q0       |
                               +---------------------------+
```

## Algorithms

### Emptiness Check (Parity Game Reduction)

```
Input:  ParityAlternatingTreeAutomaton<BooleanWeight>
Output: true if L(automaton) = emptyset

1. Initialize accepting[s] for all states:
   - Even priority => accepting[s] = true (accepting checkpoint)
   - Odd priority => accepting[s] = false
2. Fixpoint iteration:
   For each non-accepting state s with transitions:
     transition_satisfied(targets) =
       if targets empty: even_priority(s)
       else: all targets t < n and accepting[t]
     If Existential: new = any transition satisfied
     If Universal:   new = all transitions satisfied
     If new: accepting[s] = true; changed = true
3. Return !accepting[initial_state]
```

**Complexity**: O(|Q|^2 * |delta|) worst case for fixpoint convergence.

### Term Evaluation (Bottom-Up)

```
Input:  PATA, Term
Output: true if the initial state accepts the term

1. Recursively evaluate each child subtree:
   child_results[i] = set of states that accept child i
2. For each state s, check transitions matching term.symbol:
   If Existential: some transition has all directions satisfied
   If Universal:   all transitions have all directions satisfied
   Direction (child_idx, target, weight) is satisfied iff
     target in child_results[child_idx]
3. Return initial_state in accepting_states(root_term)
```

**Complexity**: O(|T| * |Q| * |delta|) where |T| is the number of nodes in the term.

### Mu-Calculus to PATA Compilation

```
Input:  MuCalculusFormula, max_arity
Output: ParityAlternatingTreeAutomaton<BooleanWeight>

compile(formula):
  True  => existential state, priority 0 (accepting leaf)
  False => existential state, priority 1 (rejecting leaf)
  Atom(a) => existential state + transition on symbol a with empty directions
  Not(phi) => compile(phi), then flip branching + priority parity
  And(phi, psi) => universal state branching to compile(phi) and compile(psi)
  Or(phi, psi)  => existential state branching to compile(phi) and compile(psi)
  Diamond{k, phi} => existential state, direction (k, compile(phi), 1)
  Box{k, phi}     => universal state, direction (k, compile(phi), 1)
  Mu{X, phi} => odd priority (liveness), bind X, compile(phi), wire
  Nu{X, phi} => even priority (safety), bind X, compile(phi), wire
```

### Inclusion Check

```
Input:  PATA A, PATA B
Output: true if L(A) ⊆ L(B)

1. Complement B: flip branching, increment priorities
2. Intersect A with complement(B) via product construction
3. check_emptiness(product)
```

## Integration

- **Alternating module** (`alternating.rs`): Shares `BranchingMode` enum. PATA extends alternation from words to trees.
- **Pipeline** (`pipeline.rs`): `ParityTreeAnalysis` reports state count, priority depth, and emptiness.
- **LTL module** (`ltl.rs`): Temporal properties on linear structures compile to alternating word automata; tree properties compile to PATAs.

## Diagnostics

No dedicated lint codes. The `ParityTreeAnalysis` report includes:
- `num_states`: Size of the compiled PATA
- `max_priority`: Maximum priority across all states (bounds alternation depth)
- `is_empty`: Whether the tree language is empty
- `priority_depth`: Number of distinct priority levels (bounds mu-calculus alternation)

## Examples

### Example 1: Atom matching on a term

```rust
let mut pata = ParityAlternatingTreeAutomaton::<BooleanWeight>::new(2);
let q0 = pata.add_state(BranchingMode::Existential, 0, Some("atom:f".into()));
pata.initial_state = Some(q0);
pata.add_transition(q0, "f".to_string(), vec![]);

let term = Term::leaf("f");
assert!(evaluate_term(&pata, &term));     // f matches atom:f

let term_g = Term::leaf("g");
assert!(!evaluate_term(&pata, &term_g));  // g does not match atom:f
```

### Example 2: Mu-calculus formula compilation

```rust
// "every node labeled 'f' has some child satisfying property p"
let formula = MuCalculusFormula::Nu {
    var: "X".into(),
    body: Box::new(MuCalculusFormula::And(
        Box::new(MuCalculusFormula::Or(
            Box::new(MuCalculusFormula::Not(
                Box::new(MuCalculusFormula::Atom("f".into()))
            )),
            Box::new(MuCalculusFormula::Diamond {
                child_idx: 0,
                body: Box::new(MuCalculusFormula::Atom("p".into())),
            }),
        )),
        Box::new(MuCalculusFormula::Box {
            child_idx: 0,
            body: Box::new(MuCalculusFormula::Var("X".into())),
        }),
    )),
};

let pata = mu_calculus_to_pata(&formula, 2);
assert!(!check_emptiness(&pata)); // non-empty: some trees satisfy this
```

### Example 3: Inclusion check

```rust
// A accepts trees with label "a" at root
// B accepts all trees => L(A) ⊆ L(B) should be true
let mut a = ParityAlternatingTreeAutomaton::<BooleanWeight>::new(0);
let qa = a.add_state(BranchingMode::Existential, 0, None);
a.initial_state = Some(qa);
a.add_transition(qa, "a".into(), vec![]);

let mut b = ParityAlternatingTreeAutomaton::<BooleanWeight>::new(0);
let qb = b.add_state(BranchingMode::Existential, 0, None);
b.initial_state = Some(qb);
// b accepts all symbols (no transitions needed; even priority leaf)

assert!(check_inclusion(&a, &b)); // L(A) ⊆ L(B)
```

## Advanced Topics

**Edge cases**: An automaton with no initial state has empty tree language. Invalid state IDs (>= num_states) in transitions are treated as rejecting. A `Term` with no children is a leaf -- matching transitions with empty direction lists.

**Interaction with other modules**: The `BranchingMode` enum is shared with the alternating word automaton module (`alternating.rs`). The parity condition connects to the WPDS module's call-graph analysis.

**Performance**: Emptiness checking is polynomial (fixpoint on |Q| states). Term evaluation is linear in the term size. Mu-calculus compilation produces O(|formula|) states. Inclusion checking requires complementation (trivial for alternating automata) and product construction.

**Future extensions**: Integration with the CEGAR refinement loop for lazy emptiness checking on large PATAs generated from complex mu-calculus specifications.

## Reference

### API Table

| Function | Input | Output | Complexity |
|----------|-------|--------|------------|
| `check_emptiness(pata)` | `PATA<BooleanWeight>` | `bool` | O(\|Q\|^2 * \|delta\|) |
| `evaluate_term(pata, term)` | PATA + Term | `bool` | O(\|T\| * \|Q\| * \|delta\|) |
| `mu_calculus_to_pata(formula, arity)` | formula + usize | `PATA<BooleanWeight>` | O(\|formula\|) |
| `check_inclusion(a, b)` | two PATAs | `bool` | O(\|Q_A\|*\|Q_B\| * \|delta\|) |
| `complement(pata)` | `PATA<BooleanWeight>` | `PATA<BooleanWeight>` | O(\|Q\| + \|delta\|) |
| `intersect(a, b)` | two PATAs | `PATA<BooleanWeight>` | O(\|Q_A\|*\|Q_B\| * \|delta\|) |
| `analyze_from_bundle(...)` | grammar data | `ParityTreeAnalysis` | O(\|categories\|) |

### Feature gate

Always available (core module).

### Citations

- Emerson, E.A. & Jutla, C.S. (1991). "Tree automata, mu-calculus and determinacy." *FOCS 1991*, 368--377.
- Zielonka, W. (1998). "Infinite games on finitely coloured graphs with applications to automata on infinite trees." *TCS*, 200(1-2), 135--183.
- Muller, D.E. & Schupp, P.E. (1995). "Simulating alternating tree automata by nondeterministic automata." *TCS*, 141(1-2), 69--107.
- Bradfield, J. & Stirling, C. (2006). "Modal mu-calculi." In *Handbook of Modal Logic*, Elsevier, 721--756.
