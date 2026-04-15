# Temporal Property Checking (LTL Model Checking)

## What Is It?

The temporal property checker verifies Linear Temporal Logic (LTL) formulas over simulation traces. Given a trace of `(term_display, is_normal_form)` pairs and an LTL formula like `F(normal_form)` ("eventually, normal form is reached"), the checker determines whether the property holds or is violated, and if violated, identifies the step where the violation occurs.

Located in `simulation/src/temporal.rs`.

## What Does It Do?

The checker implements the full automata-theoretic LTL model checking pipeline:

1. **Parse** an LTL formula string into an abstract syntax tree.
2. **Evaluate** atomic propositions at each trace step, producing label sets.
3. **Build** a system Buchi automaton from the labeled trace.
4. **Negate** the property formula and compile it to a Buchi automaton.
5. **Intersect** the system and negated-property automata.
6. **Check emptiness** of the product automaton.
7. If non-empty, the property is **violated**; extract the violating step.

## Why Was It Chosen?

### Beyond Invariants

Invariants (see [invariants.md](invariants.md)) check **state properties**: conditions that must hold at each individual step. But many important properties involve relationships between steps:

- "Eventually, normal form is reached" (liveness: F(normal_form))
- "The term size is always bounded" (safety: G(bounded_size))
- "Once normal form is reached, it stays in normal form" (stability: G(normal_form → G(normal_form)))
- "Every intermediate term is parseable until normal form" (bounded liveness: bounded_size U normal_form)

These are **temporal properties**, and LTL is the standard logic for expressing them (Pnueli (1977)).

### Theoretical Foundation

The implementation follows the automata-theoretic approach to LTL model checking pioneered by Vardi and Wolper (1986):

**Theorem (Vardi and Wolper (1986)).** For any LTL formula φ, there exists a Buchi automaton A_φ such that L(A_φ) is exactly the set of infinite words satisfying φ. The automaton has at most 2^|φ| states.

The model checking procedure exploits this: to check whether a system S satisfies φ, compute L(S) ∩ L(¬φ). If this intersection is empty, then S satisfies φ. If non-empty, a counterexample can be extracted.

```
            System trace                    LTL property φ
                │                                 │
                ▼                                 ▼
    ┌──────────────────────┐          ┌─────────────────────┐
    │  Build system Buchi  │          │  Negate: ¬φ         │
    │  automaton A_sys     │          │  Compile to Buchi   │
    │  (all states accept) │          │  automaton A_¬φ     │
    └──────────┬───────────┘          └──────────┬──────────┘
               │                                 │
               └────────────┬────────────────────┘
                            │
                            ▼
                ┌─────────────────────┐
                │  Product automaton  │
                │  A_sys × A_¬φ       │
                └──────────┬──────────┘
                           │
                           ▼
                ┌─────────────────────┐
                │  Emptiness check    │
                │  (nested DFS /      │
                │   SCC detection)    │
                └──────────┬──────────┘
                           │
                    ┌──────┴──────┐
                    │             │
                 Empty         Non-empty
                    │             │
                    ▼             ▼
              φ Satisfied    φ Violated
                            (counterexample
                             extracted)
```

## LTL Syntax

The following temporal operators are supported:

| Operator   | Symbol             | Meaning                             |
|------------|--------------------|-------------------------------------|
| Eventually | `F(φ)`             | φ holds at some future step         |
| Always     | `G(φ)`             | φ holds at every step from now on   |
| Until      | `φ U ψ`            | φ holds at every step until ψ holds |
| Next       | `X(φ)`             | φ holds at the next step            |
| Not        | `!φ` or `¬φ`       | φ does not hold                     |
| And        | `φ & ψ` or `φ ∧ ψ` | both hold                           |
| Or         | `φ | ψ` or `φ ∨ ψ` | at least one holds                  |
| True       | `true`             | always holds                        |
| False      | `false`            | never holds                         |

**Semantic definitions (over infinite word w = w₀w₁w₂...):**

```
w, i ⊨ p             iff  p ∈ label(wᵢ)
w, i ⊨ ¬φ            iff  w, i ⊭ φ
w, i ⊨ φ ∧ ψ         iff  w, i ⊨ φ  and  w, i ⊨ ψ
w, i ⊨ φ ∨ ψ         iff  w, i ⊨ φ  or   w, i ⊨ ψ
w, i ⊨ X(φ)          iff  w, i+1 ⊨ φ
w, i ⊨ F(φ)          iff  ∃ j ≥ i: w, j ⊨ φ
w, i ⊨ G(φ)          iff  ∀ j ≥ i: w, j ⊨ φ
w, i ⊨ φ U ψ         iff  ∃ j ≥ i: w, j ⊨ ψ  and  ∀ k ∈ [i, j): w, k ⊨ φ
```

## Buchi Automata

A Buchi automaton is a nondeterministic finite automaton that accepts **infinite** words. Formally, B = (Q, Σ, δ, Q₀, F) where:

- Q is a finite set of states
- Σ is the input alphabet (sets of atomic propositions)
- δ: Q × Σ → 2^Q is the transition function
- Q₀ ⊆ Q is the set of initial states
- F ⊆ Q is the set of accepting states

An infinite word w = w₀w₁w₂... is accepted by B if there exists an infinite run r = r₀r₁r₂... such that:
- r₀ ∈ Q₀
- rᵢ₊₁ ∈ δ(rᵢ, wᵢ) for all i ≥ 0
- infinitely many rᵢ are in F (the Buchi acceptance condition)

The Buchi acceptance condition captures liveness: the run must visit an accepting state infinitely often. For safety properties (G(φ)), all states are accepting; for liveness (F(φ)), the accepting states are those where φ holds.

## Atomic Propositions

Atomic propositions bridge the gap between the abstract LTL formula and the concrete simulation trace. Each proposition has a name (matching an LTL atom) and an evaluation function:

```rust
pub trait AtomicProposition: Send + Sync {
    fn name(&self) -> &str;
    fn evaluate(&self, term_display: &str, is_normal_form: bool) -> bool;
}
```

### Built-In Propositions

| Proposition         | Name           | Evaluates to `true` when...      |
|---------------------|----------------|----------------------------------|
| `IsNormalForm`      | `normal_form`  | `is_normal_form == true`         |
| `TermSizeBounded`   | `bounded_size` | `term_display.len() ≤ bound`     |
| `ContainsSubstring` | `contains`     | `term_display.contains(pattern)` |

### Custom Propositions

```rust
struct HasZeroProcess;

impl AtomicProposition for HasZeroProcess {
    fn name(&self) -> &str { "has_zero" }
    fn evaluate(&self, term: &str, _: bool) -> bool {
        term.contains("PZero")
    }
}
```

## The Checking Pipeline in Detail

### Step 1: Parse the LTL Formula

The formula string (e.g., `"F(normal_form)"`) is parsed by `ltl::parse_ltl()` from the `mettail-prattail` crate into an `LtlFormula` AST. Parse errors are reported as `LtlCheckResult::ParseError`.

### Step 2: Evaluate Propositions at Each Step

For each trace step `(term_display, is_normal_form)`, the checker evaluates every atomic proposition referenced in the formula:

```
atom_names ← formula.atoms()    // e.g., {"normal_form", "bounded_size"}

label_sets ← FOR (term, is_nf) in trace:
    { name ∈ atom_names : ∃ prop ∈ propositions
        where prop.name() == name AND prop.evaluate(term, is_nf) }
```

### Step 3: Build the System Buchi Automaton

The finite trace is modeled as an infinite word by adding a self-loop on the last state. This models the assumption that the system stays in its final state forever (a standard technique for finite-trace LTL):

```
FOR i in 0..|trace|:
    state[i] ← BuchiAutomaton.add_state(accepting = true)

initial_states ← {state[0]}

FOR i in 0..|trace|:
    next ← if i + 1 < |trace| then state[i+1] else state[i]  // self-loop on last

    // Add transitions for propositions that hold
    add_transition(state[i], "__true__", next)
    FOR prop_name in label_sets[i]:
        add_transition(state[i], prop_name, next)

    // Add negated transitions for propositions that do NOT hold
    FOR atom_name in atom_names:
        IF atom_name ∉ label_sets[i] THEN
            add_transition(state[i], "!" + atom_name, next)
```

All states are accepting because the system automaton should accept all traces (the property checking is done via the negated formula).

### Step 4: Negate and Compile to Buchi

The LTL formula φ is negated to ¬φ, and the negation is compiled to a Buchi automaton A_¬φ. This is done by the `mettail-prattail` crate's `ltl::check_ltl_property()` function, which implements the tableau-based LTL-to-Buchi translation.

### Step 5: Intersection and Emptiness Check

The product automaton A_sys × A_¬φ is computed. If its language is non-empty (there exists an accepting run), the property is violated. The counterexample is extracted as a prefix-lasso pair:

- **Prefix**: the finite sequence of states leading to the accepting cycle
- **Lasso**: the accepting cycle itself

### Step 6: Result

```rust
pub enum LtlCheckResult {
    Satisfied,                              // L(A_sys) ∩ L(A_¬φ) = ∅
    Violated { step: usize, message: String }, // non-empty intersection
    ParseError { message: String },          // formula parsing failed
}
```

## The check_trace_ltl() Function

```rust
pub fn check_trace_ltl(
    trace: &[(String, bool)],            // (term_display, is_normal_form) pairs
    formula_str: &str,                    // e.g., "F(normal_form)"
    propositions: &[Box<dyn AtomicProposition>],
) -> LtlCheckResult
```

**Empty trace handling**: An empty trace is vacuously satisfied. This is consistent with the convention that safety properties hold vacuously when there are no states to check.

**Example usage:**

```rust
let trace = vec![
    ("(AddInt 3 5)".to_string(), false),
    ("(AddInt 3 5)".to_string(), false),
    ("8".to_string(), true),
];

let props: Vec<Box<dyn AtomicProposition>> = vec![
    Box::new(IsNormalForm),
    Box::new(TermSizeBounded { bound: 100 }),
];

match check_trace_ltl(&trace, "F(normal_form)", &props) {
    LtlCheckResult::Satisfied => println!("Property holds!"),
    LtlCheckResult::Violated { step, message } => {
        println!("Violated at step {}: {}", step, message);
    }
    LtlCheckResult::ParseError { message } => {
        println!("Parse error: {}", message);
    }
}
```

## Common LTL Properties for MeTTaIL Languages

| Property    | Formula                            | Meaning                                       |
|-------------|------------------------------------|-----------------------------------------------|
| Termination | `F(normal_form)`                   | Rewriting eventually reaches normal form      |
| Boundedness | `G(bounded_size)`                  | Term size stays bounded throughout            |
| Stability   | `G(normal_form → G(normal_form))`  | Once normal form is reached, it persists      |
| Progress    | `G(¬normal_form → F(normal_form))` | Non-normal terms eventually reach normal form |
| Safety      | `G(¬error)`                        | No error state is ever reached                |

## References

- Pnueli, A. (1977). "The Temporal Logic of Programs." Proceedings of the 18th Annual Symposium on Foundations of Computer Science (FOCS), pp. 46-57.
- Vardi, M.Y. and Wolper, P. (1986). "An Automata-Theoretic Approach to Automatic Program Verification." Proceedings of the 1st Symposium on Logic in Computer Science (LICS), pp. 332-344.
- Baier, C. and Katoen, J.-P. (2008). Principles of Model Checking. MIT Press.
