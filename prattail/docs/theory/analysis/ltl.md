# LTL -- Linear Temporal Logic

| Property | Value |
|----------|-------|
| **Feature gate** | `ltl` |
| **Source file** | `prattail/src/ltl.rs` (~1668 lines) |
| **Pipeline phase** | Temporal property verification |
| **Lint codes** | L01 (`ltl-violated`), L02 (`ltl-verified`) |

## 1. Rationale

PraTTaIL grammars define parsers that process token streams -- infinite execution
traces in the model-checking sense. Temporal properties like "every open delimiter
is eventually closed" (liveness) and "the parser never enters an error state after
a valid prefix" (safety) require a temporal logic for specification and an
automata-theoretic framework for verification. LTL provides the specification
language; compilation to Buchi automata enables emptiness-based model checking.

## 2. Theoretical Foundations

### 2.1. LTL Syntax

**Definition (LTL Formula).** The syntax of LTL over a set of atomic
propositions `AP`:

```
phi ::= true | false | p        (p in AP)
      | not phi | phi and psi | phi or psi | phi -> psi
      | X phi                   (neXt)
      | F phi                   (Finally / Eventually)
      | G phi                   (Globally / Always)
      | phi U psi               (Until)
      | phi R psi               (Release)
      | phi W psi               (Weak Until)
```

### 2.2. LTL Semantics

**Definition (Trace).** A trace `sigma = sigma_0 sigma_1 sigma_2 ...` is an
infinite sequence where each `sigma_i subseteq AP`.

**Definition (Satisfaction).** `sigma, i |= phi` (trace `sigma` at position `i`
satisfies `phi`):

| Formula | Semantics |
|---------|-----------|
| `true` | always satisfied |
| `false` | never satisfied |
| `p` | `p in sigma_i` |
| `not phi` | `sigma, i |/= phi` |
| `phi and psi` | `sigma, i |= phi` and `sigma, i |= psi` |
| `X phi` | `sigma, i+1 |= phi` |
| `F phi` | `exists j >= i: sigma, j |= phi` |
| `G phi` | `for all j >= i: sigma, j |= phi` |
| `phi U psi` | `exists j >= i: sigma, j |= psi` and `for all i <= k < j: sigma, k |= phi` |
| `phi R psi` | `for all j >= i: sigma, j |= psi` or `exists k >= i: sigma, k |= phi` and `for all i <= j <= k: sigma, j |= psi` |
| `phi W psi` | `(phi U psi)` or `G phi` |

### 2.3. LTL to Buchi Compilation

**Theorem (Vardi & Wolper 1986).** For every LTL formula `phi` over `AP`, there
exists a Buchi automaton `A_phi` with at most `2^{O(|phi|)}` states such that
`L(A_phi) = {sigma | sigma |= phi}`.

**Model Checking Reduction.** A system `M` satisfies `phi` iff
`L(M) cap L(A_{not phi}) = emptyset`. Checking emptiness of Buchi automata
is decidable in polynomial time (nested DFS / SCC-based).

### 2.4. GPVW Tableau Algorithm

The GPVW (Gerth, Peled, Vardi, Wolper 1995) algorithm constructs a Buchi
automaton from an LTL formula using a **tableau-based** approach:

1. Compute the **closure** `cl(phi)` -- all subformulas and their negations.
2. Build nodes representing maximally consistent subsets of `cl(phi)`.
3. Add transitions based on the next-state requirements of `X` and `U` operators.
4. Determine accepting states from the `U` obligations: a state is accepting
   for `phi1 U phi2` iff either `phi2` holds or `phi1 U phi2` does not hold
   (the eventuality has been discharged).

## 3. Algorithm Pseudocode

### 3.1. LTL Parser (Recursive Descent)

```
function parse_ltl(input: string) -> LtlFormula:
    tokens := tokenize(input)
    parser := Parser(tokens)
    return parser.parse_implies()

    // Precedence (tightest first):
    //   1. Atoms, parenthesized, true, false
    //   2. Unary prefix: ! X G F
    //   3. U R W (binary, right-associative)
    //   4. && (and)
    //   5. || (or)
    //   6. -> (implies, right-associative)
```

### 3.2. LTL to Buchi (GPVW-style)

```
function ltl_to_buchi(phi: LtlFormula) -> BuchiAutomaton:
    atoms := phi.atoms()
    negated := negate(phi)    // construct Buchi for NOT phi

    // Build the generalized Buchi automaton
    closure := compute_closure(negated)
    nodes := generate_consistent_sets(closure)

    // Add transitions
    for each node n:
        for each successor node n':
            if consistent_transition(n, n', closure):
                add_transition(n, n')

    // Convert generalized Buchi to standard Buchi
    buchi := degeneralize(generalized_buchi)
    return buchi
```

### 3.3. Property Checking

```
function check_ltl_property(system_traces, property: LtlProperty):
    buchi_neg := ltl_to_buchi(negate(property.formula))
    product := system_traces intersect buchi_neg

    if product.is_empty():
        return LtlCheckResult::Satisfied
    else:
        (prefix, lasso) := extract_counterexample(product)
        return LtlCheckResult::Violated(prefix, lasso)
```

## 4. Complexity Analysis

| Operation | Time | Space |
|-----------|------|-------|
| `parse_ltl` | O(n) | O(n) |
| `ltl_to_buchi` (GPVW) | O(2^{|phi|}) | O(2^{|phi|}) |
| `check_ltl_property` (emptiness) | O(|A| * |B|) | O(|A| + |B|) |
| `negate` | O(|phi|) | O(|phi|) |
| `atoms` | O(|phi|) | O(|AP|) |

Where: n = input string length, |phi| = formula size, |A| = system automaton
states, |B| = Buchi automaton states.

## 5. Unicode Diagrams

### 5.1. LTL Compilation Pipeline

```
    LTL formula string
          │
          v
    ┌─────────────┐
    │  parse_ltl() │
    └──────┬──────┘
           │
           v
    ┌─────────────┐
    │ LtlFormula  │
    │   (AST)     │
    └──────┬──────┘
           │
           v
    ┌──────────────┐
    │ ltl_to_buchi()│
    │  (GPVW)      │
    └──────┬───────┘
           │
           v
    ┌──────────────────┐
    │ BuchiAutomaton    │
    └──────┬───────────┘
           │
           v
    ┌───────────────────────┐
    │ check_ltl_property()  │
    └──────────┬────────────┘
               │
      ┌────────┴────────┐
      │                 │
  Satisfied         Violated
      │            (prefix, lasso)
```

### 5.2. LTL Formula AST Example

```
    G(request -> F response)

              Always
                │
            Implies
              / \
        request   Eventually
                      │
                  response
```

### 5.3. Buchi Automaton for F(p)

```
    ┌─────┐  not p   ┌─────┐
    │ q0  │ ─────────>│ q0  │  (self-loop while p does not hold)
    │ (i) │           │     │
    └──┬──┘           └─────┘
       │ p
       v
    ┌─────┐  true    ┌─────┐
    │ q1  │ ─────────>│ q1  │  (accepting self-loop)
    │ (a) │           │     │
    └─────┘           └─────┘

    (i) = initial, (a) = accepting
```

### 5.4. Lasso Counterexample

```
    Trace:  s0 -> s1 -> s2 -> s3 -> s4 -> s2 -> s3 -> s4 -> ...
            ├───── prefix ─────┤├─────── lasso ───────────────┤
                                    ^                    │
                                    └────────────────────┘
```

## 6. PraTTaIL Integration

### 6.1. Pipeline Bridge Functions

- `parse_ltl(input)` -- Recursive descent parser for LTL formula strings.
- `ltl_to_buchi(formula)` -- GPVW-style compilation to Buchi automaton.
- `check_ltl_property(system, property)` -- End-to-end verification.
- `LtlFormula::atoms()` -- Collects all atomic propositions.
- `LtlFormula::not/and/or/next/eventually/always/until` -- Smart constructors.

### 6.2. Lint Emission

- **L01** (`ltl-violated`): Emitted when an LTL property is violated. Severity:
  Warning. Diagnostic includes the property name, the formula, and the
  counterexample trace (prefix + lasso).
- **L02** (`ltl-verified`): Emitted when an LTL property is successfully verified.
  Severity: Info. Confirms that the property holds for all traces.

### 6.3. Repair Integration

Violation traces provide constructive counterexamples. The trace prefix
identifies the shortest path to violation, and the lasso identifies the
repeating pattern. These are surfaced to the user via lint diagnostics
but no automated repair is generated (temporal properties require
design-level fixes).

## 7. Rust Implementation Notes

| Type | Role |
|------|------|
| `LtlFormula` | Recursive enum: True, False, Atom, Not, And, Or, Implies, Next, Eventually, Always, Until, Release, WeakUntil |
| `LtlProperty` | Named property: name, formula, is_safety flag |
| `LtlCheckResult` | Outcome: Satisfied, Violated(prefix, lasso), Inconclusive |
| `LtlToken` | Internal token type for the recursive descent parser |

The parser uses inline tokenization (no separate lexer). Operator precedence is
encoded in the recursive descent structure: `parse_implies` > `parse_or` >
`parse_and` > `parse_until` > `parse_unary` > `parse_atom`.

Release (`R`) and Weak Until (`W`) operators are included for full expressiveness,
even though they can be derived from `U` and `G`.

## 8. Worked Example

**Property:** "Every open parenthesis is eventually closed."

```
LTL formula: G(open_paren -> F close_paren)
```

**Parsing:**
```
parse_ltl("G(open_paren -> F close_paren)")
  -> Always(Implies(Atom("open_paren"), Eventually(Atom("close_paren"))))
```

**Negation for model checking:**
```
not G(open -> F close) = F(open and G(not close))
```

**Buchi automaton for negated formula `F(open and G(not close))`:**
```
State q0 (initial):
  - If not (open and not close): stay in q0
  - If open and not close: go to q1

State q1 (accepting):
  - If not close: stay in q1 (accepting loop)
  - If close: go to dead state q2

State q2 (non-accepting sink):
  - Self-loop on all inputs
```

**Verification against system traces:**
If the product automaton `system x buchi_neg` has an accepting run, the property
is violated. The counterexample shows a trace where an open parenthesis is
followed by infinitely many non-close tokens.

## 9. References

1. Pnueli, A. (1977).
   "The Temporal Logic of Programs."
   *Proc. 18th Annual Symposium on Foundations of Computer Science (FOCS)*,
   pp. 46--57.

2. Vardi, M.Y. & Wolper, P. (1986).
   "An Automata-Theoretic Approach to Automatic Program Verification."
   *Proc. 1st Annual IEEE Symposium on Logic in Computer Science (LICS)*,
   pp. 332--344.

3. Gerth, R., Peled, D., Vardi, M.Y. & Wolper, P. (1995).
   "Simple On-the-Fly Automatic Verification of Linear Temporal Logic."
   *Proc. 15th IFIP WG 6.1 International Symposium on Protocol Specification,
   Testing and Verification (PSTV)*, Chapman & Hall, pp. 3--18.

4. Gastin, P. & Oddoux, D. (2001).
   "Fast LTL to Buchi Automata Translation."
   *Proc. 13th International Conference on Computer Aided Verification (CAV)*,
   LNCS 2102, Springer, pp. 53--65.

5. Baier, C. & Katoen, J.-P. (2008).
   *Principles of Model Checking*. MIT Press. Chapters 5--6.
