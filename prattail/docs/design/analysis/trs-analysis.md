# Term Rewriting Systems Analysis

**Feature gate:** `trs-analysis`
**Source files:** `confluence.rs`, `termination.rs`
**Pipeline phase:** 1 (no dependencies)
**Lint codes:** S01--S06

## Rationale

A `language!` specification can contain user-defined rewrite and equation
blocks.  If the resulting term rewriting system (TRS) is not confluent, the
same expression can normalise to two different values depending on the
rewriting strategy -- a source of silent semantic bugs.  If the TRS is not
terminating, normalisation may loop.  Both properties are decidable for
finite, left-linear TRS, which is exactly what PraTTaIL generates.

This document covers the two complementary analyses: confluence via
Knuth-Bendix critical pair detection, and termination via the dependency
pair method.

---

## 1. Confluence via Critical Pairs

### 1.1 Intuition

Two rewrite rules *overlap* when the left-hand side of one unifies with a
non-variable subterm of the other.  At the overlap point, both rules apply,
forking the term into two distinct reducts.  The TRS is **locally
confluent** if and only if every such fork can be joined -- i.e., both
reducts can be reduced to a common term.  Combined with termination
(Section 2), local confluence implies full confluence by Newman's Lemma.

### 1.2 Definitions

**Term** `t ::= x | f(t1, ..., tn)` where `x` is a variable and `f` is a
function symbol of arity `n`.

**Rewrite rule** `l --> r` where `l` is a non-variable term and
`Var(r) subset Var(l)`.

**Substitution** `sigma: Var --> Term`.  Write `sigma(t)` for the result of
applying `sigma` to `t`.

**Most general unifier (MGU)** of `s` and `t` is a substitution `sigma`
such that `sigma(s) = sigma(t)`, and every other unifier `tau` factors
through `sigma`.

**Critical pair** arises from rules `l1 --> r1` and `l2 --> r2` (after
variable renaming to avoid capture) when `l2` unifies with a non-variable
subterm `l1|_p` of `l1` at position `p` via MGU `sigma`.  The critical pair
is `(sigma(r1), sigma(l1[r2]_p))` -- the two terms the overlap forks into.

### 1.3 Algorithm: `detect_critical_pairs`

```
function detect_critical_pairs(rules: [RewriteRule]) -> [CriticalPair]:
    pairs := []
    for i in 0..rules.len():
        for j in 0..rules.len():
            // Rename variables in rule_j to avoid capture
            rule_j' := rename_variables(rules[j], "_R")
            for each non-variable position p in rules[i].lhs:
                subterm := rules[i].lhs|_p
                sigma := unify(subterm, rule_j'.lhs)
                if sigma is Some:
                    term1 := sigma(rules[i].rhs)
                    term2 := sigma(rules[i].lhs[rule_j'.rhs]_p)
                    pairs.push(CriticalPair { term1, term2, i, j, p })
    return pairs
```

The unification subroutine uses Robinson's algorithm with occurs check:

```
function unify(t1: Term, t2: Term) -> Option<Substitution>:
    subst := {}
    worklist := [(t1, t2)]
    while worklist is non-empty:
        (lhs, rhs) := worklist.pop()
        lhs := apply(subst, lhs)
        rhs := apply(subst, rhs)
        if lhs == rhs: continue
        match (lhs, rhs):
            (Var(x), t) | (t, Var(x)) =>
                if occurs(x, t): return None    // occurs check
                subst[x] := t
            (App(f, as), App(g, bs)) =>
                if f != g or |as| != |bs|: return None
                for (a, b) in zip(as, bs):
                    worklist.push((a, b))
    return Some(subst)
```

### 1.4 Joinability Checking

Once critical pairs are collected, each pair `(s, t)` is tested for
joinability: reduce both `s` and `t` to normal form and check equality.

```
function check_joinability(s, t, rules, max_steps) -> JoinabilityResult:
    nf_s := normalise(s, rules, max_steps)
    nf_t := normalise(t, rules, max_steps)
    if nf_s == nf_t:
        return Joinable
    else:
        return NotJoinable { normal_form1: nf_s, normal_form2: nf_t }
```

`normalise` applies rules in a leftmost-outermost strategy, bounded by
`max_steps` to prevent divergence on non-terminating systems.

### 1.5 Confluence Result

```
function check_confluence(rules, max_steps) -> ConfluenceAnalysis:
    pairs := detect_critical_pairs(rules)
    results := [check_joinability(p.term1, p.term2, rules, max_steps)
                for p in pairs]
    non_joinable := count(r in results where r is NotJoinable)
    return ConfluenceAnalysis {
        is_confluent: non_joinable == 0,
        critical_pairs: pairs,
        joinability_results: results,
        non_joinable_count: non_joinable,
    }
```

### 1.6 Diagram: Critical Pair Fork-Join

```
                     l₁
                    ╱   ╲
              rule₁╱     ╲rule₂ (at position p)
                  ╱       ╲
                 ▼         ▼
              σ(r₁)     σ(l₁[r₂]_p)
                 ╲         ╱
            reduce╲       ╱reduce
                   ╲     ╱
                    ▼   ▼
                   nf₁  nf₂
                     │  │
                  Joinable iff nf₁ = nf₂
```

### 1.7 Repair Suggestions

When a critical pair `(s, t)` is not joinable, the repair engine
(`suggest_confluence_repairs`) produces:

- `RepairKind::AddEquation { lhs: nf₁, rhs: nf₂ }` -- orient the
  non-joinable pair as a new rewrite rule
- `RepairKind::FixConfluence` with a description suggesting how to
  restructure rules to avoid the overlap

These appear in S01 lint diagnostics with `[repair: ...]` hints.

---

## 2. Termination via Dependency Pairs

### 2.1 Intuition

A TRS is terminating if every reduction sequence is finite.  The dependency
pair method (Arts & Giesl, 2000) reduces termination to the absence of
infinite *chains* of function calls.  Each recursive call `f(...) -->
... g(...) ...` where both `f` and `g` are defined symbols generates a
dependency pair.  These pairs form a graph; cycles in this graph correspond
to potential non-termination.

### 2.2 Definitions

**Defined symbols** `D = { root(l) | l --> r in R }` -- symbols appearing
at the root of some left-hand side.

**Dependency pair** for rule `l --> r` with `l = f(t1,...,tn)`: for each
subterm `g(s1,...,sm)` of `r` where `g in D`, the pair
`<f#(t1,...,tn), g#(s1,...,sm)>` is generated (the `#` marks distinguish
DP symbols from ordinary ones).

**Dependency graph** has one node per DP and an edge from `<s,t>` to
`<u,v>` whenever `t` and `u` are unifiable (after variable renaming).

**Chain** an infinite sequence of DPs `<s1,t1>, <s2,t2>, ...` such that
consecutive targets and sources are unifiable.  A TRS is non-terminating
iff there exists an infinite chain.

### 2.3 Algorithm: Dependency Pair Extraction

```
function extract_dependency_pairs(rules) -> [DependencyPair]:
    defined := { root(r.lhs) | r in rules, r.lhs is App }
    pairs := []
    for (idx, rule) in rules.enumerate():
        if rule.lhs is Var: continue
        source_marked := mark_root(rule.lhs)   // f -> f#
        for subterm in defined_subterms(rule.rhs, defined):
            target_marked := mark_root(subterm) // g -> g#
            pairs.push(DP { source_marked, target_marked, idx })
    return pairs
```

### 2.4 Algorithm: SCC Decomposition via Tarjan

```
function build_dependency_graph(pairs) -> [DependencyScc]:
    n := pairs.len()
    adj := n x n adjacency matrix
    for i in 0..n:
        for j in 0..n:
            renamed := rename_variables(pairs[j].source, "_R")
            if unify(pairs[i].target, renamed) is Some:
                adj[i][j] := true
    sccs := tarjan_scc(n, adj)
    return sccs with self-loop detection
```

Tarjan's algorithm runs in O(V + E) time, producing strongly connected
components in reverse topological order.

### 2.5 Structural Decrease Check

For each non-trivial SCC (size > 1, or singleton with self-loop), the
subterm criterion is applied:

```
function has_structural_decrease(scc_indices, pairs) -> bool:
    min_arity := min { arity(pairs[i].source) | i in scc_indices }
    for pos in 0..min_arity:
        all_weak := true
        some_strict := false
        for i in scc_indices:
            src_arg := pairs[i].source.args[pos]
            tgt_arg := pairs[i].target.args[pos]
            if src_arg == tgt_arg:
                continue                    // weak decrease (equal)
            else if is_proper_subterm(tgt_arg, src_arg):
                some_strict := true         // strict decrease
            else:
                all_weak := false; break    // no decrease
        if all_weak and some_strict:
            return true                     // position pos witnesses termination
    return false
```

### 2.6 Diagram: Dependency Graph with SCCs

```
         ┌─────────────────────────────────────────┐
         │             Dependency Graph             │
         │                                         │
         │   DP0: <f#(s(x)), f#(x)>  ◀──┐        │
         │         │                     │        │
         │         │  (self-loop:        │        │
         │         │   f#(x) unifies     │        │
         │         │   with f#(s(x_R)))  │        │
         │         └─────────────────────┘        │
         │                                         │
         │   DP1: <g#(x), h#(x)>                  │
         │         │                               │
         │         ▼                               │
         │   DP2: <h#(x), g#(x)>                  │
         │         │                               │
         │         └──────▶ DP1  (mutual cycle)    │
         │                                         │
         │  SCC A = {DP0}  (singleton, self-loop)  │
         │  SCC B = {DP1, DP2}  (mutual recursion) │
         └─────────────────────────────────────────┘
```

SCC A: `f#(s(x)) --> f#(x)` at position 0, `s(x)` strictly decreases to
`x` (proper subterm).  Terminating.

SCC B: `g#(x) <--> h#(x)` -- arguments are identical (`x`), so no strict
decrease at any position.  Potentially non-terminating.

### 2.7 Pipeline Bridge

```rust
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
) -> Option<TerminationResult>
```

Converts `language!` syntax items to rewrite rules via
`confluence::syntax_to_rewrite_rules`, then runs `check_termination`.
Returns `None` for empty rule sets (trivially terminating).

---

## 3. Interaction Between Confluence and Termination

Newman's Lemma states:

> A terminating TRS is confluent if and only if it is locally confluent.

PraTTaIL exploits this by running both analyses and combining results:

- If `check_termination` returns `Terminating` and `check_confluence`
  returns `is_confluent = true`, the TRS is *confluent* (Church-Rosser).
  This means evaluation order does not matter -- all normalisation
  strategies yield the same result.

- If `check_termination` returns `PotentiallyNonTerminating`, the
  confluence result alone does not guarantee global confluence (only local
  confluence).  Lint S03 warns about the specific problematic SCCs.

```
  Terminating ∧ Locally confluent  ⟹  Confluent (Newman)
  Terminating ∧ ¬Locally confluent ⟹  Non-confluent (witness: CP)
  ¬Terminating                     ⟹  Confluence undecidable in general
```

---

## 4. Rust Implementation Notes

### 4.1 Term Representation

```rust
pub enum Term {
    Var(String),
    App { symbol: String, args: Vec<Term> },
}
```

Convenience constructors: `Term::var("x")`, `Term::app("f", vec![...])`,
`Term::constant("a")` (nullary `App`).

### 4.2 Rewrite Rule

```rust
pub struct RewriteRule {
    pub lhs: Term,
    pub rhs: Term,
}
```

### 4.3 Complexity

| Operation                    | Time complexity            |
|------------------------------|----------------------------|
| Dependency pair extraction   | O(n * m)  (n rules, m = max RHS subterms) |
| Unification (single pair)    | O(|t1| + |t2|)            |
| Dependency graph construction| O(d^2 * u)  (d = #DPs, u = unification cost) |
| Tarjan SCC                   | O(d + e)  (d nodes, e edges) |
| Critical pair detection      | O(n^2 * p * u)  (n rules, p = positions per rule) |
| Joinability (single pair)    | O(max_steps * |rules|)    |

---

## 5. References

- D.E. Knuth & P.B. Bendix (1970). "Simple word problems in universal
  algebras." *Computational Problems in Abstract Algebra*, pp. 263--297.
- G. Huet (1980). "Confluent reductions: abstract properties and
  applications to term rewriting systems." *JACM*, 27(4).
- T. Arts & J. Giesl (2000). "Termination of term rewriting using
  dependency pairs." *Theoretical Computer Science*, 236(1--2), pp. 133--178.
- N. Hirokawa & A. Middeldorp (2005). "Automating the dependency pair
  method." *Information and Computation*, 199(1--2), pp. 172--199.
- F. Baader & T. Nipkow (1998). *Term Rewriting and All That*. Cambridge
  University Press.  Chapter 6.
