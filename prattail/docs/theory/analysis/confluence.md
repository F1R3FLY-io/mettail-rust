# TRS Confluence Analysis

| Property | Value |
|----------|-------|
| **Feature gate** | `trs-analysis` |
| **Source file** | `prattail/src/confluence.rs` (~1640 lines) |
| **Pipeline phase** | Grammar equation verification |
| **Lint codes** | T01 (`non-joinable`), T02 (`verified`) |

## 1. Rationale

PraTTaIL's `language!` macro allows users to define rewrite and equation blocks
that specify term transformations. These define a Term Rewriting System (TRS).
For the TRS to be well-behaved, it must be **confluent** (Church-Rosser): every
term has at most one normal form, regardless of the order in which rules are
applied. Non-confluence means ambiguous rewriting -- different evaluation orders
produce different results. The Knuth-Bendix criterion detects non-confluence by
computing **critical pairs** (overlapping rule applications) and checking
whether they can be **joined** (reduced to a common reduct).

## 2. Theoretical Foundations

### 2.1. Term Rewriting Systems

**Definition (TRS).** A Term Rewriting System is a pair `(Sigma, R)` where:
- `Sigma` is a ranked alphabet (function symbols with arities)
- `R` is a finite set of rewrite rules `l -> r` where:
  - `l` is not a variable
  - `Var(r) subseteq Var(l)` (no new variables in the right-hand side)

**Definition (Term).** Terms over `(Sigma, X)` where `X` is a set of variables:
```
t ::= x         (variable, x in X)
    | f(t_1, ..., t_n)  (application, f in Sigma with arity n)
```

**Definition (Rewrite Step).** `s ->_R t` if there exists a rule `l -> r` in `R`,
a position `p` in `s`, and a substitution `sigma` such that:
- `s|_p = l * sigma` (the subterm at position p matches the LHS)
- `t = s[r * sigma]_p` (replace the subterm with the instantiated RHS)

### 2.2. Confluence

**Definition (Confluence).** A TRS `R` is **confluent** iff for all terms `s`:
if `s ->*_R t_1` and `s ->*_R t_2`, then there exists a term `u` such that
`t_1 ->*_R u` and `t_2 ->*_R u`.

```
           s
          / \
    ->*  /   \  ->*
        /     \
      t_1     t_2
        \     /
    ->*  \   /  ->*
          \ /
           u
```

**Theorem (Newman's Lemma).** A terminating TRS is confluent iff it is
**locally confluent**: for all terms `s`, if `s ->_R t_1` and `s ->_R t_2`
(single steps), then `t_1` and `t_2` are joinable.

### 2.3. Critical Pairs

**Definition (Overlap).** Rules `l_1 -> r_1` and `l_2 -> r_2` **overlap** at
position `p` in `l_2` if there exists a most general unifier `sigma` of `l_1`
and `l_2|_p` (where `l_2|_p` is a non-variable subterm of `l_2`).

**Definition (Critical Pair).** Given an overlap at position `p` with unifier
`sigma`, the critical pair is `(r_1 * sigma, (l_2[r_1 * sigma]_p) ->_R ... )`.
More precisely:
- `term_1 = r_1 * sigma` (applying rule 1 at the overlap)
- `term_2 = r_2 * sigma` (applying rule 2 at the root)

**Theorem (Knuth-Bendix Criterion).** A terminating TRS is confluent iff all
critical pairs are joinable. That is, for every critical pair `(s, t)`, there
exists a term `u` such that `s ->*_R u` and `t ->*_R u`.

### 2.4. Unification

**Definition (Most General Unifier).** A substitution `sigma` is a **most
general unifier (MGU)** of terms `s` and `t` if `s * sigma = t * sigma` and
for every other unifier `tau`, there exists a substitution `rho` such that
`tau = sigma * rho`.

The unification algorithm runs in O(n * alpha(n)) time using union-find
(Martelli-Montanari), where `n` is the size of the terms.

## 3. Algorithm Pseudocode

### 3.1. Critical Pair Detection

```
function detect_critical_pairs(rules: [RewriteRule]) -> [CriticalPair]:
    pairs := []
    for (i, rule_i) in rules:
        lhs_i' := rename_variables(rule_i.lhs, "'")   // avoid capture
        rhs_i' := rename_variables(rule_i.rhs, "'")

        for (j, rule_j) in rules:
            positions := non_var_positions(rule_j.lhs)
            for pos in positions:
                // Skip trivial self-overlap at root
                if i == j and pos is empty: continue

                subterm := rule_j.lhs |_pos
                if sigma := unify(lhs_i', subterm):
                    term1 := rhs_i'.apply(sigma)
                    term2 := rule_j.rhs.apply(sigma)
                    pairs.push(CriticalPair(term1, term2, i, j, pos))

    return pairs
```

### 3.2. Joinability Check

```
function check_joinability(pair: CriticalPair, rules, max_steps) -> Result:
    (nf1, reached1) := normalize(pair.term1, rules, max_steps)
    (nf2, reached2) := normalize(pair.term2, rules, max_steps)

    if nf1 == nf2:
        return Joinable(common_reduct: nf1)
    if reached1 and reached2:
        return NotJoinable(nf1, nf2)
    return Unknown("reduction limit exceeded")
```

### 3.3. Full Confluence Analysis

```
function check_confluence(rules, max_steps) -> ConfluenceAnalysis:
    critical_pairs := detect_critical_pairs(rules)
    results := [check_joinability(cp, rules, max_steps) for cp in critical_pairs]

    non_joinable := count NotJoinable in results
    unknown := count Unknown in results
    is_confluent := non_joinable == 0 and unknown == 0

    return ConfluenceAnalysis(is_confluent, critical_pairs, results, ...)
```

## 4. Complexity Analysis

| Operation | Time | Space |
|-----------|------|-------|
| `detect_critical_pairs` | O(R^2 * P * U) | O(R^2 * P) |
| `unify` (Martelli-Montanari) | O(n * alpha(n)) | O(n) |
| `check_joinability` (per pair) | O(max_steps * R * T) | O(T) |
| `check_confluence` | O(R^2 * P * (U + max_steps * R * T)) | O(R^2 * P + T) |
| `normalize` | O(max_steps * R * T) | O(T * max_steps) |
| `suggest_confluence_repairs` | O(non_joinable * T) | O(non_joinable) |

Where: R = number of rewrite rules, P = max non-variable positions per LHS,
U = unification cost, T = max term size, alpha = inverse Ackermann.

## 5. Unicode Diagrams

### 5.1. Critical Pair Detection

```
    Rule 1: f(g(x), y) -> h(x, y)
    Rule 2: g(a) -> b

    Overlap: Rule 2 matches at position [0] in Rule 1's LHS
             g(x) unifies with g(a) via sigma = {x -> a}

    Critical pair:
      term1 = h(a, y)     (apply Rule 1 to f(g(a), y) -> h(a, y))
      term2 = f(b, y)     (apply Rule 2 to f(g(a), y) -> f(b, y))

           f(g(a), y)
           /         \
     Rule 1 /         \ Rule 2
         /             \
      h(a, y)       f(b, y)
         \             /
          \  joinable? /
           v         v
              ???
```

### 5.2. Joinability via Normalization

```
    Critical pair: (h(a, y), f(b, y))

    Normalize h(a, y):
      h(a, y) ->_R ... ->_R nf_1

    Normalize f(b, y):
      f(b, y) ->_R ... ->_R nf_2

    If nf_1 == nf_2: Joinable (common reduct)
    If nf_1 != nf_2 and both reached normal form: NotJoinable
```

### 5.3. Confluence Analysis Flow

```
    RewriteRule set
          │
          v
    ┌─────────────────────────┐
    │ detect_critical_pairs() │
    └────────────┬────────────┘
                 │
                 v
    ┌─────────────────────────┐
    │   Vec<CriticalPair>     │
    └────────────┬────────────┘
                 │
                 v
    ┌─────────────────────────┐
    │ check_joinability()     │  (for each pair)
    │    normalize both terms │
    │    compare normal forms │
    └────────────┬────────────┘
                 │
                 v
    ┌─────────────────────────┐
    │ ConfluenceAnalysis      │
    │   is_confluent: bool    │
    │   non_joinable_count    │
    │   unknown_count         │
    └─────────────────────────┘
```

## 6. PraTTaIL Integration

### 6.1. Pipeline Bridge Functions

- `detect_critical_pairs(rules)` -- Finds all overlaps between rewrite rules.
- `check_joinability(pair, rules, max_steps)` -- Normalizes both terms and
  compares.
- `check_confluence(rules, max_steps)` -- End-to-end confluence analysis.
- `suggest_confluence_repairs(analysis)` -- Generates `RepairSuggestion`s for
  non-joinable pairs.
- `structural_similarity(t1, t2)` -- Similarity score for repair confidence.

### 6.2. Lint Emission

- **T01** (`non-joinable`): Emitted for each non-joinable critical pair.
  Severity: Warning. Diagnostic includes both normal forms and the overlapping
  rules.
- **T02** (`verified`): Emitted when all critical pairs are joinable.
  Severity: Info. Confirms the TRS is confluent.

### 6.3. Repair Integration

For each non-joinable critical pair `(t1, t2)`, two repairs are suggested:

1. **Add an equation** `t1 = t2` (edit cost 1, higher confidence when terms
   are structurally similar).
2. **Add a rewrite rule** `t1 -> t2` or `t2 -> t1` (edit cost 2, oriented
   by term size heuristic: larger -> smaller preserves termination).

Confidence is modulated by `structural_similarity(t1, t2)`:
- Similarity >= 0.5: confidence 0.7--0.9
- Similarity < 0.5: confidence 0.4--0.6

## 7. Rust Implementation Notes

| Type | Role |
|------|------|
| `Term` | Enum: `Var(String)`, `App { symbol: String, args: Vec<Term> }` |
| `RewriteRule` | LHS and RHS terms with an optional name |
| `CriticalPair` | Two terms + rule indices + overlap position |
| `JoinabilityResult` | Enum: `Joinable { common_reduct }`, `NotJoinable { nf1, nf2 }`, `Unknown { reason }` |
| `ConfluenceAnalysis` | Summary: is_confluent, pairs, results, counts |

Key helper functions:
- `unify(s, t)` -- Most general unifier via occurs check + recursive decomposition.
- `rename_variables(term, suffix)` -- Appends suffix to all variable names.
- `non_var_positions(term)` -- Collects all positions of non-variable subterms.
- `normalize(term, rules, max_steps)` -- Leftmost-outermost reduction with
  cycle detection via visited set.
- `match_term(pattern, term)` -- One-way pattern matching (term treated as ground).
- `rewrite_once(term, rules)` -- Single leftmost-outermost rewrite step.

## 8. Worked Example

**TRS rules:**
```
Rule 0: f(f(x)) -> f(x)     (idempotence)
Rule 1: f(g(x)) -> g(f(x))  (commutativity with g)
```

**Critical pair detection:**

Rule 0 vs Rule 0, overlap at position [0] (f(x) in f(f(x))):
```
sigma = {x' -> x}   (renamed variables in Rule 0 copy)
term1 = f(x)         (RHS of outer Rule 0)
term2 = f(x)         (RHS of inner Rule 0 applied at root)
Result: trivially joinable (term1 == term2)
```

Rule 0 vs Rule 1, overlap at position [0] (f(x) in f(g(x'))):
```
lhs_0' = f(f(x))    rhs_0' = f(x)
lhs_1 = f(g(x'))     subterm at [0] = g(x')
unify(f(f(x)), g(x')) fails (f != g)
No overlap.
```

Rule 1 vs Rule 0, overlap at position [0] (f(g(x)) vs f(f(x'))):
```
lhs_1' = f(g(x'))   subterm at [0] of Rule 0: f(x)
unify(f(g(x')), f(x)) succeeds: sigma = {x -> g(x')}
term1 = g(f(x'))     (RHS of Rule 1)
term2 = f(g(x'))     (RHS of Rule 0 with sigma: f(x) -> f(g(x')))
```

Check joinability of `(g(f(x')), f(g(x')))`:
```
Normalize g(f(x')): no rules apply -> g(f(x'))  (normal form)
Normalize f(g(x')): Rule 1 applies -> g(f(x'))  (normal form)
Both normal forms equal: Joinable!
```

Result: TRS is confluent (T02 emitted).

## 9. References

1. Knuth, D.E. & Bendix, P.B. (1970).
   "Simple Word Problems in Universal Algebras."
   In *Computational Problems in Abstract Algebra*, Pergamon Press, pp. 263--297.

2. Huet, G. (1980).
   "Confluent Reductions: Abstract Properties and Applications to Term
   Rewriting Systems."
   *Journal of the ACM*, 27(4), pp. 797--821.

3. Baader, F. & Nipkow, T. (1998).
   *Term Rewriting and All That*. Cambridge University Press.

4. Newman, M.H.A. (1942).
   "On Theories with a Combinatorial Definition of 'Equivalence'."
   *Annals of Mathematics*, 43(2), pp. 223--243.

5. Martelli, A. & Montanari, U. (1982).
   "An Efficient Unification Algorithm."
   *ACM Transactions on Programming Languages and Systems (TOPLAS)*,
   4(2), pp. 258--282.
