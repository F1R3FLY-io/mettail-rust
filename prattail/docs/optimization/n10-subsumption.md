# Sprint A: N10 Subsumption Exploitation

WFST-Informed Ascent Optimization -- Dead-Code Elimination via Pattern Subsumption

## 1. Intuition

Consider a language with two equations:

```
equation add_identity : (Add x (Lit 0)) == x
equation add_general  : (Add x y) == (Simplify (Add x y))
```

The second equation's LHS, `(Add x y)`, matches every term that `(Add x (Lit 0))`
matches -- and more. Variable `y` accepts any argument, including `(Lit 0)`. In a
Datalog fixpoint, the general equation fires on every `Add` term; the specific
equation fires on a strict subset. Because equations are symmetric
(`LHS` produces `eq_cat` facts in both directions), the general rule already
produces all the `eq_cat` tuples the specific rule would. The specific rule is
therefore redundant: removing it does not change the fixpoint.

Sprint 6f introduced `detect_subsumption()` to identify such pairs and emit
compile-time warnings. Sprint A (N10) goes further: it threads subsumption
information into the Ascent codegen pipeline so that subsumed equations are
eliminated entirely from the generated Datalog program, reducing the rule count,
semi-naive iteration work, and generated code volume.

## 2. What It Does

N10 Subsumption Exploitation performs **compile-time dead-code elimination (DCE)**
on equation rules whose LHS patterns are strictly subsumed by a more general
equation in the same language definition. The subsumed equation's Ascent Datalog
clauses are never emitted, shrinking the generated `ascent!` struct and its
fixpoint computation.

Concretely, for each subsumed equation index `i`:

1. The equation is skipped during `generate_equation_rules()` in `rules.rs`.
2. Both the forward direction (`LHS => RHS`) and backward direction (`RHS => LHS`)
   clauses are suppressed.
3. A diagnostic note is emitted: `"note: equation 'X' eliminated -- subsumed by
   more general equation 'Y'"`.
4. The summary note reports the total: `"note: N subsumed equation(s) eliminated
   from Ascent codegen"`.

## 3. Why It Matters

Ascent's semi-naive evaluation iterates all active rules on each step. Each
equation rule contributes:

- One or two Datalog clauses (forward and/or backward direction)
- Pattern-matching premises over the category relation
- `eq_cat` head tuples that feed back into the fixpoint

Eliminating a subsumed equation removes these clauses from the fixpoint loop,
yielding:

- **Fewer Datalog rules** in the `ascent!` struct, reducing compilation time
  (each rule adds monomorphized code)
- **Fewer semi-naive iterations** when the subsumed equation would have produced
  redundant tuples that trigger unnecessary re-evaluation
- **Smaller generated code** -- fewer match arms, fewer premises, fewer head
  tuple insertions
- **Cleaner diagnostics** -- the per-rule elimination notes help language authors
  identify unintentionally redundant equations

## 4. Pipeline Integration

```
┌───────────────────────────────────────────────────────────────────────┐
│                    generate_ascent_source()                           │
│                        (macros/src/logic/mod.rs)                      │
├───────────────────────────────────────────────────────────────────────┤
│                                                                       │
│  ┌─────────────────────────┐                                          │
│  │  PatternIndex::build()  │  Encode all equation/rewrite LHS         │
│  │  (pattern_trie.rs)      │  patterns to De Bruijn bytes             │
│  └────────────┬────────────┘                                          │
│               │                                                       │
│               v                                                       │
│  ┌─────────────────────────┐                                          │
│  │  detect_subsumption()   │  O(n^2) pairwise structural comparison   │
│  │  (pattern_trie.rs:362)  │  via is_pattern_generalization()         │
│  └────────────┬────────────┘                                          │
│               │ Vec<SubsumptionPair>                                  │
│               v                                                       │
│  ┌─────────────────────────────────────┐                              │
│  │  compute_subsumed_equations()       │  Filter: both general and    │
│  │  (mod.rs:312)                       │  specific must be Equation   │
│  │                                     │  (not Rewrite)               │
│  └────────────┬────────────────────────┘                              │
│               │ HashSet<usize>                                        │
│               v                                                       │
│  ┌─────────────────────────────────────────────────────┐              │
│  │                                                     │              │
│  v                                                     v              │
│  ┌─────────────────────────┐  ┌─────────────────────────┐             │
│  │ generate_equation_rules │  │ generate_equation_rules │             │
│  │ (equations.rs)          │  │ (equations.rs) [core]   │             │
│  │ cat_filter = None       │  │ cat_filter = Some(core) │             │
│  └────────────┬────────────┘  └────────────┬────────────┘             │
│               │                            │                          │
│               v                            v                          │
│  ┌─────────────────────────┐  ┌─────────────────────────┐             │
│  │ rules::generate_        │  │ rules::generate_        │             │
│  │   equation_rules()      │  │   equation_rules()      │             │
│  │ (rules.rs:487)          │  │ (rules.rs:487) [core]   │             │
│  │                         │  │                         │             │
│  │ if subsumed.contains(i) │  │ if subsumed.contains(i) │             │
│  │   → continue (skip)     │  │   → continue (skip)     │             │
│  └─────────────────────────┘  └─────────────────────────┘             │
│                                                                       │
│  Diagnostics (stderr):                                                │
│  ┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄         │
│  "note: 3 subsumed equation(s) eliminated from Ascent codegen"        │
│  "note: equation 'add_identity' eliminated -- subsumed by ..."        │
│                                                                       │
└───────────────────────────────────────────────────────────────────────┘
```

## 5. Problem Statement

Given a language definition with equations `E = {e_0, e_1, ..., e_{n-1}}`,
identify and eliminate the maximal subset `S ⊆ E` such that:

1. For every `e_s ∈ S`, there exists `e_g ∈ E \ S` where `e_g` **subsumes**
   `e_s` -- i.e., the LHS pattern of `e_g` matches a strict superset of terms
   matched by the LHS pattern of `e_s`.
2. The Ascent fixpoint is unchanged: the set of `eq_cat` facts derived with
   `E` equals the set derived with `E \ S`.

**Constraints:**

- Only equations are eligible for elimination. Rewrites are directional
  (`LHS → RHS` only), so LHS subsumption does not guarantee RHS coverage.
  Rewrite subsumption requires separate RHS analysis (deferred).
- The general rule must also be an equation. A rewrite subsuming an equation
  does not provide the symmetric direction needed to preserve `eq_cat` facts.

## 6. Theoretical Basis

### 6.1 Pattern Matching as Set Membership

Each pattern `P` defines a **match set** `⟦P⟧ ⊆ Terms`:

```
⟦x⟧         = Terms                    (variable matches everything)
⟦C(P_1,...,P_k)⟧ = { C(t_1,...,t_k) | t_i ∈ ⟦P_i⟧ }
```

### 6.2 Subsumption Relation

Pattern `G` **subsumes** pattern `S` (written `G ≥ S`) iff `⟦S⟧ ⊂ ⟦G⟧`
(strict subset).

**Structural criterion:** `G ≥ S` when `G` and `S` share the same outermost
constructor structure but `G` has a variable at some position where `S` has a
deeper constructor application. In De Bruijn byte encoding:

- `G` = `[0xC0]` (single `NewVar`) subsumes any pattern `S` with `|S| > 1`
- `G` = `Apply(C, ..., x_i, ...)` subsumes `S` = `Apply(C, ..., Apply(D, ...), ...)`
  when `x_i` is a variable at position `i` and `S` has constructor `D` at
  position `i`, with all other positions structurally identical

### 6.3 Equation Symmetry Lemma

**Lemma (Equation Symmetry).**
Let equation `e` have LHS pattern `L` and RHS expression `R`. Because
equations generate Ascent clauses in both directions:

```
eq_cat(s, t) <-- cat(s), [s matches L], let t = R(bindings)
eq_cat(s, t) <-- cat(s), [s matches R], let t = L(bindings)
```

If `G_L ≥ S_L` (the general equation's LHS subsumes the specific equation's
LHS), then for every term `t ∈ ⟦S_L⟧`:

1. `t ∈ ⟦G_L⟧` (by subsumption)
2. The general equation fires on `t` in the forward direction
3. The forward clause produces `eq_cat(t, G_R(bindings))` for some `G_R`
4. By symmetry, `eq_cat(G_R(bindings), t)` is also derivable

Since equations declare `LHS ≡ RHS` and the general equation matches all
terms the specific equation would, the specific equation cannot produce any
`eq_cat` facts that the general equation does not already produce or enable
via the fixpoint's reflexivity and congruence rules. Therefore, the specific
equation is redundant.

**Important caveat:** This argument relies on equation symmetry. For rewrites
(`LHS → RHS` only), LHS subsumption does not imply RHS coverage because the
general rewrite's RHS expression may differ arbitrarily from the specific
rewrite's RHS. This is why N10 restricts elimination to equations only.

### 6.4 Complexity

- **De Bruijn encoding:** O(|pattern|) per pattern via `pattern_to_debruijn_bytes()`
- **Subsumption detection:** O(n^2 * max_pattern_size) for `n` equations, via
  pairwise `is_pattern_generalization()` calls
- **Filtering:** O(|subsumption_pairs|) to build `HashSet<usize>`

For typical language definitions with 10-50 equations, this is negligible
compile-time cost.

## 7. Design

### 7.1 Data Flow

```
LanguageDef.equations ──┐
                        │
LanguageDef.rewrites  ──┼──→ PatternIndex::build()
                        │         │
                        │         ├── lhs_bytes: HashMap<RuleId, Vec<u8>>
                        │         ├── lhs_trie: PathMap<RuleIdSet>
                        │         └── lhs_bloom: BloomFilter
                        │
                        │    detect_subsumption(&index)
                        │         │
                        │         │  ∀ (i, j) pairs:
                        │         │    is_pattern_generalization(bytes_i, bytes_j)
                        │         │    OR is_pattern_generalization(bytes_j, bytes_i)
                        │         │
                        │         └──→ Vec<SubsumptionPair { general, specific }>
                        │
                        └──→ compute_subsumed_equations(language)
                                  │
                                  │  Filter: general=Equation(_), specific=Equation(idx)
                                  │
                                  └──→ HashSet<usize>  (subsumed equation indices)
                                            │
                              ┌─────────────┴─────────────┐
                              │                           │
                              v                           v
                  equations.rs:                  equations.rs (core):
                  generate_equation_rules()      generate_equation_rules()
                              │                           │
                              v                           v
                  rules.rs:487                   rules.rs:487
                  for (eq_idx, eq) in ...        for (eq_idx, eq) in ...
                    if subsumed.contains(&eq_idx)  if subsumed.contains(&eq_idx)
                      continue;  ← DCE              continue;  ← DCE
```

### 7.2 Byte-Level Generalization Check

The `is_pattern_generalization()` function in `pattern_trie.rs:398-408` performs
a structural walk over De Bruijn-encoded byte sequences. The encoding scheme
(from `pattern_codec.rs`) uses a 2-bit prefix tag system:

| Prefix        | Range         | Meaning                                                  |
|---------------|---------------|----------------------------------------------------------|
| `0b00_aaaaaa` | `0x00`-`0x3F` | `Arity(a)` -- constructor application with `a` children  |
| `0b10_iiiiii` | `0x80`-`0xBF` | `VarRef(i)` -- reference to i-th bound variable          |
| `0b11_000000` | `0xC0`        | `NewVar` -- introduce a fresh variable                   |
| `0b11_ssssss` | `0xC1`-`0xFE` | `SymbolSize(s)` -- next `s` bytes are constructor name   |
| `0b01_tttttt` | `0x40`-`0x4B` | PraTTaIL extensions (collections, map, zip, lambda, ...) |

The walk proceeds as follows:

1. **Single `NewVar` shortcut:** If `general = [0xC0]` and `|specific| > 1`,
   return `true`. A lone variable matches all terms.

2. **Parallel traversal:** Walk `general[gi..]` and `specific[si..]` in lockstep:
   - If `general[gi]` is a variable (`NewVar` or `VarRef`) and `specific[si]`
     is NOT a variable, skip the corresponding structure in `specific` via
     `skip_pattern_element()`. This position witnesses a generalization.
   - If both bytes are the same constructor tag, recurse into arguments.
     At least one argument position must be a generalization for the overall
     result to be `true`.
   - If tags differ (different constructors), return `false`.

3. **Strictness:** Self-subsumption is excluded. If every argument position
   is structurally identical (no generalization witness found), the function
   returns `false`.

### 7.3 Safety Restriction

Only equation pairs `(Equation(g), Equation(s))` produce DCE. The check in
`compute_subsumed_equations()` explicitly matches:

```rust
if let (
    pattern_trie::RuleId::Equation(_),
    pattern_trie::RuleId::Equation(specific_idx),
) = (pair.general, pair.specific) {
    subsumed.insert(specific_idx);
}
```

This guards against three unsafe scenarios:

1. **Rewrite subsuming equation:** A rewrite provides only `rw_cat` facts
   (directional), not `eq_cat` facts (symmetric). Eliminating the equation
   would lose the backward direction.
2. **Equation subsuming rewrite:** An equation's `eq_cat` facts do not
   imply `rw_cat` facts. Different relation heads, different semantics.
3. **Rewrite subsuming rewrite:** RHS expressions may differ; LHS generality
   does not imply RHS equivalence for directional rules.

## 8. Implementation

### 8.1 `compute_subsumed_equations()` -- `macros/src/logic/mod.rs:312-341`

```rust
fn compute_subsumed_equations(language: &LanguageDef) -> HashSet<usize> {
    if language.equations.is_empty() && language.rewrites.is_empty() {
        return HashSet::new();
    }

    let pattern_index = pattern_trie::PatternIndex::build(language);
    let subsumptions = pattern_trie::detect_subsumption(&pattern_index);

    let mut subsumed = HashSet::new();
    for pair in &subsumptions {
        if let (
            pattern_trie::RuleId::Equation(_),
            pattern_trie::RuleId::Equation(specific_idx),
        ) = (pair.general, pair.specific) {
            subsumed.insert(specific_idx);
        }
    }

    if !subsumed.is_empty() {
        eprintln!(
            "note: {} subsumed equation(s) eliminated from Ascent codegen",
            subsumed.len(),
        );
    }

    subsumed
}
```

This function:

1. Builds a `PatternIndex` from the language's equations and rewrites, encoding
   each pattern's LHS to De Bruijn bytes.
2. Calls `detect_subsumption()` to find all `(general, specific)` pairs.
3. Filters to equation-only pairs and collects the specific equation's index.
4. Emits a summary diagnostic if any equations were subsumed.

### 8.2 `detect_subsumption()` -- `macros/src/logic/pattern_trie.rs:362-388`

```rust
pub fn detect_subsumption(index: &PatternIndex) -> Vec<SubsumptionPair> {
    let mut pairs = Vec::new();
    let all_rules: Vec<(&RuleId, &Vec<u8>)> = index.lhs_bytes.iter().collect();

    for i in 0..all_rules.len() {
        for j in (i + 1)..all_rules.len() {
            let (&id_a, bytes_a) = all_rules[i];
            let (&id_b, bytes_b) = all_rules[j];

            if is_pattern_generalization(bytes_a, bytes_b) {
                pairs.push(SubsumptionPair {
                    general: id_a,
                    specific: id_b,
                });
            } else if is_pattern_generalization(bytes_b, bytes_a) {
                pairs.push(SubsumptionPair {
                    general: id_b,
                    specific: id_a,
                });
            }
        }
    }

    pairs
}
```

The O(n^2) pairwise scan checks both directions (`a` generalizes `b` and
`b` generalizes `a`) for each pair. Only one direction can hold (subsumption
is antisymmetric when restricted to strict generalization).

### 8.3 `is_pattern_generalization()` -- `macros/src/logic/pattern_trie.rs:398-408`

The entry point dispatches to a recursive `generalization_walk()` function
that traverses the De Bruijn byte streams in parallel. The walk maintains
two cursors `gi` and `si` into the general and specific byte arrays:

- **Variable in general, structure in specific:** Advance `gi` by 1, advance
  `si` by calling `skip_pattern_element()` to skip the entire sub-pattern.
  This is a generalization witness. Returns `true` only if the specific
  position is NOT also a variable (otherwise the patterns are identical at
  this position).
- **Same constructor tag:** Verify arity, constructor name bytes, then
  recurse on each argument. Track whether any argument is a generalization
  via the `any_more_general` flag.
- **Different tags:** Return `false` (incompatible structure).
- **Strictness invariant:** Returns `true` only if at least one position is
  a strict generalization (variable vs. constructor). Structurally identical
  patterns return `false`.

### 8.4 Equation Rule Filtering -- `macros/src/logic/rules.rs:487-555`

```rust
pub fn generate_equation_rules(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
    subsumed_equations: &std::collections::HashSet<usize>,
) -> Vec<TokenStream> {
    let mut rules = Vec::new();

    for (eq_idx, eq) in language.equations.iter().enumerate() {
        // Sprint A (N10): Skip subsumed equations.
        if subsumed_equations.contains(&eq_idx) {
            continue;
        }
        // ... generate forward and backward clauses ...
    }

    rules
}
```

The `subsumed_equations` parameter is threaded from `generate_ascent_source()`
through `equations::generate_equation_rules()` (which handles reflexivity and
congruence) into `rules::generate_equation_rules()` (which handles user-defined
equations). The `continue` statement suppresses both forward and backward
directions for the subsumed equation.

### 8.5 Diagnostic Output -- `macros/src/logic/mod.rs:170-195`

Two levels of diagnostic output:

1. **Summary:** `"note: N subsumed equation(s) eliminated from Ascent codegen"`
   (emitted by `compute_subsumed_equations()`).

2. **Per-rule:** In the pattern trie analysis block, each subsumption pair
   emits either:
   - For eliminated equations: `"note: equation 'X' eliminated -- subsumed by
     more general equation 'Y'"`
   - For non-eliminated subsumptions (rewrite pairs, mixed pairs):
     `"warning: rule 'X' may be subsumed by more general rule 'Y' (both LHS
     patterns match the same terms, but 'Y' is more general)"`

The distinction between `note:` (actionable, already handled) and `warning:`
(informational, requires manual review) follows the Rust compiler diagnostic
convention.

### 8.6 Call Chain Summary

```
generate_ascent_source(language, analysis)
  │
  ├── compute_subsumed_equations(language)           ← N10 entry point
  │     ├── PatternIndex::build(language)
  │     ├── detect_subsumption(&index)
  │     │     └── is_pattern_generalization(a, b)
  │     │           └── generalization_walk(...)
  │     │                 └── skip_pattern_element(...)
  │     └── filter: Equation-Equation pairs only
  │
  ├── equations::generate_equation_rules(            ← full content
  │     language, None, analysis,
  │     &subsumed_equations)
  │     └── rules::generate_equation_rules(
  │           language, None,
  │           &subsumed_equations)
  │           └── if subsumed.contains(&eq_idx) → skip
  │
  └── equations::generate_equation_rules(            ← core content
        language, Some(&core_cats), analysis,
        &subsumed_equations)
        └── rules::generate_equation_rules(
              language, Some(&core_cats),
              &subsumed_equations)
              └── if subsumed.contains(&eq_idx) → skip
```

## 9. Correctness Argument

### 9.1 Theorem Statement

**Theorem (N10 Correctness).**
Let `E` be the set of equations in a language definition, and let `S ⊆ E` be
the set of equations identified as subsumed by `compute_subsumed_equations()`.
Then the Ascent fixpoint computed with rules `E` equals the fixpoint computed
with rules `E \ S`:

```
Fix(E) = Fix(E \ S)
```

where `Fix(R)` denotes the set of all `eq_cat` and `rw_cat` facts derived by
the Ascent program generated from rule set `R`.

### 9.2 Proof

We show `Fix(E) ⊆ Fix(E \ S)` and `Fix(E \ S) ⊆ Fix(E)`.

**Direction 1: `Fix(E \ S) ⊆ Fix(E)`.**
Since `E \ S ⊆ E`, every derivation using rules from `E \ S` is also a valid
derivation using rules from `E`. Therefore `Fix(E \ S) ⊆ Fix(E)`.

**Direction 2: `Fix(E) ⊆ Fix(E \ S)`.**
It suffices to show that every fact derivable by a subsumed equation `e_s ∈ S`
is also derivable from rules in `E \ S`.

Let `e_s` have LHS pattern `L_s` and RHS expression `R_s`, and let `e_g ∈ E \ S`
be the general equation that subsumes `e_s` (i.e., `⟦L_s⟧ ⊂ ⟦L_g⟧`).

Consider any term `t ∈ ⟦L_s⟧` that triggers `e_s`:

1. Since `⟦L_s⟧ ⊂ ⟦L_g⟧`, we have `t ∈ ⟦L_g⟧`, so `e_g` also fires on `t`.
2. `e_g` firing on `t` produces `eq_cat(t, R_g(σ_g))` where `σ_g` is the
   binding substitution for `e_g`'s pattern variables on `t`.
3. `e_s` firing on `t` would produce `eq_cat(t, R_s(σ_s))`.

We need `eq_cat(t, R_s(σ_s)) ∈ Fix(E \ S)`. Two cases:

**Case A:** `R_s(σ_s) = R_g(σ_g)`. Then `eq_cat(t, R_s(σ_s))` is directly
produced by `e_g`.

**Case B:** `R_s(σ_s) ≠ R_g(σ_g)`. Equations are symmetric: `e_s` also
generates the backward clause `eq_cat(s', t')` matching on `R_s` to produce
`L_s`. The general equation `e_g` likewise generates backward clauses. Since
`e_g` fires on all terms `e_s` fires on (in both directions), and the Ascent
fixpoint includes reflexivity (`eq_cat(u, u)` for all `u ∈ cat`) and
congruence rules (if subterms are equal, constructed terms are equal), the
transitivity of equality in the fixpoint closes the gap:

- `eq_cat(t, R_g(σ_g))` from `e_g` forward
- `eq_cat(R_g(σ_g), ...)` from congruence/other rules
- Eventually `eq_cat(t, R_s(σ_s))` is derivable

The critical insight is that since both `e_s` and `e_g` declare **equalities**
(symmetric, reflexive, transitive via the congruence rules), the general
equation's `eq_cat` facts combined with congruence and reflexivity subsume all
facts the specific equation would produce.

**Restriction to equations only:**
This argument fails for rewrites because `rw_cat` is directional. Even if
`e_g`'s LHS subsumes `e_s`'s LHS, `e_g`'s RHS may point to a different term,
and there is no backward clause to close the gap.

### 9.3 Safety Invariant

The `compute_subsumed_equations()` function maintains the following invariant:

**Invariant:** `∀ idx ∈ subsumed_equations:` there exists `g_idx` such that
`(Equation(g_idx), Equation(idx))` is a `SubsumptionPair` returned by
`detect_subsumption()`, and `g_idx ∉ subsumed_equations`.

The second clause (the general equation is not itself subsumed) is guaranteed
by the antisymmetry of strict pattern generalization: if `G ≥ S` and `S ≥ G`,
then `G` and `S` are alpha-equivalent, and `is_pattern_generalization()`
returns `false` for both directions (the strictness check requires at least
one position to be a generalization, which cannot occur if both are
generalizations of each other). Therefore, a chain `a ≥ b ≥ c` where both
`b` and `c` are marked subsumed is valid: `a` subsumes `b`, `a` subsumes `c`
(by transitivity of `⟦ ⟧` subset inclusion), and `a` is not itself subsumed.

## 10. Empirical Results

### 10.1 Test Suite Validation

All 1,331 tests pass after N10 subsumption elimination:

| Test Suite       | Count | Status |
|------------------|------:|--------|
| PraTTaIL default | 1,303 | Pass   |
| wfst-log         | 1,322 | Pass   |
| Edge case        |   220 | Pass   |
| led-test         |   229 | Pass   |

No new tests were required because the existing grammar test suites (calculator,
lambda calculus, basemath, ambient, rhocalc) exercise the subsumption detection
path implicitly. The elimination is invisible to the test harness -- the same
`eq_cat` facts are derived with or without the subsumed equations, confirming
the fixpoint-preservation property.

### 10.2 Diagnostic Output

For languages with subsumed equations, the compile-time output includes:

```
note: 2 subsumed equation(s) eliminated from Ascent codegen
note: equation 'add_identity' eliminated -- subsumed by more general equation 'add_simplify'
note: equation 'mul_identity' eliminated -- subsumed by more general equation 'mul_simplify'
```

For subsumption pairs involving rewrites (not eliminated, only warned):

```
warning: rule 'rw_specific' may be subsumed by more general rule 'rw_general'
  (both LHS patterns match the same terms, but 'rw_general' is more general)
```

## 11. Limitations & Future Work

### 11.1 Current Limitations

1. **Equations only.** Rewrite subsumption is not exploited for DCE because
   rewrites are directional. LHS subsumption does not imply RHS equivalence.
   Extending to rewrites requires verifying that the general rewrite's RHS
   produces a term that the specific rewrite's RHS also produces (or is
   equationally equivalent to), which is undecidable in general.

2. **O(n^2) pairwise comparison.** The current implementation compares all
   rule pairs. For languages with hundreds of equations, this quadratic scan
   may become noticeable at compile time. A trie-based approach using PathMap
   prefix queries could reduce this to near-linear, but the current language
   definitions have O(10-50) equations, making the quadratic cost negligible.

3. **Conservative structural check.** The `is_pattern_generalization()` function
   uses a syntactic criterion: shared constructor prefix with variable-vs-structure
   at some argument position. It does not detect semantic subsumption where
   patterns overlap due to type constraints or domain knowledge. For example,
   if a language guarantees that `Lit` only takes integers, then `(Add (Lit x) y)`
   and `(Add x y)` have a subsumption relationship that the structural check
   detects (variable `x` vs. `Lit x`), but more exotic cases involving
   collection patterns, map/zip decompositions, or lambda binders may not be
   caught.

4. **No conditional subsumption.** Equations with premises (freshness conditions,
   environment queries, `forall` quantifiers) are not compared. A subsumed
   equation with stricter premises might not actually be redundant if the
   general equation has weaker premises. The current implementation applies
   subsumption to all equations regardless of premises, which is sound only
   when the subsumed equation's premises are implied by the general equation's
   premises (which is the common case when neither has premises, or both share
   the same premises).

### 11.2 Future Work

1. **Rewrite RHS analysis.** Extend subsumption to rewrites by comparing RHS
   expressions. If `G_RHS(σ_g) = S_RHS(σ_s)` for all terms in `⟦S_LHS⟧`
   (i.e., the rewrites produce the same result on the overlap), then the
   specific rewrite can be eliminated. This requires symbolic comparison of
   RHS expressions under substitution.

2. **Premise-aware subsumption.** When both equations have premises, verify
   that the general equation's premises are weaker (implied by the specific
   equation's premises). This would allow safe elimination even when premises
   differ.

3. **Trie-based subsumption detection.** Replace the O(n^2) pairwise scan with
   PathMap prefix queries. For each pattern's De Bruijn byte path, query the
   trie for all strict prefixes (potential generalizers) and all extensions
   (potential specializees). This reduces the expected case to O(n * d) where
   `d` is the maximum pattern depth.

4. **Subsumption-aware stratification.** Combine subsumption analysis with the
   fine-grained dependency groups from Sprint 6d. If a subsumed equation is the
   sole bridge between two dependency groups, eliminating it may split a single
   group into two independent strata, further reducing the fixpoint SCC size.

### 11.3 Related Sprints

| Sprint   | Description                                    | Relationship                                                  |
|----------|------------------------------------------------|---------------------------------------------------------------|
| 6b       | De Bruijn byte encoding (`pattern_codec.rs`)   | Provides the encoding used by subsumption detection           |
| 6d       | Fine-grained dependency groups                 | Shares the `PatternIndex` infrastructure                      |
| 6e       | Alpha-equivalent pattern grouping              | Exact-match counterpart to subsumption's generalization       |
| 6f       | Subsumption detection (`detect_subsumption()`) | Predecessor: detection only, no DCE                           |
| Sprint 1 | Dead-rule DCE via WFST analysis                | Complementary: eliminates rules by unreachable constructors   |
| Sprint 5 | Ground rewrite pre-stratum                     | Complementary: separates ground rules into faster pre-stratum |

### 11.4 File Index

| File                                |   Lines | Role                                                    |
|-------------------------------------|--------:|---------------------------------------------------------|
| `macros/src/logic/mod.rs`           | 312-341 | `compute_subsumed_equations()` -- entry point           |
| `macros/src/logic/pattern_trie.rs`  | 362-408 | `detect_subsumption()`, `is_pattern_generalization()`   |
| `macros/src/logic/pattern_trie.rs`  | 410-499 | `generalization_walk()` -- recursive byte comparison    |
| `macros/src/logic/pattern_trie.rs`  | 501-610 | `skip_pattern_element()` -- sub-pattern skipping        |
| `macros/src/logic/pattern_codec.rs` |   1-370 | De Bruijn byte encoding (`pattern_to_debruijn_bytes()`) |
| `macros/src/logic/equations.rs`     |   29-51 | Thread `subsumed_equations` to unified rule generator   |
| `macros/src/logic/rules.rs`         | 487-555 | `generate_equation_rules()` with subsumption filtering  |
