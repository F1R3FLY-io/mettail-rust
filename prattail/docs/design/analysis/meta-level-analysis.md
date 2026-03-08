# Meta-Level Analysis: Morphisms, KAT, Tensor Products, and Repair

**Source files:** `morphism.rs`, `kat.rs`, `tensor.rs`, `proof_output.rs`,
`repair.rs`
**Pipeline phase:** 6 (after temporal/provenance analyses)
**Feature gates:** `morphisms`, `kat`, `proofs` (requires `provenance`)
**Always-on:** `tensor.rs`, `repair.rs`
**Lint codes:** M01--M02, K01--K02, Z01

## Rationale

The meta-level analyses operate *across* the individual analysis modules,
providing cross-theory translation, decidable program verification, combined
analysis via semiring products, proof certificates, and actionable repair
suggestions.  These are the highest abstraction level in the framework:

- **Theory morphisms** translate between grammar theories, enabling
  verified desugaring, grammar embedding, and AST migration.
- **Kleene Algebra with Tests** (KAT) provides decidable Hoare logic for
  verifying pre/post-conditions of parse functions.
- **Tensor products** combine two independent analyses into a single pass
  with cross-analysis interaction.
- **Proof output** generates machine-readable certificates of verification
  results.
- **Repair engine** transforms analysis failures into ranked, actionable
  fix suggestions.

---

## 1. Theory Morphisms (`morphism.rs`)

### 1.1 Intuition

A theory morphism is a structure-preserving map between two formal theories.
When two grammars share structural similarities -- a source language and its
desugared form, or a grammar and its optimized version -- a morphism maps
sorts (categories) and operations (constructors) between them while
preserving the axioms (semantic invariants).

In PraTTaIL, morphisms support three use cases:
1. **Verified desugaring**: proving that syntactic sugar preserves semantics.
2. **Grammar embedding**: showing one grammar is a sub-grammar of another.
3. **AST migration**: translating parse trees between grammar versions.

### 1.2 Formal Definition

A theory `T = (S, Omega, Ax)` consists of:
- `S` -- a set of sorts (grammar categories)
- `Omega` -- a set of operations (constructors), each with a signature
  `f: s_1 x ... x s_n -> s`
- `Ax` -- a set of axioms (semantic invariants)

A theory morphism `phi: T_1 -> T_2` consists of:
- A sort map `phi_S: S_1 -> S_2`
- An operation map `phi_Omega: Omega_1 -> Terms(Omega_2)` (maps source
  operations to target term patterns)

such that for every axiom `A` in `Ax_1`, the translated axiom
`phi(A)` is a theorem of `T_2`.

### 1.3 Morphism Commutation Diagram

```
          T_1                    T_2
   ┌──────────────┐      ┌──────────────┐
   │  Sorts S_1   │      │  Sorts S_2   │
   │  Ops  Omega_1│      │  Ops  Omega_2│
   │  Axioms Ax_1 │      │  Axioms Ax_2 │
   └──────┬───────┘      └──────┬───────┘
          │                      │
          │  phi_S               │  id
          ▼                      ▼
      S_1 ─────────────────→ S_2
          │                      │
          │  phi_Omega           │  id
          ▼                      ▼
   Omega_1 ────────────────→ Terms(Omega_2)

   Preservation:  A in Ax_1  implies  phi(A) in Theorems(T_2)
```

### 1.4 Translation Cases

The operation map supports three kinds of translation:

```rust
pub enum TranslationCase {
    /// Direct: source operation maps to one target operation.
    Direct { target_op: String },
    /// Compound: source operation maps to a term built from
    /// multiple target operations (e.g., desugaring).
    Compound { description: String, template: String },
    /// Identity: operation is preserved unchanged.
    Identity,
}
```

Example: desugaring `if-then-else` to `case` + `bool`:

```
  phi(IfThenElse) = Compound {
      description: "desugar if to case",
      template: "Case(BoolTag, $1, $2)"
  }
```

### 1.5 Morphism Construction and Validation

```
function construct_morphism(name, source, target, sort_map, op_map)
    -> Result<TheoryMorphism, Error>:

    // (1) Every source sort must map to an existing target sort
    for src_sort in source.sorts:
        if src_sort not in sort_map:
            return Error("unmapped source sort")
        if sort_map[src_sort] not in target.sorts:
            return Error("target sort does not exist")

    // (2) Every source operation must have a translation case
    for src_op in source.operations:
        if src_op.name not in op_map:
            return Error("unmapped source operation")

    // (3) For Direct mappings, verify arity preservation
    for (src_name, case) in op_map:
        if case is Direct { target_op }:
            if arity(src_name) != arity(target_op):
                return Error("arity mismatch")

    return TheoryMorphism { name, sort_map, op_map, ... }
```

### 1.6 Axiom Preservation Verification

```
function verify_preservation(morphism, source_axioms)
    -> Vec<PreservationResult>:

    results := []
    for axiom in source_axioms:
        // Translate the axiom through the morphism
        translated := translate(axiom, morphism.sort_map, morphism.op_map)

        // Check whether the translated axiom holds in the target theory
        // (Currently: structural check -- axiom text appears in target)
        if target_validates(translated):
            results.push(Preserved { axiom, translated })
        else:
            results.push(NotPreserved { axiom, translated, reason })

    return results
```

### 1.7 Gap Detection

When a morphism is incomplete, the gap detector identifies what is missing:

```rust
pub struct MorphismGap {
    pub kind: GapKind,
    pub source_name: String,
    pub description: String,
}

pub enum GapKind {
    MissingSort,         // source sort has no target mapping
    MissingOperation,    // source operation has no translation case
    ArityMismatch,       // arity differs between source and target
    PreservationFailure, // axiom not preserved by translation
}
```

Gaps produce M01 lint diagnostics with repair suggestions (see Section 5).

### 1.8 Pipeline Bridge

```rust
pub fn check_from_bundle(
    all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
    categories: &[CategoryInfo],
) -> Option<MorphismCheck>
```

Constructs a self-morphism from the grammar to itself (identity on sorts
and operations), then checks completeness.  Any category or constructor
appearing in syntax but missing from the identity map produces a gap.
Returns `MorphismCheck` with `gaps`, `preservation_failures`, and
`is_complete`.

---

## 2. Kleene Algebra with Tests (`kat.rs`)

### 2.1 Intuition

Kleene Algebra with Tests (KAT) extends Kleene algebra with a Boolean
subalgebra of "tests" (predicates).  The resulting theory is powerful
enough to subsume propositional Hoare logic while remaining decidable,
making it ideal for automated verification of parser control flow.

The key result (Kozen, 1997): the Hoare triple `{b} p {c}` is valid if
and only if `b * p * not(c) = 0` in the free KAT.

### 2.2 Denotational Semantics

A KAT is a structure `(K, B, +, *, ^*, 0, 1, overline)` where:
- `(K, +, *, ^*, 0, 1)` is a Kleene algebra
- `(B, +, *, overline, 0, 1)` is a Boolean algebra with `B subset K`
- Tests interact with actions via composition: `b * p` means
  "if `b` then do `p`"

The language-theoretic interpretation maps KAT expressions to sets of
*guarded strings*:

```
  guarded string:  alpha_0 . a_1 . alpha_1 . a_2 . ... . a_n . alpha_n

  where alpha_i in 2^Atoms (Boolean atom valuations)
  and   a_i in Actions
```

Two KAT expressions are equivalent iff they denote the same set of
guarded strings.

### 2.3 Expression Types

```rust
pub enum BooleanTest {
    True,                          // always-passing test
    False,                         // always-failing test
    Atom(String),                  // atomic predicate
    Not(Box<BooleanTest>),         // negation
    And(Box<BooleanTest>, Box<BooleanTest>),  // conjunction
    Or(Box<BooleanTest>, Box<BooleanTest>),   // disjunction
}

pub enum KatExpr {
    Zero,                          // failure (empty language)
    One,                           // skip (empty string)
    Test(BooleanTest),             // Boolean guard
    Action(String),                // atomic action
    Seq(Box<KatExpr>, Box<KatExpr>),    // sequential composition
    Alt(Box<KatExpr>, Box<KatExpr>),    // alternation/choice
    Star(Box<KatExpr>),            // Kleene star (iteration)
}
```

### 2.4 Hoare Logic Encoding

The Hoare triple `{b} p {c}` asserts: "if precondition `b` holds and
program `p` executes, then postcondition `c` holds afterwards."

KAT encoding:

```
  {b} p {c}  is valid  iff  b * p * not(c) = 0

  equivalently:  check_equivalence(b ; p ; not(c), Zero) = true
```

```rust
pub fn hoare_condition(pre: BooleanTest, program: KatExpr, post: BooleanTest) -> KatExpr {
    Seq(Test(pre), Seq(program, Test(Not(post))))
}

pub fn verify_hoare_triple(triple: &HoareTriple) -> bool {
    let condition = hoare_condition(pre, program, post);
    check_equivalence(&condition, &KatExpr::Zero)
}
```

### 2.5 Equivalence Checking via Brzozowski Derivatives

KAT equivalence is decidable in PSPACE (Kozen & Smith, 1996).  The
implementation uses a bounded symbolic bisimulation approach based on
Brzozowski derivatives:

```
function check_equivalence_bounded(a, b, depth_limit) -> bool:
    // Collect all atomic test names from both expressions
    atoms := collect_atoms(a) union collect_atoms(b)
    // Build all 2^n Boolean atom valuations
    valuations := enumerate_valuations(atoms)
    // Collect all action names for derivative computation
    actions := collect_actions(a) union collect_actions(b)

    worklist := { (a, b) }
    visited  := { (a, b) }
    iterations := 0

    while worklist is non-empty and iterations < depth_limit:
        (e1, e2) := worklist.pop()
        iterations += 1

        for valuation in valuations:
            // Check nullability agreement
            if nullable(e1, valuation) != nullable(e2, valuation):
                return false   // distinguishing witness found

            // Compute Brzozowski derivatives for each action
            for action in actions:
                d1 := simplify(derivative(e1, action, valuation))
                d2 := simplify(derivative(e2, action, valuation))
                if d1 != d2 and (d1, d2) not in visited:
                    visited.add((d1, d2))
                    worklist.push((d1, d2))

    return true   // no counterexample found within depth bound
```

### 2.6 Nullability

Nullability determines whether an expression accepts the empty string
under a given Boolean valuation:

```
  nullable(Zero)       = false
  nullable(One)        = true
  nullable(Test(t))    = eval_test(t, valuation)
  nullable(Action(_))  = false         (actions consume input)
  nullable(Seq(a, b))  = nullable(a) and nullable(b)
  nullable(Alt(a, b))  = nullable(a) or  nullable(b)
  nullable(Star(_))    = true          (zero repetitions)
```

### 2.7 Brzozowski Derivative Rules

The derivative `D_a(e)` gives the expression remaining after consuming
action `a`:

```
  D_a(Zero)        = Zero
  D_a(One)         = Zero
  D_a(Test(_))     = Zero                    (tests don't consume)
  D_a(Action(a))   = One   if action matches, else Zero
  D_a(Seq(p, q))   = Alt(Seq(D_a(p), q),
                         if nullable(p) then D_a(q) else Zero)
  D_a(Alt(p, q))   = Alt(D_a(p), D_a(q))
  D_a(Star(p))     = Seq(D_a(p), Star(p))
```

### 2.8 Algebraic Simplification

A bottom-up simplification pass applies standard identities to keep
derivative expressions compact:

```
  Seq(Zero, _) = Zero          Seq(_, Zero) = Zero
  Seq(One, x)  = x             Seq(x, One)  = x
  Alt(Zero, x) = x             Alt(x, Zero) = x
  Alt(x, x)    = x             (idempotence)
  Star(Zero)   = One           Star(One)    = One
  Star(Star(x))= Star(x)
  Test(True)   = One           Test(False)  = Zero
```

### 2.9 PraTTaIL Application

KAT models PraTTaIL's parse control flow:

| Parse concept         | KAT element                             |
|-----------------------|-----------------------------------------|
| Rule chaining         | Sequential composition `p ; q`          |
| Alternative dispatch  | Alternation `p + q`                     |
| Recursive category    | Kleene star `p*`                        |
| Token predicate       | Boolean test `[token_is_open_paren]`    |
| Error recovery guard  | Boolean test `[in_recovery_mode]`       |
| Shift action          | Action `shift`                          |
| Reduce action         | Action `reduce`                         |

The pipeline bridge constructs Hoare triples from the WPDS call graph:
- For each call edge `A -> B`: `{A_reachable} call_A_B {B_reachable}`
- For each reachable category with syntax: `{has_syntax} parse_Cat {parsed}`
- For each SCC (mutual recursion): verify `star(cycle) ; star(cycle) = star(cycle)`

### 2.10 Pipeline Bridge

```rust
pub fn check_from_bundle(
    wpds_analysis: &WpdsAnalysis,
    all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
) -> Option<KatCheck>
```

Returns `KatCheck` with `hoare_results` (per-triple verdicts) and
`equivalence_results` (SCC idempotence checks).  Returns `None` when the
call graph has no edges.

### 2.11 Complexity

| Operation                    | Complexity                            |
|------------------------------|---------------------------------------|
| Derivative computation       | O(|expr|) per action per valuation    |
| Equivalence (full)           | PSPACE-complete                       |
| Bounded bisimulation         | O(depth * 2^n * |actions| * |expr|)   |
| Hoare triple verification    | Reduces to equivalence check          |

---

## 3. Tensor Product of Semirings (`tensor.rs`)

### 3.1 Intuition

The product semiring `ProductWeight<S_1, S_2>` runs two analyses
independently, operating component-wise.  The tensor product
`TensorWeight<S_1, S_2>` goes further: it allows *interaction* between
the two analyses via bilinear multiplication.  This models situations where
the result of one analysis affects the other -- for example, combining
error probability (Viterbi) with parse cost (Tropical) where errors
influence cost.

### 3.2 Algebraic Definition

Given semirings `(S_1, +_1, *_1, 0_1, 1_1)` and `(S_2, +_2, *_2, 0_2, 1_2)`,
the tensor product semiring `S_1 (x) S_2` has elements that are formal sums
of elementary tensors:

```
  sum_i  a_i (x) b_i      where a_i in S_1, b_i in S_2
```

with operations:

- **Plus**: concatenation of term lists, then merge of equal terms:
  ```
  (sum_i a_i (x) b_i) + (sum_j c_j (x) d_j) = sum_k e_k (x) f_k
  ```

- **Times**: all pairwise products via bilinearity:
  ```
  (sum_i a_i (x) b_i) * (sum_j c_j (x) d_j)
      = sum_{i,j} (a_i *_1 c_j) (x) (b_i *_2 d_j)
  ```

- **Zero**: empty sum (no terms)
- **One**: `1_1 (x) 1_2`

### 3.3 Comparison with Product Weight

| Property            | `ProductWeight<S_1, S_2>`     | `TensorWeight<S_1, S_2>`          |
|---------------------|-------------------------------|-------------------------------------|
| Representation      | Single pair `(s_1, s_2)`      | Sum of pairs `sum (s_{1,i}, s_{2,i})` |
| Plus                | Component-wise                | Union of term lists + merge        |
| Times               | Component-wise                | Bilinear (all pairwise)            |
| Interaction         | None (independent)            | Cross-analysis correlation         |
| Projections         | Trivial (`left`/`right`)      | Marginalizes: `sum s_{1,i}` or `sum s_{2,i}` |

### 3.4 Sparse Representation

To keep tensor products tractable, the implementation caps the number of
terms at `MAX_TENSOR_TERMS = 8`:

```rust
pub struct TensorWeight<S1: Semiring, S2: Semiring> {
    pub terms: Vec<(S1, S2)>,
}
```

When multiplication would exceed the cap, terms with the smallest
contribution are dropped.

### 3.5 Diagram: Tensor Product Multiplication

```
   (a1(x)b1 + a2(x)b2) * (c1(x)d1)

   = (a1*c1)(x)(b1*d1) + (a2*c1)(x)(b2*d1)

   Product of 2-term tensor with 1-term tensor
   yields 2-term result (2 * 1 = 2 pairwise products).

   In general: |result| <= |left| * |right|,
   capped at MAX_TENSOR_TERMS.
```

### 3.6 Projection (Marginalization)

Projecting a tensor weight onto one component marginalizes over the other:

```
  project_left(sum_i a_i (x) b_i)  = sum_i a_i     (in S_1)
  project_right(sum_i a_i (x) b_i) = sum_i b_i     (in S_2)
```

This collapses the tensor back to a single-semiring value, discarding the
cross-analysis correlation.

---

## 4. Proof Output (`proof_output.rs`)

### 4.1 Intuition

After all analyses complete, the proof output module generates
machine-readable certificates summarizing what was verified and how.
These certificates can be:
- Consumed by external proof checkers
- Archived for audit trails
- Used for incremental re-verification when grammars change

### 4.2 Proof Structure

```rust
pub struct ProofOutput {
    /// Overall verdict (e.g., "safe", "unsafe", "inconclusive").
    pub verdict: String,
    /// Provenance polynomial (if provenance tracking was enabled).
    pub provenance: Option<String>,
    /// Step-by-step proof justification.
    pub proof_steps: Vec<ProofStep>,
    /// Rocq/Coq certificate (if proofs feature is enabled).
    pub rocq_certificate: Option<String>,
}

pub struct ProofStep {
    /// Description of this proof step.
    pub description: String,
    /// The module that produced this step.
    pub source_module: String,
    /// Step result (pass/fail/note).
    pub result: String,
}
```

### 4.3 Certificate Generation

The pipeline generates proof output after all analyses complete:

```
function generate_proof_output(ctx: AnalysisContext) -> ProofOutput:
    steps := []

    // Collect results from each analysis phase
    if ctx.confluence_result is Some(c):
        steps.push(ProofStep {
            description: "Confluence check",
            source_module: "confluence",
            result: if c.is_confluent then "PASS" else "FAIL"
        })

    if ctx.safety_result is Some(s):
        steps.push(ProofStep {
            description: "Safety verification",
            source_module: "verify",
            result: match s.verdict { Safe => "PASS", Unsafe => "FAIL", ... }
        })

    // ... (similarly for all analysis modules)

    // Determine overall verdict
    verdict := if all steps pass then "verified" else "issues detected"

    return ProofOutput { verdict, proof_steps: steps, ... }
```

### 4.4 Lint Integration

Proof certificates are emitted as Z01 lint notes, providing a record of
verification status in the standard diagnostic stream:

```
  Z01 [note]: Proof certificate generated — verdict: verified
              Steps: confluence (PASS), safety (PASS), ...
```

---

## 5. Repair Engine (`repair.rs`)

### 5.1 Intuition

When analyses detect failures -- non-joinable critical pairs, safety
violations, morphism gaps, bisimulation mismatches -- the repair engine
transforms these failures into actionable fix suggestions.  Each suggestion
carries quantitative metrics (confidence, edit cost, alternative count)
derived from semiring values, enabling multi-criteria ranking.

### 5.2 Repair Suggestion Structure

```rust
pub struct RepairSuggestion {
    pub kind: RepairKind,           // what kind of fix
    pub description: String,        // human-readable explanation
    pub confidence: f64,            // [0.0, 1.0] from FuzzyWeight
    pub edit_cost: u32,             // minimum edit cost from EditWeight
    pub alternative_count: u64,     // from CountingWeight
    pub action: RepairAction,       // the concrete code change
}
```

### 5.3 Repair Kind Taxonomy

The 11 repair kinds cover all analysis failure modes:

| Kind                     | Source analysis   | Description                              |
|--------------------------|-------------------|------------------------------------------|
| `AddRule`                | grammar/lint      | Add a missing grammar rule               |
| `AddCrossRef`            | grammar/lint      | Add cross-category reference             |
| `Disambiguate`           | grammar/lint      | Disambiguate an ambiguous prefix          |
| `AddCongruence`          | grammar/lint      | Add missing congruence rule              |
| `FixConfluence`          | confluence        | Add equation to resolve critical pair    |
| `FixTermination`         | termination       | Add guard to break non-terminating cycle |
| `StrengthenPrecondition` | verify/KAT        | Strengthen Hoare triple precondition     |
| `WeakenPostcondition`    | verify/KAT        | Weaken Hoare triple postcondition        |
| `FixBisimulation`        | alternating       | Add transition to fix bisimulation       |
| `CompleteMorphism`       | morphism          | Add morphism translation case            |
| `Custom(String)`         | any               | Generic custom repair                    |

### 5.4 Repair Action Types

Each `RepairAction` describes a concrete code change:

```rust
pub enum RepairAction {
    AddRuleToCategory { category: String, rule_skeleton: String },
    AddCrossCategoryRef { from_category: String, to_category: String, rule_label: String },
    AddCongruenceRule { constructor: String, category: String, rule_text: String },
    AddEquation { lhs: String, rhs: String },
    AddRewrite { lhs: String, rhs: String, direction: String },
    Description(String),
}
```

### 5.5 Multi-Criteria Ranking

The `RepairSet` collection supports multiple ranking strategies:

**By confidence** (FuzzyWeight-derived):
```
  sort by confidence descending
  best_by_confidence() -> highest confidence suggestion
```

**By edit cost** (EditWeight-derived):
```
  sort by edit_cost ascending
  cheapest() -> lowest cost suggestion
```

**Multi-criteria score**:
```
  score = confidence / (edit_cost + 1)
  Higher score = better suggestion (high confidence, low cost)
```

```
function rank_multi_criteria(suggestions) -> [(suggestion, score)]:
    for s in suggestions:
        score := s.confidence / (s.edit_cost + 1.0)
    sort by score descending
    return ranked list
```

**Filtering**:
```
  filter_by_confidence(min)  -> only suggestions with confidence >= min
  filter_by_max_cost(max)    -> only suggestions with edit_cost <= max
  top_n_by_confidence(n)     -> top N by confidence
  top_n_by_cost(n)           -> top N by cheapest cost
```

### 5.6 Diagram: Repair Engine Data Flow

```
  ┌──────────────────────────────────────────────────────────────┐
  │                    Analysis Results                          │
  │                                                              │
  │  confluence    verify    morphism    alternating    grammar   │
  │  (S01)        (T01)     (M01)       (N05)         (W01,G03) │
  └──────┬─────────┬─────────┬───────────┬─────────────┬────────┘
         │         │         │           │             │
         ▼         ▼         ▼           ▼             ▼
  ┌──────────────────────────────────────────────────────────────┐
  │                    Repair Suggestion Generators              │
  │                                                              │
  │  suggest_    suggest_    suggest_    suggest_    suggest_     │
  │  confluence  safety      morphism   bisim       missing      │
  │  _repairs    _repairs    _gaps      _fixes      _rules       │
  └──────┬─────────┬─────────┬───────────┬─────────────┬────────┘
         │         │         │           │             │
         ▼         ▼         ▼           ▼             ▼
  ┌──────────────────────────────────────────────────────────────┐
  │                       RepairSet                              │
  │                                                              │
  │  merge()  →  deduplicate by description                     │
  │  rank_multi_criteria()  →  score = confidence / (cost + 1)  │
  │  filter_by_confidence(0.5)  →  drop low-confidence fixes    │
  │  top_n_by_confidence(3)  →  present top 3                   │
  └──────────────────────────┬───────────────────────────────────┘
                             │
                             ▼
  ┌──────────────────────────────────────────────────────────────┐
  │                  Lint Enrichment                             │
  │                                                              │
  │  T01 diagnostics → [repair: AddEquation ...]                │
  │  M01 diagnostics → [repair: CompleteMorphism ...]           │
  │  W01 diagnostics → [repair: AddCrossRef ...]                │
  │  G03 diagnostics → [repair: AddRule ...]                    │
  └──────────────────────────────────────────────────────────────┘
```

### 5.7 Grammar Completion Suggestions

```
function suggest_missing_rules(category, missing_tokens) -> RepairSet:
    set := empty
    for token in missing_tokens:
        skeleton := "NewRule . {category} ::= \"{token}\" ... ;"
        set.add(RepairSuggestion {
            kind: AddRule,
            description: "Add a rule to {category} starting with '{token}'",
            confidence: 0.7,
            edit_cost: 2,
            action: AddRuleToCategory { category, skeleton }
        })
    return set
```

### 5.8 Cross-Category Reference Suggestions

```
function suggest_cross_category_ref(dead_rule, dead_cat, reachable_cats)
    -> RepairSet:
    set := empty
    for cat in reachable_cats:
        set.add(RepairSuggestion {
            kind: AddCrossRef,
            description: "Add reference from {cat} to {dead_cat}",
            confidence: 0.85,
            edit_cost: 1,
            action: AddCrossCategoryRef { from: cat, to: dead_cat, ... }
        })
    return set
```

### 5.9 Congruence Rule Synthesis

```
function suggest_congruence_rules(constructor, category, arity)
    -> RepairSet:
    set := empty
    for pos in 0..arity:
        // Build congruence rule: replace argument at position pos
        lhs := "({constructor} X0 ... S ... Xn)"   // S at position pos
        rhs := "({constructor} X0 ... T ... Xn)"   // T at position pos
        rule_text := "{constructor}Cong{pos} . |- S ~> T |- {lhs} ~> {rhs} ;"

        set.add(RepairSuggestion {
            kind: AddCongruence,
            description: "Add congruence rule for {constructor} at position {pos}",
            confidence: 0.95,
            edit_cost: 1,
            action: AddCongruenceRule { constructor, category, rule_text }
        })
    return set
```

### 5.10 Lint Enrichment

The repair engine integrates with existing lint diagnostics by appending
repair hints to relevant lint codes:

**TRS repair enrichment** (feature `trs-analysis`):
```
function enrich_diagnostics_with_repairs(diagnostics, confluence_result, syntax):
    if confluence_result is confluent: return
    repairs := suggest_confluence_repairs(confluence_result)
    for diag in diagnostics where diag.id == "T01":
        diag.hint += " [repair: {repairs}]"
```

**Morphism repair enrichment** (feature `morphisms`):
```
function enrich_diagnostics_with_morphism_repairs(diagnostics, morphism_result):
    if morphism_result is complete: return
    for diag in diagnostics where diag.id == "M01":
        diag.hint += " [repair: {gap_count} gaps -- add mappings]"
```

### 5.11 Context-Sensitive Codegen Analysis

The repair module also supports analysis-driven optimizations:

**Context dispatch hints** identify categories where different callers
enable different rule subsets, allowing caller-specific dispatch code:

```rust
pub struct ContextDispatchHint {
    pub category: String,       // category being dispatched
    pub caller: String,         // calling context
    pub valid_rules: Vec<String>,    // rules valid in this context
    pub skippable_rules: Vec<String>, // rules dead in this context
}
```

**Congruence fusion hints** identify congruence rules sharing the same
constructor that can be merged into a single match arm:

```rust
pub struct CongruenceFusionHint {
    pub constructor: String,
    pub category: String,
    pub rule_count: usize,
    pub argument_positions: Vec<usize>,
}
```

---

## 6. Interaction Between Meta-Level Analyses

```
  ┌──────────────────────────────────────────────────────────────────┐
  │                     Meta-Level Analyses                         │
  │                                                                  │
  │   ┌─────────────┐  ┌──────────┐  ┌────────────┐  ┌──────────┐ │
  │   │  Morphism    │  │   KAT    │  │  Tensor    │  │  Repair  │ │
  │   │             │  │          │  │            │  │          │ │
  │   │ Cross-theory│  │ Decidable│  │ Combined   │  │ Ranked   │ │
  │   │ translation │  │ Hoare    │  │ semiring   │  │ fix      │ │
  │   │             │  │ logic    │  │ analyses   │  │ suggest. │ │
  │   └──────┬──────┘  └─────┬────┘  └──────┬─────┘  └─────┬────┘ │
  │          │               │              │               │      │
  │          ▼               ▼              ▼               ▼      │
  │       M01/M02         K01/K02       (internal)      T01/M01   │
  │                                                     W01/G03   │
  └──────────────────────────────────────────────────────────────────┘
```

- **Morphism + KAT**: a theory morphism between two grammars induces a
  KAT homomorphism between their control flows.  If the morphism preserves
  axioms, the KAT equivalence of the source and target parse flows follows.
- **Morphism + Repair**: morphism gaps feed directly into the repair engine,
  producing `CompleteMorphism` suggestions with sort/operation mappings.
- **KAT + Repair**: violated Hoare triples produce `StrengthenPrecondition`
  or `WeakenPostcondition` repair suggestions.
- **Tensor + any analysis**: tensor products combine any two semiring-based
  analyses (e.g., Tropical cost + Viterbi probability) into a single pass
  with cross-analysis correlation.
- **Proof output**: aggregates results from all meta-level analyses into a
  single certificate with per-step justifications.

---

## 7. References

- J.A. Goguen & R.M. Burstall (1992). "Institutions: abstract model
  theory for specification and programming." *JACM*, 39(1), pp. 95--146.
- T. Mossakowski (2005). "Heterogeneous specification and the heterogeneous
  tool set." Habilitation thesis, University of Bremen.
- F. Rabe & M. Kohlhase (2013). "A scalable module system." *Information
  and Computation*, 230, pp. 1--54.
- W.M. Farmer (2000). "An infrastructure for intertheory reasoning."
  *Automated Deduction -- CADE-17*, LNCS 1831, pp. 115--131.
- D. Kozen (1997). "Kleene algebra with tests." *TOPLAS*, 19(3),
  pp. 427--443.
- D. Kozen & F. Smith (1996). "Kleene algebra with tests: completeness and
  decidability." *CSL 1996*, LNCS 1258, pp. 244--259.
- D. Pous (2015). "Symbolic algorithms for language equivalence and Kleene
  algebra with tests." *POPL 2015*, pp. 357--368.
- D. Kozen (2000). "On Hoare logic and Kleene algebra with tests."
  *TOPLAS*, 22(2), pp. 307--340.
- J.A. Brzozowski (1964). "Derivatives of regular expressions." *JACM*,
  11(4), pp. 481--494.
