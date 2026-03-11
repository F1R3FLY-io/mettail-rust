# Morphological Decomposition — Feature Extraction Theory

## Motivation

By analogy with computational linguistics morphological analysis — where a word
is decomposed into morphemes that determine its grammatical class — we decompose
predicate formulas into algebraic morphemes that determine which automata
varieties are needed.

**Core question**: What are the minimal syntactic features that determine which
automata varieties are needed to analyze a predicate?

## Definitions

**Definition 2.1** (Predicate Morpheme). A **predicate morpheme** is a syntactic
pattern in a `PredicateExpr` or `WeightedMsoFormula` AST that triggers membership
in a specific automata variety. Morphemes are the "atoms" of variety classification.

**Definition 2.2** (Morphological Decomposition). The **morphological decomposition**
of a formula φ is the multiset of morphemes extracted by a single post-order
traversal of the AST. Formally: morph(φ) = ⊎_{node ∈ φ} morpheme(node).

**Definition 2.3** (Variety Activation Function). The **variety activation function**
α : Morphemes → 2^{M₁,...,M₁₁} maps each morpheme to the set of modules it
activates:

```
α(ForallInfinite)     = {M2, M3}       (ω-regular + alternating)
α(ExistsInfinite)     = {M2}           (ω-regular)
α(ForallFinite)       = {M3}           (alternating)
α(Relation_eq)        = {M6}           (data languages)
α(Relation_count)     = {M9}           (multiset)
α(CrossChannelRef)    = {M8, M11}      (multi-tape + two-way)
α(RecursivePredicate) = {M4, M5}       (VPL + μ-calculus)
α(MultiGuard)         = {M7}           (probabilistic)
α(*)                  = {M1, M10}      (base: symbolic + MSO, always)
```

The overall signature is: σ(φ) = ⋃_{m ∈ morph(φ)} α(m)

## Extraction Algorithm

Full pseudocode with O(|φ|) time complexity:

```
EXTRACT-FEATURES(φ, Γ):
  Input:  PredicateExpr φ, ChannelContext Γ
  Output: PredicateProfile

  sig ← {M1, M10}                            ▷ base modules always active
  depth ← 0, channels ← ∅, registers ← ∅
  backward ← false, cardinality ← false, recursive ← false

  WALK(node):
    match node:
      True | False | Atom(a)  →  ⟨no change⟩

      Not(ψ)                  →  WALK(ψ)

      And(ψ₁, ψ₂)            →  WALK(ψ₁); WALK(ψ₂)
      Or(ψ₁, ψ₂)             →  WALK(ψ₁); WALK(ψ₂)

      ForallFinite(x, D, ψ)  →  sig ← sig ∪ {M3}
                                 depth ← depth + 1
                                 WALK(ψ)

      ExistsFinite(x, D, ψ)  →  depth ← depth + 1
                                 WALK(ψ)

      ForallInfinite(x, ψ)   →  sig ← sig ∪ {M2, M3}
                                 depth ← depth + 1
                                 WALK(ψ)

      ExistsInfinite(x, ψ)   →  sig ← sig ∪ {M2}
                                 depth ← depth + 1
                                 WALK(ψ)

      Relation(name, args)    →
        if IS-EQUALITY(name)  then
          sig ← sig ∪ {M6}
          registers ← registers ∪ args
        if IS-CARDINALITY(name) then
          sig ← sig ∪ {M9}
          cardinality ← true
        for arg in args:
          if Γ.channel(arg) ≠ current_channel:
            sig ← sig ∪ {M8, M11}
            channels ← channels ∪ {Γ.channel(arg)}
            backward ← true
        if ¬IS-EQUALITY(name) ∧ ¬IS-CARDINALITY(name):
          sig ← sig ∪ {M6}            ▷ unknown relations default to register

      Bounded(ψ, k)           →  WALK(ψ)

  WALK(φ)
  if |channels| ≥ 2:
    sig ← sig ∪ {M7, M8}               ▷ multi-guard → selectivity ordering
  return PredicateProfile {
    signature: sig,
    quantifier_depth: depth,
    channel_count: |channels|,
    register_count: |registers|,
    has_backward_constraint: backward,
    has_cardinality: cardinality,
    has_recursive_predicate: recursive,
    decidability_tier: classify_decidability(φ),
  }
```

**Complexity**: O(|φ|) time (single post-order traversal), O(depth(φ)) stack space.

The MSO variant `extract_features_mso()` follows the same pattern for
`WeightedMsoFormula` nodes, with additional rules:
- `ForallFirst` / `ForallSecond` → M3 (alternating, universal branching)
- `AtomicPos { label: "letprop" }` → M4 + M5 (VPA + parity tree)
- `Order` / `NegOrder` → M6 (register, positional data)
- `InSet` / `NotInSet` → check for cross-channel references

## Worked Examples

### Example 2.1: Simple Equality Guard

```rholang
for (@x : x == last_seen <- ch) { P }
```

**AST**: `Relation { name: "eq", args: ["x", "last_seen"] }`
**Morphemes**: {Relation_eq}
**Activation**: α(Relation_eq) ∪ α(*) = {M1, M6, M10}
**Dispatch**: M1 (symbolic algebra), M6 (register tracking), M10 (MSO spec)

### Example 2.2: Cross-Channel Constraint

```rholang
for (@x <- ch1, @y : related(x) <- ch2) { P }
```

**Step-by-step trace**:
1. Enter `Relation { name: "related", args: ["x"] }`
2. `"related"` is not equality or cardinality → sig ∪ {M6}
3. `Γ.channel("x") = "ch1"`, current channel is `"ch2"` → cross-channel!
4. sig ∪ {M8, M11}, backward ← true, channels = {"ch1", "ch2"}
5. Post-walk: |channels| = 2 ≥ 2 → sig ∪ {M7, M8}
6. **Final signature**: M1 | M6 | M7 | M8 | M10 | M11

```
Bit accumulation:
  Base:           .... .... ..10 0000 0001  (M1 | M10)
  + M6 (register): .... .... ..10 0010 0001
  + M8 (multi):    .... .... ..10 1010 0001
  + M11 (two-way): .... .... .110 1010 0001
  + M7 (prob):     .... .... .110 1110 0001
  Final (0x06E1):  0000 0110 1110 0001
```

### Example 2.3: Recursive Behavioral Predicate

```rholang
letprop halt x = forall y. ~(x ->* y) in
for (@x : halt <- ch) { P }
```

**Morphemes**: {RecursivePredicate, ForallInfinite}
**Activation**: α(RecursivePredicate) ∪ α(ForallInfinite) ∪ α(*)
             = {M4, M5} ∪ {M2, M3} ∪ {M1, M10}
             = {M1, M2, M3, M4, M5, M10}
**Dispatch**: M1, M2 (Büchi for liveness), M3 (alternating for ∀), M4 (VPA for
nested letprop scope), M5 (parity tree for μ-calculus fixpoint), M10 (MSO spec)

## Soundness Proof

**Lemma 1.1** (from `variety-classification.md`). For any predicate formula φ
and channel context Γ:

  { M_i : M(⟦φ⟧) ∈ 𝐕_i }  ⊆  { M_i : bit i set in extract_features(φ, Γ).signature }

*Proof*: By structural induction on the AST of φ.

**Base cases** (True, False, Atom):
  The denotation ⟦True⟧ = Σ*, ⟦False⟧ = ∅, ⟦Atom(a)⟧ ⊆ Reg(Σ*).
  All regular languages have M(L) ∈ 𝐁𝐚𝐥𝐥 (the variety of all finite monoids),
  which corresponds to M10 (MSO). Their syntactic monoids may also be aperiodic
  (M1). Both M1 and M10 are in BASE, which is always set. ∎ for base cases.

**Inductive case** (Not, And, Or):
  Boolean operations preserve variety membership (Definition 1.5). The algorithm
  recursively processes subformulas, accumulating bits. Since sig only grows
  (no bits are ever cleared), the superset property is maintained. ∎

**Inductive case** (ForallInfinite):
  Universal quantification over infinite domains requires ω-regular acceptance
  (variety 𝐆, module M2) and alternation (variety 𝐉₁, module M3). The algorithm
  sets both M2 and M3 bits. Any variety 𝐕_i that could be triggered by the body
  is captured by the recursive WALK call. ∎

**Inductive case** (Relation):
  - Equality relations require data comparison → variety beyond regular (M6).
  - Cardinality relations require counting → commutative variety (M9).
  - Cross-channel references require multi-tape synchronization (M8) and
    bidirectional scanning (M11).
  In each case, the algorithm sets the appropriate bits. Unknown relation names
  default to M6 (conservative: register automata handle general data predicates). ∎

**Inductive case** (Bounded):
  Bounding does not introduce new variety requirements; the algorithm processes
  the body. ∎

Since every inductive step either (a) sets the correct bits or (b) sets a superset
of the correct bits, and bits are never cleared, the signature produced by
`extract_features()` is a superset of the true variety requirements. ∎

## §4 Grammar-Level Morphemes

The morphological decomposition framework extends beyond predicate-level analysis
to grammar-level structural patterns. Grammar morphemes are detected by
`classify_grammar()` before predicates are parsed, providing conservative module
activation based on rule structure alone.

### Definition 4.1 (Grammar Morpheme)

A **grammar morpheme** is a structural pattern in the triple
`(label: String, category: String, syntax: Vec<SyntaxItemSpec>)` that triggers
module activation. Grammar morphemes are the grammar-level analogues of the
predicate morphemes defined in §2.

The complete set of grammar morphemes:

| Grammar Morpheme | Detection | Predicate Analogue |
|-----------------|-----------|-------------------|
| DirectRecursion(C) | C ∈ refs(C) | ForallInfinite / ExistsInfinite |
| HighBranching(≥3) | ≥3 NonTerminal/Binder children | ForallFinite (universal branching) |
| PairedDelimiters | `()`/`{}`/`[]`/`begin..end` in terminals | RecursivePredicate (letprop scope) |
| RecursiveBranching | DirectRecursion ∧ HighBranching | Recursive fixpoint |
| NameBinding | Binder items present | Relation_eq (equality/freshness) |
| CategoryAmbiguity(≥3) | ≥3 rules sharing same category | MultiGuard (≥2 channels) |
| CrossCategoryRef | ≥2 distinct categories in one rule | CrossChannelRef |
| CollectionStructure | Collection / Sep items | Relation_count (cardinality) |

### Definition 4.2 (Grammar Activation Function)

The **grammar activation function** β : GrammarMorphemes → 2^{M₁,...,M₁₁} maps
each grammar morpheme to the set of modules it activates:

```
β(DirectRecursion)                = {M2}           Büchi
β(HighBranching)                  = {M3}           AWA
β(PairedDelimiters)               = {M4}           VPA
β(DirectRecursion ∩ HighBranching) = {M5}          Parity Tree
β(NameBinding)                    = {M6}           Register
β(CategoryAmbiguity)              = {M7}           Probabilistic
β(CrossCategoryRef)               = {M8, M11}      Multi-Tape + Two-Way
β(CollectionStructure)            = {M9}           Multiset
β(*)                              = {M1, M10}      Base (always)
```

The overall grammar signature is: σ_β(G) = ⋃_{m ∈ morph_β(G)} β(m)

### Conservative Approximation Relationship

Grammar morphemes conservatively approximate predicate morphemes:

**Theorem 4.1**: For any grammar G,
  σ_β(G) ⊇ σ_α(predicates_implied_by(G))

That is, the grammar activation function activates a superset of what the predicate
activation function would activate for the predicates implied by the grammar structure.
This ensures no false negatives: if a grammar's structure implies the need for a
module, the grammar heuristic activates it. False positives are acceptable because
extra module runs are cheap (O(|states|²) per module).

For the full formal soundness argument, see
[conservative-approximation.md](conservative-approximation.md).

### Implementation

Grammar morpheme detection runs in `classify_grammar()` (predicate_dispatch.rs)
in O(|rules| × max|syntax|) time, dominated by the single-pass scan over all
rules and their syntax items. No graph construction or cycle detection is needed
for direct recursion — it is a simple check `C ∈ refs(C)`.

## References

- Eilenberg, S. (1976). *Automata, Languages, and Machines*, Vol. B. Academic Press.
- Pin, J.-É. (1986). *Varieties of Formal Languages*. Plenum.
- Straubing, H. (1994). *Finite Automata, Formal Logic, and Circuit Complexity*. Birkhäuser.
- Alur, R. & Madhusudan, P. (2004). Visibly pushdown languages. *STOC 2004*.
- Kaminski, M. & Francez, N. (1994). Finite-memory automata. *TCS* 134(2).
- Rabin, M. (1969). Decidability of second-order theories and automata on infinite trees. *TAMS* 141.
- Büchi, J.R. (1962). On a decision method in restricted second-order arithmetic. *Logic, Meth., Phil. of Sci.*
