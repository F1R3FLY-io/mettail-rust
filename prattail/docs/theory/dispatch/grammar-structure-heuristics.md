# Grammar Structure Heuristics — Predicate-Free Variety Approximation

## 1. Motivation

The morphological decomposition (`morphological-decomposition.md`) extracts variety
membership from predicate ASTs. The variety classification (`variety-classification.md`)
maps syntactic monoid membership to automata modules. Both mechanisms require
predicates to be present in the grammar. But what if predicates have not yet been
written? Can we infer which automata modules will *eventually* be needed from the
grammar structure alone?

**Key observation**: Grammar rule shapes are *syntactic fingerprints* of the
computational classes that will appear in predicates. A grammar with recursive
productions, paired delimiters, name binders, and high branching factors exhibits
structural patterns that correlate strongly with the algebraic complexity of its
eventual predicate formulas.

**Why this matters**: When PraTTaIL compiles a grammar before any predicates are
attached (the common case during grammar development), it can still pre-allocate
analysis infrastructure for the modules that the grammar's structure implies.
This enables:

1. **Early diagnostic generation** — lints can warn about likely analysis
   requirements before predicates exist.
2. **Infrastructure pre-warming** — data structures for register tracking,
   VPA stacks, and Buchi acceptance can be allocated eagerly.
3. **Conservative correctness** — by over-approximating the eventual predicate
   variety, we never miss a needed module.

The theoretical foundation is Eilenberg's variety theorem (1976): the syntactic
monoid of a regular language determines which pseudovariety it belongs to.
Grammar structure constrains the space of languages that can be expressed, which
in turn constrains the space of syntactic monoids, which in turn constrains the
relevant pseudovarieties. Our heuristic scan computes a *conservative upper
approximation* of the exact variety classification — the same relationship that
`extract_features()` has to exact syntactic monoid computation, but lifted one
level from predicate ASTs to grammar rule structure.

Formally, let `morph` be the morphological decomposition of predicates
(Definition 2.2 of `morphological-decomposition.md`) and let `α` be the variety
activation function (Definition 2.3). The grammar-level activation function `β`
defined here satisfies:

  α(morph(φ)) ⊆ β(grammar(φ))   for all predicates φ expressible in the grammar

That is, `β` over-approximates the predicate-level dispatch for every formula
that the grammar can parse. This is the sense in which grammar structure
"fingerprints" predicate variety.


## 2. Definitions

### Definition 3.1 (Grammar Morpheme)

A **grammar morpheme** is a structural pattern extracted from the set of grammar
rules R = { (label_i, category_i, syntax_i) }, where each rule is a
`RuleSpec` triple of `(label: String, category: String, syntax: Vec<SyntaxItemSpec>)`.

We define eight morpheme types, each capturing a distinct structural feature of
the grammar:

**GM1. DirectRecursion(C)**

Category C contains a rule whose `syntax` vector includes a `NonTerminal` item
referencing category C itself. Formally:

  ∃ r = (l, C, s) ∈ R, ∃ item ∈ s : item = NonTerminal { category: C, ... }

*Intuition*: Direct recursion indicates self-referential structure — the grammar
can generate unboundedly nested terms of the same syntactic sort. This is the
hallmark of languages requiring fixpoint reasoning, which maps to omega-regular
acceptance (Buchi automata).

*Example*: An expression grammar where `Expr → Expr "+" Expr` is directly
recursive in category `Expr`.

**GM2. CyclicRecursion(C₁, ..., Cₖ)**

Categories C₁, ..., Cₖ form a strongly connected component (SCC) of size k ≥ 2
in the category dependency graph, where an edge C → C' exists iff some rule in
category C references C' as a `NonTerminal`.

  ∃ C₁ →⁺ C₂ →⁺ ... →⁺ Cₖ →⁺ C₁ in the category dependency graph

*Intuition*: Mutual recursion between categories creates interleaved nesting
patterns that are strictly more complex than direct recursion. The cycle structure
often corresponds to alternating quantifier patterns in predicates.

*Example*: `Proc → "for" "(" Pattern "<-" Name ")" "{" Proc "}"` and
`Pattern → Proc`, forming a cycle between `Proc` and `Pattern`.

**GM3. HighBranching(n)**

A rule has n ≥ 3 non-terminal children in its `syntax` vector. The threshold
n = 3 distinguishes binary operators (common, simple) from rules that combine
three or more subexpressions (uncommon, indicating alternating or tree-like
computation).

  ∃ r = (l, C, s) ∈ R : |{ item ∈ s : item is NonTerminal }| ≥ 3

*Intuition*: High branching corresponds to alternating universal/existential
quantification in predicates. A rule with k non-terminal children can express
k-way choices or k-fold universal constraints, requiring alternating weighted
automata (AWA) for analysis.

*Example*: A ternary conditional `Expr → Expr "?" Expr ":" Expr` has 3
non-terminal children.

**GM4. PairedDelimiters(open, close)**

A rule's `syntax` vector contains two `Terminal` items that form a matching
delimiter pair. The recognized pairs are:

  { ("(", ")"), ("[", "]"), ("{", "}"), ("⟨", "⟩"), ("⟪", "⟫") }

  ∃ r = (l, C, s) ∈ R, ∃ i < j :
    s[i] = Terminal(open) ∧ s[j] = Terminal(close) ∧ (open, close) ∈ Pairs

*Intuition*: Paired delimiters create a call/return structure that is the
defining characteristic of visibly pushdown languages (VPL). The nesting depth
cannot be tracked by a finite-state automaton; a pushdown stack is required.
This maps directly to VPA (M4).

*Example*: `Expr → "(" Expr ")"` uses the pair `("(", ")")`.

**GM5. NameBinding(var, cat)**

A rule contains a `Binder` item, which introduces a bound variable into scope.

  ∃ r = (l, C, s) ∈ R, ∃ item ∈ s :
    item = Binder { param_name: var, category: cat, ... }

*Intuition*: Name binding introduces data values (variable names) that must be
compared for equality across scopes. This requires register automata (M6), which
extend finite automata with a finite set of registers for storing and comparing
data values. The connection to Kaminski & Francez's (1994) register automata is
direct: each `Binder` corresponds to a register store operation.

*Example*: `Proc → "new" Name "in" "{" Proc "}"` binds a channel name.

**GM6. CollectionStructure(cat)**

A rule contains a `Collection` or `Sep` item, indicating that the grammar handles
variable-length sequences of elements.

  ∃ r = (l, C, s) ∈ R, ∃ item ∈ s :
    item = Collection { element_category: cat, ... }
    ∨ item = Sep { ... }

*Intuition*: Collections are inherently commutative when order is irrelevant to
semantics (e.g., argument lists, set literals, parallel compositions). The
commutativity maps to the commutative pseudovariety **Com** and multiset automata
(M9). Even when order matters syntactically, the presence of collection structure
signals that cardinality predicates (how many elements satisfy a property) are
likely, and these require commutative semigroup structure.

*Example*: `Args → Sep(Expr, ",")` represents a comma-separated argument list.

**GM7. CrossCategoryReference(C₁ → C₂)**

A rule in category C₁ references a `NonTerminal` in a different category C₂,
where C₁ ≠ C₂.

  ∃ r = (l, C₁, s) ∈ R, ∃ item ∈ s :
    item = NonTerminal { category: C₂, ... } ∧ C₁ ≠ C₂

*Intuition*: Cross-category references create multi-sorted term structure.
When predicates constrain relationships between terms of different sorts, this
requires multi-tape automata (M8) — one tape per sort — and potentially
bidirectional scanning (M11) to correlate constraints across sorts.

*Example*: `Proc → "for" "(" Pattern "<-" Name ")" "{" Proc "}"` references
three different categories: `Pattern`, `Name`, and `Proc`.

**GM8. CategoryAmbiguity(C, k)**

Category C has k ≥ 3 distinct rules (i.e., k ≥ 3 distinct labels for rules in
category C). The threshold k = 3 distinguishes simple categories (one or two
alternatives) from categories with genuine nondeterministic choice.

  |{ l : (l, C, s) ∈ R }| = k ≥ 3

*Intuition*: High rule count per category creates parsing ambiguity that maps
to probabilistic automata (M7). When multiple rules can match the same input
prefix, the grammar implicitly encodes a nondeterministic choice. In the
presence of predicates, this nondeterminism is typically resolved by priority
or probability weights, which require stochastic analysis infrastructure.

*Example*: A `Proc` category with rules for `PPar`, `PNew`, `PSend`, `PRecv`,
`PIf`, `PMatch`, `PNil`, `PEval`, etc. — 8 alternatives.


### Definition 3.2 (Grammar Activation Function)

The **grammar activation function** β : GrammarMorphemes → 2^{M₁,...,M₁₁} maps
grammar morphemes (and their combinations) to the set of automata modules whose
pseudovarieties are implied by the structural pattern. The mapping is:

```
┌─────────────────────────────────────────────┬───────────────┬──────────────────┐
│  Grammar Morpheme(s)                        │  β(·)         │  Module(s)       │
├─────────────────────────────────────────────┼───────────────┼──────────────────┤
│  DirectRecursion(C)                         │  {M2}         │  Buchi           │
│  CyclicRecursion(C₁,...,Cₖ)                 │  {M2}         │  Buchi           │
│  HighBranching(n)                           │  {M3}         │  AWA             │
│  PairedDelimiters(open, close)              │  {M4}         │  VPA             │
│  DirectRecursion(C) ∩ HighBranching(n)      │  {M5}         │  Parity Tree     │
│  NameBinding(var, cat)                      │  {M6}         │  Register        │
│  CategoryAmbiguity(C, k)                    │  {M7}         │  Probabilistic   │
│  CrossCategoryReference(C₁ → C₂)           │  {M8, M11}    │  Multi-Tape,     │
│                                             │               │  Two-Way         │
│  CollectionStructure(cat)                   │  {M9}         │  Multiset        │
│  * (any grammar)                            │  {M1, M10}    │  Symbolic,       │
│                                             │               │  Weighted MSO    │
└─────────────────────────────────────────────┴───────────────┴──────────────────┘
```

Several points deserve elaboration:

**Base modules (M1, M10)**: Every grammar, regardless of structure, activates the
symbolic automata module (M1) and weighted MSO module (M10). M1 provides the
Boolean algebra over token predicates. M10 provides the full MSO specification
language. These are the "floor" of the variety lattice — every regular language
belongs to the variety of all finite monoids (**Ball**) and has an MSO definition.

**Compound morpheme (DirectRecursion ∩ HighBranching)**: When a category is both
directly recursive *and* has high-branching rules, the combination signals tree
structure with infinite paths — the domain of parity tree automata (M5) and the
μ-calculus. Neither morpheme alone triggers M5: direct recursion without
branching is linear (Buchi suffices), and branching without recursion is bounded
(AWA suffices). The intersection creates the unbounded-branching-with-recursion
pattern that requires parity acceptance.

**Multi-Tape and Two-Way co-activation**: Cross-category references activate both
M8 and M11 because multi-sorted constraints typically require both multi-tape
synchronization (reading from different sorts simultaneously) and bidirectional
scanning (correlating a constraint on sort C₁ with information from sort C₂ that
may appear earlier or later in the input). This mirrors the predicate-level
co-activation of M8 and M11 for cross-channel references (Definition 2.3 of
`morphological-decomposition.md`).


## 3. Conservative Approximation Theorem

### Theorem 3.1 (Conservative Approximation)

For any grammar G with rules R, let β(G) = ⋃_{m ∈ morphemes(R)} β(m) be the
grammar-level activation, and let α(morph(φ)) be the predicate-level activation
for any predicate φ expressible in G. Then:

  α(morph(φ)) ⊆ β(G)

That is, the grammar-level activation is a superset of the predicate-level
activation for every predicate that the grammar can express.

**Proof**: We prove each inclusion α(m) ⊆ β(G) by showing that every predicate
morpheme m has a corresponding grammar morpheme whose β-image contains α(m).

**Case 1: α(ForallInfinite) = {M2, M3}**

A `ForallInfinite(x, ψ)` predicate quantifies universally over an infinite domain.
For this to be expressible, the grammar must support infinite structures — which
requires either direct recursion (generating unboundedly many terms) or cyclic
recursion (mutually recursive term generation). In either case,
β(DirectRecursion) ⊇ {M2} or β(CyclicRecursion) ⊇ {M2}. The universal
quantifier also requires the grammar to express alternation, which is indicated
by branching structure: multiple subterms must all satisfy the quantified
property. Thus β(HighBranching) ⊇ {M3} when present, or {M3} is conservatively
included via the interaction of recursion with any branching.

More precisely, `ForallInfinite` requires the grammar to generate infinite
sequences of terms, each of which must be inspectable. This requires recursion
(GM1 or GM2), giving M2 ∈ β(G). The "for all" aspect requires inspecting
multiple branches, which is reflected in branching structure (GM3) when present.
If GM3 is not present, the over-approximation still holds: β(G) ⊇ {M2} ⊇ {M2}
∩ α(ForallInfinite), and M3 may be a spurious over-approximation when the
grammar lacks branching. But crucially, when `ForallInfinite` predicates *do*
exist, the grammar must have some form of branching or multi-term structure to
express the "for all" semantics, and this will manifest as either GM3 or as
multiple rules (GM8, contributing CategoryAmbiguity). ∎

**Case 2: α(ExistsInfinite) = {M2}**

Similar to Case 1, but only the Buchi component is required (existential
quantification does not require alternation). Recursion (GM1 or GM2) in the
grammar ensures β(G) ⊇ {M2}. ∎

**Case 3: α(ForallFinite) = {M3}**

Universal quantification over finite domains requires alternating automata for
the universal branching. Finite-domain quantification corresponds to inspecting
a bounded set of subterms, which manifests as either high branching (GM3) or
multiple alternatives in a category (GM8). In either case,
β(G) ⊇ {M3} or β(G) ⊇ {M7} ⊇ {M3} (since M7 subsumes M3's nondeterministic
analysis). Note: the over-approximation is conservative — β may activate M3
from grammar branching even when no `ForallFinite` predicate exists. ∎

**Case 4: α(Relation_eq) = {M6}**

Equality predicates compare data values. For equality to be meaningful, the
grammar must introduce named entities — i.e., it must have `Binder` items (GM5)
or `IdentCapture` items that create bindable names. The presence of `Binder`
items gives β(NameBinding) = {M6}. If the grammar uses `IdentCapture` without
`Binder`, the heuristic may not activate M6, but `IdentCapture` alone does not
support the scoped comparison that `Relation_eq` requires. ∎

**Case 5: α(Relation_count) = {M9}**

Cardinality predicates count elements in a collection. For counting to be
expressible, the grammar must have collection structure (GM6:
`Collection` or `Sep` items), giving β(CollectionStructure) = {M9}. ∎

**Case 6: α(CrossChannelRef) = {M8, M11}**

Cross-channel references in predicates correlate values from different syntactic
categories. For this to be expressible, the grammar must have cross-category
references (GM7), giving β(CrossCategoryReference) = {M8, M11}. ∎

**Case 7: α(RecursivePredicate) = {M4, M5}**

Recursive predicates (e.g., `letprop`) define fixpoint properties. For recursive
predicates to be expressible, the grammar must support nested scope (paired
delimiters, GM4) and recursive structure (GM1 or GM2). Paired delimiters give
β(PairedDelimiters) = {M4}. Recursion combined with branching gives
β(DirectRecursion ∩ HighBranching) = {M5}. ∎

**Case 8: α(MultiGuard) = {M7}**

Multi-guard predicates express nondeterministic choice weighted by priority or
probability. For multi-guard to be expressible, the grammar must have multiple
alternatives for the same syntactic category (GM8), giving
β(CategoryAmbiguity) = {M7}. ∎

**Summary of the proof structure**:

```
Predicate Morpheme        Requires Grammar Morpheme       β-image ⊇ α-image
─────────────────────     ─────────────────────────       ──────────────────
ForallInfinite            GM1 or GM2 (recursion)          {M2} ⊇ {M2}
                          + GM3 (branching)               {M3} ⊇ {M3}
ExistsInfinite            GM1 or GM2 (recursion)          {M2} ⊇ {M2}
ForallFinite              GM3 (branching)                 {M3} ⊇ {M3}
Relation_eq               GM5 (binders)                   {M6} ⊇ {M6}
Relation_count            GM6 (collections)               {M9} ⊇ {M9}
CrossChannelRef           GM7 (cross-cat refs)            {M8,M11} ⊇ {M8,M11}
RecursivePredicate        GM4 (paired delimiters)          {M4} ⊇ {M4}
                          + GM1 ∩ GM3 (rec + branch)      {M5} ⊇ {M5}
MultiGuard                GM8 (category ambiguity)         {M7} ⊇ {M7}
*                         * (always)                       {M1,M10} ⊇ {M1,M10}
```

Since every predicate morpheme's α-image is contained in the β-image of a
grammar morpheme that the grammar must possess for that predicate to be
expressible, we have α(morph(φ)) ⊆ β(G) for all φ expressible in G. ∎

### Corollary 3.1 (No False Negatives)

The grammar heuristic never under-approximates: if a module M_i is needed for
analyzing a predicate φ expressible in grammar G, then M_i ∈ β(G).

*Proof*: Immediate from Theorem 3.1. ∎

### Corollary 3.2 (Possible False Positives)

The grammar heuristic may over-approximate: β(G) may contain modules not
required by any predicate expressible in G.

*Example*: A grammar with paired delimiters `"(" ... ")"` activates M4 (VPA),
but if no predicate ever reasons about nesting depth, M4 is not truly needed.
The over-approximation is harmless: activating an unnecessary module wastes
some analysis time but never produces incorrect results.


## 4. Worked Examples

### Example 3.1: Simple Arithmetic

Consider a grammar for arithmetic expressions:

```
category Expr:
  Num   → NUMBER
  Add   → Expr "+" Expr
  Mul   → Expr "*" Expr
  Neg   → "-" Expr
  Paren → "(" Expr ")"
```

**Morpheme extraction**:

```
Rule    │ Morphemes Detected
────────┼───────────────────────────────────────────────────────
Num     │ (none — leaf rule, no non-terminals)
Add     │ GM1: DirectRecursion(Expr)       [Expr → Expr]
        │ GM7: CrossCategoryRef — no, both are Expr
Mul     │ GM1: DirectRecursion(Expr)       [Expr → Expr]
Neg     │ GM1: DirectRecursion(Expr)       [Expr → Expr]
Paren   │ GM1: DirectRecursion(Expr)       [Expr → Expr]
        │ GM4: PairedDelimiters("(", ")")
```

**Category-level analysis**:

- DirectRecursion(Expr): present → β ⊇ {M2}
- HighBranching: Add and Mul have 2 non-terminals, Neg has 1 → max = 2 < 3 → absent
- PairedDelimiters("(", ")"): present → β ⊇ {M4}
- NameBinding: no Binder items → absent
- CollectionStructure: no Collection/Sep items → absent
- CrossCategoryReference: all references are Expr → Expr → absent
- CategoryAmbiguity(Expr, 5): 5 rules → k = 5 ≥ 3 → present → β ⊇ {M7}
- DirectRecursion ∩ HighBranching: HighBranching absent → compound absent

**Final activation**:

```
β(G) = {M1, M10}        base (always)
     ∪ {M2}             DirectRecursion
     ∪ {M4}             PairedDelimiters
     ∪ {M7}             CategoryAmbiguity
     = {M1, M2, M4, M7, M10}
```

**Diagram**:

```
                ┌─ Expr ─┐
                │        │
  ┌─────────────┼────────┼─────────────┐
  │  Num        │  Add   │  Mul        │
  │  (leaf)     │        │             │
  │             │  ┌─┐   │  ┌─┐        │
  │             │  │E│+│E│  │E│*│E│    │
  │             │  └─┘   │  └─┘        │
  │  Neg        │  Paren               │
  │  ┌─┐        │  ┌───┐               │
  │  │-│E│      │  │(│E│)│             │
  │  └─┘        │  └───┘               │
  └─────────────┴──────────────────────┘

  Detected: GM1(Expr), GM4("(",")"), GM8(Expr,5)
  Activation: {M1, M2, M4, M7, M10}
```

This is a modest over-approximation: simple arithmetic likely only needs M1
(symbolic) and M10 (MSO). The M2 (Buchi), M4 (VPA), and M7 (probabilistic)
activations are conservative — they prepare infrastructure that would be needed
if predicates reasoned about recursive evaluation, nested parenthesization, or
ambiguous parse selection.


### Example 3.2: Lambda Calculus

Consider a grammar for the untyped lambda calculus:

```
category Expr:
  Var    → IDENT
  Lam    → "λ" @x:Name "." Expr
  App    → Expr Expr
  Let    → "let" @x:Name "=" Expr "in" Expr
  If     → "if" Expr "then" Expr "else" Expr
  Paren  → "(" Expr ")"
```

**Morpheme extraction**:

```
Rule    │ Morphemes Detected
────────┼───────────────────────────────────────────────────────────────
Var     │ (none — leaf)
Lam     │ GM5: NameBinding(x, Name)        [Binder item]
        │ GM1: DirectRecursion(Expr)        [Expr → Expr]
        │ GM7: CrossCategoryRef(Expr→Name)  [references Name]
App     │ GM1: DirectRecursion(Expr)        [Expr → Expr, twice]
Let     │ GM5: NameBinding(x, Name)         [Binder item]
        │ GM1: DirectRecursion(Expr)        [Expr → Expr, twice]
        │ GM7: CrossCategoryRef(Expr→Name)  [references Name]
If      │ GM1: DirectRecursion(Expr)        [Expr → Expr, three times]
        │ GM3: HighBranching(3)             [3 non-terminal children]
Paren   │ GM1: DirectRecursion(Expr)        [Expr → Expr]
        │ GM4: PairedDelimiters("(", ")")
```

**Category-level analysis**:

- DirectRecursion(Expr): present → β ⊇ {M2}
- CyclicRecursion: no mutual recursion (only Expr ↔ Expr, which is direct) → absent
- HighBranching(3): present (If rule) → β ⊇ {M3}
- PairedDelimiters("(", ")"): present → β ⊇ {M4}
- DirectRecursion ∩ HighBranching: **both present** → β ⊇ {M5}
- NameBinding(x, Name): present → β ⊇ {M6}
- CategoryAmbiguity(Expr, 6): 6 rules → β ⊇ {M7}
- CrossCategoryReference(Expr → Name): present → β ⊇ {M8, M11}
- CollectionStructure: absent

**Final activation**:

```
β(G) = {M1, M10}               base
     ∪ {M2}                    DirectRecursion
     ∪ {M3}                    HighBranching
     ∪ {M4}                    PairedDelimiters
     ∪ {M5}                    DirectRecursion ∩ HighBranching
     ∪ {M6}                    NameBinding
     ∪ {M7}                    CategoryAmbiguity
     ∪ {M8, M11}               CrossCategoryReference
     = {M1, M2, M3, M4, M5, M6, M7, M8, M10, M11}
```

Only M9 (multiset) is absent — the lambda calculus has no collection structure.

**Dependency graph**:

```
         Expr ──────→ Name
          ↺
    (self-loop)

    SCC analysis:
      • {Expr} — self-loop (DirectRecursion)
      • {Name} — leaf (no outgoing edges)
      • Cross-edge: Expr → Name (CrossCategoryReference)
```

**Module activation diagram**:

```
    Grammar Morphemes              Activated Modules
    ─────────────────              ─────────────────
    GM1 DirectRecursion ─────────→ M2  Buchi         ◉
    GM3 HighBranching ───────────→ M3  AWA            ◉
    GM4 PairedDelimiters ────────→ M4  VPA            ◉
    GM1 ∩ GM3 ──────────────────→ M5  Parity Tree    ◉
    GM5 NameBinding ─────────────→ M6  Register       ◉
    GM8 CategoryAmbiguity ───────→ M7  Probabilistic  ◉
    GM7 CrossCategoryRef ────────→ M8  Multi-Tape     ◉
                          └──────→ M11 Two-Way        ◉
    * (always) ──────────────────→ M1  Symbolic       ◉
                          └──────→ M10 Weighted MSO   ◉
    (absent) ────────────────────→ M9  Multiset       ○

    Legend: ◉ = activated, ○ = not activated
```


### Example 3.3: Rholang Process Algebra

Consider a representative fragment of the Rholang grammar:

```
category Proc:
  PNil     → "Nil"
  PPar     → Proc "|" Proc
  PNew     → "new" Sep(@x:Name, ",") "in" "{" Proc "}"
  PSend    → Name "!" "(" Sep(Proc, ",") ")"
  PRecv    → "for" "(" Sep(Bind, ";") ")" "{" Proc "}"
  PIf      → "if" Proc "then" Proc "else" Proc
  PMatch   → "match" Proc "{" Sep(Branch, ";") "}"
  PEval    → "*" Name

category Name:
  NVar     → IDENT
  NQuote   → "@" Proc

category Bind:
  BSimple  → Pattern "<-" Name
  BPeek    → Pattern "<<-" Name

category Pattern:
  PtVar    → IDENT
  PtWild   → "_"
  PtPar    → Pattern "|" Pattern
  PtList   → "[" Sep(Pattern, ",") "]"

category Branch:
  BrCase   → Pattern "=>" "{" Proc "}"
```

**Morpheme extraction** (summary):

```
Morpheme                           │  Source Rules
───────────────────────────────────┼──────────────────────────────────
GM1 DirectRecursion(Proc)          │  PPar, PNew, PSend, PRecv, PIf,
                                   │  PMatch (Proc → ... Proc ...)
GM1 DirectRecursion(Pattern)       │  PtPar (Pattern → Pattern "|" Pattern)
GM2 CyclicRecursion(Proc, Name)    │  Proc→Name (PSend, PRecv, PEval)
                                   │  Name→Proc (NQuote: "@" Proc)
GM2 CyclicRecursion(Proc, Bind,    │  Proc→Bind→Name→Proc
    Name)                          │
GM3 HighBranching(3)               │  PIf (3 non-terminal children)
GM4 PairedDelimiters("(",")")      │  PSend, PRecv
GM4 PairedDelimiters("{","}")      │  PNew, PRecv, PMatch, BrCase
GM4 PairedDelimiters("[","]")      │  PtList
GM5 NameBinding(x, Name)          │  PNew (Binder for channel name)
GM6 CollectionStructure(Proc)      │  PSend — Sep(Proc, ",")
GM6 CollectionStructure(Bind)      │  PRecv — Sep(Bind, ";")
GM6 CollectionStructure(Name)      │  PNew — Sep(@x:Name, ",")
GM6 CollectionStructure(Branch)    │  PMatch — Sep(Branch, ";")
GM6 CollectionStructure(Pattern)   │  PtList — Sep(Pattern, ",")
GM7 CrossCategoryRef(Proc→Name)    │  PSend, PRecv, PEval
GM7 CrossCategoryRef(Proc→Bind)    │  PRecv
GM7 CrossCategoryRef(Proc→Branch)  │  PMatch
GM7 CrossCategoryRef(Name→Proc)    │  NQuote
GM7 CrossCategoryRef(Bind→Pattern) │  BSimple, BPeek
GM7 CrossCategoryRef(Bind→Name)    │  BSimple, BPeek
GM7 CrossCategoryRef(Branch→Pattern)│  BrCase
GM7 CrossCategoryRef(Branch→Proc)  │  BrCase
GM8 CategoryAmbiguity(Proc, 8)     │  8 rules in Proc
GM8 CategoryAmbiguity(Pattern, 4)  │  4 rules in Pattern
```

**Compound morphemes**:

- DirectRecursion(Proc) ∩ HighBranching(3) → M5 (Parity Tree)
- DirectRecursion(Pattern) ∩ HighBranching — no, PtPar has only 2 non-terminals

**Final activation**:

```
β(G) = {M1, M2, M3, M4, M5, M6, M7, M8, M9, M10, M11}
     = {M1, ..., M11}      ← all modules activated
```

**Category dependency graph**:

```
    ┌──────────────────────────────────────────────────────┐
    │                                                      │
    │   ┌──→ Proc ──────┬──────→ Name ←──┐                │
    │   │     ↺         │         │      │                │
    │   │   (self)      │         ↓      │                │
    │   │               │       Proc     │                │
    │   │               │     (NQuote)   │                │
    │   │               ↓                │                │
    │   │             Bind ──────────────┘                │
    │   │               │                                  │
    │   │               ↓                                  │
    │   │           Pattern ←─── Branch ←── Proc          │
    │   │             ↺                                    │
    │   │           (self)                                 │
    │   └──────────────────────────────────────────────────┘
    │
    │   SCCs: {Proc, Name, Bind} (size 3), {Pattern} (size 1), {Branch} (1)
    │   Cross-SCC edges: Proc → Branch, Branch → Pattern
```

This is the expected result for a process algebra: the rich syntactic structure
— mutual recursion between processes and names, paired delimiters for scope,
binders for channel creation, collections for parallel composition and
multi-receive patterns, and high branching for conditional/match — activates
every module in the variety hierarchy.


## 5. Heuristic Scan Algorithm

The grammar morpheme extraction is a single pass over all rules:

```
GRAMMAR-MORPHEME-SCAN(R):
  Input:  Set of rules R = { (label, category, syntax) }
  Output: Set of grammar morphemes GM, grammar activation β(G)

  ── Phase 1: Build category dependency graph ──
  cats ← { C : (l, C, s) ∈ R }
  edges ← ∅
  for each (l, C, s) ∈ R:
    for each item ∈ s:
      if item = NonTerminal { category: C', ... }:
        edges ← edges ∪ { C → C' }
      if item = Binder { category: C', ... }:
        edges ← edges ∪ { C → C' }

  ── Phase 2: SCC decomposition (Tarjan's) ──
  sccs ← TARJAN-SCC(cats, edges)

  ── Phase 3: Extract morphemes ──
  GM ← ∅
  for each (l, C, s) ∈ R:
    nt_count ← 0
    for each item ∈ s:
      match item:
        NonTerminal { category: C', ... }  →
          nt_count ← nt_count + 1
          if C' = C:
            GM ← GM ∪ { DirectRecursion(C) }
          else:
            GM ← GM ∪ { CrossCategoryReference(C → C') }

        Binder { param_name: v, category: C', ... }  →
          GM ← GM ∪ { NameBinding(v, C') }

        Collection { element_category: C', ... }  →
          GM ← GM ∪ { CollectionStructure(C') }

        Sep { ... }  →
          GM ← GM ∪ { CollectionStructure(...) }

        Terminal(t)  →
          ⟨record for delimiter matching⟩

    if nt_count ≥ 3:
      GM ← GM ∪ { HighBranching(nt_count) }

  ── Phase 4: Delimiter pairing ──
  for each (l, C, s) ∈ R:
    for each pair (open, close) ∈ KnownPairs:
      if ∃ i < j : s[i] = Terminal(open) ∧ s[j] = Terminal(close):
        GM ← GM ∪ { PairedDelimiters(open, close) }

  ── Phase 5: SCC-based morphemes ──
  for each scc ∈ sccs:
    if |scc| ≥ 2:
      GM ← GM ∪ { CyclicRecursion(scc) }

  ── Phase 6: Category ambiguity ──
  for each C ∈ cats:
    k ← |{ l : (l, C, s) ∈ R }|
    if k ≥ 3:
      GM ← GM ∪ { CategoryAmbiguity(C, k) }

  ── Phase 7: Compute activation ──
  β ← {M1, M10}                                    ▷ base, always
  if DirectRecursion ∈ GM ∨ CyclicRecursion ∈ GM:
    β ← β ∪ {M2}
  if HighBranching ∈ GM:
    β ← β ∪ {M3}
  if PairedDelimiters ∈ GM:
    β ← β ∪ {M4}
  if (DirectRecursion ∈ GM ∨ CyclicRecursion ∈ GM) ∧ HighBranching ∈ GM:
    β ← β ∪ {M5}
  if NameBinding ∈ GM:
    β ← β ∪ {M6}
  if CategoryAmbiguity ∈ GM:
    β ← β ∪ {M7}
  if CrossCategoryReference ∈ GM:
    β ← β ∪ {M8, M11}
  if CollectionStructure ∈ GM:
    β ← β ∪ {M9}

  return (GM, β)
```


## 6. Complexity Analysis

**Phase 1** (dependency graph construction): O(|R| × max_items), where max_items
is the maximum number of `SyntaxItemSpec` items in any single rule. This is
O(|R| × k) where k = max|s_i|.

**Phase 2** (SCC decomposition): Tarjan's algorithm runs in O(|cats| + |edges|).
Since |edges| ≤ |R| × k and |cats| ≤ |R|, this is O(|R| × k).

**Phase 3** (morpheme extraction): Single pass over all rules and their items.
O(|R| × k).

**Phase 4** (delimiter pairing): For each rule, scan for known pairs. With
|KnownPairs| = 5, this is O(|R| × k × 5) = O(|R| × k).

**Phase 5** (SCC morphemes): O(|sccs|) ≤ O(|cats|) ≤ O(|R|).

**Phase 6** (category ambiguity): O(|R|) with a hash map counting rules per
category.

**Phase 7** (activation): O(|GM|) ≤ O(|R| × k) (constant number of checks).

**Total**: O(|R| × k), which is linear in the total size of the grammar
(the sum of all syntax item counts across all rules).

For practical grammars:
- Simple arithmetic: |R| = 5, k = 3, total work ≈ 15 item inspections
- Lambda calculus: |R| = 6, k = 5, total work ≈ 30 item inspections
- Rholang: |R| ≈ 20, k ≈ 8, total work ≈ 160 item inspections

The cost is negligible compared to the NFA construction, DFA minimization, and
WFST composition that follow in the pipeline.


## 7. Relationship to Other Dispatch Mechanisms

The three dispatch documents form a layered approximation hierarchy:

```
    Exact variety                                              Finest
    ─────────────────────────────────────────────────────────
    α ∘ morph (predicate-level)        morphological-decomposition.md
         │
         │  ⊆ (Theorem 3.1, this document)
         ↓
    β (grammar-level)                  grammar-structure-heuristics.md
         │
         │  ⊆ (always: β ⊆ {M1,...,M11})
         ↓
    {M1, ..., M11} (all modules)                              Coarsest
```

The predicate-level dispatch (Definition 2.3 of `morphological-decomposition.md`)
is the finest approximation — it examines predicate AST structure to determine
module membership. The grammar-level dispatch (Definition 3.2 of this document)
is coarser — it examines grammar rule structure without predicates. Both are
sound (no false negatives), and both are conservative (possible false positives).

The verification layer (`dispatch-sfa-model.md`) uses an SFA over `DispatchAlgebra`
to verify that the dispatch is complete (every non-zero signature is accepted)
and consistent (base modules are always present). The grammar-level heuristic
produces `PredicateSignature` values that are valid inputs to this SFA.


## 8. Limitations and Future Work

**Limitation 1: Threshold sensitivity**. The thresholds n = 3 for HighBranching
and k = 3 for CategoryAmbiguity are heuristic choices. Lower thresholds increase
sensitivity (fewer false negatives for edge cases) at the cost of more false
positives. Higher thresholds reduce false positives but risk missing patterns.
Empirical calibration against a corpus of real grammars could improve these
thresholds.

**Limitation 2: Semantic blindness**. Grammar structure cannot distinguish between
syntactically similar but semantically different constructs. For example, a
`"(" Expr ")"` rule for grouping and a `"(" Args ")"` rule for function call
both trigger GM4 (PairedDelimiters), but only the latter implies true visibly
pushdown structure in the predicate domain.

**Limitation 3: No precision refinement**. Unlike predicate-level dispatch, which
can be refined by adding more specific predicate morpheme patterns, grammar-level
dispatch has a fixed set of 8 morphemes. Extending the morpheme vocabulary (e.g.,
distinguishing left-recursive from right-recursive rules) could improve precision.

**Future work**: Combine grammar-level and predicate-level dispatch in a two-phase
strategy: use β(G) for initial infrastructure allocation, then refine to
α(morph(φ)) when predicates become available. Modules in β(G) \ α(morph(φ))
can be deallocated, recovering resources.


## References

- Eilenberg, S. (1976). *Automata, Languages, and Machines*, Vol. B. Academic Press.
  Chapter V: The variety theorem establishing the bijection between pseudovarieties
  of finite monoids and varieties of recognizable languages.

- Pin, J.-É. (1986). *Varieties of Formal Languages*. Plenum.
  Comprehensive treatment of Eilenberg's variety theory with decidability results
  for membership in specific pseudovarieties.

- Alur, R. & Madhusudan, P. (2004). Visibly pushdown languages. *STOC 2004*,
  pp. 202–211. Definition of visibly pushdown automata and the call/return
  alphabet partition that motivates GM4 (PairedDelimiters).

- Kaminski, M. & Francez, N. (1994). Finite-memory automata. *Theoretical
  Computer Science* 134(2), pp. 329–363. Register automata for data languages,
  the theoretical foundation for GM5 (NameBinding) → M6 (Register).

- Rabin, M. O. (1969). Decidability of second-order theories and automata on
  infinite trees. *Transactions of the AMS* 141, pp. 1–35. Tree automata and
  the connection between recursive branching structure and parity acceptance,
  motivating the compound morpheme GM1 ∩ GM3 → M5.

- Buchi, J. R. (1962). On a decision method in restricted second order
  arithmetic. *Proceedings of the International Congress on Logic, Methodology,
  and Philosophy of Science*, pp. 1–11. Buchi automata for omega-regular
  languages, the foundation for GM1/GM2 → M2.
