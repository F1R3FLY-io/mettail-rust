# Core Engines: PathMap and Ascent in PraTTaIL

PraTTaIL's architecture rests on two complementary engines:

- **PathMap** — a persistent radix-256 trie providing O(k) structural indexing, pattern grouping, parse dispatch, and lattice-algebraic grammar composition
- **Ascent** — a Datalog engine providing semantic closure via semi-naive fixed-point evaluation of equations, rewrites, congruence, and custom logic

Together they form a dual-engine architecture where structural indexing accelerates semantic analysis, and semantic results inform structural optimization.

---

## Architecture

```text
    ┌─────────────────── Compile Time ───────────────────┐
    │                                                     │
    │  language! { ... }                                  │
    │       │                                             │
    │       ▼                                             │
    │  LanguageSpec ──────────────────────────────┐       │
    │       │                                     │       │
    │       ▼                                     ▼       │
    │  ┌─────────────┐                   ┌──────────────┐ │
    │  │   PathMap    │ ◄─── feedback ──► │    Ascent    │ │
    │  │  (indexing)  │                   │  (codegen)   │ │
    │  │             │                   │             │ │
    │  │ • Decision  │  dead rules,      │ • Relations │ │
    │  │   trees     │  subsumption,     │ • Eq rules  │ │
    │  │ • Pattern   │  stratification   │ • Rw rules  │ │
    │  │   trie      │  ──────────────►  │ • Congruence│ │
    │  │ • Grammar   │                   │ • Guards    │ │
    │  │   algebra   │                   │             │ │
    │  └──────┬──────┘                   └──────┬──────┘ │
    │         │                                  │       │
    │         ▼                                  ▼       │
    │  match arms (parser)            ascent! { ... }    │
    │                                                     │
    └─────────────────────────────────────────────────────┘
                          │
                          ▼
    ┌─────────────────── Runtime ────────────────────────┐
    │                                                     │
    │  Input tokens ──► Parser (match arms) ──► AST      │
    │                                            │       │
    │                                            ▼       │
    │                                   Ascent Engine    │
    │                                   (fixed-point)    │
    │                                     │              │
    │                         ┌───────────┼───────────┐  │
    │                         ▼           ▼           ▼  │
    │                    eq_cat      rw_cat      fold   │
    │                   (closure)  (rewrites)  (eval)   │
    │                         │           │           │  │
    │                         └───────────┼───────────┘  │
    │                                     ▼              │
    │                              Normal forms          │
    └─────────────────────────────────────────────────────┘
```

---

## Document Map

### Triemaps That Match

Connects the theoretical framework of *Triemaps that Match* (Peyton Jones & Graf, 2022) to PraTTaIL's implementation.

| Document | Description |
|----------|-------------|
| [**Foundations**](triemaps-that-match/foundations.md) | Paper → PathMap: ExprMap, De Bruijn, matching lookup, lattice algebra, MORK lineage |
| [**PathMap Overview**](triemaps-that-match/pathmap-overview.md) | PathMap API, Lattice/DistributiveLattice traits, AlgebraicResult, zipper API |
| [**Decision Trees**](triemaps-that-match/decision-trees.md) | Parse dispatch: encoding scheme, trie construction, segment splitting, DispatchStrategy |
| [**Pattern Indexing**](triemaps-that-match/pattern-indexing.md) | Equation index: De Bruijn encoding, PatternIndex, dependency groups, subsumption |
| [**Grammar Algebra**](triemaps-that-match/grammar-algebra.md) | Composition analysis: pjoin/pmeet/psubtract, CompositionTrieReport, algebraic properties |

### Ascent Datalog

The semantic closure engine: how Datalog rules compute fixed points over syntax trees.

| Document | Description |
|----------|-------------|
| [**Overview**](ascent-datalog/overview.md) | Datalog theory, semi-naive evaluation, Ascent in Rust, why Ascent |
| [**Relation Schema**](ascent-datalog/relation-schema.md) | Generated relations: category, equality, rewrite, fold, step_term, projections, custom |
| [**Rule Generation**](ascent-datalog/rule-generation.md) | Exploration, reflexivity, congruence, equations, rewrites, fold, optimizations |
| [**Guards and Predicates**](ascent-datalog/guards-and-predicates.md) | BehavioralPred, QuantifiedFormula, LogicT fair backtracking, ConstraintTheory, AC-matching |

### Pattern Matching

The matching and unification systems that bridge structural indexing and semantic closure.

| Document | Description |
|----------|-------------|
| [**Overview**](pattern-matching/overview.md) | Three kinds of pattern matching, theoretical connections, stack safety |
| [**Structural Matching**](pattern-matching/structural-matching.md) | Iterative match engine: MatchBindings, MatchTask, TLS pool, strategies |
| [**Unification**](pattern-matching/unification.md) | Martelli-Montanari: TermExpr, algorithm, occurs check, ConstraintTheory |
| [**De Bruijn Encoding**](pattern-matching/de-bruijn-encoding.md) | Alpha-equivalence: tag layout, EncodingEnv, MORK compatibility, proof |

### Synergy

| Document | Description |
|----------|-------------|
| [**Synergy**](synergy.md) | How PathMap + Ascent cooperate at compile time and runtime; comparison with MORK/MeTTaTron |

---

## Recommended Reading Order

**For newcomers to the architecture:**

1. [Foundations](triemaps-that-match/foundations.md) — understand the theoretical motivation
2. [PathMap Overview](triemaps-that-match/pathmap-overview.md) — learn the core data structure
3. [Ascent Overview](ascent-datalog/overview.md) — learn the semantic engine
4. [Synergy](synergy.md) — see how they work together
5. Deep-dive into whichever subsystem is most relevant to your work

**For contributors to the parser:**

1. [Decision Trees](triemaps-that-match/decision-trees.md)
2. [Pattern Matching Overview](pattern-matching/overview.md)
3. [Structural Matching](pattern-matching/structural-matching.md)

**For contributors to the Datalog engine:**

1. [Relation Schema](ascent-datalog/relation-schema.md)
2. [Rule Generation](ascent-datalog/rule-generation.md)
3. [Guards and Predicates](ascent-datalog/guards-and-predicates.md)

**For contributors to pattern trie / alpha-equivalence:**

1. [Pattern Indexing](triemaps-that-match/pattern-indexing.md)
2. [De Bruijn Encoding](pattern-matching/de-bruijn-encoding.md)

---

## Key References

1. **Peyton Jones, S. & Graf, S.** (2022/2024). "Triemaps that match." arXiv:2302.08775.
2. **Martelli, A. & Montanari, U.** (1982). "An Efficient Unification Algorithm." ACM TOPLAS 4(2).
3. **Kiselyov, O. et al.** (2005). "Backtracking, Interleaving, and Terminating Monad Transformers." ICFP 2005.
4. **de Bruijn, N. G.** (1972). "Lambda calculus notation with nameless dummies." Indagationes Mathematicae 75(5).
5. **Ceri, S. et al.** (1989). "What You Always Wanted to Know About Datalog." IEEE TKDE 1(1).
6. **Bancilhon, F.** (1986). "Naive Evaluation of Recursively Defined Relations."
7. **Sekar, R. et al.** (2001). "Term Indexing." Handbook of Automated Reasoning, Ch. 26.
