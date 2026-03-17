# How PathMap and Ascent Complement Each Other

PraTTaIL's architecture rests on two engines that serve complementary roles:

- **PathMap** (structural indexing): O(k) prefix lookup, pattern grouping, parse dispatch, lattice algebra
- **Ascent** (semantic closure): fixed-point computation of equations, rewrites, congruence, and custom logic

Neither engine alone is sufficient. Together, structural indexing accelerates semantic analysis, and semantic results inform structural optimization. This document explains the cooperation at compile time and runtime.

---

## 1. The Architectural Thesis

The key insight: **structural properties** (shared prefixes, alpha-equivalence, trie topology) and **semantic properties** (reachability, equivalence closure, rewrite confluence) require fundamentally different computational models.

| Property | Best tool | Why |
|----------|----------|-----|
| "Do these patterns share a constructor prefix?" | PathMap trie walk | O(k) prefix comparison |
| "Is this term reachable from the seed?" | Ascent fixed point | Transitive closure |
| "Are these two grammars composable?" | PathMap lattice algebra | O(min(m,n)) trie merge |
| "Does this equation imply that one?" | Ascent semi-naive eval | Monotonic rule application |
| "Which rules are dead?" | **Both** | Trie topology + semantic reachability |

Dead rule detection is a clear example of synergy: the PathMap trie reveals which dispatch paths have no entries (structural emptiness), while Ascent's demand analysis reveals which categories have no reachable seed terms (semantic emptiness). The combination is strictly more powerful than either alone.

---

## 2. Compile-Time Cooperation

During `language!` macro expansion, PathMap and Ascent-style analysis cooperate in a multi-phase pipeline:

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
```

### Phase 1: LanguageSpec Extraction

The `language!` macro parses the user's grammar, equations, rewrites, and logic blocks into a `LanguageDef` AST.

### Phase 2: Structural Analysis (PathMap)

The pipeline builds:

1. **Decision trees** (`DecisionTreeBuilder`) — byte-encoded token prefixes inserted into `PathMap<DecisionAction>` tries. One trie per category.
2. **Pattern index** (`PatternIndex::build()`) — De Bruijn-encoded equation/rewrite patterns inserted into `PathMap<RuleIdSet>` tries.
3. **FIRST/FOLLOW sets** — fixed-point computation (Ascent-style iteration, though not using the Ascent macro) to determine which tokens can begin/follow each category.

### Phase 3: Structural → Semantic Feedback

Results from structural analysis feed into Ascent code generation:

| Structural result | Semantic effect |
|-------------------|-----------------|
| Dead rules (no trie entry) | Skipped in Ascent rule generation |
| Subsumption pairs | Subsumed equations eliminated (N10 DCE) |
| Alpha-equivalence groups | Equation grouping for stratification |
| Fine-grained dependency groups | Stratum ordering (BCG06) |
| Decision tree statistics | Trie determinism → backtracking elimination |
| Composition analysis | Lint diagnostics for grammar extension |

### Phase 4: Code Generation

The pipeline produces:

- **Parser match arms** — from PathMap dispatch strategies (not runtime PathMap)
- **Ascent program** — relations, rules, and optimizations informed by trie analysis

---

## 3. Runtime Cooperation

```text
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
    │                    eq_proc     rw_proc     fold   │
    │                   (closure)  (rewrites)  (eval)   │
    │                         │           │           │  │
    │                         └───────────┼───────────┘  │
    │                                     ▼              │
    │                              Normal forms          │
    └─────────────────────────────────────────────────────┘
```

### Step 1: Parsing

The generated parser uses decision tree-derived match arms to select parse rules. This is the PathMap's contribution to runtime: not a runtime trie, but compiled dispatch logic that inherits the trie's optimality.

### Step 2: AST Seeding

The parsed AST is inserted into Ascent's `step_term` relation, seeding exploration:

```rust
theory.step_term = vec![(parsed_term.clone(),)];
theory.run();  // Ascent fixed-point evaluation
```

### Step 3: Fixed-Point Evaluation

Ascent's semi-naive evaluation applies all generated rules:
1. **Category exploration** decomposes the AST into subterms
2. **Reflexivity** seeds equivalence relations
3. **Congruence** propagates equality through constructors
4. **User equations** add domain-specific equalities
5. **Rewrites** apply directional transformations
6. **Fold rules** perform native evaluation

### Step 4: Pattern Matching in Rules

Each Ascent rule body uses generated `match_pattern` functions (or `if let` pattern matches) to decompose terms. These match functions use the same iterative work-stack design as the parser trampoline, sharing the stack-safety principle.

The De Bruijn encoding concepts from the pattern trie also appear implicitly in the match functions: variables are bound by position in the constructor (not by name), and alpha-equivalence is handled by the structural matching.

---

## 4. The Feedback Loop

PathMap informs Ascent codegen → Ascent runtime uses match patterns → match patterns use the same encoding concepts as PathMap tries.

```text
    PathMap (compile-time)
         │
         │  decision tree statistics, dead rules,
         │  subsumption, stratification
         │
         ▼
    Ascent codegen ──────► Ascent runtime
         │                      │
         │                      │  uses generated match_pattern()
         │                      │  which uses iterative work stacks
         │                      │  and positional variable binding
         │                      │  (same principles as PathMap encoding)
         │                      │
         └──────────────────────┘
                feedback loop
```

This is not a circular dependency — it's a feedforward chain: PathMap analysis at compile time produces data that shapes the Ascent program, and the Ascent program's match functions are generated using the same structural principles as the PathMap encoding.

---

## 5. Comparison with MORK and MeTTaTron

### MORK: PathMap as Both Storage and Query

In MORK, PathMap is the runtime data structure. Expressions live in the trie, and rewriting is implemented as trie operations:

```text
1. Match: walk the trie with the LHS pattern → find redexes
2. Rewrite: construct the RHS term → insert into trie
3. Repeat until fixed point
```

PathMap serves as both storage (the expression database) and query engine (matching lookup). There is no separate "semantic engine" — the trie IS the engine.

### MeTTaTron: Dual-Tier Storage

MeTTaTron separates ground atoms from variable atoms:

```text
Ground atoms (no variables): PathMap trie → O(k) lookup
Variable atoms (patterns):   Vec → O(n) linear scan
```

This is the paper's `mm_pvar` idea: pattern variables require special handling that the trie structure alone cannot provide efficiently. MeTTaTron's dual-tier approach improves over MORK's uniform trie by avoiding wildcard enumeration.

### PraTTaIL: Compile-Time Trie + Runtime Datalog

PraTTaIL goes further by separating the concerns entirely:

| Role | MORK | MeTTaTron | PraTTaIL |
|------|------|-----------|----------|
| Structural indexing | Runtime PathMap | Runtime PathMap + Vec | **Compile-time** PathMap |
| Semantic closure | Trie rewriting | Trie rewriting | **Ascent Datalog** |
| Pattern matching | Trie walk | Trie walk + linear scan | **Generated match arms** |
| Alpha-equivalence | Implicit (byte trie) | Implicit (byte trie) | **Explicit De Bruijn** |

Key advantages of PraTTaIL's separation:

1. **4-8x faster dispatch**: Match arms (jump tables) vs. trie walk (pointer chasing)
2. **Declarative semantics**: Ascent rules specify *what* to compute; trie analysis determines *how*
3. **Compile-time optimization**: Dead rule elimination, subsumption detection, and stratification happen once, not on every execution
4. **Type safety**: Ascent relations are typed by Rust enums, catching category mismatches at compile time

---

## 6. When to Use Which Engine

| Task | Engine | Reason |
|------|--------|--------|
| Parse dispatch | PathMap decision tree | O(k) prefix lookup; compile-time |
| Equation grouping | PathMap pattern trie | Alpha-equivalence via De Bruijn bytes |
| Grammar composition | PathMap lattice algebra | Trie meet/join/subtract |
| Equality closure | Ascent (`eqrel`) | Reflexivity + symmetry + transitivity |
| Rewrite application | Ascent rules | Match via `eq_cat`, construct RHS |
| Demand analysis | Ascent-style iteration | Fixed-point reachability |
| Guard evaluation | LogicT (via Ascent) | Fair backtracking over quantifiers |
| Dead rule detection | Both | Trie emptiness + semantic unreachability |

---

## Key Source Files

| File | Role in synergy |
|------|-----------------|
| `prattail/src/pipeline.rs` | Orchestrates PathMap construction + Ascent code generation |
| `prattail/src/decision_tree.rs` | PathMap decision trees (structural side) |
| `macros/src/logic/pattern_trie.rs` | PathMap pattern index (structural side) |
| `macros/src/logic/equations.rs` | Ascent rule generation (semantic side) |
| `macros/src/logic/rules.rs` | Unified rule clause generation |
| `macros/src/gen/term_ops/match_pattern.rs` | Generated match engine (bridge) |

---

**See also:** [README](README.md) for navigation and reading order.
