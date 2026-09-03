# The Case for Symbolic Finite Automata

---

## 1. The Guard Satisfiability Problem

MeTTaIL's predicated types condition communication on **guard predicates** --
constraints that a received value must satisfy before a `Comm` rule fires.
The compiler must decide, at compile time, whether each guard is satisfiable
(can any value pass?), whether two guards overlap (can the same value match
both?), and whether one guard subsumes another (does every value matching A
also match B?).  These questions reduce to a single operation:

> **Given a predicate `φ` over a (possibly infinite) domain `D`, is there any
> `d ∈ D` such that `φ(d)` holds?**

For example, the Rholang guard

```rholang
for (@x, @y <- ch) where x + y ≤ 100, x ≥ 10, y ≥ 20 { P }
```

asks: does the conjunction `x + y ≤ 100 ∧ x ≥ 10 ∧ y ≥ 20` have a
satisfying assignment?  If not, the rule is dead code.  If it does, the
compiler may need a witness (a concrete satisfying pair) for testing and
diagnostics.

MeTTaIL answers this question using **Symbolic Finite Automata** (SFA) for
compile-time guard analysis and **Ascent** (a Datalog engine) for runtime
behavioral evaluation — two complementary tools, each handling the task it
is best suited for (§6.5).  To explain why this combination was chosen, we
compare it against three alternative approaches: SAT/SMT solvers, LP/ILP
solvers, and using Datalog alone for everything.  The diagram below
summarizes all four approaches; abbreviations are expanded in later sections:

- **SAT** — satisfiability (does a solution exist?)
- **SMT** — Satisfiability Modulo Theories (§4)
- **LP** — Linear Programming (§5.1)
- **ILP** — Integer Linear Programming (§5.2)
- **NFA** — Nondeterministic Finite Automaton
- **SFA** — Symbolic Finite Automaton (NFA with predicate-labeled transitions over infinite domains)
- **SFT** — Symbolic Finite Transducer (SFA extended with output functions)
- **WFST** — Weighted Finite State Transducer (transitions carry priority weights)
- **AST** — Abstract Syntax Tree (the compiler's parsed representation of a guard)
- **BFS** — Breadth-First Search (a graph traversal that visits all reachable nodes)
- **FFI** — Foreign Function Interface (calling C/C++ code from Rust)
- **FP** — Fixed Point (the converged result of iterating Datalog rules)
- **T1–T4** — Decidability tiers for guard predicates: T1 = compile-time decidable,
  T2 = runtime decidable, T3 = semi-decidable (bounded search), T4 = undecidable
- **CHAM** — Chemical Abstract Machine (Berry & Boudol, 1992; the operational
  semantics for concurrent process reduction)
- **SYM01–SYM03** — Lint diagnostics: SYM01 = unsatisfiable guard (dead),
  SYM02 = overlapping guards (ambiguous), SYM03 = subsumed guard (shadowed)
- **MSO01** — Lint diagnostic for undecidable (T4) guard predicates
- **Presburger arithmetic** — the first-order theory of integers with addition
  (no multiplication); decidable via automata (Büchi, 1960)

```
  SAT / SMT           LP / ILP            Datalog / Ascent      Symbolic Finite Automata
  ─────────           ────────            ────────────────      ────────────────────────
  Guard AST           Guard AST           Guard AST             Guard AST
       │                   │                   │                     │
       ▼                   ▼                   ▼                     ▼
  Serialize to        Build constraint    Encode as             Compile to
  SMT-LIB2            matrix  A·x ≤ b     Datalog rules         NFA over {0,1}ᵏ
       │                   │                   │                     │
       ▼                   ▼                   ▼                     ▼
  Call Z3 / CVC5      Run simplex or      Semi-naive            BFS emptiness
  via FFI             branch-and-bound    fixed-point eval      check
       │                   │                   │                     │
       ▼                   ▼                   ▼                     ▼
  Parse model         Read feasible       Check relation        Decode witness
  from solver         point from tableau  membership in FP      from shortest path
       │                   │                   │                     │
       ▼                   ▼                   ▼                     ▼
  SAT / UNSAT         Feasible / Not      Derivable / Not       SAT / UNSAT
```

MeTTaIL uses SFAs (the fourth column) for **compile-time** guard analysis —
satisfiability, overlap, subsumption, and minterm-based dispatch (§2).  At
**runtime**, Ascent Datalog handles behavioral guard evaluation via `O(1)`
hash-indexed lookups into its fixpoint relations (§6.2).  The two are
complementary: SFAs decide what's *possible* over infinite domains; Ascent
computes what's *true* over concrete terms.  This document explains why SFAs
were chosen for compile-time guard analysis, why the three alternatives
(SMT, LP, Datalog alone) cannot fill that role, and where each alternative
would be the better choice for other tasks.

> **Cross-reference:** [predicated-types.md §16](../../../../docs/design/predicated-types.md)
> contains the original brief comparison table.  This document supersedes and
> expands that discussion.

---

## 2. From Guards to Dispatch

§1 framed the problem as a single satisfiability question.  In practice, the
compiler faces a richer challenge: when a message arrives on a channel, it
must **route** that message to the correct receiver(s) — efficiently and
deterministically.  This section shows how guard analysis feeds into
dispatch, and why it requires the `BooleanAlgebra` machinery developed in
later sections.

The end-to-end flow from guard source code to runtime message routing
proceeds through two phases — compile-time analysis and runtime execution —
connected by code generation:

```
  ╔═══════════════════════════════════════════════════════════════════════╗
  ║                        COMPILE TIME                                   ║
  ║                                                                       ║
  ║  Guard source                                                         ║
  ║  for (@x, @y <- ch) where x + y ≤ 100, x ≥ 10 { P }                   ║
  ║       │                                                               ║
  ║       ▼                                                               ║
  ║  ┌─────────────┐   ┌───────────────────┐   ┌───────────────────┐      ║
  ║  │ 1. Parse    │──▶│ 2. Classify (tier)│──▶│ 3. Compile to SFA │      ║
  ║  │ guard → AST │   │ T1/T2/T3/T4       │   │ via BooleanAlg    │      ║
  ║  └─────────────┘   └───────────────────┘   └─────────┬─────────┘      ║
  ║                                                      │                ║
  ║                 ┌────────────────────────────────────┘                ║
  ║                 │                                                     ║
  ║                 ▼                                                     ║
  ║  ┌────────────────────────────┐    ┌────────────────────────────┐     ║
  ║  │ 4. Analyze                 │───▶│ 5. Optimize                │     ║
  ║  │ • SAT(φ) → dead guard?     │    │ • Determinize (minterms)   │     ║
  ║  │ • SAT(φᵢ∧φⱼ) → overlap?    │    │ • Minimize                 │     ║
  ║  │ • SAT(φⱼ∧¬φᵢ) → subsumes?  │    │ • Fuse guards              │     ║
  ║  │ • Lint: SYM01–SYM03        │    │ • Selectivity ordering     │     ║
  ║  └────────────────────────────┘    └─────────────┬──────────────┘     ║
  ║                                                  │                    ║
  ║                                                  ▼                    ║
  ║                                    ┌────────────────────────────┐     ║
  ║                                    │ 6. Codegen                 │     ║
  ║                                    │ SFA → Rust code per tier:  │     ║
  ║                                    │ T1: eliminate              │     ║
  ║                                    │ T2: inline check / Ascent  │     ║
  ║                                    │ T3: bounded search         │     ║
  ║                                    │ T4: trust wrapper          │     ║
  ║                                    └─────────────┬──────────────┘     ║
  ╚══════════════════════════════════════════════════╪════════════════════╝
                                                     │ generated code
  ╔══════════════════════════════════════════════════╪════════════════════╗
  ║                        RUNTIME                   │                    ║
  ║                                                  ▼                    ║
  ║  Message @(q) arrives on channel n                                    ║
  ║       │                                                               ║
  ║       ▼                                                               ║
  ║  ┌──────────────────┐   ┌────────────────────┐   ┌──────────────────┐ ║
  ║  │ Layer 1:         │──▶│ Layer 2:           │──▶│ Layer 3:         │ ║
  ║  │ Structural       │   │ Guard evaluation   │   │ Behavioral       │ ║
  ║  │ dispatch         │   │ (generated code)   │   │ predicates       │ ║
  ║  │ (decision tree,  │   │                    │   │ (Ascent FP       │ ║
  ║  │  WFST ranking)   │   │ T2: if x>0 {..}    │   │  relation        │ ║
  ║  │                  │   │     or Ascent join │   │  lookups)        │ ║
  ║  │ Cost: O(k)       │   │ Cost: O(1)–O(|φ|)  │   │ Cost: O(1)       │ ║
  ║  └──────────────────┘   └────────────────────┘   └──────────────────┘ ║
  ║                                                        │              ║
  ║                                                        ▼              ║
  ║                                                   c[σ] fires          ║
  ╚═══════════════════════════════════════════════════════════════════════╝
```

The rest of this section explains each stage in detail.

### 2.1 The Unconditional Comm Rule

In the standard rho-calculus (Meredith & Radestock, 2005), communication is
unconditional.  When a send `n!(q)` and a receive `(n?x).{c}` coexist on
the same channel `n`, the Comm rule fires immediately:

    { n!(q) | (n?x).{c} }  ⟶  c[@(q)/x]

The sent process `q` is quoted into a Name `@(q)` and substituted for `x`
in the continuation `c`.  No inspection of `q` occurs — every value is
accepted.

When **multiple receives** wait on the same channel, the Chemical Abstract
Machine (CHAM) semantics (Berry & Boudol, 1992) selects one
nondeterministically.  This is the correct and intended semantics for
concurrent systems — it models the genuine concurrency of competing
processes without imposing an artificial ordering.  Predicated types do not
replace this nondeterminism; they **refine** it.  By attaching guard
predicates to receives, the programmer controls which receives are
*eligible* for a given value, narrowing the candidate set before the
nondeterministic choice occurs.  If multiple guarded receives still match,
the choice among them remains nondeterministic — by design.

### 2.2 The Guarded Comm Rule

**Predicated types** extend the Comm rule with a guard `φ` that filters
incoming values:

    { n!(q) | (n ? φ).{c} }  ⟶  c[σ]    iff match(φ, @(q)) = σ

If matching fails (`match(φ, @(q)) = ⊥`), the Comm rule does **not** fire
and the processes remain waiting.  The guard `φ` acts as a type-level
filter: only values with the right shape and properties pass through.

When multiple guarded receives wait on the same channel, the sent value
is routed to **exactly those receives whose guard matches**:

```
  n!(q)
    │
    ▼
  Channel n
    │
    ├──── match(φ₁, @(q)) = σ₁  ──▶  c₁[σ₁]    ✓ fires
    │
    ├──── match(φ₂, @(q)) = ⊥   ──▶  blocked   ✗ guard rejects
    │
    └──── match(φ₃, @(q)) = σ₃  ──▶  c₃[σ₃]    ✓ fires
```

If exactly one guard matches, routing is deterministic.  If multiple guards
match, the runtime must choose among them — the same nondeterminism problem
as the unguarded case, but now restricted to a smaller set of candidates.

### 2.3 The Compiler's Routing Questions

The compiler can analyze guards **at compile time** to reduce or eliminate
runtime nondeterminism.  For a channel `n` with guards `φ₁, φ₂, …, φₘ`,
the compiler asks four questions:

**1. Satisfiability.** Is `φᵢ` satisfiable — can any value match it?

    SAT(φᵢ) = false  ⟹  dead code; eliminate the receive entirely

**2. Overlap.** Can `φᵢ` and `φⱼ` both match the same value?

    SAT(φᵢ ∧ φⱼ) = true  ⟹  overlap; nondeterministic choice or priority needed

**3. Subsumption.** Does every value matching `φⱼ` also match `φᵢ`?

    SAT(φⱼ ∧ ¬φᵢ) = false  ⟹  φᵢ subsumes φⱼ; φⱼ is shadowed (warn via SYM03)

**4. Exhaustiveness.** Do the guards cover the entire domain?

    SAT(¬φ₁ ∧ ¬φ₂ ∧ ⋯ ∧ ¬φₘ) = false  ⟹  exhaustive; every value is handled

Each question reduces to `SAT` over Boolean combinations of guards — the
exact operation that the `BooleanAlgebra` trait provides (§3).  Questions
2-4 additionally require **complement** (`¬φ`), which is why LP and Datalog
fall short (§5.5, §6.3).

**A note on subsumption.** Of the four questions, subsumption (question 3)
deserves additional explanation because the term is less familiar than
satisfiability or overlap.

**Subsumption** means one guard is strictly more general than another — it
accepts every value the narrower guard accepts, and possibly more.  If guard
`φᵢ` subsumes guard `φⱼ`, then `φⱼ` can never match a value that `φᵢ`
doesn't also match.  The narrower guard `φⱼ` is **shadowed**: it will never
be the unique winner in dispatch, because `φᵢ` always matches too.

The test `SAT(φⱼ ∧ ¬φᵢ) = false` asks: "is there any value that satisfies
`φⱼ` but not `φᵢ`?"  If no such value exists, then `⟦φⱼ⟧ ⊆ ⟦φᵢ⟧` — the
set of values matching `φⱼ` is a subset of those matching `φᵢ`.

As a concrete example: if `φᵢ` is `x ≥ 0` and `φⱼ` is `x ≥ 10 ∧ x < 50`,
then every value in `[10, 50)` also satisfies `x ≥ 0`.  The guard `φⱼ` is
subsumed — it is a special case of `φᵢ`.  The compiler warns via SYM03
because the programmer likely intended `φⱼ` to handle a distinct case, but
`φᵢ` already covers it.  The programmer can resolve this by adding an
explicit priority or by narrowing `φᵢ`.

### 2.4 Minterm-Based Deterministic Dispatch

When guards overlap, the naive runtime strategy is **backtracking**: try
each guard in some order, back up if a choice leads to deadlock. The automata
approach replaces this with **deterministic dispatch** via minterms.

**Minterms** partition the domain into regions where every guard behaves
identically.  Within a single minterm, the set of matching guards is fixed —
no runtime testing is needed beyond identifying which minterm the value falls
into.

**Example.** Three guards on a channel receiving integer values:

```
  Guard A: x ≥ 0  ∧ x < 50       (accepts [0, 50))
  Guard B: x ≥ 30 ∧ x < 100      (accepts [30, 100))
  Guard C: x ≥ 80                 (accepts [80, ∞))
```

The three guards produce five minterms — maximal satisfiable regions where
the set of matching guards is constant:

```
  Domain:   ─────────────────────────────────────────────────▶ x
            0        30       50       80       100

  Guard A:  ├─────────────────────┤
  Guard B:            ├──────────────────────────┤
  Guard C:                                ├──────────────────▶

  Minterms: ├─────────┤──────────┤────────┤──────┤──────────▶
            [0, 30)    [30, 50)   [50, 80) [80,100) [100, ∞)
            {A}        {A, B}     {B}      {B, C}   {C}
```

The compiler produces a **dispatch table** indexed by minterm:

| Minterm     | Matching guards | Dispatch                             |
|-------------|-----------------|--------------------------------------|
| `[0, 30)`   | {A}             | Deterministic → A                    |
| `[30, 50)`  | {A, B}          | Nondeterministic choice between A, B |
| `[50, 80)`  | {B}             | Deterministic → B                    |
| `[80, 100)` | {B, C}          | Nondeterministic choice between B, C |
| `[100, ∞)`  | {C}             | Deterministic → C                    |

Three of five regions dispatch deterministically (no backtracking).  The
remaining two have exactly two candidates — far cheaper than testing all
three guards.  For guards that are **pairwise disjoint** (no overlap at all),
every minterm maps to exactly one guard and dispatch is fully deterministic.

Computing minterms requires forming `ψ₁ ∧ ψ₂ ∧ ⋯ ∧ ψₙ` where each
`ψᵢ ∈ {φᵢ, ¬φᵢ}` — exactly the `BooleanAlgebra` operations (`∧`, `¬`,
`SAT`) that the rest of this document is about.

### 2.5 The Five-Stage Guard Compilation Pipeline

The full pipeline from guard source to runtime dispatch proceeds in five
stages, each depending on automata that implement `BooleanAlgebra`:

```
  ┌──────────────┐   ┌───────────────┐   ┌──────────────┐   ┌──────────────┐   ┌──────────────┐
  │  1. Parse    │──▶│  2. Classify  │──▶│  3. Compile  │──▶│  4. Optimize │──▶│  5. Codegen  │
  │              │   │               │   │              │   │              │   │              │
  │  guard expr  │   │  decidability │   │  formula →   │   │  determinize │   │  SFA →       │
  │  → formula   │   │  tier T1–T4   │   │  SFA via     │   │  via minterms│   │  dispatch    │
  │  AST         │   │               │   │  Presburger, │   │  minimize,   │   │  table or    │
  │              │   │               │   │  Interval,   │   │  fuse guards │   │  match arms  │
  │              │   │               │   │  etc.        │   │              │   │              │
  └──────────────┘   └───────────────┘   └──────────────┘   └──────────────┘   └──────────────┘
                           │
                     ┌─────┴──────────────────────────────┐
                     │ T1: constant-fold (compile-time)   │
                     │ T2: deterministic SFA              │
                     │ T3: bounded search (depth limit k) │
                     │ T4: undecidable (emit lint MSO01)  │
                     └────────────────────────────────────┘
```

Every stage from 3 onward depends on the `BooleanAlgebra` trait: stage 3
compiles guards to SFAs via `PresburgerAlgebra` or `IntervalAlgebra`; stage 4
determinizes and minimizes using minterms (`SAT`, `∧`, `¬`); stage 5
emits dispatch code indexed by the determinized minterms.  The choice of
automata over solvers or Datalog (§4–§6) is driven by this pipeline's need
for composable, complementable, symbolically decidable predicates.

> **Cross-reference:** [predicated-types.md](../../../../docs/design/predicated-types.md) §12
> specifies the full compilation pipeline with decidability tiers and codegen
> strategies.

### 2.6 Optimized Dispatch: From Compile-Time Analysis to Runtime Code

A naive runtime would evaluate every guard on every message: when `n!(q)`
arrives, test `match(φ₁, @(q))`, then `match(φ₂, @(q))`, then
`match(φ₃, @(q))`, and so on.  For `m` receives this is `O(m · |φ|)` per
message.  The compile-time SFA analysis eliminates this linear scan — but
the SFAs themselves do **not** exist at runtime.  They are compile-time
tools that produce analysis results and inform code generation.

**What SFA analysis produces at compile time.**

The SFA pipeline (§2.5) analyzes guard predicates before any code runs.  Its
outputs are:

| Analysis                    | SFA operation                 | Compile-time result                              |
|-----------------------------|-------------------------------|--------------------------------------------------|
| Dead guard detection        | `SAT(φᵢ) = false`             | Receive eliminated entirely (no code emitted)    |
| Overlap detection           | `SAT(φᵢ ∧ φⱼ) = true`         | SYM02 lint warning: ambiguous dispatch           |
| Subsumption detection       | `SAT(φⱼ ∧ ¬φᵢ) = false`       | SYM03 lint warning: `φⱼ` shadowed by `φᵢ`        |
| Exhaustiveness check        | `SAT(¬φ₁ ∧ ⋯ ∧ ¬φₘ) = false`  | Guarantees no value blocks                       |
| Decidability classification | Tier analysis (T1–T4)         | Selects codegen strategy per guard               |
| Minterm computation         | `ψᵢ ∈ {φᵢ, ¬φᵢ}` conjunctions | Internal to determinization and overlap analysis |

The minterm computation is used internally by the SFA determinization
algorithm and by the overlap/subsumption analysis — it is **not** emitted as
a runtime dispatch table.  Its role is to inform the compiler which guards
conflict and how to classify them.

**What runs at runtime — the generated code.**

SFAs compile guards into concrete Rust code whose form depends on the
decidability tier:

- **T1 (statically decided):** The guard is constant-folded away.
  Always-true guards produce bare structural Comm rules with no guard check.
  Always-false guards are eliminated entirely — zero runtime cost.

- **T2 (decidable at runtime):** The compiler emits one of three forms:
  - **Inline arithmetic checks** — for `IntervalAlgebra` guards:
    `if x > 0 && x < 100 { fire }`.  Cost: `O(1)`.
  - **Ascent relation join clauses** — the canonical path for behavioral
    guards: an `O(1)` hash-indexed lookup into Ascent's fixpoint relation,
    inlined directly into the Ascent Comm rule body.
  - **Register machines** — for data-equality guards over infinite domains
    (M6 Register module): an `O(|value|)` walk with constant register
    operations per step.

- **T3 (bounded search):** A BFS/DFS with an explicit depth counter
  (`k`), returning `TriState::True`, `TriState::False`, or
  `TriState::Unknown` if the bound is exceeded.  Cost: `O(k · |value|)`.

- **T4 (undecidable):** An `assert_pred()` trust wrapper that
  unconditionally returns true, requiring an external proof certificate
  (Rocq) for soundness.  The compiler emits an MSO01 lint diagnostic.

**Channel-level structural dispatch** — how messages find the right
category and rule — uses a separate, token-based mechanism that is
independent of guard predicates:

- **Decision tree trie:** byte-encoded prefix trie mapping token sequences
  to parse rules.  Cost: `O(k)` where `k` is the prefix length.
- **Computed goto tables:** when a category has ≥ 20 dispatch arms, the
  compiler generates a function-pointer array indexed by token ID.
  Cost: `O(1)`.
- **Match arms:** for categories with fewer arms, the compiler's native
  `match` expression (potentially optimized to a jump table).
- **WFST prediction ranking:** when multiple rules could apply, a
  Weighted Finite State Transducer orders candidates by priority.
  WFSTs are parameterized by a **semiring** — an algebraic structure
  providing ⊕ (combine) and ⊗ (extend) operations.  The dispatch ranking
  uses the **tropical semiring** (⊕ = min, ⊗ = +, so the lowest-cost path
  wins), but other semirings are used elsewhere in the pipeline (e.g.,
  the log semiring for probabilistic analysis).  This is the one automaton
  structure that persists into runtime (§7.6).

**How the layers combine at runtime.**

When a message arrives on a channel, three layers execute in sequence:

```
              Message @(q) arrives on channel n
                             │
                             ▼
  ┌─────────────────────────────────────────────────────────────────┐
  │ Layer 1: Structural dispatch (token-based)                      │
  │ Decision tree trie or computed goto selects the category/rule.  │
  │ Cost: O(k) prefix lookup or O(1) table index.                   │
  │ This is NOT guard-based — it routes by syntactic structure.     │
  └──────────────────────────┬──────────────────────────────────────┘
                             │ category + rule identified
                             ▼
  ┌─────────────────────────────────────────────────────────────────┐
  │ Layer 2: Guard evaluation (generated code, tier-dependent)      │
  │ T1: skipped (constant-folded away at compile time).             │
  │ T2: inline check (O(1)) or Ascent join (O(1)) or register (O(n))│
  │ T3: bounded search (O(k·n)).                                    │
  │ T4: assert_pred() trust wrapper (O(1)).                         │
  │ Only the selected rule's guard is evaluated — not all guards.   │
  └──────────────────────────┬──────────────────────────────────────┘
                             │ guard passes (σ = Some)
                             ▼
  ┌─────────────────────────────────────────────────────────────────┐
  │ Layer 3: Behavioral predicates (Ascent fixpoint)                │
  │ For guards with `where R(a)` clauses: O(1) hash-indexed lookup  │
  │ into Ascent's converged fixpoint relations.                     │
  │ Runs only if the structural guard (Layer 2) succeeded.          │
  └──────────────────────────┬──────────────────────────────────────┘
                             │ all predicates pass
                             ▼
                 c[σ]  (continuation fires)
```

The compile-time SFA analysis ensures this pipeline is **minimal**: dead
guards are eliminated before codegen (Layer 2 never runs code for them),
overlapping guards are flagged so the programmer can disambiguate, and each
guard's tier determines the cheapest possible runtime representation.

**Ascent's dual role: enforcement and dispatch.**

Layer 3 deserves special attention because Ascent's behavioral check serves
two purposes simultaneously:

- **Enforcement.** The behavioral predicate is a *gate*: if `R(a[σ])` is
  not in the fixpoint, the Comm rule does not fire and the receive remains
  blocked.  This enforces the guard's semantic contract — only values that
  satisfy both the structural shape *and* the behavioral property pass
  through.

- **Dispatch.** When multiple guarded receives on the same channel pass
  Layer 2 (structural match), their behavioral predicates may differ.  A
  value might structurally match receives A, B, and C, but only A and C
  have their behavioral predicates satisfied in the current fixpoint.
  Ascent's relation lookups narrow the candidate set from {A, B, C} to
  {A, C} — this is dispatch by semantic predicate, not syntactic shape.

These two roles are inseparable: the same `O(1)` hash lookup that
*enforces* the predicate also *selects* which receives fire.  The runtime
does not distinguish between "checking a constraint" and "routing a
message" — both reduce to `R(a[σ]) ∈ FP?`.

```
  Value passes structural match for receives A, B, C
       │
       ▼
  Layer 3 (Ascent fixpoint lookups):
       │
       ├── A: safe(x) ∈ FP?    → yes  ─── A fires     (enforcement: pass)
       │
       ├── B: trusted(x) ∈ FP? → no   ─── B blocked   (enforcement: reject)
       │
       └── C: valid(x) ∈ FP?   → yes  ─── C fires     (enforcement: pass)
       │
       ▼
  Dispatch result: {A, C}     (dispatch: behavioral predicates selected the winners)
```

This is why the document describes SFAs and Ascent as complementary (§6.5):
SFAs analyze guards at compile time to eliminate dead code, detect overlaps,
and generate efficient structural checks.  Ascent evaluates behavioral
predicates at runtime to enforce semantic contracts and dispatch among
structurally compatible receives.

**Mixed guarded and unguarded receives.** When both guarded and unguarded
receives coexist on the same channel, the unguarded receives accept every
value — they require no guard evaluation at all.  The structural dispatch
layer (Layer 1) routes based on syntactic shape; unguarded receives act as
catch-all defaults when no more-specific guarded receive matches.

---

## 3. The Effective Boolean Algebra Abstraction

Before comparing the four approaches, we must understand the abstraction that
unifies all of MeTTaIL's constraint handling: the **effective Boolean algebra**
(D'Antoni & Veanes, 2017).  Every Symbolic Finite Automaton (SFA) algorithm --
emptiness, intersection, complement, determinization, equivalence -- reduces
to a small set of predicate operations.  If a constraint domain can implement
these operations, it inherits the full suite of symbolic finite automata
algorithms for free.

### 3.1 Definition

An **effective Boolean algebra** is a tuple

    𝒜 = (D, Ψ, ⊥, ⊤, ∧, ∨, ¬, SAT, WIT, EVAL)

where:

| Component        | Type       | Role                                              | Notes                                                     |
|------------------|------------|---------------------------------------------------|-----------------------------------------------------------|
| D                | set        | Domain of elements (possibly infinite)            |                                                           |
| Ψ (psi)          | set        | Decidable set of predicates over D                |                                                           |
| ⊥ ∈ Ψ            | predicate  | Contradiction: ⟦⊥⟧ = ∅ — no element satisfies it  | ⟦·⟧ maps a predicate to the set of elements satisfying it |
| ⊤ ∈ Ψ            | predicate  | Tautology: ⟦⊤⟧ = D — every element satisfies it   |                                                           |
| ∧ : Ψ × Ψ → Ψ    | operation  | Conjunction: ⟦φ ∧ ψ⟧ = ⟦φ⟧ ∩ ⟦ψ⟧                  |                                                           |
| ∨ : Ψ × Ψ → Ψ    | operation  | Disjunction: ⟦φ ∨ ψ⟧ = ⟦φ⟧ ∪ ⟦ψ⟧                  |                                                           |
| ¬ : Ψ → Ψ        | operation  | Complement: ⟦¬φ⟧ = D ∖ ⟦φ⟧                        |                                                           |
| SAT : Ψ → 𝔹      | decision   | SAT(φ) ⟺ ⟦φ⟧ ≠ ∅  (𝔹 = {true, false})             |                                                           |
| WIT : Ψ → D      | extraction | WIT(φ) (witness) returns some d ∈ ⟦φ⟧ when SAT(φ) |                                                           |
| EVAL : Ψ × D → 𝔹 | evaluation | EVAL(φ, d) ⟺ d ∈ ⟦φ⟧                              |                                                           |

> **Full formalization:** [boolean-algebra.md](../../theory/symbolic/boolean-algebra.md)
> Definition 1.1.

### 3.2 The Key Insight

All SFA algorithms reduce to calls to `SAT`, `∧`, `∨`, and `¬`.  For example:

- **Emptiness** of an SFA: explore reachable transitions; a transition
  `(q, φ, q′)` is viable iff `SAT(φ)`.
- **Intersection** of two SFAs: product construction; the guard on a product
  transition is `φ₁ ∧ φ₂`, viable iff `SAT(φ₁ ∧ φ₂)`.
- **Determinization**: compute **minterms** -- maximal satisfiable conjunctions
  of predicates and their negations -- to partition the infinite domain into
  finitely many equivalence classes.  Each minterm is a conjunction
  `ψ₁ ∧ ψ₂ ∧ ⋯ ∧ ψₖ` where each `ψᵢ ∈ {φᵢ, ¬φᵢ}`, tested for viability
  via SAT.

This means: **any domain that can implement `(∧, ∨, ¬, SAT, WIT, EVAL)` gets
the full suite of automata algorithms for free.**

The `BooleanAlgebra` requirement — particularly the involutive complement
`¬¬φ = φ` — is essential for minterm computation and determinization.
§11 explores what changes when this requirement is relaxed to a **Heyting
algebra**, where `¬¬φ ≥ φ` but equality is not guaranteed.

### 3.3 Existing Implementations

| Algebra             | Domain D              | SAT complexity | Use case                          |
|---------------------|-----------------------|----------------|-----------------------------------|
| `IntervalAlgebra`   | `i64` ranges          | O(k) intervals | Single-variable numeric guards    |
| `CharClassAlgebra`  | Unicode code points   | O(k) ranges    | Character classification          |
| `KatBooleanAlgebra` | Propositional atoms   | O(2ⁿ) atoms    | Kleene algebra tests              |
| `DispatchAlgebra`   | Module signatures     | O(1) bitwise   | Predicate dispatch gating         |
| `PresburgerAlgebra` | `ℤᵏ` (integer tuples) | NFA emptiness  | Multi-variable linear arithmetic  |

**`IntervalAlgebra`** — the simplest and most frequently used algebra.
Predicates are unions of half-open integer intervals like `[10, 100)`.
Satisfiability reduces to checking whether the interval list is non-empty.
Conjunction intersects intervals; complement inverts them against the
domain bounds.  Used for single-variable guards like `x ≥ 10 ∧ x < 100`
— the bread-and-butter case where the guard constrains one integer
variable to a range.

**`CharClassAlgebra`** — the Unicode analog of `IntervalAlgebra`.
Predicates are unions of code-point ranges (e.g., `[a-z]`, `[α-ω]`,
`[\u{1F600}-\u{1F64F}]`).  The domain is the full Unicode space
(1,114,112 code points), but the symbolic representation means the algebra
never enumerates individual characters.  Used for guards that classify
input tokens by character class — identifiers, keywords, operators, and
whitespace.

**`KatBooleanAlgebra`** — predicates are Boolean combinations of named
propositional atoms (`p`, `q`, `¬p ∧ q`, etc.).  Satisfiability checks all
`2ⁿ` truth assignments for `n` atoms.  This is the algebra for
**Kleene algebra with tests** (KAT), where guards are propositional
conditions embedded in a regular-expression-like control flow.  Used when
guard predicates reference named Boolean flags rather than numeric or
structural values.

**`DispatchAlgebra`** — a meta-level algebra that operates on
`PredicateSignature` bitfields (§7.6) rather than on data values.  Each
predicate tests whether a specific module bit is set in the guard's
feature signature (e.g., "does this guard use arithmetic?" → M12 bit).
Satisfiability is a single bitwise-AND.  Used internally by the predicate
dispatch classifier to verify that every guard activates at least one
analysis module.

**`PresburgerAlgebra`** — handles multi-variable integer arithmetic:
guards like `x + y ≤ 100` that relate two or more integer variables.
Single-variable constraints could use `IntervalAlgebra`, but the moment
a guard involves *two or more* variables, intervals cannot help — there
is no way to express `x + y ≤ 100` as a single-variable range.
`PresburgerAlgebra` compiles each linear constraint to an NFA via the
Büchi/Bartzis-Bultan construction (§7.1) and decides satisfiability via
NFA emptiness.  This is the algebra that motivated the "why automata
instead of solvers?" question — it is the alternative to LP/ILP solvers
(§5) for the same integer arithmetic domain.

### 3.4 Framing the Comparison

The question "why automata instead of solvers?" is really:

> **Why implement SAT as NFA-emptiness rather than as an SMT query or an
> LP feasibility check?**

The `BooleanAlgebra` trait requires a decision procedure for satisfiability.
The three approaches in §1 are three ways to implement that procedure.  The
decisive factor is not just the speed of a single SAT call, but how the
implementation composes with the rest of the SFA pipeline -- particularly
`∧`, `∨`, `¬`, and minterm computation.

```
  ┌───────────────────────────────────────────────────────────┐
  │                   BooleanAlgebra trait                    │
  │                                                           │
  │   Decision               Composition      Evaluation      │
  │   ─────────────────      ───────────      ──────────────  │
  │   is_satisfiable(φ)      and(φ, ψ)        evaluate(φ, d)  │
  │   witness(φ)             or(φ, ψ)                         │
  │                          not(φ)                           │
  └────────┬───────────────────┬───────────────────┬──────────┘
           │                   │                   │
           ▼                   ▼                   ▼
  ┌──────────────────┐ ┌───────────────┐ ┌────────────────────┐
  │ SMT oracle       │ │ LP oracle     │ │ NFA construction   │
  │                  │ │               │ │                    │
  │ serialize φ to   │ │ build tableau │ │ compile φ to NFA   │
  │ SMT-LIB2, call   │ │ A·x ≤ b, run  │ │ over {0,1}ᵏ, test  │
  │ Z3, parse result │ │ simplex       │ │ emptiness via BFS  │
  └──────────────────┘ └───────────────┘ └────────────────────┘
           ✗                   ✗                   ✓
     opaque oracle       opaque oracle    composable predicate
```

The ✗/✓ marks on the last row are the crux of the argument.  An SMT or LP
solver can answer `SAT(φ)`, but cannot participate as a first-class predicate
in `∧`, `∨`, `¬`, and minterm operations.  An NFA **is** a predicate -- it
composes algebraically with every other NFA in the system.

### 3.5 The SFA Framework Is Backend-Agnostic

A crucial point that the rest of this document builds on: the SFA framework
does not prescribe *how* `SAT`, `∧`, `∨`, and `¬` are implemented.  It
requires only that they satisfy the `BooleanAlgebra` interface.  The
framework is **parameterized** by its backend — any decidable theory can
serve as the alphabet algebra.

Veanes (2013) defines two concrete backends in the foundational SFA paper:

- **2^(bvk)** — the powerset algebra over `k`-bit bitvectors, implemented
  via BDDs (Binary Decision Diagrams).  Satisfiability reduces to BDD
  non-emptiness.
- **SMT^σ** — an SMT solver as the decision procedure for a theory over
  sort `σ`.  The predicate set `Ψ` contains all formulas `φ(x)` in that
  theory with one free variable `x`.  Satisfiability delegates to the
  solver's `check-sat` command.

The SFT paper (Veanes et al., 2012) explicitly uses Z3 as the backend:
*"We use the SMT solver Z3 for solving label constraints that arise during
composition and equivalence checking algorithms."*

**This means SMT solvers can power SFAs.**  The question is not "SFA vs.
SMT" but rather: *which `BooleanAlgebra` backend should the SFAs use?*

```
  ┌─────────────────────────────────────────────────────┐
  │         SFA / SFT Framework                         │
  │  (determinize, minimize, intersect, complement,     │
  │   compose, pre-image, equivalence, ...)             │
  │                                                     │
  │         requires: BooleanAlgebra backend            │
  └───────┬────────────────┬──────────────────┬─────────┘
          │                │                  │
  ┌───────▼───────┐ ┌──────▼──────┐ ┌─────────▼─────────┐
  │ SMT^σ (Z3)    │ │ 2^(bvk)     │ │ MeTTaIL backends  │
  │               │ │ (BDD)       │ │                   │
  │ SAT: check-   │ │ SAT: BDD    │ │ IntervalAlgebra   │
  │   sat via FFI │ │ non-empty   │ │ CharClassAlgebra  │
  │ ∧: assert     │ │ ∧: BDD ∩    │ │ PresburgerAlgebra │
  │ ¬: negate     │ │ ¬: BDD ∁    │ │ KatBooleanAlgebra │
  │               │ │             │ │ ProductAlgebra    │
  │ Used by:      │ │ Used by:    │ │                   │
  │ Veanes 2012   │ │ Veanes 2013 │ │ Used by: MeTTaIL  │
  └───────────────┘ └─────────────┘ └───────────────────┘
```

MeTTaIL chose the third column — pure-Rust backends with zero external
dependencies — for the practical reasons detailed in §4–§6.  The SFA
algorithms themselves (determinization, minimization, intersection,
complement, equivalence) are identical regardless of backend.

---

## 4. Approach 1: SAT/SMT Solvers

As noted in §3.5, an SMT solver is a valid `BooleanAlgebra` backend for
SFAs — this is how the original research worked (Veanes et al., 2012;
Veanes, 2013).  MeTTaIL's SFA algorithms are identical to those in the
literature; only the backend differs.  This section explains why MeTTaIL
chose **not** to use Z3 or CVC5 as its backend, despite their theoretical
compatibility.

### 4.1 How SMT Solvers Work

An SMT solver (Satisfiability Modulo Theories) combines a propositional SAT
solver core with theory-specific decision procedures. The DPLL(T)
(Davis-Putnam-Logemann-Loveland modulo Theories) architecture (Nieuwenhuis,
Oliveras, & Tinelli, 2006) works as follows:

1. **Boolean abstraction.** Replace each theory atom (e.g., `x + y ≤ 100`)
   with a fresh propositional variable (e.g., `p₁`).  The formula becomes a
   Boolean formula over `p₁, p₂, …`.

2. **SAT solving.** Find a satisfying assignment to the Boolean variables
   using DPLL/CDCL (Conflict-Driven Clause Learning).

3. **Theory checking.** Pass the implied theory atoms to the relevant theory
   solver (e.g., linear arithmetic).  If the conjunction is theory-inconsistent,
   the theory solver produces a **conflict clause** that the SAT solver uses to
   backtrack.

4. **Iterate** until a consistent assignment is found or all possibilities are
   exhausted.

When multiple theories are involved (e.g., linear arithmetic AND uninterpreted
functions), the **Nelson-Oppen** combination procedure (Nelson & Oppen, 1979)
mediates between theory solvers by exchanging implied equalities, subject to
restrictions: the theories must have disjoint signatures and be
stably-infinite.

### 4.2 What Using Z3 Would Look Like

For the running example `x + y ≤ 100 ∧ x ≥ 10 ∧ y ≥ 20`, the operational
flow would be:

**Step 1.** Serialize the guard to SMT-LIB2:

```smt2
(declare-const x Int)
(declare-const y Int)
(assert (<= (+ x y) 100))
(assert (>= x 10))
(assert (>= y 20))
(check-sat)
(get-model)
```

**Step 2.** Call `z3-sys` via Rust FFI, or serialize to a subprocess.

**Step 3.** Parse the result string:

```smt2
sat
(model
  (define-fun x () Int 10)
  (define-fun y () Int 20))
```

**Step 4.** Extract the witness `(x = 10, y = 20)` and the satisfiability
verdict.

### 4.3 Practical Costs

**Dependency weight.** The `z3-sys` crate links against the Z3 C++ library,
adding approximately 1.5 GB to the build tree.  Z3 requires a C++ toolchain
and platform-specific shared libraries.  CVC5 has similar requirements.

**WASM compilation.** Contrary to earlier claims in this document, both Z3
and CVC5 can be compiled to WebAssembly: Z3 via the
[z3.wasm](https://github.com/cpitclaudel/z3.wasm) project (Pit-Claudel),
and CVC5 via Emscripten.  However, the WASM artifacts are large (~30 MB
for Z3), require the Emscripten toolchain (not native Rust `wasm32` target),
and have limited testing in production.  MeTTaIL's pure-Rust backends
compile natively to `wasm32-unknown-unknown` with zero additional tooling.

```
                            ┌───────────────────────────────┐
  Rust application          │  z3-sys (~1.5 GB)             │
  ┌────────────────┐        │  ├── libz3.so / libz3.dylib   │
  │ prattail crate │──FFI──▶│  ├── C++ toolchain required   │
  │ (~50 KB)       │        │  ├── Platform-specific build  │
  └────────────────┘        │  └── WASM: ~30 MB via         │
                            │       Emscripten (non-native) │
                            └───────────────────────────────┘
```

**FFI overhead.** Each `check-sat` call crosses the Rust-C++ boundary.
Context creation incurs a startup cost of approximately 1 ms.  For a grammar
with hundreds of rules -- each requiring multiple satisfiability checks during
guard analysis -- this overhead accumulates.

**Serialization round-trip.** MeTTaIL's predicate AST must be flattened to
SMT-LIB2 S-expressions.  The solver's model must be parsed back into Rust
data structures.  This serialization is **lossy**: SMT-LIB2 cannot directly
represent the predicate types used in minterm computation.

**Transparency and debuggability.** This is perhaps the most significant
practical cost — one that is easy to underestimate until a guard analysis
goes wrong.  An SMT solver is an **opaque oracle**: it accepts a formula and
returns SAT/UNSAT, but the intermediate reasoning is hidden.

| Concern                 | SMT solver (Z3/CVC5)                                                                                                               | Custom automata (MeTTaIL)                                                                                       |
|-------------------------|------------------------------------------------------------------------------------------------------------------------------------|-----------------------------------------------------------------------------------------------------------------|
| **Progress visibility** | No progress indicator during solving; a `check-sat` call blocks until completion or timeout                                        | Every BFS step, NFA state, and product-construction iteration is observable                                     |
| **Reproducibility**     | Heuristics (random restarts, VSIDS activity scores, theory combination ordering) may produce different execution paths across runs | Deterministic: same input always produces same states, transitions, and result                                  |
| **Version stability**   | Z3 4.12 may have different performance characteristics than 4.11; upstream heuristic changes can silently alter analysis behavior  | No external version dependencies; behavior changes only when MeTTaIL code changes                               |
| **Failure diagnosis**   | UNSAT core maps back to SMT-LIB2 assertions, not to original guard predicates; the inverse serialization is lossy                  | Failure traces directly reference automaton states and guard predicates — the same objects the programmer wrote |
| **Incremental solving** | Push/pop protocol is stateful; doesn't compose cleanly with Rust's ownership model                                                 | Custom algebras are stateless value types; compose naturally via `ProductAlgebra`                               |
| **Memory management**   | Z3 manages its own C++ heap; long-running compilations may accumulate unreclaimable memory                                         | Rust-managed allocations with predictable lifetimes; no foreign heap leaks                                      |
| **Supply chain**        | Z3 (~300K LOC C++) and CVC5 (~500K LOC C++) are large codebases with their own dependency trees                                    | Zero external dependencies; the entire decision procedure is auditable Rust                                     |

**Intuition.** When a guard analysis produces an unexpected result — a guard
reported as dead when the programmer believes it should be satisfiable — the
debugging process differs fundamentally.  With an SMT backend, the programmer
must: serialize the guard to SMT-LIB2, run Z3 in verbose mode, interpret the
solver's internal decision log, and map the conflict back to the original
guard.  With a custom automaton, the programmer can: inspect the NFA's states
and transitions directly, run the BFS emptiness check step-by-step, and see
exactly which transition failed to fire.  The custom approach is *transparent*
— the decision procedure's internals are the same objects the programmer
reasons about.

### 4.4 Scope Mismatch

SMT solvers support theories that are irrelevant to guard predicates:

| SMT theory                      | Relevant to guard predicates?                     |
|---------------------------------|---------------------------------------------------|
| Linear integer arithmetic (LIA) | Yes                                               |
| Arrays                          | No -- guards do not index into arrays             |
| Uninterpreted functions (UF)    | No -- guard predicates are interpreted            |
| Bitvectors (BV)                 | No -- guards operate on mathematical integers     |
| Floating point (FP)             | No -- guard arithmetic is integer-only            |
| Strings                         | Rarely -- character guards use `CharClassAlgebra` |

Meanwhile, SMT solvers **lack** direct support for the operations MeTTaIL
actually needs.  Each missing operation has a concrete consequence for the
predicated types pipeline:

- **SFA intersection** — computing the product of two symbolic automata.
  Without it, the compiler cannot answer "can guards `φᵢ` and `φⱼ` both
  match the same value?" (the overlap question from §2.3).  Overlapping
  guards that go undetected lead to silent ambiguity in dispatch — the
  programmer receives no SYM02 warning.

- **Minterm partitioning** — decomposing a set of predicates into
  equivalence classes.  Without it, the compiler cannot build the
  deterministic dispatch tables described in §2.4.  Every overlapping
  guard region would require runtime backtracking instead of a precomputed
  table lookup.

- **SFA determinization** — converting an NFA to a DFA using minterms.
  Without it, the generated dispatch code must simulate NFA
  nondeterminism at runtime (tracking sets of active states), rather than
  executing a single deterministic transition per input symbol.

- **SFA equivalence** — testing whether two automata accept the same
  language.  Without it, the compiler cannot detect subsumption (`φᵢ`
  shadows `φⱼ`) or redundancy (two guards that accept exactly the same
  values).  Subsumed guards waste code space; redundant guards confuse
  the programmer.

Using an SMT solver for these operations would require marshaling automata
into SMT-LIB2 format, performing the satisfiability check, and parsing the
result back — at every step of every automata algorithm.

### 4.5 Completeness, Traceability, and the Backend Decision

As established in §3.5, an SMT solver **can** serve as a `BooleanAlgebra`
backend for SFAs — the question is not capability but tradeoff.  The SMT
backend is theoretically valid; the practical costs in §4.3 (dependency
weight, FFI overhead, serialization, transparency) are the reasons MeTTaIL
chose custom automata instead.

An SMT solver guarantees completeness for its supported theories as a
**black-box** property.  The user trusts the solver's implementation; the
decision procedure is not transparent.

MeTTaIL's automata-based procedures have **provably decidable** complexity
with known bounds derived from classical automata theory:

- **Büchi (1960):** Presburger-definable sets correspond exactly to regular
  languages over binary-encoded integers.
- **NFA emptiness:** decidable in `O(|Q| + |δ|)` via BFS, where `Q` is the
  automaton's state set and `δ` is its transition relation.
- **NFA product:** `O(|Q₁| · |Q₂| · 2ᵏ)` for `k` variables.

The decision procedure's correctness can be verified from first principles --
and MeTTaIL does exactly this via cross-validation between `PresburgerAlgebra`
(direct NFA path) and `TheoryAlgebra<PresburgerTheory>` (constraint
propagation path).

### 4.6 Theory Combination vs. ProductAlgebra

In SMT, combining theories requires the **Nelson-Oppen** procedure, which
imposes structural requirements:

1. **Disjoint signatures** -- the theories cannot share function symbols.
2. **Stably-infinite** -- every satisfiable formula has an infinite model.
3. **Equality exchange** -- the combination algorithm propagates implied
   equalities between theory solvers.
4. **Convexity** -- needed for completeness in the basic algorithm; non-convex
   theories require disjunctive splitting.

In MeTTaIL, `ProductAlgebra<A, B>` composes any two `BooleanAlgebra`
instances with **no additional requirements**.  Independent domains factor
per-disjunct.  No equality exchange, no convexity condition, no theory
combination problem.  This is detailed in §9.

---

## 5. Approach 2: LP/ILP Solvers

Unlike SMT, LP/ILP solvers **cannot** serve as a `BooleanAlgebra` backend
for SFAs.  The `BooleanAlgebra` trait requires that `not(φ)` returns a
composable predicate of the same type — but the complement of a convex
polytope is not a convex polytope (§5.5).  LP solvers are therefore not
just a different backend choice; they are **structurally incompatible** with
the SFA framework.  The Presburger NFA construction (§7.1) provides an
automata-theoretic alternative that covers the same integer arithmetic
domain while satisfying `BooleanAlgebra`.

### 5.1 Linear Programming

A **linear program** (LP) in standard form asks whether a system of linear
inequalities over real-valued variables has a feasible point:

**Definition (LP Feasibility).** Given a matrix `A ∈ ℝᵐˣᵏ` and a vector
`b ∈ ℝᵐ`, the LP feasibility problem asks:

    ∃ x ∈ ℝᵏ : A · x ≤ b ?

The **simplex method** (Dantzig, 1963) solves this by traversing vertices of
the feasible **polytope** (the convex region in `ℝᵏ` bounded by the
constraint hyperplanes — a polygon in 2D, a polyhedron in 3D, and its
higher-dimensional generalization).  Though its worst-case complexity is
exponential
(Klee & Minty, 1972), it runs in polynomial time on practical instances.
**Interior point methods** (Karmarkar, 1984) provide a polynomial worst-case
guarantee of `O(k³·⁵ · L)`, where `L` is the input bit length.

**Intuition.** Picture the feasible region as a convex polygon in `ℝᵏ`.
The simplex method walks along edges of this polygon, pivoting from vertex
to vertex, until it reaches an optimal point or determines infeasibility.
Interior point methods cut through the interior of the polygon instead,
converging geometrically.

For the running example `x + y ≤ 100 ∧ x ≥ 10 ∧ y ≥ 20`, the feasible
region is a triangle in `ℝ²`:

```
  y
  ↑
100 ┤╲
    │  ╲
    │    ╲   x + y = 100
    │      ╲
    │        ╲
 80 ┤          ╲
    │            ╲
    │  Feasible    ╲
    │  region        ╲
    │  (integer        ╲
 40 ┤   lattice          ╲
    │   points             ╲
    │   inside)              ╲
 20 ┤┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈┈╲┈┈┈  y = 20
    │                            ╲
    ├──┬──┬──┬──┬──┬──┬──┬──┬──┬──→ x
    0  10 20 30 40 50 60 70 80 90
       ↑
       x = 10
```

The triangle is bounded by `x + y ≤ 100` (hypotenuse), `x ≥ 10` (left edge),
and `y ≥ 20` (bottom edge).  Any integer point in the shaded region is a
witness -- for instance, `(x, y) = (10, 20)` is the lower-left vertex.

### 5.2 Integer Linear Programming

Guard predicates involve **integers**, not reals.  Restricting variables to
`ℤ` gives the **integer linear program** (ILP):

    ∃ x ∈ ℤᵏ : A · x ≤ b ?

**Theorem (Karp, 1972).** ILP feasibility is NP-complete.

The standard approaches are:

- **Branch-and-bound:** solve the LP relaxation (over `ℝ`); if the solution is
  not integral, branch on a fractional variable, creating two subproblems.
  Worst case: exponential tree.
- **Cutting planes (Gomory, 1958):** add inequalities that exclude fractional
  solutions without removing integer-feasible points.  Iterate until the LP
  relaxation yields an integer solution or proves infeasibility.
- **Lenstra's algorithm (1983):** for fixed dimension `k`, ILP is solvable in
  polynomial time `O(2^(O(k³)) · L)`, where `L` is the input bit length.  The
  exponential dependence is on `k`, not on the coefficients.

**Intuition.** Branch-and-bound peels the problem like an onion: solve the
continuous relaxation (easy), then carve the solution space into pieces that
"round" each variable to an integer.  Cutting planes work differently --
they tighten the continuous polytope until it hugs the integer hull.  Both
are exact but can be expensive.

### 5.3 What Using an LP/ILP Solver Would Look Like

For the running example, the operational flow would be:

**Step 1.** Build the constraint matrix:

```
     ┌         ┐  ┌   ┐   ┌     ┐
     │  1    1 │  │ x │   │ 100 │
A =  │ −1    0 │, │   │ ≤ │ −10 │ = b
     │  0   −1 │  │ y │   │ −20 │
     └         ┘  └   ┘   └     ┘
```

The second row encodes `x ≥ 10` as `−x ≤ −10`; the third encodes `y ≥ 20`
as `−y ≤ −20`.

**Step 2.** Solve the LP relaxation via simplex.  For this small system,
the LP relaxation already yields integer vertices, so no branching is needed.
The simplex method performs approximately 2-3 pivot operations and returns
the vertex `(10, 20)`.

**Step 3.** Check integrality.  Here the solution is already integral.  In
general, branch-and-bound or cutting planes would be required.

**Result:** feasible, witness = `(10, 20)`.

### 5.4 Büchi's Bridge: Presburger Sets Are Regular Languages

The theoretical foundation for the automata approach to integer arithmetic
is a classical theorem that connects two seemingly unrelated domains:

**Theorem (Büchi, 1960).** A subset `S ⊆ ℤᵏ` is Presburger-definable (i.e.,
definable by a first-order formula in the theory `Th(ℤ, +, <, 0, 1)`) if and
only if the set of binary encodings of elements of `S` is a **regular language**
over the alphabet `{0, 1}ᵏ`.

**What this means.** Every linear inequality `Σ aᵢ · xᵢ ≤ b` over integers
corresponds to a finite automaton that reads the binary representations of the
variables bit-by-bit (least significant bit first) and accepts exactly the tuples `(x₁, …, xₖ)`
satisfying the inequality.  Boolean combinations of inequalities correspond to
Boolean operations on automata (product, union, complement).  Quantifiers
correspond to projection (drop a variable's bit dimension).

This theorem establishes a precise correspondence between LP/ILP operations
and NFA operations:

| LP/ILP operation             | NFA operation           | Complexity                 |
|------------------------------|-------------------------|----------------------------|
| Add constraint (row in A)    | Product automaton (∩)   | O(\|Q₁\| · \|Q₂\| · 2ᵏ)    |
| Disjunction of constraints   | Union automaton (∪)     | O(\|Q₁\| · \|Q₂\| · 2ᵏ)    |
| Project a variable (∃xᵢ)     | Drop bit dimension      | O(\|Q\| · 2ᵏ)              |
| Feasibility check            | NFA emptiness (BFS)     | O(\|Q\| + \|δ\|)           |
| Find feasible point          | Shortest accepting path | O(\|Q\| + \|δ\|)           |
| Negation (infeasible region) | NFA complement          | O(2^\|Q\| · 2ᵏ) worst case |

Every LP feasibility question reduces to an NFA emptiness question, and
every LP witness reduces to an NFA shortest-path computation.

### 5.5 The Decisive Advantage: Algebraic Closure

The correspondence in §5.4 shows that automata can answer the same questions
as LP solvers.  But the decisive advantage is **algebraic closure**: NFA
operations are closed under the `BooleanAlgebra` trait, while LP operations
are not.

Consider what happens when you call `and(φ₁, φ₂)` on two predicates:

- **NFA approach:** `and(nfa₁, nfa₂)` returns a new NFA (the product
  automaton).  This NFA is a first-class predicate that can be passed to
  `is_satisfiable()`, combined with further predicates via `and()`/`or()`,
  negated via `not()`, and used in minterm computation.  The result type is
  the same as the input type.

- **LP approach:** `and(tableau₁, tableau₂)` would need to... what?  Stack
  the constraint matrices?  The result is a larger matrix, not a predicate in
  the same algebra.  Three concrete capabilities are lost:
  - You cannot **negate** an LP tableau (the complement of a convex polytope
    is not convex) — so subsumption detection (`SAT(φⱼ ∧ ¬φᵢ) = false?`)
    is impossible, and the compiler cannot warn about shadowed guards.
  - You cannot compute **minterms** over LP constraints (minterms require
    negation) — so deterministic dispatch tables cannot be built, and
    overlapping guards force runtime backtracking.
  - You cannot **compose** an LP feasibility problem with a character class
    predicate from `CharClassAlgebra` — so mixed-domain guards like
    `x ≥ 10 ∧ ch ∈ [a-z]` would need ad-hoc combination logic with no
    formal guarantees, rather than the uniform `ProductAlgebra` composition.

The `BooleanAlgebra` trait requires that `and()`, `or()`, and `not()` return
predicates of the **same type** that can be further composed.  NFAs satisfy
this closure property.  LP tableaux do not.

**This is why Büchi's bridge matters.** It is not merely that automata *can*
decide integer arithmetic.  It is that automata represent the solution set as
a **regular language** -- a representation that is closed under all Boolean
operations.  An LP solver represents the solution set as a **convex polytope**
-- a representation that is not closed under complement or disjunction.

```
  NFA predicate                              LP tableau
  ─────────────                              ──────────
  and(nfa₁, nfa₂) → NFA (product)            "and"(A₁,A₂) → stacked matrix
  or(nfa₁, nfa₂)  → NFA (union)              "or"(A₁,A₂)  → ✗ not expressible
  not(nfa)        → NFA (complement)         "not"(A)     → ✗ not convex
  SAT(nfa)        → BFS emptiness            SAT(A,b)     → simplex
  minterm(Φ)      → ⋀ᵢ ψᵢ (ψᵢ ∈ {φᵢ, ¬φᵢ})   minterm(Φ)   → ✗ requires ¬
```

The minterm row is critical.  Minterm computation -- the engine of SFA
determinization -- requires forming conjunctions of predicates **and their
negations**.  Since LP cannot represent the complement of a polytope, it
cannot participate in minterm computation.  An LP-backed `BooleanAlgebra`
implementation would need to fall back to explicit enumeration of the integer
domain to implement `not()` -- defeating the purpose of symbolic automata.

### 5.6 The Trade-off: State Space Complexity

The automata approach pays a cost: the NFA state space for a single linear
constraint `Σ aᵢ · xᵢ ≤ b` over `k` variables is

    O((Σ |aᵢ| + |b|) · 2ᵏ)

where the `2ᵏ` factor comes from the alphabet size (one bit per variable per
tape position).  This is **exponential in `k`**, the number of variables.

LP simplex, by contrast, is polynomial in `k` for most practical instances.
For the same constraint with `k = 8` variables, the NFA would have an alphabet
of 256 symbols per position, while simplex would perform roughly 20 pivot
operations.

| k (variables) | NFA alphabet 2ᵏ | Typical NFA states (w = bit width) | Simplex pivots (typical) |
|---------------|-----------------|------------------------------------|--------------------------|
| 1             | 2               | ~w                                 | ~2                       |
| 2             | 4               | ~2w                                | ~4                       |
| 3             | 8               | ~3w                                | ~8                       |
| 4             | 16              | ~4w                                | ~12                      |
| 8             | 256             | ~8w                                | ~20                      |
| 16            | 65 536          | ~16w                               | ~40                      |

(Here w is the bit width, typically 16 for guard predicates.)

For guard predicates in MeTTaIL, `k` is almost always ≤ 4 -- a typical guard
involves 1-3 integer variables.  At `k ≤ 4`, the NFA construction completes in
microseconds and the state count stays in the hundreds.  The exponential
factor is harmless in this regime.

For `k > 6`, LP would outperform NFA construction in raw decision speed.
However, the LP result would be an opaque "feasible/infeasible" answer that
cannot participate in the rest of the SFA pipeline.  The NFA result, by
contrast, is a composable predicate that feeds into minterm computation,
guard overlap analysis, and subsumption checking -- operations that LP
cannot support.

### 5.7 Why a Hybrid Approach Would Not Help

A natural question: could we use LP for the raw satisfiability check and
automata for everything else?  The answer is no, because `is_satisfiable()`
is not an isolated operation.

Minterm computation calls `is_satisfiable()` on conjunctions of predicates
**and their negations**.  If `is_satisfiable()` delegates to an LP solver but
`and()` and `not()` build predicate ASTs, then every minterm check would
require:

1. Convert the predicate AST to an LP constraint matrix (handling `not()` by
   enumerating the complement -- which is not a single polytope).
2. Call the LP solver.
3. Parse the result.

The `not()` in step 1 is the fatal problem.  The complement of a convex
polytope is the union of up to `m` half-spaces (where `m` is the number of
constraints).  Forming a minterm with negations would require solving
exponentially many LP instances -- one per intersection of positively and
negatively oriented half-spaces.  The NFA approach handles this naturally
because complement is a primitive operation on automata (determinize + flip
accepting states), not a derived operation requiring case splitting.

> **Cross-reference:** [presburger-algebra.md](presburger-algebra.md) §Complexity
> Analysis provides detailed bounds for all NFA operations.

---

## 6. Approach 3: Datalog / Ascent

Like LP, Datalog **cannot** serve as a `BooleanAlgebra` backend for SFAs.
It lacks classical complement (only stratified negation-as-failure), operates
over finite active domains (guard predicates range over `ℤ`), and its
relations do not compose under `and()`/`or()`/`not()` as first-class
predicates (§6.3).  However, Datalog plays a different and complementary
role: Ascent handles **runtime behavioral evaluation** (fixpoint relation
lookups) while SFAs handle **compile-time guard analysis** (satisfiability,
overlap, minterms).

A reader familiar with MeTTaIL's architecture may ask: the pipeline already
uses **Ascent** — a Datalog engine — for semantic closure.  Why not use it
for guard satisfiability analysis too, instead of building a separate automata
framework?

The answer is that Datalog and automata solve fundamentally different
computational problems.  MeTTaIL already uses both, each for what it does
best.  This section explains the boundary.

### 6.1 What Datalog Is

**Datalog** is a restricted form of logic programming: function-free Horn
clauses evaluated bottom-up to a least fixed point.  A Datalog program
consists of **rules** that derive new facts from existing ones, and
**relations** that store the facts.  Evaluation iterates the rules until no
new facts are derived — the **least fixed point** (Ceri, Gottlob & Tanca,
1990).

The standard implementation uses **semi-naive evaluation** (Bancilhon, 1986)
to avoid redundant work:

```
╔══════════════════════════════════════════════════════════════════════════╗
║  SEMI_NAIVE_EVAL(rules, seed_facts)                                      ║
║                                                                          ║
║  Compute the least fixed point of a Datalog program by tracking          ║
║  only genuinely new facts (deltas) each iteration.                       ║
║                                                                          ║
║  ── Initialization ────────────────────────────────────────────────────  ║
║                                                                          ║
║      facts  ← seed_facts                                                 ║
║      Δfacts ← seed_facts          ▷ everything is "new" initially        ║
║                                                                          ║
║  ── Iterate ───────────────────────────────────────────────────────────  ║
║                                                                          ║
║      repeat:                                                             ║
║          Δnew ← apply(rules, Δfacts) ∖ facts                             ║
║                 ▷ derive from deltas only; discard already-known facts   ║
║          facts ← facts ∪ Δnew                                            ║
║          Δfacts ← Δnew                                                   ║
║      until Δfacts = ∅              ▷ fixed point reached                 ║
║                                                                          ║
║  return facts                                                            ║
║                                                                          ║
║  ── Complexity ────────────────────────────────────────────────────────  ║
║                                                                          ║
║  Terminates in at most |D|ᵏ iterations, where D is the finite active     ║
║  domain and k is the maximum rule arity.  Each iteration adds at least   ║
║  one fact.  Uniqueness follows from Knaster-Tarski.                      ║
╚══════════════════════════════════════════════════════════════════════════╝
```

**Intuition.** Datalog answers: *"Given these rules and seed facts, what is
derivable?"*  It computes everything that's true — constructively, bottom-up,
monotonically.  Facts are never retracted.

### 6.2 How MeTTaIL Already Uses Ascent

Ascent is not a hypothetical alternative — it is already a core engine in
MeTTaIL's pipeline.  The architecture has a clear division of responsibility
between Ascent and automata:

| Task                          | Engine             | Rationale                                     |
|-------------------------------|--------------------|-----------------------------------------------|
| Structural dispatch (parsing) | PathMap / Automata | `O(k)` prefix lookup, compiled decision trees |
| Equality closure              | Ascent (`eqrel`)   | Automatic reflexivity, symmetry, transitivity |
| Rewrite propagation           | Ascent rules       | Match via `eq_cat`, construct RHS             |
| Behavioral guard evaluation   | Ascent relations   | `O(1)` hash-indexed fixpoint lookups          |
| Guard satisfiability analysis | Automata (SFA)     | Decision procedures over infinite domains     |
| Guard overlap / subsumption   | Automata (SFA)     | Complement + intersection + emptiness         |
| Minterm partitioning          | Automata (SFA)     | Conjunction of predicates and their negations |

At runtime, guard evaluation proceeds in two strictly ordered phases:

```
  n!(q) ─────┐       ┌───── (n ? φ, preds).{c}
             │       │
             ▼       ▼
       ┌───────────────────┐
       │   Channel  n      │
       │                   │
       │   Phase 1:        │
       │   Structural      │  ← Automata-like: pattern matching
       │   match(φ, @(q))  │     Cost: O(|φ|)
       │        │          │
       │   ┌────▼─────┐    │
       │   │ σ = Some │    │──── None: Comm blocked
       │   └────┬─────┘    │
       │        │          │
       │   Phase 2:        │
       │   Behavioral      │  ← Ascent: fixpoint relation lookups
       │   ∀R(a) ∈ preds:  │     Cost: O(1) per lookup (hash-indexed)
       │   R(a[σ]) ∈ FP?   │──── No: Comm blocked
       │        │          │
       │   ┌────▼─────┐    │
       │   │   c[σ]   │    │
       │   └──────────┘    │
       └───────────────────┘
```

The ordering is both a correctness requirement (behavioral predicates
reference variables bound by the structural match) and a performance
optimization (fail-fast on cheap structural checks before invoking fixpoint
lookups).

> **Cross-reference:**
> [synergy.md](../../design/core-engines/synergy.md) details the full
> compile-time and runtime cooperation between PathMap, Ascent, and automata.
> [guards-and-predicates.md](../../design/core-engines/ascent-datalog/guards-and-predicates.md)
> specifies behavioral predicate evaluation.

### 6.3 What Automata Can Do That Datalog Cannot

Four properties required for guard satisfiability analysis are absent from
Datalog.

**1. Classical negation as a composable predicate.**

Datalog supports **stratified negation-as-failure** (NAF): a rule can check
"is fact `R(x)` absent from the current stratum's fixpoint?" via `!R(x)`.
(A **stratum** is a layer in the evaluation order where all negated relations
have already reached their fixed point, making the negation check safe.)
This is a **point query** — it returns a Boolean for a specific tuple.

Automata compute `¬φ` as a **first-class predicate** — a new NFA whose
language is the complement of `φ`'s language.  The complement NFA composes
with every other NFA via `and()`, `or()`, and minterm computation.

```
  Datalog NAF                              NFA complement
  ──────────                               ──────────────
  !R(x)                                    not(nfa)
    │                                        │
    ▼                                        ▼
  "is (x) absent from R?"                  new NFA accepting
  Returns: bool                            exactly {d | d ∉ L(nfa)}
  (point query, not composable)            (first-class predicate, composable)
```

Minterm computation requires forming `ψ₁ ∧ ψ₂ ∧ ⋯ ∧ ψₙ` where each
`ψᵢ ∈ {φᵢ, ¬φᵢ}`.  This demands classical complement as a composable
object — not a point query.  Datalog's NAF cannot provide this.

**2. Infinite domains.**

Datalog requires a **finite active domain** — the set of constants
appearing in the program — for termination.  The convergence guarantee
(`|D|ᵏ` iterations) depends on `D` being finite.

Guard predicates like `x + y ≤ 100` range over `ℤ`, an infinite domain.
To represent this constraint in Datalog, you would need a relation containing
every integer pair `(x, y)` satisfying the inequality — an infinite relation
that cannot be materialized.

SFAs handle infinite domains via **symbolic predicates**: a single NFA
transition guarded by `[10, ∞)` compactly represents infinitely many
concrete values without enumerating them.

**3. No algebraic composition under `BooleanAlgebra`.**

The `BooleanAlgebra` trait requires `and()`, `or()`, and `not()` to return
predicates **of the same type** that compose further.  Datalog relations
support JOIN (`∧`) but do not return composable objects for `∨` or `¬`:

- `and(R₁, R₂)` → JOIN is natural in Datalog (rule body with two relation
  references).  But the result is a new relation **inside the Datalog
  program**, not a first-class predicate object that the SFA pipeline can
  manipulate.
- `or(R₁, R₂)` → Datalog has no built-in disjunction of relations as a
  composable predicate.
- `not(R)` → NAF is a Boolean check, not a composable predicate (see above).

Because Datalog relations do not implement `BooleanAlgebra`, they cannot
participate in minterm-based determinization or compose via
`ProductAlgebra<AscentRelation, CharClassAlgebra>`.

**4. Different computational question.**

Datalog and automata answer fundamentally different questions:

|              | Datalog                       | Automata                           |
|--------------|-------------------------------|------------------------------------|
| **Question** | "What facts are derivable?"   | "Does any assignment satisfy `φ`?" |
| **Mode**     | Constructive (bottom-up)      | Existential (decision)             |
| **Output**   | All true facts (the fixpoint) | Yes/no + optional witness          |
| **Computes** | Everything that's true        | Whether something is possible      |

A guard satisfiability check asks: *"Is there any value `d` such that `φ(d)`
holds?"*  This is an existential decision — it does not need to enumerate all
satisfying values, only determine whether at least one exists.  Automata
answer this in `O(|Q| + |δ|)` via BFS reachability.  Datalog would need to
materialize the (potentially infinite) extension of the guard predicate and
check non-emptiness — a fundamentally different (and often infeasible)
computation.

### 6.4 What Datalog Can Do That Automata Cannot

The converse is equally true — Ascent handles tasks that automata cannot.

**1. Rule-based inference with congruence propagation.**

Ascent's `eqrel` annotation automatically maintains reflexivity, symmetry,
and transitivity of equality relations.  Congruence rules propagate equality
through constructors: if `a = b`, then `f(a) = f(b)` for every constructor
`f`.  Expressing this in automata would require encoding the entire term
algebra as an automaton alphabet — impractical and unnatural.

**2. Semi-naive incremental evaluation.**

Ascent tracks **delta relations** to avoid reprocessing already-derived facts.
Each iteration explores only fact combinations involving at least one new
fact.  Automata have no analog of incremental fixpoint computation — they
are stateless decision procedures, not iterative inference engines.

**3. Declarative rule specification.**

Equations like

    eq_proc(s, t) :- proc(s), match_pattern(s, "PDrop(NQuote(p))"), let t = p

are natural in Datalog: the rule *declares* what equality holds, and the
engine determines *how* to compute it.  Encoding this logic as automata
transitions would require flattening the term structure into a symbol
alphabet and defining transitions for every possible pattern — losing the
declarative clarity that makes Ascent rules readable and maintainable.

**4. Behavioral guard evaluation at runtime.**

When a guard's behavioral predicate queries `safe(x)` at runtime, the check
reduces to a hash-indexed lookup in Ascent's fixpoint relation — `O(1)` per
query.  This is the natural representation for runtime predicate evaluation:
the fixpoint has already been computed, and the guard simply checks membership.
Automata are compile-time analysis tools; they do not persist at runtime.

### 6.5 The Complementary Architecture

The pipeline uses automata at compile time and Ascent at runtime, with each
handling the task it is best suited for:

```
  Compile time                            Runtime
  ────────────                            ───────
  ┌──────────────────────┐               ┌────────────────────────┐
  │  Guard analysis      │               │  Phase 1: Structural   │
  │  (SFA / Presburger)  │               │  match(φ, @(q))        │ ← automata-derived
  │                      │               │  Cost: O(|φ|)          │   (compiled match arms)
  │  • Satisfiable?      │               └───────────┬────────────┘
  │  • Overlap?          │                           │ σ (bindings)
  │  • Subsumes?         │               ┌───────────▼────────────┐
  │  • Dead rule?        │               │  Phase 2: Behavioral   │
  │  • Minterms?         │               │  R(a[σ]) ∈ FP?         │ ← Ascent
  └──────────────────────┘               │  Cost: O(1) per lookup │   (fixpoint relations)
                                         └────────────────────────┘
```

Automata decide what's *possible* (compile-time analysis over infinite
domains).  Ascent computes what's *true* (runtime semantic closure over
concrete terms).  Neither can replace the other: automata lack rule-based
inference, and Datalog lacks classical complement, infinite-domain support,
and `BooleanAlgebra` composability.

> **Cross-reference:**
> [synergy.md](../../design/core-engines/synergy.md) provides the full
> architectural diagram and cooperation protocol.

---

## 7. Approach 4: Automata-Based Decision Procedures (What MeTTaIL Uses)

MeTTaIL's approach compiles guard predicates into NFAs over binary-encoded
integers and reduces satisfiability to NFA language non-emptiness.  This
section summarizes the mechanics; for the full construction, see
[presburger-algebra.md](presburger-algebra.md).

### 7.1 Büchi's Construction: Carry Propagation as Automata States

The Bartzis-Bultan (2003) remainder-based construction compiles an atomic
linear constraint `Σ aᵢ · xᵢ ≤ b` into an NFA as follows.

**Intuition.** Variables are encoded in binary, read one bit at a time
starting from the least significant bit (LSB).  Each "symbol" on the NFA's
tape is a k-bit vector giving the current bit of each variable.  The
automaton tracks a **remainder** that captures the carry propagation of binary
addition -- exactly like the running remainder in long division.  If the
remainder is non-negative after all bits are read, the constraint is satisfied.

The construction works in three steps:

```
╔═════════════════════════════════════════════════════════════════════════╗
║  REMAINDER_NFA(a₁, …, aₖ, b, w)                                         ║
║                                                                         ║
║  Build an NFA that accepts binary-encoded tuples (x₁, …, xₖ) ∈ ℤᵏ       ║
║  satisfying Σᵢ aᵢ · xᵢ ≤ b, where each xᵢ is represented as a           ║
║  w-bit two's-complement integer read LSB-first.                         ║
║                                                                         ║
║  ── Step 1: Precompute bit sums ──────────────────────────────────────  ║
║                                                                         ║
║  For each possible alphabet symbol σ ∈ {0, 1}ᵏ (there are 2ᵏ of them),  ║
║  compute the weighted bit sum:                                          ║
║                                                                         ║
║      bit_sum(σ) ← Σᵢ aᵢ · σᵢ                                            ║
║                                                                         ║
║  where σᵢ is the i-th bit of σ.                                         ║
║                                                                         ║
║  ── Step 2: Build the remainder automaton ────────────────────────────  ║
║                                                                         ║
║  States are (position, remainder) pairs.                                ║
║                                                                         ║
║      initial state:   (0, b)                                            ║
║                                                                         ║
║      transition:      (j, r) ──σ──▶ (j + 1, ⌊(r − bit_sum(σ)) / 2⌋)     ║
║                                                                         ║
║  The division by 2 is the automata-theoretic analog of carry            ║
║  propagation: after accounting for the current bit's contribution,      ║
║  the remaining constraint is halved (shifting to the next bit).         ║
║                                                                         ║
║  ── Step 3: Set acceptance ───────────────────────────────────────────  ║
║                                                                         ║
║      accepting states:  { (w, r) | r ≥ 0 }                              ║
║                                                                         ║
║  After w bits, a non-negative remainder means the constraint holds.     ║
║  The NFA's language is exactly the set of binary-encoded tuples         ║
║  satisfying the constraint.                                             ║
╚═════════════════════════════════════════════════════════════════════════╝
```

> **Full construction details:** [presburger-algebra.md](presburger-algebra.md)
> §NFA Construction.

### 7.2 Boolean Operations as NFA Operations

Once atomic constraints are compiled to NFAs, Boolean combinations use
standard NFA operations:

| Boolean operation | NFA operation | Construction                                       |
|-------------------|---------------|----------------------------------------------------|
| φ ∧ ψ             | Intersection  | Product automaton: states = Q₁ × Q₂                |
| φ ∨ ψ             | Union         | Product automaton with relaxed acceptance          |
| ¬φ                | Complement    | Determinize (subset construction) + flip accepting |
| ∃xᵢ. φ            | Projection    | Drop variable i's bit from each symbol             |

A **product automaton** simulates two automata in lockstep: its states are
pairs `(q₁, q₂)` from the two input automata, and a transition fires only
when both components can advance on the same input symbol.  For intersection,
a product state is accepting iff both components accept; for union, iff
either accepts.

**Subset construction** (also called the powerset construction) converts an
NFA into a DFA by tracking *sets* of NFA states as single DFA states.  Each
DFA state represents "all the NFA states that could be active simultaneously."
Complementing the resulting DFA is trivial: flip accepting and non-accepting
states.

The critical property is that every operation produces a new NFA -- the result
type is the same as the input type.  This is the **algebraic closure** that
LP lacks (§5.5).

### 7.3 The Decision Procedures

With the NFA in hand, the two core queries become graph algorithms:

```
╔══════════════════════════════════════════════════════════════════════════╗
║  PRESBURGER_SAT(φ, w)                                                    ║
║                                                                          ║
║  Decide whether the Presburger predicate φ is satisfiable,               ║
║  returning a Boolean and (optionally) a witness assignment.              ║
║                                                                          ║
║  ── Step 1: Normalize ─────────────────────────────────────────────────  ║
║                                                                          ║
║  Convert φ to negation normal form (NNF) via PUSH_NEGATION_INWARD.       ║
║  This avoids the expensive general complement construction by            ║
║  resolving negation at the atomic level:                                 ║
║                                                                          ║
║      ¬(Σ aᵢ · xᵢ ≤ b)  ≡  Σ (−aᵢ) · xᵢ ≤ −(b + 1)                        ║
║                                                                          ║
║  Complement on the NFA is needed only for ¬∃ (i.e., ∀).                  ║
║                                                                          ║
║  ── Step 2: Compile NNF to NFA ────────────────────────────────────────  ║
║                                                                          ║
║  nfa ← COMPILE_NNF(φ_nnf, k, w)     ▷ see below                          ║
║                                                                          ║
║  ── Step 3: Decide ───────────────────────────────────────────────────   ║
║                                                                          ║
║  is_sat ← BFS from initial states of nfa; return true iff an             ║
║           accepting state is reachable.                      O(|Q|+|δ|)  ║
║                                                                          ║
║  ── Step 4: Extract witness (optional) ────────────────────────────────  ║
║                                                                          ║
║  If is_sat: trace the BFS shortest path from an initial state to an      ║
║  accepting state.  Decode the k-bit symbols along the path into          ║
║  integer values (LSB-first binary → integer).               O(|Q|+|δ|)   ║
╚══════════════════════════════════════════════════════════════════════════╝
```

The recursive NFA compilation mirrors the predicate's structure:

```
╔══════════════════════════════════════════════════════════════════════════╗
║  COMPILE_NNF(φ, k, w)                                                    ║
║                                                                          ║
║  Recursively compile a Presburger predicate in NNF to an NFA over        ║
║  the alphabet {0, 1}ᵏ with bit width w.                                  ║
║                                                                          ║
║  match φ:                                                                ║
║                                                                          ║
║      True  →  UNIVERSAL_NFA(k, w)                                        ║
║               Accept all inputs of length w over {0,1}ᵏ.                 ║
║                                                                          ║
║      False →  EMPTY_NFA(k, w)                                            ║
║               Accept nothing.                                            ║
║                                                                          ║
║      Atom(Σ aᵢ·xᵢ ≤ b)  →  REMAINDER_NFA(a₁, …, aₖ, b, w)                ║
║               The Bartzis-Bultan construction (§7.1).                    ║
║                                                                          ║
║      And(φ₁, φ₂)  →  INTERSECT(COMPILE_NNF(φ₁, k, w),                    ║
║                                 COMPILE_NNF(φ₂, k, w))                   ║
║               Product automaton: states = Q₁ × Q₂.                       ║
║                                                                          ║
║      Or(φ₁, φ₂)  →  UNION(COMPILE_NNF(φ₁, k, w),                         ║
║                            COMPILE_NNF(φ₂, k, w))                        ║
║               Product automaton with acceptance = F₁ ∪ F₂                ║
║               (Fᵢ = accepting states of NFA i).                          ║
║                                                                          ║
║      Not(Exists(v, φ′))  →  COMPLEMENT(                                  ║
║                                PROJECT(v, COMPILE_NNF(φ′, k, w)))        ║
║               ∀v.¬φ′ = ¬(∃v.φ′).  Determinize + flip.                    ║
║               This is the only case requiring complement.                ║
║                                                                          ║
║      Exists(v, φ′)  →  PROJECT(v, COMPILE_NNF(φ′, k, w))                 ║
║               Drop variable v's bit dimension, merging transitions.      ║
╚══════════════════════════════════════════════════════════════════════════╝
```

### 7.4 Minterm-Based Determinization

When Presburger predicates appear as SFA transition guards (not just as
standalone satisfiability queries), they participate in **minterm-based
determinization** (D'Antoni & Veanes, 2014).

Given a set of predicates Φ = {φ₁, …, φₙ} appearing on outgoing transitions
from an SFA state, the minterms are all maximal satisfiable conjunctions:

    m = ψ₁ ∧ ψ₂ ∧ ⋯ ∧ ψₙ     where each ψᵢ ∈ {φᵢ, ¬φᵢ}

Each minterm defines an equivalence class of domain elements that are
treated identically by every guard.  Within a single minterm, all elements
are indistinguishable -- they trigger exactly the same set of transitions.

**Why this requires algebraic closure.** Computing minterms requires calling
`SAT(ψ₁ ∧ ψ₂ ∧ ⋯ ∧ ψₙ)` where each `ψᵢ` may be a negation `¬φᵢ`.  This
is exactly the operation that LP cannot support (§5.5): the complement of an
LP polytope is not a polytope.  NFA-based Presburger predicates handle this
naturally because `¬φᵢ` is just another NFA (the complement automaton), and
`SAT(ψ₁ ∧ ⋯ ∧ ψₙ)` is a product automaton emptiness check.

**Complexity.** For `n` predicates, there are at most `2ⁿ` minterms.  Each
minterm satisfiability check requires forming a conjunction (`n − 1` product
automaton constructions) and testing emptiness.  The total cost is

    O(2ⁿ · (n − 1) · |Q|² · 2ᵏ)

For typical guard analyses, `n` is small (2-5 predicates per SFA state), making
this tractable.

> **Full formalization:** [boolean-algebra.md](../../theory/symbolic/boolean-algebra.md)
> Theorem 1.2 (Minterm-Based Determinization).

### 7.5 The NNF Optimization

The general complement construction -- determinize via subset construction,
then flip accepting states -- is `O(2^|Q|)` in the number of NFA states.  This
exponential blowup can be avoided in most cases by converting to **negation
normal form** (NNF) before compilation.

The NNF transformation pushes negation inward using De Morgan's laws and
resolves atomic negation algebraically:

    ¬(Σ aᵢ · xᵢ ≤ b)  ≡  Σ (−aᵢ) · xᵢ ≤ −(b + 1)

This is because `¬(s ≤ b)` is equivalent to `s > b`, which is `s ≥ b + 1`,
which is `−s ≤ −(b + 1)`.  The negated constraint compiles directly to an
NFA via the Bartzis-Bultan construction, avoiding complement entirely.

The only case where complement is needed is `¬∃v. φ` (universal
quantification), which cannot be expressed without complementing the
projection.  In practice, guard predicates rarely contain universal
quantification, so the exponential complement is rarely triggered.

### 7.6 Other Automata in the Compile-Time Pipeline

SFAs and Presburger NFAs are the workhorses of guard analysis, but the
pipeline includes a full suite of specialized automata for different
analytical tasks.  Nearly all operate at **compile time only** — they
produce analysis results, lint diagnostics, or codegen decisions, and their
structures are discarded after compilation.  The one exception is the WFST,
whose weighted prediction ranking persists into the generated runtime code
to order dispatch alternatives by priority.

The following diagram shows how features detected in a guard's AST trigger
specific automata modules, and how those modules' outputs converge into
the codegen and lint layers:

```
  Guard AST
       │
       ▼
  ┌────────────────────────────────────────────────────────┐
  │              Feature extraction (post-order walk)      │
  └──┬───────┬──────┬──────┬──────┬──────┬──────┬───────┬──┘
     │       │      │      │      │      │      │       │
     ▼       ▼      ▼      ▼      ▼      ▼      ▼       ▼
  ┌──────┐┌─────┐┌─────┐┌─────┐┌─────┐┌─────┐┌──────┐┌─────┐
  │ M1   ││ M3  ││ M6  ││ M8  ││ M9  ││ M12 ││ M13  ││ M15 │
  │ SFA  ││ AWA ││ Reg ││ MTp ││ MSt ││ Pres││ Unif ││ SFT │
  │      ││     ││     ││     ││     ││     ││      ││     │
  │always││ ∀   ││eq/  ││join ││count││arith││struct││xform│
  │ on   ││guard││fresh││patt ││guard││guard││guard ││guard│
  └──┬───┘└──┬──┘└──┬──┘└──┬──┘└──┬──┘└──┬──┘└──┬───┘└──┬──┘
     │       │      │      │      │      │      │       │
     └───────┴──────┴──────┴──┬───┴──────┴──────┴───────┘
                              │
                   ┌──────────┴──────────┐
                   ▼                     ▼
          ┌──────────────┐      ┌──────────────┐
          │ Lint layer   │      │ Codegen      │
          │ SYM01–SYM03  │      │ (tier-based) │
          │ PB01, UN01   │      │              │
          └──────────────┘      └──────────────┘
```

Each module is activated only when the guard contains features it handles
(e.g., M12 activates only when arithmetic operators appear).  M1 (SFA) is
always active — it provides the core satisfiability and minterm operations
that every guard analysis requires.

| Module | Automaton                                 | Role                                                                                          |
|--------|-------------------------------------------|-----------------------------------------------------------------------------------------------|
| M1     | SFA (Symbolic Finite Automaton)           | Guard satisfiability, overlap, minterm-based determinization                                  |
| M2     | Weighted Büchi Automaton                  | Liveness — detects whether infinite execution paths have bounded or unbounded cost            |
| M3     | Alternating Weighted Automaton (AWA)      | Universal/existential branching — game-semantic verification of `∀`-guards                    |
| M4     | Weighted Visibly Pushdown Automaton (VPA) | Structured parsing — delimiter matching with decidable equivalence                            |
| M5     | Parity Alternating Tree Automaton         | µ-calculus model checking — recursive structural properties over trees                        |
| M6     | Register Automaton                        | Data-equality over infinite domains — tag matching, variable freshness                        |
| M7     | Probabilistic Automaton                   | Log-domain weights, Viterbi best-path, selectivity estimation                                 |
| M8     | Multi-Tape Automaton                      | K-synchronized tapes — multi-channel join pattern coordination                                |
| M9     | Multiset Automaton                        | Process multiplicity, cardinality constraints, resource analysis                              |
| M10    | Weighted MSO                              | Büchi-Elgot-Trakhtenbrot bridge — restricted MSO → recognizable formal power series           |
| M11    | Two-Way Transducer                        | Bidirectional scanning — cross-channel constraint propagation                                 |
| M12    | Presburger NFA                            | Multi-variable linear integer arithmetic (`BooleanAlgebra` backend for `PresburgerAlgebra`)   |
| M13    | Unification Theory                        | Structural unification — occurs check, subsumption, pattern overlap                           |
| M14    | Subtype Lattice                           | Token lattice for lexical ambiguity — zero-overhead linear path                               |
| M15    | SFT (Symbolic Finite Transducer)          | Guard transformation — pre-image/post-image, composition, functionality (Veanes et al., 2012) |
| —      | CRA (Cost Register Automaton)             | Quantitative regular cost functions (Alur et al., 2013)                                       |
| —      | WFST (Weighted Finite State Transducer)   | Dispatch ranking — tropical-weighted prediction of parse rule priority                        |
| —      | Nominal Automaton                         | Orbit-finite sets for name-passing calculi — scope and α-equivalence                          |

All modules M1–M15 and the additional automata are implemented.  The WFST
is notable as the one automaton whose structure **does** persist into runtime:
it provides the weighted prediction ranking that orders dispatch alternatives
by priority.

**Intuition for each implemented automaton:**

- **Weighted Büchi (M2):** A Büchi automaton accepts infinite words by
  visiting accepting states infinitely often.  The weighted variant assigns
  semiring-valued costs to transitions, enabling the compiler to detect
  whether a recursive grammar's infinite execution has converging or
  diverging cost — a liveness property that finite-word automata cannot
  express.  *Use case:* a guard like
  `for (@x <- ch) where always_eventually(responds(x))` asserts that a
  process will always eventually respond — an omega-regular liveness
  property.  M2 checks whether the weighted accepting cycle converges,
  detecting guards that impose unrealizable liveness requirements.

- **AWA (M3):** Alternating automata generalize nondeterministic automata
  by allowing transitions to branch both existentially ("some successor
  accepts") and universally ("all successors accept").  *Use case:*
  `for (@x <- ch) where forall y in nodes. safe(y)` — the `∀` quantifier
  triggers M3.  The automaton verifies the universal property by branching
  to check every element of `nodes`, accepting only if `safe(y)` holds
  for all of them.

- **VPA (M4):** Visibly pushdown automata recognize languages where the
  push/pop structure is determined by the input symbol — matching
  brackets, delimiters, and nested scopes.  Unlike general pushdown
  automata, VPAs have decidable equivalence, making them suitable for
  compile-time guard analysis.  *Use case:* a guard pattern like
  `for (@{f(g(x))} <- ch)` has two levels of constructor nesting.  The
  VPA tracks push/pop depth to analyze whether this guard overlaps with
  the shallower `for (@{f(y)} <- ch)` — a question that flat SFAs
  cannot answer because they have no stack.

- **Parity Alternating Tree Automaton (M5):** Guards over recursive data
  types require automata that operate on trees rather than strings.  Parity
  tree automata express µ-calculus properties: alternating fixpoints of
  greatest and least fixed points, capturing both safety and liveness over
  recursive structures.  *Use case:*
  `for (@tree <- ch) where all_leaves_positive(tree)` asserts a recursive
  structural property — every leaf in a tree-shaped process must satisfy
  `positive`.  M5 checks the µ-calculus formula
  `νX. (leaf ⟹ positive) ∧ □X`, verifying the property holds at every
  node down to the leaves.

- **Register Automaton (M6):** Finite automata extended with a finite
  number of registers that store data values from an infinite domain.
  Transitions can compare the current input to register contents (equality
  or disequality) and update registers.  *Use case:*
  `for (@x, @y <- ch) where eq(x, y)` requires comparing two values from
  an infinite domain — the register stores `x` and checks whether `y`
  matches.  Similarly, `for (@x <- ch) where fresh(x)` checks that `x`
  has not been seen before — the register accumulates seen values and
  tests disequality.

- **Probabilistic Automaton (M7):** Assigns log-domain probability weights
  to transitions, enabling **selectivity estimation** for guard predicates.
  *Use case:* given guards A (`x ∈ [0, 50)`) and B (`x ∈ [30, 100)`)
  overlapping in `[30, 50)`, M7 estimates that under a uniform
  distribution, 60% of values fall in A's unique region and 40% in B's.
  The dispatch system tests A first — the more selective guard —
  reducing the expected number of evaluations per message.

- **Multi-Tape Automaton (M8):** Reads `k` input tapes simultaneously,
  synchronized at each step.  Models multi-channel join patterns where a
  guard spans values received from different channels — each channel
  corresponds to a tape, and the automaton coordinates their constraints.
  *Use case:* `for (@x <- ch1; @y <- ch2) where f(x, y)` — the guard
  `f(x, y)` relates values from two channels.  M8 builds a two-tape
  automaton where tape 1 reads `x` from `ch1` and tape 2 reads `y` from
  `ch2`, analyzing the joint constraint for satisfiability and overlap
  with other join-pattern guards on the same channels.

- **Multiset Automaton (M9):** Guards involving cardinality constraints
  operate over multisets of processes, not sequences.  Multiset automata
  track multiplicities and resource budgets.  *Use case:*
  `for (@bag <- ch) where count_ge(bag, 3)` accepts only if the bag
  contains at least 3 elements.  M9 analyzes whether this guard overlaps
  with `count_ge(bag, 5)` (yes — every bag with 5 elements also has 3)
  and detects subsumption.

- **Weighted MSO (M10):** The Büchi-Elgot-Trakhtenbrot theorem states that
  recognizable formal power series (weighted automata) correspond exactly
  to restricted MSO (Monadic Second-Order) formulas.  This module provides
  the bridge: a restricted MSO formula over a grammar can be translated to
  a weighted automaton for decidable analysis.  *Use case:* a property
  like "the number of rewrite steps to normal form is bounded by `k`" is
  expressible as an MSO formula.  M10 translates it to a weighted
  automaton, enabling the compiler to check whether the bound is
  satisfiable and whether two such bounds overlap.

- **Two-Way Transducer (M11):** Scans input bidirectionally (left-to-right
  and right-to-left), enabling cross-channel constraint propagation.
  *Use case:* `for (@x <- ch1; @y <- ch2) where depends(x, y)` — the
  constraint `depends(x, y)` references variables from both channels.
  M11 propagates the constraint bidirectionally: knowing `x`'s value
  constrains the acceptable range of `y`, and vice versa.  This is
  essential for optimizing join-pattern dispatch — the two-way scan
  determines which channel to read first for minimal backtracking.

- **Presburger NFA (M12):** The NFA constructed by the Büchi/Bartzis-Bultan
  algorithm (§7.1) for integer linear constraints.  This is the concrete
  automaton that implements `PresburgerAlgebra`'s `is_satisfiable()` — it
  reads binary-encoded integer tuples and accepts exactly those satisfying
  the constraint.  *Use case:*
  `for (@x, @y <- ch) where x + y ≤ 100, x ≥ 10` — the running example
  from §8.  M12 builds an NFA for each linear constraint and intersects
  them to analyze the joint guard.

- **Subtype Lattice (M14):** When multiple guards match a value, the
  subtype lattice provides **type-directed disambiguation**: the most
  specific guard (lowest in the lattice) takes priority.  *Use case:*
  a guard accepting `Nat` is more specific than one accepting `Number`,
  which is more specific than `Any`.  If all three guards match, the
  lattice selects `Nat` without requiring explicit priority annotations
  from the programmer.

- **SFT (M15):** Where SFAs recognize languages (accept/reject), SFTs
  compute **transformations** (input → output).  Each transition has both a
  guard (predicate on the input) and a **yield** (function producing output
  symbols).  *Use case:* given a guard `φ` on the output of a sanitizer
  function, the pre-image `SFT⁻¹(φ)` computes what raw inputs would
  produce sanitized outputs matching `φ` — answering "which unsanitized
  values would pass this guard after transformation?"  Composition
  (`SFT₁ ∘ SFT₂`) chains transformations.  The SFT algebra (Veanes et
  al., 2012) supports intersection, composition, pre-image, equivalence,
  and domain/range analysis — all using the same `BooleanAlgebra` backend
  as SFAs.

- **CRA (Cost Register Automaton):** Extends finite automata with
  semiring-valued registers updated at each input step.  In the predicated
  types pipeline, CRA drives the **cost-benefit analysis** that decides
  which automata modules to activate for a given guard.  *Use case:* for a
  grammar with 50 rules, CRA estimates that activating M8 (multi-tape)
  costs 3× more than M12 (Presburger) and skips M8 when the guard has no
  join patterns — enabling the compiler to avoid expensive analyses that
  the guard's structure doesn't require.

- **WFST (Weighted Finite State Transducer):** The one automaton that
  persists into runtime.  WFSTs are parameterized by a semiring; the
  dispatch ranking uses tropical weights (lower = higher priority), while
  other pipeline stages use different semirings (e.g., log semiring for
  probabilistic selectivity).  *Use case:* at runtime, when a value
  matches guarded receives A, B, and C, the WFST's tropical weights
  (e.g., A: 0.2, B: 0.5, C: 0.8) select A first — the most specific
  rule — avoiding unnecessary backtracking through B and C.

- **Nominal Automaton:** Extends finite automata with orbit-finite sets
  from nominal set theory (Bojańczyk et al.).  In the rho-calculus, names
  are first-class entities subject to scope, binding, and α-equivalence.
  *Use case:* `for (@x <- ch) where fresh(x, {a, b, c})` checks that `x`
  is a name distinct from `a`, `b`, and `c`.  The nominal automaton
  analyzes this using orbit-finite symmetry — recognizing that any
  permutation of names preserving {a, b, c} leaves the guard invariant —
  rather than enumerating all possible name assignments.

At compile time, the analysis results from these modules manifest as
generated code: inline checks, Ascent joins, match arms, decision trees,
computed goto tables, and WFST prediction rankings (§2.6).

---

## 8. Worked Example: Three Approaches Compared

We now trace the running example through all three approaches in full detail.

**Guard:** `x + y ≤ 100 ∧ x ≥ 10 ∧ y ≥ 20`

This is a conjunction of three linear constraints over two integer variables
(`k = 2`).  We use a bit width of `w = 8` for readability (covering integers in
[−128, 127]).

### 8.1 The SMT Path

**Step 1: Serialize.**

```smt2
(set-logic QF_LIA)          ; Quantifier-Free Linear Integer Arithmetic
(declare-const x Int)
(declare-const y Int)
(assert (<= (+ x y) 100))
(assert (>= x 10))
(assert (>= y 20))
(check-sat)
(get-model)
```

**Step 2: Call Z3.**

```
  Rust  ─── FFI ───▶  libz3.so  ─── DPLL(T) ───▶  Result
  4 μs serialize      ~1 ms startup + solve        SAT, model
```

**Step 3: Parse.**

```smt2
sat
(model
  (define-fun x () Int 10)
  (define-fun y () Int 20))
```

**Total:** ~1 ms (dominated by Z3 startup), plus the 1.5 GB dependency.

### 8.2 The LP Path

**Step 1: Normalize constraints.**

```
  x + y ≤ 100       →   a = ( 1,  1), b = 100
  x ≥ 10            →   a = (−1,  0), b = −10     (flip sign)
  y ≥ 20            →   a = ( 0, −1), b = −20     (flip sign)
```

**Step 2: Simplex tableau (Phase I for feasibility).**

Introduce slack variables s₁, s₂, s₃:

```
┌─────────────────────────────────────────────┐
│  x + y + s₁         = 100                   │
│ −x     + s₂         = −10                   │
│     −y + s₃         = −20                   │
│                                             │
│  Pivot 1: s₂ exits, x enters (row 2)        │
│  Pivot 2: s₃ exits, y enters (row 3)        │
│                                             │
│  Result: x = 10, y = 20, s₁ = 70            │
│  Feasible. Witness: (10, 20).               │
└─────────────────────────────────────────────┘
```

**Total:** ~2-3 pivots, microseconds for this size.  But the result is an
opaque point `(10, 20)` -- not a composable predicate.

### 8.3 The SFA Path

**Step 1: Normalize to `Σ aᵢ · xᵢ ≤ b` form.**

```
  C₁:  x + y ≤ 100   →  coeffs = [1, 1],  bound = 100
  C₂:  x ≥ 10        →  coeffs = [−1, 0], bound = −10     (−x ≤ −10)
  C₃:  y ≥ 20        →  coeffs = [0, −1], bound = −20     (−y ≤ −20)
```

**Step 2: Build NFA₁ for C₁ (`x + y ≤ 100`).**

Alphabet: {0, 1}² = {(0,0), (0,1), (1,0), (1,1)}.  Bit sums:

```
  bit_sum(0,0) = 0·1 + 0·1 = 0
  bit_sum(0,1) = 0·1 + 1·1 = 1
  bit_sum(1,0) = 1·1 + 0·1 = 1
  bit_sum(1,1) = 1·1 + 1·1 = 2
```

Initial state: (pos=0, rem=100).  The first few transitions:

```
  (0, 100) ──(0,0)──▶ (1, ⌊(100−0)/2⌋) = (1, 50)
  (0, 100) ──(0,1)──▶ (1, ⌊(100−1)/2⌋) = (1, 49)
  (0, 100) ──(1,0)──▶ (1, ⌊(100−1)/2⌋) = (1, 49)
  (0, 100) ──(1,1)──▶ (1, ⌊(100−2)/2⌋) = (1, 49)
```

After `w = 8` bit positions, states with remainder ≥ 0 are accepting.

**Step 3: Build NFA₂ for C₂ (`−x ≤ −10`) and NFA₃ for C₃ (`−y ≤ −20`).**

Same construction, different coefficients and bounds.

**Step 4: Intersect.**

```
  NFA₁₂ ← INTERSECT(NFA₁, NFA₂)
  NFA₁₂₃ ← INTERSECT(NFA₁₂, NFA₃)

  INTERSECT builds a product automaton:
    States:    Q₁₂₃ ⊆ Q₁ × Q₂ × Q₃
    Accept:    (q₁, q₂, q₃) is accepting iff q₁ ∈ F₁ ∧ q₂ ∈ F₂ ∧ q₃ ∈ F₃
    Transition: ((q₁,q₂,q₃), σ, (q₁′,q₂′,q₃′))
                iff q₁──σ──▶q₁′ ∧ q₂──σ──▶q₂′ ∧ q₃──σ──▶q₃′
```

**Step 5: Emptiness check.**

BFS from the initial state of NFA₁₂₃.  If an accepting state is reachable,
the guard is satisfiable.

```
  ┌───────┐    (0,1)     ┌───────┐    (1,0)     ┌───────┐         ╔═══════╗
  │ init  │ ──────────▶  │  ···  │ ──────────▶  │  ···  │  ─ ─ ─▶ ║ accept║
  │(0,100,│              │       │              │       │         ║  r≥0  ║
  │-10,-20)              │       │              │       │         ║  all  ║
  └───────┘              └───────┘              └───────┘         ╚═══════╝
                                                    8 positions
```

BFS finds an accepting state → **SAT**.

**Step 6: Witness extraction.**

Trace the BFS shortest path.  Decode the 2-bit symbols at each position:

```
  Position 0: σ = (0, 0)  →  x bit 0 = 0, y bit 0 = 0
  Position 1: σ = (1, 0)  →  x bit 1 = 1, y bit 1 = 0
  Position 2: σ = (0, 1)  →  x bit 2 = 0, y bit 2 = 1
  Position 3: σ = (1, 0)  →  x bit 3 = 1, y bit 3 = 0
  Positions 4-7: σ = (0, 0)

  x = 0·1 + 1·2 + 0·4 + 1·8 = 10  (binary: 01010000)
  y = 0·1 + 0·2 + 1·4 + 0·8 + 1·16 = 20  (binary: 00101000)
```

Witness: `(x, y) = (10, 20)`.

**Total:** 3 NFA constructions + 2 intersections + 1 BFS.  Microseconds for
`k = 2`, `w = 8`.

### 8.4 Comparison Summary

| Criterion                          | SMT (Z3)                | LP (simplex)               | Automata (Presburger NFA)       |
|------------------------------------|-------------------------|----------------------------|---------------------------------|
| Operations                         | serialize + FFI + parse | matrix setup + 2-3 pivots  | 3 NFA builds + 2 products + BFS |
| External deps                      | z3-sys (~1.5 GB)        | GLPK / COIN-OR             | None (pure Rust)                |
| Result type                        | bool + model (opaque)   | bool + point (opaque)      | NFA (composable predicate)      |
| Negatable?                         | Yes (negate formula)    | No (complement not convex) | Yes (determinize + flip)        |
| Can compose with structural guard? | Nelson-Oppen            | No                         | ProductAlgebra                  |
| Provably decidable?                | Trusted solver          | LP duality theorem         | Büchi 1960 + NFA emptiness      |
| WASM-compatible?                   | No                      | Depends on solver          | Yes                             |

### 8.5 The Composability Test

Now extend the example: suppose the guard also requires a **structural match**
-- the received value must have the form `App(f, Var(x))`, checked by
`UnificationTheory`.  The full guard is:

    (x + y ≤ 100 ∧ x ≥ 10 ∧ y ≥ 20)  ∧  match(value, App(f, Var(x)))

**SMT approach:** Would require **Nelson-Oppen theory combination** between
linear integer arithmetic (LIA) and the theory of uninterpreted constructors.
The theories must have disjoint signatures.  Equality exchange must propagate
any shared variables.  This is feasible but adds significant complexity.

**LP approach:** **Cannot handle structural constraints at all.**  LP solves
numeric systems only.  The structural guard would need a separate oracle, and
the results would need ad-hoc combination logic with no formal guarantees.

**Automata approach:** `ProductAlgebra` composes the two domains trivially:

```
  ProductAlgebra<PresburgerAlgebra, TheoryAlgebra<UnificationTheory>>

  ┌─────────────────────────────────────────────────────────────┐
  │                    ProductAlgebra                           │
  │                                                             │
  │  ┌────────────────────┐    ┌─────────────────────────────┐  │
  │  │ PresburgerAlgebra  │    │ TheoryAlgebra<Unification>  │  │
  │  │                    │    │                             │  │
  │  │ SAT: NFA emptiness │    │ SAT: unification attempt    │  │
  │  │ and: NFA product   │    │ and: constraint conjunction │  │
  │  │ not: NFA complement│    │ not: negation-as-failure    │  │
  │  │                    │    │      via LogicT gnot()      │  │
  │  └────────────────────┘    └─────────────────────────────┘  │
  │                                                             │
  │  SAT(Both(arith, struct)) = SAT_P(arith) ∧ SAT_U(struct)    │
  │  and(p, q) = structural conjunction over ProductPred        │
  │  not(p) = push negation into components                     │
  │                                                             │
  │  Minterm computation works uniformly:                       │
  │  each component answers its own SAT query independently.    │
  └─────────────────────────────────────────────────────────────┘
```

The product predicate `Both(arith_guard, struct_guard)` is satisfiable iff
the arithmetic part is satisfiable (NFA emptiness) **and** the structural part
is satisfiable (unification succeeds).  Both components participate in minterm
computation through the same `BooleanAlgebra` interface.  No theory combination
procedure, no disjoint-signature requirement, no equality exchange.

---

## 9. The Composability Advantage

The worked example in §8.5 illustrates a general principle: the automata
approach is not merely "good enough" for satisfiability -- it is
**structurally superior** for MeTTaIL's use case because of composability.

### 9.1 ProductAlgebra: Independent Domain Composition

`ProductAlgebra<A, B>` takes any two `BooleanAlgebra` implementations and
produces a new `BooleanAlgebra` over the Cartesian product of their domains.
Satisfiability factors per-disjunct:

    SAT(Both(φ_A, φ_B)) = SAT_A(φ_A) ∧ SAT_B(φ_B)

No additional theory is needed.  The product construction is correct by
definition whenever the two domains are independent (no shared variables).

The predicate type `ProductPred<A, B>` supports the full Boolean algebra:

```
  ProductPred<A, B> ::= True
                     |  False
                     |  Both(A::Pred, B::Pred)       ▷ both domains constrained
                     |  LeftOnly(A::Pred)              ▷ only A constrained
                     |  RightOnly(B::Pred)             ▷ only B constrained
                     |  And(ProductPred, ProductPred)   ▷ conjunction
                     |  Or(ProductPred, ProductPred)    ▷ disjunction
                     |  Not(ProductPred)                ▷ complement
```

Every variant composes further -- `And`, `Or`, `Not` of product predicates
are product predicates.  Algebraic closure is preserved at every level.

> **Full specification:** [product-algebra.md](product-algebra.md).

### 9.2 TheoryAlgebra: The Bridge

Not every constraint domain is naturally expressed as a `BooleanAlgebra`.
Some domains -- particularly those involving search (e.g., unification with
multiple possible substitutions) -- are more naturally expressed as a
`ConstraintTheory` with propagation and backtracking.

`TheoryAlgebra<T>` gives every `ConstraintTheory` a reject-safe interface and
lifts only `DecidableConstraintTheory` implementations into a
`BooleanAlgebra`:

```
  ConstraintTheory T             TheoryAlgebra<T>
  ──────────────────             ─────────────────
  propagate(store, c) → Store?   decide_bounded(φ) → Sat3
  is_consistent(store) → bool    witness(φ) → Option<Assignment>
  witness(store) → Assignment?   and/or/pseudo-complement
  label(store) → LogicStream

  DecidableConstraintTheory T    Exact TheoryAlgebra<T>
  ───────────────────────────    ──────────────────────
  decide_exact(φ) → exact result is_satisfiable(φ) → bool
                                  and/or/not; SFA eligible

  The bridge:
  - A checked witness proves SAT.
  - Bounded absence or implementation-stream exhaustion is DontKnow.
  - Classical UNSAT and complement require decide_exact.
```

This means every constraint domain -- Presburger, unification, lattice
subtyping, and future user-defined theories -- participates uniformly in
reject-safe composition. Only domains carrying exact-decision authority
participate in classical SFA operations.

> **Full specification:** [logict-framework.md](logict-framework.md).

### 9.3 Uniform Minterm Participation

The payoff is that all exact algebras -- direct implementations and exactly
bridged theories alike -- participate in minterm-based determinization through
the same interface, while incomplete theories cannot fabricate minterms.

A minterm computation over `ProductAlgebra<PresburgerAlgebra, CharClassAlgebra>`
proceeds as follows:

1. Collect predicates Φ = {φ₁, …, φₙ} from SFA transitions.
2. For each candidate minterm m = ψ₁ ∧ ⋯ ∧ ψₙ:
   - Project m onto the Presburger component: m_P.
   - Project m onto the CharClass component: m_C.
   - SAT(m) = SAT_P(m_P) ∧ SAT_C(m_C).
3. Each component answers its own SAT query independently.

No global theory combination is needed.  The components do not communicate
equalities, exchange constraints, or require compatible signatures.

### 9.4 Contrast with Nelson-Oppen

In SMT, combining theories via Nelson-Oppen requires:

| Requirement           | Nelson-Oppen                                                   | ProductAlgebra                                        |
|-----------------------|----------------------------------------------------------------|-------------------------------------------------------|
| Disjoint signatures   | Required -- theories cannot share symbols                      | Not needed -- domains are independent by construction |
| Stably-infinite       | Required -- every satisfiable formula must have infinite model | Not needed                                            |
| Equality exchange     | The algorithm propagates implied equalities between theories   | None -- components are independent                    |
| Convexity             | Needed for completeness; non-convex theories require splitting | Not needed                                            |
| Implementation effort | Complex protocol between solver modules                        | Trivial product construction                          |

MeTTaIL's `ProductAlgebra` avoids all of these requirements because it
operates over genuinely **independent** domains.  When domains share variables,
the sharing is handled at a higher level (e.g., the pipeline coordinator
partitions constraints by domain before dispatching to the appropriate algebra).

The Nelson-Oppen procedure is a powerful and general tool for combining
theories with shared variables.  MeTTaIL does not need that generality --
guard predicates combine independent domains (numeric constraints + structural
patterns + character classes), and `ProductAlgebra` handles this case with
zero overhead.

---

## 10. Complexity and Trade-offs

An honest comparison must account for where the automata approach pays a cost.

### 10.1 NFA State Space

The Presburger NFA for `Σ aᵢ · xᵢ ≤ b` has a state count bounded by

    |Q| ∈ O((Σ |aᵢ| + |b|) · w)

and an alphabet of `2ᵏ` symbols.  The total transition count is

    |δ| ∈ O(|Q| · 2ᵏ)

The `2ᵏ` factor is exponential in the number of variables `k`.  For `k = 2`,
this is 4 -- negligible.  For `k = 4`, it is 16 -- still manageable.  For
`k = 8`, it is 256 -- potentially expensive for large coefficients.

### 10.2 Complement Blowup

The complement operation requires determinization (subset construction),
which is `O(2^|Q|)` in the worst case.  The NNF optimization (§7.5) avoids
this for most predicates by pushing negation to atoms.  Only universal
quantification `∀v. φ` (compiled as `¬∃v. ¬φ`) triggers complement.

Guard predicates in MeTTaIL rarely contain universal quantification --
they are typically conjunctions and disjunctions of atomic constraints.
When universal quantification does appear, it is usually bounded (`∀ v ∈ S`)
and handled by the LogicT bounded-search mechanism rather than NFA complement.

### 10.3 When LP Would Win

For problems with many variables (`k > 6`), LP simplex would likely outperform
NFA construction in raw satisfiability-decision speed.  The LP relaxation
provides an answer in `O(k²)` pivots on average, regardless of coefficient
size, while the NFA construction scales as `O(w · R · 2ᵏ)` where `R` grows with
the coefficients.

However, the LP result cannot be composed with other predicates in the SFA
pipeline (§5.5).  If MeTTaIL ever needed to handle high-dimensional linear
constraint systems (k > 6), a hybrid approach could be considered: use LP
for standalone satisfiability checks and NFAs for the composable pipeline.
This would sacrifice the algebraic uniformity of the current design.

### 10.4 When SMT Would Win

For problems combining multiple complex theories -- e.g., quantified
bitvector arithmetic with array reasoning and uninterpreted functions --
SMT's theory combination machinery is essential.  Guard predicates are
far simpler: they involve one theory (linear arithmetic) optionally composed
with structural matching.

If MeTTaIL's guard language ever grew to require array reasoning, bitvector
semantics, or other theories natively supported by SMT solvers, delegating
to Z3 for those specific theories might become worthwhile.  The current
guard language does not require this.

### 10.5 The Practical Sweet Spot

| Scenario                          | Best approach                    | Rationale                                      |
|-----------------------------------|----------------------------------|------------------------------------------------|
| 1-4 variable linear arithmetic    | Automata                         | O(w · 2ᵏ) states, composable, proven decidable |
| 5+ variable linear arithmetic     | LP/ILP                           | Polynomial in k, but not composable            |
| Mixed arithmetic + structural     | Automata                         | ProductAlgebra handles composition uniformly   |
| Quantified multi-theory reasoning | SMT                              | Nelson-Oppen theory combination required       |
| WASM deployment target            | Automata                         | Pure Rust, no FFI, no external dependencies    |
| Real-valued arithmetic            | LP                               | Automata require integer encoding              |
| Polynomial (nonlinear) arithmetic | SMT                              | Presburger is limited to linear constraints    |
| Semantic closure (eq, rw, cong)   | Datalog (Ascent)                 | Least-fixpoint inference, semi-naive eval      |
| Runtime behavioral guard eval     | Datalog (Ascent)                 | O(1) hash-indexed fixpoint lookup              |
| Graph / reachability predicates   | Heyting + Ascent (proposed, §11) | Pseudo-complement models non-Boolean topology  |

Guard predicates occupy the first, third, and fifth rows — exactly where
automata excel.  Runtime semantic closure occupies the last two rows —
exactly where Ascent excels.  The two are complementary (§6.5).

---

## 11. Research Direction: Heyting Algebra Extensions

The `BooleanAlgebra` trait (§3) requires involutive complement: `¬¬φ = φ`.
This excludes predicate domains where complement is inherently
non-involutive — notably graph reachability, topological closure, and
constructive properties.  **Heyting algebras** relax this requirement:
`¬¬φ ≥ φ` (double negation is a closure operator, not identity), opening a
path to extending predicated types into these domains.

The key insight: the double-negation closure `¬¬φ` is the **best Boolean
approximation** of a Heyting predicate `φ` — the smallest regular element
containing `⟦φ⟧`.  A `BooleanApproximation<H>` bridge lifts any
`HeytingAlgebra` to a conservative `BooleanAlgebra`, enabling sound (but
potentially incomplete) compile-time analysis: `SAT(¬¬φ) = false ⟹
SAT(φ) = false`.

> **Full treatment:** The dedicated companion document
> [Heyting Algebra Extensions](heyting-algebra-extensions.md) provides:
> formal foundations and the algebraic hierarchy (§1), double-negation closure
> proofs (§2), Stone/Esakia topological duality (§3), three graph analysis
> examples — reachability, bisimulation, channel connectivity (§4),
> Curry-Howard connection to intuitionistic type theory (§5), five concrete
> use cases that Boolean algebras cannot express (§6), the formal soundness
> proof for `BooleanApproximation` (§7), lattice automata connection (§8),
> and a Rust implementation architecture sketch (§9).

## 12. Summary and Decision Rationale

### 12.1 Extended Comparison

| Criterion           | SMT (Z3/CVC5)              | LP/ILP (Simplex)           | Datalog (Ascent)                | Automata (Presburger NFA)       |
|---------------------|----------------------------|----------------------------|---------------------------------|---------------------------------|
| **External deps**   | z3-sys (~1.5 GB), C++ FFI  | GLPK / COIN-OR, C library  | None — already in pipeline      | Zero — pure Rust                |
| **Deployment**      | Platform-specific lib      | Platform-specific          | Cross-platform                  | Cross-platform, WASM-compatible |
| **Performance**     | ~1 ms FFI + solve          | Microseconds (simplex)     | Fixpoint: ms–s; lookup: O(1)    | Microseconds (NFA + BFS)        |
| **Formal basis**    | Solver completeness (opaque) | LP duality theorem       | Knaster-Tarski least fixpoint   | Büchi 1960 (provably decidable) |
| **Integration**     | SMT-LIB2 serialize / parse | Matrix setup / read        | Native Rust (proc-macro)        | Direct `BooleanAlgebra` impl    |
| **Composability**   | Nelson-Oppen (complex)     | None (opaque oracle)       | JOIN only (no ∨, no ¬)          | `ProductAlgebra` (trivial)      |
| **Negation**        | Yes (negate formula)       | No (complement not convex) | NAF only (point query)          | Yes (NFA complement)            |
| **Minterm support** | No (opaque oracle)         | No (requires negation)     | No (requires classical ¬)       | Yes (native)                    |
| **Infinite domains**| Yes                        | Yes (continuous)           | No (finite active domain)       | Yes (symbolic predicates)       |
| **Scope match**     | Over-powered               | Under-powered              | Different task (inference)      | Exact fit (decision)            |
| **Extensibility**   | Fixed theory set, FFI      | Fixed                      | User-defined Ascent rules       | Open `ConstraintTheory` trait   |

### 12.2 The Decision

Guard predicates occupy a sweet spot -- low-dimensional linear arithmetic
over integers, composed with structural and character-class constraints --
where NFA-based decision procedures are:

- **Competitive in performance:** microseconds for `k ≤ 4`, `w = 16`.
- **Provably correct:** Büchi's 1960 theorem + NFA emptiness decidability,
  with cross-validation between dual implementation paths.
- **Zero-dependency:** pure Rust, no C++ FFI, no external libraries.
- **WASM-compatible:** runs identically in browser and native targets.
- **Uniquely composable:** the only approach that produces first-class
  predicates participating in minterm computation, SFA intersection, and
  `ProductAlgebra` composition.

The last point is decisive.  SAT/SMT solvers and LP/ILP solvers can answer
"is this satisfiable?" but cannot produce a **composable predicate** that
participates in the symbolic automata pipeline.  Datalog (Ascent) answers a
fundamentally different question — "what is derivable?" — and lacks classical
complement, infinite-domain support, and `BooleanAlgebra` composability.
The automata approach is the only one that produces first-class composable
predicates for compile-time guard analysis.  Ascent complements it at runtime,
handling semantic closure and behavioral guard evaluation (§6.5).  §11
identifies one area where the Boolean requirement may be relaxable —
Heyting algebras for graph-structural predicates — as a research direction
that would extend the framework's applicability while preserving sound
compile-time analysis via the double-negation approximation bridge.

---

## 13. References

1. Bancilhon, F. (1986). ["Naive evaluation of recursively defined
   relations."](https://doi.org/10.1007/978-1-4612-4980-1_17) In *On Knowledge Base Management Systems*, pp. 165-178.
   Springer. DOI: [10.1007/978-1-4612-4980-1_17](https://doi.org/10.1007/978-1-4612-4980-1_17).

2. Bartzis, C. & Bultan, T. (2003). ["Efficient symbolic representations for
   arithmetic constraints in verification."](https://doi.org/10.1142/S0129054103001911) *International Journal of Foundations
   of Computer Science*, 14(4):605-624.
   DOI: [10.1142/S0129054103001911](https://doi.org/10.1142/S0129054103001911).

3. Büchi, J. R. (1960). ["Weak second-order arithmetic and finite automata."](https://deepblue.lib.umich.edu/handle/2027.42/3930)
   *Zeitschrift für mathematische Logik und Grundlagen der Mathematik*,
   6:66-92. DOI: [10.1002/malq.19600060105](https://doi.org/10.1002/malq.19600060105).

4. Ceri, S., Gottlob, G. & Tanca, L. (1990). [*Logic Programming and
   Databases*](https://doi.org/10.1007/978-3-642-83952-8). Springer.
   DOI: [10.1007/978-3-642-83952-8](https://doi.org/10.1007/978-3-642-83952-8).

5. D'Antoni, L. & Veanes, M. (2014). ["Minimization of symbolic automata."](https://cseweb.ucsd.edu/~ldantoni/papers/popl14.pdf)
   *Proceedings of POPL*, pp. 541-553. ACM.
   DOI: [10.1145/2535838.2535849](https://doi.org/10.1145/2535838.2535849).

6. D'Antoni, L. & Veanes, M. (2017). ["The power of symbolic automata and
   transducers."](https://doi.org/10.1007/978-3-319-63387-9_3) *CAV 2017*, LNCS 10427, pp. 47-67. Springer.
   DOI: [10.1007/978-3-319-63387-9_3](https://doi.org/10.1007/978-3-319-63387-9_3).

7. Dantzig, G. B. (1963). [*Linear Programming and Extensions*](https://doi.org/10.7249/R366).
   Princeton University Press. (RAND Corporation edition:
   DOI: [10.7249/R366](https://doi.org/10.7249/R366).)

8. de Moura, L. & Bjørner, N. (2008). ["Z3: An efficient SMT solver."](https://doi.org/10.1007/978-3-540-78800-3_24)
   *TACAS 2008*, LNCS 4963, pp. 337-340. Springer.

9. Esakia, L. (2019). [*Heyting Algebras: Duality Theory*](https://doi.org/10.1007/978-3-030-12096-2).
   Springer, Trends in Logic, vol. 50.
   DOI: [10.1007/978-3-030-12096-2](https://doi.org/10.1007/978-3-030-12096-2).

10. Johnstone, P. T. (1982). *Stone Spaces*. Cambridge University Press.
    ISBN: 0-521-23893-5.

11. Karp, R. M. (1972). ["Reducibility among combinatorial problems."](https://doi.org/10.1007/978-1-4684-2001-2_9)
    In *Complexity of Computer Computations*, pp. 85-103. Plenum Press.

12. Kiselyov, O., Shan, C., Friedman, D. P. & Sabry, A. (2005).
    ["Backtracking, interleaving, and terminating monad transformers."](https://okmij.org/ftp/Computation/LogicT.pdf)
    *Proceedings of ICFP*, pp. 192-203. ACM.
    DOI: [10.1145/1086365.1086390](https://doi.org/10.1145/1086365.1086390).

13. Le Gall, T. & Jeannet, B. (2007). ["Lattice automata: A representation
    for languages on infinite alphabets, and some applications to
    verification."](https://doi.org/10.1007/978-3-540-74061-2_4) *SAS 2007*, LNCS 4634, pp. 52-68. Springer.
    DOI: [10.1007/978-3-540-74061-2_4](https://doi.org/10.1007/978-3-540-74061-2_4).

14. Lenstra, H. W. (1983). ["Integer programming with a fixed number of
    variables."](https://doi.org/10.1287/moor.8.4.538) *Mathematics of Operations Research*, 8(4):538-548.

15. Nelson, G. & Oppen, D. C. (1979). ["Simplification by cooperating
    decision procedures."](https://doi.org/10.1145/357073.357079) *ACM Transactions on Programming Languages and
    Systems*, 1(2):245-257. DOI: [10.1145/357073.357079](https://doi.org/10.1145/357073.357079).

16. Schrijver, A. (1986). *Theory of Linear and Integer Programming*.
    John Wiley & Sons. ISBN: 0-471-98232-6.

17. Veanes, M. (2013). ["Applications of symbolic finite automata."](https://doi.org/10.1007/978-3-642-39274-0_3)
    *CIAA 2013*, LNCS 7982, pp. 16-23. Springer.
    DOI: [10.1007/978-3-642-39274-0_3](https://doi.org/10.1007/978-3-642-39274-0_3).

18. Veanes, M., Hooimeijer, P., Livshits, B., Molnar, D. & Bjørner, N.
    (2012). ["Symbolic finite state transducers: Algorithms and
    applications."](https://doi.org/10.1145/2103621.2103674) *Proceedings of POPL*, pp. 137-150. ACM.
    DOI: [10.1145/2103621.2103674](https://doi.org/10.1145/2103621.2103674).

19. Wolper, P. & Boigelot, B. (1995). ["An automata-theoretic approach to
    Presburger arithmetic constraints."](https://doi.org/10.1007/3-540-60360-3_30) *SAS 1995*, LNCS 983, pp. 21-32.
    Springer. DOI: [10.1007/3-540-60360-3_30](https://doi.org/10.1007/3-540-60360-3_30).
