# Predicated Types: Guarded Communication in MeTTaIL

---

## Part I: Motivation and Core Design

---

## 1. Introduction and Motivation

The rho-calculus Comm rule fires unconditionally. Any process sent on a channel
is accepted without question.

The standard Comm rule captures the fundamental communication primitive of the
rho-calculus: when a send `n!(q)` and a receive `(n?x).{c}` coexist on the same
channel `n`, the sent process `q` is quoted into a Name `@(q)` and substituted
for the bound variable `x` in the continuation `c`. This is a single-step
reduction in the CHAM (Chemical Abstract Machine; Berry & Boudol, 1992)
semantics — the two processes are consumed and replaced by the substituted
continuation. The rule is unconditional: no inspection of `q` occurs before the
substitution.

```
{ n!(q) | (n?x).{c} } ⟶ c[@(q)/x]
```

The notation `@(q)` denotes the quote operator (Name constructor `NQuote`),
and `c[v/x]` denotes capture-avoiding substitution of `v` for `x` in `c`.
The substitution crosses category boundaries: `x` may appear as both an `NVar`
and (via unquoting) as a `PVar` in `c`. This unconditional firing is what
predicated types aim to extend — §2 introduces the guard `φ` that conditions
this reduction.

**Predicated types** extend this picture. They condition communication on
**guard predicates** — structural and behavioral constraints that the received
value must satisfy before the Comm rule fires.

The guarded Comm rule adds a pattern `φ` between the channel and the
continuation. Where the standard rule accepts any value blindly, the guarded
variant interposes a first-order matching step (Baader & Snyder, 2001): the
received Name `@(q)` is matched against the guard pattern `φ`, and
communication proceeds only if matching succeeds. The rationale is to bring
type-like discrimination into the process algebra without departing from the
reflective "terms as patterns" discipline — the guard IS a term, not a
separate type annotation. This design preserves the rho-calculus property
that Names and Procs share a single syntactic universe. The matching
function `match(φ, @(q))` returns `(σ | ⊥)`: `σ` on success, where
`σ` maps the guard's free variables to sub-terms of `@(q)`, or `None` on
failure.

```
{ n!(q) | (n ? φ).{c} } ⟶ c[σ]    iff match(φ, @(q)) = σ
```

The guard `φ` is a Name expression with free variables, and `σ` is a
substitution (partial function from variables to terms) partitioned by natural
category — Name bindings for `NVar` positions, Proc bindings for `PVar`
positions (see §3 "Natural Categories"). When matching fails, the Comm rule
does not fire and the processes remain waiting, preserving the standard
blocking semantics. The match function's O(|φ|) complexity (§5) ensures that
the guard check adds only linear overhead proportional to the pattern size.

### Three Motivating Examples

These examples illustrate progressively more powerful guards, building from
pure structural matching to relational properties to first-order logic. Each
example introduces a new layer of expressiveness — structural decomposition,
relational join, and quantified reasoning — that maps to a distinct evaluation
mechanism in the pipeline (§12). Together, they demonstrate the full spectrum
of guard predicates that predicated types support.

**Example 1 — Structural guard.** The simplest guard form performs pure
pattern matching on the received value's term structure. The intuition is
that the guard acts as a shape filter: only values with a specific constructor
layout pass through. This corresponds to first-order matching (§3) — the
guard pattern contains free variables that bind to sub-terms of the concrete
value. The theoretical basis is the standard variable rule of first-order
matching: a free variable in the pattern matches any ground sub-term at the
corresponding position. No relational or logical reasoning is involved — just
structural decomposition.

```rholang
for (@{x!(y)} <- ch) { P }
```

The guard `@{x!(y)}` = `@(x!(y))` is a Name pattern parsed as
`NQuote(POutput(NVar(x), PVar(y)))`. The receive fires only when the value
sent on `ch` has the shape `channel!(body)`. The variables `x` and `y` bind
the channel and body sub-terms at their natural categories (`x : Name`,
`y : Proc`). The matching cost is O(|guard|) — constant for this two-variable
pattern (§5). This is a T1 or T2 guard depending on whether the pattern is
fully ground-decidable at compile time (§11).

**Example 2 — Behavioral guard.** Beyond structural shape, many communication
protocols need to condition acceptance on relational properties of the received
value — properties that emerge from the Ascent fixpoint computation rather than
the value's syntactic structure alone. The rationale for separating structural
and behavioral guards is compositionality: the structural match extracts
bindings (σ), and the behavioral predicates then query Ascent relations using
those bindings. This two-phase design (match then check) maps naturally to the
Ascent Datalog rule structure (Ceri, Gottlob & Tanca, 1990), where structural
destructuring produces `let` bindings and behavioral predicates become JOIN
clauses against declared relations (§8).

```rholang
for (@{x!(y)} <- ch) where path(y, {}) { P }
```

After structural matching succeeds (binding `x` and `y`), the `where` clause
predicate `path(y, {})` checks whether the tuple `(body, PZero)` exists in
the `path` relation of the current Ascent fixed-point. Communication fires
only if both the structural match AND all `where`-clause predicates succeed.
The runtime cost is O(1) per relation lookup (hash-indexed Ascent relation,
§8) plus the O(|guard|) structural matching cost.

**Example 3 — Quantified guard.** The most expressive guard form uses
first-order quantification to express properties that range over all (or some)
terms in a domain. The intuition is that structural matching asks "does this
value have the right shape?" and behavioral predicates ask "does this specific
tuple exist in a relation?" but quantified guards ask "does a universal or
existential property hold across an entire set of related terms?" This requires
either LogicT fair backtracking evaluation (current implementation, §8
"Quantified Behavioral Predicates") or alternating weighted automata (future
Alternating Weighted Automata (AWA) path, §16). The theoretical basis is the
automaton-theoretic characterization of first-order logic: universal quantifiers
correspond to AWA Q⊗ (tensor/conjunction) states, existential quantifiers to Q⊕
(direct-sum/disjunction) states (Droste & Gastin, 2007).

```rholang
for (@x <- ch) where forall(y, nodes, entails(reachable(x, y), safe(y))) { P }
```

This demands that for EVERY term `y` reachable from the received value `x`,
the `safe` relation holds. This is a first-order universally quantified
predicate. The `forall(y, nodes, ...)` sugar desugars to a negated
existential: the compiler searches for a counterexample `y` where
`reachable(x, y), not(safe(y))`, and the guard succeeds only if no such
counterexample exists. The guard is classified as T3 (bounded checking) or T4
(undecidable) depending on whether the reachability domain is bounded (§11).

### Language-Generic Framing

Predicated types are not specific to Rholang. Any language defined with the
MeTTaIL `language!` macro that declares a guarded receive constructor
(`PGuardedInput`) and a `logic {}` block with relations gets the full
predicated types pipeline automatically. The pipeline is parametric in the
term algebra, the guard predicate language, and the constraint theories
available. Any `language!` with a `guards { theories {} }` block (§2A) gets
theory-driven predicate dispatch, replacing the heuristic keyword lists in
[`predicate_dispatch.rs`](../../prattail/src/predicate_dispatch.rs) with explicit, data-driven routing. Languages with
`guards { channels {} }` (§2A) get deterministic M8/M11 dispatch for
multi-channel guards, replacing heuristic channel inference.

### Document Overview

This document covers the end-to-end predicated types system across
twenty-six sections in three parts:

- **Part I** (§§1–2A, 3–7A, 8–10): Core design — from surface syntax
  through the language-generic guard configuration block (§2A), structural
  matching, behavioral predicates (including quantified predicates and
  AC-matching), the guarded Comm rule, architectural overview of the five
  key subsystems (§7A), and correctness analysis. A reader can stop after
  §10 and understand single-channel guards.
- **Part II** (§§11–14A, 15–18): Formal framework — decidability tiering,
  the five-stage pipeline, guard compilation strategies, compile-time/
  runtime boundary, theory-guided LogicT evaluation (§14A), the
  BooleanAlgebra algebraic foundation, constraint theories (including
  pipeline flow, dispatch gating, and extension mechanism), and automata
  modules (including symbolic finite transducers and e-graph equality
  saturation).
- **Part III** (§§19–25): Architecture and implementation — lint
  integration, pluggable type system framework (refinement types,
  set-theoretic types, Hindley-Milner), implementation architecture,
  verification, risks, and references.

### Notation and Conventions

The following tables define mathematical symbols, metavariables, and acronyms
used throughout this document. They serve as a quick reference — each item is
also explained in context at its point of introduction.

**Greek letter metavariables:**

| Symbol   | Name     | Meaning                                            |
|----------|----------|----------------------------------------------------|
| `Γ`      | Gamma    | Type environment (mapping from variables to types) |
| `δ`      | delta    | Transition function of an automaton                |
| `θ`      | theta    | Substitution (in unification/composition contexts) |
| `μX`     | mu       | Least fixpoint operator (mu-calculus)              |
| `νX`     | nu       | Greatest fixpoint operator (mu-calculus)           |
| `σ`      | sigma    | Substitution: partial function `Var → Term`        |
| `τ`      | tau      | Monotype (unquantified type expression)            |
| `φ`, `ψ` | phi, psi | Guard formulas / logical predicates                |

**Logical connectives and constants:**

| Symbol | ASCII        | Meaning                                      |
|--------|--------------|----------------------------------------------|
| `∧`    | `and`        | Logical conjunction                          |
| `∨`    | `or`         | Logical disjunction                          |
| `¬`    | `not`        | Logical negation                             |
| `⊤`    |              | Top: universally satisfied predicate / truth |
| `⊥`    |              | Bottom: unsatisfiable predicate / falsity    |
| `⟹`    | `entails`    | Material implication (`φ ⟹ ψ` ≡ `¬φ ∨ ψ`)    |
| `⟸`    | `implied_by` | Reverse implication                          |
| `⟺`    | `iff`        | Biconditional                                |
| `≡`    |              | Definitional / logical equivalence           |

**Modal and fixpoint operators:**

| Symbol  | Meaning                                                           |
|---------|-------------------------------------------------------------------|
| `□`     | Box modality: "for all successors" (universal, mu-calculus)       |
| `◇`     | Diamond modality: "exists a successor" (existential, mu-calculus) |
| `μX. φ` | Least fixpoint of `φ` w.r.t. variable `X`                         |
| `νX. φ` | Greatest fixpoint of `φ` w.r.t. variable `X`                      |

**Algebraic and lattice operators:**

| Symbol | Meaning                                                       |
|--------|---------------------------------------------------------------|
| `⊗`    | Tensor product / semiring multiplication / conjunction in AWA |
| `⊕`    | Direct sum / semiring addition / disjunction in AWA           |
| `⊔`    | Join: least upper bound (LUB) in a lattice                    |
| `⊓`    | Meet: greatest lower bound (GLB) in a lattice                 |

**Set notation:**

| Symbol | Meaning          |
|--------|------------------|
| `∈`    | Set membership   |
| `∉`    | Not a member of  |
| `∪`    | Set union        |
| `∩`    | Set intersection |
| `⊆`    | Subset or equal  |
| `∖`    | Set difference   |

**Relations and closures:**

| Symbol | Meaning                                                                 |
|--------|-------------------------------------------------------------------------|
| `→*`   | Reflexive-transitive closure of the one-step rewrite/reduction relation |
| `↾`    | Restriction: `φ↾k` bounds all quantifiers in `φ` to depth `k`           |

**Domain-specific notation:**

| Notation | Meaning                                                                   |
|----------|---------------------------------------------------------------------------|
| `@(q)`   | Quote operator: wraps process `q` into a Name (`NQuote` constructor)      |
| `c[v/x]` | Capture-avoiding substitution of `v` for `x` in continuation `c`          |
| `⟦φ⟧`    | Interpretation function: maps formula `φ` to its automaton representation |
| `L(A)`   | The language (set of accepted words/trees) recognized by automaton `A`    |
| `FP`     | Current Ascent fixed-point state (the set of all derived relation tuples) |

**Automaton components:**

| Symbol | Meaning                                    |
|--------|--------------------------------------------|
| `Q`    | Set of states                              |
| `q₀`   | Initial state                              |
| `F`    | Set of accepting (final) states            |
| `δ`    | Transition function/relation               |
| `Q⊗`   | Universal (conjunction) states in an AWA   |
| `Q⊕`   | Existential (disjunction) states in an AWA |

**Acronyms:**

| Acronym | Expansion                                    |
|---------|----------------------------------------------|
| AWA     | Alternating Weighted Automata                |
| CEGAR   | Counterexample-Guided Abstraction Refinement |
| CHAM    | Chemical Abstract Machine                    |
| DFA     | Deterministic Finite Automaton               |
| DNF     | Disjunctive Normal Form                      |
| EBNF    | Extended Backus-Naur Form                    |
| EWPDS   | Extended Weighted Pushdown System            |
| FOL     | First-Order Logic                            |
| HM      | Hindley-Milner (type inference)              |
| KAT     | Kleene Algebra with Tests                    |
| MGU     | Most General Unifier                         |
| MSO     | Monadic Second-Order (logic)                 |
| NFA     | Nondeterministic Finite Automaton            |
| PATA    | Parity Alternating Tree Automaton            |
| RD      | Recursive Descent (parsing)                  |
| SFA     | Symbolic Finite Automaton                    |
| SFT     | Symbolic Finite Transducer                   |
| SMT     | Satisfiability Modulo Theories               |
| TLS     | Thread-Local Storage                         |
| TRS     | Term Rewriting System                        |
| VPA     | Visibly Pushdown Automaton                   |
| WFST    | Weighted Finite-State Transducer             |
| WPDS    | Weighted Pushdown System                     |

### Formal Definitions

The following two equations formalize the guarded Comm rule, first for
structural-only guards and then for the full structural + behavioral form.
The notation follows standard operational semantics conventions: `σ` denotes
a substitution (partial function `Var → Term`), `φ` denotes the guard
pattern (a term with free variables), and `match` is the first-order matching
function defined formally in §5. The key insight is that the guard extends
the standard Comm rule with a **conditional gate**: communication fires only
when the matching function returns `Some(σ)`, converting an unconditional
reduction to a pattern-conditional one.

The **guarded Comm rule** for structural guards encodes the core matching
contract. The `match` function takes a pattern and a ground term and returns
either a substitution binding the pattern's free variables or failure:

```
{ n!(q) | (n ? φ).{c} } ⟶ c[σ]
  where σ = match(φ, @(q))
        match : (T_pattern, T_ground) → (σ | ⊥)
        σ : Var → Term
```

The type signature `match : (T_pattern, T_ground) → (σ | ⊥)` makes explicit
that this is first-order matching, not unification — only the pattern may
contain free variables. This distinction is formalized in §3 and ensures
O(|pattern|) matching complexity. The rule is sound by construction: §9.1
argues that the generated Datalog clause faithfully encodes this equation.

The **guarded Comm rule** with behavioral predicates extends the structural
form with a conjunction of relational checks against the Ascent fixpoint. The
intuition is that structural matching extracts bindings, and behavioral
predicates then validate those bindings against derived relational knowledge.
The `resolve` function maps predicate arguments (which may reference match
variables by name) to their bound values in `σ`. The conjunction `∀i` requires
ALL predicates to hold — a single failing predicate blocks the Comm rule.

```
{ n!(q) | (n ? φ, R₁(a₁), …, Rₖ(aₖ)).{c} } ⟶ c[σ]
  where σ = match(φ, @(q))
        ∀i ∈ [1,k]. Rᵢ(resolve(aᵢ, σ)) ∈ FP
        FP = current Ascent fixed-point
```

Each `Rᵢ` is a declared Ascent relation, and `FP` is the current fixpoint
state. The lookup `Rᵢ(v) ∈ FP` is an O(1) hash-indexed membership test in
Ascent's internal index (§8). The conjunction is evaluated left-to-right with
short-circuit semantics, and BCG01 selectivity ordering (§13) reorders
conjuncts so the most selective predicate is checked first.

### Process Interaction Diagram

The following diagram visualizes the **rho calculus Comm rule** (Meredith &
Radestock, 2005), extended with the guard and predicate layers introduced by
this design. Read the diagram top-to-bottom as a data-flow: the sender
`n!(q)` and receiver `(n ? φ, preds).{c}` rendezvous on channel `n`, then
the received value passes through two successive gates — structural matching
and behavioral predicate checking — before the continuation fires. The two
rightward exits ("Comm blocked") represent the two failure modes: pattern
mismatch and predicate failure. This layered gate architecture maps directly
to the generated Datalog rule structure in §6, where the `if let Some(...)`
clause implements the structural gate and the JOIN clauses implement the
behavioral gate.

```
n!(q) ─────┐       ┌───── (n ? φ, preds).{c}
           │       │
           ▼       ▼
     ┌───────────────────┐
     │   Channel  n      │
     │                   │
     │   ┌─────────────┐ │
     │   │  Guard  φ   │ │
     │   └──────┬──────┘ │
     │          │        │
     │   match(φ, @(q))  │
     │          │        │
     │   ┌──────▼──────┐ │
     │   │  σ = Some   │ │──── None: Comm blocked
     │   └──────┬──────┘ │
     │          │        │
     │   ┌──────▼──────┐ │
     │   │ ∀R(a)∈preds │ │
     │   │ R(a[σ])∈FP? │ │──── No: Comm blocked
     │   └──────┬──────┘ │
     │          │        │
     │   ┌──────▼──────┐ │
     │   │   c[σ]      │ │
     │   └─────────────┘ │
     └───────────────────┘
```

The key insight is the strict ordering: structural matching ALWAYS executes
first (cheap, O(|φ|)), and behavioral predicates execute only after a
successful match (potentially expensive, involving fixpoint queries). This
ordering is both a correctness requirement (predicates reference match
variables that only exist after successful matching) and a performance
optimization (fail-fast on cheap structural checks before invoking Ascent
relation lookups).

> **Citation:** Meredith, L. G. & Radestock, M. "A Reflective Higher-Order
> Calculus." Electronic Notes in Theoretical Computer Science, 141(5), 2005.

---

## 2. Surface Syntax

### Examples First

The surface syntax uses a `where` keyword to introduce **Datalog queries** —
conjunctions of positive and negative literals compatible with Ascent's
evaluation model. The `where` clause cleanly separates structural binding (the
`@pattern <- channel` form, handled by first-order matching) from behavioral
filtering (the Datalog literals that follow `where`). Each example below
demonstrates a progressively more expressive guard, from pure structural
matching (Layer 1, handled by existing Pratt/Recursive Descent (RD) matching)
through behavioral predicates (Layer 2, Ascent relation joins) to quantified and
bounded predicates (Layers 3-4, LogicT/AWA evaluation). The `@` prefix on
patterns is still required — the compiler does not infer categories.

```rholang
// 1. Structural pattern only (no where) — unchanged
for (@{x!(y)} <- ch) { P }

// 2. Structural + behavioral guard (where OUTSIDE parens)
for (@(x /\ a!(b)) <- n) where path(b, {}), not(path(x, {})) { P }

// 3. Simple behavioral guard (no structural decomposition)
for (@x <- ch) where halts(x), primes(x) { P }

// 4. Structural + combined predicates
for (@{x!(y)} <- ch) where finite(x), ground(y) { P }

// 5. Repeated bind with where
for (@x <= ch) where valid(x) { P }

// 6. Peek bind with where
for (@x <<- ch) where test(x) { P }
```

Examples 1-4 are single-channel guards with increasing predicate complexity.
Example 2 introduces the conjunction of a structural pattern (`x /\ a!(b)`)
with a `where` clause containing both positive and negated Datalog literals.
Examples 5-6 show that `where` extends to all bind operators (`<=` for
repeated, `<<-` for peek).

#### Multi-Channel Receives

Both per-bind and trailing (global) `where` clauses are valid. Per-bind
`where` sits inside the closing `)` scoped to that bind's variables; global
`where` sits outside, seeing all bound variables:

```rholang
// Per-bind where (INSIDE parens — scoped to that bind's variables)
for (@x <- ch1, where pred1(x); @y <- ch2, where related(x, y)) { P }

// Global where (OUTSIDE parens — sees all bound variables)
for (@x <- ch1; @y <- ch2) where pred1(x), related(x, y) { P }

// Mixed — per-bind inside + global outside
for (@x <- ch1, where pred1(x); @y <- ch2) where pred2(x, y) { P }
```

#### Contracts

The `where` clause appears after the closing paren, before `=`:

```rholang
// After closing paren, before =
contract handler(@{msg!(payload)}, ret) where valid(payload) = { body }

// Without structural guard
contract processor(@x) where authorized(x) = { body }

// No where (structural only) — unchanged
contract echo(@x, ret) = { ret!(x) }
```

#### Select Branches

```rholang
select {
  case @x <- ch1 where pred(x) => { ... }
  case @y <- ch2 where other(y) => { ... }
}
```

### Where-Clause Sublanguage Grammar

The `where` clause introduces a conjunction of Datalog literals — positive and
negative relation applications, infix comparisons, and syntactic sugar for
logical connectives, implications, and quantifiers. The design rationale for
this particular fragment is decidability: every literal maps to a
`WeightedMsoFormula` AST variant (§12, M10) that has a well-defined
automaton-theoretic compilation target. Comma-separated literals map to
conjunction (Symbolic Finite Automaton (SFA) intersection); `not()` maps to SFA
complement; `or()` sugar desugars to auxiliary union relations with multiple
Ascent rules; quantifiers desugar to auxiliary relations with
negation-as-failure. The grammar is deliberately first-order — no second-order
set quantification `∀X` — to stay within the Monadic Second-Order logic (MSO)
decidability boundary for tree structures.

```
┌────────────────────────────────────────────────────────────────────────┐
│                    Where-Clause Sublanguage EBNF                       │
├────────────────────────────────────────────────────────────────────────┤
│                                                                        │
│ where_clause ::= 'where' literal (',' literal)*                        │
│                                                                        │
│ literal  ::= pos_lit                            positive literal       │
│            | NOT '(' pos_lit ')'                stratified negation    │
│            | AND '(' literal (',' literal)+ ')' conjunction sugar      │
│            | OR '(' literal (',' literal)+ ')'  disjunction sugar      │
│                                                                        │
│ pos_lit  ::= ident '(' args ')'                 relation application   │
│            | var IN ident                       set membership sugar   │
│            | term cmp term                      infix comparison       │
│            | term REWRITE term                  rewrite closure        │
│            | ENTAILS '(' literal ',' literal ')' forward impl sugar    │
│            | IMPLIED_BY '(' literal ',' literal ')' reverse impl sugar │
│            | IFF '(' literal ',' literal ')'     biconditional sugar   │
│            | FORALL '(' var [',' dom_or_bound] ','                     │
│              literal ')'                        universal sugar        │
│            | EXISTS '(' var [',' dom_or_bound] ','                     │
│              literal ')'                        existential sugar      │
│                                                                        │
│ args     ::= arg (',' arg)*                                            │
│ arg      ::= var | process_term | number | string                      │
│                                                                        │
│ dom_or_bound ::= ident                          named finite domain    │
│                | '{' arg (',' arg)* '}'         enumerated domain      │
│                | N                              depth bound (integer)  │
│                                                                        │
│ cmp      ::= '>' | '<' | GE | LE | '==' | NE                           │
│ var      ::= LOWER_IDENT                        variable reference     │
│                                                                        │
│ ── Unicode/ASCII alternates ────────────────────────────────────────── │
│ IN       ::= 'in' | '∈' | ':'                                          │
│ NOT      ::= 'not' | '¬'                                               │
│ AND      ::= 'and' | '∧'                                               │
│ OR       ::= 'or' | '∨'                                                │
│ ENTAILS  ::= 'entails' | 'implies' | '⟹'                               │
│ IMPLIED_BY ::= 'implied_by' | '⟸'                                      │
│ IFF      ::= 'iff' | '⟺'                                               │
│ FORALL   ::= 'forall' | '∀'                                            │
│ EXISTS   ::= 'exists' | '∃'                                            │
│ GE       ::= '>=' | '≥'                                                │
│ LE       ::= '<=' | '≤'                                                │
│ NE       ::= '!=' | '≠'                                                │
│ REWRITE  ::= '->*' | '→*'                                              │
│                                                                        │
└────────────────────────────────────────────────────────────────────────┘
```

Note: Pattern-level Unicode (`∧` for `/\`, `∨` for `\/`, `¬` for `~`) is
handled by the structural pattern grammar (already supported by Rholang),
not the `where`-clause grammar.

`x in T` / `x ∈ T` / `x : T` is set membership sugar — `x ∈ PosInt` desugars
to `PosInt(x)`. This provides a natural type-membership reading for refinement
types (§19) and named predicate sets. The colon form mirrors type annotation
syntax for familiarity.

`->*` / `→*` denotes the reflexive-transitive closure of the one-step rewrite
relation; `rewrites_to(x, y)` is the function-call synonym.
`ac_match(bag, pat)` tests associative-commutative matching of `bag` against
multiset pattern `pat` (see §Gap 4 and [logict.rs](../../prattail/src/logict.rs)).
`count_ge(ch, k)` / `count_eq(ch, k)` test cardinality of a collection
against a numeric bound. `dom_or_bound` optionally restricts quantifier
variables to a named domain, enumeration, or explicit depth bound (integer).

Each literal maps to a `WeightedMsoFormula` abstract syntax tree (AST) variant
in [`weighted_mso.rs`](../../prattail/src/weighted_mso.rs). The comma conjunction, `not()`, `forall()`, `exists()`
forms align with the weighted MSO specification language (M10), enabling
direct automaton compilation via `to_weighted_automaton()`.

### Built-in Predicates

```rholang
// Equality / disequality (function or infix)
where eq(x, y)       // or: x == y
where neq(x, y)      // or: x != y

// Comparisons (function or infix)
where gt(x, 5)       // or: x > 5
where le(x, y)       // or: x <= y

// Rewrite closure
where rewrites_to(x, y)    // x ->* y

// Freshness
where fresh(x)

// AC-matching
where ac_match(bag, pattern)

// Cardinality
where count_ge(ch, k)       // count(ch) >= k
where count_eq(ch, k)       // count(ch) == k
```

### Syntactic Sugar — Logical Connectives (and, or)

The `where` clause uses comma for conjunction by default, but explicit `and()`
and `or()` sugar enables nested logical structure:

```rholang
// Explicit conjunction (equivalent to comma):
for (@x <- ch) where and(path(x, {}), safe(x)) { P }
// Same as: where path(x, {}), safe(x)

// Disjunction (desugars to auxiliary union relation):
for (@x <- ch) where or(fast(x), cached(x)) { P }
// Compiler generates:
//   fast_or_cached(X) :- fast(X).
//   fast_or_cached(X) :- cached(X).
// Desugars to: where fast_or_cached(x)
```

**De Morgan normalization** — the compiler normalizes nested `not(and(...))`
and `not(or(...))` via De Morgan's Laws before Datalog compilation:

| Sugar               | De Morgan Normal Form        |
|---------------------|------------------------------|
| `not(and(A, B))`    | `or(not(A), not(B))`         |
| `not(or(A, B))`     | `not(A), not(B)`             |
| `not(not(A))`       | `A` (double negation elim.)  |
| `not(and(A, B, C))` | `or(not(A), not(B), not(C))` |
| `not(or(A, B, C))`  | `not(A), not(B), not(C)`     |

These apply recursively. Variadic forms `and(A, B, C, ...)` and
`or(A, B, C, ...)` accept 2+ arguments. `and(A, B, C)` ≡ `A, B, C`.
`or(A, B, C)` generates one Ascent rule per disjunct.

**DNF normalization** — After De Morgan normalization, the compiler converts
the formula to **Disjunctive Normal Form** (DNF): a disjunction of
conjunctions. Each conjunctive clause maps directly to one Ascent rule body,
and the disjunction is the union of multiple rules with the same head:

```
// Pipeline: Source → De Morgan → DNF → Ascent rules

// Source:
where and(or(A, B), or(C, D))

// DNF expansion (4 Ascent rules):
//   guard(X) :- A(X), C(X).
//   guard(X) :- A(X), D(X).
//   guard(X) :- B(X), C(X).
//   guard(X) :- B(X), D(X).
```

**Why DNF is the target form for Ascent** — DNF is not merely a canonical
normal form; it is the *optimal* representation for Ascent's evaluation model.
Four properties of Ascent's bottom-up semi-naive engine make DNF strictly
better than encoding nested boolean structure inside rule bodies:

1. **No runtime branching inside rules.** Each DNF clause is a flat
   conjunction of literals, which maps directly to Ascent's join-based
   evaluation — one hash-indexed lookup per literal, no conditional logic.
   A nested `or` inside a single rule body would require the engine to
   perform internal branching that bypasses join-driven execution.

2. **Selective firing via semi-naive iteration.** Ascent re-fires a rule only
   when its constituent relations have new tuples (deltas). With DNF, each
   clause is a separate rule, so only clauses whose relations changed re-fire.
   A monolithic rule body encoding a full boolean tree would re-fire whenever
   *any* sub-relation changes, wasting work on unchanged branches.

3. **Parallel evaluation.** Independent rule bodies can be evaluated
   concurrently — each DNF clause maps to a separate Ascent rule, and Ascent's
   architecture supports concurrent rule application. DNF exposes the maximal
   parallelism inherent in the disjunction.

4. **Index utilization.** Each flat conjunction can use Ascent's per-relation
   hash indices optimally. The join ordering within a clause is determined by
   the selectivity estimator (M7), which operates on flat conjunctions. Nested
   boolean structure would obscure the optimal join order from the estimator.

**DNF blowup lint** — DNF expansion of a formula with n conjuncts of k
disjuncts each produces k^n clauses. The compiler emits a lint (DNF01) when
expansion exceeds 16 clauses, warning the user to restructure their guard or
use named auxiliary relations instead of deeply nested `and`/`or`. For typical
guards (2–3 disjuncts of 2–3 conjuncts = 4–9 rules), DNF is strictly
beneficial. Beyond the lint threshold, the combinatorial blowup in rule count
may outweigh the per-rule evaluation advantages, and named auxiliary relations
should be used to factor out shared sub-expressions.

### Syntactic Sugar — Implications

`entails(A, B)` ≡ `¬A ∨ B` (synonym: `implies`). Desugars to auxiliary
Ascent relation + negation:

```rholang
// Sugar:
for (@x <- ch) where entails(reachable(x, y), safe(y)) { P }

// Compiler generates auxiliary relation:
//   reachable_but_unsafe(X) :- reachable(X, Y), not(safe(Y)).
// Desugars to:
//   where not(reachable_but_unsafe(x))
```

`implied_by(A, B)` ≡ `entails(B, A)` — reverse implication:

```rholang
// Sugar:
for (@x <- ch) where implied_by(safe(y), reachable(x, y)) { P }

// Equivalent to:
for (@x <- ch) where entails(reachable(x, y), safe(y)) { P }
```

`iff(A, B)` ≡ `(A ⟹ B) ∧ (B ⟹ A)` — biconditional. Desugars to two
auxiliary relations:

```rholang
// Sugar:
for (@x <- ch) where iff(member(x, s), valid(x)) { P }

// Compiler generates:
//   member_not_valid(X) :- member(X, S), not(valid(X)).
//   valid_not_member(X) :- valid(X), not(member(X, S)).
// Desugars to:
//   where not(member_not_valid(x)), not(valid_not_member(x))
```

### Syntactic Sugar — Quantifiers

**Universal** (`forall`) desugars to negated existential:

```rholang
// Sugar:
for (@x <- ch) where forall(y, nodes, entails(reachable(x, y), safe(y))) { P }
//   forall(var, domain, body)

// Compiler generates:
//   violates(X) :- nodes(Y), reachable(X, Y), not(safe(Y)).
// Desugars to:
//   where not(violates(x))
```

**Existential** — free variables in Datalog bodies are implicitly existential:

```rholang
// Explicit sugar:
for (@x <- ch) where exists(y, nodes, reachable(x, y)) { P }

// Equivalent plain Datalog:
for (@x <- ch) where nodes(y), reachable(x, y) { P }
```

**Bounded quantification:**

```rholang
// Bounded existential (search limited to k steps):
for (@x <- ch) where exists(y, 100, rewrites_to(x, y)) { P }

// Bounded universal:
for (@x <- ch) where forall(y, 50, entails(reachable(x, y), safe(y))) { P }
```

### Unicode Sugar

Every ASCII keyword/operator has a Unicode alternative. The parser accepts
both; Unicode desugars to the ASCII form before compilation.

| ASCII             | Unicode  | Category              |
|-------------------|:--------:|-----------------------|
| `forall`          |   `∀`    | Quantifier            |
| `exists`          |   `∃`    | Quantifier            |
| `and(...)`        | `∧(...)` | Logic (where sugar)   |
| `or(...)`         | `∨(...)` | Logic (where sugar)   |
| `not(...)`        | `¬(...)` | Logic (where)         |
| `entails(...)`    |   `⟹`    | Logic (where sugar)   |
| `implies(...)`    |   `⟹`    | Synonym for entails   |
| `implied_by(...)` |   `⟸`    | Logic (where sugar)   |
| `iff(...)`        |   `⟺`    | Logic (where sugar)   |
| `in` / `:`        |   `∈`    | Set/domain/membership |
| `>=`              |   `≥`    | Comparison            |
| `<=`              |   `≤`    | Comparison            |
| `!=`              |   `≠`    | Comparison            |
| `->*`             |   `→*`   | Rewrite closure       |
| `/\`              |   `∧`    | Pattern conjunction   |
| `\/`              |   `∨`    | Pattern disjunction   |
| `~`               |   `¬`    | Pattern negation      |

**Examples with Unicode:**

```rholang
// Quantified guard with Unicode
for (@x <- ch) where ∀(y, nodes, ⟹(reachable(x, y), safe(y))) { P }

// Domain membership
for (@x <- ch) where ∀(y ∈ nodes, safe(y)) { P }

// Comparisons
for (@x <- ch) where x ≥ 0, x ≠ 42 { P }

// Rewrite closure
for (@x <- ch) where x →* {} { P }

// Set membership (refinement type)
for (@x <- ch) where x ∈ PosInt { P }
// Equivalent ASCII forms:
// for (@x <- ch) where x in PosInt { P }
// for (@x <- ch) where x : PosInt { P }
// for (@x <- ch) where PosInt(x) { P }

// Pattern operators
for (@(x ∧ a!(b)) <- n) where path(b, {}) { P }
```

### Syntax Mapping

The canonical generic syntax for guarded receive is
`(n ? guard).{body}`,
matching the constructor declaration in §4. The design rationale for
separating Rholang surface sugar from the internal canonical form is
language-genericity: the `(n ? guard).{body}` form is language-agnostic and
maps directly to the `PGuardedInput` constructor's field layout, while
surface sugar like `for(... <- ...) where ...` is specific to each `language!`
definition. This separation ensures the pipeline (§12) and codegen (§13)
operate on a uniform internal representation regardless of the source
language.

```
"(" n "?" guard ")" "." "{" p "}"
```

This canonical form has four positional fields: channel `n`, guard pattern,
behavioral predicates (comma-separated after the structural guard), and
continuation body `p`. The question mark `?` serves as the field separator
between channel and guard, chosen to avoid collision with existing Rholang
operators.

The `for (@pattern <- channel) where preds { body }` notation used in the
examples above is Rholang-specific surface sugar. The desugaring rewrites the
`where`-clause predicates into the canonical comma-separated form and
transposes the channel from arrow-source to first field:

```
for (@(x /\ a!(b)) <- n) where path(b, {}), not(path(x, {})) { P }
⟶  (n ? @(x /\ a!(b)), path(b, {}), not(path(x, {}))).{ P }
```

The desugaring is purely syntactic — it rearranges fields without semantic
transformation. The structural guard `@(x /\ a!(b))` and behavioral
predicates `path(b, {})`, `not(path(x, {}))` are preserved verbatim; only
their position relative to the channel changes.

| Syntax Form                                      | Context                              |
|--------------------------------------------------|--------------------------------------|
| `(n ? guard, preds).{body}`                      | Generic/internal (language-agnostic) |
| `for (@pattern <- channel) where preds { body }` | Rholang for sugar (global where)     |
| `for (@pat <- ch, where preds; ...) { body }`    | Rholang for sugar (per-bind where)   |
| `contract name(args) where preds = { body }`     | Rholang contract sugar               |
| `case @pat <- ch where preds => { body }`        | Rholang select branch sugar          |

Subsequent sections (§§3–10 and beyond) use the internal `(n ? ...)` form
to remain language-agnostic. The Rholang surface sugar is specific to the
rho-calculus term algebra and would differ for other `language!`-defined
calculi. For how each language configures its own guard sublanguage —
connective keywords, built-in predicates, and constraint theory registrations
— see §2A.

---

## 2A. Language-Generic Guard Configuration

### Motivation

The guard sublanguage described in §2 uses Rholang-specific conventions:
the `where` keyword introduces guards, connectives like `and`, `or`, `not`
have hardcoded keyword spellings, and built-in predicates (`eq`, `gt`,
`fresh`, etc.) are always available with no explicit declaration. Constraint
theory dispatch in [`predicate_dispatch.rs`](../../prattail/src/predicate_dispatch.rs) uses hardcoded keyword heuristics
(`is_arithmetic_relation()`, `is_unification_relation()`, etc.) — acknowledged
as "temporary, not extensible, and brittle" (§16, Relation Name Heuristics).

The `guards {}` block solves this by letting each `language!`-defined language
explicitly declare its guard sublanguage — which logical connectives exist and
what keywords spell them, which built-in predicates are available, and which
constraint theories handle analysis — without modifying PraTTaIL internals.

### Block Syntax

```rust
language! {
    name: MyLanguage,
    types { ... },
    tokens { ... },

    guards {
        // ── Built-in predicates (direct items) ───────────────
        // Predicates with hardcoded implementations (not Ascent
        // relations).  Uses the SAME syntax template pattern as
        // `terms {}`:
        //   Label . params |- syntax_template ;
        //
        // The syntax template defines keyword spellings AND fixity.
        // Multiple syntax forms for the same predicate use `|`.
        // Params can have optional type annotations for type-
        // dependent dispatch.  Variadic params use `+` suffix;
        // syntax uses `#sep()` for separators.
        //
        // If no predicates are listed: all standard built-ins
        // enabled with default syntax.
        // If any are listed: only listed predicates available;
        // unlisted ones produce a compile-time error.
        // User-defined relations from `logic {}` are always
        // available and do NOT need to be listed here.
        //
        // Predicate definitions are direct items of `guards {}`,
        // mirroring the `tokens {}` architecture where token
        // definitions are direct items alongside sub-blocks
        // (mode {}, sync {}, tree_invariants {}).
        eq  . x, y  |- x "==" y | "eq" "(" x "," y ")" ;
        neq . x, y  |- x "!=" y | "neq" "(" x "," y ")" ;
        gt  . x, y  |- x ">" y  | "gt" "(" x "," y ")" ;
        lt  . x, y  |- x "<" y  | "lt" "(" x "," y ")" ;
        ge  . x, y  |- x ">=" y | "ge" "(" x "," y ")" ;
        le  . x, y  |- x "<=" y | "le" "(" x "," y ")" ;

        fresh       . x        |- "fresh" "(" x ")" ;
        ground      . x        |- "ground" "(" x ")" ;
        rewrites_to . x, y     |- "rewrites_to" "(" x "," y ")"
                               | x "→*" y ;
        ac_match    . bag, pat  |- "ac_match" "(" bag "," pat ")" ;
        count_ge    . ch, k     |- "count_ge" "(" ch "," k ")" ;
        count_eq    . ch, k     |- "count_eq" "(" ch "," k ")" ;

        // ── Configuration sub-blocks ─────────────────────────

        // ── Connectives ──────────────────────────────────────
        // Maps logical connective ROLES to their KEYWORD SPELLINGS.
        // Each entry: role = "primary" | "alt1" | "alt2" ;
        // The role name (and, or, not, ...) is a fixed identifier
        // that the compiler maps to the corresponding BehavioralPred
        // variant.  The strings are the keyword(s) that the guard
        // sublanguage parser recognizes for that role.
        //
        // If omitted: all connectives enabled with default keywords.
        // If present: only listed connectives are available; using an
        // unlisted connective in a guard produces a compile-time error.
        connectives {
            and         = "and"         | "∧";
            or          = "or"          | "∨";
            not         = "not"         | "¬";
            entails     = "entails"     | "⟹";
            implied_by  = "implied_by"  | "⟸";
            iff         = "iff"         | "⟺";
            forall      = "forall"      | "∀";
            exists      = "exists"      | "∃";
        }

        // ── Constraint theories ──────────────────────────────
        // Registers ConstraintTheory implementations for predicate
        // dispatch.  Replaces heuristic keyword lists in
        // predicate_dispatch.rs.
        //
        // If omitted: falls back to existing heuristic dispatch.
        theories {
            arithmetic = PresburgerAlgebra for [Int];
            patterns   = UnificationTheory for [Proc, Name];
            types      = LatticeTheory for [Proc, Name, Int, Str];
        }

        // ── Channels ──────────────────────────────────────────
        // Declares which categories serve as communication
        // channels and which term constructors are join patterns.
        // Replaces heuristic M8/M11 inference with explicit,
        // data-driven channel declarations.
        //
        // If omitted: falls back to existing heuristic dispatch.
        // If present: only declared channels/joins activate
        // M8/M11.
        channels {
            channel Name;
            join PGuardedInput(ch: Name);
        }
    },

    terms { ... },
    equations { ... },
    rewrites { ... },
    logic { ... },
}
```

### What Existing Blocks Already Handle

Before introducing the new block, it is important to clarify what is already
covered:

- **`terms {}`** handles the guard *surface syntax* via `?guard:Guard` and the
  syntax template after `|-` (e.g., `"where" guard`). This is sufficient and
  unchanged.
- **`tokens {}`** handles guard *keyword lexing* via custom token definitions
  with modal lexing (`push(guard_mode)`). This is sufficient and unchanged.
- **`logic {}`** handles *user-defined relations*. This is sufficient and
  unchanged.
- **What is missing:** connective-to-keyword mappings, built-in predicate
  declarations, and constraint theory registration — a configuration layer
  that does not fit any existing block.

### Connective Role Mapping

The `connectives {}` sub-section is the **single source of truth** for how
logical operators are spelled in a given language's guard sublanguage. The
compiler uses it in two ways:

1. **Parsing:** The guard sublanguage parser (`parse_behavioral_pred()`)
   consults the connective map to determine which keywords to recognize and
   what `BehavioralPred` variant to produce. For example, if
   `and = "&&" | "∧";` is declared, the parser recognizes `&&` and `∧` as
   conjunction (producing `BehavioralPred::And`), but NOT `"and"` (unless also
   listed). Comma `,` is **always** conjunction in guard position (it is
   structural syntax of the predicate list, not a connective keyword).

2. **Validation:** If a `BehavioralPred::Quantified(Forall, ...)` node appears
   but `forall` is not in `connectives {}`, the compiler emits:
   ```
   error: quantifier `forall` is not available in language `MeTTa`
     --> help: add `forall = "forall" | "∀";` to the `connectives {}`
               block in `guards {}`
   ```

The role names are a **closed set** of fixed identifiers — the compiler knows
exactly which `BehavioralPred` variant each maps to:

| Role         | BehavioralPred Variant            | Notes                   |
|--------------|-----------------------------------|-------------------------|
| `and`        | `And(lhs, rhs)`                   | Binary conjunction      |
| `or`         | `Or(lhs, rhs)`                    | Binary disjunction      |
| `not`        | `Not(inner)`                      | Stratified negation     |
| `entails`    | `Implies(premise, conclusion)`    | Forward implication     |
| `implied_by` | `Implies(conclusion, premise)`    | Reverse (args swapped)  |
| `iff`        | `And(Implies(a,b), Implies(b,a))` | Desugared biconditional |
| `forall`     | `Quantified { Forall, ... }`      | Universal quantifier    |
| `exists`     | `Quantified { Exists, ... }`      | Existential quantifier  |

A language that spells conjunction as `"&&"` and negation as `"~"` simply
writes:
```rust
connectives {
    and = "&&";
    not = "~";
}
```
— no `or`, `forall`, etc. are available in that language.

### Predicate Syntax Templates

Predicate definitions are **direct items** of `guards {}` (not a sub-block),
mirroring the `tokens {}` architecture where token definitions are direct
items alongside configuration sub-blocks. Each predicate declaration reuses
the **same syntax template pattern** as `terms {}` and has the form:

```
Label . params |- syntax_template ;
```

This addresses four design requirements:

**1. Keyword overriding (fixity).** The syntax template naturally expresses
fixity. The position of parameters relative to keyword literals determines
whether the predicate is infix, prefix, postfix, or mixfix:

```rust
guards {
    // Infix:   x > y
    gt  . x, y  |- x ">" y ;

    // Prefix:  gt(x, y)
    gt  . x, y  |- "gt" "(" x "," y ")" ;

    // Both (alternative forms separated by |):
    gt  . x, y  |- x ">" y | "gt" "(" x "," y ")" ;

    // Mixfix:  x between lo and hi
    between . x, lo, hi  |- x "between" lo "and" hi ;
}
```

The compiler generates a Pratt parser entry for each syntax form. Multiple
forms for the same predicate label share a canonical
`BehavioralPred::RelationQuery` with the label as the relation name.

**2. N-ary / variadic predicates.** Parameters support regex-style
repetition quantifiers. The syntax template uses `#sep()` for separator
patterns — the same `PatternOp::Sep` already used in `terms {}`:

| Quantifier | Meaning   | Example                         |
|------------|-----------|---------------------------------|
| `+`        | 1 or more | `xs+` — at least 1 argument     |
| `*`        | 0 or more | `xs*` — any number of arguments |
| `{m,n}`    | m to n    | `xs{2,5}` — 2 to 5 arguments    |
| `{m,}`     | m or more | `xs{2,}` — at least 2           |
| `{,n}`     | 0 to n    | `xs{,3}` — at most 3            |
| `{,}`      | 0 or more | `xs{,}` — equivalent to `*`     |

Quantified parameters can also have **union type annotations** via
disjunction syntax `(Type1|Type2)`, meaning each argument may be any of the
listed types:

```rust
guards {
    // 1-or-more: (== a, b, c) means eq(a,b) ∧ eq(b,c)
    eq_chain . xs+  |- "==" "(" xs.#sep(",") ")" ;

    // Infix chain: a == b == c (same desugaring)
    eq_chain . xs+  |- xs.#sep("==") ;

    // Exactly 2 args (fixed arity, same as non-variadic):
    gt . x, y  |- x ">" y ;

    // 2-or-more with range:
    between . x, bounds{2,}  |- x "between" bounds.#sep("and") ;

    // Typed variadic with union type — each arg is Int or Float:
    all_numeric . xs:(Int|Float)+  |- "all_numeric" "(" xs.#sep(",") ")" ;

    // 0-or-more optional args:
    log . msg, extras*  |- "log" "(" msg ("," extras.#sep(","))? ")" ;
}
```

The compiler desugars n-ary to pairwise conjunction: `eq_chain(a, b, c)` →
`eq(a, b) ∧ eq(b, c)`. The pairwise predicate (`eq`) must also be declared.

**3. Type-dependent dispatch.** Parameters can carry optional type
annotations from `types {}`. When the same label is declared with different
type signatures, the codegen dispatches to the most specific match:

```rust
guards {
    // Generic (any type): uses default PartialOrd
    gt . x, y       |- x ">" y ;

    // Type-specific overload: integer comparison (optimized path)
    gt . x: Int, y: Int  |- x ">" y ;

    // Type-specific overload: string comparison (lexicographic)
    gt . x: Str, y: Str  |- x ">" y ;
}
```

Resolution order: (a) exact type match, (b) generic (untyped) fallback,
(c) compile error if no match. The type of each guard variable is inferred
from the pattern binding context — e.g., if `x` was bound from an
`Int`-typed constructor parameter, the `Int` overload is selected.

**4. Relation between `guards {}` predicates and `logic {}` relations.**

- `guards {}` predicate definitions declare **built-in** predicates with
  hardcoded implementations (comparisons, freshness, structural checks).
  The compiler knows how to codegen them.
- `logic {}` declares **user-defined** Ascent relations populated by Datalog
  rules. The codegen generates hash-indexed membership tests.
- A predicate name used in a guard is resolved first against
  `guards {}` predicates, then against `logic {}` relations. If found in
  neither, it is a compile error.
- Custom predicates that are neither built-in nor Ascent relations should be
  defined as Ascent relations in `logic {}` with rules that check the
  desired property.

### Type Annotations: Analysis vs Codegen Impact

**Are typed predicates type-independent for analysis?** Yes. The compile-time
automata pipeline (SFA satisfiability, dead-rule detection, WFST weight
assignment, selectivity estimation) treats `gt` as `gt` regardless of operand
types. The pipeline operates on guard *structure* (which predicates, which
connectives, what nesting depth), not on value domains. A `gt(x, y)` guard
has the same satisfiability, the same module activation bits, and the same
pipeline flow whether `x` and `y` are `Int` or `Str`.

**Type-dependent analysis and transformations — when are they useful?**

| Use case                                 | Type-dependent?       | Benefit                                                                            |
|------------------------------------------|-----------------------|------------------------------------------------------------------------------------|
| Satisfiability (SFA)                     | No                    | Predicate identity suffices                                                        |
| Dead-rule detection                      | No                    | Structural overlap check                                                           |
| WFST weight assignment                   | No (could be refined) | Type-specific selectivity gives tighter weights                                    |
| Selectivity ordering                     | No (could be refined) | Int `gt` filters ~50%; String `gt` filters differently                             |
| Module activation (`PredicateSignature`) | **Yes**               | `gt(x: Int, y: Int)` activates M12 (Presburger); `gt(x: Str, y: Str)` does not     |
| Theory routing                           | **Yes**               | Typed predicates tell the `theories {}` dispatcher which theory handles this guard |
| Codegen                                  | **Yes**               | Emits the correct Rust comparison (`i64::cmp` vs `str::cmp`)                       |
| Validation                               | **Yes**               | "You can't compare a `Proc` with `>`"                                              |

**Summary:** Type annotations are optional. When present, they enable theory
routing, selectivity refinement, validation, and type-specific codegen. When
omitted, the predicate is generic — codegen emits trait-dispatched operations
and the pipeline uses type-agnostic analysis.

### Theory Routing via Typed Predicates

**Current mechanism (heuristic, in [`predicate_dispatch.rs`](../../prattail/src/predicate_dispatch.rs)):**

The pipeline sets `PredicateSignature` bits by matching predicate names
against hardcoded keyword lists:

```
dispatch_predicate(name: String, sig: PredicateSignature) → ()
  if name ∈ {"gt","add",">",…} then     sig |= M12    ▷ Presburger
  if name ∈ {"match","unify",…} then    sig |= M13    ▷ Unification
  if name ∈ {"subtype",":<",…} then     sig |= M14    ▷ Lattice
```

These heuristics are acknowledged as "temporary, conservative, not extensible,
brittle" (§16, Relation Name Heuristics). User-defined predicates with novel
names miss theory-specific modules.

**Proposed mechanism (type-driven, no new automata needed):**

With typed predicates (`gt . x: Int, y: Int |- x ">" y ;`) and theory
registrations (`theories { arithmetic = PresburgerAlgebra for [Int]; }`), the
pipeline can route precisely:

1. **Build a type→theory map** from `guards { theories {} }`. Each theory
   registration declares which type categories it handles via the `for [...]`
   clause.

2. **Match predicate parameter types to theories** during
   `extract_features()`:
   ```rust
   // Pseudocode for the new walk_predicate branch:
   PredicateExpr::Relation { name, args, param_types } => {
       for theory_reg in &guard_config.theories {
           if theory_handles_types(&theory_reg, param_types) {
               match theory_reg.module_id() {
                   ModuleId::Presburger => sig.set(M12_LINEAR_ARITHMETIC),
                   ModuleId::Unification => sig.set(M13_UNIFICATION),
                   ModuleId::Lattice => sig.set(M14_SUBTYPE_LATTICE),
               }
           }
       }
       // Fallback: if no typed predicate match, use existing heuristics
       if param_types.is_empty() { /* ... existing is_arithmetic_relation() etc. */ }
   }
   ```

3. **`theory_handles_types()` resolution:** Each `TheoryRegistration`
   carries an explicit `for [...]` clause mapping the theory to handled type
   categories. The explicit approach is cleanest:
   ```rust
   theories {
       arithmetic = PresburgerAlgebra for [Int];
       patterns   = UnificationTheory for [Proc, Name];
       types      = LatticeTheory for [Proc, Name, Int, Str];
   }
   ```

**No new automata types needed.** The existing 15 modules (M1–M15) and their
automata (SFA, Büchi, AWA, VPA, Parity Tree, Register, etc.) are
parameterized by `BooleanAlgebra` via `TheoryAlgebra<T>`. Typed predicates
do not change the automaton structure — they change which `BooleanAlgebra`
implementation is plugged in:

- `gt(x: Int, y: Int)` → `TheoryAlgebra<PresburgerAlgebra>` → SFA with
  Presburger transition predicates
- `gt(x: Str, y: Str)` → no theory match → falls back to generic Boolean
  predicate (M1 only)
- `subtype_of(x: Proc, y: Proc)` → `TheoryAlgebra<LatticeTheory>` → SFA
  with lattice transition predicates

The `TheoryAlgebra<T>` wrapper ([`logict.rs`](../../prattail/src/logict.rs)) already bridges
`ConstraintTheory` to `BooleanAlgebra`. No new automata types are required.

### Selectivity Refinement via Typed Predicates

**Current mechanism (in pipeline.rs / predicate_dispatch.rs):**

Selectivity estimation for guard ordering uses fixed heuristics based on
predicate structure:
- Simple relation query → cost 10 (hash lookup)
- AC-matching → cost 25
- Behavioral guard → cost 20
- Quantified guard → cost 30+ (LogicT search)

**Type-informed selectivity:**

With typed predicates, selectivity estimates can be domain-aware:

| Predicate          | Type   | Selectivity estimate | Rationale                           |
|--------------------|--------|----------------------|-------------------------------------|
| `gt(x, y)`         | `Int`  | ~0.50                | Uniform distribution assumption     |
| `gt(x, y)`         | `Str`  | ~0.50                | Lexicographic, similar distribution |
| `eq(x, y)`         | `Int`  | ~1/\|domain\|        | Point query on integer domain       |
| `eq(x, y)`         | `Str`  | ~1/\|domain\|        | Point query on string domain        |
| `fresh(x)`         | `Name` | ~0.80                | Most names are fresh                |
| `subtype_of(x, y)` | `Proc` | variable             | Depends on lattice depth            |

The `PredicateProfile` struct already has `has_arithmetic`, `has_unification`,
`has_subtype` flags. With typed predicates, these can carry the specific type
category, enabling the selectivity estimator to use domain-specific
distributions instead of uniform assumptions.

Implementation: extend `PredicateProfile` with an optional
`type_context: Vec<Ident>` field populated by typed predicate parameter
types. The cost estimator in [`cost_benefit.rs`](../../prattail/src/cost_benefit.rs) can then adjust selectivity
weights based on the type context.

### Channel Declarations for Multi-Channel Guard Dispatch

#### The Problem: Multi-Channel Guard Evaluation

Any language with concurrent communication primitives can express guards that
span multiple channels. This is not specific to Rholang — it arises wherever a
guard predicate references variables bound by different synchronization points.
Without cross-channel analysis, evaluation requires exhaustive Cartesian product
scanning of all channel value combinations.

A "channel" in this context is any binding site where a process waits for a
value — a pi-calculus channel, an ambient boundary, a tuple space pattern, an
actor mailbox, a Petri net place, or a CSP event. The `channels {}` block
generalizes this: the spec author declares which categories in their language
serve this role.

Examples across paradigms:

```rholang
// Rholang — pi-calculus channels
for (@x <- ch1; @y <- ch2) where gt(x, y) { P }

// Ambient calculus — ambient boundaries as channels
for (n1 <- ambients_at(loc1); n2 <- ambients_at(loc2))
  where can_communicate(n1, n2) { P }

// Session-typed pi-calculus — protocol-constrained channels
for (x <- ch1: !Int ?Str; y <- ch2: !Bool ?Int)
  where session_compatible(x, y) { P }

// Linda tuple space — tuple patterns as channels
for ((x, y, z) <- space; (a, b, c) <- space)
  where x + a == 5 { P }

// Petri net — places as channels, token guards
transition t . p1: Place, p2: Place
  |- guard(count_ge(p1, 2), gt(value(p1), value(p2)))
```

All these share the same structure: a guard predicate `f(x, y)` where `x` and
`y` are bound by different synchronization points.

#### Overview: Two Complementary Techniques

Multi-channel guards require two distinct optimizations. **M8 (Multi-Tape
Automata)** fuses N per-channel automata into a single synchronized traversal,
eliminating redundant passes. **M11 (Two-Way Transducers)** prunes channel
value spaces via backward constraint propagation, eliminating combinations
that cannot satisfy the guard before they are ever tried. Together, M8 and
M11 compose with M7's selectivity ordering to form a three-phase optimization
pipeline (§12, Stage 4).

**Acronyms and symbols used in this section:**
- **SFA** — Symbolic Finite Automaton: finite automaton with predicate-guarded transitions over infinite domains (M1)
- **W2T** — Weighted Two-Way Transducer: transducer whose head can move both left and right on the tape
- **WMA** — Weighted Multi-tape Automaton: automaton reading K tapes simultaneously
- **SCC** — Strongly Connected Component: maximal subgraph where every vertex reaches every other
- **BFS** — Breadth-First Search
- **W** — a semiring (W, ⊕, ⊗, 0_W, 1_W) where ⊕ is addition (combine parallel paths), ⊗ is multiplication (combine sequential steps), 0_W is the additive identity (no path), and 1_W is the multiplicative identity (trivial path)

What follows: Part I treats M8 in full, Part II treats M11 in full, then
their composition is shown as a concrete pipeline.

#### Part I — Multi-Tape Automata (M8): Traversal Fusion

##### Motivation

Consider a join pattern binding three channels:

```
for (@x <- ch1; @y <- ch2; @z <- ch3) where f(x, y, z) { P }
```

Without M8, each channel guard compiles to its own SFA and runs independently:

```
Without M8 — N separate traversals:

  ch1 guard ──► SFA₁ ──► accept/reject
  ch2 guard ──► SFA₂ ──► accept/reject     N traversals, N state machines
  ch3 guard ──► SFA₃ ──► accept/reject
```

For N channels this requires N automaton traversals, N sets of bookkeeping
state, and N separate accept/reject decisions that must be combined afterward.
The overhead is both computational (repeated loop control) and structural
(no shared state across guards). Kempe (2004) [§23, ref #22] showed that
multi-tape automata eliminate this redundancy via the **pair construction**.

##### Intuition

Think of a multi-tape automaton as a DJ with K turntables. Each turntable
plays a different record (tape). On each step, the DJ can advance any subset
of turntables — reading their next symbol — while leaving others paused
(epsilon). The DJ selects transitions that match the current symbols on all
active turntables simultaneously. The weight on each transition represents
the DJ's preference for that particular mix. A single DJ at the mixing desk
replaces K independent listeners.

##### Formal Definition

**Definition 2A.1** (Weighted Multi-Tape Automaton, after Kempe 2004).
A K-tape weighted automaton over semiring W is a tuple M = (K, Q, Σ₁…Σ_K, δ, I, F) where:

- K ∈ ℕ is the number of tapes (const-generic in the implementation)
- Q is a finite set of states, each identified by a unique index q ∈ {0, …, |Q|−1}
- Σₖ is the alphabet for tape k (1 ≤ k ≤ K)
- ε denotes the empty symbol (no consumption on a given tape)
- δ ⊆ Q × (Σ₁ ∪ {ε}) × ⋯ × (Σ_K ∪ {ε}) × Q × W is the transition relation.
  Each transition (q, a₁, …, a_K, q′, w) reads symbol aₖ from tape k
  (or ε to skip tape k), moves from state q to q′, and contributes weight w.
- I: Q → W maps initial states to entry weights (0_W for non-initial states)
- F: Q → W maps accepting states to exit weights (0_W for non-accepting states)

The weight of an accepting run ρ = (q₀, t₁, q₁, …, tₙ, qₙ) is:

  w(ρ) = I(q₀) ⊗ w(t₁) ⊗ w(t₂) ⊗ ⋯ ⊗ w(tₙ) ⊗ F(qₙ)

The automaton's semantics assigns to each K-tuple of input strings the ⊕-sum
over all accepting runs:

  ⟦M⟧(x₁, …, x_K) = ⊕{ w(ρ) | ρ accepts (x₁, …, x_K) }

With M8, the three-channel example becomes:

```
With M8 — 1 fused traversal:

  ch1,ch2,ch3 ──► pair(pair(SFA₁, SFA₂), SFA₃) ──► accept/reject
                  └─────────── 1 traversal ───────────┘
```

##### Pair Construction

The core operation is `pair(A₁, A₂)`: given two 1-tape SFAs, build a 2-tape
product automaton that synchronizes their transitions.

**Product state encoding.** For automata with |Q₁| and |Q₂| states, the
product state for (q₁, q₂) is identified by:

  id(q₁, q₂) = q₁ × |Q₂| + q₂

This bijection maps Q₁ × Q₂ → {0, …, |Q₁|×|Q₂|−1}, enabling O(1)
state lookup without hashing.

**Three transition classes.** The pair construction generates three classes of
transitions in the product automaton:

```
 Class 1 — Synchronized (both tapes advance):
 ┌─────────────────────────────────────────────────────────┐
 │  (q₁, q₂) ──[a₁, a₂]──► (q₁′, q₂′)                      │
 │  weight: w₁ ⊗ w₂                                        │
 │  For every t₁ ∈ δ₁ and t₂ ∈ δ₂                          │
 └─────────────────────────────────────────────────────────┘

 Class 2 — Tape 1 advances, tape 2 idles (epsilon on tape 2):
 ┌─────────────────────────────────────────────────────────┐
 │  (q₁, q₂) ──[a₁, ε]──► (q₁′, q₂)                        │
 │  weight: w₁                                             │
 │  For every t₁ ∈ δ₁ and every q₂ ∈ Q₂                    │
 └─────────────────────────────────────────────────────────┘

 Class 3 — Tape 2 advances, tape 1 idles (epsilon on tape 1):
 ┌─────────────────────────────────────────────────────────┐
 │  (q₁, q₂) ──[ε, a₂]──► (q₁, q₂′)                        │
 │  weight: w₂                                             │
 │  For every t₂ ∈ δ₂ and every q₁ ∈ Q₁                    │
 └─────────────────────────────────────────────────────────┘
```

**Chaining property.** The pair construction chains associatively:
`pair(pair(SFA₁, SFA₂), SFA₃)` builds a 3-tape automaton. N-channel join
patterns with N ≥ 2 channel parameters produce N-tape automata. After
construction, `minimize()` reduces the product state space.

**Complexity.** States: O(|Q₁| × |Q₂|). Transitions: O(|δ₁| × |δ₂| + |δ₁| × |Q₂| + |Q₁| × |δ₂|).

##### Operations Summary

| Operation              | Input         | Output                      | Description                                  |
|------------------------|---------------|-----------------------------|----------------------------------------------|
| `pair`                 | `SFA₁, SFA₂`  | `WMA(SFA₁ × SFA₂)` (2-tape) | Synchronize two SFAs into a 2-tape automaton |
| `auto_intersect`       | `WMA`         | `SFA`                       | Collapse tapes with shared constraints       |
| `project`              | `WMA, tape_i` | `SFA`                       | Extract single-tape projection               |
| `multi_tape_intersect` | `WMA₁, WMA₂`  | `WMA`                       | Product of two multi-tape automata           |
| `evaluate`             | `WMA, inputs` | `bool`                      | Simultaneous multi-tape acceptance test      |
| `analyze`              | `WMA`         | `MultiTapeAnalysis`         | State/transition count, dead-tape detection  |

##### Pseudocode

```
pair(A₁: SFA, A₂: SFA) → WMA₂
  allocate product state space: |Q₁| × |Q₂| states
  ∀ (i₁, w₁) ∈ I₁, (i₂, w₂) ∈ I₂:
    mark id(i₁, i₂) as initial with weight w₁ ⊗ w₂
  ∀ (f₁, w₁) ∈ F₁, (f₂, w₂) ∈ F₂:
    mark id(f₁, f₂) as accepting with weight w₁ ⊗ w₂
  ▷ synchronized transitions
  ∀ t₁ = (p₁ →[a₁] q₁, w₁) ∈ δ₁:
    ∀ t₂ = (p₂ →[a₂] q₂, w₂) ∈ δ₂:
      add (id(p₁,p₂) →[a₁,a₂] id(q₁,q₂), w₁ ⊗ w₂)
  ▷ tape 1 advances, tape 2 idles
  ∀ t₁ = (p₁ →[a₁] q₁, w₁) ∈ δ₁:
    ∀ q₂ ∈ Q₂:
      add (id(p₁,q₂) →[a₁,ε] id(q₁,q₂), w₁)
  ▷ tape 2 advances, tape 1 idles
  ∀ t₂ = (p₂ →[a₂] q₂, w₂) ∈ δ₂:
    ∀ q₁ ∈ Q₁:
      add (id(q₁,p₂) →[ε,a₂] id(q₁,q₂), w₂)
  return result
```

```
evaluate(M: WMA_K, x₁…x_K: String[K]) → W
  worklist ← { (q, [0; K], I(q)) | q ∈ initial states }
  while worklist ≠ ∅ do
    (state, positions[K], path_weight) ← pop(worklist)
    if ∀k. positions[k] = |xₖ| ∧ F(state) ≠ 0_W then
      result ← result ⊕ (path_weight ⊗ F(state))
    ∀ (state →[a₁…a_K] state′, w) ∈ δ:               ▷ transition
      ∀ k:                                           ▷ tape
        if aₖ ≠ ε then new_pos[k] ← positions[k]+1
      if ∀k. aₖ matches xₖ[positions[k]] (∨ aₖ = ε) then
        push(worklist, (state′, new_pos, path_weight ⊗ w))
  return result  (0_W if no accepting run)
```

Implementation: [multi_tape.rs](../../prattail/src/multi_tape.rs).

##### M8's Limitation

Multi-tape fusion reduces the *number of traversals* from N to 1, but it does
not filter the *input values* fed to those traversals. If ch1 has 10 values,
ch2 has 20, and ch3 has 15, the fused automaton still evaluates up to
10 × 20 × 15 = 3,000 combinations. To reduce the number of combinations
*before* they reach M8, we need backward constraint propagation — the
subject of M11.

#### Part II — Two-Way Transducers (M11): Value Space Pruning

##### Motivation

Where M8 fuses N automata into one traversal, M11 attacks the combinatorial
explosion of the Cartesian product of channel values:

```
Without M11 — exhaustive Cartesian product:

  ch1: {a,b,c} × ch2: {x,y,z} = 9 combinations tested
  ┌───┬───┬───┐
  │a,x│a,y│a,z│
  ├───┼───┼───┤
  │b,x│b,y│b,z│  ← all 9 tested, even if b never satisfies f(·,y)
  ├───┼───┼───┤
  │c,x│c,y│c,z│
  └───┴───┴───┘

With M11 — backward constraint pruning:

  ch2 guard + backward transducer ──► ch1 pruned to {a,c}
  ch1: {a,c} × ch2: {x,y,z} = 6 combinations tested
  ┌───┬───┬───┐
  │a,x│a,y│a,z│  ← b eliminated: no y exists s.t. f(b,y) holds
  ├───┼───┼───┤
  │c,x│c,y│c,z│
  └───┴───┴───┘
```

The backward transducer computes the **pre-image**: the set of ch1 values
that *can* participate in a satisfying combination. Values outside the
pre-image are provably useless and are never tried.

##### Intuition

Think of a two-way transducer as a librarian scanning a bookshelf. A one-way
librarian can only walk from left to right, reading titles. A two-way
librarian can walk in both directions — she might scan right to find a
reference, then walk back left to verify a citation, then continue rightward.
The endmarkers ⊢ and ⊣ are the walls at each end of the shelf. Each scan
produces output (notes) with a cost weight. The backward pass is what
enables constraint propagation: the librarian reads later channels first,
then walks back to prune earlier channels.

##### Formal Definition

**Definition 2A.2** (Weighted Two-Way Transducer, after Feng & Maletti 2022
[§23, ref #15]). A weighted two-way transducer over semiring W is a tuple
M = (Q→, Q←, A, B, T, ⊢, ⊣) where:

- Q→ is a finite set of **forward states** (head moves right after transition)
- Q← is a finite set of **backward states** (head moves left after transition)
- Q = Q→ ∪ Q← is the full state set, with Q→ ∩ Q← = ∅
- A is the input alphabet
- B is the output alphabet; B* denotes the set of all finite strings over B
- T ⊆ Q × (A ∪ {⊢, ⊣}) × Q × B* × W is the transition relation.
  Each transition (q, a, q′, v, w) reads symbol a, moves to state q′
  (direction determined by whether q′ ∈ Q→ or q′ ∈ Q←), emits output
  string v ∈ B*, and contributes weight w.
- ⊢ is the left endmarker (beginning of tape)
- ⊣ is the right endmarker (end of tape)

The **input tape** for a string a₁ a₂ … aₙ is:

```
Position:  0    1    2    ⋯    n   n+1
Symbol:    ⊢    a₁   a₂   ⋯   aₙ   ⊣
```

The transducer begins in an initial state at position 0 (reading ⊢) and
accepts by reaching a designated final state at position n+1 (reading ⊣).
The head direction is determined by the *target* state of each transition:
if q′ ∈ Q→, the head moves right (position + 1); if q′ ∈ Q←, the head moves
left (position − 1).

The semantics of M on input a₁…aₙ is:

  ⟦M⟧(a₁…aₙ) = ⊕{ w(ρ) ⊗ output(ρ) | ρ is an accepting run on ⊢ a₁…aₙ ⊣ }

where w(ρ) is the ⊗-product of transition weights along the run, and
output(ρ) is the concatenation of output strings along the run.

##### Enhanced Tape and Head Movement

The tape ⊢ a₁ … aₙ ⊣ has n+2 positions. A configuration is a triple
(state, position, accumulated_output). The direction of head movement is
determined by the source state's partition membership:

```
Forward state (q ∈ Q→):    position ──► position + 1  (scan right)
Backward state (q ∈ Q←):   position ◄── position − 1  (scan left)
```

Acceptance requires that the transducer reaches a final forward state at
position n+1 (the right endmarker ⊣). The ability to reverse direction is
what enables backward constraint propagation: the transducer reads downstream
channel constraints, reverses, and prunes upstream values.

##### Crossing Sequences

**Definition 2A.3** (Crossing Sequence). The crossing sequence at position
i of a run ρ is the subsequence of (state, direction) pairs observed each
time the head crosses position i. Formally, for run ρ = (q₀,p₀), (q₁,p₁), …,
the crossing sequence at position i is:

  CS_i(ρ) = ⟨(qⱼ, dir(qⱼ)) | pⱼ = i and pⱼ₊₁ ≠ pⱼ⟩

**Loop detection.** If the same (state, position, direction) triple is
encountered twice during a run, the transducer is in an infinite loop.
The triple (q, pos, dir) uniquely characterizes the transducer's future
behavior from that point, so a repeated triple means unbounded cycling.

**Theorem 2A.1** (Shepherdson 1959). Every weighted two-way transducer with
|Q| states can be converted to an equivalent one-way transducer with at most
2^O(|Q|) states. The crossing sequence at each position has length bounded
by 2|Q| (each state can cross each position at most once in each direction
before looping), giving the exponential blowup in the one-way conversion.

##### ChannelConstraint

The bridge between M11's transducer theory and the join optimization pipeline
is the `ChannelConstraint` struct (from [`two_way_transducer.rs`](../../prattail/src/two_way_transducer.rs)):

```rust
pub struct ChannelConstraint<W: Semiring> {
    pub channels: Vec<String>,
    pub transducer: WeightedTwoWayTransducer<W>,
}
```

- **Forward transduction:** ch_i value → partial guard for ch_j.
  Given a concrete value on channel i, the forward pass produces the
  constraint that channel j's value must satisfy.
- **Backward transduction:** ch_j guard → constraint on ch_i values.
  Given the guard on channel j, the backward pass computes the pre-image:
  which ch_i values can possibly lead to joint satisfaction.

The backward transduction is the **SFT pre-image** operation (M15):
`pre_image(guard_sfa) → pruned_sfa`. Values outside the pruned SFA's
language are provably incompatible and need not be tried.

The `JoinPatternAnalysis` struct aggregates results across all channels:

```rust
pub struct JoinPatternAnalysis<W: Semiring> {
    pub optimal_order: Vec<usize>,            // Channel indices, most selective first
    pub reorder_cost: W,                      // Cost of reordering
    pub deadlock_cycles: Vec<Vec<usize>>,     // Circular dependencies
    pub constraint_graph: HashMap<(usize, usize), W>,  // Inter-channel weights
}
```

Here, **SCC** (Strongly Connected Component) detection on the constraint graph
identifies deadlock cycles — groups of channels whose constraints form circular
dependencies that require special handling (e.g., breaking the cycle by
materializing an intermediate channel).

##### Pseudocode

```
transduce(M: W2T, input: a₁…aₙ) → (W, B*)
  tape ← [⊢, a₁, a₂, …, aₙ, ⊣]
  worklist ← { (q₀, 0, 1_W, ε, ∅) }    ▷ (state, pos, weight, output, visited)
  result ← (0_W, ε)
  while worklist ≠ ∅ do
    (state, pos, w, out, visited) ← pop(worklist)
    ▷ crossing sequence loop detection
    config ← (state, pos, direction(state))
    if config ∉ visited then               ▷ prune infinite loops
      visited′ ← visited ∪ {config}
      ▷ acceptance check
      if state ∈ F ∧ pos = n+1 then
        result ← result ⊕ (w, out)
      ▷ expand transitions
      ∀ (state →[tape[pos]] state′, v, w′) ∈ T:
        new_pos ← pos + 1 if state′ ∈ Q→, else pos − 1
        if 0 ≤ new_pos ≤ n+1 then
          push(worklist, (state′, new_pos, w ⊗ w′, out · v, visited′))
```

Crossing-sequence loop detection uses `(state, position, direction)` triples
to distinguish forward and backward traversals through the same position.
Implementation: [two_way_transducer.rs](../../prattail/src/two_way_transducer.rs).

#### Composition: The M7 → M11 → M8 Optimization Pipeline

##### Three-Phase Pipeline

The Stage 4 optimizer (§12) applies M7, M11, and M8 in sequence:

1. **M7 — Selectivity ordering:** Estimate per-channel selectivity (probability
   that a random value satisfies the guard). Reorder channels most-selective-first
   to maximize early pruning.
2. **M11 — Backward constraint propagation:** For each adjacent pair in the
   reordered sequence, build a backward transducer and compute the pre-image,
   pruning the earlier channel's value space.
3. **M8 — Multi-tape fusion:** Fuse the (now smaller) per-channel SFAs into a
   single K-tape product automaton. Minimize the result.

##### Worked 3-Channel Example

Consider the join pattern `for (@x <- ch1; @y <- ch2; @z <- ch3) where f(x,y,z) { P }`.

**Phase 1 — M7 Selectivity ordering:**

  sel(ch1) = 0.3,  sel(ch2) = 0.7,  sel(ch3) = 0.5
  Reorder: ch1 (0.3), ch3 (0.5), ch2 (0.7) — most selective first

**Phase 2 — M11 Backward constraint propagation:**

  |ch1| = 10, |ch3| = 15, |ch2| = 20  (before pruning)

  Step 2a: backward(ch3 → ch1) prunes ch1: 10 → 10 × sel(ch3) ≈ 6 values
  Step 2b: backward(ch2 → ch3) prunes ch3: 15 → 15 × sel(ch2) ≈ 12 values
  Effective product: 6 × 12 × 20 = 1,440 (vs. original 10 × 15 × 20 = 3,000)

**Phase 3 — M8 Multi-tape fusion:**

  pair(pair(SFA_ch1_pruned, SFA_ch3_pruned), SFA_ch2) → 3-tape automaton
  minimize(product) → minimal state space
  Single traversal evaluates all 1,440 remaining combinations

**Result:** 3,000 → 1,440 combinations (52% reduction), evaluated in 1 traversal
instead of 3.

##### Data Flow Diagram

```
┌────────────────────────────────────────────────────────────┐
│                    Stage 4: Optimize (§12)                 │
│                                                            │
│  Guard predicates                                          │
│       │                                                    │
│       ▼                                                    │
│  ┌──────────────┐   channel order  ┌────────────────────┐  │
│  │ M7 Selectiv. │ ───────────────► │ M11 Backward W2T   │  │
│  │ (estimate)   │                  │ (prune values)     │  │
│  └──────────────┘                  └────────┬───────────┘  │
│                                             │ pruned SFAs  │
│                                             ▼              │
│                                    ┌────────────────────┐  │
│                                    │ M8 Multi-Tape      │  │
│                                    │ (fuse into 1)      │  │
│                                    └────────┬───────────┘  │
│                                             │ fused WMA    │
│                                             ▼              │
│                                    ┌────────────────────┐  │
│                                    │ Codegen            │  │
│                                    │ (single traversal) │  │
│                                    └────────────────────┘  │
└────────────────────────────────────────────────────────────┘
```

##### Complexity Table

| Configuration   | Combinations Tested       | Traversals | Pre-processing Cost                |
|-----------------|---------------------------|------------|------------------------------------|
| No optimization | \|ch1\|×\|ch2\|×⋯×\|chN\| | N          | —                                  |
| M7 only         | same (reordered)          | N          | O(N log N) sorting                 |
| M7 + M11        | reduced by pruning        | N          | O(N² × \|Q_W2T\|²) backward passes |
| M7 + M11 + M8   | reduced by pruning        | **1**      | + O(\|Q₁\|×\|Q₂\|) pair per step   |

#### Applicability Across Language Paradigms

The following table maps paradigms to their "channel" constructs and the
combined M8 + M11 benefit:

| Paradigm                 | "Channel" Construct    | Multi-Channel Pattern                                     | Combined M8 + M11 Benefit                                                          |
|--------------------------|------------------------|-----------------------------------------------------------|------------------------------------------------------------------------------------|
| **Rholang (π-calculus)** | Named channels `n`     | `for (@x <- ch1; @y <- ch2)` join patterns                | Fuse per-channel guards into one traversal; prune values via backward constraints  |
| **Ambient Calculus**     | Ambient boundaries     | `in(n1)`, `out(n2)` mobility predicates spanning ambients | One-pass ambient checking; eliminate ambients that can't satisfy mobility guard    |
| **Session-Typed π**      | Typed linear channels  | Protocol-constrained multi-channel communication          | Multi-tape protocol compliance; backward-prune incompatible protocol prefixes      |
| **CSP**                  | Synchronization events | Parallel event guards: `c1 → P ‖ c2 → Q`                  | Fused event precedence; eliminate events that make synchronization impossible      |
| **Actor Model**          | Mailboxes              | Pattern-matched message dispatch across actors            | Fused mailbox guards; pre-image filters incompatible messages before dispatch      |
| **Linda Tuple Space**    | Tuple patterns         | `in(p1); in(p2)` multi-tuple coordination                 | Parallel tuple constraints; backward-prune tuples that fail combined constraint    |
| **Petri Nets**           | Places + token counts  | Multi-place transition guards                             | Token count guards in one automaton; prune token distributions that prevent firing |

**Languages where M8/M11 do not apply:**
- Purely sequential languages without communication (lambda calculus, arithmetic DSLs)
- Languages with single-channel constructs only (no cross-channel guard references)

The key insight: M8 and M11 provide a unified compilation framework for any
`language!` spec with multi-channel guards, regardless of whether the "channels"
are message-passing endpoints, spatial boundaries, pattern-matching domains, or
resource containers.

#### Current Mechanism (Heuristic)

Currently, `classify_grammar()` infers channels by treating every grammar
category as a potential channel:
- `SyntaxItemSpec::NonTerminal/Binder/Collection` items bind
  `param_name → category`
- Cross-category references in guard predicates trigger M8/M11 conservatively
- This can over-activate: a Lambda calculus with `Term` and `Type` categories
  would trigger M8 on any rule referencing both, even though there are no
  channels

This heuristic approach is acknowledged as temporary, conservative, and not
extensible — the same limitation that §16 acknowledges for heuristic theory
dispatch prior to explicit `theories {}` declarations.

#### Proposed Mechanism (Data-Driven)

The `channels {}` sub-block follows the `theories {}` precedent: an explicit,
declarative block that replaces heuristic inference with data-driven dispatch.

```rust
channels {
    // Channel category declarations:
    //   channel <Category> ;
    channel Name;

    // Join pattern declarations:
    //   join <Label>(<param>: <Category>, ...) ;
    // Lists only channel-binding parameters (not all constructor params).
    // N channel params supported (not limited to 2).
    join PGuardedInput(ch: Name);
    join PJoin(ch1: Name, ch2: Name, ch3: Name);
}
```

**Activation rules** (deterministic):
- **M8 activates** when any declared join pattern has ≥2 channel params
- **M11 additionally activates** when ≥2 distinct channel categories appear
  across join patterns
- When `channels {}` is **omitted**, falls back to heuristic dispatch
  (backward-compatible)

#### Concrete `channels {}` Examples Across Paradigms

```rust
// ── Rholang ──
guards {
    channels {
        channel Name;
        join PGuardedInput(ch: Name);
        join PJoin(ch1: Name, ch2: Name);
    }
}

// ── Ambient Calculus ──
guards {
    channels {
        channel Name;  // Ambient boundaries
        join AmbientMove(src: Name, dst: Name);
    }
}

// ── Session-Typed Pi ──
guards {
    channels {
        channel Session;  // Typed session endpoints
        join SessionPair(client: Session, server: Session);
    }
}

// ── Linda Tuple Space ──
guards {
    channels {
        channel Pattern;  // Tuple patterns
        join MultiIn(p1: Pattern, p2: Pattern, p3: Pattern);
    }
}

// ── Petri Net ──
guards {
    channels {
        channel Place;  // Petri net places
        join Transition(input1: Place, input2: Place);
    }
}
```

Languages without channels (lambda calculus, calculator) simply omit
`channels {}`.

#### Join Pattern Analysis and Lints

The pipeline validates `channels {}` declarations and emits diagnostics for
common configuration issues:

| Lint   | Severity | Condition                                                            | Message                                                     |
|--------|----------|----------------------------------------------------------------------|-------------------------------------------------------------|
| `MT01` | Warning  | Declared channel category not referenced in any join pattern         | `channel category 'X' is declared but unused`               |
| `MT02` | Error    | Join pattern references a category not declared as channel           | `join pattern references undeclared channel category 'X'`   |
| `TW01` | Note     | M11 activated but all join patterns use the same channel category    | `backward propagation has no cross-category dependencies`   |
| `TW02` | Warning  | Join pattern has only 1 channel param (M8 not needed)                | `single-channel join 'X' does not benefit from M8`          |
| `TW03` | Error    | Join pattern label does not match any term constructor in `terms {}` | `join pattern 'X' has no corresponding term constructor`    |
| `PD04` | Note     | `channels {}` omitted; heuristic dispatch is active                  | `M8/M11 dispatch is heuristic; consider adding channels {}` |

### Token References and String Literals in Syntax Templates

**Design principle:** In all `language!` syntax templates (`terms {}`,
`guards {}` predicates, `guards { connectives {} }`, `equations {}`,
`rewrites {}`), **token names from `tokens {}` are interchangeable with
string literals**. When a token name is used, it matches ALL of that token's
alternatives (disjunctions, regex patterns), not just a single literal.

**Terminal expression forms:** Anywhere a string literal `">"` can appear in a
`language!` syntax template, any of the following forms are equally valid:

| Form               | Example                        | Matches                                         |
|--------------------|--------------------------------|-------------------------------------------------|
| String literal     | `">"`                          | Exactly `>`                                     |
| Token name         | `Gt`                           | All alternatives of `Gt` token from `tokens {}` |
| Inline disjunction | `">" \| "≥" \| "greater_than"` | Any of the listed literals                      |
| Inline regex       | `/[>≥]/`                       | Any character matching the regex                |

**Resolution rules for unquoted identifiers:**
1. A declared parameter name → `SyntaxExpr::Param`
2. A declared token name from `tokens {}` → `SyntaxExpr::TokenRef`
   (expands to all alternatives)
3. Otherwise → compile error ("unknown identifier in syntax template")

**Examples:**

```rust
tokens {
    Gt    = ">" | "≥" | "greater_than";
    Where = "where" | "when" push(guard_mode);
    And   = "and" | "∧" | "&&";
}

terms {
    // String literal: matches only ">"
    PGt . x:Expr, y:Expr |- x ">" y : Expr ;

    // Token reference: matches ">", "≥", or "greater_than"
    PGt . x:Expr, y:Expr |- x Gt y : Expr ;

    // Inline disjunction: matches ">" or "≥" (no token def needed)
    PGt . x:Expr, y:Expr |- x (">" | "≥") y : Expr ;

    // Token reference for guard keyword
    PGuardedInput . ch:Name, ^[xs].pat:[Name* -> Name],
                    ?guard:Guard, ^[ys].cont:[Name* -> Proc]
        |- "for" "(" "@" "{" pat "}" "<-" ch ")" Where guard
           "{" cont "}" : Proc ;
}

guards {
    // Token reference in syntax template:
    gt . x, y |- x Gt y ;
    // Inline disjunction:
    le . x, y |- x ("<=" | "≤") y ;
    // String literal (single match):
    lt . x, y |- x "<" y ;

    connectives {
        // Token reference: and matches "and", "∧", or "&&"
        and = And;
        // Inline disjunction (no token def needed):
        or  = "or" | "∨";
        // Inline regex:
        not = /not|¬/;
    }
}
```

**Anonymous vs. named token semantics:**

Inline string literals, disjunctions, and regexes are **always anonymous
tokens** — they do NOT automatically map to `tokens {}` definitions, even if
a matching one exists. To inherit a token's properties (priority, modal
lexing, stream routing), you must use the **token name** explicitly.

| Form           | Semantics                                                 | Inherits token properties?       |
|----------------|-----------------------------------------------------------|----------------------------------|
| `">"`          | Anonymous `TerminalPattern(TokenKind::Fixed)`             | No — self-contained              |
| `Gt`           | Named token reference → expands to all `Gt` alternatives  | **Yes** — priority, mode, stream |
| `(">" \| "≥")` | Anonymous disjunction → two `TerminalPattern(Fixed)` each | No                               |
| `/[>≥]/`       | Anonymous regex → compiled NFA fragment                   | No                               |

The lint `TOK01` bridges the two worlds: when `tokens {}` is present and a
string literal has a matching token definition, the lint suggests using the
token name instead:
```
warning[TOK01]: string literal ">" has a matching token definition `Gt`
  help: use `Gt` to inherit its properties (priority, mode transitions)
```

When no `tokens {}` block is present, `TOK01` does not fire — the language
is using the simpler mode where all terminals are auto-registered from
string literals.

### Block Interaction Summary

| Concern                | Block                       | Mechanism                                             |
|------------------------|-----------------------------|-------------------------------------------------------|
| Guard surface syntax   | `terms {}`                  | Syntax template after `\|-` with `?guard:Guard` param |
| Guard keyword lexing   | `tokens {}`                 | `push(guard_mode)` on keyword token                   |
| Connective keywords    | `guards { connectives {} }` | Role → keyword mapping **(NEW)**                      |
| Built-in predicates    | `guards {}` (direct items)  | Name + arity declarations **(NEW)**                   |
| Constraint theories    | `guards { theories {} }`    | Theory registrations **(NEW)**                        |
| Channel dispatch       | `guards { channels {} }`    | Explicit M8/M11 activation **(NEW)**                  |
| User-defined relations | `logic {}`                  | `relation R(T1, T2);` declarations                    |
| Refinement type guards | `types {}`                  | `PosInt = { x: Int \| x > 0 };`                       |

**`connectives {}` vs `tokens {}`:** The `tokens {}` block defines how
keywords are **lexed** (regex patterns, priority, modal scoping). The
`connectives {}` block defines what role each keyword **plays** in the guard
sublanguage. A token defined in `tokens {}` might serve multiple roles or no
guard role at all. A connective keyword listed in `connectives {}` should
correspond to a token in `tokens {}` (or a built-in literal). If the
language omits `tokens {}`, the connective keywords are recognized as bare
identifiers by the default lexer.

### Concrete Examples

**Rholang — full guard features, standard keywords:**

```rust
language! {
    name: RhoCalc,
    types { Proc, Name, ![i64] as Int },

    tokens {
        Where   = "where"   push(guard_mode);
        mode guard_mode {
            Not     = "not"     | "¬";
            And     = "and"     | "∧";
            Or      = "or"      | "∨";
            ForAll  = "forall"  | "∀";
            Exists  = "exists"  | "∃";
            Entails = "entails" | "⟹";
            ImpliedBy = "implied_by" | "⟸";
            Iff     = "iff"     | "⟺";
        }
    },

    guards {
        eq  . x, y  |- x "==" y | "eq" "(" x "," y ")" ;
        neq . x, y  |- x "!=" y | "neq" "(" x "," y ")" ;
        gt  . x, y  |- x ">" y  | "gt" "(" x "," y ")" ;
        lt  . x, y  |- x "<" y  | "lt" "(" x "," y ")" ;
        ge  . x, y  |- x ">=" y | "ge" "(" x "," y ")" ;
        le  . x, y  |- x "<=" y | "le" "(" x "," y ")" ;
        fresh       . x        |- "fresh" "(" x ")" ;
        ground      . x        |- "ground" "(" x ")" ;
        rewrites_to . x, y     |- x "→*" y
                                | "rewrites_to" "(" x "," y ")" ;
        ac_match    . bag, pat  |- "ac_match" "(" bag "," pat ")" ;
        count_ge    . ch, k     |- "count_ge" "(" ch "," k ")" ;
        count_eq    . ch, k     |- "count_eq" "(" ch "," k ")" ;

        connectives {
            and         = "and"         | "∧";
            or          = "or"          | "∨";
            not         = "not"         | "¬";
            entails     = "entails"     | "⟹";
            implied_by  = "implied_by"  | "⟸";
            iff         = "iff"         | "⟺";
            forall      = "forall"      | "∀";
            exists      = "exists"      | "∃";
        }
        theories {
            arithmetic = PresburgerAlgebra for [Int];
            patterns   = UnificationTheory for [Proc, Name];
            types      = LatticeTheory for [Proc, Name, Int, Str];
        }
        channels {
            channel Name;
            join PGuardedInput(ch: Name);
        }
    },

    terms {
        PGuardedInput . ch:Name, ^[xs].pat:[Name* -> Name],
                        ?guard:Guard, ^[ys].cont:[Name* -> Proc]
            |- "for" "(" "@" "{" pat "}" "<-" ch ")"
               "where" guard "{" cont "}" : Proc ;
        // ...
    },
    logic {
        relation path(Proc, Proc);
        relation safe(Proc);
        path(X, Z) :- path(X, Y), path(Y, Z);
    },
    rewrites { /* ... */ },
}
```

**MeTTa — minimal guards, operator-style keywords:**

```rust
language! {
    name: MeTTa,
    types { Atom, Expression },

    tokens {
        If = "if" push(guard_mode);
        mode guard_mode {
            Amp  = "&&";
            Tild = "~";
        }
    },

    guards {
        eq  . x, y  |- x "==" y ;
        neq . x, y  |- x "!=" y ;

        // MeTTa uses && for conjunction and ~ for negation.
        // No quantifiers, no disjunction, no implications.
        connectives {
            and = "&&";
            not = "~";
        }
        theories {
            patterns = UnificationTheory for [Atom];
            types    = LatticeTheory for [Atom, Expression];
        }
        // MeTTa does not have join patterns; `channels {}` is omitted.
        // Heuristic dispatch applies if cross-category guards exist.
    },

    terms {
        MAtom . s:Symbol |- s : Atom ;
        MApp  . f:Atom, args:Atom |- "(" f args ")" : Atom ;
    },
    rewrites {
        // Conditional rewrite — fires only when guard holds
        TypedBeta . | guard(eq(type_of(f), FnType))
            |- (MApp f arg) ~> (eval f arg) ;
    },
    logic {
        relation type_of(Atom, Atom);
    },
}
```

**Guarded Lambda Calculus — minimal, restricted connectives:**

```rust
language! {
    name: GuardedLambda,
    types { Term },

    guards {
        eq . x, y  |- x "==" y ;

        // Only negation (via "not") and equality predicate.
        // Comma-separated predicates (implicit conjunction) are
        // ALWAYS available regardless of connectives {} — comma is
        // structural syntax, not a connective keyword.
        connectives {
            not = "not";
        }
        // No theories — purely behavioral (Ascent lookup)
        // No concurrent communication; M8/M11 do not apply.
        // `channels {}` is omitted.
    },

    terms {
        Var . |- Var : Term ;
        Lam . ^x.body:[Term -> Term] |- "lam" x "." body : Term ;
        App . f:Term, a:Term |- "(" f a ")" : Term ;
    },
    rewrites {
        Beta . | guard(closed(arg))
            |- (App (Lam f) arg) ~> (eval f arg) ;
    },
    logic {
        relation closed(Term);
    },
}
```

**Clojure-style — n-ary predicates, prefix-only, type overloads:**

```rust
language! {
    name: ClojureLike,
    types { Expr, ![i64] as Int, ![String] as Str },

    guards {
        // 1-or-more: (= a b c) → eq(a,b) ∧ eq(b,c)
        eq . xs+  |- "=" "(" xs.#sep(",") ")" ;

        // 2-to-5 args with range quantifier:
        between . x, bounds{2,5}
            |- "between?" "(" x "," bounds.#sep(",") ")" ;

        // Union-typed variadic: each arg can be Int or Str
        comparable . xs:(Int|Str)+
            |- "comparable?" "(" xs.#sep(",") ")" ;

        // Type-specific comparison:
        gt . x: Int, y: Int  |- ">" "(" x "," y ")" ;
        gt . x: Str, y: Str  |- ">" "(" x "," y ")" ;

        // Prefix-only predicate:
        nil_q . x  |- "nil?" "(" x ")" ;

        connectives {
            and = "and";
            or  = "or";
            not = "not";
        }
        // No join patterns; `channels {}` omitted.
    },

    terms { /* ... */ },
    logic { /* ... */ },
}
```

### Defaults (Block Omitted)

When `guards {}` is absent, the language gets the current behavior:

| Component               | Default                                                                                                                                     |
|-------------------------|---------------------------------------------------------------------------------------------------------------------------------------------|
| predicates (direct)     | All standard built-ins enabled with default syntax (infix operators + prefix call forms)                                                    |
| `connectives` sub-block | All roles enabled with standard keywords (`"and"`, `"or"`, `"not"`, `"forall"`, `"exists"`, `"entails"`, `"implied_by"`, `"iff"` + Unicode) |
| `theories` sub-block    | None registered → heuristic keyword dispatch fallback                                                                                       |
| `channels` sub-block    | None → heuristic M8/M11 inference from grammar structure                                                                                    |

Existing languages (`RhoCalc`, `Lambda`, `Ambient`, `Calculator`) work
unchanged. Languages without `?guard:Guard` in `terms {}` or `guard(...)` in
premises pay zero cost — the block is entirely optional.

### Composition Semantics

| Component               | `extends`                                                                    | `includes`    | `mixins`      |
|-------------------------|------------------------------------------------------------------------------|---------------|---------------|
| predicates (direct)     | Union (error on name+type conflict)                                          | Not inherited | Not inherited |
| `connectives` sub-block | Intersect roles; keyword sets union per shared role (error on role conflict) | Not inherited | Not inherited |
| `theories` sub-block    | Union (error on name/type conflict)                                          | Not inherited | Not inherited |
| `channels` sub-block    | Union categories; union join patterns (error on conflict)                    | Not inherited | Not inherited |

**Rationale:** `includes` imports grammar (types + terms) only. `mixins`
import types + terms from fragments. Guard configuration is semantic, not
syntactic, so it stays with the defining language — `channels {}` follows the
same pattern as `connectives`, predicates, and `theories`. `extends` inherits
everything, but connective intersection prevents unsound widening (a child
cannot add `forall` if the parent did not declare it — the parent's guard
parser would not recognize it).

### AST Representation

The AST types for `guards {}` live in [language.rs](../../macros/src/ast/language.rs):

```rust
/// Guard configuration from the `guards { ... }` block.
/// Predicate definitions are direct items (like token defs in `tokens {}`);
/// connectives, theories, and channels are configuration sub-blocks.
pub struct GuardConfig {
    /// Built-in predicate definitions (direct items of `guards {}`).
    /// `None` → all standard built-ins enabled.
    pub builtin_predicates: Option<Vec<BuiltinPredicate>>,

    /// Connective role → keyword mappings (sub-block).
    /// `None` → all connectives with default keywords.
    pub connectives: Option<Vec<ConnectiveDecl>>,

    /// Constraint theory registrations for predicate dispatch (sub-block).
    /// Empty → fall back to heuristic keyword dispatch.
    pub theories: Vec<TheoryRegistration>,

    /// Channel configuration for M8/M11 dispatch (sub-block).
    /// `None` → fall back to heuristic channel inference.
    pub channels: Option<ChannelConfig>,
}

/// Fixed set of connective roles the compiler recognizes.
pub enum ConnectiveRole {
    And, Or, Not, Entails, ImpliedBy, Iff, Forall, Exists,
}

/// A single connective declaration: `role = "kw1" | "kw2" ;`
pub struct ConnectiveDecl {
    pub role: ConnectiveRole,
    pub keywords: Vec<String>,
}

/// A built-in predicate declaration: `Label . params |- syntax ;`
pub struct BuiltinPredicate {
    pub name: Ident,
    pub params: Vec<PredicateParam>,
    pub syntax_forms: Vec<Vec<SyntaxExpr>>,
}

/// A predicate parameter with optional type annotation and quantifier.
pub struct PredicateParam {
    pub name: Ident,
    pub ty: Option<ParamType>,
    pub quantifier: Option<ParamQuantifier>,
}

/// Type constraint on a predicate parameter.
pub enum ParamType {
    Single(Ident),            // x: Int
    Union(Vec<Ident>),        // x: (Int|Float)
}

/// Regex-style repetition quantifier on a variadic parameter.
pub enum ParamQuantifier {
    OneOrMore,                // +
    ZeroOrMore,               // * or {,}
    Range { min: usize, max: Option<usize> },  // {m,n}
}

/// A constraint theory registration: `name = TheoryType for [Types] ;`
pub struct TheoryRegistration {
    pub name: Ident,
    pub theory_type: syn::Type,
    pub handled_types: Option<Vec<Ident>>,
}

/// Channel configuration from `channels { ... }` sub-block.
pub struct ChannelConfig {
    pub channel_categories: Vec<ChannelDecl>,
    pub join_patterns: Vec<JoinPatternDecl>,
}

/// `channel <category> ;`
pub struct ChannelDecl {
    pub category: Ident,
}

/// `join <Label>(<param>: <Category>, ...) ;`
pub struct JoinPatternDecl {
    pub label: Ident,
    pub channel_params: Vec<ChannelParam>,
}

/// A channel-binding parameter in a join pattern.
pub struct ChannelParam {
    pub param_name: Ident,
    pub category: Ident,
}
```

The `LanguageDef` struct gains:
```rust
pub struct LanguageDef {
    // ... existing fields ...
    pub guard_config: Option<GuardConfig>,
}
```

### Per-Predicate Selectivity and Cost Annotations

The pipeline orders guard evaluation by **selectivity** — the estimated
fraction of inputs satisfying a predicate — and breaks ties by **cost** — the
relative computational expense of evaluating the predicate. Currently, both
values are hardcoded per-predicate-pattern in [`predicate_dispatch.rs`](../../prattail/src/predicate_dispatch.rs) (§12
of that module) and [`guard_codegen.rs`](../../macros/src/gen/runtime/guard_codegen.rs). Grammar authors with domain knowledge
can provide tighter estimates via `@[...]` annotations on predicate
declarations.

**Notation.** Throughout this subsection and the following five subsections,
the following additional notation is used:

| Notation     | Meaning                                                                                                                             |
|--------------|-------------------------------------------------------------------------------------------------------------------------------------|
| sel(P)       | Selectivity estimate for predicate P: a value in [0.0, 1.0] where 0.0 means "rejects all inputs" and 1.0 means "accepts all inputs" |
| cost(P)      | Relative evaluation cost for predicate P: a value in ℕ (natural numbers) where lower values indicate cheaper evaluation             |
| \|D\|        | Cardinality (number of elements) of a finite domain D                                                                               |
| arity        | Number of parameters a predicate accepts                                                                                            |
| arity factor | Diminishing correction `1 / √(arity + 1)` that reduces selectivity estimates as arity increases                                     |
| √x           | Square root of x                                                                                                                    |
| AST          | Abstract Syntax Tree — the in-memory tree representation of parsed source code                                                      |
| k            | Quantifier bound (maximum iteration count) in bounded quantification                                                                |
| n            | Number of elements in an AC-match pattern (see §8 "AC-Matching for Collections")                                                    |

**Syntax.** The existing `BuiltinPredicate` declaration (shown above in "AST
Representation") is extended with optional trailing annotations. Annotations
appear inside `@[...]` after the predicate's syntax forms and before the `;`
terminator:

```rust
guards {
    eq    . x, y |- x "==" y    @[selectivity(0.1), cost(2)] ;
    gt    . x, y |- x ">"  y    @[selectivity(0.5)] ;
    fresh . x    |- "fresh" "(" x ")" @[cost(1)] ;
    // When no @[...] appears, the pipeline uses heuristic defaults.
    neq   . x, y |- x "!=" y ;
}
```

The `@[...]` syntax reuses the annotation bracket convention already
established in the `language!` macro for other metadata. Multiple annotations
are comma-separated within a single `@[...]` bracket.

**Annotation semantics:**

| Annotation       | Domain         | Feeds                                                        | Omission behavior                   |
|------------------|----------------|--------------------------------------------------------------|-------------------------------------|
| `selectivity(s)` | s ∈ [0.0, 1.0] | `estimate_predicate_selectivity()`, `estimate_selectivity()` | Heuristic default (see table below) |
| `cost(c)`        | c ∈ ℕ          | `condition_cost()`, `estimate_guard_cost()`                  | Heuristic default (see table below) |

Both annotations are optional and independent — a predicate may specify one,
both, or neither. When both are omitted, the predicate falls through to the
same heuristic estimation that the pipeline uses today, preserving backward
compatibility.

**Selectivity algebra for Boolean combinators.** Annotations apply to
**leaf predicates** only — atomic predicate invocations like `eq(x, y)` or
`fresh(x)`, not compound expressions built with connectives. The selectivity
of compound predicates is derived from leaf selectivities using standard
probability-theoretic identities (under an independence assumption for ∧,
meaning the satisfaction of P is assumed to be statistically independent of
the satisfaction of Q):

| Compound form       | Selectivity formula                       | Derivation                                                   |
|---------------------|-------------------------------------------|--------------------------------------------------------------|
| ¬P                  | sel(¬P) = 1 − sel(P)                      | Complement probability                                       |
| P ∧ Q               | sel(P ∧ Q) = sel(P) · sel(Q)              | Independence assumption: Pr(A ∩ B) = Pr(A) · Pr(B)           |
| P ∨ Q               | sel(P ∨ Q) = 1 − (1 − sel(P))(1 − sel(Q)) | Inclusion-exclusion: Pr(A ∪ B) = 1 − Pr(Ā) · Pr(B̄)           |
| P ⟹ Q               | sel(P ⟹ Q) = 1 − sel(P) · (1 − sel(Q))    | Material implication: P ⟹ Q ≡ ¬P ∨ Q                         |
| ∀x ∈ D. P(x)        | sel(∀) = sel(P)^\|D\|                     | Universal: all \|D\| elements must satisfy P                 |
| ∃x ∈ D. P(x)        | sel(∃) = 1 − (1 − sel(P))^\|D\|           | Existential: at least one of \|D\| elements must satisfy P   |
| ∀x (infinite). P(x) | sel(∀∞) = sel(P) · 0.05                   | Heuristic: 5% of body selectivity (very restrictive)         |
| ∃x (infinite). P(x) | sel(∃∞) = 1 − (1 − sel(P))^10             | Heuristic: 10-element proxy for unknown infinite domain size |

These formulas are implemented identically in both
`estimate_predicate_selectivity()` (in [`predicate_dispatch.rs`](../../prattail/src/predicate_dispatch.rs), operating on
`PredicateExpr` AST nodes from the `prattail` crate) and
`estimate_selectivity()` (in [`guard_codegen.rs`](../../macros/src/gen/runtime/guard_codegen.rs), operating on
`BehavioralPred` AST nodes from the `macros` crate). The `@[selectivity(...)]`
annotation overrides only the **leaf** estimate; the combinator algebra
remains unchanged.

**Updated AST.** The `BuiltinPredicate` struct gains an `annotations` field.
When the parser encounters `@[...]` after the syntax forms of a predicate
declaration, it populates the corresponding `PredicateAnnotations` fields:

```rust
pub struct BuiltinPredicate {
    pub name: Ident,
    pub params: Vec<PredicateParam>,
    pub syntax_forms: Vec<Vec<SyntaxExpr>>,
    pub annotations: PredicateAnnotations,   // ← NEW
}

/// Optional per-predicate hints that override heuristic estimates.
/// Both fields default to `None` (fall back to pipeline heuristics).
#[derive(Debug, Clone, Default)]
pub struct PredicateAnnotations {
    /// Selectivity ∈ [0.0, 1.0]: estimated fraction of inputs satisfying the
    /// predicate. Overrides the heuristic in `estimate_predicate_selectivity()`.
    pub selectivity: Option<f64>,
    /// Relative evaluation cost ∈ ℕ: lower = cheaper. Overrides the heuristic
    /// in `estimate_predicate_cost()` and `estimate_guard_cost()`.
    pub cost: Option<u32>,
}
```

**Heuristic defaults.** The following table enumerates every hardcoded
selectivity and cost value that `@[selectivity, cost]` annotations can
override. Each row shows the predicate pattern, the current heuristic value,
the source location, and the function that consumes it. The column
"Heuristic sel" gives the selectivity estimate; the column "Heuristic cost"
gives the cost estimate. A `—` entry indicates the function estimates cost
only, not selectivity (or vice versa):

| Predicate pattern                   | Heuristic sel      | Heuristic cost | Source file                | Consumer function(s)                                            |
|-------------------------------------|--------------------|----------------|----------------------------|-----------------------------------------------------------------|
| Equality (`eq`, `==`, `fresh`)      | 0.1 × arity factor | 2 + arity      | `predicate_dispatch.rs`    | `estimate_predicate_selectivity()`, `estimate_predicate_cost()` |
| Cardinality (`count`, `size`)       | 0.3 × arity factor | 2 + arity      | `predicate_dispatch.rs`    | `estimate_predicate_selectivity()`, `estimate_predicate_cost()` |
| Default (unrecognized) relation     | 0.5 × arity factor | 2 + arity      | `predicate_dispatch.rs`    | `estimate_predicate_selectivity()`, `estimate_predicate_cost()` |
| Negated relation query              | 0.1                | 2              | `guard_codegen.rs`         | `estimate_selectivity()`                                        |
| Positive relation query             | 0.5                | 2              | `guard_codegen.rs`         | `estimate_selectivity()`                                        |
| Universal quantifier (bounded, k)   | 0.05 / √k          | k + body cost  | `guard_codegen.rs`         | `estimate_selectivity()`, `estimate_guard_cost()`               |
| Existential quantifier (bounded, k) | 0.3 / √k           | k + body cost  | `guard_codegen.rs`         | `estimate_selectivity()`, `estimate_guard_cost()`               |
| AC-match (n elements)               | 0.3 / n            | 10 + 5n        | `guard_codegen.rs`         | `estimate_selectivity()`, `estimate_guard_cost()`               |
| Freshness check                     | —                  | 2              | `rules.rs`                 | `condition_cost()`                                              |
| Environment query                   | —                  | 5              | `rules.rs`                 | `condition_cost()`                                              |
| ForAll (condition-level)            | —                  | 10 + body cost | `rules.rs`                 | `condition_cost()`                                              |
| BehavioralGuard (general)           | —                  | 20             | `rules.rs`                 | `condition_cost()`                                              |
| BehavioralGuard (AC-match)          | —                  | 25             | `rules.rs`                 | `condition_cost()`                                              |


### Comprehensive Heuristic Inventory

Not all heuristics should be surfaced to grammar authors. The guiding
principle is a two-part test:

- **Semantic intent heuristics** — heuristics that guess the grammar author's
  intent from naming conventions or keyword presence — should be
  configurable, because the compiler cannot reliably infer intent from
  naming alone. Example: the heuristic that treats a predicate named `"gt"`
  as an arithmetic comparison (activating module M12, Linear Arithmetic)
  is semantic — the grammar author knows whether `"gt"` is Presburger
  arithmetic or something else entirely.

- **Structural grammar heuristics** — heuristics that derive module
  activation from directly observable grammar structure (recursion, branching
  factor, paired delimiters) — should remain internal, because the compiler
  can see the structure directly and the grammar author would gain nothing
  from restating it.

This inventory partitions every heuristic in [`predicate_dispatch.rs`](../../prattail/src/predicate_dispatch.rs) and
[`guard_codegen.rs`](../../macros/src/gen/runtime/guard_codegen.rs) into two tables based on that test. Each entry
lists the current heuristic mechanism, the source location, and either the
`guards {}` sub-block that replaces it (Configurable Heuristics table) or the
rationale for keeping it internal (Table C).

**Configurable heuristics — surfaced by `theories {}`, `channels {}`,
`connectives {}`, and `@[selectivity, cost]`.** Theory registrations replace
the `is_*_relation()` keyword-matching functions. Channel and connective
declarations replace structural inference heuristics:

| Heuristic                             | Current behavior                                                           | Module(s)               | Override mechanism                                               | Source                       |
|---------------------------------------|----------------------------------------------------------------------------|-------------------------|------------------------------------------------------------------|------------------------------|
| `is_equality_relation()`              | Keywords: `eq`, `neq`, `==`, `!=`, `fresh`, `equal`, `related`             | M6 Register             | `theories { equality = RegisterTheory for [Name, Proc]; }`       | `predicate_dispatch.rs`      |
| `is_cardinality_relation()`           | Keywords: `count`, `size`, `>=`, `<=`, `at_least`, `at_most`               | M9 Multiset             | `theories { cardinality = MultisetTheory for [Collection]; }`    | `predicate_dispatch.rs`      |
| `is_fixpoint_relation()`              | Keywords: `letprop`, `fixpoint`, `mu`, `nu`, `letrec`, `recursive`         | M4 VPA + M5 Parity Tree | `theories { fixpoints = FixpointTheory for [Proc, Name]; }`      | `predicate_dispatch.rs`      |
| `is_arithmetic_relation()`            | Keywords: `add`, `sub`, `gt`, `lt`, `>=`, `<=`, `bounded`, `range`, ...    | M12 Linear Arithmetic   | `theories { arithmetic = PresburgerAlgebra for [Int]; }`         | `predicate_dispatch.rs`      |
| `is_unification_relation()`           | Keywords: `match`, `unify`, `bind`, `pattern`, `substitute`, ...           | M13 Unification         | `theories { patterns = UnificationTheory for [Proc, Name]; }`    | `predicate_dispatch.rs`      |
| `is_subtype_relation()`               | Keywords: `subtype`, `:<`, `:>`, `is_a`, `join`, `meet`, `lub`, `glb`, ... | M14 Subtype Lattice     | `theories { types = LatticeTheory for [Proc, Name, Int, Str]; }` | `predicate_dispatch.rs`      |
| Arithmetic terminals                  | `+`, `-`, `*`, `/`, `%`, `mod`, `div`                                      | M12 Linear Arithmetic   | Same `arithmetic` theory registration                            | `predicate_dispatch.rs`      |
| Unification terminals                 | `match`, `case`, `with`, `=>`, `->`, `\|`                                  | M13 Unification         | Same `patterns` theory registration                              | `predicate_dispatch.rs`      |
| Subtype terminals                     | `extends`, `implements`, `:`, `::`, `:<`, `is`                             | M14 Subtype Lattice     | Same `types` theory registration                                 | `predicate_dispatch.rs`      |
| Cross-category → M8 Multi-Tape        | `referenced_categories.len() >= 2` in `classify_grammar()`                 | M8 Multi-Tape           | `channels { channel C; join J(p: C, q: C); }`                    | `predicate_dispatch.rs`      |
| Cross-category → M11 Two-Way          | Cross-category ref differs from rule's own category                        | M11 Two-Way             | `channels {}` with ≥ 2 distinct channel categories               | `predicate_dispatch.rs`      |
| Multi-channel → M7 Probabilistic + M8 | `channels_seen.len() >= 2` in `extract_features()`                         | M7 Prob. + M8           | `channels {}` declarations                                       | `predicate_dispatch.rs`      |
| Cross-channel variable detection      | `ChannelContext.is_cross_channel()` per relation argument                  | —                       | `channels {}` channel parameter bindings                         | `predicate_dispatch.rs`      |
| Hardcoded connective keywords         | `&&`, `\|\|`, `~`, `!`, `=>` as Rust tokens in parser                      | —                       | `connectives { and = "keyword"; ... }`                           | `language.rs`                |
| Leaf predicate selectivity            | Pattern-matched defaults (0.1, 0.3, 0.5, ...)                              | —                       | `@[selectivity(s)]` annotation                                   | See heuristic defaults table |
| Leaf predicate cost                   | Pattern-matched defaults (2, 5, 10, ...)                                   | —                       | `@[cost(c)]` annotation                                          | See heuristic defaults table |

When `theories {}` is present and non-empty, the pipeline skips all
`is_*_relation()` calls and terminal-based inference for the theories
that are explicitly registered. Unregistered theories still fall through to
heuristic dispatch, so partial registration is safe — a grammar may register
`arithmetic = PresburgerAlgebra for [Int];` without registering a unification
theory, and the `is_unification_relation()` heuristic continues to operate
for unification-like predicate names.

**Table C — Heuristics that remain internal.** These heuristics derive from
grammar structure or encode mathematical identities. The "Trigger condition"
column describes the grammar property the compiler detects; the "Rationale"
column explains why the heuristic should not be surfaced. The notation
`refs(C)` denotes the set of grammar categories referenced by category C's
production rules:

| Heuristic                       | Trigger condition                                                                                                            | Module(s)        | Source file(s)                                           | Rationale                                                                     |
|---------------------------------|------------------------------------------------------------------------------------------------------------------------------|------------------|----------------------------------------------------------|-------------------------------------------------------------------------------|
| Recursive category detection    | C ∈ refs(C) (direct self-reference in category graph)                                                                        | M2 Büchi         | `predicate_dispatch.rs`                                  | Structural: the compiler sees the category reference graph directly           |
| Multi-branch universal rules    | Rule has ≥ 3 non-terminal children                                                                                           | M3 AWA           | `predicate_dispatch.rs`                                  | Structural: branching factor is visible from syntax item count                |
| Bracket/delimiter detection     | Paired call/return terminals (`()`/`{}`/`[]`/`begin`/`end`)                                                                  | M4 VPA           | `predicate_dispatch.rs`                                  | Structural: terminal symbols are directly enumerable from grammar             |
| Recursive + branching           | Both recursion and ≥ 3-child branching present                                                                               | M5 Parity Tree   | `predicate_dispatch.rs`                                  | Structural: conjunction of two structural properties                          |
| Binder item detection           | Grammar contains `Binder` syntax items                                                                                       | M6 Register      | `predicate_dispatch.rs`                                  | Structural: `Binder` is a syntactic category the compiler sees directly       |
| Parse ambiguity                 | ≥ 3 rules in same grammar category                                                                                           | M7 Probabilistic | `predicate_dispatch.rs`                                  | Structural: rule count per category is directly computable                    |
| Collection/Sep items            | Grammar contains `Collection` or `Sep` syntax items                                                                          | M9 Multiset      | `predicate_dispatch.rs`                                  | Structural: `Collection`/`Sep` are syntactic categories visible to compiler   |
| Recursion + M11 → M15           | Recursive grammar with M11 Two-Way already activated                                                                         | M15 SFT          | `predicate_dispatch.rs`                                  | Derived: conjunction of structural (recursion) and semantic (M11) properties  |
| Module cost tiers               | `ModuleId::estimated_cost()` returns 1–6 per module                                                                          | All              | `predicate_dispatch.rs`                                  | Implementation detail: scheduling order is internal compiler policy           |
| Selectivity algebra formulas    | Boolean combinator identities (¬, ∧, ∨, ⟹)                                                                                   | —                | `predicate_dispatch.rs`                                  | Mathematical identity: correct by construction, not configurable              |
| Arity factor formula            | `1 / √(arity + 1)` diminishing correction                                                                                    | —                | `predicate_dispatch.rs`                                  | Mathematical identity: diminishing correction derived from probability theory |
| Compilation strategy thresholds | `COMPUTED_GOTO_THRESHOLD` (20), `COLD_THRESHOLD` (1.0), `BP_TABLE_LOOKUP_THRESHOLD` (8), `DIRECT_CODED_THRESHOLD` (30), etc. | —                | `dispatch.rs`, `trampoline.rs`, `pratt.rs`, `codegen.rs` | Implementation detail: codegen strategy selection is internal compiler policy |
| Cost-benefit gate ratios        | Per-optimization `GateId` thresholds in `cost_benefit.rs`                                                                    | —                | `cost_benefit.rs`                                        | Implementation detail: optimization gating is internal policy                 |


### Spec-Level Representation and Override Flow

The `GuardConfig` AST type (shown in "AST Representation" above) contains
`syn` types (`Ident`, `syn::Type`) that are available only during macro
expansion. The `prattail` crate's pipeline, which runs after macro expansion,
cannot depend on the `syn` crate. Therefore, a **lowered representation** —
`GuardConfigSpec` — carries only the information the pipeline needs, using
plain `String` and `HashMap` types instead of `syn` AST nodes.

The lowering is performed by the existing `language_def_to_spec()` function
(in [`prattail_bridge.rs`](../../macros/src/gen/syntax/parser/prattail_bridge.rs)), which already converts `LanguageDef` (syn-based)
to `LanguageSpec` (syn-free). The `GuardConfigSpec` is a new field on
`LanguageSpec`, populated during this conversion. The following diagram shows
the data flow from source to pipeline. Abbreviations: "sel" = selectivity,
"pred" = predicate. Arrows (→) denote data flow direction:

```text
┌──────────────┐   parse_guards()    ┌───────────────┐  language_def_to_spec() ┌───────────────────┐
│ language! {  │ ──────────────────► │  GuardConfig  │ ──────────────────────► │  GuardConfigSpec  │
│   guards {…} │                     │  (syn types)  │                         │  (String/HashMap) │
└──────────────┘                     └───────────────┘                         └─────────┬─────────┘
                                                                                         │
                            ┌────────────────────────────────────────────────────────────┘
                            │
              ┌─────────────┼──────────────────┬──────────────────┐
              ▼             ▼                  ▼                  ▼
     classify_grammar()  estimate_pred_sel()  estimate_sel()   condition_cost()
     (theories → module  (selectivity         (selectivity     (cost
      activation)         overrides)           overrides)       overrides)
```

The `GuardConfigSpec` struct carries the lowered guard configuration. Each
field corresponds to one pipeline concern, and the doc comments explain
which pipeline function consumes it:

```rust
/// Lowered guard configuration for pipeline consumption.
///
/// Produced by `language_def_to_spec()` from the `GuardConfig` AST.
/// All `syn` types have been resolved to plain strings; all annotation
/// values have been extracted into lookup tables.
#[derive(Debug, Clone, Default)]
pub struct GuardConfigSpec {
    /// Theory registrations: each entry maps a theory name to its type
    /// and the set of grammar categories it handles. Used by
    /// `classify_grammar()` to replace heuristic `is_*_relation()`
    /// dispatch with data-driven module activation.
    pub theories: Vec<TheoryRegistrationSpec>,

    /// Explicit channel categories. When `Some`, only the listed
    /// categories are treated as channels for M8/M11 dispatch.
    /// When `None`, the pipeline falls back to heuristic channel
    /// inference from cross-category references.
    pub channel_categories: Option<Vec<String>>,

    /// Per-predicate selectivity overrides, keyed by predicate name.
    /// Values are in [0.0, 1.0]. When a predicate name appears in
    /// this map, `estimate_predicate_selectivity()` returns the
    /// override value instead of computing a heuristic estimate.
    pub selectivity_overrides: HashMap<String, f64>,

    /// Per-predicate cost overrides, keyed by predicate name.
    /// Values are in ℕ. When a predicate name appears in this map,
    /// `estimate_predicate_cost()` and `condition_cost()` return the
    /// override value instead of computing a heuristic estimate.
    pub cost_overrides: HashMap<String, u32>,

    /// Whether the grammar author provided an explicit `connectives {}`
    /// sub-block. When `true`, the parser uses the declared connective
    /// keywords; when `false`, default Rust-token connectives apply.
    pub has_explicit_connectives: bool,

    /// Whether the grammar author provided explicit predicate
    /// declarations (direct items in `guards {}`). When `true`,
    /// closed-world validation is active (see "Predicate Resolution
    /// and Closed-World Validation" below).
    pub has_explicit_predicates: bool,
}
```

The `TheoryRegistrationSpec` carries one theory's lowered data. The
`theory_type` field is the fully-qualified Rust type path as a string
(e.g., `"PresburgerAlgebra"`), and `handled_types` lists the grammar
categories the theory is responsible for:

```rust
/// A single theory registration, lowered from `TheoryRegistration`.
///
/// Corresponds to one `name = TheoryType for [Types];` declaration
/// in the `theories {}` sub-block.
#[derive(Debug, Clone)]
pub struct TheoryRegistrationSpec {
    /// Theory name (e.g., `"arithmetic"`, `"patterns"`).
    pub name: String,
    /// Fully-qualified Rust type path (e.g., `"PresburgerAlgebra"`).
    pub theory_type: String,
    /// Grammar categories this theory handles (e.g., `["Int"]`).
    /// When `None`, the theory handles all categories.
    pub handled_types: Option<Vec<String>>,
}
```

**Override precedence.** When the pipeline estimates selectivity or cost for
a predicate, it consults three sources in priority order. The first source
that provides a value wins:

1. **Explicit annotation** — `@[selectivity(s)]` or `@[cost(c)]` on the
   predicate declaration. These are stored in the `selectivity_overrides` /
   `cost_overrides` maps of `GuardConfigSpec`.
2. **Type-informed heuristic** — when a theory registration in `theories {}`
   covers the predicate's parameter types, the theory's characteristic
   selectivity applies (e.g., Presburger predicates over bounded integers
   have tighter selectivity bounds than the generic default).
3. **Default heuristic** — the pattern-matched estimates in
   `estimate_predicate_selectivity()` and `estimate_predicate_cost()` (the
   values shown in the "Heuristic defaults" table above).

The following pseudocode shows the lookup chain. The symbol `∈` denotes
membership in a map (key lookup), and `∃` denotes "there exists":

```text
fn resolve_selectivity(pred_name, spec, expr):
    // Priority 1: explicit annotation
    if pred_name ∈ spec.selectivity_overrides:
        return spec.selectivity_overrides[pred_name]

    // Priority 2: theory-informed estimate
    if ∃ theory ∈ spec.theories such that theory covers pred_name:
        return theory.characteristic_selectivity(expr)

    // Priority 3: default heuristic
    return estimate_predicate_selectivity(expr)
```


### Extended Merge Semantics for Guard Config

When language B `extends` language A, their `guards {}` blocks must compose.
The "Composition Semantics" table above (in the subsection of the same name)
gives the high-level strategy for each sub-block. This subsection elaborates
the detailed merge rules, including how `@[selectivity, cost]` annotations
interact with inheritance, and provides concrete examples.

**Rules.** Each sub-block has a merge strategy chosen to preserve soundness
(no incorrect module activations) and respect the grammar author's intent
(the extending language's declarations take priority where appropriate):

| Sub-block                  | Merge strategy                          | Conflict resolution                                          | Rationale                                                                 |
|----------------------------|-----------------------------------------|--------------------------------------------------------------|---------------------------------------------------------------------------|
| Builtin predicates         | Union by name                           | Error if same name with different parameter types or arities | Same pattern as `terms {}` merge — predicate names are unique identifiers |
| Predicate annotations      | Extension wins (per-predicate override) | Extension's `@[selectivity, cost]` replaces base's           | The extending language has more specific domain knowledge                 |
| `connectives {}` sub-block | Extension replaces base entirely        | No per-role merge — entire block is replaced                 | Connective semantics are language-specific, not additive                  |
| `theories {}` sub-block    | Union by name                           | Error if same theory name maps to different theory types     | Conflicting theory dispatch would be unsound                              |
| `channels {}` sub-block    | Extension replaces base entirely        | No per-channel merge — entire block is replaced              | Channel topology is language-specific                                     |

**Annotation inheritance.** When language B extends language A and both
declare a predicate with the same name (e.g., `eq`), the merge of
per-predicate `@[selectivity, cost]` annotations follows field-level
override semantics — for each annotation field independently, B's value
takes precedence if present; otherwise A's value is inherited:

- If A declares `eq @[selectivity(0.1), cost(2)]` and B declares
  `eq @[selectivity(0.05)]` (cost omitted), the merged predicate has
  selectivity = 0.05 (B's override) and cost = 2 (inherited from A).
- If A declares `eq @[selectivity(0.1)]` and B declares `eq` with no
  annotations, B inherits A's selectivity = 0.1.
- If A declares `eq @[cost(2)]` and B declares `eq @[cost(5)]`, the merged
  cost is 5 (B wins).

**Example 1 — Predicate union with annotation override:**

```rust
// Base language:
language! {
    name: BaseCalc,
    types { Expr, ![i64] as Int },
    guards {
        eq  . x, y |- x "==" y @[selectivity(0.1), cost(2)] ;
        gt  . x, y |- x ">"  y @[selectivity(0.5), cost(2)] ;
        theories {
            arithmetic = PresburgerAlgebra for [Int];
        }
    },
    terms { /* ... */ },
}

// Extension — overrides gt's selectivity for a domain where ">" is
// less discriminating (e.g., floating-point comparisons):
language! {
    name: TypedCalc,
    extends: BaseCalc,
    types { ![f64] as Float },
    guards {
        // Override gt's selectivity. Cost is inherited from BaseCalc.
        gt  . x, y |- x ">"  y @[selectivity(0.7)] ;
        // New predicate, not in base:
        is_nan . x |- "is_nan" "(" x ")" @[selectivity(0.01), cost(1)] ;
        theories {
            // New theory; arithmetic is inherited from BaseCalc.
            float_arith = FloatTheory for [Float];
        }
    },
    terms { /* ... */ },
}
```

The merged `TypedCalc` guard config contains:
- `eq` with selectivity = 0.1, cost = 2 (inherited unchanged from `BaseCalc`)
- `gt` with selectivity = 0.7 (overridden by `TypedCalc`), cost = 2
  (inherited from `BaseCalc`)
- `is_nan` with selectivity = 0.01, cost = 1 (new in `TypedCalc`)
- Theories: `arithmetic` (inherited from `BaseCalc`) + `float_arith` (new)

**Example 2 — Connective replacement:**

```rust
// Base language uses verbose keywords:
language! {
    name: StdLang,
    types { Term },
    guards {
        eq . x, y |- x "==" y ;
        connectives {
            and = "and" | "∧";
            or  = "or"  | "∨";
            not = "not" | "¬";
        }
    },
    terms { /* ... */ },
}

// Extension replaces connectives entirely with operator-style keywords:
language! {
    name: OperatorLang,
    extends: StdLang,
    guards {
        // Connectives are replaced, not merged:
        connectives {
            and = "&&";
            not = "~";
            // `or` is not declared — OperatorLang does not support
            // disjunction in guards. This is intentional: the
            // extension restricts the guard sublanguage.
        }
    },
    terms { /* ... */ },
}
```

In `OperatorLang`, the only available connectives are `&&` (conjunction) and
`~` (negation). The base language's `"and"`, `"∧"`, `"or"`, `"∨"`, `"not"`,
`"¬"` are all replaced — not merged. This replacement semantics prevents
accidental widening: if `OperatorLang` intends to restrict the guard
sublanguage to conjunction and negation only, inheriting the base's `or`
connective would undermine that intent.


### Predicate Resolution and Closed-World Validation

When the grammar author provides explicit predicate declarations in
`guards {}`, those declarations define a **closed world**: any predicate
name used in a `guard(...)` premise or `where` clause that does not appear
in the declared set (and is not a user-defined relation from `logic {}`)
is a compile error. This opt-in validation catches typos, undeclared
predicates, and references to predicates from a base language that were
not inherited.

**Resolution order.** When the compiler encounters a predicate name R in a
`BehavioralPred::RelationQuery` node (the AST variant for named predicate
invocations) within a `Premise::BehavioralGuard` (the AST variant for guard
premises in rewrite rules), it resolves R against three sources, checked in
order:

1. **`guards {}` builtin predicates** — the `builtin_predicates` list in
   `GuardConfig`. If R matches a declared predicate name, resolution
   succeeds and the predicate's parameter types and arity are validated
   against the declaration.

2. **`logic {}` user-defined relations** — the `relation R(T1, T2, ...);`
   declarations in the `logic {}` block. These are Ascent relations
   populated by Datalog rules, not built-in predicates. Resolution succeeds
   if R matches a declared relation name with compatible arity.

3. **Compile error** — if R is not found in either source, the compiler
   emits a diagnostic with a help message listing available predicate names:

   ```text
   error[GUARD01]: unknown predicate `R` in guard expression
     --> src/main.rs:42:15
      |
   42 |     guard(R(x, y))
      |           ^ not found in `guards {}` or `logic {}` declarations
      |
      = help: declare `R` in `guards { R . x, y |- ... ; }` or
              `logic { relation R(Type1, Type2); }`
      = note: available predicates: eq, neq, gt, lt, fresh, path, safe
   ```

**Open world (default).** When `builtin_predicates` is `None` — that is,
the `guards {}` block is absent or contains only sub-blocks like
`connectives {}` without direct predicate declarations — all standard
built-in predicates are available. This is the default and preserves
backward compatibility with existing `language!` definitions. The standard
built-ins include all predicates recognized by the `is_*_relation()`
heuristic functions (see Table A in "Comprehensive Heuristic Inventory"
above).

The distinction between open and closed worlds is captured by the
`has_explicit_predicates` flag in `GuardConfigSpec`:

| `has_explicit_predicates` | Resolution behavior                                                                  |
|---------------------------|--------------------------------------------------------------------------------------|
| `false` (default)         | All standard built-ins available; no validation errors for known predicates          |
| `true`                    | Only declared predicates + `logic {}` relations; unknown names produce error GUARD01 |

**Validation walk.** The compiler validates predicate names during the
lowering pass (`language_def_to_spec()`), before any pipeline analysis runs.
The validation traverses every `BehavioralPred` AST node in every
`Premise::BehavioralGuard` and `Condition::BehavioralGuard` across all
rules in the language definition. The `resolution_table` is the union of
`guards {}` predicate names and `logic {}` relation names:

```text
for each rule R in language.rules:
    for each premise P in R.premises:
        if P is BehavioralGuard(pred):
            validate_pred_names(pred, resolution_table)

fn validate_pred_names(pred, table):
    match pred:
        RelationQuery { relation_name, args, .. }:
            if relation_name ∉ table:
                emit error GUARD01 with available names from table
            else:
                check arity: |args| = table[relation_name].arity
        And(a, b) | Or(a, b) | Implies(a, b):
            validate_pred_names(a, table)
            validate_pred_names(b, table)
        Not(inner):
            validate_pred_names(inner, table)
        Quantified { body, .. }:
            validate_pred_names(body, table)
        AcMatch { .. }:
            // AC-match is a structural form, not a named predicate;
            // no name resolution needed.
            pass
```

When `has_explicit_predicates` is `false`, the `resolution_table` is
pre-populated with all standard built-in predicate names (the same set that
the `is_*_relation()` heuristic functions recognize), so all currently valid
guard expressions continue to compile without changes.


### Connective Parser Integration

The guard sublanguage parser — `parse_behavioral_pred()` and its
sub-parsers `parse_pred_implies()`, `parse_pred_or()`, `parse_pred_and()`,
`parse_pred_not()`, `parse_pred_atom()` (all in [language.rs](../../macros/src/ast/language.rs))
— currently recognizes a fixed set of Rust tokens as logical connectives:
`&&` for conjunction, `||` for disjunction, `~` and `!` for negation, `=>`
for implication, and the identifiers `forall` and `exists` for quantifiers.
When `connectives {}` remaps these roles to different keywords, the parser
must recognize the new keywords without changing the recursive descent
structure.

**`ConnectiveMap` design.** A `ConnectiveMap` is a bidirectional lookup
table built from the `Vec<ConnectiveDecl>` in `GuardConfig` (the AST type
for connective declarations, defined in "AST Representation" above). It maps
each `ConnectiveRole` (the fixed enum of logical roles: `And`, `Or`, `Not`,
`Entails`, `ImpliedBy`, `Iff`, `Forall`, `Exists`) to its set of recognized
keywords, and each keyword back to its role:

```rust
/// Bidirectional mapping between connective roles and their surface keywords.
///
/// Built from `connectives {}` declarations in `GuardConfig`. When `None`
/// is passed to the parser, default Rust-token recognition applies.
#[derive(Debug, Clone)]
pub struct ConnectiveMap {
    /// Role → keywords: for each `ConnectiveRole`, the set of keywords
    /// that can represent it in the guard sublanguage. Multiple keywords
    /// per role are supported (e.g., `and = "and" | "∧";` maps both
    /// `"and"` and `"∧"` to `ConnectiveRole::And`).
    pub role_to_keywords: HashMap<ConnectiveRole, Vec<String>>,
    /// Keyword → role: reverse mapping for parser lookups. Each keyword
    /// maps to exactly one role (enforced by validation — see below).
    pub keyword_to_role: HashMap<String, ConnectiveRole>,
}
```

The parser functions receive an `Option<&ConnectiveMap>` parameter threaded
through the recursive descent call chain:

- When `None` (no `connectives {}` block), the existing Rust-token parsing
  applies unchanged — `&&` matches conjunction, `||` matches disjunction,
  etc.
- When `Some(map)`, each parser function peeks at the input and consults the
  map instead of checking hardcoded tokens.

**Keyword recognition.** Connective keywords fall into two categories
depending on whether they are valid Rust punctuation tokens or plain
identifiers. The parser uses different peek strategies for each:

| Keyword type       | Examples                        | Parser peek strategy                                                |
|--------------------|---------------------------------|---------------------------------------------------------------------|
| Rust punctuation   | `&&`, `\|\|`, `~`, `!`, `=>`    | `input.peek(Token![&&])`, `input.peek(Token![=>])`, etc.            |
| Identifier keyword | `"and"`, `"or"`, `"not"`, `"∧"` | `input.peek(Ident)` then match string against `map.keyword_to_role` |

For identifier keywords, the parser peeks `Ident`, reads its string value,
and looks it up in `keyword_to_role`. For Rust-token keywords, the parser
uses the standard `syn` crate `Token![]` macro for peeking. The
`ConnectiveMap` stores both forms uniformly as strings; the peek strategy is
determined at parse time by checking whether the keyword string corresponds
to a known Rust punctuation token.

The recursive descent structure remains unchanged: `parse_pred_implies()`
still calls `parse_pred_or()`, which calls `parse_pred_and()`, which calls
`parse_pred_not()`, which calls `parse_pred_atom()`. Only the
token-matching logic at each precedence level is parameterized by the map.

**Validation.** When `connectives {}` is present (i.e., `Some`), two
validation rules apply during parsing:

1. **No duplicate keywords across roles.** Each keyword string must map to
   exactly one `ConnectiveRole`. If the same keyword is declared for
   multiple roles, the parser emits an error:

   ```text
   error[CONN01]: keyword "and" is mapped to multiple connective roles
     --> src/main.rs:12:9
      |
   12 |     and = "and";
      |           ^^^^^ first mapped to `And` here
   ...
   15 |     or  = "and";
      |           ^^^^^ also mapped to `Or` here
   ```

2. **Unlisted connective rejection.** When a guard expression uses a
   connective token that is not in the map, the parser emits an error
   suggesting that the keyword be added to the `connectives {}` block:

   ```text
   error[CONN02]: unrecognized connective keyword `||` in guard expression
     --> src/main.rs:42:20
      |
   42 |     guard(eq(x, y) || gt(x, z))
      |                    ^^ not declared in `connectives {}`
      |
      = help: add `or = "||";` to the `connectives {}` block
      = note: declared connectives: and = "&&", not = "~"
   ```

   This validation fires only when `connectives {}` is explicitly provided.
   When the block is absent (open-world default), all standard connective
   tokens are accepted without restriction.

---

## 3. Core Principles — Terms as Patterns

### First-Order Matching

In a reflective calculus, **terms serve as their own patterns**. A term with
free variables is a pattern: matching a concrete (ground) term against it
binds the free variables to the corresponding sub-terms.

This is **first-order matching**, not unification. The distinction is
fundamental to the system's complexity guarantees and correctness model:
first-order matching is one-directional (ground term vs pattern), deterministic
(no backtracking), and linear in pattern size. Unification is bidirectional
(both inputs may contain variables), may require path compression, and
returns a most general unifier rather than a simple binding. In the guarded
Comm rule, the received value is always ground (it is a concrete term sent
on a channel), so first-order matching suffices and provides the tighter
complexity bound.

| Property                   | First-Order Matching           | Unification                        |
|----------------------------|--------------------------------|------------------------------------|
| Variables in concrete term | None (ground)                  | Allowed                            |
| Variables in pattern       | Free variables → binding sites | Free variables                     |
| Result                     | `(σ | ⊥)` (match or fail)      | `(σ | ⊥)` (most general unifier)   |
| Complexity                 | O(\|pattern\|)                 | O(n · α(n)) with path compression  |

The type signature below formalizes the matching contract. The `T_ground`
parameter is a term with no free variables (the received value); `T_pattern`
may contain free variables at binding positions. The `Option` return type
encodes the two-outcome semantics: `Some(σ)` on successful decomposition,
`None` on constructor clash or arity mismatch. The substitution `σ` maps
each free variable in the pattern to the corresponding sub-term of the
ground term, partitioned by natural category (§3 "Natural Categories").

```
match : (T_ground, T_pattern) → (σ | ⊥)
  where σ : Var → Term
```

The concrete term has no variables; only the pattern does. This asymmetry
is what makes the function O(|pattern|) rather than O(n · α(n)) — no occurs
check or variable chasing is needed. The design generalizes to any language
defined with MeTTaIL, not just the rho-calculus; see §7A "Unification" for
where bidirectional matching is used (compile-time overlap analysis, not
runtime Comm rule evaluation).

### Natural Categories

The guard `@(x!(y))` is the Name `NQuote(POutput(NVar(x), PVar(y)))`. Matching
the concrete Name `@(a!(body))` against this pattern descends through `NQuote`,
then matches the Proc `a!(body)` against `POutput(NVar(x), PVar(y))`, yielding:

- `x → a` (Name, from the Name-typed position)
- `y → body` (Proc, from the Proc-typed position)

Bindings preserve their **natural category**: Name-position variables bind
Names; Proc-position variables bind Procs.

**Natural-category property.** The following invariant captures the
category-preserving nature of the match function. The intuition is that
a variable declared in a Name-typed position (like the channel slot of
`POutput`) always binds a Name value, never a Proc — the binding respects
the syntactic position's declared category. This property is enforced
structurally by the generated `match_pattern` code (§5): each arm dispatches
to the category-appropriate constructor (`MatchBindings::name` for NVar,
`MatchBindings::proc` for PVar). The theoretical basis is the sorted
first-order matching of multi-sorted algebras — each sort (category) is
closed under substitution.

```
∀v ∈ dom(σ). category(v) = category(σ(v))
```

This invariant ensures type safety of the two-pass substitution below:
`multi_substitute_name` only encounters Name values, and `multi_substitute`
only encounters Proc values. It generalizes to any language — not just
rho-calculus with its quoting convention — because the category assignment
is derived from the `language!` macro's `terms { }` declaration, not from
any calculus-specific semantics.

### Two-Pass Substitution

Natural-category bindings require **two-pass substitution** on the continuation:

1. **`multi_substitute_name`** — replaces `NVar` occurrences (Name variables
   like `x`) with their Name values. This is cross-category: Name
   substitutions in a Proc body.
2. **`multi_substitute`** — replaces `PVar` occurrences (Proc variables like
   `y`) with their Proc values. This is same-category: Proc substitutions in
   a Proc body.

Both methods are already generated by the `language!` macro. No new
substitution infrastructure is needed — only the two-pass dispatch. The
passes are disjoint (NVar vs PVar targets), so their order is irrelevant.

### Consequence for Continuation Syntax

The continuation uses variables at their natural types, with explicit quoting
and dropping to cross categories. The intuition is that the rho-calculus
reflective operators `@` (quote, Proc→Name) and `*` (drop, Name→Proc) are
the ONLY category-crossing mechanisms — the guard design respects this
discipline rather than introducing implicit coercions. The rationale is
that explicit crossings make the programmer's intent visible and maintain
the reflective structure's formal properties (Meredith & Radestock, 2005).

```
(n ? @(x!(y))).{ @(y)!(*(x)) }
                  ↑       ↑
                  │       Name x, dropped to Proc via *
                  Proc y, quoted to Name via @
```

`@(y)` wraps the Proc variable `y` in a quote, producing a Name — correct
because `y` IS a Proc. `*(x)` drops the Name variable `x` to a Proc —
correct because `x` IS a Name. This explicit crossing convention eliminates
an entire class of category errors at the source level and ensures that the
two-pass substitution (§3 "Two-Pass Substitution") encounters only same-
category replacements in each pass.

### Match Descent Diagram

The following diagram traces the recursive descent of `match_pattern_name`
through a concrete example. Read it as two parallel trees — pattern (left) and
concrete term (right) — with matching proceeding top-down through aligned
constructors. At each level, the matching function checks constructor equality
(e.g., `NQuote` = `NQuote`) and recurses into children. When it reaches a
free variable in the pattern (`NVar(x)` or `PVar(y)`), it produces a binding
at the variable's natural category. This descent corresponds to the "Regular"
case of the match recursion equations (§5).

```
Pattern: @(x!(y))             Concrete: @(a!(body))

       NQuote                         NQuote
         │                              │
       POutput                        POutput
        ╱    ╲                        ╱      ╲
   NVar(x)  PVar(y)            a(Name)  body(Proc)
      │        │                  │          │
      └──match─┘                  └───bind───┘
       x ↦ a                      y ↦ body
       (Name)                     (Proc)
```

> **Citation:** Baader, F. & Snyder, W. "Unification Theory." In
> *Handbook of Automated Reasoning*, vol. 1, ch. 8, pp. 445–533.
> Elsevier, 2001.

---

## 4. Term Representation — PGuardedInput

### Constructor Declaration

The `PGuardedInput` constructor is declared in the `language!` macro's
`terms { }` block. The declaration uses the macro's term specification
syntax: field names with type annotations, caret-bracket binder notation
(`^[xs]` for multi-binder scopes), and a surface syntax template after `|-`.
The rationale for encoding the guard as a scoped Name (not a raw Name) is
that the guard's free variables must be protected from outer substitutions
by De Bruijn encoding (de Bruijn, 1972) — the same reason `PInputs` uses
scoped bodies. The `[Name* -> Name]` type signature indicates a multi-binder
scope (`Name*` means zero or more Name binders) whose body is a `Name` (the
guard pattern).

```rust
PGuardedInput . n:Name, ^[xs].guard:[Name* -> Name], ^[ys].p:[Name* -> Proc]
|- "(" n "?" guard ")" "." "{" p "}" : Proc ;
```

The declaration has three semantic fields (channel, guard scope, continuation
scope) but the generated enum variant has four fields because the parser
inserts the `Vec<BehavioralPred>` between the guard and continuation scopes
when behavioral predicates are present in the source text. The `TermParam::
GuardBody` variant in the macro's grammar module (§10) detects this
constructor shape and triggers the specialized guard codegen path.

The generated Rust enum variant maps each declaration field to a concrete
Rust type. The `Box<Name>` channel field is unscoped (it is a simple Name
reference, not a pattern with binders). The two `Scope` fields wrap the
guard pattern and continuation body under independent binder vectors, and
the `Vec<BehavioralPred>` sits between them as the behavioral predicate list.
This field ordering mirrors the surface syntax: channel, then guard, then
predicates, then body.

```rust
PGuardedInput(
    Box<Name>,                                   // channel
    Scope<Vec<Binder<String>>, Box<Name>>,       // guard pattern
    Vec<BehavioralPred>,                         // behavioral predicates
    Scope<Vec<Binder<String>>, Box<Proc>>,       // continuation
)
```

The `Scope<Vec<Binder<String>>, Box<T>>` type is the moniker library's
scoping mechanism: `Vec<Binder<String>>` lists the bound variables (by name),
and `Box<T>` is the body in which those variables are De Bruijn-encoded.
Calling `.unbind()` on a Scope produces fresh `FreeVar<String>` values with
the original `pretty_name`s, while `.inner()` returns the raw body with
`BoundVar` indices preserved (§5 "Iterative Work Stack Architecture" explains
when each is appropriate).

### Why the Guard is a Name

The guard is a **Name** pattern — it matches the received Name `@(q)`, not the
raw Proc `q`. This is precise: in the rho-calculus, the value available after
reception is `@(q)` (a Name), so the guard pattern should be a Name. The
matching entry point is therefore `match_pattern_name`, not `match_pattern`.
The recursion naturally descends through `NQuote` into the Proc level.

### Why Two Scopes

The guard pattern and the continuation share the same bound variables (the
pattern's free variables). Both must be protected from outer substitutions
by `Scope`. The following example illustrates why: without scoping, an outer
`new` binding for `x` could capture the guard variables `y` and `z` during
substitution, violating alpha-equivalence. The theoretical basis is Barendregt's
variable convention — bound variables must be distinct from free variables in
the surrounding context, and De Bruijn encoding enforces this mechanically.

```
new(x, (x ? @(y!(z))).{@(z)!(*(y))})
```

Here `x` is bound by `new`. The guard variables `y, z` must not be affected
by any outer substitution for `x`. Both Scopes independently protect `y` and
`z` via De Bruijn encoding, converting them to `BoundVar` indices during
`close_term` and back to fresh `FreeVar`s during `unbind()`.

At Comm time, we unbind both Scopes independently, obtaining different fresh
`FreeVar`s but connecting them by position/name. The rationale for
independent unbinding (rather than sharing a single set of fresh variables)
is that the moniker library's `unbind()` is a consuming operation — each call
generates globally unique `FreeVar`s. The connection between guard and
continuation binders is established by the parser invariant: both binder
vectors are built from the same left-to-right, depth-first traversal of the
guard pattern's free variables (§9.7).

```
unbind(guard_scope: Scope, cont_scope: Scope) → ((Binder[], Term), (Binder[], Term))
  (guard_binders, guard_body) ← unbind(guard_scope)
  (cont_binders, cont_body)  ← unbind(cont_scope)
```

The positional correspondence `guard_binders[i] ↔ cont_binders[i]` is
guaranteed by the parser: both `Scope`s are constructed with the same binder
list in the same order. The `.clone()` before `.unbind()` is necessary because
`unbind()` consumes the Scope. The generated Comm rule (§6) uses `pretty_name`
matching to connect guard bindings to continuation variables, making the code
robust to the specific `FreeVar` identities produced by each `unbind()` call.

### Dual-Scope Structure Diagram

The following diagram shows the internal AST structure of a concrete
`PGuardedInput` node for the guard `@(x!(y)) where path(y, {})`. Read it as a
tree: the four fields (channel, guard scope, predicates, continuation scope)
are children of the `PGuardedInput` constructor. Inside each `Scope`, the
binder list `[x, y]` indicates which variables are De Bruijn-encoded in the
body. The invariant at the bottom is the structural contract that the parser
enforces and that the Comm rule (§6) depends on for correct substitution.

```
PGuardedInput
├── channel: Box<Name>             ─── n
├── guard_scope: Scope<[x,y], Box<Name>>
│     └── NQuote(POutput(NVar(x), PVar(y)))
├── preds: Vec<BehavioralPred>     ─── [path(y, {})]
└── cont_scope: Scope<[x,y], Box<Proc>>
      └── POutput(NQuote(PVar(y)), PDrop(NVar(x)))

Invariant:  |guard_scope.binders| = |cont_scope.binders|
          ∧ ∀i. guard_scope.binders[i].name = cont_scope.binders[i].name
```

The invariant has two parts: equal binder counts and name-wise correspondence.
The first ensures that the two-pass substitution (§3) produces exactly one
replacement per binder. The second ensures that `pretty_name`-based lookup in
the Comm rule's substitution loop (§6, lines connecting guard bindings to
continuation variables) resolves correctly. Violation of either part would
cause silent binding errors — the parser enforces both by constructing both
binder lists from the same free-variable extraction pass.

### Mixed-Category Binders

The binder list contains BOTH Name and Proc variables (e.g., `x: Name,
y: Proc` from `@(x!(y))`). The `Scope` mechanism is category-agnostic:
`Binder<String>` wraps `FreeVar<String>`, and `close_term`/`open_term`
traverse the entire term tree across category boundaries, handling `NVar`
and `PVar` occurrences alike. A `Scope<Vec<Binder<String>>, Box<Name>>`
correctly binds Proc variables that appear inside the Name (e.g., `PVar(y)`
inside `NQuote(POutput(_, PVar(y)))`).

### VariantKind Extension

The `PGuardedInput` constructor introduces a new `VariantKind::GuardedScope`
in the macro's variant classification ([`subst.rs`](../../macros/src/gen/term_ops/subst.rs)). This extends the
existing set (`Var`, `Literal`, `Nullary`, `Regular`, `Collection`,
`Binder`, `MultiBinder`) with a variant that handles the dual-scope
structure: a Name-typed guard scope and a Proc-typed continuation scope
sharing binders, with an interleaved `Vec<BehavioralPred>`. The code
generators for substitution, normalization, display, and `match_pattern`
dispatch on this variant to handle the guard-specific structure.

---

## 5. Pattern Matching Algorithm

### MatchBindings

Matching produces bindings of **mixed categories**. The core design insight is
that a single match may bind variables at different categories — Name-typed
variables and Proc-typed variables — and these must be accumulated into a
single result type for the Comm rule's two-pass substitution (§3). Rather
than using a generic `HashMap<String, Term>` (which would lose category
information), the generated struct has one typed field per category declared
in the `language!` definition. This preserves the natural-category invariant
(§3) at the type level: Name bindings and Proc bindings are stored in
separate vectors, eliminating category confusion at the point of use. The
struct is generated by [match_pattern.rs](../../macros/src/gen/term_ops/match_pattern.rs) alongside
the AST categories.

```rust
struct MatchBindings {
    name_bindings: Vec<(String, Name)>,
    proc_bindings: Vec<(String, Proc)>,
    // ... one field per declared category in the language definition
}
```

The `Vec<(String, T)>` representation uses the variable's `pretty_name`
(a `String`) as the key, enabling O(n) lookup by name. For typical guard
patterns with 2-5 variables, this is faster than a `HashMap` due to lower
constant factors. The `merge()` operation is O(n) concatenation, and it is
associative and commutative on disjoint variable sets — a property exploited
by the recursive matching algorithm.

`MatchBindings` supports:
- `empty()` — no bindings
- `name(var, val)` — single Name binding
- `proc(var, val)` — single Proc binding (one constructor per category)
- `merge(other)` — concatenation
- `get_name(var_name: String) → (Name | ⊥)` — typed lookup (one per category)
- `get_proc(var_name: String) → (Proc | ⊥)` — typed lookup (one per category)

### Formal Specification

For each category `Cat` declared in the `language!` definition, the macro
generates a matching method on the category's Rust enum type. The method
follows the first-order matching contract established in §3: `self` (the
receiver) is the ground term with no free variables, and `pattern` is the
term that may contain free variables at binding positions. The rationale for
generating separate methods per category (rather than a single generic
function) is that each category has its own constructor set — the `match`
arms must exhaustively cover the category's enum variants, and Rust's type
system enforces this at compile time. The `_name` suffix on
`match_pattern_name` distinguishes the Name-category method from the
Proc-category method in the same module.

```rust
impl Proc {
    fn match_pattern(&self, pattern: &Proc) -> Option<MatchBindings> { ... }
}

impl Name {
    fn match_pattern_name(&self, pattern: &Name) -> Option<MatchBindings> { ... }
}
```

The `(σ | ⊥)` return type encodes the matching semantics:
`Some(bindings)` when all constructors align and all free variables bind
successfully, `None` on any constructor clash or arity mismatch. The method
bodies are generated by `generate_match_pattern()` in
[match_pattern.rs](../../macros/src/gen/term_ops/match_pattern.rs) and consist of a `match` block
over `(self, pattern)` pairs, with one arm per variant kind (§5 "Generation
Rules per Variant Kind").

### Match Recursion Equations

The following four equations define the inductive structure of first-order
matching. They form a complete case analysis over the possible pattern shapes:
constructors with matching tags (recursive descent), free variables (binding),
binders (scope opening plus body comparison), and constructor clashes
(failure). These equations are the formal specification that the generated
Rust code implements. The theoretical basis is the standard first-order
matching algorithm for term algebras (Baader & Snyder, 2001, §8.2): the
`merge` operation corresponds to the union of substitutions, and the
`category(v)` annotation is the multi-sorted extension that preserves
natural categories (§3).

```
match(C(t₁, …, tₙ), C(π₁, …, πₙ))  = merge(match(t₁, π₁), …, match(tₙ, πₙ))
match(t, Var(v))                       = {v ↦ t}  at category(v)
match(B(f̄, b̄, t), B(f̄', b̄', π))     = merge(match(f̄, f̄'), match(t, π))
                                           if |b̄| = |b̄'|     (binder arity)
                                         None  if |b̄| ≠ |b̄'|
match(C₁(…), C₂(…))  where C₁ ≠ C₂   = None     (constructor clash)
```

The binder equation reflects how scoped variants are matched. The binder names
b̄ are scope-introducing positions — they are NOT free variables and produce no
bindings in σ. Pre-scope fields f̄ (e.g., the channel names in `PInputs`) are
matched normally and may produce bindings. Bodies are compared via
`scope.inner()` + `unsafe_body`, which preserves `BoundVar`s (de Bruijn
indices) rather than freshening — this gives alpha-invariant structural
comparison. For single Binder variants the arity check is trivially satisfied
(both sides have exactly one binder). Contrast with the Comm rule (§6), which
uses `unbind()` on the guard scope to produce `FreeVar`s for top-level pattern
matching — see §6 line 832 for the rationale.

### Generation Rules per Variant Kind

The following table summarizes how the code generator handles each variant
classification. Each row corresponds to a `VariantKind` in
[match_pattern.rs](../../macros/src/gen/term_ops/match_pattern.rs). The match rule column describes
the algorithmic strategy, and the result column shows what `MatchBindings`
value is produced on success. The table is read as a dispatch table: the
code generator inspects each variant's `VariantKind` and emits the
corresponding match arm. The subsequent "Generated Code Examples" subsection
shows the concrete Rust code for each row.

```
┌──────────────┬───────────────────┬─────────────────────────────────────┐
│ Pattern Kind │ Match Rule        │ Result                              │
├──────────────┼───────────────────┼─────────────────────────────────────┤
│ Variable     │ Bind at category  │ MatchBindings::{name,proc}(v, t)    │
│ Nullary      │ Exact equality    │ MatchBindings::empty()              │
│ Regular      │ Recurse fields    │ merge(match(f₁), …, match(fₙ))      │
│ Literal      │ Value equality    │ MatchBindings::empty() if eq        │
│ Collection   │ Order-independent │ AC-match via re-entrant engine      │
│ Binder/Scope │ Arity + open +    │ merge(pre_scope_match, body_match)  │
│              │ recurse body      │ (binder names are scope — not in σ) │
└──────────────┴───────────────────┴─────────────────────────────────────┘
```

The six rows partition all possible pattern shapes. Variable and Literal are
the base cases (no recursion); Nullary is a degenerate base case (tag
equality only); Regular is the main recursive case; Collection requires
order-independent sub-matching; and Binder/Scope combines pre-scope field
matching with scope opening and body comparison.

### Generated Code Examples

**Variable (pattern is a variable).** In first-order matching, a free variable
in the pattern acts as a universal acceptor — it matches any ground term and
binds to it. This is the variable rule from the match recursion equations
above: `match(t, Var(v)) = {v ↦ t} at category(v)`. The intuition is that
a pattern variable is a "hole" that accepts whatever subterm occupies the
corresponding position in the ground term. The binding is recorded at the
variable's natural category: a `PVar` (Proc-level free variable) produces a
Proc binding, while an `NVar` (Name-level free variable) produces a Name
binding. This category-aware dispatch is why `MatchBindings` stores separate
`name_bindings` and `proc_bindings` vectors — each variable binds at its
declaration category regardless of where in the term tree the match occurs.

The generated code destructures the `OrdVar(Var::Free(fv))` wrapper to access
the `FreeVar`, extracts the variable's `pretty_name` (the user-visible name
from the source text), and constructs a single-entry `MatchBindings`. The
wildcard `_` on the ground side means any constructor matches:

```
match_var(ground: Term, PVar(x): Term) → (σ | ⊥)
  return { proc_bindings: [(name(x), ground)] }

match_var(ground: Term, NVar(x): Term) → (σ | ⊥)
  return { name_bindings: [(name(x), ground)] }
```

The cost is O(1) per variable binding — one clone of the ground term and one
`MatchBindings` constructor call. The `pretty_name.clone()?` returns `None`
if the `FreeVar` lacks a pretty name (a defensive check — in practice, all
user-declared variables have names), which propagates as a match failure.
These arms appear first in the generated match block, ensuring that any
pattern consisting solely of a free variable is handled before
constructor-specific arms are attempted.

**Nullary (no fields).** Nullary constructors (zero-argument variants like
`PZero` or `PNil`) represent the base case of the matching recursion.
Matching is pure tag equality: both sides must be the same nullary
constructor. This corresponds to `match(C(), C()) = empty` in the recursion
equations — no sub-terms to recurse into, no variables to bind. The
theoretical basis is the ground term identity: two nullary constructors are
equal iff they have the same tag.

```
match_nullary(C(): Term, C(): Term) → (σ | ⊥)
  if tag(ground) = tag(pattern) then return ∅;  else return ⊥
```

The cost is O(1) — a single discriminant comparison. Empty `MatchBindings`
are returned because nullary constructors contain no sub-terms and therefore
no variable binding sites.

**Regular (constructor with fields).** The regular case implements recursive
descent through constructor fields, corresponding to the first recursion
equation: `match(C(t₁, …, tₙ), C(π₁, …, πₙ)) = merge(match(t₁, π₁), …,
match(tₙ, πₙ))`. The intuition is that when two terms share the same
constructor, their corresponding fields are matched pairwise. The `?`
operator provides early exit on the first failing sub-match (short-circuit
evaluation). Cross-category dispatch occurs naturally: Name-typed fields
call `match_pattern_name`, Proc-typed fields call `match_pattern`, and the
returned `MatchBindings` are merged.

```
match_regular(C(t₁,…,tₙ): Term, C(π₁,…,πₙ): Term) → (σ | ⊥)
  σ ← ∅
  ∀ i ∈ 1…n: σ ← merge(σ, match(tᵢ, πᵢ))           ▷ cross-category dispatch
  return σ
```

The cost is O(|fields|) per constructor level, giving O(|pattern|) total
across the full descent. The `**n1` double-dereference unboxes the
`Box<Name>` field. The `merge()` call concatenates the Name and Proc binding
vectors from the field-level matches. Cross-category recursion
(`match_pattern_name` for Name fields, `match_pattern` for Proc) is what
enables patterns like `@(x!(y))` to collect bindings across the Name-Proc
boundary.

**Literal.** Literal values (integers, strings, booleans) are matched by
value equality rather than constructor decomposition. This is the primitive
base case for non-algebraic types: two literals match iff they hold the same
value. No bindings are produced because literals have no sub-terms. The
match guard `if v1 == v2` performs the equality test before entering the
arm body.

```
match_literal(Lit(v₁): Term, Lit(v₂): Term) → (σ | ⊥)
  if v₁ = v₂ then return ∅;  else return ⊥
```

The cost is O(1) for integer and boolean literals, O(|string|) for string
literals. Empty `MatchBindings` are returned because literals, like nullary
constructors, contain no variable binding sites.

**Collection.** Collection patterns (HashBag, Vec, HashSet) use
order-independent matching — the key challenge is that multiset elements have
no fixed position, so the matcher must find an assignment from pattern
elements to ground elements. HashBag elements are matched regardless of
position via a `claimed` bitvector: non-variable pattern elements are matched
first (finding exact structural matches among unclaimed ground elements),
then variable pattern elements bind to remaining unclaimed elements. Vec
elements are matched positionally (`g_vec[i].match_pattern(p_vec[i])`).
HashSet elements match like HashBag without multiplicity. Each element
sub-match re-enters `match_pattern()` via Thread-Local Storage (TLS), which is bounded by
collection size, not nesting depth. The theoretical basis is AC-matching for
commutative collections — see §8 (AC-Matching for Collection Guards) for the
full partition enumeration algorithm and its LogicT integration.

**Binder/Scope.** Binder patterns open both ground and pattern scopes via
`inner()` (NOT `unbind()` — no freshening), then match bodies structurally
using `unsafe_body`. The rationale for `inner()` over `unbind()` is that
structural comparison requires De Bruijn indices to be preserved — two terms
are alpha-equivalent iff they have identical `BoundVar` structure after scope
opening. Using `unbind()` would generate fresh `FreeVar`s, which would differ
between the ground and pattern terms and cause spurious mismatches. Binder
names (`unsafe_pattern`) are scope-introducing positions and are NEVER
extracted into `MatchBindings`. See §5 "Iterative Work Stack Architecture"
for the full algorithm.

**MultiBinder.** The rhocalc `PNew . ^[xs].p:[Name* -> Proc]` generates
`PNew(Scope<Vec<Binder<String>>, Box<Proc>>)` — a single argument that is the
scope itself, with no pre-scope fields. The matching algorithm first opens
both scopes via `inner()` to access the raw `BoundVar`-encoded bodies, then
checks binder arity (the ground and pattern must have the same number of
bound variables), and finally re-enters the iterative matching engine for
body comparison. The arity check is the binder equation's precondition:
`|b̄| = |b̄'|`. The `unsafe_pattern` field contains the `Vec<Binder<String>>`
binder names, which are scope-introducing and never produce bindings in σ.

```
match_multi_binder(C(Scope(b̄, body)): Term, C(Scope(b̄', body')): Term) → (σ | ⊥)
  g ← inner(Scope(b̄, body));  p ← inner(Scope(b̄', body'))
  if |binders(g)| ≠ |binders(p)| then return ⊥
  return match(body(g), body(p))
```

The cost is O(1) for the arity check plus O(|body|) for the recursive body
match. The `inner()` call is O(1) — it returns a reference to the scope's
internal representation without cloning or freshening. The re-entrant
`match_pattern()` call on the body processes the term iteratively via the
work stack, so deeply nested `PNew` chains do not cause stack overflow.

**Single Binder with pre-scope fields.** For language definitions like
ambient `PNew . ^x.p:[Name -> Proc]`, which generates
`PNew(Scope<Binder<String>, Box<Proc>>)`, there is exactly one binder per
side, so no arity check is needed (trivially satisfied). When pre-scope
fields are present (e.g., `PInputs` with channel names before the binder),
they are matched first via re-entrant `match_pattern()` before opening the
scope. This ordering — pre-scope fields, then scope opening, then body — is
essential because pre-scope fields may contain free variables that produce
bindings, and these bindings must be accumulated before entering the body.

```
match_single_binder(C(f₁,…,fₖ, Scope(b,body)): Term, C(f₁',…,fₖ', Scope(b',body')): Term) → (σ | ⊥)
  σ ← merge(match(f₁,f₁'), …, match(fₖ,fₖ'))       ▷ pre-scope fields first
  g ← inner(Scope(b,body));  p ← inner(Scope(b',body'))
  return merge(σ, match(body(g), body(p)))
```

The code structure mirrors the MultiBinder case but without the arity check.
Pre-scope field matching (when present) would appear before the `inner()`
calls, producing bindings that are merged with the body match result.

### Cross-Category Consistency

Both `match_pattern` and `match_pattern_name` return the same type
(`(σ | ⊥)`), enabling seamless cross-category recursion. The
intuition is that matching flows freely between categories — a Name pattern
may contain Proc sub-terms (via `NQuote`), and a Proc pattern may contain
Name sub-terms (via `POutput`'s channel field). The uniform return type
allows the recursion to cross category boundaries without type conversion.
This is the design's key compositionality property, and it is why a single
`MatchBindings` struct accumulates both Name and Proc entries.

```
match_pattern_name(NQuote(p_ground), NQuote(p_pattern))
    │
    └── calls match_pattern(p_ground, p_pattern)
            │
            └── calls match_pattern_name(n_ground, n_pattern)
                    │
                    └── ...
```

At every level, bindings accumulate uniformly. The following invariant
formalizes this property. The `merge()` associativity and commutativity
on disjoint variable sets ensures that the order of field recursion does
not affect the final binding set — a requirement for the iterative work
stack architecture (§5) where field processing order may differ from the
source-level left-to-right order.

```
∀ call chain C through match_pattern / match_pattern_name:
  C returns (σ | ⊥)
  ∧ MatchBindings stores both Name and Proc bindings
  ∧ merge() is associative and commutative on disjoint variable sets
```

This ensures that a pattern like `@(x!(y))`, which crosses from Name (`@`)
to Proc (`x!(y)`) and back to Name (`x`) and Proc (`y`), collects all
bindings regardless of the category at which matching began.

### Generated Code Location

Module: [match_pattern.rs](../../macros/src/gen/term_ops/match_pattern.rs)

Called from `generate_all()` in [mod.rs](../../macros/src/gen/mod.rs), alongside
substitution and normalization generation.

### Iterative Work Stack Architecture

Pattern matching uses an explicit work stack (`Vec<MatchTask>`) instead of
recursive function calls, providing stack safety for arbitrarily deep terms
(100K+ nesting depth). This mirrors the trampoline parser design.

**`MatchTask` enum.** The work stack uses a heterogeneous enum rather than a
generic `(Box<dyn Term>, Box<dyn Term>)` pair. The rationale is that each
category has its own Rust type (`Proc`, `Name`, etc.), and a heterogeneous
enum preserves type safety at each dispatch point — when the engine pops a
`MatchProc` task, it knows both values are `Proc`s and can dispatch directly
to Proc-specific match arms. This design mirrors the trampoline parser's
`Frame_Cat` enum (§ "Trampoline Parser"), which uses the same one-variant-per-
category pattern for stack-safe parsing. The `usize` position field
(not shown) tracks the current field index within Regular variants for
resumption after pushing sub-tasks.

```rust
enum MatchTask {
    MatchProc(Proc, Proc),
    MatchName(Name, Name),
}
```

Cross-category recursion (Proc → Name → Proc) is handled naturally: when
processing a `MatchProc` task with a `Name` field, the handler pushes
`MatchTask::MatchName(ground_field, pattern_field)` onto the stack. The
cost of the enum overhead is one discriminant per stack entry — negligible
compared to the term cloning cost.

**Thread-local pooling:** `Cell<Vec<MatchTask>>` with take/set at entry/exit.
Zero allocation in steady state after the first call. This is the same TLS
pooling pattern used by the trampoline parser.

**Algorithm.** The following pseudocode describes the iterative work stack
algorithm. The key insight is that all recursive structure is converted to
explicit stack operations: the Regular case pushes child tasks in LIFO order
(so they are processed left-to-right), while Collection and Binder cases use
synchronous re-entrant calls because they need immediate sub-match results.
The theoretical basis is the standard defunctionalization of recursive descent
— each recursive call becomes a push operation, and the while loop replaces
the call stack. This transformation guarantees stack safety for terms of
arbitrary depth (100K+ nesting verified in tests) at the cost of heap
allocation for the explicit stack.

```
iterative_match(ground: Term, pattern: Term) → (σ | ⊥)
  σ ← ∅;  stack ← [MatchTask(ground, pattern)]
  while stack ≠ ∅ do
    task ← pop(stack)
    case task of
      FreeVar(x)  → σ ← σ ∪ {x ↦ ground(task)}
      Var/Literal/Nullary → if ground ≠ pattern then return ⊥
      Regular(C(t₁,…,tₙ), C(π₁,…,πₙ)) →
        ∀ i ∈ {n, …, 1}: push(stack, MatchTask(tᵢ, πᵢ))
      Collection → σ ← merge(σ, match(elements))
      Binder(Scope(b̄, body), Scope(b̄', body')) →
        σ_pre ← match(pre-scope fields)
        g ← inner(Scope(b̄, body));  p ← inner(Scope(b̄', body'))
        if |binders(g)| ≠ |binders(p)| then return ⊥
        σ ← merge(σ, σ_pre, match(body(g), body(p)))
      Mismatch → return ⊥
  return σ
```

The algorithm is O(|pattern|) for Regular variants (one push per field) and
O(|collection| · |element|) for Collection variants (one re-entrant call per
element). The re-entrant calls are bounded by collection size, not nesting
depth — deep nesting within each element is handled iteratively by the inner
engine call.

**Re-entrancy for Collections/Binders.** Collection matching requires
synchronous sub-match results (to determine which ground element to claim).
These arms call `match_pattern()` per element, which re-enters the iterative
engine via TLS (gets a fresh stack since the `Cell` is taken). The re-entry
depth is bounded by the maximum collection nesting level (typically 1-2), not
by term depth — this is what makes the design stack-safe even for deeply
nested terms inside collections.

### Collection Variant Matching

Collection variants (PPar bags, lists, sets) use order-independent matching.
The core challenge is that multiset elements have no fixed position — matching
`{x, PSend(a,b), y}` against `{P, Q, R}` requires finding an assignment that
satisfies all structural constraints. The algorithm uses a deterministic
strategy: non-variable pattern elements are matched first (they have stricter
requirements and produce earlier failure), then variable elements bind to
remaining unclaimed ground elements. This is not full AC-unification (which
is NP-complete in general) but a restricted form that exploits the first-order
matching invariant: the ground side has no variables, so each non-variable
pattern element either has a unique structural match or fails.

**HashBag (multiset):** Pattern elements are matched against ground elements
regardless of order. Each pattern element is classified:
- **Non-variable:** Finds an exact structural match among unclaimed ground elements
- **Variable (FreeVar):** Binds to any unclaimed ground element

A `claimed` bitvector tracks which ground elements have been matched. If any
pattern element fails to find a match, the entire match fails.

The following trace shows the matching of a 3-element ground bag against a
pattern with one non-variable element and two variable elements. The
non-variable `PSend(a, b)` is tried first against all ground elements; once
claimed, the variables `x` and `y` bind to the remaining unclaimed elements
in iteration order.

```
match_pattern(PPar({P, Q, R}), PPar({x, PSend(a, b), y}))
  → claimed = [false, false, false]
  → try PSend(a,b) against {P, Q, R}: find structural match → claim that element
  → bind x to first unclaimed ground element
  → bind y to remaining unclaimed ground element
  → MatchBindings { proc: {x→P_matched, y→R_matched}, name: {a→..., b→...} }
```

The cost is O(|pattern| · |ground|) for non-variable elements (each is tried
against all unclaimed ground elements) plus O(|variables|) for variable
elements (each binds to the next unclaimed element). For the common case of
1-2 non-variable elements in a small bag, this is effectively linear.

**Vec (ordered):** Position-wise matching — `g_vec[i].match_pattern(p_vec[i])`
for each position. Length must match.

**HashSet:** Same as HashBag but without multiplicity tracking.

### Binder Variant Matching

Binder variants match under the binder by opening both scopes via `inner()`
(structural access — NO freshening) and matching bodies via `unsafe_body`.
The key insight is that `inner()` preserves De Bruijn indices (`BoundVar`s),
making the comparison alpha-invariant: `new(x) in { x!(P) }` and
`new(y) in { y!(P) }` both have `BoundVar(0)` at the binder position after
scope opening, so they match structurally. This is the standard
alpha-equivalence check via De Bruijn representation (de Bruijn, 1972).

**MultiBinder (canonical: rhocalc PNew).** The following trace shows the
step-by-step matching of two `PNew` terms. The arity check ensures both
sides introduce the same number of bound variables — a `new(x, y)` pattern
must not match a `new(z)` ground term. After the arity check, the body
comparison proceeds by re-entering the iterative engine.

Language definition: `PNew . ^[xs].p:[Name* -> Proc]`
Generated type: `PNew(Scope<Vec<Binder<String>>, Box<Proc>>)` — one argument
(the scope itself), no pre-scope fields.

```
match_pattern(PNew(scope_g), PNew(scope_p))
  → g_inner = scope_g.inner()
  → p_inner = scope_p.inner()
  → if |g_inner.unsafe_pattern| ≠ |p_inner.unsafe_pattern|: return None
  → (*g_inner.unsafe_body).match_pattern(&*p_inner.unsafe_body)
  → accumulate bindings from body match
```

The cost is O(1) for the `inner()` calls and arity check, plus O(|body|) for
the recursive body match. Note that binder names themselves are NOT compared
— only their count. Name comparison would break alpha-equivalence.

The `unsafe_pattern` field contains the `Vec<Binder<String>>` — the binder
names. These are scope-introducing positions and are NEVER dispatched through
the match engine's variable-catches-all arm. Although `Binder<String>` wraps
`FreeVar<String>`, the codegen only checks their count for arity and never
extracts them into `MatchBindings`. The variable-catches-all arm handles
`PVar(OrdVar(Var::Free(fv)))` and `NVar(OrdVar(Var::Free(fv)))` — term-level
free variables, not scope binders.

**Alpha-equivalence.** Because `inner()` preserves `BoundVar`s (de Bruijn
indices) rather than freshening, `new(x) in { x!(P) }` correctly matches
`new(y) in { y!(P) }` — both have the same `BoundVar` structure after scope
opening.

**Single Binder (e.g., ambient PNew).**
Language definition: `PNew . ^x.p:[Name -> Proc]`
Generated type: `PNew(Scope<Binder<String>, Box<Proc>>)` — exactly one binder
per side, so no arity check is needed.

**Pre-scope fields (e.g., PInputs).**
Language definition: `PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]`
When pre-scope fields are present, they are matched first via re-entrant
`match_pattern()` before the scope is opened. The generated code matches
each pre-scope field, then opens the scope, then matches the body.

**Distinction from the Comm rule (§6).** The `match_pattern` codegen uses
`inner()` — raw structural access with `BoundVar`s preserved — because it
performs structural comparison (two terms must have the same shape). The Comm
rule uses `unbind()` — which freshens `BoundVar`s into `FreeVar`s — because
it needs `FreeVar`s with `pretty_name`s for top-level pattern matching against
the guard. See §6 (lines 832–838) for the full rationale.

### Regular Variants with Collection Fields

When a Regular variant (non-Collection, non-Binder) has a field typed as a
collection (e.g., `MApply(Name, Vec<Proc>)`), the variant arm returns `None`
— element-wise matching is not meaningful for heterogeneous container types.
These variants require the Collection variant classification for proper matching.

---

## 6. The Guarded Comm Rule

### Auto-Generation

When the language defines a `PGuardedInput` constructor, the macro
auto-generates a corresponding rewrite rule. The user does not write this
rule in the `rewrites {}` block. Detection occurs in
[rules.rs](../../macros/src/logic/rules.rs) by inspecting the `TermParam::GuardBody` variant.

### Generated Datalog (Structural-Only)

The generated Datalog rule is the heart of the predicated types runtime. It
implements the guarded Comm rule from §1's formal definitions as an Ascent
rewrite rule, translating the mathematical equation into executable Rust code
that fires during semi-naive fixpoint evaluation. The rule has four logical
phases: (1) equational matching and bag iteration — finding a send/receive
pair on the same channel within a `PPar` bag; (2) channel matching and
received Name construction — building the Name `@(q)` from the sent process;
(3) guard unbinding and first-order matching — converting the guard scope's
De Bruijn-encoded body to `FreeVar`s and matching against the received Name;
(4) two-pass substitution into the continuation — partitioning match results
by category and applying separate Name and Proc substitutions.

The rule is structurally modeled after the existing `PInputs` Comm rule
but differs in three critical ways: it uses `match_pattern_name` (not
`unsafe_body`), it unbinds the guard scope to produce `FreeVar`s (not just
raw body access), and it performs two-pass substitution (not single-category).
The `rw_proc` head relation means this produces a rewrite: the original
term `s_orig` rewrites to `t`. The `eq_proc(s_orig, s)` clause respects
the equational theory — the rule fires on any term equivalent to the LHS.

```rust
rw_proc(s_orig.clone(), t) <--
    // Phase 1: equational matching and bag iteration
    eq_proc(s_orig, s),
    if let Proc::PPar(ref bag) = s,

    for (inp, _) in bag.iter(),
    if let Proc::PGuardedInput(ref channel, ref guard_scope,
                                ref _preds, ref cont_scope) = inp,

    for (out, _) in bag.iter(),
    if let Proc::POutput(ref out_channel, ref sent_proc) = out,
    if channel == out_channel,

    // Phase 2: received Name construction
    let received_name = Name::NQuote(sent_proc.clone()),

    // Phase 3: guard unbinding and first-order matching
    let (guard_binders, guard_body) = guard_scope.clone().unbind(),
    if let Some(match_bindings) = received_name.match_pattern_name(&*guard_body),

    // Phase 4: bag residual after consuming send/receive pair
    let rest = {
        let mut bag = bag.clone();
        bag.remove(&inp);
        bag.remove(&out);
        bag
    },

    // Phase 4 (cont.): two-pass substitution into continuation
    let t = {
        let (cont_binders, cont_body) = cont_scope.clone().unbind();

        let name_vars: Vec<&FreeVar<String>> = cont_binders.iter()
            .filter(|b| {
                let n = b.0.pretty_name.as_ref()
                    .expect("binder must have pretty_name");
                match_bindings.name_bindings.iter().any(|(k, _)| k == n)
            })
            .map(|b| &b.0)
            .collect();
        let name_repls: Vec<Name> = name_vars.iter().map(|fv| {
            let n = fv.pretty_name.as_ref()
                .expect("freevar must have pretty_name");
            match_bindings.name_bindings.iter()
                .find(|(k, _)| k == n)
                .expect("name binding must exist").1.clone()
        }).collect();

        let proc_vars: Vec<&FreeVar<String>> = cont_binders.iter()
            .filter(|b| {
                let n = b.0.pretty_name.as_ref()
                    .expect("binder must have pretty_name");
                match_bindings.proc_bindings.iter().any(|(k, _)| k == n)
            })
            .map(|b| &b.0)
            .collect();
        let proc_repls: Vec<Proc> = proc_vars.iter().map(|fv| {
            let n = fv.pretty_name.as_ref()
                .expect("freevar must have pretty_name");
            match_bindings.proc_bindings.iter()
                .find(|(k, _)| k == n)
                .expect("proc binding must exist").1.clone()
        }).collect();

        let body = (*cont_body)
            .multi_substitute_name(&name_vars, &name_repls)
            .multi_substitute(&proc_vars, &proc_repls);

        Proc::PPar({
            let mut result_bag = rest;
            Proc::insert_into_ppar(&mut result_bag, body);
            result_bag
        })
    }.normalize();
```

The substitution loop connects guard binders to continuation binders by
`pretty_name` matching: for each continuation binder, it checks whether a
same-named binding exists in `match_bindings.name_bindings` (for Name pass)
or `match_bindings.proc_bindings` (for Proc pass). The `filter` + `find`
pattern is O(|binders| · |bindings|) but both sizes are typically 2-5.
The final `.normalize()` call canonicalizes the result (e.g., flattening
nested `PPar` bags), ensuring the fixpoint engine converges.

### Key Design Decisions

**Guard matching operates on Names.** The received Name `@(q)` is matched
against the guard Name pattern. The entry point is `match_pattern_name`, not
`match_pattern`. The recursion naturally descends through `NQuote` into the
Proc level.

**Guard unbinding must use `unbind()`, not `unsafe_body()`.** The existing
`PInputs` Comm rule uses `unsafe_pattern()` / `unsafe_body()` because it only
needs the binder structure and body for substitution — it never matches
against the body's variables. The guard is different: `match_pattern_name`
expects the pattern to contain `FreeVar`s (inside `PVar` / `NVar`), not De
Bruijn `BoundVar`s. Calling `unbind()` produces fresh `FreeVar`s with the
correct `pretty_name`s, which is exactly what the matching function needs.

**Two-pass substitution.** The continuation's binders include both Name and
Proc variables. After unbinding, the code partitions the match results by
category and applies `multi_substitute_name` (for NVars) and
`multi_substitute` (for PVars) sequentially. The order does not matter —
Name substitutions target NVar occurrences and Proc substitutions target
PVar occurrences; they operate on disjoint sets.

**Guard and continuation produce DIFFERENT fresh FreeVars.** Both `unbind()`
calls generate independent fresh variables, but they share the same
`pretty_name`s (by the parser invariant). The substitution loops connect
them by name.

### Formal Semantics

The following two equations formalize the generated Datalog rule above in
standard operational semantics notation. The firing condition specifies the
existential search over the `PPar` bag (the two `for` loops in the generated
code), and the result specifies the bag transformation (removing consumed
processes and inserting the substituted continuation). These equations serve
as the correctness specification against which the generated code is validated
(§9.1 "Soundness").

**Firing condition:**

```
∃(inp, out) ∈ PPar.
    inp = PGuardedInput(ch, φ_scope, [], c_scope)
  ∧ out = POutput(ch, q)
  ∧ match(unbind(φ_scope).body, NQuote(q)) = σ
```

The empty list `[]` in the `PGuardedInput` indicates no behavioral predicates
— this is the structural-only rule. When behavioral predicates are present,
the conjunction extends with `∀i. Rᵢ(resolve(aᵢ, σ)) ∈ FP` (see §8).

**Result:**

```
PPar((bag ∖ {inp, out}) ∪ {unbind(c_scope).body[σ]}).normalize()
```

The bag difference `∖ {inp, out}` removes the consumed send and receive; the
union `∪ {body[σ]}` adds the substituted continuation. The `.normalize()`
call ensures the result is in canonical form for the fixpoint engine.

### Step-by-Step Evaluation Flow

The following diagram traces the data flow through the generated Comm rule,
corresponding to the four phases identified in the code above. Read it
top-to-bottom as a pipeline: each arrow represents a computation step, and
the two exit points (`None` and `Some(σ)`) correspond to the `if let`
guard in Phase 3. The final `.normalize()` call produces the canonical form
that the Ascent engine adds to the `rw_proc` relation.

```
PPar bag
  │
  ├── Find PGuardedInput(ch, φ_scope, [], c_scope)
  ├── Find POutput(ch, q)
  │
  ▼
received ← NQuote(q)
  │
  ▼  unbind(φ_scope)
(binders, φ_body)        ← fresh FreeVars x', y'
  │
  ▼  match_pattern_name(received, φ_body)
  │
  ├── None ──────────────► rule does not fire
  └── Some(σ) ──────────►
        │
        ▼  unbind(c_scope)
        (binders, c_body)        ← fresh FreeVars x'', y''
        │
        ├── Pass 1: c_body.multi_substitute_name(σ.names)
        ├── Pass 2: result.multi_substitute(σ.procs)
        │
        ▼
        PPar(rest ∪ {body}).normalize()
```

---

## 7. Worked Example — End-to-End Trace

This section traces the complete execution of a guarded Comm rule from input
parsing through pattern matching, substitution, and normalization. The example
exercises all key mechanisms: cross-category matching (Name→Proc→Name→Proc),
natural-category bindings (`x: Name`, `y: Proc`), two-pass substitution, and
the quoting/dropping discipline. Each step corresponds to a phase of the
generated Datalog rule in §6. Following the trace verifies the correctness
claims from §9.

### Input

The input term places a guarded receive and a send in parallel on channel `n`.
The guard pattern `@(x!(y))` decomposes the received value into a channel
name `x` and a body `y`. The continuation `@(y)!(*(x))` uses both bindings
with explicit category crossings.

```
{(n ? @(x!(y))).{@(y)!(*(x))} | n!(a!({b!({}) | (b?z).{*(z)}}))}
```

### Step 1 — Parse

The guard `@(x!(y))` parses to `NQuote(POutput(NVar(x), PVar(y)))`.
Free variables: `[x: Name, y: Proc]` (left-to-right, depth-first).

Guard scope: `Scope<[x, y], Box<Name>>` over `NQuote(POutput(NVar(x), PVar(y)))`.
Continuation scope: `Scope<[x, y], Box<Proc>>` over `POutput(NQuote(PVar(y)), PDrop(NVar(x)))`.

### Step 2 — Identify Comm Pair

The `PPar` bag contains:
- `PGuardedInput(n, guard_scope, [], cont_scope)`
- `POutput(n, a!({b!({}) | (b?z).{*(z)}}))`

### Step 3 — Channel Match

Both processes use channel `n`. ✓

### Step 4 — Construct Received Name

The sent process is quoted to a Name via the `@()` operator, producing the
value that will be matched against the guard pattern. This corresponds to
`let received_name = Name::NQuote(sent_proc.clone())` in the generated code.

```
received = @(a!({b!({}) | (b?z).{*(z)}}))
         = NQuote(POutput(a, PPar({POutput(b, PZero), PInput(b, z, PDrop(NVar(z)))})))
```

### Step 5 — Unbind Guard Scope

Unbinding the guard scope converts De Bruijn-encoded bound variables to fresh
`FreeVar`s with the original `pretty_name`s. This is necessary because
`match_pattern_name` needs `FreeVar`s to produce bindings — De Bruijn
`BoundVar`s would not carry the variable names needed for the substitution
loop.

```
(binders, guard_body) = guard_scope.unbind()
guard_body = NQuote(POutput(NVar(x'), PVar(y')))
```

Fresh `FreeVar`s `x'`, `y'` replace the De Bruijn-encoded bound variables.
The primes indicate freshness — these are globally unique identifiers, not
the original source-level names (though they share the same `pretty_name`).

### Step 6 — Pattern Match

The matching descent proceeds top-down through aligned constructors, crossing
from Name to Proc at the `NQuote` boundary. At each level, the constructor
tag is compared; when a free variable is reached, a binding is produced at
the variable's natural category. This trace demonstrates the cross-category
consistency property (§5): Name and Proc bindings accumulate into a single
`MatchBindings` regardless of the matching depth.

```
match_pattern_name(received, guard_body):

  NQuote(POutput(a, {b!({})|...}))  vs  NQuote(POutput(NVar(x'), PVar(y')))
  │                                      │
  ├── NQuote: constructors match, descend into Proc
  │   POutput(a, {b!({})|...})  vs  POutput(NVar(x'), PVar(y'))
  │   │
  │   ├── Name field: a  vs  NVar(x')  →  name_bindings: [x ↦ a]
  │   └── Proc field: {b!({})|...}  vs  PVar(y')
  │       →  proc_bindings: [y ↦ {b!({}) | (b?z).{*(z)}}]
  │
  └── Result: Some(MatchBindings { name: [x→a], proc: [y→{b!({})|...}] })
```

The result has one Name binding (`x ↦ a`, from the Name-typed channel
position of `POutput`) and one Proc binding (`y ↦ {b!({})|...}`, from the
Proc-typed body position). This confirms the natural-category property:
each variable binds at the category of its declaration position.

### Step 7 — Unbind Continuation Scope

The continuation scope is unbound independently, producing a second set of
fresh `FreeVar`s. These are connected to the guard binders by `pretty_name`
matching in the substitution loop (not by identity).

```
(cont_binders, cont_body) = cont_scope.unbind()
cont_body = POutput(NQuote(PVar(y'')), PDrop(NVar(x'')))
```

Fresh `FreeVar`s `x''`, `y''` are different from `x'`, `y'` (each `unbind()`
call generates globally unique identifiers). The `pretty_name`s `"x"` and
`"y"` are shared between the two sets, enabling the name-based lookup.

### Step 8 — Two-Pass Substitution

The substitution is split into two passes by category. Pass 1 handles
Name bindings (replacing `NVar` occurrences), Pass 2 handles Proc bindings
(replacing `PVar` occurrences). The passes are disjoint: `NVar(x'')` and
`PVar(y'')` target different wrapper types, so neither pass interferes with
the other. This confirms the ordering-independence claimed in §3.

```
Pass 1: multi_substitute_name([x''], [a]):
  NVar(x'') → a
  Result: POutput(NQuote(PVar(y'')), PDrop(a))

Pass 2: multi_substitute([y''], [{b!({}) | (b?z).{*(z)}}]):
  PVar(y'') → {b!({}) | (b?z).{*(z)}}
  Result: POutput(NQuote({b!({}) | (b?z).{*(z)}}), PDrop(a))
```

After both passes, every `FreeVar` from the continuation's `unbind()` has
been replaced by its bound value from the match result. The intermediate
result after Pass 1 shows that `PDrop(NVar(x''))` → `PDrop(a)` — the Name
variable `x''` is replaced by the Name value `a`.

### Step 9 — Normalize

The final normalization step canonicalizes the substituted term. In this
case, the term is already in normal form — no nested `PPar` flattening or
equation application is needed.

```
POutput(NQuote({b!({}) | (b?z).{*(z)}}), PDrop(a))
= @({b!({}) | (b?z).{*(z)}})!(*(a))
```

Final `PPar`: `{@({b!({}) | (b?z).{*(z)}})!(*(a))}` — the continuation has
been correctly instantiated with the match bindings. The result sends the
body `{b!({}) | (b?z).{*(z)}}` (quoted to a Name) on the channel `*(a)`
(the Name `a` dropped to a Proc), demonstrating the explicit category
crossings from §3.

---

## 7A. Architectural Overview — Component Roles and Composition

Five subsystems compose to implement predicated types. This section provides
the big picture before diving into any individual component.

### Subsystem Roles

**① PathMap Decision Tree (Parse Dispatch)**
- **Role:** Determines *which parse rule* to invoke given a token prefix.
- **Mechanism:** Byte-encoded trie over syntax item patterns (terminals occupy
  the ASCII range 0x00–0x7F; nonterminals and captures use high bytes
  0x80–0xBF to avoid collision). Each leaf is a `DecisionAction`:
  `Commit` (deterministic), `Ambiguous` (multiple candidates), `NonterminalBoundary`
  (FIRST set expansion).
- **When:** Compile-time construction, runtime dispatch per token.
- **Contract:** `token_prefix → DecisionAction { rule_label, weight }`
- **Predicated types role:** Dispatches to the parse rule for `for(φ ← channel)`
  and each constructor in the guard pattern. PathMap handles *syntactic
  disambiguation*; it does NOT evaluate guards.
- **Key file:** [decision_tree.rs](../../prattail/src/decision_tree.rs)

The following diagram shows a concrete PathMap trie that disambiguates
guarded receive (`PGuardedInput`) from unguarded receive (`PInput`). Read the
trie left-to-right: the shared prefix `FOR → LPAREN → capture(Name) → LARROW
→ capture(Name)` is common to both rules; the branch point is the 5th token,
where `RPAREN` commits to `PInput` and `IF` commits to `PGuardedInput`. This
demonstrates how PathMap resolves syntactic ambiguity at parse time in
O(prefix length) without backtracking — the guard evaluation mechanism (§5-8)
is entirely orthogonal to parse dispatch.

```
PathMap trie for parse dispatch:

  FOR ──► LPAREN ──► capture(Name) ──► LARROW ──► capture(Name)
                                                       │
                                          ┌────────────┴────────────┐
                                          ▼                         ▼
                                      RPAREN                       IF
                                          │                         │
                                          ▼                         ▼
                              Commit(PInput rule)          capture(Pred)
                              [0x00 0x80 0x00 0x80]            │
                                                               ▼
                                                           RPAREN
                                                               │
                                                               ▼
                                                   Commit(PGuardedInput rule)
                                                   [0x00 0x80 0x00 0x80 0x00 0x80]

  Byte encoding:
    0x00–0x7F: terminals (FOR, LPAREN, LARROW, IF, RPAREN)
    0x80–0x81: captures (Name, Pred)
    0x82–0xBF: nonterminal references

  The IF terminal disambiguates PInput from PGuardedInput at the
  5th byte position. PathMap resolves this in O(prefix length)
  without backtracking.
```

**② First-Order Pattern Matching (`match_pattern` / `match_pattern_name`)**
- **Role:** Extracts variable bindings by matching a ground (concrete) term against
  a pattern containing free variables. This is the structural decomposition step.
- **Mechanism:** Generated per-category Rust methods that recurse through term
  constructors. Variable positions bind; literal/nullary positions check equality;
  regular positions recurse into children. Returns `(σ | ⊥)`.
- **When:** Compile-time code generation, runtime per-Comm-rule firing.
- **Contract:** `(ground_term, pattern) → (σ | ⊥)`
- **Predicated types role:** When a Comm rule fires, `match_pattern_name` is called
  on the received value against the guard body pattern. Success yields σ (the
  substitution); failure means the Comm rule does not fire.
- **Distinction from unification:** One-directional (ground vs pattern), O(|pattern|),
  deterministic. No occurs check needed. No backtracking.
- **Key file:** [match_pattern.rs](../../macros/src/gen/term_ops/match_pattern.rs)

The following example demonstrates cross-category matching with a collection
pattern containing both non-variable (`PSend(a, b)`) and variable (`...rest`)
elements. The AC-matching strategy (§5 "Collection Variant Matching") first
matches `PSend(a, b)` structurally, then binds `rest` to the remaining
unclaimed element.

```
match_pattern_name(
  NQuote(PPar({PSend(x,y), PNil})),
  NQuote(PPar({PSend(a,b), ...rest}))
)
→ MatchBindings { name: {a→x, b→y}, proc: {rest→PNil} }
```

The result contains three bindings across two categories: `a` and `b` are
Name bindings (from the Name-typed fields of `PSend`), and `rest` is a Proc
binding (from the variable capturing the remaining bag element).

**Collection matching:** HashBag uses order-independent AC-matching with a
`claimed` bitvector — non-variable pattern elements find exact structural
matches among unclaimed ground elements, variable pattern elements bind to
remaining unclaimed elements. Vec uses positional matching. HashSet matches
like HashBag without multiplicity. Each element sub-match re-enters
`match_pattern()` via TLS pooling (bounded by collection size, not depth).

**Binder matching:** Opens both ground and pattern scopes via `.inner()`,
matches bodies structurally. If the pattern binder is a FreeVar, it binds
to the ground binder name. MultiBinder handles multiple simultaneous binders
by requiring binder count equality and matching each pair.

**③ Unification (Martelli-Montanari)**
- **Role:** Bidirectional constraint solving — finds the most general substitution
  σ such that σ(t₁) = σ(t₂), or reports failure (clash, occurs check).
- **Mechanism:** Stack-based Martelli-Montanari algorithm with occurs check.
  Operates on `TermExpr` (Var, Const, App). Integrated as `ConstraintTheory`
  with `propagate()`, `label()`, `witness()`.
- **When:** Compile-time (pattern overlap analysis, UN01–03 lints) and optionally
  runtime (MeTTa-style unification matching).
- **Contract:** `(term₁, term₂) → (σ | ⊥)` (most general unifier)
- **Predicated types role:**
  - *Compile-time:* Detects overlapping guard patterns (SYM02/SYM03 lints).
    Two guards φ₁ and φ₂ overlap iff `unify(φ₁, φ₂) ≠ ⊥`.
  - *Runtime (optional):* If the language enables unification-based matching,
    guard evaluation can use unification instead of first-order matching.
- **Key file:** [unification.rs](../../prattail/src/unification.rs)

The following comparison highlights the fundamental difference between the
two matching strategies. First-order matching (used at runtime) is
one-directional and cheaper; unification (used at compile-time for overlap
analysis) is bidirectional and handles patterns on both sides.

```
First-order matching:      ground  ← pattern   (one-directional, O(|pattern|))
Unification:               pattern ↔ pattern   (bidirectional,  O(n·α(n)))
```

In the guarded Comm rule pipeline:
- **Runtime**: `match_pattern` performs ground-vs-pattern matching per Comm fire
  (the received value is always ground; the guard body is always a pattern)
- **Compile-time**: Unification performs pattern-vs-pattern overlap detection
  (two guard patterns may both contain variables; unification finds the Most General Unifier (MGU)
  or reports incompatibility for SYM02/SYM03 lint emission)

**④ AscentClauses Bridge (Pattern → Datalog)**
- **Role:** Translates high-level pattern syntax into Ascent Datalog clause
  sequences. This is the key *bridge* between the pattern language and the
  logic engine.
- **Mechanism:** `Pattern::to_ascent_clauses()` walks the pattern tree and emits:
  - `if let` destructuring for constructor patterns
  - `let` bindings for variable capture
  - `eq_cat(x, y)` checks for duplicate variables (implicit equality constraints)
  - Collection iteration for `#map`, `#zip`, `{...rest}` patterns
  - Scope unpacking via `unsafe_pattern()` / `unsafe_body()` for binders
- **When:** Compile-time (proc_macro expansion).
- **Contract:** `Pattern → AscentClauses { clauses: Vec<TokenStream>, bindings: HashMap<String, VariableBinding> }`
- **Predicated types role:** The guarded Comm rule's structural check is generated
  as an Ascent clause via this bridge. Behavioral predicate joins are appended
  after the structural clauses. BCG01 (join ordering) interleaves condition
  checks at their earliest valid positions for fail-fast evaluation.
- **Key file:** [pattern.rs](../../macros/src/ast/pattern.rs)

The following example shows how a pattern AST node is lowered into Ascent
Datalog clauses by `to_ascent_clauses()`. Each constructor becomes an `if let`
destructuring clause; variables become `let` bindings; collection iteration
uses `for` loops. The resulting clause sequence is inserted into the Ascent
rule body, where it acts as a filter/binder chain.

```
Pattern: (PNew x (PPar {P, Q}))
↓ to_ascent_clauses()
Clauses:
  proc(s),
  if let Proc::PNew(x_binder, body) = s,
  let x = x_binder.0.clone(),
  let body_inner = &**body,
  if let Proc::PPar(bag) = body_inner,
  for (elem, count) in bag.iter(),
  ...
Bindings: { "x" → VarBinding(Name), "P" → VarBinding(Proc), "Q" → VarBinding(Proc) }
```

Each constructor match becomes an `if let` clause. Variable captures become
`let` bindings. Duplicate variable names generate `eq_cat(x, y)` equality
constraints. Binder positions use `unsafe_pattern()` / `unsafe_body()` for
scope unpacking.

**⑤ Ascent Fixpoint Engine (Logic Evaluation)**
- **Role:** Evaluates all generated Datalog rules to a fixpoint — the transitive
  closure of all equations, rewrites, congruences, Comm rules, and guard
  evaluations.
- **Mechanism:** Semi-naïve Datalog evaluation via the Ascent library. Relations
  (`cat(T)`, `eq_cat(T,T)`, `rw_cat(T,T)`, `is_refined_cat(T)`) are populated
  iteratively until no new tuples are derived.
- **When:** Runtime (after code generation).
- **Contract:** `initial_terms → fixpoint_state { all derived relations }`
- **Predicated types role:** The Ascent engine is where everything converges.
  Category rules explore the term space, equation rules establish equivalence
  classes, Comm rules fire when structural + behavioral guards are satisfied,
  and behavioral guard joins directly access fixpoint relations.

The following diagram shows the Ascent engine's internal structure. The
relations listed are the core set; user-declared relations (`R(T₁,...,Tₙ)`)
extend this set. The rule firing order follows semi-naive evaluation: each
iteration derives only NEW tuples (the delta), and the fixpoint is reached
when no iteration produces new tuples in any relation.

```
┌────────────────────────────────────────────────────────────────┐
│                    Ascent Fixpoint Engine                      │
│                                                                │
│  Relations:                                                    │
│    proc(Proc)          ← category exploration                  │
│    name(Name)          ← category exploration                  │
│    eq_proc(Proc, Proc) ← equations + congruence                │
│    rw_proc(Proc, Proc) ← rewrites + congruence                 │
│    R(T₁, ..., Tₙ)     ← user-declared semantic relations       │
│                                                                │
│  Rule firing order (semi-naïve):                               │
│    1. Category rules: proc(PNew(x,body)) → name(x), proc(body) │
│    2. Equation rules: eq_proc(PDrop(@P), P) ← proc(PDrop(@P))  │
│    3. Comm rules:                                              │
│       proc(result) ←                                           │
│         proc(PPar(bag)),                                       │
│         for (elem, _) in bag.iter(),                           │
│         if let PSend(ch, val) = elem,     ← structural match   │
│         ...,                                                   │
│         match_pattern_name(val, φ) = σ,   ← first-order match  │
│         R(σ(x), σ(y)),                    ← behavioral guard   │
│         let result = σ(continuation);     ← substitution       │
│    4. Congruence rules: propagate eq/rw through constructors   │
│                                                                │
│  Fixpoint: iterate until no new tuples in any relation         │
└────────────────────────────────────────────────────────────────┘
```

### End-to-End Composition Flow

The following diagram traces a guarded receive expression from source code
through all five subsystems. Read it top-to-bottom as a time sequence: parse
time (PathMap dispatch), compile time (match_pattern codegen + AscentClauses
bridge + guard codegen), and runtime (Ascent fixpoint). The key observation
is that compile-time subsystems (② ③ ④) execute in parallel to produce
different pieces of the generated code, which then converge at runtime in the
Ascent engine (⑤). The arrows between ② and ④ show their independence — they
produce different code artifacts that are assembled into the same Ascent rule.

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         SOURCE CODE                                     │
│   for(x <- ch if positive(x)) { P }                                     │
└───────────────────────────┬─────────────────────────────────────────────┘
                            │
                   ─── PARSE TIME ───
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  ① PathMap Decision Tree                                                │
│     Token stream: FOR LPAREN IDENT LARROW IDENT IF IDENT ... RPAREN     │
│     PathMap lookup: FOR → Commit(PInputs rule)                          │
│     Result: Parse as PGuardedInput constructor                          │
└───────────────────────────┬─────────────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  AST: PGuardedInput(ch, guard_scope, [positive(x)], cont_scope)         │
│       guard_scope.body = x  (structural pattern)                        │
│       behavioral_preds = [RelationQuery("positive", [Var("x")])]        │
└───────────────────────────┬─────────────────────────────────────────────┘
                            │
                  ─── COMPILE TIME (proc_macro) ───
                            │
                   ┌────────┴────────┐
                   ▼                 ▼
┌──────────────────────────┐  ┌──────────────────────────────────────────┐
│ ② match_pattern codegen  │  │ ④ AscentClauses bridge                   │
│                          │  │                                          │
│ Generate:                │  │ LHS Pattern → Ascent clauses:            │
│   Name::match_pattern_   │  │   proc(s),                               │
│     name(&self, pattern) │  │   if let Proc::PPar(bag) = s,            │
│   → (σ | ⊥)             │  │   for (elem, _) in bag.iter(),           │
│                          │  │   if let Proc::PSend(ch, val) = elem,    │
│ Per-variant arms:        │  │   if ch == expected_channel,             │
│   NQuote: recurse into   │  │   if let Some(mb) = val.match_pattern(φ),│
│     Proc::match_pattern  │  │   positive(mb.get_name("x")),  ← T2 join │
│   NVar: check index eq   │  │   let result = construct_continuation(σ);│
│   FreeVar: bind to σ     │  │                                          │
└──────────────────────────┘  └──────────────┬───────────────────────────┘
                                             │
                   ┌─────────────────────────┤
                   ▼                         │
┌──────────────────────────────┐             │
│ Guard Codegen (§13)          │             │
│                              │             │
│ Classify: T1/T2/T3/T4        │             │
│ (tiers defined in §11)       │             │
│ T2 → direct Ascent join or   │             │
│ SFA transition table or      │             │
│ relation lookup or range     │             │
│ check, per strategy          │             │
└──────────────────────────────┘             │
                                             │
                  ─── RUNTIME (Ascent fixpoint) ───
                                             │
                                             ▼
┌─────────────────────────────────────────────────────────────────────────┐
│ ⑤ Ascent Fixpoint Engine                                                │
│                                                                         │
│ Iteration 1: Category rules populate proc(·), name(·)                   │
│ Iteration 2: Equation rules establish eq_proc equivalence classes       │
│ Iteration N: Comm rule fires:                                           │
│   proc(PPar({PSend(ch, @42), PInput(ch, x, P)}))                        │
│   → match_pattern_name(@42, guard_body) = Some({x → 42})                │
│   → positive(42)?  ← behavioral guard join against Ascent relation      │
│   → if yes: proc(P[x := 42])  (continuation with substitution)          │
│                                                                         │
│ Fixpoint: no new tuples → DONE                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Component Interaction Matrix

The following matrix summarizes the pairwise interactions between the five
subsystems. Empty cells indicate no direct interaction. Read each row as
"this subsystem [verb] that subsystem." The matrix reveals the architecture's
key property: the Ascent engine (rightmost column) is the convergence point
that consumes all other subsystems' output, while PathMap and match_pattern
are independent of each other.

```
                PathMap  match_pattern  Unification  AscentClauses  Ascent
PathMap            —     (indirect)         —        generates      —
match_pattern      —         —              —            —         called by
Unification        —     (overlap check)    —        (lint gen)    (optional)
AscentClauses      —     references      references      —        generates
Ascent             —     calls at RT     calls at RT  consumes       —
```

- PathMap and match_pattern are **independent** — PathMap dispatches to rules,
  match_pattern evaluates within rules
- Unification and match_pattern are **complementary** — match_pattern for runtime
  ground-vs-pattern, unification for compile-time pattern-vs-pattern overlap
  detection
- AscentClauses is the **bridge** — it consumes pattern AST and produces Ascent
  code that calls match_pattern at runtime
- The Ascent engine is the **convergence point** — all other subsystems either
  generate input for it (compile-time) or are called by it (runtime)

### When Each Subsystem Is Used

| Subsystem       | Compile-Time Role                                 | Runtime Role                                          |
|-----------------|---------------------------------------------------|-------------------------------------------------------|
| PathMap         | Trie construction from grammar rules              | Token → rule dispatch (O(prefix length))              |
| match_pattern   | Code generation (methods per category)            | Ground-vs-pattern matching per Comm fire              |
| Unification     | Pattern overlap analysis (UN01–03, SYM02–03)      | Optional: unification-based matching if enabled       |
| AscentClauses   | Pattern → Datalog clause translation              | —                                                     |
| Ascent Engine   | —                                                 | Fixpoint evaluation of all generated rules            |
| Guard Codegen   | SFA compilation, tier classification, code emit   | Guard function evaluation per behavioral Comm fire    |

Guard selectivity interacts with the constraint theory suite (§16) when
guards involve theory-specific predicates.

---

## 8. Behavioral Predicates

### Motivation

Structural matching alone answers "does the received value have the right
shape?" but cannot express relational properties like "is there a path from
`y` to the empty process?" or "is `x` a well-formed output?". Behavioral
predicates bridge this gap by checking whether declared Ascent relations hold
over the match-extracted values. (For the constraint theory framework that
enables these evaluations, see §16.)

### The Core Challenge

Ascent relation queries are **JOIN clauses** — they must name a specific
relation at compile time. You cannot write a dynamic dispatch like
`check_relation(name, args)` inside a rule body. Each join clause is
statically bound to a declared relation.

However, the set of possible relation names IS known at compile time: they
are declared in the `logic {}` block of the language definition. This is the
key insight that makes behavioral predicates feasible.

### Mechanism: Per-Relation Comm Rule Specialization

The macro generates **one specialized Comm rule per declared relation** in the
logic block. Each rule handles guards whose behavioral predicate references
that specific relation.

Given a language that declares `relation path(Proc, Proc)` and
`relation is_output(Proc)`, the macro generates:

1. **Structural-only rule** (no behavioral predicates) — as in §6
2. **`path`-specialized rule** — handles guards with a `path` predicate
3. **`is_output`-specialized rule** — handles guards with an `is_output`
   predicate

### Generated Datalog (Single Behavioral Predicate)

The following rule extends the structural-only Comm rule (§6) with a
behavioral predicate JOIN. The key difference is the addition of three
clauses: (1) a guard checking that this rule handles the correct predicate
(`preds.len() == 1 && preds[0].relation_name == "path"`), (2) argument
resolution from match bindings (`resolve_arg`), and (3) a static Ascent join
against the declared relation (`path(pred_arg0, pred_arg1)`). The structural
matching reuses the same code as §6 — the behavioral layer is purely
additive. The rationale for per-relation specialization (rather than a
dynamic dispatch) is that Ascent's semi-naive evaluation requires join
clauses to name specific relations at compile time; there is no runtime
`check_relation(name, args)` mechanism.

For the declared relation `path(Proc, Proc)`:

```rust
rw_proc(s_orig.clone(), t) <--
    eq_proc(s_orig, s),
    if let Proc::PPar(ref bag) = s,

    for (inp, _) in bag.iter(),
    if let Proc::PGuardedInput(ref channel, ref guard_scope,
                                ref preds, ref cont_scope) = inp,

    if preds.len() == 1 && preds[0].relation_name == "path",

    for (out, _) in bag.iter(),
    if let Proc::POutput(ref out_channel, ref sent_proc) = out,
    if channel == out_channel,

    let received_name = Name::NQuote(sent_proc.clone()),
    let (_, guard_body) = guard_scope.clone().unbind(),
    if let Some(match_bindings) = received_name.match_pattern_name(&*guard_body),

    let pred_arg0 = preds[0].resolve_arg(0, &match_bindings),
    let pred_arg1 = preds[0].resolve_arg(1, &match_bindings),

    // JOIN: fires only if (pred_arg0, pred_arg1) exists in the path relation
    path(pred_arg0, pred_arg1),

    // ... rest, substitution, same as §6 ...
```

The critical line is `path(pred_arg0, pred_arg1)`. This is a standard Ascent
join clause: it succeeds only if the tuple `(pred_arg0, pred_arg1)` exists
in the `path` relation's hash index. The O(1) lookup cost makes behavioral
guards practically free after the structural matching phase. Since the
relation name `path` is known at macro expansion time, the join clause is
statically generated — no runtime reflection is needed.

### Behavioral Predicate Evaluation Flow

The following diagram shows the three-stage pipeline for a single behavioral
predicate: structural matching (producing σ), argument resolution (mapping
predicate arguments through σ to concrete values), and the Ascent JOIN check.
The two exit points (fire/skip) correspond to the `if let Some(...)` and
`path(...)` join clauses in the generated code above.

```
PGuardedInput(ch, φ, [R(a₁, a₂)], c)
     │
     ▼  match(φ, @(q)) = σ
     │
     ▼  resolve(a₁, σ) = v₁,  resolve(a₂, σ) = v₂
     │
     ▼  JOIN: R(v₁, v₂) ∈ Ascent fixpoint?
     │
  ┌──┴──┐
  Yes   No
  │     │
  ▼     ▼
 fire  skip
 c[σ]
```

### Predicate Argument Resolution

Each behavioral predicate argument is either a match variable reference or a
constant term. The `resolve_arg` function handles this dispatch: for
`Var("y")`, it looks up `"y"` in `match_bindings` by name; for
`Constant(PZero)`, it returns the ground term directly. The `BehavioralPred`
struct captures the full predicate specification including the relation name,
argument list, and negation flag. The `negated` field enables stratified
negation (§9): when `true`, the generated code uses `!path(...)` instead of
`path(...)`, firing when the tuple is ABSENT from the relation.

```rust
struct BehavioralPred {
    relation_name: String,
    args: Vec<PredArg>,
    negated: bool,
}

enum PredArg {
    Var(String),
    Constant(Proc),
}
```

The `relation_name` is a `String` (not a type-level identifier) because it is
resolved at macro expansion time against the `logic {}` block's declared
relations. The `PredArg::Var` variant stores the variable's `pretty_name`,
which is matched against `match_bindings` entries during resolution.

> **Note:** The `negated` field on `BehavioralPred` enables stratified
> negation support (§9).

### Conjunctions

For conjunctions of behavioral predicates (e.g., `path(y, {}) AND
is_output(*(x))`), the macro generates rules for the relevant combinations.
A guard with predicates referencing relations `R₁` and `R₂` requires a rule
with BOTH join clauses. The generated code resolves each predicate's arguments
independently and chains the joins sequentially. BCG01 selectivity ordering
(§13) may reorder the joins so the more selective relation is checked first,
enabling earlier short-circuit pruning.

```
  … structural matching …
  (r₁_arg₀, r₁_arg₁) ← resolve_args(pred₁)
  require (r₁_arg₀, r₁_arg₁) ∈ R₁                  // join clause 1
  (r₂_arg₀) ← resolve_args(pred₂)
  require (r₂_arg₀) ∈ R₂                             // join clause 2
  … continuation …
```

Both joins must succeed for the rule to fire — this is the conjunction
semantics of the `Vec<BehavioralPred>` representation.

> **Conjunction notation:** Three equivalent notations appear across the
> design documents:
>
> | Notation                                                                | Context                                                |
> |-------------------------------------------------------------------------|--------------------------------------------------------|
> | `,` (comma)                                                             | Surface syntax in the `where`-clause (§2 EBNF)         |
> | `AND`                                                                   | English prose / pseudo-syntax                          |
> | `BehavioralPred::And(a, b)` / multiple entries in `Vec<BehavioralPred>` | AST representation                                     |
>
> The §2 `where`-clause grammar uses comma-separated literals; the runtime
> representation is a `Vec<BehavioralPred>` (implicit conjunction).

### Scaling Analysis

```
|specialized_rules| ≤ C(|relations|, K)    for K predicates per guard
```

| Guard predicates          | Rules generated   | Notes                        |
|---------------------------|-------------------|------------------------------|
| 0 (structural only)       | 1                 | The base case from §6        |
| 1 from relation R         | 1 per declared R  | Only the matching rule fires |
| 2 from relations R, S     | 1 per pair (R, S) | Quadratic but K is small     |
| K from distinct relations | C(N, K)           | Practical for K ≤ 2–3        |

For languages with many declared relations, an alternative is a SINGLE rule
with an interpreted predicate checker via a generated lookup function that
accesses Ascent relation state.

### Negated Predicates

When `negated: true`, the generated rule uses Ascent's stratified negation
operator. The theoretical basis is well-founded semantics (Van Gelder et al.,
1991): negation is safe only when the negated relation is fully computed before
the rule consuming it fires. This is enforced by stratification — the negated
relation must belong to a lower stratum than the rule body.

```rust
    !path(pred_arg0, pred_arg1),
```

The `!` prefix is Ascent's negation syntax. The clause fires when the tuple
is ABSENT from the `path` relation — the semantic complement of the positive
join. Stratification validation ensures negated relations appear in lower
strata than the rules consuming them. Same-stratum negation produces a
compile-time error.

### Full Guard Check Formula

The following equation unifies the structural and behavioral guard checks
into a single formal predicate. The structural match produces σ, and each
behavioral predicate is then evaluated against the Ascent fixpoint with
polarity determined by the `negated` flag. This equation is the specification
that the generated Datalog rules implement.

```
match(φ, @(q)) = σ  ∧  ∀(R, args, neg) ∈ preds.
    (¬neg ⟹ R(resolve(args, σ)) ∈ FP) ∧
    (neg  ⟹ R(resolve(args, σ)) ∉ FP)
```

The conjunction `∀(R, args, neg) ∈ preds` requires ALL predicates in the
guard to be satisfied — a single failing predicate blocks the Comm rule.
The `resolve(args, σ)` function maps each `PredArg` through the substitution
σ: variables are looked up by name, constants are used directly.

### Quantified Behavioral Predicates

**Problem:** Current behavioral predicates are existential queries ("does
tuple exist in relation?"). Full First-Order Logic (FOL) needs universal quantification and
nested quantification.

**Infrastructure available:** LogicT provides `gnot` (negation as failure for
`not-exists`), `ifte`/`once` (committed choice for `exists-unique`), and `fair_conjoin` (fair
nested quantification `forall(x, exists(y, P(x,y)))`).

**Three evaluation strategies:**
1. Compile to Ascent aggregation (count comparison)
2. AWA evaluation at runtime (M3)
3. **LogicT evaluation** (`gnot(violation_stream)` for universals) — **SELECTED**

**Implementation (Strategy 3 — LogicT evaluation):**

Strategy 3 was selected because all LogicT primitives existed and it required
the least new code. AWA requires the unimplemented `to_weighted_automaton()`
(~2000 lines). Ascent aggregation requires codegen changes with limited
composability. The cost-benefit framework can gate to AWA later once
`to_weighted_automaton()` is implemented.

Guard syntax (inside `language!` macro):
```text
guard(forall(y, nodes, entails(reachable(x, y), safe(y))))
guard(exists(y, 100, rewrites_to(x, y)), halts(y))
guard(not(safe(x)), connected(x, z))
guard(path(x, y), connected(y, z))
```

Operators: `,` (conjunction), `not()` (negation), `entails()` (implication),
`forall()` / `exists()` (quantifiers).

The cost-benefit framework assigns cost 20 to `BehavioralGuard` conditions,
ensuring they are evaluated last in BCG01 fail-fast ordering.

> **Theory-guided LogicT evaluation:** When a quantified guard has typed
> predicate parameters (e.g., `forall(y: Int, nodes, gt(y, 0))`) and a
> matching `ConstraintTheory` is registered via `guards { theories {} }`
> (§2A), the pipeline uses `propagate()` to prune the enumeration domain
> before LogicT evaluation — fewer candidates, faster convergence. See
> §14A for the full theory-guided evaluation pipeline, TriState refinement,
> and the refinement type bridge.

### AC-Matching for Collections

**Problem:** Collection patterns (`{P | Q}` in guards) require
associative-commutative matching — the `PPar` bag is unordered, so matching
`{x | y}` against `{A | B | C}` requires trying all 2-element subsets.

**Solution:** Multiplicity-aware partition enumeration via `LogicStream`.

- `multiset_partitions()` in [logict.rs](../../prattail/src/logict.rs): lazily enumerates all
  ways to select K elements from a multiset, producing
  `LogicStream<MultisetPartition<T>>`. Uses `interleave()` for fair exploration
  across branches. Generic over element type.
- `multiset_select()`: convenience wrapper with `collect_bounded()` for T3 safety.
- `BehavioralPred::AcMatch` variant in [language.rs](../../macros/src/ast/language.rs): parsed from
  `guard(ac_match(bag, {x, y, ...rest}))` syntax.
- Codegen in [rules.rs](../../macros/src/logic/rules.rs): generates partition enumeration code
  through `Condition::BehavioralGuard` pipeline. Cost 25 (higher than standard
  behavioral guards at 20).

---

## 9. Correctness Analysis

Seven claims about the predicated types system, each stated formally then
argued.

### 9.1 Soundness

**Claim:** `∀s, t. rw_proc(s, t) ⟹ ∃σ. match(φ, @(q)) = σ ∧ t = c[σ]`

**Argument:** The generated datalog clause includes
`if let Some(match_bindings) = received_name.match_pattern_name(&*guard_body)`.
This is an Ascent `if let` clause — the rule body only continues when the
match succeeds. If the received Name does not match the guard pattern, `None`
is returned and the rewrite does not fire.

### 9.2 Binding Correctness

**Claim:** Every pattern variable is correctly available in the continuation.

**Argument:** The match result contains one entry per free variable in the
guard pattern, keyed by `pretty_name` and partitioned by category. The
continuation's `unbind()` produces binders with the same `pretty_name`s
(enforced by the parser). The two-pass substitution matches them by name.
Each binder gets exactly one replacement. The two passes are disjoint (NVar
vs PVar targets), so order is irrelevant and referential transparency holds.

### 9.3 Capture Avoidance

**Claim:** Substitution is capture-avoiding.

**Argument:** The continuation is stored in a `Scope`. Calling `unbind()`
generates fresh `FreeVar`s and opens the body. No capture is possible because:

1. The fresh `FreeVar`s are globally unique (moniker guarantee)
2. The replacement values are concrete (no free variables that could be
   captured)

### 9.4 Compositionality

**Claim:** `match(C(t₁,…,tₙ), C(π₁,…,πₙ)) = ⨆ᵢ match(tᵢ, πᵢ)`

**Argument:** `match_pattern` recurses through constructors. A guard like
`@(x!(y!(z)))` = `NQuote(POutput(NVar(x), POutput(NVar(y), PVar(z))))` yields:

- `x` → Name (channel of outer POutput)
- `y` → Name (channel of inner POutput)
- `z` → Proc (body of inner POutput)

The `MatchBindings` struct accumulates entries from both categories via
`merge()`, correctly handling the category crossings at each
`Box<Name>` / `Box<Proc>` field boundary.

### 9.5 Equation Integration

**Claim:** `eq_proc(s_orig, s)` respects the equational theory.

**Argument:** The rule matches via `eq_proc(s_orig, s)`, meaning it applies
to any term equationally equivalent to the LHS. This is consistent with the
existing Comm rule's equation matching.

### 9.6 Rho-Calculus Consistency

**Claim:** Natural-category bindings are consistent with the reflective
structure.

**Argument:** In the unguarded case, the receive binds `@(q)` — a Name. The
guarded case decomposes `@(q)` (a Name) and binds sub-components at their
natural categories. The user explicitly manages level crossings via `@()`
(quote, Proc→Name) and `*()` (drop, Name→Proc) in the continuation. This is
the standard reflective discipline of the rho-calculus.

### 9.7 Ordering and Determinism

The guard's free variables define the binder order for both Scopes. The
parser extracts free variables in a deterministic order: **left-to-right,
depth-first** occurrence order in the guard pattern.

For `@(x!(y))` = `NQuote(POutput(NVar(x), PVar(y)))`:
1. `x` (encountered first, in Name position)
2. `y` (encountered second, in Proc position)

This order determines: (a) the binder order in both Scopes, (b) the
positional correspondence between guard and continuation binders.

---

## 10. Parsing and Variable Inference

### Parser Steps

The parser decomposes a guarded receive into four semantically distinct fields,
each serving a different role in the predicated Comm rule. The core insight is
that the surface syntax `(n ? pattern, predicates).{ body }` encodes a
*structured guard*: the pattern constrains the structural shape of the received
value, the predicates constrain its behavioral properties, and the continuation
specifies the post-match computation. This decomposition is analogous to the
distinction between syntax-directed and semantics-directed analysis in
type-checking — the parser extracts sufficient information for later stages to
classify, compile, and optimize each field independently.

The following diagram annotates a concrete guarded receive, showing which
substring maps to which field:

```
(n ? @(x!(y)), path(y, {})).{ @(y)!(*(x)) }
 │   ├────────┤ ├──────────┤  ├────────────┤
 │   structural  behavioral    continuation
 channel
```

The channel `n` identifies the communication endpoint. The structural pattern
`@(x!(y))` is a Name-typed first-order pattern whose free variables `{x, y}`
become the binder list. The behavioral predicate `path(y, {})` is parsed into
a `BehavioralPred` AST node (§8) and evaluated against the Ascent fixpoint at
runtime. The continuation `@(y)!(*(x))` is the process body executed after a
successful match. All four fields are extracted in a single left-to-right parse
pass — no backtracking is needed because the delimiters (`?`, `,`, `.{`, `}`)
are unambiguous in PraTTaIL's Pratt grammar.

The parser:

1. Parses `n` as a Name expression (the channel)
2. Parses `@(x!(y))` as a Name expression (the guard pattern)
3. Extracts free variables from the guard: `{x: Name, y: Proc}`
4. Preserves natural categories in the binder list: `[x: Name, y: Proc]`
5. Parses behavioral predicates: `path(y, {})` → `BehavioralPred`
6. Parses `@(y)!(*(x))` as a Proc expression (the continuation body)
7. Constructs two Scopes with binders `[x, y]` over the guard (Name) and
   continuation (Proc)

### Free-Variable Extraction with Natural Categories

The existing [`var_inference.rs`](../../macros/src/gen/syntax/var_inference.rs) module infers variable categories from syntax
context. For the guard `@(x!(y))`:

- `x` is in a Name-typed field (channel of `POutput`) → Name category
- `y` is in a Proc-typed field (body of `POutput`) → Proc category

These natural categories are preserved through to `MatchBindings` and the
two-pass substitution. The binder list records each variable's category so
the continuation knows which variables are NVar vs PVar.

### Term Context Declaration

The `language!` macro needs a way to express the guard-binder relationship in
its term declarations — specifically, that the guard pattern and continuation
body share a common set of binders but differ in category (Name vs Proc). The
`TermParam::GuardBody` variant captures this dual-scope relationship in a
single declaration, telling the macro codegen layer to produce two
`Scope<Vec<Binder<String>>, _>` wrappers (one for Name, one for Proc) that
share the same binder list. This design avoids the need for a separate
cross-scope linking pass and ensures the binder list is constructed exactly
once during parsing, then threaded through both scopes by reference.

The variant stores two identifier-type pairs — one for the guard and one for
the continuation body — mirroring the dual-scope structure described in §4:

```rust
TermParam::GuardBody {
    guard: Ident,       // "guard"
    body: Ident,        // "p"
    guard_ty: TypeExpr, // Name
    body_ty: TypeExpr,  // Proc
}
```

From this declaration, the codegen layer generates three outputs: a
`Scope<Vec<Binder<String>>, Box<Name>>` for the guard (wrapping the structural
pattern in a Name-category scope), a `Vec<BehavioralPred>` for the behavioral
predicates (extracted during parsing but not scoped — they reference variables
by name), and a `Scope<Vec<Binder<String>>, Box<Proc>>` for the continuation
(wrapping the body in a Proc-category scope with the same binders). The guard
and continuation scopes share identical binder lists, ensuring that `unbind()`
on either scope produces the same set of free variables — the invariant
required by two-pass substitution (§6).

### Tokens Feature Integration

Guard keywords (`where`, `not`, `and`, `or`, `forall`, `exists`, `entails`,
`implies`, `implied_by`, `iff`) and their Unicode alternatives (`¬`, `∧`, `∨`,
`∀`, `∃`, `⟹`, `⟸`, `⟺`) are defined via the `tokens { ... }` block as
`TokenKind::Custom` entries. Modal lexing (`push(pred_mode)`/`pop`) activates
predicate keyword recognition inside `where`-clause scope. FIRST set
augmentation auto-wires custom guard tokens. No manual lexer Nondeterministic
Finite Automaton (NFA) / Deterministic Finite Automaton (DFA) modifications are
needed.

---

## Part II: Formal Framework

---

## 11. Decidability Tiering

### Motivation

Not all predicates are decidable. The halting problem (`halts(x)`) is a
perfectly reasonable guard to write — but it cannot be evaluated in general.
Rather than rejecting such predicates outright, the pipeline classifies every
guard into one of four **decidability tiers** and applies the appropriate
compilation strategy.
(See [weighted-mso.md](../../prattail/docs/design/weighted-mso.md) for the MSO classification
framework that informs decidability analysis.)

### Tier Classification

The four tiers correspond exactly to the four levels of the arithmetical
hierarchy relevant to predicate evaluation: decidable (computable in finite
time), computably enumerable but not decidable (semi-decidable — an answer may
come but is not guaranteed), co-computably-enumerable, and fully undecidable.
The rationale for exactly four tiers rather than a finer-grained hierarchy is
pragmatic: each tier maps to a qualitatively different compilation strategy,
and finer distinctions (e.g., separating polynomial-time decidable from
exponential-time decidable within T2) do not change the code shape — only the
constant factor. The tier system ensures that every guard receives the most
efficient compilation strategy that soundness permits: if a guard *can* be
eliminated at compile time (T1), it *is* eliminated; if it *can* be compiled
to a finite automaton (T2), it *is* compiled rather than interpreted; if it can
only be approximated (T3), the approximation is bounded and the user is warned;
if nothing can be done (T4), the burden shifts to the user via proof
certificates or trust assertions.

```
┌─────────┬───────────────────────────┬──────────────────────────────────┐
│  Tier   │  Classification           │  Handling                        │
├─────────┼───────────────────────────┼──────────────────────────────────┤
│   T1    │  Compile-time decidable   │  Static elimination (true/false) │
│         │                           │  Dead-code eliminate if false    │
│         │                           │  Runtime cost: O(0)              │
├─────────┼───────────────────────────┼──────────────────────────────────┤
│   T2    │  Runtime decidable        │  Compile to SFA/register/Ascent  │
│         │  (finite data domain)     │  join and evaluate per receive   │
│         │                           │  Runtime cost: O(value_size)     │
├─────────┼───────────────────────────┼──────────────────────────────────┤
│   T3    │  Semi-decidable           │  Bounded checking with depth k   │
│         │  (bounded quantification) │  Returns accept/reject/unknown   │
│         │                           │  Runtime cost: O(k · value_size) │
├─────────┼───────────────────────────┼──────────────────────────────────┤
│   T4    │  Undecidable              │  User assertion (assert_pred)    │
│         │  (Rice's theorem, etc.)   │  or Rocq proof certificate       │
│         │                           │  Runtime cost: O(1) (trust)      │
└─────────┴───────────────────────────┴──────────────────────────────────┘
```

The runtime cost column deserves attention: T1 achieves zero cost by
construction (no code emitted), T2's cost is linear in the received value's
size (one automaton traversal), T3 multiplies that by the user-specified bound
`k` (at most `k` unrollings of the bounded quantifier), and T4's O(1) reflects
that the guard is trusted rather than evaluated — the "cost" is the risk of
unsoundness if the user's assertion is wrong. The `classify_decidability()`
function in [`symbolic.rs`](../../prattail/src/symbolic.rs) implements this classification (see the decision tree
below).

### Classification Criteria

**T1 — Compile-time decidable:**

A formula qualifies as T1 when two conditions hold simultaneously: every atomic
predicate can be decided without runtime information (ground-decidable), and
every quantifier ranges over a finite, statically-known domain. The conjunction
of these two conditions guarantees that the formula's truth value can be fully
determined during macro expansion — the key insight is that finiteness of both
the predicate semantics and the quantification domains reduces evaluation to
bounded enumeration:

```
ground_decidable(atoms(φ)) ∧ finite_domain(quantifiers(φ))
```

| Predicate                       | Domain         | Decision                           |
|---------------------------------|----------------|------------------------------------|
| `true`                          | —              | T1 (trivially true)                |
| `false`                         | —              | T1 (trivially false, dead receive) |
| `forall(c, {R,G,B}, valid(c))`  | 3-element enum | T1 (check all 3)                   |
| `x > 5, x < 10`                 | i64 interval   | T1 (interval algebra)              |
| `is_nil(x)`                     | structural     | T1 (pattern match)                 |

**T2 — Runtime decidable:**

All `Atom` predicates correspond to declared Ascent relations in `logic {}`
or are register-testable (M6).

| Predicate          | Mechanism              | Cost             |
|--------------------|------------------------|------------------|
| `is_wellformed(x)` | Ascent relation lookup | O(1) hash lookup |
| `x == last_seen`   | Register equality test | O(1) comparison  |
| `parity(x) == 0`   | DFA state check        | O(length(x))     |

**T3 — Semi-decidable:**

A formula is T3 when it would be undecidable in general but becomes decidable
under a finite depth bound `k`. The theoretical basis is the observation that
many undecidable properties (reachability, termination) become decidable when
restricted to bounded computation traces — this is the principle behind bounded
model checking (Biere et al., 1999). The notation `φ↾k` denotes the formula
`φ` with all quantifiers restricted to depth `k`:

```
∃k. decidable(φ↾k)    where φ↾k bounds all quantifiers to depth k
```

The result is sound but incomplete: if the bounded checker accepts, the
property holds within the bound; if it rejects, the property fails within the
bound; but silence (neither accept nor reject within `k` steps) does not
imply the property holds in general.

| Predicate                        | Bound         | Completeness         |
|----------------------------------|---------------|----------------------|
| `exists(y, 100, halts(y))`       | k = 100 steps | Sound but incomplete |
| `forall(path, 50, safe(path))`   | k = 50 depth  | Sound but incomplete |

**T4 — Undecidable:**

Everything not in T1–T3. By Rice's theorem, for non-trivial semantic
properties of programs, membership is undecidable.

| Predicate                                        | Why Undecidable           | Mitigation                     |
|--------------------------------------------------|---------------------------|--------------------------------|
| `halts(x)`                                       | Rice's theorem            | User proof or Rocq certificate |
| `forall(y, entails(rewrites_to(x, y), safe(y)))` | Unbounded ∀ over ∞ domain | `assert_pred` annotation       |
| `forall(X, φ(X))`                                | Second-order universal    | Restricted MSO or user proof   |

### Classification Decision Tree

The `classify_decidability()` function implements the following decision tree,
which maps any formula `φ` to its tier in O(|φ|) time via a single recursive
descent over the formula's AST. The tree is structured to assign the
most-favorable (lowest-cost) tier first: T1 is checked before T2, T2 before
T3, and T4 is the fallback. The rationale for this priority ordering is that
lower tiers strictly subsume higher tiers in terms of runtime efficiency —
a formula that is T1-eligible should never be compiled as T2, even if T2
compilation would also succeed. The first branch distinguishes ground-decidable
atoms (structural/arithmetic predicates evaluable without runtime state) from
atoms that require runtime data (Ascent relations, register values). The
second-order check is a fast syntactic test for `∀X` quantification over
set variables, which immediately classifies as T4 per Trakhtenbrot's theorem
on the undecidability of second-order logic over infinite domains:

```
Formula φ
    │
    ├── All atoms ground-decidable?
    │   ├── Yes: All quantifiers over finite domains?
    │   │   ├── Yes ──────────────────────────────► T1
    │   │   └── No: Explicit or inferable bound?
    │   │       ├── Yes ──────────────────────────► T3
    │   │       └── No ───────────────────────────► T4
    │   └── No: All atoms are declared Ascent relations?
    │       ├── Yes ──────────────────────────────► T2
    │       └── No: Register-testable?
    │           ├── Yes ──────────────────────────► T2
    │           └── No ───────────────────────────► T4
    └── Contains ∀X (second-order universal)?
        └── Yes ──────────────────────────────────► T4 (MSO01 lint)
```

Note that the tree has no T3 path from the "No: All atoms are declared Ascent
relations?" branch — if an atom requires runtime state (Ascent relation) but
is not available as a declared relation, no amount of bounding helps, since the
issue is missing data, not unbounded search. The MSO01 lint emitted for T4
second-order formulas warns the user that their guard is inherently undecidable
and suggests either providing a Rocq proof certificate or rewriting as a
bounded (T3) variant.

### Cost Model

The following table summarizes the asymptotic costs and correctness guarantees
of each tier. The key trade-off is between compile cost and runtime cost: T1
pays a linear compile cost to achieve zero runtime cost, while T4 pays a
minimal compile cost (just verifying the proof certificate) but shifts all
correctness responsibility to the user. T2's worst-case exponential compile
cost (from SFA subset construction) is the price of achieving complete and
sound runtime evaluation — in practice, most guards produce small automata
because the SFA representation avoids the per-symbol blowup of explicit-alphabet
automata. T3's linear-in-k compile cost reflects the k-bounded unrolling of
quantifiers:

| Tier | Compile Cost                | Runtime Cost per Receive | Guarantees               |
|------|-----------------------------|--------------------------|--------------------------|
| T1   | O(\|formula\|)              | 0 (eliminated)           | Complete + sound         |
| T2   | O(2^\|formula\|) worst case | O(\|value\|)             | Complete + sound         |
| T3   | O(k · \|formula\|)          | O(k · \|value\|)         | Sound, not complete      |
| T4   | O(\|proof\|)                | O(1) (trust)             | Depends on proof quality |

> **Tier promotions via typed predicates (§2A, §14A):**
>
> - **T1 via refinement type bridge:** When a guard predicate structurally
>   matches the refinement predicate of the channel's type (e.g.,
>   `gt(val, 0)` on a channel typed `{ x: Int | x > 0 }`),
>   `RefinementTypeSystem::predicate_entails()` proves the guard is subsumed
>   by the type — the guard is statically eliminated (T1, zero runtime cost).
>   See §14A (Refinement Type Bridge Diagram).
> - **T3 → False via theory decidability:** When `TriState::Unknown` is
>   returned (depth limit exceeded during T3 evaluation), and the guard's
>   typed predicates have a matching `ConstraintTheory` from
>   `guards { theories {} }`, the pipeline invokes `propagate()` +
>   `is_consistent()`. If the refined store is inconsistent, `Unknown` is
>   refined to `False` — the guard is provably unsatisfiable even though
>   enumeration was incomplete. See §14A (TriState Refinement Diagram).

---

## 12. The Five-Stage Pipeline

The predicated types pipeline has five stages, described once here. The
pipeline is a classic compiler architecture — lex/parse, analysis, optimization,
codegen — adapted for predicate compilation rather than general-purpose
language compilation. The key insight is that predicates are themselves
*programs* (formulas that must be evaluated), and the pipeline applies the full
arsenal of compiler techniques to them: constant folding (T1 elimination),
automaton compilation (T2), bounded model checking (T3), and graceful
degradation to trust (T4).

> **Note:** All five pipeline stages execute at **compile time** during
> `language!` macro expansion. Stage 5 (Codegen) produces a `TokenStream`
> containing the guard evaluation functions and Comm rules that will execute at
> **runtime**. The pipeline infrastructure itself — automaton construction,
> analysis, optimization — is not present in the compiled binary. See §14 for
> a comprehensive compile-time vs runtime classification.

The following diagram shows the five stages as a linear pipeline, with each
box listing the stage's purpose, the modules that implement it, and (for stages
with multiple compilation paths) the tier-specific behavior. Read the diagram
top-to-bottom, following the arrows through the data flow:

```
┌──────────────────────────────────────────────────────────────────────────┐
│ Stage 1: PARSE                                                           │
│ Surface syntax → Predicate AST (WeightedMsoFormula)                      │
│ Modules: Pratt parser, weighted_mso.rs                                   │
│                                                                          │
│ Input:  for (@x <- ch) where halts(x), primes(x) { P }                   │
│ Output: WeightedMsoFormula::And(AtomicPos("halts"), AtomicPos("primes")) │
└───────────────────────┬──────────────────────────────────────────────────┘
                        │
                        ▼
┌──────────────────────────────────────────────────────────────────────────┐
│ Stage 2: CLASSIFY + DISPATCH                                             │
│ Decidability tier (T1–T4) + Module activation (M1–M15)                   │
│ Modules: symbolic.rs, predicate_dispatch.rs, weighted_mso.rs             │
│                                                                          │
│ Actions: classify_decidability() → tier                                  │
│          extract_features() → 15-bit PredicateSignature                  │
│          Cost-ordered module execution plan                              │
└───────────────────────┬──────────────────────────────────────────────────┘
                        │
                        ▼
┌──────────────────────────────────────────────────────────────────────────┐
│ Stage 3: COMPILE                                                         │
│ Formula → Automaton (T1/T2) | Bounded checker (T3) | Assert (T4)         │
│ + Constraint theory analysis (Presburger, Unification, Lattice)          │
│ Modules: weighted_mso.rs, symbolic.rs, parity_tree.rs,                   │
│          register_automata.rs, presburger.rs, unification.rs,            │
│          lattice_theory.rs                                               │
│                                                                          │
│ T1: static eval → true/false                                             │
│ T2: to_weighted_automaton() → determinize() → minimize()                 │
│ T3: unroll(k) → bounded automaton → BoundedChecker                       │
│ T4: emit MSO01 lint → assert_pred() wrapper                              │
└───────────────────────┬──────────────────────────────────────────────────┘
                        │
                        ▼
┌──────────────────────────────────────────────────────────────────────────┐
│ Stage 4: OPTIMIZE                                                        │
│ Guard simplification, overlap elimination, selectivity ordering          │
│ + Cross-theory ProductAlgebra composition                                │
│ Modules: symbolic.rs (intersect, minimize), multi_tape.rs,               │
│          two_way_transducer.rs, probabilistic.rs                         │
│                                                                          │
│ Actions: SFA intersection for guard fusion                               │
│          Multi-tape construction for cross-channel guards (M8)           │
│          Backward constraint propagation (M11)                           │
│          Selectivity ordering (M7) for short-circuit evaluation          │
└───────────────────────┬──────────────────────────────────────────────────┘
                        │
                        ▼
┌──────────────────────────────────────────────────────────────────────────┐
│ Stage 5: CODEGEN                                                         │
│ Automaton → Rust guard evaluation code + Ascent Comm rules               │
│ + Lint emission (SYM01–04, PB01–03, UN01–03, SL01–02, LT01)              │
│ Module: macros/src/gen/runtime/guard_codegen.rs                          │
│                                                                          │
│ T2 → SFA transition table or Ascent join clause                          │
│ T3 → bounded_check() with depth counter                                  │
│ T4 → assert_pred() wrapper                                               │
└──────────────────────────────────────────────────────────────────────────┘
```

The pipeline is monotonically information-preserving: each stage enriches the
representation (adding tier labels, automaton structure, optimization metadata)
without discarding the original formula, so later stages can always refer back
to the source. The overall compile-time cost is dominated by Stage 3's
automaton construction, which is O(2^|φ|) in the worst case for subset
construction but typically much smaller due to SFA's symbolic representation
of transitions.

### Stage 1: Parse

The `where`-clause sublanguage is parsed by PraTTaIL's Pratt parser into a
`WeightedMsoFormula` AST. The parser treats the `where` clause as an embedded
sublanguage: comma-separated literals form the top-level conjunction, `not()`
provides stratified negation, and sugar forms (`and()`, `or()`, `entails()`,
`forall()`, `exists()`) desugar to Datalog-compatible structures. The Pratt
parser handles all of this with the same binding-power mechanism used for the
host language — no special-purpose parser is needed.

The following example shows a simple conjunction of two atomic predicates,
which is the most common guard form:

```rholang
for (@x <- ch) where halts(x), primes(x) { P }
```

This parses to a binary `And` node, where each leaf is an `AtomicPos` recording
the predicate label and the variable it constrains:

```
WeightedMsoFormula::And(
    Box::new(AtomicPos { label: "halts", var: "x" }),
    Box::new(AtomicPos { label: "primes", var: "x" }),
)
```

The `label` field is the predicate name as written in the source, which will
be resolved to an Ascent relation during Stage 2 classification. The `var`
field identifies the bound variable from the receive pattern that the predicate
constrains.

Quantified predicates illustrate the richer AST structure. The following
example shows a universal quantifier with an implication body — the logical
reading is "for all `y`, if `x` can reach `y`, then `y` is safe":

```rholang
for (@x <- ch) where forall(y, nodes, entails(reachable(x, y), safe(y))) { P }
```

The parser desugars `entails(A, B)` to `¬A ∨ B` (material implication),
producing:

```
WeightedMsoFormula::ForallFirst {
    var: "y",
    body: Box::new(Or(
        Box::new(NegAtomicPos { label: "reachable(x, y)", var: "y" }),
        Box::new(AtomicPos { label: "safe", var: "y" }),
    )),
}
```

The `ForallFirst` variant indicates first-order universal quantification (over
values, not sets — second-order `∀X` over sets would use `ForallSecond`). The
`NegAtomicPos` node represents a negated atom, corresponding to the `¬` in the
desugared implication. This desugaring ensures that the downstream compilation
stages (§§11-13) work with a normalized AST in negation normal form.

### Stage 2: Classify

Classification determines both the decidability tier (which compilation path
to use) and the module activation set (which automaton modules to invoke). The
four-step algorithm runs in O(|φ|) time — a single pass over the formula AST
suffices to compute both the logical complexity class and the feature signature.
The feature signature is a 14-bit bitvector where each bit indicates whether a
specific module (M1–M15, excluding M0 which is always on) is needed for this
guard. Modules are then sorted by `estimated_cost()` to produce a
cost-ascending execution plan — cheapest modules execute first, enabling early
termination if a cheap module can handle the guard alone:

1. `classify_formula()` → `FirstOrder | Existential | Restricted | Full`
2. `check_decidability()` → `T1 | T2 | T3 | T4`
3. `extract_features()` → `PredicateSignature(u16)` (14 bits, one per module)
4. Modules ordered by `estimated_cost()`: cheapest execute first

### Stage 3: Compile

Compilation transforms the formula AST into an executable representation. The
central abstraction is `SymbolicAutomaton<A>`, where the type parameter `A`
represents the alphabet's BooleanAlgebra (§15) — transitions are labeled with
predicates rather than individual symbols, enabling compact representation of
guards over large or infinite domains. The compilation path begins with
`to_weighted_automaton()`, which translates the formula's logical structure
into automaton states and transitions via a compositional construction (each
connective — ∧, ∨, ¬, ∀, ∃ — has a corresponding automaton operation). From
the symbolic automaton, three paths diverge based on the formula's structure:
standard SFA determinization and minimization for most T2 guards, parity tree
Parity Alternating Tree Automaton (PATA) construction for mu-calculus fixpoint
formulas (recursive predicates via `letprop`), and register automaton
compilation for predicates that compare data values across positions (e.g.,
`x == last_seen`).

```
WeightedMsoFormula ──► to_weighted_automaton() ──► SymbolicAutomaton<A>
                                                      │
                                    ┌─────────────────┼──────────────────┐
                                    ▼                 ▼                  ▼
                            determinize()    mu_calculus_to_pata()  compile_to_register()
                                    │                 │                  │
                                    ▼                 ▼                  ▼
                            minimize()        PATA<W>         RegisterAutomaton<W>
```

The left path (determinize → minimize) is the standard SFA pipeline and
handles the majority of T2 guards. Determinization applies subset construction
over symbolic predicates (§15), and minimization applies Hopcroft's algorithm
(Hopcroft, 1971) adapted for SFAs. The middle path invokes `mu_calculus_to_pata()` (see
[parity-tree-automata.md](../../prattail/docs/design/parity-tree-automata.md)) for formulas containing
fixpoint operators (νX, μX). The right path compiles to register automata
(M6) for predicates that need to compare the current input against stored
values. All three paths produce a typed automaton that Stage 5 can lower to
Rust code.

### Stage 4: Optimize

After compilation, the optimizer applies three transformations: guard fusion
(intersecting multiple guards into a single automaton), cross-channel
coordination (building multi-tape automata for guards that span multiple
channels), and selectivity ordering (reordering guard evaluations to maximize
short-circuit elimination). The core insight behind guard fusion is that
evaluating two guards separately — SFA_A then SFA_B — requires two automaton
traversals of the input, while evaluating their intersection requires only one
traversal of a product automaton. The intersection `intersect(SFA_A, SFA_B)`
computes the product construction over symbolic predicates (transitions labeled
with `pred_A ∧ pred_B`), and the subsequent `minimize()` pass reduces the
product states using Hopcroft's algorithm.

The following diagram shows the fusion of two guards into a single minimized
automaton:

```
Guard A: halts(x)     Guard B: primes(x)
    │                      │
    ▼                      ▼
  SFA_A                  SFA_B
    │                      │
    └──────────┬───────────┘
               ▼
     intersect(SFA_A, SFA_B)
               │
               ▼
     minimize(intersection)
               │
               ▼
     Fused guard automaton
```

The fused automaton accepts exactly the intersection of the two guards'
languages — a value passes the fused guard if and only if it passes both
individual guards.

For multi-channel predicates, M8 (multi-tape) fuses cross-channel constraints
into a single multi-tape automaton that processes values from different channels
simultaneously (see §17 for the multi-tape construction). When the `channels {}`
sub-block is present (§2A), M8/M11 activation is deterministic — only declared
join patterns trigger multi-tape or two-way transducer construction. When
`channels {}` is omitted, the optimizer falls back to heuristic channel
inference from the grammar structure. M7 (probabilistic)
orders guards by selectivity — the probability that a random input passes the
guard. The rationale is that checking the most selective guard first maximizes
the probability of early rejection, avoiding the cost of evaluating subsequent
guards. The selectivity estimates come from static analysis of the guard's
structure (e.g., `halts(x)` is highly selective because most processes do not
halt):

```
Guard            Selectivity    Order
halts(x)         0.01 (1%)      1 (check first — eliminates 99%)
primes(x)        0.15 (15%)     2
ground(x)        0.80 (80%)     3 (check last — eliminates only 20%)
```

This selectivity-ordered evaluation is a compile-time decision: the generated
code evaluates guards in the selectivity-optimal order, with short-circuit
`&&` between them so that a failing guard skips all subsequent evaluations.

### Stage 5: Codegen

The final stage lowers the compiled and optimized automaton into Rust source
code emitted as a `TokenStream` during `language!` macro expansion. The code
shape varies qualitatively by tier — this is not merely a matter of different
constants or thresholds, but fundamentally different code structures reflecting
the computability-theoretic differences between tiers. T1 produces *no* code
(the guard is constant-folded away); T2 produces deterministic finite-state
code (match tables, arithmetic checks, or Ascent join clauses); T3 produces
bounded-search code with an explicit depth counter; T4 produces a trust wrapper
that defers to user-provided proof certificates. The following table summarizes
the code shape and runtime cost for each tier:

| Tier | Generated Code Shape                                                                          | Runtime Cost         |
|------|-----------------------------------------------------------------------------------------------|----------------------|
| T1   | No code (guard eliminated)                                                                    | O(0)                 |
| T2   | Inline arithmetic, Ascent join clause, register machine, or SFA `match` table                 | O(1) to O(\|value\|) |
| T3   | Breadth-first search (BFS) / depth-first search (DFS) with depth counter returning `TriState` | O(k · \|value\|)     |
| T4   | `assert_pred()` trust wrapper                                                                 | O(1)                 |

The T2 row shows a range of code shapes because T2 guards vary in complexity:
a simple arithmetic predicate like `x > 5` compiles to a single comparison
(O(1)), while a complex SFA over string patterns compiles to a match table
traversed in O(|value|) time. The T3 `TriState` return type
(accept/reject/unknown) reflects the inherent incompleteness of bounded
checking — the caller must handle the `unknown` case, typically by falling
through to a conservative default. See §13 "Generated Rust Code per Tier" for
concrete code examples of each tier.

### WeightedMsoFormula Parsing

The `tokens { }` feature provides the lexer infrastructure for guard keywords.
The next step is Pratt parser integration to parse the predicate sublanguage
into `WeightedMsoFormula` AST, connecting the surface syntax from §2 to the
pipeline's Stage 1 parse entry point.

---

## 13. Guard Compilation Strategies

### Single-Channel Guards

The simplest and most common case is a guard that constrains a single channel's
received value. The compilation strategy is a direct application of the tier
classification from §11: the formula is classified, then the appropriate
compilation path is taken. The four paths are mutually exclusive — every
single-channel guard follows exactly one. The diagram below shows the branching
structure, with each branch annotating the key functions invoked along the path:

```
φ(x)
  │
  ▼  classify_decidability()
Tier
  │
  ├─ T1 ──► static evaluate ──► eliminate or pass through
  │
  ├─ T2 ──► to_weighted_automaton() ──► determinize() ──► minimize()
  │          ──► codegen: SFA transition table or Ascent join
  │
  ├─ T3 ──► unroll(k) ──► compile bounded automaton
  │          ──► codegen: bounded_check() with depth counter
  │
  └─ T4 ──► emit MSO01 lint ──► codegen: assert_pred() wrapper
```

The T2 path is the most complex: `to_weighted_automaton()` builds an NFA-like
symbolic automaton, `determinize()` applies subset construction (potentially
exponential in |φ| but typically small), and `minimize()` applies Hopcroft's
O(n log n) algorithm. The entire T2 path executes at compile time; only the
resulting transition table appears in the generated binary.

### Multi-Channel Guards

When a guard references variables bound by multiple channels, the compilation
becomes a coordination problem: the guard cannot be evaluated until values
arrive on all referenced channels, and the order of consumption affects both
correctness and performance. The five-step process below first classifies each
channel's guard independently (reusing the single-channel pipeline), then
detects cross-channel data dependencies by scanning for free variables that
originate from other channels. The key insight is that cross-channel references
create a *dependency graph* among channels, and the compilation strategy must
respect this graph's topological order. When the `channels {}` sub-block is
present (§2A), the dependency graph is built from explicit join pattern
declarations rather than heuristic grammar scanning. When `channels {}` is
omitted, the pipeline falls back to heuristic channel inference.

```
for (@x <- ch1; @y <- ch2) where f(x, y) { P }

Step 1: Classify each guard independently
Step 2: Detect cross-channel dependencies (x referenced in ch2's guard)
Step 3: Build multi-tape automaton (M8) or two-way transducer (M11)
Step 4: Optimize consumption order via selectivity (M7)
Step 5: Codegen coordinated guard evaluation
```

In this example, the `where` clause predicate `f(x, y)` references `x`,
which is bound by `ch1`, and `y`, which is bound by `ch2`. This cross-channel
dependency means `ch1` must be consumed before the guard can be evaluated. But
the dependency can also flow backward: if the `where` clause constrains which
values on `ch1` are worth consuming (e.g., `f(x, y)` implies `x` must satisfy
certain properties), M11 (two-way transducer) can propagate this constraint
backward to prune the `ch1` value space before consumption.

The following diagram shows the `ChannelConstraint` structure that captures
the bidirectional data flow between channels:

```
for (@x <- ch1; @y <- ch2) where f(x, y) { P }
       │
       ▼  backward_constraint(ch2_guard, ch1)
    ChannelConstraint {
        forward_transducer:  ch1_value → evaluate f(x, _)
        backward_transducer: ch2_guard → constrain ch1_values
    }
```

The `forward_transducer` maps a consumed `ch1` value to a partially-evaluated
guard for `ch2` (substituting the concrete `x` value). The `backward_transducer`
inverts this: given `ch2`'s guard, it computes a predicate on `ch1` values that
filters out values guaranteed to make the combined guard fail. This backward
propagation is the Symbolic Finite Transducer (SFT) pre-image operation (§16)
applied to the guard's transducer representation.

### Recursive Predicates (letprop)

User-defined predicates allow programmers to name and reuse complex guard
formulas. The `letprop` syntax binds a predicate name to a formula, which can
then be used as an atomic predicate in subsequent guards. The compilation
strategy routes these definitions through the mu-calculus — specifically,
recursive predicate definitions map to fixpoint formulas (νX for greatest
fixpoints, μX for least fixpoints), which are then compiled to parity
alternating tree automata (PATA) via the construction in
[parity-tree-automata.md](../../prattail/docs/design/parity-tree-automata.md). The PATA representation
captures the alternation between universal and existential quantification in
the predicate's recursive structure.

The following Rholang example defines a `halt` predicate that checks whether a
process has no infinite execution trace — the standard halting property:

```rholang
letprop halt x = forall(x', not(rewrites_to(x, x'))) in
for (@x <- ch) where halt(x) { P }
```

The compilation path translates the predicate definition through four phases:
parsing to a mu-calculus formula, constructing a PATA, classifying
decidability, and (in this case) requiring user intervention because the
predicate is inherently undecidable:

```
letprop halt x = forall(x', not(rewrites_to(x, x')))
  │
  ▼  Parse to mu-calculus
νX. □_{→*}(¬X)
  │
  ▼  mu_calculus_to_pata()          [parity_tree.rs]
ParityAlternatingTreeAutomaton
  │
  ▼  classify_decidability()
T4 (undecidable in general)
  │
  ▼  Require assert_pred or bounded variant
```

The mu-calculus formula `νX. □_{→*}(¬X)` reads as: "the greatest fixpoint X
such that for all successors under the →* (reduction) relation, X does not
hold" — i.e., no infinite reduction sequence exists. This is T4 because `halt`
universally quantifies over an infinite domain (all reachable states) with no
explicit bound — the halting problem in disguise. By Rice's theorem, this
property is undecidable for any Turing-complete reduction system. A bounded
variant (`halt_{100}`) restricts the universal quantifier to depth 100,
yielding T3 and compiling to a bounded depth-first checker that returns
`TriState::Unknown` if the bound is exhausted without a definitive answer.

### Generated Rust Code per Tier

The five-stage pipeline (parse → classify → optimize → lower → codegen)
culminates in code generation, where each decidability tier (§11) produces
a qualitatively different code shape. The following examples illustrate the
generated code for each tier, with narrative explaining the theory, rationale,
and runtime behavior.

#### T1 — Static Elimination

If all atoms in a guard are ground-decidable and all quantifiers range over
finite domains (§11 T1 criteria), the formula can be fully evaluated during
macro expansion — analogous to a traditional compiler's constant-folding pass.
The result is a boolean constant: `true` means the Comm rule fires
unconditionally (no guard check emitted); `false` means the rule is dead code
and is not emitted at all (SYM01 lint). Either way, the generated binary
contains zero guard-evaluation overhead.

Theoretically, the class of ground formulas over finite domains is trivially
decidable: every atom can be evaluated by table lookup, every quantifier
expanded by enumeration. `is_statically_decidable()` detects two syntactic
patterns — tautologies (P ∨ ¬P) and contradictions (P ∧ ¬P). The SFA-based
path (once compiled to `SymbolicAutomaton`) generalizes this to semantic
tautology/contradiction detection via SFA emptiness and universality checks.

Consider a guard `x > 0, x < 100` where `x` is bound to the literal 42 at
parse time:

```rust
// Guard `x > 0, x < 100` with x bound to literal 42 at parse time:
// Entire guard statically evaluates to `true` → guard eliminated from codegen.
// No runtime code generated.
```

In the implementation, `evaluate_static_guard()` returns `Some(true)` for
tautologies and `Some(false)` for contradictions. In
`generate_guarded_comm_rules()`, always-true guards emit only the structural
Comm rule (no behavioral check); always-false guards skip rule generation
entirely.

#### T2 — Decidable Guards

T2 guards are runtime-decidable — they require input values not known until
execution, but evaluation is guaranteed to terminate with a definitive boolean
answer. T2 has three compilation targets, selected by predicate structure:
interval arithmetic for range predicates, Ascent semi-joins for relation
membership, and register machines for data-equality constraints over infinite
domains. All three are complete and sound.

**Interval Arithmetic (IntervalAlgebra)**

`IntervalAlgebra` is a `BooleanAlgebra` instance (§15) whose predicates are
conjunctions/disjunctions of intervals over ordered domains (e.g., `i64`).
When the guard's SFA is compiled with `IntervalAlgebra` as the effective
Boolean algebra, each symbolic transition corresponds to an interval membership
test. SFA minimization collapses redundant states, and the resulting DFA's
transition function is emitted as a simple conditional.

For a single-interval guard like `x > 0, x < 100`, the SFA has one
accepting transition labeled with the interval (0, 100), and codegen produces
a direct range check — the simplest possible runtime evaluation at O(1). For
disjunctions of k intervals, the generated code tests membership in the
interval union, which is O(k) but typically k is small after minimization:

```
guard_check(x: Int) → 𝔹
  return x > 0 ∧ x < 100                            ▷ compiled from SFA interval
```

**Relation Lookup (Ascent Semi-Join)**

Guards of the form `is_wellformed(x)` reference relations declared in the
`logic { }` block. These relations are populated by Ascent's semi-naive
Datalog fixpoint engine before Comm rules fire. At runtime, the guard reduces
to a hash-indexed membership test: "is this tuple in the relation?"

This is the canonical T2 fast path. `can_compile_to_ascent_join()` detects
guards that are pure conjunctions of (possibly negated) relation queries and
inlines them directly as Ascent join clauses in the rule body. Ascent's native
indexing performs O(1) lookup per tuple, and semi-naive evaluation ensures each
fact is derived exactly once.

The generated code probes Ascent's internal hash index for the runtime value.
If the tuple exists, the Comm rule fires and applies its continuation
(substitution + normalization, §6):

```
if (value) ∈ ascent.is_wellformed then               ▷ O(1) hash probe
  fire Comm rule with σ
```

For conjunctions of multiple relation queries,
`compile_guard_to_ascent_clauses()` reorders conjuncts by selectivity (§13
"Guard Selectivity") so the most selective clause appears first in the Ascent
rule body, enabling earlier short-circuit pruning.

**Register Machine (RegisterAutomaton)**

When guards involve data equality or freshness over an unbounded domain —
e.g., "every element in this list equals the first" — neither interval
arithmetic nor relation lookup suffices, because the domain of possible values
is infinite. Register automata (Kaminski & Francez, 1994; M6) solve this by
extending finite automata with a fixed set of registers that store data values.
Transitions may `TestEq` (compare the current input against a stored register)
or `TestFresh` (assert the value has not been seen before).

The generated code mirrors the register automaton's transition function
directly: it walks the term's inductive structure (e.g., a cons-list), stores
the first encountered value in register 0, and for each subsequent element
tests equality against the stored value. The recursion follows the term
structure — each recursive call processes the tail of the list, advancing the
automaton by one transition.

Runtime cost is O(|value|) — one pass over the term, with O(1) work per
register at each step. The number of registers is determined at compile time
by the guard's data-flow analysis (M6):

```
register_guard(value: Term, registers: [(Term | ⊥); R]) → 𝔹
  case value of
    App("cons", [head, tail]) →
      if registers[0] = ⊥ then
        registers[0] ← head
        return register_guard(tail, registers)
      else
        if registers[0] ≠ head then return false   ▷ TestEq fails
        return register_guard(tail, registers)
    Const("nil") → return true
    _            → return false
```

This pattern handles precisely the class of data-aware predicates (equality,
freshness, bounded counting) that SFAs over finite alphabets cannot express.
The register count is statically bounded, so the automaton remains finite-state
in its control structure — only the register contents are drawn from the
infinite domain.

#### T3 — Bounded Checking

Semi-decidable properties — those in RE \ R, recognizable but not decidable —
arise when guards quantify universally or existentially over domains whose size
is not known at compile time. The halting predicate `halts(x)` is the textbook
example: verifying that a term eventually reaches a normal form requires
exploring an unbounded rewrite graph.

To see why, consider what "checking halts(x)" actually requires. A term
rewrite system generates a chain of successor terms — each application of a
rewrite rule produces the next term in the sequence:

    t₀ → t₁ → t₂ → ⋯

Asking "does this chain ever reach a halted (normal-form) state?" means
searching for a fixed point in this sequence. But the sequence may be infinite:
the term may grow without bound, cycle through an unbounded orbit, or diverge
in some other way. No finite algorithm can explore an infinite graph in
general — this is precisely why the halting property is semi-decidable (we can
confirm halting if it happens, but we cannot confirm non-halting in bounded
time).

The bounded checking strategy (§11, T3) exploits a simple but powerful insight:
if we restrict our search to the first **k** rewrite steps, the reachable state
space is guaranteed finite. Concretely, if each call to `reduce()` produces at
most **b** successor terms (the branching factor), then the rewrite graph
within k steps contains at most **k · b** nodes. A finite graph can always be
exhaustively searched — the bound converts an infinite search problem into a
finite one.

An analogy may help. Imagine searching for an exit in a maze that might be
infinite. Without a step budget you might walk forever. With a budget of k
corridor segments, exactly three outcomes are possible: (1) you find the exit
within k segments — success; (2) you explore every reachable corridor within k
segments and none leads to an exit — definite failure within the bound; or
(3) you exhaust your budget with unexplored corridors still remaining — you
simply cannot tell whether an exit exists further on.

This transformation is **sound** — `True` and `False` within the bound are
always correct — but **incomplete**: the property might hold at step k+1, yet
we will never observe it. The bound k is a resource parameter through which the
user trades completeness for guaranteed termination.

The bound k is either user-specified via bounded quantification (e.g.,
`exists(y, 100, halts(y))`) or inferred from the guard's quantifier structure
when no explicit bound is given.

The evaluation has three possible outcomes, encoded as `TriState`:

- **`True`:** the property holds — the BFS found a witness within the bound.
- **`False`:** the property does not hold — the BFS exhausted the reachable
  state space within the bound without finding a witness, proving the property
  false over the bounded domain.
- **`Unknown`:** the depth limit was reached before the search completed. The
  property may or may not hold — we simply cannot tell within k steps. The
  Comm rule conservatively does not fire, ensuring soundness.

The soundness guarantee is critical: `True` and `False` are always correct
(within the bounded domain). Only `Unknown` introduces approximation, and it
always errs on the side of caution (not firing the rule).

The implementation uses breadth-first search over the term rewrite graph. Each
call to `reduce()` produces the set of successor terms (one rewrite step). The
`visited` set prevents re-exploration of shared subterms (DAG structure),
bounding the work to O(k · |value|):

```
bounded_check(x: Term, k: ℕ) → TriState
  visited ← ∅;  queue ← [(x, 0)]
  while queue ≠ ∅ do
    (term, depth) ← dequeue(queue)
    if depth > k then return unknown
    if is_halted(term) then return true
    if term ∉ visited then
      visited ← visited ∪ {term}
      ∀ t ∈ reduce(term):
        enqueue(queue, (t, depth + 1))
  return false
```

The choice of BFS (rather than DFS) ensures that the depth bound is respected
uniformly — all terms at depth d are explored before any at depth d+1, so
`Unknown` is only returned when the frontier genuinely exceeds the bound. In
the actual implementation, `evaluate_quantified()` from LogicT handles the
domain enumeration and depth tracking, with the `TriState` result threaded
through the `QuantifiedFormula` evaluator.

#### T4 — User Assertion

By Rice's theorem (1953), for any non-trivial semantic property of programs,
membership is undecidable. When the pipeline classifies a guard as T4 — e.g.,
unbounded universal quantification over an infinite domain with nested
quantifiers — no compilation strategy can produce a sound and complete checker.

Rather than rejecting such guards outright, the system provides an escape
hatch: `assert_pred()`, which trusts the user's annotation that the property
holds. This is analogous to Rust's `unsafe` keyword or Coq's `Admitted`
tactic: the type system acknowledges its limitation and shifts the correctness
burden to the programmer.

The MSO01 lint fires at compile time if the T4 guard is not accompanied by a
Rocq proof certificate, alerting the user that the guard's correctness is
unverified. If a certificate is provided, it is checked during macro expansion;
a valid proof silences the lint and provides the same confidence as T1–T3
evaluation — the only difference is that the proof obligation was discharged
externally rather than by the automaton tower:

```
assert_pred(value: Term) → 𝔹
  ▷ trust user annotation or Rocq proof certificate; MSO01 lint if absent
  return true
```

Runtime cost is O(1) — trivially. The correctness guarantee depends entirely
on the quality of the user's proof or assertion. This is the least automated
tier but the most expressive: any predicate whatsoever can be guarded, provided
the user accepts responsibility for its truth.

#### Tier Override Directive — `#[tier(...)]`

The compiler's structural analysis is deliberately conservative: it assigns the
*highest* (least decidable) tier that is provably sound for a given predicate
shape. This is the right default — over-classifying a guard as more decidable
than it actually is would silently introduce unsound evaluation — but it creates
friction in edge cases where the programmer possesses domain knowledge that the
compiler cannot infer. For example:

- A quantifier ranges over a domain that is *effectively* finite at runtime
  (e.g., a graph whose size is bounded by an external invariant), but the type
  system sees an unbounded domain → the compiler assigns T4.
- A predicate has a known decision procedure (published in a textbook or proved
  in Rocq), but the compiler's structural heuristics do not recognise the
  pattern → the compiler assigns T3 or T4.
- An experimental guard should be conservatively *upgraded* to T4 during
  development, even though the compiler would assign T2.

The existing mechanisms address specific instances of this problem — `Bounded`
wraps a quantifier with an explicit depth limit (T4→T3), and `assert_pred`
trusts the user unconditionally (any tier → T4 semantics). The `#[tier(...)]`
directive **unifies and generalises** these mechanisms into a single, explicit
annotation that works in any direction, carries optional proof certificates, and
integrates with the lint infrastructure.

##### Syntax

The directive is an attribute on a predicate definition or an inline guard
expression:

```
#[tier(T3)]                          // single-step downgrade
#[tier(T3, bound = 500)]             // downgrade with explicit iteration bound
#[tier(T2, force)]                   // multi-step downgrade (requires force)
#[tier(T2, proof = "path.rocq")]     // downgrade with proof certificate
#[tier(T4)]                          // conservative upgrade (always allowed)
```

The general form is:

```
#[tier( <target-tier> [, bound = <k>] [, force] [, proof = "<path>"] )]
```

where:

| Parameter       | Type      | Required                   | Description                                               |
|-----------------|-----------|----------------------------|-----------------------------------------------------------|
| `<target-tier>` | `T1`–`T4` | Yes                        | The tier the programmer asserts this predicate belongs to |
| `bound = <k>`   | `usize`   | If target is T3            | Explicit iteration depth limit for bounded checking       |
| `force`         | flag      | If downgrade spans >1 tier | Acknowledges multi-step override risk                     |
| `proof = "<p>"` | string    | No                         | Path to a Rocq proof certificate of the claimed tier      |

##### Override Direction Rules

The safety of a tier override depends on its *direction*. Downward overrides
(toward more decidable tiers) weaken soundness guarantees and require
increasingly explicit opt-in; upward overrides (toward less decidable tiers) are
always safe — they simply trade performance for conservatism.

| Override Direction | Example                   | Allowed? | Requirements          | Lint             |
|--------------------|---------------------------|----------|-----------------------|------------------|
| Single-step down   | T4→T3, T3→T2, T2→T1       | Yes      | —                     | TIER01 (warning) |
| Multi-step down    | T4→T2, T4→T1, T3→T1       | Yes      | `force` flag required | TIER01 (warning) |
| Upward             | T1→T2, T2→T3, T3→T4, etc. | Yes      | —                     | No lint          |
| Identity           | T3→T3                     | Yes      | —                     | No lint (no-op)  |

**Proof certificates**: when a `proof = "path.rocq"` parameter is supplied, the
macro-expansion phase validates the certificate against the predicate's AST. A
valid proof **silences** the TIER01 lint entirely — the override is no longer
an unverified trust assumption but a machine-checked guarantee. An invalid or
missing certificate re-enables the lint.

##### Semantic Specification

Each target tier determines the *code shape* that the guard codegen emits,
regardless of the compiler's inferred tier:

**Override to T1** — the programmer asserts that the predicate is ground-
decidable at macro-expansion time. The guard codegen evaluates the predicate
statically and eliminates the guard entirely (constant-folds to `true` or
`false`). If the predicate is *not* actually ground-decidable, macro expansion
fails with an error — this is the only target tier that provides an automatic
soundness check without a proof certificate.

**Override to T2** — the programmer asserts that a decision procedure exists and
terminates for all inputs. The guard codegen emits a decidable guard function
(inline arithmetic, Ascent join clause, or register-machine check) with no
depth bound. The programmer accepts responsibility for termination — if the
predicate does not actually terminate, the generated guard will loop at runtime.

**Override to T3** — the programmer asserts that bounded evaluation is
meaningful. The guard codegen emits a bounded checker with the depth limit
specified by `bound = k`. If `bound` is omitted, the compiler emits a hard
error (`#[tier(T3)]` without `bound` is ambiguous — the whole point of T3 is
explicit resource bounding). The checker returns `TriState`:

- `True` — predicate verified within k steps.
- `False` — predicate refuted within k steps.
- `Unknown` — depth limit exhausted; Comm rule conservatively does not fire.

**Override to T4** — the programmer requests the most conservative tier. The
guard codegen emits an `assert_pred` wrapper that unconditionally returns
`true`, placing full correctness responsibility on the programmer (or on an
external proof certificate). This is useful during development: marking an
experimental guard as T4 ensures it never silently blocks rule firing while
the predicate's properties are still being investigated.

##### Examples

**T4→T3 override with explicit bound.** The compiler classifies `reachable` as
T4 (unbounded transitive closure over an infinite graph type), but the
programmer knows the runtime graph has at most 1000 nodes:

```rust
#[tier(T3, bound = 1000)]
guard(forall(v, vertices, entails(reachable(src, v), safe(v))))
```

Generated code (bounded checker):

```
guard_reachable_safe(src: Term, vertices: [Term], k: ℕ = 1000) → TriState
  ∀ v ∈ vertices:
    result ← check_reachable_bounded(src, v, k)
    case result of
      true    → if ¬evaluate_safe(v) then return false ▷ reachable ∧ ¬safe
      unknown → return unknown                         ▷ depth exhausted
      false   →                                        ▷ vacuously true
  return true
```

**T4→T2 multi-step override with proof certificate.** The compiler classifies
a normalization predicate as T4 (potentially non-terminating rewrite), but the
programmer has a Rocq proof of strong normalisation for the type system's term
language:

```rust
#[tier(T2, force, proof = "proofs/strong_normalisation.rocq")]
guard(is_normalising(term))
```

Generated code (decidable guard — no depth bound):

```
guard_is_normalising(term: Term) → 𝔹
  ▷ termination guaranteed by strong_normalisation.rocq certificate
  nf ← reduce_to_normal_form(term)
  return nf ≠ ⊥
```

Because a valid proof certificate is provided, the TIER01 lint is silent.

##### TIER01 Lint — Unverified Tier Override

**Diagnostic code:** `TIER01`
**Severity:** Warning
**Fires when:** A `#[tier(...)]` directive specifies a *downward* override
(lower tier than the compiler infers) **without** a valid `proof` certificate.

**Message format:**

```
warning[TIER01]: unverified tier override
  --> grammar.rs:42:5
   |
42 |     #[tier(T2, force)]
   |     ^^^^^^^^^^^^^^^^^^ compiler infers T4, override claims T2
   |
   = note: override trusts programmer assertion; provide `proof = "..."` to silence
   = help: add a Rocq proof certificate, or verify manually that the predicate
           is decidable for all inputs
```

**Suppression:** Providing a `proof = "path.rocq"` parameter that passes
certificate validation silences TIER01. The lint does **not** fire for upward
overrides (those are always sound) or identity overrides (no-ops).

##### Relationship to Existing Mechanisms

The `#[tier(...)]` directive subsumes the two existing override mechanisms and
the proposed `#[assert_decidable]` annotation:

| Existing Mechanism                      | Equivalent `#[tier(...)]` Form                               | Notes                                                                                                                                                          |
|-----------------------------------------|--------------------------------------------------------------|----------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `exists(y, 100, p(y))` (explicit bound) | `#[tier(T3, bound = 100)]` on an unbounded `exists(y, p(y))` | `#[tier(T3, bound = k)]` separates the bound from the quantifier syntax, allowing the same predicate to be evaluated at different bounds in different contexts |
| `assert_pred(value)` (T4 trust)         | `#[tier(T4)]` on any predicate                               | Semantically identical — both emit an unconditional `true` wrapper. The directive form makes the trust assumption visible and greppable                        |
| `#[assert_decidable]` (MSO01 docs)      | `#[tier(T2)]` or `#[tier(T3)]` depending on intent           | The MSO01-proposed annotation lacked precision about *which* decidable tier was claimed; `#[tier(...)]` requires an explicit target, eliminating ambiguity     |

When `#[tier(...)]` is implemented, the `Bounded` wrapper in the `BehavioralPred`
AST remains as the *syntactic* mechanism for inline bounds (e.g.,
`exists(y, 100, ...)`), while `#[tier(T3, bound = k)]` serves as the
*attribute* mechanism for the same
semantics. Both paths converge in `generate_guard_function()` at the T3 codegen
branch. The `assert_pred` function remains as the T4 codegen target — `#[tier(T4)]`
simply routes through it explicitly rather than as a fallback.

### Guard Codegen Architecture ([`guard_codegen.rs`](../../macros/src/gen/runtime/guard_codegen.rs))

The actual implementation in [guard_codegen.rs](../../macros/src/gen/runtime/guard_codegen.rs) provides:

**Entry point:** `generate_guard_codegen(language)` — scans all term rules for
`TermParam::GuardBody` constructors, classifies each guard, and emits per-tier
evaluation functions as a `TokenStream`.

**Tier classification:** `classify_guard_tier(pred) → GuardTier`

```rust
enum GuardTier { T1Static, T2Decidable, T3Bounded, T4Assert }
```

The classifier walks the `BehavioralPred` AST:
- T1: `is_statically_decidable()` detects tautologies (`P ∨ ¬P`) and contradictions (`P ∧ ¬P`)
- T2: `RelationQuery` or `AcMatch` — finite joins decidable at runtime
- T3: `Quantified` with `bound: Some(k)`, or unbounded with T1/T2 body
- T4: Nested quantifiers or other undecidable structures

**T1 elimination:** `evaluate_static_guard(pred: φ) → (𝔹 | ⊥)` returns
`Some(true)` for tautologies, `Some(false)` for contradictions. In
`generate_guarded_comm_rules()`, always-false guards skip rule generation entirely,
and always-true guards emit only the structural Comm rule (no behavioral check).

**T2 fast path:** `can_compile_to_ascent_join(pred) → bool` detects guards
that can be lowered directly to Ascent join clauses. For non-negated
`RelationQuery { name, args }`, the generated code is:

```rust
// Ascent join clause (inside Comm rule body):
relation_name(arg_expr_1, arg_expr_2)
```

This uses Ascent's native hash-indexed semi-join — O(1) per lookup.

**T3 TriState:** The `TriState` enum (`True | False | Unknown`) is generated
as part of the guard codegen output. T3 guard functions use `evaluate_quantified()`
from LogicT with the specified depth limit. When the domain enumeration returns
fewer tuples than the limit, the result is definitive; at the limit,
`TriState::Unknown` triggers conservative behavior (Comm rule does not fire).

**Standalone guard functions:** Each guard also gets a standalone `__guard_N()`
function with signature:

```
guard_N(relation_query: (String, [String]) → 𝔹,
        domain_enumerate: (String) → Set<Tuple>,
        env: Map<String, String>) → 𝔹              // or TriState for T3
```

These functions serve testing, external callers, and the selectivity analysis
pipeline. The primary evaluation path for T2 guards uses inline Ascent joins.

### Guard Selectivity and Ordering

When multiple guards protect the same channel, `estimate_selectivity(pred) → f64`
computes a heuristic selectivity value in [0.0, 1.0]:

| Guard Structure            | Selectivity      | Rationale                 |
|----------------------------|------------------|---------------------------|
| Negated RelationQuery      | 0.1              | Rejects most inputs       |
| Positive RelationQuery     | 0.5              | Moderate (half of domain) |
| And(a, b)                  | sel(a) × sel(b)  | Independent conjunction   |
| Or(a, b)                   | 1 − (1−sa)(1−sb) | Independent disjunction   |
| ForAll (bounded/unbounded) | 0.05/k^0.5       | Very selective            |
| Exists (bounded/unbounded) | 0.3/k^0.5        | Moderate                  |
| AcMatch { elements }       | 0.3/\|elements\| | Depends on bag size       |
| Not(inner)                 | 1 − sel(inner)   | Complement                |

`estimate_guard_cost(pred) → u32` provides a tiebreaker for equal selectivity.

`order_guards_by_selectivity()` sorts guards by:
1. Primary: lowest selectivity first (most selective)
2. Secondary: lowest cost first (cheapest)

For And-conjunctions in the T2 fast path (`compile_guard_to_ascent_clauses`),
conjuncts are reordered by selectivity so the most selective clause appears
first in the Ascent rule body, enabling earlier short-circuit pruning.

### Guard Set Analysis

`analyze_guard_set(guards) → GuardSetAnalysis` performs compile-time analysis
on the guard set for a channel:

```rust
struct GuardSetAnalysis {
    dead_guards: Vec<usize>,       // SYM01: unsatisfiable
    overlapping_pairs: Vec<(usize, usize)>,  // SYM02: ambiguous dispatch
    subsumed_pairs: Vec<(usize, usize)>,     // SYM03: redundant guard
    has_always_true: Vec<usize>,   // T1 tautologies
    has_always_false: Vec<usize>,  // T1 contradictions
}
```

Diagnostics are emitted during `generate_guarded_comm_rules()`:
- **SYM01** (Warning): Guard is unsatisfiable — receive will never fire
- **SYM02** (Warning): Guards overlap — may cause ambiguous dispatch
- **SYM03** (Note): Guard is subsumed by another — it is redundant

The current analysis uses structural comparison of `BehavioralPred` nodes.
For complement detection (`RelationQuery` with opposite negation), the analysis
is exact. For complex predicates, the SFA-based analysis (once compiled to
`SymbolicAutomaton`) provides exact satisfiability, overlap, and subsumption
checks via SFA intersection and emptiness tests.

With the guard infrastructure defined, the next section clarifies when each
component operates — compile time vs. runtime.

---

## 14. Compile-Time vs Runtime Boundary

The predicated types system has a sharp two-phase architecture:

- **Compile time** (`cargo build`): The `language!` proc macro invokes the
  PraTTaIL pipeline — grammar analysis, automaton construction, decidability
  classification, lint emission, guard optimization, and Rust code generation.
  All `prattail/` and `macros/` code executes here. None of it appears in the
  compiled binary.
- **Runtime** (program execution): Only generated code runs — pattern matching
  methods, Comm rules, guard functions, substitution, normalization.
- **Boundary**: The `TokenStream` returned by the proc macro. Everything
  upstream is compile-time infrastructure; everything downstream is runtime
  artifact.

The following table summarizes where each subsystem operates. For detailed
discussion, see the referenced section.

| Subsystem                              | Compile-Time Role                                            | Runtime Role                                  | Section  |
|----------------------------------------|--------------------------------------------------------------|-----------------------------------------------|----------|
| Surface syntax parsing                 | Pratt parser in proc macro                                   | —                                             | §2       |
| Guard predicate sublanguage            | Parse `where` clause: `not`, `and`, `or`, `forall`, `exists` | —                                             | §2       |
| Guard configuration (`guards {}`)      | Parse connectives, predicates, theories; theory routing      | —                                             | §2A      |
| Theory-guided LogicT pruning           | Type→theory map construction; TriState refinement analysis   | Domain pruning via `propagate()` before eval  | §14A     |
| Term AST / `PGuardedInput`             | Enum variant generation                                      | —                                             | §4       |
| `match_pattern` / `match_pattern_name` | Code generation (per-category methods)                       | Ground-vs-pattern matching per Comm fire      | §5       |
| `MatchBindings`                        | —                                                            | Accumulates bindings during matching          | §5       |
| Guarded Comm rules                     | Ascent clause generation                                     | Fires during fixpoint evaluation              | §6       |
| Substitution + normalization           | —                                                            | Per-fire: `multi_substitute` + `.normalize()` | §6       |
| Behavioral predicate joins             | Ascent join clause generation                                | O(1) hash lookup in Ascent relation           | §8       |
| Quantified predicates                  | `QuantifiedFormula` AST construction                         | `evaluate_quantified()` via LogicT            | §8       |
| AC-matching                            | Partition codegen                                            | `multiset_select()` per Comm fire             | §8       |
| Decidability classification (T1–T4)    | Formula analysis → tier assignment                           | —                                             | §11      |
| Guard codegen (T1)                     | Static evaluation → dead-code elim                           | — (zero overhead)                             | §13      |
| Guard codegen (T2)                     | SFA/range/register compilation                               | Guard function: O(1)–O(\|value\|)             | §13      |
| Guard codegen (T3)                     | Bounded automaton compilation                                | BFS with depth counter: O(k·\|value\|)        | §13      |
| Guard codegen (T4)                     | Lint MSO01, Rocq certificate check                           | `assert_pred()` returns true (trust)          | §13      |
| Pipeline (Stages 1–5)                  | Parse → Classify → Compile → Optimize → Codegen              | —                                             | §12      |
| BooleanAlgebra + SFA ops               | `is_satisfiable`, intersect, minimize                        | —                                             | §15      |
| ConstraintTheory suite                 | Propagate, label, witness                                    | —                                             | §16      |
| Automata modules (M1–M15)              | Guard analysis + dispatch                                    | —                                             | §17      |
| Selectivity estimation (M7)            | Ordering decision at compile time                            | Evaluation order at runtime                   | §13, §17 |
| Predicate dispatch controller          | Feature extraction + module activation                       | —                                             | §17      |
| All lints (SYM, MSO, PT, RA, …)        | Diagnostic emission at `cargo build`                         | —                                             | §19      |
| Unification (Martelli-Montanari)       | Pattern overlap analysis (UN01–03)                           | Optional: unification-based matching          | §16      |
| LogicT / `LogicStream`                 | Fair search for CT satisfiability                            | `∀`/`∃` guard evaluation                      | §16      |
| Forward-Backward analysis              | Hot/cold path classification                                 | `#[inline]`/`#[cold]` annotations             | §17      |
| `is_refined_*` relations               | Ascent relation generation                                   | Per-tuple predicate evaluation                | §22      |
| Rocq formal proofs                     | Property verification                                        | — (not in binary)                             | §16, §22 |

Rows with both columns filled have a **dual nature** ("codegen"): compiled as
proc macro logic, they emit `TokenStream` fragments that execute at runtime.
Rows with "—" in the Runtime Role column produce **zero runtime overhead** —
no generated code, no data structures, no per-value cost in the binary. This
includes all automata modules (M1–M15), BooleanAlgebra + SFA, all
ConstraintTheory implementations, the dispatch controller, all 30+ lint codes,
and all Rocq proofs.

Three components span both phases:

- **LogicStream<T>**: Compile-time fair backtracking for `TheoryAlgebra::label()`
  satisfiability; runtime `evaluate_quantified()` for `∀`/`∃` guards (`gnot`,
  `interleave`, `collect_bounded`). When a registered `ConstraintTheory` (from
  `guards { theories {} }`, §2A) matches the guard's typed predicates, the
  runtime path gains **theory-guided domain pruning**: `propagate()` narrows
  the enumeration domain before LogicT explores it. See §14A for the full
  theory-guided evaluation pipeline.
- **Unification**: Compile-time pattern overlap detection (UN01–03); runtime
  unification-based matching if enabled (e.g., MeTTa).
- **Forward-Backward**: Compile-time hot/cold path classification; runtime
  effect is `#[inline]`/`#[cold]` annotations on generated guard functions
  (analysis code itself is not in the binary).

For the end-to-end flow diagram, see §1A (End-to-End Composition Diagram).

---

## 14A. LogicT Theory Integration

### Motivation

The `guards { theories {} }` block (§2A) registers `ConstraintTheory`
implementations per type category. When combined with typed predicates in
`guards {}` predicate definitions, the pipeline gains **theory-guided domain pruning**
at runtime: instead of enumerating all tuples in a domain and checking each
against a guard predicate, the registered theory's `propagate()` narrows the
domain *before* enumeration, and `label()` generates only satisfying
assignments. This section documents the full theory-guided LogicT evaluation
pipeline, TriState refinement, and the refinement type bridge.

### Architecture Diagram — Theory-Guided LogicT Evaluation

The following diagram traces the data flow from a `guards { theories {} }`
declaration through typed predicate matching, constraint theory invocation,
and LogicT evaluation. Read top-to-bottom:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                  Theory-Guided LogicT Evaluation Pipeline                   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  guards { theories { arithmetic = PresburgerAlgebra for [Int]; } }           │
│                              │                                              │
│                              ▼                                              │
│  ┌──────────────────────────────────────────┐                               │
│  │  Typed Predicate: gt . x: Int, y: Int    │                               │
│  │  Guard:  forall(y: Int, nodes, gt(y, 0)) │                               │
│  └──────────────┬───────────────────────────┘                               │
│                 │                                                           │
│        ┌────────┴─────────┐                                                 │
│        ▼                  ▼                                                 │
│  ┌────────────┐    ┌────────────────┐                                       │
│  │ Type→Theory│    │ PredicateSigna-│                                       │
│  │ Routing    │    │ ture Module    │                                       │
│  │            │    │ Activation     │                                       │
│  │ Int → M12  │    │ → M12_PRESB    │                                       │
│  │ (Presburger│    │ → M3_AWA       │                                       │
│  │  Algebra)  │    │   (∀ branch)   │                                       │
│  └──────┬─────┘    └────────────────┘                                       │
│         │                                                                   │
│         ▼                                                                   │
│  ┌──────────────────────────────────────────────────────┐                   │
│  │              ConstraintTheory Protocol               │                   │
│  │                                                      │                   │
│  │  1. propagate(store, gt(y, 0))                       │                   │
│  │     → Refined store: { y ∈ ℤ | y > 0 }               │                   │
│  │                                                      │                   │
│  │  2. is_consistent(refined_store) → true              │                   │
│  │                                                      │                   │
│  │  3. label(refined_store) → LogicStream<Constraint>   │                   │
│  │     generates: y=1, y=2, y=3, ...                    │                   │
│  │     (type-specific: only positive integers)          │                   │
│  └──────────────────────┬───────────────────────────────┘                   │
│                         │                                                   │
│                         ▼                                                   │
│  ┌──────────────────────────────────────────────────────┐                   │
│  │                LogicT Evaluation                     │                   │
│  │                                                      │                   │
│  │  evaluate_quantified(                                │                   │
│  │    ForAll { var: "y", domain: pruned_nodes, ... },   │                   │
│  │    env, relation_query, domain_enumerate, bound      │                   │
│  │  )                                                   │                   │
│  │                                                      │                   │
│  │  Domain "nodes" is PRUNED: only y > 0 candidates     │                   │
│  │  instead of all tuples. Fair conjoin explores        │                   │
│  │  remaining candidates via interleave scheduling.     │                   │
│  └──────────────────────┬───────────────────────────────┘                   │
│                         │                                                   │
│                         ▼                                                   │
│                  ┌───────────────┐                                          │
│                  │  Guard Result │                                          │
│                  │  true / false │                                          │
│                  │  / TriState   │                                          │
│                  └───────────────┘                                          │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Component Diagram — ConstraintTheory Ecosystem

This diagram shows the three built-in `ConstraintTheory` implementations,
how they compose through the `ConstraintTheory` trait, and how
`TheoryAlgebra<T>` bridges them into the `BooleanAlgebra`/SFA pipeline:

```
┌────────────────────────────────────────────────────────────┐
│                    guards { theories { } }                 │
│                                                            │
│  ┌──────────────────┐  ┌──────────────┐  ┌──────────────┐  │
│  │ PresburgerAlgebra│  │Unification   │  │LatticeTheory │  │
│  │ for [Int]        │  │Theory        │  │for [Proc,    │  │
│  │                  │  │for [Proc,    │  │Name,Int,Str] │  │
│  │ Constraint:      │  │Name]         │  │              │  │
│  │  LinearExpr<i64> │  │              │  │ Constraint:  │  │
│  │                  │  │ Constraint:  │  │  SubtypeRel  │  │
│  │ propagate:       │  │  Unifier<T>  │  │              │  │
│  │  Gaussian elim   │  │              │  │ propagate:   │  │
│  │                  │  │ propagate:   │  │  LUB/GLB     │  │
│  │ label:           │  │  Robinson    │  │              │  │
│  │  integer ranges  │  │  unification │  │ label:       │  │
│  │                  │  │              │  │  lattice     │  │
│  │ evaluate:        │  │ label:       │  │  walk        │  │
│  │  i64 comparison  │  │  match split │  │              │  │
│  └────────┬─────────┘  └──────┬───────┘  └──────┬───────┘  │
│           │                   │                 │          │
│           └───────────────────┼─────────────────┘          │
│                               │                            │
│                               ▼                            │
│                  ┌──────────────────────────┐              │
│                  │ impl ConstraintTheory    │              │
│                  │ ─────────────────────    │              │
│                  │ type Constraint          │              │
│                  │ type Assignment          │              │
│                  │ type Store               │              │
│                  │                          │              │
│                  │ propagate(store, c)      │              │
│                  │ is_consistent(store)     │              │
│                  │ witness(store)           │              │
│                  │ label(store)→LogicStream │              │
│                  │ evaluate(c, assign)      │              │
│                  └────────────┬─────────────┘              │
│                               │                            │
│                               ▼                            │
│                  ┌────────────────────────┐                │
│                  │ TheoryAlgebra<T>       │                │
│                  │ ────────────────       │                │
│                  │ impl BooleanAlgebra    │                │
│                  │                        │                │
│                  │ is_satisfiable(φ)      │                │
│                  │ witness(φ)             │                │
│                  │ and/or/not/complement  │                │
│                  └────────────┬───────────┘                │
│                               │                            │
│                               ▼                            │
│                  ┌────────────────────────┐                │
│                  │ SFA / Pipeline         │                │
│                  │ ──────────────         │                │
│                  │ Satisfiability check   │                │
│                  │ Dead-rule detection    │                │
│                  │ Guard optimization     │                │
│                  └────────────────────────┘                │
└────────────────────────────────────────────────────────────┘
```

### How Typed Predicates Enhance LogicT

**1. Theory-guided domain restriction.** For
`forall(y: Int, nodes, gt(y, 0))`, the typed parameter `y: Int` tells LogicT
that `y` ranges over `Int` values. Combined with
`theories { arithmetic = PresburgerAlgebra; }`, LogicT can use `propagate()`
from `PresburgerAlgebra` to prune the domain before enumeration:

```rust
// Instead of: enumerate ALL tuples in "nodes", then check gt(y, 0)
// Do: propagate constraint gt(_, 0) through PresburgerAlgebra,
//     then enumerate only satisfying tuples
```

This is implemented via the existing `ConstraintTheory::propagate()` +
`ConstraintTheory::label()` protocol. `propagate` narrows the store;
`label` generates satisfying assignments. The typed predicate tells the
pipeline which theory to use for propagation.

**2. Type-specific `label()` generators.** `ConstraintTheory::label()` returns
a `LogicStream<Constraint>` — the non-deterministic choices for search. With
typed predicates, the theory can generate type-appropriate choices:

- `PresburgerAlgebra::label()` generates integer assignments satisfying linear
  constraints
- `LatticeTheory::label()` generates type assignments consistent with the
  subtype lattice
- `UnificationTheory::label()` generates unifier candidates

Without typed predicates, `label()` must guess the domain. With them, it
knows exactly what to generate.

**3. `RefinementTypeSystem` bridge.** The existing
`RefinementTypeSystem<S, T>` in [`type_system.rs`](../../prattail/src/type_system.rs) composes a base `TypeSystem`
with a `ConstraintTheory`. Typed predicates in guards create a natural bridge:

- A guard `where gt(x, 0)` on a channel typed `{ x: Int | x > 0 }`
  (refinement type) → the guard predicate `gt(x, 0)` IS the refinement
  predicate
- The pipeline can recognize this identity and use `predicate_entails()` from
  `RefinementTypeSystem` to prove the guard is subsumed by the refinement
  type → the guard can be statically eliminated (T1 tier)

This requires typed predicates to carry enough information for the pipeline
to match guard predicates against refinement type predicates.

**4. TriState refinement.** The T3 `TriState` evaluation
(True/False/Unknown) can benefit from typed predicates: when
`TriState::Unknown` is returned (depth limit exceeded), the theory can
attempt a decidable analysis using `propagate()` on the typed predicate's
theory. If the theory's `is_consistent()` returns false, the unknown can be
refined to `False`.

### TriState Refinement Diagram

The following diagram shows how a T3 guard evaluation that returns
`TriState::Unknown` (due to depth limit) can be refined to `False` via
constraint theory decidability analysis:

```
┌──────────────────────────────────────────────────┐
│         TriState Refinement via Theory           │
├──────────────────────────────────────────────────┤
│                                                  │
│  T3 Guard Evaluation:                            │
│  forall(y: Int, nodes _{k=100}, gt(y, 0))        │
│                                                  │
│       ┌──────────┐                               │
│       │ LogicT   │                               │
│       │ evaluate │                               │
│       └────┬─────┘                               │
│            │                                     │
│    ┌───────┼───────────┐                         │
│    │       │           │                         │
│    ▼       ▼           ▼                         │
│   True   False       Unknown                     │
│    │       │          (limit hit)                │
│    │       │           │                         │
│    │       │           ▼                         │
│    │       │  ┌──────────────────┐               │
│    │       │  │ Theory Refinement│               │
│    │       │  │                  │               │
│    │       │  │ propagate(store, │               │
│    │       │  │   gt(y,0))       │               │
│    │       │  │ is_consistent?   │               │
│    │       │  └────────┬─────────┘               │
│    │       │           │                         │
│    │       │     ┌─────┴─────┐                   │
│    │       │     │           │                   │
│    │       │  consistent  inconsistent           │
│    │       │     │           │                   │
│    │       │  Unknown     False                  │
│    │       │  (genuine)   (refined!)             │
│    │       │     │           │                   │
│    ▼       ▼     ▼           ▼                   │
│ ┌──────────────────────────────────┐             │
│ │ Final:  True │ False │ Unknown   │             │
│ │ Action: fire │ skip  │ conserv.  │             │
│ │         cont │ rule  │ fire cont │             │
│ └──────────────────────────────────┘             │
└──────────────────────────────────────────────────┘
```

### Refinement Type Bridge Diagram

When a guard predicate is identical to the refinement predicate of the
channel's type, the pipeline can statically eliminate the guard (T1 tier,
zero runtime cost):

```
┌──────────────────────────────────────────────────────────────┐
│          Refinement Type ↔ Guard Predicate Bridge            │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│  Type declaration:                                           │
│    types { PosInt = { x: Int | x > 0 }; }                    │
│                                                              │
│  Guard:                                                      │
│    for (@val <- ch) where gt(val, 0) { P }                   │
│                                                              │
│  Channel type: ch : Channel<PosInt>                          │
│                                                              │
│  ┌───────────────────┐    ┌───────────────────┐              │
│  │ Refinement Type   │    │ Guard Predicate   │              │
│  │ { x: Int | x > 0 }│    │ gt(val, 0)        │              │
│  └────────┬──────────┘    └────────┬──────────┘              │
│           │                        │                         │
│           └───────────┬────────────┘                         │
│                       │                                      │
│                       ▼                                      │
│        ┌──────────────────────────────┐                      │
│        │ predicate_entails(           │                      │
│        │   premise:  x > 0,           │                      │
│        │   conclusion: val > 0        │                      │
│        │ ) → true (same predicate)    │                      │
│        └──────────────┬───────────────┘                      │
│                       │                                      │
│                       ▼                                      │
│          Guard subsumed by type ⟹                            │
│          compile-time elimination (T1 Static)                │
│          Zero runtime cost for this guard                    │
└──────────────────────────────────────────────────────────────┘
```

### Worked Examples

**Example 1: Theory-guided domain pruning (Rholang)**

Guard: `forall y in nodes. (gt(y, 0))`
With: `theories { arithmetic = PresburgerAlgebra for [Int]; }`

1. Pipeline sees `forall` → activates M3 (AWA), plus typed `y: Int` →
   activates M12 (Presburger) via theory routing
2. At runtime, `evaluate_quantified()` is called with domain `nodes`
3. Before enumerating, `PresburgerAlgebra::propagate(store, gt(y, 0))` refines
   the store to `{ y > 0 }`
4. `domain_enumerate("nodes")` returns only tuples where `y > 0` (pruned)
5. LogicT checks remaining candidates via fair conjoin — fewer candidates →
   faster convergence

Without typed predicates, the pipeline enumerates ALL `nodes` tuples and
checks `gt(y, 0)` for each — potentially much slower for large domains.

**Example 2: TriState refinement (MeTTa)**

Guard: `forall y _{k=100} in atoms. (compatible(y, target))`
With: `theories { types = LatticeTheory for [Atom]; }`

1. LogicT evaluates with bound k=100. If the domain has >100 elements,
   evaluation returns `TriState::Unknown`
2. Theory refinement: `LatticeTheory::propagate(store, compatible(y, target))`
   → if the refined store is inconsistent (e.g., no `Atom` is compatible with
   `target`), `Unknown` is refined to `False`
3. If consistent, `Unknown` remains — the guard fires conservatively

**Example 3: Refinement type bridge (Rholang)**

Type: `PosInt = { x: Int | x > 0 };`
Guard: `for (@val <- ch) where gt(val, 0) { P }`
Channel type: `ch : Channel<PosInt>`

1. Pipeline identifies that the guard predicate `gt(val, 0)` structurally
   matches the refinement predicate `x > 0` (modulo variable renaming)
2. `RefinementTypeSystem::predicate_entails(x > 0, val > 0)` returns true
3. The guard is classified as T1 (statically decidable) and eliminated entirely
4. Zero runtime cost — the type system guarantees every value on `ch` satisfies
   the guard

---

## 15. The BooleanAlgebra Framework

### Motivation

All guard analysis — satisfiability, subsumption, overlap detection,
equivalence — reduces to operations over Boolean algebras. The
`BooleanAlgebra` trait provides the algebraic foundation for the entire
predicated types pipeline. (For how SFA intersection supports guard
selectivity and overlap analysis, see §13.)

### The BooleanAlgebra Trait

The trait captures the algebraic structure `(P, ∧, ∨, ¬, ⊤, ⊥)` satisfying
De Morgan's laws, distributivity, and complementation — the minimal interface
needed to build Symbolic Finite Automata (SFAs) that operate over arbitrary
domains. The core insight is that SFA algorithms (determinization, minimization,
intersection, complement) need only these Boolean operations on transition
labels, not knowledge of the underlying domain. This makes the trait the single
extension point for adding new guard domains: implement `BooleanAlgebra` for
your domain, and all SFA operations work automatically. The `Predicate` type
represents guard conditions, while `Domain` represents the concrete values
those conditions constrain. The trait requires `Clone + Debug + Send + Sync`
because SFA operations may run in parallel during the compile-time pipeline
(§12, Stage 4).

The trait separates *core operations* (the Boolean algebra axioms) from
*derived operations* (which have default implementations using the core
methods). The core methods are the minimum an implementor must provide; the
derived methods offer convenience without additional implementation burden:

```rust
pub trait BooleanAlgebra: Clone + Debug + Send + Sync + 'static {
    type Predicate: Clone + Debug + Eq + Hash + Send + Sync + 'static;
    type Domain: Clone + Debug + Send + Sync + 'static;

    fn true_pred(&self) -> Self::Predicate;                            // ⊤
    fn false_pred(&self) -> Self::Predicate;                           // ⊥
    fn and(&self, a: &Self::Predicate, b: &Self::Predicate)
        -> Self::Predicate;                                            // ∧
    fn or(&self, a: &Self::Predicate, b: &Self::Predicate)
        -> Self::Predicate;                                            // ∨
    fn not(&self, a: &Self::Predicate) -> Self::Predicate;             // ¬
    fn is_satisfiable(&self, a: &Self::Predicate) -> bool;             // ∃x. a(x)
    fn witness(&self, a: &Self::Predicate) -> Option<Self::Domain>;    // satisfying element
    fn evaluate(&self, pred: &Self::Predicate, elem: &Self::Domain)
        -> bool;                                                       // membership test

    // Derived operations (default implementations):
    fn implies(&self, a: &Self::Predicate, b: &Self::Predicate) -> bool;
    fn equivalent(&self, a: &Self::Predicate, b: &Self::Predicate) -> bool;
    fn is_tautology(&self, a: &Self::Predicate) -> bool;
    fn overlaps(&self, a: &Self::Predicate, b: &Self::Predicate) -> bool;
}
```

The `is_satisfiable()` method is the critical decision procedure: it
determines whether a predicate can be satisfied by any element in the domain,
which is the foundation of guard liveness analysis (does this guard ever fire?)
and overlap detection (can two guards fire on the same input?). The `witness()`
method extends satisfiability with a concrete example, used for counterexample
generation in lints. The derived operations are implemented via the standard
Boolean reductions: `implies(a, b)` checks `¬is_satisfiable(a ∧ ¬b)`,
`equivalent(a, b)` checks `implies(a, b) ∧ implies(b, a)`, and
`is_tautology(a)` checks `¬is_satisfiable(¬a)`.

### Built-in Algebras

The pipeline ships with six `BooleanAlgebra` implementations covering the
common guard domains. The first five are *direct implementations* — they
implement the trait methods directly using domain-specific algorithms (interval
arithmetic, Unicode range operations, etc.). The sixth, `TheoryAlgebra<T>`, is
an *adapter* that wraps any `ConstraintTheory` (§16) into a `BooleanAlgebra`
via propagation and optional LogicT search, providing the extensibility bridge
for user-defined domains. The diagram below shows the algebra hierarchy and
the `SymbolicAutomaton<A>` type that is parameterized over any of these
algebras:

```
BooleanAlgebra trait
├── IntervalAlgebra ──── Domain: i64 ranges          (numeric guards)
├── CharClassAlgebra ─── Domain: Unicode chars        (structural patterns)
├── KatBooleanAlgebra ── Domain: propositional atoms  (behavioral predicates)
├── DispatchAlgebra ──── Domain: module signatures    (15-bit dispatch)
├── PresburgerAlgebra ── Domain: ℤⁿ linear constraints (multi-variable arithmetic)
└── TheoryAlgebra<T> ─── Domain: any ConstraintTheory (extensible)
         │
         ▼
SymbolicAutomaton<A: BooleanAlgebra>
├── determinize()        minterm-based partitioning
├── minimize()           Hopcroft equivalence
├── intersect()          guard conjunction
├── complement()         guard negation
├── is_equivalent()      guard equivalence
├── is_satisfiable()     guard liveness
└── witness()            counterexample generation
```

The `SymbolicAutomaton<A>` type is the central data structure: once a guard is
compiled to an SFA over any `BooleanAlgebra`, the full suite of automaton
operations (determinization, minimization, intersection, etc.) becomes
available without writing algebra-specific code. This is the payoff of the
algebraic abstraction — the O(n log n) Hopcroft minimization algorithm, for
example, is written once against the `BooleanAlgebra` trait and works for all
six algebras.

### Symbolic Finite Automata

A symbolic finite automaton (SFA) generalizes classical finite automata by
labeling transitions with predicates from a `BooleanAlgebra` instead of
concrete alphabet symbols. The theoretical foundation is D'Antoni and Veanes'
work on effective Boolean algebras (POPL 2014): any decidable Boolean algebra
can serve as the predicate language for SFA transitions, and the classical
automaton operations (determinization, minimization, intersection, complement)
lift to the symbolic setting with complexity proportional to the number of
*predicates* rather than the size of the *alphabet*. This is the key insight
that makes SFAs practical for guard compilation: a guard over all 64-bit
integers would require 2^64 explicit transitions in a classical DFA, but a
single `IntervalAlgebra` predicate like `x ∈ [5, 100)` in an SFA.

The formal definition mirrors the classical DFA tuple, with the transition
relation `δ` carrying a predicate label `P` on each edge:

```
SFA = (Q, q₀, F, δ)
  where δ ⊆ Q × P × Q
        P is a BooleanAlgebra predicate
```

A transition `(q, φ, q')` fires when the current input symbol satisfies
predicate `φ` (i.e., `algebra.evaluate(φ, symbol)` returns true). The
`is_satisfiable()` method on the algebra determines whether a transition can
ever fire, which is used during minimization to identify dead transitions. The
`witness()` method produces a concrete input that fires a given transition,
used for counterexample generation in lint diagnostics.

### Minterm-Based Determinization

Determinization of SFAs requires partitioning the input domain so that every
element in a partition cell behaves identically with respect to all transitions
from a given state set. Classical subset construction partitions by individual
alphabet symbols, but SFAs operate over potentially infinite domains where
enumeration is impossible. The solution, due to Veanes et al., is
**minterms** — maximal satisfiable conjunctions of predicate atoms and their
negations. Each minterm represents a region of the domain where every
predicate in the SFA evaluates to the same boolean value. For a set of `n`
predicates, there are at most 2^n minterms, but in practice many conjunctions
are unsatisfiable (detected via `is_satisfiable()`) and are pruned, yielding
far fewer minterms than the worst case.

The formal definition constructs each minterm by choosing a subset `S` of
predicates to include positively and complementing the rest:

```
minterm(S, S') = ⋀_{φ ∈ S} φ ∧ ⋀_{φ ∈ S'} ¬φ
  where S ⊆ atoms, S' = atoms ∖ S, is_satisfiable(minterm(S, S'))
```

The `is_satisfiable` guard ensures only non-empty minterms are retained. The
resulting set of minterms forms a partition of the domain: every domain element
belongs to exactly one minterm, and within each minterm, all SFA transitions
behave identically. This partitioning enables the standard powerset
construction to operate over minterms rather than individual symbols, yielding
a deterministic SFA with the same language as the original.

### SFA Compilation to Rust Match Statements

The final step of guard compilation for T2 guards is lowering the determinized,
minimized SFA into a Rust function. The `generate_sfa_transition_table()`
function in [`guard_codegen.rs`](../../macros/src/gen/runtime/guard_codegen.rs) emits a function that simulates the DFA by
iterating over the input value's symbols and matching against the transition
table. The intuition is that the DFA's state-transition graph becomes a nested
Rust `match` expression: the outer level dispatches on the current state, and
the inner level dispatches on the minterm partition that the current symbol
falls into. This encoding avoids the overhead of a generic automaton
interpreter (no vtable dispatch, no trait object indirection) — the entire
DFA is inlined as native Rust pattern matching.

The following generated function illustrates the pattern for a simple two-state
DFA with two minterms:

```
sfa_simulate(value: Term, δ: Table<(State, Minterm) → State>, F: Set<State>) → 𝔹
  state ← q₀
  ∀ σ ∈ value:                                   ▷ symbol
    m ← minterm_partition(σ)
    state ← δ[state, m]
    if state = SINK then return false            ▷ early exit
  return state ∈ F

  Example (2 states, 2 minterms):
  ┌───────┬──────────┬──────────┐
  │ State │ m = true │ m = false│
  ├───────┼──────────┼──────────┤
  │   0   │    1     │    2     │
  │   1   │    1     │   SINK   │
  └───────┴──────────┴──────────┘
  F = {1}
```

The runtime cost is O(|value|) — one match dispatch per symbol in the input
value, with each dispatch being O(1) due to the finite minterm partition. The
`_ => return false` arm handles implicit sink states (states from which no
accepting state is reachable), providing an early-exit optimization. For
`IntervalAlgebra` guards, minterm predicates compile to range checks
(`x >= 5 && x < 100`); for `KatBooleanAlgebra` guards, they compile to
boolean variable tests. The number of match arms is bounded by
|states| × |minterms|, which is typically small after Hopcroft minimization —
most real-world guards produce DFAs with fewer than 10 states.

### ProductAlgebra

When a guard combines constraints from two different domains — for example,
an arithmetic condition on a value's numeric field and a type hierarchy
condition on its structural type — the guard cannot be compiled using a single
`BooleanAlgebra`. `ProductAlgebra<A, B>` solves this by lifting two independent
algebras into their Cartesian product, where predicates are pairs `(a, b)` and
operations apply component-wise. The theoretical basis is that the product of
two Boolean algebras is itself a Boolean algebra (a standard result in
universal algebra). The key satisfiability equation decomposes into independent
checks because the two domains are independent — a product predicate is
satisfiable if and only if both components are satisfiable:

```
ProductAlgebra<A, B>.is_satisfiable((a, b)) = A.is_satisfiable(a) ∧ B.is_satisfiable(b)
```

This enables mixed-domain constraints, e.g.,
`ProductAlgebra<PresburgerAlgebra, LatticeTheory>` for guards combining
numeric and type hierarchy constraints. The SFA operations (`determinize`,
`minimize`, `intersect`) work over the product algebra without modification,
since they are generic over any `BooleanAlgebra` implementation.

> **Citation:** D'Antoni, L. & Veanes, M. "Minimization of Symbolic
> Automata." *Proceedings of POPL*, 2014. DOI: 10.1145/2535838.2535849

---

## 16. Constraint Theory Suite

### Motivation

The built-in Boolean algebras cover single-variable ranges
(`IntervalAlgebra`), Unicode characters (`CharClassAlgebra`), propositional
atoms (`KatBooleanAlgebra`), and module signatures (`DispatchAlgebra`). But
MeTTa and Rholang need more:

- **Multi-variable arithmetic**: "the sum of captures `x₁ + x₂ ≤ 5`"
  (Presburger arithmetic)
- **Structural unification**: "this MeTTa pattern unifies with that type
  expression" (first-order unification)
- **Type hierarchies**: "type A is a subtype of type B" (subtype lattice)

The constraint theory suite provides all three as pure-Rust implementations
with provably decidable decision procedures — no external Satisfiability Modulo Theories (SMT) dependency.

### Why Automata Instead of SMT

A natural question is why the pipeline uses custom automata-based decision
procedures rather than delegating to an established SMT solver (Z3, CVC5). The
rationale is threefold: deployment simplicity (no C++ FFI, no platform-specific
binaries, WASM-compatible), formal control (the decision procedures are
provably decidable with known complexity bounds, rather than relying on a
solver's completeness as an opaque guarantee), and extensibility (new domains
are added by implementing a Rust trait, not by extending an external solver's
theory combination). The following table compares the two approaches across
seven criteria:

| Criterion     | SMT (Z3/CVC5)                          | Constraint Theory Suite         |
|---------------|----------------------------------------|---------------------------------|
| External deps | z3-sys (~1.5GB), platform build        | Zero — pure Rust                |
| Deployment    | Shared lib, platform-specific          | Cross-platform, WASM-compatible |
| Performance   | FFI call per check-sat, ~1ms startup   | In-process, cacheable automata  |
| Formal basis  | Solver completeness as black-box       | Provably decidable (Büchi 1960) |
| Integration   | SMT-LIB2 serialization + model parsing | Direct `BooleanAlgebra` impl    |
| Scope match   | Over-powered (arrays, UF, bitvectors)  | Exact fit for guard predicates  |
| Extensibility | Fixed theory set, FFI boundary         | Open `ConstraintTheory` trait   |

The "scope match" row is particularly important: SMT solvers support theories
(arrays, uninterpreted functions, bitvectors) that are irrelevant to guard
predicates, while lacking direct support for the automaton-theoretic operations
(SFA intersection, minterm partitioning) that the pipeline needs. Using an
SMT solver would require marshaling automata into SMT-LIB2 format and parsing
models back — a lossy round-trip that adds complexity without benefit.

### Architecture

The constraint theory architecture has two layers connected by the
`TheoryAlgebra<T>` bridge. The upper layer is the `BooleanAlgebra` trait (§15),
which all SFA operations consume. The lower layer is the `ConstraintTheory`
trait, which domain-specific implementations provide. The bridge translates
between the two: `is_satisfiable()` on the algebra side becomes `propagate()`
plus optional `label()` search on the theory side. The left column shows direct
`BooleanAlgebra` implementations (the "fast path" — no bridge overhead), while
the right column shows the bridge path through `TheoryAlgebra<T>`. Note that
`PresburgerAlgebra` appears on both sides: it has a direct `BooleanAlgebra`
implementation for compile-time analysis performance, and a `ConstraintTheory`
implementation for validation and LogicT integration.

The key architectural insight is the `label()` method's return type: decidable
theories return `LogicStream::empty()` (propagation alone determines
satisfiability, no search needed), while search-based theories return a
non-empty `LogicStream` of search choices that LogicT explores fairly:

```
                    ┌──────────────────────────────────────────┐
                    │         BooleanAlgebra trait             │
                    │  (is_satisfiable, witness, evaluate,     │
                    │   and, or, not)                          │
                    └────────┬────────────────┬────────────────┘
                             │                │
              ┌──────────────┴──┐      ┌──────┴───────────────┐
              │ Direct impls    │      │ TheoryAlgebra<T>     │
              │ (fast path)     │      │ bridge               │
              ├─────────────────┤      ├──────────────────────┤
              │ IntervalAlgebra │      │ Wraps any            │
              │ CharClassAlgebra│      │ ConstraintTheory     │
              │ KatBooleanAlg.  │      │ into BooleanAlgebra  │
              │ DispatchAlgebra │      │ via propagation +    │
              │ PresburgerAlg.  │◄─────┤ LogicT search        │
              └─────────────────┘      └──────┬───────────────┘
                                              │
                             ┌────────────────┼────────────────┐
                             │                │                │
                   ┌─────────┴──┐  ┌──────────┴───┐  ┌─────────┴───┐
                   │ Presburger │  │ Unification  │  │ Lattice     │
                   │ Theory     │  │ Theory       │  │ Theory      │
                   │            │  │              │  │             │
                   │ label():   │  │ label():     │  │ label():    │
                   │ empty()    │  │ CustomMatch  │  │ empty()     │
                   │ (decidable)│  │ alternatives │  │ (decidable) │
                   └────────────┘  └──────────────┘  └─────────────┘

  ProductAlgebra<A, B>: composes any two BooleanAlgebra instances
  LogicStream<T>: fair backtracking search (Kiselyov et al., ICFP 2005)
```

The `ProductAlgebra<A, B>` at the bottom composes any two algebras
(direct or bridged) into a single algebra, enabling multi-domain guards. The
`LogicStream<T>` provides the fair backtracking monad that powers search-based
theories, ensuring that all branches are explored without starvation.

### The ConstraintTheory Trait

The `ConstraintTheory` trait is the extension point for adding new constraint
domains to the pipeline. Its design follows the constraint logic programming
(CLP) paradigm: a *store* accumulates constraints via *propagation* (which may
detect inconsistency and return `None`), and *labeling* generates search choices
when propagation alone cannot determine satisfiability. The separation of
propagation and labeling is the key design decision: it allows decidable
theories (where propagation is complete) to avoid search entirely, while
search-based theories (where propagation narrows but doesn't solve) can
delegate to LogicT's fair backtracking. The three associated types —
`Constraint`, `Assignment`, `Store` — separate the *what* (constraints to
satisfy), the *evidence* (a satisfying assignment), and the *state* (the
accumulated constraint set).

See [constraint-theories](../../prattail/docs/design/constraint-theories) for per-theory design docs.

```rust
pub trait ConstraintTheory {
    type Constraint: Clone + Debug + Eq + Hash;
    type Assignment: Clone + Debug;
    type Store: Clone + Debug;

    fn empty_store(&self) -> Self::Store;
    fn propagate(&self, store: &Self::Store, c: &Self::Constraint)
        -> Option<Self::Store>;
    fn is_consistent(&self, store: &Self::Store) -> bool;
    fn witness(&self, store: &Self::Store) -> Option<Self::Assignment>;
    fn label(&self, store: &Self::Store) -> LogicStream<Self::Constraint>;
    fn evaluate(&self, c: &Self::Constraint, a: &Self::Assignment) -> bool;
}
```

The `propagate()` method is the workhorse: it takes the current store and a new
constraint, and returns either `Some(new_store)` (the constraint is consistent
with the existing store) or `None` (inconsistency detected — the constraint
set is unsatisfiable). For decidable theories like Presburger arithmetic, a
sequence of propagations followed by `is_consistent()` is sufficient to
determine satisfiability — `label()` returns `LogicStream::empty()` to signal
that no search is needed. For search-based theories like unification, `label()`
returns a `LogicStream` of *labeling choices* — additional constraints that
narrow the search space — and `LogicStream::interleave` explores these choices
fairly, ensuring both branches of a disjunction receive equal attention.

### The TheoryAlgebra Bridge

The `TheoryAlgebra<T: ConstraintTheory>` adapter is the glue between the two
layers: it implements `BooleanAlgebra` for any `ConstraintTheory`, allowing
domain-specific constraint solvers to be used as SFA transition labels without
modification. The implementation translates each `BooleanAlgebra` method into
the corresponding `ConstraintTheory` operations. The critical translation is
`is_satisfiable()`, which first attempts propagation (the fast path), and only
falls back to labeling search if propagation succeeds but the store is not yet
fully determined:

```
is_satisfiable(φ) ≡ propagate(∅, φ) ≠ ⊥ ∨ label_search(store) succeeds
```

For decidable theories (Presburger, Lattice), `label()` returns
`LogicStream::empty()` and the disjunction's right branch is never evaluated —
the entire check reduces to a single `propagate()` call. For search-based
theories (Unification), the `label_search()` invokes LogicT's fair
backtracking with a configurable depth bound, ensuring that the bridge does
not loop indefinitely on theories with infinite search spaces.

### LogicStream — Fair Backtracking Monad

The `LogicStream<T>` type provides the search backbone for non-decidable
constraint theories. It implements the `msplit`-based LogicT monad of Kiselyov
et al. (ICFP 2005), which guarantees *fair* exploration of search branches —
a property that standard depth-first backtracking lacks. The key insight is
that unfair search can starve branches: if one disjunct produces infinitely
many results, depth-first search never explores the other. LogicT's
`interleave()` operation solves this by alternating between branches in a
round-robin fashion. The implementation uses an explicit `VecDeque`-based
branch queue rather than Haskell-style lazy thunks, adapting the functional
design to Rust's eager evaluation model.

The following table lists all `LogicStream` operations and their logical
semantics:

| Operation                | Semantics                               |
|--------------------------|-----------------------------------------|
| `msplit()`               | Peek at first result + remainder stream |
| `mzero()`                | Empty stream (failure)                  |
| `unit(v)`                | Single-element stream                   |
| `mplus(a, b)`            | Concatenation (unfair)                  |
| `interleave(a, b)`       | Fair disjunction (alternating)          |
| `fair_conjoin(f)`        | Fair conjunction (>>-)                  |
| `ifte(cond, then, else)` | Soft cut (if-then-else)                 |
| `once()`                 | Commit to first result                  |
| `gnot()`                 | Negation as finite failure              |

The `interleave(a, b)` operation is the critical fairness primitive: it
alternates between drawing results from `a` and `b`, ensuring both branches
are explored infinitely often even if one produces results faster. The
`fair_conjoin(f)` lifts this fairness to conjunction: rather than evaluating
`f` on all results of the first stream before moving to the second, it
interleaves the evaluations. The `gnot()` operation implements negation as
finite failure — it succeeds (with `()`) if the stream is empty, and fails
if the stream produces any result, enabling stratified negation in quantified
predicates (§8).

**Source files and design documents:**

| Module | Source | Design Doc |
|--------|--------|------------|
| M12 Presburger | [presburger.rs](../../prattail/src/presburger.rs) | [presburger-algebra.md](../../prattail/docs/design/constraint-theories/presburger-algebra.md) |
| M13 Unification | [unification.rs](../../prattail/src/unification.rs) | [unification-theory.md](../../prattail/docs/design/constraint-theories/unification-theory.md) |
| M14 Lattice | [lattice_theory.rs](../../prattail/src/lattice_theory.rs) | [lattice-theory.md](../../prattail/docs/design/constraint-theories/lattice-theory.md) |

### PresburgerAlgebra — Multi-Variable Linear Integer Arithmetic (M12)

**Motivation.** Single-variable integer constraints like `x > 0 ∧ x < 1000`
are handled by `IntervalAlgebra` (M1). But guards involving two or more
variables — e.g., `x + y ≤ budget` or `count(ch1) + count(ch2) ≤ capacity`
— require **Presburger arithmetic**: the first-order theory of the integers
with addition (not multiplication).

**Intuition.** Variables are encoded as binary numbers read least-significant
bit (LSB) first. Each "symbol" on the NFA's tape is a k-bit vector giving
the current bit of each variable. The NFA tracks the carry/remainder as it
reads bits from left to right. Satisfiability reduces to NFA language
non-emptiness; validity reduces to language universality; a witness is the
shortest accepting path decoded back to integers.

**Formal Definition.** Presburger arithmetic is the theory Th(ℤ, +, <, 0, 1).
Its atomic predicates are **linear constraints**: inequalities of the form
Σᵢ aᵢ · xᵢ ≤ b where aᵢ, b ∈ ℤ and xᵢ are integer variables. Büchi (1960)
[§23, ref #5] proved that every Presburger formula defines a regular language
over the alphabet {0,1}ᵏ (one bit per variable), providing a fully decidable
automata-theoretic decision procedure.

A `PresburgerPred` is a Boolean combination of `LinearConstraint` atoms:

```
PresburgerPred ::= True | False
                 | Atom(LinearConstraint)             — Σ aᵢ·xᵢ ≤ b
                 | And(PresburgerPred, PresburgerPred)
                 | Or(PresburgerPred, PresburgerPred)
                 | Not(PresburgerPred)
                 | Exists { var: usize, body: PresburgerPred }
```

**NFA Construction (Bartzis-Bultan).** For an atomic constraint
Σ aᵢ · xᵢ ≤ b over k variables:

- **Alphabet:** {0,1}ᵏ — one bit per variable, read LSB-first
- **States:** Remainder values tracking r = ⌊(b − Sⱼ) / 2ʲ⌋ where Sⱼ is the
  partial sum through bit position j
- **Transition:** r′ = ⌊(r − Σ aᵢ · dᵢ) / 2⌋ where dᵢ ∈ {0,1} is the current
  bit of variable xᵢ
- **Acceptance:** After w bits, accept iff r ≥ 0
- **State bound:** O((Σ|aᵢ| + |b|) · 2ᵏ)

```
Bit-vector tape for k=2 variables (x, y), encoding x=5 (101₂), y=3 (11₂):

  Position:   0     1     2
  Symbol:   (1,1) (0,1) (1,0)    ← LSB-first: bit 0 of (x,y), bit 1, bit 2
              │     │     │
              ▼     │     │
  ┌────┐  (1,1)  ┌────┐ (0,1) ┌────┐ (1,0) ╔════╗
  │ q₀ │────────►│ q₁ │──────►│ q₂ │──────►║ q₃ ║  (accept)
  └────┘         └────┘       └────┘       ╚════╝
  r=b            r=⌊(b-a₁-a₂)/2⌋           r≥0 → accept
```

**Key types** (from [presburger.rs](../../prattail/src/presburger.rs)):

| Type                | Role                                                    |
|---------------------|---------------------------------------------------------|
| `LinearConstraint`  | Atomic Σ aᵢ·xᵢ ≤ b with `terms: Vec<(usize, i64)>`      |
| `PresburgerPred`    | Boolean combination of `LinearConstraint` atoms         |
| `PresburgerNfa`     | NFA over {0,1}ᵏ alphabet with `transitions: HashMap`    |
| `PresburgerTheory`  | `ConstraintTheory` impl (LogicT integration path)       |
| `PresburgerAlgebra` | `BooleanAlgebra` impl (fast compile-time analysis path) |

**Pseudocode:**

```
encode_constraint(c: LinearConstraint, k: ℕ, w: ℕ) → NFA
  compute coefficient sum: S ← Σ|aᵢ|
  State range: r ∈ [−S, max(|b|, S)]
  Initial state: r₀ ← b
  ∀ j ∈ 0…w−1:                                  ▷ bit position
    ∀ r ∈ range:                                ▷ state
      ∀ d ∈ {0,1}ᵏ:                             ▷ bit-vector
        r′ ← ⌊(r − Σ aᵢ · dᵢ) / 2⌋
        add transition (r, d) → r′
  Accept states: { r | r ≥ 0 }
  return NFA
```

Implementation: [presburger.rs](../../prattail/src/presburger.rs).

**Boolean operations:** Intersection (NFA product construction), union (product +
accept union), complement (depth-tracked determinization + terminal flip),
existential projection (drop bit dimension, merge transitions).

**Dual implementation:** Direct `BooleanAlgebra` (fast path for compile-time
analysis) + `ConstraintTheory` (validation path via LogicT integration).

**Pipeline role:** Feature gate `presburger`. Cost 3. Activated when guard
contains arithmetic relations over multiple integer-typed parameters.

### UnificationTheory — Structural Unification (M13)

**Motivation.** When a Rholang `for` receive binds `@{x!(y)}` or MeTTa evaluates
`(= (foo $x) (foo (bar 42)))`, the system must decompose terms to extract
bindings. Two guard patterns may need to be checked for overlap ("can the same
value match both?"), subsumption ("does pattern A always match when B does?"),
or disjointness ("can they never match the same value?"). These questions reduce
to first-order syntactic unification.

**Intuition.** Unification is like solving a jigsaw puzzle where some pieces have
blank spots (variables). You try to fill in the blanks so that both sides of each
equation look identical. If a blank appears on both sides, they must eventually
be filled with the same value. If two different constructors collide (e.g.,
`Cons` vs. `Nil`), the puzzle is unsolvable.

**Formal Definition.** The term language over a signature Σ with variable set V is:

```
  t ::= x                     (variable, x ∈ V)
      | c                     (constant, c ∈ Σ with arity 0)
      | f(t₁, …, tₙ)          (application, f ∈ Σ with arity n)
```

A **substitution** σ is a finite mapping {x₁ ↦ t₁, …, xₖ ↦ tₖ} from variables
to terms. Applying σ to a term t (written σ(t) or tσ) replaces each xᵢ by tᵢ
simultaneously.

A **unifier** of terms s and t is a substitution σ such that σ(s) = σ(t).
The **most general unifier** (MGU) θ is a unifier such that for every other
unifier σ, there exists θ′ with σ = θ′ ∘ θ. The MGU is unique up to variable
renaming.

The Martelli & Montanari (1982) algorithm computes the MGU in near-linear time
O(n · α(n)) using a stack-based approach with union-find for variable binding.

| Case                                | Action                            |
|-------------------------------------|-----------------------------------|
| `Var(x) ≡ Var(x)`                   | Skip (trivial identity)           |
| `Var(x) ≡ t`                        | Occurs check; bind x ↦ t          |
| `App(f, args₁) ≡ App(f, args₂)`     | Decompose: push argsᵢ₁ ≡ argsᵢ₂   |
| `App(f, _) ≡ App(g, _)` where f ≠ g | Constructor clash → failure       |

The **occurs check** prevents circular bindings: before binding x ↦ t, verify
that x does not appear in t. Without this check, `x ≡ f(x)` would produce the
infinite term `f(f(f(…)))`.

```
Occurs check diagram:

  Var(x) ≡ App("f", [Var(x)])

  Does x occur in f(x)?
       │
  ┌────▼────┐
  │ f(...)  │ → recurse into children
  │   │     │
  │ Var(x)  │ → YES! x occurs in t → FAIL (circular)
  └─────────┘
```

**Key types** (from [unification.rs](../../prattail/src/unification.rs)):

| Type                  | Role                                                  |
|-----------------------|-------------------------------------------------------|
| `TermExpr`            | `Var(usize) \| Const(String) \| App { head, args }`   |
| `UnificationEquation` | Pair (lhs: TermExpr, rhs: TermExpr) to be unified     |
| `Substitution`        | Map `usize → TermExpr` (variable bindings)            |
| `UnificationStore`    | Pending equations + accumulated substitution          |
| `UnificationTheory`   | `ConstraintTheory` impl with optional `TermSignature` |

**Term representation.** Variables are identified by `usize` indices rather than
names to avoid alpha-equivalence complications during unification:

```rust
pub enum TermExpr {
    Var(usize),                                  // Unification variable
    Const(String),                               // Nullary constructor
    App { head: String, args: Vec<TermExpr> },   // Constructor application
}
```

**Pseudocode:**

```
unify(equations: [(TermExpr, TermExpr)]) → (σ | ⊥)
  σ ← ∅                           ▷ empty substitution
  stack ← equations               ▷ work stack of pending equations
  while stack ≠ ∅ do
    (s, t) ← pop(stack)
    s′ ← apply(σ, s);  t′ ← apply(σ, t)
    case (s′, t′) of
      (Var(x), Var(x))         →                     ▷ trivial identity
      (Var(x), t)              →
        if occurs(x, t) then return ⊥                ▷ occurs check
        σ ← σ ∪ {x ↦ t}                              ▷ bind variable
      (t, Var(x))              →
        if occurs(x, t) then return ⊥
        σ ← σ ∪ {x ↦ t}
      (App(f, as), App(f, bs)) →
        if |as| ≠ |bs| then return ⊥                 ▷ arity mismatch
        ∀ i ∈ 0…|as|−1: push(stack, (asᵢ, bsᵢ))      ▷ decompose
      (App(f, _), App(g, _))   →
        return ⊥                                     ▷ clash: f ≠ g
      (Const(a), Const(a))     →                     ▷ identity
      (Const(a), Const(b))     → return ⊥            ▷ clash: a ≠ b
      _                        → return ⊥
  return σ
```

The implementation follows the pseudocode directly; see [unification.rs](../../prattail/src/unification.rs).

**Subsumption:** σ₁ ⊑ σ₂ iff ∃θ. σ₂ = θ ∘ σ₁ (σ₁ is more general than σ₂).

**Applications:** MeTTa pattern matching, Rholang quoted process patterns.

**Pipeline role:** Feature gate `unification`. Cost 3. Activated when guard
contains pattern-matching relations requiring structural decomposition.

### LatticeTheory — Subtype Lattice (M14)

**Motivation.** Languages with subtype polymorphism need to answer questions
like: Is `Nat` a subtype of `Number`? What is the most specific common
supertype of `Int` and `Float` (join/LUB)? What is the most general type
that is a subtype of both `Readable` and `Writable` (meet/GLB)? Does a
pattern set cover all subtypes of `Value`? These reduce to operations on a
finite partially ordered set of types.

**Intuition.** The type hierarchy is a directed acyclic graph (DAG) where edges
point from subtypes to supertypes. "Is A a subtype of B?" becomes "Is there a
path from A to B?" — a graph reachability question. Computing the transitive
closure once (via Warshall's algorithm) converts all future subtype queries to
O(1) set membership checks.

**Formal Definition.** A **lattice** is a partially ordered set (L, ≤) where
every pair of elements has a **join** (least upper bound, LUB) and a **meet**
(greatest lower bound, GLB):

- **Subtyping:** a ≤ b means "a is a subtype of b"
- **Join (⊔):** a ⊔ b is the smallest c such that a ≤ c and b ≤ c
- **Meet (⊓):** a ⊓ b is the largest c such that c ≤ a and c ≤ b
- **Lattice order equivalence:** a ≤ b ⟺ a ⊔ b = b ⟺ a ⊓ b = a

Example Hasse diagram for a small type lattice:

```
              ⊤ (Any)
             ╱ ╲
            ╱   ╲
        Number  String
       ╱    ╲
     Int    Float
       ╲    ╱
        Nat
         │
         ⊥ (Nothing)

  Nat ≤ Int ≤ Number ≤ ⊤
  Nat ≤ Float ≤ Number ≤ ⊤
  Int ⊔ Float = Number  (join: least common supertype)
  Int ⊓ Float = Nat     (meet: greatest common subtype)
```

**Key types** (from [lattice_theory.rs](../../prattail/src/lattice_theory.rs)):

| Type                | Role                                               |
|---------------------|----------------------------------------------------|
| `TypeId` (= usize)  | Unique identifier for each type in the lattice     |
| `SubtypeConstraint` | Edge `{ sub: TypeId, sup: TypeId }` — sub ≤ sup    |
| `TypeAssignment`    | Map `usize → TypeId` (variable bindings)           |
| `LatticeStore`      | Edge set + transitive closure + LUB/GLB caches     |
| `LatticeTheory`     | `ConstraintTheory` impl with type universe + names |

**Pseudocode — Warshall's Transitive Closure:**

```
warshall_closure(edges: Set<(TypeId, TypeId)>, n: ℕ) → Set<(TypeId, TypeId)>
  closure ← edges ∪ { (a, a) | a ∈ 0…n−1 }     ▷ reflexive
  ∀ k ∈ 0…n−1:                                 ▷ intermediate vertex
    ∀ i ∈ 0…n−1:
      ∀ j ∈ 0…n−1:
        if (i, k) ∈ closure ∧ (k, j) ∈ closure then
          closure ← closure ∪ { (i, j) }
  ▷ cycle detection
  ∀ (a, b), a ≠ b:
    if (a, b) ∈ closure ∧ (b, a) ∈ closure then
      record cycle (a, b) — these types are equivalent
  return closure

  Complexity: O(n³) time, O(n²) space. Computed once, cached with
  dirty-flag invalidation (recomputed only when new edges are added).
```

**Pseudocode — Join (LUB):**

```
join(store: LatticeStore, a: TypeId, b: TypeId) → (TypeId | ⊥)
  if (a, b) ∈ LUB cache then return cached value
  upper_a ← { t | (a, t) ∈ closure }          ▷ all supertypes of a
  upper_b ← { t | (b, t) ∈ closure }          ▷ all supertypes of b
  common ← upper_a ∩ upper_b                  ▷ common supertypes
  minimal ← { c ∈ common | ¬∃c′ ∈ common. c′ < c }
  if |minimal| = 1 then cache and return the element
  else return ⊥ (join does not exist — not a lattice)
```

Implementation: [lattice_theory.rs — ensure_closure()](../../prattail/src/lattice_theory.rs).
Dirty-flag guard, cache invalidation, and cycle recording are detailed below.

**Implementation details:**
- Subtype DAG constructed from explicit edges via `add_edge(sub, sup)`
- Warshall's transitive closure: O(n³) once, cached with dirty-flag invalidation
- LUB/GLB computed lazily and cached in `HashMap<(TypeId, TypeId), Option<TypeId>>`
- Cycle detection: a ≤ b ≤ a with a ≠ b represents type equivalence

**Applications:** MeTTa `(:< sub super)`, Rholang bundle capabilities.

**Pipeline role:** Feature gate `lattice-theory`. Cost 2. Activated when guard
contains subtype relations or terminals referencing the type hierarchy.

### Predicate Dispatch Integration (M12–M14)

Three module bits extend the predicate dispatch controller from 11 to 14
modules:

| Bit | Module | Name              | Feature          | Cost | Detection                          |
|-----|--------|-------------------|------------------|------|------------------------------------|
| 11  | M12    | Linear Arithmetic | `presburger`     | 3    | Arithmetic relations and terminals |
| 12  | M13    | Unification       | `unification`    | 3    | Pattern-matching relations         |
| 13  | M14    | Subtype Lattice   | `lattice-theory` | 2    | Subtype relations and terminals    |

### Component Summary

| Component        | Feature Gate                   | Module              | Lines  | Tests | Purpose                                     |
|------------------|--------------------------------|---------------------|--------|-------|---------------------------------------------|
| LogicT           | `logict`                       | `logict.rs`         | ~600   | 29    | Fair backtracking monad                     |
| ConstraintTheory | `logict`                       | `logict.rs`         | —      | —     | Pluggable constraint domain trait           |
| TheoryAlgebra    | `logict` + `symbolic-automata` | `logict.rs`         | —      | —     | ConstraintTheory → BooleanAlgebra bridge    |
| Presburger       | `presburger`                   | `presburger.rs`     | ~2,200 | 83    | Multi-variable linear integer arithmetic    |
| Unification      | `unification`                  | `unification.rs`    | ~750   | 65    | Structural unification (Martelli-Montanari) |
| Lattice          | `lattice-theory`               | `lattice_theory.rs` | ~1,200 | 45    | Subtype lattice with join/meet              |
| ProductAlgebra   | (always-on)                    | `symbolic.rs`       | ~250   | 12    | Compose two BooleanAlgebra instances        |

> **Citations:**
>
> - Kiselyov, O., Shan, C., Friedman, D. P. & Sabry, A. "Backtracking,
>   Interleaving, and Terminating Monad Transformers." *Proceedings of ICFP*,
>   2005. DOI: 10.1145/1086365.1086390
> - Büchi, J. R. "Weak second-order arithmetic and finite automata."
>   *Zeitschrift für mathematische Logik und Grundlagen der Mathematik*,
>   6:66–92, 1960.
> - Martelli, A. & Montanari, U. "An Efficient Unification Algorithm."
>   *ACM TOPLAS*, 4(2):258–282, 1982.
> - Birkhoff, G. *Lattice Theory*. AMS Colloquium Publications, 1940.
> - Davey, B. A. & Priestley, H. A. *Introduction to Lattices and Order*.
>   Cambridge University Press, 2002.

### Pipeline Flow

#### Structural Analysis Pattern

Like all 22+ existing `analyze_from_bundle()` functions (e.g., [`symbolic.rs`](../../prattail/src/symbolic.rs),
[`nominal.rs`](../../prattail/src/nominal.rs), [`buchi.rs`](../../prattail/src/buchi.rs)), constraint theory analyses extract information
from `all_syntax: &[(String, String, Vec<SyntaxItemSpec>)]` without requiring
explicit guard fields on `RuleSpec`:

| Theory      | Looks for                                            | Extracts                                    |
|-------------|------------------------------------------------------|---------------------------------------------|
| Presburger  | Comparison terminals (`<`, `>=`, etc.) near captures | `LinearConstraint` → NFA satisfiability     |
| Unification | Same-category rules with overlapping structures      | `TermExpr` → Martelli-Montanari unification |
| Lattice     | Category delegation patterns (A references only B)   | Subtype edges → DAG + Warshall closure      |

### Parallel Analysis

The three constraint theories are independent — Presburger arithmetic,
structural unification, and lattice theory operate on non-overlapping aspects
of the grammar — so their analyses can run concurrently. The pipeline exploits
this via `thread::scope` (optimization gate DB03), spawning one thread per
theory. Each thread walks the same `all_syntax` bundle but extracts different
features: Presburger looks for numeric comparison terminals (`<`, `>=`, etc.)
near captures; Unification looks for overlapping structural patterns across
rules; Lattice looks for category delegation patterns (one category's rules
reference only another category). The three analysis results are joined into a
single `MathAnalysisResults` struct, which is then destructured into the
`LintContext` for downstream lint functions.

```
┌──────────────────────────────────────────────────────────────────────┐
│  thread::scope (DB03 parallel analysis)                              │
│                                                                      │
│  ┌─────────────────────┐  ┌─────────────────────┐  ┌──────────────┐  │
│  │ presburger::        │  │ unification::       │  │ lattice_     │  │
│  │ analyze_from_bundle │  │ analyze_from_bundle │  │ theory::     │  │
│  │                     │  │                     │  │ analyze_from │  │
│  │ Walk all_syntax for │  │ Walk all_syntax for │  │ _bundle      │  │
│  │ numeric comparison  │  │ structural pattern  │  │              │  │
│  │ terminals → build   │  │ overlap → build     │  │ Walk for     │  │
│  │ LinearConstraint →  │  │ TermExpr → unify →  │  │ category     │  │
│  │ NFA satisfiability  │  │ subsumption check   │  │ delegation → │  │
│  └────────┬────────────┘  └──────────┬──────────┘  │ DAG closure  │  │
│           │                          │             └───────┬──────┘  │
│           ▼                          ▼                     ▼         │
│  PresburgerAnalysis         UnificationAnalysis    LatticeAnalysis   │
└──────────────────────────────────────────────────────────────────────┘
                           │
                           ▼
              MathAnalysisResults → destructure → LintContext
                           │
                           ▼
              ┌───────────────────────────────────────┐
              │ Lint functions read analysis results: │
              │  PB01–PB03: arithmetic guards         │
              │  UN01–UN03: unification guards        │
              │  SL01–SL02: subtype lattice           │
              │  LT01: LogicT search bound            │
              └───────────────────────────────────────┘
```

The lint functions at the bottom consume the analysis results without
recomputing them — each lint function reads pre-computed data from the
`LintContext` and emits diagnostics. The PB01–PB03 lints check for
unsatisfiable arithmetic constraints, redundant comparisons, and missing
bounds; UN01–UN03 check for non-unifiable patterns, occurs-check violations,
and subsumption; SL01–SL02 check for lattice inconsistencies and missing
subtype edges; LT01 warns when LogicT search exceeds its depth bound.

### Dispatch Gating

When `predicate-dispatch` is enabled, `classify_grammar()` in
[`predicate_dispatch.rs`](../../prattail/src/predicate_dispatch.rs) sets `PredicateSignature` bits M12, M13, M14 based
on grammar structure heuristics. Each analysis checks
`dispatch_plan.requires(ModuleId::...)` before running. Grammars without
numeric terminals skip Presburger; grammars without overlapping patterns skip
Unification; grammars without category delegation skip Lattice.

### Relation Name Heuristics

Module activation currently uses **hardcoded keyword lists** in
[`predicate_dispatch.rs`](../../prattail/src/predicate_dispatch.rs) to classify `PredicateExpr::Relation` names into
theory modules. These heuristics (`is_arithmetic_relation()`,
`is_unification_relation()`, `is_subtype_relation()`) represent a **first
attempt** at automating predicate dispatch and are a **temporary, conservative
approximation**:

- **Conservative:** may activate extra modules (false positives) but never
  misses a needed one
- **Not extensible:** user-defined languages with novel relation names will
  not trigger theory-specific modules
- **Brittle:** relies on naming conventions rather than semantic declarations

Similarly, `classify_grammar()` uses **terminal symbol heuristics** (e.g.,
`+` → M12, `match` → M13, `extends` → M14) as an independent grammar-level
signal. These are equally provisional.

**This heuristic approach is superseded** by the `guards { theories {} }` block
(§2A) that makes dispatch data-driven. The spec author explicitly declares
which `ConstraintTheory` implementations handle which guards and for which
type categories, eliminating keyword guessing entirely and enabling arbitrary
user-defined constraint domains to participate in predicate dispatch without
heuristic support. See the Extension Mechanism below for the three-layer
design, and §14A for the theory-guided LogicT evaluation pipeline that
leverages these declarations at runtime.

### Extension Mechanism

#### Three-Layer Design

The constraint theory system is designed for extension. Users add new theories
through three layers. The `channels {}` sub-block (§2A) follows the same
pattern — explicit, data-driven declarations replace heuristic inference, just
as `theories {}` replaced heuristic keyword dispatch for constraint theories.
The three layers for theories are:

**Layer 1 — Rust Implementation.** The first step is implementing the
`ConstraintTheory` trait for the new domain. The example below shows a
hypothetical `ResourceTheory` for resource-usage guards (e.g., "this process
uses at most 5 MB of memory"). The implementation must provide the five
core methods. Note that `label()` returns `LogicStream::empty()`, indicating
that resource constraints are decidable by propagation alone — no search is
needed:

```rust
pub struct ResourceTheory;
impl ConstraintTheory for ResourceTheory {
    type Constraint = ResourceConstraint;
    type Assignment = ResourceAssignment;
    type Store = ResourceStore;

    fn empty_store(&self) -> Self::Store { ResourceStore::new() }
    fn propagate(&self, store: &Self::Store, c: &Self::Constraint)
        -> Option<Self::Store> { /* domain-specific propagation */ }
    fn label(&self, store: &Self::Store) -> LogicStream<Self::Constraint> {
        LogicStream::empty()  // decidable → no search needed
    }
    fn evaluate(&self, c: &Self::Constraint, a: &Self::Assignment)
        -> bool { /* membership test */ }
}
```

Once implemented, the theory automatically gains `BooleanAlgebra` support via
`TheoryAlgebra<ResourceTheory>`, which means it can be used as an SFA
transition label — all SFA operations (determinization, minimization,
intersection) work without additional code.

**Layer 2 — `language!` Declaration.** The second step registers the theory
in the `language!` macro's `guards { theories {} }` block (§2A), giving it a
name, associating it with its Rust type, and declaring which type categories
it handles via the `for [...]` clause. This declaration replaces the heuristic
keyword lists currently used for dispatch — the spec author explicitly states
which theories are available and which types they handle, eliminating
guesswork. The declaration also enables the pipeline to set the corresponding
`PredicateSignature` bit during classification, and activates theory-guided
domain pruning in LogicT evaluation (§14A):

```rust
language! {
    name: RholangLike,
    types { Proc, Name, ![i64] as Int },

    guards {
        gt . x: Int, y: Int  |- x ">" y ;
        // ... other typed predicates

        theories {
            resources  = ResourceTheory    for [Proc];  // user-defined
            arithmetic = PresburgerAlgebra for [Int];   // built-in fast path
            patterns   = UnificationTheory for [Proc, Name]; // LogicT search
            types      = LatticeTheory     for [Proc, Name, Int]; // decidable
        }
    },
    // ...
}
```

The `for [...]` clause is optional. When present, it enables type-driven
theory routing: `gt(x: Int, y: Int)` activates `PresburgerAlgebra` (M12)
because `Int` is in `PresburgerAlgebra`'s handled types. When absent, the
theory applies to all types (and the pipeline falls back to heuristic dispatch
for module activation).

**Layer 3 — Automatic Pipeline Wiring:**

1. `language!` parses `guards { theories {} }` → `Vec<TheoryRegistration>`
2. Pipeline builds `type→theory→module` map from registrations
3. `walk_predicate()` matches typed predicate parameters against
   `TheoryRegistration.handled_types` to set `PredicateSignature` bits
   precisely (replacing heuristic keyword lists)
4. `evaluate_quantified()` uses `ConstraintTheory::propagate()` to prune
   enumeration domains before LogicT exploration (§14A)
5. `TriState::Unknown` results are refined via `is_consistent()` when a
   matching theory is available (§14A, TriState Refinement Diagram)
6. Guard predicates matching refinement type predicates are statically
   eliminated via `predicate_entails()` (§14A, Refinement Type Bridge)

This replaces the heuristic keyword lists with explicit, data-driven dispatch
and enables theory-guided optimizations throughout the pipeline.

### Future Alternative: Alternating Weighted Automata (AWA) Evaluation

The current quantified predicate evaluation (section 8) uses LogicT's `gnot` and
`interleave` for fair backtracking search. An alternative strategy --
evaluation via Alternating Weighted Automata (AWA) -- is documented here for
future implementation.

AWA evaluation would compile quantified predicates to `WeightedAlternatingAutomaton`
states: `Q_tensor` (universal/conjunction) for `forall` and `Q_oplus` (existential/disjunction)
for `exists`. This requires the currently unimplemented `to_weighted_automaton()`
function (~2000 lines estimated).

**AWA advantages:**
- Formal correspondence to weighted MSO semantics (Droste & Gastin 2007)
- Better worst-case complexity for specific formula shapes (linear in automaton size)
- Composable with SFA intersection for guard fusion

**LogicT advantages (current approach):**
- Already implemented and tested
- Composable with existing `ConstraintTheory` infrastructure
- Simpler implementation
- Supports bounded evaluation (T3) naturally via `collect_bounded()`

The cost-benefit framework (`CostBenefitGate`) can gate between LogicT and AWA
evaluation once `to_weighted_automaton()` is implemented, selecting the strategy
with lower estimated cost per guard.

---

## 17. The Automata Modules (M1–M15)

Each of the 15 predicate-dispatched modules (M1–M15) contributes to the
predicated types pipeline, alongside additional feature-gated analysis modules.
The predicate dispatch controller determines the minimal set needed per guard.

> **Note:** All 15 predicate-dispatched modules are **compile-time analysis only**. They
> execute during `language!` macro expansion to analyze guards, detect issues,
> and inform codegen decisions. None of these modules or their automata appear
> in the generated binary. The only runtime effects are indirect: M7's
> selectivity analysis determines guard evaluation order, and Forward-Backward
> analysis annotates generated functions with `#[inline]`/`#[cold]`. See §14
> for details.

### Module Table

The following table lists all 15 predicate-dispatched modules and their role in
the predicated types pipeline. The modules are numbered M1–M15, matching the bit
positions in the 15-bit `PredicateSignature` bitvector that the dispatch
controller uses to determine which modules to activate per guard. Each module
corresponds to a specific automaton-theoretic formalism (SFA, Büchi, AWA,
Visibly Pushdown Automaton (VPA), PATA, register, multi-tape, etc.) and handles
a specific class of guard predicates. The table is ordered by module number,
which roughly corresponds to increasing complexity — M1 (propositional) is
simplest, M15 (transduction) is most complex. Read the "Role" column to
understand what kind of guard predicate triggers each module:

```
┌──────────────────────┬──────────────────────────────────────────────────┐
│ Module               │ Role in Predicated Types                         │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M1  Symbolic         │ BooleanAlgebra core. Guard satisfiability,       │
│                      │ overlap, subsumption. SFA compilation target.    │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M2  W. Buchi         │ Infinite behavior predicates: omega-regular      │
│                      │ guards on streams. "Channel always eventually    │
│                      │ delivers."                                       │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M3  Poly. AWA        │ ∀/∃ quantifier evaluation as ⊗/⊕ states.         │
│                      │ H-polynomial fixpoints for letprop.              │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M4  W. VPA           │ Quantifier scope nesting → call/return.          │
│                      │ Weighted inclusion for well-formedness.          │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M5  Parity Tree      │ Behavioral predicates as mu-calculus.            │
│                      │ mu_calculus_to_pata() compiles letprop.          │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M6  Register         │ Data-aware predicates: equality, freshness.      │
│                      │ Stateful guard evaluation with memory.           │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M7  Probabilistic    │ Guard selectivity estimation. Short-circuit      │
│                      │ ordering (most selective first).                 │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M8  Multi-Tape       │ Multi-channel receives → multi-tape.             │
│                      │ Cross-tape auto-intersection.                    │
│                      │ Activated by `channels {}` or heuristic.         │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M9  Multiset         │ Cardinality predicates: count(chan) >= 3.        │
│                      │ PPar analysis with HashBag multiplicities.       │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M10 W. MSO           │ THE specification language. where-clause syntax  │
│                      │ (not, and, or, forall, exists) IS weighted MSO.  │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M11 W. Two-Way       │ Cross-channel constraint propagation.            │
│                      │ Backward constraints for join reordering.        │
│                      │ Activated by `channels {}` or heuristic.         │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M12 Linear Arith.    │ Presburger arithmetic guards. NFA-based          │
│                      │ decision procedure for Σ aᵢ·xᵢ ≤ b.              │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M13 Unification      │ Structural pattern unification. Martelli-        │
│                      │ Montanari for MeTTa/Rholang pattern overlap.     │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M14 Subtype Lattice  │ Type hierarchy constraints. Warshall closure     │
│                      │ for MeTTa (:< sub super).                        │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M15 SFT              │ Output-producing transductions. Guard-based      │
│                      │ string transforms (case fold, normalize).        │
└──────────────────────┴──────────────────────────────────────────────────┘
```

M1 and M10 are the most frequently activated — M1 provides the foundational
satisfiability checks needed for all guards, and M10 classifies the guard's
logical structure. Modules M12–M14 are the constraint theory modules added
by §16 (Presburger, Unification, Lattice). M15 is the SFT module (§16) for
output-producing transductions.

> **Module design docs** (all in `prattail/docs/design/`):
> M1 → [symbolic-automata.md](../../prattail/docs/design/symbolic-automata.md), M2 → [weighted-buchi.md](../../prattail/docs/design/weighted-buchi.md),
> M3 → [polynomial-awa.md](../../prattail/docs/design/polynomial-awa.md), M4 → [weighted-vpa.md](../../prattail/docs/design/weighted-vpa.md),
> M5 → [parity-tree-automata.md](../../prattail/docs/design/parity-tree-automata.md), M6 → [register-automata.md](../../prattail/docs/design/register-automata.md),
> M7 → [probabilistic-automata.md](../../prattail/docs/design/probabilistic-automata.md), M8 → [multi-tape-automata.md](../../prattail/docs/design/multi-tape-automata.md),
> M9 → [multiset-automata.md](../../prattail/docs/design/multiset-automata.md), M10 → [weighted-mso.md](../../prattail/docs/design/weighted-mso.md),
> M11 → [two-way-transducer.md](../../prattail/docs/design/two-way-transducer.md), M12 → [presburger.md](../../prattail/docs/design/presburger.md),
> M13 → [unification.md](../../prattail/docs/design/unification.md), M14 → [lattice-theory.md](../../prattail/docs/design/lattice-theory.md),
> M15 → [symbolic-finite-transducer.md](../../prattail/docs/design/symbolic-finite-transducer.md).


### Module Subsections (M1–M15)

The following subsections provide in-depth coverage of each module. Modules
M8 and M11 have full treatments in §2A; modules M12–M14 have full treatments
in §16. These are cross-referenced below rather than duplicated.

#### M1: Symbolic Automata — BooleanAlgebra Core

**Motivation.** Every guard predicate compiles to an SFA. M1 provides the
foundational `BooleanAlgebra` trait and `SymbolicAutomaton<A>` type that all
other modules build upon. A guard like `x ∈ [0, 1000)` becomes a transition
guarded by an `IntervalPred::Range(0, 999)` rather than 1,000 individual
character transitions.

**Intuition.** A classical finite automaton labels each transition with a single
symbol from a finite alphabet. An SFA replaces the symbol with a *predicate*
over an infinite domain. Think of a museum guard who checks badge numbers: instead
of memorizing every valid number, the guard has a rule "badge numbers 100–200 are
allowed." The predicate `Range(100, 200)` replaces 101 individual transitions
with one.

**Formal Definition.** A **Symbolic Finite Automaton** (SFA) over effective
Boolean algebra A = (𝒟, Ψ, ⟦·⟧, ⊥, ⊤, ∧, ∨, ¬) is a tuple
M = (Q, A, δ, I, F) where:

- 𝒟 is the (potentially infinite) domain
- Ψ is the set of predicates (closed under ∧, ∨, ¬, with satisfiability
  decidable and witness generation)
- Q is a finite set of states
- δ ⊆ Q × Ψ × Q is the transition relation — each transition (q, φ, q′)
  fires when the current input element satisfies predicate φ
- I ⊆ Q is the set of initial states
- F ⊆ Q is the set of accepting states

The `BooleanAlgebra` trait (in [symbolic.rs](../../prattail/src/symbolic.rs))
provides ⊤, ⊥, ∧, ∨, ¬, satisfiability checking, witness generation, and
predicate evaluation over a generic domain.

**Key operations:**

| Operation       | Input       | Output             | Description                                    |
|-----------------|-------------|--------------------|------------------------------------------------|
| `intersect`     | `SFA, SFA`  | `SFA`              | Product construction (guard conjunction)       |
| `complement`    | `SFA`       | `SFA`              | Determinize + flip acceptance (guard negation) |
| `determinize`   | `SFA`       | `SFA`              | Minterm-based subset construction              |
| `is_empty`      | `SFA`       | `bool`             | BFS reachability to accepting state            |
| `is_equivalent` | `SFA, SFA`  | `bool`             | Symmetric difference emptiness check           |
| `accepts`       | `SFA, word` | `bool`             | Simulate word through transitions              |
| `analyze`       | `SFA`       | `SymbolicAnalysis` | Guard satisfiability / overlap analysis        |

**Decidability tier classification.** `classify_decidability(expr)` assigns
each predicate expression to one of four tiers (T1–T4, defined in §11).

**Concrete algebras:**

- `IntervalAlgebra { min_val, max_val }` — integer range predicates
- `CharClassAlgebra` — Unicode character class predicates
- `ProductAlgebra<A, B>` — cross-product of two algebras (multi-domain guards)

**Pipeline role:** Always-on. M1 is activated for every guard (bit 0
of the 15-bit `PredicateSignature`). All guard predicates compile to SFAs.

> Reference: D'Antoni & Veanes, POPL 2014 [§23, ref #9].
> See §15 for detailed BooleanAlgebra theory. See [symbolic-automata.md](../../prattail/docs/design/symbolic-automata.md).

#### M2: Weighted Büchi Automata — Infinite Behavior *(design-only)*

**Motivation.** Finite automata accept/reject finite words. But some guard
predicates concern infinite behaviors: "channel ch always eventually delivers
a message" (liveness), "every request is eventually acknowledged" (fairness).
These are omega-regular properties requiring Büchi acceptance.

**Intuition.** A train loops forever around a circular track. A Büchi automaton
accepts the infinite journey if the train passes through a "checkpoint" station
infinitely often. The weighted extension assigns a cost to each infinite loop,
computed via `StarSemiring` and matrix Kleene closure.

**Formal Definition.** A **Weighted Büchi Automaton** (WBA) over semiring W
and alphabet Σ is a tuple M = (Q, Σ, δ, I, F) where:

- Q, Σ, δ, I are as in a standard weighted finite automaton
- F ⊆ Q is the set of **Büchi accepting states**
- An infinite run ρ = q₀ q₁ q₂ … is accepting iff inf(ρ) ∩ F ≠ ∅,
  where inf(ρ) is the set of states visited infinitely often
- The weight of an accepting run requires the `StarSemiring` extension
  (closure operation a* = 1 ⊕ a ⊕ a² ⊕ ⋯) to sum over infinite paths

**Status:** Design-only (not yet implemented). Design doc:
[weighted-buchi.md](../../prattail/docs/design/weighted-buchi.md).

**Pipeline role:** Feature gate `omega`. Cost 3. Would be activated by guards
on infinite streams or recursive channel types.

> Reference: Büchi 1960 [§23, ref #5]; Droste & Gastin 2007 [§23, ref #13].

#### M3: Polynomial Alternating Weighted Automata — Quantifier Evaluation *(design-only)*

**Motivation.** Guards with universal and existential quantifiers —
`forall x in nodes. safe(x)` or `exists y in types. compatible(x, y)` —
require branching evaluation: universal quantifiers require *all* branches to
accept, existential quantifiers require *at least one*. Alternating automata
model this directly.

**Intuition.** An alternating automaton plays a two-player game. At an
**existential state** (Q⊕), the "prover" picks one successor — if any branch
accepts, the whole computation accepts. At a **universal state** (Q⊗), the
"refuter" picks — all branches must accept. Semiring weights generalize this:
existential combines via ⊕ (sum), universal via ⊗ (product).

**Formal Definition.** A **Polynomial Alternating Weighted Automaton** (AWA)
over semiring W is a tuple M = (Q⊕, Q⊗, Σ, δ, I, F) where:

- Q⊕ is the set of existential states (combine successors via ⊕)
- Q⊗ is the set of universal states (combine successors via ⊗)
- Q = Q⊕ ∪ Q⊗, Q⊕ ∩ Q⊗ = ∅
- Σ, δ, I, F are as in standard weighted automata
- H-polynomial fixpoints (Kostolanyi & Misun 2018) enable evaluation of
  nested quantifier patterns without exponential blowup

**Status:** Design-only (not yet implemented). Design doc:
[polynomial-awa.md](../../prattail/docs/design/polynomial-awa.md).

**Pipeline role:** Feature gate `alternating`. Cost 3. Would be activated
by quantified behavioral predicates with mixed ∀/∃ nesting.

> Reference: Chandra, Kozen & Stockmeyer 1981 [§23, ref #7];
> Kostolanyi & Misun 2018 [§23, ref #24].

#### M4: Weighted Visibly Pushdown Automata — Scope Nesting *(design-only)*

**Motivation.** Quantifier scoping — e.g., `forall x. exists y. P(x, y)` vs.
`exists y. forall x. P(x, y)` — has a natural call/return structure. Visibly
Pushdown Automata (VPA) model this: the input alphabet is partitioned into
call symbols (open scope), return symbols (close scope), and internal symbols,
with the stack discipline determined entirely by the input.

**Intuition.** A security guard at a revolving door verifies that every entry
(call) is matched by an exit (return) without knowing the building's internals.
The guard just watches the door: push on entry, pop on exit. Unlike general
pushdown automata, VPAs have decidable equivalence, intersection, and
complement — crucial for guard analysis.

**Formal Definition.** A **Weighted VPA** over semiring W is a tuple
M = (Q, Σ_c, Σ_r, Σ_int, Γ, δ, I, F) where:

- Σ_c, Σ_r, Σ_int are disjoint call, return, and internal alphabets
- Γ is the stack alphabet
- δ = δ_c ∪ δ_r ∪ δ_int with:
  - δ_c ⊆ Q × Σ_c × Q × Γ × W (call: push stack symbol)
  - δ_r ⊆ Q × Σ_r × Γ × Q × W (return: pop and match)
  - δ_int ⊆ Q × Σ_int × Q × W (internal: no stack change)

**Status:** Design-only (not yet implemented). Design doc:
[weighted-vpa.md](../../prattail/docs/design/weighted-vpa.md).

**Pipeline role:** Feature gate `vpa`. Cost 4. Would be activated by guards
with nested quantifier scopes or parenthesized expressions.

#### M5: Parity Alternating Tree Automata — Mu-Calculus

**Motivation.** Recursive behavioral predicates defined via `letprop` create
fixpoint definitions: `letprop safe(x) = base(x) ∨ (step(x) ∧ safe(child(x)))`.
These correspond to mu-calculus formulae, which compile directly to **Parity
Alternating Tree Automata** (PATA). The parity acceptance condition (minimum
priority visited infinitely often must be even) distinguishes least (μ) and
greatest (ν) fixpoints.

**Intuition.** A team of auditors inspects a corporate hierarchy (tree). At
each node, they check the symbol and branch into children. Even-priority states
mark "all clear" checkpoints; odd-priority states flag issues. The parity
condition ensures that the deepest recurring issue is resolved (even priority
wins).

**Formal Definition.** A **PATA** over Boolean semiring is a tuple
M = (Q, Σ, δ, q₀, Ω) where:

- Q = Q∃ ∪ Q∀ (existential and universal states)
- Σ is a ranked tree alphabet
- δ maps (state, symbol) → set of direction vectors (child_index, target_state, weight)
- q₀ is the initial state
- Ω: Q → ℕ assigns priorities (even = accepting, odd = rejecting)
- Acceptance: in any infinite branch, min{Ω(q) | q visited infinitely often} is even

Mu-calculus formulae:

```
  φ ::= X | ⊤ | ⊥ | p(a) | ¬φ | φ ∧ ψ | φ ∨ ψ
      | ⟨i⟩φ    (diamond: some child i satisfies φ)
      | [i]φ    (box: all children i satisfy φ)
      | μX.φ    (least fixpoint — finite unfolding)
      | νX.φ    (greatest fixpoint — infinite unfolding)
```

**Key types** (from [parity_tree.rs](../../prattail/src/parity_tree.rs)):

| Type                                | Role                                              |
|-------------------------------------|---------------------------------------------------|
| `ParityAlternatingTreeAutomaton<W>` | Tree automaton with parity acceptance             |
| `ParityTreeState`                   | `{ id, branching, priority, label }`              |
| `MuCalculusFormula`                 | Recursive enum: Var, True, False, Atom, …, Mu, Nu |
| `ParityTreeCompiler`                | PredicateCompiler impl for M5                     |
| `Term`                              | Concrete tree for evaluation                      |

**Key operations:**

| Operation            | Input           | Output              | Description                           |
|----------------------|-----------------|----------------------|---------------------------------------|
| `mu_calculus_to_pata`| `MuCalculusFormula` | `PATA`           | Compile mu-calculus to tree automaton |
| `evaluate_term`      | `PATA, Term`    | `bool`               | Bottom-up evaluation on concrete tree |
| `check_emptiness`    | `PATA`          | `bool`               | Parity game fixpoint iteration        |
| `check_inclusion`    | `PATA, PATA`    | `bool`               | Complement + product + emptiness      |

**Pseudocode — Mu-Calculus to PATA:**

```
mu_calculus_to_pata(φ: MuCalculusFormula, arity: ℕ) → PATA
  priority_counter ← 0
  case φ of
    Var(X)   → state for variable X (looked up from environment)
    True     → accepting state (priority 0, universal)
    False    → rejecting state (priority 1, universal)
    φ₁ ∧ φ₂ → universal state branching to PATA(φ₁) and PATA(φ₂)
    φ₁ ∨ φ₂ → existential state branching to PATA(φ₁) and PATA(φ₂)
    ⟨i⟩φ′   → existential state, direction = child i, recurse on φ′
    [i]φ′   → universal state, direction = child i, recurse on φ′
    μX.φ′   → priority ← next odd number; bind X; recurse on φ′
    νX.φ′   → priority ← next even number; bind X; recurse on φ′
  return PATA
```

**Pipeline role:** Feature gate `parity-tree`. Cost 4. Activated by `letprop`
recursive behavioral predicates.

> Reference: Emerson & Jutla 1991 [§23, ref #14]; Comon et al. TATA 2007 [§23, ref #8].
> See [parity-tree-automata.md](../../prattail/docs/design/parity-tree-automata.md).

#### M6: Register Automata — Data-Aware Predicates

**Motivation.** Some guards compare data values: `eq(x, y)` (the value on
channel x equals the value on channel y), `fresh(x)` (x has never been seen
before). Classical automata cannot express these — they have no memory for
previously seen values. Register automata add a fixed number of **registers**
that can store and compare data values from an infinite domain.

**Intuition.** A customs agent at a border has a clipboard with K slots
(registers). For each traveler (input symbol), the agent can: store the
passport number in a slot (`Store`), check if the number matches a stored slot
(`TestEq`), check if it differs from a stored slot (`TestNeq`), or check if
it differs from *all* stored slots (`TestFresh`). The agent's finite state
plus K register values determine the decision.

**Formal Definition.** A **Register Automaton** (RA) with k registers over
semiring W and data domain 𝒟 is a tuple M = (Q, k, Σ, δ, q₀, R₀, F) where:

- Q is a finite set of states
- k is the number of registers (each holds an element of 𝒟 or ⊥)
- Σ is a finite label alphabet (optional; may be data-only)
- δ ⊆ Q × (Σ ∪ {ε}) × RegisterOp^k × Q × W — each transition specifies one
  operation per register: `Nop`, `Store`, `TestEq`, `TestNeq`, or `TestFresh`
- q₀ is the initial state
- R₀ ∈ (𝒟 ∪ {⊥})^k is the initial register valuation
- F ⊆ Q is the set of accepting states

Register operations (from [register_automata.rs](../../prattail/src/register_automata.rs)):

```rust
pub enum RegisterOp {
    Nop,        // No operation on this register
    Store,      // Store current input value into this register
    TestEq,     // Guard: input equals this register's value
    TestNeq,    // Guard: input differs from this register's value
    TestFresh,  // Guard: input differs from ALL registers
}
```

**Key types:**

| Type                     | Role                                              |
|--------------------------|---------------------------------------------------|
| `RegisterAutomaton<W>`   | RA with `num_registers`, states, transitions       |
| `DataValue`              | `Integer(i64) \| Symbol(String) \| Unit`            |
| `RegisterOp`             | Per-register operation on each transition           |
| `RegisterAnalysis`       | Dead registers, unbound references                  |

**Pseudocode — Register Simulation:**

```
simulate_ra(M: RA, input: DataValue[]) → 𝔹
  state ← q₀;  registers ← R₀
  ∀ d ∈ input:                                   ▷ datum
    ∀ (state →[ops] state′, w) ∈ δ:              ▷ transition
      ▷ check guards
      ∀ r with ops[r]:                           ▷ register
        TestEq:    reject transition if registers[r] ≠ d
        TestNeq:   reject transition if registers[r] = d
        TestFresh: reject transition if d ∈ registers
      ▷ apply stores
      ∀ r with ops[r] = Store:                   ▷ register
        registers[r] ← d
      state ← state′
  return state ∈ F
```

**Pipeline role:** Feature gate `register-automata`. Cost 2. Activated by
equality (`eq`), inequality, or freshness (`fresh`) predicates in guards.

> Reference: Kaminski & Francez 1994 [§23, ref #21].
> See [register-automata.md](../../prattail/docs/design/register-automata.md).

#### M7: Probabilistic Automata — Selectivity Estimation

**Motivation.** When multiple guards protect different rules, evaluating them in
the right order is critical. A guard with 5% selectivity (rejects 95% of inputs)
should be evaluated before one with 80% selectivity (rejects only 20%). M7
estimates guard selectivity using probabilistic automata, enabling optimal
short-circuit ordering.

**Intuition.** A weather forecaster with multiple prediction models. Each model
(guard) assigns a probability to each outcome. The forward algorithm computes
total probability (how selective is this guard?), the Viterbi algorithm finds
the most likely path (what is the guard's best-case behavior?), and entropy
measures uncertainty (how discriminating is this guard?).

**Formal Definition.** A **Probabilistic Automaton** (PA) is a weighted
automaton where weights are log-probabilities (`LogWeight`):

- All weights are in the log-probability domain: w = −log(p) where p ∈ [0, 1]
- Initial distribution: Σ_q I(q) = 1 (normalized)
- Transition probabilities: for each state q, Σ_{(q,a,q′)} p(q,a,q′) = 1
- Selectivity: sel(M) = Σ_w ⟦M⟧(w), the total acceptance probability
- Entropy: H(M) = −Σ_w ⟦M⟧(w) · log ⟦M⟧(w), the uncertainty measure

**Key types** (from [probabilistic.rs](../../prattail/src/probabilistic.rs)):

| Type                     | Role                                            |
|--------------------------|-------------------------------------------------|
| `ProbabilisticAutomaton` | States + `LogWeight` transitions + initial dist |
| `ProbabilisticAnalysis`  | Selectivity, entropy, low-selectivity rules     |
| `ProbabilisticCompiler`  | PredicateCompiler impl for M7                   |

**Key operations:**

| Operation             | Input        | Output           | Description                                |
|-----------------------|--------------|------------------|--------------------------------------------|
| `probability_of`      | `PA, word`   | `LogWeight`      | Forward algorithm: total probability       |
| `viterbi`             | `PA, word`   | `(Weight, path)` | Most likely state sequence                 |
| `entropy`             | `PA`         | `f64`            | Shannon entropy of the distribution        |
| `selectivity`         | `PA`         | `LogWeight`      | Total acceptance probability               |
| `train_from_corpus`   | `PA, corpus` | `()`             | Baum-Welch EM parameter learning           |
| `optimal_guard_order` | `[PA]`       | `[usize]`        | Sort by selectivity (most selective first) |

**Pipeline role:** Always-on. Cost 5. M7 determines guard evaluation order for
all rules with multiple guards. Feeds M8/M11 pipeline (§2A).

> See [probabilistic-automata.md](../../prattail/docs/design/probabilistic-automata.md).

#### M8: Multi-Tape Automata — Traversal Fusion

See **§2A, "Part I — Multi-Tape Automata (M8): Traversal Fusion"** for the
complete treatment: motivation, intuition (DJ turntables analogy), formal
Definition 2A.1, pair construction with three transition classes, pseudocode
(PAIR and EVALUATE algorithms), literate code from [multi_tape.rs](../../prattail/src/multi_tape.rs),
and complexity analysis.

**Pipeline role:** Feature gate via `channels {}` or heuristic. Cost 5. Fuses
N per-channel SFAs into a single K-tape product automaton.

> Reference: Kempe 2004 [§23, ref #22].

#### M9: Multiset Automata — Cardinality Predicates

**Motivation.** Guards like `count(chan) ≥ 3` or `multiplicity(token, "x") ∈ [2,5]`
involve counting — not just accepting/rejecting symbols, but tracking how many
times features occur. Multiset automata extend weighted automata with
**feature accumulators** that count occurrences along paths.

**Intuition.** A bakery production line with ingredient counters at each station.
As a batch moves through stations (transitions), counters accumulate: "2 cups
flour," "3 eggs," "1 cup sugar." At the end, a quality inspector checks that
each ingredient falls within required bounds (cardinality constraints).

**Formal Definition.** A **Multiset Automaton** over heap semiring W with
feature set F is a tuple M = (Q, Σ, F, δ, q₀, A) where:

- Q, Σ, q₀ are standard automaton components
- F = {f₁, …, fₘ} is a finite set of feature names
- δ ⊆ Q × Σ × Q × W × (F → ℕ) — each transition carries a weight *and*
  feature effect map (how many of each feature this transition contributes)
- A is a set of `CardinalityConstraint` predicates:
  each `{ feature: f, min: Option<u64>, max: Option<u64> }` bounds
  the total accumulated count of feature f along any accepting path

The `HeapSemiring` trait (from [multiset_automata.rs](../../prattail/src/multiset_automata.rs)) enables
semirings backed by `HashMap` (non-Copy types), bridging standard `Semiring`
(Copy) and heap-allocated multiset domains:

- `MultisetWeight` — natural-number multiset with pointwise max/add
- `TropicalMultisetWeight` — tropical (min/+) over multiset features

**Key types:**

| Type                    | Role                                              |
|-------------------------|---------------------------------------------------|
| `MultisetAutomaton<W>`  | Automaton with feature accumulators               |
| `CardinalityConstraint` | `{ feature, min, max }` — bounds on feature count |
| `MultisetWeight`        | `HashMap<String, u64>` — counting semiring        |
| `MultisetCompiler`      | PredicateCompiler impl for M9                     |

**Key operations:**

| Operation               | Input                  | Output | Description                         |
|-------------------------|------------------------|--------|-------------------------------------|
| `multiplicity_of`       | `MA, feature, word`    | `u64`  | Total feature count along best path |
| `satisfies_cardinality` | `MA, constraint, word` | `bool` | Does the count meet bounds?         |
| `feature_interaction`   | `MA, f₁, f₂`           | `bool` | Do features co-occur on paths?      |

**Pipeline role:** Feature gate `multiset-automata`. Cost 2. Activated by
cardinality predicates (`count_ge`, `count_le`, `multiplicity`). PPar analysis
with HashBag multiplicities.

> See [multiset-automata.md](../../prattail/docs/design/multiset-automata.md).

#### M10: Weighted MSO — Specification Language

**Motivation.** M10 is **the** specification language. The `where`-clause syntax
— `not()`, `and()`, `or()`, `forall()`, `exists()` — *is* weighted monadic
second-order (MSO) logic. M10 classifies each guard formula, determines its
decidability tier, and routes it to the appropriate evaluation strategy.

**Intuition.** MSO is like a spreadsheet formula language where each cell is a
position in a word. Atomic predicates check which symbol is at a position (`label_a(x)`
means "position x has symbol a"). First-order quantifiers (`∀x`, `∃x`) range over
positions. Second-order quantifiers (`∀X`, `∃X`) range over *sets* of positions.
Weights replace Boolean true/false with quantitative measures.

**Formal Definition.** A **Weighted MSO formula** over alphabet Σ and semiring W:

```
  φ ::= const(s)                       (semiring constant)
      | label_a(x)                     (position x has symbol a)
      | ¬label_a(x)                    (negated atomic)
      | x < y                          (position order)
      | x ∈ X                          (set membership)
      | φ ∧ ψ | φ ∨ ψ                  (Boolean connectives)
      | ∃x. φ | ∀x. φ                  (first-order quantifiers)
      | ∃X. φ | ∀X. φ                  (second-order quantifiers)
```

**Büchi-Elgot-Trakhtenbrot Theorem.** The recognizable formal power series
(those definable by weighted automata) are exactly those definable in the
**restricted** MSO fragment: no `∀X` or `∀x` except with step-function bodies.
This is the decidability boundary.

**Formula classification** (`MsoFormulaClass`):

| Class                   | Description                           | Decidability |
|-------------------------|---------------------------------------|--------------|
| `Restricted`            | No quantifiers                        | T1           |
| `RestrictedExistential` | Only ∃x, ∃X quantifiers               | T1           |
| `FirstOrder`            | Only first-order quantifiers (∀x, ∃x) | T2           |
| `Full`                  | Second-order quantifiers (∀X, ∃X)     | T3/T4        |

**Key types** (from [weighted_mso.rs](../../prattail/src/weighted_mso.rs)):

| Type                 | Role                                                   |
|----------------------|--------------------------------------------------------|
| `WeightedMsoFormula` | Recursive enum: AtomicPos, And, Or, ExistsFirst, etc.  |
| `MsoFormulaClass`    | Classification: Restricted / FirstOrder / Full         |
| `MsoAnalysis`        | Formula class + decidability + free vars + is_sentence |
| `MsoCompiler`        | PredicateCompiler impl for M10                         |

**Pipeline role:** Always-on. Cost 1. M10 classifies every guard's logical
structure, routing it to the appropriate tier and evaluation strategy.

> Reference: Droste & Gastin 2007 [§23, ref #13]; Büchi 1960 [§23, ref #5].
> See [weighted-mso.md](../../prattail/docs/design/weighted-mso.md).

#### M11: Two-Way Transducers — Value Space Pruning

See **§2A, "Part II — Two-Way Transducers (M11): Value Space Pruning"** for
the complete treatment: motivation (Cartesian product reduction), intuition
(librarian analogy), formal Definition 2A.2, enhanced tape and head movement,
crossing sequences with Theorem 2A.1 (Shepherdson 1959), ChannelConstraint
struct, pseudocode (TRANSDUCE algorithm), and literate code from
[two_way_transducer.rs](../../prattail/src/two_way_transducer.rs).

**Pipeline role:** Feature gate via `channels {}` or heuristic. Cost 6.
Backward constraint propagation prunes channel value spaces.

> Reference: Feng & Maletti 2022 [§23, ref #15].

#### M12–M15: Constraint Theories and Transductions

M12 (Presburger Arithmetic), M13 (Unification), and M14 (Subtype Lattice)
are fully treated in §16 with formal definitions, pseudocode, and literate
code. M15 (Symbolic Finite Transducers) is treated below in this section.
Pipeline roles and feature gates are documented at the end of each
module's §16/§17 subsection.


### Predicate Dispatch Controller

The controller determines the minimal module set per guard:

1. **Feature extraction:** `extract_features(expr, ctx) → PredicateProfile`
   in O(|AST|)
2. **Signature computation:** Profile → 15-bit `PredicateSignature(u16)`
   (one bit per module, M1–M15)
3. **Cost-ordered execution:** Modules ordered by `estimated_cost()`:
   M1/M10 = 1, M6/M9/M14 = 2, M2/M3/M12/M13 = 3, M4/M5 = 4, M7/M8/M15 = 5, M11 = 6
4. **Early termination:** Skip modules not in signature; cheap modules
   resolve before expensive ones fire

**Concrete example:** Guard `eq(x, fresh_name), count_ge(ch, 2)` activates
only M1+M6+M9+M10, skipping 11 modules. The dispatch controller extracts
features (equality test → M6, cardinality → M9) and computes the 4-bit
signature, executing in cost order: M1 (satisfiability), M10
(classification), M6 (register analysis), M9 (multiset check).

### Always-On Analysis Modules

These modules run on every guard regardless of the predicate signature
(negligible amortized cost: O(|guards|) per channel):

| Module                                                   | Guard-Related Role                                                   |
|----------------------------------------------------------|----------------------------------------------------------------------|
| **Weighted Pushdown System (WPDS)**                      | Stack-aware reachability for guard evaluation chains                 |
| **Counterexample-Guided Abstraction Refinement (CEGAR)** | Iterative refinement: Boolean→Counting→Tropical abstraction ladder   |
| **Safety**                                               | Guard completeness: does every input match ≥1 guard?                 |
| **Algebraic**                                            | Path expressions summarize guard evaluation control-flow graph (CFG) |
| **Newton**                                               | Accelerated fixpoint: h+1 iterations for idempotent semirings        |
| **Forward-Backward**                                     | Hot-path guards → `#[inline]`, cold → `#[cold]`                      |

### Feature-Gated Analysis Modules

| Module                              | Guard-Related Role                                                       |
|-------------------------------------|--------------------------------------------------------------------------|
| **Term Rewriting System (TRS)**     | Guard-conditional rewrite confluence + termination                       |
| **Nominal**                         | Name-binding safety, alpha-equivalence in guard patterns                 |
| **Petri**                           | Deadlock analysis for guarded communication                              |
| **Kleene Algebra with Tests (KAT)** | Guard flow equivalence, Hoare triples                                    |
| **CRA** (Cost Register Automata)    | Quantitative guard cost metering                                         |
| **Morphism**                        | Translation verification between guard formalisms                        |
| **Provenance**                      | Derivation tracking through guard evaluation                             |
| **Proof Output**                    | Correctness certificates (confluence + termination + safety)             |
| **WTA** (Weighted Tree Automata)    | Term recognition/ranking, set-theoretic subtyping via language inclusion |
| **LTL** (Linear Temporal Logic)     | Temporal safety/liveness properties over WPDS call graphs                |
| **EWPDS** (Extended WPDS)           | Merging functions for local variable analysis at call/return boundaries  |
| **ARA** (Affine-Relation Analysis)  | Affine invariant discovery (subsumes constant/copy/linear propagation)   |
| **Relational WPDS**                 | Binary relation weight domain (`HeapSemiring`) for heap analysis         |

### Symbolic Finite Transducers (M15)

**Motivation.** Some guards do not merely accept or reject — they *transform*
values before comparison. Case-folding (`"Hello" → "hello"`), whitespace
normalization, and guard-conditional rewrites all produce output. SFTs extend
SFAs with output functions: where SFAs accept/reject, SFTs transform inputs
to outputs. Source: [sft.rs](../../prattail/src/sft.rs) (feature gate `sft`).
Design doc: [symbolic-finite-transducer.md](../../prattail/docs/design/symbolic-finite-transducer.md).

**Intuition.** An SFA is a gatekeeper that says "yes" or "no." An SFT is a
translator that reads input, transforms it according to predicate-guarded rules,
and writes output. Composition chains translators: the output of one SFT becomes
the input of the next. The pre-image operation asks: "what inputs could have
produced outputs in this target set?" — enabling backward reasoning about
transformations.

**Formal Definition.** A **Symbolic Finite Transducer** (SFT) over input
Boolean algebra A and output Boolean algebra B is a tuple
M = (Q, A, B, δ, I, F) where:

- Q is a finite set of states
- A is the input Boolean algebra (predicates over infinite input domain)
- B is the output Boolean algebra (predicates over infinite output domain)
- δ ⊆ Q × Pred(A) × (A.Domain → B.Domain*) × Q is the transition relation.
  Each transition (q, φ, f, q′) reads an input satisfying predicate φ,
  produces output f(input), and moves to state q′.
- I ⊆ Q is the set of initial states
- F ⊆ Q is the set of accepting states

The output function f on each transition is one of:
- `Epsilon` — no output produced
- `Constant(v)` — fixed output sequence v ∈ B.Domain*
- `Identity` — copy input to output unchanged
- `Map(g)` — apply function g: A.Domain → B.Domain
- `FlatMap(g)` — apply function g: A.Domain → Vec<B.Domain>

An SFA is a degenerate SFT where every transition has `Epsilon` output.

**Key operations:**

| Operation                  | Input                | Output               | Description                                              |
|----------------------------|----------------------|----------------------|----------------------------------------------------------|
| `transduce`                | `SFT, word`          | `Vec<Vec<B.Domain>>` | Apply transducer, collect all output sequences           |
| `compose`                  | `SFT<A,B>, SFT<B,C>` | `SFT<A,C>`           | Chain two transducers: output of first → input of second |
| `pre_image`                | `SFT<A,B>, SFA<B>`   | `SFA<A>`             | Input language whose outputs land in the target          |
| `post_image`               | `SFT<A,B>, SFA<A>`   | `SFA<B>`             | Output language reachable from the input language        |
| `domain_sfa`               | `SFT<A,B>`           | `SFA<A>`             | Input language accepted by the transducer                |
| `is_functional`            | `SFT<A,B>`           | `bool`               | Does each input produce exactly one output?              |
| `is_equivalent_functional` | `SFT, SFT`           | `bool`               | Same transduction on all inputs?                         |

**Data flow diagram:**

```
┌────────────┐  input  ┌───────────┐  output ┌────────────┐
│ Input SFA  │────────►│ SFT<A,B>  │────────►│ Output SFA │
│ (domain)   │         │ transduce │         │ (range)    │
└────────────┘         └───────────┘         └────────────┘
                            │
        ┌───────────────────┤
        │ pre_image         │ post_image
        ▼                   ▼
  ┌────────────┐     ┌────────────┐
  │ SFA<A>     │     │ SFA<B>     │
  │ (backward) │     │ (forward)  │
  └────────────┘     └────────────┘
```

**Pseudocode — Composition:**

```
compose(T₁: SFT<A,B>, T₂: SFT<B,C>) → SFT<A,C>
  Product states: Q₁ × Q₂ (with lookahead buffer for multi-symbol output)
  ∀ t₁ = (p₁ →[φ₁/f₁] q₁) ∈ T₁:               ▷ transition
    compute output symbols: out₁ = f₁(witness(φ₁))
    ∀ prefix ∈ prefixes(out₁) consumable by T₂:
      find matching T₂ transitions t₂ = (p₂ →[φ₂/f₂] q₂)
      where φ₂ accepts the output symbols
      Combined guard: φ₁ ∧ (f₁ satisfies φ₂)
      Combined output: f₂(f₁(·))
      add transition (p₁,p₂) →[combined_guard/combined_output] (q₁,q₂)
  Initial: I₁ × I₂.  Accepting: F₁ × F₂.
  return composed SFT
```

**Pseudocode — Transduction:**

```
transduce(T: SFT<A,B>, word: [A.Domain]) → Set<[B.Domain]>
  configs ← { (s, ε) | s ∈ initial_states(T) }
  ∀ σ ∈ word:                                       ▷ symbol
    next ← ∅
    ∀ (state, output) ∈ configs:
      ∀ (state →[φ/f] q) where φ(σ) = true:         ▷ transition
        next ← next ∪ { (q, output · f(σ)) }
    configs ← next
  return { output | (s, output) ∈ configs, s ∈ accepting_states(T) }
```

Implementation: [sft.rs — transduce()](../../prattail/src/sft.rs).

**Factories:** `case_fold_sft()`, `whitespace_normalize_sft()`, `guard_transform_sft()`.

**Pipeline role:** Feature gate `sft`. Cost 5. Module ID M15.
Pipeline: `SftAnalysis`, lints SFT01–SFT04, cost-benefit gate, predicate
dispatch M15:Sft. In the guard infrastructure, SFTs enable transducer-based
guard compilation — guards that transform input values (e.g., case-folding
before comparison) compile to SFT composition rather than post-hoc normalization.

> Reference: D'Antoni & Veanes, POPL 2014 [§23, ref #9].

### E-Graph Equality Saturation

**Motivation.** Guard predicates may contain redundant subexpressions
(`x > 0 ∧ x > 0`), algebraic identities (`x + 0 → x`), or equivalent
formulations that produce unnecessarily large SFAs. Equality saturation
discovers these equivalences at compile time, simplifying guards before SFA
compilation. Source: [egraph.rs](../../prattail/src/egraph.rs).
Feature gate: `egraph = ["trs-analysis"]`.
Design doc: [egraph-equality-saturation.md](../../prattail/docs/design/egraph-equality-saturation.md).

**Intuition.** An e-graph is a compact representation of many equivalent terms
simultaneously. Unlike destructive rewriting (which replaces a term with its
reduct, losing the original), an e-graph *adds* the reduct as a new member of
the same equivalence class, preserving all prior representations. Equality
saturation applies all rewrite rules to fixpoint, then extracts the cheapest
equivalent term.

**Formal Definition.** An **e-graph** is a tuple (E, M, U) where:

- E is a set of **e-classes** (equivalence classes of terms)
- M: ENode → EClassId is the **memo table** mapping e-nodes to their class
- U is a **union-find** data structure maintaining the equivalence partition

An **e-node** is a function application f(c₁, …, cₙ) where each cᵢ is an
e-class ID (not a concrete term). The central invariant is **congruence
closure**: if two e-nodes f(c₁, …, cₙ) and f(c₁′, …, cₙ′) have
find(cᵢ) = find(cᵢ′) for all i, they must be in the same e-class.

An **equality saturation** run applies rewrite rules (l → r) to the e-graph:

```
┌─────────────────────────────────────────────────────────────────┐
│                 Equality Saturation Loop                        │
│                                                                 │
│  ┌───────────┐  matches  ┌───────────┐ new e-nodes ┌──────────┐ │
│  │  Match    │──────────►│  Apply    │────────────►│ Rebuild  │ │
│  │  (search  │           │  (instan- │             │ (restore │ │
│  │   LHS     │           │   tiate   │             │  congru- │ │
│  │   pattern)│           │   RHS,    │             │  ence)   │ │
│  └───────────┘           │   merge)  │             └────┬─────┘ │
│       ▲                  └───────────┘                  │       │
│       │                                                 │       │
│       └─────────────────────────────────────────────────┘       │
│                                                                 │
│      Terminate when: no new merges, or resource limit hit       │
└─────────────────────────────────────────────────────────────────┘
```

> Reference: Willsey et al., "egg: Fast and Extensible Equality Saturation,"
> POPL 2021 [§23, ref #33].

**Key types** (from [egraph.rs](../../prattail/src/egraph.rs)):

| Type            | Role                                                       |
|-----------------|------------------------------------------------------------|
| `EClassId(u32)` | Unique equivalence class identifier                        |
| `ENode`         | Function application `{ symbol, children: Vec<EClassId> }` |
| `EClass`        | Equivalence class `{ id, nodes, parents }`                 |
| `EGraph`        | Core structure with union-find, memo table, pending merges |
| `ERewriteRule`  | Pattern-based rewrite `{ lhs: Pattern, rhs: Pattern }`     |
| `EGraphConfig`  | Resource limits `{ max_nodes, max_iterations }`            |

**Pseudocode — Equality Saturation:**

```
saturate(G: EGraph, rules: [RewriteRule]) → SaturationResult
  repeat
    changed ← false
    ▷ match phase
    ∀ (l → r) ∈ R:                                 ▷ rule
      matches ← search_pattern(G, l)               ▷ find LHS pattern instances
    ▷ apply phase
    ∀ (class_id, substitution) ∈ matches:          ▷ match
      rhs_id ← instantiate(G, r, substitution)     ▷ build RHS e-node
      if find(class_id) ≠ find(rhs_id) then
        merge(G, class_id, rhs_id)                 ▷ equate LHS and RHS
        changed ← true
    ▷ rebuild phase
    rebuild(G)                                     ▷ restore congruence closure
  until ¬changed ∨ |nodes(G)| > max_nodes
  return { iterations, saturated: ¬changed }
```

Implementation: [egraph.rs](../../prattail/src/egraph.rs).

**Cost-based extraction.** After saturation, `extract_best(class_id)` finds
the smallest (by AST size) equivalent term in the class, using a bottom-up
dynamic programming pass over the e-graph.

**Pipeline role:** Pipeline integration via `EGraphAnalysis`, lints EG01–EG04,
cost-benefit gate `EGraphSaturation`. In the guard infrastructure, e-graphs
simplify guard predicates via equality saturation — discovering algebraic
identities before SFA compilation, producing smaller automata and faster
runtime checks.

### WPDS Extension Family (EWPDS, ARA, Relational)

**Motivation.** A **Weighted Pushdown System** (WPDS) models recursive grammar
structures: each rule expansion is a stack push, each completion is a pop.
The **poststar** and **prestar** algorithms compute forward and backward
reachability over all possible stack configurations, weighted by a semiring.
This enables interprocedural analysis of guard evaluation chains — determining
which guard sequences are reachable and at what cost. Source:
[wpds.rs](../../prattail/src/wpds.rs). Extensions: [`ewpds.rs`](../../prattail/src/ewpds.rs), [`ara.rs`](../../prattail/src/ara.rs),
[`relational.rs`](../../prattail/src/relational.rs).

**Intuition.** Think of a WPDS as a program call stack where each function call
pushes a frame and each return pops one. The semiring weight on each
push/pop/replace rule captures the "cost" of that transition. Poststar asks:
"Starting from this initial stack, what stacks can I reach, and at what total
cost?" Prestar asks the reverse: "What initial stacks can reach this target?"

**Formal Definition.** A WPDS is a triple (P, Γ, Δ, W) where:

- P = {p} is a singleton control location (grammar has one "program point")
- Γ is the **stack alphabet** — one `StackSymbol` per grammar position
  (category entry, rule position). Each symbol carries `{ category, rule_label, position }`.
- Δ is a finite set of **rules**, each of three kinds:
  - **Pop:** ⟨p, γ⟩ ↪ ⟨p, ε⟩ with weight w (rule completes, stack shrinks)
  - **Replace:** ⟨p, γ⟩ ↪ ⟨p, γ′⟩ with weight w (advance within a rule)
  - **Push:** ⟨p, γ⟩ ↪ ⟨p, γ′ γ″⟩ with weight w (enter sub-category)
- W is a semiring over which weights are computed

A **P-automaton** represents sets of stack configurations. States correspond to
stack symbols; transitions read stack symbols bottom-to-top.

**Key types** (from [wpds.rs](../../prattail/src/wpds.rs)):

| Type                      | Role                                                  |
|---------------------------|-------------------------------------------------------|
| `StackSymbol`             | `{ category, rule_label, position }` — stack alphabet |
| `WpdsRule<W>`             | `Pop \| Replace \| Push` with semiring weight         |
| `Wpds<W>`                 | Rule set + symbol index + initial symbol              |
| `PAutomaton<W>`           | Weighted P-automaton for configuration sets           |
| `PAutomatonTransition<W>` | `(from, symbol, to, weight)` — one automaton edge     |

**Pseudocode — Poststar:**

```
poststar(wpds: WPDS, init: PAutomaton) → PAutomaton
  result ← copy(init)
  worklist ← all transitions in result
  while worklist ≠ ∅ do
    t ← pop(worklist)  where t = (p →[γ] q, w)
    ∀ r matching source symbol γ:                  ▷ rule
      case r of
        Pop(γ, w_r) →
          ▷ stack shrinks: merge q into accepting
          update_weight(result, p, accepting, w ⊗ w_r)
        Replace(γ, γ′, w_r) →
          ▷ stack unchanged: relabel
          add_or_update(result, p →[γ′] q, w ⊗ w_r)
        Push(γ, γ_bot, γ_top, w_r) →
          ▷ stack grows: new intermediate state
          q_mid ← get_or_create_state(γ_bot)
          add_or_update(result, p →[γ_top] q_mid, w ⊗ w_r)
          ▷ propagate existing transitions from q_mid
          ∀ (q_mid →[γ″] q″, w″) in result:
            push(worklist, (p →[γ_top] q″, w ⊗ w_r ⊗ w″))
  return result
```

**Data flow diagram:**

```
┌──────────────┐         ┌──────────────┐         ┌──────────────┐
│  Grammar     │ build   │    WPDS      │ poststar│ P-Automaton  │
│  Categories  │────────►│  (rules +    │────────►│ (reachable   │
│  & Rules     │         │   symbols)   │         │  configs)    │
└──────────────┘         └──────┬───────┘         └──────┬───────┘
                                │ prestar                │
                                ▼                        │ extract
                         ┌──────────────┐         ┌──────▼───────┐
                         │ P-Automaton  │         │ Call Graph   │
                         │ (backward    │         │ + SCC + Depth│
                         │  reachable)  │         │  Bounds      │
                         └──────────────┘         └──────────────┘
```

**Extension modules:**

- **EWPDS** ([`ewpds.rs`](../../prattail/src/ewpds.rs), feature `wpds-extended`): Extends WPDS with **merging
  functions** at call/return boundaries for local variable analysis. At a return
  point, the merge function combines the callee's summary with the caller's
  local state. Pipeline: `EwpdsAnalysis`.
- **ARA** ([`ara.rs`](../../prattail/src/ara.rs), feature `wpds-ara`, dep: `wpds-relational`): **Affine-Relation
  Analysis** — vector space weight domain discovering interprocedural affine
  invariants (e.g., "variable y = 2x + 1 at this point"). Pipeline: `AraAnalysis`.
- **Relational** ([`relational.rs`](../../prattail/src/relational.rs), feature `wpds-relational`): `HeapSemiring`
  trait + `RelationalWeight<G>` binary relation semiring. Weight domain
  foundation for ARA — models sets of (input, output) state pairs.

> Reference: Reps, Lal & Kidd, CAV 2007.

**Pipeline role:** Always-on (core WPDS). Stack-aware reachability for guard
evaluation chains. Extensions are feature-gated. 43 WPDS tests.

### Weighted Tree Automata (WTA)

**Motivation.** Parse trees are terms over a ranked alphabet — each grammar rule
produces a node whose children are the sub-parses. WTAs evaluate terms
bottom-up, assigning a semiring weight to each subtree. This enables term
recognition (does this tree conform to the grammar?), ranking (which parse is
cheapest?), and set-theoretic subtype checking (is the tree language of type A
included in the tree language of type B?). Source: [tree_automaton.rs](../../prattail/src/tree_automaton.rs)
(feature `tree-automata`).

**Intuition.** Think of a WTA as a team of inspectors at each node of a tree.
Each inspector checks the node's symbol and the states assigned to its children,
then assigns a weighted state to the current node. The tree is accepted if the
root receives a final state. Bottom-up evaluation ensures that every subtree is
validated before its parent.

**Formal Definition.** A **Weighted Tree Automaton** (WTA) over semiring W and
ranked alphabet Σ is a tuple M = (Q, Σ, δ, F) where:

- Q is a finite set of states
- Σ is a ranked alphabet: each symbol f ∈ Σ has a fixed arity rank(f) ∈ ℕ
- δ is the transition relation. For each symbol f with rank(f) = n:
  δ_f ⊆ Qⁿ × Q × W — a transition (q₁, …, qₙ, q, w) means: if child 1 is
  in state q₁, …, child n in state qₙ, then the f-node can be assigned state q
  with weight w.
- F ⊆ Q is the set of final (accepting) states

The weight of a run ρ on term t is the ⊗-product of all transition weights used:

  w(ρ) = ⊗{ w(v) | v is a node in t }

The automaton's semantics:

  ⟦M⟧(t) = ⊕{ w(ρ) | ρ is an accepting run on t }

**Key types** (from [tree_automaton.rs](../../prattail/src/tree_automaton.rs)):

| Type                | Role                                                 |
|---------------------|------------------------------------------------------|
| `TreeState`         | `{ id, label, is_final }` — automaton state          |
| `TreeTransition<W>` | `{ symbol, child_states, target_state, weight }`     |
| `TreeAutomaton<W>`  | States + transitions + ranked alphabet               |
| `Term`              | Concrete term tree `{ symbol, children: Vec<Term> }` |

**Pseudocode — Bottom-Up Evaluation:**

```
bottom_up_evaluate(M: WTA, t: Term) → Map<StateId, W>
  if t is a leaf (arity 0) then
    ∀ ([], q, w) ∈ δ_{symbol(t)}:                     ▷ transition
      result[q] ⊕= w
    return result
  ∀ cᵢ ∈ children(t):
    child_states[i] ← bottom_up_evaluate(M, cᵢ)       ▷ recurse
  ∀ (q₁…qₙ, q, w) ∈ δ_{symbol(t)}:                    ▷ transition
    if all qᵢ ∈ child_states[i] then
      combined ← w ⊗ child_states[0][q₁] ⊗ ⋯ ⊗ child_states[n−1][qₙ]
      result[q] ⊕= combined
  return result
```

**Term tree diagram:**

```
  Term: f(g(a, b), h(c))       WTA evaluation (bottom-up):

        f                            f: q_f (w₃)
       ╱ ╲                          ╱ ╲
      g    h                       g    h
     ╱ ╲    ╲            →        ╱ ╲    ╲
    a    b   c                   a    b   c
                                q_a  q_b  q_c
                                (w₀) (w₀) (w₀)

  Weight at root: w₃ ⊗ (w₁ ⊗ w₀ ⊗ w₀) ⊗ (w₂ ⊗ w₀)
  Accept if q_f ∈ F
```

**Pipeline role:** Feature gate `tree-automata`. `WtaAnalysis` pipeline result.
Used by `SetTheoreticTypeSystem` for subtype checking as language inclusion:
type A ≤ type B iff L(WTA_A) ⊆ L(WTA_B). Hot-path analysis identifies
frequently-used subtree patterns for specialization.

> Reference: Comon et al., TATA (2007) [§23, ref #8].

### Linear Temporal Logic (LTL)

**Motivation.** Some grammar properties are inherently temporal: "every function
call is eventually matched by a return" (liveness), "no two consecutive shifts
without a reduce" (safety), "a lock is always released before re-acquisition"
(mutual exclusion). LTL provides a declarative syntax for such properties.
Source: [ltl.rs](../../prattail/src/ltl.rs) (feature `ltl`, dep: `omega`).

**Intuition.** LTL extends propositional logic with time. "p holds now" becomes
"p holds *eventually*" (◇p), "p holds *always*" (□p), "p holds *next* step"
(Xp), or "p holds *until* q becomes true" (p U q). These temporal operators
compose: □◇p means "p holds infinitely often."

**Formal Definition.** LTL formulae over atomic propositions AP:

```
  φ ::= p           (atom, p ∈ AP)
      | ¬φ          (negation)
      | φ ∧ ψ       (conjunction)
      | φ ∨ ψ       (disjunction)
      | Xφ          (**neXt**: φ holds in the next state)
      | ◇φ          (**eventually**/Finally: φ holds at some future state)
      | □φ          (**always**/Globally: φ holds at all future states)
      | φ U ψ       (**until**: φ holds until ψ becomes true)
      | φ R ψ       (**release**: dual of until — ψ holds until φ ∧ ψ, or forever)
      | φ W ψ       (**weak until**: like U but φ may hold forever without ψ)
```

Derived: ◇φ ≡ true U φ, □φ ≡ ¬◇¬φ, φ W ψ ≡ (φ U ψ) ∨ □φ.

**LTL semantics** over an infinite word σ = s₀ s₁ s₂ … ∈ (2^AP)^ω:

- σ, i ⊨ p      iff p ∈ sᵢ
- σ, i ⊨ Xφ     iff σ, i+1 ⊨ φ
- σ, i ⊨ □φ     iff ∀j ≥ i. σ, j ⊨ φ
- σ, i ⊨ ◇φ     iff ∃j ≥ i. σ, j ⊨ φ
- σ, i ⊨ φ U ψ  iff ∃j ≥ i. σ, j ⊨ ψ ∧ ∀k ∈ [i,j). σ, k ⊨ φ

**Key types** (from [ltl.rs](../../prattail/src/ltl.rs)):

| Type             | Role                                                                                                                |
|------------------|---------------------------------------------------------------------------------------------------------------------|
| `LtlFormula`     | Recursive enum: `True \| Atom \| Not \| And \| Or \| Next \| Eventually \| Always \| Until \| Release \| WeakUntil` |
| `LtlProperty`    | Named formula with safety/liveness classification                                                                   |
| `LtlCheckResult` | `Satisfied \| Violated { prefix, lasso } \| Inconclusive`                                                           |

**Büchi translation.** `ltl_to_buchi(φ)` converts an LTL formula to a
**Büchi automaton** — an automaton over infinite words that accepts by visiting
an accepting state infinitely often. The translation uses the tableau
construction of Vardi & Wolper (1986).

**Pseudocode — LTL Model Checking via WPDS:**

```
check_ltl(wpds: WPDS, property: LtlFormula) → LtlCheckResult
  büchi ← ltl_to_buchi(¬φ)        ▷ negate: find violations
  product ← wpds × büchi          ▷ synchronous product
  post ← poststar(product)        ▷ forward reachability
  if ∃ accepting cycle in post then
    extract prefix (path to cycle) + lasso (cycle itself)
    return Violated { prefix, lasso }
  return Satisfied
```

**Verification flow diagram:**

```
┌──────────┐  ¬φ  ┌──────────┐  ×   ┌──────────────┐  poststar ┌──────────┐
│ LTL φ    │─────►│ Büchi    │─────►│ WPDS × Büchi │──────────►│ Reachable│
│ property │      │ automaton│      │ (product)    │           │ configs  │
└──────────┘      └──────────┘      └──────────────┘           └────┬─────┘
                                                                    │
                                                          accepting cycle?
                                                          ╱             ╲
                                                        Yes              No
                                                         │               │
                                                  ┌──────▼──────┐  ┌─────▼─────┐
                                                  │ Violated    │  │ Satisfied │
                                                  │ (prefix +   │  │           │
                                                  │  lasso)     │  └───────────┘
                                                  └─────────────┘
```

**Pipeline role:** Feature gate `ltl` (dep: `omega`). Full temporal operators
(□, ◇, X, U, R, W). Pipeline: `check_from_bundle()` → `Vec<LtlCheckResult>`.
Verifies temporal safety and liveness invariants over WPDS call graphs.

> Reference: Vardi & Wolper, "An Automata-Theoretic Approach to Automatic
> Program Verification," 1986.

---

## 18. Automata Composition for First-Order Logic

### Composition Operators

The key achievement of the automata module architecture is that the 15 modules
compose to support the full first-order predicate logic used in guard
specifications. Each logical connective and quantifier maps to a specific
automaton operation, and the composition is sound — the composed automaton
accepts exactly the language defined by the logical formula. The following table
shows the mapping from logical operators to compilation strategies. The left
column lists the surface syntax operators from §2; the right column shows the
automaton operation that implements each:

| Operator                        | Compilation                                       |
|---------------------------------|---------------------------------------------------|
| Conjunction (`,` / `and()`)     | SFA intersection → minimize                       |
| Disjunction (`or()`)            | SFA union → minimize                              |
| Negation (`not()`)              | SFA complement                                    |
| Universal (`forall()`)          | AWA Q⊗ branching: all successors must accept      |
| Existential (`exists()`)        | AWA Q⊕ branching: at least one accepts            |
| Implication (`entails()`)       | Desugar to `not(a), b`, then SFA ops              |
| Recursive (`letprop`)           | Mu-calculus → PATA → Zielonka solver              |
| Data equality (`eq(x, y)`)      | Register automaton TestEq                         |
| Freshness (`fresh(x)`)          | Register automaton TestFresh                      |
| Cardinality (`count_ge(ch, k)`) | Multiset automaton constraint check               |
| Multi-channel                   | Multi-tape product + two-way backward propagation |
| Infinite behavior               | Buchi acceptance condition                        |
| Rewrite closure (`rewrites_to`) | Reflexive-transitive closure via SFA compilation  |
| AC-matching (`ac_match`)        | Multiset partition enumeration via LogicT         |

The propositional connectives (∧, ∨, ¬) use SFA product and complement — these
are closed operations on regular languages. The quantifiers (∀, ∃) require the
richer AWA (alternating weighted automaton) model, where universal quantifiers
produce tensor (⊗) states and existential quantifiers produce direct-sum (⊕)
states. Recursive predicates step up to the mu-calculus and parity tree
automata, which can express fixpoint properties that alternating automata
cannot.

### Formal Definitions

The following equations define the formal semantics of the compilation mapping
from logical formulas to automaton constructs. The notation `⟦·⟧` denotes the
*interpretation function* — the denotational semantics that maps each formula
to its automaton representation. The universal quantifier maps to the
tensor-product state `Q⊗`, which requires *all* successor computations to
accept (the semiring tensor product takes the weight product of all branches).
The existential quantifier maps to the direct-sum state `Q⊕`, which requires
*at least one* successor to accept (the semiring sum takes the weight sum).
Implication desugars to its classical equivalent via `⟦¬φ ∨ ψ⟧`. Recursive
predicates compile to the greatest fixpoint `νX` in the mu-calculus, with the
box modality `□` quantifying over the reduction relation:

```
Universal:   ⟦∀y. φ(y)⟧ = Q⊗    all successors accept; weight = ⊗
Existential: ⟦∃y. φ(y)⟧ = Q⊕    at least one accepts; weight = ⊕
Implication: ⟦φ ⇒ ψ⟧   = ⟦¬φ ∨ ψ⟧
Recursive:   ⟦letprop P x = ∀x'. ¬(x →* x')⟧ = νX. □_{→*}(¬X)
```

The tensor/sum duality (⊗ vs ⊕) mirrors the standard AND/OR duality in
alternating automata theory (Chandra, Kozen & Stockmeyer, 1981). The choice
of greatest fixpoint (νX) for the recursive example reflects that `halt` is
a safety property — it must hold at every step of the computation, which is
the coinductive (greatest fixpoint) characterization.

### End-to-End Trace

To make the module composition concrete, the following trace walks through the
compilation of a real quantified guard: `forall(y, entails(reachable(x, y), safe(y)))`.
This guard says "for all processes `y` reachable from `x`, `y` must be safe."
The trace shows which modules activate, in what order, and what each module
contributes to the final compilation. The key observation is that four modules
participate (M1, M3, M5, M10) out of fifteen — the dispatch controller skips
eleven modules that are irrelevant to this guard's structure:

```
User Predicate: ∀y. (reachable(x, y) ⟹ safe(y))
                 │
                 ▼
  ┌───────────────────────────────┐
  │ M10 (MSO): classify_formula() │
  │ → FirstOrder class            │
  │ → T2 (runtime) or T4 (undec.) │
  └──────────────┬────────────────┘
                 │
    ┌────────────▼────────────┐
    │ Predicate Dispatch Ctrl │
    │ extract_features()      │
    │ → sig: M1+M3+M5+M10     │
    └────────────┬────────────┘
                 │
    ┌────────────▼────────────┐
    │ M1 (SFA): guard algebra │
    │ is_satisfiable()        │──→ SYM01 if dead
    │ overlap with other      │──→ SYM02 if ambiguous
    │ guards on same channel  │
    └────────────┬────────────┘
                 │
    ┌────────────▼────────────┐
    │ M3 (AWA): quantifiers   │
    │ ∀ → Q⊗ branching        │
    │ ⟹ desugars to ¬a ∨ b    │
    │ polynomial transitions  │
    └────────────┬────────────┘
                 │
    ┌────────────▼────────────┐
    │ M5 (PATA): recursive    │
    │ if reachable/safe are   │
    │ defined via letprop     │
    │ → mu-calculus compile   │
    │ → Zielonka emptiness    │
    └────────────┬────────────┘
                 │
    ┌────────────▼────────────┐
    │ Codegen: Ascent join    │
    │ or SFA transition table │
    │ or bounded checker      │
    └─────────────────────────┘
```

The trace illustrates the tier classification's impact on the final code shape:
if `reachable` and `safe` are declared Ascent relations (T2), the codegen
emits an Ascent join clause. If they are defined via `letprop` with unbounded
quantifiers (T4), the codegen emits an `assert_pred()` wrapper and the MSO01
lint warns the user. The M5 (PATA) module only activates when the predicates
involve recursive definitions — for simple Ascent-relation guards, the trace
would skip directly from M3 to codegen.

### Automata Role Matrix

The following matrix lists only automata with guard-related roles in the
predicated types pipeline. Parser/lexer infrastructure (NFA/DFA, FIRST/FOLLOW,
Prediction Weighted Finite-State Transducer (WFST), Decision Tree, ContextWeight, Token Lattice) is omitted —
those are documented in PraTTaIL's architecture docs. Columns cover three
compile-time pipeline phases plus the FOL feature class each automaton handles.
All entries are compile-time only (§14) — zero runtime overhead except where
noted (M7 selectivity → guard order, Forward-Backward → inline/cold attrs).
See the **Matrix Key** below the table for column definitions and cell value
glossaries.

| Automaton        |             Analyze              |       Optimize       |           Codegen            | FOL Feature                                 |
|------------------|:--------------------------------:|:--------------------:|:----------------------------:|---------------------------------------------|
| WPDS             |        Guard reachability        |                      |    Dead rule elimination     | Stack-aware guard evaluation                |
| M1 Symbolic      |         SFA compilation          |                      |     Guard disambiguation     | Propositional predicates, range constraints |
| M2 Buchi         |   Infinite-behavior acceptance   |                      |                              | Liveness (omega-regular quantifiers)        |
| M3 AWA           |    ∀/∃ quantifier evaluation     |                      |                              | First-order quantifiers (⊗/⊕ states)        |
| M4 VPA           |    Scope nesting verification    |                      |                              | Well-formed quantifier nesting              |
| M5 PATA          | Recursive predicate compilation  |                      |                              | Mu-calculus fixpoints (letprop)             |
| M6 Register      | Data equality/freshness analysis |                      |   Dead binder elimination    | Equality (x == y), freshness (fresh(x))     |
| M7 Probabilistic |      Selectivity estimation      |                      | Entropy-based guard ordering | Guard short-circuit performance             |
| M8 Multi-Tape    | Multi-channel guard construction |                      | Independent category codegen | Multi-channel receive guards                |
| M9 Multiset      | Cardinality constraint analysis  |                      |                              | Collection predicates (count(ch) >= k)      |
| M10 MSO          |      Formula classification      |                      |                              | Guard specification language (∧,∨,¬,∀,∃)    |
| M11 Two-Way      |    Cross-channel propagation     |                      |                              | Backward constraint propagation             |
| M12 Presburger   |    Linear arithmetic decision    |                      |                              | Multi-variable integer (Σ aᵢ·xᵢ ≤ b)        |
| M13 Unification  |    Pattern overlap detection     |                      |                              | Structural term unification                 |
| M14 Lattice      | Subtype relationship computation |                      |                              | Type hierarchy constraints (a <: b)         |
| M15 SFT          |   Guard transduction analysis    |                      |  Guard input transformation  | String transforms (case fold, normalize)    |
| E-Graph          |       Equality saturation        |  Predicate simplify  |                              | Algebraic identity discovery                |
| WTA              |   Term classification/ranking    |  Hot-path priority   |                              | Term recognition, set-theoretic subtyping   |
| LTL              |  Temporal property verification  |                      |                              | Safety/liveness (G, F, X, U operators)      |
| CRA              |       Guard cost metering        |  Anomaly detection   |                              | Quantitative evaluation cost                |
| EWPDS            |    Call/return merge analysis    |                      |    Scope instrumentation     | Local variable analysis at boundaries       |
| ARA              |    Affine invariant discovery    |                      |                              | Interprocedural affine relations (x'=ax+b)  |
| Relational WPDS  |    Heap relationship analysis    |                      |                              | Binary relation heap reasoning              |
| Safety           |   Guard completeness checking    |                      |                              | Input coverage (every input matches ≥1)     |
| CEGAR            | Abstraction ladder construction  | Iterative refinement |                              | Boolean→Counting→Tropical abstraction       |
| Algebraic        |   CFG path expression summary    |                      |                              | Guard evaluation control-flow summarization |
| Newton           |      Fixpoint acceleration       | Convergence speedup  |                              | Idempotent semiring convergence (h+1 iters) |
| Forward-Backward |   Hot/cold path classification   |                      |  #[inline] / #[cold] attrs   | Generated function annotation               |

#### Matrix Key

**Column definitions:**

- **Analyze** — Compile-time analysis during `language!` macro expansion.
  Detects issues, classifies guards, computes properties. No runtime cost.
- **Optimize** — Compile-time guard simplification, fusion, or reordering.
  Improves runtime performance of generated guard code.
- **Codegen** — Influences or directly produces generated Rust code that
  appears in the compiled binary.
- **FOL Feature** — The first-order logic feature or guard predicate class
  that this automaton handles.

**Cell value semantics:**

- A filled cell indicates the automaton participates in that pipeline phase.
- The cell text names the specific contribution (defined in the
  corresponding M1–M15 module subsections above).
- An empty cell means the automaton does not participate in that phase.

---

## Part III: Architecture and Implementation

---

## 19. Lint Integration

The predicated types pipeline produces diagnostics at every stage:

### Parse-Stage Lints

| Lint  | Trigger                                    |
|-------|--------------------------------------------|
| SYM01 | Guard is unsatisfiable (⊥) — dead receive  |
| SYM02 | Two guards on same channel overlap         |
| SYM03 | Guard A subsumes Guard B (redundant check) |
| SYM04 | SFA has mergeable states (non-minimal)     |

### Classification-Stage Lints

| Lint  | Trigger                                             |
|-------|-----------------------------------------------------|
| MSO01 | Formula uses `∀X` (not recognizable — T3/T4)        |
| MSO02 | `∀x. φ` where φ is not a recognizable step function |
| MSO03 | Two guard formulas have identical semantics         |

### Compilation-Stage Lints

| Lint | Trigger                                  |
|------|------------------------------------------|
| PT01 | Predicate unsatisfiable (PATA emptiness) |
| PT02 | Predicate A subsumes B (redundant)       |
| PT03 | Priority depth > 4 (exponential blowup)  |

### Codegen-Stage Lints

| Lint | Trigger                                |
|------|----------------------------------------|
| RA01 | Data value referenced but never stored |
| RA02 | Register written but never tested      |
| RA03 | Register tested but never stored       |

### Multi-Channel Lints

| Lint | Trigger                                     |
|------|---------------------------------------------|
| MT01 | Two tapes constrained to identical patterns |
| MT02 | Tape has no auto-intersection constraints   |
| TW01 | Circular channel dependency (deadlock risk) |
| TW03 | Backward constraint propagation divergent   |

### Selectivity Lints

| Lint | Trigger                              |
|------|--------------------------------------|
| PR01 | Rule handles < 1% of expected inputs |

### Constraint Theory Lints

| Lint | Trigger                                           |
|------|---------------------------------------------------|
| PB01 | Presburger constraint is tautological             |
| PB02 | Presburger constraint is unsatisfiable            |
| PB03 | Presburger guard subsumes another                 |
| UN01 | Unification produces infinite type (occurs check) |
| UN02 | Constructor clash in pattern overlap              |
| UN03 | Unification subsumption detected                  |
| SL01 | Subtype cycle detected (type equivalence)         |
| SL02 | Incomplete type hierarchy (missing join)          |
| LT01 | LogicT search bound exceeded                      |

---

## 20. Pluggable Type System Framework

**Problem:** For truly predicated types (types depending on values), the
system needs refinement types: `{ x: Int | x > 0 }` — types that combine
base type subtyping with predicate constraints on values. More broadly, the
system needs a pluggable type system framework so that arbitrary type
disciplines (Rholang structural, MeTTa gradual, refinement, Hindley-Milner (HM), dependent,
set-theoretic) can integrate into the PraTTaIL pipeline.

**Design:** A `TypeSystem` trait analogous to `ConstraintTheory` — languages
implement this trait to get pipeline integration (lints, SFA analysis,
codegen) for free. Three implementations planned:

1. **`LatticeTypeSystem`** — wraps existing `LatticeTheory` into the trait
   (finite subtype lattice, simplest reference implementation)
2. **`RefinementTypeSystem<S, T>`** — composes a base `TypeSystem S` with
   a `ConstraintTheory T` to form `{ x: S::Type | T::Constraint }` types
3. **`SetTheoreticTypeSystem`** — CDuce/XDuce-style types modeled as
   regular tree languages via `WeightedTreeAutomaton<BooleanWeight>`, with
   union/intersection/negation types and subtyping as language inclusion

### Architecture

The type system framework mirrors the two-layer architecture of the constraint
theory suite (§16): a trait defines the interface, concrete implementations
provide domain-specific logic, and a bridge adapter connects to the
`BooleanAlgebra`/SFA infrastructure. The key insight is that type system
operations — checking, inference, subtyping, join, meet — have the same
algebraic structure as constraint operations: a lattice with decidable
ordering. This parallelism is not accidental: a type system *is* a constraint
system where the constraints are type judgments and the store is the type
environment. The three implementations span a spectrum from simple (finite
lattice) to expressive (refinement types composing base types with constraint
predicates) to powerful (set-theoretic types modeled as tree automata
languages).

The diagram below shows the trait, its three implementations, and the pipeline
integration point where all three converge:

```
       ┌──────────────────────────────────────────────────┐
       │             TypeSystem Trait                     │
       │                                                  │
       │  check(env, term, type) → bool                   │
       │  infer(env, term) → Vec<Type>                    │
       │  is_subtype(env, sub, sup) → bool                │
       │  join(env, a, b) → (Type | ⊥)                     │
       │  meet(env, a, b) → (Type | ⊥)                     │
       │  extend(env, var, type) → TypeEnv                │
       │  is_inhabited(env, type) → bool                  │
       │  top() → (Type | ⊥)                              │
       │  bottom() → (Type | ⊥)                           │
       └────────────────────────┬─────────────────────────┘
                                │
              ┌─────────────────┼──────────────────────┐
              │                 │                      │
    ┌─────────▼──────┐  ┌───────▼────────┐  ┌──────────▼──────────┐
    │ LatticeType    │  │ Refinement     │  │ SetTheoreticType    │
    │ System         │  │ TypeSystem<S,T>│  │ System              │
    │                │  │                │  │                     │
    │ Wraps          │  │ ProductAlgebra │  │ Tree automata       │
    │ LatticeTheory  │  │ <LatticeType,  │  │ Types = states      │
    │                │  │  TheoryAlg<T>> │  │ Subtype = inclusion │
    │ Finite subtype │  │                │  │ ∪/∩/¬ types         │
    │ lattice        │  │ { x:T | P(x) } │  │                     │
    └─────────┬──────┘  └───────┬────────┘  └──────────┬──────────┘
              │                 │                      │
              └─────────────────┼──────────────────────┘
                                │
              ┌─────────────────▼──────────────────┐
              │    Pipeline Integration            │
              │                                    │
              │  TypeSystemAnalysis (compile-time) │
              │  Lints: RT01–RT06                  │
              │  Codegen: runtime type checks      │
              └────────────────────────────────────┘
```

The `RefinementTypeSystem<S, T>` (center column) is the most architecturally
interesting: it uses `ProductAlgebra<LatticeType, TheoryAlgebra<T>>` to compose
base-type subtyping with constraint-predicate entailment, enabling the
subtyping rule `{x: S | P(x)} <: {x: T | Q(x)}` to decompose into two
independent checks — `S <: T` via the base type system and `∀x. P(x) ⟹ Q(x)`
via the constraint theory (see Refinement Types below).

**Typed predicates and the refinement type bridge.** When a language declares
typed predicates in `guards {}` (§2A), the pipeline can
identify cases where a guard predicate structurally matches the refinement
predicate of the channel's type — e.g., `gt(val, 0)` on a channel typed
`{ x: Int | x > 0 }`. In such cases, `RefinementTypeSystem::predicate_entails()`
proves the guard is subsumed by the type, enabling T1 static elimination at
zero runtime cost. See §14A (Refinement Type Bridge Diagram) for the
complete data flow.

### TypeSystem Trait

The `TypeSystem` trait is the extension point for plugging type disciplines
into the pipeline. Its design parallels the `ConstraintTheory` trait (§16) but
operates at a higher abstraction level: where `ConstraintTheory` works with
constraints and stores, `TypeSystem` works with types and type environments.
The nine methods capture the fundamental operations of bidirectional type
checking (Pierce & Turner, 2000): `check` implements the checking direction (does this
term have this type?), `infer` implements the inference direction (what types
can this term have?), and `is_subtype`/`join`/`meet` implement the lattice
operations on the type space. The `is_inhabited` method connects to the
predicated types system: a refinement type `{x: T | P(x)}` is inhabited if
and only if `T` is inhabited AND `P` is satisfiable, so the type system must
be able to answer inhabitedness queries to support the RT01 lint.

```rust
pub trait TypeSystem: Clone + fmt::Debug + Send + Sync + 'static {
    type Type: Clone + fmt::Debug + Eq + Hash + Send + Sync + 'static;
    type TypeEnv: Clone + fmt::Debug + Send + Sync + 'static;
    type Term: Clone + fmt::Debug + Send + Sync + 'static;

    fn empty_env(&self) -> Self::TypeEnv;
    fn check(&self, env: &Self::TypeEnv, term: &Self::Term, ty: &Self::Type) -> bool;
    fn infer(&self, env: &Self::TypeEnv, term: &Self::Term) -> Vec<Self::Type>;
    fn is_subtype(&self, env: &Self::TypeEnv, sub: &Self::Type, sup: &Self::Type) -> bool;
    fn join(&self, env: &Self::TypeEnv, a: &Self::Type, b: &Self::Type) -> Option<Self::Type>;
    fn meet(&self, env: &Self::TypeEnv, a: &Self::Type, b: &Self::Type) -> Option<Self::Type>;
    fn extend(&self, env: &Self::TypeEnv, var: &str, ty: &Self::Type) -> Self::TypeEnv;
    fn is_inhabited(&self, env: &Self::TypeEnv, ty: &Self::Type) -> bool { true }
    fn top(&self) -> Option<Self::Type> { None }
    fn bottom(&self) -> Option<Self::Type> { None }
}
```

The `infer` method returns `Vec<Self::Type>` rather than `Option<Self::Type>`
to support type systems with principal type pairs or multiple valid typings
(e.g., MeTTa's gradual typing where a term may have several incomparable
types). The `top()` and `bottom()` methods return `Option` because not all type
systems have a universal supertype or an empty bottom type — `LatticeTypeSystem`
does (if the lattice has them), but `RefinementTypeSystem` may not. Default
implementations return `None` and `true` respectively, minimizing the
implementation burden for simple type systems.

### TypeSystemAlgebra Bridge

`TypeSystemAlgebra<S>` bridges `TypeSystem` to `BooleanAlgebra`, analogous
to `TheoryAlgebra<T>` for `ConstraintTheory`. This enables SFA-based
analysis of type predicates: satisfiability (`is_inhabited`), subsumption
(`is_subtype`), and overlap (intersection non-emptiness) all reduce to
BooleanAlgebra operations.

### Refinement Types

A refined type `{ x: T | P(x) }` combines:
- A **base type** `T` from a `TypeSystem S` (e.g., `Int` from `LatticeTypeSystem`)
- A **predicate** `P` from a `ConstraintTheory T` (e.g., `x > 0` from Presburger)

The subtyping rule for refinement types decomposes into two independent checks,
reflecting the product structure of `RefinementTypeSystem<S, T>`. The base type
check uses the underlying `TypeSystem S`'s `is_subtype()`, while the predicate
entailment check uses the `ConstraintTheory T`'s `is_satisfiable()` to test
whether `P(x) ∧ ¬Q(x)` is unsatisfiable (i.e., every `x` satisfying `P` also
satisfies `Q`). This decomposition is sound because the refinement type's
denotation is the intersection of the base type's denotation with the
predicate's satisfying set:

```
{ x: S | P(x) } <: { x: T | Q(x) }
  iff  S <: T   (base subtype via TypeSystem)
  AND  ∀x. P(x) ⟹ Q(x)  (predicate entailment via ConstraintTheory)
```

The entailment check `∀x. P(x) ⟹ Q(x)` reduces to `¬∃x. P(x) ∧ ¬Q(x)` via
the standard logical equivalence, which is tested by
`!algebra.is_satisfiable(algebra.and(P, algebra.not(Q)))` — reusing the
existing `BooleanAlgebra` infrastructure from §15.

Inhabitedness: `{ x: T | P(x) }` is inhabited iff `T` is inhabited AND
`P` is satisfiable (checked via `TheoryAlgebra::is_satisfiable()`).

### Set-Theoretic Types

CDuce/XDuce-style types where types are sets of values:
- **Union**: `S ∪ T` — values in S or T (or both)
- **Intersection**: `S ∩ T` — values in both S and T
- **Negation**: `¬S` — values not in S
- **Subtype**: `S <: T` iff `L(A_S) ⊆ L(A_T)` iff `L(A_S ∩ ¬A_T) = ∅`

Modeled as regular tree languages via `WeightedTreeAutomaton<BooleanWeight>`:
states = types, transitions = constructor rules, subtyping = language
inclusion (decidable via intersection + complement + emptiness).

### Surface Syntax

Refinement types are declared inline in the `types { ... }` block of the
`language!` macro, using a syntax inspired by Liquid Types (Rondon, Kawaguchi &
Jhala, PLDI 2008). The `{ variable: BaseType | predicate }` syntax makes the
refinement's three components explicit: the bound variable, the base type, and
the constraining predicate. The predicate sublanguage is the same `where`-clause
predicate language from §2 — the same `not()`, `and()`, `or()`, `forall()`,
`exists()` forms, parsed by the same Pratt parser, classified by the same
decidability
tiering (§11). This reuse ensures that refinement predicates benefit from the
full compilation pipeline: a `PosInt` predicate compiles to a T1 static check,
while a `SafeProc` predicate compiles to a T2 or T3 bounded check.

```rust
types {
    Proc { ... }
    Name { ... }
    Int:i64 { ... }
    PosInt = { x: Int | x > 0 };
    SafeProc = { p: Proc | forall(y, nodes, entails(reachable(p, y), safe(y))) };
    NonEmpty = { b: HashBag(Proc) | count(b) >= 1 };
}
```

The three examples illustrate different constraint domains: `PosInt` uses
Presburger arithmetic (`x > 0`), `SafeProc` uses a quantified behavioral
predicate (classified as T2 if `reachable`/`safe` are Ascent relations, T4
otherwise), and `NonEmpty` uses a cardinality predicate (`count(b) >= 1`)
handled by the multiset module M9.

Refinement predicates support:
- **Linear arithmetic**: `a₁*x₁ + a₂*x₂ + ... ⊕ c` (Presburger)
- **Relation queries**: `R(args)` (behavioral)
- **Quantified formulas**: `forall()`/`exists()` with optional domain and bound
- **Logical connectives**: `not()`, `and()`, `or()`, `entails()`
- **Term comparison**: `==`, `!=`

When a guard references a refinement type by name, the pipeline generates a
conjunction of the structural match (from the base type) and the refinement
predicate check. The generated code first pattern-matches the received value
against the base type's structure, then evaluates the refinement predicate on
the matched bindings:

```rholang
for (@x <- ch) where x ∈ PosInt { P }
// Equivalent: where x in PosInt / where x : PosInt / where PosInt(x)
```

This desugars to `for (@x <- ch) { if is_refined_PosInt(x) { P } }` — the
structural match extracts `x`, and the Ascent relation `is_refined_PosInt`
confirms that `x > 0`.

### Predicate Lowering

Each `RefinementPredicate` is classified into a `ConstraintDomain`:
- **Presburger** — pure linear arithmetic → Presburger NFA
- **Lattice** — pure subtype checks → LatticeTheory
- **Behavioral** — relation queries / quantifiers → LogicT evaluation
- **Unification** — structural term patterns → Martelli-Montanari
- **Product** — mixed domain → ProductAlgebra composition

The classified predicate is lowered to the appropriate `ConstraintTheory`
representation for compile-time analysis and runtime codegen.

### Pipeline Integration

`analyze_from_bundle()` extended with refinement type analysis:
1. Build `LatticeTypeSystem` from categories in `LanguageSpec::types`
2. For each refinement type, classify predicate domain
3. Check inhabitedness (RT01), tautology (RT02), pairwise intersection (RT03),
   pairwise subtyping (RT04), decidability tier (RT05), name shadowing (RT06)
4. Use `TypeSystemAlgebra<S>` for SFA-based dispatch analysis when multiple
   refinement types refine the same base type

### Lints

| Code | Severity | Description                                                          |
|------|----------|----------------------------------------------------------------------|
| RT01 | Warning  | Refinement predicate is unsatisfiable: `{ x: Int \| x > 0 ∧ x < 0 }` |
| RT02 | Note     | Refinement equivalent to base type: `{ x: Int \| true }`             |
| RT03 | Warning  | Refinement types have empty intersection                             |
| RT04 | Note     | Refinement subtype detected: `StrictPosInt <: PosInt`                |
| RT05 | Note     | Predicate decidability tier classification (T1–T4)                   |
| RT06 | Warning  | Refinement type shadows base type (same name)                        |

### Codegen

The codegen layer generates Ascent relations and population rules for each
refinement type. The generated code has two parts: a relation declaration
(`is_refined_TypeName`) that stores all values satisfying the refinement, and a
population rule that checks base-type membership and predicate satisfaction.
The population rule runs during Ascent's fixpoint evaluation (§6), so
refinement membership is automatically maintained as the fixpoint evolves — new
values entering the base-type relation are checked against the predicate and
added to the refinement relation if they satisfy it.

For simple Presburger predicates, the predicate is inlined as an Ascent `if`
guard:

```rust
// Ascent relation for refinement membership
relation is_refined_PosInt(Int);

// Population rule: base type membership + predicate check
is_refined_PosInt(x) <--
    int(x),         // base type (already exists)
    if *x > 0;      // predicate (inline for simple Presburger)
```

For behavioral predicates involving quantifiers, the predicate evaluation is
delegated to `evaluate_quantified()` (§8), which uses LogicT's fair
backtracking to evaluate `∀`/`∃` formulas:

```rust
is_refined_SafeProc(p) <--
    proc(p),
    if { evaluate_quantified(&formula, &lookup) };
```

The runtime cost depends on the predicate's decidability tier: T1 predicates
are constant-folded away (the `if` guard is always true or the rule is
eliminated), T2 predicates incur O(|value|) per population rule firing, and T3
predicates incur O(k · |value|) with the user-specified bound `k`.

### References

- Rondon, P., Kawaguchi, M., & Jhala, R. (2008). "Liquid Types." PLDI 2008.
- Freeman, T. & Pfenning, F. (1991). "Refinement Types for ML." PLDI 1991.
- Frisch, A., Castagna, G., & Benzaken, V. (2008). "Semantic subtyping."
  JACM 55(4).
- Xi, H. & Pfenning, F. (1999). "Dependent Types in Practical Programming."
  POPL 1999.
- Pierce, B. C. (2002). "Types and Programming Languages." MIT Press.
- Comon, H. et al. (2007). "Tree Automata Techniques and Applications."
  (TATA).

### Future Feature: Hindley-Milner Type Inference

The `TypeSystem` trait is designed to accommodate Hindley-Milner (HM) type
inference as a pluggable implementation. HM is the standard type discipline
for ML-family languages (OCaml, Haskell, SML) and provides **principal type**
inference: every well-typed expression has a most general type that can be
inferred without annotations.

**Use cases for HM within predicated types:**

1. **ML-family target languages** — If a `language!` definition targets an
   ML-like syntax (e.g., a MeTTa subset with let-polymorphism), the type
   system framework should be able to infer and check types using HM rules
   rather than the lattice/refinement/set-theoretic disciplines.

2. **Polymorphic guard typing** — Guards in `Comm` rules could benefit from
   HM inference to type-check polymorphic helper functions used within
   behavioral predicates. For example, a guard `map(f, xs)` where `f` is
   polymorphic benefits from principal type inference.

3. **Type-directed disambiguation** — HM's principal types can resolve
   syntactic ambiguities when multiple parse trees are type-correct.
   Integrating HM with `TypeSystemAlgebra` would allow SFA-based dispatch
   to use inferred types as disambiguation predicates.

4. **Cross-language interop** — When MeTTaIL compiles to or interoperates
   with ML-typed backends, an HM implementation validates type compatibility
   at compile time through the same `TypeSystem` trait interface.

**Implementation sketch:**

```rust
/// Hindley-Milner type system with let-polymorphism.
/// Feature gate: hm-type-system = ["type-system", "unification"]
pub struct HindleyMilnerTypeSystem {
    /// Type constructors: Int, Bool, List, →, ×, etc.
    constructors: Vec<TypeConstructor>,
    /// Known type class instances (for constrained polymorphism).
    instances: Vec<Instance>,
}

/// Monotypes: no quantifiers.
enum MonoType {
    Var(TypeVar),                         // α
    Con(String),                          // Int, Bool
    App(String, Vec<MonoType>),           // List(α), α → β
}

/// Polytypes (type schemes): ∀-quantified monotypes.
struct PolyType {
    bound: Vec<TypeVar>,                  // ∀α₁ ... αₙ
    body: MonoType,                       //  . τ
}
```

Key operations via the `TypeSystem` trait:
- `infer(Γ, e) → Vec<MonoType>` — Algorithm W/J, returns singleton (principal type)
- `check(Γ, e, τ) → bool` — infer + unify
- `is_subtype(Γ, σ, τ) → bool` — instantiation check (σ ⊑ τ iff σ is more general)
- `join(Γ, τ₁, τ₂)` — anti-unification (least general generalization)
- `meet(Γ, τ₁, τ₂)` — unification (most general unifier)

**Infrastructure already available:**

| Component              | Location         | Reuse                                |
|------------------------|------------------|--------------------------------------|
| `TypeSystem` trait     | `type_system.rs` | Direct implementation                |
| `UnificationTheory`    | `unification.rs` | Martelli-Montanari with occurs check |
| `TypeSystemAlgebra<S>` | `type_system.rs` | SFA bridge for dispatch              |
| `ConstraintTheory`     | `logict.rs`      | Constraint-based type inference      |

**References:**
- Damas, L. & Milner, R. (1982). "Principal type-schemes for functional
  programs." POPL 1982.
- Milner, R. (1978). "A Theory of Type Polymorphism in Programming." JCSS 17.
- Heeren, B., Hage, J., & Swierstra, S. D. (2002). "Generalizing
  Hindley-Milner Type Inference Algorithms." Technical Report UU-CS-2002-031.

---

## 21. Implementation Architecture

### Tokens Feature Benefits

The `tokens { ... }` block provides:

1. Custom guard tokens (`where`, `not`, `and`, `or`, `forall`, `exists`,
   `entails`, `implies`, `implied_by`, `iff` and their Unicode alternatives)
   via `TokenKind::Custom` with regex patterns and priority
2. Modal lexing (WPDS modes) for predicate keyword recognition inside
   `where` clauses
3. FIRST set augmentation for guard token disambiguation
4. VPA delimiter verification for guard scope nesting
5. Tree automata validation for guard expression structure
6. Multi-tape synchronization for multi-channel guard evaluation
7. Fragment composition via `merge_token_defs()` for clean base languages

### Guards Feature Benefits

The `guards { ... }` block (§2A) complements `tokens {}` with semantic
configuration:

1. **`connectives {}`** — maps logical connective roles (and, or, not,
   forall, exists, entails, implied_by, iff) to language-specific keyword
   spellings; restricts the available connective set per language
2. **predicates (direct items)** — declares built-in predicates with syntax
   templates (fixity, n-ary, type overloads) using the same `terms {}` pattern
   syntax; establishes the resolution order for guard predicate names
3. **`theories {}`** — registers `ConstraintTheory` implementations with
   `for [...]` type category clauses; enables type-driven
   `PredicateSignature` module activation, theory-guided domain pruning in
   LogicT (§14A), TriState refinement, and refinement type bridge
   optimization
4. **`channels {}`** — declares which categories are communication
   channels and which term constructors are join patterns; enables
   deterministic M8 (multi-tape) and M11 (two-way transducer) activation
   for multi-channel guard dispatch, replacing heuristic inference
5. **Token references** — syntax templates accept token names from
   `tokens {}` (e.g., `Gt` instead of `">"`) to inherit priority, modal
   lexing, and stream routing properties; `TOK01` lint warns on unmatched
   string literals

---

## 23. Cross-References and References

### Cross-References

**Guard configuration (§2A, §14A):**
- **§2A Language-Generic Guard Configuration:** `guards {}` block syntax,
  connective mappings, predicate syntax templates, theory registrations,
  channel declarations, token references, composition semantics, AST
  representation
- **§14A LogicT Theory Integration:** Theory-guided evaluation pipeline,
  TriState refinement, refinement type bridge, worked examples
- **Guard config AST types:** [language.rs](../../macros/src/ast/language.rs) (`GuardConfig`,
  `ConnectiveDecl`, `BuiltinPredicate`, `PredicateAnnotations`,
  `TheoryRegistration`, `ChannelConfig`, `ChannelDecl`, `JoinPatternDecl`,
  `ChannelParam`); `prattail` spec types: `GuardConfigSpec`,
  `TheoryRegistrationSpec`, `ConnectiveMap`
- **Guard config parser:** [language.rs](../../macros/src/ast/language.rs) (`parse_guards()`)
- **Guard config merge:** [merge.rs](../../macros/src/ast/merge.rs) (`merge_guard_config()`)
- **Channel dispatch:** `channels {}` sub-block for deterministic M8/M11
  activation; see §2A "Channel Declarations for Multi-Channel Guard Dispatch"

**Core infrastructure:**
- **Analysis pipeline overview:** [analysis-pipeline-overview.md](../../prattail/docs/design/analysis-pipeline-overview.md)
- **Lint layer:** [lint-layer.md](../../prattail/docs/design/lint-layer.md)
- **Predicate dispatch automaton:** [predicate-dispatch-automaton.md](../../prattail/docs/design/predicate-dispatch-automaton.md)
- **Composed dispatch:** [composed-dispatch.md](../../prattail/docs/design/composed-dispatch.md)
- **Semiring catalog:** [semiring-catalog.md](../../prattail/docs/design/semiring-catalog.md)
- **Diagnostics reference:** [README.md](../../prattail/docs/diagnostics/README.md)
- **Error recovery:** [error-recovery.md](../../prattail/docs/design/wfst/error-recovery.md)
- **Mathematical analyses:** [mathematical-analyses.md](mathematical-analyses.md)

**Automata modules (M1–M11):**
- **M1 Symbolic automata:** [symbolic-automata.md](../../prattail/docs/design/symbolic-automata.md)
- **M2 Weighted Büchi:** [weighted-buchi.md](../../prattail/docs/design/weighted-buchi.md)
- **M3 Polynomial AWA:** [polynomial-awa.md](../../prattail/docs/design/polynomial-awa.md)
- **M4 Weighted VPA:** [weighted-vpa.md](../../prattail/docs/design/weighted-vpa.md)
- **M5 Parity tree automata:** [parity-tree-automata.md](../../prattail/docs/design/parity-tree-automata.md)
- **M6 Register automata:** [register-automata.md](../../prattail/docs/design/register-automata.md)
- **M7 Probabilistic automata:** [probabilistic-automata.md](../../prattail/docs/design/probabilistic-automata.md)
- **M8 Multi-tape automata:** [multi-tape-automata.md](../../prattail/docs/design/multi-tape-automata.md)
- **M9 Multiset automata:** [multiset-automata.md](../../prattail/docs/design/multiset-automata.md)
- **M10 Weighted MSO:** [weighted-mso.md](../../prattail/docs/design/weighted-mso.md)
- **M11 Two-way transducer:** [two-way-transducer.md](../../prattail/docs/design/two-way-transducer.md)
- **Advanced automata overview:** [advanced-automata-overview.md](../../prattail/docs/design/advanced-automata-overview.md)

**Extended analyses (M15+):**
- **M15 Symbolic finite transducer:** [symbolic-finite-transducer.md](../../prattail/docs/design/symbolic-finite-transducer.md)
- **E-graph equality saturation:** [egraph-equality-saturation.md](../../prattail/docs/design/egraph-equality-saturation.md)

**Type system and constraints:**
- **Type system framework design:** [type-system-framework.md](../../prattail/docs/design/type-system-framework.md) (§20)
- **Constraint theory design docs:** [constraint-theories](../../prattail/docs/design/constraint-theories)
- **Constraint theory diagnostics:** [presburger](../../prattail/docs/diagnostics/presburger), [unification](../../prattail/docs/diagnostics/unification), [subtype-lattice](../../prattail/docs/diagnostics/subtype-lattice), [logict](../../prattail/docs/diagnostics/logict)
- **Refinement type diagnostics:** [refinement](../../prattail/docs/diagnostics/refinement) (RT01–RT06)

### References

1. Baader, F. & Snyder, W. ["Unification Theory."](https://www.cs.bu.edu/fac/snyder/publications/UnifChapter.pdf) In *Handbook of Automated
   Reasoning*, vol. 1, ch. 8, pp. 445–533. Elsevier, 2001.
   DOI: [10.1016/B978-044450813-3/50011-0](https://doi.org/10.1016/B978-044450813-3/50011-0)

2. Berry, G. & Boudol, G. ["The Chemical Abstract Machine."](https://www.lix.polytechnique.fr/~fvalenci/papers/cham.pdf) *Theoretical
   Computer Science*, 96(1):217–248, 1992.
   DOI: [10.1016/0304-3975(92)90185-I](https://doi.org/10.1016/0304-3975(92)90185-I)

3. Biere, A., Cimatti, A., Clarke, E., & Zhu, Y. ["Symbolic Model Checking
   without BDDs."](https://fmv.jku.at/papers/BiereCimattiClarkeZhu-TACAS99.pdf) *Proceedings of TACAS*, LNCS 1579, pp. 193–207. Springer,
   1999.
   DOI: [10.1007/3-540-49059-0_14](https://doi.org/10.1007/3-540-49059-0_14)

4. Birkhoff, G. [*Lattice Theory*](https://archive.org/details/in.ernet.dli.2015.166886). AMS Colloquium Publications, vol. 25, 1940.

5. Büchi, J. R. ["Weak second-order arithmetic and finite automata."](https://deepblue.lib.umich.edu/handle/2027.42/3930)
   *Zeitschrift für mathematische Logik und Grundlagen der Mathematik*,
   6:66–92, 1960.
   DOI: [10.1002/malq.19600060105](https://doi.org/10.1002/malq.19600060105)

6. Ceri, S., Gottlob, G., & Tanca, L. [*Logic Programming and Databases*](https://doi.org/10.1007/978-3-642-83952-8).
   Springer, 1990.
   DOI: [10.1007/978-3-642-83952-8](https://doi.org/10.1007/978-3-642-83952-8)

7. Chandra, A. K., Kozen, D. C., & Stockmeyer, L. J. ["Alternation."](https://doi.org/10.1145/322234.322243)
   *Journal of the ACM*, 28(1):114–133, 1981.
   DOI: [10.1145/322234.322243](https://doi.org/10.1145/322234.322243)

8. Comon, H. et al. ["Tree Automata Techniques and Applications."](http://tata.gforge.inria.fr/) (TATA),
   2007. Available at: [tata.gforge.inria.fr](http://tata.gforge.inria.fr/)

9. D'Antoni, L. & Veanes, M. ["Minimization of Symbolic Automata."](https://cseweb.ucsd.edu/~ldantoni/papers/popl14.pdf)
   *Proceedings of POPL*, pp. 541–553. ACM, 2014.
   DOI: [10.1145/2535838.2535849](https://doi.org/10.1145/2535838.2535849)

10. Damas, L. & Milner, R. ["Principal Type-Schemes for Functional Programs."](https://courses.cs.washington.edu/courses/cse503/10wi/readings/p207-damas.pdf)
    *Proceedings of POPL*, pp. 207–212. ACM, 1982.
    DOI: [10.1145/582153.582176](https://doi.org/10.1145/582153.582176)

11. Davey, B. A. & Priestley, H. A. [*Introduction to Lattices and Order*](https://doi.org/10.1017/CBO9780511809088).
    2nd ed. Cambridge University Press, 2002.
    DOI: [10.1017/CBO9780511809088](https://doi.org/10.1017/CBO9780511809088)

12. de Bruijn, N. G. ["Lambda Calculus Notation with Nameless Dummies."](https://lawrencecpaulson.github.io/papers/deBruijn-nameless-dummies.pdf)
    *Indagationes Mathematicae*, 75(5):381–392, 1972.
    DOI: [10.1016/1385-7258(72)90034-0](https://doi.org/10.1016/1385-7258(72)90034-0)

13. Droste, M. & Gastin, P. ["Weighted Automata and Weighted Logics."](https://www.informatik.uni-leipzig.de/~droste/papers/Droste-Gastin-weighted-logic-TCS.pdf)
    *Theoretical Computer Science*, 380:69–86, 2007.
    DOI: [10.1016/j.tcs.2007.02.055](https://doi.org/10.1016/j.tcs.2007.02.055)

14. Emerson, E. A. & Jutla, C. S. ["Tree Automata, Mu-Calculus and
    Determinacy."](https://doi.org/10.1109/SFCS.1991.185392) *Proceedings of FOCS*, pp. 368–377. IEEE, 1991.
    DOI: [10.1109/SFCS.1991.185392](https://doi.org/10.1109/SFCS.1991.185392)

15. Feng, B. & Maletti, A. ["Weighted Two-Way Transducers."](https://doi.org/10.1007/978-3-031-19685-0_8)
    *Proceedings of CAI*. LNCS, Springer, 2022.
    DOI: [10.1007/978-3-031-19685-0_8](https://doi.org/10.1007/978-3-031-19685-0_8)

16. Freeman, T. & Pfenning, F. ["Refinement Types for ML."](https://www.cs.cmu.edu/~fp/papers/pldi91.pdf) *Proceedings of
    PLDI*, pp. 268–277. ACM, 1991.
    DOI: [10.1145/113445.113468](https://doi.org/10.1145/113445.113468)

17. Frisch, A., Castagna, G., & Benzaken, V. ["Semantic subtyping: Dealing
    set-theoretically with function, union, intersection, and negation
    types."](https://www.irif.fr/~gc/papers/semantic_subtyping.pdf) *Journal of the ACM*, 55(4):1–64, 2008.
    DOI: [10.1145/1391289.1391293](https://doi.org/10.1145/1391289.1391293)

18. Heeren, B., Hage, J., & Swierstra, S. D. ["Generalizing Hindley-Milner
    Type Inference Algorithms."](https://www.cs.uu.nl/research/techreps/repo/CS-2002/2002-031.pdf) Technical Report UU-CS-2002-031, Utrecht
    University, 2002.

19. Hemann, J. & Friedman, D. P. ["μKanren: A Minimal Functional Core for
    Relational Programming."](http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf) *Scheme Workshop*, 2013.

20. Hopcroft, J. E. ["An n log n Algorithm for Minimizing States in a Finite
    Automaton."](http://i.stanford.edu/pub/cstr/reports/cs/tr/71/190/CS-TR-71-190.pdf) In *Theory of Machines and Computations*, pp. 189–196.
    Academic Press, 1971.

21. Kaminski, M. & Francez, N. ["Finite-Memory Automata."](https://doi.org/10.1016/0304-3975(94)90242-9) *Theoretical
    Computer Science*, 134(2):329–363, 1994.
    DOI: [10.1016/0304-3975(94)90242-9](https://doi.org/10.1016/0304-3975(94)90242-9)

22. Kempe, A. ["Weighted Multi-Tape Automata and Transducers for Natural
    Language Processing (NLP)."](https://arxiv.org/abs/cs/0406003) 2004.

23. Kiselyov, O., Shan, C., Friedman, D. P. & Sabry, A. ["Backtracking,
    Interleaving, and Terminating Monad Transformers."](https://okmij.org/ftp/Computation/LogicT.pdf) *Proceedings of ICFP*,
    pp. 192–203. ACM, 2005.
    DOI: [10.1145/1086365.1086390](https://doi.org/10.1145/1086365.1086390)

24. Kostolanyi, A. & Misun, F. ["Alternating Weighted Automata over
    Commutative Semirings."](https://doi.org/10.1016/j.tcs.2018.05.009) *Theoretical Computer Science*, 740:1–27, 2018.
    DOI: [10.1016/j.tcs.2018.05.009](https://doi.org/10.1016/j.tcs.2018.05.009)

25. Martelli, A. & Montanari, U. ["An Efficient Unification Algorithm."](http://moscova.inria.fr/~levy/courses/X/IF/03/pi/levy2/martelli-montanari.pdf)
    *ACM Transactions on Programming Languages and Systems*, 4(2):258–282,
    1982.
    DOI: [10.1145/357162.357169](https://doi.org/10.1145/357162.357169)

26. Meredith, L. G. & Radestock, M. ["A Reflective Higher-Order Calculus."](https://www.sciencedirect.com/science/article/pii/S1571066105051893)
    *Electronic Notes in Theoretical Computer Science*, 141(5):49–67, 2005.
    DOI: [10.1016/j.entcs.2005.05.016](https://doi.org/10.1016/j.entcs.2005.05.016)

27. Milner, R. ["A Theory of Type Polymorphism in Programming."](https://homepages.inf.ed.ac.uk/wadler/papers/papers-we-love/milner-type-polymorphism.pdf) *Journal of
    Computer and System Sciences*, 17(3):348–375, 1978.
    DOI: [10.1016/0022-0000(78)90014-4](https://doi.org/10.1016/0022-0000(78)90014-4)

28. Pierce, B. C. [*Types and Programming Languages*](https://mitpress.mit.edu/9780262162098/types-and-programming-languages/). MIT Press, 2002.

29. Pierce, B. C. & Turner, D. N. ["Local Type Inference."](https://www.cis.upenn.edu/~bcpierce/papers/lti-toplas.pdf) *ACM Transactions
    on Programming Languages and Systems*, 22(1):1–44, 2000.
    DOI: [10.1145/345099.345100](https://doi.org/10.1145/345099.345100)

30. Robinson, J. A. ["A Machine-Oriented Logic Based on the Resolution
    Principle."](https://doi.org/10.1145/321250.321253) *Journal of the ACM*, 12(1):23–41, 1965.
    DOI: [10.1145/321250.321253](https://doi.org/10.1145/321250.321253)

31. Rondon, P., Kawaguchi, M., & Jhala, R. ["Liquid Types."](https://goto.ucsd.edu/~rjhala/liquid/liquid_types.pdf) *Proceedings of
    PLDI*, pp. 159–169. ACM, 2008.
    DOI: [10.1145/1375581.1375602](https://doi.org/10.1145/1375581.1375602)

32. Van Gelder, A., Ross, K. A., & Schlipf, J. S. ["The Well-Founded
    Semantics for General Logic Programs."](https://doi.org/10.1145/116825.116838) *Journal of the ACM*,
    38(3):620–650, 1991.
    DOI: [10.1145/116825.116838](https://doi.org/10.1145/116825.116838)

33. Willsey, M., Nandi, C., Wang, Y. R., Flatt, O., Tatlock, Z., &
    Panchekha, P. ["egg: Fast and Extensible Equality Saturation."](https://arxiv.org/abs/2004.03082)
    *Proceedings of POPL*, pp. 23:1–23:29. ACM, 2021.
    DOI: [10.1145/3434304](https://doi.org/10.1145/3434304)

34. Xi, H. & Pfenning, F. ["Dependent Types in Practical Programming."](https://www.cs.cmu.edu/~rwh/students/xi.pdf)
    *Proceedings of POPL*, pp. 214–227. ACM, 1999.
    DOI: [10.1145/292540.292560](https://doi.org/10.1145/292540.292560)
