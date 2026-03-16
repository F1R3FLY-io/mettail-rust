# Predicated Types: Guarded Communication in MeTTaIL

**Status:** Design complete. Compile-time analysis infrastructure implemented.
Runtime guard evaluation pipeline pending. Compile-time vs runtime
classification documented in §14.

---

## Part I: Motivation and Core Design

---

## 1. Introduction and Motivation

The rho-calculus Comm rule fires unconditionally. Any process sent on a channel
is accepted without question:

```
{ n!(q) | (n?x).{c} } ⟶ c[@(q)/x]
```

The process `q` is quoted to a Name `@(q)`, substituted for `x` in the
continuation `c`, and execution proceeds. There is no mechanism to inspect,
filter, or constrain the received value before committing to the communication.

**Predicated types** extend this picture. They condition communication on
**guard predicates** — structural and behavioral constraints that the received
value must satisfy before the Comm rule fires:

```
{ n!(q) | (n ? φ).{c} } ⟶ c[σ]    iff match(φ, @(q)) = σ
```

The guard `φ` is a pattern (a Name expression with free variables). Matching
the concrete received Name `@(q)` against `φ` either succeeds — producing a
substitution `σ` that binds the guard's variables to the corresponding
sub-terms of the received value — or fails, in which case the Comm rule does
not fire and the processes remain waiting.

### Three Motivating Examples

These examples illustrate progressively more powerful guards, building from
pure structural matching to relational properties to first-order logic.

**Example 1 — Structural guard.** Accept only values that look like an output
operation:

```rholang
for (@{x!(y)} <- ch) { P }
```

The guard `@{x!(y)}` = `@(x!(y))` is a Name pattern. The receive fires only
when the value sent on `ch` has the shape `channel!(body)`. The variables `x`
and `y` bind the channel and body sub-terms at their natural categories
(`x : Name`, `y : Proc`).

**Example 2 — Behavioral guard.** Accept only when a relational property holds
over the extracted values:

```rholang
for (@{x!(y)} : path(y, {}) <- ch) { P }
```

After structural matching succeeds (binding `x` and `y`), the behavioral
predicate `path(y, {})` checks whether the tuple `(body, PZero)` exists in
the `path` relation of the current Ascent fixed-point. Communication fires
only if both the structural match AND all behavioral predicates succeed.

**Example 3 — Quantified guard.** Express a universal property over all
reachable terms:

```rholang
for (@x : forall y. (reachable(x, y) => safe(y)) <- ch) { P }
```

This demands that for EVERY term `y` reachable from the received value `x`,
the `safe` relation holds. This is a first-order universally quantified
predicate that compiles to alternating weighted automata (AWA) for evaluation.

### Language-Generic Framing

Predicated types are not specific to Rholang. Any language defined with the
MeTTaIL `language!` macro that declares a guarded receive constructor
(`PGuardedInput`) and a `logic {}` block with relations gets the full
predicated types pipeline automatically. The pipeline is parametric in the
term algebra, the guard predicate language, and the constraint theories
available.

### Document Overview

This document covers the end-to-end predicated types system:

- **Part I** (§§1–10): Core design — from surface syntax through structural
  matching, behavioral predicates, the guarded Comm rule, and correctness
  analysis. A reader can stop after §10 and understand single-channel guards.
- **Part II** (§§11–18): Formal framework — decidability tiering, the
  five-stage pipeline, guard compilation strategies, the BooleanAlgebra
  algebraic foundation, constraint theories, and automata modules.
- **Part III** (§§19–27): Architecture and implementation — lint integration,
  pipeline flow, extension mechanisms, deferred work, implementation roadmap,
  verification, risks, and references.

### Formal Definitions

The **guarded Comm rule** for structural guards:

```
{ n!(q) | (n ? φ).{c} } ⟶ c[σ]
  where σ = match(φ, @(q))
        match : (T_pattern, T_ground) → Option<σ>
        σ : Var → Term
```

The **guarded Comm rule** with behavioral predicates:

```
{ n!(q) | (n ? φ, R₁(a₁), …, Rₖ(aₖ)).{c} } ⟶ c[σ]
  where σ = match(φ, @(q))
        ∀i ∈ [1,k]. Rᵢ(resolve(aᵢ, σ)) ∈ FP
        FP = current Ascent fixed-point
```

### Process Interaction Diagram

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

> **Citation:** Meredith, L. G. & Radestock, M. "A Reflective Higher-Order
> Calculus." Electronic Notes in Theoretical Computer Science, 141(5), 2005.

---

## 2. Surface Syntax

### Examples First

```rholang
// 1. Structural pattern (Layer 1 — existing Pratt/RD matching)
for (@{x!(y)} <- ch) { P }

// 2. Predicated type guard (Layer 2+)
for (@x : halts /\ primes <- ch) { P }

// 3. Combined structural + predicated
for (@{x!(y)} : finite /\ ground <- ch) { P }

// 4. Multi-channel with cross-channel predicates
for (@x <- ch1, @y : related(x) <- ch2) { P }

// 5. Quantified predicates
for (@x : forall y. (reachable(x, y) => safe(y)) <- ch) { P }

// 6. Bounded predicates with explicit depth
for (@x : exists_{k=100} y. (x ->* y /\ halts(y)) <- ch) { P }
```

### Predicate Sublanguage Grammar

The guard predicate language is a first-order logic fragment with bounded
quantification and predicate application:

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Predicate Sublanguage EBNF                       │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│ guard  ::= atom                             atomic predicate        │
│          | guard '/\' guard                 conjunction (and)       │
│          | guard '\/' guard                 disjunction (or)        │
│          | '~' guard                        negation                │
│          | 'forall' var '.' guard           universal quantifier    │
│          | 'exists' var '.' guard           existential quantifier  │
│          | 'exists_{k=' N '}' var '.' guard bounded existential     │
│          | 'forall_{k=' N '}' var '.' guard bounded universal       │
│          | '(' guard ')'                    grouping                │
│          | guard '=>' guard                 implication (~a \/ b)   │
│                                                                     │
│ atom   ::= ident '(' args ')'              relation application     │
│          | term '==' term                   equality                │
│          | term '!=' term                   disequality             │
│          | 'fresh' '(' var ')'              name freshness          │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

Each production maps to a `WeightedMsoFormula` AST variant in
`weighted_mso.rs`. The `/\`, `\/`, `~`, `forall`, `exists` connectives
align with the weighted MSO specification language (M10), enabling direct
automaton compilation via `to_weighted_automaton()`.

---

## 3. Core Principles — Terms as Patterns

### First-Order Matching

In a reflective calculus, **terms serve as their own patterns**. A term with
free variables is a pattern: matching a concrete (ground) term against it
binds the free variables to the corresponding sub-terms.

This is **first-order matching**, not unification:

| Property                   | First-Order Matching           | Unification                        |
|----------------------------|--------------------------------|------------------------------------|
| Variables in concrete term | None (ground)                  | Allowed                            |
| Variables in pattern       | Free variables → binding sites | Free variables                     |
| Result                     | `Option<σ>` (match or fail)    | `Option<σ>` (most general unifier) |
| Complexity                 | O(\|pattern\|)                 | O(n · α(n)) with path compression  |

```
match : (T_ground, T_pattern) → Option<σ>
  where σ : Var → Term
```

The concrete term has no variables; only the pattern does. This is precise and
generalizes to any language defined with MeTTaIL, not just the rho-calculus.

### Natural Categories

The guard `@(x!(y))` is the Name `NQuote(POutput(NVar(x), PVar(y)))`. Matching
the concrete Name `@(a!(body))` against this pattern descends through `NQuote`,
then matches the Proc `a!(body)` against `POutput(NVar(x), PVar(y))`, yielding:

- `x → a` (Name, from the Name-typed position)
- `y → body` (Proc, from the Proc-typed position)

Bindings preserve their **natural category**: Name-position variables bind
Names; Proc-position variables bind Procs.

**Natural-category property:**

```
∀v ∈ dom(σ). category(v) = category(σ(v))
```

This is precise — the user knows that `x` is a Name and `y` is a Proc —
and generalizes to any language (not just rho-calculus with its quoting
convention).

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
and dropping to cross categories:

```
(n ? @(x!(y))).{ @(y)!(*(x)) }
                  ↑       ↑
                  │       Name x, dropped to Proc via *
                  Proc y, quoted to Name via @
```

`@(y)` wraps the Proc variable `y` in a quote, producing a Name — correct
because `y` IS a Proc. `*(x)` drops the Name variable `x` to a Proc —
correct because `x` IS a Name.

### Match Descent Diagram

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
`terms { }` block:

```rust
PGuardedInput . n:Name, ^[xs].guard:[Name* -> Name], ^[ys].p:[Name* -> Proc]
|- "(" n "?" guard ")" "." "{" p "}" : Proc ;
```

This generates the Rust enum variant:

```rust
PGuardedInput(
    Box<Name>,                                   // channel
    Scope<Vec<Binder<String>>, Box<Name>>,        // guard pattern (Name, under scope)
    Vec<BehavioralPred>,                          // behavioral predicates
    Scope<Vec<Binder<String>>, Box<Proc>>,         // continuation (Proc, under scope)
)
```

### Why the Guard is a Name

The guard is a **Name** pattern — it matches the received Name `@(q)`, not the
raw Proc `q`. This is precise: in the rho-calculus, the value available after
reception is `@(q)` (a Name), so the guard pattern should be a Name. The
matching entry point is therefore `match_pattern_name`, not `match_pattern`.
The recursion naturally descends through `NQuote` into the Proc level.

### Why Two Scopes

The guard pattern and the continuation share the same bound variables (the
pattern's free variables). Both must be protected from outer substitutions
by `Scope`:

```
new(x, (x ? @(y!(z))).{@(z)!(*(y))})
```

Here `x` is bound by `new`. The guard variables `y, z` must not be affected
by any outer substitution for `x`. Both Scopes independently protect `y` and
`z` via De Bruijn encoding.

At Comm time, we unbind both Scopes independently, obtaining different fresh
`FreeVar`s but connecting them by position/name:

```rust
let (guard_binders, guard_body) = guard_scope.clone().unbind();
let (cont_binders, cont_body) = cont_scope.clone().unbind();
// guard_binders[i] and cont_binders[i] correspond to the same pattern variable
```

### Dual-Scope Structure Diagram

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

### Mixed-Category Binders

The binder list contains BOTH Name and Proc variables (e.g., `x: Name,
y: Proc` from `@(x!(y))`). The `Scope` mechanism is category-agnostic:
`Binder<String>` wraps `FreeVar<String>`, and `close_term`/`open_term`
traverse the entire term tree across category boundaries, handling `NVar`
and `PVar` occurrences alike. A `Scope<Vec<Binder<String>>, Box<Name>>`
correctly binds Proc variables that appear inside the Name (e.g., `PVar(y)`
inside `NQuote(POutput(_, PVar(y)))`).

---

## 5. Pattern Matching Algorithm

### MatchBindings

Matching produces bindings of **mixed categories**. A shared struct is
generated alongside the AST categories:

```rust
struct MatchBindings {
    name_bindings: Vec<(String, Name)>,
    proc_bindings: Vec<(String, Proc)>,
}
```

`MatchBindings` supports:
- `empty()` — no bindings
- `name(var, val)` — single Name binding
- `proc(var, val)` — single Proc binding
- `merge(other)` — concatenation
- `get(var_name) → Option<MatchValue>` — lookup

### Formal Specification

For each category `Cat`, the macro generates matching methods:

```rust
impl Proc {
    fn match_pattern(&self, pattern: &Proc) -> Option<MatchBindings> { ... }
}

impl Name {
    fn match_pattern_name(&self, pattern: &Name) -> Option<MatchBindings> { ... }
}
```

The function performs first-order matching: the receiver (`self`) is a ground
term; the `pattern` may contain free variables. On success, returns bindings
for each variable in the pattern, at their natural category.

### Match Recursion Equations

```
match(C(t₁, …, tₙ), C(π₁, …, πₙ)) = merge(match(t₁, π₁), …, match(tₙ, πₙ))
match(t, Var(v))                      = {v ↦ t}  at category(v)
match(C₁(…), C₂(…))  where C₁ ≠ C₂  = None     (constructor clash)
```

### Generation Rules per Variant Kind

```
┌──────────────┬──────────────────┬─────────────────────────────────────┐
│ Pattern Kind │ Match Rule       │ Result                              │
├──────────────┼──────────────────┼─────────────────────────────────────┤
│ Variable     │ Bind at category │ MatchBindings::{name,proc}(v, t)    │
│ Nullary      │ Exact equality   │ MatchBindings::empty()              │
│ Regular      │ Recurse fields   │ merge(match(f₁), …, match(fₙ))      │
│ Literal      │ Value equality   │ MatchBindings::empty() if eq        │
│ Collection   │ (deferred)       │ None                                │
│ Binder/Scope │ (deferred)       │ None                                │
└──────────────┴──────────────────┴─────────────────────────────────────┘
```

### Generated Code Examples

**Variable (pattern is a variable):**

```rust
// Proc: bind as Proc
(_, Proc::PVar(OrdVar(Var::Free(fv)))) => {
    let name = fv.pretty_name.clone()?;
    Some(MatchBindings::proc(name, self.clone()))
}

// Name: bind as Name
(_, Name::NVar(OrdVar(Var::Free(fv)))) => {
    let name = fv.pretty_name.clone()?;
    Some(MatchBindings::name(name, self.clone()))
}
```

**Nullary (no fields):**

```rust
(Proc::PZero, Proc::PZero) => Some(MatchBindings::empty())
```

**Regular (constructor with fields):**

```rust
(Proc::POutput(n1, p1), Proc::POutput(n2, p2)) => {
    let mut bindings = (**n1).match_pattern_name(n2)?;
    bindings.merge((**p1).match_pattern(p2)?);
    Some(bindings)
}
```

**Literal:**

```rust
(Proc::CastInt(v1), Proc::CastInt(v2)) if v1 == v2 =>
    Some(MatchBindings::empty())
```

The recursion crosses categories naturally: `Name::match_pattern_name` and
`Proc::match_pattern` both return `MatchBindings`, which accumulates Name
and Proc entries uniformly.

**Collection / Binder** patterns introduce combinatorial (AC) matching and
higher-order matching respectively. Both are deferred; the generated code
returns `None` for these pattern kinds.

### Cross-Category Consistency

Both `match_pattern` and `match_pattern_name` return the same type
(`Option<MatchBindings>`), enabling seamless cross-category recursion:

```
match_pattern_name(NQuote(p_ground), NQuote(p_pattern))
    │
    └── calls match_pattern(p_ground, p_pattern)
            │
            └── calls match_pattern_name(n_ground, n_pattern)
                    │
                    └── ...
```

At every level, bindings accumulate uniformly. The property that makes this
work:

```
∀ call chain C through match_pattern / match_pattern_name:
  C returns Option<MatchBindings>
  ∧ MatchBindings stores both Name and Proc bindings
  ∧ merge() is associative and commutative on disjoint variable sets
```

This ensures that a pattern like `@(x!(y))`, which crosses from Name (`@`)
to Proc (`x!(y)`) and back to Name (`x`) and Proc (`y`), collects all
bindings regardless of the category at which matching began.

### Generated Code Location

New module: `macros/src/gen/term_ops/match_pattern.rs`

Called from `generate_all()` in `macros/src/gen/mod.rs`, alongside
substitution and normalization generation.

---

## 6. The Guarded Comm Rule

### Auto-Generation

When the language defines a `PGuardedInput` constructor, the macro
auto-generates a corresponding rewrite rule. The user does not write this
rule in the `rewrites {}` block. Detection occurs in
`macros/src/logic/rules.rs` by inspecting the `TermParam::GuardBody` variant.

### Generated Datalog (Structural-Only)

This is the rule for guards with no behavioral predicates, annotated
line-by-line:

```rust
rw_proc(s_orig.clone(), t) <--
    // Match via equational theory
    eq_proc(s_orig, s),
    if let Proc::PPar(ref bag) = s,

    // Find a PGuardedInput in the parallel bag
    for (inp, _) in bag.iter(),
    if let Proc::PGuardedInput(ref channel, ref guard_scope,
                                ref _preds, ref cont_scope) = inp,

    // Find a matching POutput on the same channel
    for (out, _) in bag.iter(),
    if let Proc::POutput(ref out_channel, ref sent_proc) = out,
    if channel == out_channel,

    // Construct the received Name: @(q)
    let received_name = Name::NQuote(sent_proc.clone()),

    // Unbind guard scope → fresh FreeVars for matching
    let (guard_binders, guard_body) = guard_scope.clone().unbind(),

    // First-order pattern match: received Name vs guard Name pattern
    if let Some(match_bindings) = received_name.match_pattern_name(&*guard_body),

    // Remove consumed processes from the bag
    let rest = {
        let mut bag = bag.clone();
        bag.remove(&inp);
        bag.remove(&out);
        bag
    },

    // Two-pass substitution into continuation
    let t = {
        let (cont_binders, cont_body) = cont_scope.clone().unbind();

        // Pass 1: Name bindings → multi_substitute_name
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

        // Pass 2: Proc bindings → multi_substitute
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

**Firing condition:**

```
∃(inp, out) ∈ PPar.
    inp = PGuardedInput(ch, φ_scope, [], c_scope)
  ∧ out = POutput(ch, q)
  ∧ match(unbind(φ_scope).body, NQuote(q)) = σ
```

**Result:**

```
PPar((bag ∖ {inp, out}) ∪ {unbind(c_scope).body[σ]}).normalize()
```

### Step-by-Step Evaluation Flow

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

### Input

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

```
received = @(a!({b!({}) | (b?z).{*(z)}}))
         = NQuote(POutput(a, PPar({POutput(b, PZero), PInput(b, z, PDrop(NVar(z)))})))
```

### Step 5 — Unbind Guard Scope

```
(binders, guard_body) = guard_scope.unbind()
guard_body = NQuote(POutput(NVar(x'), PVar(y')))
```

Fresh `FreeVar`s `x'`, `y'` replace the De Bruijn-encoded bound variables.

### Step 6 — Pattern Match

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

### Step 7 — Unbind Continuation Scope

```
(cont_binders, cont_body) = cont_scope.unbind()
cont_body = POutput(NQuote(PVar(y'')), PDrop(NVar(x'')))
```

Fresh `FreeVar`s `x''`, `y''` (different from `x'`, `y'`).

### Step 8 — Two-Pass Substitution

```
Pass 1: multi_substitute_name([x''], [a]):
  NVar(x'') → a
  Result: POutput(NQuote(PVar(y'')), PDrop(a))

Pass 2: multi_substitute([y''], [{b!({}) | (b?z).{*(z)}}]):
  PVar(y'') → {b!({}) | (b?z).{*(z)}}
  Result: POutput(NQuote({b!({}) | (b?z).{*(z)}}), PDrop(a))
```

### Step 9 — Normalize

```
POutput(NQuote({b!({}) | (b?z).{*(z)}}), PDrop(a))
= @({b!({}) | (b?z).{*(z)}})!(*(a))
```

Final `PPar`: `{@({b!({}) | (b?z).{*(z)}})!(*(a))}` ✓

---

## 8. Behavioral Predicates

### Motivation

Structural matching alone answers "does the received value have the right
shape?" but cannot express relational properties like "is there a path from
`y` to the empty process?" or "is `x` a well-formed output?". Behavioral
predicates bridge this gap by checking whether declared Ascent relations hold
over the match-extracted values.

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

For the declared relation `path(Proc, Proc)`:

```rust
rw_proc(s_orig.clone(), t) <--
    eq_proc(s_orig, s),
    if let Proc::PPar(ref bag) = s,

    for (inp, _) in bag.iter(),
    if let Proc::PGuardedInput(ref channel, ref guard_scope,
                                ref preds, ref cont_scope) = inp,

    // Check this guard has exactly one pred referencing "path"
    if preds.len() == 1 && preds[0].relation_name == "path",

    for (out, _) in bag.iter(),
    if let Proc::POutput(ref out_channel, ref sent_proc) = out,
    if channel == out_channel,

    // Structural matching (same as §6)
    let received_name = Name::NQuote(sent_proc.clone()),
    let (_, guard_body) = guard_scope.clone().unbind(),
    if let Some(match_bindings) = received_name.match_pattern_name(&*guard_body),

    // Resolve predicate arguments from match bindings
    let pred_arg0 = preds[0].resolve_arg(0, &match_bindings),
    let pred_arg1 = preds[0].resolve_arg(1, &match_bindings),

    // JOIN against the declared relation — static Ascent clause
    path(pred_arg0, pred_arg1),

    // ... rest, substitution, same as §6 ...
```

The critical line is `path(pred_arg0, pred_arg1)`. This is a standard Ascent
join clause: it succeeds only if the tuple `(pred_arg0, pred_arg1)` exists
in the `path` relation. Since the relation name `path` is known at macro
expansion time, the join clause is statically generated.

### Behavioral Predicate Evaluation Flow

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

Each behavioral predicate argument is either:

- A **match variable reference**: `y` → resolved from `match_bindings` by name
- A **constant term**: `{}` → used directly

```rust
struct BehavioralPred {
    relation_name: String,
    args: Vec<PredArg>,
    negated: bool,           // for stratified negation (§9)
}

enum PredArg {
    Var(String),              // reference to a match variable
    Constant(Proc),           // a ground term
}
```

### Conjunctions

For conjunctions of behavioral predicates (e.g., `path(y, {}) AND
is_output(*(x))`), the macro generates rules for the relevant combinations.
A guard with predicates referencing relations `R₁` and `R₂` requires a rule
with BOTH join clauses:

```rust
    // ... structural matching ...
    let r1_arg0 = ..., let r1_arg1 = ...,
    R1(r1_arg0, r1_arg1),
    let r2_arg0 = ...,
    R2(r2_arg0),
    // ... continuation ...
```

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

When `negated: true`, the generated rule uses Ascent negation:

```rust
    !path(pred_arg0, pred_arg1),    // fires when tuple is ABSENT
```

Stratification validation ensures negated relations appear in lower strata
than the rules consuming them. Same-stratum negation produces a compile-time
error.

### Full Guard Check Formula

```
match(φ, @(q)) = σ  ∧  ∀(R, args, neg) ∈ preds.
    (¬neg ⟹ R(resolve(args, σ)) ∈ FP) ∧
    (neg  ⟹ R(resolve(args, σ)) ∉ FP)
```

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

**Claim:** `match(C(π₁,…,πₙ), C(t₁,…,tₙ)) = ⨆ᵢ match(πᵢ, tᵢ)`

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

```
(n ? @(x!(y)), path(y, {})).{ @(y)!(*(x)) }
 │   ├────────┤ ├──────────┤  ├────────────┤
 │   structural  behavioral    continuation
 channel
```

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

The existing `var_inference.rs` module infers variable categories from syntax
context. For the guard `@(x!(y))`:

- `x` is in a Name-typed field (channel of `POutput`) → Name category
- `y` is in a Proc-typed field (body of `POutput`) → Proc category

These natural categories are preserved through to `MatchBindings` and the
two-pass substitution. The binder list records each variable's category so
the continuation knows which variables are NVar vs PVar.

### Term Context Declaration

The term context syntax extends to support the guard-binder pattern via a new
`TermParam` variant:

```rust
TermParam::GuardBody {
    guard: Ident,       // "guard"
    body: Ident,        // "p"
    guard_ty: TypeExpr, // Name
    body_ty: TypeExpr,  // Proc
}
```

This generates a `Scope<Vec<Binder<String>>, Box<Name>>` for the guard, a
`Vec<BehavioralPred>` for the predicates, and a
`Scope<Vec<Binder<String>>, Box<Proc>>` for the continuation.

### Tokens Feature Integration

Guard keywords (`forall`, `exists`, `/\`, `\/`, `~`, `=>`, `exists_{k=N}`)
are defined via the `tokens { ... }` block as `TokenKind::Custom` entries.
Modal lexing (`push(pred_mode)`/`pop`) activates predicate keyword
recognition inside guard scope. FIRST set augmentation auto-wires custom
guard tokens. No manual lexer NFA/DFA modifications are needed.

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

### Tier Classification

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

### Classification Criteria

**T1 — Compile-time decidable:**

```
ground_decidable(atoms(φ)) ∧ finite_domain(quantifiers(φ))
```

| Predicate                       | Domain         | Decision                           |
|---------------------------------|----------------|------------------------------------|
| `true`                          | —              | T1 (trivially true)                |
| `false`                         | —              | T1 (trivially false, dead receive) |
| `forall c in {R,G,B}. valid(c)` | 3-element enum | T1 (check all 3)                   |
| `x > 5 /\ x < 10`               | i64 interval   | T1 (interval algebra)              |
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

```
∃k. decidable(φ↾k)    where φ↾k bounds all quantifiers to depth k
```

| Predicate                        | Bound         | Completeness         |
|----------------------------------|---------------|----------------------|
| `exists_{k=100} y. halts(y)`     | k = 100 steps | Sound but incomplete |
| `forall_{k=50} path. safe(path)` | k = 50 depth  | Sound but incomplete |

**T4 — Undecidable:**

Everything not in T1–T3. By Rice's theorem, for non-trivial semantic
properties of programs, membership is undecidable.

| Predicate                      | Why Undecidable           | Mitigation                     |
|--------------------------------|---------------------------|--------------------------------|
| `halts(x)`                     | Rice's theorem            | User proof or Rocq certificate |
| `forall y. (x →* y ⟹ safe(y))` | Unbounded ∀ over ∞ domain | `assert_pred` annotation       |
| `forall X. φ(X)`               | Second-order universal    | Restricted MSO or user proof   |

### Classification Decision Tree

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

### Cost Model

| Tier | Compile Cost                | Runtime Cost per Receive | Guarantees               |
|------|-----------------------------|--------------------------|--------------------------|
| T1   | O(\|formula\|)              | 0 (eliminated)           | Complete + sound         |
| T2   | O(2^\|formula\|) worst case | O(\|value\|)             | Complete + sound         |
| T3   | O(k · \|formula\|)          | O(k · \|value\|)         | Sound, not complete      |
| T4   | O(\|proof\|)                | O(1) (trust)             | Depends on proof quality |

---

## 12. The Five-Stage Pipeline

The predicated types pipeline has five stages, described once here.

> **Note:** All five pipeline stages execute at **compile time** during
> `language!` macro expansion. Stage 5 (Codegen) produces a `TokenStream`
> containing the guard evaluation functions and Comm rules that will execute at
> **runtime**. The pipeline infrastructure itself — automaton construction,
> analysis, optimization — is not present in the compiled binary. See §14 for
> a comprehensive compile-time vs runtime classification.

```
┌──────────────────────────────────────────────────────────────────────────┐
│ Stage 1: PARSE                                                           │
│ Surface syntax → Predicate AST (WeightedMsoFormula)                      │
│ Modules: Pratt parser, weighted_mso.rs                                   │
│                                                                          │
│ Input:  for (@x : halts /\ primes <- ch) { P }                           │
│ Output: WeightedMsoFormula::And(AtomicPos("halts"), AtomicPos("primes")) │
└───────────────────────┬──────────────────────────────────────────────────┘
                        │
                        ▼
┌──────────────────────────────────────────────────────────────────────────┐
│ Stage 2: CLASSIFY + DISPATCH                                             │
│ Decidability tier (T1–T4) + Module activation (M1–M14)                   │
│ Modules: symbolic.rs, predicate_dispatch.rs, weighted_mso.rs             │
│                                                                          │
│ Actions: classify_decidability() → tier                                  │
│          extract_features() → 14-bit PredicateSignature                  │
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
│ Module: macros/src/gen/runtime/guard_codegen.rs (future)                 │
│                                                                          │
│ T2 → SFA transition table or Ascent join clause                          │
│ T3 → bounded_check() with depth counter                                  │
│ T4 → assert_pred() wrapper                                               │
└──────────────────────────────────────────────────────────────────────────┘
```

### Stage 1: Parse

The predicate sublanguage is parsed by PraTTaIL's Pratt parser into a
`WeightedMsoFormula` AST:

```rholang
for (@x : halts /\ primes <- ch) { P }
```

Parses to:

```
WeightedMsoFormula::And(
    Box::new(AtomicPos { label: "halts", var: "x" }),
    Box::new(AtomicPos { label: "primes", var: "x" }),
)
```

For quantified predicates:

```rholang
for (@x : forall y. (reachable(x, y) => safe(y)) <- ch) { P }
```

Parses to:

```
WeightedMsoFormula::ForallFirst {
    var: "y",
    body: Box::new(Or(
        Box::new(NegAtomicPos { label: "reachable(x, y)", var: "y" }),
        Box::new(AtomicPos { label: "safe", var: "y" }),
    )),
}
```

### Stage 2: Classify

Classification algorithm (in `symbolic.rs` and `weighted_mso.rs`):

1. `classify_formula()` → `FirstOrder | Existential | Restricted | Full`
2. `check_decidability()` → `T1 | T2 | T3 | T4`
3. `extract_features()` → `PredicateSignature(u16)` (14 bits, one per module)
4. Modules ordered by `estimated_cost()`: cheapest execute first

### Stage 3: Compile

Compilation path depends on tier and formula structure:

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

### Stage 4: Optimize

Guard optimization after compilation:

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

For multi-channel predicates, M8 (multi-tape) fuses cross-channel constraints.
M7 (probabilistic) orders guards by selectivity:

```
Guard            Selectivity    Order
halts(x)         0.01 (1%)      1 (check first — eliminates 99%)
primes(x)        0.15 (15%)     2
ground(x)        0.80 (80%)     3 (check last — eliminates only 20%)
```

### Stage 5: Codegen

The compiled automaton generates Rust code. Examples:

**T2 — Range check (IntervalAlgebra):**
```rust
fn guard_check(x: i64) -> bool {
    x > 0 && x < 100
}
```

**T2 — Relation lookup (Ascent join):**
```rust
if ascent_program.is_wellformed.contains(&(value.clone(),)) {
    // execute P
}
```

**T3 — Bounded iteration:**
```rust
fn bounded_check(x: &Term, depth_limit: usize) -> TriState {
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    queue.push_back((x.clone(), 0));
    while let Some((term, depth)) = queue.pop_front() {
        if depth > depth_limit { return TriState::Unknown; }
        if is_halted(&term) { return TriState::True; }
        if !visited.insert(term.clone()) { continue; }
        for next in reduce(&term) {
            queue.push_back((next, depth + 1));
        }
    }
    TriState::False
}
```

---

## 13. Guard Compilation Strategies

### Single-Channel Guards

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

### Multi-Channel Guards

```
for (@x <- ch1, @y : f(x, y) <- ch2) { P }

Step 1: Classify each guard independently
Step 2: Detect cross-channel dependencies (x referenced in ch2's guard)
Step 3: Build multi-tape automaton (M8) or two-way transducer (M11)
Step 4: Optimize consumption order via selectivity (M7)
Step 5: Codegen coordinated guard evaluation
```

For cross-channel constraint propagation, M11 (two-way transducer) resolves
backward dependencies:

```
for (@x <- ch1, @y : f(x, y) <- ch2) { P }
       │
       ▼  backward_constraint(ch2_guard, ch1)
    ChannelConstraint {
        forward_transducer:  ch1_value → evaluate f(x, _)
        backward_transducer: ch2_guard → constrain ch1_values
    }
```

### Recursive Predicates (letprop)

User-defined predicates compile through the mu-calculus:

```rholang
letprop halt x = forall x'. ~(x ->* x') in
for (@x : halt <- ch) { P }
```

Compilation path:

```
letprop halt x = forall x'. ~(x ->* x')
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

A bounded variant (`halt_{100}`) is T3 and compiles to a bounded checker.

### Generated Rust Code per Tier

**T1 — Static elimination (compile-time constant):**

```rust
// Guard `x > 0 /\ x < 100` with x bound to literal 42 at parse time:
// Entire guard statically evaluates to `true` → guard eliminated from codegen.
// No runtime code generated.
```

**T2 — Range check (IntervalAlgebra):**

```rust
fn guard_check(x: i64) -> bool {
    x > 0 && x < 100
}
```

**T2 — Relation lookup (Ascent join):**

```rust
if ascent_program.is_wellformed.contains(&(value.clone(),)) {
    // fire Comm rule: execute continuation with bindings
}
```

**T2 — Register test (RegisterAutomaton):**

```rust
fn register_guard(value: &Term, registers: &mut [Option<Term>; 4]) -> bool {
    match value {
        Term::App { head, args } if head == "cons" && args.len() == 2 => {
            // Register 0: store first element for equality comparison
            match &registers[0] {
                None => {
                    registers[0] = Some(args[0].clone());
                    register_guard(&args[1], registers)  // recurse on tail
                }
                Some(stored) => {
                    // Data equality test: compare current element against register
                    *stored == args[0] && register_guard(&args[1], registers)
                }
            }
        }
        Term::Const(c) if c == "nil" => true,  // accept: end of list
        _ => false,
    }
}
```

**T3 — Bounded iteration:**

```rust
fn bounded_check(x: &Term, depth_limit: usize) -> TriState {
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    queue.push_back((x.clone(), 0));
    while let Some((term, depth)) = queue.pop_front() {
        if depth > depth_limit { return TriState::Unknown; }
        if is_halted(&term) { return TriState::True; }
        if !visited.insert(term.clone()) { continue; }
        for next in reduce(&term) {
            queue.push_back((next, depth + 1));
        }
    }
    TriState::False
}
```

**T4 — User assertion:**

```rust
fn assert_pred(value: &Term) -> bool {
    // Trust user annotation or Rocq proof certificate.
    // Emit MSO01 lint if no certificate provided.
    true
}
```

---

## 14. Compile-Time vs Runtime Classification

The predicated types system has a sharp two-phase architecture. Understanding
which components execute at **compile time** (during `language!` macro
expansion and PraTTaIL pipeline analysis) versus **runtime** (during generated
Ascent fixpoint evaluation) is essential for reasoning about performance,
correctness, and extensibility.

### Definitions

**Compile time** = `cargo build`. The `language!` proc macro invokes the
PraTTaIL pipeline: grammar analysis, automaton construction, decidability
classification, lint emission, guard optimization, and Rust code generation.
Every module in the `prattail/` crate and `macros/` crate executes here.
None of this code appears in the compiled binary — it is discarded after
producing a `TokenStream`.

**Runtime** = program execution. The generated Ascent struct (`ascent!` macro
output) evaluates its fixpoint. Only the generated code runs: pattern matching
methods, Comm rules with structural and behavioral guards, guard evaluation
functions (range checks, relation lookups, bounded iterators), substitution,
and normalization.

**The boundary** is the `TokenStream` returned by the proc macro. Everything
upstream of that boundary is compile-time infrastructure; everything downstream
is runtime artifact.

### 14.1 Master Component Classification

The table below classifies every major component discussed in this document.
Components marked "codegen" have a dual nature: they are constructed at compile
time but produce artifacts that execute at runtime.

```
┌────────────────────────────────────────────┬─────────────┬──────────────┬───────────────────────────────────────────────────┐
│ Component                                  │ Compile-Time│ Runtime      │ Notes                                             │
├────────────────────────────────────────────┼─────────────┼──────────────┼───────────────────────────────────────────────────┤
│                                            │             │              │                                                   │
│ PART I — CORE DESIGN                       │             │              │                                                   │
│                                            │             │              │                                                   │
│ Surface syntax parsing (§2)                │ ✓           │              │ Pratt parser in proc macro                        │
│ Guard predicate sublanguage (§2)           │ ✓           │              │ /\, \/, ~, forall, exists parsed at macro time    │
│ Term representation / PGuardedInput (§4)   │ ✓           │              │ AST enum variant generation                       │
│ Dual-scope structure (§4)                  │ ✓           │              │ Scope construction during macro expansion         │
│ match_pattern methods (§5)                 │ codegen     │ per-Comm     │ Generated at compile time; called per Comm fire   │
│ match_pattern_name methods (§5)            │ codegen     │ per-Comm     │ Same — entry point for Name-level guard matching  │
│ MatchBindings accumulation (§5)            │             │ per-Comm     │ Collects Name + Proc bindings during matching     │
│ Guarded Comm rule — structural (§6)        │ codegen     │ per-fire     │ Ascent rule generated at compile, fires at run    │
│ Two-pass substitution (§6)                 │             │ per-fire     │ multi_substitute_name then multi_substitute       │
│ PPar bag manipulation (§6)                 │             │ per-fire     │ remove consumed, insert continuation              │
│ Normalization (§6)                         │             │ per-fire     │ .normalize() on result term                       │
│ Behavioral predicate joins (§8)            │ codegen     │ per-fire     │ Ascent join clauses; O(1) hash lookup at runtime  │
│ Negated predicate stratification (§8)      │ ✓           │              │ Stratum ordering validated during macro expansion │
│ Predicate argument resolution (§8)         │             │ per-fire     │ resolve_arg() maps match vars to concrete values  │
│ Variable inference + categories (§10)      │ ✓           │              │ Free-variable extraction with natural categories  │
│ Tokens feature — guard keywords (§10)      │ ✓           │              │ TokenKind::Custom, modal lexing, FIRST sets       │
│                                            │             │              │                                                   │
│ PART II — FORMAL FRAMEWORK                 │             │              │                                                   │
│                                            │             │              │                                                   │
│ Decidability classification T1–T4 (§11)    │ ✓           │              │ Formula structure analysis in pipeline            │
│ T1 guard evaluation (§11, §13)             │ ✓ (elim.)   │              │ Statically evaluated → true/false; dead-code elim │
│ T2 guard: range check (§13)                │ codegen     │ O(1)         │ Inline arithmetic (e.g. x > 0 && x < 100)         │
│ T2 guard: relation lookup (§13)            │ codegen     │ O(1) hash    │ ascent_prog.relation.contains(&(val,))            │
│ T2 guard: register automaton (§13)         │ codegen     │ O(|value|)   │ TestEq/TestFresh register machine evaluation      │
│ T2 guard: SFA transition table (§13)       │ codegen     │ O(|value|)   │ Determinized SFA as match statement               │
│ T3 guard: bounded iteration (§13)          │ codegen     │ O(k·|value|) │ BFS/DFS with depth counter; may return Unknown    │
│ T4 guard: user assertion (§13)             │ lint        │ O(1) trust   │ MSO01 lint at compile; trust annotation at run    │
│ Pipeline Stage 1: Parse (§12)              │ ✓           │              │ Surface syntax → WeightedMsoFormula AST           │
│ Pipeline Stage 2: Classify + Dispatch (§12)│ ✓           │              │ PredicateSignature (14-bit) + tier assignment     │
│ Pipeline Stage 3: Compile (§12)            │ ✓           │              │ Formula → SFA/PATA/RegisterAutomaton/bounded      │
│ Pipeline Stage 4: Optimize (§12)           │ ✓           │              │ SFA intersect/minimize, selectivity ordering      │
│ Pipeline Stage 5: Codegen (§12)            │ ✓           │              │ Automaton → TokenStream (Rust source code)        │
│ BooleanAlgebra trait + operations (§15)    │ ✓           │              │ is_satisfiable, implies, witness, evaluate        │
│ SFA determinize + minimize (§15)           │ ✓           │              │ Minterm-based partitioning, Hopcroft minimization │
│ SFA intersect / complement (§15)           │ ✓           │              │ Guard fusion + guard negation for overlap analysis│
│ ProductAlgebra<A,B> composition (§15)      │ ✓           │              │ Cross-domain constraint composition               │
│ IntervalAlgebra (§15)                      │ ✓           │              │ i64 range analysis for numeric guards             │
│ CharClassAlgebra (§15)                     │ ✓           │              │ Unicode character class analysis                  │
│ KatBooleanAlgebra (§15)                    │ ✓           │              │ Propositional atom analysis for behavioral preds  │
│ DispatchAlgebra (§15)                      │ ✓           │              │ 14-bit module signature satisfiability            │
│ ConstraintTheory::propagate (§16)          │ ✓           │              │ Constraint propagation for satisfiability checking│
│ ConstraintTheory::label (§16)              │ ✓           │              │ Search branch generation (label-based theories)   │
│ ConstraintTheory::witness (§16)            │ ✓           │              │ Satisfying assignment for counterexample gen      │
│ TheoryAlgebra<T> bridge (§16)              │ ✓           │              │ ConstraintTheory → BooleanAlgebra adapter         │
│ LogicStream — label search (§16)           │ ✓           │              │ Fair backtracking for label-based CT satisfiab.   │
│ LogicStream — quantifier eval (§16, §22)   │             │ per-fire     │ evaluate_quantified() via gnot/interleave at run  │
│ Presburger NFA construction (§16)          │ ✓           │              │ Bartzis-Bultan NFA for linear integer arithmetic  │
│ Presburger NFA operations (§16)            │ ✓           │              │ Intersection, complement, projection, emptiness   │
│ PresburgerAlgebra (fast path) (§16)        │ ✓           │              │ Direct BooleanAlgebra impl (no CT overhead)       │
│ PresburgerTheory (CT path) (§16)           │ ✓           │              │ ConstraintTheory impl for LogicT integration      │
│ Unification — pattern overlap (§16)        │ ✓           │              │ Martelli-Montanari for compile-time overlap check │
│ Unification — runtime matching (§16)       │             │ per-match    │ Term unification during pattern dispatch          │
│ LatticeTheory — Warshall closure (§16)     │ ✓           │              │ Transitive closure for compile-time subtype check │
│ LatticeTheory — LUB/GLB (§16)              │ ✓           │              │ Join/meet computation for type analysis           │
│ M1 Symbolic (§17)                          │ ✓           │              │ BooleanAlgebra core; guard sat/overlap/subsump    │
│ M2 Weighted Buchi (§17)                    │ ✓           │              │ Infinite behavior predicate analysis              │
│ M3 Polynomial AWA (§17)                    │ ✓           │              │ ∀/∃ quantifier analysis as ⊗/⊕ states             │
│ M4 Weighted VPA (§17)                      │ ✓           │              │ Quantifier scope nesting analysis                 │
│ M5 Parity Tree (§17)                       │ ✓           │              │ mu-calculus / letprop compilation analysis        │
│ M6 Register (§17)                          │ ✓           │              │ Data equality/freshness analysis + dead binders   │
│ M7 Probabilistic (§17)                     │ ✓           │ ordering     │ Selectivity estimation → runtime eval order       │
│ M8 Multi-Tape (§17)                        │ ✓           │              │ Multi-channel cross-tape analysis                 │
│ M9 Multiset (§17)                          │ ✓           │              │ Cardinality predicate analysis                    │
│ M10 Weighted MSO (§17)                     │ ✓           │              │ Formula classification + automaton compilation    │
│ M11 Weighted Two-Way (§17)                 │ ✓           │              │ Cross-channel backward constraint propagation     │
│ M12 Linear Arithmetic (§17)                │ ✓           │              │ Presburger guard analysis via NFA decision proc   │
│ M13 Unification (§17)                      │ ✓           │              │ Structural pattern overlap via Martelli-Montanari │
│ M14 Subtype Lattice (§17)                  │ ✓           │              │ Type hierarchy analysis via Warshall closure      │
│ Predicate dispatch controller (§17)        │ ✓           │              │ Feature extraction + 14-bit sig + cost ordering   │
│ Automata composition: SFA ∩/∪/¬ (§18)      │ ✓           │              │ Guard fusion and negation                         │
│ Automata composition: AWA Q⊗/Q⊕ (§18)      │ ✓           │              │ Quantifier automaton construction                 │
│ Automata composition: PATA (§18)           │ ✓           │              │ Recursive predicate (letprop) analysis            │
│ Multi-tape product construction (§18)      │ ✓           │              │ Cross-channel guard fusion                        │
│                                            │             │              │                                                   │
│ PART III — ARCHITECTURE & IMPLEMENTATION   │             │              │                                                   │
│                                            │             │              │                                                   │
│ All lints: SYM01–04 (§19)                  │ ✓           │              │ Guard satisfiability, overlap, subsumption        │
│ All lints: MSO01–03 (§19)                  │ ✓           │              │ Formula classification diagnostics                │
│ All lints: PT01–03 (§19)                   │ ✓           │              │ PATA emptiness, subsumption, depth warnings       │
│ All lints: RA01–03 (§19)                   │ ✓           │              │ Register automaton dead store/test diagnostics    │
│ All lints: MT01–02, TW01, TW03 (§19)       │ ✓           │              │ Multi-channel and two-way diagnostics             │
│ All lints: PR01 (§19)                      │ ✓           │              │ Low-selectivity rule warning                      │
│ All lints: PB01–03 (§19)                   │ ✓           │              │ Presburger tautology, unsat, subsumption          │
│ All lints: UN01–03 (§19)                   │ ✓           │              │ Unification occurs check, clash, subsumption      │
│ All lints: SL01–02 (§19)                   │ ✓           │              │ Subtype cycle, incomplete hierarchy               │
│ All lints: LT01 (§19)                      │ ✓           │              │ LogicT search bound exceeded                      │
│ Pipeline flow — parallel analysis (§20)    │ ✓           │              │ thread::scope for CT analysis parallelism         │
│ Dispatch gating (§20)                      │ ✓           │              │ Module skip based on PredicateSignature           │
│ theories {} extension mechanism (§21)      │ ✓           │              │ Data-driven CT wiring replaces keyword heuristics │
│ Gap 3: QuantifiedFormula AST (§22)         │ codegen     │              │ FOL formula AST construction at macro time        │
│ Gap 3: evaluate_quantified() (§22)         │             │ per-fire     │ LogicT-based ∀/∃ evaluation at runtime            │
│ Gap 3: BehavioralPred parser (§22)         │ ✓           │              │ guard() syntax parsing during macro expansion     │
│ Gap 4: multiset_partitions() (§22)         │             │ per-fire     │ Lazy partition enumeration at runtime             │
│ Gap 4: multiset_select() (§22)             │             │ per-fire     │ Bounded partition collection at runtime           │
│ Gap 4: AcMatch codegen (§22)               │ codegen     │ per-fire     │ Partition code generated; runs per Comm fire      │
│ Always-on: WPDS (§17)                      │ ✓           │              │ Stack-aware reachability for guard eval chains    │
│ Always-on: CEGAR (§17)                     │ ✓           │              │ Iterative abstraction refinement                  │
│ Always-on: Safety (§17)                    │ ✓           │              │ Guard completeness checking                       │
│ Always-on: Algebraic path expressions (§17)│ ✓           │              │ Guard evaluation CFG summarization                │
│ Always-on: Newton fixpoint (§17)           │ ✓           │              │ Accelerated fixpoint for idempotent semirings     │
│ Always-on: Forward-Backward (§17)          │ ✓           │ annotation   │ Hot → #[inline]; cold → #[cold] on generated code │
│ Feature-gated: TRS (§17)                   │ ✓           │              │ Guard-conditional rewrite confluence analysis     │
│ Feature-gated: Nominal (§17)               │ ✓           │              │ Alpha-equivalence in guard patterns               │
│ Feature-gated: Petri (§17)                 │ ✓           │              │ Deadlock analysis for guarded communication       │
│ Feature-gated: KAT (§17)                   │ ✓           │              │ Guard flow equivalence, Hoare triples             │
│ Feature-gated: CRA (§17)                   │ ✓           │              │ Quantitative guard cost metering                  │
│ Feature-gated: Morphism (§17)              │ ✓           │              │ Translation verification between guard formalisms │
│ Feature-gated: Provenance (§17)            │ ✓           │              │ Derivation tracking through guard evaluation      │
│ Feature-gated: Proof Output (§17)          │ ✓           │              │ Correctness certificates                          │
│ Rocq formal proofs (§16, §24)              │ verified    │              │ Proof artifacts not in binary; verify properties  │
└────────────────────────────────────────────┴─────────────┴──────────────┴───────────────────────────────────────────────────┘
```

### 14.2 Detailed Classification by Document Part

#### Part I (§§1–10) — "What Gets Generated"

Part I defines the core data structures (AST variants, constructors, scopes)
and algorithms (pattern matching, substitution, Comm rule) that the `language!`
macro generates. The macro itself executes at compile time, but its output —
the generated Rust code — executes at runtime.

**Compile-time only (no runtime artifact):**

| Component                   | Section | What happens at compile time                                                                                                            |
|-----------------------------|---------|-----------------------------------------------------------------------------------------------------------------------------------------|
| Surface syntax parsing      | §2      | PraTTaIL's Pratt parser processes `for (@x : pred <- ch) { P }` and produces the `PGuardedInput` AST node during proc macro expansion   |
| Term representation         | §4      | The `PGuardedInput` enum variant is generated: `PGuardedInput(Box<Name>, Scope<...>, Vec<BehavioralPred>, Scope<...>)`                  |
| Dual-scope structure        | §4      | Two `Scope<Vec<Binder<String>>, Box<_>>` wrappers are constructed, protecting guard and continuation variables from outer substitutions |
| Variable inference          | §10     | Free-variable extraction walks the guard pattern AST at macro time, determining each variable's natural category (Name vs Proc)         |
| Guard keyword tokens        | §10     | `TokenKind::Custom` entries for `forall`, `exists`, `/\`, `\/`, `~`, `=>` are compiled into the lexer NFA                               |
| Negated pred stratification | §8      | Stratum ordering is validated during macro expansion — an error is emitted if negated relations violate stratification                  |

**Compile-time codegen → runtime execution:**

| Component                              | Section | Compile-time action                                                             | Runtime cost per Comm fire                                                |
|----------------------------------------|---------|---------------------------------------------------------------------------------|---------------------------------------------------------------------------|
| `match_pattern` / `match_pattern_name` | §5      | Methods generated for each category (`Proc`, `Name`)                            | O(\|pattern\|) — recursive descent through constructors                   |
| Guarded Comm rule (structural)         | §6      | Ascent rule clause generated with `if let Some(match_bindings) = ...`           | Per-Comm: pattern match + bag manipulation                                |
| Two-pass substitution                  | §6      | Substitution code generated in rule body                                        | Per-fire: `multi_substitute_name` (NVars) then `multi_substitute` (PVars) |
| Behavioral predicate joins             | §8      | Per-relation specialized Comm rules with `R(pred_arg0, pred_arg1)` join clauses | Per-fire: O(1) hash lookup per relation                                   |
| Predicate argument resolution          | §8      | `resolve_arg()` code generated in rule body                                     | Per-fire: map match variable name to concrete value                       |
| PPar bag manipulation                  | §6      | `bag.remove(&inp); bag.remove(&out); Proc::insert_into_ppar(...)` generated     | Per-fire: BTreeMap operations                                             |
| Normalization                          | §6      | `.normalize()` call generated at end of Comm rule                               | Per-fire: recursive term normalization                                    |

#### Part II (§§11–18) — "Compile-Time Analysis Infrastructure"

**Part II is entirely compile-time.** Every section describes analysis
infrastructure that executes during `language!` macro expansion (via the
PraTTaIL pipeline). The only runtime artifacts from Part II are the **products
of Stage 5 codegen** — the guard evaluation functions themselves.

**Decidability classification (§11):** Runs at compile time. Classifies each
guard formula into T1–T4 by analyzing formula structure (ground-decidable
atoms, finite domains, explicit bounds, second-order quantifiers). This
classification determines which compilation strategy Stage 3 uses, and thus
what kind of runtime code Stage 5 emits:

| Tier | Compile-time action                                                    | Runtime artifact                                                                 | Runtime cost                         |
|------|------------------------------------------------------------------------|----------------------------------------------------------------------------------|--------------------------------------|
| T1   | Static evaluation → true/false                                         | **None** (dead-code eliminated)                                                  | O(0)                                 |
| T2   | SFA compiled, determinized, minimized; or Ascent join clause generated | Range check function, relation lookup, register machine, or SFA transition table | O(1) to O(\|value\|)                 |
| T3   | Bounded automaton compiled, depth limit fixed                          | Bounded iteration function with depth counter                                    | O(k · \|value\|); may return Unknown |
| T4   | MSO01 lint emitted, Rocq cert verified (if provided)                   | `assert_pred()` trust wrapper                                                    | O(1) — user takes responsibility     |

**Five-stage pipeline (§12):** All five stages run at compile time. Stage 5's
output (a `TokenStream`) is the sole bridge to runtime:

| Stage       | Compile-time purpose                                      | Runtime artifact                   |
|-------------|-----------------------------------------------------------|------------------------------------|
| 1. Parse    | Surface syntax → `WeightedMsoFormula` AST                 | None                               |
| 2. Classify | `PredicateSignature` (14-bit) + tier assignment           | None                               |
| 3. Compile  | Formula → SFA / PATA / RegisterAutomaton / BoundedChecker | None (intermediate representation) |
| 4. Optimize | SFA intersection + minimization, selectivity ordering     | None (shapes codegen decisions)    |
| 5. Codegen  | Automaton → `TokenStream` (Rust source code)              | **All runtime artifacts**          |

**BooleanAlgebra framework (§15):** Purely compile-time. SFA operations
(`determinize`, `minimize`, `intersect`, `complement`, `is_satisfiable`,
`witness`) analyze guards for satisfiability, overlap, subsumption, and
equivalence. Results flow into lints (SYM01–04) and optimization decisions.
No BooleanAlgebra code appears in the generated binary.

**Constraint theory suite (§16):** Primarily compile-time, with two exceptions:

| Component                     | Compile-time role                                                                              | Runtime role                                                                   |
|-------------------------------|------------------------------------------------------------------------------------------------|--------------------------------------------------------------------------------|
| Presburger NFA                | Build NFA for `Σ aᵢ·xᵢ ≤ b`; intersection/complement/emptiness for satisfiability + entailment | None — analysis results consumed by lints and codegen                          |
| Presburger BooleanAlgebra     | `is_satisfiable()` for PB01–03 lints                                                           | None                                                                           |
| Unification (overlap)         | `propagate()` + `unify()` for pattern overlap detection (UN01–03)                              | None                                                                           |
| Unification (matching)        | —                                                                                              | Per-match: term unification during runtime pattern dispatch (if enabled)       |
| LatticeTheory                 | Warshall closure, LUB/GLB for subtype analysis (SL01–02)                                       | None                                                                           |
| LogicStream (label search)    | Fair backtracking for label-based ConstraintTheory satisfiability                              | None                                                                           |
| LogicStream (quantifier eval) | —                                                                                              | Per-fire: `evaluate_quantified()` for ∀/∃ guard predicates via gnot/interleave |
| TheoryAlgebra bridge          | Wraps ConstraintTheory into BooleanAlgebra for SFA integration                                 | None                                                                           |
| ProductAlgebra                | Composes two BooleanAlgebra instances for mixed-domain analysis                                | None                                                                           |

**Automata modules M1–M14 (§17):** All 14 modules are **compile-time
analysis only**. None of these automata appear in the generated binary. They
analyze guard structure, detect issues, and inform codegen decisions:

- M1 (Symbolic): guard satisfiability → SYM01, guard overlap → SYM02
- M7 (Probabilistic): selectivity estimation → determines runtime evaluation
  order (compile-time analysis with a runtime *effect* — the generated guard
  check order)
- M12–M14 (Presburger, Unification, Lattice): constraint theory analysis via
  `analyze_from_bundle()` → PB/UN/SL lints

The only runtime *effects* from M1–M14 are:
1. **M7**: guard evaluation order in generated code (most selective first)
2. **Forward-Backward**: `#[inline]` / `#[cold]` annotations on generated
   functions based on hot-path analysis

**Automata composition (§18):** Purely compile-time. SFA intersection, AWA
quantifier construction, PATA recursive compilation, and multi-tape product
construction all happen during pipeline analysis. They produce intermediate
automata consumed by Stage 5 codegen.

#### Part III (§§19–27) — "Architecture and Operations"

**Part III is entirely compile-time.** No component in Part III produces
runtime artifacts directly.

| Component                                      | Section | Compile-time role                                         |
|------------------------------------------------|---------|-----------------------------------------------------------|
| All lints (SYM/MSO/PT/RA/MT/TW/PR/PB/UN/SL/LT) | §19     | Diagnostic messages emitted during `cargo build`          |
| Pipeline flow                                  | §20     | `thread::scope` parallel analysis of constraint theories  |
| Dispatch gating                                | §20     | `PredicateSignature` bits gate which analyses run         |
| Relation name heuristics                       | §20     | Keyword-based module activation (temporary)               |
| `theories {}` extension mechanism              | §21     | Data-driven ConstraintTheory wiring (replaces heuristics) |
| Gap 3: BehavioralPred parser                   | §22     | `guard(...)` syntax parsing during macro expansion        |
| Gap 3: QuantifiedFormula AST                   | §22     | FOL formula AST constructed at macro time                 |
| Gap 4: AcMatch codegen                         | §22     | Partition enumeration code generated at macro time        |

**Runtime artifacts from Part III** are generated code only:
- Gap 3: `evaluate_quantified()` calls in generated Comm rules
- Gap 4: `multiset_select()` calls in generated AC-match rules

### 14.3 Pipeline Flow with Compile/Run Boundary

```
COMPILE TIME (language! macro expansion + PraTTaIL pipeline)
════════════════════════════════════════════════════════════════════════

  ┌─────────────────────────────────────────────────────────────────┐
  │ §2  Parse surface syntax                                        │
  │     for (@x : forall y. (reachable(x,y) => safe(y)) <- ch) {P}  │
  │                                                                 │
  │     → PGuardedInput(ch, guard_scope, [preds], cont_scope)       │
  └──────────────────────────┬──────────────────────────────────────┘
                             │
  ┌──────────────────────────▼──────────────────────────────────────┐
  │ §10 Variable inference                                          │
  │     Extract free variables with natural categories:             │
  │     x: Name (from channel position), y: Proc (from body)        │
  │     Construct binder lists for both Scopes                      │
  └──────────────────────────┬──────────────────────────────────────┘
                             │
  ┌──────────────────────────▼──────────────────────────────────────┐
  │ §12 Pipeline Stage 1: Parse                                     │
  │     Guard predicate → WeightedMsoFormula AST                    │
  │     forall y. (reachable(x,y) => safe(y))                       │
  │     → ForallFirst { var: y, body: Or(NegAtomic("reach"), ...) } │
  └──────────────────────────┬──────────────────────────────────────┘
                             │
  ┌──────────────────────────▼──────────────────────────────────────┐
  │ §12 Pipeline Stage 2: Classify + Dispatch                       │
  │     classify_decidability() → T2 (runtime decidable)            │
  │     extract_features() → PredicateSignature(M1+M3+M5+M10)       │
  │     Activate only needed modules, ordered by cost               │
  └──────────────────────────┬──────────────────────────────────────┘
                             │
  ┌──────────────────────────▼──────────────────────────────────────┐
  │ §12 Pipeline Stage 3: Compile                                   │
  │     §15 BooleanAlgebra: build SFA from guard formula            │
  │     §16 ConstraintTheory: Presburger/Unification/Lattice check  │
  │     §17 M1: is_satisfiable() → SYM01 if dead guard              │
  │     §17 M3: AWA Q⊗ construction for ∀ quantifier                │
  │     §17 M5: PATA check if predicates are recursive (letprop)    │
  └──────────────────────────┬──────────────────────────────────────┘
                             │
  ┌──────────────────────────▼──────────────────────────────────────┐
  │ §12 Pipeline Stage 4: Optimize                                  │
  │     §15 SFA intersect + minimize for guard fusion               │
  │     §17 M7: selectivity estimation → evaluation order           │
  │     Forward-Backward: hot-path → #[inline], cold → #[cold]      │
  └──────────────────────────┬──────────────────────────────────────┘
                             │
  ┌──────────────────────────▼──────────────────────────────────────┐
  │ §12 Pipeline Stage 5: Codegen                                   │
  │     §19 Emit lints (SYM01–04, PB01–03, UN01–03, SL01–02, etc.)  │
  │     Generate guard evaluation functions as TokenStream          │
  │     Generate specialized Comm rules as Ascent clauses           │
  │     Generate match_pattern / match_pattern_name methods         │
  └──────────────────────────┬──────────────────────────────────────┘
                             │
═══════════════════ TokenStream boundary ═══════════════════════════
                             │
                             ▼
RUNTIME (generated Ascent fixpoint evaluation)
════════════════════════════════════════════════════════════════════════

  ┌──────────────────────────────────────────────────────────────────┐
  │ §6  Ascent rule fires: find PGuardedInput + POutput on same ch   │
  │     Construct received_name = NQuote(sent_proc)                  │
  └──────────────────────────┬───────────────────────────────────────┘
                             │
  ┌──────────────────────────▼───────────────────────────────────────┐
  │ §5  match_pattern_name(received_name, guard_body)                │
  │     Recursive first-order matching through constructors          │
  │     → Some(MatchBindings { name: [x→a], proc: [y→body] })        │
  │     → None: Comm rule does not fire                              │
  └──────────────────────────┬───────────────────────────────────────┘
                             │
  ┌──────────────────────────▼───────────────────────────────────────┐
  │ §8  Behavioral predicate evaluation                              │
  │     T2: relation(resolve_arg(0, σ), resolve_arg(1, σ))           │
  │         → O(1) hash lookup in Ascent relation                    │
  │     T2: guard_check(x) → inline range/SFA/register test          │
  │     T3: bounded_check(x, depth_limit) → BFS with counter         │
  │     T4: assert_pred(x) → true (trust)                            │
  └──────────────────────────┬───────────────────────────────────────┘
                             │
  ┌──────────────────────────▼───────────────────────────────────────┐
  │ §22 Quantified predicates (Gap 3)                                │
  │     QuantifiedFormula → evaluate_quantified(&formula, &lookup)   │
  │     ∀: gnot(∃y. ¬P(y)) via LogicStream fair search               │
  │     ∃: interleave domain search with bounded labeling            │
  │     ∃_{k}: collect_bounded(k) for T3 safety                      │
  └──────────────────────────┬───────────────────────────────────────┘
                             │
  ┌──────────────────────────▼───────────────────────────────────────┐
  │ §22 AC-matching (Gap 4) — if guard uses ac_match()               │
  │     multiset_select(&items, k, bound)                            │
  │     Enumerate partitions via LogicStream, collect first `bound`  │
  │     Each partition tested against guard pattern                  │
  └──────────────────────────┬───────────────────────────────────────┘
                             │
  ┌──────────────────────────▼───────────────────────────────────────┐
  │ §6  Two-pass substitution into continuation                      │
  │     Pass 1: multi_substitute_name(σ.names) — NVar replacements   │
  │     Pass 2: multi_substitute(σ.procs) — PVar replacements        │
  │     Passes are disjoint; order is irrelevant                     │
  └──────────────────────────┬───────────────────────────────────────┘
                             │
  ┌──────────────────────────▼───────────────────────────────────────┐
  │ §6  Result assembly                                              │
  │     PPar(rest ∪ {substituted_body}).normalize()                  │
  │     Consumed inp + out removed from bag; continuation inserted   │
  └──────────────────────────────────────────────────────────────────┘

════════════════════════════════════════════════════════════════════════
```

### 14.4 Evaluation Strategy by Decidability Tier

This matrix details the compile-time vs runtime behavior for each decidability
tier:

```
┌─────────┬─────────────────────────────────┬──────────────────────────────────────────┐
│  Tier   │  Compile-Time                   │  Runtime                                 │
├─────────┼─────────────────────────────────┼──────────────────────────────────────────┤
│   T1    │  Full evaluation → true/false   │  None (guard eliminated from codegen)    │
│         │  Dead-code elimination if false │  Zero overhead — as if guard was never   │
│         │  Lints: SYM01 if always-false   │  written                                 │
├─────────┼─────────────────────────────────┼──────────────────────────────────────────┤
│   T2    │  SFA compiled, determinized,    │  Guard function executed per receive:    │
│         │  minimized. Ascent join clauses │  - Range check: O(1) arithmetic          │
│         │  generated. Register automaton  │  - Relation lookup: O(1) hash probe      │
│         │  compiled if data equality      │  - Register machine: O(|value|)          │
│         │  needed. Selectivity estimated. │  - SFA table: O(|value|)                 │
│         │  Lints: SYM02-04, PB01-03,      │  Short-circuit: most selective first     │
│         │  UN01-03, SL01-02               │  (from compile-time M7 analysis)         │
├─────────┼─────────────────────────────────┼──────────────────────────────────────────┤
│   T3    │  Bounded automaton compiled.    │  Bounded iteration per receive:          │
│         │  Depth limit k fixed from       │  BFS/DFS with depth counter.             │
│         │  syntax (exists_{k=N}) or       │  Cost: O(k · |value|)                    │
│         │  inferred. Lints: MSO01-02      │  May return Unknown → Comm blocked       │
│         │  if bound seems insufficient    │  Configurable timeout as fallback        │
├─────────┼─────────────────────────────────┼──────────────────────────────────────────┤
│   T4    │  Lint MSO01 emitted (warning).  │  Trust user annotation: assert_pred()    │
│         │  Rocq certificate verified if   │  returns true unconditionally.           │
│         │  provided. No automaton built.  │  Optional runtime monitor for debugging. │
│         │  User must provide assert_pred  │  Cost: O(1) (no actual checking)         │
│         │  annotation or Rocq proof.      │  Correctness: user's responsibility      │
└─────────┴─────────────────────────────────┴──────────────────────────────────────────┘
```

### 14.5 Guard Selectivity Ordering (M7 Probabilistic)

When multiple guards protect the same channel, M7 estimates selectivity at
**compile time** from corpus training (`train_from_corpus()` via Baum-Welch EM)
and orders guards for short-circuit evaluation at **runtime** — most selective
guard is checked first, eliminating the most candidates earliest.

This is a case where compile-time analysis has a runtime *effect* (evaluation
order) without a runtime *component* (M7's code is not in the binary — only the
guard check ordering it determined is).

### 14.6 Components with Dual Compile-Time and Runtime Presence

Three components appear in both phases with different roles:

**LogicStream<T>:**
- **Compile time**: Used by `TheoryAlgebra<T>` for `label()`-based fair
  backtracking search when checking ConstraintTheory satisfiability. This
  supports the `UnificationTheory` which uses `label()` to enumerate
  unification alternatives.
- **Runtime**: Used by `evaluate_quantified()` for ∀/∃ guard predicate
  evaluation. `gnot()` implements ∀ as ¬∃¬, `interleave()` provides fair
  domain exploration, `collect_bounded()` enforces T3 depth limits.

**Unification (Martelli-Montanari):**
- **Compile time**: `UnificationTheory::propagate()` checks whether two patterns
  can unify (pattern overlap analysis, UN01–03 lints). Used by pipeline to
  detect ambiguous guard patterns.
- **Runtime**: If the language uses unification-based matching (e.g., MeTTa
  pattern matching), the generated code may call unification at runtime for
  pattern dispatch.

**Forward-Backward analysis:**
- **Compile time**: Identifies hot-path and cold-path guards via frequency
  analysis.
- **Runtime effect**: Hot-path guards are annotated `#[inline]`, cold-path
  guards are annotated `#[cold]`. The analysis code itself is not in the
  binary — only its annotations affect the compiler's optimization decisions.

### 14.7 What Does NOT Affect Runtime

The following infrastructure exists **exclusively** at compile time and produces
**zero runtime overhead** — no code, no data structures, no per-value cost:

- **All 14 automata modules** (M1–M14): Analysis only; automata are consumed
  by codegen and discarded
- **BooleanAlgebra trait and all implementations**: IntervalAlgebra,
  CharClassAlgebra, KatBooleanAlgebra, DispatchAlgebra, PresburgerAlgebra
- **ConstraintTheory trait and TheoryAlgebra bridge**: Used for satisfiability
  and entailment checking; results flow into lints and codegen decisions
- **SFA determinize/minimize/intersect/complement**: Guard automaton
  construction; the optimized automaton is compiled to code, then discarded
- **ProductAlgebra<A,B>**: Cross-domain constraint composition for analysis
- **Predicate dispatch controller**: Feature extraction + module activation
- **All 30+ lint codes**: Diagnostic messages emitted at `cargo build` time
- **Pipeline parallel analysis** (thread::scope): Concurrent CT analysis
- **Warshall transitive closure** (LatticeTheory): Subtype hierarchy analysis
- **Presburger NFA construction** (Bartzis-Bultan): Linear integer arithmetic
  decision procedure — automata built, queried, then discarded
- **Rocq formal proofs**: Verify properties of the analysis infrastructure
  itself; never part of any binary

---

## 15. The BooleanAlgebra Framework

### Motivation

All guard analysis — satisfiability, subsumption, overlap detection,
equivalence — reduces to operations over Boolean algebras. The
`BooleanAlgebra` trait provides the algebraic foundation for the entire
predicated types pipeline.

### The BooleanAlgebra Trait

A `BooleanAlgebra` is a structure `(P, ∧, ∨, ¬, ⊤, ⊥)` satisfying
De Morgan's laws, distributivity, and complementation:

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

### Built-in Algebras

```
BooleanAlgebra trait
├── IntervalAlgebra ──── Domain: i64 ranges          (numeric guards)
├── CharClassAlgebra ─── Domain: Unicode chars        (structural patterns)
├── KatBooleanAlgebra ── Domain: propositional atoms  (behavioral predicates)
├── DispatchAlgebra ──── Domain: module signatures    (14-bit dispatch)
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

### Symbolic Finite Automata

A symbolic finite automaton (SFA) generalizes classical finite automata by
labeling transitions with predicates from a `BooleanAlgebra` instead of
concrete alphabet symbols:

```
SFA = (Q, q₀, F, δ)
  where δ ⊆ Q × P × Q
        P is a BooleanAlgebra predicate
```

The key advantage: SFAs can operate over infinite alphabets (e.g., all
integers, all Unicode strings) without materializing the alphabet. Predicate
intersection, union, and complement map to the corresponding Boolean algebra
operations.

### Minterm-Based Determinization

Determinization of SFAs uses **minterms** — maximal satisfiable conjunctions
of predicate atoms and their negations. For a set of predicates
`{φ₁, φ₂, …, φₙ}`, the minterms partition the domain into equivalence
classes where all predicates evaluate uniformly:

```
minterm(S, S') = ⋀_{φ ∈ S} φ ∧ ⋀_{φ ∈ S'} ¬φ
  where S ⊆ atoms, S' = atoms ∖ S, is_satisfiable(minterm(S, S'))
```

This avoids enumerating the infinite domain while guaranteeing a correct
partitioning for determinization.

### ProductAlgebra

`ProductAlgebra<A, B>` composes two independent `BooleanAlgebra` instances
into their Cartesian product:

```
ProductAlgebra<A, B>.is_satisfiable((a, b)) = A.is_satisfiable(a) ∧ B.is_satisfiable(b)
```

This enables mixed-domain constraints, e.g.,
`ProductAlgebra<PresburgerAlgebra, LatticeTheory>` for guards combining
numeric and type hierarchy constraints.

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
with provably decidable decision procedures — no external SMT dependency.

### Why Automata Instead of SMT

| Criterion     | SMT (Z3/CVC5)                          | Constraint Theory Suite         |
|---------------|----------------------------------------|---------------------------------|
| External deps | z3-sys (~1.5GB), platform build        | Zero — pure Rust                |
| Deployment    | Shared lib, platform-specific          | Cross-platform, WASM-compatible |
| Performance   | FFI call per check-sat, ~1ms startup   | In-process, cacheable automata  |
| Formal basis  | Solver completeness as black-box       | Provably decidable (Büchi 1960) |
| Integration   | SMT-LIB2 serialization + model parsing | Direct `BooleanAlgebra` impl    |
| Scope match   | Over-powered (arrays, UF, bitvectors)  | Exact fit for guard predicates  |
| Extensibility | Fixed theory set, FFI boundary         | Open `ConstraintTheory` trait   |

### Architecture

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

### The ConstraintTheory Trait

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

- **Decidable theories** (Presburger, Lattice): `label()` returns
  `LogicStream::empty()` — propagation alone determines satisfiability.
- **Search-based theories** (Unification): `label()` returns search choices
  that `LogicStream::interleave` explores fairly.

### The TheoryAlgebra Bridge

`TheoryAlgebra<T: ConstraintTheory>` wraps any `ConstraintTheory` into a
`BooleanAlgebra`:

```
is_satisfiable(φ) ≡ propagate(∅, φ) ≠ ⊥ ∨ label_search(store) succeeds
```

For decidable theories, no search is needed. For search-based theories, LogicT
provides bounded fair backtracking.

### LogicStream — Fair Backtracking Monad

`LogicStream<T>` implements the `msplit`-based LogicT of Kiselyov et al.
(ICFP 2005). It uses an explicit `VecDeque`-based branch queue for
round-robin fair scheduling:

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

**Fairness guarantee:** `interleave(a, b)` alternates between branches from
`a` and `b`, ensuring both are explored infinitely often. This prevents
starvation when one branch produces results faster than the other.

### PresburgerAlgebra — Multi-Variable Linear Integer Arithmetic

**Theory:** Presburger arithmetic is the first-order theory of the natural
numbers with addition: `Th(ℤ, +, <, 0, 1)`. Büchi (1960) proved that every
Presburger formula defines a regular language over `{0,1}ᵏ`, providing an
automata-theoretic decision procedure.

**NFA Construction (Bartzis-Bultan):** For an atomic constraint
`Σ aᵢ·xᵢ ≤ b` over k variables:

- **Alphabet:** `{0,1}ᵏ` — one bit per variable, read LSB-first
- **States:** Remainder values tracking `r = ⌊(b - Sⱼ) / 2ʲ⌋`
- **Transition:** `r' = ⌊(r - Σ aᵢ · dᵢ) / 2⌋`
- **Acceptance:** After `w` bits, accept iff `r ≥ 0`
- **State bound:** O((Σ|aᵢ| + |b|) · 2ᵏ)

**Dual implementation:** Direct `BooleanAlgebra` (fast path for compile-time
analysis) + `ConstraintTheory` (validation path via LogicT integration).

**Boolean operations:** Intersection (product construction), union (product +
accept union), complement (depth-tracked determinization + terminal flip),
existential projection (drop bit dimension, merge transitions).

### UnificationTheory — Structural Unification

**Algorithm:** Martelli & Montanari (1982) stack-based unification:

```
unify(f(t₁,…,tₙ), f(s₁,…,sₙ)) = compose(unify(t₁,s₁), …, unify(tₙ,sₙ))
```

| Case                                | Action                            |
|-------------------------------------|-----------------------------------|
| `Var(x) ≡ Var(x)`                   | Skip (trivial identity)           |
| `Var(x) ≡ t`                        | Occurs check; bind `x ↦ t`        |
| `App(f, args₁) ≡ App(f, args₂)`     | Decompose: push `argsᵢ₁ ≡ argsᵢ₂` |
| `App(f, _) ≡ App(g, _)` where f ≠ g | Constructor clash → failure       |

**Term representation:**

```rust
pub enum TermExpr {
    Var(usize),
    Const(String),
    App { head: String, args: Vec<TermExpr> },
}
```

**Subsumption:** `σ₁ ⊑ σ₂` iff `∃θ. σ₂ = θ ∘ σ₁`

**Applications:** MeTTa pattern matching, Rholang quoted process patterns.

### LatticeTheory — Subtype Lattice

**Theory:** A finite partially ordered set of types with:
- **Subtyping:** `a ≤ b` (a is subtype of b)
- **Join/LUB:** smallest common supertype — `a ≤ a ⊔ b` and `b ≤ a ⊔ b`
- **Meet/GLB:** largest common subtype — `a ⊓ b ≤ a` and `a ⊓ b ≤ b`
- **Lattice order:** `a ≤ b ⟺ a ⊔ b = b`

**Implementation:**
- Subtype DAG constructed from explicit edges
- Warshall's transitive closure: O(n³) once, cached with dirty-flag
  invalidation
- LUB/GLB computed lazily and cached
- Cycle detection: `a ≤ b ≤ a` with `a ≠ b` represents type equivalence

**Applications:** MeTTa `(:< sub super)`, Rholang bundle capabilities.

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

### Rocq Formal Verification

The constraint theory suite is backed by Rocq proofs:

| Proof File                                          | Theorems                                                                                   | Lines |
|-----------------------------------------------------|--------------------------------------------------------------------------------------------|-------|
| `formal/rocq/logict/LogicTFairness.v`               | 23 theorems: msplit laws, interleave fairness, mplus/once/gnot/ifte properties             | 447   |
| `formal/rocq/presburger/PresburgerBooleanAlgebra.v` | 22 theorems: Boolean algebra axioms, De Morgan, NFA bridge correctness                     | 352   |
| `formal/rocq/unification/UnificationSoundness.v`    | 21 theorems: unification soundness, occurs check, clash unsatisfiability, TheoryAlgebra BA | 577   |
| `formal/rocq/lattice/LatticeTheoryCorrectness.v`    | 20 theorems: closure correctness, join/meet commutativity/associativity/absorption         | 480   |

All proofs have zero `Admitted` or `Axiom` statements.

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

---

## 17. The Automata Modules (M1–M14)

Each of the 14 automata modules contributes to the predicated types pipeline.
The predicate dispatch controller determines the minimal set needed per guard.

> **Note:** All 14 automata modules are **compile-time analysis only**. They
> execute during `language!` macro expansion to analyze guards, detect issues,
> and inform codegen decisions. None of these modules or their automata appear
> in the generated binary. The only runtime effects are indirect: M7's
> selectivity analysis determines guard evaluation order, and Forward-Backward
> analysis annotates generated functions with `#[inline]`/`#[cold]`. See §14
> for details.

### Module Table

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
├──────────────────────┼──────────────────────────────────────────────────┤
│ M9  Multiset         │ Cardinality predicates: count(chan) >= 3.        │
│                      │ PPar analysis with HashBag multiplicities.       │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M10 W. MSO           │ THE specification language. User syntax /\, \/,  │
│                      │ ~, forall, exists IS weighted MSO.               │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M11 W. Two-Way       │ Cross-channel constraint propagation.            │
│                      │ Backward constraints for join reordering.        │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M12 Linear Arith.    │ Presburger arithmetic guards. NFA-based          │
│                      │ decision procedure for Σ aᵢ·xᵢ ≤ b.              │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M13 Unification      │ Structural pattern unification. Martelli-        │
│                      │ Montanari for MeTTa/Rholang pattern overlap.     │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M14 Subtype Lattice  │ Type hierarchy constraints. Warshall closure     │
│                      │ for MeTTa (:< sub super).                        │
└──────────────────────┴──────────────────────────────────────────────────┘
```

### Predicate Dispatch Controller

The controller determines the minimal module set per guard:

1. **Feature extraction:** `extract_features(expr, ctx) → PredicateProfile`
   in O(|AST|)
2. **Signature computation:** Profile → 14-bit `PredicateSignature(u16)`
   (one bit per module)
3. **Cost-ordered execution:** Modules ordered by `estimated_cost()`:
   M1/M10 = 1, M6/M9 = 2, M2/M3 = 3, M4/M5 = 4, M7/M8 = 5, M11 = 6
4. **Early termination:** Skip modules not in signature; cheap modules
   resolve before expensive ones fire

**Concrete example:** Guard `x == fresh_name /\ count(ch) >= 2` activates
only M1+M6+M9+M10, skipping 10 modules. The dispatch controller extracts
features (equality test → M6, cardinality → M9) and computes the 4-bit
signature, executing in cost order: M1 (satisfiability), M10
(classification), M6 (register analysis), M9 (multiset check).

### Always-On Analysis Modules

These modules run on every guard regardless of the predicate signature:

| Module               | Guard-Related Role                                                 |
|----------------------|--------------------------------------------------------------------|
| **WPDS**             | Stack-aware reachability for guard evaluation chains               |
| **CEGAR**            | Iterative refinement: Boolean→Counting→Tropical abstraction ladder |
| **Safety**           | Guard completeness: does every input match ≥1 guard?               |
| **Algebraic**        | Path expressions summarize guard evaluation CFG                    |
| **Newton**           | Accelerated fixpoint: h+1 iterations for idempotent semirings      |
| **Forward-Backward** | Hot-path guards → `#[inline]`, cold → `#[cold]`                    |

### Feature-Gated Analysis Modules

| Module           | Guard-Related Role                                           |
|------------------|--------------------------------------------------------------|
| **TRS**          | Guard-conditional rewrite confluence + termination           |
| **Nominal**      | Name-binding safety, alpha-equivalence in guard patterns     |
| **Petri**        | Deadlock analysis for guarded communication                  |
| **KAT**          | Guard flow equivalence, Hoare triples                        |
| **CRA**          | Quantitative guard cost metering                             |
| **Morphism**     | Translation verification between guard formalisms            |
| **Provenance**   | Derivation tracking through guard evaluation                 |
| **Proof Output** | Correctness certificates (confluence + termination + safety) |

---

## 18. Automata Composition for First-Order Logic

### Composition Operators

The automata compose for complete first-order logic:

| Operator                       | Compilation                                       |
|--------------------------------|---------------------------------------------------|
| Conjunction (`/\`)             | SFA intersection → minimize                       |
| Disjunction (`\/`)             | SFA union → minimize                              |
| Negation (`~`)                 | SFA complement                                    |
| Universal (`forall`)           | AWA Q⊗ branching: all successors must accept      |
| Existential (`exists`)         | AWA Q⊕ branching: at least one accepts            |
| Implication (`=>`)             | Desugar to `~a \/ b`, then SFA ops                |
| Recursive (`letprop`)          | Mu-calculus → PATA → Zielonka solver              |
| Data equality (`x == y`)       | Register automaton TestEq                         |
| Freshness (`fresh(x)`)         | Register automaton TestFresh                      |
| Cardinality (`count(ch) >= k`) | Multiset automaton constraint check               |
| Multi-channel                  | Multi-tape product + two-way backward propagation |
| Infinite behavior              | Buchi acceptance condition                        |

### Formal Definitions

```
Universal:   ⟦∀y. φ(y)⟧ = Q⊗     all successors accept; weight = ⊗
Existential: ⟦∃y. φ(y)⟧ = Q⊕     at least one accepts; weight = ⊕
Implication: ⟦φ ⇒ ψ⟧   = ⟦¬φ ∨ ψ⟧
Recursive:   ⟦letprop P x = ∀x'. ¬(x →* x')⟧ = νX. □_{→*}(¬X)
```

### End-to-End Trace

Guard: `forall y. (reachable(x, y) => safe(y))`

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

### Automata Role Matrix

| Automaton        | Phase 0 | Phase 1  |   Phase 2   |   Phase 3    | Phase 4 |   Phase 5    | FOL Feature              |
|------------------|:-------:|:--------:|:-----------:|:------------:|:-------:|:------------:|--------------------------|
| NFA/DFA          |         | tokenize |             |              |         |              | Token recognition        |
| FIRST/FOLLOW     |         |          |  dispatch   |              |         |              | Parse prediction         |
| Prediction WFST  |         |          |   weights   |              |         |              | Disambiguation           |
| Decision Tree    |         |          | prefix trie |              | codegen |              | Parse dispatch           |
| ContextWeight    |         |          |  rule bits  |              | filter  |              | Context narrowing        |
| WPDS             |         |          | stack syms  | reachability |         |  dead rules  | Stack analysis           |
| Token Lattice    |         |          |  ambiguity  |              |         |              | Lexical ambiguity        |
| M1 Symbolic      |         |          |             | SFA compile  |         |   disambig   | Propositional, ranges    |
| M2 Buchi         |         |          |             |  ∞-behavior  |         |              | Liveness (∞ quantifiers) |
| M3 AWA           |         |          |             |   ∀/∃ eval   |         |              | First-order quantifiers  |
| M4 VPA           |         |          |             |   nesting    |         |              | Well-formed nesting      |
| M5 PATA          |         |          |             |  recursive   |         |              | Mu-calculus, letprop     |
| M6 Register      |         |          |             |   data eq    |         | dead binders | Equality, fresh          |
| M7 Probabilistic |         |          |             | selectivity  |         |   entropy    | Performance              |
| M8 Multi-Tape    |         |          |             |   multi-ch   |         |  indep cats  | Multi-channel            |
| M9 Multiset      |         |          |             | cardinality  |         |              | count/size               |
| M10 MSO          |         |          |             |   classify   |         |              | Spec language            |
| M11 Two-Way      |         |          |             |   cross-ch   |         |              | Backward constraints     |
| M12 Presburger   |         |          |             |  arithmetic  |         |              | Linear integer           |
| M13 Unification  |         |          |             |   patterns   |         |              | Structural unify         |
| M14 Lattice      |         |          |             |  subtyping   |         |              | Type hierarchy           |

> **Citations:**
>
> - Droste, M. & Gastin, P. "Weighted Automata and Weighted Logics."
>   *Theoretical Computer Science*, 380:69–86, 2007.
> - Emerson, E. A. & Jutla, C. S. "Tree Automata, Mu-Calculus and
>   Determinacy." *Proceedings of FOCS*, 1991.
> - Kostolanyi, A. & Misun, F. "Alternating Weighted Automata over
>   Commutative Semirings." *Theoretical Computer Science*, 740:1–27, 2018.

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

## 20. Pipeline Flow for Constraint Theories

### Structural Analysis Pattern

Like all 22+ existing `analyze_from_bundle()` functions (e.g., `symbolic.rs`,
`nominal.rs`, `buchi.rs`), constraint theory analyses extract information
from `all_syntax: &[(String, String, Vec<SyntaxItemSpec>)]` without requiring
explicit guard fields on `RuleSpec`:

| Theory      | Looks for                                            | Extracts                                    |
|-------------|------------------------------------------------------|---------------------------------------------|
| Presburger  | Comparison terminals (`<`, `>=`, etc.) near captures | `LinearConstraint` → NFA satisfiability     |
| Unification | Same-category rules with overlapping structures      | `TermExpr` → Martelli-Montanari unification |
| Lattice     | Category delegation patterns (A references only B)   | Subtype edges → DAG + Warshall closure      |

### Parallel Analysis via thread::scope

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

### Dispatch Gating

When `predicate-dispatch` is enabled, `classify_grammar()` in
`predicate_dispatch.rs` sets `PredicateSignature` bits M12, M13, M14 based
on grammar structure heuristics. Each analysis checks
`dispatch_plan.requires(ModuleId::...)` before running. Grammars without
numeric terminals skip Presburger; grammars without overlapping patterns skip
Unification; grammars without category delegation skip Lattice.

### Relation Name Heuristics (First Attempt — To Be Superseded)

Module activation currently uses **hardcoded keyword lists** in
`predicate_dispatch.rs` to classify `PredicateExpr::Relation` names into
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

**This heuristic approach should be superseded** by new `language!` macro
features — specifically the `theories { }` block (§21) — that make dispatch
data-driven. The spec author will explicitly declare which `ConstraintTheory`
implementations handle which guards, eliminating keyword guessing entirely
and enabling arbitrary user-defined constraint domains to participate in
predicate dispatch without heuristic support.

---

## 21. ConstraintTheory Extension Mechanism

### Three-Layer Design

The constraint theory system is designed for extension. Users add new theories
through three layers:

**Layer 1 — Rust Implementation.** Implement `ConstraintTheory`:

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

**Layer 2 — `language!` Declaration** (future):

```rust
language! {
    name: RholangLike,
    types { Proc, Name, ... },
    theories {
        resources: ResourceTheory,      // user-defined
        arithmetic: PresburgerAlgebra,  // built-in fast path
        patterns: UnificationTheory,    // built-in (LogicT search)
        types: LatticeTheory,           // built-in (decidable)
    }
    // ...
}
```

**Layer 3 — Automatic Pipeline Wiring** (future):

1. `language!` parses `theories { }` → `Vec<TheoryRegistration>`
2. `classify_grammar()` sets `PredicateSignature` bits per registered theory
3. `extract_features()` maps guards to registered theories by declaration
4. Pipeline runs `TheoryAlgebra<T>::is_satisfiable()` for analysis
5. Codegen emits theory-aware optimizations

This replaces the heuristic keyword lists with explicit, data-driven dispatch.

---

## 22. Deferred Extensions

### Gap 3: Quantified Behavioral Predicates — IMPLEMENTED

**Problem:** Current behavioral predicates are existential queries ("does
tuple exist in relation?"). Full FOL needs universal quantification and
nested quantification.

**Infrastructure available:** LogicT provides `gnot` (negation as failure for
`¬∃`), `ifte`/`once` (committed choice for `∃!`), and `fair_conjoin` (fair
nested quantification `∀x.∃y.P(x,y)`).

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

Components added:

| Component                                                 | File                         | Lines |
|-----------------------------------------------------------|------------------------------|-------|
| `QuantifiedFormula` enum (FOL AST)                        | `prattail/src/logict.rs`     | ~170  |
| `QuantifiedDomain` / `QuantifiedArg` types                | `prattail/src/logict.rs`     | ~30   |
| `evaluate_quantified()` evaluator                         | `prattail/src/logict.rs`     | ~80   |
| `BehavioralPred` / `PredArg` / `Quantifier` types         | `macros/src/ast/language.rs` | ~180  |
| `BehavioralPred::to_quantified_formula()` codegen         | `macros/src/ast/language.rs` | ~100  |
| `Premise::BehavioralGuard` / `Condition::BehavioralGuard` | `macros/src/ast/language.rs` | ~10   |
| `TermParam::GuardBody` variant                            | `macros/src/ast/grammar.rs`  | ~5    |
| Predicate sublanguage parser (`parse_behavioral_pred`)    | `macros/src/ast/language.rs` | ~180  |
| Guarded Comm rule codegen                                 | `macros/src/logic/rules.rs`  | ~80   |
| Tests (22 new)                                            | `prattail/src/logict.rs`     | ~350  |

Guard syntax (inside `language!` macro):
```text
guard(forall y in nodes. (reachable(x, y) => safe(y)))
guard(exists_{k=100} y in terms. (reachable(x, y) && halts(y)))
guard(~safe(x) || connected(x, z))
guard(path(x, y) && connected(y, z))
```

Operators: `&&` (conjunction), `||` (disjunction), `!`/`~` (negation), `=>` (implication).

The cost-benefit framework assigns cost 20 to `BehavioralGuard` conditions,
ensuring they are evaluated last in BCG01 fail-fast ordering.

### Gap 4: AC-Matching for Collections — IMPLEMENTED

**Problem:** Collection patterns (`{P | Q}` in guards) require
associative-commutative matching — the `PPar` bag is unordered, so matching
`{x | y}` against `{A | B | C}` requires trying all 2-element subsets.

**Solution:** Multiplicity-aware partition enumeration via `LogicStream`.

- `multiset_partitions()` in `prattail/src/logict.rs`: lazily enumerates all
  ways to select K elements from a multiset, producing
  `LogicStream<MultisetPartition<T>>`. Uses `interleave()` for fair exploration
  across branches. Generic over element type.
- `multiset_select()`: convenience wrapper with `collect_bounded()` for T3 safety.
- `BehavioralPred::AcMatch` variant in `macros/src/ast/language.rs`: parsed from
  `guard(ac_match(bag, {x, y, ...rest}))` syntax.
- Codegen in `macros/src/logic/rules.rs`: generates partition enumeration code
  through `Condition::BehavioralGuard` pipeline. Cost 25 (higher than standard
  behavioral guards at 20).
- 16 unit tests covering edge cases, invariants, fairness, and complement symmetry.
- Criterion benchmarks in `prattail/benches/bench_logict.rs`.

### Gap 5: Refinement Types & Pluggable Type System Framework — IMPLEMENTED

**Problem:** For truly predicated types (types depending on values), the
system needs refinement types: `{ x: Int | x > 0 }` — types that combine
base type subtyping with predicate constraints on values. More broadly, the
system needs a pluggable type system framework so that arbitrary type
disciplines (Rholang structural, MeTTa gradual, refinement, HM, dependent,
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

#### Architecture

```
                   ┌──────────────────────────────────────────────────┐
                   │             TypeSystem Trait                     │
                   │                                                  │
                   │  check(env, term, type) → bool                   │
                   │  infer(env, term) → Vec<Type>                    │
                   │  is_subtype(env, sub, sup) → bool                │
                   │  join(env, a, b) → Option<Type>                  │
                   │  meet(env, a, b) → Option<Type>                  │
                   │  extend(env, var, type) → TypeEnv                │
                   │  is_inhabited(env, type) → bool                  │
                   │  top() → Option<Type>                            │
                   │  bottom() → Option<Type>                         │
                   └────────────┬─────────────────────────────────────┘
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
    └────────────────┘  └────────────────┘  └─────────────────────┘
              │                 │                      │
              └─────────────────┼──────────────────────┘
                                │
                 ┌──────────────▼─────────────────────┐
                 │    Pipeline Integration            │
                 │                                    │
                 │  TypeSystemAnalysis (compile-time) │
                 │  Lints: RT01–RT06                  │
                 │  Codegen: runtime type checks      │
                 └────────────────────────────────────┘
```

#### TypeSystem Trait

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

#### TypeSystemAlgebra Bridge

`TypeSystemAlgebra<S>` bridges `TypeSystem` to `BooleanAlgebra`, analogous
to `TheoryAlgebra<T>` for `ConstraintTheory`. This enables SFA-based
analysis of type predicates: satisfiability (`is_inhabited`), subsumption
(`is_subtype`), and overlap (intersection non-emptiness) all reduce to
BooleanAlgebra operations.

#### Refinement Types

A refined type `{ x: T | P(x) }` combines:
- A **base type** `T` from a `TypeSystem S` (e.g., `Int` from `LatticeTypeSystem`)
- A **predicate** `P` from a `ConstraintTheory T` (e.g., `x > 0` from Presburger)

Subtyping rule:
```
{ x: S | P(x) } <: { x: T | Q(x) }
  iff  S <: T   (base subtype via TypeSystem)
  AND  ∀x. P(x) ⟹ Q(x)  (predicate entailment via ConstraintTheory)
```

Inhabitedness: `{ x: T | P(x) }` is inhabited iff `T` is inhabited AND
`P` is satisfiable (checked via `TheoryAlgebra::is_satisfiable()`).

#### Set-Theoretic Types

CDuce/XDuce-style types where types are sets of values:
- **Union**: `S ∪ T` — values in S or T (or both)
- **Intersection**: `S ∩ T` — values in both S and T
- **Negation**: `¬S` — values not in S
- **Subtype**: `S <: T` iff `L(A_S) ⊆ L(A_T)` iff `L(A_S ∩ ¬A_T) = ∅`

Modeled as regular tree languages via `WeightedTreeAutomaton<BooleanWeight>`:
states = types, transitions = constructor rules, subtyping = language
inclusion (decidable via intersection + complement + emptiness).

#### Surface Syntax

Refinement types declared inline in the `types { ... }` block:

```rust
types {
    Proc { ... }
    Name { ... }
    Int:i64 { ... }
    PosInt = { x: Int | x > 0 };
    SafeProc = { p: Proc | forall y in nodes. (reachable(p, y) => safe(y)) };
    NonEmpty = { b: HashBag(Proc) | count(b) >= 1 };
}
```

Refinement predicates support:
- **Linear arithmetic**: `a₁*x₁ + a₂*x₂ + ... ⊕ c` (Presburger)
- **Relation queries**: `R(args)` (behavioral)
- **Quantified formulas**: `forall`/`exists` with optional domain and bound
- **Boolean combinators**: `&&`, `||`, `!`/`~`, `=>`
- **Term comparison**: `==`, `!=`

Guards referencing refinement types:
```
for (@x : PosInt <- ch) { P }
```
generates conjunction of structural match AND refinement predicate check.

#### Predicate Lowering

Each `RefinementPredicate` is classified into a `ConstraintDomain`:
- **Presburger** — pure linear arithmetic → Presburger NFA
- **Lattice** — pure subtype checks → LatticeTheory
- **Behavioral** — relation queries / quantifiers → LogicT evaluation
- **Unification** — structural term patterns → Martelli-Montanari
- **Product** — mixed domain → ProductAlgebra composition

The classified predicate is lowered to the appropriate `ConstraintTheory`
representation for compile-time analysis and runtime codegen.

#### Pipeline Integration

`analyze_from_bundle()` extended with refinement type analysis:
1. Build `LatticeTypeSystem` from categories in `LanguageSpec::types`
2. For each refinement type, classify predicate domain
3. Check inhabitedness (RT01), tautology (RT02), pairwise intersection (RT03),
   pairwise subtyping (RT04), decidability tier (RT05), name shadowing (RT06)
4. Use `TypeSystemAlgebra<S>` for SFA-based dispatch analysis when multiple
   refinement types refine the same base type

#### Lints

| Code | Severity | Description                                                          |
|------|----------|----------------------------------------------------------------------|
| RT01 | Warning  | Refinement predicate is unsatisfiable: `{ x: Int \| x > 0 ∧ x < 0 }` |
| RT02 | Note     | Refinement equivalent to base type: `{ x: Int \| true }`             |
| RT03 | Warning  | Refinement types have empty intersection                             |
| RT04 | Note     | Refinement subtype detected: `StrictPosInt <: PosInt`                |
| RT05 | Note     | Predicate decidability tier classification (T1–T4)                   |
| RT06 | Warning  | Refinement type shadows base type (same name)                        |

#### Codegen

For each refinement type `PosInt = { x: Int | x > 0 }`, generated code:
```rust
// Ascent relation for refinement membership
relation is_refined_PosInt(Int);

// Population rule: base type membership + predicate check
is_refined_PosInt(x) <--
    int(x),         // base type (already exists)
    if *x > 0;      // predicate (inline for simple Presburger)
```

For behavioral predicates (quantified):
```rust
is_refined_SafeProc(p) <--
    proc(p),
    if { evaluate_quantified(&formula, &lookup) };
```

#### Compile-Time vs Runtime Classification

All `TypeSystem` trait implementations and analysis infrastructure are
**compile-time only** — they execute during `language!` macro expansion
and produce zero runtime overhead:

| Component                     | Compile-Time | Runtime   | Notes                                          |
|-------------------------------|--------------|-----------|------------------------------------------------|
| `TypeSystem` trait + impls    | ✓            |           | Abstract interface + 3 impls in `prattail`     |
| `TypeSystemAlgebra<S>` bridge | ✓            |           | TypeSystem → BooleanAlgebra adapter            |
| `RefinementPredicate` parser  | ✓            |           | Surface syntax parsing during macro expansion  |
| Predicate classification      | ✓            |           | `classify()` → ConstraintDomain                |
| Inhabitedness checking        | ✓            |           | `is_inhabited()` via TheoryAlgebra             |
| Subtype analysis              | ✓            |           | `is_subtype()` via base + predicate entailment |
| SFA dispatch analysis         | ✓            |           | SFA intersection for disjointness checking     |
| Lints RT01–RT06               | ✓            |           | Diagnostic messages at `cargo build` time      |
| Tree automaton inclusion      | ✓            |           | Set-theoretic subtype decisions                |
| `is_refined_*` relation       | codegen      | per-tuple | One Ascent relation per refinement type        |
| Predicate evaluation          | codegen      | per-tuple | Inline arith (O(1)) or LogicT (O(domain))      |
| Substitution propagation      | codegen      | per-fire  | Evaluate predicate on substituted value        |

**What does NOT affect runtime:**
- `TypeSystem` trait and all implementations (`LatticeTypeSystem`,
  `RefinementTypeSystem`, `SetTheoreticTypeSystem`)
- `TypeSystemAlgebra`, `ProductAlgebra` bridges
- Pipeline lints (RT01–RT06)
- SFA dispatch analysis
- Tree automaton emptiness/inclusion checks

**What affects runtime:**
- One `is_refined_*` Ascent relation per refinement type (per-tuple cost)
- Predicate evaluation in guard position (per-Comm cost, same as behavioral)
- Substitution propagation (per-fire cost, same as structural)

#### Infrastructure Available

| Component                     | Location                                 | Status   |
|-------------------------------|------------------------------------------|----------|
| `ConstraintTheory` trait      | `prattail/src/logict.rs`                 | COMPLETE |
| `TheoryAlgebra<T>` bridge     | `prattail/src/logict.rs`                 | COMPLETE |
| `BooleanAlgebra` trait        | `prattail/src/symbolic.rs`               | COMPLETE |
| `ProductAlgebra<A,B>`         | `prattail/src/symbolic.rs`               | COMPLETE |
| `SymbolicAutomaton<A>` (SFA)  | `prattail/src/symbolic.rs`               | COMPLETE |
| `LatticeTheory`               | `prattail/src/lattice_theory.rs`         | COMPLETE |
| `UnificationTheory`           | `prattail/src/unification.rs`            | COMPLETE |
| `PresburgerTheory`            | `prattail/src/presburger.rs`             | COMPLETE |
| `WeightedTreeAutomaton<W>`    | `prattail/src/tree_automaton.rs`         | COMPLETE |
| `IntervalAlgebra`             | `prattail/src/symbolic.rs`               | COMPLETE |
| `TypeExpr` AST                | `macros/src/ast/types.rs`                | COMPLETE |
| `BehavioralPred` + codegen    | `macros/src/ast/language.rs`, `rules.rs` | COMPLETE |
| `QuantifiedFormula` evaluator | `prattail/src/logict.rs`                 | COMPLETE |
| `LanguageSpec`                | `prattail/src/lib.rs`                    | COMPLETE |
| Pipeline + lints              | `prattail/src/pipeline.rs`, `lint.rs`    | COMPLETE |

#### Feature Gating

```toml
type-system = ["logict", "lattice-theory"]
set-theoretic-types = ["type-system"]
predicated-types = [ ..., "type-system", "set-theoretic-types" ]
full-analysis = [ ..., "type-system", "set-theoretic-types" ]
```

#### Implementation Plan

11 sprints (RT1–RT11) implementing the framework incrementally:

| Sprint | Goal                                                           | Lines | Dependencies  |
|--------|----------------------------------------------------------------|-------|---------------|
| RT1    | `TypeSystem` trait + `LatticeTypeSystem` + `TypeSystemAlgebra` | ~350  | None          |
| RT2    | `RefinementTypeSystem<S, T>`                                   | ~400  | RT1           |
| RT3    | `SetTheoreticTypeSystem` (tree automata)                       | ~400  | RT1           |
| RT4    | AST + parsing for refinement types                             | ~250  | None          |
| RT5    | Predicate lowering + classification                            | ~200  | RT4           |
| RT6    | Bridge to PraTTaIL pipeline (`RefinementTypeSpec`)             | ~150  | RT4, RT5      |
| RT7    | Pipeline analysis + lints RT01–RT06                            | ~300  | RT1, RT2, RT6 |
| RT8    | Codegen — runtime refinement checking                          | ~250  | RT4, RT5, RT7 |
| RT9    | Substitution propagation                                       | ~150  | RT8           |
| RT10   | SFA integration for type dispatch                              | ~200  | RT2, RT7      |
| RT11   | Documentation + benchmarks                                     | ~200  | All           |

Dependency graph:
```
RT1 (TypeSystem trait + LatticeTypeSystem)
  │
  ├──→ RT2 (RefinementTypeSystem<T>)
  │       │
  │       ├──→ RT7 (Pipeline + Lints)
  │       │       │
  │       │       └──→ RT8 (Codegen)
  │       │               │
  │       │               └──→ RT9 (Substitution)
  │       │
  │       └──→ RT10 (SFA dispatch)
  │
  ├──→ RT3 (SetTheoreticTypeSystem)
  │
  └──→ RT4 (AST + Parsing) ────────────────── (no deps)
          │
          └──→ RT5 (Lowering + Classification)
                  │
                  └──→ RT6 (Pipeline bridge)
                          │
                          └──→ RT7
RT11 (Docs + Benchmarks) ← all
```

Critical path: RT1 → RT2 → RT7 → RT8 → RT9 → RT11

**All 11 sprints COMPLETE (2026-03-14).** Implementation summary:
- `prattail/src/type_system.rs`: TypeSystem trait + 3 implementations + TypeSystemAlgebra + dispatch analysis (~2400 lines)
- `macros/src/ast/language.rs`: RefinementTypeDef parser, RefinementPredicate AST, ConstraintDomain classification
- `macros/src/logic/rules.rs`: Refinement codegen (relations, population rules, guard generation, substitution propagation)
- `macros/src/logic/relations.rs`: `is_refined_*` relation declarations + extraction
- `prattail/src/pipeline.rs`: `analyze_refinement_types()` + `RefinementAnalysisResult` + dispatch integration
- `prattail/src/lint.rs`: RT01–RT06 lint functions (9 tests)
- `prattail/src/cost_benefit.rs`: `RefinementTypeCheck` optimization gate
- `prattail/src/lib.rs`: `RefinementTypeSpec` + `RefinementPredKind` pipeline types
- Design doc: `prattail/docs/design/type-system-framework.md`
- Diagnostic pages: `prattail/docs/diagnostics/refinement/RT01.md`–`RT06.md`
- Benchmarks: `prattail/benches/bench_type_system.rs` (feature-gated `type-system`)

#### References

- Rondon, P., Kawaguchi, M., & Jhala, R. (2008). "Liquid Types." PLDI 2008.
- Freeman, T. & Pfenning, F. (1991). "Refinement Types for ML." PLDI 1991.
- Frisch, A., Castagna, G., & Benzaken, V. (2008). "Semantic subtyping."
  JACM 55(4).
- Xi, H. & Pfenning, F. (1999). "Dependent Types in Practical Programming."
  POPL 1999.
- Pierce, B. C. (2002). "Types and Programming Languages." MIT Press.
- Comon, H. et al. (2007). "Tree Automata Techniques and Applications."
  (TATA).

#### Future Feature: Hindley-Milner Type Inference

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

### Gap 7: Symbolic Finite Transducers — IMPLEMENTED

**Status:** Complete. Output-producing transductions over infinite domains
implemented in `prattail/src/sft.rs` (feature gate `sft`). Includes:
`SymbolicFiniteTransducer<A, B>` with composition, pre/post-image,
functionality/equivalence checks, practical factories (case fold, whitespace
normalize, guard transform), pipeline integration (SftAnalysis, 4 lints
SFT01-SFT04, cost-benefit gate, predicate dispatch M15:Sft).
See `prattail/docs/design/symbolic-finite-transducer.md` for architecture.

Reference: D'Antoni & Veanes, POPL 2012.

### Gap 8: E-Graph Equality Saturation — IMPLEMENTED

**Status:** Implemented in `prattail/src/egraph.rs` (~900 lines, 49 tests).
Feature gate: `egraph = ["trs-analysis"]`. Provides equality saturation
(Willsey et al., POPL 2021) for enhanced joinability checking, term
simplification, and equivalence discovery beyond what normalization alone
achieves. Pipeline integration via `EGraphAnalysis`, lints EG01–EG04,
cost-benefit gate `EGraphSaturation`.

### WeightedMsoFormula Parsing

The `tokens { }` feature provides the lexer infrastructure for guard keywords.
What remains is the Pratt parser integration to parse the predicate
sublanguage into `WeightedMsoFormula` AST.

---

## 23. Implementation Roadmap

### What's Already Implemented

| Component                                                                  | Status                  |
|----------------------------------------------------------------------------|-------------------------|
| M1–M14 automata modules                                                    | COMPLETE                |
| Predicate dispatch controller (~2,100 lines, 110 tests)                    | COMPLETE                |
| Pipeline integration (analyze_from_bundle)                                 | COMPLETE                |
| Guard lints (SYM01–04, PD01–04, MSO01–03, PT01–03, RA01–03, MT01–02, etc.) | COMPLETE                |
| Decidability classification T1–T4                                          | COMPLETE                |
| BooleanAlgebra trait + 5 impls                                             | COMPLETE                |
| ConstraintTheory + 3 theories + TheoryAlgebra bridge                       | COMPLETE                |
| LogicT fair backtracking monad                                             | COMPLETE                |
| ProductAlgebra composition                                                 | COMPLETE                |
| Tokens feature (all 10 sprints)                                            | COMPLETE                |
| Rocq proofs (dispatch, constraint theories)                                | COMPLETE                |
| **Gap 3: QuantifiedFormula + evaluate_quantified (LogicT strategy)**       | **COMPLETE**            |
| **Gap 3: BehavioralPred / PredArg / Quantifier types**                     | **COMPLETE**            |
| **Gap 3: Predicate sublanguage parser**                                    | **COMPLETE**            |
| **Gap 3: Guarded Comm rule codegen (BehavioralGuard)**                     | **COMPLETE**            |
| **Gap 4: AC-Matching for Collections**                                     | **COMPLETE**            |
| **Gap 5: TypeSystem trait + Pluggable Type System Framework**              | **COMPLETE** (RT1–RT11) |

### The Gap

The **runtime guard evaluation pipeline** — AST types, parser, and quantified
evaluator are now implemented (Gap 3). Remaining work:
- Phase 1A: `match_pattern`/`match_pattern_name` generation
- Phase 2A: Structural guarded Comm rule skeleton
- Phase 5A/5B: SFA + register automaton codegen (AWA strategy)
- Phase 6A: Trampoline integration for guard frames

### Tokens Feature Benefits

The `tokens { ... }` block provides:

1. Custom guard tokens (`forall`, `exists`, `/\`, `\/`) via
   `TokenKind::Custom` with regex patterns and priority
2. Modal lexing (WPDS modes) for predicate keyword recognition inside guards
3. FIRST set augmentation for guard token disambiguation
4. VPA delimiter verification for guard scope nesting
5. Tree automata validation for guard expression structure
6. Multi-tape synchronization for multi-channel guard evaluation
7. Fragment composition via `merge_token_defs()` for clean base languages

### Implementation Phases

**Phase 0 — Foundation (AST & Data Structures):**
Sprint 0A: `BehavioralPred`, `PredArg`, `TermParam::GuardBody` types.
Sprint 0B: `VariantKind::GuardedScope` in substitution infrastructure.

**Phase 1 — Pattern Matching:**
Sprint 1A: Generate `match_pattern` / `match_pattern_name` methods.

**Phase 2 — Guarded Comm Rule Codegen:**
Sprint 2A: Structural guard Comm rule (Ascent clause).
Sprint 2B: Per-relation behavioral predicate Comm rules.

**Phase 3 — Parser Integration:**
Sprint 3A: DSL parsing (`guard_body()` in term context).
Sprint 3B: Runtime parser for guard syntax.

**Phase 4 — Stratified Negation:**
Sprint 4A: Negated behavioral predicates + stratification validation.

**Phase 5 — Runtime Automaton Execution:**
Sprint 5A: SFA guard compilation codegen (all 4 tiers).
Sprint 5B: Register automaton + bounded checker codegen.

**Phase 6 — Trampoline Integration:**
Sprint 6A: Guard evaluation `Frame_Cat` variants for stack safety.

**Phase 7 — Optimization Integration:**
Sprint 7A: Guard selectivity ordering (M7).
Sprint 7B: Guard overlap and dead guard analysis (M1).

**Phase 8 — End-to-End Testing:**
Sprint 8A: Integration tests + documentation.

### Critical Path

```
0A ──→ 0B ──→ 1A ──→ 2A ──→ 2B ──→ 5A ──→ 5B ──→ 8A
                │                   │
                ├──→ 3A ──→ 3B ──→ 6A
                │              │
                │              └──→ 4A
                │
                └──→ (3A parallel with 1A)
                                     │
                              7A ──→ 7B ──→ 8A
```

**Longest chain:** 0A → 0B → 1A → 2A → 2B → 5A → 5B → 8A (8 sprints)

**Parallel tracks:** 3A/3B (parser) can start after 0A; 4A (negation) after
2B; 7A/7B (optimization) after 5A.

---

## 24. Verification Plan

### Per-Sprint Testing

Each sprint has specific tests. Aggregate counts must maintain zero failures
across `cargo test --workspace` (default features) and
`cargo test --workspace --all-features`.

### Property-Based Testing (Proptest)

- Guard satisfiability ↔ SFA emptiness correspondence
- Pattern matching symmetry: `match_pattern(a, pattern) = Some(σ)` implies
  `substitute(pattern, σ) = a`
- Stratification: randomly generated negated relation sets never violate
  stratum ordering

### Integration Testing

- §7 worked example: end-to-end trace to expected normal form
- Multi-guard dispatch: 3 guards on same channel, each fires for specific input
- T1–T4 decidability examples classified and compiled correctly
- Behavioral predicate join: fires only when relation holds in fixpoint
- Negated predicate: fires only when relation does NOT hold

### Rocq Formal Verification

- Guard compilation soundness: SFA accepts iff formula satisfied
- Quantifier correspondence: AWA Q⊗ ↔ ∀, Q⊕ ↔ ∃
- Pattern matching correctness: `match_pattern` is injective
- Stratification validation: negated-relation well-ordering implies no
  circular dependency

### Performance Testing

- Benchmark guard evaluation overhead vs unguarded Comm rules
- Measure SFA compilation time for guards of increasing complexity
- Verify trampoline frame variants don't degrade non-guard parsing

---

## 25. Risks and Mitigations

| Risk                                           | Impact                   | Mitigation                                  |
|------------------------------------------------|--------------------------|---------------------------------------------|
| Guard uses `unsafe_body` with BoundVars        | Match fails silently     | Use `unbind()` to get FreeVars (§6)         |
| Binder ordering mismatch guard↔continuation    | Wrong substitution       | Parser enforces same order, same extraction |
| Duplicate variable names in guard              | Ambiguous bindings       | Parser rejects duplicates                   |
| Collection/Scope in guard pattern              | Match returns None       | Document restriction; clear error message   |
| `match_pattern_name` per candidate pair        | Slowdown for large bags  | O(\|pattern\|) per call; acceptable         |
| Category mismatch in continuation              | Wrong substitution pass  | Parser infers categories from guard         |
| Behavioral pred references undeclared relation | No matching Comm rule    | Parser validates against declared relations |
| Combinatorial explosion for conjunction rules  | Too many generated rules | Practical for K ≤ 2–3; interpreter fallback |

---

## 26. Relationship to Brainstorming Document

The brainstorming document (`02-23-pattern-matching.md`) established the
foundational design for guarded receive with type predicates. This document
extends and restructures that content:

| Layer       | Scope                              | Document Section                                |
|-------------|------------------------------------|-------------------------------------------------|
| **Layer 1** | Structural patterns + Ascent joins | §§3–10 (core design)                            |
| **Layer 2** | First-order predicate logic        | §§11–14 (formal framework)                      |
| **Layer 3** | Analysis and verification          | §§15–18 (BooleanAlgebra, constraints, automata) |
| **Layer 4** | Extended infrastructure            | §§19–23 (pipeline, extension, roadmap)          |

Layer 1's `BehavioralPred { relation_name, args }` becomes a special case of
the general `BooleanAlgebra::Predicate` from M1.

---

## 27. Cross-References and References

### Cross-References

- **Advanced automata overview:** `prattail/docs/design/advanced-automata-overview.md`
- **Semiring catalog:** `prattail/docs/design/semiring-catalog.md`
- **Diagnostics reference:** `prattail/docs/diagnostics/README.md`
- **Predicate dispatch automaton:** `prattail/docs/design/predicate-dispatch-automaton.md`
- **Constraint theory design docs:** `prattail/docs/design/constraint-theories/`
- **Constraint theory diagnostics:** `prattail/docs/diagnostics/{presburger,unification,subtype-lattice,logict}/`
- **Rocq proofs:** `formal/rocq/{logict,presburger,unification,lattice}/`
- **Type system framework design:** `prattail/docs/design/type-system-framework.md` (Gap 5)
- **Refinement type diagnostics:** `prattail/docs/diagnostics/refinement/` (RT01–RT06)
- **Original brainstorming:** `/home/dylon/Downloads/02-23-pattern-matching.md`

### References

1. Baader, F. & Snyder, W. "Unification Theory." In *Handbook of Automated
   Reasoning*, vol. 1, ch. 8, pp. 445–533. Elsevier, 2001.

2. Birkhoff, G. *Lattice Theory*. AMS Colloquium Publications, vol. 25, 1940.

3. Büchi, J. R. "Weak second-order arithmetic and finite automata."
   *Zeitschrift für mathematische Logik und Grundlagen der Mathematik*,
   6:66–92, 1960.

4. D'Antoni, L. & Veanes, M. "Minimization of Symbolic Automata."
   *Proceedings of POPL*, pp. 541–553. ACM, 2014.
   DOI: [10.1145/2535838.2535849](https://doi.org/10.1145/2535838.2535849)

5. Davey, B. A. & Priestley, H. A. *Introduction to Lattices and Order*.
   2nd ed. Cambridge University Press, 2002.

6. Droste, M. & Gastin, P. "Weighted Automata and Weighted Logics."
   *Theoretical Computer Science*, 380:69–86, 2007.

7. Emerson, E. A. & Jutla, C. S. "Tree Automata, Mu-Calculus and
   Determinacy." *Proceedings of FOCS*, pp. 368–377. IEEE, 1991.

8. Feng, B. & Maletti, A. "Weighted Two-Way Transducers."
   *Proceedings of CAI*. LNCS, Springer, 2022.

9. Hemann, J. & Friedman, D. P. "μKanren: A Minimal Functional Core for
   Relational Programming." *Scheme Workshop*, 2013.

10. Kaminski, M. & Francez, N. "Finite-Memory Automata." *Theoretical
    Computer Science*, 134(2):329–363, 1994.

11. Kempe, A. "Weighted Multi-Tape Automata and Transducers for NLP." 2004.

12. Kiselyov, O., Shan, C., Friedman, D. P. & Sabry, A. "Backtracking,
    Interleaving, and Terminating Monad Transformers." *Proceedings of ICFP*,
    pp. 192–203. ACM, 2005.
    DOI: [10.1145/1086365.1086390](https://doi.org/10.1145/1086365.1086390)

13. Kostolanyi, A. & Misun, F. "Alternating Weighted Automata over
    Commutative Semirings." *Theoretical Computer Science*, 740:1–27, 2018.

14. Martelli, A. & Montanari, U. "An Efficient Unification Algorithm."
    *ACM Transactions on Programming Languages and Systems*, 4(2):258–282,
    1982.

15. Meredith, L. G. & Radestock, M. "A Reflective Higher-Order Calculus."
    *Electronic Notes in Theoretical Computer Science*, 141(5):49–67, 2005.

16. Robinson, J. A. "A Machine-Oriented Logic Based on the Resolution
    Principle." *Journal of the ACM*, 12(1):23–41, 1965.

17. Rondon, P., Kawaguchi, M., & Jhala, R. "Liquid Types." *Proceedings of
    PLDI*, pp. 159–169. ACM, 2008.

18. Freeman, T. & Pfenning, F. "Refinement Types for ML." *Proceedings of
    PLDI*, pp. 268–277. ACM, 1991.

19. Frisch, A., Castagna, G., & Benzaken, V. "Semantic subtyping: Dealing
    set-theoretically with function, union, intersection, and negation
    types." *Journal of the ACM*, 55(4):1–64, 2008.

20. Xi, H. & Pfenning, F. "Dependent Types in Practical Programming."
    *Proceedings of POPL*, pp. 214–227. ACM, 1999.

21. Pierce, B. C. *Types and Programming Languages*. MIT Press, 2002.

22. Comon, H. et al. "Tree Automata Techniques and Applications." (TATA),
    2007. Available at: http://tata.gforge.inria.fr/
