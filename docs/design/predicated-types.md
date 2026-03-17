# Predicated Types: Guarded Communication in MeTTaIL

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

This document covers the end-to-end predicated types system across
twenty-six sections in three parts:

- **Part I** (§§1–7A, 8–10): Core design — from surface syntax through
  structural matching, behavioral predicates (including quantified
  predicates and AC-matching), the guarded Comm rule, architectural
  overview of the five key subsystems (§7A), and correctness analysis.
  A reader can stop after §10 and understand single-channel guards.
- **Part II** (§§11–18): Formal framework — decidability tiering, the
  five-stage pipeline, guard compilation strategies, compile-time/runtime
  boundary, the BooleanAlgebra algebraic foundation, constraint theories
  (including pipeline flow, dispatch gating, and extension mechanism),
  and automata modules (including symbolic finite transducers and e-graph
  equality saturation).
- **Part III** (§§19–25): Architecture and implementation — lint
  integration, pluggable type system framework (refinement types,
  set-theoretic types, Hindley-Milner), implementation architecture,
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

### Syntax Mapping

The brainstorming document (`02-23-pattern-matching.md`) established
`(n ? guard).{body}` as the canonical generic syntax for guarded receive,
matching the constructor declaration in §4:

```
"(" n "?" guard ")" "." "{" p "}"
```

The `for(@pattern : predicate <- channel) { body }` notation used in the
examples above is Rholang-specific surface sugar. The desugaring is:

```
for (@{x!(y)} : path(y, {}) <- ch) { P }
⟶  (ch ? @(x!(y)), path(y, {})).{ P }
```

| Syntax Form                                          | Context                                 |
|------------------------------------------------------|-----------------------------------------|
| `(n ? guard, preds).{body}`                          | Generic/internal (language-agnostic)    |
| `for (@pattern : predicate <- channel) { body }`     | Rholang surface sugar                   |

Subsequent sections (§§3–10 and beyond) use the internal `(n ? ...)` form
to remain language-agnostic. The Rholang surface sugar is specific to the
rho-calculus term algebra and would differ for other `language!`-defined
calculi.

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

### VariantKind Extension

The `PGuardedInput` constructor introduces a new `VariantKind::GuardedScope`
in the macro's variant classification (`subst.rs`). This extends the
existing set (`Var`, `Literal`, `Nullary`, `Regular`, `Collection`,
`Binder`, `MultiBinder`) with a variant that handles the dual-scope
structure: a Name-typed guard scope and a Proc-typed continuation scope
sharing binders, with an interleaved `Vec<BehavioralPred>`. The code
generators for substitution, normalization, display, and `match_pattern`
dispatch on this variant to handle the guard-specific structure.

---

## 5. Pattern Matching Algorithm

### MatchBindings

Matching produces bindings of **mixed categories**. A shared struct is
generated alongside the AST categories:

```rust
struct MatchBindings {
    name_bindings: Vec<(String, Name)>,
    proc_bindings: Vec<(String, Proc)>,
    // ... one field per declared category in the language definition
}
```

`MatchBindings` supports:
- `empty()` — no bindings
- `name(var, val)` — single Name binding
- `proc(var, val)` — single Proc binding (one constructor per category)
- `merge(other)` — concatenation
- `get_name(var_name) → Option<&Name>` — typed lookup (one per category)
- `get_proc(var_name) → Option<&Proc>` — typed lookup (one per category)

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
┌──────────────┬───────────────────┬─────────────────────────────────────┐
│ Pattern Kind │ Match Rule        │ Result                              │
├──────────────┼───────────────────┼─────────────────────────────────────┤
│ Variable     │ Bind at category  │ MatchBindings::{name,proc}(v, t)    │
│ Nullary      │ Exact equality    │ MatchBindings::empty()              │
│ Regular      │ Recurse fields    │ merge(match(f₁), …, match(fₙ))      │
│ Literal      │ Value equality    │ MatchBindings::empty() if eq        │
│ Collection   │ Order-independent │ AC-match via re-entrant engine      │
│ Binder/Scope │ Unbind + recurse  │ merge(binder_bindings, body_match)  │
└──────────────┴───────────────────┴─────────────────────────────────────┘
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

**Collection** patterns use order-independent matching: HashBag elements are
matched regardless of position via a `claimed` bitvector, Vec elements are
matched positionally, and HashSet elements match like HashBag without
multiplicity. Each element sub-match re-enters `match_pattern()` via TLS,
which is bounded by collection size, not nesting depth. For behavioral
guards that use AC-matching on collection patterns, see §8 (AC-Matching
for Collection Guards). (The brainstorming document deferred collection
matching; this section implements what was deferred.)

**Binder/Scope** patterns open both ground and pattern scopes, then match
bodies structurally. If the pattern binder is a FreeVar, it binds to the
ground binder name. MultiBinder extends this to multiple simultaneous
bindings. See §5 "Iterative Work Stack Architecture" for the full algorithm.
(The brainstorming document deferred binder/scope matching; this section
implements what was deferred.)

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

Module: `macros/src/gen/term_ops/match_pattern.rs`

Called from `generate_all()` in `macros/src/gen/mod.rs`, alongside
substitution and normalization generation.

### Iterative Work Stack Architecture

Pattern matching uses an explicit work stack (`Vec<MatchTask>`) instead of
recursive function calls, providing stack safety for arbitrarily deep terms
(100K+ nesting depth). This mirrors the trampoline parser design.

**`MatchTask` enum:** A heterogeneous work item with one variant per category:

```rust
enum MatchTask {
    MatchProc(Proc, Proc),   // ground, pattern
    MatchName(Name, Name),
    // ... one per category
}
```

Cross-category recursion (Proc → Name → Proc) is handled naturally: when
processing a `MatchProc` task with a `Name` field, the handler pushes
`MatchTask::MatchName(ground_field, pattern_field)` onto the stack.

**Thread-local pooling:** `Cell<Vec<MatchTask>>` with take/set at entry/exit.
Zero allocation in steady state after the first call.

**Algorithm:**

```
1. Push initial MatchTask::MatchCat(self, pattern) onto stack
2. While stack non-empty:
   a. Pop task
   b. If pattern is FreeVar: bind to ground, continue
   c. Match constructors:
      - Var/Literal/Nullary: equality check (immediate)
      - Regular: push MatchTask for each field (LIFO → left-to-right order)
      - Collection: inline element matching with re-entrant match_pattern()
      - Binder: inline scope open with re-entrant body match_pattern()
      - Mismatch: return None
3. Return Some(bindings)
```

**Re-entrancy for Collections/Binders:** Collection matching requires
synchronous sub-match results (to select which ground element to claim).
These arms call `match_pattern()` per element, which re-enters the iterative
engine via TLS (gets a fresh stack since the Cell is taken). This re-entry is
bounded by collection size, not nesting depth — the deep nesting within each
element is handled iteratively by the inner engine call.

### Collection Variant Matching

Collection variants (PPar bags, lists, sets) use order-independent matching:

**HashBag (multiset):** Pattern elements are matched against ground elements
regardless of order. Each pattern element is classified:
- **Non-variable:** Finds an exact structural match among unclaimed ground elements
- **Variable (FreeVar):** Binds to any unclaimed ground element

A `claimed` bitvector tracks which ground elements have been matched. If any
pattern element fails to find a match, the entire match fails.

```
match_pattern(PPar({P, Q, R}), PPar({x, PSend(a, b), y}))
  → claimed = [false, false, false]
  → try PSend(a,b) against {P, Q, R}: find structural match → claim that element
  → bind x to first unclaimed ground element
  → bind y to remaining unclaimed ground element
  → MatchBindings { proc: {x→P_matched, y→R_matched}, name: {a→..., b→...} }
```

**Vec (ordered):** Position-wise matching — `g_vec[i].match_pattern(p_vec[i])`
for each position. Length must match.

**HashSet:** Same as HashBag but without multiplicity tracking.

### Binder Variant Matching

Binder variants (PNew, PInput) match under the binder by opening both scopes:

```
match_pattern(PNew(x, body_g), PNew(y, body_p))
  → match pre-scope fields (if any)
  → g_inner = ground_scope.inner()     // unbind ground
  → p_inner = pattern_scope.inner()    // unbind pattern
  → (*g_inner.unsafe_body).match_pattern(&*p_inner.unsafe_body)
  → accumulate bindings from body match
```

If the pattern binder is a FreeVar, it gets bound to the ground binder name
via the variable-catches-all arm at the top of `match_pattern()`.

**MultiBinder** extends this to multiple simultaneous bindings. Binder counts
must match between ground and pattern. Bodies are matched after unbinding all
binders with fresh names.

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
- **Key file:** `prattail/src/decision_tree.rs`

Concrete PathMap trie example for guarded vs unguarded receive:
```
PathMap trie for parse dispatch:

  FOR ──► LPAREN ──► capture(Name) ──► LARROW ──► capture(Name)
                                                       │
                                          ┌────────────┴────────────┐
                                          ▼                         ▼
                                      RPAREN                     IF
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
  regular positions recurse into children. Returns `Option<MatchBindings>`.
- **When:** Compile-time code generation, runtime per-Comm-rule firing.
- **Contract:** `(ground_term, pattern) → Option<MatchBindings>`
- **Predicated types role:** When a Comm rule fires, `match_pattern_name` is called
  on the received value against the guard body pattern. Success yields σ (the
  substitution); failure means the Comm rule does not fire.
- **Distinction from unification:** One-directional (ground vs pattern), O(|pattern|),
  deterministic. No occurs check needed. No backtracking.
- **Key file:** `macros/src/gen/term_ops/match_pattern.rs`

Concrete example:
```
match_pattern_name(
  NQuote(PPar({PSend(x,y), PNil})),
  NQuote(PPar({PSend(a,b), ...rest}))
)
→ MatchBindings { name: {a→x, b→y}, proc: {rest→PNil} }
```

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
- **Contract:** `(term₁, term₂) → Option<Substitution>` (most general unifier)
- **Predicated types role:**
  - *Compile-time:* Detects overlapping guard patterns (SYM02/SYM03 lints).
    Two guards φ₁ and φ₂ overlap iff `unify(φ₁, φ₂) ≠ ⊥`.
  - *Runtime (optional):* If the language enables unification-based matching,
    guard evaluation can use unification instead of first-order matching.
- **Key file:** `prattail/src/unification.rs`

Comparison with first-order matching:
```
First-order matching:      ground  ← pattern   (one-directional, O(|pattern|))
Unification:               pattern ↔ pattern   (bidirectional,  O(n·α(n)))
```

In the guarded Comm rule pipeline:
- **Runtime**: `match_pattern` performs ground-vs-pattern matching per Comm fire
  (the received value is always ground; the guard body is always a pattern)
- **Compile-time**: Unification performs pattern-vs-pattern overlap detection
  (two guard patterns may both contain variables; unification finds the MGU
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
- **Key file:** `macros/src/ast/pattern.rs`

Concrete pattern lowering example:
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

```
┌─────────────────────────────────────────────────────────────────┐
│                    Ascent Fixpoint Engine                        │
│                                                                 │
│  Relations:                                                     │
│    proc(Proc)          ← category exploration                   │
│    name(Name)          ← category exploration                   │
│    eq_proc(Proc, Proc) ← equations + congruence                 │
│    rw_proc(Proc, Proc) ← rewrites + congruence                 │
│    R(T₁, ..., Tₙ)     ← user-declared semantic relations       │
│                                                                 │
│  Rule firing order (semi-naïve):                                │
│    1. Category rules: proc(PNew(x,body)) → name(x), proc(body) │
│    2. Equation rules: eq_proc(PDrop(@P), P) ← proc(PDrop(@P))  │
│    3. Comm rules:                                               │
│       proc(result) ←                                            │
│         proc(PPar(bag)),                                        │
│         for (elem, _) in bag.iter(),                            │
│         if let PSend(ch, val) = elem,     ← structural match   │
│         ...,                                                    │
│         match_pattern_name(val, φ) = σ,   ← first-order match  │
│         R(σ(x), σ(y)),                    ← behavioral guard   │
│         let result = σ(continuation);     ← substitution       │
│    4. Congruence rules: propagate eq/rw through constructors    │
│                                                                 │
│  Fixpoint: iterate until no new tuples in any relation          │
└─────────────────────────────────────────────────────────────────┘
```

### End-to-End Composition Flow

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         SOURCE CODE                                     │
│   for(x <- ch if positive(x)) { P }                                    │
└───────────────────────────┬─────────────────────────────────────────────┘
                            │
                   ─── PARSE TIME ───
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  ① PathMap Decision Tree                                                │
│     Token stream: FOR LPAREN IDENT LARROW IDENT IF IDENT ... RPAREN    │
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
│   → Option<MatchBindings>│  │   for (elem, _) in bag.iter(),           │
│                          │  │   if let Proc::PSend(ch, val) = elem,    │
│ Per-variant arms:        │  │   if ch == expected_channel,             │
│   NQuote: recurse into   │  │   if let Some(mb) = val.match_pattern(φ),│
│     Proc::match_pattern  │  │   positive(mb.get_name("x")),  ← T2 join│
│   NVar: check index eq   │  │   let result = construct_continuation(σ);│
│   FreeVar: bind to σ     │  │                                          │
└──────────────────────────┘  └──────────────┬───────────────────────────┘
                                             │
                   ┌─────────────────────────┤
                   ▼                         │
┌──────────────────────────────┐             │
│ Guard Codegen (§13)          │             │
│                              │             │
│ Classify: T1/T2/T3/T4       │             │
│ (tiers defined in §11)      │             │
│ T2 → direct Ascent join or  │             │
│ SFA transition table or     │             │
│ relation lookup or range    │             │
│ check, per strategy         │             │
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
│   proc(PPar({PSend(ch, @42), PInput(ch, x, P)}))                       │
│   → match_pattern_name(@42, guard_body) = Some({x → 42})               │
│   → positive(42)?  ← behavioral guard join against Ascent relation      │
│   → if yes: proc(P[x := 42])  (continuation with substitution)         │
│                                                                         │
│ Fixpoint: no new tuples → DONE                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Component Interaction Matrix

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

> **Note:** The brainstorming document's `BehavioralPred` had only
> `relation_name` and `args`; `negated` extends the design for stratified
> negation support (§9).

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

> **Conjunction notation:** Three equivalent notations appear across the
> design documents:
>
> | Notation                        | Context                                            |
> |---------------------------------|----------------------------------------------------|
> | `/\`                            | Surface syntax in the predicate sublanguage (§2 EBNF) |
> | `AND`                           | English prose / pseudo-syntax (brainstorming document) |
> | `BehavioralPred::And(a, b)` / multiple entries in `Vec<BehavioralPred>` | AST representation |
>
> The brainstorming document uses `AND` (e.g., `path(y, {}) AND
> is_output(*(x))`); the §2 predicate sublanguage grammar uses `/\`; the
> runtime representation is a `Vec<BehavioralPred>` (implicit conjunction).

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

### Quantified Behavioral Predicates

**Problem:** Current behavioral predicates are existential queries ("does
tuple exist in relation?"). Full FOL needs universal quantification and
nested quantification.

**Infrastructure available:** LogicT provides `gnot` (negation as failure for
`not-exists`), `ifte`/`once` (committed choice for `exists-unique`), and `fair_conjoin` (fair
nested quantification `forall x. exists y. P(x,y)`).

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

### AC-Matching for Collections

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
│ Module: macros/src/gen/runtime/guard_codegen.rs                          │
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

The compiled automaton generates Rust code as a `TokenStream`. Each tier
produces a different code shape:

| Tier | Generated Code Shape | Runtime Cost |
|------|---------------------|--------------|
| T1   | No code (guard eliminated) | O(0) |
| T2   | Inline arithmetic, Ascent join clause, register machine, or SFA `match` table | O(1) to O(\|value\|) |
| T3   | BFS/DFS with depth counter returning `TriState` | O(k · \|value\|) |
| T4   | `assert_pred()` trust wrapper | O(1) |

See §13 "Generated Rust Code per Tier" for concrete code examples of each tier.

### WeightedMsoFormula Parsing

The `tokens { }` feature provides the lexer infrastructure for guard keywords.
The next step is Pratt parser integration to parse the predicate sublanguage
into `WeightedMsoFormula` AST, connecting the surface syntax from §2 to the
pipeline's Stage 1 parse entry point.

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

This is T4 because `halt` universally quantifies over an infinite domain
(all reachable states) with no explicit bound — the halting problem in
disguise. A bounded variant (`halt_{100}`) is T3 and compiles to a bounded
checker.

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

### Guard Codegen Architecture (`guard_codegen.rs`)

The actual implementation in `macros/src/gen/runtime/guard_codegen.rs` provides:

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

**T1 elimination:** `evaluate_static_guard(pred) → Option<bool>` returns
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

```rust
fn __guard_N(
    relation_query: &dyn Fn(&str, &[String]) -> bool,
    domain_enumerate: &dyn Fn(&str) -> Vec<Vec<String>>,
    env: &HashMap<String, String>,
) -> bool  // (or TriState for T3)
```

These functions serve testing, external callers, and the selectivity analysis
pipeline. The primary evaluation path for T2 guards uses inline Ascent joins.

### Guard Selectivity and Ordering

When multiple guards protect the same channel, `estimate_selectivity(pred) → f64`
computes a heuristic selectivity value in [0.0, 1.0]:

| Guard Structure                | Selectivity    | Rationale                      |
|--------------------------------|----------------|--------------------------------|
| Negated RelationQuery          | 0.1            | Rejects most inputs            |
| Positive RelationQuery         | 0.5            | Moderate (half of domain)      |
| And(a, b)                      | sel(a) × sel(b)| Independent conjunction        |
| Or(a, b)                       | 1 − (1−sa)(1−sb)| Independent disjunction      |
| ForAll (bounded/unbounded)     | 0.05/k^0.5     | Very selective                 |
| Exists (bounded/unbounded)     | 0.3/k^0.5      | Moderate                       |
| AcMatch { elements }           | 0.3/|elements| | Depends on bag size            |
| Not(inner)                     | 1 − sel(inner) | Complement                     |

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

| Subsystem | Compile-Time Role | Runtime Role | Section |
|---|---|---|---|
| Surface syntax parsing | Pratt parser in proc macro | — | §2 |
| Guard predicate sublanguage | Parse `/\`, `\/`, `~`, `forall`, `exists` | — | §2 |
| Term AST / `PGuardedInput` | Enum variant generation | — | §4 |
| `match_pattern` / `match_pattern_name` | Code generation (per-category methods) | Ground-vs-pattern matching per Comm fire | §5 |
| `MatchBindings` | — | Accumulates bindings during matching | §5 |
| Guarded Comm rules | Ascent clause generation | Fires during fixpoint evaluation | §6 |
| Substitution + normalization | — | Per-fire: `multi_substitute` + `.normalize()` | §6 |
| Behavioral predicate joins | Ascent join clause generation | O(1) hash lookup in Ascent relation | §8 |
| Quantified predicates | `QuantifiedFormula` AST construction | `evaluate_quantified()` via LogicT | §8 |
| AC-matching | Partition codegen | `multiset_select()` per Comm fire | §8 |
| Decidability classification (T1–T4) | Formula analysis → tier assignment | — | §11 |
| Guard codegen (T1) | Static evaluation → dead-code elim | — (zero overhead) | §13 |
| Guard codegen (T2) | SFA/range/register compilation | Guard function: O(1)–O(\|value\|) | §13 |
| Guard codegen (T3) | Bounded automaton compilation | BFS with depth counter: O(k·\|value\|) | §13 |
| Guard codegen (T4) | Lint MSO01, Rocq certificate check | `assert_pred()` returns true (trust) | §13 |
| Pipeline (Stages 1–5) | Parse → Classify → Compile → Optimize → Codegen | — | §12 |
| BooleanAlgebra + SFA ops | `is_satisfiable`, intersect, minimize | — | §15 |
| ConstraintTheory suite | Propagate, label, witness | — | §16 |
| Automata modules (M1–M14) | Guard analysis + dispatch | — | §17 |
| Selectivity estimation (M7) | Ordering decision at compile time | Evaluation order at runtime | §13, §17 |
| Predicate dispatch controller | Feature extraction + module activation | — | §17 |
| All lints (SYM, MSO, PT, RA, …) | Diagnostic emission at `cargo build` | — | §19 |
| Unification (Martelli-Montanari) | Pattern overlap analysis (UN01–03) | Optional: unification-based matching | §16 |
| LogicT / `LogicStream` | Fair search for CT satisfiability | `∀`/`∃` guard evaluation | §16 |
| Forward-Backward analysis | Hot/cold path classification | `#[inline]`/`#[cold]` annotations | §17 |
| `is_refined_*` relations | Ascent relation generation | Per-tuple predicate evaluation | §22 |
| Rocq formal proofs | Property verification | — (not in binary) | §16, §22 |

Rows with both columns filled have a **dual nature** ("codegen"): compiled as
proc macro logic, they emit `TokenStream` fragments that execute at runtime.
Rows with "—" in the Runtime Role column produce **zero runtime overhead** —
no generated code, no data structures, no per-value cost in the binary. This
includes all automata modules (M1–M14), BooleanAlgebra + SFA, all
ConstraintTheory implementations, the dispatch controller, all 30+ lint codes,
and all Rocq proofs.

Three components span both phases:

- **LogicStream<T>**: Compile-time fair backtracking for `TheoryAlgebra::label()`
  satisfiability; runtime `evaluate_quantified()` for `∀`/`∃` guards (`gnot`,
  `interleave`, `collect_bounded`).
- **Unification**: Compile-time pattern overlap detection (UN01–03); runtime
  unification-based matching if enabled (e.g., MeTTa).
- **Forward-Backward**: Compile-time hot/cold path classification; runtime
  effect is `#[inline]`/`#[cold]` annotations on generated guard functions
  (analysis code itself is not in the binary).

For the end-to-end flow diagram, see §1A (End-to-End Composition Diagram).

---

## 15. The BooleanAlgebra Framework

### Motivation

All guard analysis — satisfiability, subsumption, overlap detection,
equivalence — reduces to operations over Boolean algebras. The
`BooleanAlgebra` trait provides the algebraic foundation for the entire
predicated types pipeline. (For how SFA intersection supports guard
selectivity and overlap analysis, see §13.)

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

### SFA Compilation to Rust Match Statements

When a guard compiles to an SFA via `generate_sfa_transition_table()` in
`guard_codegen.rs`, the determinized and minimized DFA is encoded as a Rust
`match` statement. The minterm-based determinization produces a partitioning
of the input domain into equivalence classes, and each transition becomes a
match arm:

```rust
fn __guard_sfa_N(value: &Term) -> bool {
    let mut state: usize = 0; // initial state
    for symbol in value.iter_symbols() {
        state = match (state, /* minterm predicate */) {
            (0, true) => 1,   // minterm partition A
            (0, false) => 2,  // minterm partition B
            (1, true) => 1,   // self-loop on accepting
            (1, false) => 3,  // transition to sink
            _ => return false, // implicit sink state
        };
    }
    matches!(state, 1) // accepting states
}
```

The key insight is that minterms partition the predicate space into regions
where all transitions behave uniformly. For `IntervalAlgebra` guards, minterms
correspond to integer intervals; for `KatBooleanAlgebra` guards, minterms
correspond to propositional atom truth assignments. The number of match arms
is bounded by |states| x |minterms|, which is typically small after
minimization.

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

### Pipeline Flow

#### Structural Analysis Pattern

Like all 22+ existing `analyze_from_bundle()` functions (e.g., `symbolic.rs`,
`nominal.rs`, `buchi.rs`), constraint theory analyses extract information
from `all_syntax: &[(String, String, Vec<SyntaxItemSpec>)]` without requiring
explicit guard fields on `RuleSpec`:

| Theory      | Looks for                                            | Extracts                                    |
|-------------|------------------------------------------------------|---------------------------------------------|
| Presburger  | Comparison terminals (`<`, `>=`, etc.) near captures | `LinearConstraint` → NFA satisfiability     |
| Unification | Same-category rules with overlapping structures      | `TermExpr` → Martelli-Montanari unification |
| Lattice     | Category delegation patterns (A references only B)   | Subtype edges → DAG + Warshall closure      |

### Parallel Analysis

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

### Relation Name Heuristics

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

**This heuristic approach should be superseded** by the `theories { }` block
(see Extension Mechanism below) that makes dispatch data-driven. The spec
author will explicitly declare which `ConstraintTheory` implementations handle
which guards, eliminating keyword guessing entirely and enabling arbitrary
user-defined constraint domains to participate in predicate dispatch without
heuristic support.

### Extension Mechanism

#### Three-Layer Design

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
- Already implemented and tested (22+ tests)
- Composable with existing `ConstraintTheory` infrastructure
- Simpler implementation (~250 lines vs ~2000 estimated)
- Supports bounded evaluation (T3) naturally via `collect_bounded()`

The cost-benefit framework (`CostBenefitGate`) can gate between LogicT and AWA
evaluation once `to_weighted_automaton()` is implemented, selecting the strategy
with lower estimated cost per guard.

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

These modules run on every guard regardless of the predicate signature
(negligible amortized cost: O(|guards|) per channel):

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

### Symbolic Finite Transducers (M15)

Output-producing transductions over infinite domains implemented in
`prattail/src/sft.rs` (feature gate `sft`). Includes:
`SymbolicFiniteTransducer<A, B>` with composition, pre/post-image,
functionality/equivalence checks, practical factories (case fold, whitespace
normalize, guard transform), pipeline integration (SftAnalysis, 4 lints
SFT01-SFT04, cost-benefit gate, predicate dispatch M15:Sft).
See `prattail/docs/design/symbolic-finite-transducer.md` for architecture.

Reference: D'Antoni & Veanes, POPL 2012. In the guard infrastructure, SFTs
enable transducer-based guard compilation — guards that transform input values
(e.g., case-folding before comparison) compile to SFT composition rather than
post-hoc normalization.

### E-Graph Equality Saturation

Implemented in `prattail/src/egraph.rs` (~900 lines, 49 tests).
Feature gate: `egraph = ["trs-analysis"]`. Provides equality saturation
(Willsey et al., POPL 2021) for enhanced joinability checking, term
simplification, and equivalence discovery beyond what normalization alone
achieves. Pipeline integration via `EGraphAnalysis`, lints EG01-EG04,
cost-benefit gate `EGraphSaturation`. In the guard infrastructure, e-graphs
simplify guard predicates via equality saturation — discovering algebraic
identities (e.g., `x > 0 /\ x > 0` → `x > 0`) before SFA compilation,
producing smaller automata and faster runtime checks.

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

| Automaton        | Init | Tokenize |  Dispatch   |   Analyze    | Optimize |   Codegen    | FOL Feature              |
|------------------|:----:|:--------:|:-----------:|:------------:|:--------:|:------------:|--------------------------|
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

## 20. Pluggable Type System Framework

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

### Architecture

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

### TypeSystem Trait

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

Subtyping rule:
```
{ x: S | P(x) } <: { x: T | Q(x) }
  iff  S <: T   (base subtype via TypeSystem)
  AND  ∀x. P(x) ⟹ Q(x)  (predicate entailment via ConstraintTheory)
```

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

### Infrastructure

| Component                     | Location                                 |
|-------------------------------|------------------------------------------|
| `ConstraintTheory` trait      | `prattail/src/logict.rs`                 |
| `TheoryAlgebra<T>` bridge     | `prattail/src/logict.rs`                 |
| `BooleanAlgebra` trait        | `prattail/src/symbolic.rs`               |
| `ProductAlgebra<A,B>`         | `prattail/src/symbolic.rs`               |
| `SymbolicAutomaton<A>` (SFA)  | `prattail/src/symbolic.rs`               |
| `LatticeTheory`               | `prattail/src/lattice_theory.rs`         |
| `UnificationTheory`           | `prattail/src/unification.rs`            |
| `PresburgerTheory`            | `prattail/src/presburger.rs`             |
| `WeightedTreeAutomaton<W>`    | `prattail/src/tree_automaton.rs`         |
| `IntervalAlgebra`             | `prattail/src/symbolic.rs`               |
| `TypeExpr` AST                | `macros/src/ast/types.rs`                |
| `BehavioralPred` + codegen    | `macros/src/ast/language.rs`, `rules.rs` |
| `QuantifiedFormula` evaluator | `prattail/src/logict.rs`                 |
| `LanguageSpec`                | `prattail/src/lib.rs`                    |
| Pipeline + lints              | `prattail/src/pipeline.rs`, `lint.rs`    |

### Feature Gating

```toml
type-system = ["logict", "lattice-theory"]
set-theoretic-types = ["type-system"]
predicated-types = [ ..., "type-system", "set-theoretic-types" ]
full-analysis = [ ..., "type-system", "set-theoretic-types" ]
```

### Key Files

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

1. Custom guard tokens (`forall`, `exists`, `/\`, `\/`) via
   `TokenKind::Custom` with regex patterns and priority
2. Modal lexing (WPDS modes) for predicate keyword recognition inside guards
3. FIRST set augmentation for guard token disambiguation
4. VPA delimiter verification for guard scope nesting
5. Tree automata validation for guard expression structure
6. Multi-tape synchronization for multi-channel guard evaluation
7. Fragment composition via `merge_token_defs()` for clean base languages

---

## 22. Verification Plan

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

### Concrete Test Scenarios

The brainstorming document (Phase 6) established the following minimum
validation suite. Each scenario exercises a distinct aspect of the guarded
receive mechanism:

1. **Basic structural guard:**
   `(n ? @(x!(y))).{@(y)!(*(x))}` — verifies cross-category binding and
   two-pass substitution.

2. **Nested patterns:**
   `(n ? @(x!(y!(z)))).{ @(z)!(*(y)) }` — verifies recursive descent
   through multiple constructors with three bindings (`x: Name, y: Name,
   z: Proc`).

3. **Guard failure (no match):**
   `(n ? @(x!(y))).{...} | n!({})` — verifies that `match_pattern_name`
   returns `None` for a constructor mismatch (`PZero` vs `POutput`) and
   the Comm rule does not fire.

4. **Guard with parallel context:**
   `{(n ? @(x!(y))).{...} | n!(a!(b)) | observer}` — verifies that the
   rest-bag correctly removes both the `PGuardedInput` and matched
   `POutput`, preserving `observer`.

5. **Variable shadowing:**
   `new(x, (c ? @(x!(y))).{...})` — verifies that De Bruijn encoding
   correctly separates the outer `x` (bound by `new`) from the inner `x`
   (guard pattern variable).

6. **Behavioral predicate:**
   `(n ? @(x!(y)), path(y, {})).{...}` — verifies per-relation Comm rule
   specialization and predicate argument resolution from match bindings.

---

## 23. Risks and Mitigations

| Risk                                           | Impact                   | Mitigation                                  |
|------------------------------------------------|--------------------------|---------------------------------------------|
| Guard uses `unsafe_body` with BoundVars        | Match fails silently     | Use `unbind()` to get FreeVars (§6)         |
| Binder ordering mismatch guard↔continuation    | Wrong substitution       | Parser enforces same order, same extraction |
| Duplicate variable names in guard              | Ambiguous bindings       | Parser rejects duplicates                   |
| Large collection in guard pattern               | Combinatorial AC-match   | Re-entrant engine bounds by collection size |
| `match_pattern_name` per candidate pair        | Slowdown for large bags  | O(\|pattern\|) per call; acceptable         |
| Category mismatch in continuation              | Wrong substitution pass  | Parser infers categories from guard         |
| Behavioral pred references undeclared relation | No matching Comm rule    | Parser validates against declared relations |
| Combinatorial explosion for conjunction rules  | Too many generated rules | Practical for K ≤ 2–3; interpreter fallback |

---

## 24. Relationship to Brainstorming Document

The brainstorming document (`02-23-pattern-matching.md`) established the
foundational design for guarded receive with type predicates. This document
extends and restructures that content:

| Layer       | Scope                              | Document Section                                  |
|-------------|------------------------------------|-------------------------------------------------  |
| **Layer 1** | Structural patterns + Ascent joins | §§3-10 (core design)                              |
| **Layer 2** | First-order predicate logic        | §§11-14 (formal framework)                        |
| **Layer 3** | Analysis and verification          | §§15-18 (BooleanAlgebra, constraints, automata)   |
| **Layer 4** | Extended infrastructure            | §§19-25 (lints, types, architecture, references)  |

Layer 1's `BehavioralPred { relation_name, args }` becomes a special case of
the general `BooleanAlgebra::Predicate` from M1.

### Preserved

The following design decisions from the brainstorming document are preserved
faithfully in this specification:

- **Surface syntax:** `(n ? guard).{body}` as the generic/internal form
  (§§3, 4, 6, 7, 8, 10). The `for(... <- ch)` Rholang sugar is explicitly
  mapped to this form in §2 (Syntax Mapping).
- **Core data structures:** `PGuardedInput` constructor with dual scopes
  (§4), `MatchBindings` with `name_bindings` / `proc_bindings` (§5),
  `BehavioralPred` / `PredArg` types (§8).
- **Algorithms:** First-order matching via `match_pattern` /
  `match_pattern_name` (§5), two-pass substitution (§3, §6),
  per-relation Comm rule specialization (§8).
- **Correctness analysis:** Soundness, binding correctness, capture
  avoidance, compositionality, equational integration, reflective
  consistency (§10 — corresponding to brainstorming §9).
- **Natural-category binding:** Variables bind at their syntactic category
  (§3 — corresponding to brainstorming §§3–4).
- **Implementation plan structure:** The six phases (match_pattern,
  constructor support, Comm rule, parser, behavioral predicates, testing)
  are preserved in the §21 architecture.
- **Worked example:** §7's end-to-end trace matches the brainstorming
  §13 example.

### Extended

This specification extends the brainstorming document in the following
areas:

- **Collection matching:** The brainstorming document deferred collection
  patterns (`return None`). This spec fully implements order-independent
  matching via `claimed` bitvector with re-entrant TLS (§5).
- **Binder/Scope matching:** The brainstorming document deferred binder
  patterns. This spec implements scope-open + structural body matching (§5).
- **Quantified behavioral predicates:** LogicT-based `∀`/`∃` evaluation
  with `gnot` for universals (§8), extending the simple existential join
  from the brainstorming.
- **AC-matching:** `multiset_partitions()` / `multiset_select()` for
  collection guard patterns (§8).
- **Decidability tiering:** T1–T4 classification with compilation
  strategies (§11–§14).
- **Automata modules:** SFA (M1), WTA (M2), AWA (M3), nominal (M4),
  multi-tape (M5), SFT (M6), e-graphs (M7) (§18).
- **Constraint theories:** Presburger arithmetic, unification,
  subtype lattice, LogicT (§16).
- **BooleanAlgebra foundation:** Algebraic framework for guard predicates
  (§15).
- **Pluggable type system framework:** Refinement types, set-theoretic
  types, Hindley-Milner (§20).
- **Lint integration:** Guard-related diagnostics (§19).
- **Iterative work stack:** Stack-safe matching via `Vec<MatchTask>`
  instead of recursive calls (§5).
- **Negated predicates:** `negated: bool` field for stratified negation
  (§8, §9).

### Changed

The following design decisions differ from the brainstorming document:

- **`MatchBindings::get()` → typed accessors:** The brainstorming's
  generic `get(var_name) → Option<MatchValue>` was replaced with
  per-category typed accessors (`get_name(var) → Option<&Name>`,
  `get_proc(var) → Option<&Proc>`) for type safety (§5).
- **`BehavioralPred.negated` field:** Added `negated: bool` to support
  stratified negation (§8, §9). The brainstorming had only
  `relation_name` and `args`.
- **Iterative work stack:** The brainstorming's recursive
  `match_pattern` algorithm was replaced with an explicit
  `Vec<MatchTask>` work stack for stack safety at 100K+ nesting depth
  (§5). The semantics are identical.

### Component Mapping

The following table maps each brainstorming document component to its
location in this specification, noting what was preserved, extended, or
added:

| Brainstorming Component       | Brainstorming § | Design Spec §    | Status           |
|-------------------------------|-----------------|------------------|------------------|
| Motivation                    | §1              | §1               | Preserved        |
| Scope                         | §2              | §1, §2           | Preserved        |
| Terms as Patterns             | §3              | §3               | Preserved        |
| Natural Categories            | §4              | §3               | Preserved        |
| Term Representation           | §5              | §4               | Preserved        |
| `match_pattern`               | §6              | §5               | Extended (work stack, Collection, Binder) |
| Comm Rule                     | §7              | §6               | Preserved        |
| Parsing                       | §8              | §4, §21          | Preserved        |
| Correctness Analysis          | §9              | §10              | Preserved        |
| Ordering and Determinism      | §10             | §6               | Preserved        |
| Behavioral Predicates         | §11             | §8               | Extended (quantified, negated, AC) |
| Implementation Plan           | §12             | §21              | Preserved        |
| Worked Example                | §13             | §7               | Preserved        |
| Risks and Mitigations         | §14             | §23              | Extended          |
| Relation to Infrastructure    | §15             | §21, §24         | Preserved (this table) |
| Summary                       | §16             | §1               | Preserved        |
| *—*                           | —               | §§11–20          | **Added** (decidability, pipeline, automata, types) |

---

## 25. Cross-References and References

### Cross-References

- **Advanced automata overview:** `prattail/docs/design/advanced-automata-overview.md`
- **Semiring catalog:** `prattail/docs/design/semiring-catalog.md`
- **Diagnostics reference:** `prattail/docs/diagnostics/README.md`
- **Predicate dispatch automaton:** `prattail/docs/design/predicate-dispatch-automaton.md`
- **Constraint theory design docs:** `prattail/docs/design/constraint-theories/`
- **Constraint theory diagnostics:** `prattail/docs/diagnostics/{presburger,unification,subtype-lattice,logict}/`
- **Rocq proofs:** `formal/rocq/{logict,presburger,unification,lattice}/`
- **Type system framework design:** `prattail/docs/design/type-system-framework.md` (§20)
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
