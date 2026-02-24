# Ascent Datalog Code Generation

**Source files:** `macros/src/logic/mod.rs` (orchestrator),
`macros/src/logic/relations.rs`, `macros/src/logic/categories.rs`,
`macros/src/logic/equations.rs`, `macros/src/logic/rules.rs`,
`macros/src/logic/congruence.rs`,
`macros/src/gen/runtime/language.rs`

The Ascent Datalog engine computes the semantic consequences of a parsed term —
structural equivalences, rewrite chains, and native evaluation — as a
least-fixpoint computation.

## What is Ascent?

[Ascent](https://github.com/s-arash/ascent) is a Rust proc-macro that embeds
a Datalog engine.  You declare *relations* (tables of tuples) and *rules*
(Horn clauses that derive new tuples from existing ones).  The engine
iteratively applies all rules until no new facts are derived (the *fixpoint*).

MeTTaIL generates an `ascent!` struct for each language that contains all
relations and rules needed to evaluate programs.

## Generated Relations

**Source:** `macros/src/logic/relations.rs`

For RhoCalc with categories `{Proc, Name, Int, Float, Bool, Str}`, the
following relations are generated:

### Category relations (one per type)

```
relation proc(Proc);
relation name(Name);
relation int(Int);
relation float(Float);
relation bool_rel(Bool);       // "bool" is a keyword, so suffixed
relation str_rel(Str);
```

These hold all *discovered* terms.  Seeded with the parsed input and expanded
by category exploration rules.

### Equivalence relations

```
relation eq_proc(Proc, Proc);
relation eq_name(Name, Name);
relation eq_int(Int, Int);
relation eq_float(Float, Float);
relation eq_bool(Bool, Bool);
relation eq_str(Str, Str);
```

Hold pairs `(a, b)` where `a` and `b` are structurally equivalent per the
`equations { ... }` block.  Reflexive, symmetric, and transitive closure is
computed by generated rules.

### Rewrite relations

```
relation rw_proc(Proc, Proc);
relation rw_name(Name, Name);
```

Hold directed pairs `(source, target)` where `source ~> target` per the
`rewrites { ... }` block.

### Fold relations

```
relation fold_proc(Proc, Proc);
```

Hold pairs `(original, reduced)` where `original` is a term with `fold`
annotation (e.g., `Add(CastInt(3), CastInt(4))`) and `reduced` is its native
evaluation result (e.g., `CastInt(7)`).  Only generated for categories that
have at least one fold rule.

### Step-term relation

```
relation step_term(Proc);
```

Holds the primary-category term(s) that drive the computation.  Seeded with
the initially parsed term.  Additional terms are added as rewrites discover
new reachable states.

### Custom relations (from `logic { ... }`)

```
relation path(Proc, Proc);
relation trans(Proc, Proc, Proc);
```

Declared in the custom logic block and extracted at parse time by
`extract_relation_decls()`.

## Generated Rules

### Category Exploration Rules

**Source:** `macros/src/logic/categories.rs`

For every constructor, a *decomposition rule* is generated that extracts
sub-terms and seeds their respective category relations:

```ascent
// If we know a Proc term, decompose it
proc(__sub_n) <-- proc(p), if let Proc::PDrop(n) = p, let __sub_n = (**n).clone();
    // ↪ seeds name(n) so the Name sub-expression is explored

proc(__sub_p) <-- proc(p), if let Proc::Add(a, b) = p,
    let __sub_a = (**a).clone(),
    let __sub_b = (**b).clone();
    // ↪ seeds proc(a) and proc(b)

name(__sub_p) <-- name(n), if let Name::NQuote(p) = n, let __sub_p = (**p).clone();
    // ↪ seeds proc(p) for cross-category exploration
```

This ensures that every sub-expression reachable from the input is present
in the appropriate category relation, enabling equation/rewrite matching
at any depth.

### Equation Rules

**Source:** `macros/src/logic/equations.rs`

The `QuoteDrop` equation generates:

```ascent
// Forward: @(*(N)) = N
eq_name(__rhs, __lhs) <--
    name(__lhs),
    if let Name::NQuote(__p) = __lhs,
    if let Proc::PDrop(__n) = &**__p,
    let __rhs = (**__n).clone();

// Backward (symmetry): N = @(*(N))
eq_name(__lhs, __rhs) <--
    name(__rhs),
    // ... (symmetric pattern)
```

Additionally, *reflexivity* and *transitivity* rules are generated for each
equivalence relation:

```ascent
// Reflexivity
eq_proc(p, p) <-- proc(p);

// Transitivity
eq_proc(a, c) <-- eq_proc(a, b), eq_proc(b, c);

// Symmetry (already covered by forward + backward generation)
```

### Congruence Rules (for Equations)

**Source:** `macros/src/logic/congruence.rs`

For each constructor, congruence rules propagate equivalences through
the constructor:

```ascent
// If sub-terms are equivalent, the outer terms are equivalent
eq_proc(
    Proc::Add(Box::new(a1.clone()), Box::new(b.clone())),
    Proc::Add(Box::new(a2.clone()), Box::new(b.clone()))
) <--
    eq_proc(a1, a2), proc(b);
```

This ensures that if `3 = 3` and `4 = 4`, then `Add(3, 4) = Add(3, 4)`.

### Base Rewrite Rules

**Source:** `macros/src/logic/rules.rs`

The `Exec` rewrite generates:

```ascent
// Exec: *(@ P) ~> P
rw_proc(__rhs, __lhs) <--
    step_term(__src),
    proc(__src),
    if let Proc::PDrop(__p) = __src,
    if let Name::NQuote(__body) = &**__p,
    let __rhs = (**__body).clone();
```

The `Comm` rule generates a more complex rule with collection pattern matching,
zip iteration, and substitution — the pattern-match logic from
`macros/src/logic/rules.rs` handles `...rest`, `*zip().*map()`, and `(eval ...)`
patterns.

### Congruence Rules (for Rewrites)

Congruence rules like `ParCong` and `AddCongL`/`AddCongR` propagate rewrites
through constructors:

```ascent
// ParCong: if S ~> T then {S, ...rest} ~> {T, ...rest}
rw_proc(
    Proc::PPar(/* bag with s and rest */),
    Proc::PPar(/* bag with t and rest */)
) <--
    rw_proc(__s, __t),
    proc(Proc::PPar(__elems)),
    // ... iterate over elems, find s, replace with t

// AddCongL: if S ~> T then Add(S, X) ~> Add(T, X)
rw_proc(
    Proc::Add(Box::new(__s.clone()), Box::new(__x.clone())),
    Proc::Add(Box::new(__t.clone()), Box::new(__x.clone()))
) <--
    rw_proc(__s, __t), proc(__x);
```

### Fold / Big-Step Rules

**Source:** `macros/src/logic/rules.rs` (fold logic is integrated into the
rewrite/rules generation module)

For each term with the `fold` annotation, a fold rule is generated:

```ascent
// Add fold: if both operands reduce to native ints, compute the sum
fold_proc(
    Proc::Add(Box::new(a.clone()), Box::new(b.clone())),
    result.clone()
) <--
    proc(Proc::Add(a_box, b_box)),
    let a = (**a_box).clone(),
    let b = (**b_box).clone(),
    // Execute the native eval block:
    let result = { match (&a, &b) {
        (Proc::CastInt(a), Proc::CastInt(b)) =>
            Proc::CastInt(Box::new(*a.clone() + *b.clone())),
        _ => Proc::Err,
    }},
    if result != Proc::Err;

// Fold results become rewrites
rw_proc(original, reduced) <-- fold_proc(original, reduced);
```

The `fold` annotation triggers two things:
1. The native eval block (`![...]`) is wrapped in a fold rule
2. `fold_proc` results are promoted to `rw_proc` entries, so fold results
   participate in the rewrite graph

### Step-Term Propagation

```ascent
step_term(t) <-- rw_proc(_, t);
```

Every rewrite target is added to `step_term`, driving further exploration.

### Custom Logic

The content of the `logic { ... }` block is injected verbatim after all
generated rules:

```ascent
// From RhoCalc's logic block:
proc(p) <-- if let Ok(p) = Proc::parse("^x.{{ x | serv!(req) }}");
proc(p) <-- if let Ok(p) = Proc::parse("^x.{x}");

proc(res) <--
    step_term(p), proc(c),
    if let Proc::LamProc(_) = c,
    let app = Proc::ApplyProc(Box::new(c.clone()), Box::new(p.clone())),
    let res = app.normalize();

relation path(Proc, Proc);
path(p0, p1) <-- rw_proc(p0, p1);
path(p0, p2) <-- path(p0, p1), path(p1, p2);

relation trans(Proc, Proc, Proc);
// ...
```

## Ascent Struct Generation

**Source:** `macros/src/gen/runtime/language.rs`

The Ascent code is wrapped in a single named struct:

```rust
ascent! {
    struct RhoCalcAscent;

    // ... all relations ...
    // ... all rules ...
}
```

Key design decision: a *named* `ascent!` struct (not `ascent_run!`) is used.
This reduces monomorphization from ~13 to ~4 instances (69% reduction), cutting
compile times from ~529s to ~59s.

The raw Ascent content (relations + rules) is passed directly to the `ascent!`
macro — no `include_source!` callback, which would fail in proc-macro output.

## Data Flow: `3 + 4` Through Ascent

```
┌─────────────────────────────────┐
│ Seed: proc(Add(CastInt(3),      │
│              CastInt(4)))       │
│       step_term(Add(...))       │
└──────────────┬──────────────────┘
               │
               ▼
┌─────────────────────────────────┐
│ Category exploration:           │
│   proc(CastInt(3))              │
│   proc(CastInt(4))              │
│   int(NumLit(3))                │
│   int(NumLit(4))                │
└──────────────┬──────────────────┘
               │
               ▼
┌─────────────────────────────────┐
│ Fold rule fires:                │
│   fold_proc(                    │
│     Add(CastInt(3), CastInt(4)),│
│     CastInt(NumLit(7))          │
│   )                             │
│                                 │
│ Promoted to rewrite:            │
│   rw_proc(                      │
│     Add(CastInt(3), CastInt(4)),│
│     CastInt(NumLit(7))          │
│   )                             │
└──────────────┬──────────────────┘
               │
               ▼
┌─────────────────────────────────┐
│ step_term(CastInt(NumLit(7)))   │
│ proc(CastInt(NumLit(7)))        │
│ int(NumLit(7))                  │
│                                 │
│ No more rules fire → FIXPOINT   │
└─────────────────────────────────┘
```

The Ascent engine discovers that `3 + 4` rewrites to `7` in a single fixpoint
computation.

---

**Next:** [06-runtime-evaluation.md](06-runtime-evaluation.md) — the complete
runtime execution path from source text to displayed result.
