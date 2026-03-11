# Predicated Types Design

Predicated types extend Rholang's receive (`for`) with compile-time and
runtime guard predicates. This document describes the end-to-end pipeline from
surface syntax through MSO formula compilation to automaton-based guard
evaluation and codegen.

## 1. Surface Syntax

Rholang's receive binds values from channels. Predicated types add guard
expressions after the binder:

```rholang
// Structural pattern (Layer 1 -- existing Pratt/RD matching)
for (@{x!(y)} <- ch) { P }

// Predicated type guard (Layer 2+)
for (@x : halts /\ primes <- ch) { P }

// Combined structural + predicated
for (@{x!(y)} : finite /\ ground <- ch) { P }

// Multi-channel with cross-channel predicates
for (@x <- ch1, @y : related(x) <- ch2) { P }

// Quantified predicates
for (@x : forall y. (reachable(x, y) => safe(y)) <- ch) { P }

// Bounded predicates with explicit depth
for (@x : exists_{k=100} y. (x ->* y /\ halts(y)) <- ch) { P }
```

### Predicate Sublanguage

```
guard  ::= atom                        -- atomic predicate
         | guard '/\' guard            -- conjunction (and)
         | guard '\/' guard            -- disjunction (or)
         | '~' guard                   -- negation
         | 'forall' var '.' guard      -- universal quantification
         | 'exists' var '.' guard      -- existential quantification
         | 'exists_{k=' N '}' var '.' guard  -- bounded existential
         | 'forall_{k=' N '}' var '.' guard  -- bounded universal
         | '(' guard ')'              -- grouping
         | guard '=>' guard            -- implication (sugar for ~a \/ b)

atom   ::= IDENT                       -- named predicate (e.g. halts, primes)
         | IDENT '(' expr, ... ')'     -- parameterized predicate
         | expr '->*' expr             -- reachability
         | expr '==' expr              -- equality
```

## 2. End-to-End Pipeline

The pipeline has five stages. Each stage is labeled with the modules that
implement it.

```
┌───────────────────────────────────────────────────────────────┐
│ Stage 1: PARSE                                                │
│ Surface syntax → Predicate AST                                │
│ Modules: Pratt parser, weighted_mso.rs (WeightedMsoFormula)  │
└───────────────────┬───────────────────────────────────────────┘
                    │
                    ▼
┌───────────────────────────────────────────────────────────────┐
│ Stage 2: CLASSIFY                                             │
│ Decidability tier assignment (T1--T4)                         │
│ Modules: symbolic.rs (classify_decidability),                │
│          weighted_mso.rs (classify_formula)                   │
└───────────────────┬───────────────────────────────────────────┘
                    │
                    ▼
┌───────────────────────────────────────────────────────────────┐
│ Stage 3: COMPILE                                              │
│ Formula → Automaton (T1/T2) or bounded checker (T3)          │
│ Modules: weighted_mso.rs (to_weighted_automaton),            │
│          symbolic.rs (SymbolicAutomaton), parity_tree.rs,     │
│          register_automata.rs                                 │
└───────────────────┬───────────────────────────────────────────┘
                    │
                    ▼
┌───────────────────────────────────────────────────────────────┐
│ Stage 4: OPTIMIZE                                             │
│ Guard simplification, overlap elimination, fusion             │
│ Modules: symbolic.rs (minimize, intersect),                  │
│          multi_tape.rs (cross-channel), cost_benefit.rs      │
└───────────────────┬───────────────────────────────────────────┘
                    │
                    ▼
┌───────────────────────────────────────────────────────────────┐
│ Stage 5: CODEGEN                                              │
│ Automaton → Rust guard code (match arms, Ascent joins)       │
│ Modules: macros crate (code generation), Ascent relation     │
│          joins, probabilistic.rs (selectivity ordering)      │
└───────────────────────────────────────────────────────────────┘
```

## 3. Stage Details with Rholang Examples

### Stage 1: Parse

The predicate sublanguage is parsed by PraTTaIL's Pratt parser into a
`WeightedMsoFormula` AST:

```rholang
for (@x : halts /\ primes <- ch) { P }
```

Parses to:

```
WeightedMsoFormula::And(
    Box::new(WeightedMsoFormula::AtomicPos {
        label: "halts".into(),
        var: "x".into(),
    }),
    Box::new(WeightedMsoFormula::AtomicPos {
        label: "primes".into(),
        var: "x".into(),
    }),
)
```

For quantified predicates:

```rholang
for (@x : forall y. (reachable(x, y) => safe(y)) <- ch) { P }
```

Parses to:

```
WeightedMsoFormula::ForallFirst {
    var: "y".into(),
    body: Box::new(WeightedMsoFormula::Or(
        Box::new(WeightedMsoFormula::NegAtomicPos {
            label: "reachable(x, y)".into(),
            var: "y".into(),
        }),
        Box::new(WeightedMsoFormula::AtomicPos {
            label: "safe".into(),
            var: "y".into(),
        }),
    )),
}
```

### Stage 2: Classify (Decidability Tiering)

Every predicate formula is classified into one of four tiers. The tier
determines compile-time and runtime handling.

```
┌─────────┬───────────────────────────┬──────────────────────────────────┐
│  Tier   │  Classification           │  Handling                        │
├─────────┼───────────────────────────┼──────────────────────────────────┤
│   T1    │  Compile-time decidable   │  Static elimination (true/false) │
│         │                           │  Dead-code eliminate if false    │
├─────────┼───────────────────────────┼──────────────────────────────────┤
│   T2    │  Runtime decidable        │  Generate efficient checking     │
│         │                           │  code; Ascent relation joins     │
├─────────┼───────────────────────────┼──────────────────────────────────┤
│   T3    │  Semi-decidable           │  Bounded iteration with depth    │
│         │                           │  limit; accept/reject/unknown    │
├─────────┼───────────────────────────┼──────────────────────────────────┤
│   T4    │  Undecidable              │  Require user proof/assertion;   │
│         │                           │  optional runtime monitor        │
└─────────┴───────────────────────────┴──────────────────────────────────┘
```

#### T1 Examples: Compile-Time Decidable

```rholang
// Structural pattern only -- resolved by pattern matching at compile time
for (@{x!(y)} <- ch) { ... }

// Constant predicate
for (@x : true <- ch) { ... }           // always matches
for (@x : false <- ch) { ... }          // dead receive (SYM01 lint)

// Finite-domain universal
for (@x : forall c in {Red, Green, Blue}. color_valid(c) <- ch) { ... }
```

Classification algorithm: all quantified domains are finite and all atoms are
ground-decidable (no free variables over infinite domains).

#### T2 Examples: Runtime Decidable

```rholang
// Ascent relation query
for (@x : is_wellformed(x) <- ch) { ... }

// Register equality
for (@x : x == last_seen <- ch) { ... }

// Finite-state property
for (@x : parity(x) == 0 <- ch) { ... }
```

Classification algorithm: all `Atom` predicates correspond to declared Ascent
relations in the `logic {}` block or are register-testable (M6).

#### T3 Examples: Semi-Decidable

```rholang
// Bounded reachability
for (@x : exists_{k=100} y. (x ->* y /\ halts(y)) <- ch) { ... }

// Depth-limited model checking
for (@x : exists_{k=50} path. safe_along(path) <- ch) { ... }
```

Classification algorithm: quantifiers over non-finite domains with an explicit
or inferable bound.

#### T4 Examples: Undecidable

```rholang
// General halting (Rice's theorem)
for (@x : halts(x) <- ch) { ... }

// Unbounded universal over infinite domain
for (@x : forall y. (x ->* y => safe(y)) <- ch) { ... }
```

Classification algorithm: everything not in T1--T3. Requires user assertion
(`assert_pred`) or Rocq certificate. Generates lint MSO01 if unverified.

### Stage 3: Compile

The compilation strategy depends on the tier:

#### T1: Static Elimination

The formula is evaluated at compile time. If `true`, the guard is removed
entirely. If `false`, the receive is dead-code eliminated (lint SYM01).

#### T2: Automaton Compilation

```
WeightedMsoFormula
       │
       ▼  to_weighted_automaton()  [weighted_mso.rs]
SymbolicAutomaton<A>
       │
       ▼  determinize()            [symbolic.rs]
Deterministic SFA
       │
       ▼  minimize()               [symbolic.rs]
Minimal deterministic SFA
```

For tree-structured predicates (mu-calculus):

```
MuCalculusFormula
       │
       ▼  mu_calculus_to_pata()    [parity_tree.rs]
ParityAlternatingTreeAutomaton<W>
```

For data-aware predicates (register tests):

```
DataPredicate
       │
       ▼  compile_to_register()    [register_automata.rs]
RegisterAutomaton<W>
```

#### T3: Bounded Checker

```
BoundedFormula(k)
       │
       ▼  unroll to depth k
Finite automaton (k-bounded)
       │
       ▼  wrap in timeout/counter
BoundedChecker { automaton, depth_limit: k }
```

#### T4: User Assertion

No automaton is compiled. The guard is wrapped in an `assert_pred` call that
either trusts a user annotation or defers to a Rocq proof certificate.

### Stage 4: Optimize

Guard optimization occurs after compilation:

```
Guard A: halts(x)           Guard B: primes(x)
    │                           │
    ▼                           ▼
SFA_A                        SFA_B
    │                           │
    └─────────┬─────────────────┘
              ▼
        intersect(SFA_A, SFA_B)     [symbolic.rs]
              │
              ▼
        minimize(intersection)      [symbolic.rs]
              │
              ▼
        Fused guard automaton
```

For multi-channel predicates, M8 (multi-tape) fuses cross-channel constraints:

```
for (@x <- ch1, @y : related(x) <- ch2) { P }
       │               │
       ▼               ▼
    tape 1           tape 2
       │               │
       └───────┬───────┘
               ▼
    WeightedMultiTapeAutomaton<W, 2>   [multi_tape.rs]
               │
               ▼  auto_intersect(0, 1)
    Cross-channel constrained automaton
```

For cross-channel constraint propagation, M11 (two-way) resolves backward
dependencies:

```
for (@x <- ch1, @y : f(x, y) <- ch2) { P }
       │
       ▼  backward_constraint(ch2_guard, ch1)   [two_way_transducer.rs]
    ChannelConstraint {
        forward_transducer:  ch1_value → evaluate f(x, _)
        backward_transducer: ch2_guard → constrain ch1_values
    }
```

Cost-benefit analysis (M7 probabilistic) orders guards by selectivity:

```
Guard            Selectivity    Order
halts(x)         0.01 (1%)      1 (check first -- eliminates 99%)
primes(x)        0.15 (15%)     2
ground(x)        0.80 (80%)     3 (check last -- eliminates only 20%)
```

### Stage 5: Codegen

The compiled automaton generates Rust code for guard evaluation.

#### T2 Guard: Ascent Relation Join

```rholang
for (@x : is_wellformed(x) <- ch) { P }
```

Generates:

```rust
// In Ascent logic block
relation is_wellformed(Term);
// ... rules populating is_wellformed ...

// In receive handler
if ascent_program.is_wellformed.contains(&(value.clone(),)) {
    // execute P
}
```

#### T2 Guard: Compiled SFA Matcher

```rholang
for (@x : x > 0 /\ x < 100 <- ch) { P }
```

The `IntervalAlgebra` compiles this to a range check:

```rust
// Generated from minimized SFA with IntervalAlgebra
fn guard_check(x: i64) -> bool {
    x > 0 && x < 100  // simplified from SFA transitions
}
```

#### T2 Guard: Register Automaton

```rholang
for (@x : x == last_seen <- ch) { P }
```

Generates:

```rust
// Register automaton with 1 register
let mut reg: Option<DataValue> = None;
// ... on receive:
match reg {
    Some(ref v) if v == &x => { /* execute P */ }
    None => { reg = Some(x.clone()); /* first-time: store */ }
    _ => { /* guard fails */ }
}
```

#### T3 Guard: Bounded Iteration

```rholang
for (@x : exists_{k=100} y. (x ->* y /\ halts(y)) <- ch) { P }
```

Generates:

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
    TriState::False  // exhausted search space within bound
}
```

## 4. Module Connections

Each of the 11 advanced automata modules contributes to the predicated types
pipeline:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    PREDICATED TYPES PIPELINE                            │
├──────────────────────┬──────────────────────────────────────────────────┤
│ Module               │ Role in Predicated Types                        │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M1  Symbolic         │ BooleanAlgebra trait provides the core          │
│                      │ predicate algebra. Guard satisfiability,        │
│                      │ overlap detection, subsumption. SFA             │
│                      │ compilation target for T2 guards.               │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M2  W. Buchi         │ Infinite behavior predicates for reactive       │
│                      │ processes: omega-regular guards on streams.     │
│                      │ E.g., "channel always eventually delivers."     │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M3  Poly. AWA        │ forall/exists quantifier evaluation as          │
│                      │ product/sum states. H-polynomial fixpoints      │
│                      │ for recursive predicates (letprop). Strictly    │
│                      │ more powerful than WA for cost analysis.        │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M4  W. VPA           │ Quantifier scope nesting maps to call/return    │
│                      │ structure. Weighted inclusion checks verify     │
│                      │ guard nesting is well-formed.                   │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M5  Parity Tree      │ Behavioral predicates as mu-calculus formulas.  │
│                      │ mu_calculus_to_pata() compiles letprop to       │
│                      │ PATA. Emptiness check validates predicates.     │
│                      │ Complement generates counterexample ASTs.       │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M6  Register         │ Data-aware predicates referencing channel       │
│                      │ names and process variables. Register           │
│                      │ equality/freshness tests. Stateful guard        │
│                      │ evaluation with memory.                         │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M7  Probabilistic    │ Guard selectivity estimation -- how selective   │
│                      │ is a guard against the expected input           │
│                      │ distribution. Orders guards for short-circuit   │
│                      │ evaluation (most selective first).              │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M8  Multi-Tape       │ Multi-channel receives map to multi-tape:      │
│                      │ for (@x <- ch1, @y <- ch2) { P }               │
│                      │ Each channel is a tape. Cross-tape              │
│                      │ auto-intersection enforces shared constraints.  │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M9  Multiset         │ Cardinality predicates: count(chan) >= 3.       │
│                      │ Resource counting via multiset semiring.        │
│                      │ PPar analysis with HashBag multiplicities.      │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M10 W. MSO           │ THE specification language. User syntax         │
│                      │ forall, exists, /\, \/, ~ is literally          │
│                      │ weighted MSO. to_weighted_automaton() compiles  │
│                      │ formulas. check_decidability() assigns tiers.   │
├──────────────────────┼──────────────────────────────────────────────────┤
│ M11 W. Two-Way       │ Cross-channel predicates: given value on ch2,  │
│                      │ backward-propagate constraints to ch1.          │
│                      │ Join pattern reordering for optimal             │
│                      │ multi-channel consumption.                      │
└──────────────────────┴──────────────────────────────────────────────────┘
```

## 5. Decidability Tiering in Detail

### T1: Compile-Time Decidable

**Criterion**: Predicate contains only structural patterns, constant atoms,
and forall/exists over finite enumerable domains.

**Algorithm** (in `symbolic.rs`):
1. Check all quantified domains are finite (enum types, small finite sets).
2. Check all atoms are ground-decidable (no free variables over infinite domains).
3. If both hold: T1.

**Compile-time action**: Resolve to `true`/`false`. Dead-code eliminate false
guards. No runtime cost.

**Concrete examples**:

| Predicate | Domain | Decision |
|-----------|--------|----------|
| `true` | -- | T1 (trivially true) |
| `false` | -- | T1 (trivially false, dead receive) |
| `forall c in {R,G,B}. valid(c)` | 3-element enum | T1 (check all 3) |
| `x > 5 /\ x < 10` | `i64` interval | T1 (interval algebra) |
| `is_nil(x)` | structural | T1 (pattern match) |

### T2: Runtime Decidable

**Criterion**: Predicate references only declared Ascent relations or register-
testable properties.

**Algorithm** (in `symbolic.rs`):
1. All `Atom` predicates correspond to declared relations in `logic {}`.
2. All register operations are testable at runtime.
3. If both hold: T2.

**Compile-time action**: Generate efficient checking code. Warn if expensive
(high relation cardinality).

**Runtime action**: Ascent join clause or generated matcher. Constant or
logarithmic lookup per guard evaluation.

**Concrete examples**:

| Predicate | Mechanism | Cost |
|-----------|-----------|------|
| `is_wellformed(x)` | Ascent relation lookup | O(1) hash lookup |
| `x == last_seen` | Register equality test | O(1) comparison |
| `parity(x) == 0` | DFA state check | O(length(x)) |
| `type_of(x) == Int` | Ascent relation | O(1) hash lookup |

### T3: Semi-Decidable

**Criterion**: Quantifiers over non-finite domains with an explicit or
inferable bound.

**Algorithm** (in `symbolic.rs`):
1. Exists depth/step bound that makes the predicate decidable.
2. E.g., `forall x'. not(x ->* x')` with bound k becomes "no reduction chain
   of length <= k".
3. If bound exists: T3.

**Compile-time action**: Bounded checking with configurable depth limit. Warn
about incompleteness.

**Runtime action**: Bounded iteration with timeout. Returns
`accept`/`reject`/`unknown`.

**Concrete examples**:

| Predicate | Bound | Completeness |
|-----------|-------|-------------|
| `exists_{k=100} y. halts(y)` | k=100 steps | Sound but incomplete |
| `forall_{k=50} path. safe(path)` | k=50 depth | Sound but incomplete |
| `exists y. (x ->* y)` with inferred bound | inferred from grammar | Depends on grammar structure |

### T4: Undecidable

**Criterion**: Everything not in T1--T3. Conservative default.

**Compile-time action**: Require user proof/assertion. Lint MSO01 if unverified.

**Runtime action**: Trust user assertion. Optional runtime monitor (best-effort
detection, no guarantee).

**Concrete examples**:

| Predicate | Why Undecidable | Mitigation |
|-----------|----------------|------------|
| `halts(x)` | Rice's theorem | User proof or Rocq certificate |
| `forall y. (x ->* y => safe(y))` | Unbounded universal over infinite domain | `assert_pred` annotation |
| `forall X. phi(X)` | Second-order universal (MSO01) | Restricted MSO fragment or user proof |

### Classification Decision Tree

```
Formula φ
    │
    ├── All atoms ground-decidable?
    │   ├── Yes: All quantifiers over finite domains?
    │   │   ├── Yes ──────────────────────────► T1
    │   │   └── No: Explicit or inferable bound?
    │   │       ├── Yes ──────────────────────► T3
    │   │       └── No ───────────────────────► T4
    │   └── No: All atoms are declared Ascent relations?
    │       ├── Yes ──────────────────────────► T2
    │       └── No: Register-testable?
    │           ├── Yes ──────────────────────► T2
    │           └── No ───────────────────────► T4
    └── Contains ∀X (second-order universal)?
        └── Yes ──────────────────────────────► T4 (MSO01 lint)
```

## 6. Guard Compilation Strategy

### 6.1 Single-Channel Guards

For a single receive `for (@x : phi(x) <- ch) { P }`:

```
phi(x)
  │
  ▼  classify_decidability()
Tier
  │
  ├─ T1 ─► static evaluate ─► eliminate or pass through
  │
  ├─ T2 ─► to_weighted_automaton() ─► determinize() ─► minimize()
  │        ─► codegen: SFA transition table or Ascent join
  │
  ├─ T3 ─► unroll(k) ─► compile bounded automaton
  │        ─► codegen: bounded_check() with depth counter
  │
  └─ T4 ─► emit MSO01 lint ─► codegen: assert_pred() wrapper
```

### 6.2 Multi-Channel Guards

For `for (@x <- ch1, @y : f(x, y) <- ch2) { P }`:

```
Step 1: Classify each guard independently
Step 2: Detect cross-channel dependencies (x referenced in ch2's guard)
Step 3: Build multi-tape automaton (M8) or two-way transducer (M11)
Step 4: Optimize consumption order via selectivity (M7)
Step 5: Codegen coordinated guard evaluation
```

### 6.3 Recursive Predicates (`letprop`)

User-defined predicates compile through the mu-calculus:

```rholang
letprop halt x = forall x'. ~(x ->* x') in
for (@x : halt <- ch) { P }
```

Compilation:

```
letprop halt x = forall x'. ~(x ->* x')
  │
  ▼  Parse to mu-calculus
nu X. box_{->*}(~X)
  │
  ▼  mu_calculus_to_pata()         [parity_tree.rs]
ParityAlternatingTreeAutomaton
  │
  ▼  classify_decidability()
T4 (undecidable in general)
  │
  ▼  Require assert_pred or bounded variant
```

If the user provides a bounded variant:

```rholang
letprop halt_{100} x = forall_{k=100} x'. ~(x ->* x') in
for (@x : halt_{100} <- ch) { P }
```

This is T3 and compiles to a bounded checker.

## 7. Runtime vs Compile-Time Evaluation

```
┌───────────────────────────────────────────────────────────────────┐
│                    Evaluation Strategy                             │
├─────────┬──────────────────────┬──────────────────────────────────┤
│  Tier   │  Compile-Time        │  Runtime                         │
├─────────┼──────────────────────┼──────────────────────────────────┤
│   T1    │  Full evaluation     │  None (eliminated)               │
│         │  -> true/false       │                                  │
├─────────┼──────────────────────┼──────────────────────────────────┤
│   T2    │  Automaton compiled  │  Automaton executed per receive  │
│         │  SFA minimized       │  O(1) to O(n) per value          │
│         │  Ascent rules gen'd  │  Hash lookup for relations       │
├─────────┼──────────────────────┼──────────────────────────────────┤
│   T3    │  Bounded automaton   │  Bounded iteration per receive   │
│         │  compiled            │  May return Unknown              │
│         │  Depth limit set     │  Configurable timeout            │
├─────────┼──────────────────────┼──────────────────────────────────┤
│   T4    │  assert_pred check   │  Trust annotation                │
│         │  Rocq cert verified  │  Optional runtime monitor        │
│         │  MSO01 lint if none  │  Best-effort only                │
└─────────┴──────────────────────┴──────────────────────────────────┘
```

### Cost Model

| Tier | Compile Cost | Runtime Cost per Receive | Guarantees |
|------|-------------|-------------------------|-----------|
| T1 | O(formula) | 0 (eliminated) | Complete + sound |
| T2 | O(2^formula) worst case | O(value_size) | Complete + sound |
| T3 | O(k x formula) | O(k x value_size) | Sound, not complete |
| T4 | O(proof) | O(1) (trust) | Depends on proof quality |

## 8. Lint Integration

The predicated types pipeline produces diagnostics at several stages:

| Stage | Lint | When |
|-------|------|------|
| Parse | SYM01 | Guard is unsatisfiable (BOT) -- dead receive |
| Parse | SYM02 | Two guards on same channel overlap |
| Classify | MSO01 | Formula uses forall X (not recognizable -- T3/T4) |
| Classify | MSO02 | forall x. phi where phi is not a recognizable step function |
| Compile | PT01 | Predicate unsatisfiable (PATA emptiness) |
| Compile | PT02 | Predicate A subsumes B (redundant check) |
| Compile | PT03 | Priority depth > 4 (exponential blowup) |
| Optimize | SYM03 | Guard A subsumes Guard B (redundant) |
| Optimize | SYM04 | SFA has mergeable states (non-minimal) |
| Optimize | MSO03 | Two guard formulas have identical semantics |
| Codegen | RA01 | Data value referenced but never stored |
| Codegen | RA02 | Register written but never tested |
| Multi-ch | MT01 | Two tapes constrained to identical patterns |
| Multi-ch | MT02 | Tape has no auto-intersection constraints |
| Multi-ch | TW01 | Circular channel dependency (deadlock) |
| Multi-ch | TW03 | Backward constraint propagation divergent |
| Prob | PR01 | Rule handles < 1% of expected inputs |

## 9. Relationship to Brainstorming Doc Layers

The brainstorming document (`02-23-pattern-matching.md`) defines Layer 1 as
structural guards plus Ascent relation joins. This plan extends to Layers 2--4:

| Layer | Scope | Infrastructure |
|-------|-------|---------------|
| **Layer 1** | Structural patterns + Ascent joins | Existing Pratt/RD parser + `BehavioralPred { relation_name, args }` |
| **Layer 2** | First-order predicate logic | M1 symbolic, M3 alternating, M5 parity tree |
| **Layer 3** | Analysis and verification | Decidability classification, overlap detection, cost estimation |
| **Layer 4** | Extended infrastructure | M8 multi-tape, M9 multiset, M10 weighted MSO specification |

Layer 1's `BehavioralPred { relation_name, args }` becomes a special case of
the general `BooleanAlgebra::Predicate` from M1.

## 10. Cross-References

- **Advanced automata overview**: [advanced-automata-overview.md](../../prattail/docs/design/advanced-automata-overview.md)
- **Semiring catalog**: [semiring-catalog.md](../../prattail/docs/design/semiring-catalog.md)
- **Diagnostics reference**: [README.md](../../prattail/docs/diagnostics/README.md)
- **Plan**: `/home/dylon/.claude/plans/lexical-stargazing-whisper.md`
- **Pattern matching brainstorming**: `/home/dylon/Downloads/02-23-pattern-matching.md`

## 11. References

- Droste, M. & Gastin, P. "Weighted Automata and Weighted Logics" (TCS 380, 2007)
- D'Antoni, L. & Veanes, M. "Minimization of Symbolic Automata" (POPL 2014)
- Emerson, E. A. & Jutla, C. S. "Tree Automata, Mu-Calculus and Determinacy" (FOCS 1991)
- Feng, B. & Maletti, A. "Weighted Two-Way Transducers" (CAI 2022)
- Kaminski, M. & Francez, N. "Finite-Memory Automata" (TCS 134, 1994)
- Kempe, A. "Weighted Multi-Tape Automata and Transducers for NLP" (2004)
- Kostolanyi, A. & Misun, F. "Alternating Weighted Automata over Commutative Semirings" (TCS 740, 2018)
