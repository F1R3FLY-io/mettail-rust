# The `guards { }` Block: Language-Generic Guard Configuration

> **Authoritative reference & live-vs-spec status.** For exactly which parts of
> this `guards { }` specification parse and are wired today versus which are
> proposed sublanguage, the parser-grounded reference is
> [06 — Guard Syntax and Extensions](../architecture/semantic-predicates/06-guard-syntax-and-extensions.md)
> in the semantic-predicate suite
> ([`docs/architecture/semantic-predicates/`](../architecture/semantic-predicates/README.md)).
> Note also that guard evaluation is now **classify-only at compile time** (the
> prattail EBA `𝔅` / SFA / SFT / Heyting tower emits coverage evidence and a
> quality tag) plus **host-routed enforcement at run time** (RSpace structural
> matching, a Rholang `where` boolean guard, or a host-routed `RhoNativeJoin`) —
> it is no longer the Ascent / Datalog fixpoint model that earlier drafts assumed.

> **Scope.** This document specifies the `guards { }` block of the `language!`
> macro — the configuration layer that lets each MeTTaIL-defined language
> declare its guard sublanguage explicitly: built-in predicates, logical
> connective keyword spellings, constraint theory registrations, and channel
> declarations for multi-channel guard dispatch. The companion document
> [predicated-types.md](predicated-types.md) §2A is the design specification;
> this document is the implementor- and user-facing guide.

---

## Table of Contents

1. [Motivation and Rationale](#1-motivation-and-rationale)
2. [Notation, Symbols, and Acronyms](#2-notation-symbols-and-acronyms)
3. [The Block at a Glance](#3-the-block-at-a-glance)
4. [Predicate Declarations](#4-predicate-declarations)
5. [The `connectives { }` Sub-block](#5-the-connectives--sub-block)
6. [The `theories { }` Sub-block](#6-the-theories--sub-block)
7. [The `channels { }` Sub-block](#7-the-channels--sub-block)
8. [`@[ … ]` Selectivity and Cost Annotations](#8--selectivity-and-cost-annotations)
9. [Composition: `extends`, `includes`, `mixins`](#9-composition-extends-includes-mixins)
10. [Closed-World vs Open-World Resolution](#10-closed-world-vs-open-world-resolution)
11. [Architecture: From Macro to Pipeline](#11-architecture-from-macro-to-pipeline)
12. [Pseudocode: Key Algorithms](#12-pseudocode-key-algorithms)
13. [Worked Examples Across Paradigms](#13-worked-examples-across-paradigms)
14. [Diagnostics](#14-diagnostics)
15. [References](#15-references)

---

## 1. Motivation and Rationale

The `language!` macro generates a complete language implementation —
parser, term operations, normalizer, rewriter, Datalog logic — from a
declarative specification. Before the `guards { }` block existed, three
related concerns were handled by **hardcoded keyword heuristics** inside
the prattail crate's analysis pipeline:

1. **Logical connective spelling.** The behavioral predicate parser
   recognized `&&`, `||`, `~`/`!`, and `=>` as the only spellings of
   conjunction, disjunction, negation, and implication. A language whose
   surface syntax used `and`/`or`/`not` (Rholang) or `&&`/`~` (MeTTa-style)
   could not redirect the parser without forking the macro.

2. **Built-in predicate availability.** Predicates like `eq`, `gt`,
   `fresh`, `ground`, and `count_ge` were always available with fixed
   syntax. There was no way to enable a subset, declare alternative
   spellings, give them custom fixity, or parametrize them by type.

3. **Constraint theory dispatch.** The pipeline used name-matching
   functions like `is_arithmetic_relation()`, `is_unification_relation()`,
   and `is_subtype_relation()` to decide which automaton modules
   (M12 Linear Arithmetic, M13 Unification, M14 Subtype Lattice) to
   activate. The lists were "temporary, not extensible, brittle"
   ([predicated-types.md](predicated-types.md) §16, "Relation Name
   Heuristics"). User-defined predicates with novel names missed
   theory-specific modules.

4. **Multi-channel dispatch.** Activation of the M8 (Multi-Tape) and
   M11 (Two-Way Transducer) modules was inferred from cross-category
   references in grammar rules. This over-approximated for any language
   with multiple categories that referenced each other (e.g., a Lambda
   calculus with `Term` and `Type` categories), even when no actual
   communication channels existed.

The `guards { }` block solves all four problems by letting the grammar
author **explicitly** declare what their language exposes, what it
spells things, and which theories it uses. The macro and pipeline then
consult these declarations as the authoritative source of truth, falling
back to heuristics only when the block is omitted (preserving backward
compatibility with all existing language definitions).

> **Design principle.** *Explicit beats implicit when the implicit is
> wrong.* Heuristics serve a useful purpose as defaults — they let new
> languages compile with zero ceremony — but they should never overrule
> an explicit declaration. The `guards { }` block is the explicit channel.

---

## 2. Notation, Symbols, and Acronyms

This section defines every symbol and acronym used later in the document
so the reader never has to guess. Each item is also re-introduced in
context at its point of first use.

**Greek and mathematical symbols:**

| Symbol  | Name       | Meaning in this document                                  |
|---------|------------|-----------------------------------------------------------|
| `φ`,`ψ` | phi, psi   | Guard formula or behavioral predicate                     |
| `σ`     | sigma      | Substitution: partial function mapping variables to terms |
| `∧`     | wedge      | Logical conjunction (also written `and`, `&&`, `,`)       |
| `∨`     | vee        | Logical disjunction (also written `or`, `\|\|`)           |
| `¬`     | neg        | Logical negation (also written `not`, `~`, `!`)           |
| `⟹`     | implies    | Material implication (`φ ⟹ ψ` ≡ `¬φ ∨ ψ`)                 |
| `⟸`     | implied-by | Reverse implication (args swapped)                        |
| `⟺`     | iff        | Biconditional (desugared to `(φ⟹ψ) ∧ (ψ⟹φ)`)              |
| `∀`     | forall     | Universal quantifier                                      |
| `∃`     | exists     | Existential quantifier                                    |
| `∈`     | in         | Set membership                                            |
| `∉`     | not-in     | Set non-membership                                        |
| `∪`,`∩` | cup, cap   | Set union, set intersection                               |
| `↦`     | mapsto     | Function/map application                                  |
| `≡`     | equivalent | Definitional or logical equivalence                       |
| `ℕ`     | nats       | Natural numbers (non-negative integers)                   |
| `[a,b]` |            | Closed real interval (e.g., `selectivity ∈ [0.0, 1.0]`)   |

**Acronyms used in this document:**

| Acronym | Expansion                                                           |
|---------|---------------------------------------------------------------------|
| AST     | Abstract Syntax Tree                                                |
| AWA     | Alternating Weighted Automaton                                      |
| CHAM    | Chemical Abstract Machine (Berry & Boudol, 1992)                    |
| DNF     | Disjunctive Normal Form                                             |
| DSL     | Domain-Specific Language                                            |
| FOL     | First-Order Logic                                                   |
| LSP     | Language Server Protocol                                            |
| M*N*    | Module *N* in the predicated-types pipeline (e.g., M8 = Multi-Tape) |
| MSO     | Monadic Second-Order logic                                          |
| RAII    | Resource Acquisition Is Initialization (a Rust idiom for scoping)   |
| SFA     | Symbolic Finite Automaton                                           |
| SFT     | Symbolic Finite Transducer                                          |
| WMA     | Weighted Multi-tape Automaton (Kempe, 2004)                         |
| W2T     | Weighted Two-way Transducer (Feng & Maletti, 2022)                  |

**Module identifiers** (the 15 automaton modules that the pipeline can
activate to analyze a guard):

| ID  | Name              | Purpose (one-line)                                                |
|-----|-------------------|-------------------------------------------------------------------|
| M1  | Symbolic Automata | Always-active baseline; effective Boolean algebra over predicates |
| M2  | Büchi             | ω-regular liveness properties                                     |
| M3  | AWA               | Alternating weighted automata for branching predicates            |
| M4  | VPA               | Visibly pushdown automata for paired-bracket nesting              |
| M5  | Parity Tree       | Mu-calculus fixpoints over tree structures                        |
| M6  | Register          | Data equality and freshness tracking                              |
| M7  | Probabilistic     | Selectivity/cost-driven scheduling under ambiguity                |
| M8  | Multi-Tape        | Synchronized traversal of N channel value tapes                   |
| M9  | Multiset          | Cardinality and AC-matching over collections                      |
| M10 | Weighted MSO      | Always-active baseline; weighted MSO formula compilation          |
| M11 | Two-Way           | Backward constraint propagation across channels                   |
| M12 | Linear Arithmetic | Presburger arithmetic decision procedure                          |
| M13 | Unification       | First-order syntactic unification                                 |
| M14 | Subtype Lattice   | Finite subtype hierarchy with join/meet                           |
| M15 | SFT               | Symbolic finite transducers for output-producing transformations  |

For full definitions of M1–M15, see [predicated-types.md](predicated-types.md)
§§16–18.

---

## 3. The Block at a Glance

The `guards { }` block is a **direct sibling** of `terms { }`, `tokens { }`,
`equations { }`, `rewrites { }`, and `logic { }` inside the `language! { }`
macro. It is **entirely optional** — when omitted, the language gets the
existing heuristic dispatch behavior, exactly as before. When present, its
contents replace the corresponding heuristics for the components that the
author explicitly declares.

```rust
language! {
    name: MyLanguage,
    types { … },
    tokens { … },

    guards {
        // ── Direct items: built-in predicate declarations ──
        eq  . x, y |- x "==" y | "eq" "(" x "," y ")" @[selectivity(0.1)] ;
        gt  . x, y |- x ">"  y                        @[selectivity(0.5)] ;
        fresh . x  |- "fresh" "(" x ")"                                  ;

        // ── Configuration sub-blocks ──
        connectives {
            and = "and" | "∧";
            or  = "or"  | "∨";
            not = "not" | "¬";
        }

        theories {
            arithmetic = PresburgerAlgebra for [Int];
            patterns   = UnificationTheory for [Proc, Name];
            types      = LatticeTheory     for [Proc, Name, Int, Str];
        }

        channels {
            channel Name;
            join PGuardedInput(ch: Name);
        }
    },

    terms { … },
    equations { … },
    rewrites { … },
    logic { … },
}
```

Each top-level item inside `guards { }` is exactly one of:

| Item kind                 | Form                                   | What it declares                                       |
|---------------------------|----------------------------------------|--------------------------------------------------------|
| **Predicate declaration** | `Label . params \|- syntax @[anno]? ;` | A built-in predicate with surface syntax and overrides |
| `connectives { … }`       | sub-block                              | Logical connective role → keyword mapping              |
| `theories { … }`          | sub-block                              | Constraint theory registrations                        |
| `channels { … }`          | sub-block                              | Channel categories and join patterns                   |

The order of items inside `guards { }` is irrelevant. Each kind may
appear at most once (for sub-blocks) or any number of times (for direct
predicate declarations).

---

## 4. Predicate Declarations

A **predicate declaration** introduces a built-in predicate that grammar
authors can use inside guard expressions. The declaration form is the
same syntax-template pattern that `terms { }` uses for grammar rules:

```
Label . params |- syntax_form (| syntax_form)* @[annotations]? ;
```

**Components.**

| Component        | Purpose                                                                            |
|------------------|------------------------------------------------------------------------------------|
| `Label`          | The predicate's canonical identifier (e.g., `eq`, `gt`, `fresh`)                   |
| `params`         | Comma-separated list of parameter names with optional types and quantifiers        |
| `syntax_form`    | A sequence of literal strings and parameter references defining one surface syntax |
| `\|`             | Separates alternative syntax forms for the same predicate (e.g., infix and prefix) |
| `@[annotations]` | Optional `selectivity(s)` and/or `cost(c)` overrides (see §8)                      |

**Example: pure infix.**
```
gt . x, y |- x ">" y ;
```
The compiler generates a Pratt parser entry for the operator `>` taking
two arguments and producing the relation query `gt(x, y)`.

**Example: prefix call form only.**
```
fresh . x |- "fresh" "(" x ")" ;
```

**Example: both infix and prefix call forms (alternatives).**
```
gt . x, y |- x ">" y | "gt" "(" x "," y ")" ;
```
Either `x > y` or `gt(x, y)` parses as `gt(x, y)` in the AST.

**Example: mixfix.**
```
between . x, lo, hi |- x "between" lo "and" hi ;
```
The user can write `5 between 1 and 10`.

**Example: variadic with regex-style quantifier.**
```
eq_chain . xs+ |- "==" "(" xs ")" ;
```
The `xs+` quantifier means "one or more arguments". Other quantifiers:

| Quantifier | Meaning                         |
|------------|---------------------------------|
| `+`        | One or more                     |
| `*`        | Zero or more                    |
| `{m,n}`    | Between *m* and *n* (inclusive) |
| `{m,}`     | At least *m*                    |
| `{,n}`     | At most *n*                     |

The compiler desugars variadic predicates to pairwise applications of
the same label: `eq_chain(a, b, c)` → `eq(a, b) ∧ eq(b, c)`. The
pairwise predicate (`eq` in this case) must also be declared.

**Example: typed parameters.**
```
gt . x: Int, y: Int |- x ">" y ;
gt . x: Str, y: Str |- x ">" y ;
```
The same label `gt` may appear with different parameter types. At
guard-evaluation time, the compiler dispatches to the most specific
type-matching declaration, falling back to a generic (untyped) variant
if present.

**Example: union type for variadic parameters.**
```
all_numeric . xs:(Int|Float)+ |- "all_numeric" "(" xs ")" ;
```
Each argument may be either `Int` or `Float`.

### 4.1 The Param–Syntax Bridge

A parameter name (e.g., `x`) appearing inside a `syntax_form` is a
**Param** reference; everything else inside double quotes is a
**Literal** (terminal symbol). The compiler builds a Pratt parser entry
that consumes the literals and expects parser-recursive subparses
wherever a Param reference appears.

The fixity of the predicate is determined by the position of Params
relative to Literals:

| Pattern                 | Fixity  |
|-------------------------|---------|
| `x ">" y`               | Infix   |
| `"gt" "(" x "," y ")"`  | Prefix  |
| `x "between" y "and" z` | Mixfix  |
| `"is_nan" "(" x ")"`    | Prefix  |
| `x "?"`                 | Postfix |

The reader never has to specify fixity explicitly — it is read off the
syntax template.

---

## 5. The `connectives { }` Sub-block

The `connectives { }` sub-block maps each **logical connective role** to
the surface keyword(s) that spell it. The set of roles is **closed** —
the compiler knows exactly eight roles and which `BehavioralPred` AST
variant each maps to:

| Role         | BehavioralPred Variant            | Common spellings                |
|--------------|-----------------------------------|---------------------------------|
| `and`        | `BehavioralPred::And`             | `"and"`, `"∧"`, `"&&"`          |
| `or`         | `BehavioralPred::Or`              | `"or"`, `"∨"`, `"\|\|"`         |
| `not`        | `BehavioralPred::Not`             | `"not"`, `"¬"`, `"~"`, `"!"`    |
| `entails`    | `BehavioralPred::Implies(p, c)`   | `"entails"`, `"implies"`, `"⟹"` |
| `implied_by` | `BehavioralPred::Implies(c, p)`   | `"implied_by"`, `"⟸"`           |
| `iff`        | `And(Implies(a,b), Implies(b,a))` | `"iff"`, `"⟺"`                  |
| `forall`     | `Quantified { Forall, … }`        | `"forall"`, `"∀"`               |
| `exists`     | `Quantified { Exists, … }`        | `"exists"`, `"∃"`               |

**Example: standard Rholang spelling.**
```rust
connectives {
    and    = "and"    | "∧";
    or     = "or"     | "∨";
    not    = "not"    | "¬";
    forall = "forall" | "∀";
    exists = "exists" | "∃";
}
```

**Example: minimal MeTTa-style spelling.**
```rust
connectives {
    and = "&&";
    not = "~";
}
```
A language that lists only `and` and `not` has no disjunction, no
implication, and no quantifiers in its guard sublanguage. Attempting to
use any unlisted connective is a compile error
([CONN02](#14-diagnostics)).

### 5.1 The `ConnectiveMap` Bidirectional Lookup

Internally, the compiler stores the declarations as a `ConnectiveMap`:

```text
                     ┌──────────────────────────────┐
                     │       ConnectiveMap          │
                     ├──────────────────────────────┤
   role_to_keywords  │  And ↦ ["and", "∧"]          │
                     │  Or  ↦ ["or",  "∨"]          │
                     │  Not ↦ ["not", "¬"]          │
                     ├──────────────────────────────┤
   keyword_to_role   │  "and" ↦ And                 │
                     │  "∧"   ↦ And                 │
                     │  "or"  ↦ Or                  │
                     │  "∨"   ↦ Or                  │
                     │  "not" ↦ Not                 │
                     │  "¬"   ↦ Not                 │
                     └──────────────────────────────┘
```

The two maps satisfy the **bidirectional invariant**:

```
∀ (role, keywords) ∈ role_to_keywords. ∀ kw ∈ keywords.
    keyword_to_role[kw] = role
```

This invariant is enforced at construction time. If two roles claim the
same keyword, lint [CONN01](#14-diagnostics) fires:

> `error[CONN01]: keyword "and" is mapped to multiple connective roles
> (And and Or)`

### 5.2 How the Parser Uses the Map

The behavioral predicate parser is a recursive-descent operator-precedence
climber:

```
parse_pred_implies → parse_pred_or → parse_pred_and → parse_pred_not → parse_pred_atom
```

Each level peeks for its operator. With **no** active `ConnectiveMap`,
the levels recognize the hardcoded Rust tokens (`=>`, `||`, `&&`, `~`,
`!`). With an active map, **the same Rust tokens are still recognized**
(for backward compatibility with default-mode languages), and **in
addition**, each level checks whether the next identifier in the input
is declared as a keyword for that level's role.

The active map is held in a thread-local during parsing of a single
`language!` invocation. A RAII guard installs the map after `guards { }`
is parsed and restores the previous value (or `None`) when the
`language!` parse finishes — even if a parse error or panic occurs.
This is the `ConnectiveMapGuard` type. Because proc-macro expansion is
single-threaded per crate, no synchronization is needed.

> **Why not pass the map as a parser parameter?** The parser chain
> spans many functions across the file, called from many call sites.
> Threading an `Option<&ConnectiveMap>` parameter through every level
> would require refactoring every consumer. The thread-local guard
> achieves the same observable behavior with zero call-site changes,
> with safety guaranteed by single-threaded macro expansion.

---

## 6. The `theories { }` Sub-block

A **constraint theory** is a decision procedure for a class of
predicates: Presburger arithmetic for linear constraints over integers,
unification for syntactic equality of terms, lattice theory for
subtype membership in a finite type hierarchy. The pipeline activates
analysis modules (M12, M13, M14) based on which theories are relevant
to the language's predicates. Without explicit registrations, this
activation is heuristic and brittle (see §1).

The `theories { }` sub-block lets the grammar author register theories
explicitly, with a `for [...]` clause naming the type categories the
theory handles:

```rust
theories {
    arithmetic = PresburgerAlgebra for [Int];
    patterns   = UnificationTheory for [Proc, Name];
    types      = LatticeTheory     for [Proc, Name, Int, Str];
}
```

**Components.**

| Component  | Meaning                                                                            |
|------------|------------------------------------------------------------------------------------|
| `name`     | A local identifier for the registration (e.g., `arithmetic`)                       |
| `=`        | Separator                                                                          |
| `Type`     | The Rust type implementing the theory's `BooleanAlgebra` or `ConstraintTheory`     |
| `for [..]` | Optional list of grammar categories this theory handles (omitted = all categories) |

The current well-known theory types and the modules they activate:

| Theory type         | Module activated      | Reference                                 |
|---------------------|-----------------------|-------------------------------------------|
| `PresburgerAlgebra` | M12 Linear Arithmetic | Presburger (1929)                         |
| `UnificationTheory` | M13 Unification       | Martelli & Montanari (1982)               |
| `LatticeTheory`     | M14 Subtype Lattice   | Birkhoff (1940), Davey & Priestley (2002) |

The mapping is performed by string-matching the theory's quoted Rust
type name against this table inside `classify_grammar_with_config()`.
New theory types can be added by extending this table — no other
pipeline changes are required because all 15 modules are already
parameterized over an effective Boolean algebra via `TheoryAlgebra<T>`.

### 6.1 Why String Matching?

The macros crate uses `syn::Type` for theory type ASTs (because it must
parse arbitrary Rust types like `MyCustomTheory<f64>`). The prattail
crate, which runs the pipeline, has **no `syn` dependency** — it sees
only the lowered `String` form. The lowering happens in
`prattail_bridge.rs` via the `quote!(#ty).to_string()` round-trip,
which produces a stable string representation suitable for direct
comparison.

```text
   ┌──────────────┐  parse_guards()  ┌───────────────┐
   │ language! {  │ ───────────────► │  GuardConfig  │
   │   guards{…}  │                  │  (syn types)  │
   └──────────────┘                  └───────┬───────┘
                                             │ language_def_to_spec()
                                             │ (prattail_bridge.rs)
                                             ▼
                                    ┌────────────────────┐
                                    │  GuardConfigSpec   │
                                    │  (String / HashMap)│
                                    └────────┬───────────┘
                                             │
                                             ▼
                                  classify_grammar_with_config()
                                             │
                                             ▼
                                  Module activation bits
                                  (M12, M13, M14, …)
```

---

## 7. The `channels { }` Sub-block

A **channel** is a binding site where a process waits for a value to
arrive — a pi-calculus communication channel, an ambient boundary, a
Linda tuple-space pattern, an actor mailbox, a Petri net place. The
prattail pipeline activates **M8 (Multi-Tape Automata)** when a guard
predicate spans two or more channels (because the values must be
checked together), and **M11 (Two-Way Transducer)** when the
multi-channel guard mixes two or more distinct *categories* of channel
(because backward constraint propagation can prune one category's
value space using constraints from another).

Without explicit declarations, the pipeline heuristically treats every
grammar category that appears as a non-terminal in another category's
rule as a potential channel. This over-approximates: a Lambda calculus
with `Term` and `Type` categories triggers M8/M11 even though it has
no channels at all.

The `channels { }` sub-block lets the grammar author declare exactly
which categories are channels and which constructors are join patterns:

```rust
channels {
    channel Name;                                  // Name is a channel category
    join PGuardedInput(ch: Name);                  // 1-channel join pattern
    join PJoin(ch1: Name, ch2: Name, ch3: Name);   // 3-channel join pattern
}
```

**Items.**

| Item kind | Form                                      |
|-----------|-------------------------------------------|
| `channel` | `channel <Category> ;`                    |
| `join`    | `join <Label>(<param>: <Category>, … ) ;` |

**Activation rules** (deterministic — no heuristics):

```
M8  ⇐  ∃ join pattern J such that |J.channel_params| ≥ 2
M11 ⇐  M8 ∧ |{ p.category : p ∈ join.channel_params, J ∈ joins }| ≥ 2
```

In words: M8 fires when at least one join pattern binds two or more
channels; M11 additionally fires when the joined channels span two or
more distinct categories.

**Example: single-channel join (M8 not needed).**
```rust
channels {
    channel Name;
    join PGuardedInput(ch: Name);   // only 1 channel param
}
```
This activates neither M8 nor M11 — there is no multi-channel pattern.

**Example: same-category multi-channel join (M8 only).**
```rust
channels {
    channel Name;
    join PJoin(ch1: Name, ch2: Name);   // 2 channel params, 1 category
}
```
M8 fires; M11 does not (only one category).

**Example: cross-category multi-channel join (M8 + M11).**
```rust
channels {
    channel Name;
    channel Place;
    join PHybrid(ch: Name, p: Place);
}
```
M8 fires (2 params); M11 fires (2 distinct categories).

### 7.1 Visualization: M8 + M11 Pipeline

```
   Channels:  ch1 ────┐         ┌──── ch2
                      │         │
                      ▼         ▼
              ┌────────────────────────┐
              │  M11 backward W2T      │
              │  pre-image computation │ ── prunes ch1 values that
              └───────────┬────────────┘    cannot satisfy any ch2 value
                          │
                          ▼
              ┌────────────────────────┐
              │  M8 multi-tape product │
              │  pair(SFA₁, SFA₂)      │ ── single fused traversal
              └───────────┬────────────┘    over (pruned ch1) × ch2
                          │
                          ▼
              ┌────────────────────────┐
              │  Codegen               │
              │  (single match table)  │
              └────────────────────────┘
```

For the formal definitions of `pair`, `pre_image`, and the weighted
multi-tape automaton, see [predicated-types.md](predicated-types.md)
§§16–17 and the original sources Kempe (2004) and Feng & Maletti (2022).

---

## 8. `@[ … ]` Selectivity and Cost Annotations

### 8.1 What They Are

The pipeline orders guard evaluation by **selectivity** (the estimated
fraction of inputs satisfying the predicate) and breaks ties by **cost**
(the relative computational expense of evaluating it). When the grammar
author has domain knowledge about a specific predicate's selectivity or
cost, they can override the heuristic with an `@[…]` annotation:

```rust
guards {
    eq    . x, y |- x "==" y    @[selectivity(0.1), cost(2)] ;
    gt    . x, y |- x ">" y     @[selectivity(0.5)] ;
    fresh . x    |- "fresh" "(" x ")" @[cost(1)] ;
}
```

| Annotation       | Domain         | Meaning                                                                    |
|------------------|----------------|----------------------------------------------------------------------------|
| `selectivity(s)` | s ∈ [0.0, 1.0] | Fraction of inputs satisfying the predicate (0=rejects all, 1=accepts all) |
| `cost(c)`        | c ∈ ℕ          | Relative evaluation cost (lower is cheaper)                                |

Both fields are optional and independent: a predicate may specify one,
both, or neither. When omitted, the pipeline falls through to its
heuristic estimate.

### 8.2 Selectivity Algebra for Compound Predicates

Annotations apply to **leaf** predicates only — atomic invocations like
`eq(x, y)` or `fresh(x)`. The selectivity of a compound predicate built
from connectives is derived from leaf selectivities by standard
probability-theoretic identities under an **independence assumption**
(meaning: the satisfaction of `P` is assumed statistically independent
of the satisfaction of `Q`):

| Compound form         | Selectivity formula             | Justification                            |
|-----------------------|---------------------------------|------------------------------------------|
| `¬P`                  | `1 − sel(P)`                    | Complement probability                   |
| `P ∧ Q`               | `sel(P) · sel(Q)`               | Pr(A ∩ B) = Pr(A)·Pr(B) (indep.)         |
| `P ∨ Q`               | `1 − (1 − sel(P))·(1 − sel(Q))` | Inclusion-exclusion: Pr(A∪B)=1−Pr(¬A∩¬B) |
| `P ⟹ Q`               | `1 − sel(P)·(1 − sel(Q))`       | `P ⟹ Q ≡ ¬P ∨ Q`                         |
| `∀x ∈ D. P(x)`        | `sel(P)^|D|`                    | All `|D|` elements must satisfy P        |
| `∃x ∈ D. P(x)`        | `1 − (1 − sel(P))^|D|`          | At least one of `|D|` must satisfy       |
| `∀x (infinite). P(x)` | `sel(P) · 0.05`                 | Heuristic: 5% of body (very restrictive) |
| `∃x (infinite). P(x)` | `1 − (1 − sel(P))^10`           | Heuristic: 10-element proxy domain       |

The independence assumption is approximate. For correlated predicates
(e.g., `gt(x, 5) ∧ gt(x, 10)`), the true selectivity is the more
restrictive of the two. The pipeline accepts this approximation as
the cost of avoiding correlation analysis at compile time.

### 8.3 Override Precedence

When the pipeline estimates selectivity (or cost) for a predicate, it
consults three sources in priority order:

```
┌──────────────────────────────────────────────────┐
│  1. Explicit annotation                          │
│     @[selectivity(s)] or @[cost(c)]              │
│     (highest priority)                           │
└──────────────────────┬───────────────────────────┘
                       │ (no match)
                       ▼
┌──────────────────────────────────────────────────┐
│  2. Type-informed heuristic                      │
│     theories { } registration covers the         │
│     predicate's parameter types                  │
└──────────────────────┬───────────────────────────┘
                       │ (no match)
                       ▼
┌──────────────────────────────────────────────────┐
│  3. Pattern-matched default                      │
│     estimate_predicate_selectivity() / _cost()   │
│     (lowest priority — backward compatible)      │
└──────────────────────────────────────────────────┘
```

The first source that provides a value wins. The third source is the
existing heuristic that all current languages rely on, so adding
annotations is purely additive.

### 8.4 Why Selectivity Ordering Matters

When several guards protect the same channel, evaluating the most
selective one first is a textbook query-optimization technique
(Selinger et al., 1979): a guard that rejects 95% of inputs filters
the input stream to 5%, after which the next (probably more
expensive) guard runs on only 5% of the original load. Without
selectivity ordering, every guard runs on every input.

The pipeline's **BCG01 selectivity ordering** uses these formulas to
sort each receive's guard set, so the most selective predicate is
checked first. The `@[selectivity(...)]` annotation directly feeds
this sort.

---

## 9. Composition: `extends`, `includes`, `mixins`

The `language!` macro supports three forms of language composition:

| Clause     | What it inherits                                                       |
|------------|------------------------------------------------------------------------|
| `extends`  | Everything: types, terms, equations, rewrites, logic, **and `guards`** |
| `includes` | Grammar only: types and terms (guards NOT inherited)                   |
| `mixins`   | Fragment grammar: types and terms (guards NOT inherited)               |

The rationale for `includes` and `mixins` is that they import only
**syntax**, not semantics; guard configuration is semantic, so it
stays with the defining language.

### 9.1 Merge Rules for `extends`

When language B extends language A and both declare a `guards { }`
block, the merge follows these rules:

| Sub-block                 | Merge strategy                       | Conflict handling                                                                  |
|---------------------------|--------------------------------------|------------------------------------------------------------------------------------|
| Predicates (direct items) | Union by name                        | Same name + same arity → merge annotations field-by-field. Different arity → error |
| `connectives { }`         | **Extension replaces base entirely** | No merge — extension defines the full set or inherits                              |
| `theories { }`            | Union by name                        | Same name + same theory type → idempotent. Different type → error                  |
| `channels { }`            | **Extension replaces base entirely** | No merge — channel topology is language-specific                                   |

**Annotation inheritance** for predicates that exist in both:

For each annotation field independently, the extension's value takes
precedence if present; otherwise the base's value is inherited.
Concretely:

| Base annotation       | Extension annotation | Merged result          |
|-----------------------|----------------------|------------------------|
| `[sel(0.1), cost(2)]` | `[sel(0.05)]`        | `[sel(0.05), cost(2)]` |
| `[sel(0.1)]`          | `[]`                 | `[sel(0.1)]`           |
| `[cost(2)]`           | `[cost(5)]`          | `[cost(5)]`            |
| `[]`                  | `[sel(0.7)]`         | `[sel(0.7)]`           |

This per-field override semantics gives the extending language
**focused** control: it can refine just the selectivity for a
predicate it knows more about, without restating the cost.

### 9.2 Why Connectives and Channels Replace Rather Than Merge

If the base language declares `or = "or" | "∨"` and the extension
wants to *restrict* the guard sublanguage to no-disjunction (perhaps
because the extension targets a runtime that can't evaluate
disjunction efficiently), inheriting the base's `or` would defeat the
restriction. Replacement gives the extension full control over which
connectives it exposes.

The same logic applies to `channels { }`: the extension may add or
remove communication primitives, and partial merging would yield a
configuration the author did not intend.

### 9.3 Worked Example

```rust
// Base language with full guard config
language! {
    name: BaseCalc,
    types { Expr, ![i64] as Int },
    guards {
        eq . x, y |- x "==" y @[selectivity(0.1), cost(2)] ;
        gt . x, y |- x ">"  y @[selectivity(0.5), cost(2)] ;
        theories {
            arithmetic = PresburgerAlgebra for [Int];
        }
    },
    terms { … },
}

// Extension that overrides gt's selectivity, adds a new predicate,
// and adds a new theory.
language! {
    name: TypedCalc,
    extends: BaseCalc,
    types { ![f64] as Float },
    guards {
        // Override gt's selectivity. Cost is inherited from BaseCalc.
        gt . x, y |- x ">"  y @[selectivity(0.7)] ;
        // New predicate, not in base.
        is_nan . x |- "is_nan" "(" x ")" @[selectivity(0.01), cost(1)] ;
        theories {
            // New theory; arithmetic is inherited from BaseCalc.
            float_arith = FloatTheory for [Float];
        }
    },
    terms { … },
}
```

After merging, `TypedCalc` has:
- `eq` with `selectivity = 0.1, cost = 2` (inherited unchanged)
- `gt` with `selectivity = 0.7` (overridden), `cost = 2` (inherited)
- `is_nan` with `selectivity = 0.01, cost = 1` (new)
- Theories: `arithmetic` (inherited) + `float_arith` (new)

---

## 10. Closed-World vs Open-World Resolution

The presence or absence of explicit predicate declarations in
`guards { }` controls whether predicate name resolution uses
**closed-world** or **open-world** semantics.

### 10.1 Open World (default)

When `guards { }` is absent, or when present but contains no direct
predicate declarations (only sub-blocks), all standard built-in
predicates are available with their default syntax. Any predicate
name used in a guard expression that matches one of the standard
built-ins resolves successfully without further declaration. This is
the **default** and preserves backward compatibility — every
existing language definition compiles unchanged.

### 10.2 Closed World

When `guards { }` contains at least one direct predicate declaration,
the language enters **closed-world mode**. The predicate resolution
table is the union of:

1. The predicate names declared as direct items in `guards { }`.
2. The relation names declared in `logic { }` via `relation R(T1, T2);`.

A guard expression that references a predicate name not in this union
produces compile error [GUARD01](#14-diagnostics).

### 10.3 Resolution Walk

When validating a language, the compiler walks every behavioral
predicate AST node in every guard premise of every rewrite and
equation. For each `RelationQuery { relation_name, … }` node, it
performs a single lookup in the resolution table. The walk recurses
into compound predicates (And, Or, Implies, Not, Quantified) but
treats `AcMatch` as structural (not a named predicate, no name
resolution required).

```
┌─────────────────────────────────────────────┐
│  validate_guard_config(language)            │
│                                             │
│  1. If guard_config is None → return Ok     │
│  2. CONN01: build ConnectiveMap, error on   │
│     duplicate keyword across roles          │
│  3. GUARD01: if has_explicit_predicates,    │
│     walk all behavioral preds, check names  │
│  4. MT02: validate channel param categories │
│     against declared channel set            │
│  5. TW03: validate join pattern labels      │
│     match a known terms { } constructor     │
│  6. Return Ok or first error                │
└─────────────────────────────────────────────┘
```

---

## 11. Architecture: From Macro to Pipeline

> **See also:** [`dispatch/predicate-dispatch-integration.md`](dispatch/predicate-dispatch-integration.md)
> documents how the explicit `guards { }` configuration integrates
> with the heuristic layers in `predicate_dispatch.rs`. That document
> explains the bypass model that turns heuristics from "additive
> substitutes" into "fallback defaults" under explicit configuration,
> and proves the soundness of the bypass via a monotonicity theorem.

The `guards { }` block traverses three crates and four representations
on its way from source to runtime behavior. The diagram below shows
the data flow with one box per representation:

```
                     ┌─────────────────────────────┐
   Source code:      │   language! { guards{…} }   │
                     └──────────────┬──────────────┘
                                    │ proc-macro
                                    │ expansion
                                    ▼
                     ┌─────────────────────────────┐
   AST (macros):     │   GuardConfig               │
   syn-based         │   - builtin_predicates      │
                     │   - connectives             │
                     │   - theories                │
                     │   - channels                │
                     └──────────────┬──────────────┘
                                    │ language_def_to_spec()
                                    │ (prattail_bridge.rs)
                                    ▼
                     ┌─────────────────────────────┐
   Spec (prattail):  │   GuardConfigSpec           │
   syn-free          │   - theories: Vec<…Spec>    │
                     │   - channel_categories      │
                     │   - join_patterns           │
                     │   - selectivity_overrides   │
                     │   - cost_overrides          │
                     │   - has_explicit_*          │
                     └──────────────┬──────────────┘
                                    │ classify_grammar_with_config()
                                    │ (predicate_dispatch.rs)
                                    ▼
                     ┌─────────────────────────────┐
   Pipeline state:   │   GrammarDispatchPlan       │
                     │   - aggregate_signature     │
                     │     (M1…M15 bits)           │
                     │   - module_schedule         │
                     └──────────────┬──────────────┘
                                    │ codegen
                                    ▼
                     ┌─────────────────────────────┐
   Generated code:   │   Rust source (TokenStream) │
                     │   - parser                  │
                     │   - guard evaluation fns    │
                     │   - Ascent rules            │
                     └─────────────────────────────┘
```

### 11.1 Where Each Concern Lives

| Concern                             | Where                                                                                                                                                        |
|-------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Parsing the `guards {}` block       | `macros/src/ast/language.rs::parse_guards`                                                                                                                   |
| AST types                           | `macros/src/ast/language.rs` (`GuardConfig`, `BuiltinPredicate`, …)                                                                                          |
| Lowering syn → String               | `macros/src/gen/syntax/parser/prattail_bridge.rs::lower_guard_config`                                                                                        |
| Spec types                          | `prattail/src/lib.rs` (`GuardConfigSpec`, `TheoryRegistrationSpec`, `JoinPatternSpec`)                                                                       |
| Merge / composition                 | `macros/src/ast/merge.rs::merge_guard_config`                                                                                                                |
| Validation                          | `macros/src/ast/validation/validator.rs::validate_guard_config`                                                                                              |
| Theory-driven module activation     | `prattail/src/predicate_dispatch.rs::classify_grammar_with_config`                                                                                           |
| Selectivity / cost override         | `prattail/src/predicate_dispatch.rs::resolve_selectivity`, `resolve_cost`                                                                                    |
| Codegen-side selectivity            | `macros/src/gen/runtime/guard_codegen.rs::estimate_selectivity_with_config`                                                                                  |
| Codegen-side cost                   | `macros/src/gen/runtime/guard_codegen.rs::estimate_guard_cost_with_config`                                                                                   |
| Connective parser integration       | `macros/src/ast/language.rs` (thread-local + `ConnectiveMapGuard`)                                                                                           |
| Runtime metadata (simulator bridge) | `runtime/src/metadata.rs` (`BuiltinPredicateDef`, `TheoryDef`, `ChannelDef`, `JoinPatternDef`, `ConnectiveDef`; default-empty methods on `LanguageMetadata`) |
| Macro emission of runtime metadata  | `macros/src/gen/runtime/metadata.rs` (5 new generators + `behavioral_pred_to_display`)                                                                       |
| Simulator ingestion                 | `simulation/src/model.rs::LanguageStateMachine::from_metadata`                                                                                               |
| Simulator guard-aware invariants    | `simulation/src/invariant.rs::GuardSatisfaction`                                                                                                             |
| Channel-aware Petri nets            | `simulation/src/stochastic_petri.rs::StochasticPetriNet::from_channel_metadata`                                                                              |

### 11.2 Simulation Bridge

The `guards { }` block metadata does not stop at the macro — it flows
through the runtime crate's `LanguageMetadata` trait into the
`simulation` crate's `LanguageStateMachine`. This lets the
stochastic simulator, the model-based test runner, and the Petri-net
analysis tooling introspect declared theories, channel categories,
join patterns, built-in predicates, and connectives without
round-tripping through the macro AST.

The bridge has three layers:

1. **`LanguageMetadata` trait** (runtime/src/metadata.rs). Five new
   methods (`builtin_predicates`, `theories`, `channels`,
   `join_patterns`, `connectives`) return `&'static [… Def]` slices,
   with default-empty implementations so every existing language impl
   compiles unchanged. A new `is_guarded: bool` field on `RewriteDef`
   and `EquationDef` identifies premises that contained a
   `BehavioralGuard` in the source.

2. **Macro codegen** (macros/src/gen/runtime/metadata.rs). Five
   generator functions read `language.guard_config` and emit static
   slice literals for each of the five metadata methods. The
   `behavioral_pred_to_display` helper renders `BehavioralPred` AST
   nodes in a user-friendly unicode form (`a ∧ b`, `∀x. φ`, …) which
   replaces the previous `{:?}` debug output for `BehavioralGuard`
   premises.

3. **Simulation ingestion** (simulation/src/model.rs).
   `LanguageStateMachine::from_metadata` reads the five new methods and
   populates the corresponding `ModelBuiltinPredicate`, `ModelTheory`,
   `ModelChannel`, `ModelJoinPattern`, and `ModelConnective` vectors.
   The simulator's `GuardSatisfaction` invariant (Sim-D) uses the
   `is_guarded` flag to track which rewrite rules have guarded
   premises; its `StochasticPetriNet::from_channel_metadata` helper
   builds Gillespie-ready Petri nets with one place per declared
   channel and one transition per join pattern.

For the full story of how theory and channel declarations interact
with the heuristic dispatch layer, see
[dispatch/predicate-dispatch-integration.md](dispatch/predicate-dispatch-integration.md).

---

## 12. Pseudocode: Key Algorithms

This section presents the most important algorithms in literate
programming style — pseudocode is preferred over Rust source so the
algorithm's structure is visible without distraction.

### 12.1 `parse_guards`

The top-level parser dispatches each item by peeking the next
identifier and routing to the appropriate sub-parser.

```
function parse_guards(input):                 ▷ ParseStream → GuardConfig
    expect identifier "guards"
    open braced content

    declare builtin_predicates : list of BuiltinPredicate, initially empty
    declare connectives        : optional list of ConnectiveDecl, initially absent
    declare theories           : list of TheoryRegistration, initially empty
    declare channels           : optional ChannelConfig, initially absent
    declare saw_explicit_pred  : boolean, initially false

    while content is not empty:
        let kw ← peek next identifier
        case kw of:
            "connectives" → connectives ← parse_connectives_block(content)
            "theories"    → theories    ← parse_theories_block(content)
            "channels"    → channels    ← parse_channels_block(content)
            otherwise     →
                builtin_predicates.append(parse_builtin_predicate(content))
                saw_explicit_pred ← true

    return GuardConfig {
        builtin_predicates: if saw_explicit_pred then Some(builtin_predicates) else None,
        connectives,
        theories,
        channels,
    }
```

The choice between `Some(empty list)` and `None` for `builtin_predicates`
is deliberate: an explicitly empty list (`Some(empty)`) signals
closed-world mode with no available predicates, while absent (`None`)
signals open-world mode with all standard built-ins available. The
`saw_explicit_pred` flag distinguishes the two.

### 12.2 `ConnectiveMap::from_decls`

Building the bidirectional map enforces the CONN01 invariant:

```
function ConnectiveMap.from_decls(decls):     ▷ list of ConnectiveDecl → ConnectiveMap
    declare role_to_keywords : Map<Role, list<String>>, empty
    declare keyword_to_role  : Map<String, Role>, empty

    for each decl in decls:
        for each kw in decl.keywords:
            if kw is in keyword_to_role:
                let existing ← keyword_to_role[kw]
                if existing ≠ decl.role:
                    error CONN01: keyword `kw` mapped to two roles
                                 (`existing` and `decl.role`)
            keyword_to_role[kw]               ← decl.role
            role_to_keywords[decl.role].append(kw)

    return ConnectiveMap {
        role_to_keywords,
        keyword_to_role,
    }
```

After construction, the bidirectional invariant holds:

```
∀ (role, kws) ∈ role_to_keywords. ∀ kw ∈ kws.
    keyword_to_role[kw] = role
```

### 12.3 `merge_guard_config`

The merge function implements the §9 composition rules:

```
function merge_guard_config(base, extension, errors):
                                              ▷ Option<GC> × Option<GC> → Option<GC>
    case (base, extension) of:
        (None, None)            → return None
        (Some(b), None)         → return Some(clone of b)
        (None, Some(e))         → return Some(clone of e)
        (Some(b), Some(e))      → ▷ both present — apply per-sub-block merge

    let merged_predicates ← merge_builtin_predicates(b.preds, e.preds, errors)

    let merged_connectives ←
        if e.connectives is Some then
            e.connectives                     ▷ extension fully replaces
        else
            b.connectives                     ▷ inherit from base

    let merged_theories ← merge_theory_registrations(b.theories, e.theories, errors)

    let merged_channels ←
        if e.channels is Some then
            e.channels                        ▷ extension fully replaces
        else
            b.channels                        ▷ inherit from base

    return Some(GuardConfig {
        builtin_predicates: merged_predicates,
        connectives:        merged_connectives,
        theories:           merged_theories,
        channels:           merged_channels,
    })
```

```
function merge_builtin_predicates(base, extension, errors):
    if base is None and extension is None    → return None
    if base is None                          → return extension
    if extension is None                     → return base

    let merged   : list, empty
    let consumed : set of predicate names, empty

    ▷ Index extension predicates by name for lookup
    let ext_by_name ← map from name to predicate, built from extension

    for each base_pred in base:
        let name ← base_pred.name
        if name is in ext_by_name:
            let ext_pred ← ext_by_name[name]
            if base_pred.arity ≠ ext_pred.arity:
                errors.append(DuplicatePredicateName{name, base.arity, ext.arity})
                continue
            ▷ Field-level annotation merge: extension wins per field
            let merged_anno ← PredicateAnnotations {
                selectivity: ext_pred.anno.selectivity OR base_pred.anno.selectivity,
                cost:        ext_pred.anno.cost        OR base_pred.anno.cost,
            }
            merged.append(BuiltinPredicate from ext_pred but with merged_anno)
            consumed.insert(name)
        else:
            merged.append(base_pred)

    for each ext_pred in extension:
        if ext_pred.name not in consumed:
            merged.append(ext_pred)

    return merged
```

The OR operator on the annotations is `Option::or`: returns the first
operand if it is `Some`, otherwise the second. This implements the
"extension wins per-field, base inherited otherwise" rule.

### 12.4 `classify_grammar_with_config`

The pipeline-side dispatcher activates modules based on heuristics
**and** explicit guard config overrides. The pseudocode below shows
only the data-driven additions; the heuristic logic is unchanged from
the existing `classify_grammar`.

```
function classify_grammar_with_config(syntax, categories, guard_config):
    let aggregate ← empty PredicateSignature

    ▷ ① Run all the existing structural heuristics
    aggregate ← aggregate ∪ structural_heuristics(syntax)

    ▷ ② Apply theory-driven module activation
    if guard_config is Some:
        for each theory in guard_config.theories:
            case theory.theory_type of:
                "PresburgerAlgebra" | "Presburger" | "PresburgerTheory" →
                    aggregate.set(M12_LINEAR_ARITHMETIC)
                "UnificationTheory" | "Unification" →
                    aggregate.set(M13_UNIFICATION)
                "LatticeTheory" | "Lattice" →
                    aggregate.set(M14_SUBTYPE_LATTICE)
                otherwise → ▷ unknown theory, fall through

    ▷ ③ Apply channel-driven M8 / M11 activation (overriding heuristic)
    if guard_config is Some and guard_config.channel_categories is Some:
        let m8_active     ← false
        let distinct_cats ← empty set

        for each join in guard_config.join_patterns:
            if |join.channel_categories| ≥ 2:
                m8_active ← true
            distinct_cats ← distinct_cats ∪ join.channel_categories

        if m8_active:
            aggregate.set(M8_MULTI_TAPE)
        if m8_active and |distinct_cats| ≥ 2:
            aggregate.set(M11_TWO_WAY)

    return GrammarDispatchPlan {
        aggregate_signature: aggregate,
        module_schedule:     ordered_by_cost(aggregate),
        modules_skipped:     15 − count_set_bits(aggregate),
    }
```

### 12.5 `resolve_selectivity`

The override-precedence chain for leaf selectivity, with compound
predicates recursing through the resolver so per-leaf overrides flow
through `And`, `Or`, `Not`:

```
function resolve_selectivity(expr, guard_config):
    case expr of:
        Relation { name, args }:
            ▷ Priority 1: explicit annotation override
            if guard_config is Some and name ∈ guard_config.selectivity_overrides:
                return guard_config.selectivity_overrides[name]
            ▷ Priority 3: heuristic default (Priority 2 — type-informed —
            ▷ folded into the heuristic for the current implementation)
            return estimate_predicate_selectivity(expr)

        Not(inner):
            return 1 − resolve_selectivity(inner, guard_config)

        And(a, b):
            ▷ Independence assumption: Pr(A∩B) = Pr(A) · Pr(B)
            return resolve_selectivity(a, guard_config)
                 · resolve_selectivity(b, guard_config)

        Or(a, b):
            ▷ Inclusion-exclusion: Pr(A∪B) = 1 − Pr(¬A∩¬B)
            let sa ← resolve_selectivity(a, guard_config)
            let sb ← resolve_selectivity(b, guard_config)
            return 1 − (1 − sa) · (1 − sb)

        otherwise:
            ▷ Quantifiers and other compound forms use the heuristic estimator
            return estimate_predicate_selectivity(expr)
```

The final fall-through to `estimate_predicate_selectivity` ensures
quantifiers and other compound forms still get a sensible default;
they just don't currently consult per-predicate overrides at compound
boundaries (the current implementation overrides only at relation
leaves).

### 12.6 `walk_behavioral_pred` (GUARD01 closed-world check)

```
function walk_behavioral_pred(pred, table):
    case pred of:
        RelationQuery { relation_name, args }:
            if relation_name not in table:
                error GUARD01: unknown predicate `relation_name`
                              (available: sorted contents of table)
            return Ok

        And(a, b) | Or(a, b) | Implies(a, b):
            walk_behavioral_pred(a, table)
            walk_behavioral_pred(b, table)
            return Ok

        Not(inner):
            walk_behavioral_pred(inner, table)
            return Ok

        Quantified { body, … }:
            walk_behavioral_pred(body, table)
            return Ok

        AcMatch { … }:
            ▷ AC-match is structural, not a named predicate; skip
            return Ok
```

The walk is purely structural — every named predicate is checked
against the same table. The compiler's `validate_guard_config`
function calls this for every `BehavioralGuard` premise across all
equations and rewrites in closed-world mode.

---

## 13. Worked Examples Across Paradigms

### 13.1 Rholang (π-calculus)

```rust
language! {
    name: Rholang,
    types { Proc, Name, ![i64] as Int },

    tokens {
        Where = "where" push(guard_mode);
        mode guard_mode {
            Not    = "not"    | "¬";
            And    = "and"    | "∧";
            Or     = "or"     | "∨";
            ForAll = "forall" | "∀";
            Exists = "exists" | "∃";
        }
    },

    guards {
        eq    . x, y |- x "==" y | "eq" "(" x "," y ")" ;
        neq   . x, y |- x "!=" y | "neq" "(" x "," y ")" ;
        gt    . x, y |- x ">"  y | "gt" "(" x "," y ")" ;
        fresh . x    |- "fresh" "(" x ")" ;

        connectives {
            and    = "and"    | "∧";
            or     = "or"     | "∨";
            not    = "not"    | "¬";
            forall = "forall" | "∀";
            exists = "exists" | "∃";
        }

        theories {
            arithmetic = PresburgerAlgebra for [Int];
            patterns   = UnificationTheory for [Proc, Name];
            types      = LatticeTheory     for [Proc, Name, Int];
        }

        channels {
            channel Name;
            join PGuardedInput(ch: Name);
            join PJoin(ch1: Name, ch2: Name);
        }
    },

    terms {
        PGuardedInput . ch:Name, ^[xs].pat:[Name* -> Name],
                        ?guard:Guard, ^[ys].cont:[Name* -> Proc]
            |- "for" "(" "@" "{" pat "}" "<-" ch ")"
               "where" guard "{" cont "}" : Proc ;
        // …
    },
    logic {
        relation path(Proc, Proc);
        relation safe(Proc);
        path(X, Z) :- path(X, Y), path(Y, Z);
    },
    rewrites { … },
}
```

This activates: M8 (PJoin has 2 channel params), no M11 (only one
category, `Name`), M12 (Presburger for Int), M13 (Unification for
Proc/Name), M14 (Lattice for Proc/Name/Int).

### 13.2 MeTTa (minimal guards, operator-style keywords)

```rust
language! {
    name: MeTTa,
    types { Atom, Expression },

    guards {
        eq  . x, y |- x "==" y ;
        neq . x, y |- x "!=" y ;

        // MeTTa uses && for conjunction and ~ for negation.
        // No quantifiers, no disjunction, no implications.
        connectives {
            and = "&&";
            not = "~";
        }

        theories {
            patterns = UnificationTheory for [Atom];
            types    = LatticeTheory     for [Atom, Expression];
        }
        // No `channels {}` — MeTTa is sequential.
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

This activates M13 (Unification for Atom) and M14 (Lattice for
Atom/Expression). M8/M11 are not activated (no channels).

### 13.3 Guarded Lambda Calculus (restricted connectives)

```rust
language! {
    name: GuardedLambda,
    types { Term },

    guards {
        eq . x, y |- x "==" y ;

        // Only negation (via "not") and equality predicate.
        // Comma-separated predicates (implicit conjunction) are
        // ALWAYS available regardless of connectives {} — comma is
        // structural syntax, not a connective keyword.
        connectives {
            not = "not";
        }
        // No theories — purely behavioral (Ascent lookup).
        // No channels — sequential.
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

This activates only the baseline modules (M1, M10). The disjunction
and quantifier connectives are explicitly NOT declared, so any
attempt to use them in a guard expression is a CONN02 error.

### 13.4 Clojure-like (n-ary predicates, type overloads)

```rust
language! {
    name: ClojureLike,
    types { Expr, ![i64] as Int, ![String] as Str },

    guards {
        // 1-or-more: (= a b c) → eq(a,b) ∧ eq(b,c)
        eq . xs+ |- "=" "(" xs ")" ;

        // 2-to-5 args with range quantifier:
        between . x, bounds{2,5}
            |- "between?" "(" x "," bounds ")" ;

        // Union-typed variadic: each arg can be Int or Str
        comparable . xs:(Int|Str)+
            |- "comparable?" "(" xs ")" ;

        // Type-specific overloads: integer vs string comparison
        gt . x: Int, y: Int |- ">" "(" x "," y ")" ;
        gt . x: Str, y: Str |- ">" "(" x "," y ")" ;

        // Prefix-only:
        nil_q . x |- "nil?" "(" x ")" ;

        connectives {
            and = "and";
            or  = "or";
            not = "not";
        }
    },

    terms { … },
    logic { … },
}
```

This shows variadic, range-quantified, union-typed, and type-overloaded
predicates. The compiler dispatches `gt(x, y)` to either the `Int`
overload or the `Str` overload depending on the inferred parameter
types in the guard's binding context.

---

## 14. Diagnostics

The following lints fire during validation of the `guards { }` block:

| Code      | Severity | Condition                                                                             |
|-----------|----------|---------------------------------------------------------------------------------------|
| `CONN01`  | Error    | A keyword is mapped to two different connective roles in `connectives { }`            |
| `CONN02`  | Error    | A guard expression uses a connective keyword not declared in `connectives { }`        |
| `GUARD01` | Error    | A guard references a predicate name not in `guards { }` or `logic { }` (closed-world) |
| `MT01`    | Warning  | A channel category is declared but never referenced in any join pattern               |
| `MT02`    | Error    | A join pattern references a channel category that was not declared                    |
| `TW02`    | Warning  | A join pattern has only one channel parameter (M8 fusion does not apply)              |
| `TW03`    | Error    | A join pattern's label has no matching constructor in `terms { }`                     |

**Example diagnostic output for CONN01:**

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

**Example diagnostic output for GUARD01:**

```text
error[GUARD01]: unknown predicate `path` in guard expression
  --> src/main.rs:42:15
   |
42 |     guard(path(x, y))
   |           ^^^^ not found in `guards {}` or `logic {}` declarations
   |
   = help: declare `path` in `guards { path . x, y |- ... ; }` or
           `logic { relation path(Type1, Type2); }`
   = note: available predicates: eq, gt, fresh, safe
```

---

## 15. References

The references below are the primary sources for the theory underlying
this design. Each entry includes a DOI link where available.

1. **Berry, G. & Boudol, G.** "The Chemical Abstract Machine."
   *Theoretical Computer Science*, 96(1):217–248, 1992.
   DOI: [10.1016/0304-3975(92)90185-I](https://doi.org/10.1016/0304-3975(92)90185-I)
   *Used for:* the CHAM model that underlies the rho-calculus Comm
   rule and its guarded extension.

2. **Birkhoff, G.** *Lattice Theory.* AMS Colloquium Publications,
   vol. 25, 1940.
   *Used for:* the algebraic foundations of M14 Subtype Lattice.

3. **Davey, B. A. & Priestley, H. A.** *Introduction to Lattices and
   Order.* 2nd ed. Cambridge University Press, 2002.
   DOI: [10.1017/CBO9780511809088](https://doi.org/10.1017/CBO9780511809088)
   *Used for:* modern textbook treatment of lattice operations
   (`join`, `meet`, `top`, `bottom`) used by `LatticeTheory`.

4. **Ceri, S., Gottlob, G., & Tanca, L.** *Logic Programming and
   Databases.* Springer, 1990.
   DOI: [10.1007/978-3-642-83952-8](https://doi.org/10.1007/978-3-642-83952-8)
   *Used for:* the Datalog evaluation model underlying the `logic { }`
   block, which guards reference for behavioral predicates.

5. **D'Antoni, L. & Veanes, M.** "Minimization of Symbolic Automata."
   *Proceedings of POPL*, pp. 541–553. ACM, 2014.
   DOI: [10.1145/2535838.2535849](https://doi.org/10.1145/2535838.2535849)
   *Used for:* the SFA / Boolean-algebra framework over which
   `theories { }` registrations operate.

6. **Droste, M. & Gastin, P.** "Weighted Automata and Weighted Logics."
   *Theoretical Computer Science*, 380:69–86, 2007.
   DOI: [10.1016/j.tcs.2007.02.055](https://doi.org/10.1016/j.tcs.2007.02.055)
   *Used for:* the weighted MSO logic (M10) into which guard
   formulas are compiled.

7. **Feng, B. & Maletti, A.** "Weighted Two-Way Transducers."
   *Proceedings of CAI*. LNCS, Springer, 2022.
   DOI: [10.1007/978-3-031-19685-0_8](https://doi.org/10.1007/978-3-031-19685-0_8)
   *Used for:* the M11 Two-Way Transducer that performs backward
   constraint propagation across channels declared in `channels { }`.

8. **Kempe, A.** "Weighted Multi-Tape Automata and Transducers for
   Natural Language Processing." 2004.
   arXiv: [cs/0406003](https://arxiv.org/abs/cs/0406003)
   *Used for:* the M8 Multi-Tape Automata pair construction that
   fuses N per-channel guards declared in `channels { }`.

9. **Kiselyov, O., Shan, C., Friedman, D. P. & Sabry, A.**
   "Backtracking, Interleaving, and Terminating Monad Transformers."
   *Proceedings of ICFP*, pp. 192–203. ACM, 2005.
   DOI: [10.1145/1086365.1086390](https://doi.org/10.1145/1086365.1086390)
   *Used for:* the LogicT fair-backtracking monad that evaluates
   quantified guards at runtime, prior to AWA compilation.

10. **Martelli, A. & Montanari, U.** "An Efficient Unification
    Algorithm." *ACM Transactions on Programming Languages and
    Systems*, 4(2):258–282, 1982.
    DOI: [10.1145/357162.357169](https://doi.org/10.1145/357162.357169)
    *Used for:* the unification algorithm in `UnificationTheory`
    (M13) which the `theories { patterns = UnificationTheory for […] }`
    registration activates.

11. **Meredith, L. G. & Radestock, M.** "A Reflective Higher-Order
    Calculus." *Electronic Notes in Theoretical Computer Science*,
    141(5), 2005.
    DOI: [10.1016/j.entcs.2005.05.016](https://doi.org/10.1016/j.entcs.2005.05.016)
    *Used for:* the reflective rho-calculus whose Comm rule is
    extended by predicated types and the `guards { }` block.

12. **Presburger, M.** "Über die Vollständigkeit eines gewissen
    Systems der Arithmetik ganzer Zahlen, in welchem die Addition
    als einzige Operation hervortritt." Comptes Rendus du I congrès
    de Mathématiciens des Pays Slaves, Warsaw, 1929, pp. 92–101.
    *Used for:* the decidability of linear integer arithmetic that
    `PresburgerAlgebra` (M12) implements.

13. **Selinger, P. G., Astrahan, M. M., Chamberlin, D. D., Lorie, R. A.,
    & Price, T. G.** "Access Path Selection in a Relational Database
    Management System." *Proceedings of SIGMOD*, pp. 23–34. ACM, 1979.
    DOI: [10.1145/582095.582099](https://doi.org/10.1145/582095.582099)
    *Used for:* the selectivity-based query optimization theory that
    motivates `@[selectivity(s)]` annotations and the BCG01 guard
    ordering pass.

---

*This document specifies the user- and implementor-facing aspects of
the `guards { }` block. The pipeline-internal mathematics — automaton
constructions, decidability tiering, the formal semantics of the
guarded Comm rule — live in [predicated-types.md](predicated-types.md),
which this document complements but does not duplicate.*
