# Unification Premises for Pattern-Based COMM

## Context: problem this work solves

The team is formalizing **Rholang semantics** inside a logical framework (rhocalc / graph-structured lambda theory). The immediate goal is to define **unification premises** needed for **pattern-based COMM** (the communication reduction).

In Rholang, communication has the familiar shape:

```text
for(pattern <- channel) { P }  |  channel!(value)
```

A COMM reduction is justified **only when**:

- the sent value **matches** the receive pattern,
- bindings are produced,
- substitutions are applied **safely** (capture-avoiding).

So COMM requires a **formal pattern matching + unification** story, not ad hoc matching in the interpreter only. This document specifies the **logical foundations** and the **staged implementation** that fits the existing Ascent + macro pipeline.

## Goal (engineered rule shape)

Enable relation-based pattern matching in rewrite premises so COMM-style rules can be guarded by unification:

```text
Comm . | pattern unifies received
     |- (PPar {(PFor n pattern body), (POutput n received), ...rest})
     ~> (PPar {(apply_pattern pattern received body), ...rest})
```

The intent is to keep “does this match?” inside Ascent/Datalog fixpoint computation, while keeping binding extraction and substitution in deterministic Rust runtime code (see [Logical vs staged realization](#logical-vs-staged-realization)).

## Surfaces: language authors vs REPL users

Pattern matching touches **two** syntactic worlds:

- **Language authors** edit **`language! { … }`** in crates such as [`languages/src/rhocalc.rs`](../../../languages/src/rhocalc.rs): **`terms`**, **`rewrites`** (including **`unifies(pat, recv)`** premises and **`(apply_pattern …)`** on the RHS), **`equations`**, etc. This is **compile-time** macro input; it defines the theory and generated Ascent.

- **End users** (REPL, tests, embeddings) write **object-language** **source** that parses as **`Proc`** (and friends)—for example the strings in [`repl/src/examples/rhocalc.rs`](../../../repl/src/examples/rhocalc.rs). They **do not** type judgement rules or **`unifies(…)`** at the prompt. They only write processes; COMM with unification is triggered **implicitly** when the engine applies the **`Comm`** rewrite produced from `rewrites { … }`.

**Implication:** unification **premises** are **author-facing**; **pattern syntax** (new **`Proc`** constructors and evolved receive forms) is **user-facing**. You cannot get meaningful pattern COMM in the REPL without extending **`terms { … }`** (and usually **`PInputs`**) so patterns and payloads are **shared `Proc`** ASTs that **`unifies_proc`** can relate. See [Concrete syntax proposal](#concrete-syntax-proposal-for-this-document) below.

## Concrete syntax proposal

The following is a **single coherent package** the doc uses for examples. It is a **proposal** until implemented; adjust token choices (`$`, `pair`, …) if they clash with PraTT / lexer rules.

### Meta-level (inside `rewrites { … }`)

| Construct | Proposed form | Role |
| --------- | ------------- | ---- |
| Unification premise | **`unifies(pat, recv)`** | Conjunct in `prop_context`; lowers to **`unifies_<cat>(pat, recv)`** in Ascent. |
| COMM RHS | **`(apply_pattern pat recv body)`** | Parsed like **`eval`** / **`subst`** family; deterministic binding + subst in Rust. |
| Multi-channel (later) | **`unifies(pat1, recv1), unifies(pat2, recv2), …`** | Same comma-separated conjunction as other premises. |

Reserved: the identifier **`unifies`** in premise position is a **keyword** for **`Premise::Unification`**, not a user-defined `logic { relation unifies … }` (avoid name clashes; validate or document).

### Object-level (inside `terms { … }` — required for matching)

Patterns are **`Proc`** values built from **constructors**. At minimum:

| Construct | Proposed `language!` idea | Surface (user / REPL) | Notes |
| --------- | ------------------------- | ---------------------- | ----- |
| Pattern variable | **`PPatVar . x:Name`** | **`$`** **x** | **`$x`** is a **`Proc`** that behaves as a **pattern metavar** in the **first** argument of **`unifies_proc`** (directional matching only). **No** new category: stays **`Proc`**. |
| Structured match (illustrative) | **`PPair . u:Proc, v:Proc`** | **`pair(`** **u** **`,`** **v** **`)`** | Example binary constructor so examples can use **`pair($u, $v)`** vs **`pair(1, 2)`**; rhocalc may instead reuse **`List`** or add a different product—**the point** is a **ground** shape to recurse under **`unifies_proc`**. |

**Receive form (evolution of `PInputs`).** Today each arm is **`n "?" x`** with **`x`** a **`Name`** binder ([`PInputs` in rhocalc](../../../languages/src/rhocalc.rs)). **Target:** second position is a **`Proc` pattern** **p** (often **`$u`**, **`pair($u,$v)`**, …), with **`^[xs].body`** still abstracting the continuation; **`apply_pattern`** (or a small prelude of **`eval`** steps) connects pattern variables in **p** to occurrences in **body**. Exact **`language!`** typing of **`ps:Vec(Proc)`** vs **`Name* -> Proc`** for **`cont`** is an implementation detail—this doc assumes **aligned vectors** **`ns`**, **`pats`**, **`qs`** in the **`Comm`** LHS, same spirit as current **`ns`**, **`qs`**.

### PraTT / REPL sugar

REPL examples in this repo historically use **`for(a -> x){ … }`** style strings (see [repl examples](../../../repl/src/examples/rhocalc.rs)). **Proposal:** keep that sugar; extend the grammar so **the binding after `->`** can be a **`Proc` pattern** (e.g. **`for(c -> $x){ … }`**, **`for(c -> pair($u, $v)){ … }`**), lowering to the same **`PInputs`**-like constructor as concrete **`( c ? … ).{ … }`** form.

---

### Example — `language!` fragments (author)

**New process constructors (illustrative):**

```text
PPatVar . x:Name |- "$" x : Proc;

PPair . u:Proc, v:Proc |- "pair" "(" u "," v ")" : Proc;
```

**Receive constructor (target shape — replaces single `Name` per arm with `Proc` pattern):**

```text
PInputs . ns:Vec(Name), pats:Vec(Proc), ^[xs].p:[Name* -> Proc]
    |- "(" *zip(ns, pats).*map(|n, pat| n "?" pat).*sep(",") ")" "." "{" p "}" : Proc ;
```

**COMM rewrite (single-channel sketch; real rhocalc keeps multiset `...rest`):**

```text
CommPat . | unifies(pat, q)
    |- (PPar {(PInputs ns pats cont), *zip(ns, qs).*map(|n, q| (POutput n q)), ...rest})
    ~> (PPar {(apply_pattern_chain cont pats qs), ...rest});
```

Here **`apply_pattern_chain`** stands for the generated RHS that walks **aligned `pats`** and **`qs`** (and substitutes into **`cont`**)—either one **n-ary** helper or nested **`apply_pattern`** / **`eval`**; naming is illustrative.

---

### Example — REPL / user programs

Assuming **`$x`** and **`pair`** exist as above, and integer literals are processes (existing casts):

**1) Pattern variable vs literal payload**

```text
{ c!(7) | for(c -> $x){ int($x, 64) } }
```

**Intent:** send **`7`** as **`Proc`**; receive matches **`$x`**; continuation runs **`int($x, 64)`** with **`$x`** replaced by the matched value (requires **`int`**’s first argument to accept that **`Proc`** shape—consistent with rhocalc’s numeric **`Proc`** helpers).

**2) Structured pattern**

```text
{ c!(pair(1, 2)) | for(c -> pair($u, $v)){ int($u, 64) } }
```

**Intent:** COMM only if payload is **`pair`** of two values; bind **`u`**, **`v`**; run body with those bindings.

**3) No match (stuck w.r.t. this COMM)**

```text
{ c!("hi") | for(c -> $x){ int($x, 64) } }
```

**Intent:** if **`$x`** cannot unify with string payload under **`unifies_proc`**, this **`CommPat`** instance does not fire.

Users still **select Rho calculus** in the REPL and paste one **`{ … }`** process; stepping behavior changes only through the **new** **`Comm`** rule and **pattern** grammar.

## Key design decision: explicit variables instead of implicit binding

### Two representations

**(A) Closed lambda-theory encoding (implicit binding).** Variables are handled via meta-theoretical binding (e.g. “`lambda x . body`” style). This is simple for bare abstractions but **does not scale** to rich patterns: multiple simultaneous bindings, structured decomposition, and capture avoidance become awkward.

**(B) Explicit variable representation (chosen).** Variables are **syntax**:

- dedicated productions such as `Var(x)` (name indexed suitably for the object language),
- abstractions such as `Abs(x, body)` (or equivalent) alongside constructors.

Pattern matching then manipulates the same term algebra as the rest of the theory: **programmable substitution**, extensible pattern constructors, unification rules, and pattern environments are all tractable.

Pattern receives bind **during matching**, not only during parsing; explicit `Var` nodes make that semantics first-class.

### Capture-avoiding substitution as a semantic primitive

Pattern matching produces bindings `{ x ↦ v, … }`. COMM must then apply `P[σ]` to the continuation. So substitution is not an informal helper—it is a **core semantic primitive**.

**Logical picture (relational):** a 4-place relation (schematically):

```text
subst(term, variable, replacement, result)
```

| Argument     | Role |
| ------------ | ---- |
| `term`       | expression before replacement |
| `variable`   | variable being replaced |
| `replacement`| inserted value |
| `result`     | capture-avoiding result |

Conceptually `subst(T, v, R) = T′`, but **encoded in the logic** so reductions and future behavioral predicates can reason about it uniformly.

**Implementation note:** rhocalc already relies on Rust-side substitution utilities; the relational formulation is the **spec** those utilities should satisfy. Codegen may continue to call consolidated `subst`/`apply` helpers while the theory documents the intended relation.

## Formal COMM sketch (premises + conclusion)

Although concrete syntax is fixed by the embedding, the judgement shape is:

```text
Send(channel, value)
  |
Receive(channel, pattern, continuation)
  ────────────────────────────────────────────
  if unify(pattern, value, σ)

  →  continuation with σ applied  (capture-avoiding)
```

Implementation requires three cooperating parts:

1. **Pattern representation** in the object language (including wildcards/vars/structure as the grammar allows).
2. **Unification** as logical premises (eligibility for COMM).
3. **Substitution** application on the continuation once unification succeeds.

## Unification premises — conceptual breakdown

### Structural matching

Patterns must decompose values structurally (wildcards, variables, tuples/constructors, literals as the language defines).

| Pattern | Value | Outcome |
| ------- | ----- | ------- |
| wildcard | anything | success |
| variable `x` | `v` | bind `x ↦ v` |
| structured | same shape | recurse |

At the specification level this is **`unify(Pattern, Value, Env)`** with `Env` accumulated left-to-right (or by a fixed recursion strategy).

### Environment accumulation

Bindings form a finite map (or list-encoded map) `Env = { x ↦ v, y ↦ w, … }`. Unification **builds** this structure during recursion.

### Consistency constraint

Repeated pattern variables impose equality on matched pieces:

- `(x, x)` vs `(1, 1)` — OK if both bindings agree.
- `(x, x)` vs `(1, 2)` — fail.

The implementation must reject inconsistent merges deterministically.

### Integration with substitution

After `σ` is determined, the COMM conclusion uses **capture-avoiding** multi-substitution into the continuation, grounded in `subst`/multi-`subst` as already used in the runtime.

## Logical architecture

Rough pipeline from syntax to reduction:

```text
Syntax layer
   → Explicit variables (Var / Abs / …)
   → Unification premises (eligibility)
   → Binding environment σ
   → Capture-avoiding substitution
   → COMM reduction (plus congruence/engine as today)
```

## Relationship to behavioral types

Later work on **behavioral types** will treat many properties as **predicates over runtime behavior** of terms. Pattern unification is foundational: it lets the logic talk about **which reductions are possible** and **what bindings arise**, which feeds runtime reasoning and Ascent/Datalog-style inference over predicates.

## Logical vs staged realization

**Fully relational story (semantics):**

- `unify(pattern, value, env)` — three-place (pattern, value, binding environment).
- `subst(term, var, repl, result)` — four-place, binder-aware, capture-avoiding.

**Staged story (current engineering plan in this repo):**

- **`unifies_<cat>(pattern, value)`** — binary relation in Ascent: “match is possible” (directional pattern → value). The environment `σ` is **not** carried in the relation tuple.
- **`apply_pattern(pattern, value, body) -> Option<_>`** — after the premise succeeds, **reconstruct** bindings by a deterministic walk and apply multi-substitution to `body`.

This split reuses existing premise scheduling (`Premise → Condition`, `generate_condition_clauses`) and keeps term construction in Rust. A future refinement could surface `unify(·,·,σ)` in Datalog if behavioral rules need to mention `σ` explicitly; the conceptual sections above still describe the intended meaning.

## Current Baseline

Today, premise relations already participate in fixpoint scheduling via generated relation lookups. In particular:

- Congruence premise `S ~> T` is lowered to a relation query (`rw_<cat>(S, T)`).
- Premise lowering is handled through `Premise -> Condition` and `generate_condition_clauses` in `macros/src/logic/rules.rs`.
- Ascent evaluates premise relations to fixpoint before dependent rewrites fire.

This is the mechanism reused for unification premises: add `unifies_<cat>(pattern, value)` and plug it into the same condition-generation plumbing.

## Design Overview

The **staged** feature is split into two responsibilities:

1. **Datalog relation (`unifies_`*)** answers whether a pattern unifies with a value (eligibility).
2. **Runtime function (`apply_pattern`)** computes bindings and performs substitution once a rule fires.

This mirrors the architecture where relations express logical preconditions and Rust handles deterministic term construction/evaluation.

## Proposed Semantics (binary relation layer)

For each category `Cat` (for example `Proc`, `Name`), introduce:

```text
relation unifies_cat(Cat, Cat);
```

Read as: directional **pattern** (first argument) **matches** **value** (second argument).

High-level semantics:

- Constructor-to-constructor unification succeeds when labels match and all corresponding child positions unify.
- Pattern free variables in designated “pattern position” unify with any value at that position.
- Collection constructors unify via multiset matching (see dedicated section).
- Optional equational closure may be layered so unification sees equation-equivalent values.

## Implementation roadmap (foundational sequence)

The following steps track the **logical** dependencies; they align with but are not identical to [Rollout Plan](#rollout-plan) phases (which are ordered for incremental shipping).

1. **Extend syntax** — explicit variable nodes (`Var` / analogous) so patterns share the same representation as matchable terms.
2. **Define substitution** — specify (and implement against) capture-avoiding `subst`; keep binder-aware recursion consistent with the relational contract.
3. **Pattern AST** — wildcards, variables, structured constructors, literals as required by rhocalc.
4. **Unification** — structural rules + duplicate-variable consistency; in Ascent: generated `unifies_<cat>` plus premise lowering.
5. **Environment** — in the staged design, bindings are produced inside `apply_pattern`; if moving to a 3-place `unify`, env becomes a relation argument.
6. **Apply to continuation** — COMM RHS uses substitution / `apply_pattern` on the receive body.
7. **Encode COMM rule** — rewrite fires iff unification premises hold (and channel agreement, etc.).

## Design decisions and recommendations

This section records **investigation-backed options** for four choices that were open during design. It is grounded in the current repo: how premises parse (`macros/src/ast/language.rs`), how COMM is written today (`languages/src/rhocalc.rs`), and how `eval` lowers to substitution (`PatternTerm::MultiSubst` in the pattern parser).

### 1. Surface syntax for the unification premise

**Current parser behavior.** A premise starts with an identifier; the **next** token must be `#` (freshness), `~>` (congruence), `(` (relation call), or `.*map(` (forall). Anything else is rejected. So any new form must extend this disambiguation and stay distinct from `~>` and equation/rewrite judgements.

```862:926:macros/src/ast/language.rs
/// Parse a single premise in the propositional context
/// Grammar: freshness | congruence | relation_query | forall
///   freshness  ::= ident "#" (ident | "..." ident)
///   congruence ::= ident "~>" ident
///   relation   ::= ident "(" (ident ("," ident)*)? ")"
///   forall     ::= ident "." "*" "map" "(" "|" ident "|" premise ")"
fn parse_premise(input: ParseStream) -> SynResult<Premise> {
    let first = input.parse::<Ident>()?;
    // ... branches on #, ~>, (, . ...
```

| Option | Shape | Pros | Cons |
| ------ | ----- | ---- | ---- |
| **A** | `unifies(pat, val)` or `unifies_proc(pat, val)` | Matches “relation call” style next to `env_var(x,v)` | If implemented as a generic `RelationQuery`, needs a **reserved** builtin name and special lowering |
| **B** | `pat ~? val` | Visually paired with `~>` | Extra lexer/parser work: `~` must not commit to `~>`; authors learn another operator |
| **C** | `pat unifies val` | Reads like informal logic | New branch (ident then keyword `unifies`); odd if a metavar were named `unifies` (rare in this DSL) |
| **D** | Surface looks like **A**, AST is always **`Premise::Unification`** (not a user-defined relation) | Clear separation: user relations vs primitive; good errors in codegen | Slight conceptual duplication with `rel(args)` look |

**Recommendation.** **D** with concrete surface **`unifies(pat, val)`**, implemented by recognizing `unifies` as a **keyword** in premise position and parsing into **`Premise::Unification { pattern, value }`** (not `RelationQuery`). Rationale: fits the existing conjunction-of-premises story, avoids `~?` / `~>` edge cases, and keeps lowering explicit.

Optional: if category must be visible for disambiguation, reserve `unifies_proc` / `unifies_name`; the macro may still infer category from metavar types when possible.

### 2. Binary `unifies_cat(pattern, value)` vs three-place `unify(pattern, value, env)` in Datalog

**Pipeline context.** Congruence lowers to `rw_<cat>(S, T)`; premises become `Condition` clauses. There is no generic “environment” tuple in that path today. On the RHS, multi-arg `eval` already desugars to **`MultiSubst`** (substitution application after matching), i.e. bindings are realized when building the result term.

**Options.**

| Option | Meaning | Pros | Cons |
| ------ | ------- | ---- | ---- |
| **A** | Binary `unifies_cat(p, v)` in Ascent; `apply_pattern` / `MultiSubst` rebuilds `σ` | Smallest change; matches staged design; enough for “COMM fires or not” | Rules that must quantify over the **exact** `σ` cannot see it in Datalog |
| **B** | Three-place `unifies_proc(p, v, env)` with a concrete `Env` type | `σ` is first-class in fixpoint; natural for rich behavioral typing | Must design `Env` representation, more clauses, stratification and size risk |
| **C** | Binary for rewrites plus auxiliary relations (e.g. per-binding tuples) only where typing needs them | Incremental | Two stories to test; overlaps with `apply_pattern` |

**Recommendation.** **A for Phase 1–2:** binary `unifies_<cat>` for eligibility, `apply_pattern` (or existing `eval`/`MultiSubst` path) for `σ`. Adopt **B or C** only when a **concrete** typing or logic rule needs `σ` in a premise—not speculatively. If B is added later, choose `Env` encoding by what Ascent can stratify and what `Proc`/`Name` can index cheaply.

### 3. Scope of the first pattern-based COMM (multiset / `PPar` inside pattern)

**Baseline in rhocalc.** The existing **`Comm`** rule already matches a **parallel bag** with structured LHS syntax (`PPar`, `PInputs`, `#zip`/`*map` over outputs). The receive side is **`PInputs`** with **`^[xs].p`**: names per channel, not arbitrary **`Proc`** patterns in receive position.

```821:824:languages/src/rhocalc.rs
        Comm . |- (PPar {(PInputs ns cont), *zip(ns,qs).*map(|n,q| (POutput n q)), ...rest})
            ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});
```

```76:77:languages/src/rhocalc.rs
        PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
        |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;
```

**Multiset** complexity is already on composition for **outputs**; the gap for “pattern COMM” is **payload / receive patterns** and unification, not “first contact with bags.”

**Options.**

| Option | Scope | Pros | Cons |
| ------ | ----- | ---- | ---- |
| **A** | Minimal: e.g. single channel or keep names only; strict structural **`Proc`** patterns **without** `PPar` inside pattern | Fast to ship | Skips nested parallelism in patterns |
| **B** | Full multiset-in-pattern (pattern contains a bag) | Matches full Rholang eventually | NP-hard matching; belongs in collection-unification phase |
| **C** | **Multi-channel** as today; evolve each receive arm toward **`n ? pattern`** ( **`Proc`** pattern per bind site) | Fits current rule shape; closest incremental step to Rholang | Requires grammar + `PInputs` change + unification per arm |

**Recommendation.** **C** as the first pattern-COMM milestone, with patterns restricted to **Phase-1 structural unification** (constructors, variables, literals). Defer **B** to the dedicated [Collection Pattern Matching](#collection-pattern-matching-hard-part) phase.

### 4. Explicit `Var` in `Proc` (vs other representations)

**Current state.** Many native/nominal categories get generated **`Var`** variants and eval-time “must substitute first” behavior. **`Proc`** in rhocalc is a large fixed constructor set; receive variables today are **`Name`** slots in **`PInputs`**, not a general **`Proc::Var`**. For **structured receive patterns** (e.g. a pair of processes), variables must appear in **`Proc`** positions, not only in **`Name`**.

**Options.**

| Option | Approach | Pros | Cons |
| ------ | -------- | ---- | ---- |
| **A** | Add **`Proc`-level variable** (e.g. `PVar(x)` / `ProcVar`) | Single `Proc` AST; `unifies_proc` treats pattern-side var as wildcard (directional) | Parse, display, subst, and “no eval until ground” must include this form |
| **B** | Only **Name-level** vars | Reuses `Name::Var` | Insufficient for structured **`Proc`** patterns |
| **C** | Separate **`Pat`** category | Theoretically clean | Large migration and duplication vs `Proc` |

**Recommendation.** **A** until a concrete conflict forces **C**: one process algebra with a distinguished variable form, aligned with directional `unifies_proc` and substitution.

### Cross-cutting default for implementation

Ship **keyword surface** `unifies(pat, val)` → **`Premise::Unification`**, **binary** `unifies_<cat>` in Ascent for the first milestone, **per-bind-site** **`Proc`** patterns on **`PInputs`**, and a **`Proc`** variable constructor—matching today’s parser, today’s COMM layout, and the staged “`σ` in Rust” plan, while leaving a clear path to three-place unification and multiset patterns when a hard requirement appears.

## Macro and Runtime Changes

| File                                    | Change                                                                                                         |
| --------------------------------------- | -------------------------------------------------------------------------------------------------------------- |
| `macros/src/ast/language.rs`            | Add `Premise::Unification { pattern, value }` (or similarly named fields).                                     |
| `macros/src/ast/grammar.rs`             | Add/extend `TermParam` metadata to mark pattern-binder positions (if needed by codegen).                       |
| `macros/src/logic/relations.rs`         | Emit `unifies_<cat>` declarations for eligible categories.                                                     |
| `macros/src/logic/unification.rs` (new) | Auto-generate structural unification rules per constructor (parallel to congruence generation style).          |
| `macros/src/logic/rules.rs`             | Lower `Premise::Unification` to `Condition::EnvQuery`-like relation clause generation (new condition variant). |
| `macros/src/gen/term_ops/`              | Add `apply_pattern` helper for binding extraction + multi-substitution.                                        |
| `languages/src/rhocalc.rs`              | Add **`PPatVar`** / **`$x`**, evolve **`PInputs`** for **`Proc`** patterns, optional **`pair`** (or chosen product), and **`CommPat`** with **`unifies`** + **`apply_pattern`** (see [Concrete syntax proposal](#concrete-syntax-proposal-for-this-document)). |

## AST and Parsing

**Preferred surface:** `unifies(pat, val)` parsed as **`Premise::Unification`** (see **§1** under [Design decisions and recommendations](#design-decisions-and-recommendations)). Alternatives still on the table for minor variants:

- `pattern ~? received`
- `pattern unifies received` (infix keyword)

Selection criteria:

- Must be unambiguous with existing `~>` and `=` judgements.
- Must parse to two identifiers/terms that are already bound in the rule context.
- Should preserve existing parser constraints for premise atoms and conjunctions.

AST addition (illustrative):

```rust
pub enum Premise {
    Freshness(FreshnessCondition),
    Congruence { source: Ident, target: Ident },
    RelationQuery { relation: Ident, args: Vec<Ident> },
    ForAll { collection: Ident, param: Ident, body: Box<Premise> },
    Unification { pattern: Ident, value: Ident },
}
```

Internal `Condition` should gain a matching variant so `generate_condition_clauses` can emit `unifies_<cat>(pattern, value)`.

## Relation Declaration and Generation

In logic relation declaration generation (`macros/src/logic/relations.rs`), emit:

- `relation unifies_proc(Proc, Proc);`
- `relation unifies_name(Name, Name);`
- etc., for categories where matching is meaningful.

Generation policy should mirror existing category filters used in congruence/equations codegen to keep behavior deterministic and compile-time bounded.

## Auto-Generated Structural Unification Rules

New module `macros/src/logic/unification.rs` generates Ascent rules for each constructor shape.

### 1) Ground constructor rule

For nullary constructors, emit direct self-match rules.

### 2) Recursive constructor rule

For constructor `C` with child fields `(f1, ..., fn)`:

```text
unifies_cat(a, b) <--
  cat(a), cat(b),
  if let Cat::C(...f1a..., ...fna...) = a,
  if let Cat::C(...f1b..., ...fnb...) = b,
  unifies_child1(f1a, f1b),
  ...
  unifies_childN(fna, fnb);
```

Where each `unifies_childK` dispatches to the corresponding category relation (`unifies_proc`, `unifies_name`, etc.).

### 3) Pattern variable wildcard rule

For designated pattern-variable positions, emit rules that allow wildcard matching:

```text
unifies_cat(a, b) <-- cat(a), cat(b), if a.is_free_var();
```

Important: this must only apply in pattern role, not symmetrically in all contexts, otherwise relation meaning degrades to near-universal matching for terms containing free vars.

### 4) Optional equational closure

If equational matching is desired, add closure rules such as:

```text
unifies_cat(a, c) <-- eq_cat(a, b), unifies_cat(b, c);
unifies_cat(a, c) <-- unifies_cat(a, b), eq_cat(b, c);
```

This yields equational pattern matching while preserving relation-based guards.

## COMM Integration

COMM rule shape:

1. LHS identifies a receive form (e.g. **`(PInputs … pattern body)`** in rhocalc; the doc sketch **`PFor n pattern body`** is equivalent intent) and **`(POutput n received)`** in parallel with `...rest`.
2. Premise includes `unifies_proc(pattern, received)` (or the parsed equivalent).
3. RHS applies deterministic runtime helper:
   - `apply_pattern(pattern, received, body)` → substituted body.
4. Result term rebuilt into `PPar` with remainder.

This keeps matching eligibility in fixpoint logic and avoids re-running expensive binder extraction unless the premise already succeeded.

## `apply_pattern` Runtime Contract

`apply_pattern(pattern, value, body)` performs:

1. Structural walk over `(pattern, value)`.
2. Binding collection map `{free_var -> matched_subterm}`.
3. Conflict check (same free var bound multiple times):
   - Either require alpha-equivalent/equal assignments.
   - Or fail deterministically (rule does not fire).
4. Capture-avoiding multi substitution into `body` using existing substitution utilities (consistent with the `subst` relational spec).

Recommended signature direction:

```rust
fn apply_pattern(pattern: &Proc, value: &Proc, body: &Proc) -> Option<Proc>
```

Using `Option` (or `Result`) avoids panic paths and keeps COMM RHS generation straightforward.

## Worked examples: surface language, parsing, internals, results

Examples below mix **three layers** on purpose:

1. **Object language** — what the programmer writes (Rholang-like or rhocalc concrete syntax).
2. **`language!` judgement** — the rewrite rule the macro parses (names of pattern metasyntax variables such as `pat`, `recv`, `body`).
3. **Implementation** — AST, generated Ascent, and Rust helpers.

Some object-language constructs are **targets** of the [Design decisions](#design-decisions-and-recommendations) (per-channel **`Proc`** patterns, **`ProcVar`**); they are marked **(target)** where they are not yet the literal `rhocalc.rs` grammar.

### Baseline: COMM today (no pattern unification premise)

rhocalc already encodes multi-channel communication with **name** binders in **`PInputs`** and no `unifies` guard:

```821:824:languages/src/rhocalc.rs
        Comm . |- (PPar {(PInputs ns cont), *zip(ns,qs).*map(|n,q| (POutput n q)), ...rest})
            ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});
```

Receive syntax binds **`Name`** parameters per channel, not arbitrary **`Proc`** patterns:

```76:77:languages/src/rhocalc.rs
        PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
        |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;
```

**Parse (rule row).** The macro parses the judgement’s `prop_context` as empty here; LHS/RHS are `Pattern` trees (`PPar`, `#zip`, `*map`, etc.).

**Run.** Outputs `qs` are lined up with names `ns`; **`eval cont …`** desugars to **`MultiSubst`**: substitute quoted names into **`cont`**’s body. Matching of **payload structure** is not expressed as a premise—only arity/channel agreement via the LHS shape.

---

### Example 1 — Simple pattern variable vs literal value **(target)**

**Object language (informal).** “Receive on `k` any process bound to pattern variable `x`; send `7` (as a process).”

```text
// Rholang-like
for (x <- k) { P }  |  k!(@7)

// rhocalc / REPL (proposal — see § Concrete syntax proposal):
//   { k!(7) | for(k -> $x){ … body using $x … } }
```

**Rewrite rule (illustrative judgement).** Preferred premise shape from [§1 in Design decisions](#design-decisions-and-recommendations):

```text
CommPat . | unifies(pat, recv)
    |- (PPar {(PInputs ns cont), (POutput n recv), ...rest})   // simplified: single output vs multi today
    ~> (PPar {(apply_pattern pat recv body), ...rest});
```

In a full language, `pat` and `recv` are **metasyntax identifiers** bound by the LHS (e.g. `pat` extracted from the receive constructor, `recv` from the output). The design doc’s sketch used `PFor n pattern body`; rhocalc may keep **`PInputs`** and thread a **single** or **multi** pattern form—same idea.

**Parsing.**

1. **Propositional context:** `unifies(pat, recv)` is tokenized like a builtin call: keyword **`unifies`**, `(`, two identifiers, `)` → **`Premise::Unification { pattern: pat, value: recv }`** (not a user `RelationQuery`).
2. **Judgement:** `|- … ~> …` parses LHS/RHS `Pattern` AST as today.

**Internal processing.**

| Stage | What happens |
| ----- | ------------ |
| Macro / `premise_to_condition` | Maps unification premise to a **condition** that codegen turns into an Ascent clause requiring **`unifies_proc(pat, recv)`** (or the category inferred for metavar `pat`). |
| Generated Ascent | Rules from [Auto-Generated Structural Unification Rules](#auto-generated-structural-unification-rules) derive **`unifies_proc(pat, recv)`** when `pat` is a pattern-role variable and `recv` is e.g. `CastInt(7)`, or when both sides unify structurally. |
| COMM clause | The rewrite rule’s generated clause lists **`unifies_proc(pat, recv)`** among conditions; if it cannot be derived, the COMM **does not fire**. |
| RHS Rust | If the engine selects this rewrite, codegen emits **`apply_pattern(pat, recv, body)`** (or `Option` unwrap in a safe wrapper). |

**Result.**

- **Success:** `apply_pattern` builds `{ x ↦ CastInt(7) }` (names internalized per implementation), substitutes into **`body`**, and the parallel multiset loses the consumed receive/send pair—same high-level story as today’s **`Comm`**, but the guard is **structural** not “any name.”
- **Failure:** If `recv` is not unifiable with `pat` (e.g. pattern expects a pair, value is an int), **`unifies_proc`** never holds → **no COMM** on that rule instance.

---

### Example 2 — Structured pattern **(target)**

**Object idea.** Receive only if the payload matches **`(u, v)`**-shaped data (actual constructor names depend on rhocalc—tuple/list patterns are illustrative).

```text
Pattern pat ≅ ConsPair(PVar(a), PVar(b))     // illustrative
Value recv ≅ ConsPair(CastInt(1), CastInt(2))
Body   body uses a, b inside processes
```

**Premise.** `unifies(pat, recv)` recurses: unify heads, unify `PVar(a)` with `1`, `PVar(b)` with `2`.

**`apply_pattern`.** Walk builds `σ = { a ↦ 1, b ↦ 2 }`; then multi-subst into `body`. If `body` binds `a` under **`PNew`**, substitution remains capture-avoiding via existing binder-aware **`subst`** machinery.

**Result.** After COMM: continuation with **`a`/`b`** replaced; remainder of **`PPar`** unchanged.

---

### Example 3 — Repeated pattern variable (consistency)

**Pattern.** `ConsPair(PVar(x), PVar(x))` (**(target)** syntax).

| Value `recv` | `unifies_proc(pat, recv)` | `apply_pattern` / result |
| ------------ | ------------------------- | -------------------------- |
| `ConsPair(CastInt(1), CastInt(1))` | **yes** | `σ = { x ↦ 1 }`; body reduced |
| `ConsPair(CastInt(1), CastInt(2))` | **no** | rule does not fire; **duplicate binding conflict** |

Internally, the Ascent-side relation encodes agreement; the Rust walk **double-checks** conflicts and returns **`None`** if inconsistent—useful if codegen paths ever diverge.

---

### Example 4 — Congestion: match fails, process does not reduce on COMM

**Configuration.** `pat` expects `CastInt`, `recv` is `CastStr("hi")`.

**Ascent.** No fact **`unifies_proc(pat, recv)`** (no rule instance closes).

**Outcome.** The top-level **`PPar`** is unchanged w.r.t. this COMM rule; other rules (congruence, other communications) may still apply.

This is the practical payoff of **declarative** guards: failed match is **silent non-applicability**, not a runtime exception in the reduction engine.

---

### Example 5 — Multi-channel (today’s shape + future premise stack) **(target)**

Today’s **`Comm`** uses **`#zip(ns, qs)`** to match many outputs. A future version can **keep that shape** and add **one unification premise per channel pair** (or a single premise over combined patterns, depending on encoding):

```text
// Illustrative: two outputs, two receives — details of pat₁/pat₂ binding TBD
Comm2 . | unifies(pat1, recv1), unifies(pat2, recv2)
    |- (PPar {(PInputs ns cont), *zip(ns, recvs).*map(|n,r| (POutput n r)), ...rest})
    ~> (PPar {(apply_pattern_multi cont patterns recvs), ...rest});
```

**Parse.** Comma-separated premises → conjunction in `prop_context` (already the story in [01-26-syntax](01-26-syntax.md) for judgements).

**Internal.** Ascent requires **both** `unifies_proc` facts; RHS applies substitutions consistent with **`cont`**’s multi-binder (today’s **`^[xs].p`** style, extended so each **`xᵢ`** aligns with a **`Proc`** pattern if needed).

**Result.** Same concurrent intuition as current rhocalc **`Comm`**, with **pattern** discipline on each payload.

---

### Trace summary (mental checklist)

```text
Source text  →  language! parse  →  RewriteRule { premises, left, right }
                      ↓
               Premise::Unification → Condition → Ascent guard on COMM clause
                      ↓
Runtime term  →  Ascent fixpoint  →  unifies_* facts + rw_* / COMM conclusion
                      ↓
Selected COMM RHS  →  apply_pattern(pat, recv, body)  →  Option<Proc>
                      ↓
               Some(t) replaces redex; None ⇒ this RHS path not taken
```

## Collection Pattern Matching (Hard Part)

Structural constructor matching is straightforward; multiset patterns are the complexity center.

Case: `PPar` represented as `HashBag<Proc>` with pattern elements `P1, P2, ..., Pk, ...rest`.

Required behavior:

- Each `Pi` must match a distinct element in value bag.
- Remaining elements bind to `...rest` when present.
- Bindings from each `Pi` merge consistently.

### Search strategy

Backtracking search over pattern elements:

1. Choose next unmatched pattern element.
2. Iterate candidate value elements in remaining bag.
3. Keep candidates satisfying `unifies_proc(Pi, candidate)`.
4. Remove chosen candidate from remaining bag and recurse.
5. Merge bindings; reject branch on conflict.

Ascent can encode candidate generation through `for`-style clauses, but consumed-element tracking must be explicit (for example via iterative bag removal values in intermediate bindings).

### Complexity

General multiset matching is NP-hard. Practical mitigation:

- Patterns in language rules are usually small.
- Heuristics can reduce branching:
  - Match most selective pattern elements first (fewest candidates).
  - Prefer ground constructors before free-variable patterns.
  - Early fail on arity/size constraints.

## Soundness and Directionality Notes

To avoid accidental over-approximation:

- Treat unification premise as **directional pattern matching** (pattern -> value), even if relation is syntactically binary.
- Restrict wildcard/free-var rules to pattern side only.
- Ensure relation is not used as a generic equivalence relation unless explicitly intended.

If true symmetric unification is later needed, it should be a separate relation with different rules and performance expectations.

## Engineering constraints

- **Priority:** correctness and a working demonstration first; heavy automata/static analysis later.
- **Scope:** unification and patterns should scale toward integers, strings, algebraic data, and the full surface language—not only a minimal process fragment—without redesigning the Var/subst/unify split.
- **Integration:** interpreter, Ascent reasoning, and future behavioral predicates should all be able to rely on the same substitution/unification story.

## Build and run pipelines after pattern matching

This section highlights **what changes operationally** once pattern matching and unification premises land—separating **compile-time (build)** from **runtime (reduction / execution)**. Wording applies to the **staged** plan: binary `unifies_<cat>` in Ascent plus Rust-side `apply_pattern` (or the existing `eval` / `MultiSubst` RHS path extended for patterns).

### Build pipeline (`cargo build`, tests, CI)

**Macro expansion (`mettail_macros` / `language!`).**

- **Parsing:** the `language!` input gains new surface syntax (preferred: `unifies(pat, val)` in the propositional context; possible `Proc`/`PInputs` grammar changes for per-bind-site patterns). Expansion **fails fast** at compile time if premises or patterns are ill-formed—same class of errors as today for bad rewrite judgements.
- **AST / lowering:** `Premise::Unification` and matching `Condition` variants feed `generate_condition_clauses` so COMM rules emit **extra Ascent guard literals** (calls into `unifies_<cat>(…)`), analogous to `rw_<cat>` for congruence.
- **Generated logic:** `relations`-style emission declares **`unifies_<cat>`** for eligible categories; a **unification rule generator** (planned: `macros/src/logic/unification.rs`) adds many structurally recursive Ascent rules—**larger generated Datalog text** and slightly **longer macro expansion time** for big languages (`Proc` with many constructors). Phase 3 (multiset / `PPar`) increases rule bulk further.
- **Generated Rust:** rhocalc’s generated term algebra picks up **`Proc`-level variables** and any new constructors; **`apply_pattern`** (or extended term ops) appears under `macros/src/gen/term_ops/` and is linked from generated `impl` blocks as needed.
- **Downstream crates:** touching `macros` typically forces **rebuild of `languages`**, anything that `include!`s generated Ascent, and tests that diff codegen—**no new mandatory manual step** beyond a normal workspace `cargo build` / `cargo test`.

**Net effect on build.** Incremental **compile time and artifact size** grow modestly with generated rule count; worst-case jumps appear when collection unification lands. CI should add or extend **macro-level tests** (premise parse → expected Ascent fragments) and **integration tests** (COMM match / no-match).

### Run pipeline (rewrite engine, reductions, tooling)

**Ascent fixpoint (when rewrites run inside the logical engine).**

- The engine still runs **stratified** rounds; **new relations** `unifies_<cat>` participate in the **same** overall schedule as other generated relations (`eq_*`, `rw_*`, …). A COMM rule with a unification premise **does not fire** until matching `unifies_*` facts are derived—so some reductions become **guard-order dependent** in the same way congruence already depends on `rw_*`.
- **Work per step:** each candidate COMM may trigger **extra joins** on `unifies_proc( pattern, received )` (and later, heavier multiset search). Cost is **pattern-size- and term-size-dependent**; Phase 1 structural rules aim to stay predictable.

**Rust runtime (term construction after a rule matches).**

- When the COMM RHS runs, **bindings are not read back from Datalog tuples** in the staged design: **`apply_pattern`** (or `MultiSubst` extended for patterns) **re-walks** `(pattern, value)` and then substitutes into the continuation. That adds **deterministic CPU** proportional to pattern + value size, in exchange for a simpler relation arity and reuse of existing substitution infrastructure.

**User-visible behavior.**

- **Fewer spurious COMM steps:** sends that do not match a receive **pattern** do not reduce (soundness vs today’s name-only receive in some embeddings).
- **REPL / drivers** unchanged in **invocation** (`cargo run` on `repl`, same APIs); behavior changes only where **reduction sequences** differ.

**What stays the same.**

- Workspace layout, **Ascent engine crate** boundary (per [Non-goals](#non-goals)), and the high-level story “macro generates logic + Rust terms; engine runs fixpoint” are unchanged—pattern matching **extends** the pipelines rather than replacing them.

## Rollout Plan

### Phase 1: Minimal structural unification

- Add AST + parsing + relation declaration plumbing.
- Generate unification rules for non-collection constructors.
- Add premise lowering in rule codegen.
- Add small unit tests for constructor and free-var behavior.

### Phase 2: COMM + runtime bindings

- Add `apply_pattern` runtime helper.
- Introduce **`PPatVar`** / evolved **`PInputs`** (see [Concrete syntax proposal](#concrete-syntax-proposal-for-this-document)) in rhocalc.
- Implement COMM rewrite using unification premise and `apply_pattern`.
- Add end-to-end tests for successful/failed communication matches.

### Phase 3: Collection unification

- Implement `PPar`/bag matching with consumed-element tracking.
- Add ambiguity/conflict tests and backtracking coverage.
- Add stress tests for branching behavior and guardrails.

### Phase 4: Equational composition (optional)

- Add eq-closure integration with `unifies_`*.
- Verify compatibility with existing `eq_*` and `rw_*` closure behavior.

## Testing Strategy

1. **Codegen tests (macro level):**
   - Premise parse and AST mapping for unification syntax.
   - Generated Ascent includes `unifies_<cat>` clauses.
2. **Relation semantics tests:**
   - Ground constructor success/failure.
   - Recursive constructor descent.
   - Pattern free-var wildcard behavior and side restrictions.
3. **COMM integration tests (language level):**
   - Message matches pattern → rewrite fires with expected substitution.
   - Non-matching message → rewrite blocked.
   - Repeated variable in pattern requires consistent binding.
4. **Collection tests:**
   - Deterministic small bag matches.
   - Rest binding correctness.
   - Ambiguous branches converge to equivalent outcomes (or expected multiplicity semantics).
5. **Performance checks:**
   - Small/medium pattern sizes benchmarked to detect regressions.

## Non-Goals

- Changing Ascent engine internals.
- Replacing existing substitution or binder infrastructure wholesale without a migration story.
- General-purpose higher-order unification beyond the pattern-matching use case.

## Open Questions

Resolved directions for syntax, Datalog arity, first COMM scope, and `Proc` variables are in [Design decisions and recommendations](#design-decisions-and-recommendations); remaining items:

1. **Sign-off:** adopt `unifies(pat, val)` + `Premise::Unification` as the locked surface syntax (vs minor variants like explicit `unifies_proc`).
2. **Directionality encoding:** separate `matches(pattern, value)` relation vs directional constraints on `unifies` if we ever need symmetric unification for a different rule class.
3. **Conflict policy:** when a variable appears multiple times in a pattern, require strict structural equality or eq-closure equality?
4. **Collection semantics:** should multiple valid multiset matches produce multiple rewrites or deterministic single rewrite selection?
5. **Eq integration timing:** ship structural matching first, then add equational closure, or ship together behind a feature gate?
6. **Surfacing `σ`:** when (if ever) must binding environments appear as explicit Datalog tuples for behavioral typing rules—trigger to move from binary `unifies_<cat>` to option B/C in §2 above?

## Conceptual summary

Pattern-based COMM in a logical embedding of Rholang needs **explicit variable syntax**, a **capture-avoiding substitution** primitive (spec’d relationally as `subst`), and **unification premises** that relate receive patterns to sent values before a reduction fires. Bindings `σ` justify applying substitution to the continuation. Explicit variables are chosen over purely implicit lambda binding so patterns can bind dynamically during matching and the theory can grow toward behavioral predicates and Ascent-side reasoning without rewriting the core term algebra. The implementation can stage eligibility as binary `unifies_<cat>` in Ascent while reconstructing `σ` in `apply_pattern` on the COMM RHS, unless a later design lifts full `unify(pattern, value, env)` into relations.

## Minimal mental model

```text
match(pattern, value)  — as unification premises / unifies_*
        ↓
produce bindings σ       — via apply_pattern walk (staged) or explicit env relation (future)
        ↓
apply subst(continuation, σ)
        ↓
COMM reduction fires
```

## Expected Benefits

- Reuses existing relation-premise fixpoint machinery cleanly.
- Keeps rewrite guards declarative and compositional.
- Aligns with current macro architecture (parallel to congruence generation).
- Enables expressive COMM/pattern semantics without engine-level changes.
- Grounds future **behavioral types** in the same pattern/unification/substitution core.
