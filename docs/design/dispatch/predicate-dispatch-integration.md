# Predicate Dispatch Integration: From Heuristic Substitutes to Explicit Configuration

> **Scope.** This document explains how the explicit `guards { }` block
> from design doc §2A integrates with the heuristic dispatch layers in
> `prattail/src/predicate_dispatch.rs`. It is the implementor's reference
> for the bypass model that turns heuristics from "additive on top of
> explicit config" into "fallback when no explicit config" — the design
> intent that motivates the cleanup. The companion documents
> [predicated-types.md](../predicated-types.md) §2A and
> [guards-block.md](../guards-block.md) describe the user-facing surface
> syntax; this document describes the *how* of integration.

---

## Table of Contents

1. [Motivation and the Over-Activation Problem](#1-motivation-and-the-over-activation-problem)
2. [Notation, Symbols, Acronyms](#2-notation-symbols-acronyms)
3. [The Two-Layer Dispatch Model](#3-the-two-layer-dispatch-model)
4. [The Bypass Architecture](#4-the-bypass-architecture)
5. [Per-Module Dispatch Table](#5-per-module-dispatch-table)
6. [Soundness Theorem](#6-soundness-theorem)
7. [Pseudocode for the Key Functions](#7-pseudocode-for-the-key-functions)
8. [Worked Examples](#8-worked-examples)
9. [CONN02: Closed-World Connectives](#9-conn02-closed-world-connectives)
10. [Migration Guide](#10-migration-guide)
11. [Implementation Map](#11-implementation-map)
12. [References](#12-references)

---

## 1. Motivation and the Over-Activation Problem

The MeTTaIL pipeline classifies every grammar with a `PredicateSignature`
— a 15-bit field with one bit per automaton module M1…M15. The
classification function `classify_grammar` originally used **structural
heuristics** to set those bits: scan terminals for `+`, `*`, `/` to
guess linear arithmetic; scan for `match`, `case`, `=>` to guess
unification; scan rule shapes for cross-category references to guess
multi-channel dispatch; match relation names against keyword lists like
`{"eq", "neq", "fresh"}` to guess equality.

The heuristics were always documented as **temporary**. The plan was to
replace them with explicit declarations in a new `guards { }` block:

```rust
guards {
    theories {
        arithmetic = PresburgerAlgebra for [Int];
        patterns   = UnificationTheory for [Proc, Name];
        types      = LatticeTheory     for [Proc, Name];
    }
    channels {
        channel Name;
        join PGuardedInput(ch: Name);
    }
}
```

The `guards { }` block was implemented in the previous task (see
[guards-block.md](../guards-block.md)). But the implementation only
**added** explicit-config activation on top of the heuristics — it did
not bypass them. The result is **over-activation**:

- A Lambda calculus with `Term` and `Type` categories triggers M8
  (Multi-Tape) and M11 (Two-Way Transducer) because two cross-referenced
  categories trip the structural heuristic — even though there are no
  channels at all.
- A calculator with a `+` terminal triggers M12 (Linear Arithmetic) even
  if its guard predicates never reference Presburger arithmetic.
- A language that explicitly registers
  `theories { arithmetic = PresburgerAlgebra for [Int]; }` *also*
  triggers M9 (Multiset) if any rule mentions `count_ge`, because
  `is_cardinality_relation("count_ge") == true`.

Over-activation is not unsound — extra modules in a `PredicateSignature`
just spawn extra (and ultimately unused) compile-time analysis. But it
defeats the entire reason `guards { }` exists. The grammar author who
goes to the trouble of declaring "I use Presburger and only Presburger"
should not have their explicit choice silently overridden by a stray
`+` somewhere else in the grammar.

The cleanup described in this document re-architects the dispatch layer
so that **explicit declarations bypass the corresponding heuristics**.
Languages without `guards { }` see identical behavior to before. Only
the path with explicit configuration changes — and on that path, the
explicit declaration is now the sole authority for the affected modules.

---

## 2. Notation, Symbols, Acronyms

This section defines every symbol and acronym before first use. The
reader can skip ahead and refer back as needed.

### Mathematical and logical symbols

| Symbol | Read as  | Meaning in this document                                                  |
|--------|----------|---------------------------------------------------------------------------|
| `σ`    | sigma    | A grammar dispatch signature: a subset of `{M1,…,M15}`                    |
| `⊆`    | subset   | Subset (improper) on signatures, viewed as bit-sets                       |
| `⊇`    | superset | Superset (improper) on signatures                                         |
| `∪`    | cup      | Set union (signature merge)                                               |
| `∩`    | cap      | Set intersection                                                          |
| `∖`    | minus    | Set difference                                                            |
| `∅`    | empty    | The empty set / empty signature                                           |
| `∈`    | in       | Set or bit-set membership                                                 |
| `↦`    | mapsto   | Function or map application                                               |
| `≡`    | equiv    | Definitional or logical equivalence                                       |
| `∀`    | forall   | Universal quantifier                                                      |
| `∃`    | exists   | Existential quantifier                                                    |
| `⟦·⟧`  | denote   | Denotation function — interprets a syntactic object as its semantic value |
| `1[P]` | iverson  | Iverson bracket: `1` if predicate `P` is true, `0` otherwise              |
| `|S|`  | abs      | Cardinality of set `S`                                                    |

### Acronyms

| Acronym | Expansion                                                         |
|---------|-------------------------------------------------------------------|
| AST     | Abstract Syntax Tree                                              |
| AWA     | Alternating Weighted Automaton                                    |
| CHAM    | Chemical Abstract Machine (Berry & Boudol, 1992)                  |
| DSL     | Domain-Specific Language                                          |
| DOI     | Digital Object Identifier                                         |
| FOL     | First-Order Logic                                                 |
| MSO     | Monadic Second-Order logic                                        |
| RAII    | Resource Acquisition Is Initialization (a Rust idiom for scoping) |
| SFA     | Symbolic Finite Automaton                                         |
| SFT     | Symbolic Finite Transducer                                        |
| W2T     | Weighted Two-way Transducer (Feng & Maletti, 2022)                |
| WMA     | Weighted Multi-tape Automaton (Kempe, 2004)                       |

### Module identifiers (M1–M15)

The pipeline activates one or more of fifteen *automaton modules* per
grammar. Each module is a self-contained analysis pipeline that consumes
the grammar and emits compile-time information used by codegen,
diagnostics, or pipeline optimization. The full set:

| ID  | Name                | One-line purpose                                                                |
|-----|---------------------|---------------------------------------------------------------------------------|
| M1  | Symbolic Automata   | Always-active baseline; effective Boolean algebra over predicates               |
| M2  | Büchi               | ω-regular liveness properties                                                   |
| M3  | AWA                 | Alternating weighted automata for branching predicates                          |
| M4  | VPA                 | Visibly pushdown automata for paired-bracket nesting                            |
| M5  | Parity Tree         | Mu-calculus fixpoints over tree structures                                      |
| M6  | Register            | Data equality and freshness tracking                                            |
| M7  | Probabilistic       | Selectivity/cost-driven scheduling under ambiguity                              |
| M8  | Multi-Tape          | Synchronized traversal of N channel value tapes                                 |
| M9  | Multiset            | Cardinality and AC-matching over collections                                    |
| M10 | Weighted MSO        | Always-active baseline; weighted MSO formula compilation                        |
| M11 | Two-Way             | Backward constraint propagation across channels                                 |
| M12 | Linear Arithmetic   | Presburger arithmetic decision procedure                                        |
| M13 | Unification         | First-order syntactic unification                                               |
| M14 | Subtype Lattice     | Finite subtype hierarchy with join/meet                                         |
| M15 | SFT                 | Symbolic finite transducers for output-producing transformations                |

For full definitions of M1–M15, see
[predicated-types.md](../predicated-types.md) §§16–17.

### Theory kinds

The new `TheoryKind` enum classifies the constraint theories the pipeline
recognizes. Each variant maps to a class of theory-type identifiers a
grammar author can register in `guards { theories { } }`. The kinds in
the current implementation:

| Kind          | Activates (when registered) | Bypasses (when registered)                                        |
|---------------|-----------------------------|-------------------------------------------------------------------|
| `Presburger`  | M12 Linear Arithmetic       | `is_arithmetic_relation`, arithmetic terminals                    |
| `Unification` | M13 Unification             | `is_unification_relation`, unification terminals                  |
| `Lattice`     | M14 Subtype Lattice         | `is_subtype_relation`, subtype terminals                          |
| `Register`    | M6 Register                 | `is_equality_relation`, default M6 fallback, MSO `Order` register |
| `Multiset`    | M9 Multiset                 | `is_cardinality_relation`                                         |
| `Fixpoint`    | M4 VPA + M5 Parity Tree     | `is_fixpoint_relation`, MSO `letprop`/`mu`/`nu`                   |

A grammar author registers a theory by mapping a *local registration
name* to a *theory type*:

```rust
theories {
    arithmetic = PresburgerAlgebra for [Int];   // local name: "arithmetic"
    patterns   = UnificationTheory for [Proc];  // local name: "patterns"
}
```

The local name (`arithmetic`, `patterns`) is for the grammar author's
convenience. The pipeline matches the *theory type* string
(`"PresburgerAlgebra"`, `"UnificationTheory"`) to determine which
`TheoryKind` is active. See `known_theory_kind` in
`prattail/src/predicate_dispatch.rs`.

---

## 3. The Two-Layer Dispatch Model

The dispatch pipeline now has two complementary layers:

```
                  ┌──────────────────────────────────────┐
                  │           grammar G + guards { }     │
                  └────────────────────┬─────────────────┘
                                       │
                ┌──────────────────────┴──────────────────────┐
                │                                             │
                ▼                                             ▼
        ┌───────────────┐                          ┌─────────────────────┐
        │  Layer A:     │                          │  Layer B:           │
        │  Heuristics   │  ◀── bypassed when ──    │  Explicit config    │
        │  (fallback)   │      Layer B covers      │  (authoritative)    │
        └───────┬───────┘      the same kind       └──────────┬──────────┘
                │                                             │
                └──────────────────────┬──────────────────────┘
                                       │
                                       ▼
                              ┌────────────────┐
                              │  σ: dispatch   │
                              │  signature     │
                              │  (M1…M15 bits) │
                              └────────────────┘
```

**Layer A** is the structural and keyword-matching heuristics that have
always existed in `predicate_dispatch.rs`:

- The `is_*_relation()` functions (`is_equality_relation`,
  `is_arithmetic_relation`, `is_unification_relation`,
  `is_subtype_relation`, `is_cardinality_relation`, `is_fixpoint_relation`).
- The cross-category structural scan in `classify_grammar` that detects
  rules with ≥ 2 referenced categories.
- The terminal scans in `classify_grammar` that detect arithmetic
  symbols (`+`, `-`, `*`, `/`, `%`, `mod`, `div`), unification symbols
  (`match`, `case`, `with`, `=>`, `->`, `|`), and subtype symbols
  (`extends`, `implements`, `:`, `::`, `:<`, `is`).

**Layer B** is the explicit `guards { }` block introduced by the
previous task:

- `theories { name = TheoryType for [Cat1, Cat2]; }` registers a
  constraint theory of a known kind, activating its module(s).
- `channels { channel Cat; join Label(p: Cat, q: Cat); }` declares
  communication channels and join patterns, activating M8 / M11.

**Composition rule.** Layer B activations are *unconditional*: the
explicit declaration always activates its module, regardless of whether
Layer A would have. Layer A activations are *conditional*: a heuristic
fires only when no Layer B declaration covers the corresponding kind.

In set notation:

```
σ(G, guards) = layerB(guards) ∪ {bit ∈ layerA(G) | ¬covered(bit, guards)}
```

where `covered(bit, guards) ≡ ∃ kind. activated_by(kind, bit) ∧ kind ∈ kinds(guards)`.

The `covered` predicate is determined by the per-module bypass table in §5.

---

## 4. The Bypass Architecture

The mechanism that turns "additive heuristics" into "fallback heuristics"
is the same in every place a heuristic check appears:

```
if !theory_registered(guard_config, theory_kind) {
    // existing heuristic check
}
```

The helper `theory_registered` is the single lookup that gates every
heuristic. Its definition is short and pure:

```text
function theory_registered(gc: Option<GuardConfigSpec>, kind: TheoryKind) → bool:
    if gc is None:                                ▷ no explicit config
        return false                              ▷ heuristic runs
    for theory in gc.theories:
        if known_theory_kind(theory.theory_type) = Some(kind):
            return true                           ▷ heuristic bypassed
    return false                                  ▷ heuristic runs
```

`known_theory_kind` is a string-matching function that maps the
stringified `theory_type` (the form produced by
`quote!(#ty).to_string()` in the macro bridge) to a `TheoryKind`:

```text
function known_theory_kind(theory_type: String) → Option<TheoryKind>:
    case theory_type of:
        "PresburgerAlgebra" | "Presburger" | "PresburgerTheory" → Some(Presburger)
        "UnificationTheory" | "Unification"                    → Some(Unification)
        "LatticeTheory"     | "Lattice"                        → Some(Lattice)
        "RegisterTheory"    | "EqualityTheory"                 → Some(Register)
        "MultisetTheory"    | "CardinalityTheory"              → Some(Multiset)
        "FixpointTheory"                                       → Some(Fixpoint)
        otherwise                                              → None
```

Languages can extend this matcher by adding new arms — and registering
the same theory type via the `guards { theories { } }` block — without
otherwise touching the pipeline. The bypass remains backward compatible:
a grammar that registers a theory type unknown to `known_theory_kind`
gets the heuristic-fallback behavior (the conservative default), so no
language ever silently breaks.

### The bypass is monotone

Define the **dispatch signature** of a grammar `G` under guard config
`Γ` as `σ(G, Γ)` — the union of all module bits set by either layer.
The bypass design satisfies:

```
∀G, ∀Γ.   σ(G, Γ) ⊆ σ(G, ∅)
```

In words: adding explicit declarations can only **shrink** the
signature (by silencing over-activations), never grow it past the
unconstrained heuristic baseline.

This is the **soundness invariant** for the bypass. It is formalized in
§6 and tested as a proptest invariant in §7 of the test suite.

---

## 5. Per-Module Dispatch Table

The following table is the authoritative reference for which heuristic
gates which module, and which `TheoryKind` bypasses which heuristic.
Read each row as: "module M is activated by source X, which is bypassed
by registering theory kind K".

| Module ID | Activated by (heuristic)                                                                | Activated by (explicit)                       | Bypassed by `TheoryKind`    |
|-----------|-----------------------------------------------------------------------------------------|-----------------------------------------------|-----------------------------|
| M1        | Always (baseline)                                                                       | Always                                        | (never bypassed — baseline) |
| M2        | Recursive category detection (structural)                                               | (no explicit equivalent)                      | (none — structural)         |
| M3        | ≥3 non-terminal children per rule (structural)                                          | (no explicit equivalent)                      | (none — structural)         |
| M4        | `is_fixpoint_relation` match; MSO `letprop`/`mu`/`nu` label                             | (planned: `theories { … = FixpointTheory; }`) | `Fixpoint`                  |
| M5        | Recursion + branching (structural); `is_fixpoint_relation`; MSO `letprop`/`mu`/`nu`     | (planned: `theories { … = FixpointTheory; }`) | `Fixpoint`                  |
| M6        | `is_equality_relation` match; default fallback for unrecognized predicates; MSO `Order` | (planned: `theories { … = RegisterTheory; }`) | `Register`                  |
| M7        | ≥3 rules per category (structural); ≥2 channels per predicate                           | (no explicit equivalent)                      | (none — structural)         |
| M8        | Cross-category rule references (`≥2`); ≥2 distinct channels per predicate               | `channels { join L(p: C, q: C); }`            | (channels-driven; see §4)   |
| M9        | `is_cardinality_relation` match; collection items in grammar                            | (planned: `theories { … = MultisetTheory; }`) | `Multiset`                  |
| M10       | Always (baseline)                                                                       | Always                                        | (never bypassed — baseline) |
| M11       | Cross-category that differs from rule's own category                                    | `channels { }` with ≥2 distinct categories    | (channels-driven; see §4)   |
| M12       | `is_arithmetic_relation` match; arithmetic terminals (`+`, `-`, `*`, `/`, `%`, …)       | `theories { … = PresburgerAlgebra; }`         | `Presburger`                |
| M13       | `is_unification_relation` match; unification terminals (`match`, `case`, `with`, …)     | `theories { … = UnificationTheory; }`         | `Unification`               |
| M14       | `is_subtype_relation` match; subtype terminals (`extends`, `implements`, `:`, `::`, …)  | `theories { … = LatticeTheory; }`             | `Lattice`                   |
| M15       | Recursion + M11 already active                                                          | (derived; depends on M11)                     | (derived from channels)     |

### Reading the table

A row like `M12 ... bypassed by Presburger` means: when the grammar
config has at least one theory registration whose `theory_type` matches
`Presburger`, the M12 row's heuristic activations (the
`is_arithmetic_relation` calls in `walk_predicate` and the arithmetic
terminal scan in `classify_grammar`) do not run. M12 is then activated
**only** by the explicit theory registration block in
`classify_grammar_with_config`. If no Presburger theory is registered,
the heuristics run as before.

Rows marked "(no explicit equivalent)" or "(none — structural)" are
heuristics that have no `guards { }` analog and always run. They are
purely structural (e.g., counting rules per category) and so they
encode information that the grammar author cannot meaningfully restate.

---

## 6. Soundness Theorem

**Theorem (Bypass Monotonicity).** Let `G` be a grammar, let `Γ` and `Γ'`
be guard configurations such that `Γ ⊆ Γ'` (every theory registered in
`Γ` is also registered in `Γ'`, and similarly for channels). Then:

```
σ(G, Γ') ⊆ σ(G, Γ)   for all heuristic-gated bits
σ(G, Γ') ⊇ σ(G, Γ)   for all explicit-config bits
```

In words: adding more theories or channels to `Γ` can only *shrink* the
heuristic-driven portion of the signature (because each added theory
silences its corresponding heuristic), and only *grow* the
explicit-config portion (because each added theory or channel
activates its module).

**Corollary 1 (Backward compatibility).** When `Γ = ∅`,
`σ(G, ∅) = layerA(G)` — the original heuristic-only signature. The
bypass introduces no behavioral change for languages without
`guards { }`.

**Corollary 2 (No silent loss).** A grammar author who declares
`theories { … = PresburgerAlgebra; }` does not lose M12 activation: the
explicit-theory block in `classify_grammar_with_config` adds M12, and
the bypass only silences the heuristic that *would have* added the same
bit. The net effect is that M12 stays in the signature, but its only
source is now the explicit registration.

**Proof sketch.** The bypass is a single check `if
!theory_registered(gc, kind) { … }` around each heuristic call site.
This check is monotone in `gc`: adding a theory of kind `K` to `gc`
only *flips* `theory_registered(gc, K)` from false to true (it never
flips back). For any heuristic gated by kind `K`, the gate going from
"open" to "closed" can only remove activations. The explicit-theory
block in `classify_grammar_with_config` is independent of the
heuristics — it iterates over `gc.theories` and sets bits — so adding a
theory to `gc` is monotone increasing in that block's contribution.
The two effects compose: the heuristic-gated portion of `σ` is
monotone decreasing in `gc`; the explicit portion is monotone
increasing. The net effect on a *bypassed bit* is "removed from the
heuristic side, added on the explicit side" — a wash. The net effect on
an *unrelated bit* is unchanged. ∎

**Connection to Eilenberg's variety theorem.** The theorem above is the
dispatch-pipeline analog of Eilenberg's classical observation
(Eilenberg, 1976) that membership of a regular language in a variety is
decidable from the syntactic structure of a recognizing automaton —
provided the variety is *finitely characterized*. Here the "varieties"
are the theory kinds, and "syntactic structure" is the AST shape of
predicates and the grammar. The bypass is the operational consequence:
when the grammar author hands the pipeline an explicit characterization
("I use Presburger and only Presburger"), the pipeline trusts it and
skips the structural inference.

> **Citation.** Eilenberg, S. *Automata, Languages, and Machines,
> Vol. B.* Academic Press, 1976. ISBN 0-12-234001-9. (No DOI assigned.)

---

## 7. Pseudocode for the Key Functions

This section presents the dispatch pipeline's three core functions in
literate-programming pseudocode. The order is bottom-up: the helper
functions first, then the walker, then the grammar classifier.

### 7.1 `theory_registered`

The bypass gate. Pure, allocation-free, O(|gc.theories|) per call.

```
function theory_registered(gc: Option<GuardConfigSpec>, kind: TheoryKind) → bool:
    case gc of:
        None     → return false
        Some(g)  → for theory in g.theories:
                       if known_theory_kind(theory.theory_type) = Some(kind):
                           return true
                   return false
```

**Why optional?** Most existing call sites in the test suite (50+
locations) call `extract_features` with no guard config. Making the
parameter optional preserves their ergonomics.

**Why O(n) and not a hash lookup?** The theory list in any realistic
language is small (`≤ 6` theories). The constant-factor overhead of a
hash table dwarfs the linear scan, and the linear scan has zero
allocations and excellent cache behavior. If a language ever exceeds
~16 theories, this can be revisited.

### 7.2 `walk_predicate_with_config`

The recursive predicate-AST walker, with the bypass gates inlined into
the `Relation` arm.

```
function walk_predicate(
    expr: PredicateExpr,
    ctx: ChannelContext,
    sig: PredicateSignature (mut),
    depth, max_depth, channels, registers, has_*: (mut),
    guard_config: Option<GuardConfigSpec>,
):
    case expr of:
        True | False | Atom(_) → return                ▷ base case
        Not(inner)             → recurse(inner)
        And(a, b) | Or(a, b)   → recurse(a); recurse(b)
        ForallFinite { body }  → sig.set(M3_AWA); recurse_at_depth(body)
        ExistsFinite { body }  → recurse_at_depth(body)
        ForallInfinite { body }→ sig.set(M2_BUCHI); sig.set(M3_AWA);
                                 recurse_at_depth(body)
        ExistsInfinite { body }→ sig.set(M2_BUCHI); recurse_at_depth(body)

        Relation { name, args }:
            ▷ Layer C cleanup: gate every heuristic relation-name dispatch
            ▷ on the absence of an explicit theory of the matching kind.
            if not theory_registered(guard_config, Register)
                and is_equality_relation(name):
                sig.set(M6_REGISTER)
                for arg in args: registers.insert(arg)

            if not theory_registered(guard_config, Multiset)
                and is_cardinality_relation(name):
                sig.set(M9_MULTISET); has_cardinality ← true

            if not theory_registered(guard_config, Fixpoint)
                and is_fixpoint_relation(name):
                sig.set(M4_VPA); sig.set(M5_PARITY_TREE); has_recursive ← true

            if not theory_registered(guard_config, Presburger)
                and is_arithmetic_relation(name):
                sig.set(M12_LINEAR_ARITHMETIC); has_arithmetic ← true

            if not theory_registered(guard_config, Unification)
                and is_unification_relation(name):
                sig.set(M13_UNIFICATION); has_unification ← true

            if not theory_registered(guard_config, Lattice)
                and is_subtype_relation(name):
                sig.set(M14_SUBTYPE_LATTICE); has_subtype ← true

            ▷ Channel detection is independent of theory registration —
            ▷ channel structure is orthogonal to theory dispatch.
            for arg in args:
                if ctx.is_cross_channel(arg):
                    sig.set(M8_MULTI_TAPE); sig.set(M11_TWO_WAY)
                    has_backward ← true
                if let Some(ch) ← ctx.channel_of(arg):
                    channels.insert(ch)

            ▷ Default M6 fallback for "data comparison" predicates that
            ▷ don't match any specific heuristic. Bypassed under explicit
            ▷ Register registration.
            if not theory_registered(guard_config, Register)
                and not is_equality_relation(name)
                and not is_cardinality_relation(name):
                sig.set(M6_REGISTER)
                for arg in args: registers.insert(arg)

        Bounded { body } → recurse(body)
```

The recursive calls all thread `guard_config` through unchanged. The
structural rules for quantifiers and Boolean combinators do not
consult `guard_config` — they encode mathematical identities (e.g.,
"a universal quantifier is M3_AWA-relevant") that do not depend on
theory registrations.

### 7.3 `classify_grammar_with_config`

The grammar-level classifier. The data-flow shape is:

```
function classify_grammar_with_config(syntax, categories, guard_config):
    let σ ← empty PredicateSignature
    let category_refs, terminals, has_binders, has_branching ← scan syntax

    ▷ ── Per-rule structural / cross-category passes ──
    for (label, category, rule_syntax) in syntax:
        ▷ Layer A (gated by Layer 3 cleanup):
        ▷ when no explicit channels {} declared, infer M8/M11 from
        ▷ cross-category references in the rule body.
        if guard_config is None or guard_config.channel_categories is None:
            referenced ← all categories referenced by rule_syntax
            if |referenced| ≥ 2:
                σ.set(M8_MULTI_TAPE)
                if any cat in referenced differs from category:
                    σ.set(M11_TWO_WAY)
        ...

    ▷ ── Structural module activations (always run) ──
    if has_recursion: σ.set(M2_BUCHI)
    if has_branching: σ.set(M3_AWA)
    if has bracket-pair terminals: σ.set(M4_VPA)
    if has_recursion and has_branching: σ.set(M5_PARITY_TREE)
    if has_binders: σ.set(M6_REGISTER)
    if rules_per_category ≥ 3: σ.set(M7_PROBABILISTIC)

    ▷ ── Layer B (gated by Layer 2 cleanup): terminal-based theory inference ──
    if not theory_registered(guard_config, Presburger):
        if any arithmetic terminal in terminals: σ.set(M12_LINEAR_ARITHMETIC)

    if not theory_registered(guard_config, Unification):
        if any unification terminal in terminals: σ.set(M13_UNIFICATION)

    if not theory_registered(guard_config, Lattice):
        if any subtype terminal in terminals: σ.set(M14_SUBTYPE_LATTICE)

    if has_recursion and σ.contains(M11_TWO_WAY): σ.set(M15_SFT)

    ▷ ── Explicit-theory and explicit-channel activations (Layer B) ──
    if guard_config is Some:
        for theory in guard_config.theories:
            case known_theory_kind(theory.theory_type) of:
                Some(Presburger)  → σ.set(M12_LINEAR_ARITHMETIC)
                Some(Unification) → σ.set(M13_UNIFICATION)
                Some(Lattice)     → σ.set(M14_SUBTYPE_LATTICE)
                otherwise         → ▷ unknown — fall through
        if guard_config.channel_categories is Some:
            let m8_active ← false
            let distinct_cats ← empty set
            for jp in guard_config.join_patterns:
                if |jp.channel_categories| ≥ 2: m8_active ← true
                distinct_cats ← distinct_cats ∪ jp.channel_categories
            if m8_active: σ.set(M8_MULTI_TAPE)
            if m8_active and |distinct_cats| ≥ 2: σ.set(M11_TWO_WAY)

    return GrammarDispatchPlan { σ, schedule: order_by_cost(σ), … }
```

The structure is: Layer A first (heuristics, with bypass gates),
Layer B second (explicit declarations, unconditional). The order is
chosen so that Layer B runs *after* the gates have already silenced the
heuristic side, ensuring the explicit declaration is the unique source
of activation for any bit it sets.

### 7.4 `parse_behavioral_pred` (Layer 4 cleanup)

The CONN02 enforcement runs at the *trailing edge* of behavioral-pred
parsing. By the time the parser reaches `check_conn02_unlisted_token`,
all tokens it was willing to consume have been consumed; any leftover
Rust connective is one the user wrote but the active map does not
declare.

```
function parse_behavioral_pred(input):
    let result ← parse_pred_implies(input)?
    check_conn02_unlisted_token(input)?
    return result

function check_conn02_unlisted_token(input):
    if not has_active_connective_map():
        return Ok                                      ▷ open-world

    if input peeks `&&` and not active_role_available(And):
        error CONN02: && (role and) not declared in active connectives {}
    if input peeks `||` and not active_role_available(Or):
        error CONN02: || (role or) not declared
    if input peeks `~`  and not active_role_available(Not):
        error CONN02: ~ (role not) not declared
    if input peeks `!`  and not active_role_available(Not):
        error CONN02: ! (role not) not declared
    if input peeks `=>` and not active_role_available(Entails):
        error CONN02: => (role entails) not declared
    return Ok
```

The corresponding check inside the parser-loop functions is the
`rust_token_allowed` helper:

```
function rust_token_allowed(role: ConnectiveRole) → bool:
    if not has_active_connective_map():
        return true                                    ▷ open-world: always
    return active_role_available(role)                 ▷ closed-world: only if declared
```

Each Rust-token branch in `parse_pred_or`, `parse_pred_and`,
`parse_pred_not`, `parse_pred_implies` is gated by
`rust_token_allowed(role)`. The two-stage architecture (gate the loop
inside, then verify at the trailing edge) ensures both that the parser
doesn't wrongly consume a forbidden token *and* that a forbidden token
left behind triggers a precise diagnostic.

---

## 8. Worked Examples

### 8.1 Lambda calculus with two categories — no over-activation

```rust
language! {
    name: GuardedLambda,
    types { Term, Type },
    terms {
        Var . v:Var |- v : Term ;
        Lam . ^x.body:[Term -> Term] |- "lam" x ":" Type "." body : Term ;
        App . f:Term, a:Term |- f a : Term ;
        TBool . |- "Bool" : Type ;
        TArr . s:Type, t:Type |- s "->" t : Type ;
    },
    rewrites { … },
}
```

**Before the cleanup.** The grammar has two categories (`Term`,
`Type`) and rules that reference both. The structural cross-category
heuristic at Layer A activates **M8** and **M11** even though there
are no channels. It also detects `:` as a subtype terminal and
activates **M14**. The signature includes `{M2, M5, M6, M8, M11, M14}`
(plus the baselines) from purely structural inference.

**After the cleanup, with no `guards { }` block.** Identical behavior
— there is nothing to bypass. The signature is unchanged. **Backward
compatibility preserved.**

**After the cleanup, with explicit `guards { channels { } }` declaration:**

```rust
guards {
    channels { }   // ← explicitly empty: no communication channels
}
```

Now `guard_config.channel_categories = Some([])`. The bypass gate
in `classify_grammar_with_config` (Layer A, Phase A) skips the
cross-category structural scan. **M8 and M11 are no longer set.** The
language correctly tells the pipeline "I have no channels," and the
pipeline stops over-activating channel-related modules.

### 8.2 Rholang with theory and channel registrations

```rust
language! {
    name: Rholang,
    types { Proc, Name, ![i64] as Int },
    guards {
        theories {
            arithmetic = PresburgerAlgebra for [Int];
            patterns   = UnificationTheory for [Proc, Name];
            types_t    = LatticeTheory     for [Proc, Name];
        }
        channels {
            channel Name;
            join PGuardedInput(ch: Name);
            join PJoin(ch1: Name, ch2: Name);
        }
    },
    terms { … },
    rewrites { … },
    logic { … },
}
```

**Activations.** The explicit theories activate M12, M13, M14 via the
Layer B block. The explicit channels activate M8 (PJoin has 2 channel
parameters) but not M11 (only one channel category). The structural
heuristics for arithmetic terminals, unification terminals, subtype
terminals, and cross-category references are all bypassed because
their corresponding theory kinds (or channel category) are
registered.

**Net effect.** The signature is identical to the heuristic-only case
for this language, but every set bit now has a single, traceable
source: an explicit declaration. The grammar author who reads the
`PipelineAnalysis` output sees `M12 ← arithmetic theory`, not
`M12 ← saw "+" in some terminal somewhere`.

### 8.3 MeTTa with closed-world connectives

```rust
language! {
    name: MeTTa,
    types { Atom, Expression },
    guards {
        connectives {
            and = "&&";
            not = "~";
            // No or, no quantifiers, no implication.
        }
        theories {
            patterns = UnificationTheory for [Atom];
        }
    },
    terms { … },
    rewrites {
        Step . | guard(p(x) && q(x)) |- (App f a) ~> body ;
    },
}
```

**Layer 4 cleanup.** The active `ConnectiveMap` declares only `And`
(via `&&`) and `Not` (via `~`). The grammar author has explicitly
opted out of disjunction and implication.

A guard expression like `guard(p(x) && q(x))` parses correctly
because `&&` is declared as the spelling of `And`. But `guard(p(x) ||
q(x))` triggers CONN02:

```text
error: CONN02: connective token `||` (role `or`) is not declared in
the active `connectives {}` block
```

This is exactly the closed-world semantics the design doc specifies:
the grammar author's silence on `Or` is a positive declaration that
disjunction is unavailable in this language's guard sublanguage, not
a passive default to be filled in by the parser.

---

## 9. CONN02: Closed-World Connectives

The connective-map portion of the cleanup (Layer 4) is conceptually
distinct from the theory-bypass portion (Layers 1, 2, 3) but uses the
same architectural principle: **explicit declaration overrides
heuristic default**. In the connective case, the "heuristic default"
is the parser's hardcoded recognition of `&&`, `||`, `~`, `!`, `=>` as
the standard Rust spellings of conjunction, disjunction, negation, and
implication.

### How it works

The connective parser chain (`parse_pred_or`, `parse_pred_and`,
`parse_pred_not`, `parse_pred_implies`) consults the active
`ConnectiveMap` via the thread-local `ACTIVE_CONNECTIVE_MAP`. When the
map is `None` (no `connectives { }` block), the parsers accept all
five Rust tokens unconditionally (open-world / backward compatible).
When the map is `Some(m)`, each Rust token is gated:

```text
fn rust_token_allowed(role: ConnectiveRole) → bool:
    if no active map: return true                ▷ open-world
    return active_role_available(role)           ▷ closed-world
```

A Rust token is consumed only if the gate allows it. A forbidden token
left in the input is later caught by `check_conn02_unlisted_token` at
the trailing edge of `parse_behavioral_pred`, which emits CONN02 with
a precise diagnostic.

### Why two stages?

A single check at the trailing edge would be insufficient: without
the per-loop gate, the parser would consume the forbidden token,
reaching the trailing-edge check with empty input. The user would see
no error — only an unexpected `Or` node in their AST.

A single check inside the loop (without the trailing-edge check)
would be sufficient for *parsing*, but the resulting error message
would be the generic syn error ("expected end of input") rather than
the precise CONN02 diagnostic naming the offending token and role.

The two-stage design gives both correctness (the token is not
consumed) and good diagnostics (the trailing-edge check fires CONN02
with full context).

### Diagnostic format

```text
error: CONN02: connective token `||` (role `or`) is not declared in
the active `connectives {}` block
```

Pro-forma rendering:
```text
error[CONN02]: connective token `||` (role `or`) is not declared
  --> src/main.rs:42:20
   |
42 |     guard(eq(x, y) || gt(x, z))
   |                    ^^ not declared in `connectives {}`
   |
   = help: add `or = "||";` to the `connectives {}` block
   = note: declared connectives: and = "&&", not = "~"
```

(The current implementation produces the simpler one-line form via
`syn::Error`. The full multi-line form with `note` and `help` lines
is a planned enhancement.)

---

## 10. Migration Guide

The cleanup is **fully backward compatible**. Every existing language
definition in `languages/src/` (rholang, calculator, lambda, ambient,
led_test, basemath, extmath, mixedmath, importedmath) compiles and
passes its full test suite **unchanged**.

**Languages with no `guards { }` block** continue to work exactly as
before. Every heuristic still fires; nothing is bypassed.

**Languages with a `guards { }` block but no `theories { }` or
`channels { }` sub-blocks** continue to use the heuristics for
theory and channel dispatch. They benefit from the connective and
predicate parts of the block.

**Languages with `guards { theories { } }` registrations** now see
the corresponding heuristic bypassed. The signature for those
languages may *shrink* (silencing over-activations) but never
*grows* — see the soundness theorem in §6. If a grammar author
discovers that a previously-active module was actually only fired
by a heuristic over-activation, they can:

1. Remove the offending terminal (if it's incidental — e.g., remove
   the `+` operator from a calculator that doesn't need integer
   arithmetic), or
2. Register the missing theory explicitly to keep the module active.

**Languages with `guards { connectives { } }`** now enforce CONN02 —
guard expressions using undeclared Rust connective tokens fail to
compile. This is the only behavior change that can break an existing
language, and only if that language *both* declared `connectives { }`
*and* used a hardcoded Rust token for a role it did not declare. As
of this writing, no language in the workspace meets both conditions.

---

## 10A. Simulation Bridge

The `guards { }` block's effect is not confined to the macro and the
pipeline. The runtime crate's `LanguageMetadata` trait carries the
guard configuration all the way to the stochastic simulator in
`simulation`, so runtime analysis tools can introspect
declared theories, channels, and predicates without re-parsing
anything.

The bridge has three layers:

```text
  ┌───────────────────┐                   ┌──────────────────────┐
  │ language! { …     │ → macro codegen → │ LanguageMetadata     │
  │    guards { … } } │                   │  trait impl          │
  └───────────────────┘                   │  (generated)         │
                                          └───────────┬──────────┘
                                                      │
                                                      │ read by
                                                      ▼
                                          ┌──────────────────────┐
                                          │ LanguageStateMachine │
                                          │  (simulation crate)  │
                                          └───────────┬──────────┘
                                                      │
                          ┌───────────────────────────┼───────────────────────────┐
                          ▼                           ▼                           ▼
              ┌───────────────────┐      ┌──────────────────────┐    ┌──────────────────────┐
              │ GuardSatisfaction │      │ StochasticPetriNet:: │    │ Coverage / temporal  │
              │  invariant        │      │  from_channel_meta   │    │  property checking   │
              └───────────────────┘      └──────────────────────┘    └──────────────────────┘
```

**Layer 1: runtime metadata.** `runtime/src/metadata.rs` defines five
new `*Def` types (`BuiltinPredicateDef`, `TheoryDef`, `ChannelDef`,
`JoinPatternDef`, `ConnectiveDef`) and adds five default-empty
methods to the `LanguageMetadata` trait. The `RewriteDef` and
`EquationDef` types gain an additive `is_guarded: bool` field
identifying premises that contained a `BehavioralGuard` in the
source. Languages without a `guards { }` block produce empty slices
for the new methods and `is_guarded: false` for every rewrite /
equation — the runtime interface is fully backward compatible.

**Layer 2: macro emission.** `macros/src/gen/runtime/metadata.rs`
adds five generator functions that read `language.guard_config` and
emit static `&[…]` literals for the new `LanguageMetadata` methods.
A new `behavioral_pred_to_display` helper renders `BehavioralPred`
AST nodes in unicode form (`a ∧ b`, `∀x. φ`, `¬R(x, y)`) — used both
by the metadata `conditions` slice and by the `premise_to_display_string`
function, replacing the previous `format!("{:?}", pred)` output.

**Layer 3: simulator ingestion.** `simulation/src/model.rs` extends
`LanguageStateMachine::from_metadata` to read every new
`LanguageMetadata` method and populate corresponding
`Vec<ModelBuiltinPredicate>`, `Vec<ModelTheory>`, `Vec<ModelChannel>`,
`Vec<ModelJoinPattern>`, and `Vec<ModelConnective>` fields. New
convenience methods on `LanguageStateMachine`:

| Method                    | Returns                                                     |
|---------------------------|-------------------------------------------------------------|
| `guarded_rewrites()`      | iterator over rewrites with `is_guarded == true`            |
| `guarded_equations()`     | iterator over equations with `is_guarded == true`           |
| `has_channels()`          | `true` iff any `ChannelDef` was declared                    |
| `theory_for(category)`    | first `ModelTheory` whose `handled_types` covers `category` |
| `guarded_rewrite_count()` | count of guarded rewrites                                   |

**Downstream consumers.** Two new simulator APIs consume the guard
metadata:

1. **`GuardSatisfaction` invariant**
   (`simulation/src/invariant.rs`). Built via
   `GuardSatisfaction::from_state_machine(&state)`. Tracks the set of
   guarded rewrite rule names. Its `check` method is currently a
   no-op contract surface — it exposes the intended invariant and
   provides the hook for future runner changes that pass the firing
   rule name to invariant methods.

2. **Channel-aware Petri nets**
   (`simulation/src/stochastic_petri.rs`). The
   `StochasticPetriNet::from_channel_metadata(state, default_rate)`
   helper builds a Gillespie-ready stochastic Petri net with one
   place per `ModelChannel` and one transition per `ModelJoinPattern`
   (with input arcs from each channel parameter). This gives users a
   direct path from `guards { channels { … } }` declarations to
   simulate-able stochastic models without hand-coding places and
   transitions.

**Soundness note.** The bridge does not attempt to evaluate
`BehavioralPred` semantics at simulator-step granularity. The
current API exposes the declared contract surface; future work will
thread the firing rule label through the runner's
`step`/`check_invariants` API so that `GuardSatisfaction` can verify
guarded rules fire only when their guards hold.

## 11. Implementation Map

| Layer       | Concern                                         | Bypass site                                    | Function                       | File:line                                                            |
|-------------|-------------------------------------------------|------------------------------------------------|--------------------------------|----------------------------------------------------------------------|
| Layer 3 (A) | Cross-category M8/M11 structural                | Skip when `gc.channel_categories.is_some()`    | `classify_grammar_with_config` | `prattail/src/predicate_dispatch.rs` (cross-cat scan)                |
| Layer 2 (B) | Arithmetic terminal scan → M12                  | Skip when `theory_registered(gc, Presburger)`  | `classify_grammar_with_config` | `prattail/src/predicate_dispatch.rs` (M12 terminal block)            |
| Layer 2 (B) | Unification terminal scan → M13                 | Skip when `theory_registered(gc, Unification)` | `classify_grammar_with_config` | `prattail/src/predicate_dispatch.rs` (M13 terminal block)            |
| Layer 2 (B) | Subtype terminal scan → M14                     | Skip when `theory_registered(gc, Lattice)`     | `classify_grammar_with_config` | `prattail/src/predicate_dispatch.rs` (M14 terminal block)            |
| Layer C     | `is_equality_relation` → M6                     | Gated by `theory_registered(gc, Register)`     | `walk_predicate`               | `prattail/src/predicate_dispatch.rs` (Relation arm)                  |
| Layer C     | `is_cardinality_relation` → M9                  | Gated by `theory_registered(gc, Multiset)`     | `walk_predicate`               | `prattail/src/predicate_dispatch.rs` (Relation arm)                  |
| Layer C     | `is_fixpoint_relation` → M4 + M5                | Gated by `theory_registered(gc, Fixpoint)`     | `walk_predicate`               | `prattail/src/predicate_dispatch.rs` (Relation arm)                  |
| Layer C     | `is_arithmetic_relation` → M12                  | Gated by `theory_registered(gc, Presburger)`   | `walk_predicate`               | `prattail/src/predicate_dispatch.rs` (Relation arm)                  |
| Layer C     | `is_unification_relation` → M13                 | Gated by `theory_registered(gc, Unification)`  | `walk_predicate`               | `prattail/src/predicate_dispatch.rs` (Relation arm)                  |
| Layer C     | `is_subtype_relation` → M14                     | Gated by `theory_registered(gc, Lattice)`      | `walk_predicate`               | `prattail/src/predicate_dispatch.rs` (Relation arm)                  |
| Layer C     | Default M6 fallback for unrecognized predicates | Gated by `theory_registered(gc, Register)`     | `walk_predicate`               | `prattail/src/predicate_dispatch.rs` (Relation arm tail)             |
| Layer C     | MSO `letprop`/`fixpoint`/`mu`/`nu` → M4 + M5    | Gated by `theory_registered(gc, Fixpoint)`     | `walk_mso_formula`             | `prattail/src/predicate_dispatch.rs` (AtomicPos / NegAtomicPos arms) |
| Layer C     | MSO `Order` → M6                                | Gated by `theory_registered(gc, Register)`     | `walk_mso_formula`             | `prattail/src/predicate_dispatch.rs` (Order / NegOrder arms)         |
| Layer 4 (D) | Hardcoded `&&` token                            | Gated by `rust_token_allowed(And)`             | `parse_pred_and`               | `macros/src/ast/language.rs`                                         |
| Layer 4 (D) | Hardcoded `\|\|` token                          | Gated by `rust_token_allowed(Or)`              | `parse_pred_or`                | `macros/src/ast/language.rs`                                         |
| Layer 4 (D) | Hardcoded `~`/`!` tokens                        | Gated by `rust_token_allowed(Not)`             | `parse_pred_not`               | `macros/src/ast/language.rs`                                         |
| Layer 4 (D) | Hardcoded `=>` token                            | Gated by `rust_token_allowed(Entails)`         | `parse_pred_implies`           | `macros/src/ast/language.rs`                                         |
| Layer 4 (D) | CONN02 emission for stranded forbidden tokens   | `check_conn02_unlisted_token` at trailing edge | `parse_behavioral_pred`        | `macros/src/ast/language.rs`                                         |

---

## 12. References

The following references underpin the design decisions in this
document. Each citation includes a working DOI link where available.
References without DOIs use stable identifiers (book ISBN, arXiv ID,
or institutional URL).

1. **Berry, G. & Boudol, G.** "The Chemical Abstract Machine."
   *Theoretical Computer Science*, 96(1):217–248, 1992.
   DOI: [10.1016/0304-3975(92)90185-I](https://doi.org/10.1016/0304-3975(92)90185-I)
   *Used for:* the CHAM operational model that underlies the
   rho-calculus communication primitive whose dispatch this document
   integrates.

2. **Birkhoff, G.** *Lattice Theory.* AMS Colloquium Publications,
   vol. 25, 3rd ed. American Mathematical Society, 1967.
   DOI: [10.1090/coll/025](https://doi.org/10.1090/coll/025)
   *Used for:* the algebraic foundations of M14 Subtype Lattice and
   the `LatticeTheory` constraint theory.

3. **Davey, B. A. & Priestley, H. A.** *Introduction to Lattices and
   Order.* 2nd ed. Cambridge University Press, 2002.
   DOI: [10.1017/CBO9780511809088](https://doi.org/10.1017/CBO9780511809088)
   *Used for:* the modern textbook treatment of `join`/`meet` lattice
   operations used by the `LatticeTheory` registered as `Lattice`.

4. **D'Antoni, L. & Veanes, M.** "Minimization of Symbolic Automata."
   *Proceedings of POPL*, pp. 541–553. ACM, 2014.
   DOI: [10.1145/2535838.2535849](https://doi.org/10.1145/2535838.2535849)
   *Used for:* the symbolic automaton (SFA) framework that underlies
   M1, parameterized by the effective Boolean algebras supplied by
   `theories { }` registrations.

5. **Droste, M. & Gastin, P.** "Weighted Automata and Weighted
   Logics." *Theoretical Computer Science*, 380:69–86, 2007.
   DOI: [10.1016/j.tcs.2007.02.055](https://doi.org/10.1016/j.tcs.2007.02.055)
   *Used for:* the weighted MSO logic compiled by M10 and walked by
   `walk_mso_formula` for theory-kind classification.

6. **Eilenberg, S.** *Automata, Languages, and Machines, Vol. B.*
   Academic Press, 1976. ISBN 0-12-234001-9.
   *Used for:* the variety theorem that justifies the soundness of
   the bypass model — explicit characterizations replace structural
   inference for finitely characterized varieties.

7. **Feng, B. & Maletti, A.** "Weighted Two-Way Transducers."
   *Proceedings of CAI*. LNCS, Springer, 2022.
   DOI: [10.1007/978-3-031-19685-0_8](https://doi.org/10.1007/978-3-031-19685-0_8)
   *Used for:* the M11 Two-Way Transducer that performs backward
   constraint propagation across explicitly declared channels.

8. **Kempe, A.** "Weighted Multi-Tape Automata and Transducers for
   Natural Language Processing." 2004.
   arXiv: [cs/0406003](https://arxiv.org/abs/cs/0406003)
   *Used for:* the M8 Multi-Tape Automata pair construction that
   fuses N per-channel guards under explicit `channels { }` declarations.

9. **Kiselyov, O., Shan, C., Friedman, D. P. & Sabry, A.**
   "Backtracking, Interleaving, and Terminating Monad Transformers."
   *Proceedings of ICFP*, pp. 192–203. ACM, 2005.
   DOI: [10.1145/1086365.1086390](https://doi.org/10.1145/1086365.1086390)
   *Used for:* the LogicT fair-backtracking monad used to evaluate
   quantified guards at runtime, downstream of the dispatch pipeline.

10. **Martelli, A. & Montanari, U.** "An Efficient Unification
    Algorithm." *ACM Transactions on Programming Languages and
    Systems*, 4(2):258–282, 1982.
    DOI: [10.1145/357162.357169](https://doi.org/10.1145/357162.357169)
    *Used for:* the unification algorithm in `UnificationTheory`
    (M13), which the `theories { … = UnificationTheory; }`
    registration activates.

11. **Meredith, L. G. & Radestock, M.** "A Reflective Higher-Order
    Calculus." *Electronic Notes in Theoretical Computer Science*,
    141(5):49–67, 2005.
    DOI: [10.1016/j.entcs.2005.05.016](https://doi.org/10.1016/j.entcs.2005.05.016)
    *Used for:* the reflective rho-calculus whose Comm rule is
    extended by guarded receive (predicated types) and whose channel
    declarations drive the M8 / M11 dispatch path.

12. **Presburger, M.** "Über die Vollständigkeit eines gewissen
    Systems der Arithmetik ganzer Zahlen, in welchem die Addition
    als einzige Operation hervortritt." *Comptes Rendus du I congrès
    de Mathématiciens des Pays Slaves*, Warsaw, 1929, pp. 92–101.
    English translation: "On the completeness of a certain system
    of arithmetic of whole numbers in which addition occurs as the
    only operation," in *History and Philosophy of Logic*, 12(2):
    225–233, 1991.
    DOI: [10.1080/014453409108837187](https://doi.org/10.1080/014453409108837187)
    *Used for:* the decidability of linear integer arithmetic that
    `PresburgerAlgebra` (M12) implements.

13. **Selinger, P. G., Astrahan, M. M., Chamberlin, D. D., Lorie, R. A.,
    & Price, T. G.** "Access Path Selection in a Relational Database
    Management System." *Proceedings of SIGMOD*, pp. 23–34. ACM, 1979.
    DOI: [10.1145/582095.582099](https://doi.org/10.1145/582095.582099)
    *Used for:* the selectivity-based query-optimization theory that
    motivates the `@[selectivity(s)]` annotations interacting with
    the dispatch signature.

---

*The cleanup turns the heuristic dispatchers from "additive
substitutes for explicit configuration" into "fallback defaults under
explicit configuration." For users with no `guards { }` block, nothing
changes. For users who declared theories or channels, the explicit
declaration is now the sole authority for the affected modules — the
design intent of the `guards { }` block is finally realized in the
pipeline implementation.*
