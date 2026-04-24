# Bounded `sep` Quantifier and Collection-Infix Pratt Rules

**Status:** Exploring
**Date:** 2026-04-21
**Scope:** Extension to the `language!` macro in crates `ast`, `prattail`, `macros`
**Target consumer:** `languages/src/guarded_rho.rs` (and, optionally, future rules with chain-infix semantics)

---

## Abstract

Parallel composition in process calculi such as CCS (Milner 1980), CSP (Hoare 1978), and the reflective higher-order (ρ) calculus (Meredith and Radestock 2005) is a *flat, unordered, associative-commutative* operator: `P | Q | R` denotes three processes running concurrently, not a binary tree. The current GuardedRho grammar captures the flatness by storing children in a `HashBag<Proc>`, but it must bracket the bag in `{` … `}` delimiters because the underlying separated-repetition operator, `xs.*sep("|")`, is nullable and requires a terminating terminal to disambiguate its FIRST/FOLLOW sets. This document proposes two cooperating additions to the `language!` macro that remove the bracket requirement while preserving flat-bag semantics:

1. A regex-style bounded quantifier `xs.*sep(delim, min?, max?)` that generalises the existing 0-or-more operator to any `{m, n}` bound, making non-nullable repetition expressible directly.
2. A **collection-infix** Pratt classification that recognises rules of the shape `[NonTerminal, Sep(…)]` with `min ≥ 1` and emits a specialised left-denotation (LED) handler that accumulates into the declared collection instead of building a right-leaning binary tree.

Together, these additions let GuardedRho's parallel-composition rule be rewritten as

```
PPar . ps:HashBag(Proc) ⊢ ps.*sep("|", 1) : Proc ;
```

— no braces, flat `HashBag`, zero new runtime overhead. The design is backward-compatible: existing callers of `.*sep(delim)` see identical behaviour.

---

## 1. Introduction

### 1.1 Motivating Example

The current GuardedRho parallel-composition rule (`languages/src/guarded_rho.rs:73`) reads:

```
PPar . ps:HashBag(Proc) ⊢ "{" ps.*sep("|") "}" : Proc ;
```

Concrete syntax: `{ P | Q | R }`. AST: `Proc::PPar(HashBag{P, Q, R})`. The braces are semantically redundant — they exist only to make the separated-repetition operator `ps.*sep("|")` unambiguous to the parser. Users writing or reading programs in GuardedRho must surround every parallel composition in curly braces, diverging from the conventional rho-calculus notation (Meredith and Radestock 2005), where `P | Q | R` is written without delimiters.

The goal is to remove the braces while keeping the flat `HashBag` shape.

### 1.2 Problem Statement

A naive removal,

```
PPar . ps:HashBag(Proc) ⊢ ps.*sep("|") : Proc ;
```

produces several macro-time and pipeline-time errors. Section 3 diagnoses the four root causes. In short: the current Sep codegen assumes (i) the repetition is bracketed by a closing delimiter that provides its termination FOLLOW token, (ii) the rule is classified as a prefix rule with a concrete leading FIRST token, and (iii) any `|`-containing rule that flattens must do so through a collection parameter, which cannot be populated by the generic Pratt binary-LED template.

### 1.3 Contributions

1. **§4 — Bounded `sep` quantifier.** A principled extension of the method-chain `.*sep(…)` operator that accepts zero, one, or two additional integer arguments `(min, max)`. This lifts the current 0-or-more restriction and aligns the surface syntax with the established `{m, n}` regex convention (ISO/IEC 14977:1996, §5.5; Wirth 1977).
2. **§5 — Collection-infix Pratt classification.** A new predicate on rule shapes that routes `[NT(self), Sep(self, δ, min ≥ 1)]` rules through a specialised LED generator. The generated LED runs a loop that accumulates into the rule's declared collection, preserving flatness with a standard precedence-guard argument (§5.4).
3. **§6 — Worked GuardedRho rewrite.** A concrete before/after of the parallel-composition rule with a step-by-step parse trace showing the flat AST emerges by construction.

---

## 2. Background and Terminology

### 2.1 Glossary

| Symbol / Term                               | Meaning                                                                                                                                       |
|---------------------------------------------|-----------------------------------------------------------------------------------------------------------------------------------------------|
| **Terminal**                                | An atomic input token matched literally, e.g. `"|"`, `"{"`                                                                                    |
| **Non-terminal (NT)**                       | A grammar category that expands to other rules, e.g. `Proc`                                                                                   |
| **Rule**                                    | A named production: *label . params ⊢ syntax : result_category*                                                                               |
| **FIRST(α)**                                | The set of terminals that can start any string derivable from α (classical definition, e.g. Aho et al. 2006, §4.4)                            |
| **FOLLOW(A)**                               | The set of terminals that can appear immediately after A in some derivation                                                                   |
| **LBP** (left-binding power)                | A numeric priority a Pratt operator uses when competing for an LHS already parsed (Pratt 1973)                                                |
| **RBP** (right-binding power)               | The minimum LBP the operator will accept when parsing its own RHS, controlling associativity (Pratt 1973)                                     |
| **LED** (*led* function, "left denotation") | The Pratt handler invoked when the operator appears with an LHS in hand (Pratt 1973)                                                          |
| **NUD** (*nud*, "null denotation")          | The Pratt handler invoked with no LHS (prefix / literal case) (Pratt 1973)                                                                    |
| **`Sep`**                                   | The `SyntaxItemSpec` variant representing `xs.*sep(δ)` — a separated repetition                                                               |
| **AC**                                      | *Associativity and commutativity*. For `|`: `(P \| Q) \| R = P \| (Q \| R)` and `P \| Q = Q \| P`                                             |
| **Flat AST**                                | A representation where an n-ary operator's children are stored in a single container (list, bag, etc.), not as a nested chain of binary nodes |
| **HashBag**                                 | A multiset (unordered with multiplicity) — the GuardedRho `HashBag<Proc>` provides AC equivalence by construction                             |
| **Nullable**                                | A grammar element that can match the empty string. The current `Sep` is nullable; `.*sep(δ, 1)` is not                                        |

### 2.2 Pratt Parsing in One Paragraph

A Pratt parser (Pratt 1973) iterates: parse a prefix expression via its NUD, then while the next token has a binding power strictly greater than the current precedence threshold, consume it and dispatch its LED with the already-parsed expression as the LHS. The LED typically recurses with a higher threshold to grab its RHS. The asymmetry between LBP and RBP controls associativity: `LBP == RBP` yields right-associativity; `RBP > LBP` yields left-associativity (commonly implemented as `RBP = LBP + 1`).

### 2.3 Parallel Composition in Process Algebra

In CCS (Milner 1980, §2), the parallel composition operator `|` is associative and commutative, and the canonical semantics treat `P | Q | R` as a multiset of three concurrently executing processes. CSP (Hoare 1978) and the ρ-calculus (Meredith and Radestock 2005, §2.1) follow the same convention: `|` is not a binary operator with a privileged left child, but rather a notational flattening of multi-way parallel composition. GuardedRho inherits this convention — hence the `HashBag<Proc>` representation.

### 2.4 The `language!` Macro — Relevant Mechanics

Users declare a language as a set of rules. Each rule has a **label**, a set of **parameter bindings** (name:category, including collection declarations such as `ps:HashBag(Proc)` or `xs:Vec(Name)`), a **syntax pattern**, and a **result category**. The syntax pattern is a list of `SyntaxItemSpec` items; relevant variants are:

```rust
enum SyntaxItemSpec {
    Terminal(String),
    NonTerminal   { category: String, param_name: String },
    Sep           { body: Box<SyntaxItemSpec>, separator: String, kind: CollectionKind },
    Map           { body_items: Vec<SyntaxItemSpec> },
    Zip           { left_name, right_name, left_category, right_category, body: Box<SyntaxItemSpec> },
    Optional      { inner: Box<SyntaxItemSpec> },
    // … (eleven total)
}
```

The `Sep` variant is the target of this proposal. Existing codegen lives in:

- `ast/src/grammar.rs` — DSL AST (`PatternOp`)
- `macros/src/gen/syntax/parser/prattail_bridge.rs` — DSL → `SyntaxItemSpec` lowering
- `prattail/src/recursive.rs` — Generates the recursive-descent Sep loop
- `prattail/src/prediction.rs` — Computes FIRST/FOLLOW
- `prattail/src/classify.rs` — Routes rules to prefix / infix / collection paths

### 2.5 The Sep/Map/Zip Decomposition

The existing `.*sep`, `.*map`, and `.*zip` chain operators (documented in `docs/manual/language/features/ZipMapSep/`) decompose a repeated pattern into three orthogonal dimensions: iteration boundary (Sep), element template (Map), and multi-accumulator lockstep (Zip). The proposal here adds **quantification bounds** to Sep — orthogonal to the other two dimensions — and a **classification change** that promotes a restricted shape of Sep-using rule to an infix role.

---

## 3. The Brace-Requirement Problem

Four issues arise when `"{" ps.*sep("|") "}"` is changed to just `ps.*sep("|")`:

### 3.1 FIRST/FOLLOW Relies on a Closing Delimiter

`prattail/src/prediction.rs:407–419` computes FOLLOW propagation for `Sep { body, separator, .. }` by unioning `{separator}` with `FIRST(suffix)`, where `suffix` is everything after the `Sep` in the syntax list. In the braced form, `suffix` starts with the terminal `"}"`, so the loop's decision function — "continue if the next token is either the separator or an element's FIRST" — has a concrete termination witness `"}"`. Dropping the closing delimiter makes `suffix` empty. The loop then cannot distinguish "next iteration starts here" from "we've fallen off the end of `PPar` and are now in the FOLLOW of whatever surrounds `PPar`."

A test at `prattail/src/tests/prediction_tests.rs:620–622` explicitly locks in this assumption:

> *FOLLOW(Proc) should contain RParen (closing delimiter after Sep).*

### 3.2 Generated Termination Peek Needs a Non-Separator Follow Token

`prattail/src/recursive.rs:453–456` emits approximately:

```rust
while peek_token(tokens, *pos)
        .map(|t| matches!(t, Token::<separator>))
        .unwrap_or(false) {
    *pos += 1;
    let elem = parse_<body_category>(tokens, pos, 0)?;
    ps.insert(elem);
}
```

The loop relies on the *next* token not being the separator as a signal to exit. Without a closing delimiter, a valid ambient token (any token in FOLLOW(Proc)) must be structurally disjoint from the separator. For `|` this can be ensured by Pratt precedence — if no other rule uses `|`, then `|` appearing after the final element means another `PPar` iteration, and its absence means the surrounding rule's FOLLOW. The current codegen does not use Pratt dispatch for this decision, however; it only peeks for exact token-kind equality.

### 3.3 Classification Rejects `Sep`-Leading Rules as Prefix

`prattail/src/classify.rs:116–131`'s `classify_is_infix` requires the syntax to be `[NT(same_cat), Terminal, …]`. A rule whose *second* item is a `Sep` (not a `Terminal`) is therefore neither infix-eligible nor, with its empty deterministic FIRST set, usefully prefix-eligible. It falls through to the trampoline prefix path, which dispatches on the first concrete terminal — there is none, so the rule never fires.

### 3.4 The RhoCalc `bitor` Workaround Confirms the Issue Is Real

The closely related RhoCalc grammar (`languages/src/rhocalc.rs:168–169`) avoids `|` entirely and uses a `bitor` keyword for bitwise-or instead. That workaround exists precisely to sidestep the interaction between `|` and the brace-bracketed `PPar` production in sibling grammars. This is indirect evidence that the braces-requirement is an architectural pain point, not a cosmetic choice.

---

## 4. Design, Part I — Bounded `sep` Quantifier

### 4.1 Syntax

```
xs.*sep(δ)              — 0 or more elements, separator δ
xs.*sep(δ, m)           — at least m elements
xs.*sep(δ, m, n)        — at least m, at most n elements
```

where `δ` is a string literal naming a terminal and `m, n ∈ ℕ`.

| Surface form | Bounds (elements) |
|---|---|
| `xs.*sep("\|")` | [0, ∞) — unchanged from current |
| `xs.*sep("\|", 1)` | [1, ∞) |
| `xs.*sep("\|", 3)` | [3, ∞) |
| `xs.*sep("\|", 0, 5)` | [0, 5] |
| `xs.*sep("\|", 2, 5)` | [2, 5] |
| `xs.*sep("\|", 3, 3)` | {3} (exactly three) |

Semantics: the bounds count **elements**, not separators — matching the regex `{m, n}` convention (Wirth 1977, §2). An input with `k` separators has `k + 1` elements; a lower bound `m = 1` means "at least one element," which is equivalent to `k ≥ 0` separators.

### 4.2 Formal Semantics

Let Γ be an input token stream and ⟦·⟧ the parse relation. Write `ε` for the empty string, `s · t` for string `s` followed by `t`, and `e` for a syntactically valid element of the Sep's body category.

The existing operator satisfies

```
  ⟦ xs.*sep(δ) ⟧(Γ) = (ε, Γ)  ∨  (e · (δ · e)*, Γ')
```

(empty or a non-empty δ-separated list), read as an inductive definition where `(δ · e)*` is zero or more repetitions of the suffix.

The bounded form generalises to

```
  ⟦ xs.*sep(δ, m, n) ⟧(Γ) = (e · (δ · e)ᵏ, Γ')     where m − 1 ≤ k ≤ n − 1   (and k ≥ 0)
```

with the convention `n = ∞` when `max` is omitted. `m = 0` collapses to the original.

### 4.3 Relationship to Regex `{m, n}`

The bounded form mirrors, element for element, the bounded-repetition syntax of Extended BNF (Wirth 1977, §3; ISO/IEC 14977:1996, §5.6) and the `{m, n}` quantifier of POSIX regular expressions (IEEE Std 1003.1-2017, §9.3.6). The choice is motivated by familiarity — any grammar author who has written an EBNF production or a regex will read `sep(δ, 1)` correctly on first encounter.

### 4.4 Backward Compatibility

Existing callsites write `xs.*sep(δ)` with one argument. The new signature defaults `min = 0, max = None`, producing byte-identical codegen for the one-argument case. No grammar file in the project needs to change unless its author chooses to.

### 4.5 Error Diagnostics

Two validation points at macro-expansion time:

1. **Bound ordering:** `min > max` is rejected with a span-aware diagnostic:

   ```
   error: bounded sep has min > max
     ──> grammar.rs:42:17
      │
   42 │   ps.*sep("|", 5, 3)
      │                ^  ^── max is 3
      │                │
      │                min is 5
      = note: bounds count elements, not separators; regex {m,n} requires m ≤ n
   ```

2. **Collection capacity:** when the collection type's statically known maximum (if any) is smaller than `max`, emit a warning.

Runtime diagnostics from the generated parser:

- Too few elements: *"expected at least `m` elements in `<rule_label>`, found `k`"* — raised when EOF or a non-separator token is reached with `k < m` accumulated.
- Too many elements: *"expected at most `n` elements in `<rule_label>`, found `n + 1`"* — raised when the `(n + 1)`-th separator is consumed.

---

## 5. Design, Part II — Collection-Infix Pratt Classification

### 5.1 Motivation

Part I makes `ps.*sep("|", 1)` a valid, non-nullable repetition pattern. But the Pratt dispatcher still refuses to run a rule whose syntax is `[NT(Proc), Sep(…)]` (see §3.3). Worse, even if classification were relaxed, the default binary-LED template would build a *right-leaning binary tree*:

```
        PPar
       ╱    ╲
      P     PPar
           ╱    ╲
          Q    PPar
              ╱    ╲
             R     ⟨∅⟩
```

destroying the flat `HashBag` semantics. Part II introduces a specialised LED that preserves flatness by construction.

### 5.2 Classification Predicate

Add to `prattail/src/classify.rs`:

```rust
fn classify_is_collection_infix(rule: &Rule) -> bool {
    use SyntaxItemSpec::*;
    match rule.syntax.as_slice() {
        [ NonTerminal { category: c1, .. },
          Sep { body: box NonTerminal { category: c2, .. },
                separator: _,
                min,
                .. } ]
            if c1 == c2
            && *c1 == rule.result_category
            && *min >= 1
        => true,
        _ => false,
    }
}
```

The `min ≥ 1` requirement is load-bearing. A nullable collection-infix would admit a "zero-extra-element" match after the Pratt loop has already handed the LED an LHS, yielding `PPar(bag{lhs})` — a single-element parallel composition that is both semantically confusing and syntactically redundant with bare `lhs`.

### 5.3 LED Codegen

For a rule classified as collection-infix, emit:

```rust
fn led_ppar(
    lhs: Proc,
    tokens: &[Token], pos: &mut usize,
    _min_bp: u8,
) -> Result<Proc, ParseError> {
    let mut bag = HashBag::new();
    bag.insert(lhs);

    loop {
        match peek(tokens, *pos) {
            Some(Token::Pipe) => { *pos += 1; }
            _                 => break,
        }
        let elem = parse_Proc(tokens, pos, SELF_BP + 1)?;  // ← see §5.4
        bag.insert(elem);
    }

    Ok(Proc::PPar(bag))
}
```

This is the same accumulator-loop shape as the generic `Sep(NonTerminal)` codegen in `prattail/src/recursive.rs:446–464`, adapted to run *after* the Pratt dispatcher has provided the first element.

When `max` is `Some(n)`, the loop counts iterations and breaks at `bag.len() == n` (not `n + 1`: `lhs` is already counted). A further separator after the limit triggers the runtime "too many elements" diagnostic (§4.5).

### 5.4 Flatness Invariant (Proof Sketch)

**Claim.** Parsing `P₁ | P₂ | P₃ | … | Pₖ` under a collection-infix `PPar` rule with self-BP `b` yields exactly one `Proc::PPar(HashBag{P₁, …, Pₖ})` node, with no nested `PPar`.

**Proof sketch.** The Pratt outer loop parses `P₁` via its prefix (NUD) path, enters the loop, observes `|` with LBP `b`, and dispatches `led_ppar(P₁, …)`. The LED's loop calls `parse_Proc(tokens, pos, b + 1)` — note the `+1` precedence guard — which:

1. Parses the next prefix (i.e. `P₂`).
2. Enters its own Pratt loop with threshold `b + 1`.
3. Observes `|` with LBP `b`, notes that `b < b + 1`, and exits the loop.

The outer `led_ppar` therefore receives `P₂` as a *bare* `Proc`, not another `PPar`, and appends it to `bag`. By induction on `k`, each `Pᵢ` (`i ≥ 2`) is appended as a bare `Proc`. No recursive call into `led_ppar` ever occurs during the parse of a single `PPar` chain, so no nested `PPar` node is constructed. ∎

The precedence guard `SELF_BP + 1` is conventionally associated with left-associativity in standard Pratt (Pratt 1973). Here it serves a dual purpose: *flatness*.

### 5.5 Binding Power Assignment

`prattail/src/binding_power.rs` / `pipeline.rs:1154–1184` already assigns BP tiers to infix rules by user-declared precedence group. Collection-infix rules enter the same scheme. For GuardedRho's `PPar` we assign the loosest infix tier (below `and`, `or`, arithmetic, etc.), matching conventional process-calculus notation where `|` binds weakest.

---

## 6. Worked Example — GuardedRho Parallel Composition

### 6.1 Before and After

**Before (`languages/src/guarded_rho.rs:73`):**

```
PPar . ps:HashBag(Proc) ⊢ "{" ps.*sep("|") "}" : Proc ;
```

**After:**

```
PPar . ps:HashBag(Proc) ⊢ ps.*sep("|", 1) : Proc ;
```

Neither the `HashBag<Proc>` storage nor the `equations { }` block (AC is inherent in `HashBag`) changes.

### 6.2 Parse Trace for `P | Q | R`

Assume `P`, `Q`, `R` are parsed by some other `Proc` production (say, name-drops `*p`, `*q`, `*r`). The trace elides their internals.

```
 pos │ token stream            │ Pratt state         │ action
─────┼─────────────────────────┼─────────────────────┼──────────────────────────────
  0  │ P │ Q │ R ·             │ outer, threshold 0  │ NUD → P, state = parsed(P)
  1  │ | Q │ R ·               │ peek(|), LBP=b>0    │ dispatch led_ppar(P, …)
 ↳   │                         │ bag = {P}           │
  1  │ | Q | R ·               │ led loop peek(|)    │ consume |, pos=2
  2  │ Q | R ·                 │ parse_Proc(b+1)     │ NUD → Q
  3  │ | R ·                   │  inner Pratt: LBP=b │ b < b+1 → exit inner loop
 ↳   │                         │ bag = {P, Q}        │ append Q
  3  │ | R ·                   │ led loop peek(|)    │ consume |, pos=4
  4  │ R ·                     │ parse_Proc(b+1)     │ NUD → R
  5  │ ·                       │  inner Pratt: EOF   │ exit inner loop
 ↳   │                         │ bag = {P, Q, R}     │ append R
  5  │ ·                       │ led loop peek(EOF)  │ not |, exit led loop
 ↳   │                         │ return PPar({P,Q,R})│ flat, three-element bag
```

### 6.3 AST Shape Comparison

Before the precedence guard + collection-infix treatment (generic binary LED, hypothetical):

```
        PPar
       ╱    ╲
      P    PPar                    ← right-leaning binary tree
          ╱    ╲                     (would be produced without §5.4)
         Q    PPar
            ╱    ╲
           R    ⟨∅⟩
```

After, with the design of §5:

```
         PPar
        ╱ │ ╲
       P  Q  R                     ← flat bag, single PPar node
      ┕━━━━━━━┙
       HashBag
```

---

## 7. Interactions and Edge Cases

### 7.1 `min = 0`, `max = Some(n)` — Nullable but Bounded

This case is handled by the existing recursive-descent codegen (not the collection-infix path, which requires `min ≥ 1`). The generated loop body adds a counter `k` and exits when `k == n`. If an additional separator appears, the runtime error in §4.5 fires.

### 7.2 `min > max` — Compile-Time Rejection

Parsed by `parse_sep_op` at `ast/src/grammar.rs:874–879`; the check is one comparison and one diagnostic emission, giving the error in §4.5.

### 7.3 Separator Sharing Across Rules

If two infix rules (collection-infix or conventional) share a separator token, the Pratt dispatcher cannot deterministically pick one. This is not a new concern — it applies to any two infix rules — but because collection-infix rules tend to use "loose" separator tokens like `|`, the risk is higher. `prattail/src/lint.rs` gains a diagnostic that fires when more than one rule declares the same operator token at the same BP tier, suggesting distinct tokens or distinct tiers.

### 7.4 Trampoline Integration

`prattail/src/trampoline.rs:164–168` routes any rule containing `Sep` through a standalone parse function. Collection-infix rules bypass this — their body is inlined into the Pratt LED. The routing predicate becomes `has_sep(rule) && !is_collection_infix(rule)`.

### 7.5 Interaction with `guards { }` and Behavioural Predicates

GuardedRho uses `guards { channels { channel Name; join PGuardedInput(ch: Name); } }`. Guard emission runs over AST shapes, not grammar productions, and treats the children of a `PPar` as an unordered multiset regardless of surface syntax. The proposal is therefore transparent to the guard machinery.

---

## 8. Implementation Notes

### 8.1 File-Level Changes

| File                                                      | Change                                                              | LoC |
|-----------------------------------------------------------|---------------------------------------------------------------------|-----|
| `ast/src/grammar.rs:168–195`                              | Add `min: usize`, `max: Option<usize>` to `PatternOp::Sep`          | +12 |
| `ast/src/grammar.rs:781–879`                              | `parse_pattern_op*` / `parse_sep_op` accept 1–3 args after the coll | +40 |
| `ast/src/grammar.rs`                                      | Validate `min ≤ max` at parse time                                  | +8  |
| `prattail/src/lib.rs:770–796`                             | Add `min`, `max` to `SyntaxItemSpec::Sep`                           | +4  |
| `prattail/src/recursive.rs:40–99`                         | Add `min`, `max` to `RDSyntaxItem::Sep`                             | +4  |
| `prattail/src/recursive.rs:418–523`                       | Mandatory-prefix codegen for `min > 0`; counter codegen for `max`   | +80 |
| `prattail/src/classify.rs`                                | `classify_is_collection_infix`; OR into infix predicate             | +40 |
| `prattail/src/pratt.rs`                                   | Specialised accumulator-loop LED for collection-infix rules         | +85 |
| `prattail/src/binding_power.rs` / `pipeline.rs:1154–1184` | BP slot assignment                                                  | +15 |
| `prattail/src/prediction.rs`                              | Nullability = `min == 0`; block FOLLOW propagation when `min ≥ 1`   | +12 |
| `prattail/src/trampoline.rs:164–168`                      | Skip standalone-fn emission for collection-infix rules              | +5  |
| `macros/src/gen/syntax/parser/prattail_bridge.rs:691–845` | Plumb `min`, `max` through Sep conversion                           | +10 |
| `prattail/src/lint.rs`                                    | Warn on shared infix separators                                     | +20 |
| `languages/src/guarded_rho.rs:73`                         | Drop braces, switch to `sep("\|", 1)`                               | 1   |
| `languages/tests/gen_guardedrho_*.rs` + snapshots         | Update parse inputs                                                 | ~20 |

**Net:** ≈ 356 LoC across 14 files.

### 8.2 Staged Rollout

1. **Stage 1:** Part I (bounded `sep`) lands with `min ≥ 1` exercising only the standard recursive-descent path (no collection-infix yet). Verifiable via new unit tests.
2. **Stage 2:** Classification predicate + LED codegen. Gated off by default; `languages/src/guarded_rho.rs` stays on the braced form.
3. **Stage 3:** Flip GuardedRho to the bracket-free form. Verify property tests still pass.
4. **Stage 4:** Lint for shared infix separators. Emit as warnings initially; promote to deny-by-default after one release cycle.

---

## 9. Verification

### 9.1 Unit Tests — `prattail/src/tests/sep_bounded_tests.rs`

- `.*sep(δ, 1)` rejects empty input with a diagnostic naming the rule and "at least 1"
- `.*sep(δ, 2)` rejects single-element input
- `.*sep(δ, 0, 3)` accepts 0..=3 elements, rejects 4
- `.*sep(δ, 2, 2)` requires exactly 2 elements
- `parse("P | Q | R")` with `sep(δ, 1)` → one `PPar(bag{P, Q, R})`, no nested `PPar`
- `parse("P | Q + R")` respects precedence: `PPar(bag{P, (Q + R)})`
- Parse-time rejection of `sep(δ, 5, 3)` (min > max)
- Backward compat: `sep(δ)` behaves identically to the pre-change implementation

### 9.2 Property Tests — `languages/tests/gen_guardedrho_prop.rs`

Roundtrip (`parse(display(t)) == t`) must hold after updating the display implementation to emit `P | Q | R` without braces. The `HashBag` multiset comparison is unchanged, so AC equivalence is still automatic.

### 9.3 Snapshot — `cargo expand`

`cargo expand -p mettail-languages guarded_rho` must show the generated `parse_Proc` has a `Token::Pipe` arm in its infix match that calls an accumulator loop. Specifically, the generated body must contain **zero** recursive calls to any `parse_ppar` or `PPar` constructor from inside the LED — the only constructor invocation is the final `Proc::PPar(bag)`.

### 9.4 Benchmarks — `prattail/benches/bench_specs/`

Add a 1000-way parallel composition `P₁ | P₂ | … | P₁₀₀₀`. Expected:

- Time: O(n) — the LED loop is iterative.
- Stack depth: O(1) — no recursion through `|`.

A regression to O(n) stack usage (via accidental re-entry of `led_ppar`) would indicate a flatness-invariant break and should fail the benchmark's CI gate.

### 9.5 Analytical Tests

`languages/tests/gen_guardedrho_analytical.rs` verifies AC equations. All assertions must continue to pass: the `HashBag` type and semantics are unchanged; only the surface syntax shifts.

### 9.6 Full Regression

```
cargo test --workspace
cargo test --workspace --all-features
```

---

## 10. Related Work

**Pratt (1973).** *Top Down Operator Precedence* introduces the LED/NUD dispatch model reused here. The precedence-guard technique for left-associativity (§5.4) is attributed to the same paper. doi:[10.1145/512927.512931](https://doi.org/10.1145/512927.512931)

**Wirth (1977); ISO/IEC 14977 (1996).** *What Can We Do about the Unnecessary Diversity of Notation for Syntactic Definitions?* and ISO Extended BNF standardise the `{m, n}` bounded-repetition operator whose surface form this proposal adopts. doi:[10.1145/359863.359883](https://doi.org/10.1145/359863.359883)

**Hoare (1978).** *Communicating Sequential Processes* establishes the `|` parallel operator with AC equivalence as a flat multiset of processes. doi:[10.1145/359576.359585](https://doi.org/10.1145/359576.359585)

**Milner (1980).** *A Calculus of Communicating Systems*. Canonical reference for AC parallel composition; ρ-calculus and GuardedRho descend from this lineage. doi:[10.1007/3-540-10235-3](https://doi.org/10.1007/3-540-10235-3)

**Hutton (1992).** *Higher-Order Functions for Parsing*. Introduces `sepBy` and `chainl1` / `chainr1` parser combinators — direct conceptual ancestors of the collection-infix LED. `chainl1` in particular produces a left-leaning binary tree; our proposal is the *flat* analogue. doi:[10.1017/S0956796800000411](https://doi.org/10.1017/S0956796800000411)

**Meredith and Radestock (2005).** *A Reflective Higher-order Calculus*. The ρ-calculus whose GuardedRho is a guarded variant. The paper's semantics of `P | Q` match the flat-multiset convention preserved by the proposal. doi:[10.1016/j.entcs.2005.05.016](https://doi.org/10.1016/j.entcs.2005.05.016)

---

## 11. Summary and Future Extensions

The proposal removes the brace requirement from GuardedRho's parallel-composition production by (a) generalising `.*sep` to a bounded quantifier and (b) teaching the Pratt classifier a new infix shape that preserves flat collection semantics. Both additions are backward-compatible and sum to ≈ 356 LoC across 14 files.

Foreseeable future extensions:

- **Right-associative collection-infix.** Symmetric to the left-associative case, useful for operators like `::` (list cons) that prefer right-leaning flat lists. Requires a mirrored precedence guard `SELF_BP` (not `SELF_BP + 1`).
- **Anonymous `(…)*` groups.** Supporting literal `expr ("|" expr)*` as a free-standing grammar operator (not tied to a named collection) would require inventing auto-synthesised bindings. The bounded-sep + collection-infix design covers the same semantic ground without this complication and is therefore preferred for the present proposal. Anonymous groups remain a candidate for a follow-up design if repeated demand emerges.
- **Variable separators.** The current `Sep` accepts only a single terminal as separator. A future extension could accept a disjunction (e.g. `sep({",", ";"}, 1)`) or a sub-pattern (e.g. for permitting optional whitespace runs). Out of scope here.

---

## 12. References

1. Pratt, V. R. (1973). "Top Down Operator Precedence." *Proceedings of the 1st Annual ACM SIGACT-SIGPLAN Symposium on Principles of Programming Languages (POPL '73)*, 41–51. doi:[10.1145/512927.512931](https://doi.org/10.1145/512927.512931)
2. Wirth, N. (1977). "What Can We Do about the Unnecessary Diversity of Notation for Syntactic Definitions?" *Communications of the ACM*, 20(11), 822–823. doi:[10.1145/359863.359883](https://doi.org/10.1145/359863.359883)
3. Hoare, C. A. R. (1978). "Communicating Sequential Processes." *Communications of the ACM*, 21(8), 666–677. doi:[10.1145/359576.359585](https://doi.org/10.1145/359576.359585)
4. Milner, R. (1980). *A Calculus of Communicating Systems*. Lecture Notes in Computer Science, vol. 92. Springer. doi:[10.1007/3-540-10235-3](https://doi.org/10.1007/3-540-10235-3)
5. Hutton, G. (1992). "Higher-Order Functions for Parsing." *Journal of Functional Programming*, 2(3), 323–343. doi:[10.1017/S0956796800000411](https://doi.org/10.1017/S0956796800000411)
6. ISO/IEC. (1996). *ISO/IEC 14977:1996 — Information technology — Syntactic metalanguage — Extended BNF*. International Organization for Standardization.
7. Meredith, L. G., & Radestock, M. (2005). "A Reflective Higher-order Calculus." *Electronic Notes in Theoretical Computer Science*, 141(5), 49–67. doi:[10.1016/j.entcs.2005.05.016](https://doi.org/10.1016/j.entcs.2005.05.016)
