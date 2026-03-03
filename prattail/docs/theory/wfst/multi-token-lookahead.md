# Multi-Token Lookahead via Extended PredictionWfst

> **Date:** 2026-03-01

Formalizes the extension of PraTTaIL's single-token prediction WFST to
k-token lookahead dispatch. The primary instantiation is 2-token
lookahead (B1), which resolves pairwise-distinguishable ambiguities by
inspecting `items[1]` — the second syntax item — when it is a terminal
distinct across all rules sharing a dispatch token. This replaces the
O(n) NFA try-all strategy with an O(1) nested pattern match for
qualifying rule groups.

---

## Table of Contents

1. [Problem: Ambiguity Beyond the Dispatch Token](#1-problem-ambiguity-beyond-the-dispatch-token)
2. [Formal Model: k-Token Prediction](#2-formal-model-k-token-prediction)
   - 2.1 [Definitions and Notation](#21-definitions-and-notation)
   - 2.2 [2-Token PredictionWfst](#22-2-token-predictionwfst)
   - 2.3 [Applicability Predicate](#23-applicability-predicate)
3. [Correctness: 2-Token Disambiguation](#3-correctness-2-token-disambiguation)
   - 3.1 [Pairwise Distinguishability](#31-pairwise-distinguishability)
   - 3.2 [Disambiguation Theorem](#32-disambiguation-theorem)
   - 3.3 [Exhaustiveness and Determinism](#33-exhaustiveness-and-determinism)
4. [Relationship to LL(k) Theory](#4-relationship-to-llk-theory)
   - 4.1 [LL(k) Lookahead Sets](#41-llk-lookahead-sets)
   - 4.2 [B1 as LL(2) Dispatch](#42-b1-as-ll2-dispatch)
   - 4.3 [Differences from Classical LL(k)](#43-differences-from-classical-llk)
5. [Pseudocode](#5-pseudocode)
   - 5.1 [Analysis Phase](#51-analysis-phase)
   - 5.2 [Code Generation Phase](#52-code-generation-phase)
6. [Diagram: B1 Decision Structure](#6-diagram-b1-decision-structure)
7. [Worked Example](#7-worked-example)
   - 7.1 [Grammar Rules](#71-grammar-rules)
   - 7.2 [Analysis Trace](#72-analysis-trace)
   - 7.3 [Generated Code Structure](#73-generated-code-structure)
   - 7.4 [Runtime Execution](#74-runtime-execution)
8. [Complexity Analysis](#8-complexity-analysis)
   - 8.1 [Compile-Time Analysis](#81-compile-time-analysis)
   - 8.2 [Runtime Dispatch](#82-runtime-dispatch)
   - 8.3 [Comparison with NFA Try-All](#83-comparison-with-nfa-try-all)
9. [Non-Applicability: When B1 Does Not Apply](#9-non-applicability-when-b1-does-not-apply)
   - 9.1 [Non-Terminal Second Items](#91-non-terminal-second-items)
   - 9.2 [Shared Second Terminals](#92-shared-second-terminals)
   - 9.3 [Short Rules](#93-short-rules)
   - 9.4 [NFA Spillover Categories](#94-nfa-spillover-categories)
   - 9.5 [Frame-Pushing Rules](#95-frame-pushing-rules)
   - 9.6 [Fallback: NFA Try-All](#96-fallback-nfa-try-all)
10. [Source References](#10-source-references)

---

## 1. Problem: Ambiguity Beyond the Dispatch Token

PraTTaIL's Pratt parser dispatches on the **first terminal** of each
rule's syntax — the dispatch token. When multiple prefix rules within
the same category share the same dispatch token, the parser faces a
prefix ambiguity: it cannot determine which rule to apply from the first
token alone.

### 1.1 Example: Keyword-Prefixed Rules

Consider a category with three rules sharing the dispatch token `kw`:

```
Rule A:  kw "(" a:Expr ")"       → KwGroup(a)
Rule B:  kw "[" a:Expr "]"       → KwIndex(a)
Rule C:  kw "{" a:Expr "}"       → KwBlock(a)
```

After matching `kw`, the parser still has 3 candidates. Without
additional analysis, it must try all three using the NFA try-all
strategy: save position, attempt each parse, restore on failure, and
select the first success.

### 1.2 Observation

The **second** syntax item in each rule is a distinct terminal: `"("`,
`"["`, and `"{"`. A single additional token peek resolves the ambiguity
completely — no save/restore, no backtracking, no NFA machinery.

### 1.3 Goal

B1 (multi-token lookahead) formalizes this observation. At compile time,
it analyzes rule groups sharing a dispatch token and determines whether
all rules have distinct second terminals. When they do, it replaces the
NFA try-all with a nested `match` on the second token — achieving O(1)
disambiguation.

---

## 2. Formal Model: k-Token Prediction

### 2.1 Definitions and Notation

Let **G** = (C, R, T, N) be a PraTTaIL grammar where:

| Symbol | Type | Description |
|:------:|:----:|:------------|
| C      | set  | Categories (nonterminals at the top level) |
| R      | set  | Rules, partitioned by category |
| T      | set  | Terminal tokens |
| N      | set  | Nonterminal references (cross-category or same-category) |

Each rule r ∈ R has a **syntax sequence** s(r) = [s₀, s₁, ..., sₘ₋₁]
where each sᵢ is either a terminal (sᵢ ∈ T) or a nonterminal reference
(sᵢ ∈ N).

**Dispatch token**: For a prefix rule r, the dispatch token is d(r) = s₀(r).

**Dispatch group**: For a category c ∈ C and terminal t ∈ T, the dispatch
group is:

```
D(c, t) = { r ∈ R(c) : d(r) = t }
```

where R(c) denotes all prefix rules in category c.

A dispatch group is **ambiguous** when |D(c, t)| > 1.

### 2.2 2-Token PredictionWfst

The standard PredictionWfst is a 2-state machine: one start state, one
final state per action, with a single transition consuming the dispatch
token. Extending to 2-token prediction adds a middle layer:

**Definition.** A *2-token PredictionWfst* for an ambiguous dispatch
group D(c, t) with |D(c, t)| = n is a 3-level WFST:

```
M₂ = (Σ, Q, q₀, F, δ)
```

where:

| Component | Value |
|:---------:|:------|
| Σ         | T ∪ {ε} — the terminal alphabet |
| Q         | {q₀} ∪ {q_mid} ∪ {f₁, f₂, ..., fₙ} — start, middle, n final states |
| q₀        | Start state |
| q_mid     | Intermediate state after consuming the shared dispatch token t |
| F         | {f₁, ..., fₙ} — one final state per rule |
| δ         | δ(q₀, t) = q_mid;  δ(q_mid, s₁(rᵢ)) = fᵢ for each rᵢ ∈ D(c, t) |

The first transition consumes the shared dispatch token t; the second
transition consumes the (distinct) second terminal of each rule. Each
final state fᵢ maps to rule rᵢ's parse action.

### 2.3 Applicability Predicate

The 2-token lookahead is applicable to a dispatch group D(c, t) when
the following predicate holds:

```
B1_APPLICABLE(D(c, t)) ⟺
    |D(c, t)| ≥ 2
  ∧ ∀ r ∈ D(c, t) : |s(r)| ≥ 2
  ∧ ∀ r ∈ D(c, t) : s₁(r) ∈ T
  ∧ ∀ rᵢ, rⱼ ∈ D(c, t), i ≠ j : s₁(rᵢ) ≠ s₁(rⱼ)
```

In prose:

1. The group has at least 2 rules (otherwise no ambiguity).
2. Every rule has at least 2 syntax items (otherwise no second item to inspect).
3. Every rule's second item is a terminal (not a nonterminal, ident capture, or binder).
4. All second terminals are pairwise distinct.

---

## 3. Correctness: 2-Token Disambiguation

### 3.1 Pairwise Distinguishability

**Definition.** Two rules rᵢ, rⱼ ∈ D(c, t) are *pairwise distinguishable
at depth 2* if s₁(rᵢ) ≠ s₁(rⱼ) and both s₁(rᵢ), s₁(rⱼ) ∈ T.

**Definition.** A dispatch group D(c, t) is *fully distinguishable at
depth 2* if every pair of rules in the group is pairwise distinguishable
at depth 2 — equivalently, if B1_APPLICABLE(D(c, t)) holds.

### 3.2 Disambiguation Theorem

**Theorem (B1 Soundness).** Let D(c, t) be a dispatch group satisfying
B1_APPLICABLE(D(c, t)). Given an input token sequence where the token
at position *pos* is t and the token at position *pos* + 1 is u ∈ T,
the 2-token dispatch selects at most one rule, and that rule is the
unique r ∈ D(c, t) with s₁(r) = u (if such a rule exists).

**Proof.**

Let n = |D(c, t)| and let D(c, t) = {r₁, r₂, ..., rₙ}.

**(i) Uniqueness.** By the fourth conjunct of B1_APPLICABLE, the
function φ: D(c, t) → T defined by φ(rᵢ) = s₁(rᵢ) is injective.
Therefore, for any u ∈ T, |φ⁻¹(u)| ≤ 1. The nested match on the
second token u selects rᵢ only when φ(rᵢ) = u, so at most one rule
is selected.

**(ii) Soundness.** Suppose the correct parse of the input beginning at
position *pos* is rule rᵢ. Then the input at position *pos* is
s₀(rᵢ) = t (matched by the dispatch) and the input at position
*pos* + 1 is s₁(rᵢ) = u. The 2-token dispatch inspects the token at
position *pos* + 1, finds u, and selects rᵢ via φ⁻¹(u) = {rᵢ}.
Therefore, the selected rule matches the correct parse.

**(iii) Completeness.** If no rule r ∈ D(c, t) has s₁(r) = u, then u
does not appear as a second terminal in any rule of the group. The
nested match falls through to the wildcard `_` arm, which produces a
parse error. This is correct: no rule in the group can parse the input,
so the input is syntactically invalid with respect to this group.  ∎

### 3.3 Exhaustiveness and Determinism

**Corollary (Deterministic Dispatch).** Under B1, the dispatch for an
ambiguous group is deterministic: no backtracking, no save/restore, no
NFA machinery. The parser consumes two tokens in a fixed sequence and
selects exactly one rule (or reports an error).

**Proof.** Follows directly from parts (i) and (iii) of the
Disambiguation Theorem. The dispatch is a function from the second
token to {rule} ∪ {error}, which is deterministic by construction.  ∎

---

## 4. Relationship to LL(k) Theory

### 4.1 LL(k) Lookahead Sets

In classical LL(k) parsing theory, a grammar is **LL(k)** if, for every
pair of distinct productions A → α | β for the same nonterminal A, the
k-token lookahead sets are disjoint:

```
FIRST_k(α FOLLOW_k(A)) ∩ FIRST_k(β FOLLOW_k(A)) = ∅
```

where FIRST_k(γ) denotes the set of terminal strings of length at most k
that can begin strings derived from γ.

For k = 1, this is the standard LL(1) condition: the first tokens of
alternative productions are disjoint. When the condition fails for k = 1
but holds for k = 2, the grammar is LL(2) — the first two tokens
suffice to select the correct production.

### 4.2 B1 as LL(2) Dispatch

B1 is the LL(2) condition restricted to **dispatch groups** within a
Pratt parsing framework:

**Standard LL(2):**

```
FIRST_2(α) ∩ FIRST_2(β) = ∅
```

**B1 condition:**

```
{s₀(rᵢ)} · {s₁(rᵢ)} ∩ {s₀(rⱼ)} · {s₁(rⱼ)} = ∅    for all i ≠ j
```

Since all rules in D(c, t) share s₀ = t, this simplifies to:

```
{s₁(rᵢ)} ∩ {s₁(rⱼ)} = ∅    for all i ≠ j
```

which is exactly the injectivity of φ in the Disambiguation Theorem.

**Theorem (B1 ⟺ LL(2) restricted to dispatch groups with terminal
second items).** A dispatch group D(c, t) satisfies B1_APPLICABLE if
and only if:

1. Every rule has at least 2 terminal items at the prefix.
2. The 2-token FIRST sets of the rules are pairwise disjoint.

**Proof.** The shared dispatch token t contributes a constant first
element to every 2-token FIRST set: FIRST_2(rᵢ) = {t · s₁(rᵢ)}.
Two sets {t · a} and {t · b} are disjoint iff a ≠ b. Condition (2)
therefore holds iff s₁(rᵢ) ≠ s₁(rⱼ) for all i ≠ j, which together
with condition (1) is B1_APPLICABLE.  ∎

### 4.3 Differences from Classical LL(k)

| Aspect | Classical LL(k) | PraTTaIL B1 |
|:-------|:----------------|:------------|
| Scope | Entire grammar | Per dispatch group |
| k | Fixed for the grammar | k = 2 for qualifying groups; k = 1 (standard dispatch) for the rest |
| Nonterminal expansion | FIRST_k expands through nonterminals | B1 requires terminal second items only; nonterminals are rejected |
| Fallback | Grammar must be LL(k) globally | Non-qualifying groups fall back to NFA try-all |
| Weight ordering | N/A | NFA fallback uses WFST weight-ordered dispatch |
| Integration | Standalone parser generator | Embedded in Pratt + trampoline framework |

The key distinction is that B1 is a **local optimization** within the
Pratt framework, not a global grammar property. A grammar can have some
dispatch groups resolved by B1, others by A1 (shared prefix
left-factoring), and others by the NFA try-all fallback — all within the
same category.

---

## 5. Pseudocode

### 5.1 Analysis Phase

The analysis phase (`second_token_lookahead`) runs at compile time for
each ambiguous dispatch group.

```
function SECOND_TOKEN_LOOKAHEAD(rules: [Rule]) → Option<Map<Terminal, RuleIndex>>

    if |rules| < 2:
        return None                          // No ambiguity to resolve

    groups ← empty BTreeMap<String, Vec<usize>>

    for (idx, rule) in enumerate(rules):
        if |rule.items| < 2:
            return None                      // Rule too short for 2-token lookahead

        match rule.items[1]:
            Terminal(t):
                groups[variant_name(t)].push(idx)
            _:
                return None                  // Non-terminal second item → bail

    // Check injectivity: each second-token variant maps to exactly one rule
    if ∀ v ∈ groups.values(): |v| = 1:
        return Some({ v → v[0]  for (v, indices) in groups })
    else:
        return None                          // Shared second terminal → bail
```

### 5.2 Code Generation Phase

When B1 applies, the code generator (`write_nfa_merged_prefix_arm`)
emits a nested match instead of the NFA try-all loop.

```
function EMIT_B1_DISPATCH(buf, variant, lookahead, rules, cat)

    emit: "Token::{variant} => {"
    emit: "*pos += 1;"                       // Consume dispatch token

    emit: "if *pos < tokens.len() {"
    emit: "match &tokens[*pos].0 {"

    for (second_variant, rule_idx) in lookahead.groups:
        rule ← rules[rule_idx]
        emit: "Token::{second_variant} => {"
        emit: "*pos += 1;"                   // Consume second token
        emit: /* remaining items from rule.items[2..] */
        emit: /* AST constructor */
        emit: "},"

    emit: "_ => {"                           // No matching second token
    emit: "*pos -= 1;"                       // Restore: un-consume dispatch token
    emit: "return Err(ParseError::UnexpectedToken { ... });"
    emit: "},"

    emit: "} } else {"                       // No second token available
    emit: "*pos -= 1;"
    emit: "return Err(ParseError::UnexpectedEof { ... });"
    emit: "}"

    emit: "},"                               // Close dispatch arm
```

---

## 6. Diagram: B1 Decision Structure

### 6.1 2-State vs 3-Level Decision Tree

Standard single-token dispatch (LL(1)):

```
  tokens[*pos]
       │
       ├── Token::Kw ────► single rule (deterministic)
       ├── Token::LParen ─► single rule
       └── Token::Ident ──► single rule
```

B1 two-token dispatch (LL(2)):

```
  tokens[*pos]
       │
       └── Token::Kw ─── (ambiguous: 3 rules share "kw")
              │
              │  *pos += 1
              ▼
         tokens[*pos]
              │
              ├── Token::LParen ──► Rule A: kw "(" ...   (deterministic)
              ├── Token::LBracket ─► Rule B: kw "[" ...   (deterministic)
              ├── Token::LBrace ──► Rule C: kw "{" ...   (deterministic)
              └── _ ──────────────► ParseError            (no match)
```

### 6.2 WFST Topological View

The 2-token PredictionWfst for the same group:

```
                       "kw", w=1̄
  ┌──────────────────────────────────────────► q_mid
  │                                              │
  │                                    ┌─────────┼──────────┐
  │                                    │         │          │
  │                            "(", w=0.0  "[", w=0.0  "{", w=0.0
  │                                    │         │          │
  │                                    ▼         ▼          ▼
  │                                  f₁[A]     f₂[B]     f₃[C]
  │                                  (final)   (final)   (final)
  │
  q₀ (start)
```

Path weight for rule A: 1̄ ⊗ 0.0 ⊗ 1̄ = 0.0 (under TropicalWeight).
All paths have equal weight since the grammar is unambiguous at depth 2.

---

## 7. Worked Example

### 7.1 Grammar Rules

Consider a category `Cmd` with three rules that share the keyword `set`:

```
Rule SetField:   set "." ident:Name "=" val:Expr    → SetField(ident, val)
Rule SetIndex:   set "[" idx:Expr "]" "=" val:Expr  → SetIndex(idx, val)
Rule SetGlobal:  set "!" val:Expr                   → SetGlobal(val)
```

All three rules have `set` as their dispatch token (items[0]).

### 7.2 Analysis Trace

```
second_token_lookahead([SetField, SetIndex, SetGlobal]):

  |rules| = 3 ≥ 2                            ✓  (at least 2 rules)

  SetField:   items[1] = Terminal(".")        ✓  (terminal)
  SetIndex:   items[1] = Terminal("[")        ✓  (terminal)
  SetGlobal:  items[1] = Terminal("!")        ✓  (terminal)

  groups = {
    "Dot"      → [0],                         ✓  (unique: |v| = 1)
    "LBracket" → [1],                         ✓  (unique: |v| = 1)
    "Bang"     → [2],                         ✓  (unique: |v| = 1)
  }

  ∀ v: |v| = 1 → B1 applicable

  return Some(TwoTokenLookahead {
    groups: { "Dot" → 0, "LBracket" → 1, "Bang" → 2 }
  })
```

### 7.3 Generated Code Structure

```rust
Token::KwSet => {
    *pos += 1;                                // consume "set"
    if *pos < tokens.len() {
        match &tokens[*pos].0 {
            Token::Dot => {                   // set "."
                *pos += 1;                    // consume "."
                /* parse ident:Name, expect "=", parse val:Expr */
                /* construct SetField(ident, val) */
            },
            Token::LBracket => {              // set "["
                *pos += 1;                    // consume "["
                /* parse idx:Expr, expect "]", expect "=", parse val:Expr */
                /* construct SetIndex(idx, val) */
            },
            Token::Bang => {                  // set "!"
                *pos += 1;                    // consume "!"
                /* parse val:Expr */
                /* construct SetGlobal(val) */
            },
            _ => {
                *pos -= 1;                    // un-consume "set"
                return Err(ParseError::UnexpectedToken {
                    expected: Cow::Borrowed("Cmd expression after KwSet"),
                    found: format!("{:?}", &tokens[*pos].0),
                    range: tokens[*pos].1,
                });
            },
        }
    } else {
        *pos -= 1;                            // un-consume "set"
        return Err(ParseError::UnexpectedEof {
            expected: Cow::Borrowed("Cmd expression"),
            range: tokens[tokens.len() - 1].1,
        });
    }
},
```

### 7.4 Runtime Execution

Input: `set [ 42 ] = 100`

Tokens: `[KwSet, LBracket, Integer(42), RBracket, Eq, Integer(100)]`

```
Step 1:  tokens[*pos].0 = KwSet        → enter dispatch arm
Step 2:  *pos += 1                      → *pos = 1
Step 3:  tokens[*pos].0 = LBracket     → match Token::LBracket
Step 4:  *pos += 1                      → *pos = 2
Step 5:  ... parse remaining items for SetIndex ...
Result:  SetIndex(IntLit(42), IntLit(100))
```

Total dispatch cost: 2 token inspections, 0 save/restore, 0 backtracking.

Without B1 (NFA try-all with 3 alternatives):

```
Step 1:  save *pos = 0
Step 2:  try SetField:  consume "set", expect "." → found "[" → fail, restore *pos = 0
Step 3:  try SetIndex:  consume "set", expect "[" → found "[" → success, continue parsing
Step 4:  (SetGlobal not tried because SetIndex succeeded)
Result:  SetIndex(IntLit(42), IntLit(100))
```

NFA cost: 1 failed trial (save, partial parse, restore) + 1 successful trial.
For n alternatives, worst case is n-1 failed trials before success.

---

## 8. Complexity Analysis

### 8.1 Compile-Time Analysis

The `second_token_lookahead` function runs once per ambiguous dispatch
group during pipeline code generation.

| Operation | Cost |
|:----------|:-----|
| Iterate rules, extract items[1] | O(n) where n = |D(c, t)| |
| Insert into BTreeMap | O(n log n) |
| Check all values have length 1 | O(n) |
| **Total** | **O(n log n)** |

Since n is typically 2-5 (number of rules sharing a dispatch token),
the analysis is effectively O(1) in practice.

### 8.2 Runtime Dispatch

With B1:

| Operation | Cost |
|:----------|:-----|
| Match on first token (dispatch) | O(1) — existing match arm |
| Bounds check: `*pos < tokens.len()` | O(1) |
| Match on second token | O(1) — compiler-generated jump table |
| Advance position (`*pos += 1`) | O(1) |
| **Total per dispatch** | **O(1)** |

The second-token match is a standard Rust `match` on an enum, which the
compiler emits as a jump table or binary search over discriminants. For
typical grammar sizes (< 20 variants in a single group), this is
effectively a single indexed jump.

### 8.3 Comparison with NFA Try-All

| Metric | NFA Try-All | B1 Lookahead |
|:-------|:------------|:-------------|
| Best case | O(1) — first alternative succeeds | O(1) — always |
| Worst case | O(n) — last alternative succeeds or all fail | O(1) — always |
| Backtracking | Yes — save/restore per failed trial | None |
| Code size per group | O(n) closures + selection logic | O(n) match arms (smaller per-arm) |
| Position saves | n save/restore pairs | 0 |
| Spillover state | Writes to thread-local Vec | No thread-local access |
| Weight accumulation | Per-alternative weight tracking | No weight tracking needed |

For a dispatch group with n = 3 alternatives:

```
NFA try-all (worst case):  3 position saves + 2 failed parses + 1 success = 6 operations
B1 lookahead:              1 advance + 1 match + 1 advance = 3 operations
```

The improvement is particularly significant when the failed NFA trials
parse multiple tokens before failing (e.g., rules with long shared
prefixes beyond the second item), since each failed trial resets all
parsed state.

---

## 9. Non-Applicability: When B1 Does Not Apply

B1 is a restricted optimization. The following conditions cause
`second_token_lookahead` to return `None`, falling back to NFA try-all
or A1 left-factoring.

### 9.1 Non-Terminal Second Items

If any rule's `items[1]` is a `NonTerminal`, `IdentCapture`, `Binder`,
or `Collection`, the second item cannot be resolved by a simple token
peek — it requires parsing a subexpression.

**Example:**

```
Rule A:  error a:Expr          → ErrExpr(a)
Rule B:  error "("  a:Expr ")" → ErrGroup(a)
```

Rule A's `items[1]` is `NonTerminal { category: "Expr" }`. A single
token peek cannot determine whether the input is an Expr or a `"("`.
The function returns `None`.

### 9.2 Shared Second Terminals

If two or more rules share the same second terminal, the ambiguity
persists at depth 2.

**Example:**

```
Rule A:  error "(" a:Int  ")"  → ErrInt(a)
Rule B:  error "(" a:Bool ")"  → ErrBool(a)
```

Both rules have `items[1] = Terminal("(")`. After consuming `error`
and peeking at `"("`, the parser still cannot distinguish between the
two rules. The function returns `None`.

In such cases, A1 shared-prefix left-factoring may apply instead:
consume the shared `"("`, then NFA try-all over the divergent
remainders.

### 9.3 Short Rules

If any rule has fewer than 2 syntax items, there is no second item to
inspect.

**Example:**

```
Rule A:  error                  → ErrEmpty
Rule B:  error "(" a:Expr ")"  → ErrGroup(a)
```

Rule A has only `items[0] = Terminal("error")`. The function returns
`None`.

### 9.4 NFA Spillover Categories

When `config.needs_nfa_spillover` is true, the category has
forced-prefix replay infrastructure that requires all NFA alternatives
to be evaluated and spilled. B1's deterministic dispatch bypasses this
machinery, so it is disabled for categories that need spillover.

The guard in code generation:

```rust
if frame_pushing.is_empty() && !config.needs_nfa_spillover {
    if let Some(lookahead) = second_token_lookahead(inlineable) {
        // emit B1 dispatch
    }
}
```

### 9.5 Frame-Pushing Rules

Rules with same-category nonterminals require pushing continuation
frames onto the trampoline stack. These "frame-pushing" rules cannot
be inlined into the NFA merge arm and are excluded from B1 analysis.

The guard `frame_pushing.is_empty()` ensures B1 is only attempted when
all rules in the group are inlineable (no same-category nonterminals).

### 9.6 Fallback: NFA Try-All

When B1 does not apply, the dispatch group falls through to the NFA
try-all strategy:

1. Save position.
2. Try each alternative in WFST weight order (lowest weight first).
3. Collect successes with their positions and weights.
4. Select the first success (best weight).
5. Spill remaining alternatives to thread-local for forced-prefix replay
   (if `needs_nfa_spillover`).

This is always correct but has O(n) worst-case cost.

### 9.7 Hierarchy of Resolution Strategies

The code generator evaluates disambiguation strategies in priority order
for each ambiguous dispatch group:

```
  ┌─────────────────────────────────────────┐
  │ 1. A1: Shared terminal prefix?          │
  │    (left-factor shared tokens, then     │
  │     NFA try-all over divergent suffix)  │
  ├─────────────────────────────────────────┤
  │ 2. B1: Distinct second terminals?       │
  │    (nested match on second token)       │
  ├─────────────────────────────────────────┤
  │ 3. NFA try-all with WFST weight order   │
  │    (save/restore + weight selection)    │
  └─────────────────────────────────────────┘
```

A1 is checked first because it handles cases where rules share a
common prefix of arbitrary length. B1 is checked second because it
handles the specific case of distinct second terminals. Both are
strictly better than the NFA fallback for their qualifying groups.

---

## 10. Source References

| Symbol | Location |
|:-------|:---------|
| `TwoTokenLookahead` struct | `prattail/src/trampoline.rs:129` |
| `second_token_lookahead()` | `prattail/src/trampoline.rs:134` |
| B1 codegen in `write_nfa_merged_prefix_arm()` | `prattail/src/trampoline.rs:426–516` |
| `compute_shared_terminal_prefix()` (A1) | `prattail/src/trampoline.rs:190` |
| `TrampolineConfig.needs_nfa_spillover` | `prattail/src/trampoline.rs:1041` |
| `RDRuleInfo` | `prattail/src/recursive.rs:14` |
| `RDSyntaxItem` | `prattail/src/recursive.rs:40` |

### Tests

| Test | What it verifies |
|:-----|:----------------|
| `test_second_token_lookahead_distinct_second_terminals` | 2 rules, distinct items[1] → `Some` |
| `test_second_token_lookahead_single_rule` | 1 rule → `None` (no ambiguity) |
| `test_second_token_lookahead_shared_second_terminal` | shared items[1] → `None` |
| `test_second_token_lookahead_nonterminal_second_item` | NonTerminal items[1] → `None` |
| `test_second_token_lookahead_single_item_rule` | 1-item rule → `None` |
| `test_second_token_lookahead_three_rules_all_distinct` | 3 rules, all distinct → `Some` with 3 entries |

---

**See also:**

- [`semirings.md`](semirings.md) -- semiring axioms and TropicalWeight used in WFST weight annotation
- [`weighted-automata.md`](weighted-automata.md) -- PredictionWfst 2-state architecture (the k=1 baseline)
- [Ambiguity Targeting (A5)](../../design/wfst/ambiguity-targeting.md) -- per-token ambiguity analysis that identifies B1 candidates
- Multi-Token Lookahead Design (../../design/wfst/multi-token-lookahead.md) -- design-level companion document (planned)
