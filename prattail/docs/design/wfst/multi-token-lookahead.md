# B1: Multi-Token Lookahead

> **Date:** 2026-03-01

---

## Table of Contents

1. [Problem Statement](#1-problem-statement)
2. [Analysis Function](#2-analysis-function)
3. [Data Structure](#3-data-structure)
4. [Generated Code Structure](#4-generated-code-structure)
5. [Guard Conditions](#5-guard-conditions)
6. [Generated Code Example](#6-generated-code-example)
7. [Interaction with F2 (Early Termination)](#7-interaction-with-f2-early-termination)
8. [Interaction with A5 (Ambiguity Targeting)](#8-interaction-with-a5-ambiguity-targeting)
9. [Correctness](#9-correctness)
10. [Complexity](#10-complexity)
11. [Source References](#11-source-references)

---

## 1. Problem Statement

When multiple grammar rules within the same category share a dispatch
token, PraTTaIL's NFA disambiguation (Layer 2.5) resolves ambiguity at
runtime by *trying all alternatives*.  The NFA try-all loop saves the
current position, attempts each rule in WFST weight order, collects
successful results into `nfa_results`, and selects the best.  This
protocol is correct but imposes a cost proportional to the number of
alternatives: each alternative requires a save, a full parse attempt
(which may recurse arbitrarily deep), and a restore on failure.

### The save/restore overhead

For a dispatch token with N alternatives, the NFA try-all loop
performs up to N parse attempts.  Each attempt:

1. Restores `*pos` to the saved position (`*pos = nfa_saved;`).
2. Invokes the alternative's parse path (inline closure or standalone fn).
3. On success: pushes the result, position, and weight into parallel vectors.
4. On failure: records the first error for diagnostic use.

Even when only one alternative can succeed (because the alternatives
diverge at the very next token), the loop pays the full cost of trying
all N alternatives.  For N = 4 (e.g., `float(x)` dispatching
`FloatId`, `IntToFloat`, `BoolToFloat`, `StrToFloat`), three of the
four parse attempts are wasted when the correct rule could have been
identified by inspecting the second token.

### When two-token lookahead resolves all ambiguity

A significant class of NFA-ambiguous dispatch points have a special
property: the *second* token (the token immediately following the
shared dispatch token) is a *distinct terminal* for every alternative
rule.  In such cases, the parser can resolve ambiguity by peeking at
`tokens[*pos]` (after consuming the dispatch token) and matching
against the distinct second-token variants.

Consider the following grammar fragment:

```
category Proc {
    rule PInput  { Ident "!" "(" Proc ")" }
    rule POutput { Ident "?" "(" Proc ")" }
    rule PVar    { Ident }
}
```

All three rules dispatch on `Token::Ident`, creating a 3-way NFA
ambiguity.  However, the second tokens diverge completely:

| Rule     | items[0] | items[1] | Distinct? |
|----------|----------|----------|-----------|
| PInput   | Ident    | `!`      | Yes       |
| POutput  | Ident    | `?`      | Yes       |
| PVar     | Ident    | (none)   | Yes (< 2 items) |

Wait -- PVar has only one item, so it lacks a second terminal.  This
disqualifies the group from B1.  But consider a revised grammar:

```
category Cmd {
    rule CmdGet  { KwCmd "get" Ident }
    rule CmdSet  { KwCmd "set" Ident "=" Expr }
    rule CmdDel  { KwCmd "del" Ident }
}
```

| Rule    | items[0] | items[1] | Distinct? |
|---------|----------|----------|-----------|
| CmdGet  | KwCmd    | `get`    | Yes       |
| CmdSet  | KwCmd    | `set`    | Yes       |
| CmdDel  | KwCmd    | `del`    | Yes       |

Here, every rule has at least 2 items, every `items[1]` is a terminal,
and the three second-token variants (`KwGet`, `KwSet`, `KwDel`) are
all distinct.  B1 applies.

### Goal

B1 replaces the NFA try-all loop with a **nested match** on the second
token when the following conditions hold:

1. Every alternative rule has a distinct terminal at `items[1]`.
2. No frame-pushing rules are present in the group.
3. The category does not require NFA spillover.

The nested match is a compile-time decision -- the generated code
contains no save/restore, no `Vec<Cat>` allocation, and no trial
parse of wrong alternatives.  The parser commits to a single rule
based on the second token and either succeeds or returns an error.

---

## 2. Analysis Function

### Signature

```rust
fn second_token_lookahead(
    rules: &[&RDRuleInfo],
) -> Option<TwoTokenLookahead>
```

### Parameters

| Parameter | Type | Description |
|-----------|------|-------------|
| `rules` | `&[&RDRuleInfo]` | Slice of rules sharing the same dispatch token, within a single category |

### Algorithm

```
FUNCTION second_token_lookahead(rules):
    IF rules.len() < 2:
        RETURN None   // No ambiguity to resolve

    groups := BTreeMap<String, Vec<usize>>

    FOR (idx, rule) IN rules.enumerate():
        IF rule.items.len() < 2:
            RETURN None   // Rule has no second item

        MATCH rule.items[1]:
            Terminal(t) =>
                variant := terminal_to_variant_name(t)
                groups[variant].push(idx)
            _ =>
                RETURN None   // Second item is not a terminal

    // Check uniqueness: every second-token variant maps to exactly one rule
    IF groups.values().all(|indices| indices.len() == 1):
        RETURN Some(TwoTokenLookahead {
            groups: groups.map(|(k, v)| (k, v[0]))
        })
    ELSE:
        RETURN None   // Two rules share the same second terminal
```

### Rejection criteria

The function returns `None` (rejecting B1) in four cases:

| Case | Condition | Rationale |
|------|-----------|-----------|
| Trivial | `rules.len() < 2` | No ambiguity exists; dispatch is already deterministic |
| Short rule | Any rule has `items.len() < 2` | Cannot peek at `items[1]` because it does not exist |
| Non-terminal second | Any rule's `items[1]` is not a `Terminal` variant | NonTerminal, IdentCapture, ZipMapSep, etc. cannot be matched via a token peek |
| Collision | Two or more rules map to the same second-token variant | Ambiguity persists at depth 2; B1 does not help |

### Deterministic ordering

The `groups` map uses `BTreeMap<String, usize>`, ensuring that the
generated match arms are emitted in alphabetical order by second-token
variant name.  This provides:

- Reproducible generated code across compilations.
- Deterministic match arm ordering for snapshot testing.
- Consistent diagnostic output when logging B1 decisions.

---

## 3. Data Structure

### TwoTokenLookahead

```rust
/// B1 result: maps second-token variant -> rule index within the group.
/// Only produced when every rule has a distinct second item that is a terminal.
struct TwoTokenLookahead {
    /// second_variant -> index into the original inlineable slice
    groups: std::collections::BTreeMap<String, usize>,
}
```

The `groups` field maps each second-token variant name (e.g., `"Bang"`,
`"Question"`, `"KwGet"`) to the index of the corresponding rule within
the `inlineable` slice passed to `write_nfa_merged_prefix_arm()`.  The
index is used to look up the full `RDRuleInfo` for code generation.

### Relationship to the NFA pipeline

```
                    ┌──────────────────────────────────────────┐
                    │  write_nfa_merged_prefix_arm()           │
                    │                                          │
                    │  inlineable: &[&RDRuleInfo]              │
                    │  frame_pushing: &[&RDRuleInfo]           │
                    │  config: &TrampolineConfig               │
                    └──────────┬───────────────────────────────┘
                               │
                    ┌──────────▼───────────────────────────────┐
                    │  Guard check:                            │
                    │    frame_pushing.is_empty()              │
                    │    && !config.needs_nfa_spillover        │
                    └──────────┬───────────────────────────────┘
                               │ pass
                    ┌──────────▼───────────────────────────────┐
                    │  second_token_lookahead(inlineable)      │
                    └──────────┬───────────┬───────────────────┘
                               │           │
                          Some(la)       None
                               │           │
                    ┌──────────▼──┐  ┌─────▼──────────────────┐
                    │ B1: nested  │  │ Fall through to        │
                    │ match on    │  │ NFA try-all loop       │
                    │ second tok  │  │ (F2 may still apply)   │
                    └─────────────┘  └────────────────────────┘
```

B1 is attempted before the NFA try-all loop.  If `second_token_lookahead()`
returns `Some(la)`, the B1 code path is emitted and the function returns
immediately.  If it returns `None`, execution falls through to the standard
NFA try-all loop, where F2 (early termination) may still apply.

---

## 4. Generated Code Structure

When B1 applies, the generated code has the following structure:

```
Token::<dispatch_variant> => {
    // 1. Consume the dispatch token (already matched)
    *pos += 1;

    // 2. Peek at the second token
    if *pos < tokens.len() {
        match &tokens[*pos].0 {

            // 3. Per-rule arms: one arm per distinct second-token variant
            Token::<second_variant_A> => {
                *pos += 1;  // consume second token
                // ... remaining inline items from items[2..] ...
                // ... constructor or frame push ...
            },
            Token::<second_variant_B> => {
                *pos += 1;
                // ... remaining inline items ...
            },
            // ... more arms ...

            // 4. Fallback: second token does not match any expected variant
            _ => {
                *pos -= 1;  // restore position to before dispatch token
                return Err(ParseError::UnexpectedToken { ... });
            },
        }
    } else {
        // 5. EOF: only the dispatch token was available
        *pos -= 1;
        return Err(ParseError::UnexpectedEof { ... });
    }
},
```

### Step-by-step walkthrough

**Step 1: Consume the dispatch token.**  The outer match arm already
confirmed that `tokens[*pos].0` matches the dispatch variant.  `*pos += 1`
advances past it.  At this point, `*pos` indexes the second token (or is
past the end of the token stream).

**Step 2: Bounds check and peek.**  `if *pos < tokens.len()` guards against
reading past the end of the token array.  The `match &tokens[*pos].0` then
inspects the second token without consuming it.

**Step 3: Per-rule arms.**  For each entry `(second_variant, rule_idx)` in
`TwoTokenLookahead::groups`, one match arm is emitted.  The arm:

- Consumes the second token (`*pos += 1;`).
- Emits the remaining inline items from `items[2..]` via `write_inline_items()`.
- If the rule has a same-category NonTerminal (frame-pushing) -- but wait,
  the guard condition ensures `frame_pushing.is_empty()`, so this cannot
  happen for rules in the B1 group.  However, the rule *may* have a
  cross-category NonTerminal or an inline-only structure.  If a NonTerminal
  continuation is present, the code pushes a frame and continues the
  trampoline drive loop.  Otherwise, it emits the constructor inline via
  `write_nfa_inline_constructor()`.

**Step 4: Fallback arm.**  If the second token does not match any expected
variant, the parser restores position (`*pos -= 1` to back up past the
already-consumed dispatch token) and returns an `UnexpectedToken` error.
The error message includes both the category name and the dispatch variant
for diagnostic clarity (e.g., `"Proc expression after Ident"`).

**Step 5: EOF handling.**  If there is no second token (the dispatch token
was the last token in the stream), the parser restores position and returns
an `UnexpectedEof` error.

### No save/restore, no Vec allocation

Unlike the NFA try-all loop, B1 generates no `nfa_saved`, no
`nfa_results: Vec<Cat>`, no `nfa_positions: Vec<usize>`, and no
`nfa_weights: Vec<f64>`.  The entire disambiguation is performed via a
single bounds check and a nested match statement.  There is no trial
parse of wrong alternatives -- the parser commits to exactly one rule
based on the second token.

---

## 5. Guard Conditions

B1 is gated by two conjunctive conditions checked before
`second_token_lookahead()` is called:

```rust
if frame_pushing.is_empty() && !config.needs_nfa_spillover {
    if let Some(lookahead) = second_token_lookahead(inlineable) {
        // ... emit B1 code ...
        return;
    }
}
```

### 5.1. Why `frame_pushing` must be empty

`frame_pushing` contains rules in the current dispatch group that have
same-category NonTerminal items.  These rules require pushing a
continuation frame onto the trampoline stack and re-entering the
`'drive` loop -- they cannot be inlined into a closure for NFA
try-all.

B1 assumes that every alternative in the group can be resolved by
consuming two tokens and then either (a) completing inline or (b)
pushing a cross-category frame.  If a frame-pushing rule exists in
the group, it means at least one alternative requires same-category
recursion after the second token.  While B1 could theoretically handle
this by pushing frames from within the nested match arms, the current
architecture routes frame-pushing rules through a separate path in
`write_nfa_merged_prefix_arm()`:

- If `inlineable` is empty and `frame_pushing` has exactly one rule,
  that rule is emitted directly (single dispatch, no ambiguity).
- If `inlineable` is non-empty, the NFA try-all loop handles
  `inlineable` rules, and on `nfa_results.len() == 0`, falls back
  to the first `frame_pushing` rule.

B1 only operates on the `inlineable` slice.  When `frame_pushing` is
non-empty, the NFA try-all path is required to emit the frame-pushing
fallback.  Allowing B1 to handle only the inlineable subset while a
frame-pushing rule exists would create an inconsistency: the B1
fallback arm would return an error instead of attempting the
frame-pushing rule.

**Invariant:** B1 is emitted only when `frame_pushing.is_empty()`,
ensuring that all alternatives in the dispatch group are handled by
the nested match.

### 5.2. Why NFA spillover disables B1

When `config.needs_nfa_spillover` is `true`, the NFA try-all loop
must collect *all* successful parse results into the spillover buffer
(`NFA_PREFIX_SPILL_CAT`).  These alternatives are later consumed by
`from_alternatives()` during forced-prefix replay, which performs
semantic disambiguation (e.g., groundness analysis, type resolution).

B1 *commits* to a single alternative based on the second token.  It
does not try the other alternatives at all, so there is nothing to
spill.  If spillover is required but B1 suppresses alternative
collection, `from_alternatives()` would receive an incomplete set of
alternatives, potentially selecting a suboptimal or incorrect parse.

A concrete scenario:

```
rule Float::FloatId     { Ident }         // weight 0.0
rule Float::IntToFloat  { Int }           // weight 0.5
```

Both rules can begin with `Token::Ident` (since `Ident` is in
`FIRST(Int)` as well as `FIRST(Float)`).  If B1 resolved on the
second token and committed to `FloatId` (because `items[1]` diverged),
it would suppress the `IntToFloat` alternative entirely.  But
`FloatId` might produce a non-ground result (free variable), while
`IntToFloat` might produce a ground result.  `from_alternatives()`
needs both to choose correctly.

**Invariant:** B1 is emitted only when `!config.needs_nfa_spillover`,
ensuring that categories requiring semantic disambiguation still
collect all alternatives via the NFA try-all loop.

### 5.3. Summary of guard conditions

| Condition | Required value | Rationale |
|-----------|---------------|-----------|
| `frame_pushing.is_empty()` | `true` | All alternatives must be inlineable; no frame-pushing fallback needed |
| `config.needs_nfa_spillover` | `false` | B1 commits to one alternative; cannot populate spillover buffer |
| `second_token_lookahead(inlineable)` | `Some(la)` | Second tokens must be distinct terminals across all rules |

All three must hold for B1 to emit its nested match.

---

## 6. Generated Code Example

### 6.1. Before B1: NFA try-all with save/restore

For a grammar where `Token::KwCmd` dispatches three rules (`CmdGet`,
`CmdSet`, `CmdDel`) with distinct second terminals:

```rust
Token::KwCmd => {
    let nfa_saved = *pos;
    let mut nfa_results: Vec<Cmd> = Vec::new();
    let mut nfa_positions: Vec<usize> = Vec::new();
    let mut nfa_weights: Vec<f64> = Vec::new();
    let mut nfa_first_err: Option<ParseError> = None;

    // Alt 0: CmdGet (w=0.0)
    *pos = nfa_saved;
    match (|| -> Result<Cmd, ParseError> {
        let _t0 = expect_token!(tokens, pos, Token::KwCmd, "cmd");
        let _t1 = expect_token!(tokens, pos, Token::KwGet, "get");
        let name = parse_ident(tokens, pos)?;
        Ok(Cmd::CmdGet(name))
    })() {
        Ok(v) => {
            nfa_results.push(v);
            nfa_positions.push(*pos);
            nfa_weights.push(0.0);
        },
        Err(e) => { if nfa_first_err.is_none() { nfa_first_err = Some(e); } },
    }

    // Alt 1: CmdSet (w=0.0)
    *pos = nfa_saved;
    match (|| -> Result<Cmd, ParseError> {
        let _t0 = expect_token!(tokens, pos, Token::KwCmd, "cmd");
        let _t1 = expect_token!(tokens, pos, Token::KwSet, "set");
        let name = parse_ident(tokens, pos)?;
        let _t2 = expect_token!(tokens, pos, Token::Eq, "=");
        let val = parse_expr(tokens, pos, 0)?;
        Ok(Cmd::CmdSet(name, Box::new(val)))
    })() {
        Ok(v) => {
            nfa_results.push(v);
            nfa_positions.push(*pos);
            nfa_weights.push(0.0);
        },
        Err(e) => { if nfa_first_err.is_none() { nfa_first_err = Some(e); } },
    }

    // Alt 2: CmdDel (w=0.0)
    *pos = nfa_saved;
    match (|| -> Result<Cmd, ParseError> {
        let _t0 = expect_token!(tokens, pos, Token::KwCmd, "cmd");
        let _t1 = expect_token!(tokens, pos, Token::KwDel, "del");
        let name = parse_ident(tokens, pos)?;
        Ok(Cmd::CmdDel(name))
    })() {
        Ok(v) => {
            nfa_results.push(v);
            nfa_positions.push(*pos);
            nfa_weights.push(0.0);
        },
        Err(e) => { if nfa_first_err.is_none() { nfa_first_err = Some(e); } },
    }

    match nfa_results.len() {
        0 => { return Err(nfa_first_err.unwrap_or_else(|| /* ... */)); },
        _ => {
            *pos = nfa_positions[0];
            RUNNING_WEIGHT_CMD.with(|cell| cell.set(cell.get() + nfa_weights[0]));
            break 'prefix nfa_results.into_iter().next()
                .expect("nfa_results non-empty");
        },
    }
},
```

**Problems with the NFA try-all approach:**

1. Three `Vec` allocations (`nfa_results`, `nfa_positions`, `nfa_weights`).
2. Three save/restore cycles (`*pos = nfa_saved` before each alternative).
3. Three full parse attempts, including redundant `expect_token!` for
   `Token::KwCmd` (already matched by the outer dispatch).
4. Two of the three closures always fail (only one second-token can match).

### 6.2. After B1: nested match on second token

```rust
Token::KwCmd => {
    *pos += 1;
    if *pos < tokens.len() {
        match &tokens[*pos].0 {
            Token::KwDel => {
                *pos += 1;
                let name = parse_ident(tokens, pos)?;
                break 'prefix Cmd::CmdDel(name);
            },
            Token::KwGet => {
                *pos += 1;
                let name = parse_ident(tokens, pos)?;
                break 'prefix Cmd::CmdGet(name);
            },
            Token::KwSet => {
                *pos += 1;
                let name = parse_ident(tokens, pos)?;
                let _t2 = expect_token(tokens, pos,
                    |t| matches!(t, Token::Eq), "=")?;
                let val = parse_expr(tokens, pos, 0)?;
                break 'prefix Cmd::CmdSet(name, Box::new(val));
            },
            _ => {
                *pos -= 1;
                return Err(ParseError::UnexpectedToken {
                    expected: Cow::Borrowed("Cmd expression after KwCmd"),
                    found: format!("{:?}", &tokens[*pos].0),
                    range: tokens[*pos].1,
                });
            },
        }
    } else {
        *pos -= 1;
        return Err(ParseError::UnexpectedEof {
            expected: Cow::Borrowed("Cmd expression"),
            range: tokens[tokens.len() - 1].1,
        });
    }
},
```

**Improvements:**

| Metric | NFA try-all | B1 nested match |
|--------|-------------|-----------------|
| Vec allocations | 3 (results, positions, weights) | 0 |
| Save/restore cycles | 3 | 0 |
| Parse attempts per dispatch | 3 (all alternatives) | 1 (committed rule) |
| Redundant dispatch-token matching | 3x `expect_token!(KwCmd)` | 0 (consumed once) |
| Redundant second-token matching | 2 (wrong alternatives fail at `expect_token!`) | 0 (matched once) |
| Code branches | sequential try-all + result selection | single nested match |

### 6.3. Diff summary

The structural transformation replaces:

```
save → try A → restore → try B → restore → try C → select best
```

with:

```
consume dispatch → peek second → commit to one rule
```

No logic inside any individual rule's parse body is modified.  The
transformation only changes *how the correct rule is selected*, not
*what the rule does once selected*.

---

## 7. Interaction with F2 (Early Termination)

F2 (Early Termination on Deterministic Hit) inserts an
`if nfa_results.is_empty() { ... }` guard around alternatives after
the first weight-0.0 alternative in the NFA try-all loop.  If the
first alternative succeeds, the remaining alternatives are skipped.

### B1 subsumes F2 when applicable

When B1 applies, the NFA try-all loop is not emitted at all.  There
are no `nfa_results` to check, no alternatives to guard, and no
early termination to perform.  The nested match commits to a single
rule immediately, achieving a stronger result than F2:

| Property | F2 | B1 |
|----------|----|----|
| First alternative tried | Always | Only the correct one |
| Other alternatives tried | Only if first fails | Never |
| Vec allocations | 3 (results, positions, weights) | 0 |
| Runtime overhead on success | One closure invocation + guard check | Bounds check + match |
| Applicability | Weight-0.0 first alt, no spillover | Distinct second terminals, no frame-pushing, no spillover |

B1 strictly dominates F2 on every metric when it applies.  However,
B1 has stricter applicability requirements (distinct second terminals),
so F2 remains necessary for dispatch groups where B1 does not apply
(e.g., when rules share the same second terminal, or when the second
item is a NonTerminal).

### Decision priority

In `write_nfa_merged_prefix_arm()`, the code generator checks
optimizations in the following order:

```
1. A1 (left-factoring via shared prefix)  [line 327]
2. B1 (two-token lookahead)               [line 426]
3. NFA try-all with F2 guard              [line 518]
```

If A1 applies (shared terminal prefix beyond the dispatch token), it
handles the arm and returns.  Otherwise, if B1 applies, it handles the
arm and returns.  Otherwise, the NFA try-all loop is emitted, with F2
applied if the first alternative has weight 0.0.

A1 and B1 are mutually exclusive by construction: A1 requires that all
rules share a common second terminal (prefix), while B1 requires that
all rules have *distinct* second terminals.  Both cannot hold
simultaneously for the same dispatch group.

---

## 8. Interaction with A5 (Ambiguity Targeting)

A5 (CountingWeight-Guided Ambiguity Targeting) provides per-token
ambiguity analysis, identifying dispatch tokens with multiple
alternatives and flagging B1 candidates.  A5 runs at compile time
in the pipeline, after WFST construction.

### A5 identifies B1 candidates

A5's `TokenAmbiguityInfo` struct includes a `lookahead_candidate`
field, set to `true` when a token's `alternative_count` exceeds
the configured threshold (default: 1, meaning any token with 2+
alternatives is flagged).  The pipeline's diagnostic output marks
these with `<-- B1 candidate`:

```
  info: A5 ambiguity targeting: 3 ambiguous token(s), 14 unambiguous, max ambiguity=3
         Cmd::KwCmd -- 3 alternative(s): [CmdGet, CmdSet, CmdDel] <-- B1 candidate
         Proc::Ident -- 2 alternative(s): [PInput, PVar]
```

### A5 is advisory; B1 is the actuator

A5 identifies *which* dispatch tokens have ambiguity and *how much*
ambiguity they carry.  It does not perform any structural analysis of
the rules' syntax items.  B1 performs the structural analysis (via
`second_token_lookahead()`) and decides whether the ambiguity can be
resolved by a nested match.

The relationship:

```
    ┌──────────────────┐          ┌──────────────────────┐
    │  A5: Ambiguity   │          │  B1: Multi-Token     │
    │  Targeting       │          │  Lookahead           │
    │                  │          │                      │
    │  "KwCmd has 3    │  feeds   │  "KwCmd's rules have │
    │   alternatives"  │ ──────── │   distinct items[1]" │
    │                  │  into    │                      │
    │  (diagnostic)    │          │  (codegen decision)  │
    └──────────────────┘          └──────────────────────┘
```

A5 is purely diagnostic today -- it produces structured data and
logs it.  B1 operates independently: it checks the guard conditions
and calls `second_token_lookahead()` regardless of whether A5 has
run.  In future pipeline iterations, A5's
`AmbiguityTargetingResult.ambiguous_tokens` could be threaded to B1
to skip analysis on unambiguous tokens (an optimization that avoids
calling `second_token_lookahead()` for groups of size 1).

---

## 9. Correctness

**Theorem.**  When B1 applies (all guard conditions hold and
`second_token_lookahead()` returns `Some(la)`), the generated
nested match produces the same parse result as the NFA try-all loop.

**Definitions.**

Let R = {r_0, r_1, ..., r_{n-1}} be the set of rules in the dispatch
group, all sharing dispatch token d.  Let s_i denote the terminal at
`r_i.items[1]`.  Let v_i = `terminal_to_variant_name(s_i)`.

By the B1 precondition (`second_token_lookahead()` returns `Some`):

- For all i: `r_i.items.len() >= 2` (every rule has a second item).
- For all i: `r_i.items[1]` is a `Terminal` variant (second item is a terminal).
- For all i != j: `v_i != v_j` (second-token variants are distinct).

**Lemma 1 (Unique dispatch).**  For any input token sequence
`[d, t, ...]` where `t` is a token, at most one rule r_k in R has
`v_k == terminal_to_variant_name(t)`.

*Proof.*  By the distinctness precondition, the mapping
`v_i -> i` is injective.  Therefore, for any variant name `v`,
there exists at most one index k such that `v_k == v`.  Since
`terminal_to_variant_name` is a function, `t` maps to exactly one
variant name.  Hence at most one r_k matches.  QED

**Lemma 2 (NFA try-all selects the same rule).**  In the NFA try-all
loop, only rule r_k (whose second token matches `t`) can succeed when
the input begins with `[d, t, ...]`.  All other rules r_j (j != k)
fail at their `expect_token!` for `items[1]`, because `tokens[saved+1]`
is `t`, not `s_j`.

*Proof.*  Each alternative in the NFA try-all loop starts by
restoring `*pos = nfa_saved` and then executing the rule's inline
items sequentially.  `items[0]` is the dispatch token d, which always
matches (it was already confirmed by the outer dispatch match).
`items[1]` is `s_j`, matched via `expect_token!`.  Since
`tokens[nfa_saved + 1] == t` and `v_j != v_k` for j != k (by
distinctness), the `expect_token!` for `items[1]` fails for all
j != k.  Only r_k's `expect_token!` for `items[1]` succeeds.

Therefore, `nfa_results` contains exactly one entry (r_k's result),
and `nfa_results[0]` is r_k's parse tree.  QED

**Proof of Theorem.**

1. The B1 nested match consumes the dispatch token, inspects the
   second token, and dispatches to exactly one arm -- the arm for
   r_k whose `v_k == terminal_to_variant_name(tokens[*pos])`.
2. By Lemma 2, the NFA try-all loop would also select r_k as the
   sole successful alternative.
3. The parse body for r_k is identical in both code paths: the same
   inline items (from `items[2..]`) are emitted by the same
   `write_inline_items()` function, and the same constructor is
   produced by `write_nfa_inline_constructor()`.
4. Therefore, the B1 nested match produces the same parse result
   as the NFA try-all loop.  QED

**Corollary (Error equivalence).**  When no rule matches (the second
token is not in {v_0, ..., v_{n-1}}), the B1 fallback arm returns an
`UnexpectedToken` error, and the NFA try-all loop returns the first
error from `nfa_first_err`.  Both indicate a parse failure at the
same position.  The error messages differ in wording but convey
equivalent diagnostic information.

---

## 10. Complexity

### Compile-time (analysis)

| Operation | Cost |
|-----------|------|
| `second_token_lookahead()` call | O(N) where N = number of rules in group |
| Inner loop over rules | O(N) |
| BTreeMap insertions | O(N log N) |
| Uniqueness check | O(N) |
| Total | O(N log N) |

For typical grammars, N is small (2-6 rules per dispatch token),
making the analysis cost negligible.

### Runtime (generated code)

| Operation | NFA try-all | B1 nested match |
|-----------|-------------|-----------------|
| Bounds check | 0 | 1 (`*pos < tokens.len()`) |
| Match arms evaluated | Up to N (all alternatives) | 1 (committed rule) |
| Position saves/restores | N | 0 |
| Vec allocations | 3 | 0 |
| Closure invocations | N | 0 |
| Total work per dispatch | O(N * parse_cost) | O(1 + parse_cost) |

The key improvement is from O(N * parse_cost) to O(parse_cost): the
disambiguation overhead drops from linear in the number of alternatives
to constant (one bounds check + one match).

---

## 11. Source References

| Component | Location | Description |
|-----------|----------|-------------|
| `TwoTokenLookahead` struct | `trampoline.rs:129-132` | B1 result struct with `groups: BTreeMap<String, usize>` |
| `second_token_lookahead()` | `trampoline.rs:134-177` | Analysis function: checks distinct second terminals |
| B1 guard + codegen | `trampoline.rs:426-516` | Guard conditions check and nested match emission |
| `write_nfa_merged_prefix_arm()` | `trampoline.rs:277-733` | Enclosing function: A1, B1, NFA try-all with F2 |
| `terminal_to_variant_name()` | `automata/codegen.rs` | Maps terminal string to Token enum variant name |
| `split_rd_handler()` | `trampoline.rs` | Splits RD rule into handler segments for codegen |
| `write_inline_items()` | `trampoline.rs` | Emits inline syntax item matching code |
| `write_nfa_inline_constructor()` | `trampoline.rs:739-` | Emits `Ok(Cat::Label(...))` for NFA-inlined rules |
| `TrampolineConfig` struct | `trampoline.rs:1007-1050` | Config including `needs_nfa_spillover` field |
| `categories_needing_nfa_spillover()` | `trampoline.rs:251-266` | Determines which categories need spillover |

### See also

- `theory/wfst/multi-token-lookahead.md` -- Theoretical foundations for k-token lookahead (planned)
- `design/wfst/ambiguity-targeting.md` -- A5 CountingWeight-guided ambiguity targeting
- `design/wfst/early-termination.md` -- F2 deterministic-hit early termination
- `design/wfst/nfa-disambiguation.md` -- NFA try-all architecture (Layer 2.5)
- `design/wfst/spillover-pruning.md` -- F1 weight-based spillover pruning
