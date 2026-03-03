# Grammar Left-Factoring (A1)

**Date:** 2026-03-01

---

## Table of Contents

1. [Problem](#1-problem)
2. [Shared Terminal Prefix Analysis](#2-shared-terminal-prefix-analysis)
3. [PrefixTrie Data Structure](#3-prefixtrie-data-structure)
4. [Generated Code Structure](#4-generated-code-structure)
5. [Guard Conditions](#5-guard-conditions)
6. [Worked Example](#6-worked-example)
7. [Interaction with B1 (Two-Token Lookahead)](#7-interaction-with-b1-two-token-lookahead)
8. [Correctness](#8-correctness)
9. [Complexity](#9-complexity)
10. [Source References](#10-source-references)

---

## 1. Problem

When multiple recursive descent (RD) rules within the same category share the
same dispatch token, PraTTaIL's NFA disambiguation (Layer 2.5) resolves the
ambiguity by trying each alternative in a *save/restore* loop.  For every
alternative, the parser:

1. Saves the current cursor position (`nfa_saved = *pos`).
2. Attempts the full parse of the rule's syntax items.
3. Restores the cursor on failure and tries the next alternative.

This design is correct but performs redundant work when multiple rules share
terminal tokens *beyond* the dispatch token.  The shared terminals are matched,
consumed, and then rolled back for each failed alternative -- only to be
re-matched identically by the next one.

### Concrete instance

In the Calculator grammar, the `Float` category contains four cast/identity
rules that all begin with `"float" "("`:

```
Float category rules sharing "float":
  FloatId     . a:Float  |- "float" "(" a ")"  : Float
  IntToFloat  . a:Int    |- "float" "(" a ")"  : Float
  BoolToFloat . a:Bool   |- "float" "(" a ")"  : Float
  StrToFloat  . a:Str    |- "float" "(" a ")"  : Float
```

All four rules share the dispatch token `"float"` (items[0]) *and* the opening
parenthesis `"("` (items[1]).  They diverge only at items[2], where the inner
expression is parsed as `Float`, `Int`, `Bool`, or `Str` respectively.

Without left-factoring, the NFA try-all loop performs 4 full save/restore
cycles, each of which includes matching `"("` -- a terminal that is guaranteed
to succeed for all alternatives or fail for all.  This produces:

| Operation | Count (without A1) |
|-----------|-------------------|
| Save cursor | 4 |
| Match `"("` | 4 (identical) |
| Restore cursor | up to 3 (on failure) |
| Total terminal matches | 8 (4 dispatch + 4 paren) |

With left-factoring, the shared `"("` is matched *once* before the NFA try-all
begins.  The loop only saves/restores over the *divergent suffix* (items[2..]):

| Operation | Count (with A1) |
|-----------|----------------|
| Match `"("` | 1 |
| Save cursor | 4 (over suffixes only) |
| Restore cursor | up to 3 |
| Total terminal matches | 5 (4 dispatch + 1 paren) |

For rules with deeper shared prefixes (e.g., `"kw" "(" "[" "{" ...`), the
savings compound: *N* rules with *P* shared terminals save *P x (N - 1)*
redundant terminal matches.

---

## 2. Shared Terminal Prefix Analysis

### `compute_shared_terminal_prefix()`

The function `compute_shared_terminal_prefix()` determines the longest common
terminal prefix among a set of rules, starting from items[1] (items[0] is the
dispatch token, already handled by the outer `match`).

```rust
// trampoline.rs:190-231
fn compute_shared_terminal_prefix(rules: &[&RDRuleInfo]) -> Vec<String> {
    if rules.len() < 2 {
        return Vec::new();
    }

    // Find the minimum rule length (excluding items[0] which is the dispatch token)
    let min_suffix_len = rules
        .iter()
        .map(|r| r.items.len().saturating_sub(1))
        .min()
        .unwrap_or(0);

    if min_suffix_len == 0 {
        return Vec::new();
    }

    let mut shared = Vec::new();

    // Walk items[1..] in lockstep across all rules
    for offset in 0..min_suffix_len {
        let item_idx = offset + 1; // items[0] is dispatch token

        // Get the terminal at this position in the first rule
        let first_terminal = match &rules[0].items[item_idx] {
            RDSyntaxItem::Terminal(t) => t.clone(),
            _ => break, // Non-terminal -> stop sharing
        };

        // Check all other rules have the same terminal at this position
        let all_same = rules[1..].iter().all(|rule| {
            matches!(&rule.items[item_idx], RDSyntaxItem::Terminal(t) if *t == first_terminal)
        });

        if all_same {
            shared.push(first_terminal);
        } else {
            break; // Divergence point found
        }
    }

    shared
}
```

### Algorithm

The function walks `items[1..]` in lockstep across all rules in the group:

```
items[0]     items[1]    items[2]     items[3]    items[4]
 "float"       "("       a:Int         ")"         --
 "float"       "("       a:Bool        ")"         --
 "float"       "("       a:Str         ")"         --
 "float"       "("       a:Float       ")"         --
    ^            ^           ^
 dispatch    shared[0]   divergence
  token                  (non-terminal)
```

1. Start at `offset = 0` (items[1]).
2. Extract the syntax item from the first rule at this position.
3. If it is a `Terminal`, check whether all other rules have the same terminal
   at the same position.
4. If all match, push the terminal string onto `shared` and advance.
5. If any rule has a different terminal, a non-terminal, or is shorter than
   the current offset, stop immediately.

### Termination conditions

The prefix walk stops at the first position where any of the following holds:

| Condition | Reason |
|-----------|--------|
| The first rule has a `NonTerminal` at this position | Non-terminals cannot be compared statically |
| A subsequent rule has a different terminal | Divergence point found |
| A subsequent rule has a `NonTerminal` | Divergence point found |
| A rule is too short (no items at this offset) | Cannot index further |
| Only 1 rule in the group | No prefix to share |

The function returns an empty `Vec<String>` when no shared prefix exists,
which causes the A1 code path to be skipped entirely.

---

## 3. PrefixTrie Data Structure

### Design

The `PrefixTrie<K, V>` at `prefix_trie.rs` is a generic trie data structure
used at compile time for analyzing shared prefixes among grammar rules.  Unlike
the byte-level tries in PathMap and liblevenshtein, `PrefixTrie` operates on
sequences of arbitrary element types (`K: Eq + Hash + Clone`), making it
suitable for sequences of `RDSyntaxItem` or terminal strings.

### API inspiration

The traversal API is inspired by two existing trie implementations:

| Method | Analogous to | Description |
|--------|-------------|-------------|
| `descend(&K)` | PathMap `ZipperMoving::descend_to()` | Navigate to a child by key element |
| `children()` | liblevenshtein `DictZipper::children()` | Iterate over (element, subtrie) pairs |
| `shared_prefix_depth()` | -- | Depth of single-child chain from root |
| `shared_prefix()` | -- | Elements and divergence node of single-child chain |
| `count_values()` | PathMap `child_count()` | Total number of leaf values in subtrie |
| `insert()` | -- | Insert a key sequence with associated value |

### Structure

```rust
// prefix_trie.rs:23-28
pub struct PrefixTrie<K, V> {
    /// Value at this node (Some if a key ends here).
    pub value: Option<V>,
    /// Children: maps element -> subtrie.
    pub children: HashMap<K, PrefixTrie<K, V>>,
}
```

Each node optionally stores a value (indicating that a complete key ends at
this node) and maps key elements to child subtries.  The trie is uncompressed
-- every element in the key occupies one level of the tree.

### Key methods

**`insert(key, value)`** -- Insert a key (any `IntoIterator<Item = K>`) with
an associated value.  Traverses existing nodes, creating new ones as needed:

```rust
// prefix_trie.rs:40-46
pub fn insert(&mut self, key: impl IntoIterator<Item = K>, value: V) {
    let mut node = self;
    for elem in key {
        node = node.children.entry(elem).or_insert_with(PrefixTrie::new);
    }
    node.value = Some(value);
}
```

**`shared_prefix_depth()`** -- Returns the length of the longest single-child
chain from the root.  This is the depth at which all inserted keys agree:

```rust
// prefix_trie.rs:67-75
pub fn shared_prefix_depth(&self) -> usize {
    let mut depth = 0;
    let mut node = self;
    while node.children.len() == 1 && node.value.is_none() {
        depth += 1;
        node = node.children.values().next().expect("single child exists");
    }
    depth
}
```

The walk terminates at the first node with more than one child (divergence),
a stored value (a key ends here, so the prefix is complete for at least one
key), or zero children (leaf node).

**`shared_prefix()`** -- Returns both the key elements along the single-child
chain and a reference to the divergence node:

```rust
// prefix_trie.rs:79-88
pub fn shared_prefix(&self) -> (Vec<&K>, &PrefixTrie<K, V>) {
    let mut prefix = Vec::new();
    let mut node = self;
    while node.children.len() == 1 && node.value.is_none() {
        let (key, child) = node.children.iter().next().expect("single child exists");
        prefix.push(key);
        node = child;
    }
    (prefix, node)
}
```

### Compile-time only

The `PrefixTrie` is used exclusively at compile time during codegen.  It does
not appear in the generated parser code.  Its purpose is to analyze the
structure of rule groups and inform the codegen decisions -- specifically,
whether A1 left-factoring or B1 two-token lookahead should be applied.

### Diagram: trie for Calculator Float rules

```
  root
   │
   "("          ← shared_prefix_depth() = 1
   │
   ├── a:Int    → FloatId (if cat=Float), IntToFloat
   ├── a:Bool   → BoolToFloat
   ├── a:Str    → StrToFloat
   └── a:Float  → FloatId
```

After inserting the suffix items (items[1..]) of all four Float-cast rules,
the trie has a single-child chain of depth 1 (`"("`), then diverges into four
children at the non-terminal level.  `shared_prefix_depth()` returns 1,
confirming that one terminal can be factored out.

---

## 4. Generated Code Structure

### Overview

When A1 detects a shared terminal prefix, the generated code has two phases:

```
┌─────────────────────────────────────┐
│ Phase 1: Walk shared prefix         │
│  - Consume dispatch token           │
│  - expect_token() for each shared   │
│    terminal (no save/restore)       │
├─────────────────────────────────────┤
│ Phase 2: NFA try-all over suffixes  │
│  - Save cursor at divergence point  │
│  - Try each alternative's items     │
│    starting at items[skip_count..]  │
│  - Restore cursor between attempts  │
│  - Select best result by weight     │
└─────────────────────────────────────┘
```

### Phase 1: Shared prefix walk

The dispatch token is consumed with `*pos += 1`.  Each shared terminal is
consumed with an `expect_token()` call that either succeeds (advancing `*pos`)
or returns an error immediately.  No save/restore is needed because these
terminals are common to *all* alternatives -- if any one fails, all would fail.

```rust
// Generated code (Phase 1):
Token::KwFloat => {
    *pos += 1;                                           // consume "float"
    expect_token(tokens, pos,
        |t| matches!(t, Token::LParen), "(")?;           // shared: "("
```

The `expect_token()` helper is defined in `pratt.rs` (line 706) and performs a
single token match with position advancement:

```rust
// pratt.rs:706-726
fn expect_token<'a>(
    tokens: &[(Token<'a>, Range)],
    pos: &mut usize,
    predicate: impl Fn(&Token) -> bool,
    expected: &'static str,
) -> Result<(), ParseError> {
    if *pos >= tokens.len() {
        let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero());
        return Err(ParseError::UnexpectedEof {
            expected: Cow::Borrowed(expected), range: eof_range
        });
    }
    if predicate(&tokens[*pos].0) {
        *pos += 1;
        Ok(())
    } else {
        Err(ParseError::UnexpectedToken {
            expected: Cow::Borrowed(expected),
            found: format!("{:?}", tokens[*pos].0),
            range: tokens[*pos].1,
        })
    }
}
```

### Phase 2: NFA try-all over divergent suffixes

After the shared prefix is consumed, the cursor is at the divergence point.
The NFA try-all loop saves this position and attempts each alternative's
*remaining* items (items[skip_count..], where `skip_count = 1 + prefix_len`):

```rust
// Generated code (Phase 2):
    let nfa_saved = *pos;
    let mut nfa_results: Vec<Float> = Vec::new();
    let mut nfa_positions: Vec<usize> = Vec::new();
    let mut nfa_weights: Vec<f64> = Vec::new();
    let mut nfa_first_err: Option<ParseError> = None;

    // Alternative 1 (FloatId, weight 0.0):
    *pos = nfa_saved;
    match (|| -> Result<Float, ParseError> {
        // items[2..] only: parse_Float(tokens, pos, 0)?
        // items[3]: expect_token(... ")")
        // construct FloatId
    })() {
        Ok(v) => {
            nfa_results.push(v);
            nfa_positions.push(*pos);
            nfa_weights.push(0.0);
        },
        Err(e) => { if nfa_first_err.is_none() { nfa_first_err = Some(e); } },
    }

    // Alternative 2 (IntToFloat, weight 0.3):
    *pos = nfa_saved;
    match (|| -> Result<Float, ParseError> {
        // items[2..] only: parse_Int(tokens, pos, 0)?
        // items[3]: expect_token(... ")")
        // construct IntToFloat
    })() {
        Ok(v) => { nfa_results.push(v); nfa_positions.push(*pos); nfa_weights.push(0.3); },
        Err(e) => { if nfa_first_err.is_none() { nfa_first_err = Some(e); } },
    }

    // ... BoolToFloat (weight 0.8), StrToFloat (weight 1.5) ...

    // Result selection:
    match nfa_results.len() {
        0 => { return Err(nfa_first_err.unwrap_or_else(|| ... )); },
        _ => {
            *pos = nfa_positions[0];
            RUNNING_WEIGHT_FLOAT.with(|cell| cell.set(cell.get() + nfa_weights[0]));
            break 'prefix nfa_results.into_iter().next().expect("nfa_results non-empty");
        },
    }
},
```

### WFST weight ordering

The order in which alternatives are tried within the NFA loop is determined by
`PredictionWfst::nfa_alternative_order()`.  This function looks up each rule's
weight from the WFST prediction table and sorts alternatives by ascending
tropical weight (lowest = most likely first):

```rust
// wfst.rs:233-253
pub fn nfa_alternative_order(
    &self,
    token_name: &str,
    rule_labels: &[&str],
) -> Vec<(usize, TropicalWeight)> {
    let predictions = self.predict(token_name);
    let mut indexed: Vec<(usize, TropicalWeight)> = rule_labels
        .iter()
        .enumerate()
        .map(|(i, label)| {
            let weight = predictions
                .iter()
                .find(|a| a.action.rule_label() == *label)
                .map(|a| a.weight)
                .unwrap_or(TropicalWeight::new(0.5));
            (i, weight)
        })
        .collect();
    indexed.sort_by(|(_, wa), (_, wb)| wa.cmp(wb));
    indexed
}
```

When no `PredictionWfst` is available, all alternatives receive a default
weight of 0.5 and are tried in declaration order.

### Codegen implementation

The A1 codegen is implemented in `write_nfa_merged_prefix_arm()` at
trampoline.rs lines 322-423.  The relevant section:

```rust
// trampoline.rs:322-423 (A1 section)
if frame_pushing.is_empty() && inlineable.len() >= 2 {
    let shared_terminal_prefix = compute_shared_terminal_prefix(inlineable);
    if !shared_terminal_prefix.is_empty() {
        write!(buf, "Token::{} => {{", variant).unwrap();
        buf.push_str("*pos += 1;");

        // Walk the shared terminal prefix
        for terminal in &shared_terminal_prefix {
            let shared_variant = terminal_to_variant_name(terminal);
            write!(buf,
                "expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?;",
                shared_variant, terminal,
            ).unwrap();
        }

        let skip_count = 1 + shared_terminal_prefix.len();
        // ... NFA try-all over items[skip_count..] ...
        return; // A1 handled this arm
    }
}
```

The `skip_count` variable determines how many items each alternative skips
when emitting its inline items.  It equals `1` (dispatch token) plus the
length of the shared prefix.

---

## 5. Guard Conditions

A1 left-factoring is applied only when *both* of the following conditions hold:

```rust
frame_pushing.is_empty() && inlineable.len() >= 2
```

### Condition 1: `frame_pushing.is_empty()`

Rules in the `frame_pushing` set contain same-category non-terminal references
that require pushing trampoline frames onto the continuation stack.  These
rules cannot be inlined into a save/restore NFA loop because they interact
with the trampoline's `'drive`/`'unwind` control flow.  A1 only applies to
*inlineable* rules -- those whose parse can be expressed as a straight-line
sequence of `expect_token()` and cross-category `parse_Cat()` calls within a
closure.

When `frame_pushing` is non-empty, the arm falls through to separate handling:
single frame-pushing rules are emitted directly, and mixed groups produce a
diagnostic.

### Condition 2: `inlineable.len() >= 2`

Left-factoring requires at least two rules to share a prefix.  A single rule
has no redundancy to eliminate and is handled by the standard single-arm
codegen path.

### Additional condition: non-empty shared prefix

Even when both guard conditions are met, A1 only activates if
`compute_shared_terminal_prefix()` returns a non-empty vector.  If the rules'
items[1] positions diverge immediately (different terminals or a non-terminal),
the function returns an empty vector and A1 falls through to the B1
(two-token lookahead) check or the general NFA try-all path.

### Decision flow

```
              ┌───────────────────────────────┐
              │ Multiple rules share dispatch │
              │ token (ambiguous group)       │
              └──────────────┬────────────────┘
                             │
              ┌──────────────▼────────────────┐
              │ frame_pushing.is_empty()?     │
              └──────┬───────────────┬────────┘
                yes  │               │ no
                     │    ┌──────────▼──────────┐
                     │    │ Single frame-pushing │
                     │    │ rule → emit directly │
                     │    │ Multiple → diagnostic│
                     │    └─────────────────────┘
              ┌──────▼────────────────┐
              │ inlineable.len() >= 2?│
              └──────┬──────────┬─────┘
                yes  │          │ no
                     │   ┌──────▼──────────────┐
                     │   │ Single rule → emit  │
                     │   │ standard arm        │
                     │   └─────────────────────┘
              ┌──────▼────────────────────────┐
              │ compute_shared_terminal_      │
              │ prefix() non-empty?           │
              └──────┬──────────────┬─────────┘
                yes  │              │ no
         ┌───────────▼───────┐  ┌──▼─────────────────┐
         │ A1: Left-factored │  │ B1: Two-token       │
         │ prefix + NFA      │  │ lookahead check,    │
         │ try-all suffixes  │  │ or general NFA      │
         └───────────────────┘  └─────────────────────┘
```

---

## 6. Worked Example

### Grammar

Consider the Calculator grammar's `Float` category with these rules:

```
FloatId     . a:Float  |- "float" "(" a ")"  : Float    (weight 0.0)
IntToFloat  . a:Int    |- "float" "(" a ")"  : Float    (weight 0.3)
BoolToFloat . a:Bool   |- "float" "(" a ")"  : Float    (weight 0.8)
StrToFloat  . a:Str    |- "float" "(" a ")"  : Float    (weight 1.5)
```

### Items layout

Each rule's `RDRuleInfo.items` vector:

```
Index:   [0]       [1]    [2]         [3]
FloatId: "float"   "("    NT(Float)   ")"
IntTo:   "float"   "("    NT(Int)     ")"
BoolTo:  "float"   "("    NT(Bool)    ")"
StrTo:   "float"   "("    NT(Str)     ")"
```

### Step 1: Dispatch grouping

`group_rd_by_dispatch_token()` groups all four rules under `"float"`:

```
"float" → [FloatId, IntToFloat, BoolToFloat, StrToFloat]
```

### Step 2: Inlineable/frame-pushing classification

All four rules' non-terminal arguments (`Float`, `Int`, `Bool`, `Str`) are
*cross-category* (none reference `Float` itself recursively through a
same-category non-terminal in the items, since the NT categories are different
from the perspective of frame-pushing analysis -- except `FloatId` which does
reference `Float`, but this depends on how the split handler classifies it).

For this example, assume all four rules are inlineable (no same-category
non-terminal that requires frame pushing).

### Step 3: Guard evaluation

- `frame_pushing.is_empty()` -- yes (all four are inlineable)
- `inlineable.len() >= 2` -- yes (4 >= 2)

### Step 4: Shared prefix computation

`compute_shared_terminal_prefix()` walks items[1..]:

- **offset 0 (items[1]):** FloatId has `"("`, IntToFloat has `"("`,
  BoolToFloat has `"("`, StrToFloat has `"("`. All match. Push `"("`.
- **offset 1 (items[2]):** FloatId has `NT(Float)`. This is a `NonTerminal`,
  not a `Terminal`. Stop.

Result: `shared = vec!["("]`

### Step 5: Code generation

`skip_count = 1 + 1 = 2` (dispatch token + 1 shared terminal).

Generated code outline:

```rust
Token::KwFloat => {
    *pos += 1;                                               // consume "float"
    expect_token(tokens, pos,
        |t| matches!(t, Token::LParen), "(")?;               // shared "("

    let nfa_saved = *pos;
    let mut nfa_results: Vec<Float> = Vec::new();
    // ... nfa_positions, nfa_weights, nfa_first_err ...

    // FloatId (weight 0.0) -- items[2..]:
    *pos = nfa_saved;
    match (|| -> Result<Float, ParseError> {
        let a = parse_Float(tokens, pos, 0)?;                // items[2]: NT(Float)
        expect_token(tokens, pos,
            |t| matches!(t, Token::RParen), ")")?;            // items[3]: ")"
        Ok(Float::FloatId(Box::new(a)))
    })() { Ok(v) => { ... }, Err(e) => { ... } }

    // IntToFloat (weight 0.3) -- items[2..]:
    *pos = nfa_saved;
    match (|| -> Result<Float, ParseError> {
        let a = parse_Int(tokens, pos, 0)?;                  // items[2]: NT(Int)
        expect_token(tokens, pos,
            |t| matches!(t, Token::RParen), ")")?;            // items[3]: ")"
        Ok(Float::IntToFloat(Box::new(a)))
    })() { Ok(v) => { ... }, Err(e) => { ... } }

    // BoolToFloat (weight 0.8), StrToFloat (weight 1.5) similarly...

    match nfa_results.len() {
        0 => { return Err(...); },
        _ => {
            *pos = nfa_positions[0];
            RUNNING_WEIGHT_FLOAT.with(|cell| cell.set(cell.get() + nfa_weights[0]));
            break 'prefix nfa_results.into_iter().next()
                .expect("nfa_results non-empty");
        },
    }
},
```

### Comparison: before vs after A1

**Before A1** (full NFA try-all):

```rust
Token::KwFloat => {
    let nfa_saved = *pos;

    // FloatId: save, match "float", match "(", parse Float, match ")", restore
    *pos = nfa_saved;
    match (|| -> Result<Float, ParseError> {
        *pos += 1;                                           // "float" (redundant)
        expect_token(tokens, pos, |t| matches!(t, Token::LParen), "(")?;
        let a = parse_Float(tokens, pos, 0)?;
        expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
        Ok(Float::FloatId(Box::new(a)))
    })() { ... }

    // IntToFloat: save, match "float", match "(", parse Int, match ")", restore
    *pos = nfa_saved;
    match (|| -> Result<Float, ParseError> {
        *pos += 1;                                           // "float" (redundant)
        expect_token(tokens, pos, |t| matches!(t, Token::LParen), "(")?;
        let a = parse_Int(tokens, pos, 0)?;
        expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
        Ok(Float::IntToFloat(Box::new(a)))
    })() { ... }

    // ... 2 more alternatives with identical "float" "(" prefix ...
},
```

**After A1** (left-factored):

The `"("` is matched once.  Each alternative's closure starts at `parse_Cat()`,
not at the dispatch token.  The generated code is shorter and avoids 3
redundant `expect_token()` calls for `"("`.

---

## 7. Interaction with B1 (Two-Token Lookahead)

A1 (Grammar Left-Factoring) and B1 (Two-Token Lookahead) are complementary
optimizations that handle different patterns of ambiguity beyond the dispatch
token.  They are evaluated in sequence -- A1 first, then B1 -- and are
mutually exclusive within a single dispatch group.

### When A1 applies (shared prefix leads to non-terminal divergence)

A1 handles the case where multiple rules share a common terminal prefix
beyond the dispatch token, and the divergence point is a **non-terminal**.
Because the FIRST sets of different non-terminal categories often overlap
(e.g., all categories contain `Ident`), the parser cannot disambiguate by
inspecting the next token.  The NFA try-all over the divergent suffix is
the only correct strategy.

**Example:**

```
"float" "(" a:Int  ")"    ← items[2] is NT(Int)
"float" "(" a:Bool ")"    ← items[2] is NT(Bool)
```

Shared prefix: `"("`.  Divergence: non-terminal.  A1 applies.

### When B1 applies (shared prefix leads to terminal divergence)

B1 handles the case where the items[1] position contains **distinct terminals**
across all rules in the group.  In this case, a single look-ahead at
`tokens[*pos + 1]` suffices to select the correct rule deterministically,
with no NFA try-all needed at all.

**Example:**

```
"kw" "(" a:Int ")"        ← items[1] = "("
"kw" "[" a:Int "]"        ← items[1] = "["
"kw" "{" a:Int "}"        ← items[1] = "{"
```

No shared prefix beyond dispatch.  All items[1] are distinct terminals.
B1 applies.

### B1 takes priority when applicable

In the evaluation order within `write_nfa_merged_prefix_arm()`, A1 is
checked first.  However, B1 produces strictly better code when it applies
(deterministic dispatch vs NFA try-all).  The interaction is safe because
the two optimizations target disjoint patterns:

| Property | A1: Left-Factoring | B1: Two-Token Lookahead |
|----------|-------------------|------------------------|
| **Shared terminals at items[1]** | Yes (same terminal) | No (all distinct) |
| **Divergence type** | Non-terminal | Terminal |
| **Resolution strategy** | NFA try-all over suffixes | Nested `match` on second token |
| **Save/restore needed** | Yes (for suffixes) | No |
| **Result** | Best of N alternatives | Single deterministic rule |

When items[1] is the same terminal for all rules, `second_token_lookahead()`
returns `None` (the second tokens are identical, not distinct), and A1 is
reached.  When items[1] terminals are all distinct, A1's
`compute_shared_terminal_prefix()` returns an empty vector (the first
position already diverges), and B1 is reached.

### Evaluation order in codegen

```rust
// trampoline.rs:322-432 (simplified)
if frame_pushing.is_empty() && inlineable.len() >= 2 {
    let shared_terminal_prefix = compute_shared_terminal_prefix(inlineable);
    if !shared_terminal_prefix.is_empty() {
        // A1: left-factored prefix + NFA try-all suffixes
        return;
    }
}

// B1: two-token lookahead (checked after A1 falls through)
if frame_pushing.is_empty() && !config.needs_nfa_spillover {
    if let Some(lookahead) = second_token_lookahead(inlineable) {
        // B1: nested match on second token
        return;
    }
}

// General NFA try-all (no optimization applies)
```

### Impossible overlap

A1 and B1 cannot both apply to the same dispatch group.  If all rules share
items[1] (A1's precondition), then `second_token_lookahead()` finds that the
second-token variants are *not* all distinct (they are all the same) and
returns `None`.  Conversely, if all items[1] are distinct (B1's precondition),
then `compute_shared_terminal_prefix()` finds that items[1] diverges
immediately and returns an empty vector.

---

## 8. Correctness

### Theorem: A1 preserves parse semantics

**Claim:** For any token stream, the A1-generated parser produces the same
result as the unoptimized NFA try-all parser.

**Proof:**

Let `G = {r_1, ..., r_N}` be the set of rules sharing dispatch token `d`,
and let `P = [t_1, ..., t_P]` be the shared terminal prefix (items[1..P+1]).

1. **Prefix determinism.** All rules in `G` have the same sequence of
   terminals `d, t_1, ..., t_P` at positions items[0..P+1].  For any token
   stream, either:
   - (a) The stream matches `d, t_1, ..., t_P` at the current position, in
     which case all rules would successfully consume these terminals, or
   - (b) The stream does not match at some position `i` within the prefix,
     in which case *all* rules would fail at that same position (since the
     terminals are identical).

2. **Early failure equivalence.** In case (b), the unoptimized parser would
   try each rule, fail at position `i` during the terminal match, restore
   `*pos`, and move to the next alternative.  All `N` attempts fail at the
   same point, and `nfa_first_err` captures the error.  The A1-generated
   parser fails at position `i` during the shared `expect_token()` call and
   returns the same error class (`ParseError::UnexpectedToken` or
   `ParseError::UnexpectedEof`) with the same `expected` string.

3. **Suffix equivalence.** In case (a), after consuming the shared prefix,
   `*pos` is at position `P + 1` (relative to the dispatch token).  The
   A1-generated parser then runs the NFA try-all loop over items[P+1..],
   saving and restoring `*pos` from this point.  The unoptimized parser
   saves and restores from position 0 (before the dispatch token), but since
   the shared prefix always succeeds, the effective divergence point is the
   same: position `P + 1`.  The set of alternatives, their order, their
   WFST weights, and the result selection logic are identical.

4. **Weight preservation.** The `nfa_alternative_order()` call receives the
   same rule labels in both versions.  The WFST-sorted order is deterministic
   for a given set of labels and dispatch token.  The first successful result
   (lowest weight) is selected in both cases.

5. **Conclusion.** A1 produces the same parse result and error behavior as the
   unoptimized NFA try-all.  **QED**

### Invariant: `skip_count` correctness

The skip count `1 + shared_terminal_prefix.len()` correctly identifies the
number of items already consumed before the NFA loop begins.  Items 0 through
`skip_count - 1` are consumed by the dispatch match and `expect_token()` calls.
The remaining items `items[skip_count..]` are passed to each alternative's
closure.  Since `compute_shared_terminal_prefix()` only returns terminals that
*all* rules share at the same position, the remaining items are guaranteed to
be the first point of divergence.

---

## 9. Complexity

### Compile-time cost

| Operation | Cost |
|-----------|------|
| `compute_shared_terminal_prefix()` | O(N x P) where N = rules, P = max prefix length |
| `nfa_alternative_order()` | O(N x A) where A = WFST actions for this token |
| Codegen emission | O(N x I) where I = avg items per rule |
| `PrefixTrie` insert (when used) | O(N x I) for N keys of length I |
| `PrefixTrie` shared_prefix_depth | O(P) single traversal |

All operations are linear in the grammar size and execute once during pipeline
compilation.

### Runtime cost

| Operation | Cost (without A1) | Cost (with A1) |
|-----------|-------------------|----------------|
| Shared terminal matches | N x P | P |
| Save/restore cycles | N | N |
| Total terminal matches | N x (1 + P + S) | (1 + P) + N x S |

Where `S` = average number of suffix items per rule.  The saving is
`(N - 1) x P` terminal matches, which for the Calculator Float example
(N = 4, P = 1) eliminates 3 redundant `expect_token()` calls.

### Space cost

No additional runtime allocations.  The generated code is *smaller* with A1
because `P` terminal-matching lines are emitted once instead of `N` times.
For the Calculator Float example, A1 removes 3 x 1 = 3 `expect_token()`
calls from the generated code.

### Generated code volume

| Metric | Without A1 | With A1 | Reduction |
|--------|-----------|---------|-----------|
| `expect_token("(")` calls | N | 1 | N - 1 |
| Closure bodies | N (full) | N (suffix only) | P items each |
| Save/restore | N | N | 0 (same) |

---

## 10. Source References

| File | Lines | Description |
|------|-------|-------------|
| `prattail/src/trampoline.rs` | 190-231 | `compute_shared_terminal_prefix()` -- lockstep walk |
| `prattail/src/trampoline.rs` | 277-423 | `write_nfa_merged_prefix_arm()` -- A1 codegen section |
| `prattail/src/trampoline.rs` | 134-177 | `second_token_lookahead()` -- B1 for comparison |
| `prattail/src/trampoline.rs` | 4196-4291 | A1 unit tests (`compute_shared_terminal_prefix`) |
| `prattail/src/prefix_trie.rs` | 1-221 | `PrefixTrie<K,V>` full implementation and tests |
| `prattail/src/wfst.rs` | 233-253 | `nfa_alternative_order()` -- WFST weight sorting |
| `prattail/src/pratt.rs` | 706-726 | `expect_token()` helper function |
| `prattail/src/recursive.rs` | 14-36 | `RDRuleInfo` struct definition |
| `prattail/src/recursive.rs` | 40-65 | `RDSyntaxItem` enum definition |

### Cross-references

- `theory/wfst/left-factoring.md` -- Formal theory of grammar left-factoring
  and its relation to WFST composition
- `design/wfst/multi-token-lookahead.md` -- B1 two-token lookahead design
  (companion optimization)
- `design/wfst/nfa-disambiguation.md` -- NFA disambiguation architecture
  (Layer 2.5) that A1 optimizes
- `design/wfst/spillover-pruning.md` -- F1 spillover pruning, which applies
  to A1's NFA try-all results when spillover is active
