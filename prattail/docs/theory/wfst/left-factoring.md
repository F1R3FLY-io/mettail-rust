# Grammar Left-Factoring via WFST Prefix Sharing

> **Date:** 2026-03-01

When multiple grammar rules share the same dispatch token and an
identical sequence of subsequent terminals, the parser can walk the
shared prefix once and defer NFA try-all until the first point of
divergence. This is the WFST counterpart of classical LL left-factoring:
the shared prefix corresponds to a determinized execution path in the
transducer, and the divergence point introduces non-determinism that is
resolved by the NFA fallback. The technique is labelled **A1** in the
codebase.

---

## Table of Contents

1. [The Prefix Redundancy Problem](#1-the-prefix-redundancy-problem)
2. [Formal Definitions](#2-formal-definitions)
   - 2.1 [Rule Path Representation](#21-rule-path-representation)
   - 2.2 [Shared Terminal Prefix](#22-shared-terminal-prefix)
   - 2.3 [Divergence Point](#23-divergence-point)
3. [Prefix Trie Construction](#3-prefix-trie-construction)
   - 3.1 [The PrefixTrie<K,V> Data Structure](#31-the-prefixtriekv-data-structure)
   - 3.2 [Trie from Rule Paths](#32-trie-from-rule-paths)
   - 3.3 [Shared Prefix Extraction](#33-shared-prefix-extraction)
4. [Algorithm: Lockstep Prefix Analysis](#4-algorithm-lockstep-prefix-analysis)
   - 4.1 [Preconditions](#41-preconditions)
   - 4.2 [Pseudocode](#42-pseudocode)
   - 4.3 [Codegen Integration](#43-codegen-integration)
5. [Diagram: Factored vs Unfactored Dispatch](#5-diagram-factored-vs-unfactored-dispatch)
6. [Worked Example](#6-worked-example)
7. [Correctness](#7-correctness)
   - 7.1 [Semantic Preservation Theorem](#71-semantic-preservation-theorem)
   - 7.2 [NFA Coverage at Divergence](#72-nfa-coverage-at-divergence)
   - 7.3 [Position State Preservation](#73-position-state-preservation)
8. [Complexity](#8-complexity)
9. [Relationship to Classical Left-Factoring](#9-relationship-to-classical-left-factoring)
10. [Source Reference](#10-source-reference)
11. [Cross-References](#11-cross-references)

---

## 1. The Prefix Redundancy Problem

### 1.1 Phenomenon

Consider a grammar with cast rules that convert between categories.
The Rholang calculator grammar defines three cast rules into `Float`:

```
IntToFloat  :  float ( a:Int  )
BoolToFloat :  float ( a:Bool )
StrToFloat  :  float ( a:Str  )
```

All three rules share the same dispatch token `float` and the same
next terminal `(`. Without left-factoring, the NFA try-all loop saves
the parser position, attempts the full parse path for `IntToFloat`,
restores on failure, saves again, attempts `BoolToFloat`, restores,
saves again, and attempts `StrToFloat`. Each attempt redundantly
re-matches the `(` token.

### 1.2 Cost Model

For *n* rules sharing a dispatch token with a shared terminal prefix
of depth *d*, the unfactored NFA performs up to *n* redundant matches
of those *d* terminals. Each match involves a bounds check
(`*pos < tokens.len()`), a pattern match (`matches!(t, Token::Variant)`),
and a position increment (`*pos += 1`). For *n* = 3 and *d* = 1 this
is only 3 redundant operations, but for deep prefixes the cost scales
as O(n * d) compared to the optimal O(d + n * (len - d)) achieved by
left-factoring.

### 1.3 Code Size

The generated code volume is also affected. Each unfactored NFA
alternative contains its own copy of the shared-prefix matching code.
Left-factoring emits the shared prefix once and factors the NFA
try-all to cover only the divergent suffixes, reducing generated line
count proportionally.

---

## 2. Formal Definitions

### 2.1 Rule Path Representation

A grammar rule R with label L in category C has a concrete syntax
described by a sequence of **syntax items**:

```
R.items = [item₀, item₁, item₂, ..., itemₘ]
```

where each itemᵢ is one of:

| Variant                     | Description                                     |
|:----------------------------|:------------------------------------------------|
| Terminal(t)                 | A fixed token to match (e.g. `(`, `)`, `float`) |
| NonTerminal(cat, param)     | A recursive parse of category *cat*             |
| IdentCapture(param)         | A raw identifier capture                        |
| Binder(param, cat)          | A binder position                               |
| Collection(param, cat, sep) | A delimited collection                          |

By convention, item₀ is the **dispatch token** -- the terminal that
triggers this rule's match arm in the Pratt/trampoline dispatch. The
**suffix** of the rule is items[1..m].

### 2.2 Shared Terminal Prefix

Given a set of rules R = {R₁, R₂, ..., Rₙ} all sharing the same
dispatch token (i.e. R₁.items[0] = R₂.items[0] = ... = Rₙ.items[0]),
the **shared terminal prefix** is the longest sequence of terminals
at positions 1, 2, ..., d such that:

```
for all j in 1..=d, for all i in 1..=n:
  Rᵢ.items[j] = Terminal(tⱼ)      (same terminal for all rules)
```

and either d = min(|R₁.items|, ..., |Rₙ.items|) - 1, or position
d + 1 violates the condition (different terminals, or a non-terminal
in at least one rule).

Formally, let `suffix(R) = R.items[1..]` and define:

```
SharedPrefix(R) = LCP({ suffix(Rᵢ) | Rᵢ ∈ R } restricted to Terminal items)
```

where LCP is the longest common prefix function, and "restricted to
Terminal items" means the walk terminates at the first non-Terminal.

### 2.3 Divergence Point

The **divergence point** is position d + 1 (0-indexed from the
dispatch token), i.e. the first position in the suffix where the rules
differ. At this position, at least one of the following holds:

1. **Different terminals:** Rᵢ.items[d+1] = Terminal(t) and
   Rⱼ.items[d+1] = Terminal(t') with t != t' for some i, j.
2. **Non-terminal encountered:** Rᵢ.items[d+1] is a NonTerminal (or
   another non-Terminal variant) for some i.
3. **Length exhaustion:** Some rule Rᵢ has |Rᵢ.items| <= d + 1.

Beyond the divergence point, the rules' suffixes may share further
structure, but the left-factoring algorithm does not attempt to
discover deeper common subsequences -- it factors only the contiguous
prefix.

---

## 3. Prefix Trie Construction

### 3.1 The PrefixTrie<K,V> Data Structure

PraTTaIL provides a generic prefix trie parameterized over element
type K and value type V:

```rust
pub struct PrefixTrie<K, V> {
    pub value: Option<V>,
    pub children: HashMap<K, PrefixTrie<K, V>>,
}
```

Key operations:

| Method                | Signature                          | Description                                                      |
|:----------------------|:-----------------------------------|:-----------------------------------------------------------------|
| `insert`              | `(&mut self, key, value)`          | Insert a key sequence with a value                               |
| `shared_prefix_depth` | `(&self) -> usize`                 | Depth of the longest single-child chain from root                |
| `shared_prefix`       | `(&self) -> (Vec<&K>, &Self)`      | Walk the single-child chain, return elements and divergence node |
| `descend`             | `(&self, &K) -> Option<&Self>`     | Navigate to a child by element                                   |
| `children`            | `(&self) -> Iterator<(&K, &Self)>` | Iterate over (element, subtrie) pairs                            |
| `count_values`        | `(&self) -> usize`                 | Count total values (leaves) in the trie                          |

The traversal API is inspired by two existing projects:

- **PathMap's Zipper** (`descend_to()`, `child_mask()`, `child_count()`) --
  a functional cursor for navigating hierarchical path structures. PathMap
  uses a zipper pattern where the cursor descends into children while
  maintaining a path context for efficient ascent.

- **liblevenshtein's DictZipper** (`descend()`, `children()`, `path()`) --
  a traversal API for dictionary automata. The DictZipper provides
  depth-first navigation with O(1) child access, used during Levenshtein
  automaton intersection.

Unlike those byte-level tries (PathMap operates on path segments,
liblevenshtein on bytes/chars), PrefixTrie supports generic element
types via `K: Eq + Hash + Clone`, making it suitable for sequences of
`RDSyntaxItem` or any other hashable element.

### 3.2 Trie from Rule Paths

Given rules R = {R₁, ..., Rₙ} sharing a dispatch token, insert each
rule's suffix into the trie:

```
trie = PrefixTrie::new()
for each Rᵢ ∈ R:
    trie.insert(Rᵢ.items[1..], Rᵢ.label)
```

The resulting trie encodes all suffix paths. The shared prefix
corresponds to the single-child chain from the root:

```
Example: IntToFloat, BoolToFloat, StrToFloat

Root
 └── "(" ─────────────────────────── shared prefix (depth 1)
      ├── NonTerminal(Int,a) ──── divergence
      │    └── ")" → IntToFloat
      ├── NonTerminal(Bool,a) ── divergence
      │    └── ")" → BoolToFloat
      └── NonTerminal(Str,a) ─── divergence
           └── ")" → StrToFloat
```

### 3.3 Shared Prefix Extraction

The `shared_prefix()` method walks the single-child chain from the
root, collecting elements, until it reaches a node with more than one
child or a node that holds a value (indicating a rule terminates at
that depth). The walk also terminates if the single child's key is a
non-Terminal item.

The depth of the shared prefix equals the number of elements collected.
If the depth is zero, left-factoring provides no benefit and the
algorithm falls through to standard NFA try-all.

---

## 4. Algorithm: Lockstep Prefix Analysis

### 4.1 Preconditions

Left-factoring (A1) is applied when all of the following hold:

1. **Multiple rules**: The rule group contains at least 2 rules sharing
   the same dispatch token.
2. **All inlineable**: No rule in the group has a same-category
   nonterminal (which would require frame-pushing and cannot be merged
   into save/restore NFA).
3. **Non-empty shared prefix**: `compute_shared_terminal_prefix()`
   returns at least one terminal.

### 4.2 Pseudocode

```
function compute_shared_terminal_prefix(rules: [RDRuleInfo]) -> [String]:
    if |rules| < 2:
        return []

    min_suffix_len = min({ |R.items| - 1 : R ∈ rules })
    if min_suffix_len = 0:
        return []

    shared = []

    for offset in 0..min_suffix_len:
        item_idx = offset + 1          // skip items[0] (dispatch token)

        // Get the terminal at this position in the first rule
        match rules[0].items[item_idx]:
            Terminal(t) -> first_terminal = t
            _           -> break       // non-terminal stops sharing

        // Check all other rules at this position
        all_same = forall R ∈ rules[1..]:
            R.items[item_idx] = Terminal(first_terminal)

        if all_same:
            shared.append(first_terminal)
        else:
            break                      // divergence found

    return shared
```

The algorithm walks items[1..] in lockstep across all rules, checking
at each position whether all rules have the same terminal. It
terminates at the first non-terminal encountered in any rule, the first
position where terminals differ, or when the shortest suffix is
exhausted.

### 4.3 Codegen Integration

The codegen function `write_nfa_merged_prefix_arm()` uses the shared
prefix to generate factored dispatch code:

```
function emit_factored_arm(variant, rules, shared_prefix):
    // 1. Emit the dispatch token match arm
    emit("Token::$variant => {")
    emit("*pos += 1;")                       // consume dispatch token

    // 2. Walk the shared terminal prefix deterministically
    for terminal in shared_prefix:
        emit("expect_token(tokens, pos, |t| matches!(t, Token::$terminal), ...)?;")

    // 3. NFA try-all over divergent suffixes only
    skip_count = 1 + |shared_prefix|
    emit("let nfa_saved = *pos;")
    emit("let mut nfa_results = Vec::new();")

    for (rule, weight) in wfst_ordered(rules):
        emit("*pos = nfa_saved;")
        remaining = rule.items[skip_count..]
        emit("match (|| { ... remaining items ... })() {")
        emit("  Ok(v) => nfa_results.push(v),")
        emit("  Err(e) => ...,")
        emit("}")

    // 4. Select result (first success wins, declaration order = priority)
    emit("match nfa_results.len() { ... }")
    emit("},")
```

The key insight: steps 1-2 are executed exactly once regardless of the
number of alternative rules. Only step 3 involves try-all semantics,
and each alternative in step 3 skips the shared prefix items, parsing
only the divergent suffix.

---

## 5. Diagram: Factored vs Unfactored Dispatch

### 5.1 Unfactored (Standard NFA Try-All)

Each alternative re-matches the full suffix from scratch:

```
Token::Float =>
  ┌─── save pos ──── match "(" ──── parse Int  ──── match ")" ──── IntToFloat ───┐
  │                                                                               │
  ├─── save pos ──── match "(" ──── parse Bool ──── match ")" ──── BoolToFloat ──┤
  │                                                                               │
  └─── save pos ──── match "(" ──── parse Str  ──── match ")" ──── StrToFloat ───┘
                     ▲
                     └── redundant: "(" matched 3 times
```

### 5.2 Factored (A1 Left-Factoring)

The shared prefix is matched once; NFA try-all covers only the
divergent portion:

```
Token::Float =>
  match "(" ─────────────────── (shared prefix, matched once)
       │
       ├─── save pos ──── parse Int  ──── match ")" ──── IntToFloat  ──┐
       │                                                                │
       ├─── save pos ──── parse Bool ──── match ")" ──── BoolToFloat ──┤
       │                                                                │
       └─── save pos ──── parse Str  ──── match ")" ──── StrToFloat  ──┘
                          ▲
                          └── NFA try-all starts here (divergence point)
```

The shared `(` is consumed deterministically before the NFA try-all
begins. Each NFA alternative only needs to parse the divergent suffix
(`Int/Bool/Str` followed by `)`), saving one redundant `(` match per
alternative.

### 5.3 WFST View

In WFST terms, left-factoring determinizes the shared prefix into a
single execution path:

```
                 "("        NonTerminal(Int)         ")"
  ┌───────► q₁ ──────► q₂ ──────────────────► q₃ ──────► q₄ [IntToFloat]
  │                     ┊
  │                     ┊    NonTerminal(Bool)        ")"
  │                     ┊───────────────────────► q₅ ──────► q₆ [BoolToFloat]
  │                     ┊
 q₀ (start)             ┊    NonTerminal(Str)         ")"
  │                     └───────────────────────► q₇ ──────► q₈ [StrToFloat]
  │
  │   (unfactored: 3 separate "(" arcs from q₀)
  │   (factored:   1 shared "(" arc, then 3 arcs from q₂)
```

The factored WFST has one fewer state per shared prefix terminal. The
transition from q₁ to q₂ (matching `(`) is traversed once rather than
three times. The dotted lines (┊) from q₂ represent the NFA
non-determinism at the divergence point.

---

## 6. Worked Example

### 6.1 Grammar

The Rholang calculator grammar defines these rules in category `Float`:

```
rule IntToFloat  : Float = float ( a:Int  ) => Float::Cast(Box::new(a))
rule BoolToFloat : Float = float ( a:Bool ) => Float::Cast(Box::new(a))
rule StrToFloat  : Float = float ( a:Str  ) => Float::Cast(Box::new(a))
```

### 6.2 RDRuleInfo Representation

Each rule is translated to an `RDRuleInfo` with:

```
IntToFloat.items  = [Terminal("float"), Terminal("("), NonTerminal(Int,"a"),  Terminal(")")]
BoolToFloat.items = [Terminal("float"), Terminal("("), NonTerminal(Bool,"a"), Terminal(")")]
StrToFloat.items  = [Terminal("float"), Terminal("("), NonTerminal(Str,"a"),  Terminal(")")]
```

### 6.3 Prefix Analysis

**Step 1:** Group by dispatch token. All three rules have items[0] =
Terminal("float"), so they form one group.

**Step 2:** Compute shared terminal prefix. Walk items[1..] in
lockstep:

| Offset | item_idx | IntToFloat       | BoolToFloat       | StrToFloat       | Same? |
|:------:|:--------:|:-----------------|:------------------|:-----------------|:-----:|
|   0    |    1     | Terminal("(")    | Terminal("(")     | Terminal("(")    |  Yes  |
|   1    |    2     | NonTerminal(Int) | NonTerminal(Bool) | NonTerminal(Str) | Stop  |

**Result:** `shared_terminal_prefix = ["("]`, depth = 1.

**Divergence point:** Position 2 (0-indexed from items[0]), where the
rules have different NonTerminals.

### 6.4 Generated Code (Simplified)

```rust
Token::Float => {
    *pos += 1;  // consume "float"

    // ── A1: shared prefix (depth 1) ──
    expect_token(tokens, pos, |t| matches!(t, Token::LParen), "(")?;

    // ── NFA try-all over divergent suffixes ──
    let nfa_saved = *pos;
    let mut nfa_results: Vec<Float> = Vec::new();
    // ... (nfa_weights, nfa_positions, nfa_first_err)

    // Alternative 1: IntToFloat (suffix = [NonTerminal(Int), Terminal(")")])
    *pos = nfa_saved;
    match (|| -> Result<Float, ParseError> {
        let a = parse_Int(tokens, pos, 0)?;
        expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
        Ok(Float::Cast(Box::new(a)))
    })() {
        Ok(v) => { nfa_results.push(v); /* ... */ },
        Err(e) => { /* ... */ },
    }

    // Alternative 2: BoolToFloat (suffix = [NonTerminal(Bool), Terminal(")")])
    *pos = nfa_saved;
    match (|| -> Result<Float, ParseError> {
        let a = parse_Bool(tokens, pos, 0)?;
        expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
        Ok(Float::Cast(Box::new(a)))
    })() {
        Ok(v) => { nfa_results.push(v); /* ... */ },
        Err(e) => { /* ... */ },
    }

    // Alternative 3: StrToFloat (suffix = [NonTerminal(Str), Terminal(")")])
    *pos = nfa_saved;
    match (|| -> Result<Float, ParseError> {
        let a = parse_Str(tokens, pos, 0)?;
        expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
        Ok(Float::Cast(Box::new(a)))
    })() {
        Ok(v) => { nfa_results.push(v); /* ... */ },
        Err(e) => { /* ... */ },
    }

    // Select first success
    match nfa_results.len() {
        0 => return Err(nfa_first_err.unwrap_or_else(|| /* ... */)),
        _ => { *pos = nfa_positions[0]; break 'prefix nfa_results.into_iter().next().expect("non-empty"); },
    }
},
```

The critical difference from unfactored code: the `expect_token(..., Token::LParen, "(")` call appears exactly once, not three times. Each NFA alternative's closure starts parsing from the divergence point (after `(` has been consumed), skipping `skip_count = 1 + 1 = 2` items from the original rule.

### 6.5 Input Trace

For input `float(42)` where `42` is an integer literal:

```
Tokens:  Float  LParen  Integer(42)  RParen
         pos=0  pos=1   pos=2        pos=3
```

| Step | Action                      | pos | Note                         |
|:----:|:----------------------------|:---:|:-----------------------------|
|  1   | Match Token::Float          |  0  | Dispatch token               |
|  2   | *pos += 1                   |  1  | Consume dispatch token       |
|  3   | expect_token LParen         |  1  | Shared prefix (A1)           |
|  4   | (LParen matched, *pos += 1) |  2  | Shared prefix consumed       |
|  5   | nfa_saved = 2               |  2  | Save for NFA try-all         |
|  6   | Try IntToFloat: parse_Int   |  2  | Parses Integer(42), pos -> 3 |
|  7   | expect_token RParen         |  3  | Matches, pos -> 4            |
|  8   | Ok(Float::Cast(Int(42)))    |  4  | First success                |
|  9   | Return result               |  4  | Skip remaining alternatives  |

Without A1, steps 3-4 would be repeated inside each alternative's
closure, adding 2 redundant operations (for this example with depth 1
and 3 alternatives, that is 2 wasted expect_token calls).

---

## 7. Correctness

### 7.1 Semantic Preservation Theorem

**Theorem.** For any input token sequence *T*, left-factored dispatch
produces the same parse result as unfactored NFA try-all. That is,
factoring is semantics-preserving.

**Proof.** Let R = {R₁, ..., Rₙ} be the rules in a dispatch group with
shared terminal prefix P = [p₁, p₂, ..., p_d].

**Case 1: Shared prefix fails.** If any terminal pⱼ in the shared
prefix does not match the input at the expected position, the factored
code returns an error via `expect_token()`. In the unfactored code,
every alternative would independently fail at the same terminal pⱼ
(since all rules contain pⱼ at the same position). All alternatives
return errors, and the NFA try-all loop also returns an error. Both
paths produce the same error result.

**Case 2: Shared prefix succeeds, divergent suffixes tried.** If all
terminals in P match, the factored code advances the position past P
and begins NFA try-all over the suffixes items[d+1..]. The unfactored
code would advance the position past each pⱼ independently within
each alternative's closure and then parse the remaining items. Since
the position advancement through P is deterministic (each pⱼ is a
fixed terminal, not a non-terminal), the position at the start of the
divergent portion is identical in both cases: `pos = initial_pos + 1
(dispatch) + d (shared prefix)`.

Each alternative's closure in the factored code parses exactly
items[skip_count..] = items[d+1..], which is precisely the suffix that
remains after the shared prefix in the unfactored code. Therefore, the
parse attempts are semantically identical, and the NFA result
selection (first success in declaration order) produces the same output.

**Case 3: Empty shared prefix.** If d = 0, left-factoring is not
applied. The codegen falls through to standard NFA try-all, which is
trivially equivalent to itself. []

### 7.2 NFA Coverage at Divergence

**Theorem.** The NFA try-all at the divergence point covers all
alternative rules that were covered by the unfactored NFA.

**Proof.** The factored code iterates over all rules in the group
(ordered by WFST weight if available, otherwise by declaration order).
Each rule Rᵢ produces one NFA alternative closure that parses
Rᵢ.items[skip_count..]. Since skip_count = 1 + d and all rules share
the same items[0..=d], the factored suffix Rᵢ.items[d+1..] is the
complement of the shared prefix within each rule's item sequence.

No rule is omitted: the for loop iterates over all elements of the
ordered rule list. No spurious rule is added: the ordered list contains
only rules from the original dispatch group. Therefore, the set of
alternatives tried is exactly {R₁, ..., Rₙ}, the same as in the
unfactored case. []

### 7.3 Position State Preservation

**Theorem.** The parser position state at the start of each divergent
NFA alternative is correctly preserved via `nfa_saved`.

**Proof.** After consuming the shared prefix, the factored code records
`nfa_saved = *pos`. Before each alternative's closure, it restores
`*pos = nfa_saved`. This is the standard NFA save/restore pattern,
identical to the unfactored code's save/restore, except that `nfa_saved`
is set after the shared prefix rather than before it. Since the shared
prefix has already been consumed (and the consumed terminals are
identical for all alternatives), the divergent parse must begin at
`nfa_saved` in all cases.

Furthermore, if an alternative fails, `*pos` is restored to `nfa_saved`
before the next alternative begins, ensuring no partial position
advancement from a failed attempt leaks into the next attempt. []

---

## 8. Complexity

### 8.1 Construction Cost

Computing the shared terminal prefix over *n* rules with maximum suffix
length *m* takes:

```
O(n * d)    where d = min(m, depth of shared prefix)
```

In the worst case (all rules share the full suffix except the last
element), d = m - 1, giving O(n * m). Since this analysis runs at
compile time during codegen, the cost is amortized and does not affect
runtime performance.

The total construction cost over all dispatch groups is:

```
O(sum over all groups G of |G| * |items(G)|) = O(total rule items)
```

This is linear in the total size of the grammar specification.

### 8.2 Runtime Dispatch Improvement

Without left-factoring, the NFA try-all for a group of *n* rules with
shared prefix depth *d* performs up to:

```
Unfactored: n * (d + sᵢ) token matches   (sᵢ = divergent suffix length of rule i)
```

With left-factoring:

```
Factored: d + n * sᵢ token matches
```

The improvement is:

```
delta = (n - 1) * d token matches saved
```

For the calculator's Float cast rules (n = 3, d = 1): delta = 2 token
matches saved per dispatch. For deeply nested syntax with d = 3 and
n = 5: delta = 12 token matches saved.

### 8.3 Code Size Reduction

Each shared terminal generates one `expect_token()` call in the
factored code versus *n* calls in the unfactored code. The code size
reduction per dispatch group is:

```
delta_code = (n - 1) * d * (size of expect_token call)
```

For typical grammars this is modest but measurable in generated output
volume.

---

## 9. Relationship to Classical Left-Factoring

### 9.1 LL Left-Factoring

In classical LL(1) parsing theory (Aho, Sethi, Ullman 1986), left-
factoring transforms a grammar with common prefixes:

```
A  ->  alpha beta₁ | alpha beta₂
```

into:

```
A  ->  alpha A'
A' ->  beta₁ | beta₂
```

This eliminates the common prefix alpha from the prediction set,
making the grammar suitable for top-down predictive parsing. The
transformation is purely syntactic: it introduces a new non-terminal
A' and restructures the productions.

### 9.2 PraTTaIL's Approach

PraTTaIL's left-factoring is analogous but operates at the codegen
level rather than the grammar level:

| Aspect           | Classical LL           | PraTTaIL A1                      |
|:-----------------|:-----------------------|:---------------------------------|
| Level            | Grammar transformation | Code generation                  |
| Input            | Productions (CFG)      | RDRuleInfo (syntax items)        |
| Output           | Factored grammar       | Factored dispatch code           |
| New non-terminal | A' introduced          | None (NFA closure at divergence) |
| Determinism      | LL(1) required after   | NFA try-all at divergence        |
| Scope            | All productions        | Same-dispatch-token groups       |

The key difference: classical left-factoring requires the factored
grammar to be LL(1)-parseable after transformation. PraTTaIL does not
impose this requirement -- at the divergence point, it falls back to
NFA try-all (or two-token lookahead via B1 if applicable), which can
handle arbitrary ambiguity. This makes PraTTaIL's left-factoring
strictly more general than LL left-factoring.

### 9.3 WFST Determinization Perspective

In WFST theory, the classical determinization algorithm (Mohri 1997)
transforms a non-deterministic WFST into a deterministic one by merging
states that are reachable via the same input prefix. PraTTaIL's prefix
sharing is a restricted form of this: it determinizes only the shared
terminal prefix of a dispatch group, leaving the divergent suffix as
non-deterministic (NFA). Full WFST determinization would also merge
states in the divergent portion where possible, at the cost of
potentially exponential state blowup.

PraTTaIL's partial determinization is thus a pragmatic middle ground:
it captures the most common and most beneficial case (shared initial
terminals) without risking the worst-case complexity of full
determinization.

---

## 10. Source Reference

| Symbol / Function                   | Location                           |
|:------------------------------------|:-----------------------------------|
| `compute_shared_terminal_prefix()`  | `prattail/src/trampoline.rs`       |
| `write_nfa_merged_prefix_arm()`     | `prattail/src/trampoline.rs`       |
| `PrefixTrie<K, V>`                  | `prattail/src/prefix_trie.rs`      |
| `PrefixTrie::shared_prefix()`       | `prattail/src/prefix_trie.rs`      |
| `PrefixTrie::shared_prefix_depth()` | `prattail/src/prefix_trie.rs`      |
| `PrefixTrie::insert()`              | `prattail/src/prefix_trie.rs`      |
| `PrefixTrie::descend()`             | `prattail/src/prefix_trie.rs`      |
| `RDRuleInfo`                        | `prattail/src/recursive.rs`        |
| `RDSyntaxItem`                      | `prattail/src/recursive.rs`        |
| `split_rd_handler()`                | `prattail/src/trampoline.rs`       |
| `terminal_to_variant_name()`        | `prattail/src/automata/codegen.rs` |

**Tests (in `trampoline.rs`):**

| Test                                                  | What it verifies                                |
|:------------------------------------------------------|:------------------------------------------------|
| `test_shared_prefix_two_rules_shared_second_terminal` | `float ( a:Int )` / `float ( a:Bool )` -> ["("] |
| `test_shared_prefix_no_shared_terminals`              | Immediate divergence -> []                      |
| `test_shared_prefix_nonterminal_at_second_position`   | NonTerminal stops sharing -> []                 |
| `test_shared_prefix_deep_sharing`                     | 3 shared terminals -> ["(", "[", "{"]           |
| `test_shared_prefix_single_rule`                      | Single rule -> [] (no factoring needed)         |

**Tests (in `prefix_trie.rs`):**

| Test                                     | What it verifies                         |
|:-----------------------------------------|:-----------------------------------------|
| `test_empty_trie`                        | Empty trie properties                    |
| `test_single_key`                        | Single key: depth = key length           |
| `test_shared_prefix_two_keys`            | Two keys: shared depth = common prefix   |
| `test_no_shared_prefix`                  | Immediate divergence: depth = 0          |
| `test_descend`                           | Zipper-style navigation                  |
| `test_children_iteration`                | DictZipper-style child enumeration       |
| `test_prefix_value_at_intermediate_node` | Value at non-leaf stops prefix chain     |
| `test_with_integer_keys`                 | Generic key type (integers, not strings) |

---

## 11. Cross-References

- [Grammar Left-Factoring Design](../../design/wfst/grammar-left-factoring.md) --
  implementation decisions and codegen architecture
- [Multi-Token Lookahead](multi-token-lookahead.md) --
  B1 two-token lookahead, complementary to A1 prefix sharing
- [Weighted Automata](weighted-automata.md) --
  WFST structure and prediction pipeline
- [Token Lattices](token-lattices.md) --
  lattice representation for ambiguous tokenizations
- [Semirings](semirings.md) --
  weight algebra used in WFST-ordered alternative ranking

---

**References:**

1. **Aho, A. V., Sethi, R., & Ullman, J. D.** (1986). *Compilers:
   Principles, Techniques, and Tools.* Addison-Wesley. Chapter 4.3:
   Left factoring.

2. **Mohri, M.** (1997). Finite-state transducers in language and
   speech processing. *Computational Linguistics*, 23(2), 269-311.
   Section 4: Determinization.

3. **Mohri, M., Pereira, F., & Riley, M.** (2008). Speech recognition
   with weighted finite-state transducers. In *Springer Handbook of
   Speech Processing* (pp. 559-584). Springer.

4. **Grune, D., & Jacobs, C. J. H.** (2008). *Parsing Techniques: A
   Practical Guide.* Springer. Chapter 8.2.4: Left factoring for
   LL(1).
