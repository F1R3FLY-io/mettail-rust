# Layer 1: Lexical Disambiguation

Lexical disambiguation is the first layer in PraTTaIL's six-layer model. It
operates on raw characters and produces an unambiguous token stream. Every
subsequent layer depends on this layer having already resolved all token-level
ambiguity.

**Source files:**
- `prattail/src/automata/mod.rs` -- Token kinds and priority system
- `prattail/src/automata/nfa.rs` -- DAFSA construction, keyword trie
- `prattail/src/automata/codegen.rs` -- Maximal munch loop, DFA compression
- `prattail/src/automata/partition.rs` -- Equivalence class computation

**Cross-references:**
- [theory/finite-automata.md](../../theory/finite-automata.md) §8 (Maximal Munch), §9 (Priority)
- [design/automata-pipeline.md](../automata-pipeline.md) §3-8

---

## 1. Three Sources of Lexical Ambiguity

When converting characters to tokens, three classes of ambiguity arise:

### 1.1 Shared Prefixes

Operators like `=` and `==` share the character `=`. After reading one `=`, the
lexer does not yet know whether it has a complete token or the first half of a
two-character token.

```
Input: = = 3
       ↑
       Is this `=` (assignment) or the start of `==` (equality)?
```

Similarly, `!` and `!=` share `!`, and `>` and `>=` share `>`.

### 1.2 Keyword/Identifier Overlap

Keywords like `true` and `false` are spelled with exactly the same characters as
identifiers. After reading `t-r-u-e`, the lexer must decide: is this the boolean
keyword `true` or an identifier that happens to be spelled "true"?

```
Input: true
       ↑↑↑↑
       Keyword Boolean(true) or Ident("true")?
```

The situation is more subtle for **prefix overlaps**: `trueish` starts with `true`
but is clearly an identifier, not a keyword followed by `ish`.

### 1.3 Token Boundaries

Even without shared prefixes, the lexer must decide where one token ends and the
next begins. Consider `===`:

```
Input: ===
       ↑↑↑
       Is this `==` + `=`?  Or `=` + `==`?  Or `=` + `=` + `=`?
```

Token boundary ambiguity interacts with both shared prefixes and keyword overlap.

---

## 2. Mechanism 1: DFA State Merging (DAFSA Prefix Sharing)

PraTTaIL builds a **Directed Acyclic Finite State Automaton** (DAFSA) that merges
common prefixes of keywords and operators into shared state paths. This is the
structural foundation that makes the other two mechanisms efficient.

### 2.1 The DAFSA Construction Algorithm

The lexer's keyword/operator trie is built using the **Daciuk incremental
algorithm** (`nfa.rs`, `build_keyword_trie()`, lines 222-310):

1. **Sort** all terminals lexicographically (required by Daciuk's algorithm)
2. For each terminal, in sorted order:
   a. **Freeze** suffixes from the previous insertion by calling
      `freeze_suffixes()` (lines 180-203) -- this merges equivalent suffix
      states into canonical representatives
   b. **Walk** the common prefix with the previous terminal (reuse existing states)
   c. **Extend** with new states for the divergent suffix
   d. **Mark** the final state as accepting with the terminal's `TokenKind`
3. After all terminals: freeze all remaining path states

### 2.2 Suffix Merging

Two states are **equivalent** (and can be merged) when they have identical
`NodeSignature`s (`nfa.rs`, lines 75-109):

- Same accept token (`Option<TokenKind>`)
- Same set of outgoing transitions (sorted by byte value)

The `freeze_suffixes()` function walks backward from the deepest path entry,
computes each state's signature, and either redirects to an existing canonical
state or registers the state as the new canonical representative.

### 2.3 Worked Example: `{=, ==, !=}`

```
             ┌───[=]───→ S1 (accept: Eq)
             │             │
   S0 ──────┤             └──[=]──→ S2 (accept: EqEq)
   (start)   │
             └───[!]───→ S3
                           │
                           └──[=]──→ S4 (accept: BangEq)
```

**Prefix sharing:** `=` and `==` share the path from S0 to S1. The `=` in `!=`
starts a separate path because `!` differs from `=` at position 0.

**State S1 is both accepting and non-final:** It accepts `Eq` but also has an
outgoing transition on `=`. This is where maximal munch (§3) becomes critical --
after reaching S1, the lexer does not immediately emit `Eq` but continues to see
if `==` is possible.

### 2.4 Character-Class Fragments

In addition to the keyword/operator DAFSA, the NFA includes **character-class
fragments** for:

- **Identifiers** (`nfa.rs`, lines 435-451): `[a-zA-Z_][a-zA-Z0-9_]*`
- **Integers** (`nfa.rs`, lines 458-467): `[0-9]+`
- **Floats** (`nfa.rs`, lines 480-524): `[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?`
- **String literals** (`nfa.rs`, lines 531-552): `"[^"]*"`

All fragments are epsilon-linked from the global start state, creating parallel
recognition paths. The NFA is then converted to a DFA via subset construction,
which determinizes all overlapping paths.

---

## 3. Mechanism 2: Maximal Munch (Longest Match)

Maximal munch is the rule that when multiple token interpretations are possible,
the **longest valid prefix** wins. PraTTaIL implements this via explicit
`last_accept` tracking in the DFA driver loop.

### 3.1 The `last_accept` Tracking Algorithm

The generated lexer (`codegen.rs`, lines 369-395 for direct-coded, lines 925-951
for table-driven) maintains:

```
last_accept: Option<(state, position, line, column)>
```

The core loop:

```
1. Initialize last_accept = None (or accept at state 0 if start is accepting)
2. While input remains:
   a. Look up next state via DFA transition
   b. If next state is DEAD (u32::MAX): STOP -- backtrack to last_accept
   c. Advance position
   d. If current state is accepting: update last_accept
3. Emit token from last_accept position (or error if None)
```

**The key insight:** The lexer does not stop at the first accepting state. It
continues consuming input until the DFA reaches a dead state, then backtracks to
the **last** accepting state it passed through. This guarantees the longest valid
prefix is matched.

### 3.2 Worked Example: `"==="` → `EqEq` + `Eq`

```
Position:  0   1   2
Input:     =   =   =
State:     S0 → S1 → S2 → DEAD

Pass 1:
  pos=0: S0 --[=]--> S1 (accepting: Eq)       last_accept = (S1, pos=1)
  pos=1: S1 --[=]--> S2 (accepting: EqEq)     last_accept = (S2, pos=2)
  pos=2: S2 --[=]--> DEAD                     backtrack to pos=2
  Emit: EqEq (positions 0..2)

Pass 2:
  pos=2: S0 --[=]--> S1 (accepting: Eq)       last_accept = (S1, pos=3)
  pos=3: end of input
  Emit: Eq (positions 2..3)

Result: [EqEq, Eq]
```

Without maximal munch, the lexer might stop at S1 and emit `[Eq, Eq, Eq]`, which
is the wrong tokenization.

### 3.3 Worked Example: `"error_handler"` → `Ident`

Even if the grammar includes a keyword `error`, maximal munch ensures that
`error_handler` is tokenized as a single identifier:

```
Position:  0  1  2  3  4  5  ...  12  13
Input:     e  r  r  o  r  _  ...  e   r

Pass 1:
  pos=0..4: Walk "error" through keyword trie
            State S_error (accepting: keyword "error")
            last_accept = (S_error, pos=5)
  pos=5:    S_error --[_]--> identifier continuation state
            Still valid! Identifier pattern [a-zA-Z0-9_]* continues
  pos=5..13: Continue through identifier pattern
             Each position updates last_accept (accepting: Ident)
  pos=14:   end of input
  Emit: Ident("error_handler")

Result: [Ident("error_handler")]   (NOT: [Keyword("error"), Ident("_handler")])
```

Maximal munch beats keyword matching here because the identifier pattern
continues past where the keyword ends.

---

## 4. Mechanism 3: Token Priority

When maximal munch produces a tie -- two patterns match the **same** longest
prefix -- **token priority** breaks the tie. Higher priority tokens win.

### 4.1 The Priority Table

PraTTaIL assigns priority values to each `TokenKind` (`mod.rs`, lines 55-71):

| TokenKind | Priority | Rationale |
|-----------|----------|-----------|
| `Eof` | 0 | Sentinel, never competes |
| `Ident` | 1 | Lowest: loses to everything |
| `Integer` | 2 | Numeric literals |
| `Float` | 3 | Float > Integer (longer match usually, but priority ensures correctness) |
| `StringLit` | 2 | String literals |
| `Dollar` | 5 | Dollar syntax |
| `DoubleDollar` | 6 | Double-dollar beats single-dollar |
| `True` / `False` | 10 | Keywords: beat identifiers |
| `Fixed(...)` | 10 | Operators/keywords: beat identifiers |

### 4.2 The `set_or_upgrade_accept()` Function

When multiple patterns reach the same DFA state (after subset construction merges
NFA states), their accept tokens may conflict. The function
`set_or_upgrade_accept()` (`nfa.rs`, lines 138-151) resolves this:

```
if state has no accept token:
    set accept = new_token
else if new_token.priority() > existing.priority():
    upgrade accept = new_token
else:
    keep existing (higher priority already installed)
```

This happens at NFA construction time, so the generated DFA already has the
correct accept token baked in.

### 4.3 Worked Example: `"true"` → `Boolean(true)`

The string `true` is matched by both the identifier pattern and the keyword `true`:

```
Input: t r u e (followed by space or operator)

Both patterns match at position 4 (same length -- maximal munch is a tie).
  Ident("true")     has priority 1
  Boolean(true)      has priority 10

Priority resolution: Boolean(true) wins.
Result: [Boolean(true)]
```

### 4.4 Priority + Maximal Munch Interaction

The two mechanisms compose cleanly. Maximal munch applies first (longer match
wins), and priority applies only when matches are the same length.

**`"trueish"` → `Ident("trueish")`:**
```
Input: t r u e i s h

Keyword "true" matches at position 4.
Identifier matches at position 7 (longer).
Maximal munch: Ident wins (7 > 4), priority is irrelevant.

Result: [Ident("trueish")]
```

**`"true "` → `Boolean(true)` + whitespace:**
```
Input: t r u e (space)

Keyword "true" matches at position 4.
Identifier "true" also matches at position 4 (space is not [a-zA-Z0-9_]).
Same length: priority breaks tie.
Boolean(true) priority 10 > Ident priority 1.

Result: [Boolean(true)]
```

**`"true("` → `Boolean(true)` + `(`:**
```
Input: t r u e (

Same reasoning as above: `(` terminates both patterns at position 4.
Boolean(true) wins on priority.

Result: [Boolean(true), Fixed(LParen)]
```

### 4.5 The Composition Rule

```
  ┌────────────────────────────────────────────────────┐
  │  1. Compare match lengths                          │
  │     → Longer match ALWAYS wins (maximal munch)     │
  │                                                    │
  │  2. If same length, compare priorities             │
  │     → Higher priority wins                         │
  │                                                    │
  │  3. If same length AND same priority               │
  │     → First pattern in grammar order wins          │
  │       (deterministic but grammar-dependent)        │
  └────────────────────────────────────────────────────┘
```

---

## 5. Alphabet Equivalence Classes

After NFA→DFA conversion, PraTTaIL partitions the 256-byte alphabet into
**equivalence classes** (`partition.rs`, lines 28-92). This preserves all
disambiguation semantics while dramatically compressing the DFA transition table.

### 5.1 Motivation

A raw DFA transition table has `|states| × 256` entries, most of which are
identical. For example, all lowercase letters `a-z` (except those starting
keywords) behave identically in every state. Equivalence classes group such
bytes together.

### 5.2 The Algorithm

1. **Build byte signatures** (lines 44-62): For each byte 0-255, compute which
   DFA states it transitions from and to. Two bytes with identical signatures
   (same transitions in every state) are equivalent.

2. **Group by signature** (lines 64-85): Assign a class ID (0, 1, 2, ...) to
   each equivalence group.

3. **Output**:
   - `byte_to_class[256]`: Dense lookup mapping each byte to its class ID
   - `num_classes`: Total number of distinct classes

### 5.3 Typical Compression

Real grammars produce **12-18 equivalence classes** (vs 256 raw bytes), yielding
a **15-20x compression factor** on the transition table.

```
Example equivalence classes for a typical grammar:

  Class 0: [a-df-su-z]   (lowercase letters, not starting any keyword)
  Class 1: [t]            (starts "true")
  Class 2: [e]            (continuation of "true", starts other keywords)
  Class 3: [0-9]          (digits)
  Class 4: [=]            (starts =, ==)
  Class 5: [!]            (starts !, !=)
  Class 6: [ \t\r]        (whitespace, not newline)
  Class 7: [\n]           (newline -- tracked separately for line counting)
  Class 8: [_]            (identifier continuation, not letter/digit)
  Class 9: [(]            (structural delimiter)
  Class 10: [)]           (structural delimiter)
  ...etc
```

### 5.4 Why Equivalence Classes Preserve Disambiguation

Equivalence classes are a **lossless** transformation: two bytes are grouped
together **only if** they produce identical transitions in every DFA state. This
means:

- Maximal munch reaches the same accepting states regardless of which class
  representative is used
- Priority resolution operates on the same accept tokens
- The three-way composition (§4.5) produces identical results

No disambiguation decision is altered by equivalence class compression.

---

## 6. DFA Compression Strategies

PraTTaIL selects between three code generation strategies for the DFA transition
table (`codegen.rs`, lines 72-818):

### 6.1 Direct-Coded (≤30 states)

Each DFA state becomes a `match` arm. Transitions are inline. Used for small
grammars where code size is not a concern.

```
Threshold: DIRECT_CODED_THRESHOLD = 30 states  (codegen.rs, line 23)
```

### 6.2 Comb (Row Displacement) Compression

For larger DFAs, sparse rows are packed into shared arrays using greedy
offset selection (`codegen.rs`, lines 594-695):

```
Lookup: idx = BASE[state] + class_id
        if CHECK[idx] == state then NEXT[idx] else DEFAULT[state]
```

Rows are sorted densest-first for better packing.

### 6.3 Bitmap Compression

When `num_classes ≤ 32`, each state's transitions fit in a `u32` bitmap
(`codegen.rs`, lines 697-732):

```
Lookup: if BITMAPS[state] & (1 << class) == 0 → DEAD
        else index = popcount(BITMAPS[state] & ((1 << class) - 1))
             TARGETS[OFFSETS[state] + index]
```

Uses hardware `POPCNT` for O(1) lookup with excellent cache locality.

### 6.4 Strategy Selection

The generated lexer automatically selects the most compact strategy
(`codegen.rs`, lines 800-818):

```
  ┌──────────────────────────────────┐
  │  states ≤ 30?                    │
  │    YES → Direct-coded            │
  │    NO  → Compare comb vs bitmap  │
  │          (if classes ≤ 32)       │
  │          → Smaller total wins    │
  └──────────────────────────────────┘
```

All three strategies produce identical tokenization -- they differ only in code
size and cache behavior, not in disambiguation semantics.

---

## 7. What Lexical Disambiguation Cannot Resolve

Lexical disambiguation handles all **token-level** ambiguity, but structural
ambiguity remains:

- **Which parse rule applies?** The token `(` could start a grouping expression,
  a function call's argument list, or a tuple. The lexer emits `LParen`; Layer 2
  (parse prediction) decides which rule to use.

- **Which operator binds tighter?** The token stream `[Int(1), Plus, Int(2),
  Star, Int(3)]` is unambiguous at the token level, but `1+2*3` has two parse
  trees. Layer 3 (operator precedence) resolves this.

- **Which type category?** The token `Ident("x")` could be a variable in any
  type category (`Int`, `Bool`, `Str`). Layer 4 (cross-category resolution)
  determines which.

The lexer's job is complete once every character in the input is assigned to
exactly one token with exactly one `TokenKind`. All further disambiguation
operates on this token stream.

---

## 8. Summary

```
  Characters → DAFSA + DFA →  Maximal Munch  →  Priority  →  Token Stream
               (prefix       (longest match     (same-length   (unambiguous)
                sharing)       wins)              tiebreaker)
```

| Mechanism | Ambiguity Resolved | Implementation |
|-----------|-------------------|----------------|
| DAFSA prefix sharing | Structural: how operators relate | `build_keyword_trie()`, `freeze_suffixes()` |
| Maximal munch | Token boundaries: where tokens end | `last_accept` tracking in DFA loop |
| Token priority | Token identity: keyword vs identifier | `set_or_upgrade_accept()`, `priority()` method |
| Equivalence classes | (Preserves above, compresses DFA) | `partition.rs`, `byte_to_class[]` |

**Layer 1 output → Layer 2 input:** An unambiguous sequence of `Token<'a>` values,
each with a known `TokenKind`, source position, and (for data-carrying variants)
a zero-copy `&'a str` slice into the input buffer.
