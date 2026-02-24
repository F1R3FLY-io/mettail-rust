# PraTTaIL: Automata Pipeline (Lexer Generation)

**Date:** 2026-02-14 (updated 2026-02-17)

---

## Table of Contents

1. [Why Automata Instead of Hand-Coded Matching](#1-why-automata-instead-of-hand-coded-matching)
2. [Pipeline Overview](#2-pipeline-overview)
3. [Thompson's Construction](#3-thompsons-construction)
4. [Aho-Corasick Keyword Trie](#4-aho-corasick-keyword-trie)
5. [Alphabet Partitioning (Equivalence Classes)](#5-alphabet-partitioning-equivalence-classes)
6. [Subset Construction (NFA to DFA)](#6-subset-construction-nfa-to-dfa)
7. [Hopcroft's DFA Minimization](#7-hopcrofts-dfa-minimization)
8. [Code Generation: String-Based, Direct-Coded vs Table-Driven](#8-code-generation-string-based-direct-coded-vs-table-driven)
9. [Worked Example: RhoCalc Terminal Set](#9-worked-example-rhocalc-terminal-set)

---

## 1. Why Automata Instead of Hand-Coded Matching

A hand-coded lexer for a language with N terminals typically looks like this:

```rust
fn lex_token(input: &[u8], pos: usize) -> Option<(Token, usize)> {
    match input[pos] {
        b'+' => Some((Token::Plus, 1)),
        b'*' => Some((Token::Star, 1)),
        b'{' => {
            if pos + 1 < input.len() && input[pos + 1] == b'}' {
                Some((Token::EmptyBraces, 2))   // "{}"
            } else {
                Some((Token::LBrace, 1))         // "{"
            }
        }
        b'=' => {
            if pos + 1 < input.len() && input[pos + 1] == b'=' {
                Some((Token::EqEq, 2))           // "=="
            } else {
                Some((Token::Eq, 1))             // "="
            }
        }
        b'a'..=b'z' | b'A'..=b'Z' | b'_' => lex_ident_or_keyword(input, pos),
        b'0'..=b'9' => lex_number(input, pos),
        // ... more cases ...
    }
}
```

This approach has three problems:

1. **Combinatorial nesting.** Multi-character tokens with shared prefixes
   (e.g., `=` vs `==` vs `=>`, or `$proc` vs `$$proc(`) create nested
   if-else chains that grow quadratically in the number of prefix-sharing
   terminals.

2. **Keyword/identifier disambiguation.** Keywords like `error`, `true`,
   `false` share their character set with identifiers. Hand-coded matching
   must check "is the matched text a keyword?" after every identifier match,
   requiring a hash lookup or sorted search per token.

3. **Maintenance fragility.** Adding a new terminal requires understanding
   all existing prefix relationships and inserting the new case in the
   correct nesting position. Missing a case produces silent bugs (wrong
   token returned) rather than compile errors.

The automata approach solves all three problems:

- **Shared prefixes are handled naturally** by DFA states. The state after
  consuming `=` has transitions to both the `==` accept state and the `=`
  accept state, with maximal munch selecting the longest match.

- **Keyword priority is resolved during subset construction.** When multiple
  NFA accept states (e.g., `Ident` and `Fixed("error")`) are merged into a
  single DFA state, the higher-priority accept token wins.

- **New terminals require only adding a `TerminalPattern`** to the input list.
  The pipeline rebuilds the NFA/DFA automatically with correct prefix handling.

---

## 2. Pipeline Overview

```
  TerminalPatterns          BuiltinNeeds
  ["+", "*", "{}",          {ident: true,
   "error", "==",            integer: true,
   "(", ")", ...]            boolean: false, ...}
        │                        │
        └──────────┬─────────────┘
                   │
                   │
            ┌──────▼──────┐
            │ build_nfa() │      Aho-Corasick trie + Thompson's
            └──────┬──────┘      O(sum of terminal lengths)
                   │
                   │
               NFA (states, transitions, epsilon edges)
                   │
                   │
   ┌───────────────▼───────────────┐
   │ compute_equivalence_classes() │  Alphabet partitioning
   └───────────────┬───────────────┘  O(256 * |states| * |transitions|)
                   │
                   │
            AlphabetPartition
            (byte_to_class[256], num_classes, representatives)
                   │
                   │
      ┌────────────▼───────────┐
      │ subset_construction()  │     NFA → DFA (powerset)
      └────────────┬───────────┘     O(2^|NFA states| * num_classes) worst case
                   │                 O(|DFA states| * num_classes) typical
                   │
               DFA (states, transitions per equiv class)
                   │
                   │
          ┌────────▼─────────┐
          │ minimize_dfa()   │         Hopcroft's algorithm
          └────────┬─────────┘         O(n log n) on |DFA states|
                   │
                   │
            Minimized DFA
                   │
                   │
     ┌─────────────▼─────────────┐
     │ generate_lexer_string()   │     String-based code generation
     └─────────────┬─────────────┘     O(|states| * num_classes)
                   │
                   ▼
             String buffer
      (Token<'a> enum, Position, Range,
       ParseError, lex<'a>() function,
       CHAR_CLASS table, dfa_next/TRANSITIONS,
       accept_token<'a> match)
```

---

## 3. Thompson's Construction

Thompson's construction builds an NFA from terminal patterns by creating
small NFA fragments for each pattern and combining them with epsilon
transitions from a shared start state.

### Choice Rationale

Thompson's construction was chosen over alternatives because:

- **Glushkov's construction** produces an NFA without epsilon transitions
  but requires computing FIRST/LAST/FOLLOW for each pattern, which is
  more complex to implement for the simple case of literal strings and
  character classes.

- **Direct DFA construction** (e.g., Brzozowski derivatives) skips the
  NFA step but is harder to extend with character classes and has
  worst-case exponential state count without separate minimization.

- **Thompson's is well-understood**, easy to implement correctly, and
  naturally handles alternation (shared start state + epsilon transitions),
  which is exactly the structure we need for combining multiple terminal
  patterns.

### Fragment Construction

Each terminal pattern becomes a linear chain of states:

```
Fixed terminal "==" (2 characters):

  start ─['=']→ s1 ─['=']→ accept(Fixed("=="))


Fixed terminal "=" (1 character):

  start ─['=']→ accept(Fixed("="))


Identifier pattern [a-zA-Z_][a-zA-Z0-9_]*:

  start ─[a-z]→ accept(Ident)
        ─[A-Z]→    │
        ─['_']→    │
                   ├─[a-z]→ (self-loop)
                   ├─[A-Z]→ (self-loop)
                   ├─[0-9]→ (self-loop)
                   └─['_']→ (self-loop)


Integer pattern [0-9]+:

  start ─[0-9]→ accept(Integer)
                    │
                    └─[0-9]→ (self-loop)


Float pattern [0-9]+\.[0-9]+:

  start ─[0-9]→ s1 ─['.']→ s2 ─[0-9]→ accept(Float)
                 │                       │
                 └─[0-9]→ (self-loop)    └─[0-9]→ (self-loop)
```

### Alternation via Epsilon Transitions

All fragments are combined by adding epsilon transitions from the global
start state to each fragment's start state:

```
                 eps   ┌── start_"==" ─['=']→ s1 ─['=']→ accept(EqEq)
                ┌──────┤
                │      └── start_"="  ─['=']→ accept(Eq)
                │
  global_start──┼──eps→ start_"+"   ─['+']→ accept(Plus)
                │
                ├──eps→ start_ident ─[a-zA-Z_]→ accept(Ident)
                │                                   │
                │                                   └─[a-zA-Z0-9_]→(loop)
                │
                └──eps→ start_int   ─[0-9]→ accept(Integer)
                                                │
                                                └─[0-9]→ (self-loop)
```

### Accept Priority

When multiple NFA paths lead to the same DFA state (e.g., after consuming
`"error"`, both the `Fixed("error")` fragment and the `Ident` fragment
accept), the `TokenKind::priority()` function resolves the conflict:

```
Priority table:
  Eof          = 0
  Ident        = 1
  Integer      = 2
  Float        = 3
  True/False   = 10  (keywords beat identifiers)
  Fixed(_)     = 10  (fixed terminals beat identifiers)
  Dollar       = 5
  DoubleDollar = 6
```

The `resolve_accept()` function in `subset.rs` selects the highest-priority
accept token when multiple NFA accept states are merged into one DFA state.

---

## 4. Aho-Corasick Keyword Trie

### Motivation

The original Thompson's construction created separate NFA fragments for each
fixed terminal, joined by epsilon transitions from the global start state:

```
global_start ──eps→ start_"==" ─['=']→ s1 ─['=']→ accept(EqEq)
             ──eps→ start_"="  ─['=']→ accept(Eq)
             ──eps→ start_"+"  ─['+']→ accept(Plus)
             ──eps→ start_"*"  ─['*']→ accept(Star)
             ... (N epsilon transitions for N terminals)
```

This has two problems:

1. **Redundant states.** Terminals sharing prefixes (e.g., `=` and `==`)
   create separate chains that duplicate the shared prefix states.

2. **Epsilon explosion.** N fixed terminals create N epsilon transitions
   from the global start state. Each one is included in every epsilon
   closure computation during subset construction.

### Algorithm: build_keyword_trie()

`build_keyword_trie()` in `nfa.rs` builds a prefix-sharing trie directly
into the NFA, replacing per-terminal chains:

```
build_keyword_trie(nfa, terminals):
  trie_root = nfa.add_state()

  for each fixed terminal T with text = [c_0, c_1, ..., c_n]:
    current = trie_root
    for each character c_i in text:
      if current already has a transition on c_i:
        current = existing_target
      else:
        new_state = nfa.add_state()
        nfa.add_transition(current, c_i, new_state)
        current = new_state
    // Mark final state as accepting
    current.accept = T.kind

  return trie_root
```

The trie root is then connected to the global start with a **single** epsilon:

```
global_start ──eps→ trie_root ─['=']→ s1 (accept: Eq)
                                  │
                                  └─['=']→ s2 (accept: EqEq)
                    trie_root ─['+']→ s3 (accept: Plus)
                    trie_root ─['*']→ s4 (accept: Star)
                    trie_root ─['n']→ s5
                                  └─['o']→ s6
                                       └─['t']→ s7 (accept: KwNot)
```

### Prefix-of-Prefix Handling

When one terminal is a prefix of another (e.g., `=` and `==`), the shared
state is both accepting AND has transitions to longer matches:

```
trie_root ─['=']→ s1 (accept: Eq)    ◀── accepts "=" if no more input
                   │
                   └─['=']→ s2 (accept: EqEq)  ◀── accepts "==" if '=' follows
```

The maximal munch rule in the lexer ensures that `==` is preferred over `=`
when both characters are present.

### Priority Resolution

When the keyword trie accepts, it uses `TokenKind::priority()` for conflict
resolution (same as Thompson's construction):

```
Priority table:
  Ident        = 1
  Integer      = 2
  Float        = 3
  Dollar       = 5
  DoubleDollar = 6
  True/False   = 10  (keywords beat identifiers)
  Fixed(_)     = 10  (fixed terminals beat identifiers)
```

### State Savings

The trie significantly reduces NFA state count by sharing prefix states:

| Grammar    | Terminals | Old NFA States | Trie NFA States | Reduction |
|------------|-----------|----------------|-----------------|-----------|
| Calculator | ~15       | ~37            | ~22             | **~42%**  |
| RhoCalc    | ~18       | ~50            | ~35             | **~30%**  |
| Ambient    | ~14       | ~35            | ~21             | **~40%**  |

Fewer NFA states mean fewer epsilon closures during subset construction,
which reduces DFA build time.

### Legacy build_string_fragment()

The original per-terminal `build_string_fragment()` function is retained
with `#[cfg(test)]` annotation for unit testing. It is no longer called
in production---all fixed terminals go through `build_keyword_trie()`.

### DAFSA Suffix Sharing

#### Motivation

The prefix trie shares prefixes across terminals but **not suffixes**.
Consider terminals `input` and `output`---both end in `put`, but the trie
allocates separate chains for these shared suffixes. A **DAFSA** (Directed
Acyclic Finite State Automaton) extends prefix sharing to also share
suffix states, producing a more compact NFA.

#### Algorithm: Daciuk's Incremental Construction

PraTTaIL uses an adaptation of Daciuk et al.'s incremental algorithm
(2000) to build the DAFSA directly during trie construction. The key
insight: if two subtrees have identical structure (same transitions and
same accept token), they can be merged into one.

Two types support this:

```
NodeSignature {
    accept: Option<TokenKind>,           // Accept token (if any)
    transitions: Vec<(u8, StateId)>,     // Sorted by byte value
}

PathEntry {
    state: StateId,    // NFA state at this position in the word
    byte: u8,          // Edge label from parent to this state
}
```

`NodeSignature` captures the essential identity of an NFA state: its
accept status and outgoing transitions. Two states with identical
signatures are interchangeable.

The algorithm processes terminals in **sorted order** (guaranteed by
`BTreeSet<TerminalPattern>`), which ensures that the common prefix
between consecutive terminals is always a prefix of the current path.

```
build_keyword_trie(nfa, terminals):
  trie_root = nfa.add_state()
  registry: HashMap<NodeSignature, StateId> = {}
  previous_path: Vec<PathEntry> = []

  for each fixed terminal T with text = [c_0, c_1, ..., c_n] (sorted):
    // 1. FREEZE: share suffixes of previous word not shared with current
    common_prefix_len = longest_common_prefix(previous_path, T.text)
    freeze_suffixes(nfa, registry, previous_path, trie_root, common_prefix_len)

    // 2. INSERT: extend the trie from the divergence point
    current = if common_prefix_len > 0:
                previous_path[common_prefix_len - 1].state
              else:
                trie_root
    for each byte c_i in text[common_prefix_len..]:
      new_state = nfa.add_state()
      nfa.add_transition(current, c_i, new_state)
      path.push(PathEntry { state: new_state, byte: c_i })
      current = new_state

    // Mark final state as accepting
    current.accept = T.kind

  // 3. FINALIZE: freeze the entire last path
  freeze_suffixes(nfa, registry, path, trie_root, 0)

  return trie_root
```

#### freeze_suffixes()

```
freeze_suffixes(nfa, registry, path, trie_root, keep_count):
  // Walk backward from path end to keep_count
  for i in (keep_count..path.len()).rev():
    sig = NodeSignature::from_nfa_state(nfa, path[i].state)
    if let Some(&canonical) = registry.get(&sig):
      // Redirect parent edge to existing canonical state (suffix sharing)
      parent = if i > 0: path[i-1].state else: trie_root
      redirect parent's transition on path[i].byte → canonical
    else:
      // Register this state as the canonical representative
      registry.insert(sig, path[i].state)
```

The `trie_root` parameter is needed because `path[0]`'s parent is the
root itself, which is not part of the path.

#### Current Grammar Behavior

For current MeTTaIL grammars, **no suffix merging occurs at leaf nodes**
because every terminal has a unique `Fixed(text)` token kind. Since
`NodeSignature` includes the accept token, leaf nodes always differ.
The benefit comes from shared **non-accepting intermediate states**
(e.g., multiple keywords sharing internal character sequences).

This is validated by 4 identity tests that verify DAFSA produces
byte-identical DFA codegen compared to prefix-only trie construction
for all 4 grammars (Calculator, Ambient, RhoCalc, and the minimal spec).

#### Legacy build_keyword_trie_prefix_only()

The prefix-only trie builder `build_keyword_trie_prefix_only()` is
preserved for DFA equivalence testing. It constructs the same prefix
trie without suffix sharing, allowing tests to verify that the DAFSA
optimization does not change the DFA output.

---

## 5. Alphabet Partitioning (Equivalence Classes)

### Motivation

A naive DFA transition table has 256 columns (one per ASCII byte value).
For a DFA with S states, this is `S * 256` entries. Most of these are
redundant: bytes `a` through `z` (excluding characters that are also
single-character terminals like `+`, `*`, etc.) all trigger the same
transitions in every state.

### Algorithm

Two bytes are **equivalent** if and only if they trigger the same set of
transitions in every NFA state. The algorithm:

1. For each byte value (0-255), compute a **signature**: for each NFA state,
   record which target states the byte reaches.

2. Group bytes with identical signatures into equivalence classes.

```
Example (RhoCalc with +, *, !, ?, @, ., identifiers, integers):

  ┌─────────────┬───────────────────────────────────────┬───────┐
  │ Byte        │ NFA behavior                          │ Class │
  ├─────────────┼───────────────────────────────────────┼───────┤
  │ 'a'-'d',    │ start ident; continue ident           │   0   │
  │ 'f'-'z'     │                                       │       │
  │ 'e'         │ start ident; continue ident;          │   1   │
  │             │   also prefix of "error"              │       │
  │ 'A'-'Z'     │ start ident; continue ident           │   2   │
  │ '0'-'9'     │ continue ident; start/continue int    │   3   │
  │ '_'         │ start ident; continue ident           │   4   │
  │ '+'         │ terminal "+"                          │   5   │
  │ '*'         │ terminal "*"                          │   6   │
  │ '!'         │ terminal "!"                          │   7   │
  │ '?'         │ terminal "?"                          │   8   │
  │ '@'         │ terminal "@"                          │   9   │
  │ '.'         │ terminal "."                          │  10   │
  │ ','         │ terminal ","                          │  11   │
  │ '\|'        │ terminal "\|"                         │  12   │
  │ '('         │ terminal "("                          │  13   │
  │ ')'         │ terminal ")"                          │  14   │
  │ '{'         │ terminal "{"; prefix of "{}"          │  15   │
  │ '}'         │ terminal "}"                          │  16   │
  │ '='         │ prefix of "=="                        │  17   │
  │ ' ',\t,\n,\r│ whitespace (no transitions)           │  18   │
  │ everything  │ no transitions (dead)                 │  19   │
  │ else        │                                       │       │
  └─────────────┴───────────────────────────────────────┴───────┘
```

This compresses 256 columns to ~20 columns: a **~13x compression ratio**.

### Implementation Detail

The signature for each byte is a `Vec<(u32, Vec<u32>)>` where each entry
is `(state_id, sorted_target_states)`. Two bytes with identical signatures
are assigned the same class ID. The `AlphabetPartition` stores:

```rust
struct AlphabetPartition {
    byte_to_class: [ClassId; 256],      // 256-byte lookup table
    num_classes: usize,                  // typically 12-25
    class_representatives: Vec<u8>,      // one byte per class (for debugging)
}
```

The `classify(byte)` function is a single array lookup: O(1).

---

## 6. Subset Construction (NFA to DFA)

### Algorithm

Standard powerset construction with alphabet partitioning:

1. **Start state.** Compute `epsilon_closure({nfa.start})` to get the initial
   set of NFA states. This becomes DFA state 0.

2. **Iteration.** For each unprocessed DFA state and each equivalence class:
   a. Compute `move(current_set, class)`: the set of NFA states reachable
      via transitions on any byte in this class.
   b. Compute `epsilon_closure(move_result)`.
   c. If this set is new, create a new DFA state. Otherwise, reuse the
      existing one.
   d. Record the transition: `current_dfa_state --(class)--> target_dfa_state`.

3. **Accept resolution.** A DFA state's accept token is the highest-priority
   accept token among all NFA states in its set.

### Epsilon Closure

The `epsilon_closure()` function uses a worklist algorithm:

```
epsilon_closure(states):
  closure = set(states)
  stack = list(states)
  while stack is not empty:
    s = stack.pop()
    for t in nfa.states[s].epsilon:
      if t not in closure:
        closure.add(t)
        stack.push(t)
  return sorted(closure)
```

Sorting and deduplication ensure that NFA state sets can be used as map keys
for the `state_map: BTreeMap<Vec<StateId>, StateId>`.

### Transition Table Representation

DFA transitions are stored as sparse vectors: `Vec<(ClassId, StateId)>`.
Only non-dead transitions are stored. The `dfa_transition()` function does
a linear scan (acceptable because the number of non-dead transitions per
state is typically small---bounded by `num_classes`).

---

## 7. Hopcroft's DFA Minimization

### Motivation

After subset construction, the DFA may contain equivalent states---states
that accept the same token and transition identically on all equivalence
classes. This is common when multiple terminal patterns share prefixes
(e.g., `$proc` and `$name` both start with `$`; the shared prefix state
can often be merged with other states).

### Algorithm

Hopcroft's algorithm partitions DFA states into equivalence classes and
merges states within each class:

```
1. INITIAL PARTITION: Group states by accept token.
   - All non-accepting states form one group.
   - States accepting Fixed("+") form another.
   - States accepting Fixed("==") form another.
   - States accepting Ident form another.
   - etc.

2. WORKLIST: All partition groups initially need refinement.

3. REFINEMENT: For each splitter group and each equivalence class:
   For each partition P:
     Split P into:
       P1 = {states in P that transition to the splitter on this class}
       P2 = {states in P that do NOT transition to the splitter}
     If both P1 and P2 are non-empty:
       Replace P with the larger of P1/P2.
       Create a new partition for the smaller.
       Add the new partition to the worklist.

4. BUILD MINIMIZED DFA:
   Each non-empty partition becomes one state in the minimized DFA.
   Transitions are computed from any representative state.
```

### Complexity

O(n * k * log n) where n is the number of DFA states and k is the number
of equivalence classes. In practice, k is small (~15-25), so this is
effectively O(n log n).

### Typical Reduction

For the RhoCalc terminal set (~18 terminals + identifiers + integers):

```
┌──────────────────────┬────────┐
│ Pipeline stage       │ States │
├──────────────────────┼────────┤
│ NFA                  │   ~50  │
│ DFA (after subset)   │   ~15  │
│ Minimized DFA        │   ~10  │
└──────────────────────┴────────┘
```

The minimized DFA typically has 30-50% fewer states than the un-minimized
DFA for grammars with shared-prefix terminals.

### BFS Canonical State Reordering

After Hopcroft minimization, `canonicalize_state_order()` in `minimize.rs`
renumbers all DFA states in **BFS traversal order** starting from state 0
(the start state).

#### Motivation

Hopcroft's algorithm assigns state IDs based on partition refinement
order, which depends on the NFA topology. Different NFA constructions
(e.g., prefix-only trie vs DAFSA) may produce different intermediate
state numberings, even though the final minimized DFA is structurally
identical. This causes generated match arms to appear in different
orders, which can:

1. Confuse benchmark comparisons (identical DFAs with different codegen)
2. Make regression testing fragile (byte-non-identical output for
   equivalent DFAs)

#### Algorithm

```
canonicalize_state_order(dfa):
  // BFS from start state
  queue = [dfa.start]      // always state 0
  visited = {dfa.start}
  new_order = []

  while queue is not empty:
    state = queue.pop_front()
    new_order.push(state)
    for each (class, target) in state.transitions (sorted by class):
      if target not in visited and target != DEAD:
        visited.add(target)
        queue.push(target)

  // Early exit if already in BFS order
  if new_order[i] == i for all i: return

  // Build old_to_new mapping and rebuild state vector
  old_to_new[new_order[i]] = i for each i
  Remap all transitions: target = old_to_new[target]
  Reorder state vector to match new numbering
```

**Complexity:** O(S + T) where S = states, T = total transitions.

This is called as the final step of `minimize_dfa()`, after Hopcroft
refinement. It ensures that the generated lexer code is deterministic
regardless of the NFA construction strategy used.

---

## 8. Code Generation: String-Based, Direct-Coded vs Table-Driven

### String-Based Code Generation

PraTTaIL builds the entire lexer as a `String` buffer using `write!()`
formatting, then performs a single `str::parse::<TokenStream>()` call at
the end to convert the string to a proc-macro token stream. This approach
replaced the original `quote!`-based code generation, which created
intermediate `TokenStream` allocations for every match arm, table entry,
and function body.

**Why strings instead of quote!:**

The original approach used hundreds of `quote! { ... }` calls, each of
which:
1. Creates a `TokenStream` via proc-macro2's `RcVec` (allocation)
2. Extends the parent `TokenStream` (clone + extend)
3. Drops intermediate `TokenStream` values (deallocation)

Profiling showed that ~46% of codegen CPU time was spent on these
proc-macro2 allocation/clone/drop operations. String formatting is
dramatically cheaper---the `write!` calls to build the string buffer
consume only ~2.7% of CPU time.

**Performance improvement:** -23% to -29% across all grammar specs for
lexer codegen. The remaining cost is the irreducible `str::parse()` call
which must parse the complete generated string.

### Zero-Copy Token Enum

The generated `Token<'a>` enum uses borrowed `&'a str` fields instead of
owned `String`:

```rust
pub enum Token<'a> {
    Eof,
    Ident(&'a str),         // borrows from input
    StringLit(&'a str),     // borrows from input
    Dollar(&'a str),        // borrows from input
    DoubleDollar(&'a str),  // borrows from input
    Integer(i64),
    Float(f64),
    Boolean(bool),
    // ... fixed terminal variants (unit types, no allocation)
}
```

The lexer function signature is `lex<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Span)>, String>`,
and `accept_token` becomes `accept_token<'a>(state: u32, text: &'a str) -> Option<Token<'a>>`.
This eliminates one `String` allocation per identifier token and per string literal token.
String allocation is deferred to AST construction where `.to_string()` is called at
`get_or_create_var` sites.

### Threshold Analysis

PraTTaIL uses a threshold of **30 DFA states** to select between two
code generation strategies:

```
  DFA states <= 30:  Direct-coded (match-based)
  DFA states > 30:   Table-driven (array-based)
```

### Direct-Coded Lexer

For small DFAs (typical for most MeTTaIL grammars), each DFA state becomes
a match arm in the `dfa_next()` function:

```rust
fn dfa_next(state: u32, class: u8) -> u32 {
    match state {
        0 => match class {      // Start state
            5 => 3,             // class 5 ('+') -> state 3 (accept Plus)
            6 => 4,             // class 6 ('*') -> state 4 (accept Star)
            0 => 1,             // class 0 ('a'-'z') -> state 1 (ident)
            3 => 2,             // class 3 ('0'-'9') -> state 2 (integer)
            _ => u32::MAX,      // dead state
        },
        1 => match class {      // Identifier accumulation state
            0 | 2 | 3 | 4 => 1, // letters/digits/underscore -> stay in ident
            _ => u32::MAX,
        },
        // ... more states ...
        _ => u32::MAX,
    }
}
```

**Advantages of direct-coded:**

- Branch predictor-friendly: CPUs predict match arms well.
- No cache misses from table lookups.
- Compiler can optimize: dead code elimination, constant folding.
- Human-readable generated code.

### Table-Driven Lexer

For large DFAs (>30 states), a flat transition table is more efficient:

```rust
static TRANSITIONS: [u32; NUM_STATES * NUM_CLASSES] = [
    // state 0:  class 0, class 1, class 2, ...
    u32::MAX, 1, u32::MAX, 2, u32::MAX, 3, 4, ...
    // state 1:  ...
    1, 1, 1, 1, u32::MAX, u32::MAX, u32::MAX, ...
    // ...
];

fn dfa_next(state: u32, class: u8) -> u32 {
    TRANSITIONS[state as usize * NUM_CLASSES + class as usize]
}
```

**Advantages of table-driven:**

- Constant-time lookup (single array index).
- Compact representation for large DFAs.
- Row displacement (comb) or bitmap compression can further reduce table
  size (see below).

### Sparsity Analysis

Before selecting a compression strategy, `analyze_sparsity()` examines
the DFA transition table to determine how sparse it is:

```rust
struct SparsityInfo {
    live_per_state: Vec<usize>,  // Non-dead transitions per state
    total_live: usize,           // Total non-dead transitions across all states
    dead_fraction: f64,          // Fraction of entries that are dead (0.0-1.0)
}
```

For typical MeTTaIL grammars, the dead fraction is 0.7-0.9 (70-90% of
the flat table entries are dead/unreachable transitions). This high
sparsity motivates compression.

### Row Displacement (Comb) Compression

Row displacement packs sparse rows into a shared array by finding
offsets where non-dead entries do not overlap. This is also known as
"comb compression" (visualize the rows as combs meshing together).

```
CombTable {
    base: Vec<u32>,     // Displacement offset per state
    default: Vec<u32>,  // Default target (typically DEAD_STATE) per state
    next: Vec<u32>,     // Packed target states
    check: Vec<u32>,    // Owner state for collision detection
}
```

**Lookup formula:**

```
idx = BASE[state] + class
target = if CHECK[idx] == state { NEXT[idx] } else { DEFAULT[state] }
```

**Algorithm: `compress_rows_comb()`**

```
compress_rows_comb(dfa, num_classes):
  // 1. Extract sparse rows: only non-dead transitions
  rows = [(state_idx, [(class_id, target)])] for each state

  // 2. Sort by density (densest first) for tighter packing
  rows.sort_by_descending(|row| row.transitions.len())

  // 3. Greedy offset search
  for each row (in density order):
    for d = 0, 1, 2, ...:
      if no collision at offset d:
        BASE[state] = d
        place row entries at NEXT[d + class] = target, CHECK[d + class] = state
        break

  // 4. Pad NEXT/CHECK to max(BASE) + num_classes to eliminate bounds checks
  // 5. Set DEFAULT[state] = DEAD_STATE for all states
```

The densest-first heuristic ensures that rows with the most live entries
are placed first, when the shared array is most empty. This typically
achieves near-optimal packing.

**Generated lexer (`write_comb_driven_lexer`):**

```rust
static BASE: [u32; NUM_STATES] = [...];
static DEFAULT: [u32; NUM_STATES] = [...];
static NEXT: [u32; TABLE_SIZE] = [...];
static CHECK: [u32; TABLE_SIZE] = [...];

fn dfa_next(state: u32, class: u8) -> u32 {
    let idx = BASE[state as usize] as usize + class as usize;
    if CHECK[idx] == state { NEXT[idx] } else { DEFAULT[state as usize] }
}
```

### Bitmap Node Compression

An alternative to comb compression: represent each state's live
transitions as a bitmap, with a dense array of only the live targets.

```
BitmapTables {
    bitmaps: Vec<u32>,   // One u32 bitmap per state
    offsets: Vec<u16>,   // Start index into targets array per state
    targets: Vec<u32>,   // Dense array of live target states
}
```

**Guard:** This strategy requires `num_classes ≤ 32` (must fit in a
`u32` bitmap).

**Lookup formula:**

```
bit = 1u32 << class
if bitmaps[state] & bit == 0:
    return DEAD_STATE              // No transition on this class
else:
    index = (bitmaps[state] & (bit - 1)).count_ones()  // popcount
    return targets[offsets[state] + index]
```

The `count_ones()` call uses hardware `POPCNT` on modern CPUs (one
cycle on x86-64 with SSE4.2+), making this O(1) per lookup.

**Algorithm: `build_bitmap_tables()`**

```
build_bitmap_tables(dfa):
  for each state:
    bitmap = 0u32
    live_targets = []
    for class in 0..num_classes:
      target = dfa.transitions[state][class]
      if target != DEAD:
        bitmap |= 1u32 << class
        live_targets.push(target)
    bitmaps.push(bitmap)
    offsets.push(targets.len())
    targets.extend(live_targets)
```

**Generated lexer (`write_bitmap_driven_lexer`):**

```rust
static BITMAPS: [u32; NUM_STATES] = [...];
static OFFSETS: [u16; NUM_STATES] = [...];
static TARGETS: [u32; NUM_LIVE_TRANSITIONS] = [...];

fn dfa_next(state: u32, class: u8) -> u32 {
    let bit = 1u32 << class;
    let bm = BITMAPS[state as usize];
    if bm & bit == 0 {
        u32::MAX  // DEAD_STATE
    } else {
        let idx = OFFSETS[state as usize] as usize
            + (bm & (bit - 1)).count_ones() as usize;
        TARGETS[idx]
    }
}
```

### Strategy Selection

PraTTaIL selects the best compression strategy automatically based on
DFA size and table cost:

```
CodegenStrategy enum:
  DirectCoded       — Match arms for ≤30 DFA states (default for small grammars)
  CombCompressed    — Row displacement for >30 states or when comb is smaller
  BitmapCompressed  — Bitmap + popcount for >30 states when classes ≤ 32

Selection logic:
  if minimized_states ≤ 30:
    strategy = DirectCoded
  else:
    comb = compress_rows_comb(dfa, num_classes)
    if num_classes ≤ 32:
      bitmap = build_bitmap_tables(dfa)
      if bitmap.total_bytes() ≤ comb.total_bytes():
        strategy = BitmapCompressed
      else:
        strategy = CombCompressed
    else:
      strategy = CombCompressed
```

The `total_bytes()` method on each table type computes the total
memory footprint (array lengths × element sizes). The strategy with
the smallest footprint wins.

Each compression strategy counts different arrays:

| Strategy             | Arrays Counted                      | Description                                                                                     |
|----------------------|-------------------------------------|-------------------------------------------------------------------------------------------------|
| **CombCompressed**   | `TARGETS` + `OFFSETS` + `ROW_CHECK` | Comb-packed transitions, per-state offsets, row check for collision detection                   |
| **BitmapCompressed** | `BITMAPS` + `OFFSETS` + `TARGETS`   | u32 bitmaps (1 per state, `num_classes ≤ 32`), offsets into dense target array, packed targets  |
| **DirectCoded**      | (no table)                          | Selected when `minimized_states ≤ 30`; transitions become inline `match` arms in generated code |

`LexerStats` reports the selected strategy:

```rust
struct LexerStats {
    // ... existing fields ...
    codegen_strategy: CodegenStrategy,  // Which strategy was selected
    dead_fraction: f64,                 // Fraction of dead transitions (0.0-1.0)
}
```

### Legacy Flat Table-Driven Lexer

The original flat `write_table_driven_lexer()` function (uncompressed
`TRANSITIONS[NUM_STATES * NUM_CLASSES]` array) is preserved with
`#[allow(dead_code)]` annotation. It is no longer called in production
but may be useful for debugging or comparison.

---

## 9. Worked Example: RhoCalc Terminal Set

The RhoCalc language has the following terminal set:

```
Fixed terminals:  +  *  !  ?  @  .  ,  |  (  )  {  }  [  ]  {}  error
Built-in patterns: identifiers ([a-zA-Z_][a-zA-Z0-9_]*), integers ([0-9]+)
```

### Step 1: NFA Construction

`build_nfa()` creates fragments for each terminal and joins them:

```
Global start (state 0)
  │
  ├──eps→ s1 ─['+']→ s2 (accept: Fixed("+"))
  │
  ├──eps→ s3 ─['*']→ s4 (accept: Fixed("*"))
  │
  ├──eps→ s5 ─['!']→ s6 (accept: Fixed("!"))
  │
  ├──eps→ s7 ─['?']→ s8 (accept: Fixed("?"))
  │
  ├──eps→ s9 ─['@']→ s10 (accept: Fixed("@"))
  │
  ├──eps→ s11 ─['.']→ s12 (accept: Fixed("."))
  │
  ├──eps→ s13 ─[',']→ s14 (accept: Fixed(","))
  │
  ├──eps→ s15 ─['|']→ s16 (accept: Fixed("|"))
  │
  ├──eps→ s17 ─['(']→ s18 (accept: Fixed("("))
  │
  ├──eps→ s19 ─[')']→ s20 (accept: Fixed(")"))
  │
  ├──eps→ s21 ─['{']→ s22 (accept: Fixed("{"))
  │                         │
  │                         └─['}']→ s23 (accept: Fixed("{}"))
  │
  ├──eps→ s24 ─['}']→ s25 (accept: Fixed("}"))
  │
  ├──eps→ s26 ─['[']→ s27 (accept: Fixed("["))
  │
  ├──eps→ s28 ─[']']→ s29 (accept: Fixed("]"))
  │
  ├──eps→ s30 ─['e']→ s31 ─['r']→ s32 ─['r']→ s33
  │                                    ─['o']→ s34 ─['r']→ s35
  │                                                   (accept: Fixed("error"))
  │
  ├──eps→ s36 ─[a-zA-Z_]→ s37 (accept: Ident, self-loops on [a-zA-Z0-9_])
  │
  └──eps→ s38 ─[0-9]→ s39 (accept: Integer, self-loop on [0-9])
```

Total NFA states: ~40-50 (depends on exact fragment construction).

### Step 2: Equivalence Classes

`compute_equivalence_classes()` builds byte signatures:

```
┌───────┬────────────────┬─────────────────────────┬────────────────────────────┐
│ Class │ Representative │ Characters              │ NFA behavior               │
├───────┼────────────────┼─────────────────────────┼────────────────────────────┤
│   0   │ 'a'            │ a-d, f-z (excl. 'e')    │ start+continue ident       │
│   1   │ 'e'            │ e                       │ start+continue ident;      │
│       │                │                         │   also start "error"       │
│   2   │ 'A'            │ A-Z                     │ start+continue ident       │
│   3   │ '0'            │ 0-9                     │ continue ident; start+     │
│       │                │                         │   continue integer         │
│   4   │ '_'            │ _                       │ start+continue ident       │
│   5   │ '+'            │ +                       │ terminal "+"               │
│   6   │ '*'            │ *                       │ terminal "*"               │
│   7   │ '!'            │ !                       │ terminal "!"               │
│   8   │ '?'            │ ?                       │ terminal "?"               │
│   9   │ '@'            │ @                       │ terminal "@"               │
│  10   │ '.'            │ .                       │ terminal "."               │
│  11   │ ','            │ ,                       │ terminal ","               │
│  12   │ '\|'           │ \|                      │ terminal "\|"              │
│  13   │ '('            │ (                       │ terminal "("               │
│  14   │ ')'            │ )                       │ terminal ")"               │
│  15   │ '{'            │ {                       │ terminal "{"; prefix "{}"  │
│  16   │ '}'            │ }                       │ terminal "}"               │
│  17   │ '['            │ [                       │ terminal "["               │
│  18   │ ']'            │ ]                       │ terminal "]"               │
│  19   │ 'r'            │ r                       │ start+continue ident;      │
│       │                │                         │   continue "error"         │
│  20   │ 'o'            │ o                       │ start+continue ident;      │
│       │                │                         │   continue "error"         │
│  21   │ ' '            │ space, tab, newline, CR │ whitespace (no transitions)│
│  22   │ 0x00           │ all other bytes         │ dead (no transitions)      │
└───────┴────────────────┴─────────────────────────┴────────────────────────────┘
```

Result: **~22 equivalence classes** (compressed from 256 byte values).

### Step 3: Subset Construction

The powerset algorithm processes the epsilon closure of the start state
and follows transitions by equivalence class:

```
┌───────────┬───────────────────────────┬───────────────────────────────────┐
│ DFA State │ NFA State Set             │ Accept                            │
├───────────┼───────────────────────────┼───────────────────────────────────┤
│     D0    │ {0, s1,s3,s5,...,s36,s38} │ None (start)                      │
│     D1    │ {s37}                     │ Ident                             │
│     D2    │ {s39}                     │ Integer                           │
│     D3    │ {s2}                      │ Fixed("+")                        │
│     D4    │ {s4}                      │ Fixed("*")                        │
│     D5    │ {s6}                      │ Fixed("!")                        │
│     D6    │ {s8}                      │ Fixed("?")                        │
│     D7    │ {s10}                     │ Fixed("@")                        │
│     D8    │ {s12}                     │ Fixed(".")                        │
│     D9    │ {s14}                     │ Fixed(",")                        │
│    D10    │ {s16}                     │ Fixed("\|")                       │
│    D11    │ {s18}                     │ Fixed("(")                        │
│    D12    │ {s20}                     │ Fixed(")")                        │
│    D13    │ {s22}                     │ Fixed("{")                        │
│    D14    │ {s23}                     │ Fixed("{}")                       │
│    D15    │ {s25}                     │ Fixed("}")                        │
│    D16    │ {s27}                     │ Fixed("[")                        │
│    D17    │ {s29}                     │ Fixed("]")                        │
│    D18    │ {s31, s37}                │ Ident  ('e' then continue)        │
│    D19    │ {s32, s37}                │ Ident  ('er' then continue)       │
│    D20    │ {s33, s37}                │ Ident  ('err' then continue)      │
│    D21    │ {s34, s37}                │ Ident  ('erro' then continue)     │
│    D22    │ {s35, s37}                │ Fixed("error")  (priority > Ident)│
└───────────┴───────────────────────────┴───────────────────────────────────┘
```

Note: state D22 has both `Fixed("error")` (priority 10) and `Ident`
(priority 1) as potential accept tokens. `resolve_accept()` selects
`Fixed("error")`.

Transition table (selected entries):

```
D0  ──(class 0: a-d,f-z)──▶ D1 (ident)
D0  ──(class 1: e)─────────▶ D18 (ident, also "error" prefix)
D0  ──(class 3: 0-9)───────▶ D2 (integer)
D0  ──(class 5: +)─────────▶ D3 (accept "+")
D0  ──(class 15: {)────────▶ D13 (accept "{")
D13 ──(class 16: })────────▶ D14 (accept "{}")
D1  ──(class 0,1,2,3,4)───▶ D1 (ident self-loop)
D18 ──(class 19: r)────────▶ D19 (ident, "er" prefix)
D19 ──(class 19: r)────────▶ D20 (ident, "err" prefix)
D20 ──(class 20: o)────────▶ D21 (ident, "erro" prefix)
D21 ──(class 19: r)────────▶ D22 (accept "error")
D22 ──(class 0,1,2,3,4)───▶ D1 (ident: "errors" is an ident, not keyword)
```

Total DFA states: ~22 (before minimization).

### Step 4: Minimization

Hopcroft's algorithm merges equivalent states. States D3 through D17
(single-character terminal accept states with no outgoing transitions)
may not merge because they accept different tokens. However, states that
accept the same token and have identical transition patterns can merge.

Typical result: **~15-18 states** after minimization.

### Step 5: Code Generation

With ~18 states and ~22 equivalence classes, this falls under the
direct-coded threshold (<=30). The generated code:

```rust
static CHAR_CLASS: [u8; 256] = [
    22, 22, ...,    // 0x00-0x08: dead class
    21, 21, 21, ..., // whitespace
    ...,
    3, 3, 3, ...,   // '0'-'9': class 3
    ...,
    0, 0, 0, ...,   // 'a'-'d': class 0
    1,              // 'e': class 1
    0, 0, ...,      // 'f'-'z': class 0
    ...
];

fn dfa_next(state: u32, class: u8) -> u32 {
    match state {
        0 => match class {
            0 | 2 | 4 => 1,    // ident start
            1 => 18,            // 'e' (ident + error prefix)
            3 => 2,             // digit (integer)
            5 => 3,             // '+' (Plus)
            6 => 4,             // '*' (Star)
            // ... remaining transitions ...
            _ => u32::MAX,
        },
        1 => match class {
            0 | 1 | 2 | 3 | 4 | 19 | 20 => 1,  // ident continue
            _ => u32::MAX,
        },
        // ... remaining states ...
        _ => u32::MAX,
    }
}

fn accept_token(state: u32, text: &str) -> Option<Token> {
    match state {
        1  => Some(Token::Ident(text.to_string())),
        2  => Some(Token::Integer(text.parse::<i64>().expect("..."))),
        3  => Some(Token::Plus),
        4  => Some(Token::Star),
        // ...
        22 => Some(Token::KwError),  // "error" keyword
        _ => None,
    }
}
```

### Summary Statistics for RhoCalc

```
┌────────────────────────────┬─────────┐
│ Metric                     │ Value   │
├────────────────────────────┼─────────┤
│ Fixed terminals            │    16   │
│ Built-in patterns          │     2   │
│ NFA states                 │   ~50   │
│ Equivalence classes        │   ~22   │
│ DFA states (pre-minimize)  │   ~22   │
│ DFA states (post-minimize) │   ~18   │
│ Compression ratio          │   ~14x  │
│ Code generation strategy   │ direct  │
└────────────────────────────┴─────────┘
```
