# Finite Automata Theory for Lexer Generation

This document covers the automata theory underlying PraTTaIL's lexer
generation pipeline. Starting from the definition of regular languages, we
develop NFAs, Thompson's construction, epsilon-closure, subset construction,
DFA minimization (Hopcroft's algorithm), alphabet equivalence classes, maximal
munch tokenization, priority handling, and finally code generation. Each
concept is illustrated with worked examples and ASCII diagrams.

---

## 1. Regular Languages and Why They Matter for Lexing

### 1.1 Definition

A **regular language** is a set of strings that can be described by a regular
expression (equivalently, recognized by a finite automaton). The regular
languages are the simplest class in the Chomsky hierarchy:

```
  ┌──────────────────────────────────────────────────────┐
  │ Type 0: Recursively enumerable (Turing machines)     │
  │  ┌──────────────────────────────────────────────┐    │
  │  │ Type 1: Context-sensitive                     │    │
  │  │  ┌──────────────────────────────────────┐    │    │
  │  │  │ Type 2: Context-free (pushdown aut.) │    │    │
  │  │  │  ┌──────────────────────────────┐    │    │    │
  │  │  │  │ Type 3: Regular (finite aut.)│    │    │    │
  │  │  │  │                              │    │    │    │
  │  │  │  └──────────────────────────────┘    │    │    │
  │  │  └──────────────────────────────────────┘    │    │
  │  └──────────────────────────────────────────────┘    │
  └──────────────────────────────────────────────────────┘
```

### 1.2 Why Regular Languages for Lexing?

Most token patterns in programming languages are regular:

```
  Identifiers:   [a-zA-Z_][a-zA-Z0-9_]*
  Integers:      [0-9]+
  Floats:        [0-9]+\.[0-9]+
  Operators:     \+|\-|\*|/|==|!=|<=|>=
  Keywords:      if|else|while|for|error|true|false
  Strings:       "[^"]*"
```

Regular languages can be recognized in O(n) time with O(1) auxiliary space
(just the current state). This makes finite automata the ideal foundation for
lexers: they are fast, predictable, and provably correct.

### 1.3 Regular Language Closure Properties

Regular languages are closed under:
- **Union:** If L1 and L2 are regular, so is L1 | L2
- **Concatenation:** L1 . L2
- **Kleene star:** L1*
- **Intersection:** L1 & L2
- **Complement:** not L1
- **Difference:** L1 - L2

These closure properties are exploited throughout the lexer pipeline.

---

## 2. Nondeterministic Finite Automata (NFA)

### 2.1 Definition

An NFA is a 5-tuple `(Q, Sigma, delta, q0, F)` where:

- `Q` is a finite set of states
- `Sigma` is the input alphabet (for PraTTaIL: bytes 0..255)
- `delta: Q x (Sigma union {epsilon}) -> 2^Q` is the transition function
  (maps a state and an input symbol to a _set_ of states)
- `q0 in Q` is the start state
- `F subset Q` is the set of accepting states

**Nondeterminism** means that from a given state on a given input, the
automaton may transition to _multiple_ states simultaneously. This is a
theoretical convenience; it does not mean the implementation is nondeterministic.

### 2.2 Epsilon Transitions

An **epsilon transition** (written `--epsilon-->`) allows the automaton to
change state without consuming any input character. These are central to
Thompson's construction.

```
  Example: NFA for "a|b" (either 'a' or 'b'):

       ┌──── epsilon ────> (s1) ──'a'──> ((s2))
  (s0) ┤
       └──── epsilon ────> (s3) ──'b'──> ((s4))

  States: s0 (start), s1, s2 (accept), s3, s4 (accept)
  From s0, the NFA nondeterministically follows both epsilon edges.
```

### 2.3 Acceptance

An NFA **accepts** a string `w` if there exists _any_ sequence of transitions
(including epsilon moves) from the start state that consumes all of `w` and
ends in an accepting state.

---

## 3. Thompson's Construction

Thompson's construction (1968) converts a regular expression into an NFA.
The algorithm is compositional: each sub-expression produces an **NFA
fragment** with a single start state and a single accept state, and fragments
are combined using three operations.

### 3.1 Base Case: Single Character

For a character `c`:

```
  (start) ──'c'──> ((accept))
```

In PraTTaIL, this is `build_string_fragment` for single-character terminals:

```
  Terminal "+":   (s0) ──'+'──> ((s1: accept=Fixed("+")))
```

### 3.2 Concatenation

For `AB` (match A then B):

```
  (A.start) ──...──> (A.accept) ──epsilon──> (B.start) ──...──> ((B.accept))
```

In PraTTaIL, multi-character terminals use concatenation. For `"=="`:

```
  (s0) ──'='──> (s1) ──'='──> ((s2: accept=Fixed("==")))
```

Here the intermediate state `s1` replaces the epsilon transition with a
direct chain (an optimization for string literals).

### 3.3 Alternation (Union)

For `A|B` (match A or B):

```
              ┌── epsilon ──> (A.start) ──...──> (A.accept) ── epsilon ──┐
  (new start) ┤                                                          ├> ((new accept))
              └── epsilon ──> (B.start) ──...──> (B.accept) ── epsilon ──┘
```

In PraTTaIL, the global NFA start state uses epsilon transitions to reach
each terminal pattern's fragment start:

```
            ┌── epsilon ──> (+  fragment)
            ├── epsilon ──> (*  fragment)
  (start) ──┤── epsilon ──> (== fragment)
            ├── epsilon ──> (ident fragment)
            └── epsilon ──> (integer fragment)
```

This is implemented in `build_nfa()`:

```rust
for frag in &fragments {
    nfa.add_epsilon(global_start, frag.start);
}
```

### 3.4 Kleene Star (Repetition)

For `A*` (zero or more repetitions of A):

```
               ┌───────────── epsilon ────────────────┐
               │                                       │
               ▼                                       │
  (new start) ──epsilon──> (A.start) ──...──> (A.accept) ──epsilon──> ((new accept))
       │                                                                    ▲
       └──────────────────── epsilon ───────────────────────────────────────┘
```

In PraTTaIL, Kleene star is used implicitly in built-in patterns. For
example, the identifier pattern `[a-zA-Z_][a-zA-Z0-9_]*` uses a self-loop:

```
  (start) ──[a-zA-Z_]──> (accept) ──[a-zA-Z0-9_]──> (accept)
                                          │               ▲
                                          └───────────────┘
                                           (self-loop = Kleene star)
```

### 3.5 Complete Example

Build the NFA for a grammar with terminals `+`, `*`, and identifiers:

```
  State allocation:
    0: global start
    1: fragment start for "+"
    2: accept for "+" (accept=Fixed("+"))
    3: fragment start for "*"
    4: accept for "*" (accept=Fixed("*"))
    5: fragment start for ident
    6: accept for ident (accept=Ident)

  Transitions:
    0 ──epsilon──> 1
    0 ──epsilon──> 3
    0 ──epsilon──> 5
    1 ──'+'──> 2
    3 ──'*'──> 4
    5 ──[a-zA-Z_]──> 6
    6 ──[a-zA-Z0-9_]──> 6    (self-loop)

  Diagram:
                 ┌── eps ──> (1) ──'+'──> ((2: Fixed("+")))
                 │
  (0: start) ────┼── eps ──> (3) ──'*'──> ((4: Fixed("*")))
                 │
                 └── eps ──> (5) ──[a-zA-Z_]──> ((6: Ident))
                                                      │   ▲
                                                      └───┘
                                                   [a-zA-Z0-9_]
```

---

## 4. Epsilon-Closure

### 4.1 Definition

The **epsilon-closure** of a set of states `S` is the set of all states
reachable from any state in `S` by following zero or more epsilon transitions:

```
  epsilon_closure(S) = S union { t : s -->epsilon--> ... -->epsilon--> t, s in S }
```

### 4.2 Algorithm

```
  function epsilon_closure(nfa, states):
      closure = set(states)
      stack = list(states)
      while stack is not empty:
          state = stack.pop()
          for target in nfa.states[state].epsilon:
              if target not in closure:
                  closure.add(target)
                  stack.push(target)
      return sorted(closure)
```

> **Why sorted?** The sorted representation is essential because NFA state sets
> are used as map keys during subset construction. If the closure were returned
> unsorted, identical state sets could appear in different orders and be treated
> as distinct DFA states, producing a larger (and incorrect) DFA.

### 4.3 Worked Example

Using the NFA from section 3.5:

```
  epsilon_closure({0}) = {0, 1, 3, 5}

  Trace:
    Start: {0}
    Process 0: epsilon targets = {1, 3, 5}
    Process 1: epsilon targets = {} (no epsilon edges)
    Process 3: epsilon targets = {} (no epsilon edges)
    Process 5: epsilon targets = {} (no epsilon edges)
    Result: {0, 1, 3, 5}
```

### 4.4 Significance

Epsilon-closure is the bridge between NFAs and DFAs. Every DFA state
corresponds to a set of NFA states, and computing transitions through the
DFA requires taking the epsilon-closure after each character transition.

---

## 5. Alphabet Equivalence Classes

### 5.1 Motivation

A naive DFA has 256 transitions per state (one per byte value). But most
bytes behave identically: the letters `a` through `z` all trigger the same
transitions in the identifier pattern. **Alphabet equivalence classes**
partition the 256 byte values into groups that behave identically across all
NFA states.

### 5.2 Definition

Two bytes `b1` and `b2` are **equivalent** (written `b1 ~ b2`) if and only
if, for every NFA state `s`, the set of states reachable from `s` on `b1`
equals the set of states reachable from `s` on `b2`.

Formally:

```
  b1 ~ b2  iff  for all s in Q:  delta(s, b1) = delta(s, b2)
```

### 5.3 Algorithm

PraTTaIL computes equivalence classes as follows:

1. For each byte `b` (0..255), compute a **signature**: for each NFA state
   `s`, record the sorted set of target states reachable on `b`.

2. Group bytes with identical signatures. Each group is an equivalence class.

```
  function compute_equivalence_classes(nfa):
      for byte in 0..256:
          sig[byte] = []
          for state in nfa.states:
              targets = sorted({ t : (class, t) in state.transitions
                                     if class contains byte })
              if targets is not empty:
                  sig[byte].append((state_id, targets))

      class_id = 0
      for byte in 0..256:
          if sig[byte] matches an existing class:
              byte_to_class[byte] = that class
          else:
              byte_to_class[byte] = class_id
              class_id += 1

      return byte_to_class, class_id
```

### 5.4 Worked Example

For the grammar `{+, *, identifiers, integers}`:

```
  Equivalence classes:

  Class 0: Bytes that match no transition from any state
           (e.g., 0x00..0x08, various control characters)

  Class 1: '+' (byte 0x2B)
           Unique: only triggers transition in state 1

  Class 2: '*' (byte 0x2A)
           Unique: only triggers transition in state 3

  Class 3: [a-zA-Z_]  (letters and underscore)
           All behave identically: start or continue an identifier

  Class 4: [0-9]  (digits)
           All behave identically: start an integer or continue an identifier

  Class 5: Whitespace (space, tab, newline, carriage return)
           Handled outside the DFA, but form their own class

  Total: ~6-8 classes instead of 256
```

This yields a **15-20x compression** of the DFA transition table: instead of
256 entries per state, we need only 6-8.

### 5.5 Lookup Table

The equivalence class mapping is compiled into a 256-byte lookup table:

```rust
static CHAR_CLASS: [u8; 256] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 0, 0, 5, 0, 0,  // 0x00-0x0F
    // ...
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0,  // 0x28-0x37 (+,*)
    // ...
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,  // 0x41-0x50 (A-P)
    // ...
];
```

At runtime, classifying a byte is a single array lookup: `CHAR_CLASS[byte]`.

---

## 6. Subset Construction (NFA to DFA)

### 6.1 The Powerset Construction

The **subset construction** (also called powerset construction) converts an
NFA with `n` states into a DFA where each DFA state represents a _set_ of
NFA states.

### 6.2 Algorithm

```
  function subset_construction(nfa, partition):
      dfa_start = epsilon_closure({nfa.start})
      state_map = { dfa_start: 0 }
      worklist = [dfa_start]
      dfa = new DFA with state 0

      while worklist is not empty:
          current = worklist.pop()
          current_id = state_map[current]

          for each equivalence class c:
              // Compute move(current, c): all NFA states reachable
              // from any state in current on any byte in class c
              target = {}
              for s in current:
                  for (char_class, t) in nfa.states[s].transitions:
                      if char_class matches representative(c):
                          target.add(t)

              if target is empty: continue  // dead state

              // Take epsilon-closure
              target = epsilon_closure(target)

              // Look up or create DFA state
              if target not in state_map:
                  accept = resolve_accept(nfa, target)
                  new_id = dfa.add_state(accept)
                  state_map[target] = new_id
                  worklist.push(target)

              dfa.add_transition(current_id, c, state_map[target])

      return dfa
```

### 6.3 Worked Example

Using the NFA from section 3.5 with equivalence classes from section 5.4:

```
  Step 1: DFA start state
    D0 = epsilon_closure({0}) = {0, 1, 3, 5}
    accept = None (no accepting states in the set)

  Step 2: Process D0
    Class 1 ('+'): move({0,1,3,5}, '+') = {2}
      epsilon_closure({2}) = {2}
      D1 = {2}, accept = Fixed("+")

    Class 2 ('*'): move({0,1,3,5}, '*') = {4}
      epsilon_closure({4}) = {4}
      D2 = {4}, accept = Fixed("*")

    Class 3 ([a-zA-Z_]): move({0,1,3,5}, 'a') = {6}
      epsilon_closure({6}) = {6}
      D3 = {6}, accept = Ident

    Class 4 ([0-9]): move({0,1,3,5}, '0') = {}
      (no digit transitions from states 0,1,3,5 in our example)
      Dead state, skip.
      (With integer support: move would reach the integer accept state)

  Step 3: Process D1 = {2}
    No transitions from state 2 -> all dead. Done.

  Step 4: Process D2 = {4}
    No transitions from state 4 -> all dead. Done.

  Step 5: Process D3 = {6}
    Class 3 ([a-zA-Z_]): move({6}, 'a') = {6}
      D3 already exists -> self-loop

    Class 4 ([0-9]): move({6}, '0') = {6}
      D3 already exists -> self-loop

  Resulting DFA:
  ┌──────┬────────────┬──────────┬──────────┬──────────┐
  │State │ Class 1(+) │ Class 2(*)│ Class 3  │ Class 4  │
  │      │            │          │ (letter) │ (digit)  │
  ├──────┼────────────┼──────────┼──────────┼──────────┤
  │ D0   │    D1      │    D2    │    D3    │   dead   │
  │ D1*  │   dead     │   dead   │   dead   │   dead   │
  │ D2*  │   dead     │   dead   │   dead   │   dead   │
  │ D3*  │   dead     │   dead   │    D3    │    D3    │
  └──────┴────────────┴──────────┴──────────┴──────────┘
  * = accepting state

  D1 accepts Fixed("+")
  D2 accepts Fixed("*")
  D3 accepts Ident
```

### 6.4 Accept State Resolution (Priority)

When a DFA state represents multiple NFA states, some of which are accepting,
the highest-priority token wins. This is how PraTTaIL handles keyword vs.
identifier ambiguity:

```
  NFA states in a DFA state: { ident_accept, keyword_accept }

  ident_accept:   priority = 1  (Ident)
  keyword_accept: priority = 10 (Fixed("error"))

  Winner: keyword_accept (priority 10 > 1)

  So the DFA state accepts Fixed("error"), not Ident.
```

This means that the input `error` is lexed as the keyword token `KwError`,
not as an identifier `Ident("error")`. However, `errors` (with trailing `s`)
would be lexed as `Ident("errors")` because the keyword pattern does not
match.

---

## 7. DFA Minimization (Hopcroft's Algorithm)

### 7.1 Motivation

Subset construction may produce DFA states that behave identically -- they
accept the same token and transition to equivalent states on all inputs.
Minimization merges these redundant states, producing the unique minimal DFA.

### 7.2 The Myhill-Nerode Theorem

Two DFA states `p` and `q` are **equivalent** (written `p ~ q`) if and only
if for every string `w`, the DFA reaches an accepting state from `p` on `w`
if and only if it reaches an accepting state from `q` on `w`. The
**Myhill-Nerode theorem** guarantees that the minimal DFA is unique (up to
isomorphism).

### 7.3 Hopcroft's Algorithm

Hopcroft's algorithm (1971) computes the minimal DFA in O(n log n) time:

```
  function minimize_dfa(dfa):
      // Step 1: Initial partition by accept token
      partition = group states by their accept token kind
      // e.g., {non-accepting states}, {accept Fixed("+")},
      //        {accept Ident}, ...

      worklist = all partitions

      // Step 2: Iterative refinement
      while worklist is not empty:
          splitter = worklist.pop()

          for each equivalence class c:
              for each partition P:
                  // Split P into:
                  //   P1 = states that transition to splitter on c
                  //   P2 = states that do NOT transition to splitter on c

                  if both P1 and P2 are non-empty:
                      replace P with the larger of {P1, P2}
                      create new partition for the smaller
                      add the smaller to the worklist

      // Step 3: Build minimized DFA
      // Each final partition becomes one state in the minimal DFA
      // Representative of each partition determines transitions and accept
```

### 7.4 Worked Example

Consider a DFA for `{=, ==}`:

```
  Before minimization:
    D0 (start)
    D1 (accept: Fixed("="))     -- after one '='
    D2 (accept: Fixed("=="))    -- after two '='

  Transitions:
    D0 ──'='──> D1
    D1 ──'='──> D2

  Initial partition:
    P0 = {D0}         (non-accepting)
    P1 = {D1}         (accept Fixed("="))
    P2 = {D2}         (accept Fixed("=="))

  Refinement:
    All partitions are singletons -> no further splitting possible.
    The DFA is already minimal.

  Minimized DFA (unchanged):
    D0 ──'='──> D1 ──'='──> D2

    D0: start, non-accepting
    D1: accept Fixed("=")
    D2: accept Fixed("==")
```

Now consider a case where minimization helps -- a grammar with
`{$proc, $name, $int}`:

```
  Before minimization (naive construction):
    D0 (start)
    D1a ──'p'──> D2a ──'r'──> D3a ──'o'──> D4a ──'c'──> D5a(accept:Dollar)
    D1b ──'n'──> D2b ──'a'──> D3b ──'m'──> D4b ──'e'──> D5b(accept:Dollar)
    D1c ──'i'──> D2c ──'n'──> D3c ──'t'──> D4c(accept:Dollar)

    All share: D0 ──'$'──> D_dollar

  After minimization:
    The shared '$' prefix collapses into a single state.
    States that accept the same token kind and have the same
    future behavior are merged.
```

### 7.5 Complexity

Hopcroft's algorithm runs in **O(n * k * log n)** time, where `n` is the
number of DFA states and `k` is the alphabet size (number of equivalence
classes). Since `k` is typically 6-18 for PraTTaIL grammars, this is
effectively O(n log n).

---

## 8. Maximal Munch

### 8.1 The Principle

**Maximal munch** (also called "longest match") is the rule that the lexer
always produces the longest possible token. For example, given the input
`===`:

```
  After '=':   DFA is in accept state for "="
  After '==':  DFA is in accept state for "=="
  After '===': DFA has no transition from "==" on '=' (dead state)

  Maximal munch: produce "==" (the longest match), then restart from '='
```

### 8.2 Implementation

The lexer maintains two pieces of state during tokenization:

```
  state:        Current DFA state
  last_accept:  Most recent accepting state and position

  Algorithm:
  1. Start at DFA state 0 and current position
  2. For each byte:
     a. Classify the byte (lookup in CHAR_CLASS)
     b. Compute the next DFA state
     c. If dead state (u32::MAX), stop
     d. If accepting state, record (state, position) as last_accept
  3. If last_accept exists, emit the token and restart from last_accept.end
  4. If no last_accept, report a lexer error
```

### 8.3 Why Maximal Munch Requires Backtracking

Consider lexing the input `error_handler` in a grammar where `error` is a
keyword:

```
  After 'e':     DFA in ident state (also shared with keyword "error" prefix)
  After 'er':    DFA in ident state
  After 'err':   DFA in ident state
  After 'erro':  DFA in ident state
  After 'error': DFA in accept state for Fixed("error") AND Ident
                  Priority: Fixed("error") wins (priority 10 > 1)
                  Record last_accept = (Fixed("error"), pos=5)
  After 'error_': DFA in accept state for Ident (the '_' continues ident)
                  Record last_accept = (Ident, pos=6)
  ... continues through 'error_handler'
  After 'error_handler': DFA in accept state for Ident
                  Record last_accept = (Ident, pos=13)
  Next byte: EOF or whitespace -> dead state

  Result: Ident("error_handler")   (maximal munch chose the longest match)
```

The keyword `error` is only produced when it is a _complete_ token (not a
prefix of a longer identifier). This is why priority alone is insufficient;
maximal munch is essential.

---

## 9. Priority Handling

### 9.1 The Priority System

PraTTaIL assigns numeric priorities to each token kind:

```
  ┌──────────────────┬──────────┐
  │ Token Kind       │ Priority │
  ├──────────────────┼──────────┤
  │ Eof              │    0     │
  │ Ident            │    1     │
  │ Integer          │    2     │
  │ Float            │    3     │
  │ Dollar           │    5     │
  │ DoubleDollar     │    6     │
  │ Fixed(keyword)   │   10     │
  │ True / False     │   10     │
  └──────────────────┴──────────┘
```

### 9.2 When Priority Matters

Priority resolves ambiguity when a DFA state corresponds to multiple NFA
accept states. This happens specifically with keywords:

```
  Input "true" reaches a DFA state containing:
    - NFA accept for Ident (matches [a-zA-Z_][a-zA-Z0-9_]*)
    - NFA accept for True  (matches "true" exactly)

  Priority(True) = 10 > Priority(Ident) = 1
  Result: Token::Boolean(true)
```

### 9.3 Priority Combined with Maximal Munch

Priority and maximal munch interact:

```
  Input "trueish":
    After "true":  accept(True, priority=10) and accept(Ident, priority=1)
                   Record last_accept with True (higher priority)
    After "truei": accept(Ident, priority=1)
                   Record last_accept with Ident
    ... continues
    After "trueish": accept(Ident)
                   Record last_accept with Ident

  Result: Ident("trueish")   (maximal munch overrides keyword priority)
```

The correct behavior is that `true` is a keyword only when it is not a prefix
of a longer identifier. This falls out naturally from the combination of
maximal munch and priority.

---

## 10. Code Generation

### 10.1 Two Strategies

PraTTaIL generates lexer code using one of two strategies:

```
  ┌────────────────────────────────────────────────────────────┐
  │ DFA states <= 30: Direct-coded (match arms)                │
  │ DFA states >  30: Table-driven (flat transition array)     │
  └────────────────────────────────────────────────────────────┘
```

### 10.2 Direct-Coded Lexer

Each DFA state becomes a match arm in a nested match expression:

```rust
fn dfa_next(state: u32, class: u8) -> u32 {
    match state {
        0 => match class {
            1 => 1,     // '+' class -> state 1
            2 => 2,     // '*' class -> state 2
            3 => 3,     // letter class -> state 3
            4 => 4,     // digit class -> state 4
            _ => u32::MAX,  // dead
        },
        3 => match class {
            3 => 3,     // letter -> stay in ident state
            4 => 3,     // digit -> stay in ident state
            _ => u32::MAX,
        },
        // ... other states
        _ => u32::MAX,
    }
}
```

This compiles to efficient jump tables or if-else chains in the Rust compiler.

### 10.3 Table-Driven Lexer

For larger DFAs, a flat transition table is more cache-friendly:

```rust
// Flat array: TRANSITIONS[state * NUM_CLASSES + class] = next_state
static TRANSITIONS: [u32; NUM_STATES * NUM_CLASSES] = [
    // State 0:  class0  class1  class2  class3  class4  ...
                 DEAD,   1,      2,      3,      4,      ...
    // State 1:  ...
                 DEAD,   DEAD,   DEAD,   DEAD,   DEAD,   ...
    // State 3:  ...
                 DEAD,   DEAD,   DEAD,   3,      3,      ...
    // ...
];

// Transition function is a single array lookup:
let next = TRANSITIONS[state as usize * NUM_CLASSES + class as usize];
```

### 10.4 Accept Token Mapping

A separate function maps accepting states to tokens:

```rust
fn accept_token(state: u32, text: &str) -> Option<Token> {
    match state {
        1 => Some(Token::Plus),
        2 => Some(Token::Star),
        3 => Some(Token::Ident(text.to_string())),
        4 => Some(Token::Integer(text.parse().expect("invalid integer"))),
        _ => None,
    }
}
```

Note that `text` is passed to the accept function. For fixed terminals like
`+` and `*`, the text is ignored. For identifier and literal tokens, the text
is used to construct the token value.

### 10.5 The Complete Lex Function

```rust
pub fn lex(input: &str) -> Result<Vec<(Token, Span)>, String> {
    let bytes = input.as_bytes();
    let mut pos = 0;
    let mut tokens = Vec::new();

    while pos < bytes.len() {
        // Skip whitespace
        while pos < bytes.len() && is_whitespace(bytes[pos]) {
            pos += 1;
        }
        if pos >= bytes.len() { break; }

        let start = pos;
        let mut state: u32 = 0;
        let mut last_accept: Option<(u32, usize)> = None;

        // Maximal munch loop
        while pos < bytes.len() {
            let class = CHAR_CLASS[bytes[pos] as usize];
            let next = dfa_next(state, class);
            if next == u32::MAX { break; }  // Dead state
            state = next;
            pos += 1;
            if accept_token(state, &input[start..pos]).is_some() {
                last_accept = Some((state, pos));
            }
        }

        match last_accept {
            Some((accept_state, end)) => {
                pos = end;  // Backtrack to end of longest match
                let text = &input[start..end];
                if let Some(token) = accept_token(accept_state, text) {
                    tokens.push((token, Span { start, end }));
                }
            }
            None => {
                return Err(format!(
                    "unexpected character '{}' at position {}",
                    bytes[start] as char, start
                ));
            }
        }
    }

    tokens.push((Token::Eof, Span { start: pos, end: pos }));
    Ok(tokens)
}
```

---

## 11. The Complete Pipeline

Putting it all together, PraTTaIL's lexer generation pipeline is:

```
  Grammar rules
       │
       ▼
  ┌────────────────────────────────────┐
  │ 1. Extract terminal patterns       │  extract_terminals()
  │    from grammar rules              │
  │    + determine builtin needs       │
  └─────────────┬──────────────────────┘
                │
                ▼
  ┌────────────────────────────────────┐
  │ 2. Build NFA via Thompson's        │  build_nfa()
  │    construction:                    │
  │    - One fragment per terminal     │
  │    - Fragments for builtins        │
  │    - Alternation via epsilon edges │
  └─────────────┬──────────────────────┘
                │
                ▼
  ┌────────────────────────────────────┐
  │ 3. Compute alphabet equivalence    │  compute_equivalence_classes()
  │    classes:                         │
  │    - Byte signatures per state     │
  │    - Group by identical signature  │
  │    - Typically 6-18 classes        │
  └─────────────┬──────────────────────┘
                │
                ▼
  ┌────────────────────────────────────┐
  │ 4. Subset construction (NFA->DFA)  │  subset_construction()
  │    - Epsilon-closure of start      │
  │    - Worklist algorithm            │
  │    - Priority-based accept resolve │
  └─────────────┬──────────────────────┘
                │
                ▼
  ┌────────────────────────────────────┐
  │ 5. Hopcroft's DFA minimization     │  minimize_dfa()
  │    - Partition by accept token     │
  │    - Refine by transition behavior │
  │    - Merge equivalent states       │
  └─────────────┬──────────────────────┘
                │
                ▼
  ┌────────────────────────────────────┐
  │ 6. Code generation                  │  generate_lexer_code()
  │    - Token enum definition         │
  │    - Equivalence class table       │
  │    - DFA transition function       │
  │      (direct-coded or table)       │
  │    - Accept token function         │
  │    - Lex function with maximal     │
  │      munch                         │
  └────────────────────────────────────┘
                │
                ▼
          TokenStream
       (Rust source code)
```

---

## 12. Complexity Analysis

### 12.1 Build Time (Parser Generator)

```
  ┌─────────────────────────┬──────────────────────────────────┐
  │ Phase                   │ Time Complexity                   │
  ├─────────────────────────┼──────────────────────────────────┤
  │ Thompson's construction │ O(|R|) where |R| = sum of        │
  │                         │        terminal lengths           │
  │ Equivalence classes     │ O(256 * |NFA|) = O(|NFA|)        │
  │ Subset construction     │ O(2^|NFA|) worst case            │
  │                         │ O(|DFA| * k) practical           │
  │ Hopcroft minimization   │ O(|DFA| * k * log|DFA|)          │
  │ Code generation         │ O(|minDFA| * k)                  │
  └─────────────────────────┴──────────────────────────────────┘
  k = number of equivalence classes (typically 6-18)
```

The theoretical worst case for subset construction is exponential (each
subset of NFA states could become a DFA state). In practice, for the
simple regular expressions used in lexer terminals, the DFA is small --
typically fewer than 30 states even for grammars with 20+ terminals.

### 12.2 Run Time (Generated Lexer)

```
  ┌─────────────────────────┬──────────────────────────────────┐
  │ Operation               │ Time Complexity                   │
  ├─────────────────────────┼──────────────────────────────────┤
  │ Classify one byte       │ O(1) -- array lookup              │
  │ DFA transition          │ O(1) -- match arm or table lookup │
  │ Lex one token           │ O(|token|) -- scan its bytes      │
  │ Lex entire input        │ O(n) where n = input length       │
  │ Space (auxiliary)       │ O(1) -- just DFA state + position │
  └─────────────────────────┴──────────────────────────────────┘
```

The generated lexer processes each byte exactly once (modulo maximal munch
backtracking, which is bounded by the length of the longest terminal
pattern). The overall complexity is O(n) in the length of the input.

---

## 13. Summary of Key Algorithms

| Algorithm | Input | Output | Purpose |
|---|---|---|---|
| Thompson's construction | Terminal patterns | NFA | Build recognizer |
| Epsilon-closure | Set of NFA states | Larger set | Bridge NFA to DFA |
| Equivalence classes | NFA | Byte-to-class map | Compress alphabet |
| Subset construction | NFA + classes | DFA | Determinize |
| Hopcroft minimization | DFA | Minimal DFA | Merge equivalent states |
| Code generation | Minimal DFA + classes | Rust code | Produce lexer |
| Maximal munch | Token stream | Longest match | Resolve ambiguity |
| Priority | Multiple accepts | Single token | Keyword vs. ident |

Each algorithm is a standard result in automata theory, applied here in
a specific pipeline configuration tailored to the needs of parser generator
lexer construction.

---

## References

1. Thompson, K. (1968). "Regular Expression Search Algorithm."
   _Communications of the ACM_, 11(6), pp. 419--422.
2. Hopcroft, J. E. (1971). "An n log n Algorithm for Minimizing States in a
   Finite Automaton." _Theory of Machines and Computations_, pp. 189--196.
3. Aho, A. V., Sethi, R., & Ullman, J. D. (1986). _Compilers: Principles,
   Techniques, and Tools_ (the "Dragon Book"). Addison-Wesley. Chapters 3-4.
4. Sipser, M. (2012). _Introduction to the Theory of Computation_. 3rd ed.
   Cengage Learning. Chapter 1.
5. Watson, B. W. (1995). "Taxonomies and Toolkits of Regular Language
   Algorithms." PhD dissertation, Eindhoven University of Technology.
