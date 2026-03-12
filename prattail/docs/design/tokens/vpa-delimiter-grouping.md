# VPA-Based Delimiter Verification and Runtime Grouping

## Overview

Programming languages are built on nested structure: parentheses enclose
subexpressions, braces delimit blocks, brackets surround indices. Getting
this nesting right is so fundamental that it deserves a dedicated formal
model -- not ad-hoc stack matching, but a well-studied automaton class with
proven closure and decidability properties.

Visibly Pushdown Automata (VPA) are that model. PraTTaIL uses VPAs at
compile time to verify that the `tokens { ... }` block defines a
well-nested delimiter structure, and at runtime to group flat token streams
into hierarchical `TokenTree` structures in linear time.


## 1. Intuition: Why VPAs Are the Right Model

A pushdown automaton (PDA) can push and pop its stack based on internal
non-deterministic choices -- and this freedom makes equivalence and
inclusion undecidable. A VPA constrains the stack discipline to be
*input-driven*: the input symbol alone determines whether the automaton
pushes, pops, or leaves the stack unchanged.

This one restriction -- making stack operations "visible" in the input --
recovers all the nice properties of finite automata:

```
Finite automata (regular)     VPA (visibly pushdown)     PDA (context-free)
        |                            |                          |
   all decidable              all decidable              equivalence undecidable
   closed under               closed under               NOT closed under
   complement,                complement,                complement or
   intersection               intersection               intersection
```

The key insight for PraTTaIL: every delimiter in a `tokens { ... }` block
already declares its stack behavior through `push_mode` (push) and `is_pop`
(pop) annotations. These annotations define a natural three-way partition
of the token alphabet -- exactly what a VPA requires.

```
push_mode = Some("...")  -->  Call symbol    (pushes onto stack)
is_pop = true            -->  Return symbol  (pops from stack)
otherwise                -->  Internal symbol (stack-neutral)
```

This correspondence means VPA verification comes "for free" from
information the grammar author already provides.


## 2. The Formal VPA Model

A VPA is a tuple:

    A = (Q, Sigma_c + Sigma_r + Sigma_int, Gamma, delta, q_0, F)

where:

- **Q** is a finite set of states
- **Sigma = Sigma_c (call) + Sigma_r (return) + Sigma_int (internal)** is
  the partitioned input alphabet
- **Gamma** is the stack alphabet
- **delta** consists of three transition functions:
  - **delta_c : Q x Sigma_c --> Q x Gamma** (call: read symbol, push, move)
  - **delta_r : Q x Sigma_r x Gamma --> Q** (return: read symbol, pop, move)
  - **delta_int : Q x Sigma_int --> Q** (internal: read symbol, no stack change)
- **q_0 in Q** is the initial state
- **F subset Q** is the set of accepting states

A word w in Sigma* is accepted iff A can consume w starting from q_0 with
an empty stack and end in some state in F (with empty stack).

### Closure Properties (Alur & Madhusudan, 2004)

The class of visibly pushdown languages (VPL) is closed under:

- **Union**: L(A_1) union L(A_2) via product construction
- **Intersection**: L(A_1) intersect L(A_2) via product construction
- **Complement**: ~L(A) via determinization + acceptance swap
- **Concatenation** and **Kleene star**

These closures make VPLs strictly more expressive than regular languages
while retaining decidable equivalence and inclusion -- both reduce to
complement + intersection + emptiness, all of which are effective.


## 3. Compile-Time Verification

### 3.1 Alphabet Construction: `build_vpa_alphabet_from_modes()`

The function `build_vpa_alphabet_from_modes()` in `vpa.rs` classifies every
token from both the default lexer mode and all named modes into the VPA
alphabet partition:

```rust
pub fn build_vpa_alphabet_from_modes(
    default_tokens: &[CustomTokenSpec],
    modes: &[LexerModeSpec],
) -> VpaAlphabet
```

Classification logic per `CustomTokenSpec`:

| Field            | VPA class   | Meaning                        |
|------------------|-------------|--------------------------------|
| `push_mode.is_some()` | Call (Sigma_c)   | Opens a nested context        |
| `is_pop == true`      | Return (Sigma_r) | Closes a nested context       |
| otherwise             | Internal (Sigma_int) | No nesting effect         |

The resulting `VpaAlphabet` holds three `HashSet<String>` fields:
`call_symbols`, `return_symbols`, and `internal_symbols`.

### 3.2 `VpaAlphabet` from `CustomTokenSpec` + `LexerModeSpec`

The construction iterates all token specs across all modes, applying the
classification closure to each. A single unified alphabet is produced --
tokens with the same name but defined in different modes receive the same
classification (the first classification wins).

```
tokens {
    LParen "("  push_mode("paren_body")   // --> Call
    RParen ")"  is_pop                     // --> Return
    Plus   "+"                              // --> Internal
    Ident  /[a-z]+/                         // --> Internal
}
```

### 3.3 Well-Nesting Verification

Well-nesting means every call symbol has a matching return symbol at the
same nesting depth. VPA closure under complement makes this checkable:

1. Build VPA A from the grammar's delimiter structure
2. Build the complement VPA ~A (determinize, then swap accepting states)
3. Check emptiness of L(A) intersect L(~A_balanced)

If the intersection is non-empty, there exist token sequences where
delimiters are unbalanced. The `complement()` function in `vpa.rs`
implements step 2:

```rust
pub fn complement(vpa: &Vpa) -> Vpa {
    let det = vpa.determinize();     // Subset construction
    // Swap accepting <--> non-accepting states
    ...
}
```

### 3.4 Diagnostics

Two VPA-related diagnostics are emitted during pipeline analysis:

**V01 -- vpa-determinizable** (Note): Fires when the grammar's structured
sublanguage admits a deterministic VPA. This is good news -- it means the
delimiter structure can be verified with zero backtracking.

**V02 -- vpa-alphabet-mismatch** (Warning): Fires when a token name is
classified as both Call and Return across different modes. This indicates a
delimiter inconsistency that may cause incorrect nesting.


## 4. Runtime Skip Table: `build_skip_table()`

At runtime, the VPA alphabet classification enables an O(n) single-pass
algorithm to find matching delimiters across the entire token stream.

```rust
pub fn build_skip_table<T>(
    tokens: &[(T, Range)],
    classify: impl Fn(&T) -> SymbolKind,
) -> Vec<Option<usize>>
```

**Algorithm**: Maintain a stack of opener indices. For each token:
- **Call**: push current index onto stack
- **Return**: pop stack; if non-empty, record `skip_table[opener] = i`
- **Internal**: skip

**Invariants**:
- `skip_table[i] = Some(j)` implies i < j and tokens[i] is Call, tokens[j]
  is Return
- `skip_table[i] = None` for Internal tokens and unmatched openers
- Unmatched closers (Return with empty stack) produce no entry

### Worked Example

Input: `( a + ( b * c ) )`

```
Index:   0    1   2   3    4   5   6   7   8
Token:   (    a   +   (    b   *   c   )   )
Kind:    C    I   I   C    I   I   I   R   R
```

Stack trace:

```
i=0  (   Call    --> push 0           stack: [0]
i=1  a   Int     --> skip             stack: [0]
i=2  +   Int     --> skip             stack: [0]
i=3  (   Call    --> push 3           stack: [0, 3]
i=4  b   Int     --> skip             stack: [0, 3]
i=5  *   Int     --> skip             stack: [0, 3]
i=6  c   Int     --> skip             stack: [0, 3]
i=7  )   Return  --> pop 3, set [3]=7 stack: [0]
i=8  )   Return  --> pop 0, set [0]=8 stack: []
```

Result:

```
skip_table = [Some(8), None, None, Some(7), None, None, None, None, None]
               ^                     ^
               |                     |
        outer ( matches )      inner ( matches )
        at index 0 and 8       at index 3 and 7
```


## 5. `TokenTree<T>` -- Hierarchical Token Representation

The `TokenTree<T>` enum bridges flat token streams and tree-structured
representations:

```rust
pub enum TokenTree<T> {
    /// A leaf token (non-delimiter or unmatched delimiter).
    Token(T, Range),
    /// A delimited group: opener, contents, closer.
    Group {
        open:     (T, Range),
        close:    (T, Range),
        children: Vec<TokenTree<T>>,
    },
}
```

### 5.1 `build_token_tree()`: O(n) Construction

```rust
pub fn build_token_tree<T: Clone>(
    tokens: &[(T, Range)],
    skip_table: &[Option<usize>],
    classify: impl Fn(&T) -> SymbolKind,
) -> Vec<TokenTree<T>>
```

The algorithm recursively partitions the token stream using the skip table.
For a Call token at index i with `skip_table[i] = Some(j)`:

- The opener is `tokens[i]`
- The closer is `tokens[j]`
- Children are built by recursing into the range `[i+1, j)`
- Processing continues at `j+1`

Unmatched openers (`skip_table[i] = None`) are demoted to leaf
`TokenTree::Token` nodes.

### 5.2 Worked Example

From the skip table above, `( a + ( b * c ) )` produces:

```
Group {
    open:  ( at 0,
    close: ) at 8,
    children: [
        Token(a),
        Token(+),
        Group {
            open:  ( at 3,
            close: ) at 7,
            children: [
                Token(b),
                Token(*),
                Token(c),
            ]
        }
    ]
}
```

Visually:

```
            Group("(")
           /    |     \
       Token  Token   Group("(")
        "a"    "+"    /    |    \
                  Token  Token  Token
                   "b"    "*"    "c"
```


## 6. Error Recovery Enhancement: O(1) Skip-Ahead

During error recovery, when the parser encounters a syntax error inside a
delimited group, it needs to skip past the closing delimiter to continue
parsing. Without a skip table, this requires an O(n) forward scan counting
nesting levels. With the precomputed skip table, the recovery engine
performs a single O(1) lookup:

```
skip_table[open_pos]  -->  Some(close_pos)
```

This transforms worst-case O(n^2) error recovery (nested groups with
cascading errors) into O(n) total.

The skip table integrates with PraTTaIL's tiered error recovery system: the
recovery engine consults the skip table before attempting more expensive
heuristic strategies, using the VPA-verified delimiter structure as a
reliable anchor point.


## 7. Feature Gate

All VPA functionality is gated behind the `vpa` feature flag:

```toml
[features]
vpa = []
```

When `vpa` is disabled, the VPA alphabet construction, skip table, token
tree, complement, determinization, and V01/V02 diagnostics are all compiled
out. The parser generator still works -- it simply lacks delimiter
verification and O(1) skip-ahead recovery.

The relevant source file is `prattail/src/vpa.rs`.


## 8. Complexity Summary

| Operation                     | Time     | Space   |
|-------------------------------|----------|---------|
| `build_vpa_alphabet_from_modes` | O(t)   | O(t)    |
| `build_skip_table`            | O(n)     | O(n)    |
| `build_token_tree`            | O(n)     | O(n)    |
| `complement` (determinize + swap) | O(2^k) | O(2^k) |
| Skip-ahead during recovery    | O(1)     | --      |

Where t = total token specs, n = token stream length, k = number of VPA
states.

Note: the exponential cost of determinization applies only at compile time
and only to the VPA's state set (typically small: one state per lexer mode
pair). Runtime operations are strictly linear.


## 9. Integration Diagram

```
tokens { ... }                    Grammar definition
      |
      v
build_vpa_alphabet_from_modes()   Classify tokens into Sigma_c/Sigma_r/Sigma_int
      |
      +---> VpaAlphabet           Three-way partition
      |         |
      |         +---> [compile-time] VPA construction + complement + emptiness
      |         |         |
      |         |         v
      |         |     V01/V02 diagnostics
      |         |
      |         +---> [runtime] build_skip_table()
      |                   |
      |                   v
      |               skip_table: Vec<Option<usize>>
      |                   |
      |                   +---> build_token_tree()
      |                   |         |
      |                   |         v
      |                   |     Vec<TokenTree<T>>
      |                   |
      |                   +---> O(1) error recovery skip-ahead
      |
      v
  Parser / tree-automata validation (see tree-automata-validation.md)
```


## References

- **Alur, R. & Madhusudan, P. (2004)**. "Visibly pushdown languages."
  *Proceedings of the 36th Annual ACM Symposium on Theory of Computing
  (STOC)*, pp. 202--211. Introduces VPAs and proves closure under Boolean
  operations plus decidable equivalence and inclusion.

- **Alur, R. & Madhusudan, P. (2009)**. "Adding nesting structure to
  words." *Journal of the ACM*, 56(3), Article 16. Extended journal version
  with applications to XML validation and software model checking.

- **Alur, R., Kumar, V., Madhusudan, P. & Viswanathan, M. (2005)**.
  "Congruences for visibly pushdown languages." *Proceedings of the 32nd
  International Colloquium on Automata, Languages and Programming (ICALP)*,
  pp. 1102--1114. Myhill-Nerode theorem for VPLs, enabling state
  minimization of deterministic VPAs.
