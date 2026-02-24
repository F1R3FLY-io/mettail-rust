# Layer 3: Operator Precedence

Operator precedence is the third layer in PraTTaIL's six-layer model. It
resolves ambiguity between competing operators within a single grammar category
using **binding power pairs** and the **Pratt parsing loop**. This document
assumes basic familiarity with Pratt parsing; see
[theory/pratt-parsing.md](../../theory/pratt-parsing.md) for the full algorithm.

**Source files:**
- `prattail/src/binding_power.rs` -- BP assignment, associativity
- `prattail/src/pratt.rs` -- Led chain ordering, prefix/infix/postfix handlers
- `prattail/src/trampoline.rs` -- Stack-safe trampolined Pratt loop

**Cross-references:**
- [theory/pratt-parsing.md](../../theory/pratt-parsing.md) §2-5, §7

---

## 1. The Operator Ambiguity Problem

An expression like `1 + 2 * 3` has two legitimate parse trees:

```
  Tree A: (1 + 2) * 3 = 9       Tree B: 1 + (2 * 3) = 7

      (*)                           (+)
     /   \                         /   \
   (+)    3                       1    (*)
  / \                                  / \
 1   2                                2   3
```

Similarly, `5 - 3 - 1` could be `(5 - 3) - 1 = 1` or `5 - (3 - 1) = 3`
(associativity), and `-5!` could be `(-5)!` or `-(5!)` (prefix vs postfix).

Each of these is a **disambiguation decision** that the grammar must make
deterministically. PraTTaIL makes all such decisions through a single mechanism:
**binding power comparison**.

---

## 2. Binding Power Pairs: The Core Disambiguation Decision

Every operator has a **binding power pair** `(left_bp, right_bp)`. The Pratt loop
makes exactly one comparison at each decision point:

```
Is left_bp < min_bp?
  YES → Stop: the parent operator binds tighter (or equally, for left-assoc)
  NO  → Continue: this operator binds tighter than the parent
```

This single comparison resolves **all** of: precedence, associativity, and
prefix/postfix ordering.

### 2.1 The Tug-of-War Metaphor

Think of adjacent operators as engaged in a tug-of-war over the operand between
them. The operand goes to whichever operator pulls harder (has higher binding
power on the adjacent side):

```
Expression: 1 + 2 * 3

         1    +    2    *    3
              ↑    ↑    ↑
           right  ???  left
           bp=3        bp=4

  + has right_bp = 3 (pulling right on 2)
  * has left_bp  = 4 (pulling left on 2)

  4 > 3 → * wins → 2 belongs to *
  Result: 1 + (2 * 3)
```

### 2.2 The Formal Rule

Given the Pratt loop state where `min_bp` is the right binding power of the
parent operator and `left_bp` is the left binding power of the current operator:

```
left_bp < min_bp  →  BREAK  (parent wins, stop extending expression)
left_bp ≥ min_bp  →  BIND   (current operator wins, extend expression)
```

---

## 3. Precedence Disambiguation

Different operators have different BP magnitudes. Operators declared later in
the grammar get higher binding power values (bind tighter).

### 3.1 BP Assignment Algorithm

PraTTaIL assigns BPs automatically from declaration order (`binding_power.rs`,
lines 210-280):

```
Starting precedence = 2  (reserves 0 for entry, 1 for future use)

For each operator in declaration order (non-postfix first pass):
  Left-associative:  bp = (precedence, precedence + 1); precedence += 2
  Right-associative: bp = (precedence + 1, precedence); precedence += 2
```

### 3.2 Worked Trace: `"1 + 2 * 3 - 4"`

Assume `+` and `-` are at precedence level 2, `*` at level 4 (declared later):

```
Operator BPs:
  + : (2, 3)    left-assoc
  - : (2, 3)    left-assoc
  * : (4, 5)    left-assoc
```

Parse trace with disambiguation decisions annotated:

```
Call: parse_Int(min_bp=0)

  Step 1: PREFIX — parse literal "1"
          lhs = NumLit(1)

  Step 2: INFIX LOOP — see "+"
          + has left_bp=2, min_bp=0
          Is 2 < 0? NO → + binds
          Consume "+", recurse: parse_Int(min_bp=3)
            │
            │  Step 2a: PREFIX — parse literal "2"
            │           lhs = NumLit(2)
            │
            │  Step 2b: INFIX LOOP — see "*"
            │           * has left_bp=4, min_bp=3
            │           Is 4 < 3? NO → * binds         ← PRECEDENCE DECISION
            │           Consume "*", recurse: parse_Int(min_bp=5)
            │             │
            │             │  Step 2c: PREFIX — parse literal "3"
            │             │           lhs = NumLit(3)
            │             │
            │             │  Step 2d: INFIX LOOP — see "-"
            │             │           - has left_bp=2, min_bp=5
            │             │           Is 2 < 5? YES → stop    ← PRECEDENCE DECISION
            │             │
            │             └─ Return NumLit(3)
            │
            │  lhs = Mul(NumLit(2), NumLit(3))
            │
            │  Step 2e: INFIX LOOP — see "-"
            │           - has left_bp=2, min_bp=3
            │           Is 2 < 3? YES → stop              ← ASSOCIATIVITY DECISION
            │
            └─ Return Mul(NumLit(2), NumLit(3))

  lhs = Add(NumLit(1), Mul(NumLit(2), NumLit(3)))

  Step 3: INFIX LOOP — see "-"
          - has left_bp=2, min_bp=0
          Is 2 < 0? NO → - binds
          Consume "-", recurse: parse_Int(min_bp=3)
            │
            │  PREFIX — parse literal "4"
            │  INFIX LOOP — Eof, stop
            │
            └─ Return NumLit(4)

  lhs = Sub(Add(NumLit(1), Mul(NumLit(2), NumLit(3))), NumLit(4))

Result: ((1 + (2 * 3)) - 4)
```

**Four disambiguation decisions were made**, all via the same `left_bp < min_bp`
comparison, each resolving a different ambiguity.

---

## 4. Associativity Disambiguation

Associativity determines how **same-precedence** operators group. PraTTaIL
encodes associativity in the **asymmetry** of the BP pair.

### 4.1 Left-Associative: `left_bp < right_bp`

For left-associative `+` with pair `(2, 3)`:

```
Expression: a + b + c
                  ↑
            Second + has left_bp=2, min_bp=3 (from first +'s right_bp)
            Is 2 < 3? YES → stop

Result: (a + b) + c  (left-associated)
```

The same operator **loses** to itself because its `left_bp` (2) is less than its
own `right_bp` (3), which becomes the `min_bp` for the recursive call.

### 4.2 Right-Associative: `left_bp > right_bp`

For right-associative `^` with pair `(5, 4)`:

```
Expression: a ^ b ^ c
                  ↑
            Second ^ has left_bp=5, min_bp=4 (from first ^'s right_bp)
            Is 5 < 4? NO → ^ binds (continue)

Result: a ^ (b ^ c)  (right-associated)
```

The same operator **wins** against itself because its `left_bp` (5) is not less
than its own `right_bp` (4).

### 4.3 The Asymmetry Principle

```
  Left-Associative                  Right-Associative

  left_bp < right_bp                left_bp > right_bp
  (2, 3)                            (5, 4)

  Same op:  2 < 3 = YES → stop      Same op:  5 < 4 = NO → continue
  Result:   (a + b) + c             Result:   a ^ (b ^ c)

  ┌────────────────────────────┐    ┌────────────────────────────┐
  │  ◀── left_bp  right_bp ──► │    │  ◀── right_bp  left_bp ──► │
  │       (2)       (3)        │    │       (4)       (5)        │
  │                            │    │                            │
  │  Operand is "pushed right" │    │  Operand is "pushed left"  │
  │  (stays with left operator)│    │  (moves to right operator) │
  └────────────────────────────┘    └────────────────────────────┘
```

The `associativity()` method (`binding_power.rs`, lines 71-79) formalizes this:

```rust
pub fn associativity(&self) -> Associativity {
    if self.left_bp < self.right_bp {
        Associativity::Left
    } else {
        Associativity::Right
    }
}
```

---

## 5. Three-Tier BP Hierarchy

PraTTaIL assigns binding powers in three tiers to ensure correct interaction
between prefix, infix, and postfix operators.

### 5.1 The Hierarchy

```
  Let M = max infix BP (highest-precedence infix operator's right BP)

  BP Number Line:
  ────────────────────────────────────────────────────────► higher BP
  0        2      ...      M      M+2         M+4   ...
  ↑        ↑               ↑       ↑            ↑
  entry    infix range     max   prefix BP    postfix range
           (lowest prec    infix  (all unary   (start at M+4,
            operators      BP     prefixes     one per postfix
            first)                share M+2)   operator)
```

**Infix operators:** BP range `[2, P-1]`, assigned from declaration order.

**Unary prefix operators:** BP = P (one tier above all infix). This ensures that
prefix operators bind tighter than any infix operator but looser than postfix.

**Postfix operators:** BP range `[P+2, ...]`, highest tier. This ensures that
postfix operators bind tightest of all.

### 5.2 Automatic Assignment

The algorithm (`binding_power.rs`, lines 228-276) uses a two-pass approach:

```
Pass 1: Assign BPs to all non-postfix operators (infix + mixfix)
        Produces infix BP range [2, precedence-1]

        Prefix BP = precedence     (one step above max infix)

Pass 2: Assign BPs to postfix operators
        Starting at precedence + 2 (gap for prefix tier)
        Each postfix gets left_bp = postfix_prec + 1, right_bp = 0
```

### 5.3 Worked Example: `-5!` → `-(5!)`

Assume `-` (prefix) has `prefix_bp = 8` and `!` (postfix) has `left_bp = 10`:

```
Call: parse_Int(min_bp=0)

  Step 1: PREFIX — see "-"
          Consume "-", recurse: parse_Int(min_bp=8)
            │
            │  Step 1a: PREFIX — parse literal "5"
            │           lhs = NumLit(5)
            │
            │  Step 1b: INFIX LOOP — see "!"
            │           ! has left_bp=10, min_bp=8
            │           Is 10 < 8? NO → ! binds         ← TIER DECISION
            │           lhs = Factorial(NumLit(5))
            │
            │  Step 1c: INFIX LOOP — no more operators, stop
            │
            └─ Return Factorial(NumLit(5))

  lhs = Neg(Factorial(NumLit(5)))

Result: -(5!)   (NOT: (-5)!)
```

The three-tier hierarchy ensures `-5!` is always parsed as `-(5!)` without
requiring the grammar author to manually assign BP values.

---

## 6. Led Chain Ordering

Within the Pratt infix loop, operators are checked in a specific order
(`pratt.rs`, lines 190-258):

```
  ┌─────────────────────────────────────────────────┐
  │  1. Check POSTFIX operators                     │
  │     (bind tightest, no recursive parse needed)  │
  │                                                 │
  │  2. Check MIXFIX operators                      │
  │     (N-ary: middle operands at min_bp=0)        │
  │                                                 │
  │  3. Check INFIX operators                       │
  │     (binary: RHS parses at right_bp)            │
  │                                                 │
  │  4. None matched → break loop                   │
  └─────────────────────────────────────────────────┘
```

### 6.1 Why Postfix First?

Postfix operators do not require a recursive parse call -- they simply wrap the
current `lhs` in a constructor. Checking them first:

1. Avoids unnecessary recursive descent when a postfix operator is present
2. Ensures postfix binds before any infix operator at the same BP level

### 6.2 Mixfix Before Infix

Mixfix operators (like ternary `a ? b : c`) use unique delimiter tokens that
cannot conflict with infix operators. Checking mixfix before infix is a
correctness requirement: the `?` in a ternary must be recognized as a mixfix
operator, not an infix operator.

---

## 7. Same-Token Disambiguation: Nud vs Led

The same token can serve as both a **prefix** (nud) and an **infix** (led)
operator. The distinction is positional: a token encountered at the **start** of
an expression is a prefix operator; a token encountered **after** a complete
sub-expression is an infix operator.

### 7.1 The Classification

```
  ┌────────────────────────────────────────────────────┐
  │  Token position determines nud vs led:             │
  │                                                    │
  │  Start of expression (nud context):                │
  │    "-" → unary negation (prefix)                   │
  │    "(" → grouping                                  │
  │    literal → atom                                  │
  │                                                    │
  │  After a complete sub-expression (led context):    │
  │    "-" → binary subtraction (infix)                │
  │    "(" → function call (led, if supported)         │
  │    "!" → factorial (postfix)                       │
  └────────────────────────────────────────────────────┘
```

### 7.2 Worked Trace: `"3 - -5"` → `Sub(3, Neg(5))`

```
Call: parse_Int(min_bp=0)

  Step 1: PREFIX (nud) — see "3" (literal)
          lhs = NumLit(3)

  Step 2: INFIX LOOP (led) — see "-"
          Context: after a complete expression → led → binary subtraction
          - has left_bp=2, min_bp=0
          Is 2 < 0? NO → - binds
          Consume "-", recurse: parse_Int(min_bp=3)
            │
            │  Step 2a: PREFIX (nud) — see "-"
            │           Context: start of expression → nud → unary negation
            │           Consume "-", recurse: parse_Int(min_bp=8)
            │             │
            │             │  PREFIX — parse literal "5"
            │             │  INFIX LOOP — no more operators, stop
            │             └─ Return NumLit(5)
            │           lhs = Neg(NumLit(5))
            │
            │  Step 2b: INFIX LOOP — no more operators, stop
            │
            └─ Return Neg(NumLit(5))

  lhs = Sub(NumLit(3), Neg(NumLit(5)))

Result: 3 - (-5)
```

**The key disambiguation:** Both `-` tokens are the same `Token::Minus`, but the
first is in **led context** (after `3`) and the second is in **nud context**
(start of recursive call). No special logic is needed -- the Pratt loop structure
naturally provides the correct context.

---

## 8. Mixfix Disambiguation

Mixfix operators (N-ary, like ternary `a ? b : c`) are disambiguated through a
combination of BP comparison and delimiter matching.

### 8.1 Default Precedence

Mixfix operators default to the **lowest precedence**. This happens because
binding powers are assigned during Pass 1 in declaration order, and mixfix
operators are typically declared before higher-precedence infix operators.
Since earlier declarations receive lower BPs, mixfix operators naturally end
up with the lowest precedence. This matches common expectations:

```
a + b ? c : d    →    (a + b) ? c : d    (ternary wraps entire expression)
```

### 8.2 Middle Operand Reset

Middle operands (between delimiters) parse at `min_bp = 0`, allowing any
expression:

```
a ? b + c : d    →    a ? (b + c) : d    (full expression between ? and :)
```

### 8.3 Delimiter Matching

The mixfix handler requires exact delimiter tokens (e.g., `?` followed
eventually by `:`). If the delimiter is not found, the parse fails and the Pratt
loop considers other operator types. This prevents a mixfix operator from
"stealing" tokens intended for a different operator.

---

## 9. Trampolined Precedence

The trampoline parser (`trampoline.rs`, lines 1256-1315) preserves all
precedence disambiguation semantics while converting recursive calls to explicit
frame-based continuation passing.

### 9.1 Key Changes from Recursive to Trampolined

| Aspect         | Recursive                      | Trampolined                                                 |
|----------------|--------------------------------|-------------------------------------------------------------|
| Min BP         | Function parameter `min_bp`    | Explicit variable `cur_bp`                                  |
| Operator token | Stack variable `op_token`      | `op_pos: usize` (index into token array)                    |
| Recursive call | `parse_Cat(tokens, pos, r_bp)` | `stack.push(InfixRHS{...}); cur_bp = r_bp; continue 'drive` |
| Return         | Function return                | `break 'prefix` then unwind loop                            |

### 9.2 The InfixRHS Frame

```rust
Frame::InfixRHS {
    lhs: Cat,           // Left operand (already parsed)
    op_pos: usize,      // Index of operator token (not Token itself)
    saved_bp: u8,       // Previous cur_bp to restore on unwind
}
```

The `op_pos: usize` design avoids lifetime issues: the frame is `'static` and
can be pooled in thread-local storage. The actual token is retrieved from the
token array during unwind: `tokens[op_pos].0`.

### 9.3 Disambiguation Preservation

The trampolined version makes **exactly the same** `left_bp < cur_bp` comparison
as the recursive version. The only difference is mechanical: instead of a function
call stack, the state is tracked in an explicit `Vec<Frame>`. All precedence,
associativity, and tier decisions are preserved identically.

---

## 10. Summary

```
  Prefix/Postfix/Infix → Binding Power Pairs → left_bp < min_bp → Parse Tree
  (operator classification)  (auto-assigned)     (THE decision)    (unambiguous)
```

| Mechanism            | Ambiguity Resolved            | Implementation                          |
|----------------------|-------------------------------|-----------------------------------------|
| BP magnitude         | `+` vs `*` precedence         | Declaration-order assignment            |
| BP pair asymmetry    | Left vs right associativity   | `(lo, hi)` vs `(hi, lo)`                |
| Three-tier hierarchy | Prefix vs infix vs postfix    | Automatic: infix < prefix < postfix     |
| Led chain ordering   | Which led type to check first | Postfix → mixfix → infix                |
| Nud vs led context   | Same token as prefix/infix    | Positional: start-of-expr vs after-expr |
| Mixfix delimiters    | N-ary operator boundaries     | Delimiter matching + `min_bp=0` reset   |

**Layer 3 output → Layer 4 input:** A complete expression tree within a single
type category. If the expression involves a cross-category operator (e.g., `==`
producing a `Bool` from `Int` operands), Layer 4 handles the category transition.
