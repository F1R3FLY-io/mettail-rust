# Binding Power Fundamentals

This document introduces the core theory behind PraTTaIL's binding power system.
For the full Pratt parsing algorithm, see [theory/pratt-parsing.md](../../theory/pratt-parsing.md).

---

## 1. What Are Binding Powers?

A **binding power** (BP) is a numeric value that quantifies how tightly an
operator "pulls" on its operands. Higher values bind tighter. The key insight
of Pratt parsing is that each operator receives not one but **two** binding
powers — a left BP and a right BP — forming a **binding power pair** `(left_bp, right_bp)`.

### Why Pairs, Not Singles?

A single precedence number can encode operator ordering (`*` before `+`), but
it cannot distinguish associativity. Consider subtraction:

```
5 - 3 - 1
```

Both `(5 - 3) - 1 = 1` and `5 - (3 - 1) = 3` respect the same precedence
level, yet produce different results. The **asymmetry** between left and right
binding powers resolves this:

- The **left BP** determines whether this operator can "steal" the left operand
  from a parent operator (compared against the parent's `min_bp`).
- The **right BP** determines how tightly the operator holds its right operand
  (passed as `min_bp` to the recursive call).

---

## 2. The Asymmetry Principle

The relationship between `left_bp` and `right_bp` encodes associativity:

```
┌──────────────────────┬─────────────────┬──────────────────────────────────┐
│ Relationship         │ Associativity   │ Parse of  a OP b OP c            │
├──────────────────────┼─────────────────┼──────────────────────────────────┤
│ left_bp < right_bp   │ Left            │ (a OP b) OP c                    │
│ left_bp > right_bp   │ Right           │ a OP (b OP c)                    │
└──────────────────────┴─────────────────┴──────────────────────────────────┘
```

**Mathematical formulation.** For operator at precedence level *k* (0-indexed):

```
Left-associative:   (left_bp, right_bp) = (2k + 2,  2k + 3)
Right-associative:  (left_bp, right_bp) = (2k + 3,  2k + 2)
```

The `+2` offset reserves BP values 0 and 1 — BP 0 is used as the initial
`min_bp` for the outermost parse call, and 1 provides padding.

**Why this works.** Consider two instances of a left-associative operator with
BPs `(2k+2, 2k+3)`:

```
     a  OP  b  OP  c
        ↑      ↑
   (left=2k+2) (left=2k+2)
   (right=2k+3)

   After parsing "a OP b", the recursive call used min_bp = 2k+3.
   The second OP has left_bp = 2k+2 < 2k+3 = min_bp → STOP.
   Result: (a OP b) OP c   ✓ left-associative
```

For a right-associative operator with BPs `(2k+3, 2k+2)`:

```
     a  OP  b  OP  c
        ↑      ↑
   (left=2k+3) (left=2k+3)
   (right=2k+2)

   After parsing "a OP b", the recursive call used min_bp = 2k+2.
   The second OP has left_bp = 2k+3 ≥ 2k+2 = min_bp → CONTINUE.
   Result: a OP (b OP c)   ✓ right-associative
```

---

## 3. The Pratt Loop

The Pratt loop is the core parsing mechanism. PraTTaIL generates one per
grammar category that has infix, postfix, or mixfix operators.

### 3.1 Pseudocode

```
FUNCTION parse_Cat(tokens, pos, min_bp) → Cat:
    lhs ← parse_Cat_prefix(tokens, pos)     ▷ Nud: atom, unary prefix, grouping

    LOOP:
        token ← peek(tokens, pos)

        ▷ Check postfix first (tightest binding)
        IF postfix_bp(token) returns l_bp:
            IF l_bp < min_bp: BREAK
            consume(token)
            lhs ← make_postfix(token, lhs)
            CONTINUE

        ▷ Check mixfix next (n-ary operators like ternary)
        IF mixfix_bp(token) returns (l_bp, r_bp):
            IF l_bp < min_bp: BREAK
            consume(token)
            lhs ← handle_mixfix(token, lhs, tokens, pos, r_bp)
            CONTINUE

        ▷ Check binary infix last
        IF infix_bp(token) returns (l_bp, r_bp):
            IF l_bp < min_bp: BREAK
            consume(token)
            rhs ← parse_Cat(tokens, pos, r_bp)      ▷ Recurse with right BP
            lhs ← make_infix(token, lhs, rhs)
            CONTINUE

        BREAK                                         ▷ Not an operator for this category

    RETURN lhs
```

### 3.2 Key Decision Point

The critical comparison is:

```
l_bp < min_bp  ?
```

This single comparison resolves both **precedence** and **associativity**:

- **Precedence:** Higher-precedence operators have higher `left_bp`, so they
  pass the check and continue binding even when nested inside a lower-precedence
  operator's right-hand recursive call.

- **Associativity:** For same-precedence operators, the gap between `left_bp`
  and the parent's `right_bp` (which became the current `min_bp`) determines
  whether the operator continues or stops.

### 3.3 Led Chain Order

The led (left-denotation) chain checks operator types in a specific order
that reflects the BP hierarchy:

```
postfix  →  mixfix  →  infix  →  break
(tightest)                       (no match)
```

This ordering is cosmetic rather than semantic — the BP comparison itself
correctly handles all cases regardless of check order. However, checking
postfix first avoids unnecessary BP lookups for the common case where postfix
operators are present.

**Source:** `prattail/src/pratt.rs`, `write_led_chain()`

---

## 4. Nud and Led: Prefix vs. Infix Position

Pratt parsing divides token handling into two categories:

| Position                           | Pratt Term | PraTTaIL Function    | Handles                                                |
|------------------------------------|------------|----------------------|--------------------------------------------------------|
| **Prefix** (null denotation / nud) | `nud`      | `parse_Cat_prefix()` | Atoms, unary prefix, grouping, casts, structural rules |
| **Infix** (left denotation / led)  | `led`      | Pratt loop body      | Binary infix, postfix, mixfix                          |

### 4.1 Nud Handlers

The `parse_Cat_prefix()` function dispatches on the current token to one of:

- **Literal match:** `Token::Integer(v) → Cat::NumLit(v)` (for native types)
- **Identifier:** `Token::Ident(s) → Cat::Var(s)` (variable rules)
- **Unary prefix:** `Token::Minus → { consume; a = parse_Cat(tokens, pos, prefix_bp); Cat::Neg(a) }`
- **Grouping:** `Token::LParen → { consume; inner = parse_Cat(tokens, pos, 0); expect(RParen); inner }`
- **Structural/RD rules:** matched by FIRST-set dispatch
- **Cast rules:** `Token in FIRST(source_cat) → { k = parse_SourceCat(tokens, pos, 0); Cat::Cast(k) }`

The `prefix_bp` value for unary prefix operators is crucial: it determines
how tightly the prefix operator binds its operand. See
[02-implicit-deduction.md](02-implicit-deduction.md) §5 for the formula.

### 4.2 Led Handlers

Each operator type has a distinct led handler:

- **Binary infix:** `make_infix(token, lhs, parse_Cat(tokens, pos, r_bp))`
- **Postfix:** `make_postfix(token, lhs)` (no recursive call)
- **Mixfix:** `handle_mixfix(token, lhs, ...)` (parses middle operands at `min_bp=0`)

---

## 5. The Tug-of-War Metaphor

Binding powers create a "tug-of-war" between adjacent operators competing
for a shared operand. The operand goes to whichever side pulls harder:

```
    1   +   2   *   3   -   4
        │       │       │
       (2,3)  (6,7)   (4,5)

    Operand 2 is between + and *:
      + pulls right with right_bp = 3
      * pulls left  with left_bp  = 6
      6 > 3 → * wins → 2 goes to *

    Operand "2*3" is between + and -:
      + pulls right with right_bp = 3
      - pulls left  with left_bp  = 4
      4 > 3 → - wins ... but wait:

    Actually, + was the parent call with min_bp = 3.
    The loop sees - with left_bp = 4 ≥ 3, so - continues.
    Then - pulls right with right_bp = 5, and 4 has nothing after it,
    so the parse of "2*3-4" completes, and + gets that as its RHS.

    Final tree:
              (-)
             /   \
           (+)    4
          / \
         1  (*)
            / \
           2   3
```

### 5.1 Formal Invariant

At any point during parsing, the Pratt loop maintains this invariant:

> **The `min_bp` parameter equals the `right_bp` of the nearest enclosing
> operator call (or 0 at the top level).**

An operator with `left_bp ≥ min_bp` belongs to the current expression.
An operator with `left_bp < min_bp` belongs to a parent expression.

---

## 6. Termination and Correctness

The Pratt loop terminates because:

1. Each iteration either **consumes at least one token** (the operator) or **breaks**.
2. The input is finite.

The Pratt loop is correct because:

1. Binding power pairs are assigned with strictly increasing values for
   increasing precedence levels (gap of 2 per level).
2. Left-associative operators have `left_bp < right_bp`, guaranteeing that
   a same-level operator in the recursive call will fail the `left_bp < min_bp`
   check.
3. Right-associative operators have `left_bp > right_bp`, guaranteeing that
   a same-level operator in the recursive call will pass the check.
4. Different precedence levels have non-overlapping BP ranges, so the
   comparison is always decisive.

**Source:** [theory/pratt-parsing.md](../../theory/pratt-parsing.md) §7 for the full correctness argument.
