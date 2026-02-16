# Pratt Parsing from First Principles

This document teaches Pratt parsing (top-down operator precedence) from the
ground up. We begin with the problem it solves, develop the core algorithm
step by step, work through a complete parse trace, and then explain how
PraTTaIL generates Pratt parsers from grammar rules.

---

## 1. The Problem: Parsing Expressions with Precedence

Consider the expression `1 + 2 * 3 - 4`. A correct parser must produce:

```
           Sub
          /   \
        Add    4
       /   \
      1    Mul
          /   \
         2     3
```

This requires knowing:
- `*` binds tighter than `+` and `-` (higher precedence)
- `+` and `-` are left-associative: `1 + 2 - 3` means `(1 + 2) - 3`

In a recursive descent parser, encoding precedence typically requires a
"precedence climbing" pattern with one function per precedence level:

```
  parse_add_sub:   handles + and - (lowest precedence)
  parse_mul_div:   handles * and / (higher precedence)
  parse_unary:     handles prefix - (higher still)
  parse_atom:      handles literals and parentheses
```

This works but is brittle: adding a new precedence level requires inserting
a new function in the middle of the chain. With 10+ precedence levels (as in
many real languages), the boilerplate becomes unwieldy.

**Pratt parsing eliminates this boilerplate.** Instead of one function per
precedence level, it uses a single loop that consults a numeric **binding
power** to decide when to stop consuming operators.

---

## 2. Binding Power: The Core Abstraction

### 2.1 Binding Power as a Metaphor

Think of each operator as having a "gravitational pull" on its operands. In
`1 + 2 * 3`, the `*` pulls harder on `2` than `+` does. Concretely:

```
    1   +   2   *   3
        ^       ^
       bp=1   bp=3

  The "2" is between two operators.
  It goes with whichever pulls harder.
  Since bp(*) > bp(+), the 2 goes with *.
```

### 2.2 Why Pairs, Not Single Numbers?

A single binding power number per operator is insufficient for expressing
associativity. Consider:

```
  Left-associative:  1 - 2 - 3  =  (1 - 2) - 3
  Right-associative: 2 ^ 3 ^ 4  =  2 ^ (3 ^ 4)
```

Both `-` and `^` have a single precedence level, yet they group differently.
The solution is to assign each operator a **pair** of binding powers:
`(left_bp, right_bp)`.

```
  ┌────────────────────────────────────────────────────────────┐
  │ The binding power pair (left_bp, right_bp) for an infix   │
  │ operator controls two things:                              │
  │                                                            │
  │   left_bp:  How strongly this operator competes for its   │
  │             LEFT operand against the operator to its left  │
  │                                                            │
  │   right_bp: The minimum binding power required for the    │
  │             parser to continue consuming tokens to form    │
  │             the RIGHT operand                              │
  └────────────────────────────────────────────────────────────┘
```

**Left-associative** operators have `left_bp < right_bp`:

```
  Operator  -  :  (left_bp=2, right_bp=3)

  For "1 - 2 - 3":
    Parse 1, see -, enter with right_bp=3
    Parse 2, see -, its left_bp=2 < current min_bp=3, so STOP
    Result: (1-2), then continue outer loop to parse "- 3"
    Final: ((1-2)-3)  -- left-associative
```

**Right-associative** operators have `left_bp > right_bp`:

```
  Operator  ^  :  (left_bp=7, right_bp=6)

  For "2 ^ 3 ^ 4":
    Parse 2, see ^, enter with right_bp=6
    Parse 3, see ^, its left_bp=7 >= current min_bp=6, so CONTINUE
    Parse 4, no more operators, return 4
    Inner: (3^4), then outer: (2^(3^4))  -- right-associative
```

### 2.3 The Asymmetry Principle

The fundamental insight:

```
  ┌────────────────────────────────────────────────────────────┐
  │                                                            │
  │  LEFT-ASSOCIATIVE:   left_bp < right_bp                   │
  │  RIGHT-ASSOCIATIVE:  left_bp > right_bp                   │
  │                                                            │
  │  The asymmetry between left_bp and right_bp determines    │
  │  associativity. The absolute values determine precedence  │
  │  relative to other operators.                              │
  │                                                            │
  └────────────────────────────────────────────────────────────┘
```

In PraTTaIL, binding powers are assigned automatically from rule declaration
order. The first-declared infix rule gets the lowest precedence. For each
rule, the generator produces:

```rust
  // Left-associative: bp = (precedence, precedence + 1)
  Associativity::Left  => (precedence, precedence + 1)

  // Right-associative: bp = (precedence + 1, precedence)
  Associativity::Right => (precedence + 1, precedence)
```

---

## 3. Nud and Led: The Two Dispatch Points

Pratt parsing classifies token behavior into two categories:

### 3.1 Null Denotation (nud)

The **nud** (null denotation) defines how a token behaves when it appears at
the **beginning** of an expression -- that is, with no left-hand operand.

```
  Token       nud behavior
  ───────────────────────────────────────────
  Integer     Return the literal value (atom)
  Identifier  Return a variable reference (atom)
  (           Parse a grouped sub-expression
  -           Parse a prefix negation
  !           Parse a prefix logical NOT
  if          Parse an if-then-else
  ^           Parse a lambda abstraction
```

Atoms (literals, identifiers) are the simplest nud: they just return
themselves. Prefix operators parse their operand by recursing with a
high right binding power. Grouping tokens parse until a matching closer.

### 3.2 Left Denotation (led)

The **led** (left denotation) defines how a token behaves when it appears
**after** a left-hand operand has already been parsed.

```
  Token       led behavior
  ───────────────────────────────────────────
  +           Infix: combine lhs with rhs
  *           Infix: combine lhs with rhs
  ?           Postfix: wrap lhs
  [           Postfix: index into lhs
  (           Postfix: function call on lhs
  ? :         Ternary: lhs ? middle : right
```

Infix operators are the most common led: they consume a right-hand operand
by recursing with their right binding power. Postfix operators wrap the lhs
without consuming further operands. Mixfix constructs (ternary, array index)
consume specific additional syntax.

### 3.3 The Classification Diagram

```
  Token appears at start         Token appears after lhs
  of an expression?              has been parsed?
         │                              │
         ▼                              ▼
   ┌───────────┐                 ┌────────────┐
   │    nud    │                 │    led     │
   │           │                 │            │
   │ - Atoms   │                 │ - Infix    │
   │ - Prefix  │                 │ - Postfix  │
   │ - Group   │                 │ - Mixfix   │
   │ - Special │                 │            │
   └───────────┘                 └────────────┘

  In PraTTaIL:                   In PraTTaIL:
  parse_<Cat>_prefix()           The Pratt loop's inner match
  handles nud dispatch.          handles led dispatch via
                                 infix_bp() lookup.
```

---

## 4. The Pratt Loop

Here is the complete algorithm in pseudocode:

```
  function parse_expr(tokens, min_bp):
      // ── Step 1: Parse the prefix (nud) ──
      lhs = parse_prefix(tokens)

      // ── Step 2: Loop over infix/postfix operators (led) ──
      loop:
          token = peek(tokens)
          if token is EOF or not an infix operator:
              break

          (left_bp, right_bp) = binding_power(token)

          if left_bp < min_bp:
              break                // This operator binds less tightly
                                   // than our caller requires.

          consume(tokens, token)   // Consume the operator.

          rhs = parse_expr(tokens, right_bp)  // Recurse with right_bp
                                               // as the new minimum.

          lhs = make_node(token, lhs, rhs)    // Build the AST node.

      return lhs
```

### 4.1 How the Loop Handles Precedence

The key condition is `if left_bp < min_bp: break`. This is where precedence
is enforced:

```
  Parsing "1 + 2 * 3":

  Call: parse_expr(min_bp=0)
    nud: lhs = 1
    loop:
      peek: +, bp=(2,3), left_bp=2 >= min_bp=0, continue
      consume +
      rhs = parse_expr(min_bp=3)    <-- recurse with right_bp
        nud: lhs = 2
        loop:
          peek: *, bp=(4,5), left_bp=4 >= min_bp=3, continue
          consume *
          rhs = parse_expr(min_bp=5)
            nud: lhs = 3
            loop:
              peek: EOF, break
            return 3
          lhs = Mul(2, 3)
          loop:
            peek: EOF, break
        return Mul(2, 3)
      lhs = Add(1, Mul(2, 3))
      loop:
        peek: EOF, break
    return Add(1, Mul(2, 3))
```

### 4.2 How the Loop Handles Associativity

The asymmetry between left_bp and right_bp controls associativity:

```
  Left-associative - (bp: left=2, right=3):

  Parsing "5 - 3 - 1":
  Call: parse_expr(min_bp=0)
    nud: lhs = 5
    loop:
      peek: -, left_bp=2 >= min_bp=0, continue
      consume -
      rhs = parse_expr(min_bp=3)     <-- right_bp = 3
        nud: lhs = 3
        loop:
          peek: -, left_bp=2 < min_bp=3, BREAK   <-- key!
        return 3
      lhs = Sub(5, 3)
      loop:
        peek: -, left_bp=2 >= min_bp=0, continue
        consume -
        rhs = parse_expr(min_bp=3)
          nud: lhs = 1
          loop: EOF, break
          return 1
        lhs = Sub(Sub(5, 3), 1)
    return Sub(Sub(5, 3), 1)         <-- left-associative!

  Right-associative ^ (bp: left=7, right=6):

  Parsing "2 ^ 3 ^ 4":
  Call: parse_expr(min_bp=0)
    nud: lhs = 2
    loop:
      peek: ^, left_bp=7 >= min_bp=0, continue
      consume ^
      rhs = parse_expr(min_bp=6)     <-- right_bp = 6
        nud: lhs = 3
        loop:
          peek: ^, left_bp=7 >= min_bp=6, CONTINUE  <-- key!
          consume ^
          rhs = parse_expr(min_bp=6)
            nud: lhs = 4
            loop: EOF, break
            return 4
          lhs = Pow(3, 4)
          loop: EOF, break
        return Pow(3, 4)
      lhs = Pow(2, Pow(3, 4))
    return Pow(2, Pow(3, 4))          <-- right-associative!
```

---

## 5. Prefix and Postfix as Special Cases

### 5.1 Prefix Operators

A prefix operator (e.g., unary `-`) is a nud handler that recurses:

```
  nud for prefix -:
      consume(tokens, MINUS)
      operand = parse_expr(tokens, PREFIX_BP)   // High BP
      return Negate(operand)
```

The prefix binding power is typically higher than any infix operator, so that
`-x + y` is parsed as `(-x) + y`, not `-(x + y)`.

In PraTTaIL, prefix operators are generated as part of the
`parse_<Cat>_prefix()` function. They are match arms that consume the prefix
token and recurse into `parse_<Cat>(tokens, pos, prefix_bp)`.

### 5.2 Postfix Operators

A postfix operator (e.g., `!` for factorial) is a led handler that does not
recurse for a right operand:

```
  led for postfix !:
      bp = (postfix_bp, ())     // No right binding power needed
      if left_bp < min_bp: break
      consume(tokens, BANG)
      lhs = Factorial(lhs)
      // Do NOT recurse for rhs
```

In the binding power framework, a postfix operator has a left binding power
but no meaningful right binding power (or equivalently, its right binding
power is effectively zero -- it never tries to grab more to the right).

### 5.3 Unified View

```
  ┌────────────────────────────────────────────────────────────┐
  │  Operator Type    nud?    led?    Recurse for rhs?         │
  ├────────────────────────────────────────────────────────────┤
  │  Atom             Yes     No      No                       │
  │  Prefix           Yes     No      Yes (with high BP)       │
  │  Infix            No      Yes     Yes (with right_bp)      │
  │  Postfix          No      Yes     No                       │
  │  Mixfix (ternary) No      Yes     Yes (custom structure)   │
  │  Grouping         Yes     No      Yes (until closer)       │
  └────────────────────────────────────────────────────────────┘
```

---

## 6. The Pratt Loop as a Generalization of Shunting-Yard

Dijkstra's shunting-yard algorithm uses two explicit stacks:

```
  Shunting-Yard                    Pratt Loop
  ─────────────                    ──────────
  Operator stack   <────────>      Call stack (recursive calls)
  Operand stack    <────────>      Return values (lhs, rhs)
  Compare top of   <────────>     left_bp < min_bp?
   op stack with
   new operator
```

The Pratt loop replaces explicit stacks with recursion:

```
  Shunting-yard:
    while op_stack.top().prec >= new_op.prec:
        pop and apply

  Pratt loop:
    if left_bp < min_bp: break
    // (returning from recursive call achieves the same as "pop")
```

This is why Pratt parsing is sometimes described as a "recursive
shunting-yard." The recursion gives additional power: the nud dispatch can
handle any syntax (grouping, prefix, binders), not just operators and
operands.

---

## 7. Complete Worked Example

Let us trace the complete parse of `1 + 2 * 3 - 4 / 2` with the following
binding power table:

```
  Operator    Associativity    left_bp    right_bp
  ─────────────────────────────────────────────────
  +           Left             2          3
  -           Left             2          3
  *           Left             4          5
  /           Left             4          5
```

### 7.1 Token Stream

```
  Position:  0     1    2     3    4     5    6     7    8
  Token:     INT1  +    INT2  *    INT3  -    INT4  /    INT2
  Value:     1          2          3          4          2
```

### 7.2 Full Parse Trace

We denote each function call with its min_bp argument and use indentation
to show the call stack depth.

```
parse_expr(min_bp=0)                                          [A]
  nud: token=INT(1), lhs=1
  loop iteration 1:
    peek='+', bp(+)=(2,3), left_bp=2 >= min_bp=0? YES
    consume '+'
    rhs = parse_expr(min_bp=3)                                [B]
      nud: token=INT(2), lhs=2
      loop iteration 1:
        peek='*', bp(*)=(4,5), left_bp=4 >= min_bp=3? YES
        consume '*'
        rhs = parse_expr(min_bp=5)                            [C]
          nud: token=INT(3), lhs=3
          loop iteration 1:
            peek='-', bp(-)=(2,3), left_bp=2 >= min_bp=5? NO -> BREAK
          return 3                                            [/C]
        lhs = Mul(2, 3)
      loop iteration 2:
        peek='-', bp(-)=(2,3), left_bp=2 >= min_bp=3? NO -> BREAK
      return Mul(2, 3)                                        [/B]
    lhs = Add(1, Mul(2, 3))
  loop iteration 2:
    peek='-', bp(-)=(2,3), left_bp=2 >= min_bp=0? YES
    consume '-'
    rhs = parse_expr(min_bp=3)                                [D]
      nud: token=INT(4), lhs=4
      loop iteration 1:
        peek='/', bp(/)=(4,5), left_bp=4 >= min_bp=3? YES
        consume '/'
        rhs = parse_expr(min_bp=5)                            [E]
          nud: token=INT(2), lhs=2
          loop iteration 1:
            peek=EOF -> BREAK
          return 2                                            [/E]
        lhs = Div(4, 2)
      loop iteration 2:
        peek=EOF -> BREAK
      return Div(4, 2)                                        [/D]
    lhs = Sub(Add(1, Mul(2, 3)), Div(4, 2))
  loop iteration 3:
    peek=EOF -> BREAK
  return Sub(Add(1, Mul(2, 3)), Div(4, 2))                   [/A]
```

### 7.3 Resulting AST

```
              Sub
             /   \
          Add    Div
         /   \   / \
        1   Mul 4   2
           / \
          2   3
```

### 7.4 Call Stack Visualization

At the deepest point (call [C]), the call stack looks like:

```
  ┌──────────────────────────────────────┐
  │ parse_expr(min_bp=5)  [C]           │  <-- top
  │   lhs = 3                            │
  │   peek '-', left_bp=2 < 5, break    │
  ├──────────────────────────────────────┤
  │ parse_expr(min_bp=3)  [B]           │
  │   lhs = 2, consumed '*'             │
  │   waiting for rhs from [C]          │
  ├──────────────────────────────────────┤
  │ parse_expr(min_bp=0)  [A]           │
  │   lhs = 1, consumed '+'             │
  │   waiting for rhs from [B]          │
  └──────────────────────────────────────┘
```

---

## 8. Handling Grouping (Parentheses)

Parenthesized expressions are a nud handler:

```
  nud for '(':
      consume '('
      expr = parse_expr(tokens, min_bp=0)   // Reset to lowest BP
      expect ')'
      return expr
```

By resetting min_bp to 0, we allow any operator inside the parentheses,
regardless of the enclosing expression's binding power context. This is why
`(1 + 2) * 3` works correctly: inside the parentheses, `+` is not competing
with the outer `*`.

```
  Parsing "(1 + 2) * 3":

  parse_expr(min_bp=0)
    nud: token='(', enter grouping
      parse_expr(min_bp=0)      <-- reset to 0
        nud: lhs=1
        loop: peek='+', left_bp=2 >= 0, continue
          consume '+'
          rhs = parse_expr(min_bp=3)
            nud: lhs=2
            loop: peek=')', not an operator, break
            return 2
          lhs = Add(1, 2)
        loop: peek=')', break
      return Add(1, 2)
    expect ')'
    lhs = Add(1, 2)
    loop: peek='*', left_bp=4 >= 0, continue
      consume '*'
      rhs = parse_expr(min_bp=5)
        nud: lhs=3
        loop: EOF, break
        return 3
      lhs = Mul(Add(1, 2), 3)
    loop: EOF, break
  return Mul(Add(1, 2), 3)
```

---

## 9. Multi-Category Pratt Parsing in PraTTaIL

PraTTaIL extends classical Pratt parsing to handle multiple syntactic
categories. Each category (e.g., `Proc`, `Int`, `Bool`, `Name`) gets its
own Pratt parser with its own binding power table.

### 9.1 Per-Category Generated Functions

For each category `Cat`, PraTTaIL generates:

```
  parse_Cat(tokens, pos, min_bp)     -- Main Pratt loop
  parse_Cat_prefix(tokens, pos)      -- Nud dispatch
  infix_bp(token) -> Option<(u8,u8)> -- BP lookup
  make_infix(op, lhs, rhs) -> Cat    -- AST constructor
```

### 9.2 BP Table Example

Given a language with these rules:

```
  // Category: Proc
  PPar   : Proc "|"  Proc    (left-assoc)    // Parallel composition
  PEval  : Proc "!"  Proc    (left-assoc)    // Evaluation

  // Category: Int
  Add    : Int  "+"  Int     (left-assoc)    // Addition
  Mul    : Int  "*"  Int     (left-assoc)    // Multiplication
  Pow    : Int  "**" Int     (right-assoc)   // Exponentiation
```

PraTTaIL generates:

```
  Proc BP table:
  ┌──────────┬──────────┬──────────┬───────────────┐
  │ Operator │ left_bp  │ right_bp │ Associativity │
  ├──────────┼──────────┼──────────┼───────────────┤
  │ "|"      │    2     │    3     │ Left          │
  │ "!"      │    4     │    5     │ Left          │
  └──────────┴──────────┴──────────┴───────────────┘

  Int BP table:
  ┌──────────┬──────────┬──────────┬───────────────┐
  │ Operator │ left_bp  │ right_bp │ Associativity │
  ├──────────┼──────────┼──────────┼───────────────┤
  │ "+"      │    2     │    3     │ Left          │
  │ "*"      │    4     │    5     │ Left          │
  │ "**"     │    7     │    6     │ Right         │
  └──────────┴──────────┴──────────┴───────────────┘
```

Notice how `**` has `left_bp=7 > right_bp=6`, encoding right associativity.
The starting precedence is 2 (reserving 0 for the entry point and 1 for
future use). Each operator consumes two slots in the precedence space to
maintain the asymmetry.

### 9.3 Cross-Category Operators

Some operators take operands from one category but produce results in another.
For example:

```
  Eq : Int "==" Int -> Bool      // Equality comparison
  Lt : Int "<"  Int -> Bool      // Less-than comparison
```

These are handled by the cross-category dispatch system, not the Pratt loop
itself. The dispatch system uses FIRST-set analysis to determine whether to
route parsing to the `Int` category (and then look for `==` or `<`) or to
the `Bool` category directly. See
[prediction-and-lookahead.md](prediction-and-lookahead.md) for details.

---

## 10. How PraTTaIL Generates Pratt Parsers from Grammar Rules

### 10.1 Rule Classification

When PraTTaIL processes grammar rules, it classifies each as:

```
  ┌─────────────────────────────────────────────────────────────┐
  │ Rule shape                  Classification    Handler       │
  ├─────────────────────────────────────────────────────────────┤
  │ Cat OP Cat                  Infix             Pratt loop    │
  │ OP Cat                      Prefix            nud match arm │
  │ "(" Cat ")"                 Grouping          nud match arm │
  │ KEYWORD ... Cat ...         Structural        RD function   │
  │ ID                          Variable          nud fallback  │
  │ INT / FLOAT / BOOL / STR   Literal            nud match arm │
  │ collection with separator   Collection         RD function   │
  │ Cat OP Cat -> OtherCat     Cross-category    Dispatch      │
  └─────────────────────────────────────────────────────────────┘
```

### 10.2 The Generation Pipeline

```
  Grammar rules
       │
       ▼
  ┌──────────────────┐
  │ Classify rules   │──── Infix rules ────> analyze_binding_powers()
  │ by shape         │                            │
  └──────────────────┘                            ▼
       │                                  BindingPowerTable
       │                                       │
       ├── Prefix rules ──> PrefixHandler ─────┐
       │                    (match arms)       │
       ├── Structural ────> generate_rd_handler()
       │                    (RD functions)      │
       │                                       ▼
       │                              generate_pratt_parser()
       │                                       │
       ▼                                       ▼
  FIRST set analysis                    Per-category:
  Dispatch tables                         parse_Cat()
  Overlap analysis                        parse_Cat_prefix()
                                          infix_bp()
                                          make_infix()
```

### 10.3 Generated Code Structure (Simplified)

For a category `Int` with `+`, `*`, and `**`:

```rust
// Binding power lookup
fn infix_bp(token: &Token) -> Option<(u8, u8)> {
    match token {
        Token::Plus    => Some((2, 3)),   // Left-assoc
        Token::Star    => Some((4, 5)),   // Left-assoc
        Token::StarStar => Some((7, 6)), // Right-assoc
        _ => None,
    }
}

// AST construction
fn make_infix(token: &Token, lhs: Int, rhs: Int) -> Int {
    match token {
        Token::Plus     => Int::Add(Box::new(lhs), Box::new(rhs)),
        Token::Star     => Int::Mul(Box::new(lhs), Box::new(rhs)),
        Token::StarStar => Int::Pow(Box::new(lhs), Box::new(rhs)),
        _ => unreachable!(),
    }
}

// Main Pratt loop
fn parse_Int(tokens: &[(Token, Span)], pos: &mut usize, min_bp: u8)
    -> Result<Int, String>
{
    let mut lhs = parse_Int_prefix(tokens, pos)?;

    loop {
        if *pos >= tokens.len() { break; }
        let token = &tokens[*pos].0;
        if let Some((l_bp, r_bp)) = infix_bp(token) {
            if l_bp < min_bp { break; }
            let op_token = token.clone();
            *pos += 1;
            let rhs = parse_Int(tokens, pos, r_bp)?;
            lhs = make_infix(&op_token, lhs, rhs);
        } else {
            break;
        }
    }
    Ok(lhs)
}

// Prefix (nud) dispatch
fn parse_Int_prefix(tokens: &[(Token, Span)], pos: &mut usize)
    -> Result<Int, String>
{
    match &tokens[*pos].0 {
        Token::Integer(n) => { *pos += 1; Ok(Int::Lit(*n)) }
        Token::LParen => {
            *pos += 1;
            let expr = parse_Int(tokens, pos, 0)?;
            expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
            Ok(expr)
        }
        Token::Ident(name) => {
            *pos += 1;
            Ok(Int::IVar(/* variable */))
        }
        other => Err(format!("expected Int expression, found {:?}", other)),
    }
}
```

---

## 11. Correctness Argument

### 11.1 Invariant

The Pratt loop maintains the following invariant:

> **At each recursive call `parse_expr(min_bp)`, the parser will only consume
> infix operators whose `left_bp >= min_bp`.** All operators with lower left
> binding power are left for the caller to handle.

### 11.2 Termination

The algorithm terminates because:
1. Each iteration of the loop either consumes at least one token (the infix
   operator) or breaks.
2. Each recursive call to `parse_expr` begins by consuming at least one
   token (via the nud handler).
3. The input is finite.

Therefore the total number of function calls is bounded by O(n) where n is
the number of tokens.

### 11.3 Correctness of Precedence

Suppose operators `A` and `B` have binding powers such that `A.left_bp < B.left_bp`.
When parsing `x A y B z`:

1. The outer call parses `x`, then sees `A` and recurses with `A.right_bp`.
2. The inner call parses `y`, then sees `B`. Since `B.left_bp >= A.right_bp`
   (because `B` has higher precedence), it consumes `B` and recurses again.
3. The innermost call parses `z` and returns.
4. The result is `x A (y B z)`, which is correct: `B` binds tighter.

### 11.4 Correctness of Associativity

For a left-associative operator with `left_bp < right_bp`:
- When the same operator appears twice, `x OP y OP z`, the inner call has
  `min_bp = right_bp`.
- The second `OP` has `left_bp < right_bp = min_bp`, so it breaks.
- Result: `(x OP y) OP z`.

For a right-associative operator with `left_bp > right_bp`:
- The inner call has `min_bp = right_bp`.
- The second `OP` has `left_bp > right_bp = min_bp`, so it continues.
- Result: `x OP (y OP z)`.

---

## 12. Comparison with Other Approaches

```
  ┌─────────────────────────┬──────────────────────────────────────┐
  │ Approach                │ How precedence is encoded             │
  ├─────────────────────────┼──────────────────────────────────────┤
  │ Grammar stratification  │ One nonterminal per precedence level │
  │ (textbook RD)           │ (Expr, Term, Factor, ...)            │
  │                         │                                      │
  │ LALR precedence decls   │ %left, %right, %nonassoc directives  │
  │ (yacc/bison)            │ modifying shift-reduce decisions     │
  │                         │                                      │
  │ Precedence climbing     │ Recursive function with precedence   │
  │ (iterative RD)          │ parameter (similar to Pratt)         │
  │                         │                                      │
  │ Shunting-yard           │ Operator stack with numeric prec     │
  │ (Dijkstra)              │ (iterative, not recursive)           │
  │                         │                                      │
  │ Pratt parsing           │ Binding power pairs (left, right)    │
  │ (PraTTaIL)              │ in a recursive loop                  │
  └─────────────────────────┴──────────────────────────────────────┘
```

Pratt parsing and precedence climbing are essentially the same algorithm
expressed differently. Pratt's formulation via nud/led is more general
because it cleanly handles prefix, postfix, and mixfix operators through
the same dispatch mechanism.

---

## 13. Summary

Pratt parsing achieves expression parsing in O(n) time with a simple,
elegant algorithm:

1. Every token knows how to behave at the start of an expression (**nud**)
   and after a left operand (**led**).

2. Every infix operator carries a binding power **pair** `(left_bp, right_bp)`.
   The asymmetry between left and right encodes associativity; the magnitude
   encodes precedence.

3. A single recursive loop checks `left_bp < min_bp` to decide when to stop
   consuming operators and return the accumulated left-hand side.

4. PraTTaIL generates this loop, the binding power table, the nud dispatch,
   and the AST constructors automatically from grammar rule declarations.

The result is a parser that is as readable as hand-written recursive descent,
as correct as a grammar-driven parser generator, and as efficient as an
operator-precedence parser.

---

## References

1. Pratt, V. R. (1973). "Top Down Operator Precedence." _Proc. ACM Symposium
   on Principles of Programming Languages_, pp. 41--51.
2. Crockford, D. (2007). "Top Down Operator Precedence." _Beautiful Code_,
   O'Reilly Media, Chapter 9.
3. Matklad (2020). "Simple but Powerful Pratt Parsing."
   https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
4. Nystrom, R. (2011). "Pratt Parsers: Expression Parsing Made Easy."
   http://journal.stuffwithstuff.com/2011/03/19/pratt-parsers-expression-parsing-made-easy/
