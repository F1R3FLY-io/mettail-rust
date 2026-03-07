# Operator Forms and Their BP Treatment

This document covers every operator form supported by PraTTaIL and how each
interacts with the binding power system. For the underlying theory, see
[01-fundamentals.md](01-fundamentals.md). For the assignment algorithm, see
[02-implicit-deduction.md](02-implicit-deduction.md).

**Source files:**
- `prattail/src/binding_power.rs` — BP types and analysis
- `prattail/src/classify.rs` — structural pattern detection
- `prattail/src/pratt.rs` — Pratt loop codegen
- `prattail/src/trampoline.rs` — trampolined Pratt loop codegen
- `prattail/src/dispatch.rs` — cross-category dispatch

---

## 1. Binary Infix (Same-Category, Left-Associative)

### Structural Pattern

```
a OP b : Cat
```

DSL syntax:

```rust
Add . a:Int, b:Int |- a "+" b : Int;
```

### Classification Criteria

- `syntax.len() >= 3`
- `syntax[0]` is `NonTerminal { category: same_as_result }`
- `syntax[1]` is `Terminal`

**Source:** `classify.rs`, `classify_is_infix()`

### BP Assignment

At precedence level *k*:

```
(left_bp, right_bp) = (2k + 2, 2k + 3)
```

Since `left_bp < right_bp`, same-level operators stop the recursive call,
producing left-associative grouping.

### Generated Code

```rust
// BP lookup
fn infix_bp_Int<'a>(token: &Token<'a>) -> Option<(u8, u8)> {
    match token {
        Token::Plus => Some((2, 3)),
        _ => None,
    }
}

// AST construction
fn make_infix_Int<'a>(token: &Token<'a>, lhs: Int, rhs: Int) -> Int {
    match token {
        Token::Plus => Int::Add(Box::new(lhs), Box::new(rhs)),
        _ => unreachable!("make_infix called with non-infix token"),
    }
}
```

### Parse Example

Input: `1 + 2 + 3` with `Add` at BPs `(2, 3)`:

```
parse_Int(tokens, 0, min_bp=0)
  prefix: lhs = 1
  loop: "+" → (2, 3), 2 ≥ 0 → continue
        rhs = parse_Int(tokens, 2, min_bp=3)
          prefix: lhs = 2
          loop: "+" → (2, 3), 2 < 3 → BREAK   ← same operator stops
          return 2
        lhs = Add(1, 2)
  loop: "+" → (2, 3), 2 ≥ 0 → continue
        rhs = parse_Int(tokens, 4, min_bp=3)
          prefix: lhs = 3
          loop: end of input → break
          return 3
        lhs = Add(Add(1, 2), 3)                ← left-associative
```

---

## 2. Binary Infix (Right-Associative)

### Structural Pattern

```
a OP b : Cat right
```

DSL syntax:

```rust
Pow . a:Int, b:Int |- a "^" b : Int right;
```

### Classification Criteria

Same as left-associative infix. The `right` keyword sets
`RuleSpec::associativity = Associativity::Right`.

### BP Assignment

At precedence level *k*:

```
(left_bp, right_bp) = (2k + 3, 2k + 2)    ← swapped
```

Since `left_bp > right_bp`, same-level operators pass the `left_bp ≥ min_bp`
check in the recursive call, producing right-associative grouping.

### Generated Code

```rust
fn infix_bp_Int<'a>(token: &Token<'a>) -> Option<(u8, u8)> {
    match token {
        Token::Caret => Some((7, 6)),    // right-assoc: left > right
        _ => None,
    }
}
```

### Parse Example

Input: `2 ^ 3 ^ 4` with `Pow` at BPs `(7, 6)`:

```
parse_Int(tokens, 0, min_bp=0)
  prefix: lhs = 2
  loop: "^" → (7, 6), 7 ≥ 0 → continue
        rhs = parse_Int(tokens, 2, min_bp=6)
          prefix: lhs = 3
          loop: "^" → (7, 6), 7 ≥ 6 → continue  ← right-assoc: passes!
                rhs = parse_Int(tokens, 4, min_bp=6)
                  prefix: lhs = 4
                  return 4
                lhs = Pow(3, 4)
          return Pow(3, 4)
        lhs = Pow(2, Pow(3, 4))                    ← right-associative
```

---

## 3. Unary Prefix

### Structural Pattern

```
OP a : Cat
```

DSL syntax:

```rust
Neg . a:Int |- "-" a : Int;
```

### Classification Criteria

- `syntax.len() == 2`
- `syntax[0]` is `Terminal`
- `syntax[1]` is `NonTerminal { category: same_as_result }`

**Source:** `classify.rs`, `classify_is_unary_prefix()`

### BP Assignment

Unary prefix operators are **not** infix — they are handled by the nud
(prefix) handler. Their BP is computed in `pipeline.rs`:

```
prefix_bp = max_infix_bp + 2    (default)
          = N                   (when prefix(N) is specified)
```

Where `max_infix_bp = max(left_bp, right_bp)` across all non-postfix infix
operators in the same category.

### Generated Code

The prefix handler calls `parse_Cat(tokens, pos, prefix_bp)` for the operand:

```rust
fn parse_Int_prefix<'a>(tokens: &[(Token<'a>, Range)], pos: &mut usize)
    -> Result<Int, ParseError>
{
    match &tokens[*pos].0 {
        Token::Minus => {
            *pos += 1;
            let a = parse_Int(tokens, pos, 9)?;  // prefix_bp = max_infix_bp + 2
            Ok(Int::Neg(Box::new(a)))
        }
        // ... other prefix handlers
    }
}
```

### Parse Example

Input: `-3 + 5` with `Neg` at `prefix_bp = 9`, `Add` at `(2, 3)`:

```
parse_Int(tokens, 0, min_bp=0)
  prefix: token = "-" → consume
          a = parse_Int(tokens, 1, min_bp=9)
            prefix: lhs = 3
            loop: "+" → (2, 3), 2 < 9 → BREAK  ← + is too weak for prefix
            return 3
          lhs = Neg(3)
  loop: "+" → (2, 3), 2 ≥ 0 → continue
        rhs = parse_Int(tokens, 3, min_bp=3)
          prefix: lhs = 5
          return 5
        lhs = Add(Neg(3), 5)                    ← (-3) + 5, not -(3 + 5)
```

---

## 4. Postfix

### Structural Pattern

```
a OP : Cat
```

DSL syntax:

```rust
Fact . a:Int |- a "!" : Int;
```

### Classification Criteria

- `syntax.len() == 2`
- `syntax[0]` is `NonTerminal { category: same_as_result }`
- `syntax[1]` is `Terminal`

**Source:** `classify.rs`, `classify_is_postfix()`

### BP Assignment

Postfix operators are assigned in the **second pass** of
`analyze_binding_powers()`, above the prefix gap:

```
left_bp  = postfix_base + 1 + 2j    (j = 0-indexed postfix declaration order)
right_bp = 0                         (unused — no right operand)
```

Where `postfix_base = max_non_postfix_precedence + 2`.

### Generated Code

```rust
fn postfix_bp_Int<'a>(token: &Token<'a>) -> Option<u8> {
    match token {
        Token::Bang => Some(11),   // left_bp only
        _ => None,
    }
}

fn make_postfix_Int<'a>(token: &Token<'a>, operand: Int) -> Int {
    match token {
        Token::Bang => Int::Fact(Box::new(operand)),
        _ => unreachable!("make_postfix called with non-postfix token"),
    }
}
```

The led chain checks postfix **before** infix:

```rust
// In the Pratt loop:
if let Some(l_bp) = postfix_bp_Int(token) {
    if l_bp < min_bp { break; }
    let op_token = token.clone();
    *pos += 1;
    lhs = make_postfix_Int(&op_token, lhs);    // no recursive call
}
```

### Parse Example

Input: `3 + 5!` with `Fact` at `left_bp = 11`, `Add` at `(2, 3)`:

```
parse_Int(tokens, 0, min_bp=0)
  prefix: lhs = 3
  loop: "+" → infix (2, 3), 2 ≥ 0 → continue
        rhs = parse_Int(tokens, 2, min_bp=3)
          prefix: lhs = 5
          loop: "!" → postfix left_bp=11, 11 ≥ 3 → continue
                lhs = Fact(5)                       ← postfix binds first
          loop: end of input → break
          return Fact(5)
        lhs = Add(3, Fact(5))                       ← 3 + (5!)
```

### Prefix vs. Postfix Interaction

Input: `-5!` with `Neg` at `prefix_bp = 9`, `Fact` at `left_bp = 11`:

```
parse_Int(tokens, 0, min_bp=0)
  prefix: token = "-" → consume
          a = parse_Int(tokens, 1, min_bp=9)
            prefix: lhs = 5
            loop: "!" → postfix left_bp=11, 11 ≥ 9 → continue
                  lhs = Fact(5)                     ← postfix wins over prefix
            return Fact(5)
          lhs = Neg(Fact(5))                        ← -(5!), not (-5)!
```

---

## 5. Mixfix / N-ary

### Structural Pattern

```
a OP₁ b OP₂ c : Cat
```

DSL syntax:

```rust
Tern . c:Int, t:Int, e:Int |- c "?" t ":" e : Int right;
```

### Classification Criteria

An infix rule with ≥ 2 terminals between operands. Detected by
`extract_mixfix_parts()` in `pipeline.rs`:

- First item is `NT(same_category)` — left operand
- Second item is `Terminal` — trigger terminal (e.g., `?`)
- Remaining items alternate between `NT` and `Terminal` — middle/final operands
  with separator terminals

### BP Assignment

Mixfix operators get the same BP pair as regular infix operators at their
precedence level. The trigger terminal (first terminal after the left operand)
is used as the BP lookup key:

```
At level k:  (left_bp, right_bp) = (2k+2, 2k+3)  or  (2k+3, 2k+2) if right
```

The `left_bp` determines whether the mixfix operator can steal the left operand
from a parent. The `right_bp` is used for the **final** operand only.

### Middle Operands

Middle operands (all except the first and last) are parsed at `min_bp = 0`,
like grouping. This means any expression can appear between the separator
terminals, regardless of precedence:

```rust
// In handle_mixfix_Int():
Token::Question => {
    let param_t = parse_Int(tokens, pos, 0)?;    // middle: min_bp = 0
    expect_token(tokens, pos, Token::Colon)?;     // expect ":"
    let param_e = parse_Int(tokens, pos, r_bp)?;  // final: uses right_bp
    Ok(Int::Tern(Box::new(lhs), Box::new(param_t), Box::new(param_e)))
}
```

### Parse Example

Input: `1 + 2 ? 3 * 4 : 5` with `Tern` at `(2, 3)` right-assoc → `(3, 2)`,
`Add` at `(2, 3)`, `Mul` at `(4, 5)`:

Wait — if `Tern` is declared first (lowest precedence), it gets level 0.
Let's use a realistic ordering:

```rust
Tern . c:Int, t:Int, e:Int |- c "?" t ":" e : Int right;  // level 0: (3, 2)
Add  . a:Int, b:Int |- a "+" b : Int;                      // level 1: (4, 5)
Mul  . a:Int, b:Int |- a "*" b : Int;                      // level 2: (6, 7)
```

Input: `1 + 2 ? 3 * 4 : 5`:

```
parse_Int(tokens, 0, min_bp=0)
  prefix: lhs = 1
  loop: "+" → infix (4, 5), 4 ≥ 0 → continue
        rhs = parse_Int(tokens, 2, min_bp=5)
          prefix: lhs = 2
          loop: "?" → mixfix (3, 2), 3 < 5 → BREAK  ← ? is weaker than +
          return 2
        lhs = Add(1, 2)
  loop: "?" → mixfix (3, 2), 3 ≥ 0 → continue
        middle_t = parse_Int(tokens, 4, min_bp=0)  ← reset to 0
          parses "3 * 4" → Mul(3, 4)
        expect ":"
        final_e = parse_Int(tokens, 8, min_bp=2)
          prefix: lhs = 5
          return 5
        lhs = Tern(Add(1, 2), Mul(3, 4), 5)
```

---

## 6. Cross-Category

### Structural Pattern

```
a:CatA OP b:CatA : CatB
```

DSL syntax:

```rust
EqInt . a:Int, b:Int |- a "==" b : Bool;
```

### Classification Criteria

- `syntax.len() == 3`
- `syntax[0]` and `syntax[2]` are `NonTerminal` with the same category (`CatA`)
- `CatA != result_category` (`CatB`)
- `CatA` is a known category name

**Source:** `classify.rs`, `classify_cross_category()`

### BP Treatment

Cross-category operators participate in the BP table of their **source**
category (`CatA`), not their result category (`CatB`). This is because the
operands are parsed using `parse_CatA()`, which consults `CatA`'s BP table.

The result category (`CatB`) gets a **dispatch wrapper** that delegates to
`parse_CatA()`:

```rust
fn parse_Bool<'a>(tokens: &[(Token<'a>, Range)], pos: &mut usize, min_bp: u8)
    -> Result<Bool, ParseError>
{
    // Try own parsing first (And, Or, etc.)
    // If token matches a cross-category trigger, delegate:
    let a = parse_Int(tokens, pos, 0)?;
    match &tokens[*pos].0 {
        Token::EqEq => {
            *pos += 1;
            let b = parse_Int(tokens, pos, r_bp)?;
            Ok(Bool::EqInt(Box::new(a), Box::new(b)))
        }
        // ...
    }
}
```

### BP Independence

Since cross-category operators live in the source category's BP namespace,
they compete with that category's operators for precedence. For example, if
`Int` has `Add (2,3)` and `EqInt (4,5)`, then `1 + 2 == 3` parses as
`(1 + 2) == 3` because `==` has higher BP than `+` in the `Int` namespace.

---

## 7. Cast

### Structural Pattern

```
k:CatA : CatB
```

DSL syntax:

```rust
IntToProc . Int ::= Proc ;            // old syntax
// (cast rules are typically implicit via the type hierarchy)
```

### Classification Criteria

- `syntax.len() == 1`
- `syntax[0]` is `NonTerminal { category: CatA }` where `CatA != result_category`
- `CatA` is a known category
- Rule is not a variable rule

**Source:** `classify.rs`, `classify_cast()`

### BP Treatment

Cast rules have **no binding power involvement**. They are handled entirely
by the prefix (nud) handler. When the current token matches the FIRST set of
the source category but not the result category, the parser calls
`parse_CatA(tokens, pos, 0)` and wraps the result:

```rust
Token::Integer(_) => {
    let k = parse_Int(tokens, pos, 0)?;
    Ok(Proc::IntToProc(Box::new(k)))
}
```

Because the cast is in the prefix handler, after the cast completes, the
Pratt infix loop continues. This means cast operands participate in the
infix operators of the **result** category:

```
If Proc has parallel composition |:
  "3 + 4 | 5 + 6"
  → PPar(IntToProc(Add(3, 4)), IntToProc(Add(5, 6)))
```

---

## 8. Grouping

### Structural Pattern

```
( expr )
```

DSL syntax:

```rust
// Grouping is not an explicit rule — it's handled by structural
// prefix rules with matching delimiters:
Paren . a:Int |- "(" a ")" : Int;
```

### BP Treatment

Grouping resets `min_bp` to 0 for the inner expression. This allows any
operator inside the parentheses, regardless of the surrounding context:

```rust
Token::LParen => {
    *pos += 1;
    let inner = parse_Int(tokens, pos, 0)?;  // reset to min_bp = 0
    expect_token(tokens, pos, Token::RParen)?;
    Ok(inner)    // unwrap — no AST node for grouping
}
```

### Parse Example

Input: `(1 + 2) * 3` with `Add (2,3)`, `Mul (4,5)`:

```
parse_Int(tokens, 0, min_bp=0)
  prefix: token = "(" → consume
          inner = parse_Int(tokens, 1, min_bp=0)  ← reset
            prefix: lhs = 1
            loop: "+" → (2, 3), 2 ≥ 0 → continue
                  rhs = 2
                  lhs = Add(1, 2)
            loop: ")" → not an infix operator → break
            return Add(1, 2)
          expect ")"
          lhs = Add(1, 2)
  loop: "*" → (4, 5), 4 ≥ 0 → continue
        rhs = parse_Int(tokens, 5, min_bp=5)
          prefix: lhs = 3, return 3
        lhs = Mul(Add(1, 2), 3)                  ← grouping overrides precedence
```

---

## 9. Summary: Operator Form Comparison

```
┌──────────────┬─────────┬──────────────┬────────────┬──────────────────────┐
│ Form         │ Handler │ BP Source    │ Recursive? │ Example              │
├──────────────┼─────────┼──────────────┼────────────┼──────────────────────┤
│ Binary infix │ led     │ BP table     │ Yes (rhs)  │ a + b                │
│ Right infix  │ led     │ BP table     │ Yes (rhs)  │ a ^ b                │
│ Unary prefix │ nud     │ pipeline.rs  │ Yes        │ -a                   │
│ Postfix      │ led     │ BP table     │ No         │ a!                   │
│ Mixfix       │ led     │ BP table     │ Yes (each) │ a ? b : c            │
│ Cross-cat    │ dispatch│ source cat   │ Yes        │ a:Int == b:Int : Bool│
│ Cast         │ nud     │ None         │ Yes        │ k:Int : Proc         │
│ Grouping     │ nud     │ Reset to 0   │ Yes        │ (a + b)              │
└──────────────┴─────────┴──────────────┴────────────┴──────────────────────┘
```
