# Worked Examples: Binding Powers in Practice

This document walks through complete examples showing BP assignment, generated
code, and parse traces. Each example builds on the theory from the preceding
documents in this series.

---

## Example 1: Calculator with All Operator Types

### Grammar

```rust
language! {
    name: CalcExample,
    types { ![i32] as Int },
    terms {
        // Lowest precedence first:
        Tern . c:Int, t:Int, e:Int |- c "?" t ":" e : Int right;  // ternary (mixfix)
        Add  . a:Int, b:Int |- a "+" b : Int;                     // addition
        Mul  . a:Int, b:Int |- a "*" b : Int;                     // multiplication
        Pow  . a:Int, b:Int |- a "^" b : Int right;               // exponentiation
        Neg  . a:Int |- "-" a : Int;                              // negation (prefix)
        Fact . a:Int |- a "!" : Int;                              // factorial (postfix)
    },
}
```

### Step 1: Classification

| Rule | Form           | `is_infix` | `is_postfix` | `is_unary_prefix` |
|------|----------------|------------|--------------|-------------------|
| Tern | Mixfix (infix) | true       | false        | false             |
| Add  | Binary infix   | true       | false        | false             |
| Mul  | Binary infix   | true       | false        | false             |
| Pow  | Binary infix   | true       | false        | false             |
| Neg  | Unary prefix   | false      | false        | true              |
| Fact | Postfix        | true       | true         | false             |

### Step 2: BP Assignment

**Pass 1 — Non-postfix operators** (in declaration order):

| Rule | Level *k* | Assoc | Formula          | BP Pair    |
|------|-----------|-------|------------------|------------|
| Tern | 0         | Right | (2(0)+3, 2(0)+2) | **(3, 2)** |
| Add  | 1         | Left  | (2(1)+2, 2(1)+3) | **(4, 5)** |
| Mul  | 2         | Left  | (2(2)+2, 2(2)+3) | **(6, 7)** |
| Pow  | 3         | Right | (2(3)+3, 2(3)+2) | **(9, 8)** |

After pass 1: `precedence = 2 + 2*4 = 10`, `max_infix_bp = 9`.

**Unary prefix:**

```
prefix_bp = max_infix_bp + 2 = 9 + 2 = 11
```

**Pass 2 — Postfix operators:**

```
postfix_prec = 10 + 2 = 12
```

| Rule | Formula | left_bp |
|------|---------|---------|
| Fact | postfix_prec + 1 = 13 | **13** |

### Complete BP Table

```
 BP: 0  1  2  3  4  5  6  7  8  9  10 11 12 13
     │     │  │  │  │  │  │  │  │     │     │
     │     │ Tern│ Add │ Mul │ Pow    │     │
     │     │(R:3,2)│(L:4,5)│(L:6,7)│(R:9,8) Neg   Fact
   entry              │                  prefix postfix
  (min_bp=0)          │                  bp=11  l_bp=13
                      │
              BP number line
```

### Step 3: Generated BP Lookup Functions

```rust
fn infix_bp_Int<'a>(token: &Token<'a>) -> Option<(u8, u8)> {
    match token {
        Token::Plus  => Some((4, 5)),    // Add: left-assoc
        Token::Star  => Some((6, 7)),    // Mul: left-assoc
        Token::Caret => Some((9, 8)),    // Pow: right-assoc
        _ => None,
    }
}

fn mixfix_bp_Int<'a>(token: &Token<'a>) -> Option<(u8, u8)> {
    match token {
        Token::Question => Some((3, 2)), // Tern: right-assoc
        _ => None,
    }
}

fn postfix_bp_Int<'a>(token: &Token<'a>) -> Option<u8> {
    match token {
        Token::Bang => Some(13),         // Fact
        _ => None,
    }
}
```

### Step 4: Parse Trace for `-3! + 2 ^ 3 ^ 2 ? 1 : 0`

Tokens: `[-, 3, !, +, 2, ^, 3, ^, 2, ?, 1, :, 0]`

```
parse_Int(tokens, pos=0, min_bp=0)
│
├─ PREFIX: token = "-" → Neg handler
│  consume "-", pos=1
│  operand = parse_Int(tokens, pos=1, min_bp=11)    ← prefix_bp
│  │
│  ├─ PREFIX: token = "3" → Int literal, lhs = 3, pos=2
│  │
│  ├─ LOOP: token = "!" → postfix_bp returns 13
│  │  13 ≥ 11 → continue                             ← postfix > prefix
│  │  consume "!", pos=3
│  │  lhs = Fact(3)
│  │
│  ├─ LOOP: token = "+" → infix_bp returns (4, 5)
│  │  4 < 11 → BREAK                                 ← infix < prefix
│  │
│  └─ return Fact(3)
│
│  lhs = Neg(Fact(3))                                 ← -(3!), not (-3)!
│
├─ LOOP: token = "+" → infix_bp returns (4, 5)
│  4 ≥ 0 → continue
│  consume "+", pos=4
│  rhs = parse_Int(tokens, pos=4, min_bp=5)
│  │
│  ├─ PREFIX: token = "2" → lhs = 2, pos=5
│  │
│  ├─ LOOP: token = "^" → infix_bp returns (9, 8)
│  │  9 ≥ 5 → continue
│  │  consume "^", pos=6
│  │  rhs = parse_Int(tokens, pos=6, min_bp=8)
│  │  │
│  │  ├─ PREFIX: token = "3" → lhs = 3, pos=7
│  │  │
│  │  ├─ LOOP: token = "^" → infix_bp returns (9, 8)
│  │  │  9 ≥ 8 → continue                            ← right-assoc: 9 ≥ 8
│  │  │  consume "^", pos=8
│  │  │  rhs = parse_Int(tokens, pos=8, min_bp=8)
│  │  │  │
│  │  │  ├─ PREFIX: token = "2" → lhs = 2, pos=9
│  │  │  │
│  │  │  ├─ LOOP: token = "?" → mixfix_bp returns (3, 2)
│  │  │  │  3 < 8 → BREAK                            ← ternary too weak
│  │  │  │
│  │  │  └─ return 2
│  │  │
│  │  │  lhs = Pow(3, 2)
│  │  │
│  │  ├─ LOOP: token = "?" → mixfix_bp returns (3, 2)
│  │  │  3 < 8 → BREAK
│  │  │
│  │  └─ return Pow(3, 2)
│  │
│  │  lhs = Pow(2, Pow(3, 2))                        ← 2^(3^2), right-assoc
│  │
│  ├─ LOOP: token = "?" → mixfix_bp returns (3, 2)
│  │  3 < 5 → BREAK                                  ← ternary < add's right_bp
│  │
│  └─ return Pow(2, Pow(3, 2))
│
│  lhs = Add(Neg(Fact(3)), Pow(2, Pow(3, 2)))
│
├─ LOOP: token = "?" → mixfix_bp returns (3, 2)
│  3 ≥ 0 → continue
│  consume "?", pos=10
│  middle = parse_Int(tokens, pos=10, min_bp=0)       ← reset for middle
│  │
│  ├─ PREFIX: token = "1" → lhs = 1, pos=11
│  ├─ LOOP: token = ":" → not infix/postfix/mixfix → BREAK
│  └─ return 1
│
│  expect ":", pos=12
│  final = parse_Int(tokens, pos=12, min_bp=2)        ← right_bp of Tern
│  │
│  ├─ PREFIX: token = "0" → lhs = 0, pos=13
│  ├─ LOOP: end of input → BREAK
│  └─ return 0
│
│  lhs = Tern(Add(Neg(Fact(3)), Pow(2, Pow(3, 2))), 1, 0)
│
├─ LOOP: end of input → BREAK
│
└─ return Tern(Add(Neg(Fact(3)), Pow(2, Pow(3, 2))), 1, 0)
```

**Final AST:**

```
          Tern
         / | \
       Add  1  0
      / \
   Neg   Pow
    |    / \
  Fact  2  Pow
    |      / \
    3     3   2
```

Interpretation: `((-3!) + (2 ^ (3 ^ 2))) ? 1 : 0`
= `(-6 + 512) ? 1 : 0` = `506 ? 1 : 0` = `1` (non-zero condition)

---

## Example 2: Multi-Category with Cross-Category

### Grammar

```rust
language! {
    name: MultiCat,
    types {
        ![i32] as Int
        ![bool] as Bool
    },
    terms {
        // Int operators (declaration order = precedence order)
        Add . a:Int, b:Int |- a "+" b : Int;
        Mul . a:Int, b:Int |- a "*" b : Int;
        Neg . a:Int |- "-" a : Int;

        // Cross-category: Int operands, Bool result
        EqInt . a:Int, b:Int |- a "==" b : Bool;

        // Bool operators
        And . a:Bool, b:Bool |- a "and" b : Bool;
        Or  . a:Bool, b:Bool |- a "or"  b : Bool;
        Not . a:Bool |- "not" a : Bool;
    },
}
```

### BP Tables

**Int category:**

| Rule  | Level | Assoc | BP Pair | Form                 |
|-------|-------|-------|---------|----------------------|
| Add   | 0     | Left  | (2, 3)  | infix                |
| Mul   | 1     | Left  | (4, 5)  | infix                |
| EqInt | 2     | Left  | (6, 7)  | cross-category infix |

`max_infix_bp(Int) = 7`, `prefix_bp(Neg) = 9`

**Bool category:**

| Rule | Level | Assoc | BP Pair | Form  |
|------|-------|-------|---------|-------|
| And  | 0     | Left  | (2, 3)  | infix |
| Or   | 1     | Left  | (4, 5)  | infix |

`max_infix_bp(Bool) = 5`, `prefix_bp(Not) = 7`

Note: `EqInt`'s BPs are in the **Int** namespace (level 2), not Bool's.
Bool's own BPs are independent.

### Parse Trace: `1 + 2 == 3 * 4`

Cross-category parsing involves coordination between the source category's
Pratt loop and the result category's dispatch wrapper. The `==` operator lives
in the **Int** BP namespace, so Int-level precedence governs how operands bind:

```
parse_Bool(tokens, pos=0, min_bp=0)
│
├─ Dispatch: token "1" is an integer literal
│  → delegate to cross-category Int parsing
│
│  The dispatch wrapper parses an Int expression, checks for a
│  cross-category operator ("=="), parses the right Int operand,
│  and wraps the result as Bool::EqInt(lhs, rhs).
│
│  Within the Int parsing, BPs determine grouping:
│    "1 + 2" → Add(1, 2)   because + has (2, 3)
│    "3 * 4" → Mul(3, 4)   because * has (4, 5)
│    "==" has (6, 7), so it binds tighter than both + and *
│
│  Result: EqInt(Add(1, 2), Mul(3, 4))
│  But because == is tighter than + in Int's BP table, the actual parse is:
│    lhs = 1, then + continues, rhs of + needs min_bp=3:
│      lhs = 2, then == has left_bp=6 ≥ 3 → continue
│      rhs of == needs min_bp=7: parses "3", * has left_bp=4 < 7 → BREAK
│      lhs = EqInt(2, 3) — but this produces Bool, not Int!
│
│  This is the cross-category boundary: the dispatch wrapper in Bool
│  handles the type transition. The exact control flow depends on the
│  dispatch implementation (see prattail/src/dispatch.rs).
```

The key takeaway is that **BP values determine grouping** within the source
category, and the **dispatch wrapper** handles the category boundary.

### Key Takeaway

- **Int** BPs: `Add(2,3)`, `Mul(4,5)`, `EqInt(6,7)` — `==` binds tighter than `+`
  and `*` within Int expressions.
- **Bool** BPs: `And(2,3)`, `Or(4,5)` — independent namespace.
- Cross-category delegation happens at the Bool level, wrapping Int parsing.

---

## Example 3: Explicit `prefix(N)` Override

### Grammar

```rust
language! {
    name: PrefixExample,
    types { ![i32] as Int },
    terms {
        Add    . a:Int, b:Int |- a "+" b : Int;     // level 0: (2, 3)
        Mul    . a:Int, b:Int |- a "*" b : Int;     // level 1: (4, 5)
        Return . a:Int |- "return" a : Int prefix(3);  // explicit: 3
        Neg    . a:Int |- "-" a : Int;                 // default: 7
    },
}
```

### BP Assignment

| Rule   | Form         | BP                                             |
|--------|--------------|------------------------------------------------|
| Add    | infix        | (2, 3)                                         |
| Mul    | infix        | (4, 5)                                         |
| Return | unary prefix | prefix_bp = **3** (explicit)                   |
| Neg    | unary prefix | prefix_bp = **7** (= max_infix_bp + 2 = 5 + 2) |

### Behavior Differences

**`return` with prefix(3):**

- `return 2 + 3` → the `+` has `left_bp = 2 < 3 = min_bp` → BREAK
  → `Return(2)` then `+` is unparsed — this means `return` only captures
  the immediate atom `2`. Then `+ 3` would cause a parse error at the
  call site (unless there's an enclosing context).

  Actually, let's trace more carefully:

  ```
  parse_Int(..., min_bp=0)
    prefix: "return" → consume
      a = parse_Int(..., min_bp=3)
        prefix: lhs = 2
        loop: "+" → (2, 3), 2 < 3 → BREAK
        return 2
      lhs = Return(2)
    loop: "+" → (2, 3), 2 ≥ 0 → continue
      rhs = parse_Int(..., min_bp=3)
        prefix: lhs = 3
        return 3
      lhs = Add(Return(2), 3)
  ```

  Result: `Add(Return(2), 3)` — `return` only captured `2`, and `+` treats
  the result as a regular operand. This is because `prefix(3)` sits between
  Add's left_bp (2) and right_bp (3).

- `return 2 * 3` → `*` has `left_bp = 4 ≥ 3` → continue
  → `Return(Mul(2, 3))` — `return` captures the multiplication.

**`-` with default prefix_bp=7:**

- `-2 + 3` → `+` has `left_bp = 2 < 7` → BREAK → `Neg(2)`, then `Add(Neg(2), 3)`
- `-2 * 3` → `*` has `left_bp = 4 < 7` → BREAK → `Neg(2)`, then `Mul(Neg(2), 3)`

Both stop immediately because the default prefix_bp (7) is above all infix BPs.

### Summary

| Expression | `return` (prefix=3) | `-` (prefix=7)   |
|------------|---------------------|------------------|
| `OP 2 + 3` | `Add(Return(2), 3)` | `Add(Neg(2), 3)` |
| `OP 2 * 3` | `Return(Mul(2, 3))` | `Mul(Neg(2), 3)` |

The explicit `prefix(3)` makes `return` bind **looser** than `*` but at the
same strength as `+`, allowing multiplication to be captured but making
addition separate. The default `prefix_bp = 7` makes `-` bind **tighter**
than all infix operators, always capturing only the immediate operand.

---

## Summary of BP Mechanics

1. **Declaration order** determines precedence level *k* (0-indexed, lowest first).
2. **Associativity** determines BP pair orientation:
   - Left: `(2k+2, 2k+3)` — `left < right` → same-level stops
   - Right: `(2k+3, 2k+2)` — `left > right` → same-level continues
3. **Three-level hierarchy** ensures `infix < prefix < postfix` regardless of
   declaration order.
4. **`prefix(N)`** overrides the default prefix BP for fine-grained control.
5. **Mixfix** middle operands reset to `min_bp=0` (like grouping).
6. **Cross-category** operators live in the source category's BP namespace.
7. **Casts** bypass BP entirely (prefix handler only).
8. The single comparison `left_bp < min_bp` resolves all precedence and
   associativity decisions.
