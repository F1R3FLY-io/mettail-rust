# PraTTaIL: Pratt Parser Generator

**Date:** 2026-02-14

---

## Table of Contents

1. [Pratt Parsing Primer](#1-pratt-parsing-primer)
2. [Rule Classification](#2-rule-classification)
3. [Binding Power Assignment Algorithm](#3-binding-power-assignment-algorithm)
4. [Handling Same-Operator-Different-Category](#4-handling-same-operator-different-category)
5. [Generated Code Structure](#5-generated-code-structure)
6. [The make_infix Dispatch Table](#6-the-make_infix-dispatch-table)
7. [Interaction Between Pratt Loop and Prediction Engine](#7-interaction-between-pratt-loop-and-prediction-engine)
8. [Worked Example: RhoCalc Proc Parsing](#8-worked-example-rhocalc-proc-parsing)

---

## 1. Pratt Parsing Primer

Pratt parsing (also called "top-down operator precedence parsing") handles
infix, prefix, and postfix operators via a simple loop that uses **binding
power pairs** `(left_bp, right_bp)` to determine precedence and associativity.

The core algorithm:

```
parse(tokens, pos, min_bp):
  lhs = parse_prefix(tokens, pos)       // Parse atom/prefix (nud)

  loop:
    token = peek(tokens, pos)
    if no infix binding power for token:
      break
    (l_bp, r_bp) = infix_bp(token)
    if l_bp < min_bp:                    // Precedence too low
      break
    consume(token)
    rhs = parse(tokens, pos, r_bp)       // Recurse with right BP
    lhs = make_infix(token, lhs, rhs)    // Construct AST node

  return lhs
```

Binding power pairs encode both precedence and associativity:

```
+------------------+-----------------------------------+-------------------+
| Associativity    | Binding powers                    | Example           |
+------------------+-----------------------------------+-------------------+
| Left-associative | left_bp < right_bp                | + gets (2, 3)     |
|                  | a + b + c  =  (a + b) + c        | - gets (2, 3)     |
|                  | After parsing a+b, l_bp=2 < 3, so |                   |
|                  | the next + breaks the inner loop   |                   |
|                  | and a+b becomes the lhs.           |                   |
+------------------+-----------------------------------+-------------------+
| Right-associative| left_bp > right_bp                | ^ gets (5, 4)     |
|                  | a ^ b ^ c  =  a ^ (b ^ c)        |                   |
|                  | After parsing a, l_bp=5 >= 0, so  |                   |
|                  | we consume ^ and recurse with      |                   |
|                  | min_bp=4. Inside, b sees ^, and    |                   |
|                  | l_bp=5 >= 4, so it consumes ^ too. |                   |
+------------------+-----------------------------------+-------------------+
```

---

## 2. Rule Classification

PraTTaIL classifies each grammar rule into one of four categories:

```
+------------------+----------------------------------------+-------------------+
| Classification   | Criteria                               | Handled by        |
+------------------+----------------------------------------+-------------------+
| Infix            | is_infix == true                       | Pratt loop        |
|                  | Pattern: Cat OP Cat -> Cat              | (infix_bp,        |
|                  | Both operands and result are same cat   |  make_infix)      |
+------------------+----------------------------------------+-------------------+
| Unary Prefix     | is_unary_prefix == true                | RD handler +      |
|                  | Pattern: "OP" Cat -> Cat                | prefix dispatch   |
|                  | Exactly [Terminal, NonTerminal(same)]   | Uses high bp      |
|                  | Examples: Neg ("-" a), Not ("not" a)    | (max_infix+2)     |
+------------------+----------------------------------------+-------------------+
| Prefix           | Not infix, not var, not literal         | RD handler +      |
|                  | First syntax item is a Terminal          | prefix dispatch   |
|                  | Pattern: "terminal" ... -> Cat           | Uses bp=0         |
+------------------+----------------------------------------+-------------------+
| Atom             | is_var == true OR is_literal == true    | Auto-generated    |
|                  | Variables: bare Ident -> Cat::CatVar    | in prefix handler |
|                  | Literals: Integer/Boolean/String/Float  |                   |
+------------------+----------------------------------------+-------------------+
| Structural       | Not infix, has complex syntax           | RD handler        |
|                  | Binders, collections, patterns           | (standalone fn)   |
|                  | Pattern: "(" zip(...) ")" "." "{" ... "}" |                 |
+------------------+----------------------------------------+-------------------+
```

### Classification Algorithm

```
for each rule R in LanguageSpec.rules:
  if R.is_infix:
    classify as INFIX
    -> extract InfixRuleInfo for binding power analysis
  elif R.is_var:
    classify as ATOM (variable)
    -> auto-generate Ident match arm in prefix handler
  elif R.is_literal:
    classify as ATOM (literal)
    -> auto-generate Integer/Boolean/StringLit/Float match arm
  elif R.is_unary_prefix:
    classify as UNARY PREFIX
    -> generate RD handler with prefix_bp = max_infix_bp + 2
    -> add prefix dispatch arm for the leading terminal
  elif R.syntax starts with Terminal and has complex structure:
    classify as STRUCTURAL
    -> generate RD handler function + prefix dispatch arm
  else:
    classify as PREFIX
    -> generate RD handler function + prefix dispatch arm
```

### Unary Prefix Detection

A rule qualifies as unary prefix (`is_unary_prefix == true`) when the macros
crate's bridge layer detects this pattern in `convert_rule()`:

1. The syntax pattern has exactly 2 items
2. The first item is a `Literal` (terminal token)
3. The second item is a `Param` (nonterminal reference)
4. The param's type matches the rule's result category

This classification is set by the `prattail_bridge.rs` module before the
`LanguageSpec` reaches the parser generator.

> **Source reference:** The classification criteria are checked in the
> `convert_rule()` function in `macros/src/gen/syntax/parser/prattail_bridge.rs`.
> This is where `is_unary_prefix`, `is_infix`, `is_postfix`, and `associativity`
> fields are set on each `RuleSpec`.

### Infix Detection Criteria

A rule is classified as infix when `RuleSpec.is_infix == true`, which the
macros crate sets based on the HOL judgement syntax:

```
Add . a:Int, b:Int |- a "+" b : Int
      ^^^^^  ^^^^^    ^  ^^^  ^
      left   right   left OP  right  -> both params match result category
```

The macros crate checks:
1. The rule has exactly 3 syntax items: NonTerminal, Terminal, NonTerminal.
2. Both nonterminals reference the same category as the rule's result.
3. The terminal is a single operator token.

Cross-category binary rules (like `Eq: a:Int, b:Int |- a "==" b : Bool`)
are NOT classified as infix because the operand category (`Int`) differs
from the result category (`Bool`). These are handled by the cross-category
dispatch layer instead.

---

## 3. Binding Power Assignment Algorithm

### Input

`analyze_binding_powers` receives a list of `InfixRuleInfo` structs, each
containing a label, terminal, category, result_category, and associativity.

### Algorithm

```
GROUP infix rules by category:
  by_category = { "Int": [Add, Sub, Pow, CustomOp], "Bool": [EqBool, Comp], ... }

For each category:
  precedence = 2           // Start at 2 (leave 0 for entry, 1 for padding)

  For each rule in declaration order:
    match rule.associativity:
      Left:
        left_bp  = precedence
        right_bp = precedence + 1
        precedence += 2
      Right:
        left_bp  = precedence + 1
        right_bp = precedence
        precedence += 2

    Add to table: InfixOperator {
      terminal, category, result_category,
      left_bp, right_bp, label, is_cross_category
    }
```

### Precedence by Declaration Order

Operators declared first get the **lowest** precedence. This follows the
mathematical convention that addition (lower precedence) is typically listed
before multiplication (higher precedence). The `language!` macro user
controls precedence by ordering rules:

```
terms {
    Add . a:Int, b:Int |- a "+" b : Int;    // precedence 2 (lowest)
    Sub . a:Int, b:Int |- a "-" b : Int;    // precedence 4
    Mul . a:Int, b:Int |- a "*" b : Int;    // precedence 6
    Pow . a:Int, b:Int |- a "^" b : Int;    // precedence 8 (highest)
}
```

Resulting binding power table:

```
+----------+---------+----------+----------+---------------+
| Operator | Assoc   | left_bp  | right_bp | Meaning       |
+----------+---------+----------+----------+---------------+
| +        | Left    |    2     |    3     | 1+2+3=(1+2)+3 |
| -        | Left    |    4     |    5     | 1-2-3=(1-2)-3 |
| *        | Left    |    6     |    7     | 2*3*4=(2*3)*4 |
| ^        | Right   |    9     |    8     | 2^3^2=2^(3^2) |
+----------+---------+----------+----------+---------------+
```

### Unary Prefix Binding Power

After computing the infix binding power table, unary prefix operators receive
a binding power that ensures they bind tighter than all infix operators:

```
For each category C:
  max_infix_bp = max(all infix left_bp and right_bp for C)
  unary_prefix_bp = max_infix_bp + 2
```

For the Calculator example above (max infix bp for Int = 9):

```
+----------+-------------------+-------------------------------------------------+
| Operator | prefix_bp         | Effect                                          |
+----------+-------------------+-------------------------------------------------+
| - (Neg)  | 11 (= 9 + 2)     | -3+5 = (-3)+5 because parse_Int(tokens,pos,11)  |
|          |                   | returns after NumLit(3), before seeing "+"       |
+----------+-------------------+-------------------------------------------------+
```

This binding power is stored in `RDRuleInfo.prefix_bp` and used as the `min_bp`
argument in the recursive `parse_Category()` call within the RD handler. The
high value causes the Pratt loop to break immediately after parsing an atom,
giving unary prefix operators the highest effective precedence.

**Key insight**: The unary prefix binding power is NOT part of the `infix_bp`
table. It only affects the recursive call *inside* the prefix handler's RD
function. The Pratt infix loop is unaware of it—this separation is what allows
the same token (e.g., `-`) to work as both a unary prefix (in the RD handler)
and a binary infix (in the Pratt loop).

---

## 4. Handling Same-Operator-Different-Category

When the same operator symbol appears in multiple categories (e.g., `+` is
used for both `Int::Add` and `Str::AddStr`), the binding power table stores
separate entries per category:

```
operators = [
  InfixOperator { terminal: "+", category: "Int", label: "Add",    left_bp: 2, right_bp: 3 },
  InfixOperator { terminal: "+", category: "Str", label: "AddStr", left_bp: 2, right_bp: 3 },
]
```

The `operators_for_category(cat)` method filters by category, so:

- `parse_Int`'s `infix_bp` function knows `+` has BP (2, 3) for Int.
- `parse_Str`'s `infix_bp` function knows `+` has BP (2, 3) for Str.
- `parse_Bool`'s `infix_bp` function returns `None` for `+`.

Each category gets its **own** `infix_bp` and `make_infix` functions,
scoped to that category's operators.

Cross-category operators (like `==` in `Int "==" Int -> Bool`) are stored
with `is_cross_category: true` and filtered out of the per-category Pratt
loop. They are handled by the dispatch layer instead.

---

## 5. Generated Code Structure

For each category C, `generate_pratt_parser` produces:

```
// ---- If C has infix operators ----

fn infix_bp(token: &Token) -> Option<(u8, u8)> {
    match token {
        Token::Plus  => Some((2, 3)),     // Add, left-assoc
        Token::Minus => Some((4, 5)),     // Sub, left-assoc
        Token::Caret => Some((9, 8)),     // Pow, right-assoc
        _ => None,
    }
}

fn make_infix(token: &Token, lhs: Int, rhs: Int) -> Int {
    match token {
        Token::Plus  => Int::Add(Box::new(lhs), Box::new(rhs)),
        Token::Minus => Int::Sub(Box::new(lhs), Box::new(rhs)),
        Token::Caret => Int::Pow(Box::new(lhs), Box::new(rhs)),
        _ => unreachable!("make_infix called with non-infix token"),
    }
}

fn parse_Int(tokens: &[(Token, Span)], pos: &mut usize, min_bp: u8) -> Result<Int, String> {
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

// ---- If C has NO infix operators ----

fn parse_Name(tokens: &[(Token, Span)], pos: &mut usize, _min_bp: u8) -> Result<Name, String> {
    parse_Name_prefix(tokens, pos)
}

// ---- Prefix handler (always generated) ----

fn parse_Int_prefix(tokens: &[(Token, Span)], pos: &mut usize) -> Result<Int, String> {
    if *pos >= tokens.len() {
        return Err("unexpected end of input, expected Int expression".into());
    }
    match &tokens[*pos].0 {
        Token::Minus => { parse_neg(tokens, pos) },         // "-" a -> Neg (unary prefix)
        Token::Pipe => { parse_len(tokens, pos) },          // |s| -> Len
        Token::KwError => { parse_err(tokens, pos) },       // "error" -> Err
        Token::LParen => {                                   // Grouping
            *pos += 1;
            let expr = parse_Int(tokens, pos, 0)?;
            expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
            Ok(expr)
        },
        Token::Ident(ref name) => {                          // Variable
            let var_name = name.clone();
            *pos += 1;
            Ok(Int::IVar(OrdVar(Var::Free(get_or_create_var(var_name)))))
        },
        other => Err(format!("expected Int expression at position {}, found {:?}", *pos, other)),
    }
}

// ---- Unary prefix RD handler ----
// Generated for unary prefix rules; uses high bp to capture only immediate operand

fn parse_neg(tokens: &[(Token, Span)], pos: &mut usize) -> Result<Int, String> {
    expect_token(tokens, pos, |t| matches!(t, Token::Minus), "-")?;
    let a = parse_Int(tokens, pos, 11)?;   // 11 = max_infix_bp(9) + 2
    Ok(Int::Neg(Box::new(a)))
}
```

---

## 6. The make_infix Dispatch Table

`make_infix` is a simple token-to-constructor dispatch:

```
fn make_infix(token: &Token, lhs: Cat, rhs: Cat) -> Cat {
    match token {
        Token::Plus  => Cat::Add(Box::new(lhs), Box::new(rhs)),
        Token::Star  => Cat::Mul(Box::new(lhs), Box::new(rhs)),
        ...
        _ => unreachable!("make_infix called with non-infix token"),
    }
}
```

Key properties:

1. **One arm per operator.** The number of arms equals the number of infix
   operators in this category.

2. **All operands are Box-wrapped.** Binary infix operators always produce
   `Cat::Label(Box<Cat>, Box<Cat>)` to avoid infinite-sized types.

3. **The unreachable branch is a safety net.** It should never be reached
   because `infix_bp` returns `None` for non-infix tokens, causing the
   Pratt loop to break before calling `make_infix`.

4. **Cross-category operators are excluded.** Operators like `==` in
   `Int "==" Int -> Bool` do not appear in `make_infix` for either `Int`
   or `Bool`. They are handled by the dispatch layer's own match arms.

---

## 7. Interaction Between Pratt Loop and Prediction Engine

The Pratt loop and prediction engine interact at two points:

### Point 1: Prefix Handler Dispatch

The prediction engine's dispatch table determines which prefix handler to
call. The prefix handler is invoked by `parse_Cat_prefix`, which is called
from the Pratt loop's first line: `let mut lhs = parse_Cat_prefix(tokens, pos)?`.

```
                    parse_Cat(tokens, pos, min_bp)
                           |
                           v
                    parse_Cat_prefix(tokens, pos)
                           |
                    +------+------+
                    | Dispatch    |  <--- Prediction engine's dispatch table
                    | Table       |       determines which handler to call
                    +------+------+
                           |
              +------------+------------+
              |            |            |
         Direct(PZero) Lookahead   Variable
              |         (peek+1)      |
              v            |          v
         parse_pzero()     |     Cat::CatVar(...)
                           v
                    parse_poutput() or Cat::PVar(...)
```

### Point 2: Infix Loop Termination

The Pratt loop calls `infix_bp(token)` to determine if the next token is an
infix operator. This function is generated from the binding power table (Phase
2), NOT from the prediction engine's FIRST sets. The separation is intentional:

- **FIRST sets** determine what can *start* an expression (prefix dispatch).
- **Binding powers** determine what can *continue* an expression (infix loop).

These are disjoint concerns:

```
FIRST(Int) = {Integer, Ident, Pipe, LParen, Caret, ...}
                                                 ^-- lambda prefix
INFIX(Int) = {Plus, Minus, Star, Caret, Tilde, ...}
                                  ^-- power operator

Note: Caret appears in FIRST(Int) because lambda ^x.{body}
      starts with ^, AND in INFIX(Int) because a^b is exponentiation.
      These are different uses resolved by context: the Pratt loop
      only checks infix_bp AFTER parsing a prefix expression.
```

### Point 3: Cross-Category Dispatch Wrapper

When a category has cross-category rules, the dispatch layer wraps the
Pratt parser with additional logic:

```
parse_Bool(tokens, pos, min_bp)         // dispatch wrapper
    |
    +-- unique-to-source tokens -> parse_Int, expect ==, parse_Int
    |
    +-- unique-to-target tokens -> parse_Bool_own(tokens, pos)
    |
    +-- ambiguous tokens -> save/restore, try cross then own
    |
    +-- fallback -> parse_Bool_own(tokens, pos)

parse_Bool_own(tokens, pos)             // original Pratt parser
    |
    +-- parse_Bool_prefix(tokens, pos)  // prefix dispatch
    |
    +-- Pratt infix loop (&&, ==)       // same-category infix
```

The original `parse_Bool` (with the Pratt loop) is renamed to
`parse_Bool_own`, and a new `parse_Bool` wrapper is generated that
handles cross-category dispatch before delegating to the Pratt parser.

---

## 8. Worked Example: RhoCalc Proc Parsing

### Grammar (Proc category, infix only)

```
Add . a:Proc, b:Proc |- a "+" b : Proc   (left-associative)
```

### Binding Power Table

```
+ -> (left_bp: 2, right_bp: 3, label: "Add", category: "Proc")
```

### Parsing `{} + *(@({})) + error`

Tokens: `[EmptyBraces, Plus, Star, LParen, At, LParen, EmptyBraces, RParen,
          RParen, Plus, KwError, Eof]`

```
parse_Proc(tokens, pos=0, min_bp=0):
  1. parse_Proc_prefix(pos=0):
     match EmptyBraces -> parse_pzero():
       consume EmptyBraces, pos=1
       return Proc::PZero

  lhs = PZero

  2. Pratt loop iteration 1:
     peek(pos=1) = Plus
     infix_bp(Plus) = Some((2, 3))
     l_bp=2 >= min_bp=0 -> continue
     consume Plus, pos=2
     parse_Proc(tokens, pos=2, min_bp=3):
       parse_Proc_prefix(pos=2):
         match Star -> parse_pdrop():
           consume Star, pos=3
           consume LParen, pos=4
           parse_Name(tokens, pos=4, min_bp=0):
             parse_Name_prefix(pos=4):
               match At -> parse_nquote():
                 consume At, pos=5
                 consume LParen, pos=6
                 parse_Proc(tokens, pos=6, min_bp=0):
                   parse_Proc_prefix(pos=6):
                     match EmptyBraces -> PZero, pos=7
                   peek(pos=7) = RParen
                   infix_bp(RParen) = None -> break
                   return PZero
                 consume RParen, pos=8
                 return Name::NQuote(Box::new(PZero))
           consume RParen, pos=9
           return Proc::PDrop(Box::new(NQuote(Box::new(PZero))))

       lhs = PDrop(NQuote(PZero))

       Pratt loop: peek(pos=9) = Plus
       infix_bp(Plus) = Some((2, 3))
       l_bp=2 < min_bp=3 -> break!   (right operand ends here)
       return PDrop(NQuote(PZero))

     rhs = PDrop(NQuote(PZero))
     lhs = make_infix(Plus, PZero, PDrop(NQuote(PZero)))
         = Add(Box(PZero), Box(PDrop(NQuote(PZero))))

  3. Pratt loop iteration 2:
     peek(pos=9) = Plus
     infix_bp(Plus) = Some((2, 3))
     l_bp=2 >= min_bp=0 -> continue
     consume Plus, pos=10
     parse_Proc(tokens, pos=10, min_bp=3):
       parse_Proc_prefix(pos=10):
         match KwError -> parse_err():
           consume KwError, pos=11
           return Proc::Err
       peek(pos=11) = Eof
       infix_bp(Eof) = None -> break
       return Proc::Err

     rhs = Proc::Err
     lhs = make_infix(Plus, Add(PZero, PDrop(NQuote(PZero))), Err)
         = Add(Box(Add(Box(PZero), Box(PDrop(NQuote(PZero))))), Box(Err))

  4. Pratt loop iteration 3:
     peek(pos=11) = Eof
     infix_bp(Eof) = None -> break

  Return: Add(Add(PZero, PDrop(NQuote(PZero))), Err)
```

This is left-associative: `({} + *(@({}))) + error`, exactly as expected.
