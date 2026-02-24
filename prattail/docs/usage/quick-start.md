# PraTTaIL Quick Start Guide

**Getting started: defining a language, understanding the generated parser,
parsing input, and inspecting results.**

---

## Prerequisites

PraTTaIL is part of the MeTTaIL workspace. Ensure you have:

- Rust nightly toolchain (the workspace's `rust-toolchain.toml` selects nightly
  with cranelift; see `.cargo/config.toml` for linker and codegen details)
- The `mettail-rust` workspace checked out
- Dependencies resolved (`cargo build` from workspace root)

PraTTaIL itself is a library crate (`mettail-prattail`) used by the `mettail-macros`
proc-macro crate. You do not invoke PraTTaIL directly -- instead, you write a
`language! { ... }` definition and the macro invokes PraTTaIL at compile time.

---

## Step 1: Define a Language

Create a new Rust file (e.g., `languages/src/calculator.rs`) with a language definition:

```rust
#![allow(non_local_definitions, clippy::crate_in_macro_def)]

use mettail_macros::language;

language! {
    name: Calculator,

    types {
        ![i32] as Int
    },

    terms {
        // Infix operators: declared in precedence order (lowest first)
        Add . a:Int, b:Int |- a "+" b : Int;
        Mul . a:Int, b:Int |- a "*" b : Int;
    },

    equations {
    },

    rewrites {
        AddCongL . | S ~> T |- (Add S R) ~> (Add T R);
        AddCongR . | S ~> T |- (Add L S) ~> (Add L T);
    },
}
```

### Anatomy of the Definition

```
language! {
    name: Calculator,          ←── Language name (used for generated module naming)

    types {
        ![i32] as Int          ←── Category "Int" backed by native Rust type i32
                                   The "!" means it is a native/HOL type
                                   "Int" is the category name in the grammar
    },

    terms {
        Add . a:Int, b:Int     ←── Rule "Add" with parameters a and b, both Int
        |- a "+" b             ←── Syntax pattern: a then "+" then b
        : Int;                 ←── Result category: Int

        Mul . a:Int, b:Int     ←── Higher precedence than Add (declared second)
        |- a "*" b : Int;
    },

    equations { },             ←── Equational axioms (for normalization)
    rewrites { },              ←── Rewrite rules (for operational semantics)
}
```

---

## Step 2: What Gets Generated

When you compile this file, the `language!` macro invokes PraTTaIL, which generates:

### Token Enum
An enum with variants for every terminal symbol plus built-in tokens:

```
Token::Eof, Token::Ident(String), Token::Integer(i64),
Token::Plus, Token::Star, Token::LParen, Token::RParen
```

### Lexer
A `lex(input: &str) -> Result<Vec<(Token, Span)>, String>` function that tokenizes
input using a minimized DFA with alphabet equivalence classes.

### Parser Functions
For each category, Pratt expression parsers:

- `parse_Int(tokens, pos, min_bp)` -- Pratt loop with binding powers
- `parse_Int_prefix(tokens, pos)` -- prefix/atom handler (literals, variables, parens)
- `infix_bp(token) -> Option<(u8, u8)>` -- binding power table
- `make_infix(token, lhs, rhs) -> Int` -- AST construction

### Parse Entry Point
```rust
impl Int {
    pub fn parse(input: &str) -> Result<Int, String> { ... }
}
```

### Auto-Generated AST Variants
The macro also generates the `Int` enum with variants:
- `Int::Add(Box<Int>, Box<Int>)` -- from the Add rule
- `Int::Mul(Box<Int>, Box<Int>)` -- from the Mul rule
- `Int::NumLit(i32)` -- auto-generated for native i32
- `Int::IVar(OrdVar)` -- auto-generated variable variant
- Lambda and application variants (auto-generated for every category)

---

## Step 3: Parse Input

Use the generated `parse` method:

```rust
use mettail_languages::calculator::*;

fn main() {
    // Parse a simple expression
    let result = Int::parse("3 + 4 * 2");
    match result {
        Ok(ast) => println!("Parsed: {:?}", ast),
        Err(e) => println!("Error: {}", e),
    }

    // Parse with variables
    let result = Int::parse("x + 1");
    println!("{:?}", result);

    // Parse with parentheses (override precedence)
    let result = Int::parse("(3 + 4) * 2");
    println!("{:?}", result);
}
```

### Expected Output

```
Parsed: Add(NumLit(3), Mul(NumLit(4), NumLit(2)))

Ok(Add(IVar(OrdVar(Free(FreeVar("x")))), NumLit(1)))

Ok(Mul(Add(NumLit(3), NumLit(4)), NumLit(2)))
```

---

## Step 4: Inspect the Lexer

You can call the lexer directly to see the token stream:

```rust
let tokens = lex("3 + 4 * 2").expect("lex error");
for (token, span) in &tokens {
    println!("{:?} at {}..{}", token, span.start, span.end);
}
```

Output:

```
Integer(3) at 0..1
Plus at 2..3
Integer(4) at 4..5
Star at 6..7
Integer(2) at 8..9
Eof at 9..9
```

---

## Step 5: Use in the REPL

The MeTTaIL REPL provides an interactive environment:

```
$ cargo run -- --language calculator

MeTTaIL REPL (Calculator)
> exec 3 + 4 * 2
result: 11

> let x = 5
x = 5

> exec x + 1
result: 6

> exec (x + 1) * 2
result: 12
```

The REPL:
1. Lexes and parses the input using the PraTTaIL-generated parser
2. Applies rewrite rules to evaluate the expression
3. Displays the result

---

## Step 6: Multi-Category Language

For a language with multiple types:

```rust
language! {
    name: TypedCalc,

    types {
        ![i32] as Int       // Primary category (gets bare identifiers)
        ![bool] as Bool     // Secondary category
    },

    terms {
        Add . a:Int, b:Int |- a "+" b : Int;

        // Cross-category rule: Int operands, Bool result
        Eq . a:Int, b:Int |- a "==" b : Bool;

        // Bool-only prefix operator
        Not . a:Bool |- "not" a : Bool;
    },

    equations { },
    rewrites { },
}
```

Now you can parse both categories:

```rust
// Parse as Int
let int_expr = Int::parse("3 + 4");

// Parse as Bool (cross-category dispatch handles "3 == 4" automatically)
let bool_expr = Bool::parse("3 == 4");

// Parse Bool with not
let not_expr = Bool::parse("not true");
```

### Cross-Category Parsing

When `Bool::parse("3 == 4")` is called:
1. The lexer produces `[Integer(3), EqEq, Integer(4), Eof]`
2. The dispatch code sees `Integer(3)` -- this token is unique to Int's FIRST set
3. It takes the deterministic cross-category path:
   - Parse `Int` expression → `NumLit(3)`
   - Expect `==` → consume
   - Parse `Int` expression → `NumLit(4)`
   - Return `Bool::Eq(NumLit(3), NumLit(4))`

When `Bool::parse("x == y")` is called:
1. The lexer produces `[Ident("x"), EqEq, Ident("y"), Eof]`
2. `Ident` is in both Int and Bool FIRST sets (ambiguous)
3. The dispatch code uses save/restore backtracking:
   - Save position, try parsing as `Int`
   - `Int::parse` succeeds with `IVar(x)`
   - See `EqEq` -- this confirms the cross-category path
   - Parse right side as `Int` → `IVar(y)`
   - Return `Bool::Eq(IVar(x), IVar(y))`

---

## Step 7: Binder Syntax

Binders (lambda abstractions) use the `^x.{body}` syntax:

```rust
// Single binder
let lam = Int::parse("^x.{x + 1}");
// Result: LamInt(Scope(Binder(x), Add(IVar(x), NumLit(1))))

// Multi-binder
let mlam = Int::parse("^[x,y].{x + y}");
// Result: MLamInt(Scope([Binder(x), Binder(y)], Add(IVar(x), IVar(y))))
```

Application uses the `$type(lambda, arg)` syntax:

```rust
// Apply a lambda
let app = Int::parse("$int(^x.{x + 1}, 5)");
```

---

## Troubleshooting Quick Reference

| Symptom | Likely Cause | Fix |
|---|---|---|
| `unexpected character` | Token not in grammar | Check terminal strings in rules |
| `expected Int expression` | Missing prefix handler | Ensure rule starts with a terminal or is a literal/var |
| `unexpected token after parsing` | Trailing unconsumed input | Check for missing operators or extra tokens |
| Precedence seems wrong | Declaration order | Move higher-precedence operators later in the `terms` block |
| Variables not recognized | Non-primary category | Use `type:varname` prefix for non-primary categories |

See `troubleshooting.md` for detailed diagnostics.
