# PraTTaIL: Recursive Descent Generator

**Date:** 2026-02-14

---

## Table of Contents

1. [Purpose and Scope](#1-purpose-and-scope)
2. [Pattern Matching on Syntax Items](#2-pattern-matching-on-syntax-items)
3. [Binder Rules and Scope Management](#3-binder-rules-and-scope-management)
4. [Collection Rules](#4-collection-rules)
5. [Pattern Operations](#5-pattern-operations)
6. [Lambda and Application Handlers](#6-lambda-and-application-handlers)
7. [Constructor Generation](#7-constructor-generation)
8. [Worked Example: PInputs Rule](#8-worked-example-pinputs-rule)

---

## 1. Purpose and Scope

The recursive descent (RD) generator handles grammar rules that cannot be
expressed as simple infix or atom patterns. These are **structural constructs**
with multi-token syntax involving delimiters, binders, collections, and
pattern operations.

### What the RD Generator Handles

```
+--------------------+------------------------------------------+-------------------+
| Construct          | Example rule                             | Key feature       |
+--------------------+------------------------------------------+-------------------+
| Delimited prefix   | PDrop . n:Name |- "*" "(" n ")" : Proc  | Terminal sequence |
| Binder             | PNew . ^x.p:[Name -> Proc]               | Scope::new()     |
|                    |   |- "new" "(" x "," p ")" : Proc        |                   |
| Multi-binder       | PInputs . ns:Vec(Name), ^[xs].p          | Vec of binders   |
| Collection         | PPar . ps:HashBag(Proc)                  | HashBag/Set/Vec  |
|                    |   |- "{" ps.*sep("|") "}" : Proc          |                   |
| Zip+Map+Sep        | PInputs . ... |- *zip(ns,xs).*map(...)   | Parallel lists   |
| Optional           | #opt(...)                                 | Save/restore     |
| Cross-category     | NQuote . p:Proc |- "@" "(" p ")" : Name  | Different result |
| Unit (no params)   | PZero . |- "{}" : Proc                   | No captures      |
| Keyword terminal   | Err . |- "error" : Proc                  | Fixed keyword    |
+--------------------+------------------------------------------+-------------------+
```

### What the RD Generator Does NOT Handle

- **Infix rules** (handled by the Pratt loop).
- **Variable rules** (auto-generated in the prefix handler).
- **Literal rules** (auto-generated in the prefix handler).

---

## 2. Pattern Matching on Syntax Items

Each `RDSyntaxItem` variant produces a specific parsing action:

### Terminal -> expect_token

```rust
RDSyntaxItem::Terminal(t) => {
    let variant = terminal_to_variant_name(t);   // e.g., "*" -> "Star"
    // Generated code:
    expect_token(tokens, pos, |t| matches!(t, Token::Star), "*")?;
}
```

This consumes one token and returns an error if the token does not match.

### NonTerminal -> parse_Category

```rust
RDSyntaxItem::NonTerminal { category, param_name } => {
    let parse_fn = format_ident!("parse_{}", category);
    let param = format_ident!("{}", param_name);
    let bp = rule.prefix_bp.unwrap_or(0);
    // Generated code:
    let param_name = parse_Category(tokens, pos, bp)?;
}
```

This recursively parses an expression of the specified category and binds
the result to the parameter name.

The `bp` (binding power) argument controls how much of the right-hand side
the recursive call captures:

- **`bp = 0`** (default): Captures the entire expression to the right,
  including all infix operators. Used by most structural/prefix rules.
- **`bp > 0`** (unary prefix operators): Captures only the immediate operand,
  stopping before any infix operator with binding power ≤ `bp`. This is set
  via `RDRuleInfo.prefix_bp` for rules classified as unary prefix operators
  (see [Unary Prefix Operators](#unary-prefix-operators) below).

### Unary Prefix Operators

A rule is classified as a **unary prefix operator** when its syntax pattern
is exactly `[Terminal(op), NonTerminal(same_category)]`:

```
Neg . a:Int |- "-" a : Int        ← unary prefix (terminal, then same-category operand)
Not . a:Bool |- "not" a : Bool    ← unary prefix (terminal, then same-category operand)
PDrop . n:Name |- "*" "(" n ")"   ← NOT unary prefix (has delimiters)
Len . s:Str |- "|" s "|" : Int    ← NOT unary prefix (cross-category, has delimiters)
```

For unary prefix rules, `RDRuleInfo.prefix_bp` is set to
`max_infix_bp_for_category + 2`, which makes them bind tighter than all
infix operators in the same category. This produces standard behavior:

```
-3 + 5    →  (-3) + 5    (unary minus binds tighter than +)
-3 * 5    →  (-3) * 5    (unary minus binds tighter than *)
--3       →  Neg(Neg(3)) (recursive application)
3 - -5    →  Sub(3, Neg(5)) (binary minus, then unary minus in prefix)
not a && b → (not a) && b (matches C/Java/Rust semantics)
```

Generated parse function for `Neg`:
```rust
fn parse_neg(tokens: &[(Token, Span)], pos: &mut usize) -> Result<Int, String> {
    expect_token(tokens, pos, |t| matches!(t, Token::Minus), "-")?;
    let a = parse_Int(tokens, pos, 12)?;  // 12 = max_infix_bp + 2
    Ok(Int::Neg(Box::new(a)))
}
```

The high binding power (12 in this example) means `parse_Int` will only
capture an atom (literal, variable, or parenthesized expression) before
returning, leaving any subsequent infix operators for the outer Pratt loop.

### IdentCapture -> expect_ident

```rust
RDSyntaxItem::IdentCapture { param_name } => {
    let param = format_ident!("{}", param_name);
    // Generated code:
    let param_name = expect_ident(tokens, pos)?;
}
```

This consumes an `Ident` token and returns the identifier string.

### Binder -> expect_ident (with scope semantics)

```rust
RDSyntaxItem::Binder { param_name, binder_category } => {
    let param = format_ident!("{}", param_name);
    // Generated code:
    let param_name = expect_ident(tokens, pos)?;
    // Later used in constructor: Binder(get_or_create_var(param_name))
}
```

Binders are parsed as identifiers, but their semantic handling differs:
they are wrapped in `moniker::Binder` during constructor generation.

### Collection -> loop with separator

```rust
RDSyntaxItem::Collection { param_name, element_category, separator, kind } => {
    // Generated code (see Section 4 for full details):
    let mut param_name = CollectionType::new();
    loop {
        match parse_element(tokens, pos, 0) {
            Ok(elem) => {
                param_name.insert(elem);  // or .push(elem) for Vec
                if peek == separator { consume; } else { break; }
            }
            Err(_) => break,
        }
    }
}
```

---

## 3. Binder Rules and Scope Management

### Single Binder

A rule with `has_binder: true` has one binder and one body. The constructor
wraps them in a `moniker::Scope`:

```
Rule: PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc

Syntax items:
  Terminal("new"), Terminal("("), Binder("x", "Name"),
  Terminal(","), NonTerminal("Proc", "p"), Terminal(")")

Generated parse function:
  fn parse_pnew(tokens, pos) -> Result<Proc, String> {
      expect_token(tokens, pos, Token::KwNew, "new")?;
      expect_token(tokens, pos, Token::LParen, "(")?;
      let x = expect_ident(tokens, pos)?;          // binder
      expect_token(tokens, pos, Token::Comma, ",")?;
      let p = parse_Proc(tokens, pos, 0)?;          // body
      expect_token(tokens, pos, Token::RParen, ")")?;

      // Constructor with single binder:
      Ok(Proc::PNew(moniker::Scope::new(
          moniker::Binder(mettail_runtime::get_or_create_var(x)),
          Box::new(p),
      )))
  }
```

The `moniker::Scope::new(binder, body)` call creates a scope where the
binder variable is bound in the body. Moniker handles alpha-equivalence:
`new(x, x)` and `new(y, y)` are alpha-equivalent.

### Multi-Binder

A rule with `has_multi_binder: true` has a list of binders:

```
Rule: MLam . ^[xs].body:[Name* -> Proc] |- "^" "[" xs.*sep(",") "]" "." "{" body "}" : Proc

Generated constructor:
  let binders: Vec<moniker::Binder<FreeVar<String>>> = xs
      .into_iter()
      .map(|s| moniker::Binder(get_or_create_var(s)))
      .collect();
  Ok(Proc::MLamProc(moniker::Scope::new(
      binders,          // Vec<Binder<FreeVar<String>>>
      Box::new(body),   // Box<Proc>
  )))
```

Multi-binders are used for multi-lambda expressions (`^[x,y,z].{body}`)
and multi-input rules (`PInputs`).

---

## 4. Collection Rules

### Collection Kinds

```
+----------+--------------------------+------------------+----------------+
| Kind     | Rust type                | Insert method    | Semantics      |
+----------+--------------------------+------------------+----------------+
| HashBag  | hashbag::HashBag<T>      | .insert(elem)    | Multiset       |
|          |                          |                  | (duplicates OK)|
+----------+--------------------------+------------------+----------------+
| HashSet  | std::collections::       | .insert(elem)    | Set            |
|          |   HashSet<T>             |                  | (no duplicates)|
+----------+--------------------------+------------------+----------------+
| Vec      | Vec<T>                   | .push(elem)      | Ordered list   |
|          |                          |                  | (duplicates OK)|
+----------+--------------------------+------------------+----------------+
```

### Generated Collection Parsing

For a rule like `PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc`:

```rust
fn parse_ppar(tokens: &[(Token, Span)], pos: &mut usize) -> Result<Proc, String> {
    expect_token(tokens, pos, |t| matches!(t, Token::LBrace), "{")?;

    let mut ps = hashbag::HashBag::new();
    loop {
        match parse_Proc(tokens, pos, 0) {
            Ok(elem) => {
                ps.insert(elem);
                if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::Pipe)) {
                    *pos += 1;  // consume separator "|"
                } else {
                    break;
                }
            }
            Err(_) => break,
        }
    }

    expect_token(tokens, pos, |t| matches!(t, Token::RBrace), "}")?;

    Ok(Proc::PPar(ps))
}
```

### Empty Collection Handling

The loop uses `Err(_) => break` to handle empty collections gracefully.
If the first element parse fails (e.g., immediately seeing `}`), the loop
exits with an empty collection. This allows `{}` (no elements) and `{P}`
(one element, no separator) as well as `{P | Q | R}` (multiple elements).

---

## 5. Pattern Operations

Pattern operations are syntactic sugar in the `language!` macro that expand
into complex parsing logic.

### #sep (Separator)

`ps.*sep("|")` means "parse elements of `ps` separated by `|`".

This generates the collection loop shown in Section 4: parse element,
check for separator, consume if found, break if not.

### #map (Map)

`*zip(ns,xs).*map(|n,x| n "?" x)` means "parse pairs where each pair
consists of `n` and `x` separated by `?`".

Generated code:

```rust
// For each pair in the zip:
let mut ns = Vec::new();
let mut xs = Vec::new();
loop {
    // Parse the body of the map: n "?" x
    let n = parse_Name(tokens, pos, 0)?;
    expect_token(tokens, pos, |t| matches!(t, Token::Question), "?")?;
    let x = expect_ident(tokens, pos)?;

    ns.push(n);
    xs.push(x);

    // Check for separator
    if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::Comma)) {
        *pos += 1;
    } else {
        break;
    }
}
```

### #zip (Zip)

`*zip(ns, xs)` means "parse two parallel lists simultaneously". Combined
with `*map`, it produces parallel vectors where element `i` of `ns`
corresponds to element `i` of `xs`.

The `ZipMapSep` syntax item combines all three operations:

```rust
RDSyntaxItem::ZipMapSep {
    left_name: "ns",        // First parallel collection
    right_name: "xs",       // Second parallel collection
    left_category: "Name",  // Element type for left
    right_category: "Name", // Element type for right
    body_items: [...],      // Syntax pattern for each pair
    separator: ",",         // Separator between pairs
}
```

### #opt (Optional)

`#opt(...)` wraps a group of syntax items in a save/restore block:

```rust
// Generated code for #opt("else" body:Proc):
let saved_pos = *pos;
let opt_result = (|| -> Result<(), String> {
    expect_token(tokens, pos, |t| matches!(t, Token::KwElse), "else")?;
    let body = parse_Proc(tokens, pos, 0)?;
    // ... capture body ...
    Ok(())
})();
if opt_result.is_err() {
    *pos = saved_pos;  // Revert on failure
}
```

This uses an immediately-invoked closure to scope the `?` operator:
if any token expectation fails inside the closure, the error propagates
out of the closure, and the `if opt_result.is_err()` branch restores
the position.

### #var (Variable Reference)

Inside pattern operations, `#var(x)` refers to a previously parsed variable
or binder. This is resolved during constructor generation, not during
parsing---the parsed identifier string is later wrapped in
`mettail_runtime::get_or_create_var()`.

---

## 6. Lambda and Application Handlers

Lambda and application syntax is auto-generated for every language,
but only the **primary category** gets parse rules.

### Lambda: `^x.{body}` and `^[x,y,z].{body}`

The `generate_lambda_handlers` function produces:

```rust
fn parse_lambda(tokens: &[(Token, Span)], pos: &mut usize) -> Result<Cat, String> {
    expect_token(tokens, pos, |t| matches!(t, Token::Caret), "^")?;

    match peek_token(tokens, *pos) {
        // Multi-lambda: ^[x,y,z].{body}
        Some(Token::LBracket) => {
            *pos += 1;
            let mut binder_names = Vec::new();
            loop {
                let name = expect_ident(tokens, pos)?;
                binder_names.push(name);
                if peek_token(tokens, *pos) == Some(&Token::Comma) {
                    *pos += 1;
                } else {
                    break;
                }
            }
            expect_token(tokens, pos, Token::RBracket, "]")?;
            expect_token(tokens, pos, Token::Dot, ".")?;
            expect_token(tokens, pos, Token::LBrace, "{")?;
            let body = parse_Cat(tokens, pos, 0)?;
            expect_token(tokens, pos, Token::RBrace, "}")?;

            let binders = binder_names.into_iter()
                .map(|s| Binder(get_or_create_var(s)))
                .collect();
            Ok(Cat::MLamCat(Scope::new(binders, Box::new(body))))
        }

        // Single lambda: ^x.{body}
        Some(Token::Ident(_)) => {
            let binder_name = expect_ident(tokens, pos)?;
            expect_token(tokens, pos, Token::Dot, ".")?;
            expect_token(tokens, pos, Token::LBrace, "{")?;
            let body = parse_Cat(tokens, pos, 0)?;
            expect_token(tokens, pos, Token::RBrace, "}")?;

            Ok(Cat::LamCat(Scope::new(
                Binder(get_or_create_var(binder_name)),
                Box::new(body),
            )))
        }

        _ => Err("expected identifier or '[' after '^'".into()),
    }
}
```

### Application: `$type(lam, arg)` and `$$type(lam, args...)`

Application syntax is dispatched by the `$` prefix in the prefix handler:

```
$int(lam, arg)           -> single application, Int argument
$bool(lam, arg)          -> single application, Bool argument
$$int(lam, arg1, arg2)   -> multi application, Int arguments
$$bool(lam, arg1, arg2)  -> multi application, Bool arguments
```

Each variant is parsed by consuming the prefix token, then parsing the
lambda expression and argument(s) with their respective category parsers.

### Binder Type Inference

Both LALRPOP and PraTTaIL rely on `body.infer_var_type(&binder_name)` to
determine which lambda variant to construct. This method examines the AST
node `body` and returns the `VarCategory` of the first occurrence of the
binder variable:

```
^x.{x + 1}     -> infer_var_type("x") = Some(VarCategory::Int)
                -> construct LamInt(Scope::new(...))

^x.{x && true}  -> infer_var_type("x") = Some(VarCategory::Bool)
                -> construct LamBool(Scope::new(...))
```

---

## 7. Constructor Generation

The `generate_constructor` function examines the `Capture` list from
`generate_parse_body` and produces the appropriate AST construction:

### Unit Constructor (no captures)

```
Rule: PZero . |- "{}" : Proc
Captures: []
Generated: Ok(Proc::PZero)
```

### Simple Constructor (with captures)

```
Rule: PDrop . n:Name |- "*" "(" n ")" : Proc
Captures: [Capture { name: "n", kind: Simple }]
Generated: Ok(Proc::PDrop(n))

Note: For nonterminal captures in rules that produce Box-wrapped
fields, the Box::new() wrapping is handled at the call site, not
in the constructor generator.
```

### Binder Constructor

```
Rule: PNew . ^x.p |- "new" "(" x "," p ")" : Proc
Captures: [Capture { name: "x", kind: Binder },
           Capture { name: "p", kind: Simple }]
Generated:
  Ok(Proc::PNew(moniker::Scope::new(
      moniker::Binder(get_or_create_var(x)),
      Box::new(p),
  )))
```

### Multi-Binder Constructor

```
Rule: PInputs . ns:Vec(Name), ^[xs].p |- ...
Captures: [Capture { name: "ns", kind: Collection },
           Capture { name: "xs", kind: Binder },    // multi-binder
           Capture { name: "p",  kind: Simple }]
Generated:
  let binders: Vec<Binder<FreeVar<String>>> = xs
      .into_iter()
      .map(|s| Binder(get_or_create_var(s)))
      .collect();
  Ok(Proc::PInputs(ns, Scope::new(binders, Box::new(p))))
```

### Ident Capture Constructor

```
Rule with IdentCapture:
Captures: [Capture { name: "v", kind: Ident }]
Generated:
  Ok(Cat::CatVar(OrdVar(Var::Free(get_or_create_var(v)))))
```

Ident captures are wrapped in the `OrdVar(Var::Free(get_or_create_var(...)))`
chain that MeTTaIL uses for variable representation. The `get_or_create_var`
function ensures that the same variable name always produces the same
`FreeVar` (interning).

---

## 8. Worked Example: PInputs Rule

The most complex rule in RhoCalc is `PInputs`:

```
PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
|- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc
```

This means: parse a comma-separated list of `Name "?" Ident` pairs inside
parentheses, followed by `.` `{` body `}`.

### Syntax Item Decomposition

```
Items:
  1. Terminal("(")
  2. ZipMapSep {
       left_name: "ns",   left_category: "Name",
       right_name: "xs",  right_category: "Name",
       body_items: [NonTerminal("Name", "n"), Terminal("?"), IdentCapture("x")],
       separator: ","
     }
  3. Terminal(")")
  4. Terminal(".")
  5. Terminal("{")
  6. NonTerminal("Proc", "p")
  7. Terminal("}")
```

### Generated Parse Function

```rust
fn parse_pinputs(tokens: &[(Token, Span)], pos: &mut usize) -> Result<Proc, String> {
    // 1. Opening paren
    expect_token(tokens, pos, |t| matches!(t, Token::LParen), "(")?;

    // 2. Zip+Map+Sep: parse pairs of (Name "?" Ident)
    let mut ns = Vec::new();
    let mut xs = Vec::new();
    loop {
        // Parse one pair: Name "?" Ident
        let n = parse_Name(tokens, pos, 0)?;
        expect_token(tokens, pos, |t| matches!(t, Token::Question), "?")?;
        let x = expect_ident(tokens, pos)?;

        ns.push(n);
        xs.push(x);

        // Check for comma separator
        if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::Comma)) {
            *pos += 1;  // consume comma
        } else {
            break;
        }
    }

    // 3. Closing paren
    expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;

    // 4. Dot
    expect_token(tokens, pos, |t| matches!(t, Token::Dot), ".")?;

    // 5. Opening brace
    expect_token(tokens, pos, |t| matches!(t, Token::LBrace), "{")?;

    // 6. Body
    let p = parse_Proc(tokens, pos, 0)?;

    // 7. Closing brace
    expect_token(tokens, pos, |t| matches!(t, Token::RBrace), "}")?;

    // Constructor: multi-binder
    let binders: Vec<moniker::Binder<mettail_runtime::FreeVar<String>>> = xs
        .into_iter()
        .map(|s| moniker::Binder(mettail_runtime::get_or_create_var(s)))
        .collect();
    Ok(Proc::PInputs(ns, moniker::Scope::new(binders, Box::new(p))))
}
```

### Parsing Trace: `(n?x, m?y).{x | y}`

```
Input tokens: [LParen, Ident("n"), Question, Ident("x"), Comma,
               Ident("m"), Question, Ident("y"), RParen, Dot,
               LBrace, Ident("x"), Pipe, Ident("y"), RBrace, Eof]

1. consume LParen, pos=1

2. Loop iteration 1:
   parse_Name(pos=1): Ident("n") -> Name::NVar("n"), pos=2
   consume Question, pos=3
   expect_ident(pos=3): "x", pos=4
   ns = [NVar("n")], xs = ["x"]
   peek = Comma -> consume, pos=5

3. Loop iteration 2:
   parse_Name(pos=5): Ident("m") -> Name::NVar("m"), pos=6
   consume Question, pos=7
   expect_ident(pos=7): "y", pos=8
   ns = [NVar("n"), NVar("m")], xs = ["x", "y"]
   peek = RParen -> break

4. consume RParen, pos=9
5. consume Dot, pos=10
6. consume LBrace, pos=11

7. parse_Proc(pos=11):
   parse_Proc_prefix: Ident("x") -> PVar("x"), pos=12
   Pratt loop: peek = Pipe -> NOT an infix operator for Proc (wait,
     actually "|" is not the "+" operator, so infix_bp returns None)
   Actually, "|" is a separator, not an infix operator. The Pratt loop
   breaks, returning PVar("x").

   Hmm, but PPar uses "|" as a separator. The issue is that this body
   is parsed as a bare Proc expression, not as a PPar.

   In practice, the body `x | y` would need to be written as `{x | y}`
   to trigger the PPar rule. If written as `(n?x, m?y).{{x | y}}`, the
   outer braces are from PInputs and the inner braces trigger PPar.

   Let us re-trace with input `(n?x, m?y).{{x | y}}`:
   [LParen, Ident("n"), Question, Ident("x"), Comma,
    Ident("m"), Question, Ident("y"), RParen, Dot,
    LBrace, LBrace, Ident("x"), Pipe, Ident("y"), RBrace, RBrace, Eof]

   Steps 1-6 unchanged, pos=11.
   7. parse_Proc(pos=11):
      parse_Proc_prefix: LBrace -> parse_ppar():
        consume LBrace, pos=12
        Loop: parse_Proc(pos=12) -> PVar("x"), pos=13
              peek = Pipe -> consume separator, pos=14
              parse_Proc(pos=14) -> PVar("y"), pos=15
              peek = RBrace -> break
        ps = HashBag{PVar("x"), PVar("y")}
        consume RBrace, pos=16
        return PPar(HashBag{PVar("x"), PVar("y")})
      Pratt loop: peek = RBrace -> not infix -> break
      return PPar(...)

8. consume RBrace, pos=17

9. Constructor:
   binders = [Binder(FreeVar("x")), Binder(FreeVar("y"))]
   Proc::PInputs(
     [NVar("n"), NVar("m")],
     Scope::new(binders, Box::new(PPar(HashBag{PVar("x"), PVar("y")})))
   )
```

This demonstrates how the RD generator handles the most complex rule in
the RhoCalc grammar: multi-binder zip+map+sep with delimiters and a
recursive body parse.
