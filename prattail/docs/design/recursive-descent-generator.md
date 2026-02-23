# PraTTaIL: Recursive Descent Generator

**Date:** 2026-02-14 (updated 2026-02-17)

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
┌────────────────────┬──────────────────────────────────────────┬───────────────────┐
│ Construct          │ Example rule                             │ Key feature       │
├────────────────────┼──────────────────────────────────────────┼───────────────────┤
│ Delimited prefix   │ PDrop . n:Name |- "*" "(" n ")" : Proc  │ Terminal sequence │
│ Binder             │ PNew . ^x.p:[Name → Proc]               │ Scope::new()      │
│                    │   |- "new" "(" x "," p ")" : Proc       │                   │
│ Multi-binder       │ PInputs . ns:Vec(Name), ^[xs].p         │ Vec of binders    │
│ Collection         │ PPar . ps:HashBag(Proc)                  │ HashBag/Set/Vec   │
│                    │   |- "{" ps.*sep("|") "}" : Proc        │                   │
│ Zip+Map+Sep        │ PInputs . ... |- *zip(ns,xs).*map(...)  │ Parallel lists    │
│ Optional           │ #opt(...)                                │ Save/restore      │
│ Cross-category     │ NQuote . p:Proc |- "@" "(" p ")" : Name │ Different result  │
│ Unit (no params)   │ PZero . |- "{}" : Proc                  │ No captures       │
│ Keyword terminal   │ Err . |- "error" : Proc                 │ Fixed keyword     │
└────────────────────┴──────────────────────────────────────────┴───────────────────┘
```

### What the RD Generator Does NOT Handle

- **Infix rules** (handled by the Pratt loop).
- **Variable rules** (auto-generated in the prefix handler).
- **Literal rules** (auto-generated in the prefix handler).

---

## 2. Pattern Matching on Syntax Items

Each `RDSyntaxItem` variant produces a specific parsing action:

### Terminal → expect_token

```rust
RDSyntaxItem::Terminal(t) => {
    let variant = terminal_to_variant_name(t);   // e.g., "*" -> "Star"
    // Generated code:
    expect_token(tokens, pos, |t| matches!(t, Token::Star), "*")?;
}
```

This consumes one token and returns an error if the token does not match.

### NonTerminal → parse_Category

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

### IdentCapture → expect_ident

```rust
RDSyntaxItem::IdentCapture { param_name } => {
    let param = format_ident!("{}", param_name);
    // Generated code:
    let param_name = expect_ident(tokens, pos)?;
}
```

This consumes an `Ident` token and returns the identifier string.

### Binder → expect_ident (with scope semantics)

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

### Collection → loop with separator

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
Rule: PNew . ^x.p:[Name → Proc] |- "new" "(" x "," p ")" : Proc

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
Rule: MLam . ^[xs].body:[Name* → Proc] |- "^" "[" xs.*sep(",") "]" "." "{" body "}" : Proc

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
┌──────────┬──────────────────────────┬──────────────────┬────────────────┐
│ Kind     │ Rust type                │ Insert method    │ Semantics      │
├──────────┼──────────────────────────┼──────────────────┼────────────────┤
│ HashBag  │ hashbag::HashBag<T>      │ .insert(elem)    │ Multiset       │
│          │                          │                  │ (duplicates OK)│
├──────────┼──────────────────────────┼──────────────────┼────────────────┤
│ HashSet  │ std::collections::       │ .insert(elem)    │ Set            │
│          │   HashSet<T>             │                  │ (no duplicates)│
├──────────┼──────────────────────────┼──────────────────┼────────────────┤
│ Vec      │ Vec<T>                   │ .push(elem)      │ Ordered list   │
│          │                          │                  │ (duplicates OK)│
└──────────┴──────────────────────────┴──────────────────┴────────────────┘
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

The `write_lambda_handlers` function produces a `parse_lambda` function
that uses **inference-driven variant selection** — the `infer_var_type`
result determines which `Lam{Domain}` or `MLam{Domain}` variant to
construct:

```rust
fn parse_lambda(tokens: &[(Token, Span)], pos: &mut usize) -> Result<Cat, ParseError> {
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

            // Infer binder domain from first variable's usage in body
            let inferred = if let Some(name) = binder_names.first() {
                body.infer_var_type(name)
            } else {
                None
            };
            let binders = binder_names.into_iter()
                .map(|s| Binder(get_or_create_var(s)))
                .collect();
            let scope = Scope::new(binders, Box::new(body));
            // Select MLam variant based on inferred domain type
            Ok(match inferred {
                Some(InferredType::Base(VarCategory::Name)) => Cat::MLamName(scope),
                Some(InferredType::Base(VarCategory::Int))  => Cat::MLamInt(scope),
                // ... one arm per category in all_categories ...
                _ => Cat::MLamCat(scope)  // fallback to primary category default
            })
        }

        // Single lambda: ^x.{body}
        Some(Token::Ident(_)) => {
            let binder_name = expect_ident(tokens, pos)?;
            expect_token(tokens, pos, Token::Dot, ".")?;
            expect_token(tokens, pos, Token::LBrace, "{")?;
            let body = parse_Cat(tokens, pos, 0)?;
            expect_token(tokens, pos, Token::RBrace, "}")?;

            // Infer binder domain from variable usage in body
            let inferred = body.infer_var_type(&binder_name);
            let scope = Scope::new(
                Binder(get_or_create_var(binder_name)),
                Box::new(body),
            );
            // Select Lam variant based on inferred domain type
            Ok(match inferred {
                Some(InferredType::Base(VarCategory::Name)) => Cat::LamName(scope),
                Some(InferredType::Base(VarCategory::Int))  => Cat::LamInt(scope),
                // ... one arm per category in all_categories ...
                _ => Cat::LamCat(scope)  // fallback to primary category default
            })
        }

        _ => Err(ParseError::UnexpectedToken { ... }),
    }
}
```

The match arms are generated at compile time from `all_categories`,
ensuring every domain category has a corresponding arm. The `_ =>`
fallback covers `None` (variable not found in body) and higher-order
function types (`InferredType::Arrow` / `MultiArrow`).

### Application: `$type(lam, arg)` and `$$type(lam, args...)`

Application syntax is dispatched by the `$` prefix in the prefix handler:

```
$int(lam, arg)           → single application, Int argument
$bool(lam, arg)          → single application, Bool argument
$$int(lam, arg1, arg2)   → multi application, Int arguments
$$bool(lam, arg1, arg2)  → multi application, Bool arguments
```

Each variant is parsed by consuming the prefix token, then parsing the
lambda expression and argument(s) with their respective category parsers.

### Dollar Syntax Handlers: `write_dollar_handlers()`

The `write_dollar_handlers()` function generates parsing functions for
the dollar application syntax (`$cat(f,x)` and `$$cat(f,xs...)`):

```
write_dollar_handlers(buf: &mut String, primary_category: &str, all_categories: &[String])
    -> Vec<PrefixHandler>
```

For each domain category in `all_categories`, it generates two parse
functions:

1. **`parse_dollar_{dom}`** — Handles `$dom(f, x)` (single application):
   ```rust
   fn parse_dollar_proc(tokens: &[(Token, Span)], pos: &mut usize) -> Result<Proc, String> {
       // Token::DollarProc already consumed by prefix dispatch
       expect_token(tokens, pos, |t| matches!(t, Token::LParen), "(")?;
       let f = parse_Proc(tokens, pos, 0)?;    // lambda (always primary category)
       expect_token(tokens, pos, |t| matches!(t, Token::Comma), ",")?;
       let x = parse_Proc(tokens, pos, 0)?;    // argument (domain category)
       expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
       Ok(Proc::ApplyProc(Box::new(f), Box::new(x)))
   }
   ```

2. **`parse_ddollar_{dom}`** — Handles `$$dom(f, x1, x2, ...)` (multi-application):
   ```rust
   fn parse_ddollar_proc(tokens: &[(Token, Span)], pos: &mut usize) -> Result<Proc, String> {
       // Token::DdollarProcLp already consumed (includes opening paren)
       let f = parse_Proc(tokens, pos, 0)?;    // lambda (always primary category)
       let mut args = Vec::new();
       while peek_token(tokens, *pos) == Some(&Token::Comma) {
           *pos += 1;  // consume comma
           let arg = parse_Proc(tokens, pos, 0)?;
           args.push(arg);
       }
       expect_token(tokens, pos, |t| matches!(t, Token::RParen), ")")?;
       Ok(Proc::MApplyProc(Box::new(f), args))
   }
   ```

**Token variant naming:**

| Dollar syntax | Token variant          | Notes                              |
|---------------|------------------------|------------------------------------|
| `$proc`       | `Token::DollarProc`    | Followed by `(` parsed separately  |
| `$name`       | `Token::DollarName`    | Followed by `(` parsed separately  |
| `$int`        | `Token::DollarInt`     | Followed by `(` parsed separately  |
| `$$proc(`     | `Token::DdollarProcLp` | Opening paren is part of the token |
| `$$name(`     | `Token::DdollarNameLp` | Opening paren is part of the token |
| `$$int(`      | `Token::DdollarIntLp`  | Opening paren is part of the token |

Note that `$$cat(` is a **single token** — the opening parenthesis is
consumed as part of the token, not parsed separately. This avoids
ambiguity with the `$` prefix.

The function returns a `Vec<PrefixHandler>` with dispatch entries for
both single and multi-application forms, which are wired into the Pratt
prefix handler for the primary category.

### Binder Type Inference

PraTTaIL uses `body.infer_var_type(&binder_name)` to determine which
lambda variant to construct. This method examines the AST node `body`
and returns an `Option<InferredType>` indicating how the binder variable
is used:

```
^x.{x + 1}          → infer_var_type("x") = Some(Base(VarCategory::Int))
                    → match selects LamInt(Scope::new(...))

^x.{x && true}      → infer_var_type("x") = Some(Base(VarCategory::Bool))
                    → match selects LamBool(Scope::new(...))

^loc.{loc!(init)}   → infer_var_type("loc") = Some(Base(VarCategory::Name))
                    → match selects LamName(Scope::new(...))

^f.{f}              → infer_var_type("f") = Some(Base(VarCategory::Proc))
                    → match selects LamProc(Scope::new(...))
```

**Why this matters for beta-reduction:** The normalizer's
`ApplyDom(lam, arg)` arm specifically matches `LamDom(scope)`. If the
lambda variant doesn't match the application variant (e.g.,
`ApplyName(LamProc(...), ...)` instead of `ApplyName(LamName(...), ...)`),
the beta-reduction falls through to the `_ =>` arm and returns the
un-reduced term. Inference-driven variant selection ensures the lambda
variant matches the dollar syntax's domain.

**Implementation in `write_lambda_handlers`:** Before the `write!` call
that generates `parse_lambda`, match arm strings are pre-built from
`all_categories`:

```rust
let lam_match_arms: String = all_categories.iter().map(|dom| {
    format!(
        "Some(InferredType::Base(VarCategory::{})) => {}::Lam{}(scope), ",
        dom, cat, dom
    )
}).collect::<Vec<_>>().join("");
```

These are interpolated into the format string as `{lam_match_arms}`,
producing one match arm per category. The same pattern is used for
`mlam_match_arms` in the multi-lambda case.

**Trampoline parser:** The same inference-driven selection is applied in
the trampoline parser's unwind handlers (`LambdaBody_Single` and
`LambdaBody_Multi` frame variants in `trampoline.rs`), ensuring
consistent behavior between the recursive-descent and trampoline
code paths.

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
PInputs . ns:Vec(Name), ^[xs].p:[Name* → Proc]
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
   parse_Name(pos=1): Ident("n") → Name::NVar("n"), pos=2
   consume Question, pos=3
   expect_ident(pos=3): "x", pos=4
   ns = [NVar("n")], xs = ["x"]
   peek = Comma → consume, pos=5

3. Loop iteration 2:
   parse_Name(pos=5): Ident("m") → Name::NVar("m"), pos=6
   consume Question, pos=7
   expect_ident(pos=7): "y", pos=8
   ns = [NVar("n"), NVar("m")], xs = ["x", "y"]
   peek = RParen → break

4. consume RParen, pos=9
5. consume Dot, pos=10
6. consume LBrace, pos=11

7. parse_Proc(pos=11):
   parse_Proc_prefix: Ident("x") → PVar("x"), pos=12
   Pratt loop: peek = Pipe → NOT an infix operator for Proc (wait,
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
      parse_Proc_prefix: LBrace → parse_ppar():
        consume LBrace, pos=12
        Loop: parse_Proc(pos=12) → PVar("x"), pos=13
              peek = Pipe → consume separator, pos=14
              parse_Proc(pos=14) → PVar("y"), pos=15
              peek = RBrace → break
        ps = HashBag{PVar("x"), PVar("y")}
        consume RBrace, pos=16
        return PPar(HashBag{PVar("x"), PVar("y")})
      Pratt loop: peek = RBrace → not infix → break
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

---

## 8. Error Propagation in RD Handlers

RD handlers use the `?` operator for fail-fast error propagation. When any
sub-parse fails (e.g., a missing delimiter, an unexpected token, or a
failed recursive parse), the error propagates immediately to the caller
without partial recovery.

This design is correct for structural constructs because:

1. **Mandatory delimiters:** Structural rules like `( expr )` or `{ body }`
   require every delimiter to be present. A missing `)` means the construct
   is malformed — there is no meaningful partial result to return.

2. **Deterministic structure:** Unlike infix expressions (where the Pratt loop
   can stop at any point and return a valid partial expression), structural
   rules have a fixed sequence of tokens. Partial execution produces an
   invalid state.

3. **Recovery at a higher level:** Error recovery is handled by the separate
   `_recovering` parser variants, which wrap the fail-fast RD handlers and
   catch their errors. This keeps the fast path (no errors) at zero overhead
   while still enabling recovery when needed.
