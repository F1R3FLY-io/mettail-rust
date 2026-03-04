# PraTTaIL Grammar Features Reference

**Complete reference for all grammar DSL features in the `language!` macro.**

---

## Table of Contents

1. [Language Declaration](#1-language-declaration)
   1. [Language Composition Clauses](#11-language-composition-clauses)
   2. [Language Fragments](#12-language-fragments)
   3. [Composed Languages](#13-composed-languages)
2. [Type Declarations](#2-type-declarations)
3. [Term Rules Overview](#3-term-rules-overview)
4. [Prefix Rules](#4-prefix-rules)
5. [Infix Rules](#5-infix-rules)
   1. [Postfix Operators](#51-postfix-operators)
   2. [Mixfix (N-ary) Operators](#52-mixfix-n-ary-operators)
6. [Structural Rules](#6-structural-rules)
7. [Binder Rules](#7-binder-rules)
8. [Collection Rules](#8-collection-rules)
9. [Pattern Operations](#9-pattern-operations)
10. [Cross-Category Rules](#10-cross-category-rules)
11. [Cast Rules](#11-cast-rules)
12. [Lambda and Application](#12-lambda-and-application)
13. [HOL Native Evaluation](#13-hol-native-evaluation)
14. [Equations and Rewrites](#14-equations-and-rewrites)

---

## 1. Language Declaration

```rust
language! {
    name: LanguageName,

    types { ... },
    terms { ... },
    equations { ... },
    rewrites { ... },
    logic { ... },           // Optional: Ascent Datalog rules
}
```

The `name` field determines the name used in generated code comments and diagnostic
messages. It must be a valid Rust identifier.

### 1.1 Language Composition Clauses

PraTTaIL supports three composition clauses that allow languages to inherit, import,
or mix in definitions from other languages and fragments. These clauses appear
immediately after `name:` and before the `types` block.

#### `extends: [Base1, Base2]` -- Full Inheritance

Full inheritance merges **all** sections from the base language(s): types, terms,
equations, rewrites, and logic. Duplicate labels trigger a compile-time error
(`DuplicateStrategy::Error`), so extending languages must not redeclare any rule
already present in the base.

```rust
language! {
    name: ExtMath,
    extends: [BaseMath],
    types {
    },  // inherits BaseMath's types
    terms {
    },  // inherits BaseMath's terms + equations + rewrites + logic
    equations {
    },
    rewrites {
    },
}
```

In this example, `ExtMath` inherits every type, term rule, equation, and rewrite rule
from `BaseMath`. Additional types, terms, equations, and rewrites can be declared in
the respective blocks alongside the inherited ones.

#### `includes: [Calc, BoolLogic]` -- Grammar-Only Import

Grammar-only import merges **types and terms only** from the referenced language(s).
Equations, rewrites, and logic blocks are NOT imported -- the including language must
provide its own. Duplicate labels are resolved by override
(`DuplicateStrategy::Override`), allowing the including language to shadow imported
rules by redeclaring them with the same label.

```rust
language! {
    name: ImportedMath,
    includes: [BaseMath],
    types {
    },
    terms {
        Div . a:Num, b:Num |- a "/" b : Num ![a / b] fold;
    },
    equations {
    },
    rewrites {
        // Must provide rewrites for ALL rules (imported + local)
        AddCongL . | S ~> T |- (Add S R) ~> (Add T R);
        AddCongR . | S ~> T |- (Add L S) ~> (Add L T);
        SubCongL . | S ~> T |- (Sub S R) ~> (Sub T R);
        SubCongR . | S ~> T |- (Sub L S) ~> (Sub L T);
        DivCongL . | S ~> T |- (Div S R) ~> (Div T R);
        DivCongR . | S ~> T |- (Div L S) ~> (Div L T);
    },
}
```

Here, `ImportedMath` imports the `Num` type and `Add`/`Sub` term rules from
`BaseMath`, adds its own `Div` rule, and provides a complete set of rewrites
covering all three rules.

#### `mixins: [ArithOps, BoolOps]` -- Fragment Import

Fragment import pulls definitions from `language_fragment!` declarations (see
Section 1.2). Like `includes:`, it merges **types and terms only**, using
`DuplicateStrategy::Override`. The key difference is the source: `mixins:` imports
from fragments (which generate no code on their own), while `includes:` imports from
full `language!` definitions.

```rust
language! {
    name: MixedMath,
    mixins: [IntArithFragment, BoolOpsFragment],
    types {
    },
    terms {
        Neg . a:Int |- "-" a : Int ![(-a)] fold;
    },
    equations {
    },
    rewrites {
        AddIntCongL . | S ~> T |- (AddInt S R) ~> (AddInt T R);
        AddIntCongR . | S ~> T |- (AddInt L S) ~> (AddInt L T);
        // ... rewrites for all imported + local rules ...
    },
}
```

#### Composition Clause Comparison

| Clause     | Merges Types | Merges Terms | Merges Equations | Merges Rewrites | Merges Logic | On Duplicate       |
|------------|:------------:|:------------:|:----------------:|:---------------:|:------------:|--------------------|
| `extends`  | Yes          | Yes          | Yes              | Yes             | Yes          | Error (no overlap) |
| `includes` | Yes          | Yes          | No               | No              | No           | Override (shadow)  |
| `mixins`   | Yes          | Yes          | No               | No              | No           | Override (shadow)  |

### 1.2 Language Fragments

Language fragments define reusable grammar building blocks that exist only in the
macro registry. They generate **no code** -- no parser, no AST enum, no Ascent
program. They serve purely as libraries of type and term definitions that can be
pulled into full languages via `mixins: [...]`.

#### Syntax

```rust
use mettail_macros::language_fragment;

language_fragment! {
    name: FragmentName,
    types {
        // Type declarations (same syntax as language! types)
    },
    terms {
        // Term rules (same syntax as language! terms)
    }
}
```

#### Example

```rust
language_fragment! {
    name: IntArithFragment,
    types {
        ![i32] as Int
    },
    terms {
        AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        SubInt . a:Int, b:Int |- a "-" b : Int ![a - b] fold;
        MulInt . a:Int, b:Int |- a "*" b : Int ![a * b] fold;
    }
}

language_fragment! {
    name: BoolOpsFragment,
    types {
        ![bool] as Bool
    },
    terms {
        And . a:Bool, b:Bool |- a "and" b : Bool ![a && b] step;
        Or  . a:Bool, b:Bool |- a "or" b  : Bool ![a || b] step;
        Not . a:Bool |- "not" a : Bool ![!a] step;
    }
}
```

These fragments can then be consumed by any number of languages:

```rust
language! {
    name: MixedMath,
    mixins: [IntArithFragment, BoolOpsFragment],
    // ...
}
```

### 1.3 Composed Languages

The `compose_languages!` macro creates a **delegation wrapper** that combines
multiple independently-defined languages into a single unified language. Unlike
`extends` or `includes`, composition does not merge grammars -- each sub-language
retains its own parser, AST, and Ascent program. The composed language delegates
parsing to each sub-language in declaration order, returning the first successful
parse result.

#### Syntax

```rust
use mettail_macros::compose_languages;

compose_languages! {
    name: ComposedName,
    languages: [crate::path::to::Language1, crate::path::to::Language2],
}
```

#### Generated Types

The macro generates:

- `{Name}TermInner` -- an enum wrapping each sub-language's term type
- `{Name}Term` -- a wrapper type implementing the `Term` trait
- `{Name}Env` -- a combined environment type
- `{Name}Language` -- a struct implementing the `Language` trait via delegation

#### Parsing Behavior

The composed language tries each sub-language's parser in declaration order. The
first sub-language that successfully parses the input wins. If all sub-languages
fail, the error from the last attempt is returned.

#### Example

```rust
compose_languages! {
    name: CalcLambda,
    languages: [crate::calculator::Calculator, crate::lambda::Lambda],
}
```

This creates `CalcLambda` which can parse both calculator expressions (`1 + 2 * 3`)
and lambda expressions (`^x.{x}`), delegating to the `Calculator` parser first and
falling back to `Lambda` if that fails.

---

## 2. Type Declarations

Types define the **categories** (sorts) of the language. Each category becomes a Rust
enum in the generated AST.

### Syntax

```
types {
    CategoryName                     // Abstract category (no native backing)
    ![RustType] as CategoryName      // Native-backed category
}
```

### Examples

```rust
types {
    Proc                    // Abstract process type
    Name                    // Abstract name type
    ![i64] as Int           // Integers backed by i64
    ![bool] as Bool         // Booleans backed by bool
    ![str] as Str           // Strings backed by str
}
```

### Primary Category

The **first** category declared is the **primary** category. This affects:

- **Variable syntax**: the primary category gets bare identifiers (`x`, `foo`).
  Non-primary categories require type prefixes (`bool:x`, `str:s`).
- **Lambda ownership**: lambda parsing rules are generated only for the primary
  category's parser (to avoid ambiguity).
- **Default dispatch**: the primary category is the default entry point for parsing.

### Supported Native Types

| Rust Type                                    | Lexer Token         | Literal Pattern           |
|----------------------------------------------|---------------------|---------------------------|
| `i32`, `i64`, `u32`, `u64`, `isize`, `usize` | `Integer(i64)`      | `[0-9]+`                  |
| `f32`, `f64`                                 | `Float(f64)`        | `[0-9]+\.[0-9]+`          |
| `bool`                                       | `Boolean(bool)`     | `true` / `false` keywords |
| `str`, `String`                              | `StringLit(String)` | `"[^"]*"`                 |

---

## 3. Term Rules Overview

Term rules define the constructors and concrete syntax of the language. Each rule
has the general form:

```
Label . params |- syntax_pattern : ResultCategory [optional_annotations];
```

### Parts of a Rule

```
Add . a:Int, b:Int |- a "+" b : Int ![a + b] step;
^^^   ^^^^^^^^^^^^    ^^^^^^^^   ^^^  ^^^^^^^  ^^^^
 |         |              |       |      |       |
Label   Parameters    Syntax   Result  HOL    Eval
                      Pattern  Cat.    code   mode
```

**Label**: Constructor name in the generated AST enum (e.g., `Int::Add`).

**Parameters**: Typed parameter declarations. Each `name:Type` pair declares a
sub-expression that the parser will capture.

**Syntax Pattern**: The concrete syntax, using terminals (quoted strings) and
parameter names to describe how the rule looks in source text.

**Result Category**: The type/category this rule produces.

**HOL code** (optional): Native Rust evaluation expression in `![...]`.

**Eval mode** (optional): `step` (single-step) or `fold` (recursive fold).

---

## 4. Prefix Rules

Prefix rules start with a terminal token followed by sub-expressions.

### Unit (Nullary) Rules

```rust
PZero . |- "{}" : Proc;               // Matches literal "{}"
Err . |- "error" : Proc;              // Matches keyword "error"
```

Generated AST:
```rust
enum Proc {
    PZero,                             // No arguments
    Err,                               // No arguments
}
```

### Structural Prefix Rules

```rust
PDrop . n:Name |- "*" "(" n ")" : Proc;
```

The first terminal token triggers the dispatch: when the parser sees `Token::Star`
(for `*`), it calls the corresponding RD handler. Rules with delimiters or multiple
terminals always use `bp=0` for their recursive calls, capturing the full expression.

Generated parse function for `PDrop`:
```
fn parse_pdrop(tokens, pos):
    expect "*"
    expect "("
    let n = parse_Name(tokens, pos, 0)
    expect ")"
    return Proc::PDrop(Box::new(n))
```

### Unary Prefix Operators

Unary prefix operators have exactly the syntax pattern `Terminal(op) NonTerminal(same_category)`,
where the operand is the **same category** as the result. These operators bind tighter than all
infix operators, capturing only their immediate operand.

```rust
Neg . a:Int |- "-" a : Int ![(-a)] fold;
Not . a:Bool |- "not" a : Bool ![{ match a { true => false, false => true } }] step;
```

**Binding power**: Unary prefix operators receive `right_bp = max_infix_bp + 2` for their
category. This ensures they bind tighter than any infix operator.

**Behavioral examples**:

| Expression          | Parse tree                                 | Evaluation |
|---------------------|--------------------------------------------|------------|
| `-3`                | `Neg(NumLit(3))`                           | `-3`       |
| `-3 + 5`            | `Add(Neg(NumLit(3)), NumLit(5))`           | `2`        |
| `-3 * 5`            | `Mul(Neg(NumLit(3)), NumLit(5))`           | `-15`      |
| `--3`               | `Neg(Neg(NumLit(3)))`                      | `3`        |
| `3 - -5`            | `Sub(NumLit(3), Neg(NumLit(5)))`           | `8`        |
| `not true && false` | `Comp(Not(BoolLit(true)), BoolLit(false))` | `false`    |

**Shared tokens**: When a token is used for both a unary prefix and an infix operator
(e.g., `-` for both `Neg` and `Sub`), Pratt parsing naturally resolves the ambiguity:
- In **prefix position** (start of expression or after an operator): the token triggers
  the RD handler for the unary prefix rule.
- In **infix position** (after a complete sub-expression): the token triggers the
  Pratt infix loop for the binary rule.

**Classification criteria**: A rule is classified as unary prefix when:
1. Its syntax has exactly 2 items: `[Terminal, NonTerminal]`
2. The nonterminal's category matches the result category
3. The rule is not cross-category (operand and result are the same sort)

Rules that do **not** qualify:
- `PDrop . n:Name |- "*" "(" n ")" : Proc` -- has delimiters (3+ syntax items)
- `Len . s:Str |- "|" s "|" : Int` -- cross-category (Str operand, Int result)
- `NQuote . p:Proc |- "@" "(" p ")" : Name` -- has delimiters and is cross-category

---

## 5. Infix Rules

Infix rules have the form `a OP b` where `a` and `b` are of the **same category**
as the result.

### Syntax

```rust
Add . a:Int, b:Int |- a "+" b : Int;
Mul . a:Int, b:Int |- a "*" b : Int;
PPar . a:Proc, b:Proc |- a "|" b : Proc;
```

### Classification Criteria

A rule is classified as infix when:
1. It has exactly 3 syntax items: `[NonTerminal, Terminal, NonTerminal]`
2. Both nonterminals have the same category as the result
3. The rule is not a cross-category rule

### Precedence

Precedence is determined by **declaration order** within a category:
- First-declared infix operator gets the **lowest** precedence
- Each subsequent operator gets higher precedence

```rust
terms {
    Add . a:Int, b:Int |- a "+" b : Int;    // Precedence 1 (lowest)
    Sub . a:Int, b:Int |- a "-" b : Int;    // Precedence 2
    Mul . a:Int, b:Int |- a "*" b : Int;    // Precedence 3
    Pow . a:Int, b:Int |- a "^" b : Int;    // Precedence 4 (highest)
}
```

### Associativity

By default, all infix operators are **left-associative**:
- `1 + 2 + 3` parses as `(1 + 2) + 3`

Right-associativity is specified with the `right` keyword at the end of the rule,
after the eval mode annotation (if present):

```rust
Pow . a:Int, b:Int |- a "^" b : Int right;
Pow . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] step right;
```

With right-associativity:
- `1 ^ 2 ^ 3` parses as `1 ^ (2 ^ 3)` (i.e., `Pow(1, Pow(2, 3))`)

The `right` keyword can be combined with eval mode and `prefix(N)` annotations:

```
Label . params |- syntax : Cat ![code] mode right prefix(N);
```

#### Binding Power Encoding

The binding power (BP) pairs encode associativity:
- Left-associative: `(2n, 2n+1)` -- the left side binds tighter, so the right
  operand recurses at a higher minimum BP than the left saw
- Right-associative: `(2n+1, 2n)` -- the right side binds tighter, so the right
  operand recurses at the same level as the left, allowing right nesting

#### Parsing Example

Given `1 ^ 2 ^ 3` with `Pow` declared as right-associative:

1. Parse `1` as a literal
2. See `^` with BP `(2n+1, 2n)` -- left_bp = 2n+1
3. The current min_bp (0) < left_bp (2n+1), so consume `^`
4. Recurse for right operand with min_bp = 2n (right_bp)
5. Parse `2`, see another `^` with left_bp = 2n+1
6. Current min_bp (2n) < left_bp (2n+1), so consume `^`
7. Recurse again, parse `3`
8. Result: `Pow(1, Pow(2, 3))`

### 5.1 Postfix Operators

Postfix operators have exactly the syntax pattern `NonTerminal(same_category) Terminal`,
where the operand category matches the result category. They bind tighter than both
infix and prefix operators.

#### Syntax

```rust
Fact . a:Int |- a "!" : Int;
```

This parses expressions like `3!`, producing `Int::Fact(Box::new(NumLit(3)))`.

#### Classification Criteria

A rule is classified as postfix when:
1. Its syntax has exactly 2 items: `[NonTerminal, Terminal]`
2. The nonterminal's category matches the result category

Note that postfix classification implies infix classification internally -- postfix
operators are handled in the Pratt infix loop, consuming the trailing terminal after
the left operand has been parsed.

#### Binding Power Assignment

Postfix operators use a **two-pass BP analysis** to ensure they bind tighter than
all other operator types:

1. **First pass**: All non-postfix operators (regular infix and mixfix) are assigned
   BPs starting at `(2, 3)`, incrementing by 2 per operator
2. **Gap**: Unary prefix operators receive `max_non_postfix_bp + 2`
3. **Second pass**: Postfix operators start at `max_non_postfix_bp + 4`, incrementing
   by 2 for each additional postfix operator

This produces the binding hierarchy: **infix < prefix < postfix**.

#### Parsing Examples

| Expression | Parse Tree                          | Notes                                     |
|------------|-------------------------------------|--------------------------------------------|
| `3!`       | `Fact(NumLit(3))`                   | Simple postfix application                 |
| `3! + 5`   | `Add(Fact(NumLit(3)), NumLit(5))`   | Postfix binds tighter than infix `+`       |
| `-3!`      | `Neg(Fact(NumLit(3)))`              | Postfix binds tighter than prefix `-`      |
| `3! * 2!`  | `Mul(Fact(NumLit(3)), Fact(NumLit(2)))` | Both operands get postfix applied first |

### 5.2 Mixfix (N-ary) Operators

Mixfix operators have 3 or more syntax items with at least 2 terminals and at least
2 nonterminals. The classic example is the ternary conditional `a ? b : c`.

#### Syntax

```rust
Tern . cond:Int, a:Int, b:Int |- cond "?" a ":" b : Int;
```

The first terminal (`"?"`) is the **trigger terminal** -- it is the operator token
matched in the Pratt infix loop. Subsequent terminal-nonterminal pairs are stored as
`MixfixPart` structures:

```
cond "?" a ":" b
     ^^^       -- trigger terminal
         ^ ^^^ -- MixfixPart { operand: "a", separator: Some(":") }
              ^ -- MixfixPart { operand: "b", separator: None }
```

#### Precedence

Mixfix operators are assigned BPs alongside regular infix operators in declaration
order. They receive the **lowest precedence** by default (if declared before infix
operators). Middle operands (between the trigger and the last terminal) are parsed
at `min_bp = 0`, resetting precedence like grouping parentheses. The final operand
is parsed at the operator's `right_bp`.

#### Parsing Example

Given `x > 0 ? x : -x` with `Tern` as a mixfix operator and `Gt` as a comparison:

1. Parse `x > 0` as `Gt(Var("x"), NumLit(0))` (higher-precedence comparison)
2. See `?` trigger -- matches `Tern` mixfix with its left_bp
3. Parse middle operand `x` at `min_bp = 0` (full reset)
4. Expect `:` separator
5. Parse final operand `-x` at `right_bp`
6. Result: `Tern(Gt(Var("x"), NumLit(0)), Var("x"), Neg(Var("x")))`

---

## 6. Structural Rules

Structural rules have complex multi-token syntax with delimiters, multiple
sub-expressions, and mixed terminals.

### Examples

```rust
// Output: name "!" "(" process ")"
POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc;

// Quote: "@" "(" process ")"
NQuote . p:Proc |- "@" "(" p ")" : Name;

// Parallel composition with delimiter: "{" p "|" q "}"
PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
```

Each structural rule generates a dedicated recursive descent parse function
(`parse_poutput`, `parse_nquote`, etc.) with a match arm in the category's
prefix handler.

---

## 7. Binder Rules

Binder rules introduce bound variables using the `^` syntax.

### Single Binder

```
^x.body
```

The grammar DSL uses `^[xs].p:[Type -> Type]` notation:

```rust
// For each name, bind a variable in the continuation process
PInput . n:Name, ^x.p:[Name -> Proc]
|- n "?" "(" x ")" "." "{" p "}" : Proc;
```

This generates code that creates a `moniker::Scope` with a single `Binder`:

```rust
Proc::PInput(
    Box::new(n),
    Scope::new(
        Binder(get_or_create_var(x)),
        Box::new(p),
    ),
)
```

### Multi-Binder

```
^[x,y,z].body
```

```rust
PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
|- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc;
```

Multi-binders create a `Scope` with a `Vec<Binder>`:

```rust
Proc::PInputs(
    Scope::new(
        binders,          // Vec<Binder<FreeVar<String>>>
        Box::new(p),
    ),
)
```

### Binder Type Annotations

The type annotation `[Name -> Proc]` or `[Name* -> Proc]` specifies:
- The binder variable category (`Name`)
- The body category (`Proc`)
- `*` indicates multiple binders (multi-binder)

---

## 8. Collection Rules

Collections parse repeated elements into aggregate data structures.

### Supported Collection Types

| Type           | Rust Type               | Insert Method | Properties                   |
|----------------|-------------------------|---------------|------------------------------|
| `HashBag(Cat)` | `hashbag::HashBag<Cat>` | `.insert()`   | Multiset (allows duplicates) |
| `HashSet(Cat)` | `HashSet<Cat>`          | `.insert()`   | Set (no duplicates)          |
| `Vec(Cat)`     | `Vec<Cat>`              | `.push()`     | Ordered sequence             |

### Usage

```rust
// Parallel composition as a bag of processes
PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;

// Input channels as a vector of names
PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
|- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc;
```

The generated parser creates the collection, then loops:
1. Parse one element
2. Check for separator token
3. If separator found: consume it, continue loop
4. If no separator: break

---

## 9. Pattern Operations

Pattern operations (`#` or `*` prefixed) control how collections are parsed.
The Sep/Map/Zip system uses composable primitives that can be combined freely,
replacing the earlier monolithic `ZipMapSep` approach.

### `*sep(separator)` -- Separated Lists

Repeats a body pattern with a separator between repetitions. Nullable (0 iterations
are valid). The body can be any `SyntaxItemSpec`: a `NonTerminal` (simple separated
list), a `Map` (structured separated list with a single accumulator), or a
`Zip { body: Map { .. } }` (dual-accumulator structured list).

```rust
PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
//                                    ^^^
//  Parse Proc elements separated by "|" into a HashBag
```

Input: `{ P1 | P2 | P3 }`
Result: `HashBag { P1, P2, P3 }`

#### Standalone Sep with NonTerminal

The simplest form: a separated list of a single nonterminal category.

```rust
// Separate process list by pipe
PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
```

#### Sep with Map

A separated list where each element is a structured multi-item pattern.

```rust
// Each element is a name followed by "!" and a process
Outputs . ns:Vec(Name), qs:Vec(Proc)
|- ns.*map(|n| n "!" q).*sep(",") : Proc;
```

### `*zip(a, b)` -- Dual-Accumulator Collection

Pairs elements from two parallel sequences. Each iteration produces values for
both the left and right accumulators in lockstep.

```rust
PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
|- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc;
```

This parses pairs like `n1 ? x1 , n2 ? x2 , ...` and collects:
- `ns` = `[n1, n2, ...]` (names)
- `xs` = `[x1, x2, ...]` (binder variables)

#### Standalone Zip

When used without `Sep`, `Zip` collects a dual-accumulator sequence without
separators.

### `*map(|params| body)` -- Element-Level Pattern

Applies a pattern template to each element (or each pair from `*zip`).

```rust
*zip(ns,xs).*map(|n,x| n "?" x).*sep(",")
//                      ^^^^^^^^
//  Each pair parses as: Name "?" Ident
```

The body `n "?" x` means: for each iteration, parse a `Name`, expect `?`, then
parse an identifier (which becomes a binder variable).

#### Standalone Map

When used without `Sep` or `Zip`, `Map` defines a structured inline sequence of
items forming one logical element.

### `#opt(pattern)` / `*opt(pattern)` -- Optional Sub-Pattern

Makes a sub-pattern optional. If parsing fails, the position is restored.

```rust
// Optional type annotation
Rule . x:Ident, #opt(":" t:Type), body:Expr
|- x #opt(":" t) "=" body : Decl;
```

Generated code:
```rust
let saved_pos = *pos;
let opt_result = (|| -> Result<(), String> {
    // try parsing the optional group
    Ok(())
})();
if opt_result.is_err() {
    *pos = saved_pos;  // restore on failure
}
```

### `#var` -- Variable Reference

References a variable position in the pattern (for BNFC-style patterns).
Variables are always identifiers.

### Composition Table

The following table shows which combinations of outer and inner pattern operations
are valid:

| Outer | Inner        | Valid | Example                                         |
|-------|--------------|:-----:|--------------------------------------------------|
| Sep   | NonTerminal  | Yes   | `ps.*sep("\|")`                                  |
| Sep   | Map          | Yes   | `ns.*map(\|n\| n "!" q).*sep(",")`               |
| Sep   | Zip          | Yes   | `*zip(ns,xs).*sep(",")`                          |
| Sep   | Zip(Map)     | Yes   | `*zip(ns,xs).*map(\|n,x\| n "?" x).*sep(",")` |
| Zip   | Map          | Yes   | `*zip(ns,xs).*map(\|n,x\| n "?" x)`             |
| Map   | (standalone) | Yes   | Element-level structured pattern                 |
| Zip   | (standalone) | Yes   | Dual-accumulator collection without separator    |

---

## 10. Cross-Category Rules

Cross-category rules take operands from one category and produce results in another.

### Syntax

```rust
// Int operands, Bool result
Eq . a:Int, b:Int |- a "==" b : Bool;

// Str operands, Bool result
EqStr . a:Str, b:Str |- a "==" b : Bool;

// Str operand, Int result
Len . s:Str |- "|" s "|" : Int;
```

### How They Differ from Infix Rules

Cross-category rules are **not** placed in the Pratt infix loop because their
operand category differs from their result category. Instead, they are handled by
the cross-category dispatch system (`dispatch.rs`).

### FIRST Set Dispatch

PraTTaIL uses FIRST set analysis to optimize cross-category dispatch:

```
FIRST(Int)  = {Integer, Ident}
FIRST(Bool) = {KwTrue, KwFalse, KwNot, Ident}

For "Eq . a:Int, b:Int |- a '==' b : Bool":
  Token "Integer" is unique to Int -> deterministic cross-category path
  Token "Ident" is in both -> needs backtracking
```

For unambiguous tokens, the generated code directly parses the source category:
```rust
Token::Integer(_) => {
    let left = parse_Int(tokens, pos, 0)?;
    expect_token(tokens, pos, |t| matches!(t, Token::EqEq), "==")?;
    let right = parse_Int(tokens, pos, 0)?;
    Ok(Bool::Eq(Box::new(left), Box::new(right)))
}
```

For ambiguous tokens, save/restore backtracking is used:
```rust
Token::Ident(_) => {
    let saved = *pos;
    if let Ok(left) = parse_Int(tokens, pos, 0) {
        if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::EqEq)) {
            *pos += 1;
            let right = parse_Int(tokens, pos, 0)?;
            return Ok(Bool::Eq(Box::new(left), Box::new(right)));
        }
    }
    *pos = saved;
    parse_Bool_own(tokens, pos)
}
```

---

## 11. Cast Rules

Cast rules embed one category into another without additional syntax.

### Syntax

```rust
CastInt . k:Int |- k : Proc;
```

This means: wherever a `Proc` is expected, an `Int` expression can appear directly,
wrapped as `Proc::CastInt(Box::new(int_expr))`.

### Dispatch

Cast rules participate in FIRST set analysis. When a token uniquely belongs to the
source category's FIRST set, the cast is deterministic:

```rust
// Integer token uniquely triggers Int parse, then wrap as Proc
Token::Integer(_) => {
    let val = parse_Int(tokens, pos, 0)?;
    Ok(Proc::CastInt(Box::new(val)))
}
```

### Critical Implementation Detail

Cast rules **must** be placed in the Pratt PREFIX handler, not in dispatch
wrappers. This ensures that after a cast parse completes, the Pratt infix loop
continues to check for infix operators at the call site. If cast rules were in
dispatch wrappers instead, the infix loop would never see operators following
the cast expression. See `pratt.rs` for the generated prefix match arm.

---

## 12. Lambda and Application

PraTTaIL auto-generates lambda abstraction and application syntax for every language.

### Lambda Syntax

```
^x.{body}              Single-binder lambda
^[x,y,z].{body}        Multi-binder lambda
```

Lambda rules are generated **only for the primary category** to avoid grammar
ambiguity. The binder type is inferred from how the bound variable is used in the
body.

> **Implementation note:** The lambda keyword in the generated lexer is `"lam "`
> (with a trailing space) to distinguish it from identifiers that happen to start
> with `lam`. The lexer's maximal munch + keyword priority ensures correct
> tokenization.

### Application Syntax

```
$type(lambda, arg)         Single application (typed by argument category)
$$type(lambda, arg1, arg2) Multi-application
```

Examples:
```
$int(^x.{x + 1}, 5)           Apply int-lambda to int argument
$bool(^x.{x && true}, false)   Apply bool-lambda to bool argument
$$int(^[x,y].{x + y}, 3, 4)   Apply multi-lambda to two int arguments
```

### Type Inference

When parsing `^x.{x + 1}`:
1. The body `x + 1` is parsed as the primary category
2. `body.infer_var_type("x")` examines the AST to find where `x` is used
3. If `x` appears in an `Add` (Int operation), the binder type is inferred as `Int`
4. The appropriate lambda variant is constructed: `Int::LamInt(Scope::new(...))`

### Generated Variants

For a language with `Int` and `Bool`, the primary category (`Int`) gets:

```rust
enum Int {
    // ... other variants ...

    // Lambda variants (one per category)
    LamInt(Scope<Binder<FreeVar<String>>, Box<Int>>),
    LamBool(Scope<Binder<FreeVar<String>>, Box<Int>>),

    // Multi-lambda variants
    MLamInt(Scope<Vec<Binder<FreeVar<String>>>, Box<Int>>),
    MLamBool(Scope<Vec<Binder<FreeVar<String>>>, Box<Int>>),

    // Application variants
    ApplyInt(Box<Int>, Box<Int>),
    ApplyBool(Box<Int>, Box<Bool>),
    MApplyInt(Box<Int>, Vec<Int>),
    MApplyBool(Box<Int>, Vec<Bool>),
}
```

### Beta-Reduction and Normalization

PraTTaIL languages implement the `normalize_term` method on the
`Language` trait to perform beta-reduction before evaluation:

```rust
pub trait Language: Send + Sync {
    /// Normalize a term (beta-reduce Apply/MApply of Lam/MLam, flatten
    /// collections, etc.). Default: returns a clone (no normalization).
    fn normalize_term(&self, term: &dyn Term) -> Box<dyn Term> {
        term.clone_box()
    }
}
```

Each generated language overrides this method to perform:

1. **Beta-reduction of single applications:**
   `ApplyDom(LamDom(scope), arg)` -> `body[binder := arg].normalize()`

2. **Beta-reduction of multi-applications:**
   `MApplyDom(MLamDom(scope), [arg1, arg2, ...])` -> `body[binders := args].normalize()`

3. **Recursive normalization** of all sub-terms.

**REPL integration:** The REPL calls `normalize_term` automatically after
environment variable substitution, before `try_direct_eval` and
`run_ascent`. This ensures that beta-redexes introduced by variable
substitution are reduced before the Ascent Datalog engine processes the
term.

### Inference-Driven Variant Selection

The lambda parser uses `infer_var_type` to select the correct
`Lam{Domain}` / `MLam{Domain}` variant based on how the binder
variable is used in the body. For each category in `all_categories`,
a match arm is generated:

```rust
let inferred = body.infer_var_type(&binder_name);
let scope = Scope::new(Binder(get_or_create_var(binder_name)), Box::new(body));
Ok(match inferred {
    Some(InferredType::Base(VarCategory::Proc)) => Proc::LamProc(scope),
    Some(InferredType::Base(VarCategory::Name)) => Proc::LamName(scope),
    Some(InferredType::Base(VarCategory::Int))  => Proc::LamInt(scope),
    // ... one arm per category ...
    _ => Proc::LamProc(scope)  // fallback to primary category default
})
```

The `_ =>` fallback handles `None` (variable not found in body) and
`InferredType::Arrow`/`MultiArrow` (higher-order function types) by
falling back to the default primary category variant.

**Type matching requirement:** The lambda variant **must** match the
dollar application variant for beta-reduction to succeed. `ApplyName`
checks for `LamName`; `ApplyProc` checks for `LamProc`. A mismatch
causes the normalizer to return the un-reduced term.

| Expression                    | Inferred Type       | Lambda Variant | Result                                                                    |
|-------------------------------|---------------------|----------------|---------------------------------------------------------------------------|
| `$proc(^x.{x}, {})`           | `VarCategory::Proc` | `LamProc`      | `{}`                                                                      |
| `$name(^loc.{loc!(init)}, n)` | `VarCategory::Name` | `LamName`      | `n!(init)`                                                                |
| `$int(^x.{x + 1}, 5)`         | `VarCategory::Int`  | `LamInt`       | `6`                                                                       |
| `$proc(^x.{*(x)}, {})`        | `VarCategory::Name` | `LamName`      | `*(x)` (no reduction -- `ApplyProc` expects `LamProc` but finds `LamName`) |

Note: In the last case, `x` appears in `*(x)` which uses `x` as a
`Name` (the drop operator `*` takes a Name argument). The inference
correctly creates `LamName`, but the dollar prefix `$proc` creates
`ApplyProc` -- the domain mismatch prevents reduction. The correct
invocation would be `$name(^x.{*(x)}, n)` which creates `ApplyName`
matching `LamName`.

---

## 13. HOL Native Evaluation

Rules can include native Rust code for evaluation using the `![...]` annotation.

### Syntax

```rust
Add . a:Int, b:Int |- a "+" b : Int ![a + b] step;
//                                    ^^^^^   ^^^^
//                                    Code    Mode
```

### Evaluation Modes

| Mode | Behavior |
|---|---|
| `step` | Single-step evaluation: apply once, return result |
| `fold` | Recursive fold: apply repeatedly until no more reductions |

### Examples

```rust
// Simple arithmetic
Add . a:Int, b:Int |- a "+" b : Int ![a + b] step;
Sub . a:Int, b:Int |- a "-" b : Int ![a - b] fold;
Pow . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] step;

// Boolean operations
Not . a:Bool |- "not" a : Bool ![{match a {
    true => false,
    false => true,
}}] step;

// String operations
Concat . a:Str, b:Str |- a "++" b : Str ![[a, b].concat()] step;
Len . s:Str |- "|" s "|" : Int ![s.len() as i32] step;

// Complex block expression
Add . a:Proc, b:Proc |- a "+" b : Proc ![{
    if let Proc::CastInt(a) = a {
        if let Proc::CastInt(b) = b {
            Proc::CastInt(Box::new(*a.clone() + *b.clone()))
        } else {
            Proc::Err
        }
    } else {
        Proc::Err
    }
}] fold;
```

The code inside `![...]` receives the rule's parameters as their native Rust types
(after any cast unwrapping). Block expressions use `![{ ... }]` syntax.

---

## 14. Equations and Rewrites

### Equations

Equational axioms define structural equivalences used for normalization:

```rust
equations {
    QuoteDrop . |- (NQuote (PDrop N)) = N;
    //             ^^^^^^^^^^^^^^^^^^^^  ^^
    //             Left-hand side         Right-hand side
}
```

This means `@(*N)` normalizes to `N` -- quoting a dereference cancels out.

### Rewrites

Rewrite rules define the operational semantics (computation steps):

```rust
rewrites {
    // Communication rule: input + output -> substitute and continue
    Comm . |- (PPar {(PInputs ns cont), *zip(ns,qs).*map(|n,q| (POutput n q)), ...rest})
        ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});

    // Execution rule: dereference a quoted process
    Exec . |- (PDrop (NQuote P)) ~> P;

    // Congruence rules: allow rewriting inside contexts
    ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});
    AddCongL . | S ~> T |- (Add S X) ~> (Add T X);
    AddCongR . | S ~> T |- (Add X S) ~> (Add X T);
}
```

### Rewrite Rule Anatomy

```
RuleName . | premise |- lhs ~> rhs;
```

- **premise** (optional): `S ~> T` means "given that S rewrites to T"
- **lhs**: pattern to match (using constructor syntax)
- **rhs**: replacement (with substitution)
- `...rest` captures remaining elements in a collection (bag/set/vec)
- `*zip`, `*map` patterns in rewrites match against the data structure

### Congruence Rules

Congruence rules propagate rewrites into subterms:

```
AddCongL . | S ~> T |- (Add S X) ~> (Add T X);
```

This says: if `S` rewrites to `T`, then `Add(S, X)` rewrites to `Add(T, X)`.
The `S` and `T` variables are bound by the premise.

---

## Complete Grammar Feature Summary

| Feature              | Syntax                                       | Module                      |
|----------------------|----------------------------------------------|-----------------------------|
| Type declaration     | `types { Cat }` or `types { ![T] as Cat }`   | lib.rs                      |
| Infix operator       | `a OP b : Cat`                               | binding_power.rs + pratt.rs |
| Right-assoc infix    | `a OP b : Cat right`                         | binding_power.rs + pratt.rs |
| Unary prefix op      | `OP a : Cat` (same-category, tight binding)  | recursive.rs (prefix_bp)    |
| Postfix operator     | `a OP : Cat` (same-category, tightest)       | binding_power.rs + pratt.rs |
| Mixfix operator      | `a OP1 b OP2 c : Cat` (3+ items, 2+ terms)  | binding_power.rs + pratt.rs |
| Structural prefix    | `OP "(" a ")" : Cat`                         | recursive.rs                |
| Unit constructor     | `\|- "token" : Cat`                          | recursive.rs                |
| Structural rule      | `\|- term1 "op" term2 : Cat`                 | recursive.rs                |
| Single binder        | `^x.p:[Type -> Type]`                        | recursive.rs                |
| Multi-binder         | `^[xs].p:[Type* -> Type]`                    | recursive.rs                |
| HashBag collection   | `ps:HashBag(Cat)`                            | recursive.rs                |
| HashSet collection   | `ps:HashSet(Cat)`                            | recursive.rs                |
| Vec collection       | `ns:Vec(Cat)`                                | recursive.rs                |
| Separator list       | `*sep("delim")`                              | recursive.rs                |
| Map pattern          | `*map(\|x\| ...)`                            | recursive.rs                |
| Zip collection       | `*zip(a,b)`                                  | recursive.rs                |
| Zip+Map+Sep          | `*zip(a,b).*map(\|x,y\| ...).*sep(",")`     | recursive.rs                |
| Optional             | `#opt(...)`                                  | recursive.rs                |
| Cross-category       | `a:CatA, b:CatA \|- a OP b : CatB`          | dispatch.rs                 |
| Cast                 | `k:CatA \|- k : CatB`                       | dispatch.rs                 |
| Lambda               | `^x.{body}` (auto-generated)                | pratt.rs + recursive.rs     |
| Application          | `$type(lam, arg)` (auto-generated)           | pratt.rs                    |
| HOL native           | `![rust_expr] mode`                          | recursive.rs                |
| Equation             | `\|- lhs = rhs`                              | (macro crate)               |
| Rewrite              | `\| premise \|- lhs ~> rhs`                  | (macro crate)               |
| `extends`            | `extends: [Base1, Base2]`                    | merge.rs + registry.rs      |
| `includes`           | `includes: [Lang1, Lang2]`                   | merge.rs + registry.rs      |
| `mixins`             | `mixins: [Frag1, Frag2]`                     | merge.rs + registry.rs      |
| `language_fragment!` | `language_fragment! { name: F, ... }`        | fragment.rs + registry.rs   |
| `compose_languages!` | `compose_languages! { name: C, ... }`        | compose.rs + compose_gen.rs |
