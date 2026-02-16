# LALRPOP Parser Integration: Limitations and Workarounds

> **Historical** -- These limitations were resolved by PraTTaIL in Phase 3 (LALRPOP removed).
> Kept for architectural context and to document why certain design decisions were made.

**Date:** 2026-02-14

---

## Table of Contents

1. [Introduction](#1-introduction)
2. [Background: LR(1) Parsing and LALRPOP](#2-background-lr1-parsing-and-lalrpop)
3. [Issue 1: Context-Sensitive Variable Disambiguation](#3-issue-1-context-sensitive-variable-disambiguation)
4. [Issue 2: Operator Precedence and Associativity](#4-issue-2-operator-precedence-and-associativity)
5. [Issue 3: Lambda Syntax Ambiguity](#5-issue-3-lambda-syntax-ambiguity)
6. [Issue 4: Var+Terminal Rule Partitioning](#6-issue-4-varterminal-rule-partitioning)
7. [Summary Table](#7-summary-table)
8. [Key Source Files](#8-key-source-files)

---

## 1. Introduction

MeTTaIL uses a **two-phase parser generation pipeline**: language definitions written in a
Rust proc-macro DSL are compiled into `.lalrpop` grammar files, which LALRPOP then compiles
into Rust LR(1) parsers. This extra level of indirection---generating a grammar from a
higher-level specification---means that the generator must work around several fundamental
limitations of LR(1) parsing, particularly when a single language definition has **multiple
type categories** (e.g. `Proc`, `Name`, `Int`) that share the same identifier token.

```
                                                  LALRPOP
  ┌───────────────┐   lalrpop.rs  ┌───────────┐  compiler ┌────────────┐
  │  language! {  │ ────────────> │  .lalrpop │ ────────> │ Rust LR(1) │
  │    types ...  │   (codegen)   │  grammar  │           │   parser   │
  │    terms ...  │               └───────────┘           └────────────┘
  │  }            │
  └───────────────┘
      DSL macro                   Generated file          Compiled parser
  (e.g. rhocalc.rs)           (e.g. rhocalc.lalrpop)
```

This document catalogs the four main categories of issues encountered during integration,
explains why LALRPOP cannot handle the naive grammar, and describes the workarounds
implemented in the grammar generator.

---

## 2. Background: LR(1) Parsing and LALRPOP

### LR(1) Parsing in Brief

An **LR(1)** parser reads input left-to-right, constructs a rightmost derivation in
reverse, and uses a single token of lookahead to decide between two actions at each step:

- **Shift**: push the current token onto the parse stack and advance.
- **Reduce**: pop the top *n* symbols from the stack, match them to the right-hand side of
  a production, and push the left-hand non-terminal.

A **conflict** arises when the parser cannot decide which action to take for a given
(state, lookahead) pair:

| Conflict Type | Meaning |
|---|---|
| **Shift-reduce** | The parser cannot decide whether to shift the next token or reduce what is already on the stack. |
| **Reduce-reduce** | Two different productions could both reduce the symbols on top of the stack, and the parser cannot tell which one applies. |

LALRPOP generates **LR(1)** parsers (or, equivalently, LALR(1) with conflict resolution).
It does not support GLR (generalized LR), so every conflict must be eliminated before the
grammar compiles.

### LALRPOP-Specific Features

LALRPOP provides several features beyond bare LR(1) that the MeTTaIL generator exploits:

- **`match {}` blocks**: a tokenizer-level priority system that gives fixed-string tokens
  precedence over regex tokens.
- **Macros**: parameterized rules like `Comma<T>` for comma-separated lists.
- **Inline actions**: Rust code in `=> { ... }` blocks that runs when a production reduces.
- **`pub` entry points**: multiple exported non-terminals per grammar.

LALRPOP does **not** support:
- `%left` / `%right` precedence declarations (unlike Yacc/Bison).
- GLR or ambiguous grammars.
- Context-sensitive tokenization (the same token cannot reduce to different non-terminals
  based on parser context).

---

## 3. Issue 1: Context-Sensitive Variable Disambiguation

### The Problem

In MeTTaIL, **every type category** can have variables. When a language has multiple
categories---say `Int`, `Bool`, and `Str` in the Calculator language---each category needs a
rule that parses a bare identifier into a variable of that type:

```
// Naive grammar (DOES NOT COMPILE)
IntAtom: Int = {
    <v:Ident> => Int::IVar(...)     // Rule A
};

BoolAtom: Bool = {
    <v:Ident> => Bool::BVar(...)    // Rule B
};

StrAtom: Str = {
    <v:Ident> => Str::SVar(...)     // Rule C
};
```

When the parser sees an identifier like `x`, it cannot decide which rule to use. All three
rules match the same token (`Ident`), and the parser has no lookahead information to
distinguish them. This is a classic **reduce-reduce conflict**: the parser has `Ident` on
top of the stack and three competing reductions (to `Int`, `Bool`, or `Str`).

### Why LALRPOP Cannot Handle It

In an LR(1) parser, the choice between reductions must be deterministic given the current
stack state and one token of lookahead. But in expressions like:

```
x + 3         -- x is Int
x && true     -- x is Bool
x ++ "hello"  -- x is Str
```

the variable `x` appears in an identical lexical context (bare `Ident` at the start of an
expression). The type is only determined by what comes *after* the variable---`+` vs `&&` vs
`++`---but by the time the parser sees the operator, it has already committed to reducing
`Ident` to a specific category. LR(1) parsers reduce bottom-up, so the leaf node (`Ident`)
must be reduced *before* the operator is seen.

### The Workaround: Type-Prefixed Variables

The generator uses a **type-prefix** scheme to disambiguate:

1. The **first category** (the "primary" category, listed first in the `types {}` block)
   gets bare `Ident` for variables. For the Calculator, this is `Int`.
2. All other categories require an explicit prefix: `"bool" ":" Ident` for `Bool`,
   `"str" ":" Ident` for `Str`.

Here is the actual generated grammar for the Calculator language
(`languages/src/generated/calculator.lalrpop`):

```lalrpop
// Int (primary category) -- bare Ident
IntAtom: Int = {
    ...
    <v:Ident> => Int::IVar(
        mettail_runtime::OrdVar(
            mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var(v.clone()))))
};

// Bool (non-primary) -- requires "bool:" prefix
BoolAtom: Bool = {
    ...
    "bool" ":" <v:Ident> => Bool::BVar(
        mettail_runtime::OrdVar(
            mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var(v.clone()))))
};

// Str (non-primary) -- requires "str:" prefix
StrAtom: Str = {
    ...
    "str" ":" <v:Ident> => Str::SVar(
        mettail_runtime::OrdVar(
            mettail_runtime::Var::Free(
                mettail_runtime::get_or_create_var(v.clone()))))
};
```

**User-facing effect**: in the Calculator language, users write bare `x` for integer
variables but `bool:x` for boolean variables and `str:s` for string variables:

```
exec 3 + x          -- x is Int (bare identifier)
exec bool:b && true  -- b is Bool (prefixed)
exec str:s ++ "hi"   -- s is Str (prefixed)
```

### The `match {}` Keyword Block

The type prefixes `"bool"` and `"str"` are alphanumeric strings. Without special handling,
LALRPOP's tokenizer would match them as `Ident` (via the regex `[a-zA-Z_][a-zA-Z0-9_]*`),
making them indistinguishable from variable names. The generator emits a LALRPOP `match {}`
block that gives these keywords priority:

```lalrpop
match {
    "bool",
    "str",
} else {
    r"[a-zA-Z_][a-zA-Z0-9_]*",
    _
}
```

This ensures that when the tokenizer sees the string `bool`, it produces the fixed-string
token `"bool"` rather than `Ident`. The `else` clause makes the regex and all other tokens
lower priority. Without this block, `bool:x` would be tokenized as three tokens---`Ident("bool")`,
`":"`, `Ident("x")`---and the parser would attempt to reduce `Ident("bool")` as a variable
name, failing to parse.

The `match {}` block is only emitted when the language has **3 or more types**
(`lalrpop.rs:131`), since two-type languages (like Ambient Calculus with `Proc` and `Name`)
use a different strategy described below.

### The `Name` Special Case

The `Name` category in RhoCalc and similar two-type languages receives special treatment:
it gets **both** the prefixed form (`"name" ":" Ident`) and a bare `Ident` fallback.

From the generated `rhocalc.lalrpop`:

```lalrpop
pub Name: Name = {
    "@" "(" <p:Proc> ")" => Name::NQuote(Box::new(p)),
    "name" ":" <v:Ident> => Name::NVar(...),
    <v:Ident> => Name::NVar(...)        // bare Ident also accepted
};
```

This is safe because `Name` is used as a sub-expression inside `Proc` rules (e.g.,
`n "!" "(" q ")"` for `POutput`), where the parser context is unambiguous: the `Name`
non-terminal is called explicitly from within `Proc` rules, so there is no reduce-reduce
conflict at that call site.

The generator enables bare `Ident` for a non-primary category when either:
- The language has exactly 2 types (so only one non-primary category), or
- The category name is `"Name"` (a frequently used subcategory in process calculi).

This logic is at `lalrpop.rs:1810`:

```rust
let allow_bare_ident = language.types.len() == 2 || cat_str == "Name";
```

### The REPL Pre-Substitution Workaround

Even with type prefixes, the REPL user experience would be poor if users had to manually
prefix every non-primary variable. Consider the Calculator:

```
x = true             -- binds x to a Bool value
exec x && (3 == 3)   -- FAILS: parser sees bare "x" and treats it as Int
```

The REPL's `pre_substitute_env` function (`repl/src/repl.rs:16-30`) solves this by
performing **whole-word textual substitution** of bound environment identifiers before
parsing. When `x` is bound to `true` (a `Bool`), the REPL replaces bare `x` with its
display representation before the parser ever sees it:

```
Input:     x && (3 == 3)
After sub: true && (3 == 3)    -- "x" replaced with "true"
Parser:    parses successfully as Bool
```

The substitution is order-independent because bindings are sorted by name length
(descending), so `foobar` is replaced before `foo`:

```rust
fn pre_substitute_env(input: &str, language: &dyn Language, env: &dyn Any) -> String {
    let bindings = language.list_env(env);
    // Sort by name length descending so "foobar" is replaced before "foo"
    let mut bindings: Vec<_> = bindings.into_iter().map(|(n, d, _)| (n, d)).collect();
    bindings.sort_by(|a, b| b.0.len().cmp(&a.0.len()));
    let mut result = input.to_string();
    for (name, display) in bindings {
        result = replace_whole_word(&result, &name, &display);
    }
    result
}
```

Only whole-word matches are replaced (checked via `is_identifier_char` boundary tests), so
a binding for `x` does not replace the `x` inside `extra`.

---

## 4. Issue 2: Operator Precedence and Associativity

### The Problem

When a language has binary infix operators (like `+`, `-`, `^` in the Calculator, or `+`
in RhoCalc), the naive grammar is ambiguous:

```
// Naive grammar (DOES NOT COMPILE)
pub Int: Int = {
    <left:Int> "+" <right:Int> => Int::Add(...),
    <left:Int> "-" <right:Int> => Int::Sub(...),
    <left:Int> "^" <right:Int> => Int::Pow(...),
    <i:Integer> => Int::NumLit(i),
    <v:Ident> => Int::IVar(...)
};
```

The expression `1 + 2 + 3` is ambiguous: should it parse as `(1 + 2) + 3` (left-associative)
or `1 + (2 + 3)` (right-associative)? This causes a **shift-reduce conflict**: after parsing
`1 + 2`, the parser sees `+` and cannot decide whether to reduce `1 + 2` to `Int` (then
shift `+`) or shift `+` onto the stack (making the `2` part of the right operand).

### Why LALRPOP Cannot Handle It

Unlike Yacc/Bison, LALRPOP does **not** support `%left` / `%right` / `%nonassoc`
precedence declarations. LALRPOP does have `#[precedence]` and `#[assoc]` attributes, but
the MeTTaIL generator uses a more robust solution: **tiered productions**.

### The Workaround: Tiered Productions

The generator splits each category into three LALRPOP non-terminals that form a precedence
hierarchy:

```
Cat     (top-level entry point, delegates to CatInfix)
  │
  ├── CatInfix   (handles binary infix operators, left-recursive)
  │     │
  │     └── CatAtom   (handles atoms: literals, variables, parenthesized exprs)
  │
  └── (Var+Terminal rules, if any, handled at top level)
```

Here is the actual generated grammar for `Int` in Calculator
(`languages/src/generated/calculator.lalrpop`):

```lalrpop
pub Int: Int = {
    <IntInfix>
};

IntInfix: Int = {
    <IntAtom>,                                                         // base case
    <left:IntInfix> "^" <right:IntAtom> => Int::Pow(Box::new(left), Box::new(right)),
    <left:IntInfix> "+" <right:IntAtom> => Int::Add(Box::new(left), Box::new(right)),
    <left:IntInfix> "-" <right:IntAtom> => Int::Sub(Box::new(left), Box::new(right)),
    <left:IntInfix> "~" <right:IntAtom> => Int::CustomOp(Box::new(left), Box::new(right)),
};

IntAtom: Int = {
    "(" <Int> ")",                   // parenthesized: goes back to top-level
    "|" <s:Str> "|" => Int::Len(Box::new(s)),
    <i:Integer> => Int::NumLit(i),
    <v:Ident> => Int::IVar(...),
    ...                              // lambdas, applications
};
```

**How the tiering works:**

1. `Int` delegates to `IntInfix`.
2. `IntInfix` is **left-recursive**: `<left:IntInfix> "op" <right:IntAtom>`. The left
   operand is `IntInfix` (allowing chaining), but the right operand is `IntAtom` (forcing
   the parser to reduce the right side to an atom before continuing). This produces
   **left-associative** parsing with no ambiguity.
3. `IntAtom` handles all non-infix constructs. Parenthesized expressions `"(" <Int> ")"`
   reference the top-level `Int` rule, allowing any expression inside parentheses.

**Parsing `1 + 2 + 3` step by step:**

```
Stack               Input         Action
                    1 + 2 + 3     shift 1
1                   + 2 + 3       reduce IntAtom -> IntInfix
IntInfix            + 2 + 3       shift +
IntInfix +          2 + 3         shift 2
IntInfix + 2        + 3           reduce IntAtom (right operand)
IntInfix + IntAtom  + 3           reduce IntInfix (left-recursive rule)
IntInfix            + 3           shift +
IntInfix +          3             shift 3
IntInfix + 3                      reduce IntAtom
IntInfix + IntAtom                reduce IntInfix
IntInfix                          reduce Int
Int                               accept → (1 + 2) + 3
```

### Cross-Category Infix Guard

Not all binary rules should be in the infix tier. Rules like `Eq . a:Int, b:Int |- a "==" b : Bool`
take two `Int` operands but produce a `Bool` result. If placed in the `BoolInfix` tier, the
generated rule would incorrectly reference `BoolInfix`/`BoolAtom` for the operands, but the
operands are actually `Int`.

The `is_hol_infix_rule` function (`lalrpop.rs:261-300`) prevents this by checking that
**both parameter types equal the rule's result category**:

```rust
fn is_hol_infix_rule(rule: &GrammarRule) -> bool {
    // ...
    // Both params must have type equal to rule.category (result type).
    // If not, this is a cross-category rule and must NOT be infix.
    left_ty.to_string() == cat_str && right_ty.to_string() == cat_str
}
```

Cross-category binary rules stay in the `Atom` tier instead. For example, `Eq` is placed
in `BoolAtom`, where both operands reference the top-level `Int` non-terminal:

```lalrpop
BoolAtom: Bool = {
    "(" <Bool> ")",
    <a:Int> "==" <b:Int> => Bool::Eq(Box::new(a), Box::new(b)),    // cross-category
    <a:Str> "==" <b:Str> => Bool::EqStr(Box::new(a), Box::new(b)), // cross-category
    "not" <a:BoolAtom> => Bool::Not(Box::new(a)),                   // unary prefix
    <b:Boolean> => Bool::BoolLit(b),
    "bool" ":" <v:Ident> => Bool::BVar(...)
};
```

### Atom-Tier Same-Category Substitution

When a rule in the `Atom` tier takes a parameter of the **same category**, the generator
replaces the non-terminal with `CatAtom` to prevent shift-reduce conflicts between the
Atom tier and the Infix tier. For example, `"not" <a:Bool>` would cause a conflict because
after shifting `"not"`, the parser would need to decide whether a following infix operator
belongs to the `Bool` inside `not` or to an outer `BoolInfix` rule. Using `BoolAtom`
forces the inner expression to be an atom (or parenthesized), eliminating the ambiguity.

From `lalrpop.rs:1016-1032`:

```rust
fn analyze_pattern_rule(
    rule: &GrammarRule,
    term_context: &[TermParam],
    syntax_pattern: &[SyntaxExpr],
    use_atom_for_same_category: bool,
) -> AnalyzedRule {
    // ...
    let rule_category = if use_atom_for_same_category {
        rule.category.to_string()
    } else {
        String::new()
    };
    // When nonterminal == rule_category, uses CatAtom instead of Cat
}
```

### Disabled Unary Minus

The grammar generator has **commented-out** support for unary minus on numeric types
(`lalrpop.rs:368-387`). Unary minus (`"-" <i:Integer>`) creates a shift-reduce conflict
with binary minus (`<left:IntInfix> "-" <right:IntAtom>`): after parsing a complete `Int`
expression, when the parser sees `-`, it cannot decide whether to reduce and treat `-` as
a binary operator, or to shift `-` as the start of a unary minus inside another rule.

```rust
// Commented out in generate_tiered_production:
// if type_str == "i32" || type_str == "i64" {
//     if let Some(rule) = filtered_other_rules.iter().find(|r| is_integer_literal_rule(r)) {
//         let label = rule.label.to_string();
//         production.push_str(&format!(
//             "    \"-\" <i:Integer> => {}::{}(-i),\n",
//             cat_str, label
//         ));
//     }
// }
```

As a result, negative integer literals are currently not supported in the generated parsers.
If needed, users can express negation via `0 - n`.

---

## 5. Issue 3: Lambda Syntax Ambiguity

### The Problem

MeTTaIL auto-generates lambda abstraction and application syntax for every language. A
lambda `^x.{body}` binds `x` in `body`, and `$type(lam, arg)` applies a lambda to an
argument. When multiple categories exist, the question is: which category's parser should
own the lambda rules?

If every category had its own lambda parsing rule, the grammar would have conflicts.
Consider:

```
// Hypothetical (DOES NOT COMPILE for multi-type languages)
IntAtom: Int = {
    "^" <x:Ident> "." "{" <body:Int> "}" => ...
};
BoolAtom: Bool = {
    "^" <x:Ident> "." "{" <body:Bool> "}" => ...
};
```

The expression `^x.{x + 1}` would parse correctly under `Int`, but `^x.{x && true}` would
need to start parsing under `Bool`. The parser must decide which non-terminal to enter when
it sees `"^"`, but at that point it has no information about the body's type. This is another
reduce-reduce conflict: the parser cannot predict which category the lambda body belongs to.

### The Workaround: Primary-Category-Only Lambdas

The generator only emits lambda parsing rules for the **primary (first) category**. The
lambda body always parses as the primary category, and **type inference at parse time**
determines which variant to construct.

From `lalrpop.rs:1822-1828`:

```rust
// Auto-generate lambda alternatives
// ONLY for the FIRST (primary) exported category to avoid grammar ambiguity
let first_export = language.types.first().map(|t| &t.name);
let is_primary_category = first_export.map(|f| f == category).unwrap_or(false);

if is_primary_category {
    // ... emit lambda rules
}
```

For example, in the Calculator (`Int` is primary), all lambda rules appear in `IntAtom`:

```lalrpop
IntAtom: Int = {
    // ... other Int rules ...

    // Single-binder lambda
    "^" <x:Ident> "." "{" <body:Int> "}" => {
        let binder = mettail_runtime::Binder(
            mettail_runtime::get_or_create_var(x.clone()));
        match body.infer_var_type(&x) {
            Some(ref t) => match t.base_type() {
                VarCategory::Int  => Int::LamInt(Scope::new(binder, Box::new(body))),
                VarCategory::Bool => Int::LamBool(Scope::new(binder, Box::new(body))),
                VarCategory::Str  => Int::LamStr(Scope::new(binder, Box::new(body))),
            },
            None => panic!("Lambda binder '{}' not used in body", x),
        }
    },

    // Lambda application (typed by argument category)
    "$int"  "(" <lam:Int> "," <arg:Int>  ")" => Int::ApplyInt(...),
    "$bool" "(" <lam:Int> "," <arg:Bool> ")" => Int::ApplyBool(...),
    "$str"  "(" <lam:Int> "," <arg:Str>  ")" => Int::ApplyStr(...),
};
```

**Key design decisions:**

1. **Binder type is inferred from usage**: `body.infer_var_type(&x)` examines how `x`
   appears in `body` and returns the appropriate `VarCategory`. This works because the body
   has already been parsed as the primary category (`Int`), and variable references carry
   type information in the AST.

2. **Application uses `$type(...)` prefix**: `$int(lam, arg)` applies a lambda expecting an
   `Int` argument; `$bool(lam, arg)` applies one expecting `Bool`. The `$` prefix and
   parenthesized syntax are unambiguous because `$int` is not a valid identifier and `(`
   after a keyword provides clear framing.

3. **Multi-lambda** (`^[x,y,z].{body}`) and **multi-application** (`$$type(lam, args...)`)
   follow the same pattern.

### Impact on Non-Primary Categories

Non-primary categories (`Bool`, `Str`, `Name`) have lambda **variants** in their AST (e.g.,
`Bool::LamInt`, `Bool::LamBool`) but no **parser rules** for lambda syntax. Lambdas that
return `Bool` are still representable---they are constructed programmatically (e.g., in
rewrite rules or Ascent logic) and can be displayed. They simply cannot be written directly
as input syntax in non-primary positions.

---

## 6. Issue 4: Var+Terminal Rule Partitioning

### The Problem

Some grammar rules start with a variable followed by a terminal, such as:

```
POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc ;
```

Here, the first element `n` is a `Name` variable, followed by the terminal `"!"`. If this
rule were placed in the `Atom` tier alongside the bare-variable rule (`<v:Ident> => PVar(...)`),
the parser would face a shift-reduce conflict: after seeing an `Ident`, it must decide
whether to reduce to `PVar` or to shift `"!"` to continue matching `POutput`.

### The Workaround: Top-Level Partitioning

Rules that match the pattern `Var Terminal ...` are detected by `is_var_terminal_rule`
(`lalrpop.rs:187-191`) and placed at the **top level** of the tiered production (above
`CatInfix`), where they are tried **first**:

```rust
fn is_var_terminal_rule(rule: &GrammarRule) -> bool {
    rule.items.len() >= 2
        && matches!(&rule.items[0], GrammarItem::NonTerminal(nt)
            if nt.to_string() == "Var")
        && matches!(&rule.items[1], GrammarItem::Terminal(_))
}
```

The generated RhoCalc grammar shows this partitioning
(`languages/src/generated/rhocalc.lalrpop`):

```lalrpop
pub Proc: Proc = {
    <ProcInfix>                 // delegates to infix tier
};

ProcInfix: Proc = {
    <ProcAtom>,                 // base case: atoms
    <left:ProcInfix> "+" <right:ProcAtom> => Proc::Add(...),  // infix
};

ProcAtom: Proc = {
    "(" <Proc> ")",
    "{}" => Proc::PZero,
    "*" "(" <n:Name> ")" => Proc::PDrop(...),
    ...
    <n:Name> "!" "(" <q:ProcAtom> ")" => Proc::POutput(...),  // Name starts with Ident
    ...
    <v:Ident> => Proc::PVar(...)   // bare variable (tried last)
};
```

Note: In the current RhoCalc grammar, `POutput` happens to be in `ProcAtom` rather than at
the top level because `Name` is a separate non-terminal (not a bare `Var`). The top-level
partitioning applies specifically to rules defined with the old BNFC-style `Var "=" Expr`
pattern. For the current language definitions using the HOL-style judgement syntax
(`n:Name |- n "!" "(" q ")" : Proc`), the `Name` non-terminal provides natural
disambiguation through the parser calling `Name` explicitly. The `POutput` rule is placed in
`ProcAtom` where it is tried before the bare `Ident` fallback, and LALRPOP resolves the
ambiguity because the `Name` non-terminal handles the initial `Ident` parsing before
`ProcAtom` needs to decide.

### How Recursive References Work

Within var+terminal rules, recursive references to the same category use `CatInfix` instead
of `Cat` to avoid circular references with the top-level rule. References to different
categories use their top-level non-terminal as-is. This is implemented in
`generate_var_terminal_alternative` (`lalrpop.rs:520-565`):

```rust
if nt == category {
    // Recursive reference: use CatInfix to avoid circular reference
    pattern.push_str(&format!(" <{}:{}Infix>", var_name, cat_str));
} else {
    // Different category: use as-is
    pattern.push_str(&format!(" <{}:{}>", var_name, nt));
}
```

---

## 7. Summary Table

| Issue | Symptom | Root Cause | Workaround | Source Location |
|---|---|---|---|---|
| **Context-sensitive variables** | Reduce-reduce conflict: `Ident` matches multiple category Var rules | LR(1) cannot determine which category an identifier belongs to without future context | Primary category gets bare `Ident`; others use `"type" ":" Ident` prefix | `lalrpop.rs:1766-1818` (`generate_auto_alternatives`) |
| **Keyword tokenization** | Type prefixes like `"bool"` tokenized as `Ident` instead of keyword | LALRPOP regex has no priority over fixed strings by default | `match {}` block gives keywords priority | `lalrpop.rs:129-148` (`generate_lalrpop_grammar`) |
| **REPL variable usability** | Users must write `bool:x` even after binding `x` to a Bool | Parser requires prefixes for non-primary variables | Pre-substitution: replace bound names with their values before parsing | `repl/src/repl.rs:16-30` (`pre_substitute_env`) |
| **Operator precedence** | Shift-reduce conflict for chained infix operators | LR(1) cannot resolve `a + b + c` associativity without precedence declarations | Three-tier production: `Cat` -> `CatInfix` (left-recursive) -> `CatAtom` | `lalrpop.rs:302-415` (`generate_tiered_production`) |
| **Cross-category infix** | `Int "==" Int : Bool` would be mis-placed in `BoolInfix` tier | Infix tier assumes both operands match result category | Guard: only rules where both param types == result category become infix | `lalrpop.rs:261-300` (`is_hol_infix_rule`) |
| **Atom-tier same-category** | `"not" Bool` shift-reduce with `BoolInfix "&&" BoolAtom` | Unary prefix followed by same-category operand creates ambiguity | Same-category params in Atom use `CatAtom` instead of `Cat` | `lalrpop.rs:1016-1032` (`analyze_pattern_rule`) |
| **Unary minus** | Shift-reduce with binary minus | `"-" Integer` vs `IntInfix "-" IntAtom` | Unary minus disabled (commented out) | `lalrpop.rs:368-387` |
| **Lambda ambiguity** | Multiple categories all want `"^" Ident "." "{" body "}"` | Parser cannot predict body category at `"^"` token | Lambda rules only in primary category; type inferred at parse time | `lalrpop.rs:1822-1920` (`generate_auto_alternatives`) |
| **Lambda application** | `(lam, arg)` ambiguous across categories | Parser cannot determine argument category | `$type(lam, arg)` prefix syntax with explicit type annotation | `lalrpop.rs:1894-1918` |
| **Var+Terminal rules** | Shift-reduce: `Ident` could be start of `Var "=" Expr` or bare `Var` | Parser cannot decide between reducing `Ident` and shifting terminal | Var+terminal rules placed at top level of tiered production | `lalrpop.rs:187-191`, `lalrpop.rs:318-325` |

---

## 8. Key Source Files

| File | Purpose |
|---|---|
| `macros/src/gen/syntax/parser/lalrpop.rs` | Core grammar generator (~2139 lines). Contains all workaround logic. |
| `languages/src/rhocalc.rs` | RhoCalc language definition (3 types: `Proc`, `Name`, `Int`). |
| `languages/src/calculator.rs` | Calculator language definition (3 types: `Int`, `Bool`, `Str`). |
| `languages/src/generated/rhocalc.lalrpop` | Generated RhoCalc grammar. Shows `match {}` block, type prefixes, tiered `Proc` rules. |
| `languages/src/generated/calculator.lalrpop` | Generated Calculator grammar. Shows `match {}` block, type prefixes, all three tiers for `Int`/`Bool`/`Str`. |
| `languages/src/generated/lambda.lalrpop` | Generated Lambda calculus grammar (1 type). Shows simple single-tier grammar with no workarounds needed. |
| `languages/src/generated/ambient.lalrpop` | Generated Ambient calculus grammar (2 types: `Proc`, `Name`). Shows bare `Ident` on both categories (2-type special case). |
| `repl/src/repl.rs` | REPL implementation. Contains `pre_substitute_env` for variable pre-substitution. |
