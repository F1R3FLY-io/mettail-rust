# Module 7: The PraTTaIL Parser Generator

**Goal**: Understand how syntax declarations become parsers.

PraTTaIL (Pratt + Recursive Descent parser generator) is a custom parser generator built specifically for MeTTaIL. It replaces LALRPOP and generates significantly less code (~2,000 lines vs ~20,000).

---

## 7.1 Why a Custom Parser Generator?

MeTTaIL initially used [LALRPOP](https://github.com/lalrpop/lalrpop), a popular Rust parser generator. But several limitations made it painful:

1. **Cross-category parsing** - In RhoCalc, a `Name` can appear where a `Proc` is expected (via `NQuote`). LALRPOP requires manual workarounds for this.
2. **Collection parsing** - `HashBag` and `Vec` with separators needed hand-written grammar rules.
3. **Binder parsing** - Variable binding syntax required special handling.
4. **Code size** - LALRPOP generated ~20,000 lines of parser code per language.

PraTTaIL eliminates all four issues by design.

---

## 7.2 Architecture Overview

```
language! { ... }
       │
       ▼
macros/src/gen/syntax/parser/prattail_bridge.rs
       │  (converts LanguageDef → LanguageSpec)
       ▼
prattail/src/pipeline.rs
       │
       ├── automata/ (lexer generation)
       │   ├── NFA → DFA → Minimize
       │   └── Equivalence classes → lex() function
       │
       ├── prediction.rs (FIRST sets)
       │   └── Dispatch tables for cross-category parsing
       │
       ├── pratt.rs (Pratt parser generation)
       │   └── Binding power tables → infix/postfix loops
       │
       ├── recursive.rs (Recursive descent generation)
       │   └── Prefix handlers → structured syntax
       │
       └── trampoline.rs (CPS transformation)
           └── Prevent stack overflow on deep nesting
       │
       ▼
TokenStream (complete parser as Rust source code)
```

---

## 7.3 Pratt Parsing: Handling Operators

[Pratt parsing](https://en.wikipedia.org/wiki/Operator-precedence_parser) is an algorithm for parsing expressions with infix, prefix, and postfix operators at different precedence levels.

### Binding Power

Each operator gets a **binding power** (precedence number). Higher binding power = tighter binding:

```
+ has binding power 10 (lower)
* has binding power 20 (higher)
```

So `2 + 3 * 4` parses as `2 + (3 * 4)` because `*` binds tighter.

In PraTTaIL, binding power is determined by **declaration order** in the `terms` section. Terms declared later have higher binding power.

### The Pratt Loop

The core algorithm (simplified):

```
parse_expr(min_bp):
  left = parse_prefix()     // "2" → NumLit(2)

  while next_token has bp >= min_bp:
    op = next_token          // "+"
    bp = binding_power(op)   // 10
    right = parse_expr(bp+1) // recurse with higher min_bp
    left = make_node(op, left, right)  // AddInt(left, right)

  return left
```

For right-associative operators, the recursive call uses `bp` instead of `bp+1`.

### What PraTTaIL Generates

**File**: `prattail/src/pratt.rs`

For each category, PraTTaIL generates a `parse_Cat` function that implements the Pratt loop. The binding power table is computed from the declaration order:

```rust
// Generated (conceptual):
fn parse_Int(tokens: &[(Token, Range)], pos: &mut usize, min_bp: u8) -> Result<Int, ParseError> {
    let mut left = parse_Int_prefix(tokens, pos)?;

    loop {
        match tokens.get(*pos) {
            Some((Token::Plus, _)) if 10 >= min_bp => {
                *pos += 1;
                let right = parse_Int(tokens, pos, 11)?;  // left-assoc: bp+1
                left = Int::AddInt(Box::new(left), Box::new(right));
            }
            Some((Token::Star, _)) if 20 >= min_bp => {
                *pos += 1;
                let right = parse_Int(tokens, pos, 21)?;
                left = Int::MulInt(Box::new(left), Box::new(right));
            }
            Some((Token::Caret, _)) if 30 >= min_bp => {
                *pos += 1;
                let right = parse_Int(tokens, pos, 30)?;  // right-assoc: bp (not bp+1)
                left = Int::PowInt(Box::new(left), Box::new(right));
            }
            _ => break,
        }
    }
    Ok(left)
}
```

---

## 7.4 Recursive Descent: Handling Structure

For terms that aren't simple infix/prefix/postfix, PraTTaIL generates recursive descent parsers. This handles:

- **Delimited expressions**: `"{" ps.*sep("|") "}"`
- **Keyword syntax**: `"new" "(" xs ")" "in" "{" p "}"`
- **Function-call syntax**: `"sin" "(" a ")"`
- **Collections**: `ps.*sep("|")` (elements separated by `|`)

**File**: `prattail/src/recursive.rs`

These generate prefix handlers that are called at the start of the Pratt loop:

```rust
// Generated (conceptual):
fn parse_Proc_prefix(tokens: &[(Token, Range)], pos: &mut usize) -> Result<Proc, ParseError> {
    match tokens.get(*pos) {
        Some((Token::LBrace, _)) => {
            // PPar or PZero
            *pos += 1;  // consume "{"
            if matches!(tokens.get(*pos), Some((Token::RBrace, _))) {
                *pos += 1;
                return Ok(Proc::PZero);
            }
            let mut elements = Vec::new();
            elements.push(parse_Proc(tokens, pos, 0)?);
            while matches!(tokens.get(*pos), Some((Token::Pipe, _))) {
                *pos += 1;  // consume "|"
                elements.push(parse_Proc(tokens, pos, 0)?);
            }
            expect(tokens, pos, Token::RBrace)?;
            Ok(Proc::PPar(HashBag::from_iter(elements)))
        }
        Some((Token::New, _)) => {
            // PNew
            *pos += 1;  // consume "new"
            expect(tokens, pos, Token::LParen)?;
            let binders = parse_ident_list(tokens, pos, ",")?;
            expect(tokens, pos, Token::RParen)?;
            expect(tokens, pos, Token::In)?;
            expect(tokens, pos, Token::LBrace)?;
            let body = parse_Proc(tokens, pos, 0)?;
            expect(tokens, pos, Token::RBrace)?;
            Ok(Proc::PNew(Scope::new(binders, body)))
        }
        // ... more prefix handlers
    }
}
```

---

## 7.5 The Lexer: Automata-Optimized Tokenization

**File**: `prattail/src/automata/`

PraTTaIL generates a lexer using finite automata theory:

```
Terminal strings from grammar
    ↓
NFA (Nondeterministic Finite Automaton)
    ↓ subset construction
DFA (Deterministic Finite Automaton)
    ↓ Hopcroft minimization
Minimal DFA
    ↓ equivalence class extraction
Character → class mapping + DFA transition table
    ↓ codegen
lex() function (Rust source code)
```

This produces a very efficient lexer that:
- Processes one character at a time
- Uses a small lookup table (not a giant match statement)
- Handles keywords, operators, identifiers, and literals
- Produces `Vec<(Token, Range)>` with source positions

The `Token` enum includes all terminals from the grammar plus built-in tokens for identifiers, integers, floats, strings, and booleans.

---

## 7.6 Cross-Category Parsing

In RhoCalc, a `Name` can appear where a `Proc` is expected (e.g., in `CastInt`). PraTTaIL handles this with **prediction** and **dispatch**:

**File**: `prattail/src/prediction.rs`, `prattail/src/dispatch.rs`

1. Compute FIRST sets for each category (what tokens can start a parse of that category)
2. When a category's prefix handler encounters a token that belongs to another category's FIRST set, try parsing that category
3. If successful, wrap the result in the appropriate cross-category constructor

This is transparent to the user - the generated parser just handles it.

---

## 7.7 Trampolining for Deep Nesting

**File**: `prattail/src/trampoline.rs`

Deeply nested terms like `{ { { { ... } } } }` can overflow the call stack with recursive descent. PraTTaIL uses **trampolining** (CPS transformation) to convert recursion to iteration:

Instead of:
```rust
fn parse_Proc(...) -> Result<Proc> {
    // ... calls parse_Proc recursively (can overflow)
}
```

It generates:
```rust
enum Continuation {
    Return(Proc),
    CallParseProc { pos: usize, then: Box<dyn FnOnce(Proc) -> Continuation> },
}

fn parse_Proc_trampoline(...) -> Result<Proc> {
    let mut cont = start_parse_Proc(...);
    loop {
        match cont {
            Continuation::Return(result) => return Ok(result),
            Continuation::CallParseProc { pos, then } => {
                let inner = parse_prefix_and_infix(...)?;
                cont = then(inner);
            }
        }
    }
}
```

This uses heap allocation instead of stack frames, preventing overflow on deeply nested inputs.

---

## 7.8 The Bridge: Macro to PraTTaIL

**File**: `macros/src/gen/syntax/parser/prattail_bridge.rs`

The bridge converts the macro's `LanguageDef` into PraTTaIL's `LanguageSpec`:

```rust
// LanguageDef (macro world)     →    LanguageSpec (PraTTaIL world)
// LanguageDef.types             →    Vec<CategorySpec>
// LanguageDef.terms             →    Vec<RuleSpec>
// GrammarItem::Terminal("+")    →    SyntaxItemSpec::Terminal("+")
// GrammarItem::NonTerminal(a)   →    SyntaxItemSpec::NonTerminal { ... }
// collection with sep           →    SyntaxItemSpec::Collection { ... }
// zip+map+sep pattern           →    SyntaxItemSpec::ZipMapSep { ... }
```

PraTTaIL then automatically classifies each rule (is it infix? postfix? a collection? a cast?) and generates the appropriate parser code.

---

## 7.9 Collection Parsing

Collections like `HashBag` and `Vec` get special treatment:

```rust
PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
```

This generates a parser that:
1. Expects `{`
2. Parses zero or more `Proc` terms separated by `|`
3. Expects `}`
4. Collects results into a `HashBag<Proc>`

The `.*sep("|")` combinator handles the separator. Other patterns:
- `xs.*sep(",")` - comma-separated list
- `*zip(ns,xs).*map(|n,x| n "?" x).*sep(",")` - zipped, mapped, and separated

---

## Exercises

### Exercise 1: Read the Architecture

Read `prattail/src/lib.rs` for the module overview. List all the modules and write one sentence about what each does.

### Exercise 2: Run Parser Tests

```bash
cargo test -p prattail
```

How many tests pass? What areas do they cover?

### Exercise 3: Trace Precedence

For the Calculator with terms declared in order: `Tern`, comparisons, boolean ops, `Add/Sub`, `Mul/Div`, `Pow`, `Neg`, `Fact`:

1. What binding power does `+` get? What about `*`? What about `^`?
2. How does `2 + 3 * 4` parse? Draw the AST tree.
3. How does `2 ^ 3 ^ 2` parse? (Hint: `^` is `right`)

### Exercise 4: Trace Collection Parsing

For `{ P | Q | R }` in RhoCalc:
1. What token starts the parse? (`{`)
2. How does the parser know to try `PPar` vs `PZero`?
3. How are the `|` separators handled?
4. What AST node is produced?

---

## Checkpoint

Before moving on, make sure you can:

1. **Explain** why PraTTaIL was built instead of using LALRPOP
2. **Describe** how Pratt parsing handles operator precedence
3. **Describe** how declaration order determines binding power
4. **Explain** what trampolining is and why it's needed
5. **Trace** how a collection syntax pattern becomes a parser

---

**Next**: [Module 8: The Ascent Datalog Engine](08-ascent-datalog.md) - How term rewriting becomes Datalog computation
