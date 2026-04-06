# MeTTaIL Developer README.

This file explains the project with examples.

If you are new: do not worry about all the names (`Ascent`, `PraTTaIL`, `rewrite`, etc.).  
Think of this project as a **language factory** + **language runner**:

- **Build-time pipeline** = factory: turns your `language! { ... }` definition into Rust code.
- **Runtime pipeline** = runner: takes user text and computes results using parser + rewrite/equation logic.

---

## Part 1: Build-time pipeline (compile `language!` DSL into Rust code)

### 1) Starting point: you write a language

You write code like this in files such as:

- `languages/src/rhocalc.rs`
- `languages/src/calculator.rs`
- `languages/src/lambda.rs`

Inside these files, the main input is:

```rust
language! {
  name: MyLang,
  types { ... },
  terms { ... },
  equations { ... },
  rewrites { ... },
  logic { ... }
}
```

Think of this as:  
**"Here is the grammar + math rules of my language."**

---

### 2) The macro entry point reads that DSL

Main file:

- `macros/src/lib.rs`

The `language!` procedural macro does this:

1. Parse DSL text into an internal AST (`LanguageDef`)
2. Validate it
3. Generate AST/types code
4. Generate parser/lexer code
5. Generate rewrite/equation logic code (Ascent rules)
6. Generate runtime language wrapper + metadata

---

### 3) DSL parser stage (turn syntax into structured data)

Important files:

- `macros/src/ast/language.rs` (main language AST and parser)
- `macros/src/ast/grammar.rs` (terms/grammar pieces)
- `macros/src/ast/pattern.rs` (pattern structures)
- `macros/src/ast/validation/validator.rs` (checks + errors)

Simple idea:  
`language!` text -> Rust structs that are easier for code generation.

---

### 4) Bridge to parser-generator format

Important file:

- `macros/src/gen/syntax/parser/prattail_bridge.rs`

This converts macro AST (`LanguageDef`) into PraTTaIL format (`LanguageSpec`), which parser generation understands.

PraTTaIL core types:

- `prattail/src/lib.rs`

Think of this as:

- **Input format A** (macro world) -> **Input format B** (parser-generator world)

---

### 5) Parser + lexer code generation

Important files:

- `prattail/src/pipeline.rs` (orchestrates parser+lexer generation)
- `prattail/src/automata/*` (regex/NFA/DFA lexer generation)
- `prattail/src/pratt.rs` (Pratt parser generation)
- `prattail/src/recursive.rs` (recursive-descent parts)
- `prattail/src/trampoline.rs` (parser trampoline)

Meaning in simple words:

- Lexer = split text into tokens (`3`, `+`, `4`)
- Parser = tokens -> AST tree (`Add(3, 4)`)

---

### 6) Rewrite/equation engine code generation (Ascent)

Important files:

- `macros/src/logic/mod.rs` (logic orchestrator)
- `macros/src/logic/relations.rs`
- `macros/src/logic/categories.rs`
- `macros/src/logic/equations.rs`
- `macros/src/logic/congruence.rs`
- `macros/src/logic/rules.rs`

Simple meaning:

- Generate relation tables (like `rw_proc`, `eq_proc`)
- Generate rules saying when one term rewrites to another
- Let Ascent compute all consequences to fixpoint

---

### 7) Runtime glue + term operations are generated too

Important files:

- `macros/src/gen/mod.rs` (top-level codegen orchestrator)
- `macros/src/gen/types/*` (AST enums)
- `macros/src/gen/term_ops/subst.rs` (substitution)
- `macros/src/gen/term_ops/normalize.rs` (normalization)
- `macros/src/gen/runtime/language.rs` (implements runtime `Language` trait)
- `macros/src/gen/runtime/metadata.rs` (metadata for REPL/help)

This is the “glue” so generated language can run in the app.

---

### 8) Where generated files actually go

Most generated Rust code is macro-expanded during compile (not manually edited files).

One explicit file output exists for Blockly:

- `macros/src/gen/blockly/writer.rs` writes to:
  - `languages/src/generated/<language>-blocks.ts`
  - `languages/src/generated/<language>-categories.ts`

---

### Build-time mini sample (mental model)

You write:

```text
Add . a "+" b : Proc ![a + b] fold;
```

Factory creates:

- Token rules for `+`
- Parser rule for infix add
- AST variant like `Proc::Add(...)`
- Fold/rewrite logic so `3 + 4` can become `7`

---

## Part 2: Runtime pipeline (user input -> parse/evaluate/rewrite -> results)

Now the generated language is used by users, mostly from REPL.

### 1) Runtime entry point

Important files:

- `repl/src/main.rs` (CLI app start)
- `repl/src/repl.rs` (interactive commands)
- `languages/src/lib.rs` (language registry exports)

User runs:

```bash
cargo run --bin mettail-repl
```

Then in REPL:

```text
lang rhocalc
exec 3 + 4
```

---

### 2) Core runtime interfaces

Important file:

- `runtime/src/language.rs`

Defines:

- `Term` trait
- `Language` trait (`parse_term`, `normalize_term`, `run_ascent`, etc.)
- `AscentResults` (all terms, rewrites, equivalences, custom relations)

Generated language code implements these traits.

---

### 3) Runtime stages (easy version)

When user enters `exec <expr>`, flow is:

1. **Lex**: text -> tokens
2. **Parse**: tokens -> AST term
3. **Normalize**: simplify (beta-like substitutions/flattening)
4. **Direct eval (optional fast path)**: if expression is simple ground arithmetic
5. **Ascent fixpoint**: apply rewrite/equation logic until stable
6. **Extract/display**: show normal forms, rewrites, eq classes

---

### 4) Runtime sample A: arithmetic

Input:

```text
exec 3 + 4
```

Pipeline:

- Lexer: `Integer(3)`, `+`, `Integer(4)`
- Parser: `Add(CastInt(3), CastInt(4))`
- Direct eval may short-circuit to `7`
- Otherwise Ascent fold/rewrite derives result

Output (conceptually):

```text
7
```

---

### 5) Runtime sample B: process rewrite (COMM-style context)

Input (rho style):

```text
{ @({}) ! ({}) | *(@({})) }
```

Pipeline:

- Parse into process AST (`PPar`, `POutput`, `PDrop`, ...)
- Ascent explores subterms and applies equations/rewrites
- COMM/Exec/congruence-like rules derive new terms
- Fixpoint reached when no more new rewrites/facts

Output:

- one or more reachable normal forms
- optional rewrite graph / equivalence classes

---

### 6) Query endpoint over computed results

Important files:

- `query/src/lib.rs`
- `query/src/run.rs` (re-exported by `query/src/lib.rs`)

This lets you run Datalog-like queries against `AscentResults` after execution.

---

## Project map (one-line purpose per crate)

- `languages/` -> language definitions (`language!` input)
- `macros/` -> compiler from DSL to generated Rust code
- `prattail/` -> parser/lexer generator engine
- `runtime/` -> shared runtime traits/data structures
- `repl/` -> command-line interactive frontend
- `query/` -> query engine over runtime results

---

## Glossary (quick newbie terms)

- **DSL**: domain-specific language (your `language! { ... }` syntax)
- **Token**: small unit from lexer (`+`, `123`, `ident`)
- **AST**: tree form of parsed program
- **Rewrite**: rule that transforms one term to another (`~>`)
- **Equation / Equivalence**: terms considered equal (`=`)
- **Fixpoint**: keep applying rules until nothing new appears
- **Ascent**: Rust Datalog engine used to compute rewrite/equation closures
- **Congruence**: if subterm changes, outer term changes consistently

---

## TL;DR

- Build-time: `language!` spec -> generated parser + AST + rewrite engine glue.
- Runtime: user expression -> parse/normalize/rewrite -> final results.
- If you know these files, you can navigate almost everything:
  - `languages/src/rhocalc.rs`
  - `macros/src/lib.rs`
  - `macros/src/gen/mod.rs`
  - `macros/src/logic/mod.rs`
  - `prattail/src/lib.rs`
  - `runtime/src/language.rs`
  - `repl/src/repl.rs`
