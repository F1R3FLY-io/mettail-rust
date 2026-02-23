# PraTTaIL: Motivation and Design Rationale

**Date:** 2026-02-14

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [The Four LALRPOP Limitations](#2-the-four-lalrpop-limitations)
   - [Limitation 1: Variable Disambiguation via Type Prefixes](#limitation-1-variable-disambiguation-via-type-prefixes)
   - [Limitation 2: Precedence/Associativity via Tiered Productions](#limitation-2-precedenceassociativity-via-tiered-productions)
   - [Limitation 3: Lambda Ambiguity](#limitation-3-lambda-ambiguity)
   - [Limitation 4: Var+Terminal Rule Partitioning](#limitation-4-varterminal-rule-partitioning)
3. [Code Size Explosion](#3-code-size-explosion)
4. [Two-Phase Build Complexity](#4-two-phase-build-complexity)
5. [PraTTaIL Design Goals](#5-prattail-design-goals)
6. [Why Not pest / tree-sitter / Other Generators?](#6-why-not-pest--tree-sitter--other-generators)
7. [Summary](#7-summary)

---

## 1. Executive Summary

PraTTaIL (Pratt + Recursive Descent + Automata-Interleaved Lexing) is a custom
parser generator built specifically for MeTTaIL. It exists because the previous
LALRPOP-based pipeline suffers from four fundamental limitations inherent to
LR(1) parsing, a code-size explosion that scales multiplicatively with grammar
complexity, and a two-phase build process that creates unnecessary coupling
between the proc-macro crate and the LALRPOP toolchain.

PraTTaIL replaces all of this with a single proc-macro pass that generates
~1,500-2,000 lines of parser code per language---a 10-14x reduction from the
~20,000 lines the LALRPOP pipeline produces across 5 grammars---while
eliminating every workaround the old pipeline required.

---

## 2. The Four LALRPOP Limitations

MeTTaIL's `language!` macro compiles language definitions into parsers. When
LALRPOP is the backend, the generated `.lalrpop` grammars must work around four
categories of LR(1) conflicts. Each workaround degrades either the user-facing
syntax, the generated code quality, or both.

### Limitation 1: Variable Disambiguation via Type Prefixes

**The Problem.** In a multi-category language (e.g., Calculator with `Int`,
`Bool`, `Str`), every category can have variables. All variable rules match the
same token---a bare identifier:

```
IntAtom:  <v:Ident> => Int::IVar(...)     // Rule A
BoolAtom: <v:Ident> => Bool::BVar(...)    // Rule B
StrAtom:  <v:Ident> => Str::SVar(...)     // Rule C
```

When the parser sees `x`, it has `Ident` on the stack and must decide which
category to reduce into. This is a **reduce-reduce conflict**: three productions
compete for the same token, and no amount of lookahead resolves it because the
type of `x` depends on its *usage context* (the operator that follows it), not
its lexical form.

**The LALRPOP Workaround.** The primary (first-declared) category keeps bare
identifiers. All other categories require an explicit type prefix:

```
Int:  x           -- bare identifier (primary category)
Bool: bool:b      -- requires "bool:" prefix
Str:  str:s       -- requires "str:" prefix
```

This imposes an artificial syntactic burden on users and requires a `match {}`
block to give prefix keywords priority over the identifier regex. The REPL
further papers over this with a `pre_substitute_env` function that textually
replaces bound variable names with their values before parsing---a fragile
workaround that breaks on shadowing, name collisions inside longer identifiers,
and nested scopes.

**How PraTTaIL Eliminates It.** PraTTaIL uses top-down parsing with context
propagation. When `parse_Bool(tokens, pos, 0)` is called, the parser *knows* it
is looking for a `Bool` expression. A bare identifier in that context is
unambiguously a `Bool` variable. There is no bottom-up reduction ambiguity
because the category is determined by the caller, not by the token.

```
Parsing:   b && true

  parse_Bool calls parse_Bool_prefix
    sees Ident("b") ──▶ BVar("b")  (unambiguous: we are in Bool context)
  Pratt loop sees Token::AmpAmp (&&)
    calls parse_Bool for right operand
      sees Token::Boolean(true) ──▶ BoolLit(true)
  Result: Comp(BVar("b"), BoolLit(true))
```

### Limitation 2: Precedence/Associativity via Tiered Productions

**The Problem.** LR(1) parsers cannot handle ambiguous infix operator chains
without explicit disambiguation. The expression `1 + 2 + 3` causes a
shift-reduce conflict: after parsing `1 + 2`, the parser sees `+` and cannot
decide whether to reduce `1 + 2` into `Int` (left-associative) or shift `+`
(right-associative).

Unlike Yacc/Bison, LALRPOP has no `%left`/`%right` declarations.

**The LALRPOP Workaround.** The generator splits each category into three
non-terminals forming a precedence hierarchy:

```
Cat (entry) ──▶ CatInfix (left-recursive infix) ──▶ CatAtom (atoms)
```

`CatInfix` uses left-recursion: `<left:CatInfix> "+" <right:CatAtom>`, forcing
left-associativity. The right operand is constrained to `CatAtom`, so the parser
must reduce it to an atom before seeing the next operator.

This is correct but verbose: every infix operator must be declared in `CatInfix`
with explicit `CatAtom` on the right. Cross-category operators (like
`Int "==" Int : Bool`) must be carefully excluded from the infix tier and
placed in `CatAtom` with a guard checking that operand types match the result
category. Unary minus is disabled entirely because it creates an unresolvable
shift-reduce conflict with binary minus.

**How PraTTaIL Eliminates It.** Pratt parsing handles precedence and
associativity natively via binding power pairs `(left_bp, right_bp)`:

```
Left-associative:   left_bp < right_bp   e.g., + gets (2, 3)
Right-associative:  left_bp > right_bp   e.g., ^ gets (5, 4)
```

The Pratt loop checks `if l_bp < min_bp { break; }` to decide whether to
continue or return. No grammar transformation is needed; operators are simply
entries in a binding power table. Cross-category operators are handled by the
dispatch layer, not the Pratt loop.

### Limitation 3: Lambda Ambiguity

**The Problem.** MeTTaIL auto-generates lambda syntax (`^x.{body}`) for every
language. When multiple categories exist, each would need its own lambda rule:

```
IntAtom:  "^" <x:Ident> "." "{" <body:Int>  "}" => ...
BoolAtom: "^" <x:Ident> "." "{" <body:Bool> "}" => ...
```

The parser sees `^` and cannot predict which category's body will follow. This
is a reduce-reduce conflict at the point where the parser must choose which
non-terminal to enter for the body.

**The LALRPOP Workaround.** Lambda rules were generated only for the primary
category. The body always parsed as the primary type, and a fixed lambda
variant was constructed (e.g., always `LamProc` for a Proc-primary language).
This meant lambdas binding non-primary-category variables could not be
written directly in input syntax---they could only be constructed
programmatically (e.g., building `LamName` in Rust code).

**How PraTTaIL Eliminates It.** PraTTaIL uses top-down parsing with
inference-driven variant selection to make **all** lambda domain variants
constructible from surface syntax. The process has three steps:

```
^x.{*(x)}
   │
   ├─ Step 1: Parse body as primary category
   │          body = PDrop(NVar("x"))
   │
   ├─ Step 2: Call body.infer_var_type("x")
   │          x appears in PDrop(n:Name) → VarCategory::Name
   │
   └─ Step 3: Match on inferred type, construct matching variant
              VarCategory::Name → Proc::LamName(Scope::new(binder, body))
```

Because the parser is top-down, every category's parser *can* encounter
lambda syntax without ambiguity---the dispatch decision is made by the
caller before the lambda token is consumed. The `infer_var_type` call
examines the parsed body AST to determine which category the bound
variable occupies, then a generated `match` expression selects the
corresponding `Lam{Domain}` variant (one arm per category). This
eliminates both the reduce-reduce conflict and the limitation that
non-primary lambda variants were inaccessible from surface syntax.

### Limitation 4: Var+Terminal Rule Partitioning

**The Problem.** Rules where the first element is a variable (parsed as
`Ident`) followed by a terminal create a shift-reduce conflict with the bare
variable fallback:

```
POutput:  <n:Name> "!" "(" <q:Proc> ")"   -- starts with Ident, then "!"
PVar:     <v:Ident>                         -- just Ident
```

After seeing `Ident`, the parser cannot decide whether to reduce to `PVar` or
shift `"!"` to continue matching `POutput`.

**The LALRPOP Workaround.** The generator detects rules matching the pattern
`Var Terminal ...` and places them at the top level of the tiered production,
above the infix tier. This forces the parser to try var+terminal rules before
falling through to the bare variable rule.

**How PraTTaIL Eliminates It.** In a Pratt/RD parser, the prefix handler for
a category receives the current token and can peek ahead. When it sees `Ident`
followed by `!`, it matches the `POutput` pattern. When it sees `Ident`
followed by an infix operator or end-of-expression, it falls through to the
variable handler. The decision is made by lookahead in the prefix function,
not by grammar structure.

---

## 3. Code Size Explosion

The LALRPOP pipeline suffers from multiplicative code growth:

```
┌──────────────────┬─────────────────────┬──────────────────────────────────┐
│ Component        │ Per-grammar cost    │ 5 grammars (Lambda, Ambient,     │
│                  │                     │  RhoCalc, Calculator, Space)     │
├──────────────────┼─────────────────────┼──────────────────────────────────┤
│ .lalrpop file    │ ~70-140 lines       │ ~430 lines total                 │
│ LALRPOP output   │ ~2,000-5,000 lines  │ ~10,000-25,000 lines             │
│ lalrpop.rs gen   │ 2,139 lines (shared)│ 2,139 lines                      │
│ Tiered prods     │ ~30 lines/category  │ ~150 lines (across 5 grammars)   │
│ Lambda/App code  │ ~50 lines/category  │ ~250 lines                       │
│ match{} blocks   │ ~10 lines/grammar   │ ~50 lines                        │
├──────────────────┼─────────────────────┼──────────────────────────────────┤
│ Total LALRPOP    │                     │ ~15,000-20,000+ lines generated  │
└──────────────────┴─────────────────────┴──────────────────────────────────┘
```

The LALRPOP-generated Rust files contain enormous state machine tables,
reduction functions, and error recovery logic. These files are not
human-readable and compile slowly because the Rust compiler must process
thousands of match arms and table entries.

**PraTTaIL target:** ~1,500-2,000 lines total per grammar, ~300 for the lexer,
~200-400 for the Pratt loops, ~200-400 for RD handlers, and a compact
cross-category dispatch layer. The generator itself is ~4,300 lines
(comparable to the single `lalrpop.rs` generator), but its output is an order
of magnitude smaller.

---

## 4. Two-Phase Build Complexity

The LALRPOP pipeline requires two distinct compilation phases:

```
Phase 1: Proc-macro expansion
  language! { ... }
       │
       ▼
  Generate .lalrpop file to disk (lalrpop.rs, ~2,139 lines)
       │
       ▼
  .lalrpop file written to languages/src/generated/

Phase 2: LALRPOP compilation (build.rs)
  build.rs detects .lalrpop files
       │
       ▼
  LALRPOP compiler runs (external dependency)
       │
       ▼
  Generates Rust parser code (.rs files)
       │
       ▼
  Rust compiler compiles the generated code
```

This two-phase build has several consequences:

1. **File-system coupling.** The proc-macro writes files to disk that a
   `build.rs` script must discover and process. This creates an ordering
   dependency between macro expansion and the build script.

2. **External toolchain dependency.** LALRPOP is an external crate with its own
   parser for `.lalrpop` files, its own conflict detection, and its own code
   generation. Bugs in LALRPOP's LR(1) table construction are opaque and
   difficult to debug.

3. **Error locality.** When a generated grammar has a conflict, the error
   message refers to line numbers in the `.lalrpop` file, not the original
   `language!` macro. The user must mentally map from LALRPOP's error to the
   original language definition.

4. **Incremental build fragility.** Changes to the `language!` macro may not
   trigger re-running the LALRPOP compiler if the build system does not detect
   the regenerated `.lalrpop` file as changed.

**PraTTaIL eliminates the two-phase build entirely.** The `language!` macro
expands directly to Rust code in a single proc-macro pass:

```
language! { ... }  ─(proc-macro)─→  TokenStream (Rust source code)
```

No intermediate files, no external toolchain, no build.rs integration.

---

## 5. PraTTaIL Design Goals

PraTTaIL is designed around four primary goals:

### Goal 1: Correctness

The generated parser must produce identical ASTs to the LALRPOP parser for all
valid inputs and report clear errors for invalid inputs. Correctness is
established through:

- **Shared test suite.** The same corpus of test inputs exercises both parsers.
- **Property-based testing.** Random term generation verifies round-trip
  (pretty-print then re-parse) for all language constructs.
- **Formal foundations.** Pratt parsing has well-understood correctness
  properties (it is equivalent to operator-precedence parsing). Recursive
  descent is trivially correct when each production is deterministic, which the
  FIRST set analysis guarantees.

### Goal 2: Efficiency

The generated parser must run in O(n) time and O(n) space for all inputs:

- **Lexer.** DFA-based lexing is O(n) with constant-factor optimization via
  equivalence class compression (~15-20x fewer transition table columns).
- **Parser.** Pratt parsing is O(n) for expression parsing with bounded
  recursion depth proportional to nesting. Recursive descent handlers are
  O(n) per rule invocation. No backtracking occurs for unambiguous FIRST
  sets; bounded backtracking (save/restore) is used only for cross-category
  overlap, which is statically bounded.

### Goal 3: Minimal Code

The generated code must be small enough to:

- **Compile quickly.** Fewer lines means less work for the Rust compiler.
  The Pratt loop for a category is ~20-30 lines. A binding power table is a
  single match expression with one arm per operator.
- **Be auditable.** A developer should be able to read the generated code
  and understand what the parser does. LALRPOP's table-driven output is
  opaque; PraTTaIL's direct-coded output is readable Rust.
- **Have a small binary footprint.** Important for WASM targets and
  embedded deployments.

### Goal 4: Extensibility

The generator must accommodate new language features without modifying the
core parsing algorithm:

- **New operators** require only a binding power table entry and a make_infix
  arm. No grammar restructuring.
- **New structural constructs** (binders, collections, pattern operations) are
  handled by recursive descent handlers that pattern-match on syntax items.
- **New categories** require a new Pratt parser instance and dispatch table
  entries. Cross-category dispatch is auto-generated from FIRST set analysis.

---

## 6. Why Not pest / tree-sitter / Other Generators?

Several alternative parser generators were considered and rejected:

### pest (PEG Parser)

```
┌───────────────────────────┬──────────────────────────────────────────┐
│ Advantage                 │ Disadvantage for MeTTaIL                 │
├───────────────────────────┼──────────────────────────────────────────┤
│ Elegant PEG syntax        │ Produces untyped parse trees (Pairs)     │
│ No separate build phase   │ Requires manual AST construction         │
│ Well-maintained           │ PEG ordered choice hides ambiguity       │
│ Good error messages       │ No binding power / precedence support    │
│                           │ O(n) but with high constant factor       │
└───────────────────────────┴──────────────────────────────────────────┘
```

pest produces `Pairs<Rule>` trees that must be manually walked to construct
typed ASTs. For MeTTaIL's typed categories (Proc, Name, Int, Bool, Str), this
would require writing conversion code for every constructor---the exact code
that PraTTaIL auto-generates. pest's PEG ordered choice (`/`) silently picks
the first matching alternative, which can hide ambiguity bugs.

### tree-sitter

```
┌───────────────────────────┬──────────────────────────────────────────┐
│ Advantage                 │ Disadvantage for MeTTaIL                 │
├───────────────────────────┼──────────────────────────────────────────┤
│ Incremental parsing       │ C-based (FFI overhead, no proc-macro)    │
│ Error recovery            │ Grammar defined in JavaScript            │
│ Battle-tested             │ Produces untyped CST, not typed AST      │
│ LSP-friendly              │ External build toolchain (node.js)       │
│                           │ Designed for editors, not interpreters   │
└───────────────────────────┴──────────────────────────────────────────┘
```

tree-sitter is designed for editor integration (syntax highlighting, code
folding), not for constructing typed ASTs for interpretation and rewriting.
It produces concrete syntax trees (CSTs) that would need a full CST-to-AST
pass. Its grammar is defined in JavaScript and compiled by a separate
toolchain, reintroducing the two-phase build problem.

### nom (Parser Combinator)

```
┌───────────────────────────┬──────────────────────────────────────────┐
│ Advantage                 │ Disadvantage for MeTTaIL                 │
├───────────────────────────┼──────────────────────────────────────────┤
│ Pure Rust, no codegen     │ Manual parser, not generated             │
│ Composable                │ No precedence handling                   │
│ Zero-copy capable         │ Code duplication across grammars         │
│ Good for binary formats   │ Not designed for PL grammars             │
└───────────────────────────┴──────────────────────────────────────────┘
```

nom is excellent for hand-written parsers but provides no generation
infrastructure. Each grammar would require writing a parser manually,
defeating the purpose of MeTTaIL's declarative `language!` macro.

### chumsky / winnow / combine

Similar to nom: parser combinator libraries that require hand-written code.
They do not generate parsers from grammar specifications.

### Why a Custom Generator?

MeTTaIL's requirements are specific and well-defined:

1. Typed ASTs with constructor variants matching grammar rules.
2. Multi-category parsing with cross-category operators and casts.
3. Binding/scoping support (moniker integration).
4. Collection types (HashBag, HashSet, Vec) with separators.
5. Lambda/application auto-generation.
6. Integration with the Ascent Datalog engine for logic rules.

No existing generator supports all of these. PraTTaIL is purpose-built to
generate exactly the code MeTTaIL needs, with no wasted abstraction layers.

---

## 7. Summary

```
┌────────────────────────────┬────────────────────┬─────────────────────┐
│ Dimension                  │ LALRPOP Pipeline   │ PraTTaIL            │
├────────────────────────────┼────────────────────┼─────────────────────┤
│ Parsing algorithm          │ LR(1) bottom-up    │ Pratt + RD top-down │
│ Variable disambiguation    │ Type prefixes      │ Context propagation │
│ Precedence/associativity   │ Tiered productions │ Binding power pairs │
│ Lambda ambiguity           │ Primary-only rules │ Caller-context      │
│ Var+terminal partitioning  │ Top-level placement│ Lookahead in prefix │
│ Generated code per grammar │ ~3,000-5,000 lines │ ~1,500-2,000 lines  │
│ Total for 5 grammars       │ ~15,000-20,000+    │ ~7,500-10,000       │
│ Build phases               │ 2 (macro + LALRPOP)│ 1 (proc-macro only) │
│ External dependencies      │ lalrpop crate      │ None                │
│ Lexer strategy             │ Regex (LALRPOP)    │ DFA (automata)      │
│ Time complexity            │ O(n)               │ O(n)                │
│ Space complexity           │ O(n) + tables      │ O(n) + compact DFA  │
└────────────────────────────┴────────────────────┴─────────────────────┘
```

PraTTaIL exists because the LALRPOP pipeline's workarounds are fundamental
consequences of LR(1) parsing that cannot be fixed without changing the
parsing algorithm. By switching to Pratt + recursive descent with automata-
optimized lexing, PraTTaIL eliminates all four categories of workarounds,
produces dramatically less generated code, and removes the two-phase build
complexity---all while maintaining O(n) time and space complexity.
