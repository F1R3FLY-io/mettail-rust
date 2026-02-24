# RhoCalc End-to-End Pipeline

This document set traces a single RhoCalc expression through every stage of the
MeTTaIL / PraTTaIL compilation and evaluation pipeline.  Each file is
self-contained but cross-referenced; read them in order for the full picture.

## Pipeline Diagram

```
                          ┌─────────────────────────────┐
                          │   language! { ... }  DSL    │  languages/src/rhocalc.rs
                          └──────────────┬──────────────┘
                                         │  proc-macro expansion
                                         ▼
                          ┌─────────────────────────────┐
                          │       LanguageDef  AST      │  macros/src/ast/language.rs
                          └──────────────┬──────────────┘
                                         │  prattail_bridge.rs
                                         ▼
                          ┌─────────────────────────────┐
                          │       LanguageSpec          │  prattail/src/lib.rs
                          │  (categories + rules +      │
                          │   classify flags)           │
                          └──────────────┬──────────────┘
                            ┌────────────┴────────────┐
                            ▼                         ▼
                 ┌──────────────────────┐  ┌──────────────────────┐
                 │   Lexer Generation   │  │  Parser Generation   │
                 │ NFA → DFA → Minimize │  │ FIRST/FOLLOW → Pratt │
                 │ → direct-coded lexer │  │ + RD → trampoline    │
                 └──────────┬───────────┘  └──────────┬───────────┘
                            │  prattail/src/automata/ │  prattail/src/
                            └───────────→┬←───────────┘
                                         ▼
                          ┌─────────────────────────────┐
                          │   Ascent Datalog Codegen    │  macros/src/logic/
                          │  relations, category rules, │
                          │  equations, rewrites, folds │
                          └──────────────┬──────────────┘
                                         │
                                         ▼
                          ┌─────────────────────────────┐
                          │   Generated Rust Code       │
                          │  Token enum, lexer, parser, │
                          │  AST enums, Ascent struct,  │
                          │  Language trait impl        │
                          └──────────────┬──────────────┘
                                         │
                                         ▼
                ┌──────────────────────────────────────────────────┐
                │              Runtime Evaluation                  │
                │  source → lex → parse → normalize → Ascent →     │
                │  extract results (rewrites, equivalences, folds) │
                └──────────────────────────────────────────────────┘
                                runtime/ + repl/
```

## Crate Map

| Crate         | Path         | Role                                                                                                                      |
|---------------|--------------|---------------------------------------------------------------------------------------------------------------------------|
| **macros**    | `macros/`    | `language!` proc-macro, DSL parsing (`ast/`), bridge to PraTTaIL, Ascent codegen (`logic/`), AST enum generation (`gen/`) |
| **prattail**  | `prattail/`  | Lexer + parser generation engine: automata pipeline, FIRST/FOLLOW, Pratt BP, trampoline codegen                           |
| **runtime**   | `runtime/`   | Runtime types: `Term`, `Language`, `AscentResults`, `HashBag`, bindings, `CanonicalFloat64`                               |
| **languages** | `languages/` | Language definitions (`rhocalc.rs`, `calculator.rs`, ...) and generated code                                              |
| **repl**      | `repl/`      | Interactive evaluation loop, pretty printing, history, environment                                                        |
| **query**     | `query/`     | Runtime query parsing and execution against `AscentResults`                                                               |

## Reading Guide

| File                                                 | Topic                      | Key Question Answered                                        |
|------------------------------------------------------|----------------------------|--------------------------------------------------------------|
| [01-language-spec.md](01-language-spec.md)           | The `language!` DSL        | How is RhoCalc **defined**?                                  |
| [02-macro-expansion.md](02-macro-expansion.md)       | LanguageDef → LanguageSpec | How does the DSL become data the code generator can consume? |
| [03-lexer-generation.md](03-lexer-generation.md)     | Automata pipeline          | How are terminals turned into a fast lexer?                  |
| [04-parser-generation.md](04-parser-generation.md)   | PraTTaIL parser            | How is the parser constructed from grammar rules?            |
| [05-ascent-codegen.md](05-ascent-codegen.md)         | Ascent Datalog rules       | How are semantic rules compiled to a fixpoint engine?        |
| [06-runtime-evaluation.md](06-runtime-evaluation.md) | End-to-end execution       | What happens when you type `3 + 4` in the REPL?              |

## Running Example

Throughout these documents we trace several expressions:

- **`3 + 4`** — arithmetic fold (simplest path through the pipeline)
- **`{ @({}) ! ({}) | *(@({})) }`** — communication rule (Comm), the core rho-calculus reduction
- **`@(*(@({})))`** — the QuoteDrop equation (structural equivalence)

These are real RhoCalc programs that you can evaluate in the REPL:

```
$ cargo run --bin mettail-repl
> lang rhocalc
> exec 3 + 4
```
