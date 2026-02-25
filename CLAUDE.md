# CLAUDE.md - MeTTaIL Rust Project Guide

## Project Overview

MeTTaIL is a **meta-language framework** in Rust for defining formal languages via a `language!` macro. It auto-generates parsers, AST types, substitution logic, and a Datalog-based rewrite engine. The primary use case is the **rho-calculus** (the concurrent language behind [f1r3fly](https://github.com/F1R3FLY-io)).

## Quick Start

```bash
# Requires Rust nightly (auto-configured by rust-toolchain.toml)
cargo run                  # Launch the REPL
cargo run -- rhocalc       # Launch REPL with RhoCalc pre-loaded
cargo test                 # Run all tests
cargo test -p mettail-languages  # Run language-specific tests
```

Dev builds use **Cranelift** for fast compilation; release builds use LLVM.

## Workspace Crates

| Crate | Path | Purpose |
|-------|------|---------|
| `mettail-macros` | `macros/` | The `language!` procedural macro - parses DSL, generates all code |
| `mettail-runtime` | `runtime/` | Runtime traits (`Language`, `Term`), `HashBag`, `Scope`, `CanonicalFloat64` |
| `mettail-languages` | `languages/` | Language definitions (RhoCalc, Calculator, Ambient, Lambda) + tests |
| `mettail-repl` | `repl/` | Interactive REPL binary with command loop and examples |
| `prattail` | `prattail/` | Custom Pratt + Recursive Descent parser generator |
| `ascent_syntax_export` | `ascent_syntax_export/` | Vendored Ascent parser for code gen |
| `query` | `query/` | Runtime Datalog-style query executor |

## Key Dependencies

- **ascent** - Datalog engine (bottom-up evaluation to fixpoint)
- **moniker** - Variable binding with alpha-equivalence
- **syn/quote** - Proc macro parsing and code generation
- **rustyline** - REPL line editing

## Architecture Flow

```
language! { ... }  -->  macros/src/ast/   (parse DSL)
                   -->  macros/src/gen/   (generate AST enums, parser, Display, subst)
                   -->  macros/src/logic/ (generate Ascent Datalog rules)
                   -->  runtime/          (Language + Term traits implemented)
                   -->  repl/             (interactive exploration)
```

## Conventions

- Language definitions live in `languages/src/` (one file per language)
- Generated Datalog code goes to `languages/src/generated/`
- Tests go in `languages/tests/` (integration) or inline (unit)
- The `language!` macro is the single source of truth for a language definition
- Variable binding uses `moniker` with thread-local caching (`clear_var_cache()` between tests)

---

# Tutorial: MeTTaIL for Rust Newcomers

A structured learning path from zero Rust to contributing to MeTTaIL. Each module builds on the previous. Full tutorial content is in [`docs/tutorial/`](docs/tutorial/).

| Module | File | Topic |
|--------|------|-------|
| 1 | [01-rust-foundations.md](docs/tutorial/01-rust-foundations.md) | Rust prerequisites: ownership, enums, traits, pattern matching |
| 2 | [02-big-picture.md](docs/tutorial/02-big-picture.md) | What MeTTaIL does, rho-calculus, the `language!` macro |
| 3 | [03-runtime-layer.md](docs/tutorial/03-runtime-layer.md) | `Language`/`Term` traits, `HashBag`, `Scope`, var cache |
| 4 | [04-calculator-language.md](docs/tutorial/04-calculator-language.md) | First complete language: term syntax, eval, congruence |
| 5 | [05-rhocalc-language.md](docs/tutorial/05-rhocalc-language.md) | Full complexity: binding, collections, COMM, equations |
| 6 | [06-procedural-macros.md](docs/tutorial/06-procedural-macros.md) | How `language!` generates code (macros crate) |
| 7 | [07-prattail-parser.md](docs/tutorial/07-prattail-parser.md) | Pratt + Recursive Descent parser generator |
| 8 | [08-ascent-datalog.md](docs/tutorial/08-ascent-datalog.md) | Term rewriting as Datalog fixpoint computation |
| 9 | [09-repl.md](docs/tutorial/09-repl.md) | Interactive REPL: commands, state, extending |
| 10 | [10-contributing.md](docs/tutorial/10-contributing.md) | Making your first change, common pitfalls, TODO list |

---

## Appendix A: Glossary

| Term | Meaning |
|------|---------|
| **AST** | Abstract Syntax Tree - the in-memory representation of parsed code |
| **Ascent** | A Rust Datalog engine used for term rewriting |
| **Alpha-equivalence** | Two terms are equal if they differ only in bound variable names |
| **Binder / Scope** | A variable binding construct: `^x.body` binds `x` in `body` |
| **Category / Type** | A sort in the language (e.g., `Proc`, `Name`, `Int`) |
| **Congruence rule** | If `S ~> T`, then `f(S) ~> f(T)` - rewrites propagate through constructors |
| **COMM rule** | The communication rule of rho-calculus: send meets receive |
| **Datalog** | A logic programming language for computing relations to fixpoint |
| **Equation** | A structural equality axiom (e.g., `@(*(n)) = n`) |
| **Extrusion** | Moving a `new` binder outward past parallel composition |
| **Fixpoint** | The state where no new facts can be derived - computation is done |
| **HashBag** | A multiset (bag) - like a set but elements can appear multiple times |
| **Moniker** | A Rust library for correct variable binding with alpha-equivalence |
| **Normal form** | A term with no applicable rewrites - it's fully reduced |
| **PraTTaIL** | The custom Pratt + Recursive Descent parser generator in this project |
| **Proc macro** | A Rust procedural macro that transforms code at compile time |
| **Rewrite rule** | A directed reduction: `lhs ~> rhs` |
| **Rho-calculus** | A concurrent process algebra with quoting/unquoting |
| **Scope extrusion** | `{ new(x) in { P } | Q }` = `new(x) in { { P | Q } }` when `x` not free in `Q` |

## Appendix B: Key Command Reference

```
cargo run                           # Start REPL
cargo run -- rhocalc                # Start with RhoCalc loaded
cargo test                          # All tests
cargo test -p mettail-languages     # Language tests only
cargo test -p prattail              # Parser tests only
cargo bench -p mettail-languages    # Benchmarks
cargo doc --open                    # Generated API docs
```

## Appendix C: REPL Commands Quick Reference

```
help              Show all commands
lang <name>       Load a language (rhocalc, calculator, ambient, lambda)
exec <term>       Parse and fully evaluate a term
step <term>       Single-step evaluation
rewrites          Show rewrites from current term
apply <n>         Apply rewrite number n
goto <n>          Jump to history entry n
env               List environment bindings
assign x = expr   Define a variable
typeof <term>     Show inferred type
normal-forms      Show all normal forms from last execution
equations         Show equivalence classes
relations         List custom Datalog relations
relation <name>   Show contents of a relation
query ...         Run a custom Datalog query
example <name>    Load a predefined example
list-examples     Show available examples
```
