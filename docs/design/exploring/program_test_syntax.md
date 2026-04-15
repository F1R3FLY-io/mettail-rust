# Design Proposal: `program { }` Block within `tests { }`

## Status

**Proposal** — documentation only. This does NOT modify `macros/src/ast/language.rs`.

## Motivation

The `tests { }` block (see `test_block_syntax.md`) handles single-expression test
cases. However, many interesting language behaviors emerge from multi-step programs
with environment state:

- **Variable binding**: `let x = 1 + 2; eval x` should yield `3`
- **Multi-step reduction**: `for(x <- @0) { *x } | @0!(1 + 2)` requires multiple
  rewrites to reach a normal form
- **Environment interactions**: substitution of env-bound variables into terms
- **Channel communication**: Rholang-style message passing requires source + sink
- **Import chains**: testing `extends`/`includes`/`mixins` composition

These scenarios cannot be expressed as single roundtrip or eval assertions.

## Proposed Syntax

```text
language! {
    name: RhoCalc,
    // ... types, terms, equations, rewrites ...

    tests {
        // Single-expression tests (from test_block_syntax.md)
        roundtrip "0" : Int;
        eval "1 + 2" : Int => "3";

        // Multi-step program tests
        program "basic_communication" {
            // Each line is a REPL-style command
            let x = "1 + 2" : Int;
            assert_eq x "3";

            let p = "for (y <- @0) { *y }" : Proc;
            let q = "@0!(1 + 2)" : Proc;
            let system = "({p} | {q})" : Proc;

            // Run Ascent and check normal form
            run system;
            assert_normal_form "3";
        }

        program "scope_extrusion" {
            let p = "new x in (*x | @0!(*x))" : Proc;
            run p;
            // After scope extrusion: new x in (... | @0!(*x))
            // should reduce via comm + exec
            assert_rewrites_applied >= 1;
        }

        program "environment_binding" {
            env x = "42" : Int;
            eval "x + 1" : Int => "43";

            env y = "true" : Bool;
            eval "if y then 1 else 0" : Int => "1";
        }

        program "multi_step_lambda" {
            let id = "lam x. x" : Term;
            let app = "(id, 42)" : Term;
            run app;
            assert_normal_form "42";
        }
    }
}
```

## Syntax Grammar (EBNF)

```ebnf
program_block  = "program" STRING "{" program_stmt* "}" ;

program_stmt   = let_stmt | env_stmt | run_stmt | assert_stmt | eval_stmt ;

let_stmt       = "let" IDENT "=" STRING ":" IDENT ";" ;
env_stmt       = "env" IDENT "=" STRING ":" IDENT ";" ;
run_stmt       = "run" IDENT ";" ;
eval_stmt      = "eval" STRING ":" IDENT "=>" STRING ";" ;

assert_stmt    = assert_eq_stmt | assert_nf_stmt | assert_rewrites_stmt ;
assert_eq_stmt      = "assert_eq" IDENT STRING ";" ;
assert_nf_stmt      = "assert_normal_form" STRING ";" ;
assert_rewrites_stmt = "assert_rewrites_applied" CMP_OP INT ";" ;

CMP_OP = ">=" | "<=" | "==" | ">" | "<" ;
```

### String interpolation

Within program strings, `{ident}` refers to a previously bound variable.
This enables building composite terms from named components.

## Code Generation

Each `program` block generates a `#[test]` function that:

1. Creates a language instance (`let lang = {Lang}Language;`)
2. Creates a mutable environment (`let mut env = lang.create_env();`)
3. For each `let`:
   - Parses the string into a term
   - Stores in a local `HashMap<String, Box<dyn Term>>`
   - Optionally evaluates via `run_ascent`
4. For each `env`:
   - Parses the string and adds to the language environment
   - Calls `lang.add_to_env(&mut env, name, &term)`
5. For each `run`:
   - Calls `lang.run_ascent(term)` on the named variable
   - Stores the `AscentResults` for subsequent assertions
6. For each `assert`:
   - `assert_eq`: displays the variable and compares to expected string
   - `assert_normal_form`: checks that the latest `run` produced the expected NF
   - `assert_rewrites_applied`: checks the rewrite count against the comparison

## Implementation Strategy

1. Add `ProgramBlock` and `ProgramStmt` to `macros/src/ast/language.rs`
2. Parse `program` blocks inside `tests { }` in the test block parser
3. Create `macros/src/gen/test_gen/program_tests.rs` to generate code
4. Each program becomes a sequential test with local state
5. String interpolation is resolved at codegen time by substituting
   variable references with `format!("{}", var_name)`

## Integration with `ProgramTestSuite`

The `testkit` crate already has a `ProgramTestSuite` builder at
`testkit/src/program.rs`. The generated program tests should use this builder
rather than generating inline code, to keep the generated test files small
and leverage the testkit's assertion infrastructure:

```rust
#[test]
fn program_basic_communication() {
    let suite = mettail_testkit::program::ProgramTestSuite::new(RhoCalcLanguage);
    suite
        .bind("x", "1 + 2", "Int")
        .assert_eq("x", "3")
        .bind("p", "for (y <- @0) { *y }", "Proc")
        .bind("q", "@0!(1 + 2)", "Proc")
        .run_composite("({p} | {q})", "Proc")
        .assert_normal_form("3")
        .execute()
        .expect("program test failed");
}
```

## Relationship to `tests { }`

`program { }` blocks appear INSIDE `tests { }`. They are distinguished from
simple test items by the `program` keyword. A `tests { }` block can contain
any mix of simple tests and program tests:

```text
tests {
    roundtrip "0" : Int;           // simple
    program "my_scenario" { ... }  // multi-step
    eval "1 + 2" : Int => "3";    // simple
    program "another" { ... }      // multi-step
}
```

## Non-Goals

- **Concurrent program testing**: testing parallel channel communication
  with specific scheduling is out of scope. That requires the scheduler
  infrastructure from `prattail::scheduler`.
- **Exhaustive state space exploration**: programs are executed once
  (not model-checked). For exhaustive testing, use the analytical modules
  (CESK coverage, LTL model checking).
- **Performance benchmarking**: program tests are functional, not performance.
  Use `criterion` benchmarks for timing.

## Compatibility

The `program` blocks within `tests { }` are optional. Languages without them
continue to get all auto-generated tests plus any simple test items. Both the
`tests { }` block and `program { }` blocks within it are backward-compatible
additions to the `language!` macro.
