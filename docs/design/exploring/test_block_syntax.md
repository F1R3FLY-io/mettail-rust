# Design Proposal: `tests { }` Block Syntax in `language!`

## Status

**Proposal** — documentation only. This does NOT modify `macros/src/ast/language.rs`.

## Motivation

Currently, test generation for `language!` specifications is entirely automatic:
proptest strategies, per-constructor roundtrip tests, equation tests, rewrite tests,
and analytical tests are all derived from the grammar, equations, and rewrites. While
this provides excellent baseline coverage, language authors often need to test specific
scenarios that the auto-generated tests cannot anticipate:

- **Edge cases**: parsing ambiguity, operator precedence with specific operand shapes
- **Semantic invariants**: alpha-equivalence with specific binder configurations
- **Regression tests**: previously-failing inputs that should remain passing
- **Integration scenarios**: multi-step reduction chains

## Proposed Syntax

```text
language! {
    name: Rholang,
    types { ... },
    terms { ... },
    equations { ... },
    rewrites { ... },

    tests {
        // Simple parse-display roundtrip
        roundtrip "0" : Int;
        roundtrip "x + y" : Int;
        roundtrip "for (x <- @0) { *x }" : Proc;

        // Specific parse result assertion
        parse "1 + 2" : Int => (Add (IntLit 1) (IntLit 2));

        // Evaluation assertion
        eval "1 + 2" : Int => "3";
        eval "*@0" : Proc => "0";

        // Equation assertion (both directions)
        equation QuoteDrop => "@*x" = "x";

        // Rewrite assertion (one direction)
        rewrite Exec => "*@P" ~> "P";

        // Alpha-equivalence assertion
        alpha_eq "lam x. x" "lam y. y" : Term;

        // Named test groups
        group "arithmetic" {
            roundtrip "1 + 2 * 3" : Int;
            eval "1 + 2 * 3" : Int => "7";
        }

        // Negative tests (expected parse failure)
        fail_parse "" : Int;
        fail_parse "+" : Int;
    }
}
```

## Syntax Grammar (EBNF)

```ebnf
tests_block    = "tests" "{" test_item* "}" ;
test_item      = roundtrip_test | parse_test | eval_test
               | equation_test | rewrite_test | alpha_eq_test
               | fail_parse_test | group_test ;

roundtrip_test  = "roundtrip" STRING ":" IDENT ";" ;
parse_test      = "parse" STRING ":" IDENT "=>" pattern ";" ;
eval_test       = "eval" STRING ":" IDENT "=>" STRING ";" ;
equation_test   = "equation" IDENT "=>" STRING "=" STRING ";" ;
rewrite_test    = "rewrite" IDENT "=>" STRING "~>" STRING ";" ;
alpha_eq_test   = "alpha_eq" STRING STRING ":" IDENT ";" ;
fail_parse_test = "fail_parse" STRING ":" IDENT ";" ;
group_test      = "group" STRING "{" test_item* "}" ;
```

## Code Generation

Each test item generates a `#[test]` function in the generated test file:

- **`roundtrip`**: generates `parse(input)` + `assert_eq!(display(parsed), input)`
- **`parse`**: generates `parse(input)` + structural equality against pattern
- **`eval`**: generates `parse(input)` + `run_ascent` + normal form check
- **`equation`**: generates both-direction equivalence via `run_ascent`
- **`rewrite`**: generates one-direction rewrite via `run_ascent`
- **`alpha_eq`**: generates `parse` + `assert_alpha_eq` from testkit
- **`fail_parse`**: generates `parse(input)` + `assert!(result.is_err())`
- **`group`**: generates a `mod` block with the group name

## Implementation Strategy

1. Add `TestBlock` and `TestItem` to `macros/src/ast/language.rs` (new AST types)
2. Parse `tests { }` after `rewrites { }` in `LanguageDef::parse()`
3. Add `pub tests: Vec<TestItem>` to `LanguageDef`
4. Create `macros/src/gen/test_gen/user_tests.rs` to generate code from `TestItem`
5. Wire into `generate_test_file()` in `mod.rs`

## Non-Goals

- This proposal does NOT handle program-level tests (multi-step scripts with
  environment state). Those belong in the `program { }` block proposal.
- This proposal does NOT generate proptest strategies from user tests.
  Auto-generated proptests remain separate.

## Compatibility

The `tests { }` block is optional. Languages without it continue to get all
auto-generated tests. The block is parsed after `rewrites { }` (and `logic { }`
if present) and before the closing brace of `language!`.
