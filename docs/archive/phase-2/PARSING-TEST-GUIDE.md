# Testing Actual Parsing - Quick Guide

## What We Just Did

1. ✅ Created `simple_calc.lalrpop` - A real LALRPOP grammar
2. ✅ Updated `lib.rs` to include the generated parser
3. ✅ Created `parsing_tests.rs` - 8 comprehensive tests

## What Happens Next

When you run `cargo build` or `cargo test`:

1. **Build Script Runs** (`build.rs`)
   - LALRPOP finds `simple_calc.lalrpop`
   - Generates Rust parser code
   - Writes to `$OUT_DIR/simple_calc.rs`

2. **Compilation**
   - `lib.rs` includes the generated parser
   - Module `simple_calc` becomes available
   - Parser type: `simple_calc::ExprParser`

3. **Tests Run**
   - Parse "42" → 42
   - Parse "2 + 3" → 5
   - Parse "2 + 3 * 4" → 14 (precedence works!)
   - Error handling tested

## Expected Test Results

All 8 tests should pass:
```
test test_parse_number ... ok
test test_parse_addition ... ok
test test_parse_multiplication ... ok
test test_parse_precedence ... ok
test test_parse_parentheses ... ok
test test_parse_complex_expression ... ok
test test_parse_error ... ok
test test_parse_whitespace ... ok
```

## Linter Errors (Expected)

The linter will show errors until we build:
- ❌ `simple_calc.rs` doesn't exist (yet)
- ✅ This is normal - file is generated at build time

## Next Command

```bash
cargo test --package runtime parsing_tests -- --nocapture
```

This will:
1. Build the runtime (generating the parser)
2. Run the parsing tests
3. Show output with `--nocapture`

## After Success

Once this works, we can:
1. Generate parsers from `theory!` macros
2. Parse Rho Calculus terms
3. Implement round-trip testing (parse → print → parse)

---

**Status:** Ready to build and test actual parsing! 🚀

