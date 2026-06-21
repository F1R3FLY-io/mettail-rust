# Phase 2: Quick Start Guide for Next Session

## 🎯 Current Status

**Completed:** ✅ LALRPOP integration, grammar generation module, comprehensive tests
**Next:** 🎯 Binder handling, file I/O, parser integration

---

## 📂 Key Files

### Core Implementation
- `macros/src/lalrpop_gen.rs` - Grammar generation logic
- `runtime/build.rs` - LALRPOP build integration
- `runtime/src/lib.rs` - Runtime exports

### Tests
- `macros/src/lalrpop_gen.rs` - Unit tests (5 tests)
- `theories/grammar_test.rs` - Integration tests (3 theories)
- `runtime/tests/lalrpop_integration.rs` - Integration test

### Documentation
- `docs/phase-2/SESSION-SUMMARY.md` - Full session summary
- `docs/phase-2/WEEK-1-PROGRESS.md` - Week 1 progress
- `docs/phase-2/LALRPOP-DESIGN.md` - Architecture docs
- `docs/ROADMAP.md` - Updated roadmap

---

## 🔧 Quick Commands

```bash
# Run all grammar generation tests
cargo test --package macros --lib lalrpop_gen

# See test output
cargo test --package macros --lib lalrpop_gen -- --nocapture

# Run example theories
cargo run --bin grammar_test

# Run Rho Calculus
cargo run --bin rhocalc

# Check all tests
cargo test
```

---

## 🎯 Next Priorities (In Order)

### 1. Binder Syntax (HIGH PRIORITY)
**File:** `macros/src/lalrpop_gen.rs`
**Function:** `generate_rule_alternative()` and `generate_sequence_alternative()`
**Task:** Generate `Scope::new(Binder(...), body)` for binder rules

**Example:**
```rust
// Input: PInput . Proc ::= "for" "(" Name <Name> ")" "{" Proc "}" ;

// Need to generate:
"for" "(" <ch:Name> <x:Ident> ")" "{" <body:Proc> "}"
=> Proc::PInput(
    Box::new(ch),
    Scope::new(
        Binder(FreeVar::fresh_named(x)),
        Box::new(body)
    )
)
```

### 2. Precedence Detection (MEDIUM PRIORITY)
**File:** `macros/src/lalrpop_gen.rs`
**Task:** Detect infix operators, generate tiered grammar

**Example:**
```rust
// Detect that PPar uses "|" infix
// Generate:
pub Proc: Proc = { <Proc1> };
Proc1: Proc = {  // Tier 1: Low precedence
    <l:Proc1> "|" <r:Proc2> => ...,
    <Proc2>,
};
Proc2: Proc = {  // Tier 2: High precedence (atoms)
    "0" => ...,
    "(" <Proc> ")",
};
```

### 3. File I/O Integration (HIGH PRIORITY)
**Task:** Write generated `.lalrpop` files during macro expansion or build

**Options:**
- **A:** Write in proc macro (during `theory!` expansion)
- **B:** Write in build script (during `cargo build`)
- **C:** Write in separate tool (run manually)

**Recommendation:** Option B (build script approach)

### 4. Test with Rho Calculus (NEXT TEST)
**File:** Create `theories/rho_parse_test.rs`
**Task:** Generate grammar for full Rho Calculus, verify syntax

---

## 🐛 Known Issues

### Issue 1: Binders Generate Box, Not Scope
**Status:** Known limitation
**Impact:** Can't parse binder syntax yet
**Fix:** Implement Scope generation (Priority #1)

### Issue 2: No Precedence
**Status:** Known limitation
**Impact:** `0 + 1 * 2` parses incorrectly
**Fix:** Implement precedence detection (Priority #2)

### Issue 3: Grammars Not Written to Disk
**Status:** Design phase
**Impact:** Can't actually use generated parsers
**Fix:** Add file I/O (Priority #3)

---

## 📝 Design Decisions to Make

### Decision 1: Where to Write Grammar Files?
**Options:**
- `target/generated/theories/*.lalrpop`
- `runtime/src/parsers/*.lalrpop`
- User's build directory

**Considerations:**
- Build script has access to `OUT_DIR`
- Need to `include!` generated parsers
- Want version control or not?

### Decision 2: How to Handle Name Hints?
**Issue:** Variables are parsed as strings but become FreeVar
**Need:** Preserve names for pretty-printing
**Options:**
- Store name hints in FreeVar (moniker supports this)
- Separate name map
- Add to AST

### Decision 3: Precedence Annotation Syntax?
**Options:**
- **Automatic:** Infer from rule structure
- **Manual:** `@precedence(10, left)` annotation
- **Hybrid:** Infer + allow overrides

---

## 🔍 Testing Strategy

### Unit Tests (Current: 5)
- ✅ Simple grammar generation
- ✅ Multi-terminal grammar
- ✅ Infix operator grammar
- ✅ Variable grammar
- ✅ Header generation

### Integration Tests (Current: 3 theories)
- ✅ SimpleCalc
- ✅ BoolCalc
- ✅ ListTheory

### Next Tests Needed
- ⏭️ Binder grammar (lambda calculus)
- ⏭️ Rho Calculus full grammar
- ⏭️ Precedence (nested expressions)
- ⏭️ Round-trip (parse → print → parse)

---

## 💡 Implementation Hints

### Hint 1: Detecting Binders
```rust
// In generate_sequence_alternative():
if let Some((binder_idx, body_indices)) = &rule.bindings.get(0) {
    // This rule has a binder!
    // Generate Scope creation code
}
```

### Hint 2: Infix Operator Detection
```rust
// Check if rule has form: NonTerm Terminal NonTerm
if rule.items.len() == 3
    && matches!(rule.items[0], GrammarItem::NonTerminal(_))
    && matches!(rule.items[1], GrammarItem::Terminal(_))
    && matches!(rule.items[2], GrammarItem::NonTerminal(_))
{
    // This is an infix operator!
}
```

### Hint 3: File Writing
```rust
// In build.rs or macro:
let grammar_content = generate_lalrpop_grammar(&theory);
let out_dir = std::env::var("OUT_DIR")?;
let path = Path::new(&out_dir).join("theory_name.lalrpop");
std::fs::write(path, grammar_content)?;
```

---

## 🎓 Key Concepts

### LALRPOP Production Format
```lalrpop
pub CategoryName: RustType = {
    pattern => constructor_code,
    pattern => constructor_code,
};
```

### Pattern Syntax
```lalrpop
"literal"              // Match terminal
<var:Type>             // Capture as variable
<l:Type> "+" <r:Type>  // Multiple captures
```

### Action Code
```lalrpop
=> Category::Constructor(args)
=> Box::new(value)
=> Scope::new(binder, body)
```

---

## 📚 Reference

### LALRPOP Documentation
- Tutorial: https://lalrpop.github.io/lalrpop/
- Reference: https://lalrpop.github.io/lalrpop/lexer_tutorial/001_lexer_gen.html

### Moniker Documentation
- Crate: https://docs.rs/moniker/
- BoundTerm: How to create Scopes

### Our Architecture
- See: `docs/phase-2/LALRPOP-DESIGN.md`

---

## ✅ Pre-Session Checklist

Before starting next session:
- [ ] Review SESSION-SUMMARY.md
- [ ] Check current test failures (should be none)
- [ ] Read LALRPOP-DESIGN.md for context
- [ ] Have lalrpop_gen.rs open
- [ ] Have rhocalc.rs open for reference

---

## 🚀 Ready to Start!

**Estimated next session:** 2-3 hours
**Goal:** Binder support + file I/O + Rho Calculus test
**Stretch goal:** Basic parser integration

**Command to start:**
```bash
cargo test --package macros --lib lalrpop_gen -- --nocapture
```

Good luck! 🎉

