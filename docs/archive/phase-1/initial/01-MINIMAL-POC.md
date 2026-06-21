# Minimal Proof-of-Concept: MeTTaIL Rust Macros

## Goal

Demonstrate the **core feasibility** of implementing MeTTaIL as Rust procedural macros by building the smallest possible working example that proves the concept.

---

## POC Scope: The Absolute Minimum

### What We'll Build

A single theory with minimal features:

```rust
theory! {
    name: SimpleMonoid,

    exports {
        Elem;
    }

    terms {
        Zero . Elem ::= "0";
        Plus . Elem ::= Elem "+" Elem;
    }
}
```

**Generated Output:**
1. AST enum for `Elem`
2. Parser for the grammar
3. Basic validation (compile-time check that terms reference exported categories)

### What We'll Prove

✅ **Procedural macros can parse theory syntax**
✅ **Can generate AST types**
✅ **Can perform compile-time validation**
✅ **Generated code integrates with Rust**

### What We'll Defer

⏸️ Theory composition (conjunction/disjunction)
⏸️ Equations and rewrites
⏸️ Parameterized theories
⏸️ Replacements and binders
⏸️ Network serialization
⏸️ Full interpreter generation

---

## Implementation Plan

### Phase 1: Project Setup (1 hour)

Create workspace structure:
```
mettail-rust-exploration/
├── macros/       # Procedural macro crate
├── runtime/      # Runtime support library
├── examples/             # Example usage
└── docs/                 # Documentation
```

**Deliverable:** Compiling empty crates

### Phase 2: Minimal Macro (4-6 hours)

**File:** `macros/src/lib.rs`

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Ident};

#[proc_macro]
pub fn theory(input: TokenStream) -> TokenStream {
    let theory_def = parse_macro_input!(input as TheoryDef);

    // Validate at compile time
    validate_theory(&theory_def)
        .unwrap_or_else(|e| panic!("Theory validation failed: {}", e));

    // Generate code
    let ast_types = generate_ast(&theory_def);

    quote! {
        #ast_types
    }
    .into()
}

struct TheoryDef {
    name: Ident,
    exports: Vec<Ident>,
    terms: Vec<GrammarRule>,
}

struct GrammarRule {
    label: Ident,
    category: Ident,
    items: Vec<GrammarItem>,
}

enum GrammarItem {
    Terminal(String),
    NonTerminal(Ident),
}
```

**What it does:**
1. Parses `theory! { ... }` blocks
2. Validates categories are exported
3. Generates Rust enum for each category

**Deliverable:** Macro that generates AST types

### Phase 3: Validation (2 hours)

Add compile-time checks:

```rust
fn validate_theory(theory: &TheoryDef) -> Result<(), String> {
    // Check: all referenced categories are exported
    let exported: HashSet<_> = theory.exports.iter().collect();

    for rule in &theory.terms {
        if !exported.contains(&rule.category) {
            return Err(format!(
                "Category '{}' in rule '{}' is not exported",
                rule.category, rule.label
            ));
        }

        for item in &rule.items {
            if let GrammarItem::NonTerminal(cat) = item {
                if !exported.contains(cat) {
                    return Err(format!(
                        "Category '{}' referenced but not exported",
                        cat
                    ));
                }
            }
        }
    }

    Ok(())
}
```

**Test Cases:**
```rust
// Should compile
theory! {
    name: Valid,
    exports { Elem; }
    terms {
        Zero . Elem ::= "0";
    }
}

// Should FAIL to compile
theory! {
    name: Invalid,
    exports { Elem; }
    terms {
        // ERROR: Name not exported
        Quote . Name ::= "@" Elem;
    }
}
```

**Deliverable:** Compile-time validation with clear error messages

### Phase 4: Code Generation (3-4 hours)

Generate AST enums:

```rust
fn generate_ast(theory: &TheoryDef) -> proc_macro2::TokenStream {
    let mut enums = Vec::new();

    for cat in &theory.exports {
        let variants = theory.terms
            .iter()
            .filter(|r| r.category == *cat)
            .map(|rule| {
                let label = &rule.label;
                let fields = rule.items
                    .iter()
                    .filter_map(|item| match item {
                        GrammarItem::NonTerminal(t) => Some(t),
                        _ => None,
                    })
                    .collect::<Vec<_>>();

                if fields.is_empty() {
                    quote! { #label }
                } else {
                    quote! { #label(#(#fields),*) }
                }
            });

        enums.push(quote! {
            #[derive(Debug, Clone, PartialEq)]
            pub enum #cat {
                #(#variants),*
            }
        });
    }

    quote! {
        #(#enums)*
    }
}
```

**Generated Output:**
```rust
// From SimpleMonoid theory
#[derive(Debug, Clone, PartialEq)]
pub enum Elem {
    Zero,
    Plus(Elem, Elem),
}
```

**Deliverable:** Working AST generation

### Phase 5: Example Usage (1 hour)

Create example that uses the generated code:

```rust
// examples/simple_monoid.rs
use mettail_macros::theory;

theory! {
    name: SimpleMonoid,

    exports {
        Elem;
    }

    terms {
        Zero . Elem ::= "0";
        Plus . Elem ::= Elem "+" Elem;
    }
}

fn main() {
    // Use the generated AST
    let expr = Elem::Plus(
        Box::new(Elem::Zero),
        Box::new(Elem::Zero),
    );

    println!("Expression: {:?}", expr);
}
```

**Deliverable:** Runnable example

---

## Timeline

**Total Estimated Time:** 11-14 hours

| Phase | Time | Cumulative |
|-------|------|------------|
| Setup | 1h | 1h |
| Minimal Macro | 4-6h | 5-7h |
| Validation | 2h | 7-9h |
| Code Generation | 3-4h | 10-13h |
| Example | 1h | 11-14h |

**Target:** Complete POC in 1-2 days of focused work

---

## Success Metrics

### Must Have ✅
- [ ] `theory! {}` macro compiles successfully
- [ ] Generates valid Rust AST enums
- [ ] Compile-time error for invalid category reference
- [ ] Example code runs and uses generated types

### Nice to Have 🎯
- [ ] Parser for subset of `.module` file syntax
- [ ] Pretty error messages with span information
- [ ] Basic documentation
- [ ] Unit tests for validation logic

### Out of Scope ⛔
- Full parser generation (LALRPOP integration)
- Interpreter generation
- Rewrite rules
- Theory composition
- Network serialization

---

## File Structure

```
mettail-rust-exploration/
├── 00-PROJECT-UNDERSTANDING.md     (this file)
├── 01-MINIMAL-POC.md               (implementation plan)
│
├── macros/
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs                   (proc macro entry point)
│       ├── parser.rs                (parse theory! syntax)
│       ├── validator.rs             (compile-time checks)
│       └── codegen.rs               (generate AST types)
│
├── runtime/
│   ├── Cargo.toml
│   └── src/
│       └── lib.rs                   (runtime support, if needed)
│
├── examples/
│   ├── simple_monoid.rs
│   └── category_check.rs            (compile-fail test)
│
└── Cargo.toml                       (workspace)
```

---

## Workspace Cargo.toml

```toml
[workspace]
members = ["macros", "runtime", "examples"]
resolver = "2"

[workspace.dependencies]
proc-macro2 = "1.0"
quote = "1.0"
syn = { version = "2.0", features = ["full", "extra-traits"] }
```

---

## Next Step: Code Implementation

See `02-IMPLEMENTATION-GUIDE.md` for step-by-step coding instructions.

---

## Validation Criteria

Before considering POC complete, verify:

1. **Macro works:**
   ```bash
   cargo build --all
   cargo run --example simple_monoid
   ```

2. **Validation works:**
   - Change `simple_monoid.rs` to reference non-exported category
   - Should get compile error with clear message

3. **Generated code is idiomatic:**
   - Run `cargo clippy`
   - No warnings in generated code

4. **Documentation exists:**
   - README explaining what was built
   - Comments in macro code
   - Example with output

---

## Decision Points

After POC completion, decide:

### ✅ Continue with Macros?
**If YES:** Expand to full features (rewrites, composition, etc.)
**If NO:** Fall back to LALRPOP + runtime interpreter

### Evaluation Criteria:
- **Complexity:** Is the macro code manageable?
- **Ergonomics:** Is the `theory! {}` syntax pleasant?
- **Error Messages:** Are compile errors understandable?
- **Performance:** How fast is macro expansion?
- **Team Comfort:** Do developers feel confident extending it?

---

## Alternative: Hybrid Approach

If pure macros prove too complex, consider:

1. **Macro for simple theories** - Single, non-parameterized theories
2. **Runtime for complex theories** - Composition, parameterization
3. **Translator** - Convert `.module` to Rust at build time (build.rs)

---

## Risk Mitigation

### Risk 1: Macros too complex
**Mitigation:** POC reveals complexity early; can pivot to simpler approach

### Risk 2: Poor error messages
**Mitigation:** Use `proc_macro_error` crate, invest in span tracking

### Risk 3: Integration friction
**Mitigation:** Generate standard Rust idioms, no exotic patterns

### Risk 4: Compilation time
**Mitigation:** Measure from start, cache generated code if needed

---

## Resources for Implementation

### Procedural Macros
- [Rust Macros Book](https://veykril.github.io/tlborm/)
- [syn documentation](https://docs.rs/syn/)
- [quote documentation](https://docs.rs/quote/)

### Example Projects
- `serde_derive` - Good model for derive macros
- `diesel` - Complex query DSL macros
- `rocket` - Route macro examples

### Testing
- [trybuild](https://docs.rs/trybuild/) - Compile-fail tests
- [macrotest](https://docs.rs/macrotest/) - Macro expansion tests

---

## Conclusion

This POC focuses on **proving feasibility** with the simplest possible implementation. Success means we can confidently proceed to full implementation. Failure means we learn early and can adjust approach.

**Next Action:** Begin Phase 1 (Project Setup) - see `02-IMPLEMENTATION-GUIDE.md`

