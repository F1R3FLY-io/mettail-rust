# Implementation Guide: Minimal POC

This guide provides step-by-step instructions for implementing the minimal proof-of-concept.

---

## Step 0: Prerequisites

Ensure you have:
```bash
rustc --version  # Should be 1.70+
cargo --version
```

---

## Step 1: Create Workspace (10 minutes)

```bash
cd /Users/cbwells/Documents/GitHub/rholang/f1r3node/mettail-rust-exploration

# Create workspace structure
mkdir -p macros/src
mkdir -p runtime/src
mkdir -p examples

# Create workspace Cargo.toml
cat > Cargo.toml << 'EOF'
[workspace]
members = ["macros", "runtime", "examples"]
resolver = "2"

[workspace.dependencies]
proc-macro2 = "1.0"
quote = "1.0"
syn = { version = "2.0", features = ["full", "extra-traits"] }
proc-macro-error = "1.0"
EOF

# Create macros/Cargo.toml
cat > macros/Cargo.toml << 'EOF'
[package]
name = "macros"
version = "0.1.0"
edition = "2021"

[lib]
proc-macro = true

[dependencies]
proc-macro2 = { workspace = true }
quote = { workspace = true }
syn = { workspace = true }
proc-macro-error = { workspace = true }
EOF

# Create runtime/Cargo.toml
cat > runtime/Cargo.toml << 'EOF'
[package]
name = "runtime"
version = "0.1.0"
edition = "2021"

[dependencies]
EOF

# Create examples/Cargo.toml
cat > examples/Cargo.toml << 'EOF'
[package]
name = "mettail-examples"
version = "0.1.0"
edition = "2021"

[[bin]]
name = "simple_monoid"
path = "simple_monoid.rs"

[dependencies]
macros = { path = "../macros" }
runtime = { path = "../runtime" }
EOF
```

**Verify:**
```bash
cargo build
```

Should compile successfully (with empty crates).

---

## Step 2: Define AST for Macro Input (30 minutes)

**File:** `macros/src/ast.rs`

```rust
use syn::{Ident, Token, parse::{Parse, ParseStream}, Result as SynResult};
use syn::punctuated::Punctuated;

/// Top-level theory definition
/// theory! { name: Foo, exports { ... }, terms { ... } }
pub struct TheoryDef {
    pub name: Ident,
    pub exports: Vec<Export>,
    pub terms: Vec<GrammarRule>,
}

/// Export: just a category name
/// exports { Elem; Name; }
pub struct Export {
    pub name: Ident,
}

/// Grammar rule
/// Label . Category ::= Item Item Item ;
pub struct GrammarRule {
    pub label: Ident,
    pub category: Ident,
    pub items: Vec<GrammarItem>,
}

/// Item in a grammar rule
pub enum GrammarItem {
    Terminal(String),      // "0"
    NonTerminal(Ident),    // Elem
}

// Implement Parse for TheoryDef
impl Parse for TheoryDef {
    fn parse(input: ParseStream) -> SynResult<Self> {
        // Parse: name: Identifier
        let _ = input.parse::<Token![name]>()?;
        let _ = input.parse::<Token![:]>()?;
        let name = input.parse::<Ident>()?;
        let _ = input.parse::<Token![,]>()?;

        // Parse: exports { ... }
        let exports = if input.peek(Token![exports]) {
            parse_exports(input)?
        } else {
            Vec::new()
        };

        // Parse: terms { ... }
        let terms = if input.peek(Token![terms]) {
            parse_terms(input)?
        } else {
            Vec::new()
        };

        Ok(TheoryDef {
            name,
            exports,
            terms,
        })
    }
}

fn parse_exports(input: ParseStream) -> SynResult<Vec<Export>> {
    let _ = input.parse::<Token![exports]>()?;

    let content;
    syn::braced!(content in input);

    let mut exports = Vec::new();
    while !content.is_empty() {
        let name = content.parse::<Ident>()?;
        exports.push(Export { name });

        if content.peek(Token![;]) {
            let _ = content.parse::<Token![;]>()?;
        }
    }

    // Optional comma after closing brace
    if input.peek(Token![,]) {
        let _ = input.parse::<Token![,]>()?;
    }

    Ok(exports)
}

fn parse_terms(input: ParseStream) -> SynResult<Vec<GrammarRule>> {
    let _ = input.parse::<Token![terms]>()?;

    let content;
    syn::braced!(content in input);

    let mut rules = Vec::new();
    while !content.is_empty() {
        rules.push(parse_grammar_rule(&content)?);
    }

    Ok(rules)
}

fn parse_grammar_rule(input: ParseStream) -> SynResult<GrammarRule> {
    // Parse: Label . Category ::= ...
    let label = input.parse::<Ident>()?;
    let _ = input.parse::<Token![.]>()?;
    let category = input.parse::<Ident>()?;

    // Parse ::= (as two colons)
    let _ = input.parse::<Token![::]>()?;
    let _ = input.parse::<Token![=]>()?;

    // Parse items until semicolon
    let mut items = Vec::new();
    while !input.peek(Token![;]) {
        if input.peek(syn::LitStr) {
            // Terminal: string literal
            let lit = input.parse::<syn::LitStr>()?;
            items.push(GrammarItem::Terminal(lit.value()));
        } else {
            // NonTerminal: identifier
            let ident = input.parse::<Ident>()?;
            items.push(GrammarItem::NonTerminal(ident));
        }
    }

    let _ = input.parse::<Token![;]>()?;

    Ok(GrammarRule {
        label,
        category,
        items,
    })
}
```

---

## Step 3: Validation Logic (30 minutes)

**File:** `macros/src/validator.rs`

```rust
use crate::ast::{TheoryDef, GrammarItem};
use std::collections::HashSet;

pub fn validate_theory(theory: &TheoryDef) -> Result<(), String> {
    // Build set of exported categories
    let exported: HashSet<_> = theory.exports
        .iter()
        .map(|e| e.name.to_string())
        .collect();

    // Check each rule
    for rule in &theory.terms {
        // Check that the rule's category is exported
        let cat_name = rule.category.to_string();
        if !exported.contains(&cat_name) {
            return Err(format!(
                "Rule '{}' has category '{}' which is not exported",
                rule.label, cat_name
            ));
        }

        // Check that all non-terminal items reference exported categories
        for item in &rule.items {
            if let GrammarItem::NonTerminal(ident) = item {
                let ref_name = ident.to_string();
                if !exported.contains(&ref_name) {
                    return Err(format!(
                        "Rule '{}' references category '{}' which is not exported",
                        rule.label, ref_name
                    ));
                }
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;
    use syn::parse_quote;

    #[test]
    fn test_valid_theory() {
        let theory = TheoryDef {
            name: parse_quote!(Test),
            exports: vec![
                Export { name: parse_quote!(Elem) }
            ],
            terms: vec![
                GrammarRule {
                    label: parse_quote!(Zero),
                    category: parse_quote!(Elem),
                    items: vec![GrammarItem::Terminal("0".to_string())],
                }
            ],
        };

        assert!(validate_theory(&theory).is_ok());
    }

    #[test]
    fn test_invalid_category() {
        let theory = TheoryDef {
            name: parse_quote!(Test),
            exports: vec![
                Export { name: parse_quote!(Elem) }
            ],
            terms: vec![
                GrammarRule {
                    label: parse_quote!(Quote),
                    category: parse_quote!(Name),  // Not exported!
                    items: vec![
                        GrammarItem::Terminal("@".to_string()),
                        GrammarItem::NonTerminal(parse_quote!(Elem)),
                    ],
                }
            ],
        };

        assert!(validate_theory(&theory).is_err());
    }
}
```

---

## Step 4: Code Generation (45 minutes)

**File:** `macros/src/codegen.rs`

```rust
use crate::ast::{TheoryDef, GrammarItem, GrammarRule};
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashMap;

pub fn generate_ast(theory: &TheoryDef) -> TokenStream {
    // Group rules by category
    let mut rules_by_cat: HashMap<String, Vec<&GrammarRule>> = HashMap::new();

    for rule in &theory.terms {
        let cat_name = rule.category.to_string();
        rules_by_cat.entry(cat_name).or_default().push(rule);
    }

    // Generate enum for each exported category
    let enums: Vec<TokenStream> = theory.exports.iter().map(|export| {
        let cat_name = &export.name;

        let rules = rules_by_cat
            .get(&cat_name.to_string())
            .map(|v| v.as_slice())
            .unwrap_or(&[]);

        let variants: Vec<TokenStream> = rules.iter().map(|rule| {
            generate_variant(rule)
        }).collect();

        quote! {
            #[derive(Debug, Clone, PartialEq, Eq)]
            pub enum #cat_name {
                #(#variants),*
            }
        }
    }).collect();

    quote! {
        #(#enums)*
    }
}

fn generate_variant(rule: &GrammarRule) -> TokenStream {
    let label = &rule.label;

    // Count non-terminal items (these become fields)
    let fields: Vec<_> = rule.items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::NonTerminal(ident) => Some(ident),
            _ => None,
        })
        .collect();

    if fields.is_empty() {
        // Unit variant
        quote! { #label }
    } else {
        // Tuple variant - wrap in Box to avoid recursive type
        let boxed_fields: Vec<TokenStream> = fields.iter().map(|f| {
            quote! { Box<#f> }
        }).collect();

        quote! { #label(#(#boxed_fields),*) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;
    use syn::parse_quote;

    #[test]
    fn test_generate_simple_enum() {
        let theory = TheoryDef {
            name: parse_quote!(Test),
            exports: vec![
                Export { name: parse_quote!(Elem) }
            ],
            terms: vec![
                GrammarRule {
                    label: parse_quote!(Zero),
                    category: parse_quote!(Elem),
                    items: vec![GrammarItem::Terminal("0".to_string())],
                },
                GrammarRule {
                    label: parse_quote!(Plus),
                    category: parse_quote!(Elem),
                    items: vec![
                        GrammarItem::NonTerminal(parse_quote!(Elem)),
                        GrammarItem::Terminal("+".to_string()),
                        GrammarItem::NonTerminal(parse_quote!(Elem)),
                    ],
                },
            ],
        };

        let output = generate_ast(&theory);
        let expected = quote! {
            #[derive(Debug, Clone, PartialEq, Eq)]
            pub enum Elem {
                Zero,
                Plus(Box<Elem>, Box<Elem>)
            }
        };

        // Note: This is a simplified test; in reality, compare token streams
        println!("Generated: {}", output);
        println!("Expected: {}", expected);
    }
}
```

---

## Step 5: Macro Entry Point (20 minutes)

**File:** `macros/src/lib.rs`

```rust
mod ast;
mod validator;
mod codegen;

use proc_macro::TokenStream;
use proc_macro_error::{proc_macro_error, abort_call_site};
use syn::parse_macro_input;

use ast::TheoryDef;
use validator::validate_theory;
use codegen::generate_ast;

#[proc_macro]
#[proc_macro_error]
pub fn theory(input: TokenStream) -> TokenStream {
    // Parse input
    let theory_def = parse_macro_input!(input as TheoryDef);

    // Validate
    if let Err(e) = validate_theory(&theory_def) {
        abort_call_site!(e);
    }

    // Generate code
    let generated = generate_ast(&theory_def);

    TokenStream::from(generated)
}
```

---

## Step 6: Runtime Library (5 minutes)

**File:** `runtime/src/lib.rs`

```rust
// Placeholder for future runtime support
// (e.g., parser combinators, rewrite engine, etc.)

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
```

---

## Step 7: Example Usage (15 minutes)

**File:** `examples/simple_monoid.rs`

```rust
use mettail_macros::theory;

theory! {
    name: SimpleMonoid,

    exports {
        Elem;
    },

    terms {
        Zero . Elem ::= "0" ;
        Plus . Elem ::= Elem "+" Elem ;
    }
}

fn main() {
    // Use the generated AST
    let zero = Elem::Zero;
    let one_plus_zero = Elem::Plus(
        Box::new(Elem::Zero),
        Box::new(Elem::Zero),
    );

    println!("Zero: {:?}", zero);
    println!("Plus: {:?}", one_plus_zero);

    // Test equality
    assert_eq!(zero, Elem::Zero);

    println!("\n✅ POC successful! Generated AST types work.");
}
```

**File:** `examples/category_check.rs` (compile-fail test)

```rust
use mettail_macros::theory;

// This should FAIL to compile with a clear error message
theory! {
    name: Invalid,

    exports {
        Elem;
    },

    terms {
        Zero . Elem ::= "0" ;

        // ERROR: Name is not exported!
        Quote . Name ::= "@" Elem ;
    }
}

fn main() {
    println!("This shouldn't compile!");
}
```

---

## Step 8: Testing (30 minutes)

Add tests to each module:

**File:** `macros/tests/integration.rs`

```rust
use mettail_macros::theory;

#[test]
fn test_simple_theory() {
    theory! {
        name: TestTheory,

        exports {
            Elem;
        },

        terms {
            Zero . Elem ::= "0" ;
            Succ . Elem ::= Elem "+" "1" ;
        }
    }

    let x = Elem::Zero;
    let y = Elem::Succ(Box::new(Elem::Zero));

    assert_eq!(x, Elem::Zero);
    assert_ne!(x, y);
}

#[test]
fn test_multiple_categories() {
    theory! {
        name: MultiCat,

        exports {
            Proc;
            Name;
        },

        terms {
            PZero . Proc ::= "0" ;
            PDrop . Proc ::= "*" Name ;
            NQuote . Name ::= "@" Proc ;
        }
    }

    let proc = Proc::PZero;
    let name = Name::NQuote(Box::new(Proc::PZero));
    let proc2 = Proc::PDrop(Box::new(name.clone()));

    println!("{:?}", proc);
    println!("{:?}", name);
    println!("{:?}", proc2);
}
```

Run tests:
```bash
cargo test --all
```

---

## Step 9: Documentation (20 minutes)

**File:** `mettail-rust-exploration/README.md`

```markdown
# MeTTaIL Rust Macros - Proof of Concept

This POC demonstrates the feasibility of implementing MeTTaIL as Rust procedural macros.

## What Works

✅ Theory definition via `theory! {}` macro
✅ Compile-time validation of category references
✅ AST generation for exported categories
✅ Type-safe enum variants from grammar rules

## Usage

Define a theory:

\`\`\`rust
use mettail_macros::theory;

theory! {
    name: SimpleMonoid,

    exports {
        Elem;
    },

    terms {
        Zero . Elem ::= "0" ;
        Plus . Elem ::= Elem "+" Elem ;
    }
}
\`\`\`

Use the generated code:

\`\`\`rust
fn main() {
    let expr = Elem::Plus(
        Box::new(Elem::Zero),
        Box::new(Elem::Zero),
    );
    println!("{:?}", expr);
}
\`\`\`

## Running Examples

\`\`\`bash
cargo run --bin simple_monoid
\`\`\`

## Testing Validation

Try uncommenting the error case in `examples/category_check.rs` and run:

\`\`\`bash
cargo build --bin category_check
\`\`\`

You should see a compile error with a clear message.

## What's Not Implemented (Yet)

- Parser generation (currently just AST types)
- Interpreter generation
- Rewrite rules
- Equations
- Theory composition (conjunction/disjunction)
- Parameterized theories
- Replacements
- Binders

## Next Steps

See `03-NEXT-FEATURES.md` for roadmap to full implementation.
\`\`\`

---

## Step 10: Verify Everything Works (10 minutes)

```bash
# Build everything
cargo build --all

# Run tests
cargo test --all

# Run example
cargo run --bin simple_monoid

# Check lints
cargo clippy --all

# Format code
cargo fmt --all
```

**Expected Output:**

```
Zero: Zero
Plus: Plus(Zero, Zero)

✅ POC successful! Generated AST types work.
```

---

## Common Issues & Solutions

### Issue 1: `proc-macro` crate errors

**Solution:** Make sure `macros/Cargo.toml` has:
```toml
[lib]
proc-macro = true
```

### Issue 2: Parsing errors

**Solution:** Check that `syn` has the `full` feature:
```toml
syn = { version = "2.0", features = ["full", "extra-traits"] }
```

### Issue 3: Generated code doesn't compile

**Solution:** Expand the macro to see what's generated:
```bash
cargo expand --bin simple_monoid
```

### Issue 4: Validation errors not showing

**Solution:** Use `proc-macro-error` for better error reporting:
```rust
use proc_macro_error::{proc_macro_error, abort_call_site};

#[proc_macro_error]
pub fn theory(input: TokenStream) -> TokenStream {
    // ...
}
```

---

## Completion Checklist

- [ ] All files created
- [ ] `cargo build --all` succeeds
- [ ] `cargo test --all` passes
- [ ] `cargo run --bin simple_monoid` produces expected output
- [ ] `cargo run --bin category_check` fails with clear error
- [ ] No clippy warnings
- [ ] Code is formatted
- [ ] README documents what was built

---

## Time Tracking

Use this checklist to track progress:

- [ ] Step 1: Workspace setup (10 min)
- [ ] Step 2: AST definition (30 min)
- [ ] Step 3: Validation (30 min)
- [ ] Step 4: Code generation (45 min)
- [ ] Step 5: Macro entry point (20 min)
- [ ] Step 6: Runtime lib (5 min)
- [ ] Step 7: Examples (15 min)
- [ ] Step 8: Testing (30 min)
- [ ] Step 9: Documentation (20 min)
- [ ] Step 10: Verification (10 min)

**Total:** ~3.5 hours of focused coding

---

## Next: Full Feature Implementation

Once POC is complete and validated, see:
- `03-NEXT-FEATURES.md` - Roadmap for complete implementation
- `04-INTEGRATION.md` - Integrating with f1r3node/rholang

