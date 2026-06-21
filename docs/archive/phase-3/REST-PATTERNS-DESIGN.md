# Collection Rest Patterns Design

## Overview

**Rest patterns** allow partial matching of collections in rewrite rules, essential for structural operational semantics. This enables rules like `({P | Q}) => P` to extract elements from a multiset.

## Motivation

Rhocalc rewrite rules need to operate on parallel composition (`PPar`) structurally:

```rust
// Current (binary PPar):
(PPar P Q) => P  // Extract left process

// With collections:
({P, ...rest}) => P  // Extract any process from the multiset
```

Without rest patterns, we can't write rules that match "a bag containing at least one element P".

## Syntax

### Pattern Forms

```rust
// Extract one element
({P, ...rest}) => P

// Extract multiple specific elements
({P, Q, ...rest}) => (PPar P Q)

// Match exact collection (no rest)
({P, Q}) => ...  // Only matches bags with exactly P and Q

// Rest can be empty
{P, ...rest}  // Matches {P} with rest=∅, or {P,Q} with rest={Q}, etc.

// Use rest in RHS
({P, ...rest}) => ({P, (process P), ...rest})
```

### Parsing Grammar Extension

```bnf
<collection-pattern> ::= "{" <elem-list> "}"
<elem-list> ::= <expr> ("," <expr>)* ("," "..." <ident>)?
              | "..." <ident>
```

## Implementation Plan

### Step 1: AST Extension

**File**: `macros/src/ast.rs`

```rust
#[derive(Clone, Debug)]
pub enum Expr {
    Var(Ident),
    Apply { constructor: Ident, args: Vec<Expr> },
    Subst { term: Box<Expr>, var: Ident, replacement: Box<Expr> },

    // NEW: Collection pattern with rest
    CollectionPattern {
        constructor: Ident,      // PPar, etc.
        elements: Vec<Expr>,     // Specific elements to match
        rest: Option<Ident>,     // Variable to bind remaining elements
    },
}
```

**Rationale**: We need a distinct pattern type because collection patterns have special matching semantics (order-independent, partial matching).

### Step 2: Parser Extension

**File**: `macros/src/ast.rs` (in `parse_expr`)

```rust
fn parse_expr(input: ParseStream) -> SynResult<Expr> {
    if input.peek(syn::token::Brace) {
        // Collection pattern: {P, Q, ...rest}
        let content;
        syn::braced!(content in input);

        let mut elements = Vec::new();
        let mut rest = None;

        while !content.is_empty() {
            // Check for rest pattern
            if content.peek(Token![...]) {
                let _ = content.parse::<Token![...]>()?;
                rest = Some(content.parse::<Ident>()?);
                if content.peek(Token![,]) {
                    let _ = content.parse::<Token![,]>()?;
                }
                break;
            }

            elements.push(parse_expr(&content)?);

            if content.peek(Token![,]) {
                let _ = content.parse::<Token![,]>()?;
            } else {
                break;
            }
        }

        // Infer constructor from context (or require explicit annotation)
        // For now, we'll need to look this up during validation
        return Ok(Expr::CollectionPattern {
            constructor: Ident::new("_INFER_", proc_macro2::Span::call_site()),
            elements,
            rest,
        });
    }

    // ... existing code for Apply, Var, etc.
}
```

### Step 3: Validation

**File**: `macros/src/validator.rs`

```rust
fn validate_collection_pattern(
    pattern: &Expr,
    theory: &TheoryDef,
) -> Result<(), ValidationError> {
    if let Expr::CollectionPattern { constructor, elements, rest } = pattern {
        // 1. Verify constructor is a collection type
        let rule = theory.terms.iter()
            .find(|r| r.label == *constructor)
            .ok_or_else(|| ValidationError::UnknownConstructor {
                name: constructor.to_string(),
                span: constructor.span(),
            })?;

        let has_collection = rule.items.iter().any(|item| {
            matches!(item, GrammarItem::Collection { .. })
        });

        if !has_collection {
            return Err(ValidationError::InvalidCollectionPattern {
                constructor: constructor.to_string(),
                span: constructor.span(),
            });
        }

        // 2. Validate element patterns recursively
        for elem in elements {
            validate_expr(elem, theory)?;
        }

        // 3. Check rest variable doesn't shadow
        if let Some(rest_var) = rest {
            // Add to context, check for duplicates
        }
    }
    Ok(())
}
```

### Step 4: Ascent Code Generation

**File**: `macros/src/ascent_gen.rs` (in `generate_rewrite_clause`)

For a rule like `({P, ...rest}) => P`:

```rust
fn generate_collection_pattern_matching(
    pattern: &Expr,
    source_var: &TokenStream,
    bindings: &mut HashMap<String, TokenStream>,
    clauses: &mut Vec<TokenStream>,
) {
    if let Expr::CollectionPattern { constructor, elements, rest } = pattern {
        let cat = extract_category_from_constructor(constructor);
        let cat_lower = format_ident!("{}", cat.to_string().to_lowercase());

        // Match the constructor
        clauses.push(quote! {
            if let #cat::#constructor(bag) = #source_var
        });

        // Check minimum size
        let min_size = elements.len();
        if min_size > 0 {
            clauses.push(quote! {
                if bag.len() >= #min_size
            });
        }

        // Generate matching for each specific element
        for (i, elem_pattern) in elements.iter().enumerate() {
            match elem_pattern {
                Expr::Var(var_name) => {
                    // Bind variable to an element from the bag
                    let var_ident = format_ident!("{}", var_name.to_string());

                    if i == 0 {
                        // First element: take any one
                        clauses.push(quote! {
                            let #var_ident = bag.iter().next().unwrap().0.clone()
                        });
                    } else {
                        // Subsequent elements: take from remaining
                        clauses.push(quote! {
                            let #var_ident = bag.iter()
                                .skip(#i)
                                .next()
                                .unwrap().0.clone()
                        });
                    }

                    bindings.insert(var_name.to_string(), quote! { #var_ident });
                }
                Expr::Apply { constructor: c, args } => {
                    // Match specific constructor pattern
                    // This is more complex - need to iterate and find matching element
                    // For MVP, we can require variables only
                    panic!("Nested patterns in collections not yet supported");
                }
                _ => panic!("Invalid pattern in collection"),
            }
        }

        // Bind rest variable if present
        if let Some(rest_var) = rest {
            let rest_ident = format_ident!("{}", rest_var.to_string());
            let remove_vars: Vec<_> = elements.iter().filter_map(|e| {
                if let Expr::Var(v) = e {
                    let vi = format_ident!("{}", v.to_string());
                    Some(quote! { #vi })
                } else {
                    None
                }
            }).collect();

            clauses.push(quote! {
                let mut #rest_ident = bag.clone()
            });

            for var in remove_vars {
                clauses.push(quote! {
                    #rest_ident.remove(&#var)
                });
            }

            bindings.insert(rest_var.to_string(), quote! { #rest_ident });
        }
    }
}
```

### Step 5: RHS Construction

**File**: `macros/src/ascent_gen.rs` (in `generate_equation_rhs`)

For RHS like `({P, ...rest})`:

```rust
// In generate_equation_rhs, handle CollectionPattern
Expr::CollectionPattern { constructor, elements, rest } => {
    let elem_constructions: Vec<TokenStream> = elements.iter().map(|e| {
        generate_equation_rhs(e, bindings, theory, true)
    }).collect();

    let mut bag_construction = quote! {
        {
            let mut bag = mettail_runtime::HashBag::new();
            #(bag.insert(#elem_constructions);)*
        }
    };

    // If rest is present, merge it in
    if let Some(rest_var) = rest {
        let rest_ident = format_ident!("{}", rest_var.to_string());
        bag_construction = quote! {
            {
                let mut bag = #rest_ident.clone();
                #(bag.insert(#elem_constructions);)*
                bag
            }
        };
    }

    quote! {
        #constructor(#bag_construction)
    }
}
```

## Testing Strategy

### Unit Tests

```rust
#[test]
fn test_parse_rest_pattern() {
    let input = quote! { {P, ...rest} };
    let expr = parse_expr(input);
    assert!(matches!(expr, Expr::CollectionPattern { .. }));
}

#[test]
fn test_rest_pattern_validation() {
    // Valid: one rest per collection
    // Invalid: multiple rests
    // Invalid: rest on non-collection
}
```

### Integration Tests

```rust
theory! {
    name: TestRest,
    exports { Proc }
    terms {
        PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
        PZero . Proc ::= "0" ;
        POne . Proc ::= "1" ;
    }
    rewrites {
        // Extract one element
        ({P, ...rest}) => P ;

        // Extract two elements
        ({P, Q, ...rest}) => ({P, Q}) ;
    }
}

#[test]
fn test_rest_pattern_rewrite() {
    let proc = Proc::PPar({
        let mut bag = HashBag::new();
        bag.insert(Proc::PZero);
        bag.insert(Proc::POne);
        bag
    });

    // Apply rewrite - should extract one element
    let result = apply_rewrites(proc);
    // Should be either PZero or POne
    assert!(matches!(result, Proc::PZero | Proc::POne));
}
```

### Rhocalc Integration Test

```rust
// examples/rhocalc_collections.rs
theory! {
    name: RhoCalcColl,
    exports { Proc, Name }
    terms {
        PZero . Proc ::= "0" ;
        PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
        PInput . Proc ::= "for" "(" Name "->" <Name> ")" "{" Proc "}" ;
        POutput . Proc ::= Name "!" "(" Proc ")" ;
        PDrop . Proc ::= "*" Name ;

        NQuote . Name ::= "@" "(" Proc ")" ;
        NVar . Name ::= Var ;
    }
    equations {
        // Collections are automatically AC
        // No need for: (PPar P Q) == (PPar Q P)
    }
    rewrites {
        // COMM rule with rest patterns
        ({(Output chan Q), (Input chan x P), ...rest}) =>
            ({(subst P x (Quote Q)), ...rest}) ;
    }
}
```

## Performance Considerations

1. **Iterator Efficiency**: Using `bag.iter().next()` is O(1)
2. **Cloning**: Need to clone the bag for rest binding - acceptable for small bags
3. **Removal**: `HashBag::remove()` is O(1) amortized
4. **Non-determinism**: Order of element extraction is non-deterministic but that's OK (AC semantics)

## Open Questions

1. **Nested Patterns**: Should we support `({(PPar P Q), ...rest})`?
   - **Decision**: Phase 2 - start with variables only

2. **Multiple Rests**: Should we allow `{...rest1, P, ...rest2}`?
   - **Decision**: No - ambiguous and rarely needed

3. **Empty Rest**: Should `{P}` be sugar for `{P, ...∅}`?
   - **Decision**: Yes - makes patterns more natural

4. **Rest in Equations**: Should equations support rest patterns?
   - **Decision**: Yes - same syntax and semantics as rewrites

## Migration Path

### Before (Binary PPar)
```rust
PPar . Proc ::= Proc "|" Proc ;

equations {
    (PPar P Q) == (PPar Q P) ;
    (PPar P (PPar Q R)) == (PPar (PPar P Q) R) ;
}

rewrites {
    (PPar (Output chan Q) (PPar (Input chan x P) R)) =>
        (PPar (subst P x (Quote Q)) R) ;
}
```

### After (HashBag PPar)
```rust
PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;

equations {}  // AC is automatic!

rewrites {
    ({(Output chan Q), (Input chan x P), ...rest}) =>
        ({(subst P x (Quote Q)), ...rest}) ;
}
```

**Key Changes**:
1. Constructor definition uses `HashBag`
2. No AC equations needed
3. Rewrite patterns use `{...}` with rest patterns
4. Much cleaner and more efficient!

## Implementation Checklist

- [ ] Extend `Expr` enum with `CollectionPattern`
- [ ] Implement parser for `{..., ...rest}` syntax
- [ ] Add validation for collection patterns
- [ ] Generate Ascent matching code for rest patterns
- [ ] Generate Ascent construction code for rest in RHS
- [ ] Unit tests for parsing and validation
- [ ] Integration tests with simple theory
- [ ] Rhocalc migration example
- [ ] Performance benchmarks
- [ ] Documentation and examples

