# Substitution Generation Refactoring

## Current Problems

### 1. Rule-Dependent Generation

The current code generates substitution by iterating over `GrammarRule`s:

```rust
fn generate_substitute_method(category, rules, ...) {
    let match_arms: Vec<TokenStream> = rules.iter()
        .map(|rule| generate_substitution_arm(category, rule, ...))
        .collect();
    // ...
}
```

This is wrong because:
- Substitution is a property of the **AST structure**, not grammar rules
- Auto-generated variants (like `PVar`, `NumLit`) need special handling
- The same rule can be represented multiple ways (old vs new syntax)

### 2. Separate Single vs Multi Substitution

The code has parallel implementations:
- `generate_substitute_method` + `generate_substitution_arm`
- `generate_multi_substitute_method` + `generate_multi_substitution_arm`
- `generate_cross_category_substitute_method` + `generate_cross_multi_substitution_arm`

This is ~1000 lines of nearly-duplicate code. Single substitution should just call multi-substitution with a single element.

### 3. Scattered Var Handling

Auto-generated Var variants are handled separately:
```rust
let has_var_rule = rules.iter().any(|rule| is_var_constructor(rule));
if !has_var_rule {
    let var_arm = generate_auto_var_substitution_arm(category, ...);
    match_arms.push(var_arm);
}
```

This leads to duplicate logic and easy-to-miss edge cases.

### 4. Complex Binder Detection

The code tries to support both old and new syntax:
```rust
let is_multi_binder = rule.term_context.as_ref().map_or(false, |ctx| {
    ctx.iter().any(|p| matches!(p, TermParam::MultiAbstraction { .. }))
});

if is_multi_binder { ... }
else if !rule.bindings.is_empty() { ... }  // old syntax
```

This dual-path logic is error-prone and confusing.

### 5. Incorrect Cross-Category Method Selection

When substituting, we need to call the right method on nested terms:
```rust
let subst_method = if field_cat_str == replacement_cat_str {
    quote! { substitute }
} else {
    let method_name = format_ident!("substitute_{}", replacement_cat_str.to_lowercase());
    quote! { #method_name }
};
```

This is repeated many times and is prone to errors.

## New Design

### Principle 1: Structure-Based, Not Rule-Based

Generate substitution based on the **AST structure** of each category, not grammar rules:

```rust
pub fn generate_substitution(theory: &TheoryDef) -> TokenStream {
    let impls: Vec<TokenStream> = theory.exports.iter()
        .map(|export| generate_category_substitution(export, theory))
        .collect();
    quote! { #(#impls)* }
}

fn generate_category_substitution(export: &Export, theory: &TheoryDef) -> TokenStream {
    let category = &export.name;
    
    // Get all variants for this category (from all sources)
    let variants = collect_category_variants(category, theory);
    
    // Generate one unified substitution method
    let subst_impl = generate_subst_impl(category, &variants, theory);
    
    quote! {
        impl #category {
            #subst_impl
        }
    }
}
```

### Principle 2: Unified Multi-Substitution

Single substitution is just multi-substitution with one variable:

```rust
impl Proc {
    /// Substitute a single variable
    pub fn substitute(&self, var: &FreeVar<String>, replacement: &Self) -> Self {
        self.subst(&[var], &[replacement.clone()])
    }
    
    /// Substitute multiple variables simultaneously (capture-avoiding)
    pub fn subst(&self, vars: &[&FreeVar<String>], repls: &[Self]) -> Self {
        // Unified implementation
    }
}
```

### Principle 3: Generate for All Category Pairs

For each pair `(TermCategory, ReplacementCategory)`, generate a substitution method:

```rust
// For theory with exports { Proc; Name; }

impl Proc {
    // Same-category substitution
    pub fn subst(&self, vars: &[&FreeVar<String>], repls: &[Proc]) -> Proc { ... }
    
    // Cross-category substitution (Name vars in Proc terms)
    pub fn subst_name(&self, vars: &[&FreeVar<String>], repls: &[Name]) -> Proc { ... }
}

impl Name {
    pub fn subst(&self, vars: &[&FreeVar<String>], repls: &[Name]) -> Name { ... }
    pub fn subst_proc(&self, vars: &[&FreeVar<String>], repls: &[Proc]) -> Name { ... }
}
```

### Principle 4: Variant-Based Match Arms

Each variant type has a uniform substitution pattern:

| Variant Type | Pattern | Substitution Logic |
|-------------|---------|-------------------|
| Var | `PVar(OrdVar)` | Check if matches any var, return replacement or self |
| Literal | `NumLit(i32)` | Return self (no variables) |
| Nullary | `PZero` | Return self |
| Regular | `Add(Box<T>, Box<T>)` | Recurse into fields |
| Collection | `PPar(HashBag<T>)` | Map substitution over elements |
| Binder | `PInput(n, Scope<...>)` | Filter shadowed vars, recurse into body |
| MultiBinder | `PInputs(ns, Scope<Vec<...>>)` | Filter all shadowed vars, recurse |

## Implementation

### Data Structures

```rust
/// Represents a variant of an AST enum for substitution purposes
#[derive(Debug, Clone)]
enum VariantKind {
    /// Variable: PVar(OrdVar)
    Var { label: Ident },
    
    /// Literal: NumLit(i32)
    Literal { label: Ident },
    
    /// Nullary constructor: PZero
    Nullary { label: Ident },
    
    /// Regular constructor with fields
    Regular {
        label: Ident,
        fields: Vec<FieldInfo>,
    },
    
    /// Collection constructor: PPar(HashBag<Proc>)
    Collection {
        label: Ident,
        element_cat: Ident,
        coll_type: CollectionType,
    },
    
    /// Single binder: PInput(Name, Scope<Binder<String>, Box<Proc>>)
    Binder {
        label: Ident,
        pre_scope_fields: Vec<FieldInfo>,
        binder_cat: Ident,
        body_cat: Ident,
    },
    
    /// Multi-binder: PInputs(Vec<Name>, Scope<Vec<Binder<String>>, Box<Proc>>)
    MultiBinder {
        label: Ident,
        pre_scope_fields: Vec<FieldInfo>,
        binder_cat: Ident,
        body_cat: Ident,
    },
}

#[derive(Debug, Clone)]
struct FieldInfo {
    index: usize,
    category: Ident,
    is_collection: bool,
    coll_type: Option<CollectionType>,
}
```

### Collection Function

```rust
/// Collect all variants for a category from grammar rules and auto-generated variants
fn collect_category_variants(category: &Ident, theory: &TheoryDef) -> Vec<VariantKind> {
    let mut variants = Vec::new();
    
    // From grammar rules
    for rule in theory.terms.iter().filter(|r| r.category == *category) {
        variants.push(rule_to_variant_kind(rule));
    }
    
    // Auto-generated Var variant (if no explicit Var rule)
    let has_var = variants.iter().any(|v| matches!(v, VariantKind::Var { .. }));
    if !has_var {
        variants.push(VariantKind::Var {
            label: generate_var_label(category),
        });
    }
    
    // Auto-generated Literal variant (for native types)
    if let Some(export) = theory.get_export(category) {
        if let Some(native_type) = &export.native_type {
            let has_lit = variants.iter().any(|v| matches!(v, VariantKind::Literal { .. }));
            if !has_lit {
                variants.push(VariantKind::Literal {
                    label: generate_literal_label(native_type),
                });
            }
        }
    }
    
    variants
}

/// Convert a grammar rule to a VariantKind
fn rule_to_variant_kind(rule: &GrammarRule) -> VariantKind {
    // Use term_context if available (new syntax), otherwise infer from items (old syntax)
    if let Some(ctx) = &rule.term_context {
        variant_kind_from_term_context(&rule.label, ctx)
    } else {
        variant_kind_from_items(&rule.label, &rule.items, &rule.bindings)
    }
}
```

### Unified Substitution Generation

```rust
fn generate_subst_impl(
    category: &Ident,
    variants: &[VariantKind],
    theory: &TheoryDef,
) -> TokenStream {
    let category_str = category.to_string();
    
    // Generate match arms for the main subst method
    let match_arms: Vec<TokenStream> = variants.iter()
        .map(|v| generate_subst_arm(category, v, category, theory))
        .collect();
    
    // Generate cross-category methods
    let cross_methods: Vec<TokenStream> = theory.exports.iter()
        .filter(|e| e.name != *category)
        .map(|e| {
            let repl_cat = &e.name;
            let method_name = format_ident!("subst_{}", repl_cat.to_string().to_lowercase());
            let cross_arms: Vec<TokenStream> = variants.iter()
                .map(|v| generate_subst_arm(category, v, repl_cat, theory))
                .collect();
            
            quote! {
                pub fn #method_name(
                    &self,
                    vars: &[&mettail_runtime::FreeVar<String>],
                    repls: &[#repl_cat],
                ) -> Self {
                    if vars.is_empty() { return self.clone(); }
                    debug_assert_eq!(vars.len(), repls.len());
                    match self {
                        #(#cross_arms),*
                    }
                }
            }
        })
        .collect();
    
    // Self-alias for uniform cross-category calls
    let self_alias = format_ident!("subst_{}", category_str.to_lowercase());
    
    quote! {
        /// Single-variable substitution
        pub fn substitute(
            &self,
            var: &mettail_runtime::FreeVar<String>,
            replacement: &Self,
        ) -> Self {
            self.subst(&[var], &[replacement.clone()])
        }
        
        /// Multi-variable simultaneous substitution (capture-avoiding)
        pub fn subst(
            &self,
            vars: &[&mettail_runtime::FreeVar<String>],
            repls: &[Self],
        ) -> Self {
            if vars.is_empty() { return self.clone(); }
            debug_assert_eq!(vars.len(), repls.len());
            match self {
                #(#match_arms),*
            }
        }
        
        /// Alias for uniform cross-category calls
        pub fn #self_alias(
            &self,
            vars: &[&mettail_runtime::FreeVar<String>],
            repls: &[Self],
        ) -> Self {
            self.subst(vars, repls)
        }
        
        #(#cross_methods)*
    }
}
```

### Per-Variant Match Arm Generation

```rust
fn generate_subst_arm(
    category: &Ident,
    variant: &VariantKind,
    repl_cat: &Ident,
    theory: &TheoryDef,
) -> TokenStream {
    match variant {
        VariantKind::Var { label } => {
            generate_var_subst_arm(category, label, repl_cat)
        }
        VariantKind::Literal { label } => {
            quote! { #category::#label(_) => self.clone() }
        }
        VariantKind::Nullary { label } => {
            quote! { #category::#label => self.clone() }
        }
        VariantKind::Regular { label, fields } => {
            generate_regular_subst_arm(category, label, fields, repl_cat, theory)
        }
        VariantKind::Collection { label, element_cat, coll_type } => {
            generate_collection_subst_arm(category, label, element_cat, coll_type, repl_cat)
        }
        VariantKind::Binder { label, pre_scope_fields, binder_cat, body_cat } => {
            generate_binder_subst_arm(category, label, pre_scope_fields, binder_cat, body_cat, repl_cat)
        }
        VariantKind::MultiBinder { label, pre_scope_fields, binder_cat, body_cat } => {
            generate_multi_binder_subst_arm(category, label, pre_scope_fields, binder_cat, body_cat, repl_cat)
        }
    }
}

fn generate_var_subst_arm(
    category: &Ident,
    label: &Ident,
    repl_cat: &Ident,
) -> TokenStream {
    let same_category = category == repl_cat;
    
    if same_category {
        // Can substitute - check if var matches
        quote! {
            #category::#label(mettail_runtime::OrdVar(mettail_runtime::Var::Free(v))) => {
                for (i, var) in vars.iter().enumerate() {
                    if v == *var {
                        return repls[i].clone();
                    }
                }
                self.clone()
            }
            #category::#label(_) => self.clone()
        }
    } else {
        // Different category - can't substitute
        quote! { #category::#label(_) => self.clone() }
    }
}

fn generate_regular_subst_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
    repl_cat: &Ident,
    theory: &TheoryDef,
) -> TokenStream {
    let field_names: Vec<Ident> = fields.iter()
        .enumerate()
        .map(|(i, _)| format_ident!("f{}", i))
        .collect();
    
    let field_substs: Vec<TokenStream> = fields.iter()
        .zip(field_names.iter())
        .map(|(field, name)| {
            let method = subst_method_for_category(&field.category, repl_cat);
            if field.is_collection {
                // Collection field - map over elements
                quote! {
                    {
                        let mut bag = mettail_runtime::HashBag::new();
                        for (elem, count) in #name.iter() {
                            let s = elem.#method(vars, repls);
                            for _ in 0..count { bag.insert(s.clone()); }
                        }
                        bag
                    }
                }
            } else {
                // Regular field - recurse
                quote! { Box::new((**#name).#method(vars, repls)) }
            }
        })
        .collect();
    
    quote! {
        #category::#label(#(#field_names),*) => {
            #category::#label(#(#field_substs),*)
        }
    }
}

/// Get the substitution method name for a field category
fn subst_method_for_category(field_cat: &Ident, repl_cat: &Ident) -> TokenStream {
    if field_cat == repl_cat {
        quote! { subst }
    } else {
        let method = format_ident!("subst_{}", repl_cat.to_string().to_lowercase());
        quote! { #method }
    }
}
```

### Binder Handling

```rust
fn generate_binder_subst_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
    binder_cat: &Ident,
    body_cat: &Ident,
    repl_cat: &Ident,
) -> TokenStream {
    let should_filter = binder_cat == repl_cat;
    let body_method = subst_method_for_category(body_cat, repl_cat);
    
    // Generate field names
    let field_names: Vec<Ident> = pre_scope_fields.iter()
        .enumerate()
        .map(|(i, _)| format_ident!("f{}", i))
        .collect();
    
    let pattern = if field_names.is_empty() {
        quote! { #category::#label(scope) }
    } else {
        quote! { #category::#label(#(#field_names,)* scope) }
    };
    
    if should_filter {
        // Same category binder - need to check for shadowing
        quote! {
            #pattern => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                
                // Filter out shadowed variables
                let (fvars, frepls): (Vec<_>, Vec<_>) = vars.iter()
                    .zip(repls.iter())
                    .filter(|(v, _)| binder.0 != ***v)
                    .map(|(v, r)| (*v, r.clone()))
                    .unzip();
                
                if fvars.is_empty() {
                    self.clone()
                } else {
                    let new_body = (**body).#body_method(&fvars[..], &frepls);
                    let new_scope = mettail_runtime::Scope::new(binder.clone(), Box::new(new_body));
                    #category::#label(#(#field_names.clone(),)* new_scope)
                }
            }
        }
    } else {
        // Different category binder - no shadowing, just recurse
        quote! {
            #pattern => {
                let binder = &scope.inner().unsafe_pattern;
                let body = &scope.inner().unsafe_body;
                let new_body = (**body).#body_method(vars, repls);
                let new_scope = mettail_runtime::Scope::new(binder.clone(), Box::new(new_body));
                #category::#label(#(#field_names.clone(),)* new_scope)
            }
        }
    }
}
```

## Summary of Changes

| Aspect | Before | After |
|--------|--------|-------|
| Entry point | `generate_substitution(theory)` iterates rules | Same, but delegates to variant-based logic |
| Single vs Multi | Separate 1000-line implementations | Single method (`subst`), `substitute` is alias |
| Var handling | Scattered, rule-dependent | Uniform `VariantKind::Var` |
| Binder detection | Dual old/new syntax paths | Unified via `VariantKind` |
| Cross-category | Repeated method generation | Generated from Cartesian product of exports |
| Method naming | `substitute`, `multi_substitute`, `substitute_X`, `multi_substitute_X` | `substitute`, `subst`, `subst_X` |
| Lines of code | ~1660 | ~400 (estimated) |

## Migration

1. Create `VariantKind` enum and collection functions
2. Implement unified `generate_subst_impl`
3. Implement per-variant arm generators
4. Test against existing theories (Calculator, RhoCalc, Ambient)
5. Remove old code

## Backward Compatibility

The generated API changes slightly:
- `multi_substitute` → `subst` (shorter, clearer)
- `multi_substitute_name` → `subst_name`

We can add aliases for backward compatibility if needed, but since this is compile-time generated code, breakage should be limited to internal usage.
