# Collection Metasyntax: A General Framework

**Status:** Design  
**Date:** January 2026

---

## 1. The Goal

Design a **compositional** pattern-matching framework where:
1. Each collection operation has independent semantics
2. Operations compose arbitrarily
3. The algorithm generates efficient matching code for any composition
4. Multi-communication is just one special case

---

## 2. The Core Insight: Comprehensions as Universal Patterns

Every collection operation can be expressed as a **comprehension**:

```
[expr | generator₁, guard₁, generator₂, guard₂, ...]
```

Where:
- **generator**: `pattern <- source` — iterate source, bind variables in pattern
- **guard**: `predicate` — filter, must hold for element to be included

This is the foundation. All `#` combinators desugar to comprehensions.

---

## 3. Combinator Desugaring

| Combinator | Comprehension Equivalent |
|------------|--------------------------|
| `xs.#map(\|x\| f(x))` | `[f(x) \| x <- xs]` |
| `xs.#filter(\|x\| p(x))` | `[x \| x <- xs, p(x)]` |
| `#zip(xs, ys)` | `[(x,y) \| x <- xs, y <- ys, same_index]` |
| `xs.#concat(ys)` | `[z \| z <- xs] ++ [z \| z <- ys]` |
| `xss.#flatten` | `[x \| xs <- xss, x <- xs]` |
| `xs.#fold(init, \|a,x\| f)` | *not a comprehension* (aggregation) |

Compositions desugar recursively:
```
xs.#filter(|x| p(x)).#map(|x| f(x))
  = [f(x) | x <- xs, p(x)]

xs.#map(|x| f(x)).#filter(|y| p(y))  
  = [y | x <- xs, let y = f(x), p(y)]
```

---

## 4. Variable Modes

Variables in patterns have **modes** determined by context:

| Mode | Meaning | Determined By |
|------|---------|---------------|
| **Input** | Already bound | Appears in earlier pattern or is function parameter |
| **Output** | Will be bound | Target of `<-` in generator with unbound source |
| **Iterate** | Bound per iteration | Left of `<-` in generator with bound source |
| **Search** | Extracted from context | In pattern that searches a bound collection |

Example analysis:
```
qs = [q | n <- ns, (POutput n q) <- bag]
      ↑       ↑        ↑      ↑       ↑
   output  iterate   input search  input
```

- `qs`: output (being defined)
- `n`: iterate (bound per iteration of `ns`)
- `ns`: input (bound from earlier)
- `q`: search (extracted from bag)
- `bag`: input (bound from pattern context)

---

## 5. Generator Classification

Generators fall into two categories:

### 5.1 Iteration Generators
```
x <- xs    where xs is input (bound)
```
Produces: loop over `xs`, binding `x` each iteration

### 5.2 Search Generators  
```
pattern <- source    where pattern contains search variables
```
Produces: find element in `source` matching `pattern`, bind search variables

The **key insight**: whether a generator iterates or searches depends entirely on the binding status of its components.

---

## 6. The Pattern-Matching Algorithm

### Input
- Pattern expression (possibly containing comprehensions)
- Set of already-bound variables

### Output
- Rust code that matches and binds variables
- Returns `Option<bindings>` (None = match failure)

### Algorithm

```
generate_match(pattern, bound_vars) -> Code:
    
    case Var(x):
        if x ∈ bound_vars:
            // Equality check
            emit: if value != x { return None; }
        else:
            // Binding
            emit: let x = value;
            bound_vars.insert(x)
    
    case Constructor(name, args):
        emit: if let Name(arg_bindings...) = value {
            for arg in args:
                generate_match(arg, bound_vars)
        } else { return None; }
    
    case Comprehension(result_expr, generators, guards):
        // 1. Classify each generator
        for gen in generators:
            classify(gen, bound_vars) -> Iterate | Search
        
        // 2. Order: iterations before searches
        ordered_gens = topological_sort(generators)
        
        // 3. Generate nested loops/searches
        emit: let mut result = vec![];
        for gen in ordered_gens:
            if gen is Iterate(x, xs):
                emit: for x in xs.iter() {
            else if gen is Search(pattern, source):
                emit: let extracted = source.find(|elem| matches(elem, pattern))?;
                      // bind search variables from extracted
        
        // 4. Generate guards
        for guard in guards:
            emit: if !guard { continue; }
        
        // 5. Collect result
        emit: result.push(result_expr);
        
        // 6. Close loops
        for gen in ordered_gens.reverse():
            emit: }
        
        emit: Some(result)
```

---

## 7. Examples

### 7.1 Simple Map (RHS)
```
xs.#map(|x| f(x))
= [f(x) | x <- xs]
```
Generated:
```rust
let result: Vec<_> = xs.iter().map(|x| f(x)).collect();
```

### 7.2 Simple Filter
```
xs.#filter(|x| p(x))
= [x | x <- xs, p(x)]
```
Generated:
```rust
let result: Vec<_> = xs.iter().filter(|x| p(x)).cloned().collect();
```

### 7.3 Zip (Both Bound)
```
#zip(xs, ys)
= [(x,y) | x <- xs, y <- ys, same_index]
```
Generated:
```rust
assert_eq!(xs.len(), ys.len());
let result: Vec<_> = xs.iter().zip(ys.iter()).collect();
```

### 7.4 Join/Search (One Unbound) — The Multi-Comm Case
```
qs = [q | n <- ns, (POutput n q) <- bag]
```
Analysis:
- `ns`: input (bound) → iteration generator
- `bag`: input (bound) → search source  
- `n`: iterate variable
- `q`: search variable (output)
- `qs`: output

Generated:
```rust
let mut qs = Vec::with_capacity(ns.len());
for n in ns.iter() {
    let q = bag.iter().find_map(|(elem, _)| {
        match elem {
            Proc::POutput(n2, q2) if n2.as_ref() == n => Some((**q2).clone()),
            _ => None
        }
    })?;  // Return None if not found
    qs.push(q);
}
Some(qs)
```

### 7.5 Filter Then Map
```
xs.#filter(|x| p(x)).#map(|x| f(x))
= [f(x) | x <- xs, p(x)]
```
Generated:
```rust
let result: Vec<_> = xs.iter()
    .filter(|x| p(x))
    .map(|x| f(x))
    .collect();
```

### 7.6 Nested Iteration (Cross Product)
```
[(x,y) | x <- xs, y <- ys]
```
Generated:
```rust
let result: Vec<_> = xs.iter()
    .flat_map(|x| ys.iter().map(|y| (x.clone(), y.clone())))
    .collect();
```

### 7.7 Multiple Search Conditions
```
// Find pairs where both elements exist in bag
[(p,q) | n <- ns, m <- ms, (POutput n p) <- bag, (POutput m q) <- bag]
```
Generated:
```rust
let mut result = vec![];
for n in ns.iter() {
    for m in ms.iter() {
        let p = bag.iter().find_map(|(e,_)| match e {
            Proc::POutput(n2, p2) if n2.as_ref() == n => Some((**p2).clone()),
            _ => None
        })?;
        let q = bag.iter().find_map(|(e,_)| match e {
            Proc::POutput(m2, q2) if m2.as_ref() == m => Some((**q2).clone()),
            _ => None
        })?;
        result.push((p, q));
    }
}
Some(result)
```

### 7.8 Flatten
```
xss.#flatten
= [x | xs <- xss, x <- xs]
```
Generated:
```rust
let result: Vec<_> = xss.iter().flat_map(|xs| xs.iter().cloned()).collect();
```

### 7.9 Concat
```
xs.#concat(ys)
```
Generated:
```rust
let result: Vec<_> = xs.iter().chain(ys.iter()).cloned().collect();
```

---

## 8. The `#zip` Special Case

The `#zip(a, b).#map(|x,y| Pattern)` syntax has dual semantics:

### In RHS (Construction)
Both `a` and `b` are input:
```
#zip(ns, qs).#map(|n,q| POutput n q)
= [POutput(n,q) | (n,q) <- zip(ns, qs)]
```

### In LHS (Matching)  
When second arg is unbound, it becomes a **search/join**:
```
#zip(ns, qs).#map(|n,q| POutput n q)
= qs <- [q | n <- ns, (POutput n q) <- bag]
```

The desugaring depends on binding analysis:
- Both bound → parallel iteration (zip)
- Second unbound → search comprehension (join)

---

## 9. Failure Semantics

| Situation | Behavior |
|-----------|----------|
| Search finds nothing | Pattern fails (returns None) |
| Guard is false | Element skipped (filtered out) |
| Length mismatch in zip | Pattern fails |
| Empty iteration source | Empty result (not failure) |

---

## 10. Implementation Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                     Pattern Expression                       │
│   #zip(ns,qs).#map(|n,q| POutput n q)                       │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                   Combinator Desugaring                      │
│   Converts #map, #filter, #zip to comprehension form         │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                    Comprehension IR                          │
│   [q | n <- ns, (POutput n q) <- bag]                       │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                   Binding Analysis                           │
│   Classify: ns=input, bag=input, n=iterate, q=search        │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                  Generator Ordering                          │
│   Order by dependencies: iterate before search               │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                    Code Generation                           │
│   Emit Rust: loops, find_map, guards, collect                │
└─────────────────────────────────────────────────────────────┘
```

---

## 11. Comprehension IR

Define an intermediate representation for normalized comprehensions:

```rust
struct Comprehension {
    /// The expression to collect (may reference bound vars)
    result: Expr,
    
    /// Generators in dependency order
    generators: Vec<Generator>,
    
    /// Boolean guards (filters)
    guards: Vec<Expr>,
}

enum Generator {
    /// Iterate over bound collection
    Iterate {
        var: Ident,
        source: Ident,      // must be bound
    },
    
    /// Search in collection for matching pattern
    Search {
        pattern: Expr,      // pattern containing search vars
        source: Ident,      // must be bound (the "bag")
        extracted: Vec<Ident>,  // variables to extract
    },
    
    /// Parallel iteration (zip)
    Zip {
        vars: Vec<Ident>,
        sources: Vec<Ident>,  // all must be bound, same length
    },
}
```

---

## 12. Collection Types: Vec vs HashBag

| Operation | Vec (ordered) | HashBag (unordered) |
|-----------|---------------|---------------------|
| **Iterate** | ✓ in order | ✓ arbitrary order |
| **Search** | ✓ find first | ✓ find any |
| **Zip** | ✓ same-index | ✗ no ordering |
| **Filter** | ✓ preserves order | ✓ |
| **Map** | ✓ preserves order | ✓ |

The framework handles both by:
1. Tracking `CollectionType` in the IR
2. Generating appropriate iteration code (`.iter()` vs `.iter()` with `(elem, count)`)
3. Validating `#zip` only applies to `Vec`

---

## 13. Implementation Plan (Based on Codebase Review)

### Current State

**Exists:**
- `Expr::Map` — for RHS transformations (`macros/src/ast/types.rs:148`)
- `Expr::CollectionPattern` — for `{P, Q, ...rest}` (`types.rs:158`)
- Collection pattern LHS codegen — nested loops for bags (`patterns.rs:192`)
- RHS Map codegen — `iter().map().collect()` (`rhs.rs:353`)
- `CollectionType` enum — Vec/HashBag/HashSet (`types.rs:571`)

**Needed:**
- Comprehension IR for normalized representation
- `#zip` and `#filter` AST variants
- Desugaring to comprehension form
- Search generator codegen for LHS
- Binding analysis

### Phase 1: Extend AST (1 day)

**File:** `macros/src/ast/types.rs`

```rust
// Add to Expr enum:

/// Filter: xs.#filter(|x| pred)
Filter {
    collection: Box<Expr>,
    param: Ident,
    predicate: Box<Expr>,
},

/// Zip: #zip(xs, ys) - pairs by index (Vec only)
Zip {
    left: Box<Expr>,
    right: Box<Expr>,
},

/// Concat: xs.#concat(ys)
Concat {
    left: Box<Expr>,
    right: Box<Expr>,
},

/// Flatten: xss.#flatten
Flatten {
    collection: Box<Expr>,
},
```

- [ ] Add variants to `Expr` enum
- [ ] Update `free_vars()` for new variants
- [ ] Update `substitute()` for new variants
- [ ] Update parsing in `parse_rhs_expr()` to handle chained operations
- [ ] Add tests

### Phase 2: Comprehension IR (1 day)

**File:** `macros/src/ast/comprehension.rs` (new)

```rust
pub struct Comprehension {
    pub result: Expr,
    pub generators: Vec<Generator>,
    pub guards: Vec<Expr>,
}

pub enum Generator {
    Iterate { var: Ident, source: Ident },
    Search { pattern: Expr, source: Ident, extracted: Vec<Ident> },
    Zip { vars: Vec<Ident>, sources: Vec<Ident> },
}

pub enum CollectionKind {
    Vec,
    HashBag,
}
```

- [ ] Define IR types
- [ ] Implement `desugar_to_comprehension(expr: &Expr) -> Comprehension`
- [ ] Handle Map, Filter, Zip chains
- [ ] Unit tests for desugaring

### Phase 3: Binding Analysis (1 day)

**File:** `macros/src/ast/comprehension.rs`

```rust
pub fn analyze_bindings(
    comprehension: &Comprehension,
    bound_vars: &HashSet<String>,
) -> Result<AnalyzedComprehension, String> {
    // Classify each generator as Iterate/Search/Zip
    // Determine which vars are extracted
    // Validate constraints (zip needs Vec, search source must be bound)
}
```

- [ ] Implement binding classification
- [ ] Track collection types for Vec vs HashBag
- [ ] Validate #zip only on ordered collections
- [ ] Unit tests

### Phase 4: LHS Codegen for Comprehensions (2 days)

**File:** `macros/src/ascent/rewrites/patterns.rs`

Extend `generate_ascent_pattern` to handle `Expr::Map` when it appears in LHS:

```rust
Expr::Map { collection, params, body } => {
    // Check if this is a search pattern (has unbound vars)
    let comprehension = desugar_to_comprehension(expr);
    let analyzed = analyze_bindings(&comprehension, &bound_vars)?;
    
    for gen in analyzed.generators {
        match gen {
            Generator::Iterate { var, source } => {
                clauses.push(quote! { for #var in #source.iter() });
            }
            Generator::Search { pattern, source, extracted } => {
                // Generate find_map code
                clauses.push(quote! {
                    if let Some((#(#extracted),*)) = 
                        #source.iter().find_map(|elem| match_pattern(elem))
                });
            }
            Generator::Zip { vars, sources } => {
                clauses.push(quote! {
                    for (#(#vars),*) in #(#sources.iter()).zip()
                });
            }
        }
    }
}
```

- [ ] Handle `Expr::Map` in LHS patterns
- [ ] Generate Search code with `find_map`
- [ ] Handle HashBag iteration (includes count)
- [ ] Bind extracted variables
- [ ] Unit tests

### Phase 5: RHS Codegen Extensions (1 day)

**File:** `macros/src/ascent/rewrites/rhs.rs`

Extend existing `generate_rhs_expr_code` to handle new combinators:

- [ ] Handle `Expr::Filter` — generate `.filter().collect()`
- [ ] Handle `Expr::Zip` — generate `.zip().collect()`
- [ ] Handle `Expr::Concat` — generate `.chain().collect()`
- [ ] Handle `Expr::Flatten` — generate `.flat_map().collect()`
- [ ] Unit tests

### Phase 6: Integration & Testing (2 days)

**Files:** `theories/src/rhocalc.rs`, `theories/tests/rhocalc.rs`

- [ ] Enable `PInputs` constructor in rhocalc
- [ ] Add multi-communication rewrite rule
- [ ] End-to-end test: parse multi-comm pattern
- [ ] End-to-end test: execute multi-comm reduction
- [ ] Test with different collection types (Vec, HashBag)

---

## 14. File Summary

| File | Changes |
|------|---------|
| `macros/src/ast/types.rs` | Add Filter, Zip, Concat, Flatten to Expr |
| `macros/src/ast/comprehension.rs` | **New:** Comprehension IR and analysis |
| `macros/src/ast/mod.rs` | Export comprehension module |
| `macros/src/ascent/rewrites/patterns.rs` | LHS codegen for comprehensions |
| `macros/src/ascent/rewrites/rhs.rs` | RHS codegen for new combinators |
| `theories/src/rhocalc.rs` | Enable PInputs, add multi-comm rule |
| `theories/tests/rhocalc.rs` | Integration tests |

---

## 15. Summary

The key insight is that **comprehensions are the universal pattern**:

1. All `#` combinators desugar to comprehensions
2. Comprehensions have uniform semantics
3. Generators are classified by binding analysis
4. Code generation handles each generator type independently
5. Composition is just multiple generators in one comprehension
6. Both Vec and HashBag are supported (with Zip restricted to Vec)

The multi-communication pattern:
```rust
#zip(ns,qs).#map(|n,q| POutput n q)
```

Is simply:
```
[q | n <- ns, (POutput n q) <- bag]
```

Which generates a loop + search, like any other join pattern.

**Estimated effort:** 8 days  
**Risk:** Medium (comprehension desugaring has edge cases)

### Quick Reference

| Combinator | LHS (match) | RHS (construct) |
|------------|-------------|-----------------|
| `#map(\|x\| f)` | Destruct, bind vars | Transform elements |
| `#filter(\|x\| p)` | Require predicate | Select subset |
| `#zip(a, b)` | Join if one unbound | Pair by index |
| `#concat(a, b)` | Split (ambiguous) | Combine |
| `#flatten` | (rarely used in LHS) | Un-nest |
