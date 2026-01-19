# Pattern Type: Unified Rule Specification Language

**Status:** Partially Implemented  
**Date:** January 2026  
**Supersedes:** `lhs-pattern-matching.md` (LhsPattern concept)

---

## Implementation Status (January 2026)

### Completed ✓

| Feature | Status | Notes |
|---------|--------|-------|
| `Pattern` and `PatternTerm` types | ✓ | Core enums implemented |
| `Pattern::Collection` with `...rest` | ✓ | LHS matching and RHS construction |
| `Pattern::Term(PatternTerm::Apply)` | ✓ | Constructor matching/construction |
| `Pattern::Term(PatternTerm::Lambda)` | ✓ | Single-binder scopes |
| `Pattern::Term(PatternTerm::Subst)` | ✓ | Substitution in RHS |
| `pattern.category()` | ✓ | Category inference |
| `pattern.var_occurrences()` | ✓ | Duplicate variable detection |
| `pattern.to_ascent_clauses()` | ✓ | LHS → Ascent Datalog |
| `pattern.to_ascent_rhs()` | ✓ | RHS → Rust expression |

### Remaining for Multi-Communication

| Feature | Status | Required For |
|---------|--------|--------------|
| `Pattern::Map` in RHS | Not started | Transform collections |
| `Pattern::Zip` in RHS | Not started | Pair collections |
| `Pattern::Zip` in LHS (search) | Not started | Extract matching elements |
| `PatternTerm::MultiLambda` | Partial | Multi-binder `^[x,y].body` |
| `PatternTerm::MultiSubst` | Not started | Simultaneous substitution |
| `Vec(T)` collection type | Not started | Ordered collections |
| `#sep` for display | Not started | Parser/display syntax |

---

## 1. The Key Insight

Collection metasyntax (`#map`, `#zip`, `#filter`, etc.) is **not** part of the object language. It's **metasyntax** for specifying rules that gets compiled away. At runtime, you never have a term like `args.#map(|a| (Subst a x v))` — you have concrete lists like `[(Subst arg0 x v), (Subst arg1 x v)]`.

Therefore:
- **Term**: Object-language constructs that exist at runtime
- **Pattern**: Rule specification metasyntax for matching/construction

Both LHS and RHS of equations and rewrites use `Pattern`, with interpretation differing by position.

---

## 2. Type Definitions

### 2.1 Term (Object Language)

```rust
/// Object-language terms (actual runtime values)
/// These are the real AST nodes that exist in evaluated programs.
pub enum Term {
    /// Variable reference
    Var(Ident),
    
    /// Constructor application: (Cons arg0 arg1 ...)
    Apply { constructor: Ident, args: Vec<Term> },
    
    /// Single-variable lambda: \x.body
    Lambda { binder: Ident, body: Box<Term> },
    
    /// Multi-variable lambda: ^[x0,x1,...].body
    MultiLambda { binders: Vec<Ident>, body: Box<Term> },
    
    /// Single substitution: term[replacement/var]
    Subst { term: Box<Term>, var: Ident, replacement: Box<Term> },
    
    /// Multi-substitution: (multisubst scope r0 r1 ...)
    MultiSubst { scope: Box<Term>, replacements: Vec<Term> },
    
    // NO collection metasyntax here - that's Pattern's job
}
```

### 2.2 PatternTerm (Lifted Term for Rule Specification)

```rust
/// Term-like structure for rule specification.
/// Mirrors Term but allows Pattern in sub-expression positions.
/// This lets metasyntax (#map, #zip, etc.) appear anywhere in a term.
pub enum PatternTerm {
    /// Variable (binds on LHS, references on RHS)
    Var(Ident),
    
    /// Constructor application: (Cons arg0 arg1 ...)
    /// Args are Pattern, allowing metasyntax in any position
    Apply { constructor: Ident, args: Vec<Pattern> },
    
    /// Lambda: \x.body
    Lambda { binder: Ident, body: Box<Pattern> },
    
    /// Multi-lambda: ^[x0,x1,...].body
    MultiLambda { binders: Vec<Ident>, body: Box<Pattern> },
    
    /// Substitution: term[replacement/var]
    Subst { term: Box<Pattern>, var: Ident, replacement: Box<Pattern> },
    
    /// Multi-substitution: (multisubst scope r0 r1 ...)
    MultiSubst { scope: Box<Pattern>, replacements: Vec<Pattern> },
}
```

### 2.3 Pattern (Rule Specification Language)

```rust
/// Rule specification patterns (metasyntax for matching/construction)
/// Used in both LHS and RHS of equations and rewrites.
/// Interpretation differs by position:
///   - LHS: pattern matching, variable binding
///   - RHS: term construction
pub enum Pattern {
    /// A term-like pattern (the common case)
    /// Wraps PatternTerm for all "normal" patterns
    Term(PatternTerm),
    
    // --- Collection metasyntax (only these add new capabilities) ---
    
    /// Collection: {P, Q, ...rest}
    /// LHS: match elements, bind remainder to `rest`
    /// RHS: construct collection, merge with `rest`
    Collection {
        constructor: Option<Ident>,
        elements: Vec<Pattern>,
        rest: Option<Ident>,
    },
    
    /// Map: xs.#map(|x| body)
    /// LHS: for each x in xs (if xs bound), match body, extract unbound vars
    /// RHS: transform each element by body
    Map {
        collection: Box<Pattern>,
        params: Vec<Ident>,
        body: Box<Pattern>,
    },
    
    /// Zip: #zip(xs, ys)
    /// LHS: if one unbound, search/join; if both bound, parallel iterate
    /// RHS: pair-wise combination
    Zip {
        collections: Vec<Pattern>,
    },
    
    /// Filter: xs.#filter(|x| pred)
    /// LHS: conditional match (require predicate)
    /// RHS: keep elements satisfying predicate
    Filter {
        collection: Box<Pattern>,
        params: Vec<Ident>,
        predicate: Box<Condition>,
    },
    
    /// Flatten: xss.#flatten
    /// RHS: un-nest nested collections
    Flatten {
        collection: Box<Pattern>,
    },
    
    /// Concat: xs.#concat(ys)
    /// RHS: concatenate collections
    Concat {
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
}
```

Note: `PatternTerm` is separate from `Pattern` to reduce the number of cases when matching. Most patterns are `Pattern::Term(PatternTerm::...)`, and the metasyntax variants only appear when needed.

**Not included:**
- `Fold` - Aggregation operations like `xs.#fold(init, |acc,x| f)` don't fit the comprehension model. They could be added later if needed.
- `Any`/`All` - Existential/universal quantifiers over collections. Consider for future if LHS needs "exists element matching pattern".

**Dependencies:**
- `Condition` in `Filter` refers to the existing condition type from `theory.rs` (freshness, env queries, etc.)

### 2.4 Equations and Rewrites

```rust
pub struct Equation {
    pub conditions: Vec<Condition>,
    pub left: Pattern,   // interpretation: match (but equations are symmetric)
    pub right: Pattern,  // interpretation: construct
}

pub struct RewriteRule {
    pub conditions: Vec<Condition>,
    pub premise: Option<(Ident, Ident)>,  // for congruence rules
    pub left: Pattern,   // interpretation: match
    pub right: Pattern,  // interpretation: construct
    pub env_actions: Vec<EnvAction>,
}
```

---

## 3. Dual Semantics

The same pattern has different meanings based on position:

| Pattern | LHS (match) | RHS (construct) |
|---------|-------------|-----------------|
| `Term(Var(x))` | Bind `x` to matched value | Reference `x`'s bound value |
| `Term(Apply{..})` | Destructure, recurse on args | Construct, recurse on args |
| `Term(Lambda{..})` | Match against Scope, bind body | Construct Scope |
| `Collection { elements, rest }` | Match elements, bind remainder to `rest` | Build from elements, merge with `rest` |
| `Map { collection, body }` | For each in collection, match body | Transform each by body |
| `Zip { [a, b] }` | If `b` unbound: search/join | Pair-wise combine |
| `Filter { predicate }` | Only match if predicate holds | Keep satisfying elements |
| `Flatten { collection }` | Rarely used in LHS | Un-nest collections |
| `Concat { left, right }` | Ambiguous split | Concatenate |

**Important:** All variants except `Pattern::Term(...)` are **metasyntax** — they have no `Term` equivalent and are compiled away during code generation. `Collection` always requires special handling because `Term` has no inherent notion of "collections" (they're represented as e.g., `PPar(HashBag<Proc>)` at runtime).

---

## 4. Examples

### 4.1 Simple Rewrite (Terms Only)

```rust
// (POutput n (PSome p)) => (POutput n p)
RewriteRule {
    left: Pattern::Term(PatternTerm::Apply {
        constructor: "POutput",
        args: [
            Pattern::Term(PatternTerm::Var("n")),
            Pattern::Term(PatternTerm::Apply {
                constructor: "PSome",
                args: [Pattern::Term(PatternTerm::Var("p"))]
            })
        ]
    }),
    right: Pattern::Term(PatternTerm::Apply {
        constructor: "POutput",
        args: [
            Pattern::Term(PatternTerm::Var("n")),
            Pattern::Term(PatternTerm::Var("p"))
        ]
    }),
}
```

### 4.2 Collection with Rest (Congruence)

```rust
// if S => T then (PPar {S, ...rest}) => (PPar {T, ...rest})
RewriteRule {
    premise: Some(("S", "T")),
    left: Pattern::Collection {
        constructor: Some("PPar"),
        elements: [Pattern::Term(PatternTerm::Var("S"))],
        rest: Some("rest"),
    },
    right: Pattern::Collection {
        constructor: Some("PPar"),
        elements: [Pattern::Term(PatternTerm::Var("T"))],
        rest: Some("rest"),
    },
}
```

### 4.3 Map in RHS (Lambda Calculus)

With `PatternTerm`, metasyntax can appear anywhere because `PatternTerm::Apply.args` is `Vec<Pattern>`:

```rust
// (Subst (App f args) x v) => (App (Subst f x v) args.#map(|a| (Subst a x v)))
RewriteRule {
    left: Pattern::Term(PatternTerm::Apply {
        constructor: "Subst",
        args: [
            Pattern::Term(PatternTerm::Apply { 
                constructor: "App", 
                args: [
                    Pattern::Term(PatternTerm::Var("f")),
                    Pattern::Term(PatternTerm::Var("args"))
                ] 
            }),
            Pattern::Term(PatternTerm::Var("x")),
            Pattern::Term(PatternTerm::Var("v")),
        ]
    }),
    right: Pattern::Term(PatternTerm::Apply {
        constructor: "App",
        args: [
            Pattern::Term(PatternTerm::Apply { 
                constructor: "Subst", 
                args: [
                    Pattern::Term(PatternTerm::Var("f")),
                    Pattern::Term(PatternTerm::Var("x")),
                    Pattern::Term(PatternTerm::Var("v"))
                ] 
            }),
            // HERE: args.#map(|a| (Subst a x v)) - metasyntax in arg position!
            Pattern::Map {
                collection: Box::new(Pattern::Term(PatternTerm::Var("args"))),
                params: vec!["a"],
                body: Box::new(Pattern::Term(PatternTerm::Apply {
                    constructor: "Subst",
                    args: [
                        Pattern::Term(PatternTerm::Var("a")),
                        Pattern::Term(PatternTerm::Var("x")),
                        Pattern::Term(PatternTerm::Var("v"))
                    ]
                })),
            }
        ]
    }),
}
```

### 4.4 Multi-Communication Pattern (The Motivating Example)

```rust
// (PPar {(PInputs ns scope), #zip(ns,qs).#map(|n,q| POutput n q)})
//     => (multisubst scope qs.#map(|q| NQuote q))
RewriteRule {
    left: Pattern::Collection {
        constructor: Some("PPar"),
        elements: [
            // Match PInputs, binding ns and scope
            Pattern::Term(PatternTerm::Apply {
                constructor: "PInputs",
                args: [
                    Pattern::Term(PatternTerm::Var("ns")),
                    Pattern::Term(PatternTerm::Var("scope"))
                ]
            }),
            // Search for matching outputs, extracting qs
            Pattern::Map {
                collection: Box::new(Pattern::Zip {
                    collections: [
                        Pattern::Term(PatternTerm::Var("ns")),    // bound
                        Pattern::Term(PatternTerm::Var("qs")),    // unbound - to extract
                    ]
                }),
                params: vec!["n", "q"],
                body: Box::new(Pattern::Term(PatternTerm::Apply {
                    constructor: "POutput",
                    args: [
                        Pattern::Term(PatternTerm::Var("n")),
                        Pattern::Term(PatternTerm::Var("q"))
                    ]
                })),
            }
        ],
        rest: None,  // or Some("rest") to capture remaining processes
    },
    right: Pattern::Term(PatternTerm::MultiSubst {
        scope: Box::new(Pattern::Term(PatternTerm::Var("scope"))),
        replacements: [
            Pattern::Map {
                collection: Box::new(Pattern::Term(PatternTerm::Var("qs"))),
                params: vec!["q"],
                body: Box::new(Pattern::Term(PatternTerm::Apply {
                    constructor: "NQuote",
                    args: [Pattern::Term(PatternTerm::Var("q"))]
                })),
            }
        ]
    }),
}
```

### 4.5 Why PatternTerm?

The key insight is that `PatternTerm::Apply.args` is `Vec<Pattern>`, not `Vec<Term>`. This allows metasyntax to appear at any position in a term-like structure, solving the nesting problem elegantly.

---

## 5. Final Type Definitions

### 5.1 Term (unchanged - pure object language)

```rust
/// Object-language terms. These exist at runtime.
/// No metasyntax - this is the actual AST of evaluated programs.
pub enum Term {
    Var(Ident),
    Apply { constructor: Ident, args: Vec<Term> },
    Lambda { binder: Ident, body: Box<Term> },
    MultiLambda { binders: Vec<Ident>, body: Box<Term> },
    Subst { term: Box<Term>, var: Ident, replacement: Box<Term> },
    MultiSubst { scope: Box<Term>, replacements: Vec<Term> },
}
```

### 5.2 PatternTerm (lifted Term for rule specification)

```rust
/// Term-like structure where sub-expressions can be Pattern.
/// Mirrors Term but allows metasyntax in any position.
pub enum PatternTerm {
    /// Variable
    Var(Ident),
    
    /// Constructor application
    /// Note: args are Pattern, allowing metasyntax anywhere
    Apply { constructor: Ident, args: Vec<Pattern> },
    
    /// Lambda
    Lambda { binder: Ident, body: Box<Pattern> },
    
    /// Multi-lambda
    MultiLambda { binders: Vec<Ident>, body: Box<Pattern> },
    
    /// Substitution
    Subst { term: Box<Pattern>, var: Ident, replacement: Box<Pattern> },
    
    /// Multi-substitution
    MultiSubst { scope: Box<Pattern>, replacements: Vec<Pattern> },
}
```

### 5.3 Pattern (rule specification with metasyntax)

```rust
/// Pattern for rule specification (both LHS and RHS).
/// Wraps PatternTerm for "normal" patterns, adds metasyntax variants.
pub enum Pattern {
    /// A term-like pattern (the common case)
    Term(PatternTerm),
    
    // --- Collection metasyntax ---
    
    /// Collection: {P, Q, ...rest}
    Collection {
        constructor: Option<Ident>,
        elements: Vec<Pattern>,
        rest: Option<Ident>,
    },
    
    /// Map: xs.#map(|x| body)
    Map {
        collection: Box<Pattern>,
        params: Vec<Ident>,
        body: Box<Pattern>,
    },
    
    /// Zip: #zip(xs, ys)
    Zip {
        collections: Vec<Pattern>,
    },
    
    /// Filter: xs.#filter(|x| pred)
    Filter {
        collection: Box<Pattern>,
        params: Vec<Ident>,
        predicate: Box<Condition>,
    },
    
    /// Flatten: xss.#flatten
    Flatten {
        collection: Box<Pattern>,
    },
    
    /// Concat: xs.#concat(ys)
    Concat {
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
}
```

### 5.4 Conversion Functions

```rust
/// Convert a Term to a Pattern (no metasyntax, just lifting)
pub fn term_to_pattern(term: &Term) -> Pattern {
    Pattern::Term(term_to_pattern_term(term))
}

fn term_to_pattern_term(term: &Term) -> PatternTerm {
    match term {
        Term::Var(v) => PatternTerm::Var(v.clone()),
        Term::Apply { constructor, args } => PatternTerm::Apply {
            constructor: constructor.clone(),
            args: args.iter().map(term_to_pattern).collect(),
        },
        Term::Lambda { binder, body } => PatternTerm::Lambda {
            binder: binder.clone(),
            body: Box::new(term_to_pattern(body)),
        },
        Term::MultiLambda { binders, body } => PatternTerm::MultiLambda {
            binders: binders.clone(),
            body: Box::new(term_to_pattern(body)),
        },
        Term::Subst { term, var, replacement } => PatternTerm::Subst {
            term: Box::new(term_to_pattern(term)),
            var: var.clone(),
            replacement: Box::new(term_to_pattern(replacement)),
        },
        Term::MultiSubst { scope, replacements } => PatternTerm::MultiSubst {
            scope: Box::new(term_to_pattern(scope)),
            replacements: replacements.iter().map(term_to_pattern).collect(),
        },
    }
}

/// Try to convert a Pattern to a Term (fails if pattern contains metasyntax)
pub fn pattern_to_term(pattern: &Pattern) -> Option<Term> {
    match pattern {
        Pattern::Term(pt) => pattern_term_to_term(pt),
        // Metasyntax cannot be converted to Term
        Pattern::Collection { .. } | Pattern::Map { .. } | Pattern::Zip { .. } 
        | Pattern::Filter { .. } | Pattern::Flatten { .. } | Pattern::Concat { .. } => None,
    }
}

fn pattern_term_to_term(pt: &PatternTerm) -> Option<Term> {
    match pt {
        PatternTerm::Var(v) => Some(Term::Var(v.clone())),
        PatternTerm::Apply { constructor, args } => {
            let term_args: Option<Vec<Term>> = args.iter().map(pattern_to_term).collect();
            term_args.map(|a| Term::Apply { constructor: constructor.clone(), args: a })
        },
        PatternTerm::Lambda { binder, body } => {
            pattern_to_term(body).map(|b| Term::Lambda { 
                binder: binder.clone(), 
                body: Box::new(b) 
            })
        },
        PatternTerm::MultiLambda { binders, body } => {
            pattern_to_term(body).map(|b| Term::MultiLambda { 
                binders: binders.clone(), 
                body: Box::new(b) 
            })
        },
        PatternTerm::Subst { term, var, replacement } => {
            let t = pattern_to_term(term)?;
            let r = pattern_to_term(replacement)?;
            Some(Term::Subst { 
                term: Box::new(t), 
                var: var.clone(), 
                replacement: Box::new(r) 
            })
        },
        PatternTerm::MultiSubst { scope, replacements } => {
            let s = pattern_to_term(scope)?;
            let rs: Option<Vec<Term>> = replacements.iter().map(pattern_to_term).collect();
            rs.map(|r| Term::MultiSubst { scope: Box::new(s), replacements: r })
        },
    }
}

/// Check if a pattern contains any metasyntax
/// Returns true for Collection, Map, Zip, Filter, Flatten, Concat
/// (These cannot be converted to Term)
pub fn has_metasyntax(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Term(pt) => has_metasyntax_in_pattern_term(pt),
        // All collection variants are metasyntax (no Term equivalent)
        Pattern::Collection { .. } | Pattern::Map { .. } | Pattern::Zip { .. } 
        | Pattern::Filter { .. } | Pattern::Flatten { .. } | Pattern::Concat { .. } => true,
    }
}

fn has_metasyntax_in_pattern_term(pt: &PatternTerm) -> bool {
    match pt {
        PatternTerm::Var(_) => false,
        PatternTerm::Apply { args, .. } => args.iter().any(has_metasyntax),
        PatternTerm::Lambda { body, .. } => has_metasyntax(body),
        PatternTerm::MultiLambda { body, .. } => has_metasyntax(body),
        PatternTerm::Subst { term, replacement, .. } => {
            has_metasyntax(term) || has_metasyntax(replacement)
        },
        PatternTerm::MultiSubst { scope, replacements } => {
            has_metasyntax(scope) || replacements.iter().any(has_metasyntax)
        },
    }
}
```

---

## 6. Migration from Current State

### Current State

| Type | Purpose |
|------|---------|
| `Term` | Object language + `CollectionConstruct` (metasyntax leak) |
| `LhsPattern` | LHS-only patterns with `CollectionMatch` |
| `Equation.left: LhsPattern, right: Term` | Asymmetric |
| `RewriteRule.left: LhsPattern, right: Term` | Asymmetric |

### Target State

| Type | Purpose |
|------|---------|
| `Term` | Pure object language (no metasyntax) |
| `PatternTerm` | Lifted Term where args are Pattern |
| `Pattern` | Unified rule specification (Term + metasyntax) |
| `Equation.left: Pattern, right: Pattern` | Symmetric |
| `RewriteRule.left: Pattern, right: Pattern` | Symmetric |

### Migration Steps

1. **Create `PatternTerm` enum** mirroring Term with Pattern args
2. **Create `Pattern` enum** wrapping PatternTerm + metasyntax variants
3. **Update `Equation` and `RewriteRule`** to use `Pattern` for both sides
4. **Remove `Term::CollectionConstruct`** (replaced by `Pattern::Collection`)
5. **Remove `LhsPattern`** (functionality merged into `Pattern`)
6. **Update parsing** to produce `Pattern` for both LHS and RHS
7. **Update code generation** to handle `Pattern` symmetrically
8. **Add conversion functions** between `Term`, `PatternTerm`, and `Pattern`

---

## 7. Implementation Plan

### Phase 1: Pattern Type Foundation ✓ COMPLETE

**Files:** `macros/src/ast/pattern.rs`

- [x] Define `PatternTerm` enum (mirrors Term with Pattern args)
- [x] Define `Pattern` enum (wraps PatternTerm + metasyntax variants)
- [x] Implement `free_vars()` for PatternTerm and Pattern
- [x] Implement `category()` for category inference
- [x] Implement `var_occurrences()` and `duplicate_vars()`
- [x] Implement `to_ascent_clauses()` for LHS matching
- [x] Implement `to_ascent_rhs()` for RHS construction

### Phase 2: AST Migration ✓ COMPLETE

**Files:** `macros/src/ast/term.rs`, `macros/src/ast/theory.rs`

- [x] Remove `Term::CollectionConstruct` (replaced by `Pattern::Collection`)
- [x] Remove `LhsPattern` (merged into Pattern)
- [x] Update `Equation.left` and `Equation.right` to `Pattern`
- [x] Update `RewriteRule.left` and `RewriteRule.right` to `Pattern`
- [x] Update parsing functions to return `Pattern`

### Phase 3: Parsing Extensions (Partial)

**Files:** `macros/src/ast/theory.rs`

- [ ] Parse `#map(xs, |x| body)` or `xs.#map(|x| body)`
- [ ] Parse `#zip(xs, ys)`
- [ ] Parse `#filter(xs, |x| pred)` or `xs.#filter(|x| pred)`
- [ ] Parse `#flatten(xs)` or `xs.#flatten`
- [ ] Parse `#concat(xs, ys)` or `xs.#concat(ys)`
- [ ] Handle chained operations: `xs.#filter(...).#map(...)`
- [x] Parse collection with rest: `{P, Q, ...rest}`
- [x] Parse single-binder lambda: `^x.body`
- [ ] Parse multi-binder lambda: `^[x,y].body`

### Phase 4: Validation Updates ✓ COMPLETE

**Files:** `macros/src/validation/validator.rs`

- [x] Pattern validation (validate_pattern)
- [x] Binding analysis (binders included in pattern vars)
- [x] Freshness condition validation
- [ ] Validate: `#zip` second arg must be unbound in LHS context
- [ ] Validate: `#zip` on Vec only (not HashBag)

### Phase 5: Code Generation - RHS ✓ COMPLETE (basic)

**Files:** `macros/src/ast/pattern.rs` (`to_ascent_rhs`)

- [x] Handle `PatternTerm` recursively
- [x] Handle `Pattern::Collection` in RHS: merge with `rest`
- [x] Handle `PatternTerm::Lambda` in RHS with binder identity preservation
- [x] Handle `PatternTerm::Subst` in RHS
- [ ] Handle `Pattern::Map` in RHS: generate `.iter().map().collect()`
- [ ] Handle `Pattern::Zip` in RHS: generate `.zip().collect()`
- [ ] Handle `PatternTerm::MultiLambda` in RHS
- [ ] Handle `PatternTerm::MultiSubst` in RHS

### Phase 6: Code Generation - LHS ✓ COMPLETE (basic)

**Files:** `macros/src/ast/pattern.rs` (`to_ascent_clauses`, `generate_clauses`)

- [x] Handle `PatternTerm` recursively
- [x] Handle `Pattern::Collection` in LHS: destructure, bind rest
- [x] Handle `PatternTerm::Lambda` in LHS with binder identity preservation
- [x] Duplicate variable detection and eq_* checks
- [ ] Handle `Pattern::Map` in LHS (iterate and match)
- [ ] Handle `Pattern::Zip` in LHS (search/join)

### Phase 7: Comprehension IR (Deferred)

**Files:** `macros/src/ast/comprehension.rs` (new)

- [ ] Define `Comprehension` IR for normalized patterns
- [ ] Implement desugaring from Pattern combinators to Comprehension
- [ ] Use Comprehension for unified LHS/RHS code generation

### Phase 8: Integration Testing ✓ COMPLETE (basic)

**Files:** `theories/tests/rhocalc.rs`, `examples/ambient_tests.rs`

- [x] Test Collection with rest in both LHS and RHS
- [x] Test binder equations (scope extrusion, freshness)
- [x] Test communication rewrite with collection rest
- [ ] Test Map in RHS: lambda calculus substitution distribution
- [ ] Test Zip in RHS: list operations
- [ ] Test multi-communication pattern (the motivating example)

---

## 8. Summary

| Aspect | Before | After |
|--------|--------|-------|
| Object language | `Term` (with CollectionConstruct leak) | `Term` (pure) |
| Rule specification | `LhsPattern` (LHS only) + `Term` | `Pattern` (both sides) |
| Term lifting | N/A | `PatternTerm` (args are Pattern) |
| LHS type | `LhsPattern` | `Pattern` |
| RHS type | `Term` | `Pattern` |
| `#map`, `#zip`, etc. | Not implemented | `Pattern` variants |
| Dual semantics | Implicit | Explicit by position |

### Key Benefits of PatternTerm

1. **Clean separation**: `Term` is pure object language, `Pattern` is rule specification
2. **Metasyntax anywhere**: `PatternTerm::Apply.args` is `Vec<Pattern>`, so `#map` can appear in any position
3. **Reduced case explosion**: Most patterns are `Pattern::Term(PatternTerm::...)`, metasyntax variants are separate
4. **Symmetric rules**: Both LHS and RHS are `Pattern`, interpretation differs by context
5. **Conversion safety**: `pattern_to_term()` fails cleanly when metasyntax is present

---

## 9. Roadmap: Multi-Communication Support

The multi-communication pattern in rho-calculus demonstrates the full power of collection metasyntax:

```rust
// Target syntax (from rhocalc.rs):
// PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc] 
//     |- "for" "(" #zip(ns,xs).#map(|n,x| x "<-" n).#sep(",") ")" "{" p "}" : Proc ;

// Rewrite rule:
// (PPar {(PInputs ns scope), #zip(ns,qs).#map(|n,q| POutput n q)})
//     => (multisubst scope qs.#map(|q| NQuote q))
```

### Required Features (in implementation order)

#### 1. Vec Collection Type (Grammar)
**Effort:** 1-2 days

Add `Vec(T)` as a collection type distinct from `HashBag(T)`:
- `Vec` preserves order, supports `#zip`
- `HashBag` is unordered, doesn't support `#zip`
- Grammar: `ns:Vec(Name)` in constructor syntax

**Changes:**
- `macros/src/ast/grammar.rs`: Add `Vec` variant to collection handling
- `macros/src/codegen/ast_gen.rs`: Generate `Vec<T>` fields
- `macros/src/codegen/parser/lalrpop.rs`: Parse comma-separated lists

#### 2. Multi-Binder Syntax (Grammar + Pattern)
**Effort:** 2-3 days

Support `^[x0,x1,...].body` for binding multiple variables:
- Grammar: `^[xs].p:[Name* -> Proc]` means `p` binds list `xs` of Names
- Uses `mettail_runtime::Scope<Vec<Binder>, T>`

**Changes:**
- `macros/src/ast/theory.rs`: Parse `^[xs].body` syntax
- `macros/src/codegen/ast_gen.rs`: Generate multi-binder Scope fields
- `macros/src/ast/pattern.rs`: Handle `PatternTerm::MultiLambda` in LHS/RHS

#### 3. Pattern::Map in RHS
**Effort:** 1 day

Transform each element of a bound collection:
```rust
// qs.#map(|q| NQuote q) generates:
{
    let mut result = Vec::new();
    for q in qs.iter() {
        result.push(Name::NQuote(Box::new(q.clone())));
    }
    result
}
```

**Changes:**
- `macros/src/ast/pattern.rs`: Implement `generate_map_rhs()`

#### 4. Pattern::Zip in RHS
**Effort:** 1 day

Pair-wise iteration over two collections:
```rust
// #zip(ns, qs).#map(|n,q| POutput n q) generates:
{
    let mut result = Vec::new();
    for (n, q) in ns.iter().zip(qs.iter()) {
        result.push(Proc::POutput(Box::new(n.clone()), Box::new(q.clone())));
    }
    result
}
```

**Changes:**
- `macros/src/ast/pattern.rs`: Implement `generate_zip_rhs()`

#### 5. Pattern::Zip in LHS (Search/Join)
**Effort:** 2-3 days

When second arg is unbound, search for matching elements:
```rust
// #zip(ns, qs).#map(|n,q| POutput n q) in LHS:
// For each n in ns, find a (POutput n q) in the bag and extract q
let mut qs = Vec::new();
for n in ns.iter() {
    let q = bag.iter().find_map(|(elem, _)| {
        if let Proc::POutput(n2, q2) = elem {
            if n2.as_ref() == n { Some((**q2).clone()) } else { None }
        } else { None }
    })?;  // Pattern fails if not found
    qs.push(q);
}
```

**Changes:**
- `macros/src/ast/pattern.rs`: Implement `generate_zip_lhs_clauses()`
- Variable mode analysis (input/output/search classification)

#### 6. MultiSubst in RHS
**Effort:** 1 day

Simultaneous substitution for all binders:
```rust
// (multisubst scope qs) where scope has binders [x0,x1,...]:
scope.substitute_all(&[x0, x1, ...], &[q0, q1, ...])
```

**Changes:**
- `macros/src/ast/pattern.rs`: Handle `PatternTerm::MultiSubst` in RHS

#### 7. Display Syntax (#sep)
**Effort:** 1 day

Separator syntax for pretty-printing collections:
```rust
// ps.#sep("|") displays as "p0 | p1 | p2"
```

**Changes:**
- `macros/src/codegen/display.rs`: Handle `#sep` in display generation
- `macros/src/codegen/parser/lalrpop.rs`: Parse separator-delimited lists

### Summary

| Feature | Estimated Days | Difficulty |
|---------|----------------|------------|
| Vec collection type | 1-2 | Low |
| Multi-binder syntax | 2-3 | Medium |
| Map in RHS | 1 | Low |
| Zip in RHS | 1 | Low |
| Zip in LHS (search) | 2-3 | High |
| MultiSubst | 1 | Low |
| Display #sep | 1 | Low |
| **Total** | **~10-12 days** | |

The key challenge is the **search semantics** for `#zip` in LHS patterns, which requires binding analysis to determine which variables are input (iterate) vs output (search).
