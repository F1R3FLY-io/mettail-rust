# Type Refactoring Design

## Overview

This document describes the refactoring of `macros/src/ast/types.rs` (3000+ lines) into a cleaner, more principled organization.

## Current Issues

### 1. Monolithic `types.rs`

One file contains everything:
- Theory structure (`TheoryDef`, `GrammarRule`, `RewriteRule`, `Equation`)
- Term expressions (`Expr`)
- Syntax patterns (`SyntaxExpr`, `PatternOp`)
- Type system (`TypeExpr`, `TypeContext`, `TypeError`)
- Grammar items (`GrammarItem`, `TermParam`)
- All parsing logic (scattered `impl Parse` blocks)

### 2. `Expr` is Overloaded

```rust
pub enum Expr {
    Var(Ident),                    // Object-level
    Apply { ... },                 // Object-level
    CollectionPattern { ... },     // LHS pattern only
    Lambda { ... },                // Meta-abstraction
    MultiLambda { ... },           // Meta-abstraction
    Subst { ... },                 // Meta-operation
    MultiSubst { ... },            // Meta-operation
    Map { ... },                   // WRONG - compile-time directive
}
```

Problems:
- `CollectionPattern` is only valid in LHS patterns, not terms
- `Map` is a compile-time code generation directive, not a term
- No distinction between LHS patterns and RHS constructions

### 3. Wrong Type for `MultiSubst` ✅ FIXED

Was:
```rust
MultiSubst {
    scope: Ident,             // Wrong - should be Term like Subst
    replacements: Box<Expr>,  // Can hold Expr::Map - wrong!
}
```

Now (Phase 4 complete):
```rust
MultiSubst {
    scope: Box<Term>,         // Parallels Subst - can be any term
    replacements: Vec<Term>,  // Clean list of terms
}
```

## Proposed Structure

### File Organization

```
macros/src/ast/
├── mod.rs              # Re-exports
├── theory.rs           # TheoryDef, Export, GrammarRule, RewriteRule, Equation
├── term.rs             # Term enum (object-level + meta-operations)
├── pattern.rs          # Pattern enum (LHS patterns)
├── syntax.rs           # SyntaxExpr, PatternOp, SyntaxToken (compile-time grammar)
├── types.rs            # TypeExpr, CollectionType
├── grammar.rs          # GrammarItem, TermParam
├── context.rs          # TypeContext, ConstructorSig, TypeError
└── parsing/
    ├── mod.rs
    ├── theory.rs       # Parse impls for theory structure
    ├── term.rs         # Parse impls for terms
    ├── pattern.rs      # Parse impls for patterns
    └── syntax.rs       # Parse impls for syntax patterns
```

### Core Types

#### `Term` (in `term.rs`)

Object-level terms plus meta-operations on terms:

```rust
/// Term in the meta-language
/// 
/// Represents both object-level syntax and meta-level operations.
/// Used in RHS of equations and rewrites for construction.
pub enum Term {
    /// Variable reference
    Var(Ident),
    
    /// Constructor application: Label(arg1, arg2, ...)
    Apply {
        constructor: Ident,
        args: Vec<Term>,
    },
    
    /// Lambda abstraction: ^x.body
    /// Meta-level function over terms
    Lambda {
        binder: Ident,
        body: Box<Term>,
    },
    
    /// Multi-binder lambda: ^[x0, x1, ...].body
    /// Packages ^x0.^x1...^xn.body as a single abstraction
    /// Runtime: Scope<Vec<Binder<String>>, Box<Body>>
    MultiLambda {
        binders: Vec<Ident>,  // Actual binder names [x0, x1, x2, ...]
        body: Box<Term>,
    },
    
    /// Single substitution: term[replacement/var]
    Subst {
        term: Box<Term>,
        var: Ident,
        replacement: Box<Term>,
    },
    
    /// Multi-substitution: body[arg0/x0, ..., argn/xn]
    /// Applied to a multi-binder scope
    MultiSubst {
        /// Pattern variable bound to Scope<Vec<Binder>, Body>
        scope: Ident,
        /// Replacement terms (same length as binders)
        replacements: Vec<Term>,
    },
    
    /// Collection construction: {elem1, elem2} or {elem1, ...rest}
    /// Builds a collection, optionally merging with a bound rest variable
    CollectionConstruct {
        constructor: Ident,
        elements: Vec<Term>,
        /// If Some, merge with this bound collection variable
        merge_with: Option<Ident>,
    },
}
```

#### `LhsPattern` (in `pattern.rs`)

LHS patterns for matching. Builds on `Term` rather than duplicating variants:

```rust
/// Pattern for LHS matching
/// 
/// Patterns can bind variables and destructure collections.
/// Only valid on the left-hand side of equations and rewrites.
pub enum LhsPattern {
    /// A term used as a pattern
    /// - Variables become bindings
    /// - Constructor applications destructure
    /// - Lambdas match against Scope values
    Term(Term),
    
    /// Collection match pattern: {P, Q, ...rest}
    /// Destructures collection, binding remainder to `rest`
    CollectionMatch {
        constructor: Ident,
        elements: Vec<LhsPattern>,
        /// If Some, binds the remainder of the collection
        rest: Option<Ident>,
    },
    
    // Future: ZipExtract for #zip.#map patterns in LHS
}
```

#### Semantics of `...rest`

The `...rest` syntax has different meanings in LHS vs RHS:

| Location | Type | Syntax | Meaning |
|----------|------|--------|---------|
| LHS | `CollectionMatch` | `{P, Q, ...rest}` | **Bind** remainder to `rest` |
| RHS | `CollectionConstruct` | `{T, ...rest}` | **Merge** with bound `rest` |

Example rule: `if S => T then (PPar {S, ...rest}) => (PPar {T, ...rest})`
- LHS: `CollectionMatch { elements: [Term(S)], rest: Some("rest") }` - binds remainder
- RHS: `CollectionConstruct { elements: [T], merge_with: Some("rest") }` - merges back

#### Why `LhsPattern` Wraps `Term`?

1. **No duplication**: `Var`, `Apply`, `Lambda`, `MultiLambda` are reused via `Term`
2. **Clear extension**: Only adds LHS-specific constructs (`CollectionMatch`)
3. **Type safety**: RHS cannot accidentally use `CollectionMatch`
4. **Shared logic**: Type inference, free vars, etc. work on `Term` uniformly

#### Equations and Rewrites

```rust
/// Equation: LHS == RHS
/// LHS is a pattern (for matching), RHS is a term (for construction)
/// Bidirectional: code gen produces rules for both directions
pub struct Equation {
    pub conditions: Vec<FreshnessCondition>,
    pub left: LhsPattern,  // Pattern for matching (primary direction)
    pub right: Term,       // Term for construction (primary direction)
}

/// Rewrite rule: LHS => RHS
/// LHS is a pattern (for matching), RHS is a term (for construction)
pub struct RewriteRule {
    pub conditions: Vec<Condition>,
    pub premise: Option<(Ident, Ident)>,
    pub left: LhsPattern,   // Pattern for matching (can bind via ...rest)
    pub right: Term,        // Term for construction (can merge via ...rest)
    pub env_actions: Vec<EnvAction>,
}
```

**Bidirectional Equation Handling:**

For equations with `{..., ...rest}` on both sides:
- Primary direction (left→right): `CollectionMatch.rest` binds, `CollectionConstruct.merge_with` merges
- Reverse direction (right→left): `CollectionConstruct.merge_with` binds, `CollectionMatch.rest` merges

The code generator handles this duality by interpreting the same `...rest` identifier as either binding or merging based on context.
```

#### Example: Congruence Rule

```rust
// Rule: if S => T then (PPar {S, ...rest}) => (PPar {T, ...rest})

RewriteRule {
    premise: Some(("S", "T")),
    left: LhsPattern::CollectionMatch {
        constructor: "PPar",
        elements: vec![LhsPattern::Term(Term::Var("S"))],
        rest: Some("rest"),  // Binds remainder
    },
    right: Term::CollectionConstruct {
        constructor: "PPar",
        elements: vec![Term::Var("T")],
        merge_with: Some("rest"),  // Merges with bound rest
    },
    // ...
}
```

### Relationship to Collection Metasyntax

The collection metasyntax (`#map`, `#zip`, `#filter`, etc.) is **separate** from these types:

1. **`SyntaxExpr` / `PatternOp`**: Compile-time grammar generation (already separate)
2. **Collection operations in rewrites**: Will be a thin layer that produces `Vec<Term>` at macro expansion time

For example, `(multisubst scope qs.#map(|q| NQuote q))`:
- The `#map` is parsed and expanded at compile-time
- It produces a `Vec<Term>` containing `[NQuote(q0), NQuote(q1), ...]`
- `MultiSubst.replacements` receives this `Vec<Term>`

The collection metasyntax design is documented separately in `collection-metasyntax.md`.

## Migration Path

### Phase 1: Split Files (Non-breaking) ✓

1. ✓ Create new file structure
2. ✓ New modules re-export from `types.rs` (reverse direction for now)
3. ✓ Keep `types.rs` intact with all definitions and parsing
4. ✓ All tests pass

**Current state:** Module structure established. The focused modules exist and re-export from `types.rs`. This allows code to use `crate::ast::term::Expr` or `crate::ast::Expr` interchangeably.

```
macros/src/ast/
├── mod.rs              # Re-exports from types.rs
├── term.rs             # Re-exports Expr from types.rs
├── syntax.rs           # Re-exports SyntaxExpr, PatternOp, SyntaxToken
├── typesystem.rs       # Re-exports TypeExpr, TypeContext, etc.
├── grammar.rs          # Re-exports GrammarItem, TermParam
├── theory.rs           # Re-exports TheoryDef, RewriteRule, etc.
├── types.rs            # All definitions (3000+ lines) - to be migrated
└── types_test.rs       # Tests
```

### Phase 2: Rename `Expr` → `Term` (Breaking but localized) ✓

1. ✓ Rename `Expr` to `Term` in `term.rs`
2. ✓ Update all internal references
3. ✓ Keep `Expr` as a type alias: `pub type Expr = Term;`
4. ✓ All tests pass

### Phase 3: Extract `LhsPattern` (Breaking) ✅

1. ✅ Create `LhsPattern` enum wrapping `Term`
2. ✅ Rename `CollectionPattern` → `CollectionMatch` in `LhsPattern`
3. ✅ Add `CollectionConstruct` to `Term` (with `merge_with` field)
4. ✅ Update `RewriteRule.left` to use `LhsPattern`
5. ✅ Update `RewriteRule.right` to use `Term` with `CollectionConstruct`
6. ✅ Update rewrite pattern matching code generation
7. ✅ Remove `Term::Map` variant
8. ✅ Update `Equation.left` to use `LhsPattern`
9. ✅ Update equation parsing to use `parse_lhs_pattern` for LHS
10. ✅ Update equation code generation (`equations.rs`) to handle `LhsPattern`
11. ✅ Share pattern matching code via `generate_ascent_lhs_pattern`
12. Clean up unused code and imports (pending)

### Phase 4: Fix `MultiLambda` and `MultiSubst` (Breaking) ✅

1. ✅ Change `MultiLambda.binder: Ident` to `MultiLambda.binders: Vec<Ident>`
2. ✅ Update parsing to handle comma-separated binder list: `^[x0, x1, x2].body`
3. ✅ Update all pattern matches across codebase
4. ✅ Add tests for multi-lambda parsing, display, and substitution
5. ✅ Change `MultiSubst.scope: Ident` to `scope: Box<Term>` (parallels `Subst`)
6. ✅ Change `MultiSubst.replacements: Box<Expr>` to `replacements: Vec<Term>`
7. ✅ Update code generation in `rhs.rs` and all pattern matches

### Phase 5: Clean Up

1. Remove temporary type aliases
2. Remove dead code
3. Update documentation

## Files Affected

### High Impact (Pattern Matching Changes)
- `macros/src/ascent/rewrites/patterns.rs` - LHS pattern generation
- `macros/src/ascent/rewrites/rhs.rs` - RHS construction
- `macros/src/ascent/rewrites/clauses.rs` - Clause generation
- `macros/src/ascent/congruence/analysis.rs` - Congruence analysis

### Medium Impact (Type References)
- `macros/src/ascent/equations.rs`
- `macros/src/ascent/relations.rs`
- `macros/src/ascent/categories.rs`
- `macros/src/validation/validator.rs`
- `macros/src/validation/typechecker.rs`
- `macros/src/codegen/ast_gen.rs`
- `macros/src/codegen/subst.rs`

### Low Impact (Simple Renames)
- `macros/src/codegen/parser/lalrpop.rs`
- `macros/src/codegen/display.rs`
- `macros/src/codegen/termgen/*.rs`

## Success Criteria

1. ✅ All existing tests pass
2. ✅ `types.rs` is split into focused files < 500 lines each (Phases 1-2)
3. ✅ `Term` has `CollectionConstruct` with `merge_with: Option<Ident>` (Phase 3)
4. ✅ `LhsPattern` wraps `Term` and adds `CollectionMatch` with `rest: Option<Ident>` (Phase 3)
5. ✅ `MultiLambda.binders` is `Vec<Ident>` (Phase 4)
6. ✅ `MultiSubst.scope` is `Box<Term>`, `replacements` is `Vec<Term>` (Phase 4)
7. ✅ `Term::Map` is removed (Phase 3)
8. ✅ `RewriteRule` uses `LhsPattern` for left, `Term` for right (Phase 3)
9. ✅ `Equation` uses `LhsPattern` for left, `Term` for right (Phase 3)
10. ✅ Equations and rewrites share pattern matching logic via `generate_ascent_lhs_pattern` (Phase 3)

## Open Questions

1. **Type alias for migration?**
   - Keep `pub type Expr = Term;` for how long?
   - Recommendation: Remove after all internal code updated

2. **MultiLambda syntax sugar?**
   - User writes `^[xs].p` but AST has `binders: Vec<Ident>`
   - Need to decide: expand during parsing, or keep sugar and expand later?
   - Recommendation: Expand during parsing when we have the actual binder names

3. ~~**Equations with collections?**~~ RESOLVED
   - ✅ Equations use `LhsPattern` for LHS, same as rewrites
   - ✅ Collection patterns like `{P, Q, ...rest}` work via `CollectionMatch`
   - If so, `Equation.left/right` might need `LhsPattern` too
   - Recommendation: Start with `Term` only; add patterns if needed later
