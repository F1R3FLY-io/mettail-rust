# Unified Judgement Syntax for MeTTaIL

**Status:** Design Proposal  
**Date:** January 26, 2026

---

## 1. Motivation

### 1.1 The Problem

The `language!` macro currently has inconsistent syntax across its three main declaration types:

**Terms** — Use judgement-style syntax with rule names:
```rust
terms {
    PZero . |- "0" : Proc;
    PDrop . n:Name |- "*" "(" n ")" : Proc ;
    PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc] 
        |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;
}
```

**Equations** — No rule names, no explicit context:
```rust
equations {
    (NQuote (PDrop N)) = N ;
    if x # ...rest then (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest}));
}
```

**Rewrites** — No rule names, conditions as prefix:
```rust
rewrites {
    (PDrop (NQuote P)) ~> P;
    if S ~> T then (PPar {S, ...rest}) ~> (PPar {T, ...rest});
}
```

### 1.2 Standard Judgement Syntax

Type theory and categorical logic use a standard judgement form:

```
{rule_name}  Γ ; Δ ⊢ J
```

Where:
- `{rule_name}` — Names the rule (for reference in derivations)
- `Γ` — Type/term context (variable bindings)
- `Δ` — Propositional/assumption context (premises, conditions)
- `J` — The judgement itself (typing, term formation, equation, rewrite)

Judgement forms:
- `⊢ T type` — T is a well-formed type
- `⊢ t : T` — Term t has type T
- `⊢ p prop` — p is a well-formed proposition
- `⊢ p` (or `⊢ p true`) — p holds

For our purposes:
- **Terms**: `RuleName . Γ |- syntax : Type`  (currently implemented)
- **Equations**: `RuleName . Γ | Δ |- lhs = rhs`
- **Rewrites**: `RuleName . Γ | Δ |- lhs ~> rhs`

---

## 2. Current State Analysis

### 2.1 Terms (Implemented)

The `terms {}` block already uses judgement syntax:

```rust
// Syntax: Label . term_context |- syntax_pattern : Type ;
PInput . n:Name, ^x.p:[Name->Proc] |- "for" "(" x "<-" n ")" "{" p "}" : Proc ;
```

Components:
- **Label** (`PInput`) — Rule name / Rust enum variant
- **term_context** (`n:Name, ^x.p:[Name->Proc]`) — Variable bindings with types
- **`|-`** — Turnstile separator
- **syntax_pattern** — Concrete syntax
- **`: Type`** — Result type

The term_context supports:
- Simple parameters: `n:Name`
- Abstractions: `^x.p:[Name -> Proc]`
- Multi-abstractions: `^[xs].p:[Name* -> Proc]`
- Collections: `ns:Vec(Name)`

### 2.2 Equations (Partial)

Currently:
```rust
equations {
    (NQuote (PDrop N)) = N ;
    if x # ...rest then (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest}));
}
```

**Missing**:
- Rule names
- Explicit type context (variables are implicitly free)
- Separation of conditions from the equation itself

### 2.3 Rewrites (Partial)

Currently:
```rust
rewrites {
    (PDrop (NQuote P)) ~> P;
    if S ~> T then (PPar {S, ...rest}) ~> (PPar {T, ...rest});
    if x # Q then (Something x Q) ~> (Result);
}
```

**Missing**:
- Rule names
- Clear distinction between:
  - Type context (what variables exist)
  - Propositional context (freshness, congruence premises, env queries)

---

## 3. Design Proposal

### 3.1 Unified Syntax Template

```
RuleName . type_context | prop_context |- judgement ;
```

Where:
- `RuleName` — Identifier naming the rule (required)
- `type_context` — Variable bindings (optional, can be empty or inferred)
- `|` — Separator between type and propositional contexts
- `prop_context` — Premises and conditions (optional, can be empty)
- `|-` — Turnstile
- `judgement` — The actual judgement (term formation, equation, rewrite)

### 3.2 Terms (Unchanged)

Terms continue to use their current syntax:

```rust
terms {
    PZero . |- "0" : Proc ;
    PDrop . n:Name |- "*" "(" n ")" : Proc ;
}
```

Note: Terms don't typically need a propositional context, so `|` is omitted.

### 3.3 Equations (Proposed)

```rust
equations {
    // Simple equation (empty contexts)
    QuoteDrop . |- (NQuote (PDrop N)) = N ;
    
    // With explicit type context
    NewComm . P:Proc, Q:Proc |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P)) ;
    
    // With propositional context (freshness conditions)
    ScopeExtrusion . | x # ...rest |- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest})) ;
    
    // Both type and propositional contexts
    InNew . P:Proc | x # P |- (PIn N (PNew ^x.P)) = (PNew ^x.(PIn N P)) ;
    
    // Multiple freshness conditions (conjunction)
    DoubleNew . | x # Q, y # P |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.Q)) ;
}
```

### 3.4 Rewrites (Proposed)

```rust
rewrites {
    // Simple rewrite (empty contexts)
    DropQuote . |- (PDrop (NQuote P)) ~> P ;
    
    // Congruence rule
    ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest}) ;
    
    // Freshness condition
    Comm . | x # Q |- (PPar {(PInput n ^x.P), (POutput n Q), ...rest}) ~> (PPar {(eval ^x.P (NQuote Q)), ...rest}) ;
    
    // Environment query
    EnvLookup . | env_var(x, v) |- (Var x) ~> (NumLit v) ;
    
    // Multiple premises (conjunction)
    ComplexRule . | x # Q, S ~> T |- ... ~> ... ;
    
    // Mixed premises: freshness + relation query
    EnvFresh . | x # P, env_var(y, v) |- ... ~> ... ;
}
```

### 3.5 Grammar Summary

```
// Terms (no changes)
term_rule     ::= Label "." term_context "|-" syntax_pattern ":" Type ";"

// Equations (new)
equation_rule ::= Label "." contexts "|-" lhs "=" rhs ";"

// Rewrites (new)
rewrite_rule  ::= Label "." contexts "|-" lhs "~>" rhs ";"

// Shared context grammar
contexts      ::= type_context? ("|" prop_context)?
type_context  ::= typed_param ("," typed_param)*
typed_param   ::= ident ":" Type
prop_context  ::= premise ("," premise)*
premise       ::= freshness | congruence | relation_query
freshness     ::= ident "#" target
target        ::= ident | "..." ident
congruence    ::= ident "~>" ident
relation_query::= ident "(" (ident ("," ident)*)? ")"
```

Note: The `|-` turnstile is always required. Empty contexts are written as `|- judgement`.

---

## 4. Benefits of Rule Names

### 4.1 Documentation and Debugging

Rule names make generated code readable:
```rust
// Generated Ascent clause comment
// Rule: ScopeExtrusion
// Context: x # ...rest
eq_proc(s.clone(), t) <-- ...
```

### 4.2 REPL Introspection

```
mettail> :rules equations
Equations:
  QuoteDrop : (NQuote (PDrop N)) = N
  ScopeExtrusion : (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest}))
    where x # ...rest
```

### 4.3 Error Messages

```
Error in rule 'ScopeExtrusion': 
  Freshness condition 'x # ...rest' references unbound variable 'x'
```

### 4.4 Derivation Traces

```
mettail> :trace reductions
Step 1: ParCong applied to {A | B | C}
  premise: A ~> A' (by DropQuote)
  result: {A' | B | C}
```

### 4.5 Selective Application

```
mettail> :reduce --only DropQuote,ParCong
```

---

## 5. Implementation Plan

### 5.1 Phase 1: AST Changes

**File**: `macros/src/ast/language.rs`

#### 5.1.1 Unify Condition Types

Currently there's duplication:
- `Equation.conditions: Vec<FreshnessCondition>` (freshness only)
- `RewriteRule.conditions: Vec<Condition>` (freshness + env query)
- `RewriteRule.premise: Option<(Ident, Ident)>` (congruence, separate field)

**Change**: Unify into a single `Premise` enum used by both:

```rust
/// A premise in a propositional context (part of a conjunction)
#[derive(Debug, Clone)]
pub enum Premise {
    /// Freshness: x # P (x is fresh in P)
    Freshness(FreshnessCondition),
    
    /// Congruence: S ~> T (if S rewrites to T)
    Congruence { source: Ident, target: Ident },
    
    /// Relation query: rel(arg1, arg2, ...) 
    /// Currently used for env_var(x, v), extensible to arbitrary relations
    RelationQuery { relation: Ident, args: Vec<Ident> },
}
```

#### 5.1.2 Update Equation Struct

```rust
pub struct Equation {
    pub name: Ident,                    // NEW: Rule name (required)
    pub type_context: Vec<TypedParam>,  // NEW: Explicit type bindings (optional)
    pub premises: Vec<Premise>,         // RENAMED from conditions, uses Premise
    pub left: Pattern,
    pub right: Pattern,
}
```

#### 5.1.3 Update RewriteRule Struct

```rust
pub struct RewriteRule {
    pub name: Ident,                    // NEW: Rule name (required)
    pub type_context: Vec<TypedParam>,  // NEW: Explicit type bindings (optional)
    pub premises: Vec<Premise>,         // UNIFIED: replaces conditions + premise
    pub left: Pattern,
    pub right: Pattern,
}
```

Note: `premise: Option<(Ident, Ident)>` is removed. Congruence premises become `Premise::Congruence` in the `premises` vector.

#### 5.1.4 Add TypedParam Struct

```rust
/// A typed parameter in the type context
#[derive(Debug, Clone)]
pub struct TypedParam {
    pub name: Ident,
    pub ty: TypeExpr,
}
```

#### 5.1.5 Backward Compatibility Helper

For migration, add a method to extract congruence premise for existing code:

```rust
impl RewriteRule {
    /// Extract the congruence premise (S ~> T), if any.
    /// For backward compatibility with code that expects `premise: Option<(Ident, Ident)>`.
    pub fn congruence_premise(&self) -> Option<(&Ident, &Ident)> {
        self.premises.iter().find_map(|p| {
            if let Premise::Congruence { source, target } = p {
                Some((source, target))
            } else {
                None
            }
        })
    }
}
```

### 5.2 Phase 2: Parser Updates

**File**: `macros/src/ast/language.rs`

#### 5.2.1 New Unified Parser for Rules

Replace `parse_equation` and `parse_rewrite_rule` with a unified approach:

```rust
/// Parse a rule in judgement form:
///   Name . type_context | prop_context |- judgement ;
/// 
/// Grammar:
///   rule       ::= name "." contexts "|-" judgement ";"
///   contexts   ::= type_ctx? ("|" prop_ctx)?
///   type_ctx   ::= typed_param ("," typed_param)*
///   prop_ctx   ::= premise ("," premise)*
///   premise    ::= freshness | congruence | relation
///   freshness  ::= ident "#" target
///   congruence ::= ident "~>" ident
///   relation   ::= ident "(" args ")"
fn parse_rule_contexts(input: ParseStream) -> SynResult<(Vec<TypedParam>, Vec<Premise>)> {
    let mut type_context = Vec::new();
    let mut premises = Vec::new();
    
    // Parse until we see "|-"
    // Determine if current segment is type_ctx or prop_ctx based on "|" separator
    
    let mut in_prop_context = false;
    
    loop {
        // Check for "|-" (end of contexts)
        if input.peek(Token![|]) && input.peek2(Token![-]) {
            break;
        }
        
        // Check for "|" (separator between type and prop contexts)
        if input.peek(Token![|]) && !input.peek2(Token![-]) {
            let _ = input.parse::<Token![|]>()?;
            in_prop_context = true;
            continue;
        }
        
        if in_prop_context {
            // Parse premise
            premises.push(parse_premise(input)?);
        } else {
            // Could be type_ctx param OR first premise (if no explicit type_ctx)
            // Disambiguate: type param has ":" after name, premise has "#", "~>", or "("
            let fork = input.fork();
            let name = fork.parse::<Ident>()?;
            
            if fork.peek(Token![:]) && !fork.peek(Token![::]) {
                // Type parameter: name:Type
                type_context.push(parse_typed_param(input)?);
            } else {
                // Not a type param, switch to prop_context
                in_prop_context = true;
                premises.push(parse_premise(input)?);
            }
        }
        
        // Check for comma (more items) or end
        if input.peek(Token![,]) {
            let _ = input.parse::<Token![,]>()?;
        } else {
            break;
        }
    }
    
    // Consume "|-"
    if input.peek(Token![|]) && input.peek2(Token![-]) {
        let _ = input.parse::<Token![|]>()?;
        let _ = input.parse::<Token![-]>()?;
    } else {
        return Err(input.error("expected '|-' after contexts"));
    }
    
    Ok((type_context, premises))
}

/// Parse a single premise
fn parse_premise(input: ParseStream) -> SynResult<Premise> {
    let first = input.parse::<Ident>()?;
    
    if input.peek(Token![#]) {
        // Freshness: x # target
        let _ = input.parse::<Token![#]>()?;
        let term = if input.peek(Token![...]) {
            let _ = input.parse::<Token![...]>()?;
            FreshnessTarget::CollectionRest(input.parse::<Ident>()?)
        } else {
            FreshnessTarget::Var(input.parse::<Ident>()?)
        };
        Ok(Premise::Freshness(FreshnessCondition { var: first, term }))
    } else if input.peek(Token![~]) && input.peek2(Token![>]) {
        // Congruence: S ~> T
        let _ = input.parse::<Token![~]>()?;
        let _ = input.parse::<Token![>]>()?;
        let target = input.parse::<Ident>()?;
        Ok(Premise::Congruence { source: first, target })
    } else if input.peek(syn::token::Paren) {
        // Relation query: rel(args)
        let args_content;
        syn::parenthesized!(args_content in input);
        let mut args = Vec::new();
        while !args_content.is_empty() {
            args.push(args_content.parse::<Ident>()?);
            if args_content.peek(Token![,]) {
                let _ = args_content.parse::<Token![,]>()?;
            }
        }
        Ok(Premise::RelationQuery { relation: first, args })
    } else {
        Err(syn::Error::new(first.span(), 
            "expected premise: 'x # term', 'S ~> T', or 'rel(args)'"))
    }
}
```

#### 5.2.2 Update parse_equation

```rust
fn parse_equation(input: ParseStream) -> SynResult<Equation> {
    // Parse: Name .
    let name = input.parse::<Ident>()?;
    let _ = input.parse::<Token![.]>()?;
    
    // Parse contexts and turnstile
    let (type_context, premises) = parse_rule_contexts(input)?;
    
    // Parse: lhs = rhs ;
    let left = parse_pattern(input)?;
    let _ = input.parse::<Token![=]>()?;
    let right = parse_pattern(input)?;
    let _ = input.parse::<Token![;]>()?;
    
    Ok(Equation { name, type_context, premises, left, right })
}
```

#### 5.2.3 Update parse_rewrite_rule

```rust
fn parse_rewrite_rule(input: ParseStream) -> SynResult<RewriteRule> {
    // Skip comments
    // ...
    
    // Parse: Name .
    let name = input.parse::<Ident>()?;
    let _ = input.parse::<Token![.]>()?;
    
    // Parse contexts and turnstile
    let (type_context, premises) = parse_rule_contexts(input)?;
    
    // Parse: lhs ~> rhs ;
    let left = parse_pattern(input)?;
    let _ = input.parse::<Token![~]>()?;
    let _ = input.parse::<Token![>]>()?;
    let right = parse_pattern(input)?;
    
    // Optional semicolon
    if input.peek(Token![;]) {
        let _ = input.parse::<Token![;]>()?;
    }
    
    Ok(RewriteRule { name, type_context, premises, left, right })
}
```

### 5.3 Phase 3: Code Generation Updates

**Files**: `macros/src/logic/rules.rs`, `macros/src/logic/equations.rs`, `macros/src/logic/congruence.rs`

#### 5.3.1 Update generate_condition_clauses

Rename to `generate_premise_clauses` and handle `Premise` enum:

```rust
fn generate_premise_clauses(
    premises: &[Premise],
    lhs_clauses: &AscentClauses,
) -> (Vec<TokenStream>, HashMap<String, VariableBinding>) {
    let mut clauses = Vec::new();
    let mut bindings = HashMap::new();
    
    for premise in premises {
        match premise {
            Premise::Freshness(f) => {
                if let Some(clause) = generate_freshness_clause(f, lhs_clauses) {
                    clauses.push(clause);
                }
            }
            Premise::Congruence { source, target } => {
                // Congruence premises are handled separately in congruence.rs
                // They don't generate inline clauses; instead they trigger
                // generation of a separate Ascent rule with rw_* in the body
            }
            Premise::RelationQuery { relation, args } => {
                // Generate relation query clause
                let clause = generate_relation_query_clause(relation, args, lhs_clauses, &mut bindings);
                clauses.push(clause);
            }
        }
    }
    
    (clauses, bindings)
}
```

#### 5.3.2 Update generate_equation_rules

```rust
pub fn generate_equation_rules(language: &LanguageDef) -> Vec<TokenStream> {
    let mut rules = Vec::new();
    
    for eq in &language.equations {
        // Convert Premise::Freshness to Condition for backward compat with generate_rule_clause
        let conditions: Vec<Condition> = eq.premises.iter()
            .filter_map(|p| match p {
                Premise::Freshness(f) => Some(Condition::Freshness(f.clone())),
                Premise::RelationQuery { relation, args } => 
                    Some(Condition::EnvQuery { relation: relation.clone(), args: args.clone() }),
                Premise::Congruence { .. } => None, // Equations don't use congruence premises
            })
            .collect();
        
        // ... rest of generation (unchanged)
    }
    
    rules
}
```

#### 5.3.3 Update congruence.rs

Change `rule.premise.as_ref()` to `rule.congruence_premise()`:

```rust
pub fn generate_explicit_congruence(
    rule: &RewriteRule,
    language: &LanguageDef,
) -> Option<TokenStream> {
    // Use the backward-compat helper method
    let (source_var, _target_var) = rule.congruence_premise()?;
    
    // ... rest unchanged
}
```

#### 5.3.4 Add Rule Names to Generated Comments

```rust
// In generated Ascent code, add comments with rule names
quote! {
    // Rule: #rule_name
    #relation_name(#lhs_var.clone(), #rhs_var) <--
        // ...
}
```

### 5.4 Phase 4: Metadata Extension

**File**: `macros/src/gen/runtime/metadata.rs`

```rust
pub struct EquationMetadata {
    pub name: String,
    pub premises: Vec<String>,  // Display form of each premise
    pub display: String,        // "lhs = rhs"
}

pub struct RewriteMetadata {
    pub name: String,
    pub premises: Vec<String>,
    pub display: String,        // "lhs ~> rhs"
    pub is_congruence: bool,    // Has Premise::Congruence
}
```

Update `generate_metadata()` to include equation and rewrite names.

### 5.5 Phase 5: Validation

**File**: `macros/src/ast/validation/validator.rs`

Add validation for the unified syntax:

```rust
fn validate_equation(eq: &Equation, language: &LanguageDef) -> Result<(), ValidationError> {
    // 1. Check that name is a valid identifier
    // 2. Check that type_context params don't shadow each other
    // 3. Check that premise variables are bound (in LHS or type_context)
    // 4. Check that Congruence premises aren't used in equations (invalid)
    
    for premise in &eq.premises {
        if matches!(premise, Premise::Congruence { .. }) {
            return Err(ValidationError::new(
                eq.name.span(),
                "Congruence premises (S ~> T) are not valid in equations"
            ));
        }
    }
    
    Ok(())
}

fn validate_rewrite(rw: &RewriteRule, language: &LanguageDef) -> Result<(), ValidationError> {
    // 1. Check name is valid
    // 2. Check type_context
    // 3. Check at most one Congruence premise (current limitation)
    
    let congruence_count = rw.premises.iter()
        .filter(|p| matches!(p, Premise::Congruence { .. }))
        .count();
    
    if congruence_count > 1 {
        return Err(ValidationError::new(
            rw.name.span(),
            "Multiple congruence premises not yet supported"
        ));
    }
    
    Ok(())
}
```

### 5.6 Phase 6: Migration

**Files**: All language definitions

Transform:
```rust
// Old syntax
equations {
    (NQuote (PDrop N)) = N ;
    if x # P then (A) = (B) ;
}
rewrites {
    (PDrop (NQuote P)) ~> P;
    if S ~> T then (PPar {S, ...rest}) ~> (PPar {T, ...rest});
    if x # Q then (A) ~> (B);
}
```

To:
```rust
// New syntax
equations {
    QuoteDrop . |- (NQuote (PDrop N)) = N ;
    ScopeExtrusion . | x # P |- (A) = (B) ;
}
rewrites {
    DropQuote . |- (PDrop (NQuote P)) ~> P ;
    ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest}) ;
    SomeRule . | x # Q |- (A) ~> (B) ;
}
```

This is a **breaking change**. Migration script can automate most of it.

---

## 6. Syntax Comparison

### 6.1 Current vs Proposed (Equations)

| Current | Proposed |
|---------|----------|
| `(A) = (B);` | `Name . |- (A) = (B);` |
| `if x # P then (A) = (B);` | `Name . \| x # P |- (A) = (B);` |
| `if x # P, y # Q then (A) = (B);` | `Name . \| x # P, y # Q |- (A) = (B);` |

### 6.2 Current vs Proposed (Rewrites)

| Current | Proposed |
|---------|----------|
| `(A) ~> (B);` | `Name . |- (A) ~> (B);` |
| `if S ~> T then (A) ~> (B);` | `Name . \| S ~> T |- (A) ~> (B);` |
| `if x # Q then (A) ~> (B);` | `Name . \| x # Q |- (A) ~> (B);` |
| `if x # Q then if S ~> T then ...` | `Name . \| x # Q, S ~> T |- ...` |

---

## 7. Design Decisions

### 7.1 Rule Names: Required

**Decision**: Required for all equations and rewrites.

**Rationale**: 
- Consistency with `terms {}` which already requires labels
- Enables debugging, tracing, error messages, selective application
- Breaking change but migration is mechanical (add `Name . |-` prefix)

**Alternative rejected**: Auto-generated names (`Eq1`, `Rw1`) — uninformative for debugging.

### 7.2 Type Context: Optional

**Decision**: Type context is optional (variables are typed by inference).

**Rationale**:
- Most rules don't need explicit typing
- Pattern variables are typed by constructor signatures
- Explicit context available for documentation or disambiguation

**When explicit helps**:
```rust
// Makes it clear P, Q are Proc without examining patterns
NewComm . P:Proc, Q:Proc | x # Q |- ... = ...
```

### 7.3 Turnstile `|-`: Required

**Decision**: The `|-` turnstile is always required.

**Rationale**:
- Clear visual separator between contexts and judgement
- Consistent with standard type-theoretic notation
- Simplifies parsing (unambiguous grammar)

### 7.4 Unified Premise Syntax

**Decision**: All premises use the same comma-separated syntax. No `if ... then` prefix.

- Freshness: `x # P`
- Congruence: `S ~> T`
- Relation: `rel(args)`

**Rationale**:
- One syntax to learn and implement
- Standard notation from inference rules
- Extends naturally to arbitrary relations

---

## 8. Examples: RhoCalc in Unified Syntax

### 8.1 Current Syntax

```rust
language! {
    name: RhoCalc,
    
    types { Proc; Name; },
    
    terms {
        PZero . |- "0" : Proc;
        PDrop . n:Name |- "*" "(" n ")" : Proc ;
        POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc ;
        PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc] 
            |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;
        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
        NQuote . p:Proc |- "@" "(" p ")" : Name ;
    },
    
    equations {
        (NQuote (PDrop N)) = N ;
    },
    
    rewrites {
        (PPar {(PInputs ns cont), *zip(ns,qs).*map(|n,q| (POutput n q)), ...rest}) 
            ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});
        (PDrop (NQuote P)) ~> P;
        if S ~> T then (PPar {S, ...rest}) ~> (PPar {T, ...rest});
    },
}
```

### 8.2 Proposed Syntax

```rust
language! {
    name: RhoCalc,
    
    types { Proc; Name; },
    
    terms {
        // Terms unchanged (already use judgement syntax)
        PZero . |- "0" : Proc;
        PDrop . n:Name |- "*" "(" n ")" : Proc ;
        POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc ;
        PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc] 
            |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;
        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
        NQuote . p:Proc |- "@" "(" p ")" : Name ;
    },
    
    equations {
        // Now with rule names and turnstile
        QuoteDrop . |- (NQuote (PDrop N)) = N ;
    },
    
    rewrites {
        // All rules have names; conditions use | prefix
        Comm . |- (PPar {(PInputs ns cont), *zip(ns,qs).*map(|n,q| (POutput n q)), ...rest}) 
            ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});
        
        DropQuote . |- (PDrop (NQuote P)) ~> P ;
        
        ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest}) ;
    },
}
```

### 8.3 Ambient Calculus Example

```rust
language! {
    name: Ambient,
    
    types { Proc; Name; },
    
    terms {
        PZero . |- "0" : Proc;
        PIn . n:Name, p:Proc |- "in" "(" n "," p ")" : Proc;
        POut . n:Name, p:Proc |- "out" "(" n "," p ")" : Proc;
        POpen . n:Name, p:Proc |- "open" "(" n "," p ")" : Proc;
        PAmb . n:Name, p:Proc |- n "[" p "]" : Proc;
        PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc;
        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
    },
    
    equations {
        // Alpha-equivalence for nested new
        NewComm . |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P)) ;
        
        // Scope extrusion (with freshness)
        ScopeExtrusion . | x # ...rest |- 
            (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest})) ;
        
        // Scope extrusion for other constructors
        InNew . | x # P |- (PIn N (PNew ^x.P)) = (PNew ^x.(PIn N P)) ;
        OutNew . | x # P |- (POut N (PNew ^x.P)) = (PNew ^x.(POut N P)) ;
        OpenNew . | x # P |- (POpen N (PNew ^x.P)) = (PNew ^x.(POpen N P)) ;
        AmbNew . | x # P |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P)) ;
    },
    
    rewrites {
        // In capability
        InRule . |- (PPar {(PAmb N (PPar {(PIn M P), ...rest1})), (PAmb M R), ...rest2})
            ~> (PPar {(PAmb M (PPar {(PAmb N (PPar {P, ...rest1})), R})), ...rest2}) ;
        
        // Out capability  
        OutRule . |- (PAmb M (PPar {(PAmb N (PPar {(POut M P), ...rest1})), R, ...rest2}))
            ~> (PPar {(PAmb N (PPar {P, ...rest1})), (PAmb M R), ...rest2}) ;
        
        // Open capability
        OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
            ~> (PPar {P, Q, ...rest}) ;
        
        // Congruence rules
        ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest}) ;
        NewCong . | S ~> T |- (PNew ^x.S) ~> (PNew ^x.T) ;
        AmbCong . | S ~> T |- (PAmb N S) ~> (PAmb N T) ;
    },
}
```

---

## 9. Design Decisions (Revised)

### 9.1 Propositional Context as Conjunction

The propositional context represents a **conjunction of premises**. Multiple premises are comma-separated:

```rust
// Multiple premises (all must hold)
Rule . | x # P, S ~> T, env_var(y, v) |- lhs ~> rhs ;
```

This means: "if x is fresh in P, AND S rewrites to T, AND env_var(y, v) holds, then..."

**Rationale**: 
- A judgement rule naturally has multiple premises
- Future extensions (arbitrary relations, custom rules) will need this
- Comma-separation is the standard notation in inference rules

### 9.2 No "if-then" Shorthand

The unified syntax uses **only** the judgement form. There is no `if ... then` prefix syntax.

```rust
// Canonical form (the only form)
Rule . | conditions |- judgement ;

// Simple rule (empty prop_context)
Rule . |- judgement ;
```

**Rationale**:
- One syntax is easier to parse, document, and understand
- Avoids ambiguity between shorthand and full form
- Cleaner migration: existing rules become invalid, forcing explicit update

### 9.3 Type Annotations in Patterns

Not needed. Variable types are inferred from:
- Constructor signatures (pattern matching)
- Collection element types
- Abstraction domain/codomain types

If explicit typing is ever needed, it can be added to the type_context:
```rust
Rule . P:Proc, Q:Proc | ... |- ... ;
```

---

## 10. Correctness Considerations

### 10.1 Parsing Invariants

The parser must ensure:

1. **Unambiguous context parsing**: After `Name .`, the parser must correctly identify:
   - Type parameters (`name:Type`) — has `:` after identifier
   - Freshness (`x # target`) — has `#` after identifier  
   - Congruence (`S ~> T`) — has `~>` after identifier
   - Relation (`rel(args)`) — has `(` after identifier

2. **Context separator handling**: 
   - `|` followed by `-` means turnstile `|-`
   - `|` not followed by `-` means context separator

3. **Semicolon termination**: Each rule ends with `;`

### 10.2 Semantic Invariants

The AST must satisfy:

1. **Equations cannot have congruence premises**: `Premise::Congruence` in an `Equation` is invalid
2. **At most one congruence premise per rewrite** (current limitation)
3. **Type context variables must not shadow**: `P:Proc, P:Name` is invalid
4. **Premise variables must be bound**: Referenced variables must appear in LHS or type_context

### 10.3 Code Generation Invariants

Generated Ascent code must:

1. **Handle premises in order**: Freshness/relation checks before pattern matching if they constrain
2. **Preserve congruence semantics**: Congruence rules generate special Ascent patterns with `rw_*` in body
3. **Include rule name in comments**: For debugging

### 10.4 Migration Correctness

Automated migration must verify:

1. **Name uniqueness**: No two equations/rewrites have the same name
2. **Pattern preservation**: LHS and RHS patterns are unchanged
3. **Condition translation**: `if x # P then` → `| x # P |-` exactly

---

## 11. Summary

### 11.1 Key Changes

1. **Rule names required** for all equations and rewrites
2. **Unified syntax**: `Name . type_ctx | prop_ctx |- judgement`
3. **Turnstile `|-` required** (no shorthand forms)
4. **Comma-separated premises** for conjunctions
5. **Unified `Premise` type** replaces separate condition fields

### 11.2 Migration Path

1. Prefix each equation/rewrite with `Name . |-`
2. Convert `if x # P then` to `| x # P |-`
3. Convert `if S ~> T then` to `| S ~> T |-`
4. Convert multiple `if` prefixes to comma-separated: `| x # P, S ~> T |-`

Example:
```rust
// Before
if x # P then (A) = (B);

// After  
SomeRule . | x # P |- (A) = (B);
```

### 11.3 Estimated Effort

| Phase | Description | Effort |
|-------|-------------|--------|
| 1 | AST changes (`Premise` enum, struct updates) | 1 day |
| 2 | Parser updates (`parse_rule_contexts`, etc.) | 2 days |
| 3 | Code generation updates | 1-2 days |
| 4 | Metadata extension | 0.5 days |
| 5 | Validation | 0.5 days |
| 6 | Migration of existing languages | 1 day |
| **Total** | | **~1 week** |

### 11.4 Impact

- **Breaking change**: All equations/rewrites must update
- **Clean break**: Old syntax rejected (no ambiguity)
- **Future-proof**: Supports arbitrary relations and premises
- **High value**: Debugging, tracing, documentation, REPL introspection

---

## 12. Future Improvements

### 12.1 REPL Enhancements

1. **Full syntax display in `info` command**: Currently the REPL `info` command shows simplified representations of equations and rewrites. With rule names now available, the display should show the complete unified syntax:
   ```
   rewrites:
     Comm . |- (PPar {(PInputs ns cont), ...}) ~> ...
     ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest})
   ```

2. **Rule-specific tracing**: Add REPL commands to trace specific rules by name:
   ```
   > trace ParCong
   Tracing enabled for rule: ParCong
   > rw term
   [ParCong] (PPar {P, Q}) ~> (PPar {P', Q})
   ```

### 12.2 Filtered Rewriting by Rule Name

Add the ability to filter rewrites by name, enabling selective application of rules. This would involve:

1. **Parameterized rewrite relations**: Extend `rw_*` relations with a rule name parameter:
   ```rust
   // Current: rw_proc(source, target)
   // Enhanced: rw_proc_named(rule_name, source, target)
   ```

2. **Query interface**: Allow REPL/API to request rewrites using only specific rules:
   ```
   > rw term using [Comm, Beta]
   ```

3. **Step-by-step execution**: Combined with tracing, enables pedagogical step-through of reductions showing which rule fired at each step.

**Implementation complexity**: This requires changes to Ascent rule generation to include rule identifiers and filtering predicates. The unified syntax with mandatory rule names makes this possible.

### 12.3 Additional Improvements

1. **Rule dependency analysis**: With named rules, analyze and visualize which rules can trigger other rules (e.g., after `Comm` fires, `ParCong` may apply to the result).

2. **Coverage reporting**: Track which rules fire during evaluation; identify unused rules.

3. **Rule priorities/strategies**: Allow users to specify evaluation strategies:
   - Outermost-first vs innermost-first
   - Prioritize certain rules over others
   - Exhaustive vs single-step application

4. **Rule documentation**: Support doc comments on rules that flow through to metadata:
   ```rust
   /// The communication rule: parallel input synchronizes with outputs
   Comm . |- (PPar {...}) ~> ...;
   ```

5. **Validation warnings**: Warn about potentially problematic patterns:
   - Rules that may cause infinite loops (e.g., symmetric rewrites without termination)
   - Overlapping LHS patterns between rules
   - Unused variables in type context

6. **Rule export/import**: Support modular language definitions where rules can be imported from other language modules.
