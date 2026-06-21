# Data Structures in MeTTaIL: Design Document

**Status:** Design Phase
**Date:** November 3, 2025
**Author:** System Architecture Review

---

## 🎯 Motivation

### The Problem

Currently, MeTTaIL defines parallel composition (`PPar`) as a **binary operation** with **equations** for commutativity and associativity:

```rust
PPar . Proc ::= Proc "|" Proc ;

equations {
    (PPar P Q) == (PPar Q P) ;              // Commutativity
    (PPar P (PPar Q R)) == (PPar (PPar P Q) R) ;  // Associativity
    (PPar P PZero) == P ;                   // Identity
}
```

**Why this is problematic:**
1. **Performance**: Nested binary trees are inefficient (O(n) depth for n parallel processes)
2. **Equation handling**: Commutativity/associativity require e-graph integration (Phase 5) or expensive normalization
3. **Pattern matching**: Finding a specific process in `P|Q|R|S|...` requires traversing the tree
4. **Realistic semantics**: Real process calculi implementations use multisets/bags for parallel composition

### The Solution

Replace binary `PPar` with a **multiset-based** parallel composition:

```rust
PPar . Proc ::= multiset<Proc> ;  // HashBag of processes

// No equations needed - commutativity/associativity are implicit!
// Identity (empty multiset) is implicit!
```

**Benefits:**
1. **O(1) insertion/removal** via HashMap
2. **Automatic canonicalization** - no need for equations
3. **Efficient pattern matching** - direct lookup in the bag
4. **Matches real implementations** - closer to actual Rholang

---

## 📊 Current Architecture Analysis

### AST Generation (`codegen.rs`)

**Current approach:**
- Each grammar rule generates an **enum variant**
- Binary operators create recursive types like `PPar(Box<Proc>, Box<Proc>)`
- All fields are explicitly typed

**Key code:**
```rust
fn generate_variant(rule: &GrammarRule) -> TokenStream {
    let label = &rule.label;

    if !rule.bindings.is_empty() {
        return generate_binder_variant(rule);
    }

    let fields: Vec<_> = rule.items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::NonTerminal(ident) => Some(ident),
            _ => None,
        })
        .collect();

    // Generate tuple variant with Box<T> fields
    let boxed_fields: Vec<TokenStream> = fields.iter().map(|f| {
        quote! { Box<#f> }
    }).collect();

    quote! { #label(#(#boxed_fields),*) }
}
```

### Parser Generation (`lalrpop_gen.rs`)

**Current approach:**
- LALRPOP rules are generated for each grammar rule
- Infix operators get **tiered precedence** handling
- Left-associativity via recursive grammar

**Key challenge:** How to parse multiset syntax?

**Example current output:**
```lalrpop
ProcInfix: Proc = {
    <left:ProcInfix> "|" <right:ProcAtom> => Proc::PPar(Box::new(left), Box::new(right)),
    <ProcAtom>
};
```

### Rewrite Engine (`rewrite_gen.rs`)

**Current approach:**
- Pattern matching via nested `if let` chains
- Bindings collected in `HashMap<String, TokenStream>`
- Freshness checking on bound variables

**Key challenge:** How to match patterns against multisets?

**Example current output:**
```rust
pub fn try_rewrite_rule_0(term: &Proc) -> Option<Proc> {
    if let Proc::PPar(field_0, field_1) = term {
        if let Proc::PInput(chan, scope_field) = &(**field_0) {
            let (binder, body) = scope_field.clone().unbind();
            if let Proc::POutput(chan2, q) = &(**field_1) {
                // Freshness check
                if !is_fresh(&binder, &(**q)) {
                    return None;
                }
                // Apply substitution
                return Some((*body).clone().substitute_name(&binder.0, &quote));
            }
        }
    }
    None
}
```

### Substitution (`substitution.rs`)

**Current approach:**
- Recursive traversal of AST
- Special handling for `Scope` types (binders)
- Cross-category substitution support

**Key question:** How to substitute into multisets?

---

## 🎨 Design Proposal

### 1. Syntax Extension

#### 1.1 Grammar Rule Syntax

**Add new `GrammarItem` variant for data structures:**

```rust
// In ast.rs
pub enum GrammarItem {
    Terminal(String),
    NonTerminal(Ident),
    Binder { category: Ident },

    // NEW: Data structure types
    DataStructure {
        kind: DataStructureKind,
        element_type: Ident,
    },
}

pub enum DataStructureKind {
    Multiset,      // hashbag
    List,          // Vec
    Set,           // HashSet
    Map { key_type: Ident },  // HashMap
}
```

**User syntax:**

```rust
theory! {
    name: RhoCalc,
    exports { Proc, Name }

    terms {
        PZero . Proc ::= "0" ;

        // NEW SYNTAX: multiset<Type> for multiset fields
        PPar . Proc ::= multiset<Proc> ;

        // Could also support:
        // PList . Proc ::= list<Proc> ;        // Vec<Proc>
        // PSet . Proc ::= set<Name> ;          // HashSet<Name>
        // PMap . Proc ::= map<Name, Proc> ;    // HashMap<Name, Proc>

        // ... other constructors
    }
}
```

#### 1.2 Parsing Data Structure Syntax

```rust
// In ast.rs, inside parse_grammar_rule
while !input.peek(Token![;]) {
    if input.peek(syn::LitStr) {
        // Terminal
        let lit = input.parse::<syn::LitStr>()?;
        items.push(GrammarItem::Terminal(lit.value()));
    } else if input.peek(Token![<]) {
        // Could be binder <Name> or type parameter
        let _ = input.parse::<Token![<]>()?;
        let next = input.parse::<Ident>()?;

        if input.peek(Token![>]) {
            // Binder: <Name>
            let _ = input.parse::<Token![>]>()?;
            items.push(GrammarItem::Binder { category: next });
        } else {
            // Type parameter - part of a data structure
            // This should be handled differently
            panic!("Type parameters not yet supported in this context");
        }
    } else if input.peek(Ident) {
        let ident = input.parse::<Ident>()?;

        // Check if it's a data structure keyword
        let ident_str = ident.to_string();
        match ident_str.as_str() {
            "multiset" | "list" | "set" | "map" => {
                // Parse type parameters
                let _ = input.parse::<Token![<]>()?;
                let elem_type = input.parse::<Ident>()?;
                let _ = input.parse::<Token![>]>()?;

                let kind = match ident_str.as_str() {
                    "multiset" => DataStructureKind::Multiset,
                    "list" => DataStructureKind::List,
                    "set" => DataStructureKind::Set,
                    _ => panic!("Unsupported data structure"),
                };

                items.push(GrammarItem::DataStructure {
                    kind,
                    element_type: elem_type,
                });
            }
            _ => {
                // Regular non-terminal
                items.push(GrammarItem::NonTerminal(ident));
            }
        }
    }
}
```

### 2. AST Generation

#### 2.1 Type Selection

**Need to choose concrete Rust types:**

| MeTTaIL Type | Rust Type | Rationale |
|--------------|-----------|-----------|
| `multiset<T>` | `hashbag::HashBag<T>` | O(1) insert/remove, efficient |
| `list<T>` | `Vec<Box<T>>` | Standard dynamic array |
| `set<T>` | `HashSet<T>` | Efficient membership testing |
| `map<K,V>` | `HashMap<K, Box<V>>` | Standard key-value mapping |

**Dependency:** Need to add `hashbag` crate to `runtime`

```toml
# runtime/Cargo.toml
[dependencies]
hashbag = "0.1"  # Or implement our own
```

#### 2.2 Variant Generation

```rust
// In codegen.rs
fn generate_variant(rule: &GrammarRule) -> TokenStream {
    let label = &rule.label;

    // Check for data structures
    let fields: Vec<TokenStream> = rule.items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::NonTerminal(ident) => {
                Some(quote! { Box<#ident> })
            }
            GrammarItem::DataStructure { kind, element_type } => {
                Some(generate_data_structure_type(kind, element_type))
            }
            _ => None,
        })
        .collect();

    if fields.is_empty() {
        quote! { #label }
    } else {
        quote! { #label(#(#fields),*) }
    }
}

fn generate_data_structure_type(
    kind: &DataStructureKind,
    elem_type: &Ident
) -> TokenStream {
    match kind {
        DataStructureKind::Multiset => {
            quote! { mettail_runtime::HashBag<Box<#elem_type>> }
        }
        DataStructureKind::List => {
            quote! { Vec<Box<#elem_type>> }
        }
        DataStructureKind::Set => {
            quote! { std::collections::HashSet<Box<#elem_type>> }
        }
        DataStructureKind::Map { key_type } => {
            quote! { std::collections::HashMap<#key_type, Box<#elem_type>> }
        }
    }
}
```

**Generated AST:**

```rust
pub enum Proc {
    PZero,
    PPar(mettail_runtime::HashBag<Box<Proc>>),
    PInput(Box<Name>, Scope<Binder<String>, Box<Proc>>),
    POutput(Box<Name>, Box<Proc>),
    // ...
}
```

### 3. Parser Generation (LALRPOP)

#### 3.1 The Challenge

**Key question:** How should we parse multiset syntax?

**Option A: Delimited list with explicit braces**
```
PPar := "{" Proc "|" Proc "|" ... "}"
```
- Pro: Explicit boundaries
- Con: Not backward compatible with existing `P | Q` syntax

**Option B: Use `|` as delimiter, collect into multiset**
```
PPar := Proc ("|" Proc)*
```
- Pro: Backward compatible with existing syntax
- Con: Ambiguous - is `P|Q` a binary operator or a 2-element multiset?

**Option C: Special constructor function**
```
PPar := "par" "{" Proc ("," Proc)* "}"
```
- Pro: Explicit multiset construction
- Con: Requires changing existing programs

**Recommended: Hybrid Approach**

Support **both** syntaxes with automatic conversion:

1. **Legacy binary syntax:** `P | Q` → `PPar({P, Q})`
2. **Multiset syntax:** `par{P, Q, R}` → `PPar({P, Q, R})`

#### 3.2 Grammar Generation

```rust
// In lalrpop_gen.rs
fn generate_rule_alternative(rule: &GrammarRule) -> String {
    let label = &rule.label;

    // Check if this rule uses data structures
    let has_multiset = rule.items.iter().any(|item| {
        matches!(item, GrammarItem::DataStructure {
            kind: DataStructureKind::Multiset, ..
        })
    });

    if has_multiset {
        // Generate special multiset parsing rule
        return generate_multiset_alternative(rule);
    }

    // Standard generation
    // ...
}

fn generate_multiset_alternative(rule: &GrammarRule) -> String {
    let label = &rule.label;
    let category = &rule.category;

    // For PPar with multiset<Proc>:
    // Option 1: Parse delimited list
    format!(
        r#""par" "{{" <elems:Comma<{}>> "}}" =>
            {}::{}(elems.into_iter().map(Box::new).collect())"#,
        category, category, label
    )

    // Option 2: Parse infix | as multiset builder
    // This is more complex - needs custom action
}
```

#### 3.3 Backward Compatibility Strategy

**Solution: Generate TWO constructors**

1. **New multiset constructor:** `PPar(HashBag<Box<Proc>>)`
2. **Helper function for binary syntax:**

```rust
// Generated in codegen
impl Proc {
    /// Helper: construct PPar from two processes (for backward compatibility)
    pub fn par(left: Proc, right: Proc) -> Self {
        let mut bag = hashbag::HashBag::new();

        // Flatten if left is already PPar
        match left {
            Proc::PPar(mut sub_bag) => {
                for (proc, count) in sub_bag.set_iter() {
                    for _ in 0..count {
                        bag.insert(Box::new((*proc).clone()));
                    }
                }
            }
            other => {
                bag.insert(Box::new(other));
            }
        }

        // Flatten if right is already PPar
        match right {
            Proc::PPar(mut sub_bag) => {
                for (proc, count) in sub_bag.set_iter() {
                    for _ in 0..count {
                        bag.insert(Box::new((*proc).clone()));
                    }
                }
            }
            other => {
                bag.insert(Box::new(other));
            }
        }

        Proc::PPar(bag)
    }
}
```

**LALRPOP rule:**

```lalrpop
ProcInfix: Proc = {
    <left:ProcInfix> "|" <right:ProcAtom> => Proc::par(left, right),
    <ProcAtom>
};

// OR for explicit multiset syntax:
ProcAtom: Proc = {
    "par" "{" <elems:Comma<Proc>> "}" => {
        let mut bag = hashbag::HashBag::new();
        for elem in elems {
            bag.insert(Box::new(elem));
        }
        Proc::PPar(bag)
    },
    // ... other atom rules
};
```

### 4. Pattern Matching in Rewrite Engine

#### 4.1 The Challenge

**Current pattern:** `(PPar (PInput chan x P) (POutput chan Q))`

With binary `PPar`, this matches the **direct children** of a `PPar` node.

With multiset `PPar`, this should match **any two elements** in the bag.

**Key questions:**
1. How to express "extract two specific elements from a multiset"?
2. What happens to the rest of the elements?
3. How to handle multiplicity (same process appears multiple times)?

#### 4.2 Pattern Semantics

**Option A: Extract and Remove (Recommended)**

Pattern `(PPar P Q)` means:
- Find processes `P` and `Q` in the multiset
- Remove them both
- RHS can reconstruct the multiset with remaining elements

**Syntax:**
```rust
rewrites {
    // Match two specific processes, bind the REST
    if x # Q then (PPar (PInput chan x P) (POutput chan Q) ...rest)
        => (PPar (subst P x (NQuote Q)) ...rest)
}
```

**Option B: Explicit Multiset Operations**

Provide operators for multiset manipulation:
```rust
rewrites {
    // Match: extract two elements
    if x # Q then
        let in = extract (PPar bag) with (PInput chan x P)
        let out = extract bag with (POutput chan Q)
        in is_some and out is_some
    then
        (PPar (insert (insert rest_bag (subst P x (NQuote Q))) PZero))
}
```

Too verbose, not recommended.

**Option C: Implicit Rest Parameter**

Pattern matching automatically binds `@rest` for remaining elements:

```rust
rewrites {
    // Pattern: PPar{PInput, POutput, @rest}
    if x # Q then (PPar (PInput chan x P) (POutput chan Q))
        => (PPar (subst P x (NQuote Q)))
        // Implicitly: @rest is merged back in
}
```

#### 4.3 Implementation Strategy

**Generate specialized matching code:**

```rust
pub fn try_rewrite_rule_0(term: &Proc) -> Option<Proc> {
    if let Proc::PPar(bag) = term {
        // Try to find PInput in the bag
        for input_proc in bag.iter() {
            if let Proc::PInput(chan, scope_field) = &(**input_proc) {
                let (binder, body) = scope_field.clone().unbind();

                // Try to find matching POutput
                for output_proc in bag.iter() {
                    if let Proc::POutput(chan2, q) = &(**output_proc) {
                        // Check channels match
                        if chan != chan2 {
                            continue;
                        }

                        // Freshness check
                        if !is_fresh(&binder, &(**q)) {
                            continue;
                        }

                        // Found a match! Construct result
                        let mut result_bag = bag.clone();
                        result_bag.remove(input_proc);
                        result_bag.remove(output_proc);

                        let substituted = (*body).clone()
                            .substitute_name(&binder.0, &Name::NQuote(q.clone()));

                        result_bag.insert(Box::new(substituted));

                        return Some(Proc::PPar(result_bag));
                    }
                }
            }
        }
    }
    None
}
```

**Key features:**
1. **Double iteration** - try all pairs
2. **Clone and modify** - remove matched elements, add result
3. **Early continue** - skip non-matching elements
4. **Automatic rest handling** - remaining elements stay in the bag

#### 4.4 Pattern Syntax Extension

Need to extend the pattern language to support:

1. **Matching specific elements:**
   ```rust
   (PPar P Q)  // Match any two processes
   ```

2. **Matching specific elements with rest:**
   ```rust
   (PPar P Q ...R)  // Match P, Q, bind rest to R
   ```

3. **Matching zero or more:**
   ```rust
   (PPar ...)  // Match any multiset (trivial)
   ```

4. **Matching specific count:**
   ```rust
   (PPar P{2})  // Match two copies of P
   ```

**For Phase 1, recommend:** Support only simple pattern `(PPar P Q)` with implicit rest.

### 5. Substitution

#### 5.1 Substitution into Multisets

**Question:** What does `subst (PPar bag) x t` mean?

**Answer:** Substitute into each element of the bag.

```rust
// In substitution.rs
impl Proc {
    pub fn substitute_name(self, var: &FreeVar<String>, replacement: &Name) -> Self {
        match self {
            Proc::PPar(bag) => {
                let new_bag = bag.into_iter()
                    .map(|proc| {
                        Box::new((*proc).substitute_name(var, replacement))
                    })
                    .collect();
                Proc::PPar(new_bag)
            }
            // ... other cases
        }
    }
}
```

**Generated code:**

```rust
match self {
    Proc::PPar(bag) => {
        Proc::PPar(
            bag.into_iter()
                .map(|elem| Box::new((*elem).substitute_name(var, replacement)))
                .collect()
        )
    }
}
```

### 6. Display (Pretty-Printing)

#### 6.1 How to Print Multisets?

**Options:**

1. **Infix `|` (backward compatible):**
   ```
   P | Q | R
   ```

2. **Braced list:**
   ```
   par{P, Q, R}
   ```

3. **Hybrid:** Use infix for 2-3 elements, braced for more:
   ```
   P | Q                // 2 elements
   par{P, Q, R, S, T}   // 5 elements
   ```

**Recommendation:** Infix `|` for backward compatibility.

```rust
// In display_gen.rs
match self {
    Proc::PPar(bag) => {
        let elements: Vec<_> = bag.iter().collect();
        if elements.is_empty() {
            write!(f, "0")  // Empty multiset = identity
        } else if elements.len() == 1 {
            write!(f, "{}", elements[0])
        } else {
            write!(f, "{}", elements[0])?;
            for elem in &elements[1..] {
                write!(f, " | {}", elem)?;
            }
            Ok(())
        }
    }
}
```

**Issue:** HashBag iteration order is non-deterministic!

**Solution:** Sort elements before printing (need `Ord` on `Proc`).

### 7. Type System Extensions

#### 7.1 Type Checking Data Structures

Need to track that `multiset<Proc>` is a valid type.

```rust
// In typechecker.rs
fn check_grammar_item_type(
    item: &GrammarItem,
    categories: &HashSet<String>
) -> Result<(), TypeError> {
    match item {
        GrammarItem::DataStructure { element_type, .. } => {
            // Check that element_type is a known category
            if !categories.contains(&element_type.to_string()) {
                return Err(TypeError::UnknownCategory(element_type.clone()));
            }
            Ok(())
        }
        // ... other cases
    }
}
```

#### 7.2 Equation Obsolescence

**Key insight:** With multiset `PPar`, we **no longer need equations** for:
- Commutativity: Built into HashBag
- Associativity: Flat structure, not nested
- Identity: Empty multiset

**Action:** When a constructor uses a multiset, **deprecate or warn** if equations are defined for it.

```rust
// In validator.rs
fn validate_theory(theory: &TheoryDef) -> Result<(), ValidationError> {
    // Check for obsolete equations
    for rule in &theory.terms {
        let has_multiset = rule.items.iter().any(|item| {
            matches!(item, GrammarItem::DataStructure {
                kind: DataStructureKind::Multiset, ..
            })
        });

        if has_multiset {
            // Check if equations reference this constructor
            for eq in &theory.equations {
                if equation_references_constructor(eq, &rule.label) {
                    eprintln!(
                        "Warning: Equation for {} is obsolete with multiset representation",
                        rule.label
                    );
                }
            }
        }
    }

    Ok(())
}
```

---

## 🏗️ Implementation Plan

### Phase 1: Foundation (Week 1-2)

**Goal:** Get basic multiset support working without breaking existing functionality.

**Tasks:**
1. ✅ **Add `hashbag` dependency** to `runtime`
2. ✅ **Extend `GrammarItem`** enum with `DataStructure` variant
3. ✅ **Parse `multiset<T>` syntax** in grammar rules
4. ✅ **Generate multiset AST types** in `codegen.rs`
5. ✅ **Test:** Basic AST generation with multiset fields

**Deliverable:** Theory with multiset compiles and generates AST.

**Test case:**
```rust
theory! {
    name: TestMultiset,
    exports { Proc }
    terms {
        PZero . Proc ::= "0" ;
        PPar . Proc ::= multiset<Proc> ;
    }
}
```

### Phase 2: Parser Integration (Week 3-4)

**Goal:** Parse multiset syntax in LALRPOP.

**Tasks:**
1. ✅ **Generate helper `par()` function** for binary compat
2. ✅ **Generate LALRPOP rules** for infix `|` → multiset conversion
3. ✅ **Handle empty multiset** (identity element)
4. ✅ **Test:** Parse `P | Q | R` → `PPar({P, Q, R})`

**Deliverable:** Can parse programs into multiset-based AST.

### Phase 3: Pattern Matching (Week 5-8)

**Goal:** Rewrite rules work with multisets.

**Tasks:**
1. ✅ **Detect multiset patterns** in rewrite LHS
2. ✅ **Generate multiset matching code** (double iteration)
3. ✅ **Handle element extraction** and rest reconstruction
4. ✅ **Test:** Communication rule works with multisets

**Deliverable:** Rewrite rules execute correctly on multiset terms.

### Phase 4: Substitution & Display (Week 9-10)

**Goal:** Complete feature parity.

**Tasks:**
1. ✅ **Generate substitution for multisets** (map over elements)
2. ✅ **Generate Display impl** (infix `|` with sorted elements)
3. ✅ **Add `Ord` derivation** for deterministic printing
4. ✅ **Test:** Full round-trip (parse → display → parse)

**Deliverable:** Multiset-based Rho Calculus fully working.

### Phase 5: Validation & Polish (Week 11-12)

**Goal:** Production-ready multiset support.

**Tasks:**
1. ✅ **Deprecation warnings** for obsolete equations
2. ✅ **Documentation** for multiset syntax
3. ✅ **Examples** for multiple data structures
4. ✅ **Performance benchmarks** (multiset vs. binary tree)

**Deliverable:** Ship multiset support in MeTTaIL v0.2.

---

## 🔬 Design Alternatives Considered

### Alternative 1: E-graph Only

**Idea:** Keep binary `PPar`, use e-graphs for equation handling.

**Pros:**
- No syntax changes
- Matches Phase 5 plan
- Theoretically elegant

**Cons:**
- Still inefficient for runtime (deep trees)
- Requires Phase 5 completion (months away)
- Doesn't match real implementations

**Verdict:** ❌ Rejected. E-graphs are good for optimization, but runtime needs efficient data structures.

### Alternative 2: Array-Based Multiset

**Idea:** Use `Vec<Box<Proc>>` instead of `HashBag`.

**Pros:**
- No new dependency
- Simple implementation
- Cache-friendly

**Cons:**
- O(n) lookup and removal
- Must sort for canonicalization
- Multiplicities not tracked

**Verdict:** 🤔 Possible fallback if `hashbag` issues arise.

### Alternative 3: Explicit Multiset Constructors

**Idea:** Add explicit syntax for multiset literals:

```rust
PPar . Proc ::= "{|" (Proc ",")* "|}" ;
```

**Pros:**
- Clear distinction from binary `|`
- No parsing ambiguity
- Familiar to mathematical notation

**Cons:**
- Not backward compatible
- Verbose
- Harder to type

**Verdict:** ❌ Rejected for primary syntax, but could be alternate notation.

### Alternative 4: Generic Data Structure Framework

**Idea:** Support ALL data structures from the start (list, set, map, tree, etc.)

**Pros:**
- Maximum flexibility
- Future-proof

**Cons:**
- Massive complexity increase
- Unclear use cases for most structures
- YAGNI (You Aren't Gonna Need It)

**Verdict:** ⏳ Defer. Start with multiset, add others as needed.

---

## 🚧 Migration Path

### For Existing Theories

**Question:** How do existing theories using binary `PPar` migrate?

**Answer: Automatic Migration**

1. **Parser compatibility:** Old syntax `P | Q` still works, gets converted to multiset
2. **Generated code:** Multiset-based AST is a drop-in replacement
3. **Deprecation warnings:** Equations for commutativity/associativity trigger warnings

**Example migration:**

**Before (v0.1):**
```rust
theory! {
    name: RhoCalc,
    terms {
        PPar . Proc ::= Proc "|" Proc ;
    }
    equations {
        (PPar P Q) == (PPar Q P) ;
        (PPar P (PPar Q R)) == (PPar (PPar P Q) R) ;
        (PPar P PZero) == P ;
    }
}
```

**After (v0.2):**
```rust
theory! {
    name: RhoCalc,
    terms {
        PPar . Proc ::= multiset<Proc> ;
    }
    // Equations removed - built into multiset!
}
```

**Migration script:**
```bash
# Automated migration tool (future)
$ mettail migrate theory.rs
Migrated PPar from binary to multiset
Removed 3 obsolete equations
```

---

## 🧪 Testing Strategy

### Unit Tests

1. **AST Generation:**
   - Generate multiset fields correctly
   - Derive `Hash`, `Eq` for multiset types

2. **Parser:**
   - Parse `P | Q` → multiset
   - Parse `P | Q | R | S` → multiset
   - Parse empty multiset (`0`)

3. **Pattern Matching:**
   - Match two elements in multiset
   - Handle non-matching cases
   - Preserve rest of multiset

4. **Substitution:**
   - Substitute into all elements
   - Preserve multiset structure

### Integration Tests

1. **Rho Calculus:**
   - Communication rule works with multiset `PPar`
   - Reduction sequences preserve semantics

2. **Round-trip:**
   - Parse → Display → Parse produces equivalent AST

3. **Performance:**
   - Benchmark multiset vs. binary tree
   - Target: 10x speedup for n > 10 processes

### Regression Tests

Ensure existing functionality still works:
- Binary `PPar` parsing (compatibility mode)
- Binder handling
- Cross-category substitution

---

## 📚 Open Questions

### 1. Multiplicity Handling

**Question:** Should `PPar{P, P}` be distinct from `PPar{P}`?

**Context:** HashBag supports multiplicities, but semantics unclear.

**Options:**
- **A:** Treat as multiset (P appears twice)
- **B:** Treat as set (duplicate removed)
- **C:** User-configurable

**Recommendation:** **A** (multiset). Matches process calculus semantics where `P|P` ≠ `P`.

### 2. Ordering for Display

**Question:** How to order elements when printing multisets?

**Options:**
- **A:** Random (HashBag iteration order)
- **B:** Sorted (requires `Ord` on Proc)
- **C:** Insertion order (requires Vec backing)

**Recommendation:** **B** (sorted). Deterministic output essential for testing.

**Issue:** Recursive types can't auto-derive `Ord`. Need custom implementation.

### 3. Pattern Matching Complexity

**Question:** What patterns should we support?

**Minimum (Phase 1):**
- `(PPar P Q)` - match any two elements

**Nice to have (Future):**
- `(PPar P Q ...R)` - match two and bind rest
- `(PPar P{n})` - match n copies of P
- `(PPar P where pred)` - match with predicate

**Recommendation:** Start minimal, extend based on user needs.

### 4. Performance vs. Semantics Trade-offs

**Question:** Should we allow user control over internal representation?

**Idea:** Annotations for performance tuning:

```rust
PPar . Proc ::= multiset<Proc> @backend("hashbag") ;
// Or: @backend("vec"), @backend("btree"), etc.
```

**Verdict:** ⏳ Defer to Phase 6 (optimization).

### 5. Interaction with E-graphs (Phase 5)

**Question:** How do multisets interact with equation handling?

**Scenario:** If we add multisets now, will it break e-graph integration later?

**Analysis:**
- E-graphs work on term equivalence
- Multisets are already canonical (no equations needed)
- Should be compatible, but needs prototyping

**Action:** Document this design constraint for Phase 5.

---

## 📈 Success Metrics

### Phase 1 Success

- ✅ Theory with multiset compiles
- ✅ AST generated correctly
- ✅ No existing tests break

### Phase 2 Success

- ✅ Parse `P | Q | R` into multiset
- ✅ Round-trip tests pass
- ✅ Backward compatibility maintained

### Phase 3 Success

- ✅ Communication rule executes correctly
- ✅ Pattern matching works on multisets
- ✅ Performance improvement measured

### Phase 4 Success

- ✅ Full Rho Calculus works with multisets
- ✅ Substitution correct
- ✅ Display output deterministic

### Overall Success

- 📊 **10x speedup** for parallel composition with n > 10
- 🎯 **Zero breaking changes** for existing theories
- 📚 **Documentation complete** with examples
- ✅ **All tests passing** (unit + integration)

---

## 🔄 Next Steps

### Immediate (This Week)

1. Review this design with team
2. Prototype `GrammarItem::DataStructure` in branch
3. Add `hashbag` to dependencies
4. Begin Phase 1 implementation

### Short Term (Next Month)

1. Complete Phase 1-2 (AST + Parser)
2. Update Rho Calculus example
3. Document multiset syntax

### Medium Term (2-3 Months)

1. Complete Phase 3-4 (Pattern Matching + Substitution)
2. Performance benchmarks
3. Publish v0.2 with multiset support

### Long Term (6+ Months)

1. Extend to other data structures (list, set, map)
2. E-graph integration with multisets
3. Generic data structure framework

---

## 📝 References

### Related Papers

1. **Process Calculi Implementations**
   - Rholang: Uses multisets for parallel composition
   - Pict: Hash-based process storage

2. **Data Structures**
   - "Purely Functional Data Structures" (Okasaki) - persistent bags
   - "Hash Array Mapped Tries" - efficient persistent maps

3. **Rewriting Systems**
   - "Term Rewriting and All That" (Baader & Nipkow) - matching strategies
   - K Framework documentation - multiset rewriting

### Rust Crates

- `hashbag` - multiset implementation
- `im` - persistent data structures
- `indexmap` - ordered HashMap (possible alternative)

---

**Status:** Ready for implementation
**Estimated Effort:** 8-12 weeks (full multiset support)
**Risk Level:** Medium (major refactor but well-scoped)
**Impact:** High (enables efficient process calculus execution)


