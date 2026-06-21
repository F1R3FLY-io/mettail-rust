# Session Summary: Equational Rewrite Engine & Performance Analysis

**Date**: November 2025
**Status**: Major milestone completed ✅

---

## 🎯 What Was Accomplished

### 1. Ascent-Based Rewrite Engine (COMPLETE)

**Problem**: Original rewrite engine used syntactic equality, preventing matching modulo equations.

**Example**:
```rust
// Rewrite: for(chan x){P} | chan!(Q) => P[@Q/x]
// Should match when channels are EQUAL, not just syntactically identical
for(@(0) x){P} | @(0|0)!(Q)  // Should match if @(0) == @(0|0)
```

**Solution**: Generated rewrite rules as Ascent clauses with equational matching.

#### Key Innovations

1. **Duplicate Variable Detection**
   - Track variables appearing multiple times in LHS
   - Generate `eq_cat()` checks instead of syntactic equality

2. **Explicit Category Tracking**
   - Eliminated heuristic-based type inference
   - Track variable categories during pattern matching
   - Derive types from constructor applications

3. **Reflexivity Rules**
   - Added `eq_cat(t, t) <-- cat(t)` for all categories
   - Seed `eqrel` data structure with identity relations

4. **Snake_case Compliance**
   - Convert all variable names to snake_case in generated code
   - Eliminate linter warnings

#### Generated Code Example

```rust
rw_proc(s, t) <--
    proc(s),
    if let Proc::PPar(s_f0, s_f1) = s,
    if let Proc::PInput(s_f0_f0_scope) = &**s_f0,
    let (chan, x_scope) = s_f0_f0_scope.clone().unbind(),
    let (x, p) = x_scope.unbind(),
    if let Proc::POutput(chan2, q) = &**s_f1,

    // Equational matching (NEW!)
    eq_name((**chan).clone(), (**chan2).clone()),

    if mettail_runtime::is_fresh(&x.0, &**q),
    let t = p.substitute_name(&x.0, &Name::NQuote((**q).clone()));
```

### 2. Performance Analysis & Diagnosis

#### Current Performance
- **Small terms (depth ≤3)**: ~1 second
- **Medium terms (depth 4-5)**: ~10 seconds
- **Complex terms (depth 6+)**: 60-80 seconds

#### Root Cause Identified

**Binary associative-commutative operations** (e.g., `PPar . Proc ::= Proc "|" Proc`) cause exponential blowup:

1. **Equations generate many equivalences**:
   ```
   (PPar P Q) == (PPar Q P)                    // Commutativity
   (PPar P (PPar Q R)) == (PPar (PPar P Q) R) // Associativity
   ```

2. **Congruence rules amplify exponentially**:
   ```
   if S => T then (PPar P S) => (PPar P T)
   ```

3. **Result**: For term `a|b|c|d|e`, Ascent generates thousands of equivalent representations

#### Proposed Solution: Collection Types

See [Collection Types Design](design/COLLECTION-TYPES-DESIGN.md) for full details.

**Key Idea**: Replace binary constructors with multisets:
```rust
// Before
PPar . Proc ::= Proc "|" Proc ;
// Generates: Proc::PPar(Box<Proc>, Box<Proc>)

// After
PPar . Proc ::= HashBag(Proc) sep "|" ;
// Generates: Proc::PPar(HashBag<Proc>)
```

**Expected Speedup**: 100x+ (< 1 second for complex terms)

---

## 🔧 Technical Deep Dives

### Eliminating Type Inference Heuristics

**Problem**: Variable types were guessed from naming conventions:
```rust
// Heuristic: starts with 'n' → Name, otherwise → Proc
if var_lower.starts_with('n') { /* Name */ }
```

**Solution**: Explicit category tracking:
```rust
fn generate_ascent_pattern(
    expr: &Expr,
    term_name: &Ident,
    expected_category: &Ident,  // ← NEW: pass down from parent
    // ...
    variable_categories: &mut HashMap<String, Ident>,  // ← NEW: track bindings
) {
    match expr {
        Expr::Var(v) if duplicate_vars.contains(v) => {
            if !variable_categories.contains_key(v) {
                // First occurrence: record category
                variable_categories.insert(v.clone(), expected_category.clone());
            }
            // Subsequent occurrences: use recorded category
            let cat = &variable_categories[v];
            let eq_rel = format_ident!("eq_{}", cat.to_lowercase());
            equational_checks.push(quote! {
                if #eq_rel(#first_binding.clone(), #current_binding.clone())
            });
        }
    }
}
```

**Result**: Type-safe, robust, no heuristics.

### Congruence Rule Generation Issues

**Initial Approach**: Automatically generate congruence for all constructors:
```rust
eq_proc(Proc::PPar(p1, q1), Proc::PPar(p2, q2)) <--
    proc(p1), proc(p2), proc(q1), proc(q2),
    eq_proc(p1, p2), eq_proc(q1, q2);
```

**Problem**: Exponential blowup for large terms.

**Current Status**: Congruence rules temporarily disabled. Ascent's `eqrel` handles transitivity and symmetry automatically, but user must explicitly state all base equalities.

**Future Work**: Selective congruence generation based on term structure analysis.

---

## 📊 Metrics

### Code Generation
| Metric | Value |
|--------|-------|
| Core implementation | ~5500 LOC |
| Generated (rhocalc) | ~13000 LOC |
| Compile time | 0.8s |

### Performance (Rhocalc)
| Term Depth | Rewrites | Time |
|------------|----------|------|
| 3 | ~10 | ~1s |
| 4 | ~50 | ~10s |
| 6 | ~100+ | 60-80s |

### Features
- ✅ Equational matching
- ✅ Nested pattern matching (arbitrary depth)
- ✅ Type-aware variable binding
- ✅ Freshness checking
- ✅ Cross-category substitution
- ✅ Term generation (exhaustive + random)
- ⚠️ Performance (needs collection types)

---

## 🎯 Next Steps

### Immediate (Performance)
1. **Implement `HashBag<T>` in `runtime`**
   - Multiset with `HashMap<T, usize>` backing
   - `Clone + Eq + Hash + Ord + BoundTerm`
2. **Extend grammar syntax for collections**
   - `HashBag(T) sep "|"`
   - `HashSet(T) sep ","`
   - `Vec(T) sep ";"`
3. **Update codegen for collection types**
   - AST generation
   - Parser generation
   - Display generation
   - Substitution generation
4. **Pattern matching over collections**
   - Extract elements from bags
   - Rest patterns
   - Equational matching within bags

### Medium Term (Type System)
1. **Category inference refinement**
2. **Better error messages for type mismatches**
3. **Type constraints in theory definitions**

### Long Term (Theory Composition)
1. **Theory imports and parameters**
2. **Module system**
3. **E-graph integration**

---

## 🔍 Key Insights

1. **Ascent + Equational Matching is Powerful**: Leveraging Datalog semantics for rewrite matching provides elegant transitive closure and symmetry for free.

2. **Performance Matters Early**: The 80-second rewrite times, while acceptable for small demos, are a blocker for real-world use. Collection-based representations are essential.

3. **Type Safety is Non-Negotiable**: Heuristic-based type inference led to subtle bugs. Explicit tracking eliminates entire classes of errors.

4. **Code Generation Complexity**: The generated Ascent code is verbose (~13K LOC), but correctness and maintainability are more important than brevity.

5. **Datalog is Not Free**: Ascent's relation overhead is significant. Future work should explore compiled/specialized data structures.

---

## 📚 Related Documentation

- [Collection Types Design](design/COLLECTION-TYPES-DESIGN.md)
- [Rewrite Equational Matching Design](design/REWRITE-EQUATIONAL-MATCHING.md)
- [Variable Equality Implementation](../VARIABLE-EQUALITY-IMPLEMENTATION.md)
- [Binder Shadowing Fix](design/BINDER-SHADOWING-FIX.md)
- [Term Generation Assumptions](design/TERM-GENERATION-ASSUMPTIONS.md)
- [Phase 2 Complete](phase-2/PHASE-2-COMPLETE.md)

---

## 🙏 Acknowledgments

This work builds on:
- **Ascent**: Datalog in Rust (s-arash/ascent)
- **moniker**: Locally nameless binders (brendanzab/moniker)
- **LALRPOP**: Parser generator (lalrpop/lalrpop)
- **MeTTa**: Inspiration for metalanguage design

