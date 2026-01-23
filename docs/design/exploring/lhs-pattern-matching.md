# LHS Pattern Matching for Collection Comprehensions

**Status:** Design  
**Date:** January 2026  
**Prerequisite:** Multi-substitution (completed)

---

## 1. Goal

Enable pattern matching that extracts multiple elements from collections based on join conditions. The motivating example is multi-channel communication in Rho Calculus:

```rust
// Multi-communication rule
(PPar {(PInputs ns scope), #zip(ns,qs).#map(|n,q| POutput n q)})
    => (multisubst scope qs.#map(|q| NQuote q))
```

This matches:
```
{ for(x0<-n0, x1<-n1){p}, n0!(q0), n1!(q1), ...other... }
```

And extracts:
- `ns = [n0, n1]` — from `PInputs`
- `scope = ^[x0,x1].p` — from `PInputs`  
- `qs = [q0, q1]` — by matching outputs against names

---

## 2. Syntax and Semantics

### 2.1 The `#zip` + `#map` Pattern

```
#zip(bound_collection, unbound_collection).#map(|x,y| Pattern)
```

| Component | Role |
|-----------|------|
| `bound_collection` | Already bound from earlier in pattern (e.g., `ns` from `PInputs`) |
| `unbound_collection` | Being extracted (e.g., `qs`) |
| `|x,y|` | Lambda params: `x` iterates `bound`, `y` is extracted into `unbound` |
| `Pattern` | What to match for each element (e.g., `POutput n q`) |

### 2.2 Binding Direction Inference

The macro determines bound vs. unbound from **pattern context**:

1. Scan the full LHS pattern left-to-right
2. Variables bound earlier (e.g., `ns` in `PInputs ns scope`) are **bound**
3. New variables in `#zip` second position are **unbound** (being extracted)
4. Variables in `#map` lambda params shadow outer bindings within the body

Example:
```rust
(PPar {(PInputs ns scope), #zip(ns,qs).#map(|n,q| POutput n q)})
//              ^^         bound                   ↑match  ↑extract
//                         ^^                      
//                         unbound (new)
```

### 2.3 Dual Semantics

The same syntax has dual meaning in LHS vs RHS:

| Context | `#zip(A,B).#map(|a,b| Pattern)` |
|---------|--------------------------------|
| **RHS** (construction) | Zip A,B → map to Pattern → produce list |
| **LHS** (matching) | For each `a` in A, find Pattern, collect `b` into B |

This mirrors parsing/display duality.

---

## 3. Datalog Generation

### 3.1 Generated Clause Structure

For the multi-comm pattern:

```rust
// Input: (PPar {(PInputs ns scope), #zip(ns,qs).#map(|n,q| POutput n q)})

proc(p0),
if let Proc::PPar(bag) = p0,

// Step 1: Extract PInputs, binding ns and scope
if let Some((ns, scope)) = extract_pinputs_from_bag(&bag),

// Step 2: Match outputs for each n in ns, collecting qs
if let Some(qs) = match_zip_pattern(&bag, &ns),

// Step 3: Compute RHS
let result = { 
    let (__binders, __body) = scope.clone().unbind();
    let __vars: Vec<_> = __binders.iter().map(|b| &b.0).collect();
    let __repls: Vec<_> = qs.iter().map(|q| Name::NQuote(Box::new(q.clone()))).collect();
    (*__body).multi_substitute_name(&__vars, &__repls)
};
```

### 3.2 Helper Function Generation

The macro generates a specialized match function:

```rust
/// Generated for: #zip(ns,qs).#map(|n,q| POutput n q)
fn match_zip_pattern(bag: &HashBag<Proc>, ns: &[Name]) -> Option<Vec<Proc>> {
    let mut qs = Vec::with_capacity(ns.len());
    
    for n in ns.iter() {
        // Find POutput(n, q) in bag where first arg matches n
        let q = bag.iter().find_map(|(elem, _count)| {
            match elem {
                Proc::POutput(out_n, out_q) if out_n.as_ref() == n => {
                    Some((**out_q).clone())
                }
                _ => None
            }
        })?;  // Return None if any n has no matching output
        
        qs.push(q);
    }
    
    Some(qs)
}
```

### 3.3 Pattern Analysis

The code generator must:

1. **Parse the `#map` body** to identify:
   - Constructor being matched (`POutput`)
   - Which lambda param is the join key (`n` → position 0)
   - Which lambda param is being extracted (`q` → position 1)

2. **Generate field access** based on constructor structure:
   - `POutput` has fields `(Box<Name>, Box<Proc>)`
   - Join on field 0, extract field 1

3. **Handle nested patterns** (future):
   - `#map(|n,q| POutput n (PSome q))` — extract from nested position

---

## 4. Implementation Plan

### Phase 1: AST Support (1 day)

- [x] `Expr::Map` variant exists
- [ ] Add `ZipMapPattern` analysis struct:
  ```rust
  struct ZipMapPattern {
      bound_collection: Ident,      // e.g., ns
      unbound_collection: Ident,    // e.g., qs  
      bound_param: Ident,           // e.g., n
      extracted_param: Ident,       // e.g., q
      constructor: Ident,           // e.g., POutput
      join_field_idx: usize,        // which field has bound_param
      extract_field_idx: usize,     // which field has extracted_param
  }
  ```
- [ ] Add pattern analysis function to extract `ZipMapPattern` from `Expr::Map`

### Phase 2: Binding Analysis (1 day)

- [ ] Implement `collect_bound_variables(expr: &Expr) -> HashSet<String>`
  - Walks pattern, collects all variables that would be bound
- [ ] Implement `classify_zip_bindings(zip_expr, bound_vars) -> (bound, unbound)`
  - Given `#zip(A,B)`, determines which is bound vs unbound
- [ ] Add validation: first `#zip` arg must be bound, second must be unbound

### Phase 3: Datalog LHS Generation (2 days)

- [ ] Extend `generate_ascent_pattern` to handle `Expr::Map` with `#zip` source
- [ ] Generate extraction helper function for each unique `#zip.#map` pattern
- [ ] Generate `if let Some(unbound) = match_helper(&bag, &bound)` clause
- [ ] Handle collection type (Vec vs HashBag) in iteration

### Phase 4: Integration (1 day)

- [ ] Wire up pattern generation to rewrite rule processing
- [ ] Ensure `qs` is available as binding in RHS generation
- [ ] Test with multi-communication rule

### Phase 5: Testing (1 day)

- [ ] Unit test: pattern analysis extracts correct `ZipMapPattern`
- [ ] Unit test: binding classification works correctly
- [ ] Integration test: full multi-comm rule parses and generates valid Datalog
- [ ] Runtime test: multi-comm actually reduces correctly

---

## 5. Edge Cases

### 5.1 Multiple Matches

What if multiple outputs match the same name?

```
{ for(x<-n){p}, n!(q1), n!(q2) }
```

**Current design:** First match wins (via `find_map`).  
**Alternative:** Could require exactly one match, or collect all.

### 5.2 Missing Matches

What if some name has no matching output?

```
{ for(x0<-n0, x1<-n1){p}, n0!(q0) }  // n1 has no output!
```

**Design:** Pattern fails to match (returns `None`). Rule doesn't fire.

### 5.3 Extra Outputs

What if there are outputs for names not in `ns`?

```
{ for(x<-n0){p}, n0!(q0), n1!(q1) }  // n1 not in ns
```

**Design:** Extra outputs are ignored. Only `ns` determines what to match.

### 5.4 `...rest` Interaction

```rust
(PPar {(PInputs ns scope), #zip(ns,qs).#map(|n,q| POutput n q), ...rest})
```

The `...rest` should capture remaining elements after:
1. Removing the `PInputs`
2. Removing the matched `POutput` terms

**Implementation:** Track which bag elements were consumed by pattern matching.

---

## 6. Example Trace

Input process:
```
{ for(x0<-@(0), x1<-@(1)){*(x0)|*(x1)}, @(0)!(0), @(1)!(0) }
```

Pattern matching:
1. Match `PPar(bag)` ✓
2. Find `PInputs` → `ns = [@(0), @(1)]`, `scope = ^[x0,x1].{*(x0)|*(x1)}`
3. For `n = @(0)`: find `POutput(@(0), 0)` → `q = 0`
4. For `n = @(1)`: find `POutput(@(1), 0)` → `q = 0`
5. Result: `qs = [0, 0]`

RHS construction:
1. `multisubst scope qs.#map(|q| NQuote q)`
2. Map qs: `[@(0), @(0)]`
3. Unbind scope: `([x0, x1], {*(x0)|*(x1)})`
4. Multi-substitute: `{*(@(0))|*(@(0))}`

Final result:
```
{ {*(@(0))|*(@(0))} }  // The inner par with substituted body
```

---

## 7. Summary

| Aspect | Decision |
|--------|----------|
| Syntax | `#zip(bound,unbound).#map(\|x,y\| Pattern)` |
| Binding inference | From pattern context (earlier = bound) |
| Match semantics | For each in bound, find Pattern, collect into unbound |
| Missing match | Pattern fails (None), rule doesn't fire |
| Multiple match | First wins |
| Extra elements | Ignored |
| Rest capture | Supported via `...rest` |

**Estimated effort:** 5-6 days  
**Dependencies:** Multi-substitution (✓), `Expr::Map` AST (✓)  
**Risk:** Medium (pattern analysis complexity)
