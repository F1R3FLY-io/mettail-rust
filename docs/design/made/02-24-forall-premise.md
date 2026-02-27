# 02-24: ForAll premise and scope extrusion

## Motivation

RhoCalc's scope extrusion equation requires a universally quantified freshness condition:

```
Extrude . xs.*map(|x| x # ...rest)
    |- (PPar {(PNew ^[xs].p), ...rest}) = (PNew ^[xs].(PPar {p, ...rest}))
```

This says: a `new` binder can be moved outside a parallel composition *if every bound name is fresh in the remaining parallel elements*. The existing `Premise` enum only supported single predicates (`x # P`, `S ~> T`, `rel(args)`), with no way to express universal quantification over a collection.

## Design

Added a `ForAll` variant rather than `Vec<Premise>` or a conjunction combinator. This is compositional — `ForAll` wraps a single body `Premise` and can be nested or combined with other premise types in the future.

### Syntax

```
ident.*map(|ident| premise)
```

The parser recognizes the `.*map(` token sequence after an identifier and parses the closure-style `|param|` body recursively via `parse_premise`.

### AST

```rust
pub enum Premise {
    Freshness(FreshnessCondition),
    Congruence { source: Ident, target: Ident },
    RelationQuery { relation: Ident, args: Vec<Ident> },
    ForAll { collection: Ident, param: Ident, body: Box<Premise> },
}

pub enum Condition {
    Freshness(FreshnessCondition),
    EnvQuery { relation: Ident, args: Vec<Ident> },
    ForAll { collection: Ident, param: Ident, body: Box<Condition> },
}
```

`Premise` is the parsed representation; `Condition` is the internal form used during codegen (omitting `Congruence`, which is handled separately by the congruence pipeline).

### Collection-variable binder matching

The LHS pattern `(PNew ^[xs].p)` uses a single variable `xs` in a `MultiLambda` position. This triggers "collection-variable mode": `xs` binds to the entire `Vec<Binder<String>>` from the scope (rather than iterating individual binders). The RHS reconstructs the scope using this vector directly via `Scope::from_parts_unsafe`.

### Code generation

`generate_forall_clause` translates `ForAll` with a `Freshness` body into Ascent `if` guards. For the extrusion equation:

```
xs.*map(|x| x # ...rest)
```

generates:

```rust
if xs_binding.iter().all(|x|
    rest_binding.clone().iter().all(|(elem, _)|
        !BoundTerm::free_vars(elem).contains(&x.0)
    )
)
```

This checks that *every* binder name in `xs` is absent from the free variables of *every* element in `...rest`.

### Equation-rewrite closure

The Extrude equation produces `eq_proc(A, B)` entries, but congruence rules match `proc(lhs)` directly (not through `eq_proc`). When the equation rewrites the structural form and congruence fires on the new form, rewrites from the original term were missing. Fixed by adding a closure rule for every category:

```
rw_cat(a, c) <-- eq_cat(a, b), rw_cat(b, c);
```

This is a no-op when `eq` only has reflexive entries (the common case without user-defined equations).

## Files changed

| File | Change |
|---|---|
| `macros/src/ast/language.rs` | `ForAll` on `Premise` and `Condition`; `parse_premise` extended |
| `macros/src/ast/validation/validator.rs` | `validate_premise` handles `ForAll` recursively |
| `macros/src/gen/runtime/metadata.rs` | `premise_to_display_string` for `ForAll` |
| `macros/src/logic/rules.rs` | `premise_to_condition` and `generate_forall_clause` |
| `macros/src/logic/mod.rs` | Equation-rewrite closure rule generation |
| `macros/src/ast/pattern.rs` | Collection-variable binder matching in `generate_clauses` and `to_ascent_rhs` |
| `languages/src/rhocalc.rs` | `Extrude` equation added |

## Example: scope extrusion in action

```
Input:  { new(x) in { (a?z).{*(z)} } | a!(0) }
  =extrude=  new(x) in { { (a?z).{*(z)} | a!(0) } }
  →comm→     new(x) in { { *(@(0)) } }
  →exec→     new(x) in { 0 }
```

The freshness check passes because `x` does not appear free in `a!(0)`. If the bound name were `a` instead of `x`, extrusion would be blocked — `a` appears free in `a!(0)`.
