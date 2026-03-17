# Generated Relation Schema

PraTTaIL's `language!` macro generates a set of Ascent relations for each syntactic category. These relations form the "database schema" of the Datalog program: category membership, equality, rewriting, folding, collection projections, and user-defined custom relations.

**Prerequisites:** [Ascent Overview](overview.md)

---

## 1. Category Relations

For each type declared in `language! { types { ... } }`, a unary relation is generated:

```text
relation proc(Proc);     // Category membership: all known Proc terms
relation name(Name);     // Category membership: all known Name terms
```

These are the **ground truth** relations. Every term discovered during exploration is inserted here. All other rules read from category relations to find terms to operate on.

**Data structure:** Default (hash set). No special indexing needed since category relations are always scanned in full.

---

## 2. Equality Relations

Binary equivalence relations tracking which terms are semantically equal:

```text
#[ds(crate::eqrel)]
relation eq_proc(Proc, Proc);    // Proc equality
#[ds(crate::eqrel)]
relation eq_name(Name, Name);    // Name equality
```

The `eqrel` annotation is critical: Ascent automatically maintains the equivalence closure:
- **Reflexivity**: `eq_cat(t, t)` for all `t` in `cat`
- **Symmetry**: `eq_cat(a, b) → eq_cat(b, a)`
- **Transitivity**: `eq_cat(a, b) ∧ eq_cat(b, c) → eq_cat(a, c)`

Without `eqrel`, these three properties would require explicit rules and many more iterations to converge.

---

## 3. Rewrite Relations

Binary relations tracking directional rewriting:

```text
#[ds(crate::dual_indexed)]
relation rw_proc(Proc, Proc);    // Proc rewrites: rw(source, target)
```

**Data structure:** `dual_indexed` — hash index on both columns. This is A-RT03: body clauses binding either column get hash-based index access instead of full-relation scan.

Rewrites differ from equations in two ways:
1. **Directional**: `rw_cat(a, b)` does NOT imply `rw_cat(b, a)`
2. **Controlled propagation**: Rewrite congruences are NOT auto-generated; users explicitly declare where rewrites propagate

---

## 4. Fold Relations

For categories with `fold`-annotated constructors (big-step evaluation):

```text
#[ds(crate::dual_indexed)]
relation fold_proc(Proc, Proc);    // fold(source, normal_form)
```

Only generated when at least one constructor in the category has `eval_mode = Fold`. Fold rules implement native evaluation (e.g., arithmetic: `fold(Add(3, 4), 7)`).

---

## 5. Step-Term Relation

A singleton seed relation for the primary category:

```text
relation step_term(Proc);    // The term being reduced
```

`step_term` holds only the top-level term being stepped. It seeds the exploration: when the runtime inserts `step_term(t)`, the Ascent engine discovers all subterms of `t` via category exploration rules, then applies equations and rewrites.

The `step_term` relation prevents blow-up in transitive rules: instead of applying rewrites to all known terms, rules can restrict application to subterms of the stepped term.

---

## 6. Collection Projection Relations

For constructors with collection fields, automatic projection relations are generated:

```text
// For PPar(HashBag<Proc>):
#[ds(crate::dual_indexed)]
relation ppar_contains(Proc, Proc);    // ppar_contains(parent, element)
```

These relations are populated by category exploration rules that iterate over collection elements. They enable rules to reference individual collection elements without pattern-matching the entire collection.

**Naming convention:** `<constructor_lowercase>_contains`

Multi-binder constructors (those with `MultiAbstraction` parameters) are excluded from projection generation since their collection semantics differ.

---

## 7. Custom Logic Relations

Users can declare additional relations in `logic { ... }` blocks:

```text
// In language! definition:
logic {
    relations {
        reachable(Proc, Proc);
        safe(Proc);
    }
    rules {
        reachable(x, y) <-- ...;
    }
}
```

These are generated with default data structures and participate in the same Datalog fixed point as the built-in relations.

---

## 8. Refinement Type Membership Relations

For each refinement type definition (e.g., `PosInt = { x: Int | x > 0 }`):

```text
relation is_refined_posint(Int);    // Membership predicate
```

These unary relations track which base-type terms satisfy the refinement predicate. They are populated by rules generated from the refinement type's constraint expression.

---

## 9. Relation Dependency Graph

The generated relations form a dependency graph that drives evaluation order:

```text
    step_term(Proc)
         │
         ▼
    proc(Proc) ◄──────────── Category exploration rules
     │   │   │                decompose terms into subterms
     │   │   ▼
     │   │  name(Name) ◄──── Cross-category extraction
     │   │
     │   ▼
     │  eq_proc(Proc, Proc) ◄── Reflexivity, congruence, user equations
     │       │
     │       ▼
     │  rw_proc(Proc, Proc) ◄── User rewrites (read eq_proc for matching)
     │       │
     │       ▼
     │  fold_proc(Proc, Proc) ◄── Native evaluation (fold-mode constructors)
     │
     ▼
    ppar_contains(Proc, Proc) ◄── Collection element iteration
         │
         ▼
    custom_rel(...) ◄── User-defined logic rules
         │
         ▼
    is_refined_posint(Int) ◄── Refinement type membership
```

### Key Dependencies

- `eq_proc` reads `proc` (to find terms to equate)
- `rw_proc` reads `eq_proc` (to apply rewrites to equivalent terms)
- `fold_proc` reads `proc` (to find terms to evaluate)
- Collection projections read `proc` (to find collection terms)
- All rules may read any relation (including custom and refinement)

---

## 10. Relation Listing for Extraction

The function `list_all_relations_for_extraction()` (`relations.rs:23-125`) provides a unified list of all relations with their parameter types. This is used for:

1. **Custom relation extraction**: Bridging Ascent results to user code
2. **Demand analysis**: Determining which categories are actually referenced
3. **Diagnostics**: Reporting relation statistics

```rust
pub struct RelationForExtraction {
    pub name: proc_macro2::Ident,       // e.g., "eq_proc"
    pub param_types: Vec<String>,       // e.g., ["Proc", "Proc"]
}
```

---

## Important Design Decision: All Relations Are Always Declared

From `relations.rs:127-138`:

> ALL categories get their full relation set (cat, eq_cat, rw_cat, fold_cat) declared. Even if a category is not "demanded" by any user equation/rewrite/logic rule, auto-generated rules (congruence, equation-rewrite closure) may reference its eq/rw relations. The ART06 demand filtering applies to **rules**, not relations.

This means a category with no user equations still gets `eq_cat` declared (the `eqrel` annotation ensures reflexivity). The demand filter controls which *rules* are generated, not which relations exist.

---

## Key Source Files

| File | Lines | Role |
|------|-------|------|
| `macros/src/logic/relations.rs` | 1-282 | All relation declarations |
| `macros/src/logic/common.rs` | — | `relation_names()`, demand computation |

---

**Next:** [Rule Generation](rule-generation.md) — how rules are generated from `language!` definitions.
