# Substitution Generation

## Overview

The substitution module generates capture-avoiding substitution methods for
every exported category in a MeTTaIL language definition. It is the largest
module in `term_ops/` (1500+ lines) and provides the foundational mechanism
by which Ascent rewrite rules transform terms: replacing free variables with
replacement terms while respecting binding structure.

**Source:** `macros/src/gen/term_ops/subst.rs`

## Generated Methods

For each category `Cat` in a language with categories `{Cat, Other, ...}`,
the generator produces:

| Method | Signature | Purpose |
|--------|-----------|---------|
| `substitute()` | `(&self, var, replacement) -> Self` | Single-variable substitution (same category) |
| `subst()` | `(&self, vars, repls) -> Self` | Multi-variable simultaneous substitution |
| `multi_substitute()` | `(&self, vars, repls) -> Self` | Alias for `subst()` |
| `substitute_<cat>()` | `(&self, var, replacement) -> Self` | Typed alias for cross-category calls |
| `multi_substitute_<cat>()` | `(&self, vars, repls) -> Self` | Typed alias for cross-category calls |
| `subst_<other>()` | `(&self, vars, repls) -> Self` | Cross-category substitution (`Cat[Other/vars]`) |
| `substitute_env()` | `(&self, env) -> Self` | Name-based substitution from environment |
| `unify_freevars()` | `(&self) -> Self` | Canonicalize `FreeVar` identities via `VAR_CACHE` |

## Algorithm Description

### Core: Capture-Avoiding Substitution

Substitution is defined structurally on the `VariantKind` classification.
Each variant maps to a specific substitution strategy:

```
subst(Var(x), [x := t])         = t                     -- match
subst(Var(y), [x := t])         = Var(y)                -- no match
subst(Lit(n), _)                = Lit(n)                 -- leaf
subst(Nullary, _)               = Nullary                -- leaf
subst(Ctor(f1,...,fn), sigma)   = Ctor(f1[sigma],...,fn[sigma])  -- recurse
subst(Coll(elems), sigma)       = Coll(map(subst, elems))       -- map
subst(Bind(^x.body), [x := t]) = Bind(^x.body)          -- shadowed
subst(Bind(^x.body), [y := t]) = Bind(^x.body[y := t])  -- recurse
```

### Binder Shadowing (Single Binder)

For `Binder` variants (e.g., `PInput(name, ^x.body)`), the substitution
filters out any variable that is shadowed by the binder before recursing
into the body:

```rust
Cat::PInput(f0, scope) => {
    let binder = &scope.inner().unsafe_pattern;
    let body = &scope.inner().unsafe_body;

    // Filter out shadowed variables
    let (fvars, frepls): (Vec<_>, Vec<_>) = vars.iter()
        .zip(repls.iter())
        .filter(|(v, _)| binder.0 != ***v)    // <-- shadow check
        .map(|(v, r)| (*v, r.clone()))
        .unzip();

    if fvars.is_empty() {
        self.clone()
    } else {
        let new_body = (**body).subst(&fvars[..], &frepls);
        let new_scope = Scope::new(binder.clone(), Box::new(new_body));
        Cat::PInput(
            Box::new((**f0).subst(vars, repls)),
            new_scope,
        )
    }
}
```

The shadow check compares `FreeVar` identity (not names), ensuring that
alpha-equivalent terms substitute correctly.

### Multi-Binder Shadowing

For `MultiBinder` variants (e.g., `PInputs(names, ^[x1,...,xn].body)`), all
binder variables are checked:

```rust
let (fvars, frepls): (Vec<_>, Vec<_>) = vars.iter()
    .zip(repls.iter())
    .filter(|(v, _)| !binders.iter().any(|b| &b.0 == **v))  // filter ALL
    .map(|(v, r)| (*v, r.clone()))
    .unzip();
```

### Cross-Category Substitution

When category `Cat` contains fields of category `Other`, the generated
`subst_other()` method recurses into those fields using `Other`'s own
substitution method:

```rust
impl Cat {
    pub fn subst_other(
        &self,
        vars: &[&FreeVar<String>],
        repls: &[Other],
    ) -> Self {
        match self {
            Cat::PSend(f0, f1) => {
                // f0 is Name -- use Name::subst_other
                // f1 is Proc -- return unchanged (different replacement category)
                Cat::PSend(
                    Box::new(f0.subst_other(vars, repls)),
                    f1.clone(),
                )
            }
            // ...
        }
    }
}
```

The method name dispatch is handled by `subst_method_for_category()`:
- If the field's category matches the replacement category: use `subst()`
- Otherwise: use `subst_<repl_cat>()` on the field

### Environment Substitution

The `substitute_env()` method performs **name-based** substitution (not
`FreeVar` identity-based) from an environment map. It iterates until a fixed
point is reached (or 100 iterations, as a safety bound), then unifies
`FreeVar` identities and normalizes:

```rust
pub fn substitute_env(&self, env: &LangEnv) -> Self {
    let mut result = self.clone();
    for _ in 0..100 {
        let prev_str = format!("{}", result);
        // Apply name-based substitution for each category
        result = result.subst_by_name_proc(&env.proc.0);
        result = result.subst_by_name_name(&env.name.0);
        // ...
        if format!("{}", result) == prev_str { break; }
    }
    let result = result.unify_freevars();
    result.normalize()
}
```

### FreeVar Unification

The `unify_freevars()` method traverses the term and replaces each `FreeVar`
with the canonical instance from the thread-local `VAR_CACHE` (provided by
`runtime/src/binding.rs`). This ensures that variables with the same pretty
name share the same `unique_id`, which is necessary for Ascent equality
checks to work correctly when terms originate from different parsing contexts.

## Variant Classification (`VariantKind`)

All term-ops generators share this enum, defined in `subst.rs`:

```rust
enum VariantKind {
    Var { label },
    Literal { label },
    Nullary { label },
    Regular { label, fields: Vec<FieldInfo> },
    Collection { label, element_cat, coll_type },
    Binder { label, pre_scope_fields, binder_cat, body_cat },
    MultiBinder { label, pre_scope_fields, binder_cat, body_cat },
}

struct FieldInfo {
    category: Ident,
    is_collection: bool,
    coll_type: Option<CollectionType>,
}
```

The `collect_category_variants()` function builds this classification by
examining grammar rules, auto-generated variants (Var, Literal, Lambda, Apply),
and detecting binder/multi-binder structure from `bindings` and `term_context`.

## Integration with Codegen Pipeline

```
generate_all()
    +-- generate_substitution(language)      --> subst(), substitute(), cross-cat
    +-- generate_env_substitution(language)   --> substitute_env(), unify_freevars()
```

Substitution methods are called from:
- **Beta-reduction** in `normalize()`: `body.substitute_d(&binder.0, &arg)`
- **Ascent rewrite rules**: generated rule bodies invoke `subst()` to apply rewrites
- **Environment application**: `substitute_env()` applies REPL/test environments

## Key Functions

| Function | Purpose |
|----------|---------|
| `generate_substitution()` | Entry point: self-category and cross-category substitution |
| `generate_env_substitution()` | Name-based environment substitution + `unify_freevars()` |
| `generate_category_substitution()` | Per-category: collects variants, emits `impl Cat` |
| `collect_category_variants()` | Shared: builds `Vec<VariantKind>` from `LanguageDef` |
| `generate_binder_subst_arm()` | Single-binder: shadow-filtered substitution |
| `generate_multi_binder_subst_arm()` | Multi-binder: all-binder shadow filtering |
| `generate_var_subst_arm()` | Variable: match-and-replace logic |
| `generate_regular_subst_arm()` | Regular: recurse into each field |
| `generate_collection_subst_arm()` | Collection: map substitution with correct iterator |

## Source References

- Generator: `macros/src/gen/term_ops/subst.rs` (~1550 lines)
- Pipeline call site: `macros/src/gen/mod.rs` (lines 75--76)
- Variable cache: `runtime/src/binding.rs` (`get_or_create_var`, `get_or_insert_var`)
- Scope wrapper: `runtime/src/binding.rs` (`Scope`, `OrdVar`)
