# Normal Form Computation

## Overview

The normalization module generates per-category `normalize()` methods that
reduce MeTTaIL terms to a canonical form. Normalization performs three
transformations in a single recursive pass:

1. **Collection flattening** -- nested collections of the same type are merged
   (e.g., `PPar({PPar({a, b}), c})` becomes `PPar({a, b, c})`)
2. **Beta-reduction** -- `Apply(Lam(^x.body), arg)` is reduced to `body[arg/x]`
3. **Cancellation pair collapse** -- inverse constructor compositions are
   eliminated (e.g., `PDrop(NQuote(P))` becomes `P`)

For native-type categories (e.g., `Int`), normalization also performs constant
folding via `try_fold_to_literal()`.

These methods are used by the BCG05 normalize-on-insert deduplication
optimization to ensure that structurally equivalent terms are recognized as
identical before being inserted into Ascent relations.

**Source:** `macros/src/gen/term_ops/normalize.rs`

## Algorithm Description

### Collection Flattening

For each grammar rule with a collection field (e.g., `PPar(HashBag<Proc>)`),
the generator emits a flattening insert helper:

```rust
impl Proc {
    fn insert_into_ppar(bag: &mut HashBag<Proc>, elem: Proc) {
        match elem {
            Proc::PPar(inner) => {
                // Flatten: recursively merge inner bag contents
                for (e, count) in inner.iter() {
                    for _ in 0..count {
                        Self::insert_into_ppar(bag, e.clone());
                    }
                }
            }
            _ => { bag.insert(elem); }
        }
    }
}
```

The `normalize()` match arm for `PPar` rebuilds the collection by normalizing
each element, then feeding it through the flattening helper:

```rust
Proc::PPar(bag) => {
    let mut new_bag = HashBag::new();
    for (elem, count) in bag.iter() {
        for _ in 0..count {
            let normalized_elem = elem.normalize();
            Self::insert_into_ppar(&mut new_bag, normalized_elem);
        }
    }
    Proc::PPar(new_bag)
}
```

### Beta-Reduction

For each domain type `D` in the language, the generator emits two reduction
arms per category:

**Single-argument:**
```rust
Cat::ApplyD(lam_box, arg_box) => {
    let lam_normalized = lam_box.as_ref().normalize();
    match &lam_normalized {
        Cat::LamD(scope) => {
            let (binder, body) = scope.clone().unbind();
            let arg_normalized = arg_box.as_ref().normalize();
            (*body).substitute_d(&binder.0, &arg_normalized).normalize()
        }
        _ => Cat::ApplyD(
            Box::new(lam_normalized),
            Box::new(arg_box.as_ref().normalize()),
        )
    }
}
```

**Multi-argument:**
```rust
Cat::MApplyD(lam_box, args) => {
    let lam_normalized = lam_box.as_ref().normalize();
    match &lam_normalized {
        Cat::MLamD(scope) => {
            let (binders, body) = scope.clone().unbind();
            let vars: Vec<_> = binders.iter().map(|b| &b.0).collect();
            let args_normalized: Vec<_> = args.iter()
                .map(|a| a.normalize()).collect();
            (*body).multi_substitute_d(&vars, &args_normalized).normalize()
        }
        _ => Cat::MApplyD(
            Box::new(lam_normalized),
            args.iter().map(|a| a.normalize()).collect(),
        )
    }
}
```

The normalization strategy is call-by-value: both the function and argument
positions are normalized before substitution, and the result is normalized
again to handle any new redexes exposed by substitution.

### Cancellation Pair Collapse

Cancellation pairs are detected at compile time by
`crate::ast::pattern::detect_cancellation_pairs()`. Each pair specifies an
outer constructor and an inner constructor whose composition is the identity.

For example, `PDrop(NQuote(P)) = P`:

```rust
Proc::PDrop(f0) => {
    let inner_normalized = f0.as_ref().normalize();
    match inner_normalized {
        Name::NQuote(p) => p.as_ref().normalize(),
        other => Proc::PDrop(Box::new(other)),
    }
}
```

The arm normalizes the inner field first, then pattern-matches to check if the
inner constructor is present. If matched, it extracts the innermost value and
re-normalizes as a safety net.

### Native-Type Categories

For categories with a `native_type` (e.g., `Int ~ i32`), normalization
recurses into subterms and then attempts constant folding:

```rust
impl Int {
    pub fn normalize(&self) -> Self {
        let reconstructed = match self {
            Int::IAdd(ref f0, ref f1) => {
                Int::IAdd(
                    Box::new(f0.as_ref().normalize()),
                    Box::new(f1.as_ref().normalize()),
                )
            }
            Int::NumLit(_) => self.clone(),
            Int::IVar(_) => self.clone(),
            _ => self.clone(),
        };
        reconstructed.try_fold_to_literal().unwrap_or(reconstructed)
    }
}
```

## Generated Code Patterns

The generator categorizes rules and produces a `normalize()` method with
prioritized match arms:

```rust
impl Cat {
    pub fn normalize(&self) -> Self {
        match self {
            // 1. Beta-reduction arms (highest priority)
            Cat::ApplyD(lam_box, arg_box) => { ... },
            Cat::MApplyD(lam_box, args) => { ... },

            // 2. Cancellation pair arms
            Cat::PDrop(f0) => { ... },

            // 3. Regular constructor arms (collection flattening, recursion)
            Cat::PPar(bag) => { ... },
            Cat::PSend(f0, f1) => { ... },

            // 4. Fallback
            _ => self.clone(),
        }
    }
}
```

### Binder Normalization

For binder constructors (both old-syntax and multi-binder), the scope body is
normalized using `Scope::from_parts_unsafe()` to reconstruct the scope without
re-closing:

```rust
Cat::PInput(f0, scope) => {
    Cat::PInput(
        f0.clone(),
        Scope::from_parts_unsafe(
            scope.inner().unsafe_pattern.clone(),
            Box::new(scope.inner().unsafe_body.as_ref().normalize()),
        ),
    )
}
```

## Integration with Codegen Pipeline

```
generate_all()
    +-- detect_cancellation_pairs(language) --> cancellation_pairs
    +-- generate_flatten_helpers(language)
    +-- generate_normalize_functions(language, &cancellation_pairs)
```

### BCG05 Normalize-on-Insert Deduplication

The BCG05 optimization inserts a `normalize()` call before every Ascent
relation insert. Combined with the epoch-scoped dedup `HashSet` (cleared via
`bump_bcg05_epoch()` in `runtime/src/binding.rs`), this ensures that
structurally equivalent terms are only inserted once per fixpoint iteration.

## Key Functions

| Function | Purpose |
|----------|---------|
| `generate_normalize_functions()` | Entry point: produces `normalize()` methods for all categories |
| `generate_flatten_helpers()` | Produces per-collection `insert_into_<label>()` flattening helpers |
| `generate_beta_reduction_arms()` | Produces `Apply/MApply` match arms with substitution |
| `generate_cancellation_pair_arm()` | Produces match arms for inverse constructor collapse |

## Source References

- Normalization generator: `macros/src/gen/term_ops/normalize.rs`
- Cancellation pair detection: `macros/src/ast/pattern.rs` (`detect_cancellation_pairs`)
- Pipeline call site: `macros/src/gen/mod.rs` (lines 69--74)
- BCG05 epoch mechanism: `runtime/src/binding.rs` (`bump_bcg05_epoch()`)
