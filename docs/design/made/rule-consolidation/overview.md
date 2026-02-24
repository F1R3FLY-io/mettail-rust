# Ascent Rule Consolidation

## Pipeline Context

Rule consolidation operates within the Ascent code generation pipeline, transforming the generated rules before they are emitted:

```
language! { ... }
    │
    └── Ascent Code Gen ────> Ascent Rules (O(C² × N) rules)
          │                        │
          │   Rule Consolidation   │
          │   (Opt 1)              │
          v                        v
          N per-constructor   →   1 consolidated
          if-let rules            match rule (O(C²) rules)
```

The formal proofs demonstrate that this transformation preserves semantics — the consolidated Datalog program computes exactly the same fixpoint as the original. For complete proofs, see [formal-proofs.md](formal-proofs.md). For Rocq build instructions and theorem catalog, see [rocq-artifacts.md](rocq-artifacts.md).

## Problem

Each Ascent Datalog rule expands to ~120 lines of Rust code during proc-macro compilation. When we added a 4th category type (Str) to the calculator language, compilation time increased 18.3x (from 1:32 to 28:00) because the number of auto-generated rules grew quadratically with the number of categories.

The root cause: many rules follow identical structural patterns, differing only in the constructor name. For example, subterm extraction generated one Ascent rule per constructor per (source, target) category pair:

```text
int(f0.as_ref().clone()) <-- int(t), if let Int::Add(f0, f1) = t;
int(f0.as_ref().clone()), int(f1.as_ref().clone()) <-- int(t), if let Int::Pow(f0, f1) = t;
int(f0.as_ref().clone()) <-- int(t), if let Int::Neg(f0) = t;
// ... one rule per constructor
```

With C categories and N constructors, this produces O(C^2 * N) rules, each of which Ascent compiles independently.

## Key Insight

Normal Rust `match` expressions compile orders of magnitude faster per line than Ascent rules. Replacing N per-constructor rules with 1 rule containing an inline `match` preserves semantics while dramatically reducing the number of generated Ascent rules.

The semantic equivalence argument is straightforward: a Datalog rule fires independently for each binding of its variables. An inline match over all constructors in a single `for` clause produces exactly the same set of bindings as N separate `if let` rules would — the union of all constructor matches.

## The Technique

### Before: N rules, one per constructor

```text
tgt(f0.as_ref().clone()) <--
    src(t),
    if let Src::A(f0) = t;

tgt(f0.as_ref().clone()), tgt(f1.as_ref().clone()) <--
    src(t),
    if let Src::B(f0, f1) = t;
```

### After: 1 rule with inline match

```text
tgt(sub.clone()) <--
    src(t),
    for sub in (match t {
        Src::A(f0) => vec![f0.as_ref().clone()],
        Src::B(f0, f1) => vec![f0.as_ref().clone(), f1.as_ref().clone()],
        _ => vec![],
    }).into_iter();
```

The key mechanism is `for <var> in <expr>` in Ascent, which iterates over the elements of an expression for each matching tuple. By using a match expression that returns a `Vec` of extracted values, we merge N rules into 1.

For congruence rules (which need to rebuild the term), we use variant indices to track which constructor was matched:

```text
rw_cat(lhs.clone(), match (lhs, vi) {
    (Cat::A(_, x1), 0usize) => Cat::A(Box::new(t.clone()), x1.clone()),
    (Cat::B(x0, _), 1usize) => Cat::B(x0.clone(), Box::new(t.clone())),
    _ => unreachable!(),
}) <--
    cat(lhs),
    for (field_val, vi) in (match lhs {
        Cat::A(x0, _) => vec![((**x0).clone(), 0usize)],
        Cat::B(_, x1) => vec![((**x1).clone(), 1usize)],
        _ => vec![],
    }).into_iter(),
    rw_cat(field_val, t);
```

## Results

| Language   | Before  | After   | Reduction |
|------------|---------|---------|-----------|
| Calculator | 138     | 61      | 56%       |
| Rho Calc   | 116     | 52      | 55%       |
| Ambient    | 84      | 35      | 58%       |
| Lambda     | 9       | 9       | 0%        |
| **Total**  | **347** | **157** | **55%**   |

Lambda has only 1 category (Term) so there was nothing to consolidate.

## Source Files

### New files

| File                          | Purpose                                                                                               |
|-------------------------------|-------------------------------------------------------------------------------------------------------|
| `macros/src/logic/common.rs`  | Shared helpers: `RelationNames`, `literal_label_for()`, `builtin_op_token/expr()`, `fold_*` utilities |
| `macros/src/logic/helpers.rs` | Area 1 (subterm extraction) and Area 2 (auto-variant congruence) consolidation                        |
|                               |                                                                                                       |

### Modified files

| File                             | Changes                                                                                |
|----------------------------------|----------------------------------------------------------------------------------------|
| `macros/src/logic/mod.rs`        | Areas 5-6 (fold triggers/identities), semantic rule unification, pretty-printing fixes |
| `macros/src/logic/categories.rs` | Delegates to consolidated helpers instead of per-constructor generation                |
| `macros/src/logic/equations.rs`  | Area 3: groups constructors by field-type signature for consolidated congruence        |
| `macros/src/logic/congruence.rs` | Area 4: groups simple congruences by (source_cat, field_cat) pair                      |
| `macros/src/logic/relations.rs`  | Cleaned up to use `RelationNames` from common                                          |
| `macros/src/logic/rules.rs`      | Unified clause assembly for equations and rewrites                                     |

### See Also

- [README.md](README.md) — Executive summary, proof architecture, results
- [`consolidation-areas.md`](consolidation-areas.md) — Detailed before/after for each of the 6 consolidation areas
- [`formal-proofs.md`](formal-proofs.md) — Complete formal proofs: definitions, theorems, area applications
- [`rocq-artifacts.md`](rocq-artifacts.md) — Build instructions, theorem catalog, hypothesis audit
- [`codegen-dry.md`](codegen-dry.md) — DRY improvements to the codegen source code
- [Ascent Runtime Optimizations](../ascent-optimizations/) — Opts 2-5: TLS pooling, dead rule pruning, ordering, SCC splitting
- [Rocq Source](../../../../formal/rocq/rule_consolidation/theories/) — The `.v` proof files
