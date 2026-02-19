# Consolidation Areas

Six areas of Ascent rule generation were consolidated. Each replaces N per-constructor rules with a single rule containing an inline `match` expression.

---

## Area 1: Subterm Extraction

**File**: `macros/src/logic/helpers.rs` (`generate_consolidated_deconstruction_rules`)

**What it consolidates**: Rules that extract subterms from constructors and add them to their category relations. For example, extracting all `Int` subterms from an `Int` term, or all `Name` subterms from a `Proc` term.

**Grouping key**: `(source_category, target_category)` pair

### Before (3 separate rules)

```text
int(f0.as_ref().clone()), int(f1.as_ref().clone()) <--
    int(t), if let Int::Add(f0, f1) = t;

int(f0.as_ref().clone()) <--
    int(t), if let Int::Neg(f0) = t;

int(f0.as_ref().clone()), int(f1.as_ref().clone()), int(f2.as_ref().clone()) <--
    int(t), if let Int::Tern(f0, f1, f2) = t;
```

### After (1 consolidated rule)

```text
int(sub.clone()) <--
    int(t),
    for sub in (match t {
        Int::Add(f0, f1) => vec![f0.as_ref().clone(), f1.as_ref().clone()],
        Int::Neg(f0) => vec![f0.as_ref().clone()],
        Int::Tern(f0, f1, f2) => vec![f0.as_ref().clone(), f1.as_ref().clone(), f2.as_ref().clone()],
        _ => vec![],
    }).into_iter();
```

**Why it works**: Each arm returns all subterms matching the target category. The `for` clause iterates over them, producing exactly the same facts as the separate rules. Constructors with no matching subterms produce an empty vec and contribute nothing.

### Formal Proof Reference

- **Rocq theorem**: `area1_subterm_extraction` in `AreaProofs.v` (instance of `for_match_equiv` / R1)
- **Pedagogical proof**: [formal-proofs.md, Section 2](formal-proofs.md#2-core-theorem-for-match-equivalence-r1) and [Section 6.1](formal-proofs.md#area-1-subterm-extraction)
- **proptest property**: `prop_subterm_extraction_equiv` in `languages/tests/consolidation_tests.rs`

---

## Area 2: Auto-Variant Congruence

**File**: `macros/src/logic/helpers.rs` (`generate_consolidated_congruence_rules`)

**What it consolidates**: Rewrite congruence rules for auto-generated `Apply{Dom}` and `MApply{Dom}` variants. These propagate rewrites through the lambda/application variants that are automatically generated for each domain type.

**Grouping key**:
- **Lam congruence**: All domains merged into one rule per source category (the `lam` field is always `Box<SourceCat>` regardless of domain)
- **Arg congruence**: One rule per `(source_category, domain)` pair

### Before (6 rules per category for 3 domains)

```text
rw_int(t.clone(), Int::ApplyInt(Box::new(new_lam), arg.clone())) <--
    int(t), if let Int::ApplyInt(lam, arg) = t, rw_int(lam.clone(), new_lam);

rw_int(t.clone(), Int::MApplyInt(Box::new(new_lam), args.clone())) <--
    int(t), if let Int::MApplyInt(lam, args) = t, rw_int(lam.clone(), new_lam);

rw_int(t.clone(), Int::ApplyBool(Box::new(new_lam), arg.clone())) <--
    int(t), if let Int::ApplyBool(lam, arg) = t, rw_int(lam.clone(), new_lam);

// ... 3 more for MApplyBool, ApplyStr, MApplyStr
```

### After (1 lam rule + 3 arg rules)

```text
// Lam congruence: ONE rule across all domains
rw_int(t.clone(), match t {
    Int::ApplyInt(_, arg) => Int::ApplyInt(Box::new(new_lam.clone()), arg.clone()),
    Int::MApplyInt(_, args) => Int::MApplyInt(Box::new(new_lam.clone()), args.clone()),
    Int::ApplyBool(_, arg) => Int::ApplyBool(Box::new(new_lam.clone()), arg.clone()),
    Int::MApplyBool(_, args) => Int::MApplyBool(Box::new(new_lam.clone()), args.clone()),
    Int::ApplyStr(_, arg) => Int::ApplyStr(Box::new(new_lam.clone()), arg.clone()),
    Int::MApplyStr(_, args) => Int::MApplyStr(Box::new(new_lam.clone()), args.clone()),
    _ => unreachable!(),
}) <--
    int(t),
    for lam in (match t {
        Int::ApplyInt(lam, _) => vec![lam.as_ref().clone()],
        Int::MApplyInt(lam, _) => vec![lam.as_ref().clone()],
        Int::ApplyBool(lam, _) => vec![lam.as_ref().clone()],
        Int::MApplyBool(lam, _) => vec![lam.as_ref().clone()],
        Int::ApplyStr(lam, _) => vec![lam.as_ref().clone()],
        Int::MApplyStr(lam, _) => vec![lam.as_ref().clone()],
        _ => vec![],
    }).into_iter(),
    rw_int(lam, new_lam);
```

**Why it works**: The `lam` field is always `Box<SourceCat>` for all Apply/MApply variants, so the extraction match always yields values of the same type. The rebuild match in the head uses the original term `t` to determine which variant to reconstruct.

**Savings**: For C categories with C domains each: 2C rules per category become 1 + C rules (1 merged lam + C arg rules). Total: (2C-1)*C rules eliminated across all categories.

### Formal Proof Reference

- **Rocq theorem**: `area2_auto_variant_lam_congruence` in `AreaProofs.v` (instance of `for_match_equiv` / R1)
- **Pedagogical proof**: [formal-proofs.md, Section 2](formal-proofs.md#2-core-theorem-for-match-equivalence-r1) and [Section 6.2](formal-proofs.md#area-2-auto-variant-congruence)

---

## Area 3: Equation Congruence

**File**: `macros/src/logic/equations.rs` (`generate_congruence_rules`)

**What it consolidates**: Demand-driven equality congruence rules. If two terms have equal arguments, the terms themselves are equal. E.g., `eq(Add(a,b), Add(c,d))` if `eq(a,c)` and `eq(b,d)`.

**Grouping key**: `(category, ordered_field_types_tuple)` — constructors with the same result category and same types for each field position are grouped together.

### Before (4 separate rules for Int binary constructors)

```text
eq_int(s, t) <--
    int(s), int(t),
    if let Int::Add(s0, s1) = s, if let Int::Add(t0, t1) = t,
    eq_int(s0.clone(), t0.clone()), eq_int(s1.clone(), t1.clone());

eq_int(s, t) <--
    int(s), int(t),
    if let Int::Sub(s0, s1) = s, if let Int::Sub(t0, t1) = t,
    eq_int(s0.clone(), t0.clone()), eq_int(s1.clone(), t1.clone());

// ... Pow, CustomOp (same pattern)
```

### After (1 consolidated rule)

```text
eq_int(s.clone(), t.clone()) <--
    int(s),
    int(t),
    for (s_f0, s_f1, t_f0, t_f1) in (match (s, t) {
        (Int::Pow(sf0, sf1), Int::Pow(tf0, tf1)) => vec![(sf0.as_ref().clone(), sf1.as_ref().clone(), tf0.as_ref().clone(), tf1.as_ref().clone())],
        (Int::Add(sf0, sf1), Int::Add(tf0, tf1)) => vec![(sf0.as_ref().clone(), sf1.as_ref().clone(), tf0.as_ref().clone(), tf1.as_ref().clone())],
        (Int::Sub(sf0, sf1), Int::Sub(tf0, tf1)) => vec![(sf0.as_ref().clone(), sf1.as_ref().clone(), tf0.as_ref().clone(), tf1.as_ref().clone())],
        (Int::CustomOp(sf0, sf1), Int::CustomOp(tf0, tf1)) => vec![(sf0.as_ref().clone(), sf1.as_ref().clone(), tf0.as_ref().clone(), tf1.as_ref().clone())],
        _ => vec![],
    }).into_iter(),
    eq_int(s_f0, t_f0),
    eq_int(s_f1, t_f1);
```

**Why it works**: The match over `(s, t)` simultaneously destructures both terms. Only matching pairs of the same constructor produce extractions. The subsequent `eq_*` checks verify field-wise equality. This is exactly the semantics of the separate per-constructor rules.

**Important**: Only constructors with identical field-type tuples can share a rule, because the equality relation names (`eq_int`, `eq_bool`, etc.) must match each field position.

### Formal Proof Reference

- **Rocq theorem**: `area3_equation_congruence` in `AreaProofs.v` (instance of `pair_match_equiv` / R3)
- **Pedagogical proof**: [formal-proofs.md, Section 4](formal-proofs.md#4-pair-match-equivalence-r3) and [Section 6.3](formal-proofs.md#area-3-equation-congruence)
- **proptest property**: `prop_pair_match_equiv` in `languages/tests/consolidation_tests.rs`

---

## Area 4: Explicit Rewrite Congruence

**File**: `macros/src/logic/congruence.rs` (`generate_consolidated_simple_congruence`)

**What it consolidates**: User-declared explicit congruence rules for "simple" constructors (non-binder, non-collection). These control where rewrites propagate through term constructors.

**Grouping key**: `(source_category, field_category)` — all constructors in the same category whose rewritten field has the same type are grouped.

### Before (5 rules for Int constructors with Int fields)

```text
rw_int(lhs, Int::Add(Box::new(t), x1.clone())) <--
    int(lhs), if let Int::Add(x0, x1) = lhs, rw_int((*x0).clone(), t);
rw_int(lhs, Int::Add(x0.clone(), Box::new(t))) <--
    int(lhs), if let Int::Add(x0, x1) = lhs, rw_int((*x1).clone(), t);
rw_int(lhs, Int::Neg(Box::new(t))) <--
    int(lhs), if let Int::Neg(x0) = lhs, rw_int((*x0).clone(), t);
// ... Sub field 0, Sub field 1
```

### After (1 consolidated rule with variant indices)

```text
rw_int(lhs.clone(), match (lhs, vi) {
    (Int::Add(_, x1), 0usize) => Int::Add(Box::new(t.clone()), x1.clone()),
    (Int::Add(x0, _), 1usize) => Int::Add(x0.clone(), Box::new(t.clone())),
    (Int::Neg(_), 2usize) => Int::Neg(Box::new(t.clone())),
    (Int::Sub(_, x1), 3usize) => Int::Sub(Box::new(t.clone()), x1.clone()),
    (Int::Sub(x0, _), 4usize) => Int::Sub(x0.clone(), Box::new(t.clone())),
    _ => unreachable!(),
}) <--
    int(lhs),
    for (field_val, vi) in (match lhs {
        Int::Add(x0, x1) => vec![((**x0).clone(), 0usize), ((**x1).clone(), 1usize)],
        Int::Neg(x0) => vec![((**x0).clone(), 2usize)],
        Int::Sub(x0, x1) => vec![((**x0).clone(), 3usize), ((**x1).clone(), 4usize)],
        _ => vec![],
    }).into_iter(),
    rw_int(field_val, t);
```

**Why it works**: The extraction match produces `(field_value, variant_index)` pairs. The variant index uniquely identifies which constructor and which field position was extracted. The rebuild match in the head uses `(lhs, vi)` to reconstruct the correct constructor with the rewritten field, preserving all other fields.

**Design detail**: The extraction match groups entries by constructor (one arm per constructor, possibly yielding multiple `(value, index)` pairs for multi-field constructors), while the rebuild match has one arm per entry (each field position of each constructor gets its own rebuild pattern).

### Formal Proof Reference

- **Rocq theorem**: `area4_explicit_congruence_extraction` and `area4_explicit_congruence` in `AreaProofs.v` (instance of `variant_index_extract_equiv` / V4)
- **Pedagogical proof**: [formal-proofs.md, Section 5](formal-proofs.md#5-variant-index-rebuild-v4) and [Section 6.4](formal-proofs.md#area-4-explicit-rewrite-congruence)
- **proptest properties**: `prop_rebuild_roundtrip`, `prop_extraction_completeness`, `test_variant_index_injectivity` in `languages/tests/consolidation_tests.rs`

---

## Area 5: Fold Triggers

**File**: `macros/src/logic/mod.rs` (`generate_fold_big_step_rules`)

**What it consolidates**: The trigger rule that connects fold evaluation to the rewrite system. For each fold-mode constructor, there was a separate rule: `rw_cat(s, t) <-- cat(s), if let Cat::FoldCtor(...) = s, fold_cat(s, t)`.

**Grouping key**: Category — one consolidated trigger per category with fold-mode constructors.

### Before (N rules, one per fold-mode constructor)

```text
rw_int(s, t) <-- int(s), if let Int::Neg(_) = s, fold_int(s, t);
rw_int(s, t) <-- int(s), if let Int::Sub(_, _) = s, fold_int(s, t);
rw_int(s, t) <-- int(s), if let Int::CustomOp(_, _) = s, fold_int(s, t);
```

### After (1 consolidated rule)

```text
rw_int(s.clone(), t.clone()) <--
    int(s),
    if (match s {
        Int::Neg(_) => true,
        Int::Sub(_, _) => true,
        Int::CustomOp(_, _) => true,
        _ => false,
    }),
    fold_int(s, t);
```

**Why it works**: The `if (match s { ... })` acts as a boolean predicate. It evaluates to `true` for exactly the same constructors as the separate `if let` rules would match, so `fold_int(s, t)` is queried for the same set of terms.

### Formal Proof Reference

- **Rocq theorem**: `area5_fold_triggers` in `AreaProofs.v` (instance of `if_match_equiv` / R2)
- **Pedagogical proof**: [formal-proofs.md, Section 3](formal-proofs.md#3-if-match-equivalence-r2) and [Section 6.5](formal-proofs.md#area-5-fold-triggers)
- **proptest property**: `prop_fold_trigger_equiv` in `languages/tests/consolidation_tests.rs`

---

## Area 6: Fold Identities

**File**: `macros/src/logic/mod.rs` (`generate_fold_big_step_rules`)

**What it consolidates**: Identity fold rules for non-native categories. For non-native fold categories (e.g., Proc with CastInt/Add), each non-fold constructor is its own fold identity: `fold_proc(t, t) <-- proc(t), if let Proc::PZero = t`.

**Grouping key**: Category — one consolidated identity rule per non-native fold category.

### Before (N rules, one per non-fold constructor)

```text
fold_proc(t, t) <-- proc(t), if let Proc::PZero = t;
fold_proc(t, t) <-- proc(t), if let Proc::PDrop(_) = t;
fold_proc(t, t) <-- proc(t), if let Proc::PPar(_) = t;
fold_proc(t, t) <-- proc(t), if let Proc::POutput(_, _) = t;
// ... etc.
```

### After (1 consolidated rule)

```text
fold_proc(t.clone(), t.clone()) <--
    proc(t),
    if (match t {
        Proc::PZero => true,
        Proc::PDrop(_) => true,
        Proc::PPar(_) => true,
        Proc::POutput(_, _) => true,
        Proc::PInputs(_, _) => true,
        Proc::CastInt(_) => true,
        Proc::Err => true,
        _ => false,
    });
```

**Why it works**: Same boolean predicate technique as Area 5. The identity `fold_proc(t, t)` fires for exactly the non-fold constructors.

### Formal Proof Reference

- **Rocq theorem**: `area6_fold_identities` in `AreaProofs.v` (instance of `if_match_equiv` / R2)
- **Pedagogical proof**: [formal-proofs.md, Section 3](formal-proofs.md#3-if-match-equivalence-r2) and [Section 6.6](formal-proofs.md#area-6-fold-identities)
