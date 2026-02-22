# Opt 3: Dead Rule Pruning (Reachability-Based)

## 1. Motivation

The Ascent code generator produces cross-category subterm extraction rules for every `(src, tgt)` category pair. For example, in RhoCalc with 6 categories, a naive generator emits rules for all 36 pairs (6 x 6). Many of these rules can never fire because no constructor path connects the source to the target.

Consider the pair `(Proc, Float)`: no `Proc` constructor has a field of type `Float`, and no intermediate category bridges them. The rule `float(sub) <-- proc(t), ...` will fire on every `Proc` term but always extract nothing — pure waste.

Pruning these dead rules:
- Reduces Ascent compilation time (fewer rules for the Ascent macro to process)
- Reduces fixpoint iteration cost (fewer rules to evaluate per step)
- Improves code size (fewer match arms in generated code)

## 2. The Optimization

### 2.1 Category Graph Construction

Build a directed graph from user-defined constructor field types:

- **Nodes:** Grammar categories (e.g., `Proc`, `Name`, `Expr`, `Chan`, `Ground`, `Float`)
- **Edges:** If category `A` has a constructor with a field of type `B`, add edge `A → B`

**Implementation:** `common.rs:215-298` (`compute_category_reachability`)

The function:
1. Scans all grammar rules for field type references (lines 224-265)
2. Adds self-loops for every category (lines 271-272)
3. Adds direct edges from field references (lines 273-278)
4. Computes the transitive closure via iterative saturation (lines 281-295)

**Important:** Auto-generated variants (`Apply`, `MApply`, `Lam`, `MLam`) are excluded from the base graph. They create edges between all category pairs, which is exactly what we want to prune. Only user-defined constructor paths determine reachability.

### 2.2 Dead Rule Skip

During rule generation, each `(src, tgt)` pair is checked against the reachable set:

```rust
// categories.rs:34-48
let reachable = compute_category_reachability(language);

let effective_reachable = if let Some(filter) = cat_filter {
    core_reachable = reachable
        .iter()
        .filter(|(s, t)| filter.contains(s) && filter.contains(t))
        .cloned()
        .collect();
    &core_reachable
} else {
    &reachable
};
```

The `effective_reachable` set is passed to `generate_consolidated_deconstruction_rules`, which only generates match arms for pairs in the set. Unreachable pairs are silently skipped.

## 3. Graph Model

**Definition (Node, Edge).** A directed graph `G = (Node, edge)` where `Node` is a finite type with decidable equality, and `edge : Node → Node → Prop` is the adjacency relation.

**Definition (Reachability).** Reachability is the reflexive-transitive closure of `edge`:

```
Inductive reach : Node → Node → Prop :=
  | reach_refl : ∀ n, reach n n
  | reach_step : ∀ a b c, edge a b → reach b c → reach a c
```

**Lemma (reach_edge).** Direct edges are reachable:

> `∀ a b, edge a b → reach a b`

**Proof.** `reach_step a b b (edge a b) (reach_refl b)`. **QED.**

**Lemma (reach_trans).** Reachability is transitive:

> `∀ a b c, reach a b → reach b c → reach a c`

**Proof.** Induction on the derivation of `reach a b`:
- **Base (`reach_refl`):** `a = b`, so `reach a c = reach b c`. **QED.**
- **Step (`reach_step a x b`):** We have `edge a x`, `reach x b`, and by IH `reach x c`. Apply `reach_step a x c`. **QED.**

## 4. Extraction Model

**Definition (extract).** `extract(src, tgt, t)` returns all `tgt`-typed subterms from the `src`-typed term `t`. This models the generated match arms per `(src, tgt)` pair.

**Hypothesis (P1: extract_empty_when_unreachable).**

> `∀ src tgt t, ¬reach(src, tgt) → extract(src, tgt, t) = []`

**Justification:** The code generator (`categories.rs:50-53`) only emits match arms for constructors that exist. If no constructor path from `src` to `tgt` exists, no match arm produces a `tgt`-typed value. The generated match falls through to the default arm, which returns `[]`.

This is an axiom in the Rocq proof because it reflects a property of the code generator rather than a mathematical truth. The generator's behavior guarantees this invariant.

**Definition (rule_derive).** One rule's derivation:

```
rule_derive(src, tgt, db) := flat_map (extract src tgt) (get_rel db src)
```

Apply the `(src, tgt)` extraction to all `src`-typed terms in the database.

**Definition (full_derive).** The immediate consequence operator for a target category:

```
full_derive(tgt, db) := flat_map (λ src. rule_derive(src, tgt, db)) all_cats
```

Aggregate derivations from all source categories.

**Definition (pruned_derive).** The pruned immediate consequence operator:

```
pruned_derive(tgt, db) := flat_map (λ src. rule_derive(src, tgt, db))
                                    (filter (λ src. reach(src, tgt)) all_cats)
```

Only considers reachable source categories.

## 5. Theorems and Proofs

### 5.1 P2: Dead Rules Derive Nothing

**Theorem (P2: dead_rule_derives_nothing).**

> `∀ src tgt db, ¬reach(src, tgt) → rule_derive(src, tgt, db) = []`

**Proof.** Unfold `rule_derive`. Apply `flat_map_all_nil`. For each term `t ∈ get_rel(db, src)`, by hypothesis P1, `extract(src, tgt, t) = []` since `¬reach(src, tgt)`. **QED.**

### 5.2 P3: Pruned Equals Full

**Theorem (P3: pruned_equals_full).**

> `∀ tgt db, full_derive(tgt, db) = pruned_derive(tgt, db)`

**Proof.** Unfold `full_derive` and `pruned_derive`. Apply `flat_map_filter_nil`. For each source category `src` that was filtered out (`¬reach(src, tgt)`), we show `rule_derive(src, tgt, db) = []` by P2. Since removed elements contribute `[]`, the flat_map result is unchanged. **QED.**

### 5.3 Fixpoint Unchanged

**Corollary (fixpoint_unchanged).**

> `∀ tgt db, full_derive(tgt, db) = pruned_derive(tgt, db)`

**Proof.** Immediate from P3. Since the immediate consequence operator is identical with or without dead rules, and fixpoints are determined by the operator, the least fixpoints are identical. **QED.**

## 6. Example: RhoCalc Dead Rules

### 6.1 Category Graph

```
          ┌───────┐
    ┌────>│ Proc  │<────┐
    │     └───┬───┘     │
    │         │         │
    │   ┌─────┴─────┐   │
    │   │ edge_P→N  │   │ edge_N→P
    │   v           │   │
    │ ┌───────┐     │   │
    │ │ Name  │─────┘   │
    │ └───┬───┘         │
    │     │ edge_N→N    │
    │     └─────────────┘
    │   edge_P→P
    │
    │     ┌───────┐
    │     │ Expr  │───────> {Proc, Name, Expr, Ground}
    │     └───────┘
    │
    │     ┌───────┐
    │     │ Chan  │───────> Name
    │     └───────┘
    │
    │     ┌─────────┐
    │     │ Ground  │  (no outgoing edges — literals)
    │     └─────────┘
    │
    │     ┌───────┐
    │     │ Float │  (no outgoing edges — literals)
    │     └───────┘
```

### 6.2 Dead Pairs from Proc

Since `Proc` can only reach `{Proc, Name}` (proven in `rho_Proc_reach_only_Proc_Name`), the following pairs are dead:

| Source | Target | Dead? | Reason |
|--------|--------|-------|--------|
| Proc | Expr | Dead | Proc cannot reach Expr |
| Proc | Chan | Dead | Proc cannot reach Chan |
| Proc | Ground | Dead | Proc cannot reach Ground |
| Proc | Float | Dead | Proc cannot reach Float |
| Name | Expr | Dead | Name only reaches {Proc, Name} |
| Name | Chan | Dead | Name only reaches {Proc, Name} |
| Name | Ground | Dead | Name only reaches {Proc, Name} |
| Name | Float | Dead | Name only reaches {Proc, Name} |

These 8 dead rules (out of 36 total pairs) are pruned, reducing rule count by 22%.

## 7. Hypothesis Justification

| Hypothesis | Statement | Justification |
|------------|-----------|---------------|
| P1: `extract_empty_when_unreachable` | `¬reach(src,tgt) → extract(src,tgt,t) = []` | Code generator only emits match arms for constructors that exist. If no constructor path `src → tgt` exists, the generated match has no arms producing `tgt` values — it falls through to the default `[] / {}` arm. See `categories.rs:50-53` and `helpers.rs`. |
| `reach_dec` | `∀ src tgt, {reach src tgt} + {¬reach src tgt}` | Reachability is decidable on finite graphs: `compute_category_reachability` computes the transitive closure as a `BTreeSet`. Membership is decidable. |
| `all_cats_complete` | `∀ c, In c all_cats` | All categories are enumerated from `language.types`, which is the complete list of declared types. |

## 8. Spec-to-Code Traceability

| Rocq Definition | Rust / Ascent Code | Location |
|-----------------|-------------------|----------|
| `Node` | category names (`String`) | `common.rs:216` |
| `edge` | direct adjacency list from constructor fields | `common.rs:219-265` |
| `reach` | transitive closure loop | `common.rs:267-297` |
| `extract` | generated match arms per `(src, tgt)` pair | `categories.rs:50-53` |
| dead rule skip | reachability check before rule gen | `categories.rs:34-48` |
| `rule_derive` | consolidated subterm extraction rule | `helpers.rs` |
| `full_derive` | Ascent fixpoint iteration step | `ascent!` macro output |
| `P2_dead_rule_derives_nothing` | — | `DeadRulePruning.v:109-120` |
| `P3_pruned_equals_full` | — | `DeadRulePruning.v:150-163` |
| `fixpoint_unchanged` | — | `DeadRulePruning.v:176-181` |

## 9. Rocq Source Reference

- **Files:** `formal/rocq/ascent_optimizations/theories/GraphReachability.v` (156 lines), `formal/rocq/ascent_optimizations/theories/DeadRulePruning.v` (183 lines)
- **Dependencies:** `GraphReachability.v` depends on `Prelude.v`; `DeadRulePruning.v` depends on `Prelude.v` and `GraphReachability.v`
- **Key constructs:**
  - `GraphReachability.v`: `reach` (inductive), `reach_edge`, `reach_trans`, `bidi_reach`, `unreachable_no_field_types`
  - `DeadRulePruning.v`: `extract`, `rule_derive`, `full_derive`, `pruned_derive`, `P2_dead_rule_derives_nothing`, `P3_pruned_equals_full`, `fixpoint_unchanged`
