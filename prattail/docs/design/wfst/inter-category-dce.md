# A4: Inter-Category Dead-Code Elimination via Forward-Backward Analysis

**Date:** 2026-03-01

Inter-category dead-code elimination (A4) extends PraTTaIL's three-tier
dead-rule detection with a fourth tier that reasons about the full
inter-category dispatch graph.  Where Tiers 1--3 analyze each category in
isolation, Tier 4 builds a `BooleanWeight` WFST over the inter-category
connections and applies the forward-backward algorithm to identify
categories that are structurally isolated from the root (primary)
category.  Rules in isolated categories are dead regardless of their
intra-category FIRST-set status.

---

## Table of Contents

1. [Problem Statement](#1-problem-statement)
2. [Mechanism](#2-mechanism)
3. [Graph Construction](#3-graph-construction)
4. [Forward-Backward with BooleanWeight](#4-forward-backward-with-booleanweight)
5. [Extension of Existing Detection](#5-extension-of-existing-detection)
6. [Worked Example](#6-worked-example)
7. [Integration with Lint Layer](#7-integration-with-lint-layer)
8. [Correctness Properties](#8-correctness-properties)
9. [Algorithm Complexity](#9-algorithm-complexity)
10. [Source References](#10-source-references)

---

## 1. Problem Statement

### Per-category blindness

The existing three-tier dead-rule detection (`pipeline.rs:detect_dead_rules`)
analyzes each category in isolation:

| Tier | Scope | What it finds |
|------|-------|---------------|
| 1 | Single category | Literal rule with no `native_type` |
| 2 | Single category | Infix/var rule in category with no reachable prefix |
| 3 | Single category | Prefix/cast/cross-cat rule with no FIRST-set dispatch |

This per-category view misses three classes of dead paths that span
multiple categories:

**Dead infix operators in isolated categories.** If a category is
reachable only from itself (it has its own FIRST tokens, so Tier 2 passes)
but no cast or cross-category rule connects it to any category that is
transitively reachable from the root, all of its rules are dead.  The
parser entry point is the root category; a category that the root can
never reach is never parsed.

**Dead cross-category paths.** A cross-category rule `A -> B` may appear
live to Tier 3 (its dispatch token is in FIRST(A), and the WFST routes to
it), yet category `B` may itself be a dead end: no rule in `B` produces a
value that flows back to the root category.  The entire chain is dead, but
each individual tier sees only its own link as live.

**Dead recovery sync tokens.** Error recovery sync predicates reference
the FOLLOW set.  If a category is unreachable from the root, its sync
tokens are dead weight in the generated code.

### Goal

Add a Tier 4 analysis that treats the grammar's categories as a graph and
determines which categories participate in a live path through the root.
Report rules in structurally isolated categories as
`InterCategoryDeadPath` warnings, but only for rules not already flagged
by Tiers 1--3.

---

## 2. Mechanism

### Overview

Tier 4 constructs a directed graph where:

- **Nodes** are grammar categories.
- **Edges** are inter-category connections (cast rules, cross-category
  rules) weighted with `BooleanWeight::one()`.
- **Self-edges** mark categories with non-empty FIRST sets (they can
  start a parse from their own tokens).

The forward-backward algorithm from `forward_backward.rs` is applied
twice with `BooleanWeight`:

1. **Forward pass** from the root (primary) category: compute which
   categories are reachable from the root.
2. **Backward pass** to the root category: compute which categories can
   reach the root.

A category is live if and only if both its forward score and its backward
score are `BooleanWeight(true)`.  Formally:

    live(C) = forward[C] ∧ backward[C]

A rule is flagged as `InterCategoryDeadPath` if `!live(rule.category)`.

### Why BooleanWeight?

The question being answered is pure reachability -- "does any path exist?"
-- not "what is the best path?" (TropicalWeight) or "how many paths
exist?" (CountingWeight).  BooleanWeight is the cheapest semiring that
answers this question: one bit per node, logical OR for alternatives,
logical AND for sequencing.

---

## 3. Graph Construction

### Node assignment

Every category declared in the grammar becomes a node.  Categories are
indexed by their position in the `categories: Vec<CategoryInfo>` vector,
providing O(1) lookup via `cat_to_idx: HashMap<String, usize>`.

### Edge types

Three kinds of edges populate the adjacency list:

**Cast rules** (`rule.is_cast == true`).  A cast rule
`IntToFloat: a:Int |- "float" "(" a ")" : Float` establishes a directed
edge from the source category (`Int`) to the target category (`Float`).
The source is extracted from the first `NonTerminal` in
`rule.first_items`.

```
  Int ──BooleanWeight::one()──→ Float
```

**Cross-category rules** (`rule.is_cross_category == true`).  A cross-
category infix rule `IntAdd: a:Expr + b:Int : Expr` establishes an edge
from `Int` (source) to `Expr` (target).  The same extraction logic
applies.

```
  Int ──BooleanWeight::one()──→ Expr
```

**Self-edges** for categories with non-empty FIRST sets.  A category that
has its own terminals (e.g., `Int` has `Integer`) can start a parse
independently.  A self-edge ensures that the forward pass marks it as
reachable once any path reaches it.

```
  Int ──BooleanWeight::one()──→ Int   (self-loop)
```

### Bidirectional edges for reachability

Both forward and backward reachability require traversing the graph.  The
forward pass follows edges in the natural direction (source to target);
the backward pass needs to traverse edges in the reverse direction.
Rather than building a separate reverse adjacency list, the
implementation inserts **bidirectional edges** for each cast/cross-
category rule:

```
  source ──BooleanWeight::one()──→ target   (forward: source can produce target)
  target ──BooleanWeight::one()──→ source   (backward: target was produced by source)
```

This is correct because BooleanWeight's `plus` operation is `∨`
(idempotent OR): adding a redundant edge from a reverse traversal does
not change the forward result, and vice versa.  The forward pass starting
from node 0 (root) only visits nodes reachable in the forward direction
because it processes nodes in index order (topological).

### Pseudocode

```
function build_inter_category_graph(rule_infos, categories, first_sets):
    cat_to_idx = { c.name → i for i, c in enumerate(categories) }
    edges = [[] for _ in range(len(categories))]

    for rule in rule_infos:
        if rule.is_cast or rule.is_cross_category:
            target_idx = cat_to_idx[rule.category]
            for fi in rule.first_items:
                if fi is NonTerminal(src_cat):
                    src_idx = cat_to_idx[src_cat]
                    edges[src_idx].append((target_idx, BooleanWeight::one()))
                    edges[target_idx].append((src_idx, BooleanWeight::one()))

    for cat, fs in first_sets:
        if fs.tokens is not empty:
            idx = cat_to_idx[cat]
            edges[idx].append((idx, BooleanWeight::one()))

    return edges
```

---

## 4. Forward-Backward with BooleanWeight

### Forward pass

The forward pass computes `alpha[i]` = total weight of all paths from the
root (node 0) to node `i`.  With `BooleanWeight`:

| Operation | Formula | Meaning |
|-----------|---------|---------|
| Initialize root | `alpha[root] = BooleanWeight::one()` | Root is reachable |
| Initialize others | `alpha[i] = BooleanWeight::zero()` | Assume unreachable |
| Propagate | `alpha[target] = alpha[target] ⊕ (alpha[source] ⊗ w)` | |
| ⊕ = `plus` | `a ∨ b` | Any path makes reachable |
| ⊗ = `times` | `a ∧ b` | Both segments must be reachable |

After the forward pass, `alpha[i] == BooleanWeight(true)` iff there
exists at least one path from the root to category `i`.

**Formal statement.** Let G = (V, E) be the inter-category graph with
V = categories, E = edges with BooleanWeight.  Then:

    forward[C] = ⊤   iff   ∃ path (root = C₀, C₁, ..., Cₖ = C)
                            such that ∀ j : (Cⱼ, Cⱼ₊₁) ∈ E

### Backward pass

The backward pass computes `beta[i]` = total weight of all paths from
node `i` to the root.  Processing nodes in reverse index order:

| Operation | Formula | Meaning |
|-----------|---------|---------|
| Initialize root | `beta[root] = BooleanWeight::one()` | Root is target |
| Initialize others | `beta[i] = BooleanWeight::zero()` | Assume cannot reach root |
| Propagate | `beta[source] = beta[source] ⊕ (w ⊗ beta[target])` | |

After the backward pass, `beta[i] == BooleanWeight(true)` iff there
exists at least one path from category `i` to the root.

### Dead category criterion

A category C is dead if the forward-backward conjunction is false:

    dead(C) = ¬forward[C] ∨ ¬backward[C]

The direction field in the warning distinguishes three cases:

| `forward[C]` | `backward[C]` | Direction | Interpretation |
|--------------|---------------|-----------|----------------|
| `false` | `false` | `"forward+backward"` | Completely isolated |
| `false` | `true` | `"forward"` | Reachable from root but cannot return |
| `true` | `false` | `"backward"` | Can return to root but not reachable |
| `true` | `true` | -- | Live (no warning) |

---

## 5. Extension of Existing Detection

Tier 4 is strictly additive.  It does not modify or replace the existing
three tiers.

### Decision flow with Tier 4

```
  Rule
   │
   ▼
  ┌────────────────────────────────┐
  │ Tier 1: Literal rule?          │
  │ (rule_info.is_literal == true) │
  └────────┬───────────────────────┘
           │
     ┌─────┴─────┐
     │yes        │no
     ▼            ▼
  ┌──────────┐  ┌────────────────────────────────────────────┐
  │ Check:   │  │ Tier 2: Same-category infix/var?           │
  │ category │  │ (is_infix && !is_cross_category) || is_var │
  │ has      │  └────────┬───────────────────────────────────┘
  │ native_  │           │
  │ type?    │     ┌─────┴─────┐
  └────┬─────┘     │yes        │no
       │           ▼            ▼
  ┌────┴────┐  ┌──────────┐  ┌──────────────────────────┐
  │no →DEAD │  │ Check:   │  │ Tier 3: WFST reachable?  │
  │yes→LIVE │  │ category │  │ (prefix, cast, cross-cat)│
  └─────────┘  │ reachable│  └────────┬─────────────────┘
               │ ?        │           │
               └────┬─────┘     ┌─────┴─────┐
                    │           │yes        │no
               ┌────┴────┐     ▼            ▼
               │no →DEAD │  ┌──────┐    ┌──────┐
               │yes→LIVE │  │ LIVE │    │ DEAD │
               └─────────┘  └──────┘    └──────┘
                                │
                    (all rules collected from Tiers 1-3)
                                │
                                ▼
                  ┌─────────────────────────────────────┐
                  │ Tier 4: Inter-category reachability │
                  │ (forward-backward with BooleanWeight│
                  │  over inter-category dispatch graph)│
                  └────────────┬────────────────────────┘
                               │
                         ┌─────┴─────┐
                         │per rule:  │
                         │already    │
                         │flagged?   │
                         ▼           ▼
                       ┌────┐    ┌───────────────────────┐
                       │skip│    │ forward[cat] ∧         │
                       └────┘    │ backward[cat] == false?│
                                 └────────┬──────────────┘
                                    ┌─────┴─────┐
                                    │yes        │no
                                    ▼            ▼
                                 ┌──────┐    ┌──────┐
                                 │ DEAD │    │ LIVE │
                                 └──────┘    └──────┘
```

### Tier summary

| Tier | Variant | Condition | Scope |
|------|---------|-----------|-------|
| 1 | `LiteralNoNativeType` | Literal rule, no `native_type` | Single category |
| 2 | `UnreachableCategory` | Infix/var in category with no prefix | Single category |
| 3 | `WfstUnreachable` | No FIRST token dispatches via WFST | Single category |
| 4 (A4) | `InterCategoryDeadPath` | Category isolated from root | Inter-category |

### Deduplication

Tier 4 runs after Tiers 1--3 and only adds `InterCategoryDeadPath`
warnings for rules whose labels do not appear in any Tier 1--3 warning.
This prevents duplicate diagnostics: if a rule is already dead by
Tier 3 (e.g., WFST shadowing), the more specific Tier 3 warning is
preferred over the broader Tier 4 diagnosis.

The deduplication is implemented by collecting the rule labels from
Tiers 1--3 into a `HashSet<String>` and filtering Tier 4 candidates
against it.

---

## 6. Worked Example

### Grammar

Consider a 4-category grammar with the following structure:

```
categories: Proc (primary), Int, Float, Ghost
```

Rules:

| Rule | Category | Type | Connects |
|------|----------|------|----------|
| Nil | Proc | prefix | -- |
| Par | Proc | infix | -- |
| NumLit | Int | literal | -- |
| Add | Int | infix | -- |
| IntToProc | Int | cast | Int -> Proc |
| IntToFloat | Int | cast | Int -> Float |
| FAdd | Float | infix | -- |
| Haunt | Ghost | prefix | -- |
| GhostMul | Ghost | infix | -- |

### Step 1: Build the inter-category graph

```
  Nodes: 0=Proc, 1=Int, 2=Float, 3=Ghost

  Edges from rules:
    IntToProc:  Int(1) → Proc(0), Proc(0) → Int(1)      [cast, bidirectional]
    IntToFloat: Int(1) → Float(2), Float(2) → Int(1)     [cast, bidirectional]

  Self-edges from FIRST sets:
    Proc(0):  has Nil keyword           → 0 → 0
    Int(1):   has Integer literal       → 1 → 1
    Ghost(3): has Haunt keyword         → 3 → 3
    Float(2): no own FIRST tokens       → (no self-edge)
```

Adjacency list:

```
  0 (Proc):  [(1, ⊤), (0, ⊤)]
  1 (Int):   [(0, ⊤), (2, ⊤), (1, ⊤)]
  2 (Float): [(1, ⊤)]
  3 (Ghost): [(3, ⊤)]
```

### Step 2: Forward pass from root (Proc, index 0)

```
  Initialize: alpha = [⊤, ⊥, ⊥, ⊥]

  Process node 0 (Proc):
    Edge 0→1: alpha[1] = ⊥ ∨ (⊤ ∧ ⊤) = ⊤
    Edge 0→0: alpha[0] = ⊤ ∨ (⊤ ∧ ⊤) = ⊤   (no change)

  Process node 1 (Int):
    Edge 1→0: alpha[0] = ⊤ ∨ (⊤ ∧ ⊤) = ⊤   (no change)
    Edge 1→2: alpha[2] = ⊥ ∨ (⊤ ∧ ⊤) = ⊤
    Edge 1→1: alpha[1] = ⊤ ∨ (⊤ ∧ ⊤) = ⊤   (no change)

  Process node 2 (Float):
    Edge 2→1: alpha[1] = ⊤ ∨ (⊤ ∧ ⊤) = ⊤   (no change)

  Process node 3 (Ghost):
    Edge 3→3: alpha[3] = ⊥ ∨ (⊥ ∧ ⊤) = ⊥   (still unreachable!)

  Result: alpha = [⊤, ⊤, ⊤, ⊥]
                   Proc Int Float Ghost
```

### Step 3: Backward pass to root (Proc, index 0)

```
  Initialize: beta = [⊤, ⊥, ⊥, ⊥]

  Process node 3 (Ghost), reverse order:
    Edge 3→3: beta[3] = ⊥ ∨ (⊤ ∧ ⊥) = ⊥   (Ghost cannot reach Proc)

  Process node 2 (Float):
    Edge 2→1: beta[2] = ⊥ ∨ (⊤ ∧ beta[1])
              beta[1] not yet computed... but initialized to ⊥
              beta[2] = ⊥ ∨ (⊤ ∧ ⊥) = ⊥     (initially)

  Process node 1 (Int):
    Edge 1→0: beta[1] = ⊥ ∨ (⊤ ∧ ⊤) = ⊤     (Int can reach Proc!)
    Edge 1→2: beta[1] = ⊤ ∨ (⊤ ∧ ⊥) = ⊤     (no change)
    Edge 1→1: beta[1] = ⊤ ∨ (⊤ ∧ ⊤) = ⊤     (no change)

  Process node 0 (Proc):
    Edge 0→1: beta[0] = ⊤ ∨ (⊤ ∧ ⊤) = ⊤     (no change)
    Edge 0→0: beta[0] = ⊤ ∨ (⊤ ∧ ⊤) = ⊤     (no change)

  Result: beta = [⊤, ⊤, ⊥, ⊥]
                  Proc Int Float Ghost
```

### Step 4: Forward AND backward conjunction

| Category | forward | backward | forward ∧ backward | Status |
|----------|---------|----------|---------------------|--------|
| Proc | ⊤ | ⊤ | ⊤ | Live |
| Int | ⊤ | ⊤ | ⊤ | Live |
| Float | ⊤ | ⊥ | ⊥ | **Dead** (backward) |
| Ghost | ⊥ | ⊥ | ⊥ | **Dead** (forward+backward) |

### Step 5: Warnings generated

**Before deduplication** (Tier 4 raw output):

| Rule | Category | Direction |
|------|----------|-----------|
| FAdd | Float | backward |
| Haunt | Ghost | forward+backward |
| GhostMul | Ghost | forward+backward |

**After deduplication** against Tiers 1--3: assume Tiers 1--3 produced no
warnings for FAdd, Haunt, or GhostMul.  All three Tier 4 warnings are
emitted.

### Diagnostic output

```text
warning[W01]: rule FAdd in category Float is on a dead inter-category path (backward) — forward-backward analysis with BooleanWeight indicates no live path through this category
  = hint: check inter-category connections; this category may be isolated

warning[W01]: rule Haunt in category Ghost is on a dead inter-category path (forward+backward) — forward-backward analysis with BooleanWeight indicates no live path through this category
  = hint: check inter-category connections; this category may be isolated

warning[W01]: rule GhostMul in category Ghost is on a dead inter-category path (forward+backward) — forward-backward analysis with BooleanWeight indicates no live path through this category
  = hint: check inter-category connections; this category may be isolated
```

### Interpretation

- **Float** has a forward path from the root (via `Proc -> Int -> Float`
  through `IntToFloat`) but no backward path to the root.  Values parsed
  as `Float` are never consumed by any rule that produces a `Proc` (root)
  value.  The `IntToFloat` cast creates `Float` values, but nothing
  converts them back.

- **Ghost** is completely isolated: no rule connects it to any other
  category.  Despite having its own FIRST tokens (so Tier 2 does not flag
  it), the parser entry point is `Proc`, and `Ghost` is never entered.

---

## 7. Integration with Lint Layer

### Call site

Tier 4 analysis is invoked from `lint_w01_dead_rule()` in `lint.rs`,
immediately after the Tier 1--3 `detect_dead_rules()` call:

```
lint_w01_dead_rule(ctx, diagnostics):
    // Tiers 1-3
    warnings = detect_dead_rules(ctx.rules, ctx.categories,
                                 ctx.first_sets, ctx.prediction_wfsts)

    // Tier 4 (A4)
    inter_cat_warnings = detect_inter_category_dead_paths(
        ctx.rules, ctx.categories, ctx.first_sets)

    // Deduplication: only add Tier 4 for unflagged rules
    existing_rules = { w.rule_label for w in warnings }
    for w in inter_cat_warnings:
        if w.rule_label not in existing_rules:
            warnings.append(w)

    // Emit all as W01 LintDiagnostics
    for w in warnings:
        diagnostics.append(LintDiagnostic {
            id: "W01",
            name: "dead-rule",
            severity: Warning,
            category: w.category,
            rule: w.rule_label,
            message: format(w),
            hint: tier_specific_hint(w),
        })
```

### LintDiagnostic mapping

| Variant | Hint |
|---------|------|
| `LiteralNoNativeType` | "add a native_type to the category or remove the literal rule" |
| `UnreachableCategory` | "add a prefix rule to make the category reachable" |
| `WfstUnreachable` | "remove the rule or add a unique dispatch token" |
| `InterCategoryDeadPath` | "check inter-category connections; this category may be isolated" |

### Data flow

```
  pipeline.rs: generate_parser_code()
       │
       ▼
  ┌──────────────────────────────────────────────────────┐
  │ lint::LintContext                                    │
  │ { categories, rules, first_sets, prediction_wfsts } │
  └──────────────────┬───────────────────────────────────┘
                     │
                     ▼
  lint::run_lints(&ctx)
       │
       ├─ W01: lint_w01_dead_rule
       │       │
       │       ├─ detect_dead_rules()           ◄── Tiers 1-3
       │       │
       │       ├─ detect_inter_category_dead_paths()  ◄── Tier 4 (A4)
       │       │
       │       └─ deduplication + LintDiagnostic emission
       │
       ├─ W02..W06, G01..G10, R01..R07, C01..C04, P02..P04
       │
       ▼
  Vec<LintDiagnostic>
       │
       ▼
  lint::emit_diagnostics()  →  stderr
```

---

## 8. Correctness Properties

### No false positives

Tier 4 uses **necessary conditions** for liveness.  A rule flagged as
`InterCategoryDeadPath` is provably unreachable:

- **Forward false**: If `forward[C] == BooleanWeight(false)`, then no
  sequence of cast/cross-category edges connects the root to category C.
  Since parsing begins at the root and can only enter other categories
  via cast or cross-category rules, the parser never enters C.  This is
  a structural property of the grammar, not a runtime property.

- **Backward false**: If `backward[C] == BooleanWeight(false)`, then no
  sequence of edges connects C back to the root.  A value produced in C
  is never consumed by any rule chain that ultimately produces a root-
  category value.  Since the parser requires a root-category result,
  values stranded in C are unused.

### Permitted false negatives

The analysis is intentionally conservative.  Known sources of false
negatives:

- **Infix chains within an isolated category**: If category C has
  prefix, infix, and postfix rules but is isolated from the root, Tier 4
  flags all rules in C.  However, if C is connected to the root via an
  infix rule in the root category (e.g., `Proc + Ghost`), the
  bidirectional edge makes C reachable.  An infix rule that references
  C via its RHS NonTerminal is not modeled as an edge (only cast and
  cross-category rules are edges), so some live paths through infix
  references may be missed.

- **Error recovery paths**: Categories reachable only via error recovery
  token insertion are not modeled.  This is consistent with Tiers 1--3,
  which also do not model recovery paths.

### Monotonicity

Adding a cast or cross-category rule can only add edges to the graph,
which can only increase forward and backward scores (BooleanWeight is a
bounded lattice with ⊥ <= ⊤).  Therefore, adding rules never makes a
previously live category dead.

### Relation to Tier 2

Tier 2's `reachable_categories` set computes a similar fixed-point, but
with an important difference: it seeds from all categories with non-empty
FIRST sets, not just the root.  A category with its own FIRST tokens is
Tier 2-reachable even if isolated from the root.  Tier 4's forward pass
starts only from the root, so it catches isolated categories that Tier 2
misses.

```
  Tier 2 reachable:  { C | FIRST(C) != empty } ∪ { C transitively reachable }
  Tier 4 forward:    { C | path from root to C in inter-category graph }

  Tier 4 forward ⊆ Tier 2 reachable   (root-seeded is stricter)
```

---

## 9. Algorithm Complexity

| Phase | Complexity | Description |
|-------|-----------|-------------|
| Graph construction | O(\|rules\| + \|categories\|) | Single pass over rules and FIRST sets |
| Forward pass | O(\|categories\| + \|edges\|) | Linear in graph size |
| Backward pass | O(\|categories\| + \|edges\|) | Linear in graph size |
| Warning collection | O(\|rules\|) | Single pass, O(1) per rule |
| Deduplication | O(\|warnings\|) | HashSet insert + lookup |

Total: O(|rules| + |categories| + |edges|), which is dominated by the
single pass over rules during graph construction.  Since |edges| <=
2 * |rules| + |categories| (each cast/cross-cat rule produces 2 edges,
each FIRST-set category produces 1 self-edge), this simplifies to
O(|rules| + |categories|).

In practice, the inter-category graph is small (typically 3--15
categories), so the forward-backward passes complete in constant time
for all practical grammars.

---

## 10. Source References

| Component | File | Description |
|-----------|------|-------------|
| `detect_inter_category_dead_paths()` | `pipeline.rs` | Tier 4 graph construction + forward-backward + warning collection |
| `forward_scores()` | `forward_backward.rs` | Generic forward pass over adjacency list |
| `backward_scores()` | `forward_backward.rs` | Generic backward pass over adjacency list |
| `BooleanWeight` | `automata/semiring.rs` | Boolean semiring: `(∨, ∧, false, true)` |
| `Semiring` trait | `automata/semiring.rs` | Generic semiring interface |
| `DeadRuleWarning::InterCategoryDeadPath` | `pipeline.rs` | Warning variant with direction field |
| `lint_w01_dead_rule()` | `lint.rs` | Tier 4 invocation and deduplication logic |
| `CategoryInfo` | `pipeline.rs` | Category metadata including `is_primary` flag |
