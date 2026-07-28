# Implicit BP Deduction from Declaration Order

PraTTaIL deduces binding power pairs from the **order** in which rules are
declared and their **structural patterns**. No explicit precedence annotations
are required for standard cases. This document details the full algorithm.

**Source files:**
- `prattail/src/binding_power.rs` — `analyze_binding_powers()`
- `prattail/src/classify.rs` — structural classification
- `prattail/src/pipeline.rs:1111-1155` — BP table construction, `max_infix_bp`

---

## 1. Declaration-Order Precedence

Within a grammar category, **earlier-declared infix rules get lower precedence**
(bind less tightly). This mirrors the mathematical convention where "weaker"
operations (addition) are stated before "stronger" ones (multiplication):

```rust
terms {
    Add . a:Int, b:Int |- a "+" b : Int;   // precedence level 0 (lowest)
    Mul . a:Int, b:Int |- a "*" b : Int;   // precedence level 1 (higher)
    Pow . a:Int, b:Int |- a "^" b : Int right;  // precedence level 2 (highest)
}
```

This yields:

| Rule | Precedence Level *k* | BP Pair               |
|------|----------------------|-----------------------|
| Add  | 0                    | (2, 3)  — left-assoc  |
| Mul  | 1                    | (4, 5)  — left-assoc  |
| Pow  | 2                    | (7, 6)  — right-assoc |

The formula is spelled out below (§3).

---

## 2. Structural Classification

Before BP assignment, each rule is classified by its syntactic shape. The
classifier (`classify.rs`) examines `SyntaxItemSpec` sequences to detect:

| Classification          | Pattern                               | Criteria                                                          |
|-------------------------|---------------------------------------|-------------------------------------------------------------------|
| **Same-category infix** | `[NT(Cat), Terminal, NT(Cat), ...]`   | First item is `NT(same_category)`, second is `Terminal`, ≥3 items |
| **Postfix**             | `[NT(Cat), Terminal]`                 | Exactly 2 items: `NT(same_category)` then `Terminal`              |
| **Unary prefix**        | `[Terminal, NT(Cat)]`                 | Exactly 2 items: `Terminal` then `NT(same_category)`              |
| **Cross-category**      | `[NT(CatA), Terminal, NT(CatA)]`      | 3 items, both NTs same category but ≠ result category             |
| **Cast**                | `[NT(CatB)]`                          | Single NT of different known category                             |
| **Mixfix**              | `[NT(Cat), T₁, NT(...), T₂, NT(...)]` | Infix with 2+ terminals (e.g., ternary `a ? b : c`)               |

**Key rule:** `is_infix = classify_is_infix(syntax) || is_postfix || is_cross_category`.
Postfix and cross-category rules are both classified as infix for BP purposes
because they participate in the Pratt loop's led chain.

Unary prefix rules are **not** classified as infix. They are handled by the
nud (prefix) handler, not the led (infix) chain. Their binding power is
computed separately (§5).

**Source:** `prattail/src/classify.rs`, `classify_rule()`

---

## 3. The `analyze_binding_powers()` Algorithm

The algorithm takes a list of `InfixRuleInfo` structs (one per infix rule) and
produces a `BindingPowerTable`. It operates **per category** in two passes.

### 3.1 Full Pseudocode

```
FUNCTION analyze_binding_powers(rules: [InfixRuleInfo]) → BindingPowerTable:
    table ← empty BindingPowerTable
    by_category ← group rules by category (preserving declaration order)

    FOR EACH category in by_category:
        precedence    ← 2                           ▷ Reserve 0 (entry), 1 (padding)
        level_is_open ← FALSE

        ▷ ─── Pass 1: Non-postfix operators ────────
        FOR EACH rule in category WHERE NOT rule.is_postfix:
            ▷ Advance once per LEVEL, not once per rule. A rule marked `same`
            ▷ joins the level its predecessor opened.
            IF level_is_open AND NOT rule.shares_level_with_previous:
                precedence ← precedence + 2
            level_is_open ← TRUE

            IF rule.associativity = Left:
                left_bp  ← precedence
                right_bp ← precedence + 1
            ELSE:  ▷ Right-associative
                left_bp  ← precedence + 1
                right_bp ← precedence

            table.add(InfixOperator {
                terminal:  rule.terminal,
                category:  rule.category,
                left_bp, right_bp,
                label:     rule.label,
                is_postfix:  false,
                is_mixfix:   rule.is_mixfix,
                ...
            })

        ▷ ─── Pass 2: Postfix operators ────────────
        ▷ Pass 1 advances lazily, so `precedence` ends ON the last level rather
        ▷ than one past it. Reconstruct the first free slot before adding the gap.
        first_free   ← IF level_is_open THEN precedence + 2 ELSE precedence
        postfix_prec ← first_free + 2               ▷ Gap for prefix BP

        FOR EACH rule in category WHERE rule.is_postfix:
            table.add(InfixOperator {
                terminal:  rule.terminal,
                left_bp:   postfix_prec + 1,
                right_bp:  0,                        ▷ Unused (no right operand)
                is_postfix: true,
                ...
            })
            postfix_prec ← postfix_prec + 2

    RETURN table
```

### 3.2 Mathematical Formulas

Let a category declare *n* non-postfix infix operators partitioned into *L* precedence
**levels** (levels, not rules — a `same`-annotated rule joins its predecessor's level, so
`L ≤ n`, with equality exactly when no rule carries `same`), and *m* postfix operators.

**Non-postfix operator on level *k* (0 ≤ k < L):**

```math
\text{Left-associative:}\quad  (\ell, r) = (2k + 2,\; 2k + 3)
```

```math
\text{Right-associative:}\quad (\ell, r) = (2k + 3,\; 2k + 2)
```

Both satisfy $`\min(\ell, r) = 2k + 2`$, which is how a consumer recovers the level, and
they differ only in the ORDER of the pair, which is how a consumer recovers the
associativity. The two are independent, so a single level may hold operators of both
kinds — as Rholang's level 6 does, with right-associative `matches` beside
left-associative `==` and `!=`.

> **Historical note (2026-07-28).** Both branches used to end in `precedence ← precedence
> + 2`, so `L = n` always. Rule *i* then received $`\ell \in \{2 + 2i,\; 3 + 2i\}`$, and
> two rules $`i < j`$ could share an $`\ell`$ only if $`3 + 2i = 2 + 2j`$, i.e.
> $`2(j - i) = 1`$ — unsatisfiable over the integers. Equal precedence was therefore
> **unrepresentable**, not merely unused: no grammar could express that `*` and `/` bind
> equally tightly, and `6 * 3 / 2` parsed as `6 * (3 / 2)`.

**Max non-postfix BP** (after pass 1):

```
M = max{left_bp, right_bp} across all non-postfix operators
  = 2n + 1   (when n ≥ 1)
```

If no non-postfix operators exist, `M = 0`.

**Unary prefix BP** (computed in `pipeline.rs`, not `binding_power.rs`):

```
prefix_bp = M + 2 = 2n + 3   (default)
          = explicit_value    (when prefix(N) is specified)
```

**Postfix operator at index *j* (0 ≤ j < m):**

```
left_bp  = M + 4 + 2j = 2(n + j) + 5
right_bp = 0  (unused)
```

### 3.3 BP Number Line

```
 0    2   3    4   5   ...  2n  2n+1  2n+2  2n+3  2n+4  2n+5  ...
 │    └─ op₀ ─┘   └─ op₁ ─┘        │      │      │      │
 │    (infix, level 0)             M     M+1    M+2    M+3
 │                                 │             │      │
entry                           max non-       prefix  first
(min_bp=0)                      postfix BP      BP    postfix
                                                      left_bp
```

---

## 4. Per-Category Independence

Each grammar category gets its own BP namespace, starting at `precedence = 2`.
BPs are **not shared** across categories. This means:

- `Int::Add` with BP `(2, 3)` and `Bool::And` with BP `(2, 3)` are independent.
- A cross-category operator like `a:Int == b:Int : Bool` gets BPs in the
  **source** category's namespace (`Int`), not the result category (`Bool`).

**Why?** The Pratt loop only runs within a single category. When parsing an
`Int` expression, only `Int`-category BPs are consulted. Cross-category
operators are dispatched via a wrapper function in the result category.

---

## 5. The Three-Level BP Hierarchy

PraTTaIL enforces a strict hierarchy between operator forms:

```
                    ┌─────────────────────────────────┐
                    │        Postfix (tightest)       │
                    │   left_bp = M + 4 + 2j          │
                    ├─────────────────────────────────┤
                    │      Unary Prefix (middle)      │
                    │   prefix_bp = M + 2             │
                    ├─────────────────────────────────┤
                    │    Binary Infix (loosest)       │
                    │   BPs from 2 to M               │
                    └─────────────────────────────────┘
```

This hierarchy ensures standard mathematical conventions:

| Expression | Interpretation | Reason                            |
|------------|----------------|-----------------------------------|
| `-a + b`   | `(-a) + b`     | Prefix binds tighter than infix   |
| `-a!`      | `-(a!)`        | Postfix binds tighter than prefix |
| `a + b!`   | `a + (b!)`     | Postfix binds tighter than infix  |

### 5.1 The Two-Pass Algorithm

The two-pass structure (non-postfix first, then postfix) creates a **gap** in
the BP number line between infix and postfix operators. This gap is where the
unary prefix BP lives:

```
Pass 1 output:  precedence = 2n + 2  (one past the last non-postfix right_bp)
Gap:            prefix_bp  = 2n + 3  (= precedence + 1, i.e., M + 2)
Pass 2 starts:  postfix_prec = 2n + 4  (= precedence + 2)
```

The gap is exactly two BP values wide (`precedence` and `precedence + 1`),
which is enough for the prefix BP to sit between infix and postfix without
overlapping either range.

### 5.2 Declaration Order for Postfix

Like non-postfix operators, multiple postfix operators get ascending BPs in
declaration order. However, since all postfix operators bind tighter than all
infix operators regardless of declaration order, the relative ordering among
postfix operators matters only when multiple postfix operators apply to the
same operand (which is unusual but valid).

---

## 6. Data Flow: Rules → BP Table

```
┌────────────────────────┐    ┌────────────────────────┐    ┌───────────────────┐
│ language! { terms { }} │    │  macros crate          │    │  PraTTaIL crate   │
│                        │───▶│  prattail_bridge.rs    │───▶│  pipeline.rs      │
│  Add . a:Int ...       │    │  convert_rule()        │    │                   │
│  Mul . a:Int ...       │    │  GrammarRule →         │    │  1. Filter        │
│  Neg . a:Int ...       │    │    RuleSpecInput →     │    │     is_infix      │
│  Fact . a:Int ...      │    │      RuleSpec          │    │  2. Extract       │
│                        │    └────────────────────────┘    │     InfixRuleInfo │
└────────────────────────┘                                  │  3. Call          │
                                                            │     analyze_      │
                              ┌────────────────────────┐    │     binding_      │
                              │ BindingPowerTable      │◀───│     powers()      │
                              │  operators: Vec<       │    │  4. Compute       │
                              │    InfixOperator>      │    │     max_infix_bp  │
                              └────────────────────────┘    │  5. Assign        │
                                                            │     prefix_bp     │
                                                            └───────────────────┘
```

**Source:** `prattail/src/pipeline.rs:1111-1155`
