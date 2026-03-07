# Explicit BP Specification via DSL Annotations

While PraTTaIL deduces binding powers implicitly from declaration order
(see [02-implicit-deduction.md](02-implicit-deduction.md)), two DSL annotations
allow explicit control: `right` for associativity and `prefix(N)` for unary
prefix binding power.

**Source files:**
- `macros/src/ast/grammar.rs:97-340` — DSL parsing of `right` and `prefix(N)`
- `macros/src/gen/syntax/parser/prattail_bridge.rs:84-123` — Bridge: `GrammarRule` to `RuleSpecInput`
- `prattail/src/pipeline.rs:1211-1220` — Prefix BP override logic

---

## 1. The `right` Keyword

### 1.1 Syntax

The `right` keyword appears after the rule body and optional evaluation mode:

```rust
// Right-associative infix
Pow . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] step right;

// Right-associative without HOL code
Pow . a:Int, b:Int |- a "^" b : Int right;

// Right-associative mixfix (ternary)
Tern . c:Int, t:Int, e:Int |- c "?" t ":" e : Int right;
```

### 1.2 Semantics

The `right` keyword sets `GrammarRule::is_right_assoc = true`, which
propagates through the bridge as `associativity: Associativity::Right` on
the `RuleSpec`.

During BP assignment in `analyze_binding_powers()`, a right-associative operator
at precedence level *k* receives **swapped** BPs:

```
Left-associative  (default):  (left_bp, right_bp) = (2k+2, 2k+3)
Right-associative (right):    (left_bp, right_bp) = (2k+3, 2k+2)
```

The swap means `left_bp > right_bp`. When the Pratt loop sees a second instance
of the same operator, its `left_bp` (2k+3) is ≥ the parent's `right_bp` (2k+2,
now serving as `min_bp`), so parsing **continues** into the right operand —
producing right-associative grouping.

### 1.3 Example: Exponentiation

```rust
Add . a:Int, b:Int |- a "+" b : Int;      // level 0: (2, 3)
Mul . a:Int, b:Int |- a "*" b : Int;      // level 1: (4, 5)
Pow . a:Int, b:Int |- a "^" b : Int right; // level 2: (7, 6)  ← swapped
```

Parsing `2 ^ 3 ^ 4`:

```
Step 1: parse_Int(tokens, pos, 0)
  prefix: lhs = 2
  loop: token = "^", infix_bp returns (7, 6)
        7 ≥ 0 → continue, consume "^"
        rhs = parse_Int(tokens, pos, 6)    ← recursive call with min_bp = 6
          prefix: lhs = 3
          loop: token = "^", infix_bp returns (7, 6)
                7 ≥ 6 → continue           ← right-assoc: 7 ≥ 6 passes!
                consume "^"
                rhs = parse_Int(tokens, pos, 6)
                  prefix: lhs = 4
                  loop: no more tokens → break
                  return 4
                lhs = Pow(3, 4)
                loop: no more tokens → break
          return Pow(3, 4)
        lhs = Pow(2, Pow(3, 4))            ← correct: right-associative
```

If `Pow` were left-associative with BPs `(6, 7)`, the second `^` would have
`left_bp = 6 < 7 = min_bp` → **break**, yielding `Pow(Pow(2, 3), 4)`.

---

## 2. The `prefix(N)` Annotation

### 2.1 Syntax

The `prefix(N)` annotation appears after `right` (if present) or after the
evaluation mode:

```rust
// Explicit prefix BP
Neg . a:Int |- "-" a : Int prefix(5);

// Combined with eval mode
Neg . a:Int |- "-" a : Int ![(-a)] fold prefix(5);

// Combined with right (unusual but valid)
Neg . a:Int |- "-" a : Int right prefix(5);
```

`N` must be a `u8` literal.

### 2.2 Semantics

By default, all unary prefix operators in a category share the same BP:

```
prefix_bp = max_infix_bp + 2
```

where `max_infix_bp` is the maximum of all `left_bp` and `right_bp` values
across non-postfix operators in the same category.

The `prefix(N)` annotation overrides this default with the explicit value `N`.
This allows different unary prefix operators to have different binding powers.

### 2.3 Override Logic

The override happens in `pipeline.rs` when constructing `RDRuleInfo`:

```rust
let prefix_bp = if rule.is_unary_prefix {
    if let Some(explicit_bp) = rule.prefix_precedence {
        Some(explicit_bp)         // ← prefix(N) override
    } else {
        let cat_max = max_infix_bp.get(&rule.category).copied().unwrap_or(0);
        Some(cat_max + 2)         // ← default: max_infix_bp + 2
    }
} else {
    None
};
```

**Source:** `prattail/src/pipeline.rs:1211-1220`

### 2.4 When to Use `prefix(N)`

Use `prefix(N)` when you need:

1. **Different prefix operators at different precedence levels.** For example,
   if `not` should bind looser than `-`:

   ```rust
   Not . a:Int |- "not" a : Int prefix(3);  // binds loosely
   Neg . a:Int |- "-" a : Int;              // default: max_infix_bp + 2
   ```

2. **A prefix operator that binds looser than some infix operators.** The
   default (`max_infix_bp + 2`) places prefix above all infix, but sometimes
   a "statement-level" prefix should bind below multiplication:

   ```rust
   // With Add (2,3), Mul (4,5): max_infix_bp = 5, default prefix_bp = 7
   Return . a:Int |- "return" a : Int prefix(3);  // between Add and Mul
   ```

   With `prefix(3)`, `return 2 * 3` parses as `return (2 * 3)` because `*`
   has `left_bp = 4 ≥ 3 = min_bp`. But `return 2 + 3` also parses as
   `return (2 + 3)` because `+` has `left_bp = 2 < 3 = min_bp` — wait, that
   would **stop** at `+`, giving `(return 2) + 3`. This shows that explicit
   prefix BPs require careful analysis of the desired behavior.

---

## 3. Combining `right` and `prefix(N)`

Both annotations can appear on the same rule. They are orthogonal:

- `right` affects the **infix** BP pair assignment (swaps left/right).
- `prefix(N)` affects the **prefix** BP (only meaningful for unary prefix rules).

In practice, combining them is unusual because:
- `right` is meaningful for infix/mixfix rules.
- `prefix(N)` is meaningful for unary prefix rules.
- A rule is rarely both (and structurally cannot be — infix has 3+ items,
  unary prefix has exactly 2).

However, the parser accepts both on any rule without error, and the bridge
propagates both fields independently:

```rust
RuleSpecInput {
    associativity: if rule.is_right_assoc { Right } else { Left },
    prefix_precedence: rule.prefix_bp,
    ...
}
```

---

## 4. Data Flow: DSL to Codegen

```
┌─────────────────────────────────────────────────────────────────────────┐
│                          DSL Source                                     │
│  Pow . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] step right;     │
│  Neg . a:Int |- "-" a : Int ![(-a)] fold prefix(5);                     │
└────────────────────────────────┬────────────────────────────────────────┘
                                 │
                                 ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                  macros/src/ast/grammar.rs                              │
│  parse_grammar_rule_new() →                                             │
│    GrammarRule {                                                        │
│      is_right_assoc: true,     ← from "right" keyword                   │
│      prefix_bp: Some(5),       ← from "prefix(5)" annotation            │
│      ...                                                                │
│    }                                                                    │
└────────────────────────────────┬────────────────────────────────────────┘
                                 │
                                 ▼
┌─────────────────────────────────────────────────────────────────────────┐
│            macros/.../prattail_bridge.rs                                │
│  convert_rule() →                                                       │
│    RuleSpecInput {                                                      │
│      associativity: Associativity::Right,                               │
│      prefix_precedence: Some(5),                                        │
│      ...                                                                │
│    }                                                                    │
└────────────────────────────────┬────────────────────────────────────────┘
                                 │
                                 ▼
┌─────────────────────────────────────────────────────────────────────────┐
│            prattail/src/pipeline.rs                                     │
│                                                                         │
│  classify_rule() →                                                      │
│    RuleSpec {                                                           │
│      associativity: Right,     ← used by analyze_binding_powers()       │
│      is_unary_prefix: false,   ← Pow is infix, not prefix               │
│      prefix_precedence: Some(5),                                        │
│      ...                                                                │
│    }                                                                    │
│                                                                         │
│  For Neg (is_unary_prefix = true):                                      │
│    prefix_bp = Some(5)         ← explicit override from prefix(5)       │
│    (default would be max_infix_bp + 2 = 7 + 2 = 9)                      │
│                                                                         │
│  For Pow (is_infix = true):                                             │
│    analyze_binding_powers() uses associativity = Right                  │
│    → (left_bp, right_bp) = (2k+3, 2k+2) = (7, 6) at level 2             │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 5. Annotation Parsing Details

The DSL parser (`grammar.rs:294-321`) processes annotations in a loop after
the optional evaluation mode:

```rust
while input.peek(syn::Ident) {
    let kw = fork.parse::<syn::Ident>()?;
    if kw == "right" {
        is_right_assoc = true;
    } else if kw == "prefix" {
        // Parse (N) — parenthesized u8 literal
        let bp_val: u8 = content.parse::<LitInt>()?.base10_parse()?;
        prefix_bp = Some(bp_val);
    } else {
        return Err("expected 'right', 'prefix(N)', or ';'");
    }
}
```

This means annotations can appear in any order after the eval mode:

```rust
Rule . ... : Cat ![code] step right prefix(5);   // ✓
Rule . ... : Cat ![code] step prefix(5) right;   // ✓
Rule . ... : Cat right prefix(5);                 // ✓ (no HOL code)
Rule . ... : Cat prefix(5);                       // ✓
Rule . ... : Cat right;                           // ✓
```

**Source:** `macros/src/ast/grammar.rs:294-321`
