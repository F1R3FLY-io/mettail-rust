# Layer 2: Parse Prediction

Parse prediction is the second layer in PraTTaIL's six-layer model. It consumes
the token stream produced by Layer 1 (lexical disambiguation) and determines
**which parse rule** to apply for a given grammar category, given the next token(s).

Without parse prediction, the parser would need to try every rule for a category
and backtrack on failure -- O(rules) work per parse decision. Prediction makes most
decisions O(1) by precomputing dispatch tables from FIRST sets.

**Source files:**
- `prattail/src/prediction.rs` -- FIRST/FOLLOW sets, dispatch tables, overlap analysis

**Cross-references:**
- [theory/prediction-and-lookahead.md](../../theory/prediction-and-lookahead.md) §2-4
- [design/prediction-engine.md](../prediction-engine.md) §2-5, §7, §10

---

## 1. The Parse Decision Problem

A grammar category like `Proc` (process) may have many alternative rules:

```
Proc ::= PZero          // "0"
       | PInput          // "for" "(" ... ")" "{" ... "}"
       | POutput         // name "!" "(" ... ")"
       | PNew            // "new" name "in" "{" ... "}"
       | PIf             // "if" expr "then" ... "else" ...
       | PVar            // name (variable)
       | PPar            // proc "|" proc
       | ...
```

When the parser needs a `Proc` and sees the next token, it must decide which rule
to try. Trying all rules sequentially would require backtracking and is O(n) in
the number of rules. The parse prediction layer eliminates this trial-and-error.

---

## 2. FIRST Set Computation as Disambiguation

A **FIRST set** for a grammar category is the set of tokens that can legally
begin an expression of that category. If FIRST sets for different rules within a
category are **disjoint**, the next token uniquely determines which rule to apply.

### 2.1 Fixed-Point Iteration Algorithm

PraTTaIL computes FIRST sets via fixed-point iteration (`prediction.rs`,
`compute_first_sets()`, lines 181-244):

```
1. Initialize: FIRST(Cat) = {} for all categories
2. Repeat until no changes:
   For each non-infix rule R in category Cat:
     For each FirstItem in R.first_items:
       - Terminal(t):     FIRST(Cat) += {variant_name(t)}
       - NonTerminal(C):  FIRST(Cat) += FIRST(C)
       - Ident:           FIRST(Cat) += {"Ident"}
3. Convergence: at most |categories| + 1 iterations
   (each iteration expands at least one set, or the algorithm terminates)
```

**Why infix rules are skipped (line 203-204):** Infix rules like `A + A` start
with a recursive reference to the same category (`A`), which is handled by the
Pratt loop (Layer 3). They do not contribute new tokens to FIRST sets -- the
tokens that begin the left operand are already in FIRST(A) from the prefix rules.

### 2.2 Worked Example: Calculator Language

Consider a calculator with three categories:

```
Category Int:                     Category Bool:
  NumLit(Integer)                   BTrue("true"), BFalse("false")
  IVar(Ident)                       BVar(Ident)
  INeg("-", Int)                    BNot("!", Bool)
  IAdd(Int, "+", Int)               BAnd(Bool, "&&", Bool)
  Eq(Int, "==", Int) → Bool         Eq rule is cross-category
```

FIRST set computation:

```
Iteration 1:
  FIRST(Int)  = {Integer, Ident, Minus}    (from NumLit, IVar, INeg)
  FIRST(Bool) = {Boolean, Ident, Bang}     (from BTrue/BFalse, BVar, BNot)

Iteration 2:
  No changes -- no non-terminal first items reference other categories
  in prefix position.

Result:
  FIRST(Int)  = {Integer, Ident, Minus}
  FIRST(Bool) = {Boolean, Ident, Bang}
```

### 2.3 Disjoint FIRST Sets → Deterministic Dispatch

When each rule within a category starts with a unique token, the dispatch is
fully deterministic:

```
Category Proc dispatch:

  Token         Rule        Reason
  ─────────────────────────────────────────────────
  "0"      →    PZero       Only rule starting with "0"
  "for"    →    PInput      Only rule starting with "for"
  "new"    →    PNew        Only rule starting with "new"
  "if"     →    PIf         Only rule starting with "if"
  Ident    →    PVar        Default (variable fallback)

  ┌──────────────────────────────────────────────┐
  │         Token seen?                          │
  │                                              │
  │  "0" ──→ parse_PZero()                       │
  │  "for"──→ parse_PInput()                     │
  │  "new"──→ parse_PNew()                       │
  │  "if" ──→ parse_PIf()                        │
  │  Ident ─→ parse_PVar()  (fallback)           │
  │  other ─→ error                              │
  └──────────────────────────────────────────────┘
```

Each parse decision is a single token inspection: O(1).

---

## 3. Dispatch Table Construction

The dispatch table maps each first token to a `DispatchAction` (`prediction.rs`,
`build_dispatch_tables()`, lines 547-712).

### 3.1 The DispatchAction Enum

| Action | When Used | Description |
|--------|-----------|-------------|
| `Direct` | Unambiguous single rule | Call parse function immediately |
| `Lookahead` | Multiple rules share first token | Inspect second token to disambiguate |
| `CrossCategory` | Rule references different category | Parse source category, check for operator |
| `Cast` | Type embedding rule | Parse source category, wrap result |
| `Grouping` | Parenthesized expression | Match open, parse inner, match close |
| `Variable` | Default fallback | Accept any Ident as variable |

### 3.2 The Construction Algorithm

For each category:

1. Collect all non-infix rules
2. Build map: `first_token → [matching_rules]`
3. For each first token:
   - **One rule:** Emit `Direct`, `Cast`, or `Variable` action
   - **Multiple rules:** Emit `Lookahead` action with alternatives
4. If category has a variable rule: set as `default_action`

### 3.3 Dispatch Table Data Structure

```rust
struct DispatchTable {
    category: String,
    entries: BTreeMap<String, DispatchAction>,   // token → action
    default_action: Option<DispatchAction>,      // usually Variable
}
```

The `BTreeMap` ensures deterministic code generation order. The `default_action`
handles tokens not explicitly listed in `entries` (typically the variable rule
which accepts any `Ident`).

---

## 4. Lookahead as Disambiguation

When FIRST sets overlap -- multiple rules in the same category start with the
same token -- PraTTaIL uses **two-token lookahead** to disambiguate.

### 4.1 When Lookahead Is Needed

Lookahead is needed in two situations:

1. **Multiple structural rules share a first token:** Two rules both start with
   `Ident` but diverge at the second token.

2. **One structural rule + variable fallback:** A rule starts with `Ident`
   followed by a specific operator, but `Ident` alone could also be a variable.

### 4.2 Worked Example: POutput vs PVar

Both `POutput` (name `!` `(` ... `)`) and `PVar` (name) start with `Ident`:

```
Input: x ! ( 42 )     →  POutput (x sends 42)
Input: x               →  PVar    (variable x)

First token: Ident in both cases.
```

Lookahead resolves this by inspecting the second token:

```
  ┌──────────────────────────────────────────────┐
  │  Token[0] = Ident                            │
  │                                              │
  │  Peek Token[1]:                              │
  │    "!" ──→ parse_POutput()                   │
  │    other → parse_PVar()  (variable fallback) │
  └──────────────────────────────────────────────┘
```

The generated code:

```rust
// DispatchAction::Lookahead with variable fallback
Token::Ident(_) => {
    if let Some(next) = peek_ahead(tokens, *pos) {
        match next {
            Token::Bang => parse_POutput(tokens, pos)?,
            _ => /* variable fallback */ ...
        }
    } else {
        /* variable fallback (end of input) */ ...
    }
}
```

### 4.3 The LookaheadAlternative Structure

Each lookahead alternative specifies the second token and the rule to dispatch to:

```rust
struct LookaheadAlternative {
    lookahead_token: String,    // Token at position +1
    rule_label: String,         // Rule constructor to use
    parse_fn: String,           // Parse function to call
}
```

Multiple alternatives can be listed for the same first token, each with a
different second token.

### 4.4 Lookahead Bounds

PraTTaIL uses at most **2-token lookahead** (current + peek). This is sufficient
for all grammar patterns PraTTaIL supports because:

- Pratt rules are classified by their **first terminal** (prefix) or by the
  operator between operands (infix)
- Non-Pratt rules have unique structural patterns that diverge within 2 tokens
- The variable fallback catches any remaining ambiguity

---

## 5. Variable Fallback

Every category with a variable rule has a **default fallback** that catches any
`Ident` token not claimed by a structural rule.

### 5.1 How It Works

1. Variable rules are marked `is_var: true` during rule classification
2. The dispatch table builder sets `default_action = Variable { category }`
3. At parse time: if no `entries` key matches the current token, and the token
   is `Ident`, the fallback produces a variable node

### 5.2 Priority Ordering

Variable rules have the **lowest** dispatch priority:

```
Priority (highest to lowest):
  1. Exact terminal match (Direct/Cast/Grouping actions)
  2. Lookahead alternatives
  3. Lookahead fallback → Variable
  4. Default action → Variable
```

This ensures that `for` dispatches to `PInput` (exact match) even though `for`
is technically also a valid identifier in some languages.

### 5.3 Disambiguation Role

Variable fallback resolves a class of ambiguity that FIRST sets alone cannot:
the token `Ident("x")` appears in the FIRST set of every category that has
variables. Without variable fallback, the parser would need to try each rule
that starts with `Ident`. With fallback, the dispatch table handles `Ident`
via lookahead (for structural rules) or falls through to variable construction.

---

## 6. Native Literal Token Augmentation

When a grammar category has a **native type** (e.g., `i64` for Int, `bool` for
Bool), PraTTaIL automatically adds the corresponding literal token to the
category's FIRST set.

### 6.1 The Mapping

| Native Type | Token Added to FIRST Set | Token Variant |
|-------------|--------------------------|---------------|
| `i64` / `i32` | `Integer` | `Token::Integer(i64)` |
| `f64` / `f32` | `Float` | `Token::Float(f64)` |
| `bool` | `Boolean` | `Token::Boolean(bool)` |
| `String` | `StringLit` | `Token::StringLit(&str)` |

### 6.2 Disambiguation Effect

Native literal augmentation makes literal tokens **unique** to their category:

```
FIRST(Int)  contains Integer   (unique -- no other category has Integer)
FIRST(Bool) contains Boolean   (unique -- no other category has Boolean)
```

This enables deterministic dispatch: seeing `Integer` → immediately parse as
`Int` without trying other categories. See Layer 4
([04-cross-category-resolution.md](04-cross-category-resolution.md)) for how
this feeds into cross-category disambiguation.

---

## 7. Grammar Warnings

PraTTaIL detects potential disambiguation problems at compile time and emits
warnings (`prediction.rs`, lines 771-1013).

### 7.1 AmbiguousPrefix Warning

**Condition:** Multiple non-infix, non-variable, non-literal rules in the same
category start with the same terminal token.

```
warning: ambiguous prefix token "Ident" in category Proc
         (rules: POutput, PInput)
```

**Detection:** `detect_ambiguous_prefix()` (lines 861-900) builds a
`terminal → rule_labels` map and flags entries with 2+ rules.

**What to do:** Add a distinguishing first terminal, or restructure rules so
FIRST sets are disjoint. PraTTaIL will use lookahead as a workaround but warns
that the grammar may be confusing.

### 7.2 LeftRecursion Warning

**Condition:** A rule's first syntax item is a non-terminal of the **same**
category (direct left recursion).

```
warning: left recursion in rule Add of category Int
```

**Detection:** `detect_left_recursion()` (lines 903-948).

**Exceptions:** Infix, postfix, and mixfix rules are **exempt** because the
Pratt loop handles their left recursion iteratively via binding power comparison.
Only pure recursive-descent rules trigger this warning.

### 7.3 UnusedCategory Warning

**Condition:** A category is declared in the grammar's `types` section but never
referenced in any rule's syntax.

```
warning: unused category Str
```

**Detection:** `detect_unused_categories()` (lines 951-977) collects all
categories referenced in rule syntax items and flags any declared category not in
the reference set.

---

## 8. What Parse Prediction Cannot Resolve

Parse prediction handles **which rule to try** but leaves several disambiguation
classes to later layers:

- **Operator precedence:** Once a prefix rule is selected and its operand parsed,
  the infix loop must decide which operator binds tighter. This is Layer 3.

- **Cross-category ambiguity:** When `Ident` appears in FIRST sets of multiple
  categories, prediction identifies the overlap but does not resolve it. Layer 4
  handles the actual backtracking dispatch.

- **Error recovery:** When no rule matches (syntax error), prediction has no
  fallback. Layer 5 determines where to resynchronize.

---

## 9. Summary

```
  Token Stream → FIRST Sets → Dispatch Tables → Parse Decision
                 (fixed-point    (token → action    (O(1) or
                  iteration)      mapping)           O(1) with
                                                     1 peek)
```

| Mechanism | Ambiguity Resolved | Implementation |
|-----------|-------------------|----------------|
| FIRST sets | Which tokens can begin each rule | `compute_first_sets()`, fixed-point |
| Dispatch tables | Which rule to try for a given token | `build_dispatch_tables()` |
| 2-token lookahead | Multiple rules sharing first token | `LookaheadAlternative` |
| Variable fallback | Ident could be variable or structural | `default_action = Variable` |
| Native augmentation | Literal tokens unique to categories | `native_type` → token mapping |
| Grammar warnings | Compile-time ambiguity detection | `detect_grammar_warnings()` |

**Layer 2 output → Layer 3 input:** A selected parse rule and control flow
entering the Pratt prefix handler or recursive-descent function for that rule.
