# Layer 6: Semantic Disambiguation — Groundness-Based Resolution

Semantic disambiguation is the sixth and final layer in PraTTaIL's disambiguation
model. Unlike Layers 1-5, which resolve ambiguity **within** a single parse
invocation using syntactic information, Layer 6 resolves ambiguity **across**
multiple category parsers using semantic information: variable bindings and
structural groundness.

**Source files:**
- `macros/src/gen/term_ops/ground.rs` -- `is_ground()` method generation
- `macros/src/gen/runtime/language.rs` -- `Ambiguous` variant, `from_alternatives()`,
  `substitute_env()`, `run_ascent_typed()`, NFA-style multi-category parse

**Cross-references:**
- [04-cross-category-resolution.md](04-cross-category-resolution.md) -- Layer 4
  handles syntactic cross-category dispatch; Layer 6 handles the cases Layer 4 cannot
- [06-layer-interactions.md](06-layer-interactions.md) -- Layer interaction properties
  and end-to-end traces

---

## 1. The Semantic Ambiguity Problem

Layers 1-5 resolve syntactic ambiguity within a single parse invocation:
- Layer 1 resolves token boundaries (`==` vs `=` + `=`)
- Layer 2 selects which rule to try (`Integer` → cross-category, `Boolean` → direct)
- Layer 3 determines operator binding (`1+2*3` → `1+(2*3)`)
- Layer 4 resolves which category owns a token via operator peek + backtracking
- Layer 5 recovers from errors

But multi-category languages (e.g., a Calculator with `Int`, `Float`, `Bool`, `Str`)
face a different class of ambiguity: **the same input may parse validly under
multiple categories**. Consider:

```
Input: "a + b"

Category Int:   parse succeeds → IntAdd(IntVar("a"), IntVar("b"))
Category Float: parse succeeds → FloatAdd(FloatVar("a"), FloatVar("b"))
Category Bool:  parse fails    (no "+" operator for Bool)
Category Str:   parse succeeds → StrConcat(StrVar("a"), StrVar("b"))
```

All three successful parses are **structurally valid**. No syntactic layer can
distinguish them — the token sequences are identical, the operator precedence
is well-defined in each category, and there is no cross-category operator peek
that could differentiate them (unlike `==` which bridges `Int → Bool`).

Resolution requires **semantic information**: what are the variables `a` and `b`
bound to? If `a = 1.0` and `b = 2.0`, the Float parse is the correct
interpretation. If `a = 1` and `b = 2`, the Int parse wins.

---

## 2. NFA-Style Multi-Category Parsing

When a language has multiple type categories, the parser uses an NFA-style
strategy: try **all** category parsers on the input and collect successes.

**Source:** `macros/src/gen/runtime/language.rs` lines 1003-1049

```
parse_preserving_vars(input):
  successes = []
  first_err = None

  for each category in parse_order:
    match Cat::parse(input):
      Ok(term) → successes.push(TermInner::Cat(term))
      Err(e)   → if first_err is None: first_err = Some(e)

  match successes.len():
    0 → Err(first_err)
    1 → Ok(Term(successes[0]))         // unambiguous
    _ → Ok(Term(from_alternatives(successes)))  // may be Ambiguous
```

### 2.1 Parse Ordering

When both `Float` and `Int` exist, `Float` is tried before `Int` for
deterministic ordering (so the Float alternative appears first in any
`Ambiguous` variant). Other categories follow their declaration order.

**Source:** `macros/src/gen/runtime/language.rs` lines 1006-1037

```
Parse order (Calculator example):
  1. Float   (tried first when Float+Int coexist)
  2. Int
  3. Bool
  4. Str
```

### 2.2 Branching Diagram

```
              ┌─────────────────┐
              │  Input: "a + b" │
              └────────┬────────┘
                       │
        ┌──────────────┼──────────────┬──────────────┐
        ▼              ▼              ▼              ▼
  Float::parse    Int::parse    Bool::parse    Str::parse
  (Layers 1-5)   (Layers 1-5)  (Layers 1-5)  (Layers 1-5)
        │              │              │              │
        ▼              ▼              ▼              ▼
  Ok(FloatAdd(    Ok(IntAdd(      Err(no "+"    Ok(StrConcat(
   FVar,FVar))    IVar,IVar))    for Bool)      SVar,SVar))
        │              │                           │
        └──────────────┼───────────────────────────┘
                       ▼
              from_alternatives([
                Float(FloatAdd(...)),
                Int(IntAdd(...)),
                Str(StrConcat(...))
              ])
                       │
                       ▼
              Ambiguous([Float(...), Int(...), Str(...)])
```

---

## 3. The `Ambiguous` Variant

When multiple category parsers succeed, their results are collected into an
`Ambiguous` variant on the term's inner enum.

**Source:** `macros/src/gen/runtime/language.rs` lines 240-244

```rust
pub enum {Name}TermInner {
    Float(Float),
    Int(Int),
    Bool(Bool),
    Str(Str),
    /// Multiple parse alternatives (2+, flat -- no nested Ambiguous).
    Ambiguous(Vec<{Name}TermInner>),
}
```

### 3.1 Flat Invariant

The `Ambiguous` variant maintains a **flat invariant**: no nested `Ambiguous`
values. This is enforced by `from_alternatives()` which flattens on construction.

### 3.2 `from_alternatives()`

**Source:** `macros/src/gen/runtime/language.rs` lines 261-279

```
from_alternatives(alts):
  flat = alts.flat_map(|a| match a {
    Ambiguous(inner) → inner,   // flatten
    other → [other],
  })

  match flat.len():
    0 → panic("empty alternatives")
    1 → flat[0]                         // singleton unwrap
    _ →
      accepting = flat.filter(is_accepting)
      if accepting.len() == 1:
        return accepting[0]             // ground-filter: exactly one ground → wins
      Ambiguous(flat)                   // still ambiguous
```

The critical optimization is the **ground-filter**: if among N alternatives,
exactly one is a ground term (no free variables), it is selected immediately.
This resolves many ambiguities at parse time without needing substitution.

---

## 4. Ground-Term Checking: `is_ground()`

The `is_ground()` method determines whether a term is fully concrete — all leaf
positions are literals or nullary constructors, with no free variables at any
depth.

**Source:** `macros/src/gen/term_ops/ground.rs` lines 1-185

### 4.1 Per-Category Method Generation

`generate_is_ground_methods()` produces one `impl Cat { pub fn is_ground(&self) -> bool }` block per category. The generated match arms cover every variant:

| Variant Kind | Ground Check |
|-------------|--------------|
| **Var** | Always `false` (variables are not ground) |
| **Literal** | Always `true` (e.g., `NumLit(42)`) |
| **Nullary** | Always `true` (e.g., `BTrue`, `BFalse`) |
| **Regular** | `&&` over all fields (recursive) |
| **Collection** | `.iter().all(\|x\| x.is_ground())` with `(x, _count)` for HashBag |
| **Binder** | Pre-scope fields `&&` `scope.inner().unsafe_body.is_ground()` |

**Source:** `macros/src/gen/term_ops/ground.rs` lines 62-93

### 4.2 Collection Iteration Patterns

Different collection types have different iteration patterns:

**Source:** `macros/src/gen/term_ops/ground.rs` lines 98-107

```rust
// HashBag yields (&T, usize) tuples:
coll.iter().all(|(x, _count)| x.is_ground())

// Vec and HashSet yield &T:
coll.iter().all(|x| x.is_ground())
```

### 4.3 Binder Handling

Binder variants contain a `Scope` that binds variables. The body inside the
scope is checked via `scope.inner().unsafe_body.is_ground()`. Pre-scope fields
(if any) are checked before the scope body, and all checks are joined with `&&`.

**Source:** `macros/src/gen/term_ops/ground.rs` lines 155-184

### 4.4 Why Not `is_accepting()`?

The previous `is_accepting()` implementation had two problems:

1. **Wasteful**: For native types it called `try_eval()` which computes the full
   native value then discards it, only to be re-evaluated later during Ascent.
2. **Shallow**: For non-native types it only checked for bare variables at the
   top level, missing variables nested inside compound terms like
   `IntAdd(NumLit(1), IntVar("x"))`.

`is_ground()` fixes both: zero arithmetic, deep recursive traversal. The
`is_accepting()` method now simply delegates to `is_ground()`:

**Source:** `macros/src/gen/runtime/language.rs` lines 248-255

```rust
fn is_accepting(&self) -> bool {
    match self {
        TermInner::Float(inner) => inner.is_ground(),
        TermInner::Int(inner) => inner.is_ground(),
        TermInner::Bool(inner) => inner.is_ground(),
        TermInner::Str(inner) => inner.is_ground(),
        TermInner::Ambiguous(_) => false,
    }
}
```

---

## 5. Three-Stage Resolution Pipeline

Semantic disambiguation operates in three stages, each progressively more
expensive. Many ambiguities resolve early, avoiding the cost of later stages.

```
  ┌─────────────────────────────────────────────────────────────┐
  │  Stage A: PARSE-TIME (from_alternatives)                     │
  │  Ground-filter: exactly 1 ground alternative → select it     │
  │  Cost: O(alternatives) * O(is_ground per term)               │
  └──────────────────────────┬──────────────────────────────────┘
                             │ still Ambiguous?
  ┌──────────────────────────▼──────────────────────────────────┐
  │  Stage B: SUBSTITUTION-TIME (substitute_env)                 │
  │  Substitute each alternative, keep progressed, dedup,        │
  │  re-run from_alternatives                                    │
  │  Cost: O(alternatives) * O(substitution per term)            │
  └──────────────────────────┬──────────────────────────────────┘
                             │ still Ambiguous?
  ┌──────────────────────────▼──────────────────────────────────┐
  │  Stage C: EVALUATION-TIME (run_ascent_typed)                 │
  │  Run Ascent independently on each alternative, merge results │
  │  Cost: O(alternatives) * O(Ascent fixpoint per term)         │
  └──────────────────────────┬──────────────────────────────────┘
                             │
                        Resolved term(s)
```

### 5.1 Stage A: Parse-Time (`from_alternatives`)

**Source:** `macros/src/gen/runtime/language.rs` lines 261-279

After NFA-style parsing collects all successful category parses,
`from_alternatives()` applies the ground-filter:

- If exactly one alternative is ground, return it immediately.
- Otherwise, wrap in `Ambiguous`.

**Example — `"0.5"` (Float literal):**
```
Float::parse("0.5") → Ok(FloatLit(0.5))    ← ground (literal)
Int::parse("0.5")   → Err(...)             ← fails (0.5 not valid Int)

successes = [Float(FloatLit(0.5))]
len == 1 → unambiguous, no Ambiguous created
```

**Example — `"42"` (integer literal):**
```
Float::parse("42") → Ok(FloatLit(42.0))    ← ground
Int::parse("42")   → Ok(NumLit(42))        ← ground

successes = [Float(FloatLit(42.0)), Int(NumLit(42))]
from_alternatives: 2 ground alternatives → Ambiguous persists
```

**Example — `"a + b"` (variables, no env yet):**
```
Float::parse("a + b") → Ok(FloatAdd(FloatVar("a"), FloatVar("b")))  ← NOT ground
Int::parse("a + b")   → Ok(IntAdd(IntVar("a"), IntVar("b")))        ← NOT ground

successes = [Float(FloatAdd(...)), Int(IntAdd(...))]
from_alternatives: 0 ground alternatives → Ambiguous persists
```

### 5.2 Stage B: Substitution-Time (`substitute_env`)

**Source:** `macros/src/gen/runtime/language.rs` lines 281-340

When the REPL evaluates a term with an environment (variable bindings),
`substitute_env()` substitutes each `Ambiguous` alternative independently:

```
substitute_env(Ambiguous(alts), env):
  orig_displays = alts.map(Display)

  results = alts.map(|alt|
    substituted = alt.substitute_env(env)
    cross_resolved = try_cross_category_resolution(substituted, env)
    cross_resolved
  )

  result_displays = results.map(Display)

  // Keep only alternatives that made substitution progress
  progressed = indices where result_displays[i] != orig_displays[i]

  kept = if progressed.is_empty():
    results                    // none progressed → keep all
  else:
    results[progressed]        // only the ones that changed

  // Dedup by Display
  unique = dedup_by_display(kept)

  from_alternatives(unique)    // may resolve via groundness now
```

**Key insight:** Substitution can only **reduce** ambiguity. If a variable is
bound to a Float value, the Float path progresses (Display changes) while the
Int path does not (IntVar("a") stays as-is when `a` is not in the Int env).
The progress filter discards non-progressing alternatives.

**Cross-category variable resolution:** If after substitution an alternative
is still a bare variable (e.g., `IntVar("a")`), but the variable exists in
another category's environment (e.g., `float_env["a"] = 1.0`), the cross-category
resolution replaces it with the value from the other category.

**Source:** `macros/src/gen/runtime/language.rs` lines 146-180 (cross-resolve arms)

### 5.3 Stage C: Evaluation-Time (`run_ascent_typed`)

**Source:** `macros/src/gen/runtime/language.rs` lines 1148-1189

For still-`Ambiguous` terms that survive substitution (e.g., `"42"` which is
ground in both Float and Int), Ascent evaluation runs on each alternative
independently and merges results:

```
run_ascent_typed(Term(Ambiguous(alts))):
  all_term_infos = []
  all_rewrites = []
  all_custom = {}

  for alt in alts:
    sub_result = run_ascent_typed(Term(alt))
    all_term_infos.extend(sub_result.all_terms)
    all_rewrites.extend(sub_result.rewrites)
    merge(all_custom, sub_result.custom_relations)

  // Dedup term_infos by term_id
  seen_ids = {}
  all_term_infos.retain(|t| seen_ids.insert(t.term_id))

  AscentResults { all_term_infos, all_rewrites, ..., all_custom }
```

This is the fallback — it evaluates all alternatives and presents all results.
In practice, most ambiguities are resolved by Stage A or Stage B.

---

## 6. End-to-End Trace: `"a + b"` with env {a=1.0, b=2.0}

This trace follows the input through all six layers plus the three semantic
stages, showing how Float is selected as the correct interpretation.

### 6.1 Layers 1-5: Per-Category Parsing

Each category parser independently runs the syntactic layers:

```
Layer 1 (Lexical): "a + b" → [Ident("a"), Plus, Ident("b")]
                   (same token stream for all categories)

Float::parse:
  Layer 2 (Prediction): Ident → variable prefix handler
  Layer 3 (Precedence): FloatVar("a"), Plus binds (bp 2 ≥ 0), FloatVar("b")
  Result: FloatAdd(FloatVar("a"), FloatVar("b"))

Int::parse:
  Layer 2 (Prediction): Ident → variable prefix handler
  Layer 3 (Precedence): IntVar("a"), Plus binds (bp 2 ≥ 0), IntVar("b")
  Result: IntAdd(IntVar("a"), IntVar("b"))

Bool::parse:
  Layer 2 (Prediction): Ident → variable prefix handler
  Layer 3 (Precedence): BVar("a"), Plus is NOT a Bool operator → break
  After infix loop: only consumed 1 token, expected Eof → parse fails

Str::parse:
  Layer 2 (Prediction): Ident → variable prefix handler
  Layer 3 (Precedence): StrVar("a"), Plus binds (bp 2 ≥ 0), StrVar("b")
  Result: StrConcat(StrVar("a"), StrVar("b"))
```

### 6.2 Layer 6, Stage A: Parse-Time Ground-Filter

```
successes = [
  Float(FloatAdd(FloatVar("a"), FloatVar("b"))),   ← NOT ground (has vars)
  Int(IntAdd(IntVar("a"), IntVar("b"))),            ← NOT ground (has vars)
  Str(StrConcat(StrVar("a"), StrVar("b"))),         ← NOT ground (has vars)
]

from_alternatives: 0 ground → Ambiguous([Float(...), Int(...), Str(...)])
```

### 6.3 Layer 6, Stage B: Substitution

Environment: `float_env = {"a": 1.0, "b": 2.0}` (Float bindings only).

```
Ambiguous alternatives before substitution:
  [0] Float(FloatAdd(FloatVar("a"), FloatVar("b")))  Display: "a + b"
  [1] Int(IntAdd(IntVar("a"), IntVar("b")))           Display: "a + b"
  [2] Str(StrConcat(StrVar("a"), StrVar("b")))        Display: "a + b"

After substitute_env + cross-category resolution:
  [0] Float(FloatAdd(FloatLit(1.0), FloatLit(2.0)))  Display: "1.0 + 2.0"  ← PROGRESSED
  [1] Int(IntAdd(IntVar("a"), IntVar("b")))           Display: "a + b"      ← no change
  [2] Str(StrConcat(StrVar("a"), StrVar("b")))        Display: "a + b"      ← no change

Progress filter: only [0] progressed → kept = [Float(FloatAdd(FloatLit(1.0), FloatLit(2.0)))]

from_alternatives: len == 1 → unwrap singleton → Float(FloatAdd(FloatLit(1.0), FloatLit(2.0)))
```

**Result:** Ambiguity fully resolved. Float wins because it was the only
category whose variables were bound in the environment.

### 6.4 Ascent Evaluation

```
run_ascent_typed(Float(FloatAdd(FloatLit(1.0), FloatLit(2.0)))):
  Not Ambiguous → seed Float relation, run Ascent
  Ascent rewrites: FloatAdd(FloatLit(1.0), FloatLit(2.0)) → FloatLit(3.0)
  Result: "3.0"
```

### 6.5 Complete Decision Summary

| # | Layer | Decision | Mechanism |
|---|-------|----------|-----------|
| 1 | 1 | `"a"` → `Ident("a")`, `"+"` → `Plus`, `"b"` → `Ident("b")` | Maximal munch |
| 2 | 2 | `Ident` → variable prefix handler (per category) | Dispatch table |
| 3 | 3 | `Plus` binds in Float, Int, Str; not in Bool | BP comparison |
| 4 | 6A | 3 non-ground alternatives → `Ambiguous` | Ground-filter (0 ground) |
| 5 | 6B | Float progressed (vars → lits), others did not | Substitution progress |
| 6 | 6B | Singleton after filter → Float wins | `from_alternatives` unwrap |
| 7 | Ascent | `FloatAdd(1.0, 2.0)` → `FloatLit(3.0)` | Rewrite rule |

---

## 7. End-to-End Trace: `"42"` (integer literal, no env)

This trace shows a case where semantic disambiguation cannot fully resolve at
parse time, requiring the Ascent fallback.

### 7.1 Layers 1-5: Per-Category Parsing

```
Layer 1 (Lexical): "42" → [Integer(42)]

Float::parse:
  Layer 2 (Prediction): Integer → native literal prefix handler
  Result: FloatLit(42.0)    ← Float treats Integer token as FloatLit

Int::parse:
  Layer 2 (Prediction): Integer → native literal prefix handler
  Result: NumLit(42)

Bool::parse:
  Layer 2 (Prediction): Integer not in FIRST(Bool) → parse fails

Str::parse:
  Layer 2 (Prediction): Integer not in FIRST(Str) → parse fails
```

### 7.2 Layer 6, Stage A: Parse-Time Ground-Filter

```
successes = [
  Float(FloatLit(42.0)),  ← ground (literal)
  Int(NumLit(42)),        ← ground (literal)
]

from_alternatives: 2 ground → neither wins → Ambiguous([Float(...), Int(...)])
```

Both alternatives are ground, so the ground-filter cannot disambiguate.

### 7.3 Layer 6, Stage B: Substitution (no-op)

With an empty environment, substitution changes nothing:

```
substitute_env(Ambiguous([Float(FloatLit(42.0)), Int(NumLit(42))]), empty_env):
  Neither alternative progresses → keep all
  Still Ambiguous([Float(FloatLit(42.0)), Int(NumLit(42))])
```

### 7.4 Layer 6, Stage C: Ascent Evaluation

```
run_ascent_typed(Ambiguous([Float(FloatLit(42.0)), Int(NumLit(42))])):
  Run Ascent on Float(FloatLit(42.0)):
    → term_infos: [{id: hash(Float(FloatLit(42.0))), display: "42.0", normal: true}]
  Run Ascent on Int(NumLit(42)):
    → term_infos: [{id: hash(Int(NumLit(42))), display: "42", normal: true}]

  Merge: dedup by term_id → both kept (different hashes)
  Result: both "42.0" and "42" are valid interpretations
```

### 7.5 Complete Decision Summary

| # | Layer | Decision | Mechanism |
|---|-------|----------|-----------|
| 1 | 1 | `"42"` → `Integer(42)` | Maximal munch |
| 2 | 2 | `Integer` → native literal in Float and Int | FIRST set (native type) |
| 3 | 6A | 2 ground alternatives → `Ambiguous` persists | Ground-filter (2 ground) |
| 4 | 6B | No env → no progress → `Ambiguous` persists | Substitution (no change) |
| 5 | 6C | Run Ascent on both, merge results | Ascent fallback |

---

## 8. Interaction with Syntactic Layers

Layer 6 sits **after** the syntactic pipeline (Layers 1-5) and consumes their
output. The relationship is complementary, not redundant.

### 8.1 Layer 1 (Lexical) → Layer 6

Layer 1 determines token identity through priority. When both Float and Int
exist, both have `Integer` as a native literal token. Layer 1 produces a single
`Integer(42)` token — it cannot resolve whether this is a Float or Int literal.
Layer 6 handles this ambiguity after both category parsers run.

### 8.2 Layer 2 (Prediction) → Layer 6

Layer 2's FIRST set analysis augments each category's FIRST set with native
literal tokens. This means both `Float` and `Int` dispatch tables include
`Integer` as a valid prefix token. Layer 2 cannot disambiguate when `Integer`
appears in multiple categories' FIRST sets. Layer 6 resolves this after
parallel parsing.

### 8.3 Layer 4 (Cross-Category) → Layer 6

Layer 4 handles syntactic cross-category dispatch: when parsing `Bool` and
encountering `Ident`, it tries `Int` first, peeks for `==`, and either
succeeds (single unambiguous path) or backtracks to `Bool`-own.

Layer 6 handles the **multi-parse-path** cases that Layer 4 cannot:
- Layer 4: "This `Ident` begins either an `Int` or a `Bool` expression —
  determine which one via operator peek"
- Layer 6: "This input parses validly as both `Float` and `Int` —
  determine which one via variable bindings and groundness"

### 8.4 When Each Layer Resolves

| Scenario | Resolving Layer | Example |
|----------|----------------|---------|
| Token boundary ambiguity | Layer 1 | `==` vs `=`+`=` |
| Single-category token | Layer 2 | `Boolean(true)` → Bool only |
| Operator precedence | Layer 3 | `1+2*3` → `1+(2*3)` |
| Cross-category with operator peek | Layer 4 | `x == y` → Int comparison in Bool |
| Multi-category with one ground | Layer 6A | `"0.5"` → Float only |
| Multi-category with env bindings | Layer 6B | `"a + b"` with `a=1.0` → Float |
| Multi-category, all ground, no env | Layer 6C | `"42"` → both Float and Int |

---

## 9. Design Properties

### 9.1 Completeness

Every multi-category ambiguity is eventually resolved:
- **Stage A** resolves when exactly one parse is ground (common for literals
  unique to one category like `0.5` for Float)
- **Stage B** resolves when variable bindings disambiguate (common in REPL
  sessions where an environment accumulates)
- **Stage C** is the universal fallback — it runs Ascent on all alternatives
  and merges results, ensuring no valid interpretation is lost

### 9.2 Monotonicity

Substitution can only **reduce** ambiguity, never increase it:
- Each substitution step replaces variables with values, potentially making
  a term ground (or at least changing its Display)
- The progress filter discards alternatives that did not change, so the
  set of alternatives can only shrink or stay the same
- `from_alternatives()` can only reduce to a singleton (never add alternatives)

### 9.3 Zero Arithmetic Overhead

The `is_ground()` check performs **no evaluation**. It is a pure structural
traversal:
- Var → false (constant time)
- Literal → true (constant time)
- Regular → recurse on fields (proportional to term depth)
- No `try_eval()`, no arithmetic, no hash computation

This is important because `is_ground()` runs on every alternative at every
stage. The previous `is_accepting()` implementation called `try_eval()` for
native types, performing redundant arithmetic that would be repeated during
Ascent evaluation.

### 9.4 Deep Checking

Unlike the old shallow `is_accepting()` which only checked the top-level
variant, `is_ground()` recursively traverses the entire term structure:

```
IntAdd(NumLit(1), IntVar("x"))
  ├── NumLit(1).is_ground() → true
  └── IntVar("x").is_ground() → false
  ∴ IntAdd(...).is_ground() → false

IntAdd(NumLit(1), NumLit(2))
  ├── NumLit(1).is_ground() → true
  └── NumLit(2).is_ground() → true
  ∴ IntAdd(...).is_ground() → true
```

The old implementation would have returned `true` for both (only checking if
the top-level constructor was non-variable), incorrectly accepting the first
term as ground when it contains a nested variable.

---

## 10. Key Source Files

| File | Lines | Purpose |
|------|-------|---------|
| `macros/src/gen/term_ops/ground.rs` | 1-185 | `is_ground()` method generation for all categories |
| `macros/src/gen/term_ops/ground.rs` | 31-59 | `generate_is_ground_methods()`: per-category impl blocks |
| `macros/src/gen/term_ops/ground.rs` | 62-93 | `generate_is_ground_arm()`: variant-specific ground checks |
| `macros/src/gen/term_ops/ground.rs` | 98-107 | `collection_all_ground()`: HashBag/Vec/HashSet iteration |
| `macros/src/gen/term_ops/ground.rs` | 155-184 | `generate_binder_arm()`: scope body checking |
| `macros/src/gen/runtime/language.rs` | 240-244 | `Ambiguous` variant definition |
| `macros/src/gen/runtime/language.rs` | 248-255 | `is_accepting()` delegation to `is_ground()` |
| `macros/src/gen/runtime/language.rs` | 261-279 | `from_alternatives()`: flatten, singleton, ground-filter |
| `macros/src/gen/runtime/language.rs` | 281-340 | `substitute_env()` for Ambiguous terms |
| `macros/src/gen/runtime/language.rs` | 1003-1049 | NFA-style multi-category parse |
| `macros/src/gen/runtime/language.rs` | 1006-1037 | Parse ordering (Float before Int) |
| `macros/src/gen/runtime/language.rs` | 1148-1189 | `run_ascent_typed()` for Ambiguous terms |
