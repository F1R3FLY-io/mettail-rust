# Layer 6: Semantic Disambiguation — Groundness-Based Resolution

Semantic disambiguation is the sixth and final layer in PraTTaIL's disambiguation
model. Where Layers 1–5 resolve ambiguity **within** a single parse invocation
using syntactic information (token boundaries, dispatch tables, binding power,
operator peek, error recovery), Layer 6 resolves ambiguity **across** multiple
category parsers using **semantic** information: variable bindings and structural
groundness.

This document explains why Layer 6 exists, how it works, and how grammar
declaration order flows through the entire pipeline to guarantee deterministic
resolution. Each concept builds on the previous one, with concrete examples
preceding abstract rules.

**Source files:**
- `macros/src/gen/term_ops/ground.rs` — `is_ground()` method generation
- `macros/src/gen/runtime/language.rs` — `Ambiguous` variant, `from_alternatives()`,
  `substitute_env()`, `run_ascent_typed()`, NFA-style multi-category parse

**Cross-references:**
- [04-cross-category-resolution.md](04-cross-category-resolution.md) — Layer 4
  handles syntactic cross-category dispatch; Layer 6 handles cases Layer 4 cannot
- [06-layer-interactions.md](06-layer-interactions.md) — Layer interaction properties
  and end-to-end traces

---

## 1. The Semantic Ambiguity Problem

Consider a Calculator language with four type categories — `Int`, `Float`,
`Bool`, `Str` — and the input `"a + b"`. Each category parser independently
runs Layers 1–5 and produces:

```
Category Int:   parse succeeds → IntAdd(IntVar("a"), IntVar("b"))
Category Float: parse succeeds → FloatAdd(FloatVar("a"), FloatVar("b"))
Category Bool:  parse fails    (no "+" operator for Bool)
Category Str:   parse succeeds → StrConcat(StrVar("a"), StrVar("b"))
```

Three structurally valid parses. No syntactic layer can distinguish them: the
token sequences are identical, the operator precedence is well-defined in each
category, and no cross-category operator peek (Layer 4) differentiates them —
unlike `==`, which bridges `Int → Bool`, the `+` operator exists independently
in Int, Float, and Str with identical token structure.

Resolution requires **semantic information**: what are `a` and `b` bound to?
If `a = 1.0` and `b = 2.0`, the Float parse is the correct interpretation.
If `a = 1` and `b = 2`, the Int parse wins. And if no environment exists at all,
the language needs a deterministic fallback — which is where grammar declaration
order comes in.

The following sections build the machinery to handle all three scenarios:
unambiguous literals (§5.1), environment-driven resolution (§5.2), and
declaration-order fallback (§5.3), all anchored by the NFA-style multi-category
parse strategy (§2) and the `Ambiguous` data representation (§3).

---

## 2. Multi-Category Parsing

When a language has multiple type categories, the parser cannot know in advance
which category the user intends. Instead of guessing, it uses an **NFA-style
strategy**: try all category parsers on the input and collect every successful
parse. Resolution happens afterward, not during parsing.

Here is the overall flow (`macros/src/gen/runtime/language.rs`, lines 1003–1084):

```
parse_preserving_vars(input):
  // Lexer probe (only for languages with non-native categories)
  if has_non_native_categories:
    probe_tokens = lex(input)
    first_tok = probe_tokens[0]

  successes = []
  first_err = None

  for each category in parse_order:     // declaration order
    // Skip native categories when first token is Ident (§2.3)
    if has_non_native_categories AND category.is_native AND first_tok is Ident:
      continue
    match Cat::parse(input):
      Ok(term) → successes.push(TermInner::Cat(term))
      Err(e)   → if first_err is None: first_err = Some(e)

  match successes.len():
    0 → Err(first_err)
    1 → Ok(Term(successes[0]))                  // unambiguous
    _ → Ok(Term(from_alternatives(successes)))   // may be Ambiguous
```

Two details are critical: the order in which parsers run (§2.1), and the
optimization that avoids redundant parses (§2.3).

### 2.1 Parse Ordering

Parse order always follows **grammar declaration order**. The first-declared
category is tried first, and its alternative appears first in any `Ambiguous`
variant. This provides a deterministic, user-controlled priority: the category
the user declares first is the preferred interpretation when all else is equal.

The ordering is constructed directly from the grammar's `types` block
(`language.rs`, line 1006):

```rust
let parse_order: Vec<syn::Ident> = language.types.iter().map(|t| t.name.clone()).collect();
```

For Calculator, which declares `types { ![i32] as Int, ![f64] as Float,
![bool] as Bool, ![String] as Str }`, the parse order is:

```
1. Int     (declared first — preferred at Stage C)
2. Float
3. Bool
4. Str
```

This ordering is preserved at every subsequent step in the pipeline. §6
traces the full invariant chain from grammar source to final resolution.

### 2.2 Branching Diagrams

The following diagrams show how multi-category parsing branches for two
representative languages. Note that alternatives appear in declaration order
throughout.

**Calculator (all-native, no lexer probe):** All 4 parsers run unconditionally
in declaration order.

```
              ┌─────────────────┐
              │  Input: "a + b" │
              └────────┬────────┘
                       │
        ┌──────────────┼──────────────┬──────────────┐
        ▼              ▼              ▼              ▼
  Int::parse     Float::parse   Bool::parse    Str::parse
  (Layers 1-5)   (Layers 1-5)  (Layers 1-5)  (Layers 1-5)
        │              │              │              │
        ▼              ▼              ▼              ▼
  Ok(IntAdd(      Ok(FloatAdd(    Err(no "+"    Ok(StrConcat(
   IVar,IVar))    FVar,FVar))    for Bool)      SVar,SVar))
        │              │                           │
        └──────────────┼───────────────────────────┘
                       ▼
              from_alternatives([
                Int(IntAdd(...)),       ← declaration order
                Float(FloatAdd(...)),
                Str(StrConcat(...))
              ])
                       │
                       ▼
              Ambiguous([Int(...), Float(...), Str(...)])
```

**rhocalc (has non-native categories, lexer probe active):** `"p"` triggers the
lexer probe; `first_tok = Ident("p")` → native categories are skipped, leaving
only `Proc` and `Name`.

```
              ┌────────────────┐
              │  Input: "p"    │
              └───────┬────────┘
                      │
              ┌───────▼────────┐
              │ Lexer probe:   │
              │ first_tok =    │
              │ Ident("p")     │
              └───────┬────────┘
                      │
  ┌───────────┬───────┼───────┬───────────┬───────────┐
  ▼           ▼       ▼       ▼           ▼           ▼
Float       Int     Proc    Name        Bool        Str
SKIP        SKIP   ::parse  ::parse     SKIP        SKIP
(native+    (native (non-   (non-       (native+    (native+
 Ident)      +Ident) native) native)     Ident)      Ident)
                    │       │
                    ▼       ▼
              Ok(ProcVar  Ok(NameVar
               ("p"))      ("p"))
                    │       │
                    └───┬───┘
                        ▼
              from_alternatives([
                Proc(ProcVar("p")),
                Name(NameVar("p"))
              ])
                        │
                        ▼
              Ambiguous([Proc(...), Name(...)])
              (2-way, not 6-way)
```

### 2.3 Lexer-Guided Parse Filtering

The NFA strategy of trying all category parsers works correctly but can be
wasteful. In rhocalc (6 categories), a bare identifier like `"p"` would
succeed under *all* categories — each has an auto-generated variable fallback
(`Token::Ident → Cat::XVar`). The result is 6-way ambiguity that downstream
stages must untangle, even though the lexer already knows that `"p"` is
`Token::Ident`, not `Token::Float` or `Token::Integer`.

The **lexer probe** optimization eliminates this waste. Before trying category
parsers, it lexes the input once to classify the first token. If the first
token is an identifier, it skips all native-type categories (those with
`native_type.is_some()`) — an identifier is never a native literal, so the
native parsers would only succeed via their variable fallback, producing
alternatives that are always less informative than non-native parsers.

| First Token | Category Type | Action |
|-------------|---------------|--------|
| `Token::Ident` | Non-native (Proc, Name) | Try parser |
| `Token::Ident` | Native (Float, Int, Bool, Str) | **Skip** |
| Any other token | Any | Try parser |

Here is the effect on `"p"` in rhocalc:

*Without lexer probe:*
```
Float::parse("p") → Ok(FloatVar("p"))   ← succeeds via variable fallback
Int::parse("p")   → Ok(IntVar("p"))     ← succeeds via variable fallback
Proc::parse("p")  → Ok(ProcVar("p"))    ← succeeds
Name::parse("p")  → Ok(NameVar("p"))    ← succeeds
Bool::parse("p")  → Ok(BoolVar("p"))    ← succeeds via variable fallback
Str::parse("p")   → Ok(StrVar("p"))     ← succeeds via variable fallback

Result: 6-way Ambiguous([Float(...), Int(...), Proc(...), Name(...), Bool(...), Str(...)])
```

*With lexer probe:*
```
first_tok = Ident("p")

Float::parse → SKIPPED (native + Ident)
Int::parse   → SKIPPED (native + Ident)
Proc::parse("p")  → Ok(ProcVar("p"))    ← non-native: always tried
Name::parse("p")  → Ok(NameVar("p"))    ← non-native: always tried
Bool::parse  → SKIPPED (native + Ident)
Str::parse   → SKIPPED (native + Ident)

Result: 2-way Ambiguous([Proc(...), Name(...)])
```

**When it applies:** Only languages with at least one non-native category emit
the lexer probe. All-native languages (e.g., Calculator) skip it entirely —
all parsers run unconditionally (`language.rs`, lines 1039–1084).

**Cost:** One extra `lex()` call per `parse_preserving_vars` invocation
(microseconds), which is negligible compared to the avoided cost of running 4
redundant category parsers.

### 2.4 Primary-Category Type Inference

The `type` REPL command calls `infer_term_type()`. For `Ambiguous` terms, this
previously returned `"Ambiguous"`, which is unhelpful — the user typically
expects the **primary category** (the first type in the language definition,
e.g., `Proc` for rhocalc, `Int` for Calculator) as the default interpretation.

When the `Ambiguous` alternatives include the primary category,
`infer_term_type()` reports that category's type. Otherwise it falls back to
`"Ambiguous"` (`language.rs`, lines 1717–1725).

```
infer_term_type(Ambiguous(alts)):
  for alt in alts:
    if alt is PrimaryCategory(_):       // e.g. Proc for rhocalc, Int for Calculator
      return TermType::Base("Proc")     // primary category name
  return TermType::Base("Ambiguous")    // fallback if primary not present
```

---

## 3. The `Ambiguous` Variant

When multiple category parsers succeed, their results are collected into an
`Ambiguous` variant on the term's inner enum (`language.rs`, lines 240–244):

```rust
pub enum {Name}TermInner {
    Float(Float),
    Int(Int),
    Bool(Bool),
    Str(Str),
    /// Multiple parse alternatives (2+, flat — no nested Ambiguous).
    Ambiguous(Vec<{Name}TermInner>),
}
```

### 3.1 Flat Invariant

The `Ambiguous` variant maintains a **flat invariant**: no element of its `Vec`
is itself `Ambiguous`. This simplifies every downstream consumer — they need
only match on concrete category variants, never recurse into nested ambiguity.

### 3.2 `from_alternatives()`

The `from_alternatives()` constructor enforces the flat invariant and performs
an early ground-filter (`language.rs`, lines 261–279):

```
from_alternatives(alts):
  flat = alts.flat_map(|a| match a {
    Ambiguous(inner) → inner,   // flatten nested → preserves element order
    other → [other],
  }).collect()                  // Vec preserves insertion order

  match flat.len():
    0 → panic("empty alternatives")
    1 → flat[0]                          // singleton unwrap
    _ →
      accepting = flat.filter(is_accepting)
      if accepting.len() == 1:
        return accepting[0]              // ground-filter: exactly one ground → wins
      Ambiguous(flat)                    // still ambiguous
```

Two properties to note:

1. **Order preservation:** `flat_map` followed by `collect()` into a `Vec`
   preserves the order of the input elements. Alternatives that entered in
   declaration order emerge in declaration order. This is critical for Stage C
   resolution (§5.3) and is part of the broader declaration-order invariant
   (§6).

2. **Early resolution:** If exactly one alternative is a ground term (no free
   variables), it wins immediately — no `Ambiguous` wrapper is created. This
   resolves many literal-only inputs at parse time, before substitution or
   evaluation are ever attempted (see Stage A in §5.1).

---

## 4. Ground-Term Checking: `is_ground()`

Before examining the three-stage resolution pipeline, we need to understand the
predicate it relies on. A term is **ground** when it is fully concrete — every
leaf position is a literal or nullary constructor, with no free variables at any
depth. The `is_ground()` method performs this check as a pure structural
traversal: no arithmetic, no evaluation, no side effects.

### 4.1 How It Works

The check is recursive over the term structure:

| Variant Kind | Ground? | Reasoning |
|-------------|---------|-----------|
| **Var** (`IntVar`, `FloatVar`, ...) | Always `false` | Variables are not concrete |
| **Literal** (`NumLit(42)`, `FloatLit(0.5)`) | Always `true` | Literals are fully determined |
| **Nullary** (`BTrue`, `BFalse`) | Always `true` | No fields to check |
| **Regular** (`IntAdd(l, r)`) | `l.is_ground() && r.is_ground()` | Recurse on all fields |
| **Collection** (`Vec`, `HashBag`) | `.iter().all(\|x\| x.is_ground())` | All elements must be ground |
| **Binder** (scoped terms) | Pre-scope fields `&&` body `.is_ground()` | Recurse into scope body |

Two examples illustrate deep vs. shallow checking:

```
IntAdd(NumLit(1), IntVar("x"))
  ├── NumLit(1).is_ground() → true
  └── IntVar("x").is_ground() → false
  ∴ IntAdd(...).is_ground() → false    ← variable nested inside compound term

IntAdd(NumLit(1), NumLit(2))
  ├── NumLit(1).is_ground() → true
  └── NumLit(2).is_ground() → true
  ∴ IntAdd(...).is_ground() → true     ← fully concrete
```

### 4.2 Per-Category Method Generation

`generate_is_ground_methods()` produces one `impl Cat { pub fn is_ground(&self)
-> bool }` block per category, with match arms covering every variant
(`macros/src/gen/term_ops/ground.rs`, lines 31–93).

Collection types require different iteration patterns:

```rust
// HashBag yields (&T, usize) tuples:
coll.iter().all(|(x, _count)| x.is_ground())

// Vec and HashSet yield &T:
coll.iter().all(|x| x.is_ground())
```

Binder variants check pre-scope fields first, then recurse into the scope body
via `scope.inner().unsafe_body.is_ground()` (lines 155–184).

### 4.3 Replacing `is_accepting()`

The previous `is_accepting()` implementation had two problems: (1) for native
types, it called `try_eval()` which computed the full native value only to
discard it, duplicating work that Ascent would repeat later; (2) for non-native
types, it only checked whether the top-level constructor was a variable, missing
variables nested inside compound terms like `IntAdd(NumLit(1), IntVar("x"))`.

`is_ground()` fixes both: zero arithmetic and deep recursive traversal. The
`is_accepting()` method now simply delegates to `is_ground()`
(`language.rs`, lines 248–255):

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

## 5. The Three-Stage Resolution Pipeline

With the `Ambiguous` representation (§3) and the `is_ground()` predicate (§4)
in hand, we can now describe the three-stage pipeline that resolves semantic
ambiguity. Each stage is progressively more expensive, and many ambiguities
resolve early — a literal input never reaches Stage B, and an environment-bound
expression never reaches Stage C.

```
  ┌─────────────────────────────────────────────────────────────┐
  │  Stage A: PARSE-TIME (from_alternatives)                     │
  │  Ground-filter: exactly 1 ground alternative → select it     │
  │  Cost: O(alternatives) × O(is_ground per term)               │
  └──────────────────────────┬──────────────────────────────────┘
                             │ still Ambiguous?
  ┌──────────────────────────▼──────────────────────────────────┐
  │  Stage B: SUBSTITUTION-TIME (substitute_env)                 │
  │  Substitute each alternative, keep progressed, dedup,        │
  │  re-run from_alternatives                                    │
  │  Cost: O(alternatives) × O(substitution per term)            │
  └──────────────────────────┬──────────────────────────────────┘
                             │ still Ambiguous?
  ┌──────────────────────────▼──────────────────────────────────┐
  │  Stage C: EVALUATION-TIME (run_ascent_typed)                 │
  │  Declaration-order resolution: evaluate first alternative    │
  │  Cost: O(1) × O(Ascent fixpoint per term)                    │
  └──────────────────────────┬──────────────────────────────────┘
                             │
                        Resolved term
```

### 5.1 Stage A: Parse-Time Ground-Filter

After NFA-style parsing collects all successful parses, `from_alternatives()`
(§3.2) applies the ground-filter: if exactly one alternative is ground, return
it immediately; otherwise wrap in `Ambiguous`.

**Example — `"0.5"` (Float literal):**
```
Int::parse("0.5")   → Err(...)              ← fails (0.5 not valid Int)
Float::parse("0.5") → Ok(FloatLit(0.5))     ← ground (literal)

successes = [Float(FloatLit(0.5))]
len == 1 → unambiguous, no Ambiguous created
```

**Example — `"42"` (integer literal):**
```
Int::parse("42")    → Ok(NumLit(42))         ← ground (Token::Integer matches i32)
Float::parse("42")  → Err(...)              ← fails (Token::Integer not in FIRST(Float))

successes = [Int(NumLit(42))]
len == 1 → unambiguous, no Ambiguous created
```

Note: `f64` only accepts `Token::Float` (e.g., `42.0`), not `Token::Integer`
(`prattail/src/pratt.rs`, lines 476–481). FIRST set augmentation adds only
`Float` to Float's FIRST set, not `Integer` (`prattail/src/pipeline.rs`, lines
438–440). So `"42"` is inherently unambiguous — only Int succeeds.

**Example — `"a + b"` (variables, no env yet):**
```
Int::parse("a + b")   → Ok(IntAdd(IntVar("a"), IntVar("b")))        ← NOT ground
Float::parse("a + b") → Ok(FloatAdd(FloatVar("a"), FloatVar("b")))  ← NOT ground
Str::parse("a + b")   → Ok(StrConcat(StrVar("a"), StrVar("b")))     ← NOT ground

successes = [Int(IntAdd(...)), Float(FloatAdd(...)), Str(StrConcat(...))]
from_alternatives: 0 ground → Ambiguous([Int(...), Float(...), Str(...)])
```

All three contain variables, so none are ground. The ambiguity persists to
Stage B.

### 5.2 Stage B: Substitution-Time Progress Filter

When the REPL evaluates a term with an environment (variable bindings),
`substitute_env()` substitutes each `Ambiguous` alternative independently
(`language.rs`, lines 281–340):

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

**Key insight:** Substitution can only **reduce** ambiguity, never increase it.
If a variable is bound to a Float value, the Float path progresses (Display
changes from `"a + b"` to `"1.0 + 2.0"`) while the Int path does not
(`IntVar("a")` stays as-is when `a` is absent from the Int env). The progress
filter discards non-progressing alternatives, and the final `from_alternatives`
call may resolve to a singleton if exactly one survives.

**Cross-category variable resolution:** If after substitution an alternative
is still a bare variable (e.g., `IntVar("a")`), but the variable exists in
another category's environment (e.g., `float_env["a"] = 1.0`), the cross-
category resolution replaces it with the value from the other category
(`language.rs`, lines 146–180).

### 5.3 Stage C: Evaluation-Time Declaration-Order Resolution

For `Ambiguous` terms that survive both Stages A and B, Stage C uses
**declaration-order resolution**: evaluate only the first alternative
(`alts[0]`) and return its result (`language.rs`, lines 1163–1171):

```
run_ascent_typed(Term(Ambiguous(alts))):
  // Declaration-order resolution: evaluate only the first alternative.
  // alts[0] is the first-declared category (parse order = declaration order).
  run_ascent_typed(Term(alts[0]))
```

All alternatives that reach Stage C are structurally valid parses — they will
all produce normal forms when evaluated by Ascent. Since the alternatives are
ordered by grammar declaration order (§6 proves this invariant end-to-end),
`alts[0]` is the first-declared category that successfully parsed the input.
Evaluating only this alternative provides:

- **Deterministic resolution:** the same input always produces the same result
- **User-controlled priority:** the user determines which category "wins" by
  declaring it first in the grammar
- **Performance:** evaluates 1 alternative instead of N, reducing Stage C cost
  from `O(N) × O(Ascent fixpoint)` to `O(1) × O(Ascent fixpoint)`

This is consistent with `infer_term_type()` (§2.4), which already prefers the
primary category (first-declared) for `Ambiguous` terms.

In practice, most ambiguities are resolved by Stage A or Stage B before
Stage C is reached.

---

## 6. The Declaration-Order Invariant

Stage C (§5.3) relies on a critical claim: `alts[0]` is always the
first-declared category. This section proves that claim by tracing how grammar
declaration order flows through every transformation in the pipeline, from the
`types {}` block in the grammar source to the final `alts.first()` call.

### 6.1 The Invariant Chain

Every step uses order-preserving `Vec` operations — `iter().map().collect()`,
`flat_map().collect()`, `Vec::push`, ascending index filter. No `HashMap`,
`HashSet`, sorting, or shuffling ever touches the alternatives vector.

```
                    ┌─────────────────────────────────────┐
                    │  Grammar: types { Int, Float, ... } │
                    │  language.types = Vec in decl order  │
                    └──────────────┬──────────────────────┘
                                   │ .iter().map().collect()
                    ┌──────────────▼──────────────────────┐
                    │  parse_order = [Int, Float, Bool, …] │
                    └──────────────┬──────────────────────┘
                                   │ .map() → sequential code blocks
                    ┌──────────────▼──────────────────────┐
                    │  parse_preserving_vars:              │
                    │  successes.push() in parse_order     │
                    │  (Vec::push preserves insertion order)│
                    └──────────────┬──────────────────────┘
                                   │ from_alternatives(successes)
                    ┌──────────────▼──────────────────────┐
                    │  Stage A: from_alternatives          │
                    │  flat_map + collect → Vec in order   │
                    │  Ambiguous(flat) stores ordered Vec  │
                    └──────────────┬──────────────────────┘
                                   │ substitute_env(Ambiguous(alts))
                    ┌──────────────▼──────────────────────┐
                    │  Stage B: substitute_env             │
                    │  alts.iter().map() → results (order) │
                    │  (0..n).filter() → ascending indices │
                    │  results[i] → subset in orig order   │
                    │  dedup by Display → insertion order   │
                    └──────────────┬──────────────────────┘
                                   │ run_ascent_typed(Ambiguous(alts))
                    ┌──────────────▼──────────────────────┐
                    │  Stage C: run_ascent_typed           │
                    │  alts.first() = alts[0]              │
                    │  = first-declared surviving category │
                    └──────────────────────────────────────┘
```

### 6.2 Step-by-Step Verification

| Step | Code Location | Order Mechanism |
|------|---------------|-----------------|
| Grammar source | `types { ![i32] as Int, ![f64] as Float, ![bool] as Bool, ![String] as Str }` | Textual declaration order → `Vec` |
| `parse_order` | `language.rs`, line 1006 | `language.types.iter().map(\|t\| t.name.clone()).collect()` — `Vec` iteration preserves order |
| `parse_tries` | `language.rs`, lines 1020–1041 | `parse_order.iter().map()` — generates code blocks in declaration order |
| `successes` | Generated `parse_preserving_vars` | Sequential `successes.push()` in the order `parse_tries` are emitted — `Vec::push` preserves insertion order |
| Stage A | `from_alternatives`, line 261 | `flat_map` + `collect()` into `Vec` — processes elements left-to-right, collects in input order |
| Stage B | `substitute_env`, lines 309–316 | `(0..results.len()).filter()` produces ascending indices; `results[i].clone()` preserves relative order within the subset |
| Stage B dedup | `substitute_env`, lines 320–323 | `HashSet::insert` returns `false` for duplicates — first occurrence (by insertion order) is kept |
| Stage C | `run_ascent_typed`, line 1169 | `alts.first()` = `alts[0]` = first-declared surviving category |

### 6.3 The Invariant Statement

> **Declaration-Order Invariant:** At every stage of the disambiguation
> pipeline, the alternatives in an `Ambiguous` vector are ordered by grammar
> declaration order. The first element (`alts[0]`) is always the first-declared
> category that successfully parsed the input and survived all previous
> filtering stages.

This invariant holds because:
1. The source of order is the `types {}` block, stored as a `Vec`.
2. Every transformation uses order-preserving `Vec` patterns: `iter().map()`,
   `flat_map().collect()`, `Vec::push`, ascending index filter.
3. No `HashMap`, `HashSet` (for storage), sorting, or shuffling is applied to
   the alternatives vector itself. (The `HashSet` in Stage B dedup is used only
   for *filtering* — it tracks seen Display strings but does not reorder the
   output `Vec`.)

---

## 7. End-to-End Traces

This section presents three worked examples that exercise different resolution
paths. Each trace follows the input through all six layers plus the semantic
stages, with alternatives shown in declaration order throughout.

### 7.1 `"a + b"` with env `{a=1.0, b=2.0}` — Resolved by Stage B

This is the canonical example from §1: an expression with variables that
becomes unambiguous once the environment provides Float bindings.

**Layers 1–5 (per-category parsing):**

```
Layer 1 (Lexical): "a + b" → [Ident("a"), Plus, Ident("b")]
                   (same token stream for all categories)

Int::parse:
  Layer 2 (Prediction): Ident → variable prefix handler
  Layer 3 (Precedence): IntVar("a"), Plus binds (bp 2 ≥ 0), IntVar("b")
  Result: IntAdd(IntVar("a"), IntVar("b"))

Float::parse:
  Layer 2 (Prediction): Ident → variable prefix handler
  Layer 3 (Precedence): FloatVar("a"), Plus binds (bp 2 ≥ 0), FloatVar("b")
  Result: FloatAdd(FloatVar("a"), FloatVar("b"))

Bool::parse:
  Layer 2 (Prediction): Ident → variable prefix handler
  Layer 3 (Precedence): BVar("a"), Plus is NOT a Bool operator → break
  After infix loop: only consumed 1 token, expected Eof → parse fails

Str::parse:
  Layer 2 (Prediction): Ident → variable prefix handler
  Layer 3 (Precedence): StrVar("a"), Plus binds (bp 2 ≥ 0), StrVar("b")
  Result: StrConcat(StrVar("a"), StrVar("b"))
```

**Layer 6, Stage A (parse-time ground-filter):**

```
successes = [
  Int(IntAdd(IntVar("a"), IntVar("b"))),            ← NOT ground (has vars)
  Float(FloatAdd(FloatVar("a"), FloatVar("b"))),    ← NOT ground (has vars)
  Str(StrConcat(StrVar("a"), StrVar("b"))),         ← NOT ground (has vars)
]

from_alternatives: 0 ground → Ambiguous([Int(...), Float(...), Str(...)])
```

**Layer 6, Stage B (substitution with `float_env = {"a": 1.0, "b": 2.0}`):**

```
Ambiguous alternatives before substitution:
  [0] Int(IntAdd(IntVar("a"), IntVar("b")))           Display: "a + b"
  [1] Float(FloatAdd(FloatVar("a"), FloatVar("b")))   Display: "a + b"
  [2] Str(StrConcat(StrVar("a"), StrVar("b")))        Display: "a + b"

After substitute_env + cross-category resolution:
  [0] Int(IntAdd(IntVar("a"), IntVar("b")))           Display: "a + b"      ← no change
  [1] Float(FloatAdd(FloatLit(1.0), FloatLit(2.0)))   Display: "1.0 + 2.0"  ← PROGRESSED
  [2] Str(StrConcat(StrVar("a"), StrVar("b")))        Display: "a + b"      ← no change

Progress filter: only [1] progressed → kept = [Float(FloatAdd(FloatLit(1.0), FloatLit(2.0)))]

from_alternatives: len == 1 → unwrap singleton → Float(FloatAdd(FloatLit(1.0), FloatLit(2.0)))
```

**Ascent evaluation:**

```
run_ascent_typed(Float(FloatAdd(FloatLit(1.0), FloatLit(2.0)))):
  Not Ambiguous → seed Float relation, run Ascent
  Ascent rewrites: FloatAdd(FloatLit(1.0), FloatLit(2.0)) → FloatLit(3.0)
  Result: "3.0"
```

**Decision summary:**

| # | Layer | Decision | Mechanism |
|---|-------|----------|-----------|
| 1 | 1 | `"a"` → `Ident("a")`, `"+"` → `Plus`, `"b"` → `Ident("b")` | Maximal munch |
| 2 | 2 | `Ident` → variable prefix handler (per category) | Dispatch table |
| 3 | 3 | `Plus` binds in Int, Float, Str; not in Bool | BP comparison |
| 4 | 6A | 3 non-ground alternatives → `Ambiguous` | Ground-filter (0 ground) |
| 5 | 6B | Float progressed (vars → lits), Int and Str did not | Substitution progress |
| 6 | 6B | Singleton after filter → Float wins | `from_alternatives` unwrap |
| 7 | Ascent | `FloatAdd(1.0, 2.0)` → `FloatLit(3.0)` | Rewrite rule |

### 7.2 `"42"` — Resolved by Layer 2 (No Layer 6 Needed)

Integer literals are inherently unambiguous because each native type maps to a
distinct token type. This trace shows how Layer 2 (Prediction) resolves the
ambiguity before Layer 6 is ever reached.

**Layers 1–5 (per-category parsing):**

```
Layer 1 (Lexical): "42" → [Integer(42)]

Int::parse:
  Layer 2 (Prediction): Integer → native literal prefix handler (i32 accepts Token::Integer)
  Result: NumLit(42)

Float::parse:
  Layer 2 (Prediction): Integer not in FIRST(Float) → parse fails
  (f64 only accepts Token::Float, not Token::Integer)

Bool::parse:
  Layer 2 (Prediction): Integer not in FIRST(Bool) → parse fails

Str::parse:
  Layer 2 (Prediction): Integer not in FIRST(Str) → parse fails
```

**Layer 6: no disambiguation needed.**

```
successes = [Int(NumLit(42))]
len == 1 → unambiguous, no Ambiguous created
Result: Int(NumLit(42))
```

Because `f64` only accepts `Token::Float` (e.g., `42.0`) and `i32` only
accepts `Token::Integer`, there is no ambiguity between Float and Int for
bare integer literals. Layer 2's FIRST set analysis resolves this entirely:
`Token::Integer` is in `FIRST(Int)` but not `FIRST(Float)`.

**Ascent evaluation:**

```
run_ascent_typed(Int(NumLit(42))):
  Not Ambiguous → seed Int relation, run Ascent
  NumLit(42) is already a normal form
  Result: "42"
```

**Decision summary:**

| # | Layer | Decision | Mechanism |
|---|-------|----------|-----------|
| 1 | 1 | `"42"` → `Integer(42)` | Maximal munch |
| 2 | 2 | `Integer` → native literal in Int only | FIRST set (`i32` → `Token::Integer`; `f64` → `Token::Float` only) |
| 3 | — | 1 success → unambiguous (no Layer 6 needed) | Single-parse resolution |
| 4 | Ascent | `NumLit(42)` → `NumLit(42)` (already normal) | Identity rewrite |

### 7.3 `"a + b"` with No Environment — Resolved by Stage C

When no variable bindings exist, Stages A and B cannot resolve the ambiguity.
Stage C provides the deterministic fallback using declaration order.

```
Parse: Int(IntAdd(IVar, IVar)), Float(FloatAdd(FVar, FVar)), Str(StrConcat(SVar, SVar))
Stage A: 0 ground → Ambiguous([Int(...), Float(...), Str(...)])
Stage B: empty env → no progress → Ambiguous persists
Stage C: evaluate alts[0] = Int(IntAdd(IntVar("a"), IntVar("b")))
  → Ascent returns IntAdd result as normal form
  → Single deterministic result (Int, the first-declared category)
```

Declaration order ensures deterministic resolution: the user's first-declared
category (`Int` in Calculator) is always preferred at Stage C. This is not
arbitrary — the grammar declaration order is the user's explicit statement
of priority among otherwise-equivalent interpretations.

---

## 8. Interaction with Syntactic Layers

Layer 6 sits **after** the syntactic pipeline (Layers 1–5) and consumes their
output. The relationship is complementary, not redundant — each layer resolves
a different class of ambiguity.

### 8.1 Layer 1 (Lexical) → Layer 6

Layer 1 determines token identity through maximal munch and priority rules.
For numeric input, it produces distinct token types: `"42"` becomes
`Token::Integer(42)`, while `"42.0"` becomes `Token::Float(42.0)`. These
distinct token types feed into Layer 2's FIRST set analysis, which maps each
token type to exactly one category's FIRST set. So for numeric literals, the
ambiguity is resolved at Layer 1+2, not Layer 6.

Layer 6 handles the cases where Layer 1 produces tokens that appear in
*multiple* categories' FIRST sets — most commonly `Token::Ident`, which every
category accepts through its variable fallback.

### 8.2 Layer 2 (Prediction) → Layer 6

Layer 2's FIRST set analysis augments each category's FIRST set with the native
literal token that matches its `native_type`. This augmentation is **selective**
(`prattail/src/pipeline.rs`, lines 434–451):

- `i32` / `i64` / `u32` / `u64` / `isize` / `usize` → adds `Token::Integer` to FIRST set
- `f32` / `f64` → adds `Token::Float` to FIRST set
- `bool` → adds `Token::Boolean` to FIRST set
- `str` / `String` → adds `Token::StringLit` to FIRST set

Each native type maps to a **different** token type. This means Int's FIRST set
includes `Integer` but not `Float`, and Float's FIRST set includes `Float` but
not `Integer`. Layer 2 can therefore resolve literal ambiguity entirely through
dispatch tables — `Token::Integer` dispatches to Int only, `Token::Float`
dispatches to Float only.

Layer 6 handles cases that survive Layer 2: variable expressions where
`Token::Ident` appears in all categories' FIRST sets, making Layer 2's dispatch
tables unable to select a single category.

### 8.3 Layer 4 (Cross-Category) → Layer 6

Layer 4 handles syntactic cross-category dispatch: when parsing `Bool` and
encountering `Ident`, it tries `Int` first, peeks for `==`, and either
succeeds (single unambiguous path) or backtracks to `Bool`-own.

Layer 6 handles the **multi-parse-path** cases that Layer 4 cannot:
- Layer 4: "This `Ident` begins either an `Int` or a `Bool` expression —
  determine which one via operator peek"
- Layer 6: "This input parses validly as both `Int` and `Float` —
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
| Multi-category, no env | Layer 6C | `"a + b"` (no env) → first-declared wins |

---

## 9. Design Properties

### 9.1 Completeness

Every multi-category ambiguity is eventually resolved:
- **Stage A** resolves when exactly one parse is ground (common for literals
  unique to one category, like `0.5` for Float)
- **Stage B** resolves when variable bindings disambiguate (common in REPL
  sessions where an environment accumulates)
- **Stage C** is the deterministic fallback — it evaluates the first-declared
  alternative, providing a consistent, user-controlled resolution

### 9.2 Monotonicity

Substitution can only **reduce** ambiguity, never increase it:
- Each substitution step replaces variables with values, potentially making
  a term ground (or at least changing its Display)
- The progress filter discards alternatives that did not change, so the
  set of alternatives can only shrink or stay the same
- `from_alternatives()` can only reduce to a singleton (never add alternatives)

### 9.3 Zero Arithmetic Overhead

The `is_ground()` check performs no evaluation — it is a pure structural
traversal: Var → false (constant time), Literal → true (constant time),
Regular → recurse on fields (proportional to term depth). No `try_eval()`,
no arithmetic, no hash computation.

This matters because `is_ground()` runs on every alternative at every stage.
The previous `is_accepting()` implementation called `try_eval()` for native
types, performing redundant arithmetic that Ascent evaluation would repeat.

### 9.4 Deep Checking

Unlike the old shallow `is_accepting()` which only checked the top-level
variant, `is_ground()` recursively traverses the entire term structure. See §4.1
for examples showing how nested variables like `IntAdd(NumLit(1), IntVar("x"))`
are correctly identified as non-ground.

### 9.5 Determinism

Declaration order provides a **total ordering** on alternatives. When multiple
categories successfully parse the same input, the alternatives in the
`Ambiguous` vector are ordered by the user's grammar declaration order
(first-declared category = `alts[0]`). §6 proves this invariant holds through
every transformation in the pipeline.

Stage C evaluates only `alts[0]`, ensuring:
- **Deterministic resolution**: the same input always produces the same result
  regardless of evaluation order or timing
- **User-controlled priority**: the user determines which category "wins" by
  declaring it first in the grammar
- **Consistency with type inference**: `infer_term_type()` (§2.4) already
  prefers the primary category (first-declared) for `Ambiguous` terms

**Performance benefit:** Stage C cost drops from `O(N) × O(Ascent fixpoint)`
to `O(1) × O(Ascent fixpoint)`, where N is the number of surviving
alternatives (typically 2–4).

---

## 10. Key Source Files

| File | Lines | Purpose |
|------|-------|---------|
| `macros/src/gen/term_ops/ground.rs` | 1–185 | `is_ground()` method generation for all categories |
| `macros/src/gen/term_ops/ground.rs` | 31–59 | `generate_is_ground_methods()`: per-category impl blocks |
| `macros/src/gen/term_ops/ground.rs` | 62–93 | `generate_is_ground_arm()`: variant-specific ground checks |
| `macros/src/gen/term_ops/ground.rs` | 98–107 | `collection_all_ground()`: HashBag/Vec/HashSet iteration |
| `macros/src/gen/term_ops/ground.rs` | 155–184 | `generate_binder_arm()`: scope body checking |
| `macros/src/gen/runtime/language.rs` | 240–244 | `Ambiguous` variant definition |
| `macros/src/gen/runtime/language.rs` | 248–255 | `is_accepting()` delegation to `is_ground()` |
| `macros/src/gen/runtime/language.rs` | 261–279 | `from_alternatives()`: flatten, singleton, ground-filter |
| `macros/src/gen/runtime/language.rs` | 281–340 | `substitute_env()` for Ambiguous terms |
| `macros/src/gen/runtime/language.rs` | 1003–1052 | NFA-style multi-category parse with lexer-guided filtering |
| `macros/src/gen/runtime/language.rs` | 1006 | Parse ordering (declaration order) |
| `macros/src/gen/runtime/language.rs` | 1039–1084 | Lexer probe + native-category guards |
| `macros/src/gen/runtime/language.rs` | 1155–1170 | `run_ascent_typed()` declaration-order resolution |
| `macros/src/gen/runtime/language.rs` | 1717–1725 | Primary-category type inference for Ambiguous terms |
