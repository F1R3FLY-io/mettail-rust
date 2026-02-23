# Layer Interactions: How the Six Layers Compose

This is the keystone document of the disambiguation series. It shows how
PraTTaIL's six disambiguation layers interact through end-to-end traces of real
input, explains why the layers are ordered as they are, and provides a master
flowchart for disambiguation decisions.

**Prerequisites:** This document references all six layer documents:
- [01-lexical-disambiguation.md](01-lexical-disambiguation.md)
- [02-parse-prediction.md](02-parse-prediction.md)
- [03-operator-precedence.md](03-operator-precedence.md)
- [04-cross-category-resolution.md](04-cross-category-resolution.md)
- [05-error-recovery.md](05-error-recovery.md)
- [07-semantic-disambiguation.md](07-semantic-disambiguation.md)

---

## 1. The Layered Architecture

The six layers form a pipeline where each layer's output constrains the next
layer's choices:

```
  ┌───────────────────────────────────────────────────────────────────────┐
  │                         SOURCE TEXT                                   │
  │  "b && (x == y)"                                                      │
  └──────────────────────────────┬────────────────────────────────────────┘
                                 │
  ┌──────────────────────────────▼────────────────────────────────────────┐
  │  LAYER 1: LEXICAL DISAMBIGUATION                                      │
  │  DFA + maximal munch + priority                                       │
  │  Resolves: token boundaries, keyword/ident, operator boundaries       │
  │                                                                       │
  │  "b"    → Ident("b")                                                  │
  │  "&&"   → AmpAmp         (maximal munch: && not & + &)                │
  │  "("    → LParen                                                      │
  │  "x"    → Ident("x")                                                  │
  │  "=="   → EqEq           (maximal munch: == not = + =)                │
  │  "y"    → Ident("y")                                                  │
  │  ")"    → RParen                                                      │
  └──────────────────────────────┬────────────────────────────────────────┘
                                 │
  ┌──────────────────────────────▼────────────────────────────────────────┐
  │  TOKEN STREAM                                                         │
  │  [Ident("b"), AmpAmp, LParen, Ident("x"), EqEq, Ident("y"), RParen]   │
  └──────────────────────────────┬────────────────────────────────────────┘
                                 │
  ┌──────────────────────────────▼────────────────────────────────────────┐
  │  LAYER 2: PARSE PREDICTION                                            │
  │  FIRST sets + dispatch tables                                         │
  │  Resolves: which rule to try first                                    │
  │                                                                       │
  │  Goal: parse Bool. First token: Ident("b")                            │
  │  Dispatch: Ident is in FIRST(Int) ∩ FIRST(Bool) → AMBIGUOUS           │
  │  → Try cross-category first (Layer 4)                                 │
  └──────────────────────────────┬────────────────────────────────────────┘
                                 │
  ┌──────────────────────────────▼────────────────────────────────────────┐
  │  LAYER 4: CROSS-CATEGORY RESOLUTION                                   │
  │  FIRST set partition + save/restore                                   │
  │  Resolves: Ident("b") → Int var? Or Bool var?                         │
  │                                                                       │
  │  Save pos. parse_Int("b") → IVar("b"). Peek: AmpAmp ≠ EqEq.           │
  │  Cross-category FAILS. Restore pos. → parse_Bool_own                  │
  └──────────────────────────────┬────────────────────────────────────────┘
                                 │
  ┌──────────────────────────────▼────────────────────────────────────────┐
  │  LAYER 3: OPERATOR PRECEDENCE                                         │
  │  Binding power pairs + Pratt loop                                     │
  │  Resolves: "b" as Bool var, "&&" infix, "(x == y)" as right operand   │
  │                                                                       │
  │  PREFIX: Ident("b") → BVar("b")                                       │
  │  INFIX:  AmpAmp, left_bp=2, min_bp=0 → && binds                       │
  │  RHS:    parse_Bool(min_bp=3) → enters nested call (all layers)       │
  │                                                                       │
  │  NESTED: "(" triggers grouping → parse_Bool(min_bp=0) for interior    │
  │    → Layer 4: Ident("x") ambiguous → try Int → IVar("x")              │
  │    → Peek: EqEq ✓ → cross-category succeeds!                          │
  │    → parse_Int → IVar("y") → Bool::Eq(IVar("x"), IVar("y"))           │
  │  Close ")" → grouping complete                                        │
  │                                                                       │
  │  Result: BAnd(BVar("b"), Eq(IVar("x"), IVar("y")))                    │
  └──────────────────────────────┬────────────────────────────────────────┘
                                 │
  ┌──────────────────────────────▼────────────────────────────────────────┐
  │  LAYER 5: ERROR RECOVERY                                              │
  │  (Not activated -- parse succeeded)                                   │
  └──────────────────────────────┬────────────────────────────────────────┘
                                 │
  ┌──────────────────────────────▼────────────────────────────────────────┐
  │  AST: BAnd(BVar("b"), Eq(IVar("x"), IVar("y")))                       │
  └───────────────────────────────────────────────────────────────────────┘
```

---

## 2. End-to-End Trace: `"b && (x == y)"`

This trace follows every disambiguation decision through all active layers.

### 2.1 Layer 1: Character-by-Character Lexing

```
Characters: b   &  &  (  x     =  =  y     )
            ↓   ↓  ↓  ↓  ↓     ↓  ↓  ↓     ↓
DFA:        S0→S_id  S0→S_amp→S_ampamp  S0→S_eq→S_eqeq  ...

Decision 1: "b" — DFA reaches identifier accept, next char " " → dead state.
            Maximal munch: emit Ident("b").

Decision 2: "&&" — First "&" reaches S_amp (accept: Amp).
            Second "&" reaches S_ampamp (accept: AmpAmp).
            Next char " " → dead state.
            Maximal munch: backtrack to last accept = AmpAmp.
            Emit AmpAmp (not Amp + Amp).

Decision 3: "==" — Same pattern as "&&".
            First "=" → Eq (accept). Second "=" → EqEq (accept).
            Space → dead. Backtrack to EqEq.
            Emit EqEq (not Eq + Eq).

Decision 4: "x", "y" — Single-character identifiers. Emit Ident.

Decision 5: "(", ")" — Single-character delimiters. Emit LParen, RParen.
```

**Layer 1 output:** `[Ident("b"), AmpAmp, LParen, Ident("x"), EqEq, Ident("y"), RParen]`

### 2.2 Layer 2: Dispatch Table Lookup

Goal: parse `Bool` expression. Look at first token.

```
Token: Ident("b")

Dispatch table for Bool:
  Integer  → CrossCategory(source=Int)     [unique to Int]
  Ident    → Ambiguous(Int ∩ Bool)         [try cross-cat, fallback own-cat]
  Boolean  → Direct(BTrue/BFalse)          [unique to Bool]
  Bang     → Direct(BNot)                  [unique to Bool]

Decision 6: Ident is ambiguous → cross-category dispatch (Layer 4).
```

### 2.3 Layer 4: Cross-Category for `Ident("b")`

```
Save pos = 0 (pointing at Ident("b")).

Try: parse_Int(tokens, pos, 0)
  → PREFIX: Ident("b") → IVar("b"). pos now = 1.
  → INFIX LOOP: peek token = AmpAmp.
    AmpAmp is not an Int operator → break infix loop.
  → Return Ok(IVar("b")).

Peek: tokens[1] = AmpAmp.
Expected: EqEq (cross-category operator).
AmpAmp ≠ EqEq.

Decision 7: Cross-category FAILS. Restore pos = 0.
→ Call parse_Bool_own(tokens, pos, 0).
```

### 2.4 Layer 3: Pratt Loop for Bool

```
parse_Bool_own(tokens, pos=0, min_bp=0):

  PREFIX: Ident("b") → BVar("b"). pos = 1.

  INFIX LOOP iteration 1:
    Token: AmpAmp
    Decision 8: AmpAmp is a Bool infix operator.
    left_bp = 2, min_bp = 0.
    Is 2 < 0? NO → && binds.
    Consume AmpAmp. pos = 2.

    Recurse: parse_Bool(tokens, pos=2, min_bp=3)
```

### 2.5 Nested Parse: `(x == y)` — All Layers Again

The recursive call to `parse_Bool` at pos=2 sees `LParen`:

```
Layer 2 (nested): Token = LParen
  Dispatch: LParen → Grouping(open=LParen, close=RParen)

Decision 9: LParen triggers grouping handler.
  Consume LParen. pos = 3.
  Recurse: parse_Bool(tokens, pos=3, min_bp=0)
```

Now parsing the interior of the parentheses:

```
Layer 2 (nested²): Token = Ident("x")
  Dispatch: Ident is ambiguous → cross-category.

Layer 4 (nested²):
  Save pos = 3.
  Try: parse_Int(tokens, pos=3, 0) → IVar("x"). pos = 4.
  Peek: tokens[4] = EqEq.
  Expected: EqEq.
  EqEq == EqEq ✓

  Decision 10: Cross-category SUCCEEDS.
  Consume EqEq. pos = 5.
  parse_Int(tokens, pos=5, 0) → IVar("y"). pos = 6.
  Construct: Bool::Eq(IVar("x"), IVar("y")).

Back in grouping handler:
  Expect RParen at pos = 6. ✓ Consume. pos = 7.
  Return: Bool::Eq(IVar("x"), IVar("y")).

Back in Bool Pratt infix loop (from §2.4):
  rhs = Bool::Eq(IVar("x"), IVar("y"))
  lhs = BAnd(BVar("b"), Eq(IVar("x"), IVar("y")))

  INFIX LOOP iteration 2:
    pos = 7 (end of input / Eof).
    Decision 11: No more operators → break.

Return: BAnd(BVar("b"), Eq(IVar("x"), IVar("y")))
```

### 2.6 Decision Summary

| #   | Layer | Decision                              | Mechanism                                |
|-----|-------|---------------------------------------|------------------------------------------|
| 1   | 1     | `"b"` → `Ident("b")`                  | Maximal munch (1 char, space terminates) |
| 2   | 1     | `"&&"` → `AmpAmp` (not `Amp + Amp`)   | Maximal munch (2 > 1)                    |
| 3   | 1     | `"=="` → `EqEq` (not `Eq + Eq`)       | Maximal munch (2 > 1)                    |
| 4-5 | 1     | `"x"`, `"y"` → `Ident`                | Maximal munch (1 char)                   |
| 6   | 2     | `Ident` ambiguous → try cross-cat     | FIRST set overlap                        |
| 7   | 4     | Cross-cat fails (peek AmpAmp ≠ EqEq)  | Operator peek + restore                  |
| 8   | 3     | `&&` binds (`left_bp=2 ≥ min_bp=0`)   | BP comparison                            |
| 9   | 2     | `(` → grouping handler                | Dispatch table (Direct)                  |
| 10  | 4     | Cross-cat succeeds (peek EqEq = EqEq) | Operator peek                            |
| 11  | 3     | Eof → break infix loop                | No operator found                        |

---

## 3. Layer Ordering Matters

The layers are ordered for a reason. Reordering would break correctness.

### 3.1 Why Lexical Before Prediction

Prediction operates on **tokens**, not characters. It needs to know that `&&` is
a single `AmpAmp` token (not `Amp` followed by `Amp`) before it can look up the
dispatch table. Layer 1 must fully resolve token boundaries before Layer 2 can
operate.

### 3.2 Why Prediction Before Precedence

The Pratt loop needs to know which **prefix handler** to invoke. Without
dispatch tables (Layer 2), the Pratt parser would not know whether to parse
`42` as an `Int` literal, a `Bool` literal, or attempt a cross-category path.
Layer 2 selects the rule; Layer 3 handles operator precedence within that rule.

### 3.3 Why Cross-Category Before Error Recovery

Cross-category resolution (Layer 4) may consume tokens and then **backtrack**.
If error recovery were to activate during a cross-category attempt, it would
skip tokens that should be preserved for the fallback path. Layer 4's
backtracking must complete before Layer 5 considers error recovery.

### 3.4 Why Precedence and Cross-Category Interleave

Layers 3 and 4 do not strictly sequence -- they **interleave**:

```
  Layer 3: Pratt prefix handler
    ↓ (encounters cross-category token)
  Layer 4: Cross-category dispatch
    ↓ (calls source category Pratt parser)
  Layer 3: Source category Pratt loop
    ↓ (returns to Layer 4)
  Layer 4: Operator peek, construct cross-category node
    ↓ (returns to Layer 3)
  Layer 3: Continue target category infix loop
```

This interleaving is safe because each layer maintains its own state:
- Layer 3 tracks `min_bp` / `cur_bp` per invocation
- Layer 4 tracks `saved_pos` per cross-category attempt

---

## 4. End-to-End Trace: `"3 + x == y - 1 && true"`

This trace exercises all syntactic layers (1-5). The expected parse:
`BAnd(Eq(IAdd(NumLit(3), IVar("x")), ISub(IVar("y"), NumLit(1))), BTrue)`

### 4.1 Layer 1: Lexing

```
Characters:  3   +   x       =  =   y       -   1       &  &       t  r  u  e
             ↓   ↓   ↓       ↓  ↓   ↓       ↓   ↓       ↓  ↓       ↓  ↓  ↓  ↓

Decision L1a: "3" → Integer(3)              [digit, maximal munch]
Decision L1b: "+" → Plus                    [single char, no longer match]
Decision L1c: "x" → Ident("x")             [letter, maximal munch]
Decision L1d: "==" → EqEq                  [maximal munch: 2 > 1]
Decision L1e: "y" → Ident("y")             [letter, maximal munch]
Decision L1f: "-" → Minus                   [single char]
Decision L1g: "1" → Integer(1)              [digit]
Decision L1h: "&&" → AmpAmp                [maximal munch: 2 > 1]
Decision L1i: "true" → Boolean(true)        [maximal munch ties, priority: 10 > 1]
```

**Token stream:** `[Integer(3), Plus, Ident("x"), EqEq, Ident("y"), Minus, Integer(1), AmpAmp, Boolean(true)]`

Note decision L1i: `"true"` is matched by both the keyword pattern (Boolean,
priority 10) and the identifier pattern (Ident, priority 1). Maximal munch
produces a tie (both 4 chars), so **priority** breaks the tie: Boolean wins.

### 4.2 Layer 2: Initial Dispatch

Goal: parse `Bool`. First token: `Integer(3)`.

```
Decision L2a: Integer is in FIRST(Int) but NOT FIRST(Bool).
              → Unique to Int → deterministic cross-category dispatch.
              → parse_Int, then expect "==" for Eq rule.
```

No ambiguity -- `Integer` uniquely identifies the `Int` category.

### 4.3 Layer 3: Int Pratt Loop (left of `==`)

```
parse_Int(tokens, pos=0, min_bp=0):

  PREFIX: Integer(3) → NumLit(3). pos = 1.

  INFIX LOOP iteration 1:
    Token: Plus
    Decision L3a: Plus is an Int infix operator.
    left_bp = 2, min_bp = 0. Is 2 < 0? NO → + binds.
    Consume Plus. pos = 2.

    Recurse: parse_Int(tokens, pos=2, min_bp=3)
      PREFIX: Ident("x") → IVar("x"). pos = 3.
      INFIX LOOP: Token = EqEq.
        Decision L3b: EqEq is NOT an Int infix operator → break.
      Return: IVar("x").

    lhs = IAdd(NumLit(3), IVar("x")). pos = 3.

  INFIX LOOP iteration 2:
    Token: EqEq.
    Decision L3c: EqEq is NOT an Int infix operator → break.

  Return: IAdd(NumLit(3), IVar("x")).
```

**Key Layer 3 decision (L3b):** The `==` token does NOT appear in Int's BP table.
It is a cross-category operator (`Int == Int → Bool`), not an Int infix operator.
So the Int Pratt loop correctly stops at `==`, allowing Layer 4 to handle it.

### 4.4 Layer 4: Cross-Category `==` Bridge

Back in the `Bool` dispatch wrapper:

```
Int parse returned: IAdd(NumLit(3), IVar("x")).
Peek: EqEq ✓ (matches expected cross-category operator).

Decision L4a: Cross-category succeeds. Consume EqEq. pos = 4.

parse_Int(tokens, pos=4, min_bp=0) for right operand:
  PREFIX: Ident("y") → IVar("y"). pos = 5.
  INFIX LOOP:
    Token: Minus.
    Decision L3d: Minus is an Int infix operator.
    left_bp = 2, min_bp = 0. Is 2 < 0? NO → - binds.
    Consume Minus. pos = 6.

    Recurse: parse_Int(tokens, pos=6, min_bp=3)
      PREFIX: Integer(1) → NumLit(1). pos = 7.
      INFIX LOOP: Token = AmpAmp.
        Decision L3e: AmpAmp is NOT an Int operator → break.
      Return: NumLit(1).

    lhs = ISub(IVar("y"), NumLit(1)). pos = 7.

  INFIX LOOP:
    Token: AmpAmp.
    Decision L3f: AmpAmp is NOT an Int operator → break.

  Return: ISub(IVar("y"), NumLit(1)).

Construct: Bool::Eq(IAdd(NumLit(3), IVar("x")), ISub(IVar("y"), NumLit(1))).
```

### 4.5 Layer 3: Bool Pratt Loop (with `&&`)

```
Back in parse_Bool(min_bp=0):
  lhs = Eq(IAdd(NumLit(3), IVar("x")), ISub(IVar("y"), NumLit(1))). pos = 7.

  INFIX LOOP:
    Token: AmpAmp.
    Decision L3g: AmpAmp is a Bool infix operator.
    left_bp = 2, min_bp = 0. Is 2 < 0? NO → && binds.
    Consume AmpAmp. pos = 8.

    Recurse: parse_Bool(tokens, pos=8, min_bp=3)
      Layer 2: Boolean(true) → unique to Bool → Direct(BTrue).
      PREFIX: Boolean(true) → BTrue. pos = 9.
      INFIX LOOP: Eof → break.
      Return: BTrue.

    lhs = BAnd(Eq(...), BTrue). pos = 9.

  INFIX LOOP: Eof → break.

Return: BAnd(Eq(IAdd(NumLit(3), IVar("x")), ISub(IVar("y"), NumLit(1))), BTrue)
```

### 4.6 Complete Decision Table

| #   | Layer | Token(s)  | Decision                           | Mechanism            |
|-----|-------|-----------|------------------------------------|----------------------|
| L1a | 1     | `"3"`     | → `Integer(3)`                     | Maximal munch        |
| L1b | 1     | `"+"`     | → `Plus`                           | Single char          |
| L1c | 1     | `"x"`     | → `Ident("x")`                     | Maximal munch        |
| L1d | 1     | `"=="`    | → `EqEq` (not `Eq`+`Eq`)           | Maximal munch        |
| L1e | 1     | `"y"`     | → `Ident("y")`                     | Maximal munch        |
| L1f | 1     | `"-"`     | → `Minus`                          | Single char          |
| L1g | 1     | `"1"`     | → `Integer(1)`                     | Maximal munch        |
| L1h | 1     | `"&&"`    | → `AmpAmp` (not `Amp`+`Amp`)       | Maximal munch        |
| L1i | 1     | `"true"`  | → `Boolean(true)` (not `Ident`)    | Priority (10 > 1)    |
| L2a | 2     | `Integer` | → deterministic cross-cat dispatch | Unique to Int        |
| L3a | 3     | `Plus`    | → + binds (`2 ≥ 0`)                | BP comparison        |
| L3b | 3     | `EqEq`    | → not Int op → break               | Led chain (no match) |
| L3c | 3     | `EqEq`    | → not Int op → break               | Led chain (no match) |
| L4a | 4     | `EqEq`    | → cross-cat operator matches       | Operator peek        |
| L3d | 3     | `Minus`   | → - binds (`2 ≥ 0`)                | BP comparison        |
| L3e | 3     | `AmpAmp`  | → not Int op → break               | Led chain (no match) |
| L3f | 3     | `AmpAmp`  | → not Int op → break               | Led chain (no match) |
| L3g | 3     | `AmpAmp`  | → && binds (`2 ≥ 0`)               | BP comparison        |

---

## 5. When Layers Conflict: Resolution Rules

In normal operation, the layers do not conflict -- each layer handles a distinct
class of ambiguity. But understanding the resolution boundaries clarifies the
design.

### 5.1 Maximal Munch vs Priority (Layer 1 Internal)

**Rule:** Maximal munch applies first. Priority is a tiebreaker.

```
"trueish" → Ident("trueish")     Maximal munch: 7 > 4. Priority irrelevant.
"true "   → Boolean(true)         Same length 4. Priority: 10 > 1.
"true("   → Boolean(true)         Same length 4. Priority: 10 > 1.
```

They never truly conflict because they operate at different levels of
specificity.

### 5.2 FIRST Set Overlap vs Binding Power (Layers 2-3)

When multiple rules share a first token (Layer 2 overlap), Layer 2 uses
lookahead or variable fallback to select a rule. Once inside a rule, Layer 3's
BP comparison takes over. These are sequential: Layer 2 selects the rule, Layer 3
executes within it.

### 5.3 Backtracking vs Error Recovery (Layers 4-5)

Cross-category backtracking (Layer 4) and error recovery (Layer 5) both involve
skipping tokens, but they operate in different contexts:

```
Layer 4 backtracking:
  - Triggered by: cross-category operator peek failure
  - Scope: restores to exact saved position
  - Cost: bounded (one sub-expression + one peek)
  - Outcome: falls through to own-category parse

Layer 5 error recovery:
  - Triggered by: complete parse failure (no rule matched)
  - Scope: skips forward to sync point (potentially many tokens)
  - Cost: unbounded skip (up to Eof)
  - Outcome: error node in AST
```

Layer 4 always completes before Layer 5 activates. If Layer 4 backtracks and
own-category parse also fails, **then** Layer 5 takes over.

---

## 6. Complete Disambiguation Decision Flowchart

```
                            ┌─────────────┐
                            │  Characters │
                            └──────┬──────┘
                                   │
                    ┌──────────────▼──────────────┐
                    │  LAYER 1: Lexical           │
                    │  ┌───────────────────────┐  │
                    │  │ Run DFA on input      │  │
                    │  └───────────┬───────────┘  │
                    │              │              │
                    │  ┌───────────▼───────────┐  │
                    │  │ Dead state? Backtrack │  │
                    │  │ to last_accept        │  │
                    │  │ (MAXIMAL MUNCH)       │  │
                    │  └───────────┬───────────┘  │
                    │              │              │
                    │  ┌───────────▼───────────┐  │
                    │  │ Multiple accepts at   │  │
                    │  │ same length? Use      │  │
                    │  │ PRIORITY tiebreaker   │  │
                    │  └───────────┬───────────┘  │
                    │              │              │
                    │       Emit Token            │
                    └──────────────┊──────────────┘
                                   │
                    ┌──────────────▼──────────────┐
                    │  LAYER 2: Prediction        │
                    │  ┌──────────────────────┐   │
                    │  │ Look up dispatch     │   │
                    │  │ table for category   │   │
                    │  └──────────┬───────────┘   │
                    │             │               │
                    │    ┌────────┼─────────┐     │
                    │    ▼        ▼         ▼     │
                    │  Direct  Lookahead  Cross   │
                    │  match   (peek +1)  Cat.    │
                    │    │        │         │     │
                    │    ▼        ▼         │     │
                    │  Call    Dispatch     │     │
                    │  parse_fn to matched  │     │
                    │           rule or     │     │
                    │           variable    │     │
                    │           fallback    │     │
                    └──────────────┬────────┊─────┘
                                   │        │
                    ┌──────────────▼────┐   │
                    │ LAYER 3:          │   │
                    │ Precedence        │   │
                    │ ┌───────────┐     │   │
                    │ │ Pratt     │     │   │
                    │ │ prefix    │     │   │
                    │ │ handler   │     │   │
                    │ └─────┬─────┘     │   │
                    │       │           │   │
                    │ ┌─────▼─────┐     │   │
                    │ │ Infix     │     │   │
                    │ │ loop:     │     │   │ (bypass)
                    │ │ l_bp <    │     │   │
                    │ │ min_bp?   │     │   │
                    │ │           │     │   │
                    │ │ YES→break │     │   │
                    │ │ NO →bind  │     │   │
                    │ └─────┬─────┘     │   │
                    │       │           │   │
                    │  Expression       │   │
                    │  tree │           │   │
                    └───────┊───────────┘   │
                            │               │
                    ┌───────▼───────────────▼─────┐
                    │  LAYER 4: Cross-Category    │
                    │  ┌────────────────────────┐ │
                    │  │ Token unique to source?│ │
                    │  │ YES → deterministic    │ │
                    │  │ NO  → save/restore     │ │
                    │  └──────────┬─────────────┘ │
                    │             │               │
                    │  ┌──────────▼─────────────┐ │
                    │  │ Operator peek matches? │ │
                    │  │ YES → cross-cat node   │ │
                    │  │ NO  → restore, own-cat │ │
                    │  └──────────┬─────────────┘ │
                    └─────────────┊───────────────┘
                                  │
                    ┌─────────────▼───────────────┐
                    │  Parse succeeded?           │
                    │  YES → return AST node      │
                    │  NO  ↓                      │
                    └─────────────┬───────────────┘
                                  │
                    ┌─────────────▼───────────────┐
                    │  LAYER 5: Error Recovery    │
                    │  ┌────────────────────────┐ │
                    │  │ is_sync_Cat(token)?    │ │
                    │  │ YES → resume here      │ │
                    │  │ NO  → skip, try next   │ │
                    │  └──────────┬─────────────┘ │
                    │             │               │
                    │  Error node + resumed parse │
                    └─────────────┊───────────────┘
                                  │
                            ┌─────▼─────┐
                            │    AST    │
                            └───────────┘
```

---

## 7. Design Properties

### 7.1 Completeness

Every class of parsing ambiguity is handled by exactly one layer:

| Ambiguity                | Layer | Guarantee                                                                               |
|--------------------------|-------|-----------------------------------------------------------------------------------------|
| Token boundaries         | 1     | Maximal munch always produces longest valid token                                       |
| Token identity           | 1     | Priority always resolves same-length conflicts                                          |
| Rule selection           | 2     | Dispatch table covers all FIRST set tokens                                              |
| Operator precedence      | 3     | BP comparison is total ordering on operators                                            |
| Operator associativity   | 3     | BP pair asymmetry determines left/right                                                 |
| Category ownership       | 4     | Three-way partition + backtracking is exhaustive                                        |
| Error recovery           | 5     | Sync predicate guarantees eventual sync (at Eof worst case)                             |
| Multi-category ambiguity | 6     | Groundness + substitution + declaration-order evaluation resolves all multi-parse cases |

### 7.2 Composability

The layers compose without interference because each layer:
1. Consumes the previous layer's output format (characters → tokens → rules → expressions → typed nodes → disambiguated nodes)
2. Resolves a disjoint class of ambiguity
3. Preserves all information needed by subsequent layers

### 7.3 Performance Characteristics

| Layer             | Happy-Path Cost                  | Failure Cost                          |
|-------------------|----------------------------------|---------------------------------------|
| 1. Lexical        | O(n) in input length             | N/A (always succeeds for valid chars) |
| 2. Prediction     | O(1) per parse decision          | O(1) (dispatch lookup)                |
| 3. Precedence     | O(1) per operator                | O(1) (comparison always resolves)     |
| 4. Cross-Category | O(1) for unique tokens           | O(k) for ambiguous tokens             |
| 5. Error Recovery | O(0) (not activated)             | O(skip) tokens skipped                |
| 6. Semantic       | O(cats) * O(parse) for NFA-style | O(cats) * O(Ascent) for fallback      |

**Total:** O(n) for lexing + O(tokens) for parsing, with O(1) per syntactic
disambiguation decision. Layer 6 adds O(categories) overhead for multi-category
parsing, with most ambiguities resolved in O(is_ground) structural checks.
No exponential blowup from backtracking (Layer 4 is bounded).

### 7.4 Separation of Concerns

Each layer is implemented in separate source files with well-defined interfaces:

```
Layer 1: automata/     (mod.rs, nfa.rs, codegen.rs, partition.rs)
Layer 2: prediction.rs (FIRST sets, dispatch tables, warnings)
Layer 3: binding_power.rs, pratt.rs (BP assignment, Pratt loop)
Layer 4: dispatch.rs   (cross-category wrapper generation)
Layer 5: prediction.rs (FOLLOW sets, sync predicates)
```

Layer 6 (semantic disambiguation) was added as a new layer rather than modifying
existing layers, confirming this separation-of-concerns property. See
[07-semantic-disambiguation.md](07-semantic-disambiguation.md) for the full
design: NFA-style multi-category parsing, the `Ambiguous` variant, deep
`is_ground()` checking, and the three-stage resolution pipeline.

**Layer 1 → Layer 6 direct interaction (lexer probe):** In languages with
non-native categories (e.g. rhocalc's `Proc` and `Name`), Layer 6 now uses a
single-token **lexer probe** from Layer 1's `lex()` to pre-filter category
parsers before NFA-style multi-category parsing begins. If the first token is
`Token::Ident`, native-only categories (Float, Int, Bool, Str) are skipped
entirely, since identifiers cannot be native literals. This is a direct
Layer 1 → Layer 6 interaction not mediated by Layers 2-5: Layer 1's lexer
classifies the token, and Layer 6 uses that classification to prune the set
of category parsers to invoke. For all-native languages (e.g. Calculator),
no probe is emitted and all parsers run unconditionally. See
[07-semantic-disambiguation.md](07-semantic-disambiguation.md) §2.3 for details.

---

## 8. Comparison: All Layers on One Token

To illustrate how the same token passes through different layers in different
contexts, consider `Ident("x")`:

| Context                          | Layer   | Decision                                                                   |
|----------------------------------|---------|----------------------------------------------------------------------------|
| In source text `"x + 1"`         | Layer 1 | Maximal munch: `"x"` → `Ident("x")`                                        |
| Parsing `Bool`, first token      | Layer 2 | Ambiguous (in FIRST(Int) ∩ FIRST(Bool))                                    |
| Cross-category attempt           | Layer 4 | Save, parse as `IVar("x")`, peek for `==`                                  |
| Peek fails (next is `&&`)        | Layer 4 | Restore, fall through to `parse_Bool_own`                                  |
| In `parse_Bool_own` prefix       | Layer 3 | Dispatch to `BVar` (variable rule)                                         |
| After error in expression        | Layer 5 | `Ident` is NOT a sync token → skip past                                    |
| NFA-style multi-category parse   | Layer 6 | `Ident("x")` → both `IntVar("x")` and `FloatVar("x")` → `Ambiguous`        |
| With env `{x=1.0}`, substitution | Layer 6 | Float progresses (`FloatVar` → `FloatLit(1.0)`), Int does not → Float wins |

The same token `Ident("x")` is handled by up to five different layers depending
on the parsing context, and each layer resolves a different question about it.
