# Parser Generation

**Source files:** `prattail/src/pipeline.rs`, `prattail/src/prediction.rs`,
`prattail/src/binding_power.rs`, `prattail/src/classify.rs`,
`prattail/src/trampoline.rs`, `prattail/src/pratt.rs`,
`prattail/src/recursive.rs`, `prattail/src/dispatch.rs`

PraTTaIL generates a **trampolined Pratt + recursive descent parser** — a
hybrid that uses Pratt binding powers for precedence-sensitive infix/prefix/postfix
parsing and recursive descent for structured patterns (binders, collections,
ZipMapSep).

## Pipeline Stages

The parser generation pipeline runs inside `pipeline::run_pipeline()`:

```
  LanguageSpec
       │
       ▼
  ┌──────────┐    Extract data bundles (LexerBundle + ParserBundle)
  │ Extract  │    from &LanguageSpec (main thread, LanguageSpec is !Send)
  └────┬─────┘
       │
       ▼
  ┌──────────┐    FIRST/FOLLOW sets, binding powers, dispatch tables
  │ Generate │    lexer code + parser code (sequential)
  └────┬─────┘
       │
       ▼
  ┌──────────┐    Concatenate code strings → parse into TokenStream
  │ Finalize │
  └────┬─────┘
       │
       ▼
   TokenStream
```

## FIRST and FOLLOW Sets

**Source:** `prattail/src/prediction.rs`

### FIRST Sets

FIRST(Cat) is the set of tokens that can begin a parse of category Cat.

For RhoCalc:

| Category | FIRST set                                                                                                                                            |
|----------|------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Proc`   | `{`, `{}`, `*`, `(`, `@`, `Integer`, `Float`, `Boolean`, `StringLit`, `not`, `concat`, `len`, `int`, `float`, `bool`, `str`, `new`, `error`, `Ident` |
| `Name`   | `@`, `Ident`                                                                                                                                         |
| `Int`    | `Integer`                                                                                                                                            |
| `Float`  | `Float` (literal float)                                                                                                                              |
| `Bool`   | `Boolean`                                                                                                                                            |
| `Str`    | `StringLit`                                                                                                                                          |

Proc's FIRST set includes tokens from:
- Its own prefix rules: `{}` (PZero), `*` (PDrop), `(` (PInputs/POutput), `not` (Not), etc.
- Cast rules: `Integer` (CastInt), `Float` (CastFloat), etc.
- Cross-category casts from Name: `@` (NQuote → Proc via cast path)

FIRST sets are computed iteratively (dirty-flag convergence): the computation
repeats until no set changes.  Cast rules contribute FIRST(source_category)
into FIRST(target_category).

### FOLLOW Sets

FOLLOW(Cat) is the set of tokens that can appear after a complete parse of Cat.

```
FOLLOW(Proc) = { ")", "}", "|", ",", "+", "-", "*", "/", "==", "!=",
                 ">", "<", ">=", "<=", "and", "or", Eof, ... }
FOLLOW(Name) = { "!", "?", ",", ")", ... }
```

FOLLOW sets are used for:
1. **Error recovery** — sync predicates: when the parser encounters an error,
   skip tokens until a FOLLOW set member (or structural delimiter) is found
2. **Lookahead disambiguation** — when multiple prefix handlers match, FOLLOW
   helps determine which one to try first

### Sync Predicates

`generate_sync_predicate()` produces a function `is_sync_token_Cat(tok)` that
returns true for tokens in FOLLOW(Cat) ∪ structural_delimiters that appear in
the grammar's terminal set.  This is used by the recovering parser to find
resynchronization points after errors.

## Rule Classification

**Source:** `prattail/src/classify.rs`

Every rule is classified when `LanguageSpec::with_options()` constructs the
spec.  Here is how key RhoCalc rules are classified:

| Rule      | Pattern                                                                                         | Classification                            |
|-----------|-------------------------------------------------------------------------------------------------|-------------------------------------------|
| `PZero`   | `Terminal("{}")`                                                                                | literal (prefix)                          |
| `PDrop`   | `Terminal("*") Terminal("(") NT(Name) Terminal(")")`                                            | prefix                                    |
| `PPar`    | `Terminal("{") Collection(Proc,"\|") Terminal("}")`                                             | prefix, collection                        |
| `POutput` | `NT(Name) Terminal("!") Terminal("(") NT(Proc) Terminal(")")`                                   | cross-category (Name in Proc)             |
| `PInputs` | `Terminal("(") ZipMapSep(...) Terminal(")") Terminal(".") Terminal("{") NT(Proc) Terminal("}")` | prefix, multi-binder                      |
| `NQuote`  | `Terminal("@") Terminal("(") NT(Proc) Terminal(")")`                                            | prefix (in Name category), cross-category |
| `Add`     | `NT(Proc) Terminal("+") NT(Proc)`                                                               | infix                                     |
| `Not`     | `Terminal("not") NT(Proc)`                                                                      | unary prefix                              |
| `CastInt` | `NT(Int)`                                                                                       | cast (Int → Proc)                         |
| `Err`     | `Terminal("error")`                                                                             | literal (prefix)                          |

## Binding Power Analysis

**Source:** `prattail/src/binding_power.rs`

`analyze_binding_powers()` examines all infix rules in a category and assigns
binding power pairs `(left_bp, right_bp)`:

For RhoCalc `Proc` category:

| Operator          | left_bp | right_bp | Associativity | Notes                          |
|-------------------|---------|----------|---------------|--------------------------------|
| `or`              | 2       | 3        | Left          | lowest precedence              |
| `and`             | 4       | 5        | Left          |                                |
| `==` `!=`         | 6       | 7        | Left          | comparison                     |
| `>` `<` `>=` `<=` | 8       | 9        | Left          | relational                     |
| `+` `-`           | 10      | 11       | Left          | additive                       |
| `*` `/`           | 12      | 13       | Left          | multiplicative                 |
| `not`             | —       | 15       | Prefix        | `prefix_bp = max_infix_bp + 2` |

(Exact BP values depend on rule declaration order within a precedence group;
operators declared earlier get lower BP.  The table above illustrates the
relative ordering.)

**BP hierarchy**: infix < unary prefix < postfix.  This ensures `not 3 + 4`
parses as `(not 3) + 4` and (hypothetically) `a!` would bind tighter than `not`.

Left-associative operators use `(bp, bp+1)`:

```
3 + 4 + 5
─── left_bp=10, right_bp=11 ───
Pratt loop: parse 3, see +, left_bp=10 ≥ min_bp=0 → enter infix
  parse RHS with min_bp=11: parse 4, see +, left_bp=10 < min_bp=11 → stop
  result: Add(3, 4)
see +, left_bp=10 ≥ min_bp=0 → enter infix
  parse RHS: parse 5, see Eof → stop
  result: Add(Add(3, 4), 5)
```

Result: `Add(Add(CastInt(3), CastInt(4)), CastInt(5))` — left-associated.

## Trampolined Parser Codegen

**Source:** `prattail/src/trampoline.rs` (~2,027 lines)

The parser uses a *trampoline* architecture: instead of recursive function calls,
it maintains an explicit `Vec<Frame_Cat>` continuation stack.  This makes the
parser stack-safe (limited only by heap memory, not call stack depth).

### Frame Enum

For each category, a `Frame_Cat` enum is generated with variants for every
recursion point:

```rust
// (simplified — actual generated code has more variants)
enum Frame_Proc<'a> {
    // Infix: we parsed the left operand and operator, now need the right
    InfixRHS {
        left: Proc,
        op_pos: usize,          // position of operator token (not Token<'a>!)
        label: &'static str,    // "Add", "Sub", ...
        right_bp: u8,
    },
    // Prefix handler continuation: parsed some tokens, need a sub-expression
    PrefixCont_PDrop {
        // saved state for after parsing the Name sub-expression
    },
    // Collection element: parsing elements of a PPar
    CollectionElem_PPar {
        elements: Vec<Proc>,
        // ...separator info
    },
    // ... more variants for other rules
}
```

Key design decisions:
- Frames are `'static` (no borrowed Token references) — `op_pos: usize` instead
  of `op_token: Token<'a>` avoids lifetime issues
- Thread-local frame pool: `Cell<Vec<Frame_Cat>>` enables allocation reuse
  across parse calls (`Cell` not `RefCell` — standalone functions cause
  re-entrancy that would panic with `RefCell`)
- CastWrap frames are unnecessary — cross-category dispatch has bounded
  recursion depth, so casts are inlined directly

### Two-Loop State Machine

The trampolined parser has two alternating loops:

```
'drive: loop {
    // PHASE 1: Parse prefix — produce a value or push a frame
    //   - Match leading token against FIRST set
    //   - For simple prefixes: consume tokens, produce value
    //   - For complex prefixes: consume partial tokens, push frame, recurse
    //   - For casts: call sub-category parser directly (bounded depth)

    'unwind: loop {
        // PHASE 2: Infix loop + unwind
        //   - Peek at next token
        //   - If it's an infix operator with left_bp ≥ min_bp:
        //       push InfixRHS frame, continue 'drive to parse right operand
        //   - If not: pop a frame from the stack
        //       apply continuation, back to top of 'unwind (TCO)
        //   - If stack empty: return the value
    }
}
```

### Handler Routing

Not all rules are trampolined inline.  Complex patterns use standalone
functions:

| Pattern                               | Routing              | Reason                 |
|---------------------------------------|----------------------|------------------------|
| Simple prefix (PZero, Err)            | Inline in 'drive     | No recursion           |
| Prefix with sub-parse (PDrop, NQuote) | Frame + recurse      | One level of recursion |
| Collection (PPar)                     | CollectionElem frame | Loop via frame stack   |
| ZipMapSep (PInputs)                   | Standalone function  | Too complex for frames |
| Binder (PNew)                         | Standalone function  | Needs variable scoping |
| Infix (Add, Mul, ...)                 | InfixRHS frame       | Standard Pratt         |
| Cast (CastInt, ...)                   | Inline dispatch      | Bounded depth          |

The helpers `is_simple_collection()` and `should_use_standalone_fn()` in
trampoline.rs decide the routing.

## Cross-Category Dispatch

**Source:** `prattail/src/dispatch.rs`

When a rule in category A needs to parse a sub-expression of category B,
cross-category dispatch is needed.

For RhoCalc: `POutput` is in `Proc` but has a `Name` parameter.  The parser
for `Proc` must be able to call the parser for `Name`.

Cast rules generate dispatch wrappers: `parse_proc` can call `parse_name`
when it sees a token in FIRST(Name).  The wrapper parses the `Name` value
and wraps it in a cast constructor (e.g., `Proc::CastName` if such existed, but
for `NQuote` the prefix handler in `Name` is invoked directly).

Cross-category infix rules (not present in RhoCalc but supported) generate
dispatch wrappers that parse the left operand in one category and produce a
result in another.

## Recursive Descent Handlers

**Source:** `prattail/src/recursive.rs`

For rules that cannot be handled by the Pratt loop alone, RD handlers are
generated:

- **Binder parsing**: `PNew` needs to parse `"new" "(" x "," body ")"`.
  The `x` is an identifier captured as a binder variable.  The `body` is
  parsed as a `Proc` with the binder in scope.

- **Collection parsing**: `PPar` needs to parse `"{" proc ("|" proc)* "}"`.
  The RD handler loops parsing `Proc` values separated by `|` until `}`.

- **ZipMapSep parsing**: `PInputs` needs to parse
  `"(" (name "?" ident ",")* ")" "." "{" body "}"`.
  This is a standalone function that handles the pairwise zip+map+sep pattern.

## Tracing `3 + 4 * 5` Through the Parser

Token stream: `[Integer("3"), Plus, Integer("4"), Star, Integer("5"), Eof]`

```
parse_proc(tokens, pos=0, min_bp=0):
  'drive: prefix phase
    peek = Integer("3") → matches CastInt cast rule
    parse_int(tokens, pos=0, min_bp=0) → Int::NumLit(3), pos=1
    value = Proc::CastInt(Box::new(Int::NumLit(3)))

  'unwind: infix loop
    peek = Plus, left_bp=10 ≥ min_bp=0 → enter infix for Add
    push frame: InfixRHS { left: CastInt(3), op_pos: 1, label: "Add", right_bp: 11 }
    pos=2, continue 'drive with min_bp=11

  'drive: prefix phase
    peek = Integer("4") → CastInt cast
    parse_int → Int::NumLit(4), pos=3
    value = Proc::CastInt(Box::new(Int::NumLit(4)))

  'unwind: infix loop
    peek = Star, left_bp=12 ≥ min_bp=11 → enter infix for Mul
    push frame: InfixRHS { left: CastInt(4), op_pos: 3, label: "Mul", right_bp: 13 }
    pos=4, continue 'drive with min_bp=13

  'drive: prefix phase
    peek = Integer("5") → CastInt cast
    value = Proc::CastInt(Box::new(Int::NumLit(5))), pos=5

  'unwind: infix loop
    peek = Eof, no infix operator → pop frame
    frame = InfixRHS { left: CastInt(4), label: "Mul" }
    value = Proc::Mul(Box::new(CastInt(4)), Box::new(CastInt(5)))

  'unwind: continue infix loop
    peek = Eof, no infix operator → pop frame
    frame = InfixRHS { left: CastInt(3), label: "Add" }
    value = Proc::Add(Box::new(CastInt(3)), Box::new(Mul(CastInt(4), CastInt(5))))

  'unwind: stack empty → return value
```

Result AST:

```
Add
├── CastInt(NumLit(3))
└── Mul
    ├── CastInt(NumLit(4))
    └── CastInt(NumLit(5))
```

Multiplication binds tighter than addition because `left_bp(Star)=12 > min_bp=11`
while `left_bp(Plus)=10 < min_bp=11`.

## Error Recovery

For each category, a separate `parse_Cat_recovering()` function is generated
that accepts an `&mut Vec<ParseError>` accumulator.  On parse failure, it:

1. Records the error
2. Skips tokens until a sync token (from FOLLOW set + structural delimiters)
3. Returns a sentinel `Cat::Err` value
4. Continues parsing the rest of the input

This provides zero overhead on the non-recovering path — the main `parse_Cat()`
function is a clean, fast parser with no error-handling code.

---

**Next:** [05-ascent-codegen.md](05-ascent-codegen.md) — how the parsed AST is
evaluated by the Ascent Datalog engine.
