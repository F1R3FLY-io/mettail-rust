# Tape-Based Term Generation Strategies

## What Is It?

The MeTTaIL simulation framework generates random terms for property-based testing using a **tape-based iterative term builder**. Rather than constructing terms via recursive strategy combinators (which overflow the Rust stack on deeply nested grammars), the system generates a flat byte vector ("instruction tape") via proptest and interprets it iteratively to produce structured terms.

This approach was designed specifically for the MeTTaIL language system, where term grammars can contain dozens of mutually recursive categories (e.g., `Proc`, `Name`, `Int`, `Bool`, `Str` in Rholang) and term depth can easily reach 30+ levels of nesting.

## What Does It Do?

The strategy system:

1. **Generates random terms** from any MeTTaIL language definition, respecting type constraints and depth bounds.
2. **Supports proptest shrinking** natively: shorter tapes produce simpler terms.
3. **Handles cross-category references**: a `Proc` term can contain `Name` sub-terms without recursive function calls.
4. **Produces display strings** suitable for parsing by the language's parser, closing the generate-parse-rewrite loop.

## Why Was It Chosen?

### The Problem with Recursive Strategies

The naive approach to generating terms for a recursive grammar uses proptest's `prop_recursive`:

```rust
// DANGEROUS: overflows the stack on deeply nested grammars
fn arb_proc() -> BoxedStrategy<Proc> {
    let leaf = prop_oneof![
        Just(Proc::PZero),
        // ...
    ];
    leaf.prop_recursive(8, 256, 10, |inner| {
        prop_oneof![
            inner.clone().prop_map(|p| Proc::PPar(vec![p])),
            inner.clone().prop_map(|p| Proc::PNew(vec!["x"], p)),
            // ...
        ]
    }).boxed()
}
```

Each level of `prop_recursive` creates a closure that holds a reference to the inner strategy. For a grammar with 6 mutually recursive categories and depth 30, this creates a tower of ~180 nested closures. Rust's default 8 MB stack cannot hold this, resulting in stack overflows during test generation (not during test execution).

### The Tape-Based Solution

The tape-based approach replaces recursion with iteration:

```
proptest generates:  Vec<u8>  (flat, shrinkable)
                      │
                      ▼
               ┌─────────────────┐
               │  TapeReader     │  Consumes bytes from the tape
               │  .next_byte()   │  Wraps around when exhausted
               │  .next_u32()    │
               │  .next_i64()    │
               │  .next_f64()    │
               │  .next_string() │
               └────────┬────────┘
                        │ bytes → constructor choices, literal values
                        ▼
               ┌─────────────────┐
               │  Work Stack     │  Vec<BuildTask>
               │  BuildProc      │  Push child tasks for recursive fields
               │  BuildName      │  Store results in indexed slots
               │  BuildInt       │
               └────────┬────────┘
                        │
                        ▼
               ┌─────────────────┐
               │  Result Slots   │  Vec<Option<AnyTerm>>
               │  slot[0] = Proc │
               │  slot[1] = Name │
               │  ...            │
               └─────────────────┘
```

This design was inspired by QuickCheck's approach to arbitrary instance generation (Claessen and Hughes (2000)), adapted for iterative execution.

## How Does It Work?

### The TapeReader

The `TapeReader` is a simple cursor over the byte tape:

```
PROCEDURE TapeReader.next_byte():
    IF tape is empty THEN RETURN 0
    b ← tape[pos mod |tape|]      // wrap around
    pos ← pos + 1
    RETURN b
```

The wrap-around behavior is essential: it means every tape, no matter how short, produces a valid (if degenerate) term. Shorter tapes produce simpler terms because the same bytes are reused, biasing toward repetitive (and thus structurally simpler) choices.

Compound types are read by consuming multiple bytes:

```
PROCEDURE TapeReader.next_u32():
    RETURN next_byte()
         | (next_byte() << 8)
         | (next_byte() << 16)
         | (next_byte() << 24)

PROCEDURE TapeReader.next_string():
    len ← next_byte() mod 8        // strings at most 7 characters
    RETURN concatenate(
        for i in 0..len:
            char('a' + (next_byte() mod 26))
    )
```

### The BuildTask Pipeline

Each language category gets a `BuildTask` variant:

```
ENUM BuildTask:
    BuildProc { depth: u32, slot: usize }
    BuildName { depth: u32, slot: usize }
    BuildInt  { depth: u32, slot: usize }
    ...
```

The builder processes tasks from a work stack:

```
PROCEDURE build_from_tape(tape: [u8], max_depth: u32) → Term:
    reader ← TapeReader(tape)
    slots  ← [None; estimated_slots]
    stack  ← [BuildPrimaryCategory { depth: max_depth, slot: 0 }]

    WHILE stack is not empty:
        task ← stack.pop()

        MATCH task:
            BuildProc { depth, slot }:
                IF depth == 0 THEN
                    // Choose a leaf constructor (nullary or literal)
                    choice ← reader.next_byte() mod |leaf_constructors|
                    slots[slot] ← Some(leaf_constructors[choice])
                ELSE
                    // Choose any constructor
                    choice ← reader.next_byte() mod |all_constructors|
                    ctor ← all_constructors[choice]

                    // Allocate slots for children
                    FOR each field f in ctor.fields:
                        child_slot ← allocate_slot()
                        stack.push(BuildCategory(f.type) {
                            depth: depth - 1,
                            slot: child_slot
                        })

                    // Record that slot depends on child slots
                    slots[slot] ← Some(PendingCtor(ctor, child_slots))

            BuildInt { depth, slot }:
                // Native types read directly from tape
                slots[slot] ← Some(reader.next_i64())

            // ... similarly for other categories

    RETURN assemble(slots[0])
```

### Constructor Classification

Each category's constructors are classified into two groups:

| Classification | Description                                  | Example                                |
|----------------|----------------------------------------------|----------------------------------------|
| **Leaf**       | No recursive fields; can be built at depth 0 | `PZero`, `42`, `true`                  |
| **Recursive**  | Has fields of the same or other categories   | `PPar(Proc, Proc)`, `PNew(Name, Proc)` |

At depth 0, only leaf constructors are chosen. At depth > 0, any constructor may be chosen, with recursive constructors pushing child `BuildTask` entries onto the work stack at depth - 1.

### The AnyTerm Wrapper

Because the work stack processes tasks for multiple categories, results must be stored in a homogeneous container. The `AnyTerm` enum wraps all category types:

```rust
enum AnyTerm {
    WrapProc(Proc),
    WrapName(Name),
    WrapInt(Int),
    WrapBool(Bool),
    WrapStr(Str),
    // ...
}
```

Each variant provides an unwrap method (e.g., `unwrap_proc()`) for extracting the concrete type when assembling the final term.

### The arb_ Strategy Function

The public strategy for each category follows a uniform pattern:

```
FUNCTION arb_proc(max_depth: u32) → BoxedStrategy<String>:
    max_tape ← estimate_tape_size(max_depth)
    RETURN proptest::collection::vec(any::<u8>(), 1..max_tape)
        .prop_map(|tape| {
            term ← build_proc_from_tape(&tape, max_depth)
            format!("{}", term)       // display string for parsing
        })
        .boxed()
```

The strategy produces `String` values (not typed terms) because the simulation runner feeds them to `language.parse_term()`, which closes the generate → parse → rewrite loop.

## Shrinking Semantics

Proptest's built-in shrinking for `Vec<u8>` provides free shrinking of generated terms:

```
Original tape:  [0xA3, 0x17, 0xFF, 0x42, 0x00, 0x91, 0x3E, ...]
                 │      │      │      │
                 │      │      │      └─ constructor choice
                 │      │      └─ literal value byte
                 │      └─ constructor choice
                 └─ root constructor choice

Shrunk tape:    [0x00, 0x00, 0x00]
                 │
                 └─ all choices go to index 0 (typically the simplest constructor)
```

Shrinking operates at two levels:

1. **Tape length reduction**: shorter tapes produce fewer constructor choices, yielding shallower terms. The wrap-around behavior means no tape is ever "too short" to produce a term.

2. **Byte value reduction**: proptest shrinks individual bytes toward 0. Since constructor choice uses `byte mod num_constructors`, smaller bytes bias toward earlier constructors, which by convention are simpler (leaf constructors are listed first).

The combined effect is that shrinking produces the structurally simplest term that still triggers the failure, without any custom shrinking logic. This is a key advantage over hand-written shrinkers.

### Shrinking in the SimulationRunner

The `SimulationRunner.try_shrink()` method wraps proptest's value tree with an additional shrinking loop:

```
PROCEDURE try_shrink(value_tree, initial_failure, seed) → SimulationFailure:
    best ← initial_failure
    FOR step in 0..128:           // max 128 shrink steps
        IF NOT value_tree.simplify() THEN
            IF NOT value_tree.complicate() THEN BREAK
        input ← value_tree.current()
        result ← run_to_normal_form(input)
        IF result is Err(failure) THEN
            best ← failure         // still fails; try simplifying more
        ELSE
            IF NOT value_tree.complicate() THEN BREAK
            // shrunk input passes; complicate to find boundary
    RETURN best
```

The `simplify()` / `complicate()` dance implements proptest's binary-search-style shrinking: simplify until the failure disappears, then complicate to find the boundary. The result is a minimal reproducing input.

## Public Strategy API

The generated strategies follow a consistent naming convention:

```rust
/// Generate a random Proc term as a display string.
fn arb_proc(max_depth: u32) -> BoxedStrategy<String>

/// Generate a random Name term as a display string.
fn arb_name(max_depth: u32) -> BoxedStrategy<String>

/// Generate a random Int term as a display string.
fn arb_int(max_depth: u32) -> BoxedStrategy<String>
```

These are generated by the `macros` crate's `generate_strategies()` function at compile time, one per category in the language definition.

For the `SimulationRunner`, any `Strategy<Value = String>` can be passed to `run_campaign()`:

```rust
let strategy = arb_proc(20);  // generated for the Rholang language
let results = runner.run_campaign(strategy);
```

## Integration with proptest

The tape-based design integrates seamlessly with proptest's infrastructure:

| proptest Feature | Integration                                                      |
|------------------|------------------------------------------------------------------|
| `TestRunner`     | Provides RNG; `SimulationRunner.run_campaign()` instantiates one |
| `Strategy`       | `arb_*()` returns `BoxedStrategy<String>`                        |
| `ValueTree`      | Proptest's `VecValueTree` handles shrinking of the byte tape     |
| `Config`         | Campaign uses `proptest::test_runner::Config { cases, .. }`      |
| `TestRng`        | Optional fixed seed (`[u8; 32]`) for deterministic replay        |

## References

- Claessen, K. and Hughes, J. (2000). "QuickCheck: A Lightweight Tool for Random Testing of Haskell Programs." ACM SIGPLAN Notices, 35(9), pp. 268-279.
- Hedgehog contributors (2017). "Hedgehog: Release with Confidence." Integrated shrinking design.
