# I04: beam-feature-required

**Severity:** Warning
**Category:** infrastructure
**Feature Gate:** Emitted only when `wfst-log` feature is **not** enabled

## Description

Warns that the grammar's `beam_width` configuration is set to `Auto` but the
`wfst-log` feature is not enabled. Automatic beam width computation requires
the log-semiring WFST infrastructure to compute per-category entropy estimates,
which are used to determine optimal beam widths. Without `wfst-log`, the
auto-beam logic falls back to `Disabled` (no beam pruning), which may result
in larger WFST state spaces and slower pipeline construction.

The beam width controls how aggressively the transducer cascade prunes
low-probability WFST paths. With `Auto`, the pipeline computes the Shannon
entropy of each category's token distribution and sets the beam width
inversely proportional to entropy: low-entropy (deterministic) categories
get no beam (already focused), while high-entropy (ambiguous) categories
get tighter beams to prune unlikely alternatives.

```
  Beam width auto-computation flow:

  ┌────────────────────┐
  │ beam_width = Auto   │
  └────────┬───────────┘
           │
     wfst-log enabled?
     ├── yes -> compute per-category entropy
     │          ├── low entropy  -> no beam (I03 note)
     │          └── high entropy -> beam = f(entropy)
     │
     └── no  -> fall back to Disabled
                └── emit I04 warning
```

## Trigger Conditions

All of the following must hold:

- The grammar specifies `beam_width: auto` (or the default is `Auto`).
- The `wfst-log` Cargo feature is **not** enabled at compile time.

One diagnostic is emitted per grammar.

## Example

### Cargo.toml

```toml
[dependencies]
mettail-prattail = { version = "0.1", features = [] }
# Note: wfst-log is NOT in the feature list
```

### Grammar

```rust
language! {
    name: TestGrammar,
    beam_width: auto,
    // ...
}
```

### Output

```
warning[I04] (TestGrammar): beam_width: auto requires feature `wfst-log`; falling back to disabled
  = hint: enable `wfst-log` feature or use explicit beam_width
```

## Resolution

1. **Enable the `wfst-log` feature.** Add `wfst-log` to the feature list in
   your `Cargo.toml`:

   ```toml
   [dependencies]
   mettail-prattail = { version = "0.1", features = ["wfst-log"] }
   ```

   This enables log-semiring WFST construction and entropy-based automatic
   beam width computation.

2. **Set an explicit beam width.** If you do not want the `wfst-log`
   dependency, replace `beam_width: auto` with an explicit value:

   ```rust
   language! {
       name: TestGrammar,
       beam_width: 8,
       // ...
   }
   ```

3. **Disable beam pruning.** If beam pruning is not needed:

   ```rust
   language! {
       name: TestGrammar,
       beam_width: disabled,
       // ...
   }
   ```

## Hint Explanation

The hint **"enable `wfst-log` feature or use explicit beam_width"** presents
the two available paths:

- **Enable `wfst-log`**: unlocks the log-semiring infrastructure that `Auto`
  depends on. This adds a compile-time dependency on log-weight arithmetic
  but provides the best automatic beam configuration.
- **Use explicit beam_width**: bypasses the need for entropy computation by
  providing a fixed beam width. This is simpler but may not be optimal for
  all categories in the grammar.

## Related Lints

- [I01](I01-transducer-cascade.md) -- Transducer cascade summary. The beam
  width affects which cascade passes run and how aggressively they prune.
- [I03](I03-beam-auto-computed.md) -- Beam auto-computed. The positive
  counterpart: emitted when `wfst-log` is enabled and auto-beam succeeds.
- [W10](../wfst/W10-nfa-spillover-eliminable.md) -- NFA spillover eliminable
  by lookahead. Beam pruning can reduce WFST ambiguity and eliminate
  spillover.
