# CEK-2: Continuation Compression (Unary Chain Merging)

## Intuition

When parsing nested unary prefix operators like `---42`, the trampoline pushes one frame per operator. BP02's `tail_wrap: Option<(u8, u8)>` handles one level of tail-call elimination, but chains of consecutive prefixes still push N individual frames.

Continuation compression extends `tail_wrap` to accumulate chains: `---42` produces a single `Vec` of `(tag, bp)` pairs instead of 3 separate frames.

## Theoretical Basis

### Two-Way Transducer Pattern Detection

A chain of unary prefixes `op₁ op₂ ⋯ opₙ x` is a sequence recognized by a regular expression `(prefix_token)*`. The two-way transducer module (`two_way_transducer.rs`) can identify such compressible patterns via crossing sequence analysis.

### Buchi Periodicity

For recursive grammars producing **unbounded** unary chains (e.g., a prefix operator that recurses), the Buchi automaton module (`buchi.rs`) identifies the ultimately periodic repeating unit. The compression applies uniformly to the repeating unit.

## Algorithm

### Before (BP02, single tail_wrap)

```
Parse "---42":
  [pos=0] match '-': tail_wrap = Some((NEG, bp)), cur_bp = prefix_bp, continue 'drive
  [pos=1] match '-': ERROR — tail_wrap already set, must push frame instead
          push UnaryPrefix_Neg { saved_bp }
          continue 'drive
  [pos=2] match '-': push UnaryPrefix_Neg { saved_bp }
          continue 'drive
  [pos=3] match '42': lhs = Lit(42)
  [unwind] pop UnaryPrefix_Neg → lhs = Neg(lhs)
  [unwind] pop UnaryPrefix_Neg → lhs = Neg(lhs)
  [unwind] apply tail_wrap → lhs = Neg(lhs)
  Stack depth: 2 (+ 1 tail_wrap)
```

### After (BP06, chain compression)

```
Parse "---42":
  [pos=0] match '-': tail_wraps.push((NEG, cur_bp)), cur_bp = prefix_bp, continue 'drive
  [pos=1] match '-': tail_wraps.push((NEG, cur_bp)), cur_bp = prefix_bp, continue 'drive
  [pos=2] match '-': tail_wraps.push((NEG, cur_bp)), cur_bp = prefix_bp, continue 'drive
  [pos=3] match '42': lhs = Lit(42)
  [unwind] while tail_wraps.pop():
    (NEG, bp) → lhs = Neg(lhs), cur_bp = bp
    (NEG, bp) → lhs = Neg(lhs), cur_bp = bp
    (NEG, bp) → lhs = Neg(lhs), cur_bp = bp
  Stack depth: 0
```

## Implementation

### Type Change

```rust
// Before:
let mut tail_wrap: Option<(u8, u8)> = None;

// After (when BP06 enabled):
let mut tail_wraps: Vec<(u8, u8)> = Vec::new();
```

### Prefix Phase Change

```rust
// Before:
tail_wrap = Some((tag, saved_bp));
cur_bp = rule_bp;
continue 'drive;

// After:
tail_wraps.push((tag, cur_bp));
cur_bp = rule_bp;
continue 'drive;
```

### Unwind Phase Change

```rust
// Before:
if let Some((tw, tw_bp)) = tail_wrap.take() {
    match tw { /* apply constructor */ }
    cur_bp = tw_bp;
}

// After:
while let Some((tw, tw_bp)) = tail_wraps.pop() {
    match tw { /* apply constructor */ }
    cur_bp = tw_bp;
}
```

### Optimization Gate

- **Code:** `BP06`
- **Name:** `ContinuationCompression`
- **Speedup:** 0.1 (modest — reduces stack depth for prefix chains)
- **Cost:** 0.05 (very low — extends existing mechanism)
- **Applicability:** Always applicable (extends BP02)

## Correctness

**Theorem CEK.4 (BP02 Tail-Call Correctness):** The `tail_wrap` optimization produces the same result as full frame push/pop. Each frame in the chain carries no captures (`accumulated_captures.is_empty()`), so `tail_wrap = (tag, saved_bp)` stores identical information. The chain extension preserves this property because `Vec::pop()` applies constructors in reverse order — exactly matching the frame pop order.

Proof: `formal/rocq/trampoline/theories/TailCallCorrectness.v`.
