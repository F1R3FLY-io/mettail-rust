# Railroad Diagram Generation Guide

## Overview

PraTTaIL generates railroad diagrams from `LanguageSpec` grammar specifications. Each grammar category gets one diagram showing all its rules as alternatives.

## Generation

```rust
use mettail_prattail::railroad::*;

let spec: LanguageSpec = /* your language spec */;
let diagrams = generate_railroad_diagrams(&spec);

for (category, diagram) in &diagrams {
    println!("=== {} ===", category);
    println!("{}", diagram_to_text(&diagram.root));
}
```

## Output Formats

### ASCII Art (Built-in)

```
=== Expr ===
──┬────[ integer ]──
  ├──⟨ Expr ⟩──[ + ]──⟨ Expr ⟩──
  └──[ ( ]──⟨ Expr ⟩──[ ) ]──
```

### Abstract Node Tree

The `RailroadNode` enum provides a format-independent representation:

```rust
match &diagram.root {
    RailroadNode::Choice { alternatives } => {
        for alt in alternatives {
            // Process each alternative
        }
    },
    RailroadNode::Sequence { children } => { /* ... */ },
    // etc.
}
```

## Trace Annotation

After parsing with a `TraceCollector`, annotate diagrams with execution frequency:

```rust
use mettail_prattail::cek::TraceCollector;

let mut collector = TraceCollector::new();
// ... drive parser with trace collection ...

annotate_diagrams(&mut diagrams, &collector);

// Now diagram.hit_counts has per-rule hit counts
for (rule, count) in &diagrams["Expr"].hit_counts {
    println!("  {}: {} hits", rule, count);
}
```

## Node Types

| Node | Rendering | Used For |
|------|-----------|----------|
| `Terminal` | `──[ text ]──` | Keywords, operators, punctuation |
| `NonTerminal` | `──⟨ name ⟩──` | Category references, ident captures |
| `Sequence` | `──A──B──C──` | Rule items in order |
| `Choice` | Vertical branches | Multiple rules per category |
| `Optional` | Bypass path | `Optional { inner }` items |
| `Repeat` | Loop-back arrow | Collections with separators |
| `Empty` | `──ε──` | Epsilon transitions |
