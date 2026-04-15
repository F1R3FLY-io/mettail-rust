# CEK-7: Railroad Diagrams + Debug Trace Visualization

## Intuition

The grammar's `LanguageSpec` / `RuleSpec` / `SyntaxItemSpec` items map directly to railroad diagram nodes. Each category gets one diagram, and runtime trace entries annotate the diagram with execution frequency.

## Grammar → Railroad Mapping

| PraTTaIL | Railroad Node |
|----------|--------------|
| `Terminal(t)` | ──[ t ]── (rounded box) |
| `NonTerminal { category }` | ──⟨ category ⟩── (square box) |
| `Optional { inner }` | bypass path around inner |
| Collection rule | loop-back with separator |
| Multiple rules for category | vertical choice branches |
| Rule items in sequence | horizontal chain |
| Infix operator | lhs ──[ op ]── rhs |

## Runtime Annotation

When a `CekMachine` is driven with a `TraceCollector`, hit counts per rule map onto the diagram:

- **Hot paths** (high frequency): thick red lines
- **Warm paths** (medium frequency): orange lines
- **Cold paths** (low frequency): thin blue lines
- **Dead paths** (never taken): dashed gray lines

Branch points annotated with taken/not-taken counts. The current position during step-through debugging is highlighted.

## Probabilistic Path Annotation

Using probabilistic automata analysis (`probabilistic.rs`):
- Branch probabilities from corpus-trained weights
- Expected path entropy indicates visual complexity
- Low-probability paths rendered as dashed lines

## Provenance Tracking

Using the provenance semiring (`provenance.rs`):
- Each diagram path → set of grammar rules that contribute to it
- "Click path → see rules" interaction for interactive tools

## Implementation

### Abstract Node Type

```rust
pub enum RailroadNode {
    Terminal { text },
    NonTerminal { text },
    Sequence { children },
    Choice { alternatives },
    Optional { inner },
    Repeat { element, separator },
    Empty,
}
```

This abstract representation is crate-independent — it can be rendered to:
- ASCII art (built-in `diagram_to_text()`)
- SVG (via `railroad` crate, feature-gated)
- JSON (for web-based rendering)

### Generation

```rust
pub fn generate_railroad_diagrams(spec: &LanguageSpec) -> HashMap<String, CategoryDiagram>
```

One diagram per category. Infix rules rendered as `lhs op rhs`. Collections rendered as loops.

### Annotation

```rust
pub fn annotate_diagrams(diagrams: &mut HashMap<String, CategoryDiagram>, trace: &TraceCollector)
```

Maps `trace.rule_hits` to diagram nodes for frequency visualization.
