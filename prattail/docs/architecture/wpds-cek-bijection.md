# WPDS ↔ Frame Bijection

## Intuition

The WPDS (`wpds.rs`) and the trampoline parser (`trampoline.rs`) model the same pushdown automaton from different angles. The WPDS represents stack configurations abstractly as sequences of `StackSymbol` triples; the trampoline uses concrete `Frame_Cat` enum variants with typed fields.

The **CEK-3 bijection** maps between these representations, enabling compile-time WPDS analysis results (reachability, dead rules, context-sensitive FIRST sets) to be transferred directly to runtime frame structures.

## Mapping Table

| Frame Variant | WPDS StackSymbol |
|---------------|-----------------|
| `RD_{label}_{pos}` | `rule_position(cat, label, pos+1)` |
| `InfixRHS` | `rule_position(cat, "__infix__", 1)` |
| `GroupClose` | `rule_position(cat, "__group__", 1)` |
| `UnaryPrefix_{label}` | `rule_position(cat, label, 1)` |
| `CollectionElem_{label}` | `rule_position(cat, label, 1)` |
| `Mixfix_{label}_{pos}` | `rule_position(cat, label, pos+1)` |

## Abstraction Function

```
α : Frame_Cat → StackSymbol

α(InfixRHS)              = ⟨cat, __infix__, 1⟩
α(GroupClose)             = ⟨cat, __group__, 1⟩
α(UnaryPrefix_L)          = ⟨cat, L, 1⟩
α(RD_L_i)                = ⟨cat, L, i+1⟩
α(CollectionElem_L)       = ⟨cat, L, 1⟩
α(Mixfix_L_i)            = ⟨cat, L, i+1⟩
```

The inverse `α⁻¹` is well-defined because:
1. Frame variant names are deterministic from rule structure
2. Position offsets are 1-indexed in WPDS, 0-indexed in trampoline
3. `__infix__` and `__group__` are reserved labels (no grammar rule uses them)

## Implementation

```rust
pub struct CekWpdsBijection {
    pub frame_to_symbol: HashMap<String, StackSymbol>,
    pub symbol_to_frame: HashMap<StackSymbol, String>,
}
```

Built by `build_cek_bijection(spec: &LanguageSpec)` which walks the grammar rules and creates both directions of the mapping.

## Applications

### CEK-4: Dead Frame Elimination

```
WPDS poststar → P-automaton → is_symbol_accepted(sym)
                                    │
                              (if false)
                                    │
                      bijection.symbol_to_frame(sym)
                                    │
                         suppress frame variant codegen
```

### CEK-5: Context-Sensitive FIRST Sets

```
For each frame variant F:
  sym = bijection.frame_to_symbol(F)
  contexts = poststar.reachable_contexts(sym)
  FIRST_cs(F) = ∪_{ctx ∈ contexts} FIRST(suffix(F), ctx)
```

## Correctness

The bijection is verified at build time by two assertions:
1. **Completeness**: Every frame variant has a corresponding symbol
2. **Soundness**: Every relevant symbol has a corresponding frame variant

```rust
assert!(bijection.is_complete());
```

## Theorem (Forward Simulation)

For every concrete transition `s → s'`:

```
α(s) →*_WPDS α(s')
```

Proof by case analysis on the 10 transition rules.
See `formal/rocq/trampoline/theories/WpdsSimulation.v`.
