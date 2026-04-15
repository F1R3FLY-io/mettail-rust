# CEK-5: Context-Sensitive FIRST Sets via WPDS

## Intuition

Standard FIRST set computation (`compute_first_sets()` in `prediction.rs`) unions all possible first tokens across all contexts. But some tokens are only valid FIRST tokens in certain stack contexts — context-free FIRST sets over-approximate.

By using the WPDS poststar P-automaton to enumerate reachable stack configurations, we compute **context-sensitive FIRST sets** that account for the calling context. This eliminates false ambiguities in grammars where different callers expose different subsets of rules.

## Algorithm

1. For each `StackSymbol` in the WPDS, compute the set of reachable stack configurations via poststar
2. For each category C and stack context ctx:
   - `FIRST_cs(C, ctx)` = tokens that can begin a parse of C when called from context ctx
3. When the decision tree or NFA disambiguation needs FIRST sets:
   - If context is known (e.g., from a specific caller), use `FIRST_cs(C, ctx)`
   - If context is unknown, fall back to context-free `FIRST(C)`

## Formal Definition

Given a grammar G, a WPDS W constructed from G, and a category C:

```
FIRST_cs(C, ctx) = { t ∈ Σ | ∃ derivation C ⟹* t γ
                      reachable from stack context ctx }
```

where ctx is a stack suffix below C's entry frame in the P-automaton.

## Implementation

### New Function: `compute_context_sensitive_first_sets()`

```rust
pub fn compute_context_sensitive_first_sets(
    standard_first: &HashMap<String, FirstSet>,
    wpds: &Wpds<BooleanWeight>,
    pa: &PAutomaton<BooleanWeight>,
    bijection: &CekWpdsBijection,
) -> HashMap<(String, String), FirstSet>  // (category, context_key) → refined FIRST
```

### Optimization Gate

- **Code:** `CEK03`
- **Name:** `ContextSensitiveFirst`
- **Speedup:** 0.25 (reduces false ambiguities → fewer NFA try-all paths)
- **Cost:** 0.2 (requires WPDS poststar + context enumeration)
- **Applicability:** When grammar has overlapping FIRST sets AND cross-category calls

## Example

Consider a grammar where category `B` has two rules:
- `B_Foo` starting with token `x`
- `B_Bar` starting with token `x`

These overlap in FIRST — NFA try-all is needed. But if:
- Category `A` only calls `B` from contexts where `B_Foo` is reachable
- Category `C` only calls `B` from contexts where `B_Bar` is reachable

Then context-sensitive analysis can resolve the ambiguity: `FIRST_cs(B, from_A) = {x}` (only Foo), `FIRST_cs(B, from_C) = {x}` (only Bar).

## Enhanced Analysis

### Weighted Alternating FIRST Sets

Using weighted alternating automata (`alternating.rs`): nondeterministic FIRST set computation with WFST path weights → **weighted FIRST sets** that rank alternatives by probability.

### Multi-Tape Cross-Category FIRST Sets

Using multi-tape automata (`multi_tape.rs`): parallel-tape FIRST computation for multiple categories simultaneously → cross-category FIRST sets accounting for all possible calling contexts.
