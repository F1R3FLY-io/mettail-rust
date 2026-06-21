# Rest Patterns Implementation - Complete

## Summary

Successfully implemented explicit `...rest` pattern support for the ambient calculus, enabling rewrite rules to match collection patterns with variable-length contexts. All tests passing (17/17).

## Problem Statement

The ambient calculus uses associative parallel composition `{P, Q}`, which should satisfy `P == {P, 0}`. Rewrite rules like:

```
{n[{in(m,p), q}], m[r]} => {m[{n[{p, q}], r}]}
```

Should match terms like `{n[{in(m,p)}], m[r]}` (where `q` is empty), but weren't matching because rewrite rules were doing syntactic pattern matching rather than matching modulo equivalence.

## Solution

Implemented explicit `...rest` variables that can match empty or non-empty collections:

```rust
// Entry rule with rest
(PPar {(PAmb N (PPar {(PIn M P) , ...rest})) , (PAmb M R)})
    => (PPar {(PAmb M (PPar {(PAmb N (PPar {P , ...rest})), R}))});

// Exit rule with rest
(PAmb M (PPar {(PAmb N (PPar {(POut M P), ...rest})), R}))
    => (PPar {(PAmb N (PPar {P, ...rest})), (PAmb M R)});
```

## Implementation Details

### 1. AST Extensions (`congruence_analysis.rs`)
- Added `rest_var: Option<Ident>` to `ElementPatternInfo`
- Extract rest variables from collection patterns during projection analysis
- Track rest variables through the entire generation pipeline

### 2. Projection Signature (`congruence_analysis.rs`)
- Extended projection relations to include `HashBag<ElemCat>` for rest variables
- Compute rest bags by cloning the parent bag and removing matched elements
- Handle rest variables separately from regular captures (different type)

### 3. Binding Propagation (`ascent_gen.rs`)
- Track rest variables in `generate_joined_base_rewrite_clause`
- Pass rest variables through projection calls with marker `field_idx = usize::MAX`
- Include rest variables in `bindings` map for RHS reconstruction

### 4. Move Semantics (`rewrite_gen.rs`)
- Store rest variables with `.clone()` since `HashBag` doesn't implement `Copy`
- Prevent "use of moved value" errors when rest variables are referenced multiple times

### 5. Base Rewrite Generation Fix (`rewrite_gen.rs`)
- **Critical fix**: Only skip base rewrites if the **root** of the LHS is a collection constructor covered by congruence
- Previously was skipping any rewrite with a collection pattern anywhere in the LHS
- Added `get_constructor_collection_element_type` to check root constructor only
- This fixed the exit rules which have pattern `(PAmb M (PPar {...}))` - root is `PAmb`, not `PPar`

## Test Coverage

Created comprehensive test suite (`examples/ambient_tests.rs`) with 17 tests:

### Basic Rest Patterns
- ✅ `enter_empty_rest`: Empty rest pattern matching
- ✅ `exit_empty_rest`: Exit with empty rest
- ✅ `open_basic`: Basic open capability
- ✅ `enter_nonempty_rest`: Non-empty rest preservation
- ✅ `enter_multiple_rest`: Multiple items in rest
- ✅ `exit_nonempty_rest`: Exit preserving context
- ✅ `exit_multiple_rest`: Exit with multiple rest items

### Context Preservation
- ✅ `context_preservation`: Both ambients preserve local state
- ✅ `zero_in_context`: Zero explicitly in rest
- ✅ `nested_ambients_in_rest`: Nested structures in rest

### Advanced Scenarios
- ✅ `parallel_entry`: Multiple simultaneous entries
- ✅ `sequential_mobility`: Chained mobility operations
- ✅ `nested_mobility`: Parent-child mobility
- ✅ `entry_then_exit`: Sequential enter/exit
- ✅ `open_after_entry`: Entry followed by open

### Congruence
- ✅ `congruence_in_ambient`: Rewrites under ambient constructor
- ✅ `congruence_in_parallel`: Rewrites in parallel context

## Examples Library

Extended `repl/src/examples.rs` with 7 new ambient calculus examples demonstrating rest patterns:

- `AMB_REST_EMPTY`: Empty rest matching
- `AMB_REST_NONEMPTY`: Non-empty context
- `AMB_REST_CONTEXT`: State preservation
- `AMB_REST_NESTED`: Multi-level nesting
- `AMB_REST_MULTIPLE`: Parallel operations
- `AMB_REST_PRESERVATION`: Sequential steps
- `AMB_REST_COMPLEX`: Complex interactions

## Key Insights

1. **Type Safety**: Rest variables have type `HashBag<ElemCat>`, different from element type
2. **Move Semantics**: Must use `.clone()` for rest variables due to `HashBag` not implementing `Copy`
3. **Projection Strategy**: Rest computation happens in Ascent population rules by cloning and removing
4. **Root vs Nested**: Critical distinction between root collection constructors and nested collections
5. **Empty Bags**: Rest can be empty `HashBag::new()`, enabling optional context patterns

## Performance

All tests run in < 4 seconds, demonstrating efficient compilation and execution.

## Next Steps

Potential enhancements:
1. Support multiple rest variables in a single pattern (e.g., `...rest1, ...rest2`)
2. Optimize rest computation for large bags
3. Add more complex nested rest pattern examples
4. Extend to other calculi (pi-calculus, lambda-calculus)

## Conclusion

Explicit rest patterns provide a clean, correct solution for matching variable-length collection contexts. The implementation is robust, well-tested, and ready for use in complex process calculi specifications.

