# Phase 6.1 Complete: Detection & Analysis ✅

**Status**: Implemented and compiling
**Time**: ~1 hour
**Files Modified**: `macros/src/rewrite_gen.rs`

## What Was Built

### 1. Data Structures (Lines 7-55)
- `ProjectionSpec`: Complete metadata for a projectable pattern
- `ElementPattern`: Information about each nested pattern
- `CaptureInfo`: Details about captured variables

### 2. Detection Functions (Lines 179-205)
- `requires_indexed_projection()`: Determines if a rule needs projections
  - Checks for nested Apply patterns in collections
  - Checks for shared variables across patterns
  - Returns `true` only when both conditions are met

### 3. Helper Functions (Lines 207-255)
- `find_shared_variables_in_collection()`: Finds variables appearing in multiple elements
- `collect_vars_in_expr()`: Extracts all variable names from an expression
- `collect_vars_recursive()`: Recursive variable collection

### 4. Analysis Function (Lines 257-359)
- `analyze_collection_pattern()`: Main analysis entry point
  - Extracts parent constructor and category
  - Finds collection field index
  - Analyzes each element pattern
  - Identifies shared variables (join keys)
  - Builds complete `ProjectionSpec`

### 5. Capture Extraction (Lines 361-434)
- `extract_captures_from_args()`: Extracts variable captures from constructor args
- `find_grammar_index_for_arg()`: Maps arg position to grammar position
- `get_field_category()`: Gets category for a grammar field

## Key Design Decisions

1. **Only trigger for complex patterns**: Simple variable-only collections don't need projections
2. **Track everything**: Capture categories, field indices, binder status for complete info
3. **Identify join keys**: Separate shared variables from other captures
4. **Fail gracefully**: Return `None` if pattern doesn't fit (fall back to old code)

## Test Example

For the rho-calculus rule:
```rust
(PPar {(PInput chan x P), (POutput chan Q), ...rest}) => ...
```

The analyzer produces:
```rust
ProjectionSpec {
    collection_field_idx: 0,
    element_patterns: [
        ElementPattern {
            constructor: "PInput",
            category: "Proc",
            pattern_idx: 0,
            captures: [
                CaptureInfo { var_name: "chan", category: "Name", field_idx: 0, is_binder: false },
                CaptureInfo { var_name: "x", category: "Name", field_idx: 1, is_binder: true },
                CaptureInfo { var_name: "P", category: "Proc", field_idx: 2, is_binder: false },
            ],
            join_key_indices: [0], // "chan" is a join key
        },
        ElementPattern {
            constructor: "POutput",
            category: "Proc",
            pattern_idx: 1,
            captures: [
                CaptureInfo { var_name: "chan", category: "Name", field_idx: 0, is_binder: false },
                CaptureInfo { var_name: "Q", category: "Proc", field_idx: 1, is_binder: false },
            ],
            join_key_indices: [0], // "chan" is a join key
        },
    ],
    shared_variables: ["chan"],
    rest_variable: Some("rest"),
    parent_constructor: "PPar",
    parent_category: "Proc",
}
```

## Next: Phase 6.2

Now that we have complete metadata, we can generate:
1. Projection relations (one per element pattern)
2. Extraction rules (populate projections from collections)
3. Join-based rewrite rules (use Ascent's optimized joins)

Estimated time: 6-8 hours

