# WFST Pipeline Integration

**Date:** 2026-02-22

This document explains exactly where the WFST subsystem attaches to the
PraTTaIL compile-time pipeline, what data flows between each stage, and
how the `DispatchStrategy` enum determines whether WFST construction
actually runs. Reading this document alongside `pipeline.rs` and
`prediction.rs` should leave no gaps about when and why WFST code fires.

---

## Table of Contents

1. [Pipeline State Machine](#1-pipeline-state-machine)
2. [WFST Insertion Point](#2-wfst-insertion-point)
3. [DispatchStrategy Resolution](#3-dispatchstrategy-resolution)
4. [Data Flow Inside generate_parser_code](#4-data-flow-inside-generate_parser_code)
5. [Data Bundles Annotated](#5-data-bundles-annotated)
6. [Runtime Data Flow](#6-runtime-data-flow)
7. [Codegen Outputs](#7-codegen-outputs)
8. [Debugging the Pipeline](#8-debugging-the-pipeline)
9. [Source Map](#9-source-map)

---

## 1. Pipeline State Machine

The PraTTaIL pipeline is a three-state machine. Each call to `advance()`
moves it one step forward; it cannot go backwards.

```
  ┌──────────────────────────────────────────────────────────────────────┐
  │  PipelineState                                                       │
  │                                                                      │
  │  ┌───────────┐   advance()   ┌─────────────┐   advance()            │
  │  │  Ready    │ ─────────────►│  Generated  │ ─────────────►Complete │
  │  │           │               │             │                        │
  │  │ lexer_    │               │ lexer_code  │               Token-   │
  │  │  bundle   │               │             │               Stream   │
  │  │ parser_   │               │ parser_code │                        │
  │  │  bundle   │               │             │                        │
  │  └───────────┘               └─────────────┘                        │
  └──────────────────────────────────────────────────────────────────────┘
```

`Ready → Generated` calls `generate_lexer_code()` and
`generate_parser_code()` sequentially, producing two Rust source strings.

`Generated → Complete` concatenates the two strings and parses them into
a single `TokenStream` that the proc-macro returns to the compiler.

`run_pipeline()` in `pipeline.rs` is the sole entry point. It calls
`extract_from_spec()` to project the `LanguageSpec` into `Send+Sync`
bundles, then loops `advance()` until `Complete`.

---

## 2. WFST Insertion Point

WFST construction lives entirely inside `generate_parser_code()`. It is
inserted after the FIRST/FOLLOW sets are ready and before any codegen
output is written to the output buffer. The overall sequence is:

```
  generate_parser_code(bundle: &ParserBundle)
  │
  ├─ 1. compute_first_sets()          ← FIRST sets per category
  │
  ├─ 2. augment FIRST with native     ← Integer/Float/Boolean/StringLit
  │      literal tokens
  │
  ├─ 3. analyze_cross_category_overlaps()  ← ambiguous token sets
  │
  ├─ 4. compute_follow_sets_from_inputs()  ← FOLLOW sets per category
  │
  ├─ 5. DispatchStrategy::resolve()   ← Static or Weighted decision
  │           │
  │           ▼
  ├─ 6. [wfst] WFST construction ─────── ← INSERT POINT ──────────────────┐
  │       │                                                                 │
  │       ├─ a. build_dispatch_action_tables()   (prediction.rs)           │
  │       ├─ b. build_prediction_wfsts()         (wfst.rs)                 │
  │       ├─ c. apply beam width config          (pipeline.rs)             │
  │       ├─ d. TokenIdMap::from_names()         (token_id.rs)             │
  │       └─ e. build_recovery_wfsts()           (recovery.rs)             │
  │                                                                         │
  ├─ 7. write_rd_handler() × N        ← RD prefix handlers                 │
  │                                                                         │
  ├─ 8. write_trampolined_parser() ←───── uses prediction_wfst per cat ────┘
  │      per category
  │
  ├─ 9. [wfst] write_category_dispatch_weighted()  (dispatch.rs)
  │    else     write_category_dispatch()
  │
  ├─ 10. write_recovery_helpers()
  │
  └─ 11. per category:
         ├─ generate_sync_predicate()
         ├─ [wfst] generate_wfst_recovery_fn()     (pipeline.rs private)
         └─ [wfst] write_trampolined_parser_recovering_wfst()
              else  write_trampolined_parser_recovering()
```

If the `wfst` feature is absent, steps 6, 9, and the WFST branches in
step 11 are entirely removed by the compiler. The resulting binary is
identical to a build that never had WFST code.

---

## 3. DispatchStrategy Resolution

`DispatchStrategy` is an enum on `LanguageSpec` with three variants.
It is resolved to a concrete `Static` or `Weighted` decision at the
start of the WFST block in step 6. The resolution happens after overlap
analysis so that `ambiguous_overlap_count` is available.

```
  ┌─────────────────────────────────────────────────────────────────────┐
  │  DispatchStrategy::resolve(                                         │
  │      total_rules,                                                   │
  │      cross_category_count,                                          │
  │      ambiguous_overlap_count,                                       │
  │  ) -> DispatchStrategy                                              │
  │                                                                     │
  │     ┌──────────────────────────────────────────────────────────┐   │
  │     │  feature = "wfst" absent?                                │   │
  │     │         │                                                │   │
  │     │        YES ──► warn if Weighted ──► return Static        │   │
  │     │         │                                                │   │
  │     │        NO                                                │   │
  │     │         │                                                │   │
  │     │         ▼                                                │   │
  │     │   self == Static? ──YES──► return Static                 │   │
  │     │         │                                                │   │
  │     │        NO                                                │   │
  │     │         │                                                │   │
  │     │   self == Weighted? ──YES──► return Weighted             │   │
  │     │         │                                                │   │
  │     │        NO  (Auto)                                        │   │
  │     │         │                                                │   │
  │     │         ▼                                                │   │
  │     │   (total_rules ≥ 30 AND cross_category_count > 0)        │   │
  │     │         OR ambiguous_overlap_count ≥ 3                   │   │
  │     │         │           │                                    │   │
  │     │        YES          NO                                   │   │
  │     │         │           │                                    │   │
  │     │         ▼           ▼                                    │   │
  │     │      Weighted     Static                                 │   │
  │     └──────────────────────────────────────────────────────────┘   │
  └─────────────────────────────────────────────────────────────────────┘
```

The thresholds in `Auto` mode reflect the empirical finding that WFST
overhead is negligible relative to compilation time once a grammar has 30
or more rules with cross-category interactions, or when three or more
token-overlap ambiguities require weighted tie-breaking.

`Static` is the default because most small-to-medium grammars do not need
weighted dispatch. The `Weighted` variant forces WFST construction
regardless of grammar size.

---

## 4. Data Flow Inside generate_parser_code

This section traces every input and output of the WFST construction block
(step 6 from section 2) in the order the code executes.

### Step 6a — build_dispatch_action_tables

```
  Inputs:
    category_names       &[String]          — all grammar categories
    first_sets           BTreeMap<String,   — FIRST set per category
                           TokenSet>
    overlaps             BTreeMap<(String,  — cross-category overlaps,
                           String),           including ambiguous tokens
                           OverlapInfo>
    rd_rules             &[RDRuleInfo]       — recursive-descent rules
    cross_rules          &[CrossCategoryRule]
    cast_rules           &[CastRule]
    native_types         BTreeMap<String,   — category → Rust type (opt)
                           Option<String>>

  Outputs:
    dispatch_actions     BTreeMap<String,   — per-category dispatch
                           Vec<DispatchAction>>  action tables
```

`DispatchAction` records carry the token variant name, the rule label it
dispatches to, the rule category, and an initial weight derived from rule
priority and overlap count. These become the transition weights in the
prediction WFST.

### Step 6b — build_prediction_wfsts

```
  Inputs:
    category_names       &[String]
    first_sets           BTreeMap<String, TokenSet>
    overlaps             BTreeMap<...>
    dispatch_actions     BTreeMap<String, Vec<DispatchAction>>

  Outputs:
    prediction_wfsts     BTreeMap<String,   — one PredictionWfst per
                           PredictionWfst>    category
```

Each `PredictionWfst` is a small DFA where arcs are token variants and
arc weights are `TropicalWeight` values derived from the dispatch action
table. The initial state represents the start of a prefix; each arc
transitions to a state corresponding to one or more rules that could match
that token prefix.

### Step 6c — apply beam width

```
  Inputs:
    bundle.beam_width    BeamWidthConfig    — Disabled | Explicit(f64) | Auto
    prediction_wfsts     (mutable)

  Effect:
    For each PredictionWfst: wfst.set_beam_width(Some(TropicalWeight))
    if BeamWidthConfig is not Disabled.
```

Beam pruning discards prediction paths whose total cost exceeds
`beam_width` times the cost of the best surviving path. `Auto` mode
requires `wfst-log` and a `log_semiring_model_path` option.

### Step 6d — TokenIdMap::from_names

```
  Inputs:
    all tokens from FIRST sets   Vec<String>
    all tokens from FOLLOW sets  Vec<String>
    structural tokens            "Eof", "RParen", "RBrace", "RBracket",
                                 "Semi", "Comma"

  Outputs:
    token_id_map         TokenIdMap         — shared across recovery WFSTs
```

Tokens are collected, sorted, and deduplicated before being assigned
compact `u16` IDs. Sorting ensures deterministic ID assignment across
incremental recompiles.

### Step 6e — build_recovery_wfsts

```
  Inputs:
    category_names       &[String]
    follow_sets          BTreeMap<String, TokenSet>
    grammar_terminals    BTreeSet<String>   — raw terminal strings from
                                              the grammar + structural delims
    token_id_map         &TokenIdMap

  Outputs:
    recovery_wfsts       Vec<RecoveryWfst>  — one per category
```

Each `RecoveryWfst` encodes three classes of repair actions for every
token in the grammar:

- **Skip** — advance the input pointer past an unexpected token (cost:
  `costs::SKIP`).
- **Delete** — remove a token from the expected stream (cost:
  `costs::DELETE`).
- **Substitute** — replace an unexpected token with the nearest sync
  token in the FOLLOW set (cost: `costs::SUBSTITUTE`).

Viterbi over the recovery WFST finds the minimum-cost repair sequence for
a given error position.

---

## 5. Data Bundles Annotated

The diagram below shows the data bundles that exist at each stage of
the pipeline together with the WFST-specific fields added by each step.

```
  LanguageSpec
  (rules, types, beam_width, dispatch_strategy)
         │
         ▼ extract_from_spec()
  ┌─────────────────────────────────────────────────┐
  │  LexerBundle                                    │
  │  { grammar_rules, type_infos, has_binders,      │
  │    category_names }                             │
  └─────────────────────────────────────────────────┘
  ┌─────────────────────────────────────────────────┐
  │  ParserBundle                                   │
  │  { categories, rule_infos, rd_rules,            │
  │    cross_rules, cast_rules, bp_table,           │
  │    follow_inputs, has_binders,                  │
  │    dispatch_strategy,        ← DispatchStrategy │
  │    beam_width }              ← BeamWidthConfig  │
  └─────────────────────────────────────────────────┘
         │
         ▼ compute_first_sets() / compute_follow_sets_from_inputs()
  { first_sets, follow_sets, overlaps }    ← grammar analysis output
         │
         ▼ DispatchStrategy::resolve()
  use_wfst: bool               ← gate for WFST construction
         │
         ▼ [wfst] build_dispatch_action_tables()
  dispatch_actions             ← token→rule weight tables
         │
         ▼ [wfst] build_prediction_wfsts()
  prediction_wfsts             ← BTreeMap<category, PredictionWfst>
         │
         ▼ [wfst] TokenIdMap::from_names()
  token_id_map                 ← compact u16 token identifiers
         │
         ▼ [wfst] build_recovery_wfsts()
  recovery_wfsts               ← Vec<RecoveryWfst>
         │
         ▼ codegen (write_* functions)
  ┌──────────────────────────────────────────────────────────────────────┐
  │  Generated parser code (String)                                      │
  │                                                                      │
  │  • RD prefix handlers      ← write_rd_handler() × N                 │
  │  • Trampolined parsers      ← write_trampolined_parser()             │
  │      ↳ prediction_wfst injected into TrampolineConfig per category   │
  │  • Cross-cat dispatch       ← write_category_dispatch_weighted()     │
  │      (or static fallback)     [wfst] weight-ordered match arms       │
  │  • Sync predicates          ← generate_sync_predicate()              │
  │  • WFST recovery fns        ← generate_wfst_recovery_fn()    [wfst]  │
  │  • Recovering parsers       ← write_trampolined_parser_              │
  │                               recovering_wfst()               [wfst]  │
  └──────────────────────────────────────────────────────────────────────┘
```

---

## 6. Runtime Data Flow

Sprints 1–4 of the WFST integration plan completed the full runtime
wiring. In addition to the compile-time dispatch arm reordering described
in earlier sections, the pipeline now **embeds WFST data structures as
static arrays** in the generated parser code, enabling runtime prediction
and recovery.

### 6.1 CSR Static Embedding (Prediction)

`emit_prediction_wfst_static()` in `pipeline.rs` serializes each
`PredictionWfst` into **Compressed Sparse Row (CSR)** format:

```rust
// Generated code (under #[cfg(feature = "wfst")])
static WFST_TRANSITIONS_Cat: &[(u16, u32, f64)] = &[
    // (token_id, target_state, weight)
    (0, 1, 0.0), (1, 1, 0.5), (2, 1, 2.0), ...
];
static WFST_STATE_OFFSETS_Cat: &[(usize, usize, bool, f64)] = &[
    // (trans_start, trans_count, is_final, final_weight)
    (0, 3, false, f64::INFINITY), (3, 0, true, 0.0), ...
];
static WFST_TOKEN_NAMES_Cat: &[&str] = &["Plus", "Ident", "Var", ...];
static WFST_BEAM_WIDTH_Cat: Option<f64> = Some(1.5);

static PREDICTION_Cat: LazyLock<PredictionWfst> = LazyLock::new(|| {
    PredictionWfst::from_flat(
        "Cat",
        WFST_STATE_OFFSETS_Cat,
        WFST_TRANSITIONS_Cat,
        WFST_TOKEN_NAMES_Cat,
        WFST_BEAM_WIDTH_Cat,
    )
});
```

The `LazyLock` ensures zero-cost initialization until first use, then
process-lifetime persistence. The CSR format is compact: one contiguous
`&[(u16, u32, f64)]` for all transitions, with per-state offset/count
pairs for random access.

### 6.2 Static Embedding (Recovery)

`emit_recovery_wfst_static()` serializes each `RecoveryWfst` as static
arrays of sync token IDs and their sources:

```rust
static RECOVERY_SYNC_TOKENS_Cat: &[u16] = &[0, 3, 7, ...];
static RECOVERY_SYNC_SOURCES_Cat: &[(u16, u8)] = &[(0, 0), (3, 1), ...];
static RECOVERY_TOKEN_NAMES_Cat: &[&str] = &["Eof", "Semi", "RParen", ...];
```

These are reconstructed via `RecoveryWfst::from_flat()` at runtime.

### 6.3 Runtime Prediction Path

```
  Generated parser (runtime)
       │
       ▼
  PREDICTION_Cat.predict(&token_variant)
       │
       ▼
  Vec<WeightedAction>  (sorted by ascending weight)
       │
       ▼
  Try-in-order dispatch: first action = fast path (no save/restore),
  subsequent actions = save pos, try, restore on failure
```

### 6.4 Runtime Recovery Path

The generated `wfst_recover_Cat()` function now accepts full context:

```rust
fn wfst_recover_Cat<'a>(
    tokens: &[(Token<'a>, Span)],
    pos: &mut usize,
    depth: usize,
    binding_power: u8,
    open_parens: u16,
    open_braces: u16,
    open_brackets: u16,
) -> bool
```

Bracket balance is estimated by scanning tokens consumed so far. All four
repair strategies (skip, delete, insert, substitute) are evaluated with
3-tier context multipliers, and the minimum-cost repair is applied.

---

## 7. Codegen Outputs

This section describes each piece of WFST-specific code that appears in
the generated parser source.

### 7.1 Weighted Prefix Dispatch Comment

`generate_weighted_dispatch()` in `wfst.rs` is called from
`write_prefix_match_arms()` in `trampoline.rs` when a `PredictionWfst`
is present in the `TrampolineConfig`. It emits a comment block above the
Pratt prefix `match` listing each predicted rule with its weight:

```rust
// wfst prediction: ["LetExpr"(0.0), "CallExpr"(1.0), "LitExpr"(2.0)]
```

This comment is informational; the actual ordering is applied by sorting
the `ident_lookahead` handlers by WFST weight before emitting their
`match` arms.

### 7.2 Weighted Cross-Category Dispatch

`write_category_dispatch_weighted()` in `dispatch.rs` emits a `match`
block for cross-category dispatch where arms are ordered from lowest
WFST weight (highest priority) to highest. This replaces the unweighted
`write_category_dispatch()` function which orders arms by FIRST-set
insertion.

### 7.3 WFST Recovery Function

`generate_wfst_recovery_fn()` in `pipeline.rs` emits a function with
the signature:

```rust
fn wfst_recover_Cat<'a>(
    tokens: &[(Token<'a>, Span)],
    pos: &mut usize,
    depth: usize,
    binding_power: u8,
    open_parens: u16,
    open_braces: u16,
    open_brackets: u16,
) -> bool
```

The body evaluates all four repair strategies (skip-to-sync, delete,
insert, substitute) with full 3-tier context multipliers:

- **Tier 1** (frame context): depth and binding power adjust skip/insert
  multipliers.
- **Tier 2** (bracket balance): unmatched brackets get a 0.3× insert
  multiplier for the matching closer.
- **Tier 3** (parse simulation): simulated continuation validates the
  repair leads to a plausible parse state.

The minimum-cost repair is applied and the function returns `true` if
recovery succeeded (pos was advanced to a sync point).

### 7.4 WFST-Recovering Trampoline Entry

`write_trampolined_parser_recovering_wfst()` in `pipeline.rs` emits a
wrapper around the fail-fast trampoline parser:

```rust
pub fn parse_Cat_recovering<'a>(
    tokens: &'a [Token<'a>],
    pos: usize,
) -> Result<(Cat, usize), ParseError<'a>>
```

This wrapper catches `ParseError`, invokes `recover_Cat()`, applies the
repair actions (advancing `pos` and skipping tokens as instructed), and
retries parsing. The non-recovering path is zero-overhead: when parsing
succeeds the recovery function is never called.

---

## 8. Debugging the Pipeline

Two environment variables enable inspection of intermediate pipeline
outputs without modifying source code.

### PRATTAIL_DUMP_EBNF

```
PRATTAIL_DUMP_EBNF=1 cargo build
PRATTAIL_DUMP_EBNF=/tmp/dump cargo build
```

When set to `1`, the EBNF representation of the grammar is written to
`./prattail-ebnf-<language>.txt` in the current directory. When set to a
path, that path is used as the output directory. The EBNF dump is produced
before WFST construction, so it reflects the grammar as seen by the
pipeline regardless of feature flags.

### PRATTAIL_DUMP_PARSER

```
PRATTAIL_DUMP_PARSER=1 cargo build
PRATTAIL_DUMP_PARSER=/tmp/dump cargo build
```

When set, the full generated parser Rust source is written to
`prattail-parser-<categories>.rs`. This file includes the WFST-generated
comments, weighted dispatch arms, recovery functions, and recovering
trampoline entries when the `wfst` feature is active. Diff two dumps
(with and without `--features wfst`) to see exactly what the WFST
subsystem adds.

---

## 9. Source Map

The following table maps each concept in this document to its primary
source location.

| Concept | File | Line Range |
|---------|------|-----------|
| `PipelineState` state machine | `pipeline.rs` | ~83–131 |
| `run_pipeline()` entry point | `pipeline.rs` | ~143–174 |
| `generate_parser_code()` | `pipeline.rs` | ~429–857 |
| `DispatchStrategy` enum + `resolve()` | `lib.rs` | ~140–201 |
| WFST construction block | `pipeline.rs` | ~504–598 |
| `build_dispatch_action_tables()` | `prediction.rs` | ~1055–end |
| `build_prediction_wfsts()` | `wfst.rs` | ~294–386 |
| `generate_weighted_dispatch()` | `wfst.rs` | ~387–448 |
| Beam width application | `pipeline.rs` | ~537–543 |
| `TokenIdMap::from_names()` | `token_id.rs` | ~42–51 |
| `build_recovery_wfsts()` | `recovery.rs` | ~487–540 |
| `write_category_dispatch_weighted()` | `dispatch.rs` | ~212–end |
| Weighted ident-lookahead sort | `trampoline.rs` | ~948–973 |
| `emit_prediction_wfst_static()` | `pipeline.rs` | (wfst-gated) |
| `emit_recovery_wfst_static()` | `pipeline.rs` | (wfst-gated) |
| `generate_wfst_recovery_fn()` | `pipeline.rs` | (wfst-gated) |
| `write_trampolined_parser_recovering_wfst()` | `pipeline.rs` | (wfst-gated) |
| `PredictionWfst::from_flat()` | `wfst.rs` | (wfst-gated) |
| `PredictionWfst::with_trained_weights()` | `wfst.rs` | (wfst-log-gated) |
| `RecoveryWfst::from_flat()` | `recovery.rs` | (wfst-gated) |
| `ParseSimulator::from_flat()` | `recovery.rs` | (wfst-gated) |
| `TrainedModel::from_embedded()` | `training.rs` | (wfst-log-gated) |
| `PRATTAIL_DUMP_EBNF` handler | `pipeline.rs` | ~158–162 |
| `PRATTAIL_DUMP_PARSER` handler | `pipeline.rs` | ~847–855 |

---

## Cross-References

- Module inventory and dependency graph: see
  [module-map.md](module-map.md) (this directory).
- `PredictionWfst` construction details: see
  [../design/prediction.md](../design/prediction.md).
- `RecoveryWfst` edit-cost encoding: see
  [../design/error-recovery.md](../design/error-recovery.md).
- Beam width DSL option: see
  [../usage/dsl-configuration.md](../usage/dsl-configuration.md).
- Overall pipeline overview: see
  [../../../design/architecture-overview.md](../../../design/architecture-overview.md).
- Trampoline parser architecture: see
  [../../../architecture/generated-code-anatomy.md](../../../architecture/generated-code-anatomy.md).
