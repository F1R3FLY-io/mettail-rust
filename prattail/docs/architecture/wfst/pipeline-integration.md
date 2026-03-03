# WFST Pipeline Integration

**Date:** 2026-02-28

This document explains exactly where the WFST subsystem attaches to the
PraTTaIL compile-time pipeline, what data flows between each stage, and
how WFST construction is wired into every grammar build. All grammars
receive WFST-weighted dispatch — there is no feature gate or strategy
enum controlling whether WFST construction runs. Reading this document
alongside `pipeline.rs` and `prediction.rs` should leave no gaps about
when and why WFST code fires.

---

## Table of Contents

1. [Pipeline State Machine](#1-pipeline-state-machine)
2. [WFST Insertion Point](#2-wfst-insertion-point)
3. [Data Flow Inside generate_parser_code](#3-data-flow-inside-generate_parser_code)
4. [Dead-Rule Detection](#4-dead-rule-detection)
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

`Ready -> Generated` calls `generate_lexer_code()` and
`generate_parser_code()` sequentially, producing two Rust source strings.

`Generated -> Complete` concatenates the two strings and parses them into
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
  ├─ 5. WFST construction ──────────────────────────────────────────────┐
  │       │                                                              │
  │       ├─ a. build_dispatch_action_tables()   (prediction.rs)        │
  │       ├─ b. build_prediction_wfsts()         (wfst.rs)              │
  │       ├─ c. TransducerCascade optimization    (transducer.rs)       │
  │       │       WeightNormalization → DeadStateElimination            │
  │       │       → StateMinimization (→ BeamPruning if configured)     │
  │       ├─ d. TokenIdMap::from_names()         (token_id.rs)          │
  │       ├─ e. build_recovery_wfsts()           (recovery.rs)          │
  │       ├─ f. dead-rule detection              (BooleanWeight)        │
  │       └─ g. NFA spillover detection          (trampoline.rs)       │
  │                                                                      │
  ├─ 6. resolve_dispatch_winners() ← composed dispatch resolution       │
  │                                                                      │
  ├─ 7. write_rd_handler() × N        ← RD prefix handlers              │
  │                                                                      │
  ├─ 8. write_trampolined_parser() ←───── uses prediction_wfst per cat ─┘
  │      per category
  │
  ├─ 9. write_category_dispatch_weighted()  (dispatch.rs)
  │
  ├─ 10. write_recovery_helpers()
  │
  └─ 11. per category:
         ├─ generate_sync_predicate()
         ├─ generate_wfst_recovery_fn()     (pipeline.rs)
         └─ write_trampolined_parser_recovering_wfst()
```

WFST construction always runs. There is no conditional branch or feature
gate — every grammar build produces prediction and recovery WFSTs.

---

## 3. Data Flow Inside generate_parser_code

This section traces every input and output of the WFST construction block
(step 5 from section 2) in the order the code executes.

### Step 5a — build_dispatch_action_tables

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

### Step 5b — build_prediction_wfsts

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

### Step 5c — E1 TransducerCascade optimization

```
  Inputs:
    prediction_wfsts     (mutable)         — per-category PredictionWfst
    bundle.beam_width    BeamWidthConfig    — Disabled | Explicit(f64) | Auto

  Process (pipeline.rs, after build_prediction_wfsts()):
    cascade = TransducerCascade::new()
    cascade.push(WeightNormalization)
    cascade.push(DeadStateElimination)
    cascade.push(StateMinimization)
    if beam_width != Disabled:
        cascade.push(BeamPruning::new(beam_width))
    for each wfst in prediction_wfsts.values_mut():
        cascade.apply(&mut wfst)

  Effect:
    Each PredictionWfst is normalized, pruned of dead states, minimized,
    and optionally beam-pruned in a single composed pass. This replaces
    the previous standalone beam-width application block (B3 minimization)
    with a composable, extensible optimization pipeline.
```

The `TransducerCascade` applies each `OptimizationPass` in sequence.
Passes are idempotent and composable: running the cascade twice produces
the same result as running it once. `BeamPruning` is appended only when
a beam width is configured (`Explicit(f64)` or `Auto`). `Auto` mode
requires `wfst-log` and a `log_semiring_model_path` option.

### Step 5d — TokenIdMap::from_names

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

### Step 5e — build_recovery_wfsts

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

### Step 5f — dead-rule detection (three-tier)

```
  Inputs:
    rule_infos           &[RuleInfo]        — all grammar rules
    categories           &[CategoryInfo]    — category metadata
    first_sets           HashMap<String,    — FIRST set per category
                           FirstSet>
    prediction_wfsts     HashMap<String,    — per-category PredictionWfst
                           PredictionWfst>

  Process (detect_dead_rules() in pipeline.rs:106–207):
    Tier 1: Literal rules — dead if category has no native_type
    Tier 2: Same-cat infix/var — dead if category unreachable
            (fixed-point over cross-cat/cast edges)
    Tier 3: Prefix/cast/cross-cat — dead if no FIRST token
            dispatches to rule via prediction WFST

  Outputs:
    Vec<DeadRuleWarning>   — one per dead rule, three variants:
      LiteralNoNativeType  (tier 1)
      UnreachableCategory  (tier 2)
      WfstUnreachable      (tier 3)
```

Detection runs through the unified lint layer: `lint_w01_dead_rule()` in
`lint.rs:786–832` wraps `detect_dead_rules()` into `LintDiagnostic`
entries with variant-specific hints. Known dead rules in the calculator
grammar: FloatToStr, FloatToBool, StrToBool, IntId, FloatId, BoolId,
StrId, POutput (8 total). RhoCalc has 36 dead rules.

### Step 5g — NFA spillover detection

```
  Inputs:
    rd_rules             &[RDRuleInfo]       — recursive-descent rules
    category_names       &[String]           — all grammar categories
    prediction_wfsts     &BTreeMap<String,   — per-category PredictionWfst
                           PredictionWfst>

  Process:
    categories_needing_nfa_spillover(rd_rules, category_names) identifies
    categories where multiple RD rules share the same dispatch token.
    For each such category, group_rd_by_dispatch_token_pub() enumerates
    the ambiguous token groups. If a PredictionWfst is available,
    nfa_alternative_order() sorts the alternatives by tropical weight
    and emits CountingWeight-based ambiguity diagnostics.

  Outputs:
    nfa_spillover_categories   HashSet<String>  — categories needing NFA
                                                  merged arms and spillover
                                                  thread-locals

  Effects:
    TrampolineConfig.needs_nfa_spillover set for each ambiguous category.
    CountingWeight warnings emitted for equal-weight groups.
    Sets up codegen for NFA merged prefix arms, thread-local declarations,
    and forced-prefix checks in the trampolined parser.
```

NFA spillover detection identifies intra-category rule ambiguity — where
Layer 2's dispatch tables map a single token to multiple rules within one
category. This feeds into the trampoline codegen, which emits NFA merged
prefix arms that try all alternatives via save/restore. See
[../../design/disambiguation/08-nfa-wfst-disambiguation.md](../../design/disambiguation/08-nfa-wfst-disambiguation.md)
for the full Layer 2.5 architecture.

---

## 4. Dead-Rule Detection

After WFST construction, the pipeline performs a three-tier analysis to
identify dead rules.  Detection runs via `detect_dead_rules()` in
`pipeline.rs:106–207` and is surfaced through the unified lint layer
(`lint.rs`, lint ID W01).

```
  Three-Tier Dead-Rule Detection (pipeline.rs:106–207)
  ┌───────────────────────────────────────────────────────────────┐
  │                                                               │
  │  For each rule R:                                             │
  │                                                               │
  │  Tier 1 — Literal rules                                       │
  │    if R.is_literal:                                           │
  │      dead if category has no native_type                      │
  │      (no match arm generated → definitionally unreachable)    │
  │                                                               │
  │  Tier 2 — Same-category infix/var rules                       │
  │    if (R.is_infix && !R.is_cross_category) || R.is_var:      │
  │      dead if category ∉ reachable_categories                  │
  │      (reachable = μX. {C|FIRST(C)≠∅} ∪                       │
  │                        {C|∃cast/cross-cat r: src∈X,tgt=C})   │
  │                                                               │
  │  Tier 3 — Prefix/cast/cross-category rules                    │
  │    dead if no token in FIRST(R.category) dispatches to R      │
  │    via the prediction WFST (implicit BooleanWeight query)     │
  │                                                               │
  │  Data flow:                                                   │
  │    detect_dead_rules() → Vec<DeadRuleWarning>                 │
  │      → lint_w01_dead_rule() → Vec<LintDiagnostic>             │
  │        → emit_diagnostics() → stderr                          │
  │                                                               │
  │  Dead rules are reported but not removed from the grammar     │
  │  (they may be intentionally present for documentation or      │
  │  future use). The diagnostic helps grammar authors identify   │
  │  rules that are shadowed by higher-priority alternatives.     │
  │                                                               │
  └───────────────────────────────────────────────────────────────┘
```

See [../../design/wfst/dead-rule-detection.md](../../design/wfst/dead-rule-detection.md)
for the full design document including correctness properties, complexity
analysis, and practical results.

---

## 5. Data Bundles Annotated

The diagram below shows the data bundles that exist at each stage of
the pipeline together with the WFST-specific fields added by each step.

```
  LanguageSpec
  (rules, types, beam_width)
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
  │    beam_width }              ← BeamWidthConfig  │
  └─────────────────────────────────────────────────┘
         │
         ▼ compute_first_sets() / compute_follow_sets_from_inputs()
  { first_sets, follow_sets, overlaps }    ← grammar analysis output
         │
         ▼ build_dispatch_action_tables()
  dispatch_actions             ← token→rule weight tables
         │
         ▼ build_prediction_wfsts()
  prediction_wfsts             ← BTreeMap<category, PredictionWfst>
         │
         ▼ TransducerCascade::apply() (E1: normalize → dead-state elim → minimize → beam)
  prediction_wfsts             ← optimized in-place
         │
         ▼ TokenIdMap::from_names()
  token_id_map                 ← compact u16 token identifiers
         │
         ▼ build_recovery_wfsts()
  recovery_wfsts               ← Vec<RecoveryWfst>
         │
         ▼ dead-rule detection (three-tier: literal / category-reachability / WFST)
  DeadRuleWarning[]            ← per-rule dead-rule classification
         │
         ▼ lint::run_lints() (23 lints including W01 dead-rule)
  LintDiagnostic[]             ← structured warnings for unreachable rules
         │
         ▼ resolve_dispatch_winners()
  composed_resolutions         ← BTreeMap<(cat, token), (rule, weight)>
         │
         ▼ codegen (write_* functions)
  ┌──────────────────────────────────────────────────────────────────────┐
  │  Generated parser code (String)                                      │
  │                                                                      │
  │  * RD prefix handlers      ← write_rd_handler() × N                 │
  │  * Trampolined parsers      ← write_trampolined_parser()             │
  │      ↳ prediction_wfst injected into TrampolineConfig per category   │
  │  * Cross-cat dispatch       ← write_category_dispatch_weighted()     │
  │      weight-ordered match arms                                       │
  │  * Sync predicates          ← generate_sync_predicate()              │
  │  * WFST recovery fns        ← generate_wfst_recovery_fn()            │
  │  * Recovering parsers       ← write_trampolined_parser_              │
  │                               recovering_wfst()                      │
  └──────────────────────────────────────────────────────────────────────┘
```

---

## 6. Runtime Data Flow

The pipeline **embeds WFST data structures as static arrays** in the
generated parser code, enabling runtime prediction and recovery.

### 6.1 CSR Static Embedding (Prediction)

`emit_prediction_wfst_static()` in `pipeline.rs` serializes each
`PredictionWfst` into **Compressed Sparse Row (CSR)** format:

```rust
// Generated code
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

The generated `wfst_recover_Cat()` function accepts full context:

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
WFST weight (highest priority) to highest. Arms are sorted by the
weight from `build_complete_weight_map()`, which covers all
(category, token) pairs: ambiguous pairs use composed weights,
deterministic pairs use rule specificity weights.

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
- **Tier 2** (bracket balance): unmatched brackets get a 0.3x insert
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

### 7.5 NFA Thread-Locals and Merged Arms

For categories with NFA-ambiguous prefix groups (e.g., Float in Calculator),
the trampoline codegen emits three additional pieces:

**Thread-local declarations** (per category, emitted for all categories):

```rust
thread_local! {
    static NFA_PREFIX_SPILL_FLOAT: Cell<Vec<(Float, usize, f64)>> = Cell::new(Vec::new());
    static NFA_FORCED_PREFIX_FLOAT: Cell<Option<(Float, usize, f64)>> = Cell::new(None);
    static NFA_PRIMARY_WEIGHT_FLOAT: Cell<f64> = Cell::new(0.5);
}
```

**Forced-prefix check** (at top of each category's prefix block):

```rust
{ let forced = NFA_FORCED_PREFIX_FLOAT.with(|cell| cell.take());
  if let Some((forced_val, forced_pos, _)) = forced {
      *pos = forced_pos;
      break 'prefix forced_val;
  } }
```

**NFA merged prefix arm** (for ambiguous token groups only):

```rust
Token::KwFloat => {
    let nfa_saved = *pos;
    // Try each alternative with save/restore, collect results
    // Best → break 'prefix; N-1 → NFA_PREFIX_SPILL
}
```

These are generated by `write_nfa_merged_prefix_arm()` in `trampoline.rs`.
The full architecture is documented in
[../../design/disambiguation/08-nfa-wfst-disambiguation.md](../../design/disambiguation/08-nfa-wfst-disambiguation.md).

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
pipeline.

### PRATTAIL_DUMP_PARSER

```
PRATTAIL_DUMP_PARSER=1 cargo build
PRATTAIL_DUMP_PARSER=/tmp/dump cargo build
```

When set, the full generated parser Rust source is written to
`prattail-parser-<categories>.rs`. This file includes the WFST-generated
comments, weighted dispatch arms, recovery functions, and recovering
trampoline entries. Diff two dumps (with and without `--features wfst-log`)
to see exactly what the `wfst-log` subsystem adds.

---

## 9. Source Map

The following table maps each concept in this document to its primary
source location.

| Concept | File |
|---------|------|
| `PipelineState` state machine | `pipeline.rs` |
| `run_pipeline()` entry point | `pipeline.rs` |
| `generate_parser_code()` | `pipeline.rs` |
| WFST construction block | `pipeline.rs` |
| `build_dispatch_action_tables()` | `prediction.rs` |
| `resolve_dispatch_winners()` | `prediction.rs` |
| `build_prediction_wfsts()` | `wfst.rs` |
| `generate_weighted_dispatch()` | `wfst.rs` |
| E1 TransducerCascade application | `pipeline.rs` + `transducer.rs` |
| `OptimizationPass` trait | `transducer.rs` |
| `TransducerCascade` | `transducer.rs` |
| `WeightNormalization` / `DeadStateElimination` / `StateMinimization` / `BeamPruning` | `transducer.rs` |
| `TokenIdMap::from_names()` | `token_id.rs` |
| `build_recovery_wfsts()` | `recovery.rs` |
| `write_category_dispatch_weighted()` | `dispatch.rs` |
| `build_complete_weight_map()` | `dispatch.rs` / `prediction.rs` |
| Weighted ident-lookahead sort | `trampoline.rs` |
| `emit_prediction_wfst_static()` | `pipeline.rs` |
| `emit_recovery_wfst_static()` | `pipeline.rs` |
| `generate_wfst_recovery_fn()` | `pipeline.rs` |
| `write_trampolined_parser_recovering_wfst()` | `pipeline.rs` |
| `PredictionWfst::from_flat()` | `wfst.rs` |
| `PredictionWfst::with_trained_weights()` | `wfst.rs` (wfst-log) |
| `RecoveryWfst::from_flat()` | `recovery.rs` |
| `ParseSimulator::from_flat()` | `recovery.rs` |
| `TrainedModel::from_embedded()` | `training.rs` (wfst-log) |
| `RepairAction::edit_cost()` | `recovery.rs` |
| `detect_dead_rules()` (three-tier) | `pipeline.rs` |
| `DeadRuleWarning` enum | `pipeline.rs` |
| `lint_w01_dead_rule()` | `lint.rs` |
| `run_lints()` (23 lints) | `lint.rs` |
| NFA spillover detection | `pipeline.rs` + `trampoline.rs` |
| `categories_needing_nfa_spillover()` | `trampoline.rs` |
| `group_rd_by_dispatch_token()` | `trampoline.rs` |
| `write_nfa_merged_prefix_arm()` | `trampoline.rs` |
| `write_nfa_inline_constructor()` | `trampoline.rs` |
| `nfa_alternative_order()` | `wfst.rs` |
| NFA thread-local declarations | `trampoline.rs` (codegen) |
| Forced-prefix check | `trampoline.rs` (codegen) |
| `AMBIGUOUS_WEIGHTS` thread-local | `language.rs` (macros) |
| `PRATTAIL_DUMP_EBNF` handler | `pipeline.rs` |
| `PRATTAIL_DUMP_PARSER` handler | `pipeline.rs` |

---

## Cross-References

- Module inventory and dependency graph: see
  [module-map.md](module-map.md) (this directory).
- Semiring axioms and instances: see
  [../../theory/wfst/semirings.md](../../theory/wfst/semirings.md).
- Viterbi algorithm and forward-backward algorithm: see
  [../../theory/wfst/viterbi-and-forward-backward.md](../../theory/wfst/viterbi-and-forward-backward.md).
- Beam width DSL option: see
  [../../usage/wfst/dsl-configuration.md](../../usage/wfst/dsl-configuration.md).
- Trampoline parser architecture: see
  [../../architecture/generated-code-anatomy.md](../../architecture/generated-code-anatomy.md).
