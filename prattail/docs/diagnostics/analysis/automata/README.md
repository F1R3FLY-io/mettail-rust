# Automata Analysis Diagnostics (V-Category)

**Source:** `prattail/src/vpa.rs`, `prattail/src/tree_automaton.rs`, `prattail/src/lint.rs`
**Feature Gates:** `vpa` (V01, V02), `tree-automata` (V03, V04)

## 1 Overview

The V-category lints report on the **automata-theoretic** properties of a
PraTTaIL grammar, analyzing two complementary aspects of its formal language
structure:

- **Visibly Pushdown Automata (VPA):** Analyze the grammar's delimiter
  structure -- the paired open/close tokens that drive stack-based parsing.
  VPA analysis verifies that the grammar's structured sublanguage (the fragment
  involving matched delimiters) admits efficient, deterministic, zero-backtracking
  parsing.

- **Weighted Tree Automata (WTA):** Analyze the grammar's AST structure --
  the tree shapes that the grammar can produce. WTA analysis verifies that every
  term pattern used in the pipeline is recognized by the automaton and
  identifies high-weight patterns that are candidates for specialization.

```
  Automata Analysis Architecture
  ══════════════════════════════

  ┌──────────────────────────────────────────────────────────┐
  │                     Grammar Rules                       │
  │                                                         │
  │  ┌───────────────────────┐  ┌─────────────────────────┐ │
  │  │   VPA Analysis        │  │   WTA Analysis          │ │
  │  │   (delimiter stack)   │  │   (term tree shapes)    │ │
  │  │                       │  │                         │ │
  │  │  1. Classify tokens   │  │  1. Build ranked        │ │
  │  │     into Sigma_c,     │  │     alphabet from       │ │
  │  │     Sigma_r, Sigma_i  │  │     rule constructors   │ │
  │  │                       │  │                         │ │
  │  │  2. Construct NFA     │  │  2. Build bottom-up     │ │
  │  │     from delimiter    │  │     transitions from    │ │
  │  │     patterns          │  │     rule arities        │ │
  │  │                       │  │                         │ │
  │  │  3. Determinize       │  │  3. Check term          │ │
  │  │     (subset constr.)  │  │     coverage            │ │
  │  │                       │  │                         │ │
  │  │  ┌──────┐ ┌────────┐ │  │  ┌──────┐ ┌──────────┐ │ │
  │  │  │ V01  │ │  V02   │ │  │  │ V03  │ │   V04    │ │ │
  │  │  └──────┘ └────────┘ │  │  └──────┘ └──────────┘ │ │
  │  └───────────────────────┘  └─────────────────────────┘ │
  └──────────────────────────────────────────────────────────┘
```

The two analysis domains are orthogonal: VPA analyzes the **input** structure
(how tokens interact with the parsing stack), while WTA analyzes the **output**
structure (what tree shapes the parser can produce). Together, they provide a
comprehensive formal-language characterization of the grammar.

## 2 Lint Index

| ID | Severity | Name | Feature | Description |
|----|----------|------|---------|-------------|
| [V01](V01-vpa-determinizable.md) | Note | vpa-determinizable | `vpa` | Grammar's structured sublanguage admits deterministic VPA |
| [V02](V02-vpa-alphabet-mismatch.md) | Warning | vpa-alphabet-mismatch | `vpa` | Token classified as both call and return delimiter |
| [V03](V03-wta-unrecognized-term.md) | Warning | wta-unrecognized-term | `tree-automata` | Term pattern not in regular tree language |
| [V04](V04-wta-hot-path.md) | Note | wta-hot-path | `tree-automata` | Frequently weighted term pattern (specialization candidate) |

## 3 Activation Status

The V-category lints are split across two independent feature gates:

### VPA lints (V01, V02)

```toml
[dependencies]
prattail = { version = "...", features = ["vpa"] }
```

When the `vpa` feature is enabled, the pipeline runs VPA analysis after rule
extraction. The analysis classifies terminal tokens into the VPA three-way
alphabet (Sigma_c, Sigma_r, Sigma_i), constructs a nondeterministic VPA,
attempts determinization, and checks for alphabet consistency.

Results are stored in the lint context as `vpa_result: Option<&VpaAnalysis>`.

| Lint | Required context field | Fires when |
|------|----------------------|------------|
| V01 | `vpa_result` | `is_determinizable == true` |
| V02 | `vpa_result` | `alphabet_mismatches` is non-empty |

### WTA lints (V03, V04)

```toml
[dependencies]
prattail = { version = "...", features = ["tree-automata"] }
```

When the `tree-automata` feature is enabled, the pipeline constructs a weighted
tree automaton from the grammar's rule constructors and arities. The WTA's
regular tree language is compared against term patterns used in the pipeline,
and transition weights are aggregated to identify hot paths.

Results are stored in the lint context as `wta_result: Option<&WtaAnalysis>`.

| Lint | Required context field | Fires when |
|------|----------------------|------------|
| V03 | `wta_result` | `unrecognized_terms` is non-empty |
| V04 | `wta_result` | `hot_paths` is non-empty |

## 4 Theoretical Background

### Visibly Pushdown Languages (VPL)

VPAs were introduced by Alur and Madhusudan (2004) as a subclass of pushdown
automata where the stack action (push, pop, or no-op) is determined solely by
the input symbol. This "visibility" constraint yields strong closure properties
not available for general context-free languages:

| Property | CFL | VPL |
|----------|-----|-----|
| Union | Yes | Yes |
| Intersection | No | Yes |
| Complement | No | Yes |
| Determinization | N/A | Yes (no blowup for well-matched words) |
| Emptiness | PTIME | PTIME |
| Inclusion | Undecidable | EXPTIME-complete |

The key insight for PraTTaIL is that if the grammar's delimiter structure forms
a VPL, then the delimiter-matching phase of parsing can be performed
deterministically with zero backtracking, regardless of the complexity of the
rest of the grammar.

### Weighted Tree Automata

WTAs generalize finite tree automata with semiring-valued weights. A WTA over a
ranked alphabet Sigma and semiring K assigns to each ground term t a weight in K
computed by summing (in K) over all accepting runs, where each run's weight is
the product (in K) of its transition weights.

PraTTaIL uses WTAs for two purposes:

1. **Coverage analysis:** Verify that every term pattern referenced by the
   pipeline is in the regular tree language L(A). Gaps indicate missing rules
   (V03).

2. **Weight distribution:** Aggregate transition weights to identify
   structurally dominant patterns. Hot paths guide specialization and
   optimization (V04).

## 5 Data Types

### VpaAnalysis

```
┌──────────────────────────────────────────────┐
│ VpaAnalysis                                  │
│ ──────────────────────────────────────────── │
│ is_determinizable:    bool                   │
│ alphabet_mismatches:  Vec<String>            │
│ state_count:          usize                  │
└──────────────────────────────────────────────┘
```

### WtaAnalysis

```
┌──────────────────────────────────────────────┐
│ WtaAnalysis                                  │
│ ──────────────────────────────────────────── │
│ unrecognized_terms:   Vec<String>            │
│ hot_paths:            Vec<String>            │
│ state_count:          usize                  │
│ transition_count:     usize                  │
└──────────────────────────────────────────────┘
```

## 6 Related Diagnostic Categories

- **T (TRS Analysis):** [T01--T04](../trs/README.md) -- Term rewriting system
  analysis (confluence and termination). Orthogonal to automata analysis but
  part of the same mathematical analysis framework.
- **G (Grammar Structure):** G01--G10 -- Structural grammar lints. G09
  (unbalanced delimiters) is a precursor to V02 (alphabet mismatch).
- **W (WFST-Specific):** W01--W16 -- WFST prediction lints. Dead rules (W01)
  may correlate with unrecognized WTA terms (V03).
- **D (Decision Tree):** D01--D09 -- Decision tree lints. Hot paths (V04)
  may correlate with high-traffic trie paths (D08 optimization suggestions).
- **S (Safety):** S01--S06 -- Safety verification lints, using model checking
  and automata-theoretic techniques.
