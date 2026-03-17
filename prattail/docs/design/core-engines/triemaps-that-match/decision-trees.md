# Parse Dispatch via PathMap Decision Trees

PraTTaIL uses PathMap tries as **decision trees** for parse dispatch. Each syntactic category gets a trie mapping byte-encoded token prefixes to parse rules, replacing seven ad-hoc dispatch optimizations with a single trie-based mechanism.

**Prerequisites:** [Foundations](foundations.md), [PathMap Overview](pathmap-overview.md)

---

## 1. The Dispatch Problem

When the parser encounters a token, it must decide which parse rule to attempt. There are 8 categories of dispatch sites:

| Category | Example | Dispatch strategy |
|----------|---------|-------------------|
| Terminal-first RD rules | `"if" Proc "then" Proc` | Trie lookup on first token |
| Cross-category rules | `Proc "+" Proc` | FIRST set of source category + operator token |
| Cast rules | `Proc` embedded in `Expr` | Unique FIRST tokens of source vs. target |
| Unary prefix rules | `"-" Proc` | Prefix BP table (separate) |
| Collection rules | `"{" Proc* "}"` | Dedicated paths (not in trie) |
| Variable capture | `x` (an Ident) | Fallback after trie miss |
| Grouping rules | `"(" Proc ")"` | Dedicated grouping path |
| NT-first rules | `Proc "+" Proc` | Infix dispatch (separate) |

The decision tree handles the first three categories. The others are handled by specialized parser paths that complement the trie.

---

## 2. Token Encoding Scheme

Every dispatch token is encoded as a single byte in the range `[0x00, 0xC1]`:

```text
0x00..0x7F  Terminal token IDs (from TokenIdMap; max ~100 typical)
0x80        IDENT_CAPTURE — consumes exactly one Ident token
0x81        BINDER_CAPTURE — consumes exactly one Ident (binding position)
0x82..0xBF  NonTerminal category IDs (0x82 + category_index)
0xC0        OPTIONAL_START marker
0xC1        OPTIONAL_END marker
```

This encoding is distinct from the De Bruijn encoding used in `pattern_codec.rs` (which uses the same byte ranges for different purposes). The decision tree encoding maps token types to bytes for trie indexing:

| Byte range | Purpose | Constants |
|-----------|---------|-----------|
| `0x00-0x7F` | Terminal token variant IDs | From `TokenIdMap` |
| `0x80` | Ident capture position | `IDENT_CAPTURE` |
| `0x81` | Binder capture position | `BINDER_CAPTURE` |
| `0x82-0xBF` | Nonterminal category IDs | `NT_BASE + index` |
| `0xC0` | Optional group start | `OPTIONAL_START` |
| `0xC1` | Optional group end | `OPTIONAL_END` |

---

## 3. Trie Construction

### Pattern Elements

Before byte encoding, each parse rule is decomposed into typed `PatternElement` values (`decision_tree.rs:66-79`):

```rust
pub enum PatternElement {
    Terminal { variant: String, id: u8 },
    IdentCapture { param_name: String },
    BinderCapture { param_name: String },
    NonTerminal { category: String, category_id: u8 },
    OptionalStart,
    OptionalEnd,
}
```

### Construction Pipeline

```text
RD Rules ──► pattern_from_rd_rule() ──► Vec<PatternElement>
                                              │
                                              ▼
                                    encode_terminal_prefix()
                                              │
                                              ▼
                                  (prefix_bytes, nt_boundary_info)
                                              │
                                              ▼
                                    PathMap::insert(prefix_bytes, action)
```

1. `pattern_from_rd_rule()` converts each `RDRuleInfo` into `Vec<PatternElement>`
2. `encode_terminal_prefix()` encodes the terminal prefix as bytes, stopping at the first nonterminal boundary
3. The byte prefix and a `DecisionAction::Commit` are inserted into the category's PathMap
4. If a nonterminal boundary was encountered, a continuation segment is created

### Cross-Category and Cast Rules

Cross-category rules (e.g., `Proc "+" Proc → Expr`) are inserted by expanding the source category's FIRST set and combining with the operator token:

```text
For rule: Proc "+" Proc → Expr
  FIRST(Proc) = {If, Let, Int, ...}
  Inserted paths: [If, +], [Let, +], [Int, +], ... → Commit(rule)
```

Cast rules insert under the unique tokens in the source FIRST set that are not in the target FIRST set.

---

## 4. Segment Splitting at Nonterminal Boundaries

When a pattern contains a nonterminal (e.g., `"if" Proc "then" Proc`), the trie is **split into segments**:

```text
Segment 0 (terminal prefix):     ["if"] → NonterminalBoundary
Segment 1 (after first NT):      ["then"] → NonterminalBoundary
Segment 2 (after second NT):     ["else"] → Commit(If)  or  ε → Commit(IfThen)
```

The `CategoryDecisionTree` stores these as a vector of `PathMap<DecisionAction>`:

```rust
pub struct CategoryDecisionTree {
    pub category: String,
    pub segments: Vec<PathMap<DecisionAction>>,  // segments[0] = root
    pub stats: TreeStats,
}
```

### Nonterminal Boundaries

At a nonterminal boundary, the parser must:
1. Parse the nonterminal category (recursively)
2. Return to the continuation segment
3. Dispatch on the next token using the continuation trie

The `NTBoundaryInfo` records what comes after the nonterminal:

```rust
pub struct NTBoundaryInfo {
    pub category: String,
    pub category_id: u8,
    pub remaining_pattern: Vec<PatternElement>,
    pub position: usize,
}
```

### CD02: Safe Segment Merging

When all continuation suffixes after a nonterminal boundary have pairwise disjoint FIRST sets, the parser can skip one level of nonterminal parsing indirection. This is the CD02 optimization (`decision_tree.rs:779-800`).

---

## 5. DecisionAction Lattice

The `DecisionAction` enum is the value type stored at trie leaves:

```rust
pub enum DecisionAction {
    Commit { rule_label: String, category: String, weight: f64 },
    Ambiguous { candidates: Vec<AmbiguousCandidate> },
    NonterminalBoundary { options: Vec<NTOption> },
}
```

### Lattice Semantics

The lattice on `DecisionAction` (`decision_tree.rs:139-227`) models grammar composition:

| Operation | Effect |
|-----------|--------|
| `Commit ⊔ Commit` | → `Ambiguous` (two rules compete at same dispatch point) |
| `Ambiguous ⊔ X` | Extend candidate list |
| `Commit ⊓ Commit` | → `Commit` if same rule, `None` if different |
| `Ambiguous ⊓ X` | Keep only shared rule labels |
| `X ∖ Y` | Remove rules in Y from X |

This has a natural lattice interpretation:

```text
                  ⊤ (all rules)
                 / | \
          Ambiguous{A,B}  Ambiguous{B,C}  ...
            / | \
    Commit(A) Commit(B) Commit(C)  ...
                 \  |  /
                  ⊥ (None)
```

---

## 6. Dispatch Strategy Query

The primary consumer of decision trees is the trampoline parser. It queries the trie via `dispatch_strategy()` (`decision_tree.rs:2806`), which returns one of four strategies:

```rust
pub enum DispatchStrategy {
    NotPresent,                           // No rule dispatches on this token
    Singleton { rule_label: String },     // Direct arm (no ambiguity)
    DisjointSuffix {                      // Deterministic multi-arm (A1+G1)
        shared_prefix_len: usize,
        shared_terminals: Vec<u8>,
        suffix_map: BTreeMap<String, String>,  // suffix_token → rule_label
    },
    NfaTryAll {                           // Must try all candidates
        rule_labels: Vec<String>,
        shared_prefix_len: usize,
        shared_terminals: Vec<u8>,
        live_rules_context: Option<HashMap<String, ContextWeight>>,
    },
}
```

### Strategy Selection

```text
                     ┌─ 0 entries ────► NotPresent
                     │
dispatch_strategy() ─┤─ 1 entry, Commit ────► Singleton
                     │
                     ├─ 1 entry, Ambiguous ──► NfaTryAll
                     │
                     └─ N entries ──┬─ all suffixes disjoint ──► DisjointSuffix
                                    └─ some overlap ───────────► NfaTryAll
```

### Subsumption of Ad-Hoc Optimizations

The decision tree subsumes 7 prior optimizations with a single mechanism:

| Prior optimization | Description | Decision tree equivalent |
|--------------------|-------------|------------------------|
| A1 left-factoring | Group rules by first token | Trie root branching |
| B1 two-token lookahead | Disambiguate by second token | Trie depth ≥ 2 |
| G1 Phase 1 | Compute shared terminal prefix | Single-child chains |
| G1 Phase 2 | Suffix disjointness check | Disjoint children after prefix |
| G1 Phase 3 | Save/restore elimination | Deterministic trie nodes |
| G1 Phase 4 | `first_of_rd_suffix()` FIRST sets | NT boundary FIRST expansion |
| CD01 composition analysis | Grammar algebra | `composition_trie_analysis()` |

---

## 7. Statistics and Diagnostics

Each decision tree tracks statistics for adaptive output and lint diagnostics:

```rust
pub struct TreeStats {
    pub total_states: usize,          // All trie nodes
    pub deterministic_nodes: usize,   // Single-child or Commit
    pub ambiguous_nodes: usize,       // Ambiguous action
    pub max_depth: usize,             // Longest root-to-leaf path
    pub min_lookahead: usize,         // Tokens needed for determinism
    pub nonterminal_boundaries: usize, // NT boundary nodes
    pub shared_prefix_savings: usize, // Nodes saved by sharing
    pub total_rules: usize,           // Rules in tree
    pub deterministic_rules: usize,   // Fully deterministic rules
}
```

The ratio `deterministic_rules / total_rules` indicates how effective the trie is at eliminating backtracking. A grammar where all terminal-first rules have unique prefixes achieves 100% determinism.

---

## 8. Output Format

The decision tree is **not** embedded in the generated parser as a runtime trie. Instead, during codegen, the trie's dispatch strategy results are compiled into Rust match arms:

- **Small/medium grammars** (≤256 states): Pattern match arms in `parse_Cat()` functions
- **Large grammars**: Flat dispatch table (future)

Match arms are 4-8x faster per dispatch step than runtime trie walk because:
1. No pointer chasing through trie nodes
2. The Rust compiler optimizes match arms into jump tables
3. No dynamic allocation during dispatch

---

## Key Source Files

| File | Lines | Role |
|------|-------|------|
| `prattail/src/decision_tree.rs` | ~3500 | Trie construction, dispatch strategy, composition, diagnostics |
| `prattail/src/trampoline.rs` | 569-1023 | Dispatch strategy consumption in parser |
| `prattail/src/prediction.rs` | — | FIRST set computation |
| `prattail/src/token_id.rs` | — | Token variant → byte ID mapping |

---

**Next:** [Pattern Indexing](pattern-indexing.md) — how De Bruijn-encoded pattern tries index equations for Ascent optimization.
