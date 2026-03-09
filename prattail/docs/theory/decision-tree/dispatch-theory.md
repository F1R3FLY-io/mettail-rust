# Dispatch Theory: PathMap Trie for Parse Dispatch

| Metadata | Value                     |
|----------|---------------------------|
| Date     | 2026-03-09                |
| Status   | Reference documentation   |

---

## Table of Contents

- [1 PathMap Trie Theory](#1-pathmap-trie-theory)
- [2 Formal Definition of the Dispatch Problem](#2-formal-definition-of-the-dispatch-problem)
- [3 Commit, Try, and Fallback Semantics](#3-commit-try-and-fallback-semantics)
- [4 Worked Examples](#4-worked-examples)
- [5 Lattice Operations](#5-lattice-operations)
- [6 Connection to CategoryDecisionTree Construction](#6-connection-to-categorydecisiontree-construction)
- [7 Theoretical Foundations](#7-theoretical-foundations)
- [References](#references)

---

## 1 PathMap Trie Theory

### 1.1 Byte Encoding Scheme

PraTTaIL encodes grammar rules as byte sequences for insertion into a PathMap
trie. Each byte position in the sequence corresponds to a syntactic element
in the rule's left-hand-side pattern. The encoding partitions the byte space
`[0x00, 0xFF]` into five regions:

```text
  ┌───────────────────────────────────────────────────────────────────┐
  │ Byte Range      │ Designation        │ Semantics                  │
  ├─────────────────┼────────────────────┼────────────────────────────┤
  │ 0x00 .. 0x7F    │ Terminal token IDs  │ From TokenIdMap; max ~100  │
  │                 │                    │ typical; maps to Token enum│
  │                 │                    │ variants via               │
  │                 │                    │ terminal_to_variant_name() │
  ├─────────────────┼────────────────────┼────────────────────────────┤
  │ 0x80            │ IDENT_CAPTURE      │ Consumes exactly one       │
  │                 │                    │ Token::Ident (binding      │
  │                 │                    │ a variable name)           │
  ├─────────────────┼────────────────────┼────────────────────────────┤
  │ 0x81            │ BINDER_CAPTURE     │ Consumes exactly one       │
  │                 │                    │ Token::Ident (binding      │
  │                 │                    │ a binder name, e.g. ^x)    │
  ├─────────────────┼────────────────────┼────────────────────────────┤
  │ 0x82 .. 0xBF    │ NonTerminal IDs    │ 0x82 + category_index;     │
  │                 │                    │ triggers segment split     │
  ├─────────────────┼────────────────────┼────────────────────────────┤
  │ 0xC0            │ OPTIONAL_START     │ Marks beginning of ?-group │
  │ 0xC1            │ OPTIONAL_END       │ Marks end of ?-group       │
  └─────────────────┴────────────────────┴────────────────────────────┘
```

**Definition 1 (Encoding Function).** Let `encode : PatternElement -> byte` be:

```
  encode(Terminal { variant, id })         = id          (0x00..0x7F)
  encode(IdentCapture { .. })              = 0x80
  encode(BinderCapture { .. })             = 0x81
  encode(NonTerminal { category_id, .. })  = 0x82 + category_id
  encode(OptionalStart)                    = 0xC0
  encode(OptionalEnd)                      = 0xC1
```

**Definition 2 (Terminal Prefix).** For a pattern P = (e_1, e_2, ..., e_n),
the *terminal prefix* is the maximal prefix `encode(e_1), ..., encode(e_k)`
such that none of e_1, ..., e_k is a `NonTerminal`. That is, encoding stops
at the first nonterminal boundary. The function `encode_terminal_prefix()`
implements this, returning both the byte sequence and an optional
`NTBoundaryInfo` describing what follows the boundary.

### 1.2 Trie Structure

A `PathMap<DecisionAction>` is a trie where:
- **Edges** are labeled with bytes from the encoding scheme above.
- **Nodes** may carry a `DecisionAction` value (the node is a *valued* node)
  or be purely internal (no value, only children).
- **Paths** from root to valued nodes correspond to terminal prefixes of
  grammar rules.

The trie supports three algebraic operations (see [Section 5](#5-lattice-operations)):
`join` (merge tries), `meet` (intersect tries), `subtract` (difference).

### 1.3 Segment Splitting at Nonterminal Boundaries

When a rule's pattern contains a nonterminal (e.g., `"if" <Expr> "then" <Expr>`),
the trie cannot directly encode the nonterminal parse as a byte. Instead, the
trie is **split into linked segments**:

```text
  Segment 0 (root):        Segment 1 (continuation after <Expr>):
  ┌─────────┐              ┌──────────┐
  │ "if"    │              │ "then"   │
  │  (0x05) │──NT─boundary─│  (0x12)  │
  │         │              │          │──→ Commit(IfThenElse)
  └─────────┘              └──────────┘
```

**Definition 3 (Segment).** A `CategoryDecisionTree` consists of an ordered
list of `PathMap<DecisionAction>` segments:
- `segments[0]` is the root segment, containing terminal-only prefixes.
- `segments[i]` for i >= 1 are continuation segments, each corresponding to
  the pattern suffix after a nonterminal parse.

The `NTBoundaryRecord` stored in the builder's `nt_boundary_map` links a
root-segment path to its continuation segment index, the nonterminal category,
and the remaining pattern elements.

### 1.4 Rule Insertion

For each rule in a category, the `DecisionTreeBuilder` performs:

1. Convert the rule's `RDSyntaxItem` list to `Vec<PatternElement>` via
   `pattern_from_rd_rule()`.
2. Compute the terminal prefix via `encode_terminal_prefix()`.
3. If the prefix is non-empty, create a `DecisionAction::Commit` and insert
   it into `segments[0]` of the category's tree.
4. If a value already exists at that path (prefix collision), merge via the
   `pjoin` lattice operation (producing `Ambiguous` if labels differ).
5. If a nonterminal boundary was encountered, create a continuation segment
   and insert the remaining suffix pattern into it.

Rules that start with nonterminals (cast rules, ident-lookahead rules) or
that are dead (in `dead_rules` set) are excluded from trie insertion.

---

## 2 Formal Definition of the Dispatch Problem

**Definition 4 (Dispatch Problem).** Given:
- A syntactic category C with rules R_1, ..., R_n
- A token stream s = (t_1, t_2, t_3, ...)
- The encoding function `encode` and the category's decision tree T_C

The *dispatch problem* is to determine:
1. Which rule R_i should the parser attempt?
2. Should it commit (no backtracking) or try multiple alternatives?
3. How many lookahead tokens are needed for the decision?

**Definition 5 (Dispatch Function).** The dispatch function D_C maps a
lookahead token sequence to a dispatch strategy:

```
  D_C : Token* -> DispatchStrategy
```

where `DispatchStrategy` is one of:
- `Singleton { rule_label }` -- exactly one rule matches; commit.
- `DisjointSuffix { shared_prefix_len, suffix_map }` -- multiple rules
  share a terminal prefix but diverge at a disjoint suffix point.
- `NfaTryAll { rule_labels, ... }` -- multiple rules overlap; must try all
  candidates in order (NFA semantics with backtracking).
- `NotPresent` -- no rule dispatches on this token.

**Observation.** The dispatch function is computed at **compile time** from
the decision tree. At runtime, the generated parser contains `match` arms
(or function pointer tables for CD03) that implement D_C directly, with no
trie traversal overhead.

**Definition 6 (Lookahead Depth).** The *minimum lookahead depth* for
category C is:

```
  k_min(C) = max { depth(p) | p is a path in T_C that reaches a leaf }
```

where `depth(p)` is the length of path p. This is the maximum number of
tokens the parser must peek at before making a deterministic dispatch
decision for all rules in C.

For a grammar that is LL(1) for category C, k_min(C) = 1 (all dispatch
decisions are resolved by the first token). The decision tree naturally
handles LL(k) for arbitrary k without a separate LL(k) parse table.

---

## 3 Commit, Try, and Fallback Semantics

The three `DecisionAction` variants encode progressively weaker dispatch
guarantees:

### 3.1 Commit (Deterministic)

```
  DecisionAction::Commit { rule_label, category, weight }
```

**Semantics:** The parser has enough lookahead information to determine that
exactly one rule matches. It commits to parsing rule `rule_label` without
saving a backtrack point.

**Invariant:** At a `Commit` node, the set of rules reachable through any
extension of the current path is a singleton `{ rule_label }`.

**Generated code:**

```rust
Token::KwIf => {
    // COMMIT: deterministic dispatch to IfThenElse
    parse_if_then_else(tokens, pos)
}
```

### 3.2 Ambiguous (Multiple Candidates)

```
  DecisionAction::Ambiguous { candidates: Vec<AmbiguousCandidate> }
```

**Semantics:** Multiple rules remain viable at this trie node. The parser
must use a fallback strategy to determine which rule succeeds:

1. **NFA try-all:** Save position, attempt each candidate in weight order
   (lowest weight = highest priority), restore on failure, try next.
2. **ContextWeight narrowing (H1):** Use 2-token lookahead ContextWeight
   bitmask to prune candidates before trying.
3. **Pratt infix fallback:** If the ambiguity is between an RD prefix rule
   and a Pratt infix operator, the Pratt loop handles disambiguation via
   binding power comparison.

**Weight ordering:** Candidates are ordered by `weight` (TropicalWeight:
lower = more likely). This ensures the most probable parse is attempted
first, minimizing average backtracking.

**Generated code:**

```rust
Token::LParen => {
    // AMBIGUOUS: 3 candidates — try by weight order
    let save = pos;
    // Candidate 1 (weight 0.0): Grouping
    if let Ok(r) = parse_grouping(tokens, pos) { return Ok(r); }
    pos = save;
    // Candidate 2 (weight 0.3): TupleExpr
    if let Ok(r) = parse_tuple(tokens, pos) { return Ok(r); }
    pos = save;
    // Candidate 3 (weight 0.7): FnCall
    if let Ok(r) = parse_fn_call(tokens, pos) { return Ok(r); }
    pos = save;
    return Err(ParseError::no_match("Proc", pos));
}
```

### 3.3 NonterminalBoundary (Continuation)

```
  DecisionAction::NonterminalBoundary { options: Vec<NTOption> }
```

**Semantics:** The parser has consumed all terminal tokens in the prefix and
reached a point where a nonterminal must be parsed. Each `NTOption` specifies:
- The nonterminal category to parse
- FIRST set tokens for the continuation after the nonterminal parse
- The index of the continuation segment to resume in

**Dispatch after NT parse:** After successfully parsing the nonterminal, the
parser peeks at the next token and dispatches into the continuation segment.
If the FIRST sets of all continuations are pairwise disjoint (CD02 safety
condition), the dispatch is deterministic. Otherwise, NFA try-all is used.

---

## 4 Worked Examples

### 4.1 Simple LL(1) Grammar

Consider a category `Expr` with three rules:

```
  LetIn:    "let" <Ident> "=" <Expr> "in" <Expr>
  IfElse:   "if" <Expr> "then" <Expr> "else" <Expr>
  IntLit:   <Integer>
```

**Trie (segment 0):**

```text
            root
          ╱   │    ╲
     0x03    0x05   0x20
    "let"   "if"   Integer
      │       │       │
   Commit  Commit  Commit
   LetIn   IfElse  IntLit
```

All three rules have distinct first tokens. Dispatch is LL(1):
- `D_Expr("let" ...) = Singleton { LetIn }`
- `D_Expr("if" ...)  = Singleton { IfElse }`
- `D_Expr(Integer)   = Singleton { IntLit }`
- `D_Expr(other)     = NotPresent`

`k_min(Expr) = 1`.

### 4.2 Shared Prefix with Disjoint Suffix

Consider two rules sharing the prefix `"for"`:

```
  ForIn:    "for" <Ident> "in" <Expr> "{" <Expr> "}"
  ForAll:   "for" <Ident> "." <Expr>
```

**Trie (segment 0):**

```text
           root
             │
           0x07
          "for"
             │
           0x80
        IDENT_CAPTURE
          ╱       ╲
       0x08       0x09
       "in"        "."
         │           │
      Commit      Commit
      ForIn       ForAll
```

After consuming `"for" <Ident>`, the parser peeks at the next token:
- `"in"` uniquely identifies ForIn
- `"."` uniquely identifies ForAll

This is the `DisjointSuffix` dispatch strategy:
- `D_Expr("for" ...) = DisjointSuffix { shared_prefix_len: 2, suffix_map: {"in": "ForIn", ".": "ForAll"} }`

No backtracking is needed.

### 4.3 Ambiguous Prefix Requiring NFA Try-All

Consider three rules all starting with `"("`:

```
  Grouping:  "(" <Expr> ")"
  TupleLit:  "(" <Expr> "," <Expr> ")"
  UnitExpr:  "(" ")"
```

**Trie (segment 0):**

```text
           root
             │
           0x0A
          "LParen"
             │
        ┌────┴────┐
      0x0B       [other]
    "RParen"       │
        │       Ambiguous
     Commit     {Grouping,
    UnitExpr     TupleLit}
```

After consuming `"("`:
- If the next token is `")"`, commit to `UnitExpr`.
- Otherwise, both `Grouping` and `TupleLit` are viable -- the parser
  cannot distinguish them until it parses `<Expr>` and then checks for
  `","` vs `")"`.

The dispatch strategy for non-RParen tokens is:
- `D_Expr("(" t ...) = NfaTryAll { rule_labels: ["Grouping", "TupleLit"], shared_prefix_len: 0, ... }`

The parser tries `Grouping` first (lower weight), and if it fails (e.g.,
because a comma follows), backtracks and tries `TupleLit`.

### 4.4 Cross-Category Cast Dispatch

Consider category `Proc` with a cast from `Int`:

```
  Cast_IntToProc:  (source: Int) -- cast rule, no explicit syntax
```

The cast rule inserts paths for each token in `FIRST(Int) \ FIRST(Proc)`.
If `Integer` is in `FIRST(Int)` but not `FIRST(Proc)`:

```text
  Proc root
      │
    0x20
  "Integer"
      │
   Commit
  Cast_IntToProc
```

The parser sees `Integer` while parsing `Proc` and knows it must be an
`Int` cast. This is `Singleton { Cast_IntToProc }`.

---

## 5 Lattice Operations

The `DecisionAction` type implements the `Lattice` and `DistributiveLattice`
traits from the PathMap crate, enabling algebraic operations on tries. These
operations lift pointwise from node values to the entire trie structure.

### 5.1 Join (Merge)

**Definition 7 (Join).** For actions a and b:

```
  a `join` b = Ambiguous(candidates(a) `cup` candidates(b))
```

where `candidates` extracts the set of `AmbiguousCandidate` records, treating
`Commit` as a singleton set.

**Special case:** If one operand is `NonterminalBoundary`, the join returns
the other operand unchanged (`AlgebraicResult::Identity`).

**Normalization:** A result with exactly one candidate is collapsed to `Commit`.

**Application:** `join` is used when inserting a new rule into a trie node
that already has a value. The existing `Commit` becomes `Ambiguous` with the
new candidate added.

**Trie-level:** `T_A join T_B` is the trie containing all paths from both
`T_A` and `T_B`, with values merged at shared paths. This corresponds to
composing two grammars: the composed grammar accepts anything that either
source grammar accepts.

### 5.2 Meet (Intersect)

**Definition 8 (Meet).** For actions a and b:

```
  a `meet` b = Ambiguous(candidates(a) `cap` candidates(b))
```

where intersection is computed on rule labels: a candidate survives if its
rule label appears in both `labels(a)` and `labels(b)`.

**Application:** `meet` computes the common sublanguage of two grammars. A
path survives in `T_A meet T_B` only if both tries have a value at that path
with at least one shared rule label.

### 5.3 Subtract (Difference)

**Definition 9 (Subtract).** For actions a and b:

```
  a `subtract` b = Ambiguous(candidates(a) \ { c | c.rule_label `in` labels(b) })
```

**Application:** `subtract` removes rules from one grammar that are already
present in another. Useful for identifying which rules are unique to a
composed language extension.

### 5.4 Properties

The lattice operations satisfy (see [grammar-algebra.md](grammar-algebra.md)
for full proofs):

| Property        | Join (`join`)                  | Meet (`meet`)                  |
|-----------------|-------------------------------|-------------------------------|
| Commutativity   | `a join b = b join a`         | `a meet b = b meet a`         |
| Associativity   | `(a join b) join c = a join (b join c)` | `(a meet b) meet c = a meet (b meet c)` |
| Idempotency     | `a join a = a`                | `a meet a = a`                |
| Absorption      | `a join (a meet b) = a`       | `a meet (a join b) = a`       |
| Distributivity  | `a subtract (a meet b) = a subtract b` | --                   |

**Note:** `NonterminalBoundary` is treated as an algebraic identity for `join`
and `meet`, which means it passes through unchanged. This is sound because
NT boundaries represent structural (not value-level) information that should
not be merged with rule-level dispatch actions.

---

## 6 Connection to CategoryDecisionTree Construction

### 6.1 Builder Algorithm

The `DecisionTreeBuilder` constructs decision trees in three phases:

**Phase 1: RD Rule Insertion** (`insert_rd_rules`)

For each recursive-descent rule R in the category:
1. Skip if R is dead, a collection, has prefix BP, or starts with a nonterminal.
2. Convert R to `Vec<PatternElement>` via `pattern_from_rd_rule()`.
3. Compute terminal prefix and NT boundary info.
4. Insert `Commit(R)` into `segments[0]` at the terminal prefix path.
5. On collision, merge via `pjoin` (producing `Ambiguous`).
6. If an NT boundary exists, create a continuation segment.

**Phase 2: Cross-Category Rule Insertion** (`insert_cross_category_rules`)

For each cross-category rule X (e.g., `Proc::IntAdd` with source `Int`):
1. Compute the operator token byte.
2. For each token in `FIRST(source_category)`, insert a 2-byte path
   `[source_first_token, operator_token]` into the result category's tree.
3. Merge via `pjoin` on collision.

**Phase 3: Cast Rule Insertion** (`insert_cast_rules`)

For each cast rule (e.g., `Int -> Proc`):
1. Compute `FIRST(source) \ FIRST(target)` -- tokens unique to source.
2. For each unique token, insert a 1-byte path `[token]` into the target
   category's tree with a `Commit` action.
3. Merge via `pjoin` on collision (may become `Ambiguous` if target already
   has a rule for that token).

### 6.2 Statistics Computation

After all insertions, `compute_statistics()` traverses each tree and computes:

| Statistic               | Description                                          |
|-------------------------|------------------------------------------------------|
| `total_states`          | Nodes with children or values                        |
| `deterministic_nodes`   | Nodes with `Commit` value or single child            |
| `ambiguous_nodes`       | Nodes with `Ambiguous` value                         |
| `max_depth`             | Longest root-to-leaf path                            |
| `min_lookahead`         | Minimum tokens to resolve all deterministic dispatch |
| `nonterminal_boundaries`| Count of NT boundary points                          |
| `shared_prefix_savings` | States saved vs. per-rule individual tries           |
| `total_rules`           | Rules inserted into this tree                        |
| `deterministic_rules`   | Rules reachable without ambiguity                    |

### 6.3 Dispatch Strategy Derivation

The `dispatch_strategy()` method converts trie structure into a
`DispatchStrategy` for a given dispatch token:

```text
  Input: token_variant (e.g., "KwIf")
         │
         ▼
  Step 1: Look up token byte ID via TokenIdMap
         │
         ▼
  Step 2: Retrieve value at path [token_byte] from segments[0]
         │
         ├──→ No value → NotPresent
         │
         ├──→ Commit { rule_label } → Singleton { rule_label }
         │
         └──→ Ambiguous { candidates }
                │
                ▼
         Step 3: Check children at depth 1
                │
                ├──→ Children exist and all lead to Commit
                │    with pairwise disjoint labels
                │    → DisjointSuffix { suffix_map }
                │
                └──→ Otherwise
                     → NfaTryAll { rule_labels }
```

### 6.4 Post-Construction Refinement

After initial construction, the pipeline applies several refinements:

1. **Trie-informed WFST weight scaling** -- Deeper unique prefixes get lower
   prediction weights (higher confidence); short shared prefixes get higher
   weights. Computed by `compute_weight_adjustments()`.

2. **Trie+WFST dead-rule confirmation** -- Second pass of
   `collect_dead_rule_labels()` with trie reachability cross-validation.
   Rules dead in both WFST and trie are confirmed dead.

3. **NFA spillover pruning** -- Categories marked for NFA spillover may
   have all ambiguous tokens resolved to `DisjointSuffix` by the trie,
   eliminating the need for spillover buffers.

4. **CD02 segment merging** -- `merge_safe_nonterminal_boundaries()` replaces
   NT boundaries with direct token dispatch when continuation suffixes have
   pairwise disjoint FIRST sets.

5. **Dead-prefix recovery weight penalty** -- Dispatch tokens whose entire
   trie subtree leads only to dead rules get increased recovery WFST weights.

---

## 7 Theoretical Foundations

### 7.1 Connection to Tries

The PathMap trie is a standard trie (Fredkin, 1960) over a byte alphabet
Sigma = {0x00, ..., 0xFF}, augmented with lattice-algebraic value operations.
The key insight of the PraTTaIL decision tree is that **parse dispatch over a
finite set of grammar rules is isomorphic to prefix matching in a trie** when
rule patterns are encoded as byte sequences.

**Theorem (Dispatch-Trie Isomorphism).** Let C be a category with rules
R_1, ..., R_n. Let P_i = encode(R_i) be the byte-encoded terminal prefix of
rule R_i. Then the trie T_C with entries `{P_i -> Commit(R_i)}` computes
the correct LL(k) parse table for C, where k = max_i(|P_i|).

*Proof sketch.* The trie lookup `T_C.get(encode(t_1), ..., encode(t_k))` for
a token sequence (t_1, ..., t_k) follows the unique path labeled by the
encoded bytes. If the path reaches a `Commit(R_i)`, then R_i is the unique
rule whose terminal prefix matches the lookahead. If multiple rules share a
prefix (ambiguity), the `pjoin` operation at the collision point produces
`Ambiguous`, which the trie faithfully reports. See
[foundations.md](foundations.md) Theorem 3 for the full proof.

### 7.2 Connection to DFA Minimization

The decision tree bears a structural relationship to DFA minimization
(Hopcroft, 1971). Each trie node corresponds to a DFA state; each byte-labeled
edge corresponds to a DFA transition. Nodes with the same `DecisionAction`
at the same depth are candidates for merging (analogous to state merging in
DFA minimization).

The `shared_prefix_savings` statistic in `TreeStats` measures the state
reduction: it counts how many states were saved by sharing prefixes in the
trie vs. having independent per-rule tries. This is directly analogous to
the state reduction from DFA minimization.

However, the trie is **not** a DFA in the classical sense because:
- It operates on byte-encoded patterns, not character-by-character input.
- Nonterminal boundaries introduce a "pushdown" aspect (segment linking).
- The lattice operations (join, meet, subtract) have no DFA analog.

### 7.3 Connection to Pattern Matching Theory

The dispatch problem is an instance of the **first-match pattern compilation**
problem studied in functional programming (Augustsson, 1985; Maranget, 2008).
Given a set of patterns P_1, ..., P_n and an input, determine which pattern
matches first.

PraTTaIL's trie-based approach corresponds to the **decision tree** strategy
in Maranget's framework:
- Each internal node tests a position in the input (a byte in the encoded
  lookahead sequence).
- Branches correspond to byte values.
- Leaves correspond to matched rules or failure.

The key difference from classical pattern matching compilation is that
PraTTaIL's patterns are **prefixes** of token streams (not full patterns
over a finite depth), and the trie may contain `Ambiguous` leaves where
classical compilation would require backtracking or heuristic splitting.

**Completeness guarantee.** The trie construction is complete: every
non-dead rule in the grammar is either represented in the trie (via its
terminal prefix) or handled by a fallback mechanism:
- Rules starting with nonterminals are dispatched via ident-lookahead or
  infix/postfix Pratt loops.
- Rules with no terminal prefix (e.g., pure ident capture) are handled
  by the Pratt loop's `NullDen` handler.
- Dead rules (confirmed via WFST + trie cross-validation) are excluded.

### 7.4 Complexity

| Operation                    | Time Complexity        | Space Complexity       |
|------------------------------|------------------------|------------------------|
| Rule insertion               | O(|prefix|) per rule   | O(sum of |prefix_i|)   |
| Dispatch lookup (compile)    | O(k) per token         | --                     |
| Join two tries               | O(|T_A| + |T_B|)       | O(|T_A| + |T_B|)       |
| Meet two tries               | O(min(|T_A|, |T_B|))   | O(min(|T_A|, |T_B|))   |
| Statistics computation       | O(|T|)                 | O(1) auxiliary          |
| Dispatch strategy derivation | O(k + |candidates|)    | O(|candidates|)         |

where k is the maximum prefix depth, |T| is the number of trie nodes, and
|candidates| is the number of rules sharing a dispatch token.

At **runtime**, the generated parser contains no trie -- the dispatch is
compiled into `match` arms or function pointer tables, achieving O(1)
dispatch per token (O(log n) for match arms due to binary search, O(1) for
computed-goto CD03).

---

## References

- Fredkin, E. (1960). "Trie memory." Communications of the ACM, 3(9).
- Hopcroft, J.E. (1971). "An n log n algorithm for minimizing states in a finite automaton." Theory of Machines and Computations, Academic Press.
- Augustsson, L. (1985). "Compiling pattern matching." Functional Programming Languages and Computer Architecture, Springer.
- Maranget, L. (2008). "Compiling pattern matching to good decision trees." ML Workshop 2008.
- Aho, A.V., Lam, M.S., Sethi, R., Ullman, J.D. (2006). "Compilers: Principles, Techniques, and Tools." 2nd edition, Pearson.
- Adams, M.D. and Might, M. (2014). "Parsing with derivatives: a functional pearl." ICFP 2014.

---

*Source files:*
[`prattail/src/decision_tree.rs`](../../src/decision_tree.rs),
[`prattail/docs/design/decision-tree/overview.md`](../design/decision-tree/overview.md),
[`prattail/docs/theory/decision-tree/foundations.md`](foundations.md),
[`prattail/docs/theory/decision-tree/grammar-algebra.md`](grammar-algebra.md)
