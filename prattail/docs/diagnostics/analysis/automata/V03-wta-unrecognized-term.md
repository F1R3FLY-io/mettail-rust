# V03: wta-unrecognized-term

**Severity:** Warning
**Category:** analysis/automata
**Feature Gate:** `tree-automata`

## Description

Detects term patterns in the grammar's AST that are **not recognized** by the
weighted tree automaton (WTA) constructed from the grammar's rules. A WTA
defines a regular tree language -- the set of all well-formed AST shapes that
the grammar can produce. When a term pattern falls outside this language, it
means either the grammar is missing a rule or transition to handle that
structural case, or the term pattern is dead code that can never be constructed
by the parser.

A **weighted tree automaton** is a tuple A = (Q, Sigma, Delta, F, K) where:

- Q is a finite set of states,
- Sigma is a ranked alphabet (constructors with fixed arities),
- Delta subset of Q^k x Sigma_k x Q is a set of transitions for each k-ary
  symbol,
- F subset of Q is the set of accepting (final) states,
- K is a semiring of weights (e.g., TropicalWeight for shortest-path).

A transition (q₁, ..., q_k, f, q) means: if the k children of a node labeled
f are in states q₁, ..., q_k respectively, then the node can be assigned
state q. The tree language L(A) is the set of all ground terms t such that
the bottom-up state assignment reaches a final state at the root.

```
  Bottom-Up State Assignment
  ══════════════════════════

         Add              state assignment:
        / \
       /   \              Num(3):   q_num    (leaf rule)
     Mul    Num(3)        Num(5):   q_num    (leaf rule)
    / \       |           Num(7):   q_num    (leaf rule)
   /   \    q_num         Mul(q_num, q_num): q_expr  (binary rule)
 Num(5) Num(7)            Add(q_expr, q_num): q_expr (binary rule)
  |       |
q_num   q_num             root state: q_expr in F  =>  accepted

  But what about:

         Div              Div(q_expr, q_num): ???
        / \
       /   \              no transition for Div!
     Num(5) Num(3)        term not in L(A)  =>  V03 fires
      |       |
    q_num   q_num
```

In the diagram, the WTA has transitions for `Add`, `Mul`, and `Num` but not
for `Div`. When the analysis encounters a term pattern using `Div`, it cannot
assign a state to the `Div` node, and the term falls outside the regular tree
language. V03 reports this as an unrecognized term pattern.

## Trigger Conditions

All of the following must hold:

- The `tree-automata` feature is enabled at compile time.
- A `WtaAnalysis` result is available in the lint context.
- The `unrecognized_terms` list contains at least one entry (at least one
  term pattern was found that the WTA does not accept).

One V03 diagnostic is emitted per unrecognized term pattern.

## Example

### Grammar

```rust
language! {
    name: CalcLang,
    types {
        ![i32] as Expr
    },
    terms {
        Num . |- <int> : Expr;
        Add . a:Expr, b:Expr |- a "+" b : Expr ![a + b] fold;
        Mul . a:Expr, b:Expr |- a "*" b : Expr ![a * b] fold;
        Neg . a:Expr |- "-" a : Expr ![{ -a }];

        // Suppose a downstream analysis or transformation references
        // a Div pattern, but no rule produces Div terms:
        //   pattern: Div(Expr, Expr)  -- not in L(WTA)
    },
}
```

### Output

```
warning[V03] (CalcLang): term pattern `Div(Expr, Expr)` not in regular tree language
  = hint: add a rule or transition to recognize this term pattern
```

## Resolution

1. **Add a grammar rule.** If the term pattern represents a valid syntactic
   form that should be parseable, add a corresponding production rule. For the
   example, adding a `Div` rule makes the pattern recognizable:
   ```
   Div . a:Expr, b:Expr |- a "/" b : Expr ![a / b] fold;
   ```

2. **Add a WTA transition.** If the term pattern arises from a transformation
   or optimization pass (not directly from parsing), add an explicit transition
   to the WTA that assigns a state to the unrecognized constructor. This
   extends the regular tree language without modifying the grammar's surface
   syntax.

3. **Remove the dead pattern.** If the term pattern is referenced in downstream
   code (e.g., a pattern match in a semantic analysis pass) but no grammar rule
   can produce it, the downstream reference is dead code. Remove the pattern
   match case to eliminate the warning.

4. **Verify arity consistency.** An unrecognized term pattern can also arise
   when the constructor exists but with the wrong arity. For example, if `Neg`
   is defined as unary but a pattern references `Neg(Expr, Expr)` (binary),
   the WTA has no transition for the 2-ary version. Fix the pattern's arity to
   match the grammar rule.

## Hint Explanation

The hint **"add a rule or transition to recognize this term pattern"** identifies
the two standard ways to extend the WTA's tree language:

- **Adding a rule** means introducing a new production in the grammar's
  `language!` macro. This creates both the parser rule and the corresponding
  WTA transition, ensuring the constructor is recognized at all levels of the
  pipeline.

- **Adding a transition** is the lower-level alternative: directly extending the
  WTA's transition relation Delta with a new entry (q₁, ..., q_k, f, q) for
  the missing constructor f. This is appropriate when the term pattern arises
  from an internal transformation pass and should not be exposed as surface
  syntax.

The key insight is that every unrecognized term pattern represents a **gap**
between the grammar's intended tree language and the WTA's actual tree language.
The hint directs the author to close this gap by extending either the grammar
(high-level) or the automaton (low-level).

## Related Lints

- [V04](V04-wta-hot-path.md) -- Identifies frequently weighted term patterns
  that are candidates for specialization. V03 and V04 are complementary: V03
  finds terms the WTA misses, V04 finds terms the WTA recognizes but
  disproportionately often.
- [V01](V01-vpa-determinizable.md) -- VPA analysis of the delimiter structure.
  Orthogonal to WTA term analysis.
- [V02](V02-vpa-alphabet-mismatch.md) -- VPA alphabet classification.
  Orthogonal to WTA.
- [W01](../../wfst/W01-dead-rule.md) -- Dead-rule detection at the WFST level.
  A rule that is dead in the WFST may also produce unrecognized term patterns
  in the WTA.
