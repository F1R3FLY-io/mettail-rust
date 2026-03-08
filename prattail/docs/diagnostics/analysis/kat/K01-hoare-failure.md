# K01: hoare-failure

**Severity:** Warning
**Category:** analysis/kat
**Feature Gate:** `kat`

## Description

A Hoare triple `{p} e {q}` asserts that if precondition `p` holds before executing program `e`, then postcondition `q` holds afterwards. In Kleene Algebra with Tests (KAT), this assertion is encoded as an algebraic equation and checked for validity via automata-theoretic decision procedures. K01 fires when a Hoare triple is invalid -- the grammar's parse control flow does not satisfy its pre/post specification.

### Hoare Triple Encoding in KAT

The central insight from Kozen (1997) is that propositional Hoare logic embeds completely into KAT. The encoding is:

```
{p} e {q}   is valid   iff   test(p) . e . test(not q) = 0
```

where:
- `test(p)` is the Boolean test corresponding to precondition `p`
- `e` is the KAT expression representing the program
- `test(not q)` is the Boolean test corresponding to the negation of postcondition `q`
- `.` is sequential composition
- `= 0` means the expression denotes the empty language (no execution path)

The intuition: `test(p) . e . test(not q)` represents "start in a state satisfying `p`, execute `e`, and end in a state violating `q`." If this expression equals zero, no such execution path exists, and the Hoare triple is valid. If it is nonzero, there exists a concrete execution that satisfies the precondition but violates the postcondition.

### KAT Algebra Structure

A Kleene Algebra with Tests `(K, B, +, ., *, 0, 1)` consists of:

- A Kleene algebra `(K, +, ., *, 0, 1)` with:
  - `+` : alternation/choice (idempotent, commutative, associative)
  - `.` : sequential composition (associative, distributes over `+`)
  - `*` : Kleene star (reflexive transitive closure)
  - `0` : failure (identity for `+`, annihilator for `.`)
  - `1` : skip (identity for `.`)

- A Boolean subalgebra `B` of tests with:
  - `b + c` : disjunction
  - `b . c` : conjunction
  - `not b` : complement (exists in `B` for every `b in B`)
  - Tests commute with each other: `b . c = c . b`

### Decision Procedure

KAT equivalence (and hence Hoare triple validity) is decidable in PSPACE via the following automata-based procedure:

```
  Hoare triple: {p} e {q}
           |
           v
  Construct: h = test(p) . e . test(not q)
           |
           v
  ┌──────────────────────────────┐
  │  Compile h to a             │
  │  guarded-string automaton   │
  │                             │
  │  States: derivatives of h   │
  │  Alphabet: atoms x actions  │
  │  Accept: epsilon in L(h)    │
  └──────────────────────────────┘
           |
           v
  ┌──────────────────────────────┐
  │  Bisimulation check:        │
  │                             │
  │  Is L(automaton(h)) = empty? │
  │                             │
  │  Bounded BFS up to depth    │
  │  limit (default: 100)       │
  └──────────────────────────────┘
           |
      ┌────┴────┐
      |         |
      v         v
   L = empty  L != empty
      |         |
      v         v
   VALID      INVALID
   (silent)   (K01 fires)
```

The decision procedure constructs an automaton recognizing the guarded strings of the Hoare condition expression `h`, then checks whether its language is empty. If non-empty, the automaton provides a witness: a guarded string (atom sequence interleaved with actions) that demonstrates a failing execution path.

## Trigger Conditions

K01 fires once per failed Hoare triple. Specifically:

- The `kat` feature gate is enabled.
- The pipeline has computed a `KatCheck` result.
- The `hoare_results` field contains at least one `(description, false)` pair.
- One K01 diagnostic is emitted per failed triple.

Hoare triples that pass (value `true`) are silently accepted. K01 only reports failures.

## Example

### Grammar

```
language! {
    name: ParserFlow;
    primary: Stmt;

    category Stmt {
        native_type: Identifier;

        Assign = <ident> "=" Expr;
        If     = "if" Expr "then" Stmt "else" Stmt;
        While  = "while" Expr "do" Stmt;
        Seq    = Stmt ";" Stmt;
        Skip   = "skip";
        CastE  = Expr;
    }

    category Expr {
        native_type: Integer;

        Num    = <int>;
        Var    = <ident>;
        Add    = Expr "+" Expr;
        Eq     = Expr "==" Expr;
    }
}
```

With a Hoare triple specification:

```
{token_available}  parse_stmt  {ast_complete}
```

This asserts: "If a token is available, then after parsing a statement, the AST is complete." If the grammar permits `parse_stmt` to succeed without consuming all tokens (e.g., `Skip` consumes zero tokens from `Expr`), the postcondition `ast_complete` may not hold.

### Output

```
warning[K01] (ParserFlow): Hoare triple failed: {token_available} parse_stmt {ast_complete}
  = hint: p.e.not q != 0 -- the program does not satisfy its specification
```

## Resolution

1. **Examine the Hoare triple.** The description identifies the precondition, program, and postcondition. Determine whether the specification is too strong or the grammar is too permissive.

2. **Strengthen the program.** Add grammar constraints that ensure the postcondition holds. For example:
   - Add EOF checks after statement parsing to ensure all tokens are consumed.
   - Add guard tests at dispatch points to prevent premature completion.

3. **Weaken the postcondition.** If the grammar legitimately allows partial parses, weaken `q` to `ast_partial | ast_complete`.

4. **Strengthen the precondition.** If the triple only holds under additional assumptions, add them to `p`. For example, `{token_available /\ not at_eof}`.

5. **Inspect the counterexample.** The nonzero expression `test(p) . e . test(not q)` has a witness -- a sequence of actions and tests that leads from a state satisfying `p` to a state violating `q`. Tracing this sequence through the grammar reveals the specific parse path that violates the specification.

## Hint Explanation

> p.e.not q != 0 -- the program does not satisfy its specification

The hint restates the KAT encoding of the Hoare triple failure. The expression `p . e . not q` (precondition, program, negated postcondition) denotes a non-empty set of guarded strings, meaning there exists at least one execution path that starts in a state satisfying `p`, runs the program `e`, and ends in a state violating `q`. The unicode dot `.` denotes sequential composition, and `not q` (also written `q-bar`) denotes the complement of test `q`.

## Related Lints

- [K02](K02-kat-equivalence.md) -- KAT equivalence checking. K01 checks Hoare triples (a special case of KAT equivalence where one side is zero); K02 checks general expression equivalence.
- [L01](../temporal/L01-ltl-violated.md) -- LTL violation. Both K01 and L01 detect specification failures, but at different abstraction levels: K01 checks pre/post conditions on finite executions; L01 checks temporal properties on infinite traces.
- [P06](../P06-analysis-pipeline-cost.md) -- Reports total analysis phase time, which includes KAT analysis when the feature is enabled.
