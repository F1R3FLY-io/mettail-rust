# LEX04: dfa-state-explosion

**Severity:** Note
**Category:** lexer
**Feature Gate:** None

## Description

Reports when the total count of terminal token occurrences across all rules in
the grammar exceeds 50, signaling that the resulting lexer DFA may have a
large number of states. DFA state explosion occurs during subset construction
(the NFA-to-DFA conversion) when many overlapping NFA states must be tracked
simultaneously, producing a combinatorial blowup in the number of DFA states.

In the worst case, an NFA with N states can produce a DFA with 2^N states.
While PraTTaIL's lexer uses DFA minimization to reduce the final state count,
the intermediate explosion during construction can consume significant memory
and compile time. Grammars with many terminals -- especially terminals that
share prefixes or use overlapping character classes -- are most susceptible.

This lint uses the terminal token count as a **proxy** for the actual DFA
state count, since the full `LexerStats` data is not available in the current
lint context. The threshold of 50 terminal occurrences was chosen to flag
grammars that are likely to produce large DFAs.

```
  Subset construction state growth

  NFA states (5 terminals, simple):     ○─a─○─b─○
                                         ○─c─○─d─○
                                         ○─a─○─c─○

  DFA states after subset construction:
  ┌─────────────────────────┐
  │ {q0}                    │
  │   ─a→ {q1, q5}         │  ← merged NFA states
  │   ─c→ {q3}             │
  ├─────────────────────────┤
  │ {q1, q5}                │  ← powerset grows
  │   ─b→ {q2}             │
  │   ─c→ {q6}             │
  └─────────────────────────┘

  With 50+ terminals: state count can reach thousands
```

## Trigger Conditions

All of the following must hold:

- The total count of `SyntaxItemSpec::Terminal(_)` occurrences across all
  rules in the grammar exceeds 50.

One diagnostic is emitted per grammar.

## Example

### Grammar

```rust
language! {
    name: KeywordHeavy,
    types {
        ![String] as Stmt,
        ![String] as Expr,
        ![String] as Type
    },
    terms {
        // 50+ rules with diverse terminal keywords and operators
        Lit       . s:Expr |- s : Expr;
        If        . c:Expr, t:Stmt, e:Stmt |- "if" c "then" t "else" e : Stmt;
        While     . c:Expr, b:Stmt |- "while" c "do" b "end" : Stmt;
        For       . v:Expr, r:Expr, b:Stmt |- "for" v "in" r "do" b "end" : Stmt;
        Match     . e:Expr, b:Stmt |- "match" e "with" b "end" : Stmt;
        Try       . b:Stmt, c:Stmt |- "try" b "catch" c "end" : Stmt;
        Class     . n:Expr, b:Stmt |- "class" n "{" b "}" : Stmt;
        Fn        . n:Expr, p:Expr, b:Stmt |- "fn" n "(" p ")" "->" b : Stmt;
        Let       . n:Expr, t:Type, v:Expr |- "let" n ":" t "=" v ";" : Stmt;
        Import    . m:Expr |- "import" m ";" : Stmt;
        Export    . m:Expr |- "export" m ";" : Stmt;
        Return    . e:Expr |- "return" e ";" : Stmt;
        Yield     . e:Expr |- "yield" e ";" : Stmt;
        Throw     . e:Expr |- "throw" e ";" : Stmt;
        Assert    . e:Expr |- "assert" e ";" : Stmt;
        // ... many more rules with distinct terminals
    },
}
```

### Output

```
note[LEX04] (KeywordHeavy): 62 terminal tokens -- monitor DFA state count for potential explosion
  = hint: consider keyword MPH (AL04) to reduce DFA states for keyword-heavy grammars
```

## Resolution

1. **Enable keyword MPH (AL04).** The AL04 optimization replaces the
   standard DFA-based keyword recognition with a minimal perfect hash
   function. This collapses all keyword transitions into a single hash
   lookup, dramatically reducing DFA state count for keyword-heavy grammars.

2. **Factor common terminal prefixes.** If many terminals share prefixes
   (e.g., `"let"`, `"letmut"`, `"letref"`), left-factor them so the DFA
   shares transition paths.

3. **Use a scanner-less approach for keywords.** Instead of encoding each
   keyword as a separate terminal, lex identifiers generically and perform
   a keyword lookup in a post-lexing pass. This keeps the DFA small at the
   cost of an extra lookup step.

4. **Reduce terminal count.** Review whether all terminals are necessary.
   Some grammars accumulate terminals over time (e.g., deprecated syntax
   alternatives) that can be removed.

5. **Monitor but accept.** Grammars for production languages routinely have
   60-100+ terminals. PraTTaIL's DFA minimization keeps the final state
   count manageable for most grammars. The lint is a monitoring signal, not
   necessarily an action item.

## Hint Explanation

The hint **"consider keyword MPH (AL04) to reduce DFA states for keyword-
heavy grammars"** refers to the AL04 codegen optimization:

- **MPH (Minimal Perfect Hashing)** assigns each keyword to a unique slot
  using a hash function with no collisions. At lex time, a candidate
  identifier is hashed and the slot is checked -- O(1) keyword recognition
  regardless of the number of keywords.

- **AL04** is the PraTTaIL optimization ID for this technique. When enabled,
  it replaces the DFA's keyword transition arcs with a single identifier
  arc followed by an MPH lookup, reducing the DFA state count by roughly
  the number of keywords.

## Related Lints

- [LEX03](LEX03-excessive-equiv-classes.md) -- A diverse character set
  increases the equivalence class count, which compounds with many terminals
  to produce larger DFA tables.
- [LEX02](LEX02-unreachable-token-pattern.md) -- Unreachable token patterns
  may indicate terminals that can be removed, reducing DFA size.
- [DIS03](../dispatch/DIS03-decision-tree-depth.md) -- A large DFA often
  corresponds to a deep decision tree, since many terminals create many
  branching points.
