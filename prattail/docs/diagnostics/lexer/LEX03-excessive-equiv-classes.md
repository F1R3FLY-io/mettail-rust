# LEX03: excessive-equiv-classes

**Severity:** Note
**Category:** lexer
**Feature Gate:** None

## Description

Reports when the number of distinct characters across all terminal strings in
the grammar exceeds 25, indicating an unusually diverse character set. In DFA-
based lexing, each distinct character (or equivalence class of characters)
requires separate transition table entries. A grammar that uses a large
variety of characters -- for example, mixing ASCII operators, Unicode
mathematical symbols, and multi-script keywords -- produces more equivalence
classes, which increases the size of the DFA transition tables.

The DFA transition table for a lexer with N states and K equivalence classes
has N x K entries. When K is large, the table grows proportionally, consuming
more memory and potentially reducing cache efficiency during lexing.

This lint uses the distinct character count as a **proxy** for the actual
equivalence class count. The true equivalence class count (computed during DFA
construction) may be lower if characters that appear in the same positions can
be merged, but a high distinct character count is a reliable signal of a
complex lexer alphabet.

```
  Character diversity analysis

  Terminals:    +  -  *  /  ==  !=  <=  >=  &&  ||  ::  ->  =>
                (  )  [  ]  {  }  ;  ,  .  ..  ...  @  #  $  ~
                ^  %  <<  >>  >>>  ?  !

  Distinct characters: { +, -, *, /, =, !, <, >, &, |, :, (, ), [,
                         ], {, }, ;, ,, ., @, #, $, ~, ^, %, ?, ? }

  Count: 27 > threshold 25 → LEX03 fires
```

## Trigger Conditions

All of the following must hold:

- The number of distinct characters (Unicode codepoints) across all
  terminal strings in the grammar exceeds 25.

One diagnostic is emitted per grammar.

## Example

### Grammar

```rust
language! {
    name: RichOps,
    types {
        ![i64] as Expr
    },
    terms {
        Num    . n:Expr |- n : Expr;
        Add    . a:Expr, b:Expr |- a "+" b : Expr;
        Sub    . a:Expr, b:Expr |- a "-" b : Expr;
        Mul    . a:Expr, b:Expr |- a "*" b : Expr;
        Div    . a:Expr, b:Expr |- a "/" b : Expr;
        Mod    . a:Expr, b:Expr |- a "%" b : Expr;
        Pow    . a:Expr, b:Expr |- a "^" b : Expr;
        BitAnd . a:Expr, b:Expr |- a "&" b : Expr;
        BitOr  . a:Expr, b:Expr |- a "|" b : Expr;
        BitXor . a:Expr, b:Expr |- a "~" b : Expr;
        Shl    . a:Expr, b:Expr |- a "<<" b : Expr;
        Shr    . a:Expr, b:Expr |- a ">>" b : Expr;
        Eq     . a:Expr, b:Expr |- a "==" b : Expr;
        Ne     . a:Expr, b:Expr |- a "!=" b : Expr;
        Le     . a:Expr, b:Expr |- a "<=" b : Expr;
        Ge     . a:Expr, b:Expr |- a ">=" b : Expr;
        And    . a:Expr, b:Expr |- a "&&" b : Expr;
        Or     . a:Expr, b:Expr |- a "||" b : Expr;
        Range  . a:Expr, b:Expr |- a ".." b : Expr;
        Pipe   . a:Expr, b:Expr |- a "|>" b : Expr;
        Apply  . f:Expr, a:Expr |- f "(" a ")" : Expr;
        Index  . a:Expr, i:Expr |- a "[" i "]" : Expr;
        Block  . a:Expr |- "{" a "}" : Expr;
        At     . a:Expr |- "@" a : Expr;
        Hash   . a:Expr |- "#" a : Expr;
        Dollar . a:Expr |- "$" a : Expr;
        Quest  . a:Expr |- a "?" : Expr;
        Semi   . a:Expr, b:Expr |- a ";" b : Expr;
        Comma  . a:Expr, b:Expr |- a "," b : Expr;
    },
}
```

### Output

```
note[LEX03] (RichOps): 28 distinct characters across all terminals -- grammar has unusually diverse character set
  = hint: consider whether all terminals are necessary -- large character sets increase DFA table size
```

## Resolution

1. **Review terminal necessity.** Check whether all terminal strings are
   truly needed. Grammars that accumulate operators over time may include
   terminals that are never actually used in practice.

2. **Use keyword-based alternatives.** Replace single-character symbol
   operators with keyword alternatives where appropriate. For example,
   `"and"` instead of `"&&"` reduces the character set (alphabetic
   characters are already present for identifiers).

3. **Enable MPH keyword optimization (AL04).** For keyword-heavy grammars,
   the AL04 optimization uses minimal perfect hashing to reduce DFA state
   count, which partially mitigates the impact of a large character set.

4. **Accept the diversity.** Many real-world languages (C, Rust, Haskell)
   use 30+ distinct characters in their operator sets. The lint is
   informational; the DFA will still function correctly.

## Hint Explanation

The hint **"consider whether all terminals are necessary -- large character
sets increase DFA table size"** explains:

- The **DFA table size** grows with the number of equivalence classes,
  which correlates with the number of distinct characters. Each new
  character that does not share transition behavior with an existing one
  adds a column to the transition table.

- The recommendation to **review terminal necessity** encourages the grammar
  author to audit the operator set, removing unused or redundant terminals
  to keep the lexer compact.

## Related Lints

- [LEX04](LEX04-dfa-state-explosion.md) -- DFA state explosion is the
  downstream consequence: many equivalence classes combined with many
  terminals can produce an exponential number of DFA states.
- [LEX02](LEX02-unreachable-token-pattern.md) -- Unreachable patterns may
  indicate terminals that can be removed, reducing character diversity.
