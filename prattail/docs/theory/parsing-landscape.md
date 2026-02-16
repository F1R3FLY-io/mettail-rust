# The Parsing Landscape: Positioning PraTTaIL

This document surveys the major families of parsing techniques, explains their
trade-offs, and shows where PraTTaIL sits in the design space. The goal is to
give the reader enough background to understand _why_ PraTTaIL combines Pratt
parsing, recursive descent, and automata-driven lexing rather than adopting any
single existing approach wholesale.

---

## 1. What Parsers Do

A **parser** transforms a flat sequence of characters (or tokens) into a
structured representation -- typically an abstract syntax tree (AST) or a
concrete syntax tree (CST). Two broad phases are involved:

```
  Source text           Tokens              AST / CST
 ┌───────────┐      ┌──────────┐      ┌──────────────┐
 │ "3 + 4*5" │─────>│ INT PLUS │─────>│     Add      │
 │           │ Lex  │ INT STAR │ Parse│    / \       │
 │           │      │ INT      │      │   3  Mul     │
 └───────────┘      └──────────┘      │      / \    │
                                       │     4   5   │
                                       └──────────────┘
```

**Lexing** (also called scanning or tokenization) groups characters into
tokens: identifiers, literals, operators, keywords, delimiters. **Parsing**
consumes the token stream and builds structure according to a grammar.

These two phases may be separate (as in traditional compiler construction) or
interleaved (as in scannerless parsers). PraTTaIL keeps them separate, using
automata theory for the lexer and a hybrid Pratt/recursive-descent strategy
for the parser.

---

## 2. Grammars: The Specification Language

Before discussing parsing algorithms, we must distinguish two major grammar
formalisms.

### 2.1 Context-Free Grammars (CFG)

A context-free grammar `G = (V, T, P, S)` consists of:

- `V`: a finite set of nonterminal symbols
- `T`: a finite set of terminal symbols
- `P`: a finite set of production rules `A -> alpha`, where `A in V` and
  `alpha` is a string over `V union T`
- `S in V`: the start symbol

CFGs generate **context-free languages** (CFL), recognized by pushdown
automata. Most programming language syntaxes are specified as CFGs (or
subsets thereof).

**Ambiguity.** A CFG is _ambiguous_ if some string has more than one leftmost
derivation. The classic example is the "dangling else" problem. Ambiguity is
the central challenge that parsing algorithms must address.

### 2.2 Parsing Expression Grammars (PEG)

A parsing expression grammar replaces the nondeterministic choice `|` of CFGs
with an _ordered_ choice `/`. Given `A <- e1 / e2`, the PEG parser tries `e1`
first; only if `e1` fails does it try `e2`.

```
  CFG:  Expr -> Expr "+" Term | Term        (ambiguous in isolation)
  PEG:  Expr <- Expr "+" Term / Term        (ordered: try "+" first)
```

**Advantages of PEG:**
- Never ambiguous by construction (ordered choice resolves all ambiguity)
- Unlimited lookahead via backtracking
- Can express some non-context-free patterns (e.g., `a^n b^n c^n`)

**Disadvantages of PEG:**
- Left recursion causes infinite loops (requires transformation)
- Ordered choice can silently shadow alternatives (subtle bugs)
- Backtracking can cause exponential parse time without memoization
- With memoization (packrat parsing), O(n) time but O(n * |G|) space

### 2.3 Comparison

```
  ┌──────────────────────┬───────────────────┬───────────────────────┐
  │ Property             │ CFG               │ PEG                   │
  ├──────────────────────┼───────────────────┼───────────────────────┤
  │ Choice semantics     │ Unordered (|)     │ Ordered (/)           │
  │ Ambiguity            │ Possible          │ Impossible            │
  │ Left recursion       │ Allowed           │ Infinite loop         │
  │ Expressiveness class │ CFL               │ Incomparable with CFL │
  │ Typical parse time   │ O(n) - O(n^3)     │ O(n) with packrat     │
  │ Space                │ O(n)              │ O(n * |G|) packrat    │
  │ Error reporting      │ Good (LR/LL)      │ Poor (backtracking)   │
  └──────────────────────┴───────────────────┴───────────────────────┘
```

PraTTaIL's grammar specification is closer to a CFG: rules declare alternatives
without imposing an ordering. The parser generator then analyzes FIRST sets and
binding powers to determine the correct dispatch strategy, avoiding the silent
shadowing pitfall of PEG while still achieving O(n) parse time.

---

## 3. Top-Down Parsing

Top-down parsers build the parse tree from the root (start symbol) downward,
predicting which production to apply by examining the upcoming tokens.

### 3.1 Recursive Descent (RD)

The simplest and most widely used top-down technique. Each nonterminal becomes
a function. Each function examines the current token and decides which
alternative to pursue.

```
  fn parse_expr(tokens) -> AST:
      left = parse_term(tokens)
      while peek(tokens) == PLUS:
          consume(tokens, PLUS)
          right = parse_term(tokens)
          left = Add(left, right)
      return left
```

**Strengths:**
- Extremely clear and debuggable
- Easy to add semantic actions, error recovery, and context-dependent parsing
- No separate tool required (can be hand-written)

**Weaknesses:**
- Cannot handle left recursion directly (requires transformation to iteration)
- Precedence and associativity encoded manually (tedious and error-prone)
- Naive implementations may backtrack exponentially

### 3.2 LL(k) Parsing

LL(k) grammars are a restricted subset of CFGs that can be parsed top-down
with `k` tokens of lookahead. The name means: scan **L**eft-to-right,
produce **L**eftmost derivation, with `k` lookahead tokens.

```
  LL(1) parse table for arithmetic:

  ┌──────────┬───────┬───────┬───────┬───────┬───────┐
  │          │  INT  │   +   │   *   │   (   │   $   │
  ├──────────┼───────┼───────┼───────┼───────┼───────┤
  │ Expr     │ T E'  │       │       │ T E'  │       │
  │ Expr'    │       │ +T E' │       │       │  eps  │
  │ Term     │ F T'  │       │       │ F T'  │       │
  │ Term'    │       │  eps  │ *F T' │       │  eps  │
  │ Factor   │ INT   │       │       │(Expr) │       │
  └──────────┴───────┴───────┴───────┴───────┴───────┘
```

**LL(1)** is the most common restriction: one token of lookahead. LL(1) grammars
must satisfy:
1. For any nonterminal `A` with alternatives `A -> alpha | beta`,
   `FIRST(alpha)` and `FIRST(beta)` must be disjoint.
2. If `epsilon in FIRST(alpha)`, then `FIRST(beta)` and `FOLLOW(A)` must
   be disjoint.

**Strengths:**
- Predictable O(n) parse time
- FIRST/FOLLOW set analysis catches ambiguities at grammar-compile time
- Maps directly onto recursive descent code

**Weaknesses:**
- Many natural grammars are not LL(1) without transformation
- Left recursion must be eliminated (distorts the grammar)
- Limited expressiveness compared to LR

### 3.3 LL(*) and ALL(*)

ANTLR's LL(*) and its successor ALL(*) extend LL(k) with adaptive lookahead.
Instead of a fixed `k`, the parser uses a decision automaton (essentially a
small DFA) at each decision point to look ahead as far as needed.

```
  LL(1):   peek 1 token  -->  decision
  LL(k):   peek k tokens -->  decision
  LL(*):   run DFA on token stream --> decision
  ALL(*):  run DFA, using full parser as subroutine on ambiguity
```

ALL(*) achieves the expressiveness of PEG with better error reporting and
without the ordered-choice pitfall, but at the cost of potentially exponential
parse time on adversarial inputs (though linear on practical grammars).

---

## 4. Bottom-Up Parsing

Bottom-up parsers build the parse tree from the leaves upward, identifying
the right-hand side of a production in the input and reducing it to the
left-hand side.

### 4.1 LR(k) Parsing

LR(k) parsers scan **L**eft-to-right and produce a **R**ightmost derivation
(in reverse) with `k` lookahead tokens. They are strictly more powerful than
LL(k) parsers.

```
  Shift-Reduce example for "3 + 4 * 5":

  Stack                 Input         Action
  ─────────────────────────────────────────────
  $                     3 + 4 * 5 $   Shift
  $ 3                     + 4 * 5 $   Reduce: F -> int
  $ F                     + 4 * 5 $   Reduce: T -> F
  $ T                     + 4 * 5 $   Reduce: E -> T
  $ E                     + 4 * 5 $   Shift
  $ E +                     4 * 5 $   Shift
  $ E + 4                     * 5 $   Reduce: F -> int
  $ E + F                     * 5 $   Reduce: T -> F
  $ E + T                     * 5 $   Shift (prec: * > +)
  $ E + T *                     5 $   Shift
  $ E + T * 5                     $   Reduce: F -> int
  $ E + T * F                     $   Reduce: T -> T * F
  $ E + T                         $   Reduce: E -> E + T
  $ E                             $   Accept
```

The major LR variants are:

```
  ┌───────────┬──────────────────────────────────────────────────┐
  │ Variant   │ Description                                      │
  ├───────────┼──────────────────────────────────────────────────┤
  │ LR(0)     │ No lookahead; very restricted                    │
  │ SLR(1)    │ Uses FOLLOW sets for lookahead; simple tables     │
  │ LALR(1)   │ Merges LR(1) states with same core; practical    │
  │ LR(1)     │ Full 1-token lookahead; largest tables            │
  │ GLR       │ Handles all CFGs; forks on conflicts              │
  └───────────┴──────────────────────────────────────────────────┘
```

**LALR(1)** is the workhorse of production parsers (yacc, bison, LALRPOP).
It handles most programming language grammars and produces compact parse
tables.

**Strengths:**
- Handles left recursion natively
- Strictly more powerful than LL(k)
- O(n) parse time for unambiguous grammars
- Precedence/associativity handled via table annotations

**Weaknesses:**
- Parse tables are opaque -- hard to debug
- Error messages require careful engineering
- Shift-reduce and reduce-reduce conflicts are notoriously difficult to resolve
- Cannot easily interleave semantic actions or context-dependent parsing

### 4.2 Operator-Precedence Parsing

A specialized bottom-up technique for expression languages. Instead of a full
LR parse table, it uses a precedence relation between terminal symbols.

Given operators `a` and `b`, the precedence relation defines:
- `a <. b` : `a` yields precedence to `b` (shift)
- `a .> b` : `a` takes precedence over `b` (reduce)
- `a .= b` : `a` and `b` have equal precedence (e.g., matching delimiters)

The **Dijkstra shunting-yard algorithm** is the most famous implementation:
it uses two stacks (operators and operands) to convert infix expressions to
postfix or directly build an AST.

```
  Shunting-yard for "3 + 4 * 5":

  Output stack      Operator stack    Input        Action
  ──────────────────────────────────────────────────────────
                                      3 + 4 * 5
  3                                     + 4 * 5    Push operand
  3                 +                     4 * 5    Push op (stack empty)
  3 4               +                       * 5    Push operand
  3 4               + *                       5    Push op (* > +)
  3 4 5             + *                            Push operand
  3 4 5 *           +                              Pop * (prec)
  3 4 5 * +                                        Pop +
```

This is elegant for pure expression languages but cannot handle general
syntax (binders, pattern matching, control flow).

---

## 5. Pratt Parsing: The Best of Both Worlds

Vaughan Pratt's top-down operator-precedence parsing (1973) combines the
strengths of recursive descent and operator-precedence parsing. It is
sometimes called "top-down operator precedence" (TDOP).

### 5.1 Key Insight

Pratt's insight is that the recursive descent paradigm and operator-precedence
paradigm can be unified through **binding power** -- a numeric strength
assigned to each operator that controls how tightly it binds to its operands.

```
  ┌───────────────────────────────────────────────────────────┐
  │              Pratt Parsing = RD + Binding Power            │
  │                                                           │
  │  From Recursive Descent:                                  │
  │    - Top-down structure                                   │
  │    - Easy to add non-expression syntax                    │
  │    - Clear, debuggable control flow                       │
  │    - Context-sensitive parsing                            │
  │                                                           │
  │  From Operator-Precedence:                                │
  │    - Precedence via numeric binding powers (not grammar)  │
  │    - Associativity via left/right BP asymmetry            │
  │    - O(1) precedence decisions                            │
  │    - Handles arbitrary precedence levels                  │
  └───────────────────────────────────────────────────────────┘
```

### 5.2 The Pratt Loop

The core algorithm is a single loop with two dispatch points:

1. **Null denotation (nud):** How does a token behave when it appears at the
   _start_ of an expression? (Prefix operators, atoms, grouping.)

2. **Left denotation (led):** How does a token behave when it appears _after_
   a left-hand operand? (Infix operators, postfix operators, mixfix.)

The loop continues consuming tokens as long as the next operator's left
binding power exceeds the current minimum. This is the _Pratt loop_ and it
generalizes the shunting-yard algorithm to a recursive-descent framework.

The full details of Pratt parsing, including worked examples, are covered in
[pratt-parsing.md](pratt-parsing.md).

---

## 6. Where PraTTaIL Sits

PraTTaIL is a **parser generator** that combines:

1. **Automata-driven lexing:** Thompson's construction, subset construction,
   Hopcroft's minimization, alphabet equivalence classes, and code generation.
   This produces a provably correct, minimal DFA-based lexer. See
   [finite-automata.md](finite-automata.md).

2. **Pratt parsing for expressions:** Infix operators are handled by a
   generated Pratt loop with binding power pairs. No grammar transformation
   is needed -- left recursion and precedence are handled natively.

3. **Recursive descent for structure:** Non-expression syntax (binders,
   collections, pattern operations, multi-token constructs) uses generated
   recursive descent handlers.

4. **FIRST-set prediction for dispatch:** At each parse decision point,
   precomputed FIRST sets and dispatch tables eliminate trial-and-error.
   See [prediction-and-lookahead.md](prediction-and-lookahead.md).

### 6.1 Architecture Diagram

```
  language! { ... }
         |
         v
   ┌─────────────────────────────────────────────────────────┐
   │                 PraTTaIL Pipeline                        │
   │                                                         │
   │  Phase 1: Lexer generation                              │
   │  ┌─────────────────────────────────────────────────┐    │
   │  │ Terminals -> NFA (Thompson's)                   │    │
   │  │          -> Equiv Classes (alphabet partition)  │    │
   │  │          -> DFA (subset construction)           │    │
   │  │          -> Minimized DFA (Hopcroft)            │    │
   │  │          -> Rust code (match arms or table)     │    │
   │  └─────────────────────────────────────────────────┘    │
   │                                                         │
   │  Phase 2: Binding power analysis                        │
   │  ┌─────────────────────────────────────────────────┐    │
   │  │ Infix rules -> BP pairs (left_bp, right_bp)     │    │
   │  │             -> BP lookup table per category      │    │
   │  │             -> AST constructor dispatch          │    │
   │  └─────────────────────────────────────────────────┘    │
   │                                                         │
   │  Phase 3: Prediction engine                             │
   │  ┌─────────────────────────────────────────────────┐    │
   │  │ Rules -> FIRST sets (fixed-point iteration)     │    │
   │  │       -> Dispatch tables per category            │    │
   │  │       -> Cross-category overlap analysis         │    │
   │  └─────────────────────────────────────────────────┘    │
   │                                                         │
   │  Phase 4: RD handler generation                         │
   │  ┌─────────────────────────────────────────────────┐    │
   │  │ Structural rules -> parse functions              │    │
   │  │                  -> match arms for dispatch      │    │
   │  └─────────────────────────────────────────────────┘    │
   │                                                         │
   │  Phase 5: Pratt parser generation                       │
   │  ┌─────────────────────────────────────────────────┐    │
   │  │ Per category:                                    │    │
   │  │   parse_<Cat>(tokens, pos, min_bp)  -- loop     │    │
   │  │   parse_<Cat>_prefix(tokens, pos)   -- nud      │    │
   │  │   infix_bp(token) -> (left, right)  -- led bp   │    │
   │  │   make_infix(op, lhs, rhs) -> Cat   -- builder  │    │
   │  └─────────────────────────────────────────────────┘    │
   │                                                         │
   │  Phase 6: Cross-category dispatch                       │
   │  Phase 7: Assembly                                      │
   └─────────────────────────────────────────────────────────┘
         |
         v
    TokenStream (Rust source code)
```

---

## 7. Complexity Comparison

The following table compares the major parsing strategies across key
dimensions relevant to language implementation:

```
  ┌────────────────────┬────────┬────────────┬───────────┬──────────────┐
  │ Technique          │ Time   │ Space      │ Left Rec  │ Precedence   │
  ├────────────────────┼────────┼────────────┼───────────┼──────────────┤
  │ Recursive descent  │ O(n)*  │ O(depth)   │ No        │ Manual       │
  │ LL(1)              │ O(n)   │ O(depth)   │ No        │ Via grammar  │
  │ LL(k)              │ O(n)   │ O(depth)   │ No        │ Via grammar  │
  │ ALL(*)             │ O(n)** │ O(n)       │ No***     │ Via grammar  │
  │ LALR(1)            │ O(n)   │ O(depth)   │ Yes       │ Via table    │
  │ LR(1)              │ O(n)   │ O(depth)   │ Yes       │ Via table    │
  │ GLR                │ O(n^3) │ O(n)       │ Yes       │ Ambiguity    │
  │ Earley             │ O(n^3) │ O(n^2)     │ Yes       │ Ambiguity    │
  │ Packrat (PEG)      │ O(n)   │ O(n*|G|)   │ No        │ Via ordering │
  │ Shunting-yard      │ O(n)   │ O(depth)   │ N/A****   │ Numeric BP   │
  │ Pratt (TDOP)       │ O(n)   │ O(depth)   │ Yes*****  │ Numeric BP   │
  │ PraTTaIL           │ O(n)   │ O(n)       │ Yes*****  │ Numeric BP   │
  └────────────────────┴────────┴────────────┴───────────┴──────────────┘

  *     Without backtracking; exponential with naive backtracking.
  **    O(n) on practical grammars; worst case can be exponential.
  ***   ANTLR 4 supports left recursion via rewriting.
  ****  Only handles expressions; left recursion is not applicable.
  ***** Infix left recursion handled natively via the Pratt loop;
        general left recursion not applicable (non-expression rules
        use RD, which avoids left recursion by design).
```

### 7.1 Additional Comparison Dimensions

```
  ┌────────────────────┬─────────────┬─────────────┬──────────────────┐
  │ Technique          │ Error Msgs  │ Debuggable  │ Context Passing  │
  ├────────────────────┼─────────────┼─────────────┼──────────────────┤
  │ Recursive descent  │ Excellent   │ Excellent   │ Easy             │
  │ LL(1)              │ Good        │ Good        │ Via parse stack  │
  │ LALR(1)            │ Poor*       │ Poor        │ Hard             │
  │ Packrat (PEG)      │ Poor**      │ Medium      │ Medium           │
  │ Pratt (TDOP)       │ Excellent   │ Excellent   │ Easy             │
  │ PraTTaIL           │ Good        │ Good        │ Yes (generated)  │
  └────────────────────┴─────────────┴─────────────┴──────────────────┘

  *  LALR error messages require significant engineering (error
     productions, recovery strategies) to be usable.
  ** PEG error messages are poor because the parser backtracks past
     the actual error point before failing elsewhere.
```

---

## 8. Why Not Just Use LALR(1)?

MeTTaIL was originally parsed with LALRPOP, an LALR(1) parser generator for
Rust. Four fundamental issues arose:

1. **Operator precedence ambiguity.** The grammar has operators like `|`
   (parallel composition) that are syntactically identical to other uses. LALR(1)
   produces shift-reduce conflicts requiring grammar refactoring.

2. **Cross-category expressions.** Expressions like `Int "==" Int -> Bool`
   mix categories. LALR(1) requires duplicated or factored productions that
   inflate the grammar.

3. **Binder scope ambiguity.** Lambda-like binders (`^x.{body}`) create
   conflicts between the binder syntax and expression alternatives. LALR(1)
   grammars must introduce extra nonterminals.

4. **Collection syntax.** Separated lists with different collection types
   (HashBag, HashSet, Vec) require grammar-level encoding in LALR(1).

PraTTaIL eliminates all four issues by design:

```
  ┌───────────────────────────┬─────────────────────────────────────┐
  │ LALR(1) Issue             │ PraTTaIL Solution                   │
  ├───────────────────────────┼─────────────────────────────────────┤
  │ Operator precedence       │ Binding power pairs (automatic)     │
  │ Cross-category exprs      │ Cross-category dispatch + FIRST     │
  │ Binder scope ambiguity    │ RD handlers with context passing    │
  │ Collection syntax         │ Collection combinators in RD        │
  └───────────────────────────┴─────────────────────────────────────┘
```

---

## 9. Why Not Just Use PEG / Packrat?

PEG parsers (pest, nom with ordered choice, tree-sitter to a degree) avoid
ambiguity entirely. However:

1. **Silent shadowing.** Ordered choice can mask valid alternatives, producing
   incorrect parses rather than errors. With MeTTaIL's multi-category grammar,
   this is a serious risk.

2. **Space overhead.** Packrat parsing requires O(n * |G|) memoization space.
   For MeTTaIL grammars with many categories and rules, this overhead is
   significant.

3. **No typed AST.** Most PEG tools produce generic CST nodes. PraTTaIL
   generates typed Rust AST constructors directly, like LALRPOP but without
   the grammar restrictions.

4. **Error reporting.** PEG parsers backtrack past the actual error point.
   PraTTaIL's prediction engine detects errors at the point of mismatch.

---

## 10. Why Not Hand-Written Recursive Descent?

Hand-written recursive descent parsers are the gold standard for control and
error quality. GCC, Clang, Rust's own parser, and Go's parser are all
hand-written RD. However:

1. **Maintenance burden.** MeTTaIL's grammar evolves as the language develops.
   A parser generator absorbs grammar changes automatically.

2. **Precedence encoding.** Manual precedence climbing or Pratt loop
   implementation is tedious for many operators across multiple categories.

3. **Cross-category dispatch.** The FIRST-set analysis and overlap detection
   that PraTTaIL automates would need to be maintained by hand.

4. **Code volume.** PraTTaIL generates approximately 1,500-2,000 lines of
   parser code. The equivalent LALRPOP-generated code was approximately
   20,000 lines -- a 10-14x reduction. A hand-written parser would be
   somewhere in between, but without the automatic correctness guarantees.

---

## 11. The Design Space Map

The following diagram positions PraTTaIL relative to other tools and
techniques along two axes: generality (what grammars can they handle) and
code quality (how readable/debuggable is the generated or written parser).

```
  Code Quality (readability, debuggability, error messages)
       ^
       |
  High |  Hand-written RD          PraTTaIL
       |     (GCC, rustc)        (Pratt + RD + automata)
       |
       |                 ANTLR
       |                (ALL(*))
       |
  Med  |   tree-sitter           LALRPOP
       |   (GLR-ish)             (LALR(1))
       |
       |        pest                yacc / bison
       |        (PEG)               (LALR(1))
  Low  |
       |
       +──────────────────────────────────────────> Generality
                 LL(1)    LALR(1)    LR(1)   GLR/Earley
```

PraTTaIL occupies the upper-right quadrant: it handles the grammar features
needed by MeTTaIL (multi-category, cross-category, binders, collections,
arbitrary precedence) while producing readable, direct-coded parsers with
good error messages.

---

## 12. Summary

| Concern | PraTTaIL's Approach |
|---|---|
| Lexing | Automata pipeline: NFA -> DFA -> minimize -> codegen |
| Expression parsing | Pratt loop with binding power pairs |
| Structural syntax | Generated recursive descent handlers |
| Parse dispatch | FIRST set prediction + dispatch tables |
| Cross-category | Overlap analysis + backtrack-when-needed |
| Precedence | Automatic from rule declaration order |
| Associativity | Left/right via BP pair asymmetry |
| Error reporting | Point-of-mismatch detection |
| Output | Typed Rust AST (no generic CST) |
| Complexity | O(n) time, O(n) space |

The key insight is that no single parsing technique optimally addresses all
concerns. By composing Pratt parsing (for expressions), recursive descent
(for structure), and automata theory (for lexing and prediction), PraTTaIL
achieves a parser generator that is both powerful and produces high-quality
code.

---

## References

1. Pratt, V. R. (1973). "Top Down Operator Precedence." _Proc. ACM Symposium
   on Principles of Programming Languages_, pp. 41--51.
2. Aho, A. V., Sethi, R., & Ullman, J. D. (1986). _Compilers: Principles,
   Techniques, and Tools_ (the "Dragon Book"). Addison-Wesley.
3. Ford, B. (2004). "Parsing Expression Grammars: A Recognition-Based
   Syntactic Foundation." _POPL_, pp. 111--122.
4. Parr, T. & Fisher, K. (2011). "LL(*): The Foundation of the ANTLR Parser
   Generator." _PLDI_, pp. 425--436.
5. Hopcroft, J. E. (1971). "An n log n Algorithm for Minimizing States in a
   Finite Automaton." _Theory of Machines and Computations_, pp. 189--196.
6. Dijkstra, E. W. (1961). "Shunting-Yard Algorithm." Numerische Mathematik.
7. Thompson, K. (1968). "Regular Expression Search Algorithm."
   _Communications of the ACM_, 11(6), pp. 419--422.
