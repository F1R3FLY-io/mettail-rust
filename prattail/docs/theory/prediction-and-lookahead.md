# Prediction and Lookahead in PraTTaIL

This document explains the prediction-driven parsing techniques used by
PraTTaIL to minimize backtracking and achieve deterministic parse dispatch.
We cover FIRST sets, FOLLOW sets, decision automata, cross-category
prediction, memoization, and comparisons with LL(1) and LR(1) lookahead.

---

## 1. The Dispatch Problem

At each parse decision point, the parser must choose among multiple
alternatives. For a category `Proc` with rules:

```
  PZero   : "0"                          // Zero process
  PInput  : "for" "(" Name "<-" Name ")" "{" Proc "}"
  POutput : Name "!" "(" Proc ")"
  PPar    : Proc "|" Proc                // Infix (handled by Pratt loop)
  PVar    : identifier                   // Variable
```

When the parser sees the next token, it must decide which rule to try:

```
  Token         Correct rule
  ──────────────────────────
  "0"           PZero
  "for"         PInput
  identifier    POutput? or PVar?  <-- ambiguity
```

The `identifier` case is ambiguous: it could be the start of `POutput`
(where `Name` begins with an identifier) or `PVar` (a bare variable).
PraTTaIL resolves this using **FIRST set analysis** and **lookahead**.

---

## 2. FIRST Sets

### 2.1 Definition

The **FIRST set** of a grammar symbol or string of symbols is the set of
terminal tokens that can appear as the first token when parsing that symbol.

Formally, for a string of grammar symbols `alpha`:

```
  FIRST(alpha) = { t in Terminals : alpha =>* t beta, for some beta }
                 union (if alpha =>* epsilon then { epsilon } else {})
```

For PraTTaIL, which does not have epsilon-producing rules in the traditional
sense, the FIRST set of a category is simply the set of tokens that can
begin any rule in that category.

### 2.2 Fixed-Point Computation

FIRST sets are computed iteratively because categories can reference each
other. The algorithm is a classic **fixed-point iteration**:

```
  function compute_first_sets(rules, categories):
      // Initialize empty FIRST sets
      for cat in categories:
          FIRST[cat] = {}

      // Iterate until no set changes
      repeat:
          changed = false
          for rule in rules:
              if rule.is_infix: continue  // Infix handled by Pratt loop

              for item in rule.first_items:
                  tokens = resolve_item(item, FIRST)
                  for token in tokens:
                      if token not in FIRST[rule.category]:
                          FIRST[rule.category].add(token)
                          changed = true

      until not changed

      return FIRST
```

Where `resolve_item` handles three cases:

```
  resolve_item(Terminal(t), FIRST)     = { variant_name(t) }
  resolve_item(NonTerminal(cat), FIRST) = FIRST[cat]
  resolve_item(Ident, FIRST)            = { "Ident" }
```

### 2.3 Why Fixed-Point?

Consider two mutually recursive categories:

```
  Category A:
    RuleA1: "x" B        // FIRST includes "x"
    RuleA2: B "+" A       // FIRST includes FIRST(B)

  Category B:
    RuleB1: "y"           // FIRST includes "y"
    RuleB2: A "-" B       // FIRST includes FIRST(A)
```

The dependency is circular: `FIRST(A)` depends on `FIRST(B)` which depends
on `FIRST(A)`. Fixed-point iteration resolves this:

```
  Iteration 1:
    FIRST(A) = { "x" }           (from RuleA1)
    FIRST(B) = { "y" }           (from RuleB1)

  Iteration 2:
    FIRST(A) = { "x", "y" }      (from RuleA2: FIRST(B) = {"y"})
    FIRST(B) = { "y", "x" }      (from RuleB2: FIRST(A) = {"x"})

  Iteration 3:
    FIRST(A) = { "x", "y" }      (no change)
    FIRST(B) = { "y", "x" }      (no change)

  Fixed point reached.
```

### 2.4 Convergence Guarantee

The fixed-point iteration is guaranteed to converge because:

1. FIRST sets can only grow (we only add tokens, never remove).
2. FIRST sets are bounded by the finite set of all terminal tokens.
3. Each iteration either adds at least one token or reaches the fixed point.

The maximum number of iterations is bounded by `|categories| * |terminals|`,
though in practice convergence occurs in 2-3 iterations. PraTTaIL bounds
the iteration count at `|categories| + 1` for safety.

### 2.5 Worked Example

For PraTTaIL's MeTTaIL grammar:

```
  Categories: Proc, Name, Int, Bool

  FIRST(Proc) = { "0", "for", "new", "!", "^", "(", "error",
                  Ident, Integer, Boolean }
  FIRST(Name) = { Ident, "@" }
  FIRST(Int)  = { Integer, Ident, "(", "-" }
  FIRST(Bool) = { Boolean, Ident, "(", "!" }
```

Notice that `Ident` appears in all four FIRST sets, reflecting that any
category can start with a variable reference.

---

## 3. FOLLOW Sets

### 3.1 Definition

The **FOLLOW set** of a nonterminal `A` is the set of terminal tokens that
can appear immediately after `A` in any valid derivation:

```
  FOLLOW(A) = { t in Terminals : S =>* alpha A t beta }
              union (if S =>* alpha A then { $ })
```

where `$` represents end-of-input.

### 3.2 When FOLLOW Sets Matter

FOLLOW sets are essential in LL(1) parsing for handling nullable (epsilon)
productions. If a rule `A -> alpha | epsilon` has `epsilon` as an
alternative, the parser must choose `epsilon` when the current token is in
`FOLLOW(A)` (meaning `A` should produce nothing, and the token belongs to
the enclosing context).

PraTTaIL does not use FOLLOW sets directly because:

1. PraTTaIL's grammar rules do not have epsilon alternatives (every rule
   produces at least one token).
2. The Pratt loop handles "when to stop" via binding power, not FOLLOW sets.
3. Collection rules use explicit delimiters and separators.

However, FOLLOW sets are implicitly used in two places:

- **Collection parsing:** When parsing a separated list, the parser checks
  whether the next token is a separator (continue) or a closing delimiter
  (stop). The closing delimiter is effectively in the FOLLOW set of the
  list element.

- **Cross-category dispatch:** When a cross-category rule like
  `Int "==" Int -> Bool` is tried and fails, the parser backtracks. The
  decision of _when_ to backtrack is informed by whether the next token
  could validly follow the source-category parse.

### 3.3 LL(1) FOLLOW Computation (for Reference)

```
  function compute_follow_sets(grammar, FIRST):
      FOLLOW[start_symbol] = { $ }
      for all other A: FOLLOW[A] = {}

      repeat:
          for each rule A -> X1 X2 ... Xn:
              for each Xi that is a nonterminal:
                  // Add FIRST(Xi+1 Xi+2 ... Xn) to FOLLOW(Xi)
                  // (what can follow Xi within this rule)
                  trailer = FIRST(Xi+1 Xi+2 ... Xn)
                  FOLLOW[Xi] = FOLLOW[Xi] union (trailer - {epsilon})

                  // If Xi+1 ... Xn can derive epsilon,
                  // add FOLLOW(A) to FOLLOW(Xi)
                  if epsilon in FIRST(Xi+1 ... Xn):
                      FOLLOW[Xi] = FOLLOW[Xi] union FOLLOW[A]

      until no change
```

---

## 4. Decision Automata

### 4.1 From FIRST Sets to Dispatch Tables

A **dispatch table** maps the current token to the parsing action to take.
PraTTaIL builds one dispatch table per category:

```
  DispatchTable for Proc:
  ┌─────────────┬─────────────────────────────────────────────┐
  │ Token       │ Action                                       │
  ├─────────────┼─────────────────────────────────────────────┤
  │ KwZero      │ Direct: call parse_pzero()                  │
  │ KwFor       │ Direct: call parse_pinput()                 │
  │ KwNew       │ Direct: call parse_pnew()                   │
  │ KwError     │ Direct: call parse_perror()                 │
  │ Bang        │ Direct: call parse_poutput() [prefix !]     │
  │ Caret       │ Direct: call parse_lambda()                 │
  │ LParen      │ Grouping: parse sub-expression              │
  │ Integer     │ Cast or Cross-category: try Int category    │
  │ Boolean     │ Cast or Cross-category: try Bool category   │
  │ Ident       │ Lookahead: multiple rules start with ident  │
  └─────────────┴─────────────────────────────────────────────┘
```

### 4.2 Dispatch Action Types

PraTTaIL defines five types of dispatch actions:

```
  ┌────────────────────────────────────────────────────────────────┐
  │ Action        │ Condition                │ Behavior             │
  ├────────────────────────────────────────────────────────────────┤
  │ Direct        │ Token uniquely           │ Call the parse       │
  │               │ identifies a rule        │ function directly    │
  ├────────────────────────────────────────────────────────────────┤
  │ Lookahead     │ Multiple rules share     │ Peek at token+1 to  │
  │               │ the same first token     │ disambiguate         │
  ├────────────────────────────────────────────────────────────────┤
  │ CrossCategory │ Token belongs to a       │ Try source category  │
  │               │ source category in a     │ parse, then check    │
  │               │ cross-category rule      │ for operator         │
  ├────────────────────────────────────────────────────────────────┤
  │ Cast          │ Token uniquely triggers  │ Parse source and     │
  │               │ embedding one category   │ wrap in target       │
  │               │ into another             │ constructor          │
  ├────────────────────────────────────────────────────────────────┤
  │ Variable      │ Fallback when no other   │ Treat as variable    │
  │               │ rule matches             │ reference            │
  └────────────────────────────────────────────────────────────────┘
```

### 4.3 LL(k) Lookahead as Small DFAs

When a single token of lookahead is insufficient (the `Lookahead` action),
PraTTaIL's approach is analogous to the decision automata in LL(*) parsing.
Conceptually, the disambiguating lookahead forms a small DFA:

```
  Ident ambiguity in Proc category:
    POutput starts: Name "!" ...  ->  Ident then "!"
    PVar starts:    Ident         ->  Ident then anything else

  Decision DFA:
         ┌── Ident ──> (?)  ── "!" ──> POutput
    (s0) ┤                   ── other ──> PVar
         └── (not Ident) ──> (error)

  In practice, PraTTaIL generates:
    Token::Ident => {
        match peek_ahead(tokens, pos, 1) {
            Some(Token::Bang) => parse_poutput(tokens, pos),
            _ => /* variable fallback */
        }
    }
```

This is a 2-token lookahead decision automaton. For most grammars, 1-2
tokens of lookahead suffice at each decision point.

---

## 5. Cross-Category Prediction

### 5.1 The Problem

Cross-category rules create a unique challenge. Consider:

```
  Category Bool:
    BEq : Int "==" Int         // Equality: takes Int operands, produces Bool
    BAnd: Bool "&&" Bool       // Conjunction: takes Bool operands
    BVar: identifier           // Bool variable

  Category Int:
    IAdd: Int "+" Int
    IVar: identifier
```

When parsing a Bool expression and the next token is `Ident`:
- It could be `BVar` (a Bool variable)
- It could be the start of `BEq` (parse an Int expression, then look for `==`)

Both `Bool` and `Int` have `Ident` in their FIRST sets.

### 5.2 FIRST Set Overlap Analysis

PraTTaIL computes the intersection, unique-to-A, and unique-to-B sets for
every pair of categories:

```
  function analyze_cross_category_overlaps(categories, FIRST):
      for each pair (A, B):
          ambiguous  = FIRST(A) intersect FIRST(B)
          unique_A   = FIRST(A) - FIRST(B)
          unique_B   = FIRST(B) - FIRST(A)

          if ambiguous is not empty:
              record CrossCategoryOverlap(A, B, ambiguous, unique_A, unique_B)
```

### 5.3 Worked Example

```
  FIRST(Int)  = { Integer, Ident, LParen, Minus }
  FIRST(Bool) = { Boolean, Ident, LParen, Bang }

  Intersection (ambiguous):  { Ident, LParen }
  Unique to Int:             { Integer, Minus }
  Unique to Bool:            { Boolean, Bang }
```

### 5.4 Dispatch Strategy Based on Overlap

```
  ┌─────────────────────────────────────────────────────────────────────┐
  │ Token type      │ Strategy                                          │
  ├─────────────────────────────────────────────────────────────────────┤
  │ Unique to       │ Deterministic: directly parse source category,   │
  │ source category │ then check for cross-category operator.          │
  │ (Integer, Minus)│ No backtracking needed.                          │
  │                 │                                                   │
  │ Unique to       │ Deterministic: parse own category directly.      │
  │ target category │ No backtracking needed.                          │
  │ (Boolean, Bang) │                                                   │
  │                 │                                                   │
  │ Ambiguous       │ Save position, try cross-category parse.         │
  │ (Ident, LParen) │ If operator found after source parse, commit.    │
  │                 │ If not, restore position and parse own category. │
  └─────────────────────────────────────────────────────────────────────┘
```

### 5.5 Generated Code Pattern

```rust
// Parsing Bool, encountering an Integer token:
Token::Integer(_) => {
    // UNIQUE to Int: deterministic cross-category dispatch
    let left = parse_Int(tokens, pos, 0)?;
    expect_token(tokens, pos, |t| matches!(t, Token::EqEq), "==")?;
    let right = parse_Int(tokens, pos, 0)?;
    Ok(Bool::BEq(Box::new(left), Box::new(right)))
}

// Parsing Bool, encountering an Ident token:
Token::Ident(_) => {
    // AMBIGUOUS: save/restore backtracking
    let saved = *pos;
    if let Ok(left) = parse_Int(tokens, pos, 0) {
        if peek_token(tokens, *pos).map_or(false,
            |t| matches!(t, Token::EqEq))
        {
            *pos += 1;  // consume "=="
            let right = parse_Int(tokens, pos, 0)?;
            return Ok(Bool::BEq(Box::new(left), Box::new(right)));
        }
    }
    // Cross-category parse failed -- backtrack
    *pos = saved;
    parse_Bool_own(tokens, pos)  // Try own-category parsing
}
```

---

## 6. Memoization

### 6.1 Packrat Parsing

**Packrat parsing** (Ford, 2002) is a memoization technique for PEG parsers.
The key idea: every call to `parse_A(pos)` is memoized, so if the same
nonterminal is attempted at the same position twice, the result is reused.

```
  memo = HashMap<(Category, Position), Result>

  function parse_A(pos):
      if (A, pos) in memo:
          return memo[(A, pos)]
      result = ... actual parsing ...
      memo[(A, pos)] = result
      return result
```

This guarantees O(n * |G|) time (linear in input size times the number of
grammar rules) at the cost of O(n * |G|) space.

### 6.2 PraTTaIL's Approach to Memoization

PraTTaIL does **not** use full packrat memoization. Instead, it minimizes the
need for memoization through prediction:

```
  ┌─────────────────────────────────────────────────────────────────┐
  │ Packrat approach:  Try everything, memoize to avoid re-parsing │
  │                                                                 │
  │ PraTTaIL approach: Predict the correct alternative using FIRST │
  │                    sets, only backtrack when truly ambiguous    │
  └─────────────────────────────────────────────────────────────────┘
```

The key insight is that **most parse decisions are deterministic** once FIRST
sets are analyzed. Backtracking only occurs at cross-category overlap points,
and even there, the overlap analysis minimizes the set of ambiguous tokens.

### 6.3 When Memoization Would Help

In pathological cases where cross-category overlaps are extensive, memoization
could prevent redundant re-parsing. For example:

```
  Parsing "x + y == z + w" as a Bool expression:
    1. Try: parse_Int(pos=0) -> succeeds, returns Int::Add(x, y)
    2. Check for "==": found at pos=3, consume
    3. Parse_Int(pos=4) -> succeeds, returns Int::Add(z, w)
    4. Result: Bool::BEq(Add(x,y), Add(z,w))

  Without memoization, if step 1 fails (no "==" follows), we backtrack
  and try parse_Bool_own(pos=0), which might re-parse "x" as a Bool variable.
  But "x" is only one token, so the re-parsing cost is minimal.
```

For PraTTaIL's current grammar structure, the cost of backtracking is bounded
by the length of one sub-expression parse. Full memoization would add space
overhead without measurable time benefit.

### 6.4 Future Memoization Strategy

If grammar evolution introduces more cross-category overlap (e.g., deeply
nested cross-category expressions), PraTTaIL could add selective memoization
at specific high-overlap decision points without adopting full packrat:

```
  // Selective memoization for specific categories at backtrack points
  let memo_key = (Category::Int, *pos);
  if let Some(cached) = memo.get(&memo_key) {
      return cached.clone();
  }
  let result = parse_Int(tokens, pos, 0);
  memo.insert(memo_key, result.clone());
```

This "targeted memoization" strategy combines prediction (to avoid unnecessary
memoization) with caching (to avoid redundant re-parsing at known backtrack
points).

---

## 7. Comparison with LL(1) Prediction

### 7.1 LL(1) Parse Tables

In LL(1) parsing, the parse table is a 2D array indexed by
`(nonterminal, token)`:

```
  table[A][t] = the production to use when parsing A and next token is t

  Conditions for LL(1):
    For all pairs of alternatives A -> alpha | beta:
      1. FIRST(alpha) intersect FIRST(beta) = {}
      2. If epsilon in FIRST(alpha), then FIRST(beta) intersect FOLLOW(A) = {}
```

### 7.2 How PraTTaIL Differs

PraTTaIL's dispatch tables are conceptually similar to LL(1) parse tables
but differ in three ways:

```
  ┌────────────────────┬─────────────────────────────────────────────┐
  │ LL(1)              │ PraTTaIL                                     │
  ├────────────────────┼─────────────────────────────────────────────┤
  │ Single table for   │ Separate dispatch table per category, plus │
  │ entire grammar     │ Pratt loop handles infix operators          │
  │                    │                                             │
  │ Conflicts are      │ Conflicts handled by:                      │
  │ grammar errors     │   - Lookahead (peek at token+1)            │
  │ (must refactor     │   - Cross-category backtracking            │
  │  grammar)          │   - Variable fallback                      │
  │                    │                                             │
  │ Left recursion     │ Left recursion handled natively by Pratt   │
  │ forbidden          │ loop (not a grammar restriction)           │
  │                    │                                             │
  │ One token          │ Adaptive: 1 token when sufficient,         │
  │ lookahead only     │ 2+ tokens at ambiguous points              │
  └────────────────────┴─────────────────────────────────────────────┘
```

### 7.3 Worked Comparison

Suppose we have:

```
  Rules for Proc:
    PInput : "for" "(" Name "<-" Name ")" "{" Proc "}"
    PNew   : "new" Name "in" "{" Proc "}"
    PVar   : identifier
```

**LL(1) approach:** Build a row of the parse table for `Proc`:

```
  table[Proc]["for"]   = PInput
  table[Proc]["new"]   = PNew
  table[Proc][Ident]   = PVar
  table[Proc][other]   = ERROR
```

This works because the FIRST sets are disjoint. No conflict.

**PraTTaIL approach:** Build a dispatch table for `Proc`:

```
  KwFor  -> Direct(PInput, parse_pinput)
  KwNew  -> Direct(PNew, parse_pnew)
  Ident  -> Variable(Proc)
  _      -> error
```

The result is essentially the same as LL(1) for this non-ambiguous case.
The difference emerges when FIRST sets overlap -- PraTTaIL gracefully
degrades to lookahead or backtracking, while LL(1) declares a grammar error.

---

## 8. Comparison with LR(1) Lookahead

### 8.1 LR(1) Items and Lookahead

In LR(1) parsing, lookahead is used differently. An LR(1) **item** is a
production with a position marker and a lookahead token:

```
  [A -> alpha . beta, t]

  Meaning: "We have seen alpha and expect to see beta.
            After reducing, the next token should be t."
```

The lookahead `t` determines when to reduce (shift-reduce decisions).

### 8.2 PraTTaIL vs. LR(1)

```
  ┌────────────────────┬─────────────────────────────────────────────┐
  │ LR(1) lookahead    │ PraTTaIL lookahead                          │
  ├────────────────────┼─────────────────────────────────────────────┤
  │ Used to decide     │ Used to decide which alternative to try    │
  │ shift vs. reduce   │ (prediction, not shift/reduce)             │
  │                    │                                             │
  │ Operates on the    │ Operates on the token stream directly      │
  │ parse stack        │ (top-down, not bottom-up)                  │
  │                    │                                             │
  │ Conflict means     │ Overlap means graceful degradation to      │
  │ grammar is not     │ backtracking (never a grammar error)       │
  │ LR(1)              │                                             │
  │                    │                                             │
  │ Fixed: always      │ Adaptive: 0 lookahead for direct dispatch, │
  │ exactly 1 token    │ 1-2 for ambiguous, full backtrack for      │
  │                    │ cross-category                             │
  └────────────────────┴─────────────────────────────────────────────┘
```

The fundamental philosophical difference is that LR(1) lookahead is used
**after** partial recognition (to decide how to reduce), while PraTTaIL's
lookahead is used **before** recognition begins (to decide which rule to
try). This is the top-down vs. bottom-up distinction applied to prediction.

---

## 9. Putting It All Together

### 9.1 The Prediction Pipeline

```
  Grammar rules
       │
       ▼
  ┌──────────────────────────────────────────┐
  │ 1. Compute FIRST sets                    │  compute_first_sets()
  │    Fixed-point iteration over categories │
  └──────────────────┬───────────────────────┘
                     │
                     ▼
  ┌──────────────────────────────────────────┐
  │ 2. Build dispatch tables                 │  build_dispatch_tables()
  │    For each category:                    │
  │      token -> rules mapping              │
  │      1 rule: Direct dispatch             │
  │      N rules: Lookahead dispatch         │
  │      var + other: Variable fallback      │
  └──────────────────┬───────────────────────┘
                     │
                     ▼
  ┌──────────────────────────────────────────┐
  │ 3. Analyze cross-category overlaps       │  analyze_cross_category_overlaps()
  │    For each category pair (A, B):        │
  │      Compute FIRST(A) intersect FIRST(B) │
  │      Identify unique and ambiguous tokens│
  └──────────────────┬───────────────────────┘
                     │
                     ▼
  ┌──────────────────────────────────────────┐
  │ 4. Generate dispatch code                │  generate_category_dispatch()
  │    Unique tokens: deterministic dispatch │
  │    Ambiguous tokens: save/restore        │
  │    Fallback: own-category parse          │
  └──────────────────────────────────────────┘
```

### 9.2 Dispatch Decision Flowchart

When the parser needs to parse a category `C` and sees token `t`:

```
  Token t
    │
    ▼
  Is t in DispatchTable[C]?
    │
    ├── Yes, Direct(rule) ──────────────> Call parse_rule()
    │
    ├── Yes, Lookahead(alts) ───────────> Peek at token+1
    │                                       │
    │                                       ├── Match alt ──> Call parse_alt()
    │                                       └── No match ──> Variable fallback
    │
    ├── Yes, CrossCategory(src, op) ────> Save pos
    │                                     Try parse_src()
    │                                       │
    │                                       ├── Success + op found ──> Commit
    │                                       └── Failure or no op ──> Restore pos
    │                                                                  parse_C_own()
    │
    ├── Yes, Cast(src, wrapper) ────────> parse_src(), wrap in Cat::wrapper()
    │
    ├── Yes, Variable(C) ──────────────> Parse as variable
    │
    └── No ──────────────────────────────> Error: unexpected token
```

### 9.3 Complexity

```
  ┌──────────────────────────────┬─────────────────────────────────┐
  │ Phase                        │ Complexity                       │
  ├──────────────────────────────┼─────────────────────────────────┤
  │ FIRST set computation        │ O(|rules| * |categories| *      │
  │                              │   |terminals|)                   │
  │ Dispatch table construction  │ O(|rules| * |terminals|)        │
  │ Overlap analysis             │ O(|categories|^2 * |terminals|) │
  │ Per-token dispatch (runtime) │ O(1) for direct dispatch        │
  │                              │ O(1) for 1-token lookahead      │
  │                              │ O(k) for cross-category         │
  │                              │   backtracking (k = sub-expr    │
  │                              │   length)                       │
  └──────────────────────────────┴─────────────────────────────────┘
```

All compile-time analysis phases are polynomial and fast. The runtime dispatch
is O(1) for the common case (deterministic dispatch) and O(k) for the
backtracking case, where `k` is bounded by the length of one sub-expression.
Overall parsing remains O(n) in the input length.

---

## 10. Summary

| Concept | Role in PraTTaIL |
|---|---|
| FIRST sets | Determine which tokens can start each category |
| FOLLOW sets | Implicit in collection delimiters and Pratt loop termination |
| Dispatch tables | Map first token to parse action per category |
| Direct dispatch | O(1) when FIRST sets are disjoint |
| Lookahead dispatch | Peek at token+1 when FIRST sets overlap within a category |
| Cross-category overlap | FIRST set intersection analysis across categories |
| Deterministic cross-category | Unique tokens trigger direct cross-category parse |
| Backtracking cross-category | Ambiguous tokens use save/restore |
| Memoization | Not currently needed; targeted memoization is a future option |

The prediction engine transforms what would be trial-and-error parsing into
mostly-deterministic dispatch. By analyzing FIRST set overlaps at compile
time, PraTTaIL generates parsers that backtrack only when structurally
necessary and dispatch directly in all other cases.

---

## References

1. Aho, A. V., Sethi, R., & Ullman, J. D. (1986). _Compilers: Principles,
   Techniques, and Tools_ (the "Dragon Book"). Addison-Wesley. Chapter 4.
2. Ford, B. (2002). "Packrat Parsing: Simple, Powerful, Lazy, Linear Time."
   _ICFP_, pp. 36--47.
3. Parr, T. & Fisher, K. (2011). "LL(*): The Foundation of the ANTLR Parser
   Generator." _PLDI_, pp. 425--436.
4. Parr, T., Harwell, S., & Fisher, K. (2014). "Adaptive LL(*) Parsing: The
   Power of Dynamic Analysis." _OOPSLA_, pp. 579--598.
