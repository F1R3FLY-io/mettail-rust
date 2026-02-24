# PraTTaIL: Prediction Engine

**Date:** 2026-02-14 (updated 2026-02-16)

---

## Table of Contents

1. [Purpose](#1-purpose)
2. [FIRST Set Computation](#2-first-set-computation)
3. [Nullable Category Detection](#3-nullable-category-detection)
4. [FOLLOW Set Computation](#4-follow-set-computation)
5. [Dispatch Table Construction](#5-dispatch-table-construction)
6. [Cross-Category Overlap Analysis](#6-cross-category-overlap-analysis)
7. [Grammar Warning Detection](#7-grammar-warning-detection)
8. [Sync Predicate Generation](#8-sync-predicate-generation)
9. [When Memoization Is Generated vs Unnecessary](#9-when-memoization-is-generated-vs-unnecessary)
10. [Decision Automaton Construction](#10-decision-automaton-construction)
11. [Worked Example: Calculator (3 Types, Cross-Category Rules)](#11-worked-example-calculator-3-types-cross-category-rules)

---

## 1. Purpose

The prediction engine computes which tokens can begin and follow expressions in
each category and uses this information to generate deterministic dispatch tables,
sync predicates for error recovery, and grammar quality warnings. Its outputs
drive five critical decisions:

1. **Prefix dispatch.** When `parse_Int_prefix` sees a token, the dispatch
   table tells it which rule to invoke---or whether to use lookahead.

2. **Cross-category routing.** When `parse_Bool` sees a token that could
   start either a `Bool` expression or an `Int` expression (for the `Eq`
   rule `Int "==" Int → Bool`), the overlap analysis determines whether
   deterministic dispatch or save/restore backtracking is needed.

3. **Error reporting.** FIRST sets provide the "expected" set in error
   messages: `"expected Bool expression, found '+' at position 5"`.

4. **Error recovery.** FOLLOW sets drive sync predicate generation:
   `is_sync_Int()` identifies tokens where the recovering parser can
   resume after an error (tokens that can legitimately follow an Int
   expression).

5. **Grammar diagnostics.** Warning detection identifies potential
   grammar issues (ambiguous prefixes, left recursion, unused categories)
   at compile time without blocking compilation.

---

## 2. FIRST Set Computation

### Definition

For a grammar category C, `FIRST(C)` is the set of token variant names that
can appear as the first token of any expression in C. This includes:

- **Terminal tokens** from rules that begin with a terminal
  (e.g., `PZero` starts with `"{}"`  →  `EmptyBraces` in `FIRST(Proc)`).

- **Identifier token** from variable rules and rules that begin with a
  nonterminal parameter
  (e.g., `IVar` starts with `Ident`  →  `Ident` in `FIRST(Int)`).

- **Transitive tokens** from rules that begin with a reference to another
  category
  (e.g., if rule `CastInt . k:Int |- k : Proc`, then `FIRST(Int)` is
  included in `FIRST(Proc)`).

### Fixed-Point Iteration Algorithm

FIRST sets for recursive or mutually-recursive categories require iterative
computation. The algorithm is a standard fixed-point iteration:

```
INITIALIZE:
  For each category C:
    FIRST(C) = empty set

ITERATE:
  repeat:
    snapshot = copy of all FIRST set sizes
    for each rule R:
      if R is an infix rule: skip (infix rules are handled by Pratt loop)
      for each first_item in R.first_items:
        match first_item:
          Terminal(t)     → add terminal_to_variant_name(t) to FIRST(R.category)
          NonTerminal(C') → add all tokens from FIRST(C') to FIRST(R.category)
          Ident           → add "Ident" to FIRST(R.category)
    if all FIRST set sizes unchanged from snapshot: break

BOUND: At most |categories| + 1 iterations (each iteration must add at
least one new token to some FIRST set, or the algorithm terminates).
```

### Handling Recursive Categories

Consider a grammar where `Proc` has a rule `CastInt . k:Int |- k : Proc`
and `Int` has no reference back to `Proc`. The FIRST set computation:

```
Iteration 0:
  FIRST(Proc) = {}
  FIRST(Int)  = {}

Iteration 1:
  FIRST(Int) += {Ident}           (from IVar rule)
  FIRST(Int) += {KwInteger}       (from NumLit rule, if terminal "Integer")
  FIRST(Proc) += {EmptyBraces}    (from PZero rule)
  FIRST(Proc) += {Star}           (from PDrop rule)
  FIRST(Proc) += {Ident}          (from PVar rule)
  FIRST(Proc) += FIRST(Int)       (from CastInt rule, NonTerminal("Int"))
               = {Ident, KwInteger}  (but Ident already present)

Iteration 2:
  No changes → terminate.
```

For mutually recursive categories (e.g., `Proc` contains `Name` references
and `Name` contains `Proc` references via `NQuote`), the iteration may
require 2-3 rounds:

```
Iteration 0:
  FIRST(Proc) = {}, FIRST(Name) = {}

Iteration 1:
  FIRST(Name) += {At}             (from NQuote: "@" "(" Proc ")")
  FIRST(Name) += {Ident}          (from NVar)
  FIRST(Proc) += {EmptyBraces, Star, LBrace, Ident, Caret, ...}
  FIRST(Proc) += FIRST(Name)      (from POutput: n "!" "(" q ")")
               = {At, Ident}      (Ident already present)

Iteration 2:
  FIRST(Name) += FIRST(Proc)?     (only if Name has a rule starting with Proc)
  No new tokens from Proc → FIRST(Name) unchanged.
  FIRST(Proc) += FIRST(Name)      (still {At, Ident}, no new tokens)
  No changes → terminate.
```

### Convergence Guarantee

The fixed-point terminates because:

1. FIRST sets are monotonically growing (tokens are only added, never removed).
2. The total number of distinct token variant names is finite (bounded by
   the number of terminals plus built-in token types).
3. Each iteration that does not terminate must add at least one new token
   to some FIRST set.

Therefore, the algorithm terminates in at most `|total_tokens|` iterations,
but in practice it terminates in `|categories| + 1` iterations because
each iteration propagates through one level of category references.

---

## 3. Nullable Category Detection

### Definition

A category C is **nullable** if it contains a rule whose syntax pattern has
zero items — that is, the rule matches without consuming any tokens. Concretely,
a nullable rule looks like a unit constructor with no syntax:

```
Unit . |- : Cat;
```

This rule produces `Cat::Unit` without consuming any input tokens.

### Practical Note

MeTTaIL grammars do not currently have nullable categories — every defined rule
consumes at least one token. The nullable flag exists for correctness of the
FOLLOW set fixed-point algorithm: if a category B is nullable, then `FOLLOW(A)`
must include tokens that can follow B in any syntax pattern where B appears
after A, because B might produce nothing.

### Algorithm

A category is nullable if any of its rules has an empty syntax pattern AND
no non-terminal parameters from other categories (which would require consuming
tokens). The nullable flag is stored as `FirstSet.nullable` and computed
during FIRST set iteration.

```
IS_NULLABLE(category C):
  for each rule R in C:
    if R.syntax is empty:
      if R has no non-terminal params from other categories:
        return true
  return false
```

### Usage

The nullable flag is used by:

1. **FOLLOW set computation**: if category B is nullable, then
   `FOLLOW(A) += FOLLOW(B)` when A is followed by B in a syntax pattern.

2. **FIRST set computation**: if a non-terminal B at the start of a rule
   is nullable, then FIRST(C) should include tokens from the next syntax
   item as well (not currently applicable in practice because MeTTaIL
   grammars don't have nullable categories in leading positions).

---

## 4. FOLLOW Set Computation

### Definition

For a grammar category C, `FOLLOW(C)` is the set of token variant names that
can appear immediately after an expression of category C in any valid parse.
FOLLOW sets are critical for error recovery: they tell the recovering parser
which tokens represent safe synchronization points.

### Algorithm

`compute_follow_sets_from_inputs()` in `prediction.rs` implements a standard
fixed-point iteration over `FollowSetInput` records (lightweight projections
containing only the `category` and `syntax` fields needed by the algorithm).

```
INITIALIZE:
  For the primary category P:
    FOLLOW(P) = { Eof }    // The primary category is followed by end-of-input
  For all other categories C:
    FOLLOW(C) = { }

ITERATE:
  repeat:
    snapshot = copy of all FOLLOW set sizes
    for each input I (rule with category and syntax):
      for each position i in I.syntax:
        if I.syntax[i] is NonTerminal(B):
          // What can follow B in this rule?
          rest = I.syntax[i+1..]
          FOLLOW(B) += FIRST(rest)           // Tokens that start the rest
          if rest is empty OR rest is nullable:
            FOLLOW(B) += FOLLOW(I.category)  // B is at end: inherit parent's FOLLOW
    if all FOLLOW set sizes unchanged from snapshot: break

BOUND: At most |categories| + 1 iterations (each iteration propagates through
one level of category references).
```

### Native Literal Token Augmentation

FOLLOW sets are augmented with native literal tokens in the same way as
FIRST sets. If a category has `native_type` of `i32`/`i64`, then `Integer`
is considered a valid token in the computation. Similarly, `Boolean` for
`bool` types.

### Data Bundle: FollowSetInput

The `FollowSetInput` struct is a lightweight Send+Sync projection of
`RuleSpec`:

```rust
pub struct FollowSetInput {
    pub category: String,
    pub syntax: Vec<SyntaxItemSpec>,
}
```

This allows FOLLOW set computation to operate on Send+Sync data without
needing access to the `!Send` `LanguageSpec`.

### Example

For the TypedCalc grammar:

```
Rules:
  Add . a:Int, b:Int |- a "+" b : Int
  Mul . a:Int, b:Int |- a "*" b : Int
  Eq  . a:Int, b:Int |- a "==" b : Bool

FOLLOW(Int) starts as {}
FOLLOW(Bool) starts as {}
Int is primary: FOLLOW(Int) = {Eof}

Iteration 1:
  Add: syntax = [a:Int, "+", b:Int]
    a:Int at pos 0: rest = ["+", b:Int]
      FOLLOW(Int) += {"+"} = {Eof, Plus}
    b:Int at pos 2: rest = []
      FOLLOW(Int) += FOLLOW(Int) = {Eof, Plus} (already present)

  Mul: syntax = [a:Int, "*", b:Int]
    a:Int at pos 0: rest = ["*", b:Int]
      FOLLOW(Int) += {"*"} = {Eof, Plus, Star}
    b:Int at pos 2: rest = []
      FOLLOW(Int) += FOLLOW(Int) (already present)

  Eq: syntax = [a:Int, "==", b:Int]
    a:Int at pos 0: rest = ["==", b:Int]
      FOLLOW(Int) += {"=="} = {Eof, Plus, Star, EqEq}
    b:Int at pos 2: rest = []
      FOLLOW(Int) += FOLLOW(Bool) = {} (no new tokens)

Iteration 2:
  No changes → terminate.

Final: FOLLOW(Int) = {Eof, Plus, Star, EqEq}
       FOLLOW(Bool) = {Eof}
```

---

## 5. Dispatch Table Construction

### Structure

For each category C, the dispatch table maps first tokens to dispatch
actions:

```
DispatchTable {
  category: "Proc",
  entries: {
    "EmptyBraces" → Direct { rule_label: "PZero", parse_fn: "parse_pzero" },
    "Star"        → Direct { rule_label: "PDrop", parse_fn: "parse_pdrop" },
    "LBrace"      → Direct { rule_label: "PPar",  parse_fn: "parse_ppar"  },
    "Ident"       → Lookahead { ... } or Variable { ... },
    "KwError"     → Direct { rule_label: "Err",   parse_fn: "parse_err"   },
    ...
  },
  default_action: Some(Variable { category: "Proc" }),
}
```

### Algorithm

```
BUILD_DISPATCH(category C, rules, first_sets):
  1. Collect all non-infix rules for category C.

  2. Build token_to_rules map:
     For each rule R in C:
       For each first_item in R.first_items:
         Compute the set of tokens T this item contributes.
         For each t in T:
           token_to_rules[t].append(R)

  3. For each token t in token_to_rules:
     If only one rule matches:
       If rule is variable: entries[t] = Variable(C)
       If rule is cast:     entries[t] = Cast(source_cat, wrapper)
       Else:                entries[t] = Direct(rule.label, parse_fn)

     If multiple rules match:
       Partition into non-variable and variable rules.
       If only variable rules:
         entries[t] = Variable(C)
       If one non-var rule + variable fallback:
         entries[t] = Lookahead(
           alternatives: [non_var_rule],
           fallback: Some(C)
         )
       If multiple non-var rules:
         entries[t] = Lookahead(
           alternatives: all non_var_rules,
           fallback: if any var rules then Some(C) else None
         )
```

### Dispatch Actions

```
┌───────────────────┬─────────────────────────────────────────────────────┐
│ Action            │ Description                                         │
├───────────────────┼─────────────────────────────────────────────────────┤
│ Direct            │ Unambiguous: call parse_<rule>() directly           │
│ Lookahead         │ Ambiguous first token: peek at next token(s) to     │
│                   │   disambiguate, with optional variable fallback     │
│ CrossCategory     │ Try parsing source category, then expect operator   │
│ Cast              │ Parse source category and wrap in constructor       │
│ Grouping          │ Parenthesized expression: consume "(", recurse, ")" │
│ Variable          │ Fall through to variable handler for this category  │
└───────────────────┴─────────────────────────────────────────────────────┘
```

---

## 6. Cross-Category Overlap Analysis

### Motivation

Cross-category rules like `Eq . a:Int, b:Int |- a "==" b : Bool` create
a parsing challenge: when `parse_Bool` sees a token, it must decide whether
to try parsing an `Int` expression (hoping to find `==` afterwards) or to
parse a native `Bool` expression.

The overlap analysis partitions tokens into three sets for each pair of
categories (A, B):

```
  unique_to_A:     Tokens in FIRST(A) but not FIRST(B)
  unique_to_B:     Tokens in FIRST(B) but not FIRST(A)
  ambiguous_tokens: Tokens in both FIRST(A) and FIRST(B)
```

### Algorithm

```
ANALYZE_OVERLAPS(categories, first_sets):
  overlaps = {}
  for each pair (A, B) where A != B:
    first_A = first_sets[A]
    first_B = first_sets[B]
    intersection = first_A INTERSECT first_B
    if intersection is not empty:
      overlaps[(A, B)] = CrossCategoryOverlap {
        category_a: A,
        category_b: B,
        ambiguous_tokens: intersection,
        unique_to_a: first_A MINUS first_B,
        unique_to_b: first_B MINUS first_A,
      }
  return overlaps
```

### How Overlap Drives Dispatch

For a cross-category rule `Eq: Int "==" Int → Bool`, the dispatch
wrapper for `parse_Bool` uses the overlap to generate three code paths:

```
match current_token:
  // Case 1: Token unique to Int (e.g., Integer literal "42")
  //   Deterministic: must be cross-category path.
  Token::Integer(_) => {
    let left = parse_Int(tokens, pos, 0)?;
    expect_token(tokens, pos, Token::EqEq, "==")?;
    let right = parse_Int(tokens, pos, 0)?;
    Ok(Bool::Eq(Box::new(left), Box::new(right)))
  }

  // Case 2: Token unique to Bool (e.g., "true", "false")
  //   Deterministic: must be own-category path.
  Token::Boolean(_) => {
    parse_Bool_own(tokens, pos)
  }

  // Case 3: Ambiguous token (e.g., Ident -- could be Int var or Bool var)
  //   Save/restore backtracking.
  Token::Ident(_) => {
    let saved = *pos;
    if let Ok(left) = parse_Int(tokens, pos, 0) {
      if peek_token(tokens, *pos) == Some(&Token::EqEq) {
        *pos += 1;
        let right = parse_Int(tokens, pos, 0)?;
        return Ok(Bool::Eq(Box::new(left), Box::new(right)));
      }
    }
    *pos = saved;          // Backtrack
    parse_Bool_own(tokens, pos)  // Try own category
  }
```

The backtracking is **bounded**: we attempt to parse one Int expression and
peek at one token. If the operator is not found, we restore and try the
alternative. This is not general backtracking---it is a statically-determined
two-way branch.

---

## 7. Grammar Warning Detection

### Purpose

PraTTaIL detects potential grammar issues at compile time and emits warnings
that don't block compilation. This helps grammar authors identify problems
before encountering runtime parse failures.

### GrammarWarning Enum

```rust
pub enum GrammarWarning {
    /// Multiple non-variable rules in the same category start with the same token.
    AmbiguousPrefix {
        token: String,
        category: String,
        rules: Vec<String>,   // labels of the conflicting rules
    },

    /// A rule's first syntax item is a non-terminal of the same category,
    /// which would cause infinite left recursion in a recursive descent parser.
    LeftRecursion {
        rule_label: String,
        category: String,
    },

    /// A category is defined but never referenced by any rule's non-terminal
    /// parameters in other categories (may indicate dead grammar rules).
    UnusedCategory {
        category: String,
    },
}
```

### Detection Algorithm

`detect_grammar_warnings()` in `prediction.rs` performs three checks:

```
DETECT_WARNINGS(rules, categories, all_syntax):
  warnings = []

  // Check 1: Ambiguous prefix tokens
  for each category C:
    token_to_rules = {}
    for each non-infix, non-variable rule R in C:
      for each token T in FIRST({R}):
        token_to_rules[T].append(R.label)
    for each (token, rule_list) in token_to_rules:
      if rule_list.len() > 1:
        warnings.push(AmbiguousPrefix { token, category: C, rules: rule_list })

  // Check 2: Left recursion
  for each rule R:
    if R.syntax[0] is NonTerminal(C) where C == R.category:
      warnings.push(LeftRecursion { rule_label: R.label, category: C })

  // Check 3: Unused categories
  referenced = set of categories appearing as NonTerminal in any rule
  for each category C:
    if C is not primary AND C not in referenced:
      warnings.push(UnusedCategory { category: C })

  return warnings
```

### Behavior

Warnings are emitted at compile time via `eprintln!` during the `language! { ... }`
macro expansion. They do NOT prevent compilation---the grammar is still usable.
This is intentional: some grammar patterns (like apparent left recursion) may be
handled correctly by the Pratt parser's infix loop even though they would be
problematic in a pure recursive descent parser.

---

## 8. Sync Predicate Generation

### Purpose

Sync predicates identify tokens where the recovering parser can resume after
encountering an error. They are used by the `sync_to()` helper function to
advance past error tokens to a synchronization point.

### Algorithm

`generate_sync_predicate()` in `prediction.rs` generates one sync predicate
function per grammar category:

```
GENERATE_SYNC(category C, FOLLOW(C), grammar_terminals):
  sync_tokens = FOLLOW(C)

  // Add structural delimiters, but ONLY if they appear in the grammar
  for delimiter in [")", "}", "]", ";", ","]:
    if delimiter in grammar_terminals:
      sync_tokens += { terminal_to_variant_name(delimiter) }

  // Always include Eof
  sync_tokens += { Eof }

  // Generate: fn is_sync_<C>(token) → bool { matches!(token, ...) }
```

### Critical Design Constraint

Sync predicates must NOT hardcode structural delimiters. If a grammar does
not use `;` as a terminal, then `Token::Semi` does not exist in the generated
`Token<'a>` enum, and including it would cause a compile error. The function
takes `grammar_terminals: &BTreeSet<String>` and checks membership before
including each delimiter.

### Example

For a grammar with `+`, `*`, `==`, `(`, `)` terminals:

```rust
fn is_sync_Int<'a>(token: &Token<'a>) -> bool {
    matches!(token,
        Token::Eof
        | Token::RParen    // ")" is in grammar_terminals
        | Token::Plus      // In FOLLOW(Int) from Add rule
        | Token::Star      // In FOLLOW(Int) from Mul rule
        | Token::EqEq      // In FOLLOW(Int) from Eq rule
    )
    // Note: Token::Semi NOT included (no ";" in grammar)
    // Note: Token::Comma NOT included (no "," in grammar terminals)
}
```

### Usage

The sync predicates are used by:

1. **`sync_to(tokens, pos, is_sync_Cat)`** -- advances past error tokens
2. **`parse_Cat_recovering()`** -- calls sync_to after prefix/infix failures
3. **`parse_recovering(input)`** -- top-level entry point for multi-error parsing

---

## 9. When Memoization Is Generated vs Unnecessary

### When Memoization Is Unnecessary

For most grammars, memoization is **not needed** because:

1. **Pratt parsing is linear.** Each token is consumed exactly once by the
   Pratt loop. There is no re-parsing of the same input range.

2. **RD handlers are called once per match.** Each `parse_<rule>()` function
   is invoked when its leading terminal has already been matched by the
   dispatch table. It does not speculatively parse.

3. **Cross-category backtracking is bounded.** The save/restore pattern
   parses at most one sub-expression before deciding. The re-parse on
   backtrack covers the same token range, but this happens at most once
   per ambiguous token at each call site.

### When Memoization Would Be Generated

Memoization would be generated if:

1. **A category appears as a sub-expression in multiple cross-category rules
   with different operators.** For example, if both `Eq: Int "==" Int → Bool`
   and `Lt: Int "<" Int → Bool` exist, and the token is ambiguous, the
   parser might parse `Int` twice (once for the `==` attempt, once for the
   `<` attempt). A memo table for `parse_Int` at each position would prevent
   re-parsing.

2. **Grammar rules allow the same nonterminal to appear multiple times at the
   same position.** This does not occur in current MeTTaIL grammars because
   cross-category rules are dispatched by their operator token, not by
   re-parsing the source category.

Currently, PraTTaIL does **not** generate memoization tables. If future
grammars require it, the implementation would add:

```rust
thread_local! {
    static MEMO_INT: RefCell<HashMap<usize, Option<(Int, usize)>>> =
        RefCell::new(HashMap::new());
}

fn parse_Int_memo(tokens: &[(Token, Span)], pos: &mut usize, min_bp: u8)
    -> Result<Int, String>
{
    let key = *pos;
    if let Some(cached) = MEMO_INT.with(|m| m.borrow().get(&key).cloned()) {
        match cached {
            Some((val, end_pos)) => { *pos = end_pos; return Ok(val); }
            None => return Err("cached failure".into()),
        }
    }
    let result = parse_Int(tokens, pos, min_bp);
    let entry = result.as_ref().ok().map(|v| (v.clone(), *pos));
    MEMO_INT.with(|m| m.borrow_mut().insert(key, entry));
    result
}
```

---

## 10. Decision Automaton Construction

### Concept

For categories with ambiguous dispatch (multiple rules starting with the
same token), PraTTaIL constructs a **decision automaton** that examines
tokens at position +0, +1, +2, etc. to determine which rule to invoke.

### Structure

```
Decision automaton for Proc prefix dispatch on Ident:

  position 0: Token::Ident(_)
                │
                ├── position 1: Token::Bang       → POutput rule (n "!" ...)
                │
                ├── position 1: Token::Question   → PInputs (via Name)
                │
                ├── position 1: infix operator    → PVar (variable)
                │
                ├── position 1: Token::Eof        → PVar (variable)
                │
                └── position 1: other             → PVar (variable, fallback)
```

### Generated Code

The decision automaton is generated as nested match expressions:

```rust
Token::Ident(ref name) => {
    match peek_ahead(tokens, *pos, 1) {
        Some(Token::Bang) => {
            // Parse Name (which consumes the Ident), then dispatch to POutput
            parse_poutput(tokens, pos)
        }
        _ => {
            // Default: treat as variable
            let var_name = name.clone();
            *pos += 1;
            Ok(Proc::PVar(OrdVar(Var::Free(get_or_create_var(var_name)))))
        }
    }
}
```

### When Decision Automata Are Used

Decision automata are generated when:

1. A token maps to more than one non-variable rule in the dispatch table
   (i.e., `DispatchAction::Lookahead` with multiple alternatives).

2. The second token provides sufficient discrimination. If the second
   token is also ambiguous, deeper lookahead is needed (currently not
   implemented; would fall back to save/restore).

For current MeTTaIL grammars, the deepest lookahead needed is 1 token
ahead, because:

- Most structural rules start with a unique terminal (`*`, `{}`, `@`, etc.)
- The only ambiguous cases involve `Ident` followed by a distinguishing
  terminal (`!`, `?`, `[`) vs. `Ident` as a variable (followed by an
  infix operator or end of expression).

---

## 11. Worked Example: Calculator (3 Types, Cross-Category Rules)

### Language Definition

```
types:
  Int (i32)     -- primary
  Bool (bool)
  Str (str)

rules:
  Add     . a:Int,  b:Int  |- a "+"  b : Int   (infix, left-assoc)
  Sub     . a:Int,  b:Int  |- a "-"  b : Int   (infix, left-assoc)
  Pow     . a:Int,  b:Int  |- a "^"  b : Int   (infix, right-assoc)
  Eq      . a:Int,  b:Int  |- a "==" b : Bool  (cross-category)
  EqBool  . a:Bool, b:Bool |- a "==" b : Bool  (same-category infix)
  EqStr   . a:Str,  b:Str  |- a "==" b : Bool  (cross-category)
  Comp    . a:Bool, b:Bool |- a "&&" b : Bool  (same-category infix)
  Not     . a:Bool         |- "not" a  : Bool  (prefix)
  Len     . s:Str          |- "|" s "|" : Int   (delimited)
  Concat  . a:Str,  b:Str  |- a "++" b : Str   (infix, left-assoc)
  AddStr  . a:Str,  b:Str  |- a "+"  b : Str   (infix, left-assoc)
  NumLit  : Int    (literal integer)
  BoolLit : Bool   (literal boolean)
  StringLit : Str  (literal string)
  IVar    : Int    (variable)
  BVar    : Bool   (variable)
  SVar    : Str    (variable)
```

### Step 1: FIRST Set Computation

**Iteration 0:**
```
FIRST(Int)  = {}
FIRST(Bool) = {}
FIRST(Str)  = {}
```

**Iteration 1:** Process non-infix rules.
```
FIRST(Int)  += {Ident}          (from IVar)
FIRST(Int)  += {Integer}        (from NumLit, native i32 → Integer token)
FIRST(Int)  += {Pipe}           (from Len: "|" s "|")

FIRST(Bool) += {Ident}          (from BVar)
FIRST(Bool) += {KwTrue, KwFalse} (from BoolLit, native bool)
FIRST(Bool) += {KwNot}          (from Not: "not" a)
FIRST(Bool) += FIRST(Int)       (from Eq: a:Int "==" b:Int → Bool)
             = {Ident, Integer, Pipe}  (Ident already present)
FIRST(Bool) += FIRST(Str)       (from EqStr: a:Str "==" b:Str → Bool)
             = {}                (Str is still empty)

FIRST(Str)  += {Ident}          (from SVar)
FIRST(Str)  += {StringLit}      (from StringLit, native str)
```

**Iteration 2:** Propagate Str into Bool.
```
FIRST(Bool) += FIRST(Str)       (from EqStr)
             = {Ident, StringLit}  (Ident already present, StringLit is new)
```

**Iteration 3:** No changes. Terminate.

**Final FIRST sets:**
```
FIRST(Int)  = {Ident, Integer, Pipe}
FIRST(Bool) = {Ident, Integer, Pipe, KwTrue, KwFalse, KwNot, StringLit}
FIRST(Str)  = {Ident, StringLit}
```

### Step 2: Cross-Category Overlap Analysis

```
Overlap(Int, Bool):
  ambiguous:    {Ident, Integer, Pipe}        (in both)
  unique_to_Int: {}                            (all of Int's are in Bool)
  unique_to_Bool: {KwTrue, KwFalse, KwNot, StringLit}

Overlap(Int, Str):
  ambiguous:    {Ident}
  unique_to_Int: {Integer, Pipe}
  unique_to_Str: {StringLit}

Overlap(Str, Bool):
  ambiguous:    {Ident, StringLit}
  unique_to_Str: {}                            (all of Str's are in Bool)
  unique_to_Bool: {Integer, Pipe, KwTrue, KwFalse, KwNot}

Overlap(Bool, Int):
  ambiguous:    {Ident, Integer, Pipe}
  unique_to_Bool: {KwTrue, KwFalse, KwNot, StringLit}
  unique_to_Int: {}
```

### Step 3: Dispatch Tables

**Int dispatch table:**
```
  Integer  → Direct: NumLit
  Ident    → Lookahead: {IVar (fallback: variable)}
  Pipe     → Direct: Len
  LParen   → Grouping
```

**Bool dispatch table (without cross-category):**
```
  KwTrue   → Direct: BoolLit
  KwFalse  → Direct: BoolLit
  KwNot    → Direct: Not
  Ident    → Lookahead: {BVar (fallback: variable)}
  LParen   → Grouping
```

**Str dispatch table:**
```
  StringLit → Direct: StringLit
  Ident     → Lookahead: {SVar (fallback: variable)}
  LParen    → Grouping
```

### Step 4: Cross-Category Dispatch for Bool

Bool has two cross-category rules: `Eq` (from Int) and `EqStr` (from Str).

The `parse_Bool` wrapper becomes:

```
match current_token:
  // Tokens unique to Bool → parse_Bool_own
  Token::KwTrue | Token::KwFalse | Token::KwNot => {
    parse_Bool_own(tokens, pos)
  }

  // Integer unique to Int (not in Bool's own first set excluding cross)
  // Actually Integer IS in Bool's FIRST because of cross-category.
  // But it's unique_to_Int relative to Bool's *own* rules.
  // The dispatch checks source FIRST vs target FIRST.
  Token::Integer(_) => {
    // Deterministic: must be Eq path (Int "==" Int → Bool)
    let left = parse_Int(tokens, pos, 0)?;
    expect_token(tokens, pos, Token::EqEq, "==")?;
    let right = parse_Int(tokens, pos, 0)?;
    Ok(Bool::Eq(Box::new(left), Box::new(right)))
  }

  // Pipe unique to Int → Eq path
  Token::Pipe => {
    let left = parse_Int(tokens, pos, 0)?;
    expect_token(tokens, pos, Token::EqEq, "==")?;
    let right = parse_Int(tokens, pos, 0)?;
    Ok(Bool::Eq(Box::new(left), Box::new(right)))
  }

  // StringLit unique to Str → EqStr path
  Token::StringLit(_) => {
    let left = parse_Str(tokens, pos, 0)?;
    expect_token(tokens, pos, Token::EqEq, "==")?;
    let right = parse_Str(tokens, pos, 0)?;
    Ok(Bool::EqStr(Box::new(left), Box::new(right)))
  }

  // Ident is ambiguous (in Int, Bool, and Str FIRST sets)
  Token::Ident(_) => {
    let saved = *pos;
    // Try Int "==" Int path
    if let Ok(left) = parse_Int(tokens, pos, 0) {
      if peek_token(tokens, *pos) == Some(&Token::EqEq) {
        *pos += 1;
        let right = parse_Int(tokens, pos, 0)?;
        return Ok(Bool::Eq(Box::new(left), Box::new(right)));
      }
    }
    // Backtrack and try Str "==" Str path
    *pos = saved;
    if let Ok(left) = parse_Str(tokens, pos, 0) {
      if peek_token(tokens, *pos) == Some(&Token::EqEq) {
        *pos += 1;
        let right = parse_Str(tokens, pos, 0)?;
        return Ok(Bool::EqStr(Box::new(left), Box::new(right)));
      }
    }
    // Backtrack and try own-category (Bool)
    *pos = saved;
    parse_Bool_own(tokens, pos)
  }

  // Fallback
  _ => parse_Bool_own(tokens, pos)
```

### Parsing Trace: `3 == 4`

```
Input tokens: [Integer(3), EqEq, Integer(4), Eof]

1. parse_Bool(tokens, pos=0, min_bp=0)
2. Cross-category dispatch sees Integer(3):
   - Integer is unique to Int → deterministic Eq path
3. parse_Int(tokens, pos=0, min_bp=0)
   - parse_Int_prefix sees Integer(3) → NumLit(3), pos=1
   - Pratt loop: peek = EqEq, infix_bp(EqEq) = None (not an Int infix)
   - Return NumLit(3), pos=1
4. expect_token EqEq: found at pos=1, pos=2
5. parse_Int(tokens, pos=2, min_bp=0)
   - parse_Int_prefix sees Integer(4) → NumLit(4), pos=3
   - Pratt loop: peek = Eof, break
   - Return NumLit(4), pos=3
6. Construct Bool::Eq(Box::new(NumLit(3)), Box::new(NumLit(4)))
```

### Parsing Trace: `x == y` (ambiguous)

```
Input tokens: [Ident("x"), EqEq, Ident("y"), Eof]

1. parse_Bool(tokens, pos=0, min_bp=0)
2. Cross-category dispatch sees Ident("x"):
   - Ident is ambiguous → save/restore
3. saved = 0
4. Try parse_Int(tokens, pos=0, min_bp=0):
   - parse_Int_prefix sees Ident("x") → IVar("x"), pos=1
   - Pratt loop: peek = EqEq, infix_bp(EqEq) = None (not Int infix), break
   - Return IVar("x"), pos=1
5. Peek at pos=1: Token::EqEq → match!
6. *pos = 2 (consume ==)
7. parse_Int(tokens, pos=2, min_bp=0):
   - Ident("y") → IVar("y"), pos=3
   - Return IVar("y"), pos=3
8. Construct Bool::Eq(Box::new(IVar("x")), Box::new(IVar("y")))
```

### Parsing Trace: `b && true` (own-category)

```
Input tokens: [Ident("b"), AmpAmp, KwTrue, Eof]

1. parse_Bool(tokens, pos=0, min_bp=0)
2. Cross-category dispatch sees Ident("b"):
   - Ident is ambiguous → save/restore
3. saved = 0
4. Try parse_Int(tokens, pos=0, min_bp=0):
   - Ident("b") → IVar("b"), pos=1
   - Pratt loop: peek = AmpAmp, infix_bp(AmpAmp) = None for Int, break
   - Return IVar("b"), pos=1
5. Peek at pos=1: Token::AmpAmp (not EqEq) → no match
6. Backtrack: *pos = 0
7. parse_Bool_own(tokens, pos=0):
   - parse_Bool_prefix sees Ident("b") → BVar("b"), pos=1
   - Pratt loop: peek = AmpAmp, infix_bp(AmpAmp) = Some((2,3))
     - 2 >= 0 (min_bp), so continue
     - Consume AmpAmp, pos=2
     - parse_Bool(tokens, pos=2, min_bp=3):
       - KwTrue → BoolLit(true), pos=3
       - Pratt loop: Eof, break
     - make_infix(AmpAmp, BVar("b"), BoolLit(true))
       = Comp(BVar("b"), BoolLit(true))
   - Pratt loop: peek = Eof, break
8. Return Comp(BVar("b"), BoolLit(true))
```

This demonstrates the interplay between cross-category dispatch (Phase 6),
FIRST set overlap analysis (Phase 3), and the Pratt parser (Phase 5).
