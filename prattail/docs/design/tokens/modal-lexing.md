# WPDS Stack-Aware Modal Lexing

**Date:** 2026-03-11

---

## 1. Why Flat DFA Lexing Fails

A traditional DFA lexer applies one set of token rules uniformly to every byte.
This breaks for languages that require context-dependent lexical regimes.

**String interpolation.** Consider `"hello ${name + 1} world"`. Three regimes
coexist: normal expression tokens outside strings, literal characters and
escape sequences inside the string body, and expression tokens again inside
`${...}`. A single DFA cannot distinguish these because it has no memory of
whether it entered via `"` or `${`. Encoding all combinations into one DFA
causes exponential state blowup -- every nesting depth x regime pair becomes a
separate DFA state.

**Nested comments.** In `(* outer (* inner *) still outer *)`, a flat DFA
matches the first `*)` against the opening `(*`, prematurely closing the outer
comment. It cannot track nesting depth.

The root cause is identical: a finite automaton has no stack. It cannot track
nesting or remember which lexical context it came from.

---

## 2. Syntax: Mode Blocks and Stack Operations

PraTTaIL extends `tokens { ... }` with **lexer modes** and **stack actions**.

```
tokens {
    // Default mode (implicit)
    DQuote = '"'  push(string_body)

    mode string_body {
        Chars      = /[^"\\$]+/
        Escape     = /\\[nrt\\'"]/
        InterpOpen = '${' push(default)
        DQuoteEnd  = '"'  pop
    }
}
```

**`push(mode)`** -- pushes the target mode onto the stack; lexing continues
with the target mode's DFA. The current mode is preserved underneath.

**`pop`** -- pops the current mode, returning to the previously stacked mode.
If the stack would empty, it resets to `[default]` (safety invariant).

**Implicit default mode.** Tokens outside explicit `mode` blocks belong to
mode `default` (mode ID 0).

**Combined push/pop.** A token may carry both (pop executes first, then push):

```
tokens {
    mode a { Transition = />>/ pop push(b) }   // sibling transition
}
```

---

## 3. WPDS Encoding

PraTTaIL's WPDS models inter-category call/return structure (see `wpds.rs`).
Modal lexing extends this: each mode becomes a stack symbol in the WPDS,
and push/pop actions become WPDS rules.

### 3.1 Formal WPDS

W = (P, Gamma, Delta, f) where:

  - P = {p} -- single control location (the lexer process)
  - Gamma -- set of mode names (stack alphabet)
  - Delta -- rules derived from token definitions
  - f: Delta -> S -- weight function over semiring S

### 3.2 Rule Types

Each token in mode gamma produces one WPDS rule:

| Token action | WPDS rule | Stack effect |
|---|---|---|
| Internal (no push/pop) | `<p, gamma> ->_d <p, gamma>` | Unchanged |
| `push(gamma')` | `<p, gamma> ->_d <p, gamma' gamma>` | gamma' pushed on top |
| `pop` | `<p, gamma> ->_d <p, epsilon>` | gamma removed |

### 3.3 String Interpolation Encoding

```
Rule 1:  <p, default>     ->_d  <p, string_body default>   [DQuote]
Rule 2:  <p, string_body> ->_d  <p, string_body>           [Chars]
Rule 3:  <p, string_body> ->_d  <p, string_body>           [Escape]
Rule 4:  <p, string_body> ->_d  <p, default string_body>   [InterpOpen]
Rule 5:  <p, string_body> ->_d  <p, epsilon>               [DQuoteEnd]
```

Poststar saturation (Reps et al. 2005) computes all reachable mode-stack
configurations, enabling compile-time checks:

  - **Unclosed mode:** a path pushes gamma but never pops it
  - **Dead mode:** no push rule ever targets a declared mode
  - **Stack depth bounds:** maximum nesting depth reachable

---

## 4. DFA-per-Mode Architecture

Each mode gets its own NFA -> DFA -> minimize pipeline:

```
LexerModeInput("string_body")
       |
       v
  Thompson NFA  -->  equivalence classes  -->  subset construction  -->  Hopcroft
       |
       v
  ModeDfaResult { name: "string_body", mode_id: 1, min_dfa, partition, ... }
```

Generated tables are suffixed by mode name:

  - `CHAR_CLASS_DEFAULT[256]`, `CHAR_CLASS_STRING_BODY[256]`
  - `dfa_next_default(state, class)`, `dfa_next_string_body(state, class)`
  - `accept_default(state)`, `accept_string_body(state)`
  - `push_target_default(state)` (returns `u8::MAX` for no-push)
  - `should_pop_default(state)` (returns `bool`)

Separate pipelines are intentional: modes have radically different alphabets.
A string body mode distinguishes `\` and `$` but not `+` or `=`; sharing
equivalence classes would inflate every DFA unnecessarily.

---

## 5. Runtime Mode Stack

Generated code maintains `Vec<u8>` initialized to `[0u8]`. The lex loop
dispatches to the active mode's tables based on `mode_stack.last()`:

```rust
let mut mode_stack: Vec<u8> = vec![0u8];

while pos < bytes.len() {
    let mode = *mode_stack.last().expect("mode stack empty");

    // Longest-match DFA walk using mode's tables
    let mut state: u32 = 0;
    let mut last_accept = None;
    while pos < bytes.len() {
        let c = /* CHAR_CLASS_{mode}[bytes[pos]] */;
        let next_state = /* dfa_next_{mode}(state, c) */;
        if next_state == DEAD { break; }
        state = next_state;
        if /* accept_{mode}(state) */ { last_accept = Some((state, pos)); }
        pos += 1;
    }

    // Emit token, then execute mode transitions
    if let Some((accept_state, end)) = last_accept {
        tokens.push((token, range));
        let target = /* push_target_{mode}(accept_state) */;
        if target != u8::MAX { mode_stack.push(target); }
        if /* should_pop_{mode}(accept_state) */ {
            mode_stack.pop();
            if mode_stack.is_empty() { mode_stack.push(0u8); }
        }
    }
}
```

The safety guard on empty stacks ensures malformed input with excess pops
degrades gracefully to default-mode lexing rather than panicking.

---

## 6. Mode Stack Evolution Diagram

Input: `"hello ${name + 1} world"`

```
Step  Cursor  Token matched   Action          Mode stack (bottom -> top)
----  ------  -------------   ------          --------------------------
 0    ^                       (initial)       [default]
 1    "       DQuote          push(str_body)  [default, str_body]
 2    hello   Chars           (internal)      [default, str_body]
 3    ${      InterpOpen      push(default)   [default, str_body, default]
 4    name    Ident           (internal)      [default, str_body, default]
 5    +       Plus            (internal)      [default, str_body, default]
 6    1       Integer         (internal)      [default, str_body, default]
 7    }       RBrace          pop             [default, str_body]
 8    world   Chars           (internal)      [default, str_body]
 9    "       DQuoteEnd       pop             [default]
```

At step 3 the lexer re-enters default mode for the interpolated expression.
At step 7 the closing `}` pops back to `string_body`. At step 9 the closing
`"` pops to `default`. Stack depth peaks at 3; doubly-nested interpolation
like `"a ${f("b ${x}")} c"` would reach 5.

---

## 7. Mathematical Model

A modal lexer is a tuple M = (Gamma, Sigma, delta, gamma_0) where:

  - Gamma = {default, m_1, ..., m_k} is the finite set of modes
  - Sigma = {0, 1, ..., 255} is the byte alphabet
  - delta: Gamma -> (Q_gamma x Sigma -> Q_gamma) assigns each mode gamma its
    own DFA D_gamma = (Q_gamma, Sigma_gamma, delta_gamma, q_0, F_gamma)
  - gamma_0 = [default] is the initial mode stack

A **configuration** is a pair (w, sigma) where w in Gamma* is the mode stack
(top = rightmost) and sigma in Sigma* is the remaining input. A **step**:

```
(w . gamma, a . sigma)  |-->  (w', sigma')
```

D_gamma consumes a longest match from `a . sigma`, producing token t. Then:

  - push(gamma'): w' = w . gamma . gamma'
  - pop:          w' = w
  - otherwise:    w' = w . gamma

The recognized language is { sigma_0 | (gamma_0, sigma_0) |-->* ([default], epsilon) }.

---

## 8. Additional Examples

### 8.1 Nested Block Comments

```
tokens {
    CommentOpen = '(*' push(comment)

    mode comment {
        CommentOpen  = '(*' push(comment)   // recursive nesting
        CommentClose = '*)' pop
        CommentChar  = /[^(*]/
        CommentStar  = /\*[^)]/
        CommentParen = /\([^*]/
    }
}
```

WPDS self-push rule: `<p, comment> ->_d <p, comment comment>`. Poststar
reveals unbounded stack depth, reportable as lint G34.

### 8.2 Heredoc Strings

```
tokens {
    HeredocStart = /<<<[A-Z]+/ push(heredoc)

    mode heredoc {
        HeredocLine = /[^\n]*/
        HeredocEnd  = /^[A-Z]+;/ pop
        Newline     = /\n/
    }
}
```

The heredoc mode lexes raw text until the delimiter line triggers a pop.

---

## 9. Generated Code Skeleton

```rust
// Per-mode tables
static CHAR_CLASS_DEFAULT: [u8; 256] = [ ... ];
static CHAR_CLASS_STRING_BODY: [u8; 256] = [ ... ];
fn dfa_next_default(state: u32, class: u8) -> u32 { ... }
fn dfa_next_string_body(state: u32, class: u8) -> u32 { ... }
fn accept_default(state: u32) -> Option<Token> { ... }
fn accept_string_body(state: u32) -> Option<Token> { ... }
fn push_target_default(state: u32) -> u8 { ... }   // u8::MAX = no push
fn push_target_string_body(state: u32) -> u8 { ... }
fn should_pop_default(state: u32) -> bool { ... }
fn should_pop_string_body(state: u32) -> bool { ... }

const MODE_DEFAULT: u8 = 0;
const MODE_STRING_BODY: u8 = 1;

pub fn lex<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Range)>, String> {
    lex_with_file_id(input, None)
}

pub fn lex_with_file_id<'a>(input: &'a str, file_id: Option<u32>)
    -> Result<Vec<(Token<'a>, Range)>, String>
{
    let bytes = input.as_bytes();
    let mut pos = 0usize;
    let mut tokens = Vec::with_capacity(input.len() / 2);
    let mut mode_stack: Vec<u8> = vec![MODE_DEFAULT];

    while pos < bytes.len() {
        let mode = *mode_stack.last().expect("mode stack empty");
        // ... DFA walk dispatched by mode ...
        // ... emit token ...
        // ... push/pop mode transitions ...
    }

    tokens.push((Token::Eof, eof_range));
    Ok(tokens)
}
```

---

## 10. References

1. A. Bouajjani, J. Esparza, and O. Maler. "Reachability analysis of pushdown
   automata: Application to model-checking." *CONCUR '97*, LNCS 1243,
   pp. 135--150, 1997. Foundational pushdown reachability algorithms underpinning
   poststar/prestar saturation.

2. T. Reps, S. Schwoon, S. Jha, and D. Melski. "Weighted pushdown systems and
   their application to interprocedural dataflow analysis." *Science of Computer
   Programming*, 58(1-2):206--263, 2005. Extended WPDS with semiring weights for
   quantitative analysis over pushdown configurations.

3. M. Droste, S. Dziadek, and W. Kuich. "Weighted simple reset pushdown
   automata." *Journal of Automata, Languages and Combinatorics*, 24(2-4):
   275--294, 2019. Normal form (push/pop/noop) matching PraTTaIL's modal
   stack operations.
