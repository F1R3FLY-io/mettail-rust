# PraTTaIL Extension Points

**How to extend PraTTaIL with new pattern operations, collection types, native types,
precedence annotations, and lexer token patterns.**

---

## Overview

PraTTaIL is designed with clear interfaces between its pipeline phases. Each extension
point corresponds to a specific data type or function that can be augmented without
restructuring the overall architecture. This document catalogs the primary extension
points and explains what changes are needed in each module.

---

## 1. Adding a New Pattern Operation

**Current pattern operations** (defined in `recursive.rs` as `RDSyntaxItem` variants):
- `Collection` -- parse a separated list into HashBag/HashSet/Vec
- `SepList` -- `#sep(separator)` for separated lists
- `ZipMapSep` -- `#zip(a,b).#map(|x,y| body).#sep(sep)` for parallel iteration
- `Optional` -- `#opt(...)` for optional groups

### Steps to Add a New Pattern Op (e.g., `#repeat(n, Cat)`)

**Step 1: Define the syntax item variant**

File: `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/recursive.rs`

```rust
pub enum RDSyntaxItem {
    // ... existing variants ...

    /// A bounded repetition: parse exactly N elements.
    Repeat {
        count_name: String,
        element_category: String,
        collection_name: String,
    },
}
```

**Step 2: Handle parsing code generation**

In the same file, add a match arm in `generate_parse_body()`:

```rust
RDSyntaxItem::Repeat { count_name, element_category, collection_name } => {
    let param = format_ident!("{}", collection_name);
    let count = format_ident!("{}", count_name);
    let parse_elem = format_ident!("parse_{}", element_category);

    stmts.push(quote! {
        let mut #param = Vec::new();
        for _ in 0..#count {
            let elem = #parse_elem(tokens, pos, 0)?;
            #param.push(elem);
        }
    });

    captures.push(Capture {
        name: collection_name.clone(),
        kind: CaptureKind::Collection,
    });
}
```

**Step 3: Wire it through `SyntaxItemSpec`**

File: `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/lib.rs`

Add a variant to `SyntaxItemSpec` and a mapping in the Phase 4 loop inside
`generate_parser()`.

**Step 4: Add the macro DSL syntax**

File: `macros/src/ast/language.rs` (or the macro parsing code)

Parse the `#repeat(n, Cat)` syntax in the DSL and produce the corresponding
`SyntaxItemSpec::Repeat`.

---

## 2. Adding a New Collection Type

**Current collection types** (in `recursive.rs`):

```rust
pub enum CollectionKind {
    HashBag,
    HashSet,
    Vec,
}
```

### Steps to Add a New Collection Type (e.g., `BTreeSet`)

**Step 1: Add the variant**

```rust
pub enum CollectionKind {
    HashBag,
    HashSet,
    Vec,
    BTreeSet,    // New
}
```

**Step 2: Add initialization and insertion code**

In `generate_parse_body()`, the `Collection` and `SepList` arms generate initialization
and insertion code. Add match arms:

```rust
let collection_init = match kind {
    CollectionKind::HashBag => quote! { hashbag::HashBag::new() },
    CollectionKind::HashSet => quote! { std::collections::HashSet::new() },
    CollectionKind::Vec => quote! { Vec::new() },
    CollectionKind::BTreeSet => quote! { std::collections::BTreeSet::new() },
};

let insert_method = match kind {
    CollectionKind::HashBag | CollectionKind::HashSet | CollectionKind::BTreeSet => {
        quote! { insert }
    },
    CollectionKind::Vec => quote! { push },
};
```

**Step 3: Update the macro DSL**

The `language!` macro currently recognizes `HashBag(Cat)`, `HashSet(Cat)`, and
`Vec(Cat)` in term rule syntax. Add parsing for `BTreeSet(Cat)` in the macro's
AST module.

**Step 4: Ensure the AST type derives necessary traits**

`BTreeSet` requires `Ord` on its elements. Verify that the category's AST type
implements `Ord`, or add appropriate trait bounds to the generated code.

---

## 3. Adding a New Native Type

**Current native types** (detected in `lexer.rs` via `extract_terminals()`):

| Rust Type                                    | TokenKind      | Builtin Pattern         |
|----------------------------------------------|----------------|-------------------------|
| `i32`, `i64`, `u32`, `u64`, `isize`, `usize` | `Integer`      | `[0-9]+`                |
| `f32`, `f64`                                 | `Float`        | `[0-9]+\.[0-9]+`        |
| `bool`                                       | `True`/`False` | `true`/`false` keywords |
| `str`, `String`                              | `StringLit`    | `"[^"]*"`               |

### Steps to Add a New Native Type (e.g., `char`)

**Step 1: Add detection in terminal extraction**

File: `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/lexer.rs`

In `extract_terminals()`, add a case:

```rust
Some("char") => {
    needs.char_lit = true;
}
```

**Step 2: Add the BuiltinNeeds flag**

File: `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/automata/nfa.rs`

```rust
pub struct BuiltinNeeds {
    // ... existing fields ...
    pub char_lit: bool,
}
```

**Step 3: Build the NFA fragment**

In the same file, add:

```rust
fn build_char_lit_fragment(nfa: &mut Nfa) -> NfaFragment {
    let start = nfa.add_state(NfaState::new());
    let inside = nfa.add_state(NfaState::new());
    let accept = nfa.add_state(NfaState::accepting(TokenKind::CharLit));

    // Opening single quote
    nfa.add_transition(start, inside, CharClass::Single(b'\''));
    // Any single character
    for byte in 0u8..=127 {
        if byte != b'\'' {
            nfa.add_transition(inside, accept, CharClass::Single(byte));
        }
    }
    // Closing single quote (after the accept, not needed -- single char)
    // Actually: 'c' is 3 chars total. Adjust as needed.

    NfaFragment { start, accept }
}
```

And call it in `build_nfa()`:

```rust
if needs.char_lit {
    let frag = build_char_lit_fragment(&mut nfa);
    fragments.push(frag);
}
```

**Step 4: Add the TokenKind variant**

File: `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/automata/mod.rs`

```rust
pub enum TokenKind {
    // ... existing variants ...
    CharLit,
}
```

Set its priority (e.g., `2` like other literals).

**Step 5: Add codegen for the new token**

File: `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/automata/codegen.rs`

In `generate_token_enum()`, add a case:

```rust
TokenKind::CharLit => {
    if seen.insert("CharLit".to_string()) {
        variants.push(quote! {
            /// Character literal
            CharLit(char)
        });
    }
}
```

In `token_kind_to_constructor()`:

```rust
TokenKind::CharLit => quote! {
    Token::CharLit(text.chars().nth(1).expect("invalid char literal"))
},
```

**Step 6: Update FIRST set generation**

In `prediction.rs`, ensure `CharLit` is handled in `generate_first_set_check()`:

```rust
"CharLit" => quote! { Token::CharLit(_) },
```

---

## 4. User-Defined Precedence Annotations

Precedence is assigned by **declaration order** plus one relative annotation. The first
infix rule declared in a category opens the loosest precedence **level**; each subsequent
rule opens the next, tighter level — unless it carries `same`, in which case it joins the
level its predecessor opened. Associativity is separate and per-rule (`right`; the default
is left).

```
MulInt . a:Int, b:Int |- a "*" b : Int ![a * b] fold;        // opens a level
DivInt . a:Int, b:Int |- a "/" b : Int ![a / b] fold same;   // joins it
ModInt . a:Int, b:Int |- a "%" b : Int ![a % b] fold same;   // joins it
PowInt . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] step right;  // next level, right
```

The result is a total **preorder**: a sequence of levels, each an unordered set of
operators. Declaration order supplies the ordering; `same` supplies the ties.

> **This section previously described `same` as an unimplemented extension point.** It was
> implemented on 2026-07-28, because the gap it left was not cosmetic: without it,
> `analyze_binding_powers` advanced its counter in both associativity branches, so rule
> $`i`$ received $`\ell \in \{2 + 2i,\; 3 + 2i\}`$ and two rules $`i < j`$ could share an
> $`\ell`$ only if $`2(j - i) = 1`$. Equal precedence was **unrepresentable**, and
> `6 * 3 / 2` parsed as `6 * (3 / 2)`. See
> `prattail/docs/design/binding-powers/02-implicit-deduction.md` §3.

### Why a relative marker rather than absolute levels

Two absolute designs were considered and rejected. Both are recorded here because they
keep being proposed.

**`@prec(n)` per rule:**

```
Add . a:Int, b:Int |- a "+" b : Int  @prec(1);
Mul . a:Int, b:Int |- a "*" b : Int  @prec(2);
```

**A `precedence { }` block:**

```
precedence {
    level 1 { "+" "-" }
    level 2 { "*" "/" }
    level 3 right { "^" }
}
```

| Property | `same` | `@prec(n)` | `precedence { }` block |
|---|---|---|---|
| Total by construction | yes — every rule has a predecessor or opens the first level | no — a rule may omit `@prec` | no — a rule may be unlisted |
| Renumbering churn on insert | none | every tighter level | every tighter level |
| Two rules can disagree about a level | impossible — no operand | yes | yes |
| Second source of truth for ordering | no | yes | yes — the block and `terms` can disagree |
| Associativity stays per-operator | yes | yes | **no** — `level 3 right` attaches it to the level |

The last row is disqualifying rather than merely inconvenient. Rholang's normative grammar
declares `matches` as `prec.right(6, …)` beside `==` and `!=` as `prec.left(6, …)`: one
level, two associativities. A `precedence { level n <assoc> { … } }` block cannot express
that, so it cannot express the language MeTTaIL exists to implement.

### If an absolute scheme is nevertheless wanted

It must be **additive** — `same` continues to mean what it means, and an absolute
annotation only overrides it — and it must keep associativity attached to the rule, never
to the level.

**Step 1** — add the field beside the existing one on `RuleSpec` and `RuleSpecInput`
(`prattail/src/lib.rs`), so it travels the same path:

```rust
pub struct RuleSpec {
    // ... existing fields ...
    pub shares_level_with_previous: bool,
    /// Explicit level, overriding the relative marker. Higher = binds tighter.
    pub precedence: Option<u8>,
}
```

**Step 2** — consume it in `analyze_binding_powers` (`prattail/src/binding_power.rs`),
which is the ONLY assigner. Both the parser codegen and `Display` call it, which is what
keeps them from disagreeing; an override applied anywhere else would reintroduce exactly
the parser/printer split that the mixfix associativity bug caused.

**Step 3** — surface it in the DSL alongside `right`, `prefix(N)`, `canonical` and `same`
(`ast/src/grammar.rs`), and carry it on `GrammarRule`.

**Step 4** — populate it at every `InfixRuleInfo` construction site. Adding a
non-`Option` field is deliberately a compile error at each one, so the compiler enumerates
the sites rather than leaving a silent default behind.

---

## 5. Adding New Lexer Token Patterns

The lexer supports two kinds of tokens:
- **Fixed terminals**: exact string matches (e.g., `"+"`, `"error"`, `"=="`)
- **Character-class patterns**: regex-like patterns (ident, integer, float, string)

### Adding a Custom Character-Class Pattern (e.g., Hex Literals)

**Step 1: Define the NFA fragment**

File: `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/automata/nfa.rs`

```rust
/// Build an NFA fragment for hex literals: `0x[0-9a-fA-F]+`
fn build_hex_fragment(nfa: &mut Nfa) -> NfaFragment {
    let start = nfa.add_state(NfaState::new());
    let zero = nfa.add_state(NfaState::new());
    let x = nfa.add_state(NfaState::new());
    let accept = nfa.add_state(NfaState::accepting(TokenKind::HexInteger));

    nfa.add_transition(start, zero, CharClass::Single(b'0'));
    nfa.add_transition(zero, x, CharClass::Single(b'x'));
    nfa.add_transition(x, accept, CharClass::Range(b'0', b'9'));
    nfa.add_transition(x, accept, CharClass::Range(b'a', b'f'));
    nfa.add_transition(x, accept, CharClass::Range(b'A', b'F'));
    nfa.add_transition(accept, accept, CharClass::Range(b'0', b'9'));
    nfa.add_transition(accept, accept, CharClass::Range(b'a', b'f'));
    nfa.add_transition(accept, accept, CharClass::Range(b'A', b'F'));

    NfaFragment { start, accept }
}
```

**Step 2: Add to BuiltinNeeds and build_nfa()**

```rust
pub struct BuiltinNeeds {
    // ... existing ...
    pub hex_integer: bool,
}

pub fn build_nfa(terminals: &[TerminalPattern], needs: &BuiltinNeeds) -> Nfa {
    // ... existing ...
    if needs.hex_integer {
        let frag = build_hex_fragment(&mut nfa);
        fragments.push(frag);
    }
    // ...
}
```

**Step 3: Add TokenKind, codegen, FIRST set handling**

Follow the same steps as for a new native type (Section 3 above).

### Customizing Literal Token Patterns (Implemented)

Builtin literal token patterns (ident, integer, float, string) are compiled from
configurable regex specifications. The defaults are defined in `literal_patterns.ebnf`:

```ebnf
<integer> = /[0-9]+/ ;
<float>   = /[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?/ ;
<string>  = /"([^"\\]|\\.)*"/ ;
<ident>   = /[a-zA-Z_][a-zA-Z0-9_]*/ ;
```

**Pipeline**: `parse_literal_patterns_ebnf(content)` → `LiteralPatterns` →
`build_nfa(terminals, needs, patterns)` → `compile_regex(pattern, nfa, token_kind)`
per needed builtin.

To customize a pattern, edit the regex between `/` delimiters in
`literal_patterns.ebnf`. For example, to enable Unicode identifiers:

```ebnf
<ident> = /\p{XID_Start}\p{XID_Continue}*/ ;
```

Multi-byte Unicode codepoints are decomposed into byte-level NFA transition chains
at compile time via `automata/utf8.rs` using `regex_syntax::utf8::Utf8Sequences`.
The downstream pipeline operates on `[u8; 256]` tables unchanged — zero UTF-8
decoding at lex time.

**Supported regex syntax**: literals, `[a-z]` / `[^…]` character classes,
`\d` / `\w` / `\s` / `\D` / `\W` / `\S` shorthand classes, `*` / `+` / `?` /
`{n,m}` / `{,n}` quantifiers, `|` alternation, `(…)` grouping, `.` dot, `\u{XXXX}` /
`\uXXXX` / `\UXXXXXXXX` Unicode escapes, `\p{Name}` / `\P{Name}` Unicode
properties. Not supported: backreferences, lookahead/lookbehind, lazy quantifiers,
named groups, anchors.

> **Cross-reference:** See [quick-reference.md §2.8](../design/quick-reference.md#28-regex-pattern-syntax)
> for the full supported regex syntax table.

---

## 6. Adding a New Dispatch Strategy

The prediction module currently supports these dispatch actions:
- `Direct` -- unambiguous single-rule dispatch
- `Lookahead` -- k>1 lookahead for ambiguous prefixes
- `CrossCategory` -- cross-category parse path
- `Cast` -- category embedding
- `Grouping` -- parenthesized expressions
- `Variable` -- variable fallback

### Adding a New Strategy (e.g., `Contextual`)

**Step 1: Add the variant to DispatchAction**

File: `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/prediction.rs`

```rust
pub enum DispatchAction {
    // ... existing ...
    Contextual {
        category: String,
        context_token: String,
        alternatives: Vec<(String, String)>,  // (context_value, rule_label)
    },
}
```

**Step 2: Generate the dispatch code**

This would go in either `dispatch.rs` (for cross-category contexts) or `pratt.rs`
(for within-category contexts), depending on the semantics.

---

## 7. Adding Custom Token Kinds via `tokens { ... }`

The `tokens { ... }` block in the `language!` macro allows users to define custom
token kinds, override built-in patterns, and enable advanced lexer features (modal
lexing, multi-stream, VPA grouping, tree automata validation).

### Step 1: Define a `TokenDef` in the macro AST

File: `macros/src/ast/language.rs`

The `TokenDef` struct captures each token definition:

```rust
pub struct TokenDef {
    pub name: Ident,           // Token name (e.g., "HexLiteral")
    pub pattern: String,       // Regex pattern
    pub category: Option<Ident>, // Optional target category
    pub rust_code: Option<TokenStream>, // Constructor code
    pub priority: Option<u8>,  // Disambiguation priority
    pub push_mode: Option<Ident>, // Push into named mode
    pub is_pop: bool,          // Pop current mode
    pub stream: Option<Ident>, // Output stream name
}
```

### Step 2: Bridge to `CustomTokenSpec`

File: `macros/src/gen/syntax/parser/prattail_bridge.rs`

Each `TokenDef` is converted to a `CustomTokenSpec` (defined in `prattail/src/lib.rs`).
Built-in names (`Integer`, `Float`, `StringLit`, `Ident`) set `is_builtin_override = true`
and modify `LiteralPatterns` instead of adding a new token kind.

### Step 3: NFA construction

File: `prattail/src/automata/nfa.rs`

- **Default mode tokens**: `build_nfa_with_custom()` compiles non-override custom token
  regex patterns as additional NFA fragments alongside built-in patterns.
- **Named mode tokens**: `build_nfa_for_mode()` builds a separate NFA containing only
  the mode's declared token patterns.

### Step 4: Codegen

File: `prattail/src/automata/codegen.rs`

Custom tokens generate:
- **Token enum variants**: `HexLit(i64),` (payload) or `MyToken,` (unit)
- **Constructor code**: `Token::HexLit({ let text = text; user_code })`
- **Display impl**: Payload variants bind the value, unit variants use the name

For modal lexing, `generate_modal_lexer_string()` produces per-mode DFA tables with
suffixed names and a mode-dispatched lex loop.

### Step 5: Parser integration

File: `prattail/src/pipeline.rs`

Custom tokens with `: Category` are added to that category's FIRST set, allowing
the parser to recognize them as alternative literal producers (e.g., `HexLiteral`
tokens produce `Int` values alongside `Integer` tokens).

> **Detailed documentation**: See [tokens/ design docs](../design/tokens/README.md)

---

## 8. Adding a New Constraint Theory

The `ConstraintTheory` trait (feature: `logict`) provides the extension point for
pluggable constraint domains. Implementing it gives the theory bounded,
certificate-checked `RejectSafeAlgebra` integration through `TheoryAlgebra`.
SFA determinization, minterm computation, inclusion, and equivalence additionally
require `DecidableConstraintTheory`, whose total procedure proves exact emptiness.

### Steps to Add a New Constraint Theory (e.g., `ResourceTheory`)

**Step 1: Implement `ConstraintTheory`**

File: new module (e.g., `prattail/src/resource_theory.rs`)

```text
Algorithm IMPLEMENT-CONSTRAINT-THEORY(ResourceTheory)
Input: domain configuration and a ResourceStore
Output: a ConstraintTheory implementation

1. empty_store returns the unconstrained resource store.
2. propagate(store, constraint) returns a narrowed store, or inconsistency.
3. is_consistent(store) checks the accumulated conjunction.
4. witness(store) returns a concrete assignment only when one is known.
5. label(store) fairly enumerates implementation search alternatives; it may
   be empty, but emptiness does not certify semantic completeness.
6. evaluate_checked(constraint, assignment) returns true, false, or unknown
   without guessing when evaluation is partial.
```

**Step 2: Use via `TheoryAlgebra`**

```text
Algorithm BOUNDED-RESOURCE-DECISION(theory, predicate, budget)
1. Construct TheoryAlgebra(theory, budget).
2. Invoke the RejectSafeAlgebra three-valued satisfiability operation.
3. Return Sat only with a rechecked witness, Unsat only with a proof, and
   DontKnow when the bounded procedure establishes neither result.
```

`result` is `Sat`, `Unsat`, or `DontKnow`; a budget-exhausted search never
fabricates `Unsat`.

**Step 3: Add an exact-decision capability when justified (optional)**

Implement `DecidableConstraintTheory::decide_exact` only when the domain owns a
terminating and complete decision procedure. Its positive branch must return a
witness satisfying the whole predicate, and its negative branch must prove no
such assignment exists. Only this implementation makes
`TheoryAlgebra<ResourceTheory>` a `BooleanAlgebra` suitable for classical SFA
algorithms.

**Step 4: Add feature gate (optional)**

In `Cargo.toml`:
```toml
resource-theory = ["logict"]
```

**Step 5: Add predicate dispatch integration (optional)**

In `predicate_dispatch.rs`, add a new `PredicateSignature` bit and `ModuleId`
variant, with detection logic in `extract_features()` and `classify_grammar()`.

**Step 6: Add lints (optional)**

In `lint.rs`, add lint functions that consume an analysis result struct from
your theory module, gated on your feature flag.

> **Cross-reference:** See [design/constraint-theories/README.md](../design/constraint-theories/README.md)
> for the full constraint theory architecture, and
> [design/constraint-theories/logict-framework.md](../design/constraint-theories/logict-framework.md)
> for `ConstraintTheory` trait details.

---

## Summary of Files to Modify per Extension

| Extension              | lib.rs         | automata/                    | lexer.rs               | binding_power.rs       | prediction.rs            | pratt.rs                | recursive.rs             | dispatch.rs                |
|------------------------|----------------|------------------------------|------------------------|------------------------|--------------------------|-------------------------|--------------------------|----------------------------|
| New PatternOp          | SyntaxItemSpec | --                           | --                     | --                     | --                       | --                      | RDSyntaxItem + codegen   | --                         |
| New CollectionType     | --             | --                           | --                     | --                     | --                       | --                      | CollectionKind + codegen | --                         |
| New Native Type        | --             | mod.rs + nfa.rs + codegen.rs | extract_terminals      | --                     | generate_first_set_check | --                      | --                       | --                         |
| Precedence Annotations | RuleSpec       | --                           | --                     | analyze_binding_powers | --                       | --                      | --                       | --                         |
| New Lexer Pattern      | --             | nfa.rs + mod.rs + codegen.rs | BuiltinNeeds + extract | --                     | generate_first_set_check | --                      | --                       | --                         |
| New Dispatch Strategy  | --             | --                           | --                     | --                     | DispatchAction           | generate_prefix_handler | --                       | generate_category_dispatch |
| Custom Token Kind      | CustomTokenSpec| nfa.rs + codegen.rs          | LexerInput + pipeline  | --                     | FIRST set augmentation   | --                      | --                       | --                         |
| Constraint Theory      | --             | --                           | --                     | --                     | --                       | --                      | --                       | predicate_dispatch (opt)   |
