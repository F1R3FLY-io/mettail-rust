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

| Rust Type | TokenKind | Builtin Pattern |
|---|---|---|
| `i32`, `i64`, `u32`, `u64`, `isize`, `usize` | `Integer` | `[0-9]+` |
| `f32`, `f64` | `Float` | `[0-9]+\.[0-9]+` |
| `bool` | `True`/`False` | `true`/`false` keywords |
| `str`, `String` | `StringLit` | `"[^"]*"` |

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

Currently, precedence is assigned by **declaration order**: the first infix operator
declared in a category gets the lowest precedence, the second gets higher, and so on.
Associativity is specified via the rule's `associativity` field.

### Extending to Explicit Precedence Levels

**Step 1: Add precedence to RuleSpec**

File: `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/lib.rs`

```rust
pub struct RuleSpec {
    // ... existing fields ...
    /// Explicit precedence level (if specified by user). Higher = binds tighter.
    pub precedence: Option<u8>,
}
```

**Step 2: Use explicit precedence in binding power analysis**

File: `/home/dylon/Workspace/f1r3fly.io/mettail-rust/prattail/src/binding_power.rs`

Modify `analyze_binding_powers()`:

```rust
pub fn analyze_binding_powers(rules: &[InfixRuleInfo]) -> BindingPowerTable {
    // ... group by category ...

    for (_category, cat_rules) in &by_category {
        // Sort by explicit precedence if present, then by declaration order
        let mut sorted_rules = cat_rules.clone();
        sorted_rules.sort_by_key(|r| r.precedence.unwrap_or(u8::MAX));

        let mut precedence: u8 = 2;
        for rule in sorted_rules {
            // ... assign (left_bp, right_bp) as before ...
        }
    }
}
```

**Step 3: Add the macro DSL syntax**

In the `language!` macro, allow precedence annotations:

```
Add . a:Int, b:Int |- a "+" b : Int  @prec(1);
Mul . a:Int, b:Int |- a "*" b : Int  @prec(2);
```

Or use a precedence group syntax:

```
precedence {
    level 1 { "+" "-" }
    level 2 { "*" "/" }
    level 3 right { "^" }
}
```

**Step 4: Propagate through InfixRuleInfo**

Add `precedence: Option<u8>` to `InfixRuleInfo` and map it from `RuleSpec` in
`generate_parser()`.

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

### Adding User-Defined Regex Patterns

For full generality, one could extend `TerminalPattern` to carry a regex specification
alongside its text:

```rust
pub struct TerminalPattern {
    pub text: String,
    pub kind: TokenKind,
    pub is_keyword: bool,
    pub regex: Option<String>,     // New: user-defined regex pattern
}
```

Then implement a regex-to-NFA compiler (extending Thompson's construction) in
`nfa.rs`. This would handle patterns like `[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?` for
scientific notation floats.

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

## Summary of Files to Modify per Extension

| Extension | lib.rs | automata/ | lexer.rs | binding_power.rs | prediction.rs | pratt.rs | recursive.rs | dispatch.rs |
|---|---|---|---|---|---|---|---|---|
| New PatternOp | SyntaxItemSpec | -- | -- | -- | -- | -- | RDSyntaxItem + codegen | -- |
| New CollectionType | -- | -- | -- | -- | -- | -- | CollectionKind + codegen | -- |
| New Native Type | -- | mod.rs + nfa.rs + codegen.rs | extract_terminals | -- | generate_first_set_check | -- | -- | -- |
| Precedence Annotations | RuleSpec | -- | -- | analyze_binding_powers | -- | -- | -- | -- |
| New Lexer Pattern | -- | nfa.rs + mod.rs + codegen.rs | BuiltinNeeds + extract | -- | generate_first_set_check | -- | -- | -- |
| New Dispatch Strategy | -- | -- | -- | -- | DispatchAction | generate_prefix_handler | -- | generate_category_dispatch |
