# HashBag — Full Pipeline Trace

This document traces the `HashBag(T)` collection type through every stage of
the MeTTaIL/PraTTaIL pipeline, using the RhoCalc `PPar` constructor (parallel
composition) as the running example.

## 1. DSL Definition

```text
PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
```

| Component          | Meaning                                                   |
|--------------------|-----------------------------------------------------------|
| `PPar`             | Constructor label                                         |
| `ps:HashBag(Proc)` | Parameter `ps` has type `HashBag` of `Proc` elements      |
| `ps.*sep("\|")`    | Elements of `ps` are separated by `\|` in concrete syntax |
| `"{" ... "}"`      | Delimiters: braces                                        |
| `: Proc`           | Result category                                           |

Concrete syntax: `{ a \| b \| c }` → `Proc::PPar(HashBag { a, b, c })`

## 2. LanguageDef AST

**File:** `macros/src/ast/grammar.rs`

### Term Context Parameter

```text
TermParam::Simple {
    name: Ident("ps"),
    ty:   TypeExpr::Collection {
              coll_type: CollectionType::HashBag,
              element:   Box(TypeExpr::Base(Ident("Proc"))),
          },
}
```

### Syntax Pattern

The pattern `"{" ps.*sep("|") "}"` parses as:

```text
[
    SyntaxExpr::Literal("{"),
    SyntaxExpr::Op(
        PatternOp::Sep {
            collection: Ident("ps"),
            separator:  "|",
            source:     None,           ← simple sep (no zip/map chain)
        }
    ),
    SyntaxExpr::Literal("}"),
]
```

The `source: None` distinguishes a simple separated list from a chained
[ZipMapSep](../ZipMapSep/00-overview.md) pattern.  The parser function
`parse_pattern_op_with_receiver()` routes `ps.*sep("|")` to a `Sep` with
`collection = ps` and no source.

## 3. Bridge: LanguageDef → LanguageSpec

**File:** `macros/src/gen/syntax/parser/prattail_bridge.rs`

`convert_pattern_op()` handles `PatternOp::Sep { source: None }`:

```rust
PatternOp::Sep { collection, separator, source: None } => {
    let coll_name = collection.to_string();   // "ps"
    let (elem_cat, kind) = find_collection_info(&coll_name, context);
    items.push(SyntaxItemSpec::Collection {
        param_name:       coll_name,           // "ps"
        element_category: elem_cat,            // "Proc"
        separator:        separator.clone(),   // "|"
        kind,                                  // CollectionKind::HashBag
    });
}
```

`find_collection_info()` looks up `"ps"` in the term context, finds
`TypeExpr::Collection { coll_type: HashBag, element: Base(Proc) }`, and returns
`("Proc", CollectionKind::HashBag)`.

### Complete SyntaxItemSpec List

```text
[
    Terminal("{"),
    Collection {
        param_name:       "ps",
        element_category: "Proc",
        separator:        "|",
        kind:             HashBag,
    },
    Terminal("}"),
]
```

## 4. Classification

**File:** `prattail/src/classify.rs`

```text
classify_collection(syntax):
  → finds Collection { kind: HashBag, separator: "|" } at position 1
  → (true, Some(HashBag), Some("|"))
```

| Flag              | Value           | Reason                        |
|-------------------|-----------------|-------------------------------|
| `is_collection`   | `true`          | `Collection` item present     |
| `collection_type` | `Some(HashBag)` | From `Collection::kind`       |
| `separator`       | `Some("\|")`    | From `Collection::separator`  |
| `is_infix`        | `false`         | First item is `Terminal("{")` |
| `has_binder`      | `false`         | No `Binder` items             |

## 5. Lexer Impact

| Terminal | Token Variant   | Notes                                         |
|----------|-----------------|-----------------------------------------------|
| `{`      | `Token::LBrace` | Structural delimiter (always in terminal set) |
| `\|`     | `Token::Pipe`   | Separator token                               |
| `}`      | `Token::RBrace` | Structural delimiter                          |

**Lexer note:** The grammar also defines `PZero` with syntax `"{}"` (empty
braces as a single token).  The lexer must distinguish `Token::Braces` (the
two-character `{}`) from separate `Token::LBrace` + `Token::RBrace`.  This is
handled by the DFA: the longest match `{}` produces `Token::Braces`, while
`{` followed by any non-`}` character produces `Token::LBrace`.

## 6. Parser Codegen

**Files:** `prattail/src/recursive.rs`, `prattail/src/trampoline.rs`

### Routing Decision

```text
is_simple_collection(PPar)?
  is_collection = true
  has_binder = false
  has_multi_binder = false
  has_zipmapsep = false
  → true  (PPar IS a simple collection — trampolined)

should_use_standalone_fn(PPar)?
  has_zipmapsep = false
  has_multi_binder = false
  → false
```

PPar is a **simple collection** — it gets a dedicated `CollectionElem` frame
variant in the trampoline rather than a standalone function.

### Frame Variant

```text
Frame_Proc::CollectionElem_PPar {
    elements:  mettail_runtime::HashBag<Proc>,
    saved_pos: usize,
    saved_bp:  u8,
}
```

| Field       | Type            | Purpose                                         |
|-------------|-----------------|-------------------------------------------------|
| `elements`  | `HashBag<Proc>` | Accumulates parsed elements                     |
| `saved_pos` | `usize`         | Position after opening delimiter                |
| `saved_bp`  | `u8`            | Binding power to restore after collection parse |

### Generated Code (Conceptual)

**Prefix phase** (`'drive` loop, on seeing `Token::LBrace`):

```rust
Token::LBrace => {
    *pos += 1;   // consume "{"
    stack.push(Frame_Proc::CollectionElem_PPar {
        elements:  mettail_runtime::HashBag::new(),
        saved_pos: *pos,
        saved_bp:  cur_bp,
    });
    cur_bp = 0;  // elements parsed at minimum binding power
    continue 'drive;
}
```

**Unwind phase** (popping `CollectionElem_PPar`):

```rust
Some(Frame_Proc::CollectionElem_PPar {
    mut elements, saved_pos, saved_bp,
}) => {
    // Add the just-parsed element to the bag
    elements.insert(lhs);

    // Check for separator
    if peek_token(tokens, pos, Token::Pipe) {
        *pos += 1;  // consume "|"

        // Re-push frame for next element (tail-call optimization)
        stack.push(Frame_Proc::CollectionElem_PPar {
            elements,
            saved_pos: *pos,
            saved_bp,
        });
        cur_bp = 0;
        continue 'drive;  // parse next element
    }

    // No more elements — finalize
    expect_token(tokens, pos, Token::RBrace)?;  // consume "}"
    lhs = Proc::PPar(elements);
    cur_bp = saved_bp;
}
```

### Collection Parse Loop Diagram

```text
  Token stream:  {    3 + 4    |    5 * 2    |    7    }
                 ▲      ▲      ▲      ▲      ▲    ▲    ▲
  'drive:        │      │      │      │      │    │    │
    consume ─────┘      │      │      │      │    │    │
    push CollectionElem_PPar (empty bag, bp=0)    │    │
    continue 'drive ────┘      │      │      │    │    │
      (parse Proc)             │      │      │    │    │
                               │      │      │    │    │
  'unwind:                     │      │      │    │    │
    pop CollectionElem_PPar    │      │      │    │    │
    elements.insert(Add(NumLit(3), NumLit(4)))    │    │
    peek Pipe → consume ───────┘      │      │    │    │
    re-push frame                     │      │    │    │
    continue 'drive ──────────────────┘      │    │    │
      (parse Proc)                           │    │    │
                                             │    │    │
  'unwind:                                   │    │    │
    pop CollectionElem_PPar                  │    │    │
    elements.insert(Mul(NumLit(5), NumLit(2)))    │    │
    peek Pipe → consume ─────────────────────┘    │    │
    re-push frame                                 │    │
    continue 'drive ──────────────────────────────┘    │
      (parse Proc)                                     │
                                                       │
  'unwind:                                             │
    pop CollectionElem_PPar                            │
    elements.insert(NumLit(7))                         │
    peek RBrace (not Pipe) → finalize                  │
    consume RBrace ────────────────────────────────────┘
    lhs = Proc::PPar(HashBag { Add(NumLit(3), NumLit(4)), Mul(NumLit(5), NumLit(2)), NumLit(7) })
```

### Key Codegen Details

- **Insert method:** `elements.insert(lhs)` — `HashBag::insert` increments the
  count for the element (or inserts with count 1)
- **Tail-call optimization:** Re-pushing the frame and doing `continue 'drive`
  avoids growing the stack — the loop is iterative
- **Empty collection:** If the first token after `{` is `}`, the `'drive` phase
  will parse an element, fail, and the frame is never re-pushed.  Special
  handling for empty collections uses `break 'prefix Proc::PPar(HashBag::new())`
  when `Token::RBrace` is the immediate next token

## 7. Runtime HashBag

**File:** `runtime/src/hashbag.rs`

`HashBag<T>` is a multiset backed by `HashMap<T, usize, BuildHasherDefault<FxHasher>>`:

```text
HashBag<Proc> {
    counts: {
        Add(NumLit(3), NumLit(4)) → 1,
        Mul(NumLit(5), NumLit(2)) → 1,
        NumLit(7) → 1,
    },
    total_count: 3,
}
```

### Key Operations

| Method            | Signature                 | Behaviour                                |
|-------------------|---------------------------|------------------------------------------|
| `new()`           | `→ Self`                  | Empty bag                                |
| `insert(item)`    | `T →`                     | Increment count (or insert with count 1) |
| `remove(item)`    | `&T → bool`               | Decrement count; remove entry at 0       |
| `contains(item)`  | `&T → bool`               | Count > 0                                |
| `count(item)`     | `&T → usize`              | Element count (0 if absent)              |
| `len()`           | `→ usize`                 | Total element count (sum of all counts)  |
| `iter()`          | `→ Iterator<(&T, usize)>` | Unique elements with counts              |
| `iter_elements()` | `→ Iterator<&T>`          | Each element repeated by count           |

### Trait Implementations

| Trait              | Strategy                                                          |
|--------------------|-------------------------------------------------------------------|
| `PartialEq` / `Eq` | Compare `total_count` + `counts` map                              |
| `Hash`             | Sort entries by `Debug` format, hash `(elem, count)` pairs        |
| `Ord`              | Compare total count, then sorted element vectors                  |
| `Display`          | `{ elem1, elem1, elem2 }` (sorted, repeated by count)             |
| `BoundTerm<N>`     | Delegates to elements for `close_term`/`open_term` (rebuilds map) |
| `FromIterator<T>`  | Builds bag from iterator                                          |

### BoundTerm Integration

`HashBag<T>` implements `BoundTerm<N>` by iterating elements and delegating
binding operations.  Since keys may change identity after `close_term` or
`open_term`, the map is rebuilt:

```rust
fn close_term(&mut self, state: ScopeState, on_free: &impl OnFreeFn<N>) {
    let old_counts = std::mem::take(&mut self.counts);
    self.counts = HashMap::default();
    for (mut elem, count) in old_counts {
        elem.close_term(state, on_free);
        self.counts.insert(elem, count);
    }
}
```

## 8. Ascent Decomposition

For how Ascent decomposes `HashBag` terms during fixpoint computation, see
[03-ascent-decomposition.md](03-ascent-decomposition.md).

**Quick summary:** The category exploration rule iterates bag elements and seeds
each into the element category's relation:

```text
ppar_contains(parent.clone(), elem.clone()) <--
    proc(parent),
    if let Proc::PPar(ref bag_field) = parent,
    for (elem, _count) in bag_field.iter();
```

## 9. Runtime Evaluation — Trace

**Input:** `{ 3 + 4 | 5 * 2 }`

### Lexing

```text
Input:   {  3  +  4  |  5  *  2  }
Tokens:  LBrace  Integer(3)  Plus  Integer(4)  Pipe  Integer(5)  Star  Integer(2)  RBrace
```

### Parsing

```text
 1. Match Token::LBrace
 2. Push CollectionElem_PPar { elements: HashBag::new(), ... }
 3. Parse Proc → Int::Add(NumLit(3), NumLit(4))  [cast to Proc]
 4. Unwind: elements.insert(Add(3,4)); peek Pipe → consume; re-push
 5. Parse Proc → Int::Mul(NumLit(5), NumLit(2))  [cast to Proc]
 6. Unwind: elements.insert(Mul(5,2)); peek RBrace → finalize
 7. Consume RBrace
 8. Result: Proc::PPar(HashBag { Add(3,4): 1, Mul(5,2): 1 })
```

### Ascent Seeding

```text
proc(Proc::PPar(bag))       ← initial seed
proc(Add(NumLit(3), NumLit(4)))   ← from bag.iter_elements()
proc(Mul(NumLit(5), NumLit(2)))   ← from bag.iter_elements()
```

If fold evaluation is enabled for `Add` and `Mul`, the fixpoint engine
produces:

```text
rw_proc(Add(3,4), NumLit(7))       ← fold: 3 + 4 = 7
rw_proc(Mul(5,2), NumLit(10))      ← fold: 5 * 2 = 10
rw_proc(PPar({Add(3,4), Mul(5,2)}),
        PPar({NumLit(7), NumLit(10)}))  ← congruence
```

---

**See also:**
- [00-overview.md](00-overview.md) — Collections overview
- [02-hashset-and-vec.md](02-hashset-and-vec.md) — HashSet and Vec differences
- [03-ascent-decomposition.md](03-ascent-decomposition.md) — Ascent decomposition details
- [../binders/01-single-binders.md](../binders/01-single-binders.md) — PNew uses PPar as body
