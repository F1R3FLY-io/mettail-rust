# ZipMapSep — DSL Syntax and AST

This document traces the ZipMapSep metasyntax from the `language!` DSL through
the macro parser and bridge to the `LanguageSpec` that PraTTaIL uses for
codegen.  The running example is RhoCalc's `PInputs`.

## 1. DSL Syntax

```text
PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
       |- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;
```

### Chained Operations

The three operations are chained with dot notation:

```text
*zip(ns, xs)                     ← base: pair two param lists
  .*map(|n, x| n "?" x)         ← transform: apply pattern to each pair
  .*sep(",")                     ← separator: comma between mapped elements
```

**Parsing order:** The `*` sigil introduces a pattern operation.  The DSL
parser (`parse_syntax_expr` in `grammar.rs`) dispatches on `*` to
`parse_pattern_op()`, which parses the first operation (`zip`), then checks
for `.` followed by `*` for chaining.

### Parameter References

| Reference | Refers To                                | Kind                        |
|-----------|------------------------------------------|-----------------------------|
| `ns`      | `ns:Vec(Name)`                           | Collection of channel names |
| `xs`      | `^[xs]` in `^[xs].p:[Name* -> Proc]`     | Multi-binder vector         |
| `n`       | Closure param → maps to `ns` (left zip)  | Individual channel name     |
| `x`       | Closure param → maps to `xs` (right zip) | Individual bound variable   |
| `p`       | Body of abstraction                      | Proc body                   |

The closure parameters `n` and `x` are *local* to the `*map` body — they
reference individual elements from the zipped pair, not the full collections.

## 2. LanguageDef AST — Nested PatternOp Tree

**File:** `macros/src/ast/grammar.rs`

### Parsing Sequence

1. `parse_syntax_expr()` sees `*` → calls `parse_pattern_op()`
2. `parse_pattern_op()` sees `zip` → calls `parse_zip_op()`
3. After `zip`, checks for `.` `*` → calls `parse_pattern_op_with_receiver()`
4. Receiver is `Zip { left: ns, right: xs }`
5. Sees `map` → calls `parse_map_closure()` for `|n, x| n "?" x`
6. After `map`, checks for `.` `*` → calls `parse_pattern_op_with_receiver()` again
7. Receiver is `Map { source: Zip{...}, params: [n,x], body: [...] }`
8. Sees `sep` → wraps everything in `Sep`

### Result: Nested PatternOp

```text
PatternOp::Sep
├── collection: Ident("__chain__")      ← placeholder (source is not a simple collection)
├── separator: ","
└── source: Some(
        PatternOp::Map
        ├── source:
        │   PatternOp::Zip
        │   ├── left: Ident("ns")
        │   └── right: Ident("xs")
        ├── params: [Ident("n"), Ident("x")]
        └── body:
            ├── SyntaxExpr::Param(Ident("n"))
            ├── SyntaxExpr::Literal("?")
            └── SyntaxExpr::Param(Ident("x"))
    )
```

### Diagram: PatternOp Nesting

```text
    ┌──────────────────────────────────────────────────────────┐
    │  Sep                                                     │
    │  ├── separator: ","                                      │
    │  └── source:                                             │
    │      ┌──────────────────────────────────────────────┐    │
    │      │  Map                                         │    │
    │      │  ├── params: [n, x]                          │    │
    │      │  ├── body: [Param(n), Lit("?"), Param(x)]    │    │
    │      │  └── source:                                 │    │
    │      │      ┌──────────────────────────┐            │    │
    │      │      │  Zip                     │            │    │
    │      │      │  ├── left: ns            │            │    │
    │      │      │  └── right: xs           │            │    │
    │      │      └──────────────────────────┘            │    │
    │      └──────────────────────────────────────────────┘    │
    └──────────────────────────────────────────────────────────┘
```

### Full Syntax Pattern Vector

The complete `syntax_pattern` for PInputs is:

```text
[
    SyntaxExpr::Literal("("),
    SyntaxExpr::Op(PatternOp::Sep { ... }),    ← the entire chain
    SyntaxExpr::Literal(")"),
    SyntaxExpr::Literal("."),
    SyntaxExpr::Literal("{"),
    SyntaxExpr::Param(Ident("p")),
    SyntaxExpr::Literal("}"),
]
```

## 3. Bridge: LanguageDef → LanguageSpec

**File:** `macros/src/gen/syntax/parser/prattail_bridge.rs`

### Dispatch Path

`convert_syntax_pattern()` iterates the pattern vector.  When it reaches the
`SyntaxExpr::Op(Sep { ... })`, it calls `convert_pattern_op()`:

```text
convert_pattern_op()
  → match Sep { source: Some(map_op) }
  → convert_chained_sep(map_op, separator=",", ...)
```

`convert_chained_sep()` is the key function — it unwraps the
`Sep(Map(Zip(...)))` chain.

### Unwrapping the Chain

```rust
fn convert_chained_sep(
    source_op: &PatternOp,
    separator: &str,
    context: &[TermParam],
    cat_names: &[String],
    items: &mut Vec<SyntaxItemSpec>,
) {
    match source_op {
        PatternOp::Map { source, params, body } => {
            match source.as_ref() {
                PatternOp::Zip { left, right } => {
                    let left_name = left.to_string();
                    let right_name = right.to_string();

                    // Determine categories for left and right from the term context
                    let left_cat = find_param_category(&left_name, context);
                    let right_cat = find_param_category(&right_name, context);

                    // Build a mapping from closure params to zip params
                    // e.g., |n,x| means n→ns (left), x→xs (right)
                    let mut param_mapping: std::collections::HashMap<String, String> =
                        std::collections::HashMap::new();
                    if !params.is_empty() {
                        param_mapping.insert(params[0].to_string(), left_name.clone());
                    }
                    if params.len() >= 2 {
                        param_mapping.insert(params[1].to_string(), right_name.clone());
                    }

                    // Convert body items, resolving closure params to their original context
                    let body_items: Vec<SyntaxItemSpec> = body
                        .iter()
                        .map(|expr| match expr {
                            SyntaxExpr::Literal(text) => SyntaxItemSpec::Terminal(text.clone()),
                            SyntaxExpr::Param(name) => {
                                let name_str = name.to_string();
                                // Check if this is a closure param and map it back
                                if let Some(original) = param_mapping.get(&name_str) {
                                    classify_param_from_context(original, context, cat_names)
                                } else {
                                    classify_param_from_context(&name_str, context, cat_names)
                                }
                            },
                            SyntaxExpr::Op(_) => {
                                // Nested ops in map body — fallback to ident capture
                                SyntaxItemSpec::IdentCapture {
                                    param_name: "__nested_op__".to_string(),
                                }
                            },
                        })
                        .collect();

                    items.push(SyntaxItemSpec::ZipMapSep {
                        left_name,
                        right_name,
                        left_category: left_cat,
                        right_category: right_cat,
                        body_items,
                        separator: separator.to_string(),
                    });
                },
                _ => {
                    // Unsupported map source — fall back to simple collection
                    items.push(SyntaxItemSpec::Collection {
                        param_name: "__chain__".to_string(),
                        element_category: "Unknown".to_string(),
                        separator: separator.to_string(),
                        kind: CollectionKind::Vec,
                    });
                },
            }
        },
        _ => {
            // Unsupported sep source — fall back to simple collection
            items.push(SyntaxItemSpec::Collection {
                param_name: "__chain__".to_string(),
                element_category: "Unknown".to_string(),
                separator: separator.to_string(),
                kind: CollectionKind::Vec,
            });
        },
    }
}
```

### Parameter Mapping

The bridge builds a mapping from closure parameter names to the original zip
parameter names:

```text
params[0] = "n"  →  left_name  = "ns"
params[1] = "x"  →  right_name = "xs"
```

When resolving body items, each `SyntaxExpr::Param` is first checked against
this mapping, then resolved via `classify_param_from_context()` using the
*original* context parameter.

### Body Item Resolution

| Body Item      | Closure Param | Maps To                                             | Context Lookup                                                  | Result          |
|----------------|---------------|-----------------------------------------------------|-----------------------------------------------------------------|-----------------|
| `Param("n")`   | `n` → `ns`    | `TermParam::Simple { name: "ns", ty: Vec(Name) }`   | `NonTerminal { category: "Name", param_name: "ns" }`            |
| `Literal("?")` | —             | —                                                   | —                                                               | `Terminal("?")` |
| `Param("x")`   | `x` → `xs`    | `TermParam::MultiAbstraction { binder: "xs", ... }` | `Binder { param_name: "xs", category: "Name", is_multi: true }` |

The critical distinction: `n` maps to a *simple* parameter (`ns:Vec(Name)`)
and becomes a `NonTerminal`, while `x` maps to the *binder* field of a
`MultiAbstraction` and becomes a `Binder { is_multi: true }`.

### Produced SyntaxItemSpec

```text
SyntaxItemSpec::ZipMapSep {
    left_name:      "ns",
    right_name:     "xs",
    left_category:  "Name",
    right_category: "Name",
    body_items: [
        NonTerminal { category: "Name", param_name: "ns" },
        Terminal("?"),
        Binder { param_name: "xs", category: "Name", is_multi: true },
    ],
    separator: ",",
}
```

### `find_param_category()` Details

This helper searches the term context for a parameter name and extracts its
base category:

```text
find_param_category("ns", context):
  → TermParam::Simple { name: "ns", ty: Vec(Name) }
  → extract_base_category(Vec(Name))
  → extract_base_category(Name)    [recurse into Collection element]
  → "Name"

find_param_category("xs", context):
  → TermParam::MultiAbstraction { binder: "xs", ty: Arrow(MultiBinder(Name), Base(Proc)) }
  → extract_base_category(Arrow(MultiBinder(Name), Base(Proc)))
  → extract_base_category(Base(Proc))    [recurse into Arrow codomain]
  → "Proc"
```

Wait — `xs` resolves to `"Proc"` via the codomain?  No.  The bridge calls
`find_param_category("xs", context)` which matches the binder field.  For
`MultiAbstraction`, the type path is `Arrow { domain: MultiBinder(Name), codomain: Base(Proc) }`.
The `extract_base_category` function follows the codomain for `Arrow`, yielding
`"Proc"`.  However, the `right_category` on the `ZipMapSep` spec is set from
this result — but the body item `Binder { category: "Name" }` correctly uses the
domain type.  The `right_category` field is used for type annotations, while the
actual parse dispatch uses the body items' own categories.

## 4. Complete SyntaxItemSpec List for PInputs

After bridge conversion, the full syntax item list is:

```text
[
    Terminal("("),
    ZipMapSep {
        left_name:      "ns",
        right_name:     "xs",
        left_category:  "Name",
        right_category: "Name",
        body_items: [
            NonTerminal { category: "Name", param_name: "ns" },
            Terminal("?"),
            Binder { param_name: "xs", category: "Name", is_multi: true },
        ],
        separator: ",",
    },
    Terminal(")"),
    Terminal("."),
    Terminal("{"),
    NonTerminal { category: "Proc", param_name: "p" },
    Terminal("}"),
]
```

## 5. Classification Impact

**File:** `prattail/src/classify.rs`

The ZipMapSep item affects classification through recursive binder detection:

```text
has_binder_recursive(syntax, check_multi=true):
  → item[1] is ZipMapSep → recurse into body_items
  → body_items[2] is Binder { is_multi: true }
  → returns true
```

This sets `has_multi_binder = true` on the `RuleSpec`, which in turn triggers
the standalone-function routing in the trampoline.

## 6. LanguageSpec Storage

The `ZipMapSep` is stored on the `RuleSpec` as part of its `syntax` vector:

```text
RuleSpec {
    label:            "PInputs",
    category:         "Proc",
    syntax:           [Terminal("("), ZipMapSep{...}, Terminal(")"), ...],
    has_multi_binder: true,
    is_collection:    false,     ← ZipMapSep is NOT a Collection item
    ...
}
```

The parser generator uses this `RuleSpec` to generate the standalone parse
function — see [02-parser-and-runtime.md](02-parser-and-runtime.md).

---

**See also:**
- [00-overview.md](00-overview.md) — ZipMapSep overview and pipeline diagram
- [02-parser-and-runtime.md](02-parser-and-runtime.md) — Parser codegen, Ascent rules, runtime trace
- [../binders/02-multi-binders.md](../binders/02-multi-binders.md) — Multi-binder context for PInputs
- [../collections/02-hashset-and-vec.md](../collections/02-hashset-and-vec.md) — Vec collection (used by `ns`)
