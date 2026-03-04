# Grammar-Only Import (`includes:`)

## Intuition

"includes imports the *shape* of a grammar without its *meaning*." When language B
includes language A, B gets A's types and terms but NOT equations, rewrites, or
logic. B provides its own operational semantics.

## Why Important

Sharing syntax across languages with different operational semantics. Example: two
languages share the same arithmetic syntax but have different evaluation strategies.

## Syntax

```rust
language! {
    name: ImportedMath,
    includes: [BaseMath],     // Import types + terms only
    types { },
    terms {
        Div . a:Num, b:Num |- a "/" b : Num;   // Add local rules
    },
    rewrites {
        // Provide own rewrites (BaseMath's NOT inherited)
        DivCongL . | S ~> T |- (Div S X) ~> (Div T X);
    },
}
```

## Stripping Semantics

`includes:` uses `merge_language_defs(base, ext, DuplicateStrategy::Override)` but
ONLY merges types and terms:

- equations: NOT merged (extension provides its own)
- rewrites: NOT merged
- logic: NOT merged
- `DuplicateStrategy::Override`: if the importing language defines a rule with the
  same label, the local definition wins

## Comparison Diagram with extends

```
  extends:                              includes:
  +------------------------+           +------------------------+
  | Merged:                |           | Merged:                |
  |   types       YES      |           |   types       YES      |
  |   terms       YES      |           |   terms       YES      |
  |   equations   YES      |           |   equations   NO       |
  |   rewrites    YES      |           |   rewrites    NO       |
  |   logic       YES      |           |   logic       NO       |
  |                        |           |                        |
  | DuplicateStrategy:     |           | DuplicateStrategy:     |
  |   Error (reject dupes) |           |   Override (local wins)|
  +------------------------+           +------------------------+
```

## End-to-End Example

From `languages/src/composition/grammar_import_lang.rs`:

```rust
language! {
    name: ImportedMath,
    includes: [BaseMath],
    types { },
    terms {
        Div . a:Num, b:Num |- a "/" b : Num;
    },
    rewrites {
        AddCongL . | S ~> T |- (Add S X) ~> (Add T X);
        AddCongR . | S ~> T |- (Add X S) ~> (Add X T);
        SubCongL . | S ~> T |- (Sub S X) ~> (Sub T X);
        SubCongR . | S ~> T |- (Sub X S) ~> (Sub X T);
        DivCongL . | S ~> T |- (Div S X) ~> (Div T X);
        DivCongR . | S ~> T |- (Div X S) ~> (Div X T);
    },
}
```

Note: ImportedMath re-defines its own congruence rules because BaseMath's rewrites
are NOT inherited.

## Integration

Merged LanguageDef --> pipeline --> single parser. The parser handles all imported +
local rules.
