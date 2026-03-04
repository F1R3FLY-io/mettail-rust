# Fragment Import (`mixins:`)

## Intuition

"mixins are reusable grammar building blocks -- LEGO bricks for languages."
Fragments are defined once via `language_fragment!` and mixed into multiple
consuming languages.

## Why Important

Composable operator sets, grammar libraries, code reuse. Define arithmetic
operators once, mix into any language that needs them.

## language_fragment! Macro

```rust
language_fragment! {
    name: IntArithFragment,
    types { ![i32] as Int },
    terms {
        AddInt . a:Int, b:Int |- a "+" b : Int;
        SubInt . a:Int, b:Int |- a "-" b : Int;
        MulInt . a:Int, b:Int |- a "*" b : Int;
    },
}

language_fragment! {
    name: BoolOpsFragment,
    types { ![bool] as Bool },
    terms {
        And . a:Bool, b:Bool |- a "&&" b : Bool;
        Or  . a:Bool, b:Bool |- a "||" b : Bool;
        Not . a:Bool |- "not" a : Bool;
    },
}
```

Fragments generate NO code. They exist only in the global registry for consumption
by `mixins:`.

## Consuming Fragments

```rust
language! {
    name: MixedMath,
    mixins: [IntArithFragment, BoolOpsFragment],
    types { },
    terms {
        Neg . a:Int |- "-" a : Int;   // Local additions
    },
    rewrites {
        // Must provide own rewrites (fragments have none)
        AddIntCongL . | S ~> T |- (AddInt S X) ~> (AddInt T X);
        // ...
    },
}
```

## Registry Lifecycle

```
  language_fragment! { name: IntArithFragment, ... }
      |
      v
  REGISTRY.register(IntArithFragment)
      |
      (no code generated)

  language! { name: MixedMath, mixins: [IntArithFragment], ... }
      |
      v
  apply_mixins()
      |
      +-- REGISTRY.lookup("IntArithFragment")
      +-- merge_language_defs(fragment, consuming_lang, Override)
      |     (types + terms only, equations/rewrites/logic stripped)
      |
      v
  Merged LanguageDef --> pipeline --> Generated Parser
```

## DuplicateStrategy::Override

If the consuming language defines a rule with the same label as a fragment rule, the
local definition wins silently. This enables customization:

```rust
language_fragment! {
    name: ArithFrag,
    types { ![i32] as Int },
    terms { Add . a:Int, b:Int |- a "+" b : Int; },
}

language! {
    name: CustomArith,
    mixins: [ArithFrag],
    types { },
    terms {
        // Override: use saturating addition
        Add . a:Int, b:Int |- a "+" b : Int ![a.saturating_add(b)] step;
    },
}
```

## Comparison with includes

Both use `DuplicateStrategy::Override` and merge types+terms only. The difference is
the source:

- `includes:` imports from a full `language!` definition
- `mixins:` imports from a `language_fragment!` definition

## End-to-End Example

From `languages/src/composition/mixed_lang.rs`:

MixedMath mixes IntArithFragment and BoolOpsFragment, adds Neg, and provides its
own rewrites for all operators.
