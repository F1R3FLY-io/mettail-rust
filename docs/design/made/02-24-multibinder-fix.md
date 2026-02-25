# 02-24: Multi-binder-only term support

## Context

Adding `PNew . ^[xs].p:[Name* -> Proc] |- "new" xs.*sep(",") "in" "{" p "}" : Proc` to rhocalc triggered 15 compilation errors. PNew is the first term with a multi-abstraction binder (`^[xs].p`) and *no* other fields — previous multi-binder terms like PInputs always had regular fields alongside the binder.

## Root causes

### 1. No parser spec for standalone binder collections (PraTTaIL)

`xs.*sep(",")` in the syntax pattern hit the `PatternOp::Sep` handler, which called `find_collection_info("xs", ...)`. That function only matches `TermParam::Simple`, so it returned `("Unknown", Vec)` — producing `Collection { element_category: "Unknown" }`. This caused `parse_Unknown` calls and prevented `has_multi_binder` from being set on the rule, so the constructor generated `PNew(xs, p)` instead of `PNew(Scope::new(binders, Box::new(p)))`.

**Fix**: Added `BinderCollection { param_name, separator }` variant to `SyntaxItemSpec` and `RDSyntaxItem`. The bridge detects when a Sep target is a multi-abstraction binder and emits this variant. Handled across all exhaustive matches: classify, pipeline, compose, ebnf, prediction, grammar_gen, recursive, trampoline.

### 2. Binder category extracted from codomain instead of domain (bridge)

`extract_base_category()` on Arrow type `[Name* -> Proc]` follows Arrow→codomain, returning `"Proc"`. Binder positions need the domain category (`"Name"`).

**Fix**: Added `extract_binder_category()` (follows Arrow→domain) and used it in `convert_syntax_pattern`, `classify_param_from_context`, and `find_param_category`.

### 3. Macro codegen assumed non-scope fields always precede scope (MeTTaIL macros)

- `normalize.rs` hardcoded `(field_0, scope)` for all multi-binder terms; PNew has only `(scope)`.
- `exhaustive.rs` created `Scope::new(binder, ...)` (single) instead of `Scope::new(vec![binder], ...)` for multi-abstractions.
- `display.rs` iterated the binder name as a HashBag field; for binder-only terms it lives in `binder_names` from `scope.unbind()`.

**Fix**: normalize now counts pre-scope fields from `term_context`; exhaustive accepts an `is_multi_binder` flag for scope construction; display checks whether the Sep collection matches the abstraction binder and iterates `binder_names` accordingly.

## Files changed

| File | Change |
|---|---|
| `prattail/src/lib.rs` | `BinderCollection` variant on `SyntaxItemSpec` |
| `prattail/src/recursive.rs` | `BinderCollection` on `RDSyntaxItem` + separated-ident parse codegen |
| `prattail/src/classify.rs` | Recognize `BinderCollection` as multi-binder |
| `prattail/src/pipeline.rs` | Conversion + terminal collection for `BinderCollection` |
| `prattail/src/compose.rs` | Validation passthrough |
| `prattail/src/ebnf.rs` | EBNF formatting + conversion |
| `prattail/src/prediction.rs` | FIRST set: `Ident`, nullable |
| `prattail/src/grammar_gen.rs` | Proptest strategy for binder collection |
| `prattail/src/trampoline.rs` | Segment splitting + inline codegen |
| `macros/src/gen/syntax/parser/prattail_bridge.rs` | `BinderCollection` emission + `extract_binder_category()` |
| `macros/src/gen/syntax/display.rs` | Binder-aware Sep display |
| `macros/src/gen/term_ops/normalize.rs` | Dynamic pre-scope field count |
| `macros/src/gen/term_gen/exhaustive.rs` | Multi-binder scope construction |

## Follow-up: NewCong congruence rule (body not added to `proc`)

### Symptom

After the compilation fixes above, `NewCong . | S ~> T |- (PNew ^[xs].S) ~> (PNew ^[xs].T)` compiled but produced 0 rewrites at runtime — e.g. `step new (x) in { { a!(0) | (a?z).{*(z)} } }` reported "already a normal form" even though the body should reduce via Comm.

### Root cause

The deconstruction pipeline was not adding PNew's body to the `proc` relation. Since the body was never in `proc`, sub-term rewrites (Comm, etc.) never fired, and NewCong had no `S ~> T` premise to satisfy.

### Fix

Updated the deconstruction codegen to emit the body of binder-only scope terms (like PNew) into the appropriate category relation (`proc`), ensuring sub-terms are available for rewriting. After the fix, Comm fires inside PNew's body and NewCong propagates the rewrite correctly.
