# Collection-Primary Infix Binding-Power Fix (WPDA parser)

**Target:** branch `feature/wfst-architecture`, baseline HEAD `ad08a9a8`.
**Status:** design complete + verified against HEAD (Plan agent `a75661aaa3e299613`); implementation in progress.

## The bug (general class)

`Proc::parse("str({a} <= {a})")` (rhocalc) returns ERR `1:5 no accepting branch … found Fixed({)`,
while `str(1 <= 2)` parses OK. This is **general**: any collection primary that is **not at the
parse root** (cast argument, list element, any mid-parse frame) cannot attach **any** infix operator
(`<=`,`<`,`==`,`!=`,`+`,`or`,`and`), for any collection type (`{}`/PPar, `[]`/List), any nesting
depth, any prefix-cast keyword (`str`,`bigint`,`bigrat`).

## Root cause

Collection primaries never feed the enclosing Pratt `InfixLoop`:

- An **atomic** primary returns through a `Return` frame whose `Unwinding`-pop forces
  `InfixLoop{cur_bp}` (`macros/.../wpda_codegen/engine_impl.rs:529-532`), so the infix attaches
  on the still-present body `CategoryEntry` **before** it pops.
- A **collection** finalizes via `Fork[ConsumeAtAndPop/Unwinding]`
  (`macros/.../wpda_codegen/collection.rs:458,487`) which pops the `CollectionMarker` straight to
  `Unwinding`. The body-`CategoryEntry` pop table (`prattail/src/wpda_walker.rs:18726-18755`;
  mirror `:16367-16373`) only re-enters `InfixLoop` when the predecessor is the root or another
  `CategoryEntry`. For `str(`, the predecessor is the `str` `BinderRule` `RuleAt` (a `Some(_)`) ⇒
  `Unwinding` ⇒ `<=` never attaches. At top level `{a} <= {a}` works only because the predecessor
  is the root (`GSS_NODE_NONE`).

Unrelated to RC-A/RC-B: rhocalc `LtEq`/`ToStr` are **same-category** (`Proc→Proc`), invisible to the
cross-cat-LHS / `prefix_cast_into` machinery (`semantic_actions.rs:339` skips same-category casts).

## Control-flow fact (carrier rationale)

The `CollectionLoop` **state** is destroyed across an element sub-parse: after each element the cursor
is in `Unwinding` on the `CollectionMarker`, and `engine_impl.rs:584-665` reconstructs `CollectionLoop`
purely from the persistent marker symbol. So the dispatch bp **must ride on the `CollectionMarker`
symbol** — it cannot live only in the state. The marker's `bp` slot already holds `slot_idx`, so a
**distinct carrier** is required.

## Design decision — the carrier + the binder/Pratt distinction

Two pieces of information are needed at the collection close: (a) **the dispatch bp** (for
`InfixLoop`), which is per-parse and must ride on the GSS-persistent `CollectionMarker` (the
`CollectionLoop` state is destroyed across each element sub-parse and rebuilt from the marker); and
(b) **whether this collection is a Pratt primary or a binder-internal slot** — binder-internal
collections (Class 2/3 binder rule slots, e.g. `pair ( xs ) ( ys )`) must NOT re-enter the Pratt
`InfixLoop` on close (they resume the binder rule continuation via `Unwinding`); only Class-5
Pratt-primary collections should `InfixLoop`. (b) is a **codegen-static** fact (the rule kind is
known at macro-expansion time), so it does not need to ride on the marker.

- **(a) the bp carrier:** `pub coll_dispatch_bp: Option<u8>` on `StackSymbolV2`. `Some(cur_bp)` for a
  `CollectionMarker` (the Pratt bp captured at the open delimiter), `None` for every other symbol kind
  ⇒ no change to their `Eq/Hash/Ord` identity or GSS-merge behavior. For collection markers it
  participates in GSS-node identity; two markers dispatched at different bps become distinct GSS nodes
  (sound — matching the `GroupingMarker.bp` precedent; a given source `{` is dispatched at one `cur_bp`
  per derivation context, so real sharing is not fragmented). This grows `StackSymbolV2` 8→10 bytes
  (the `stack_symbol_v2_size_is_compact` assertion is updated `≤8`→`≤10`, documented). The 2 bytes
  buy the cleanest, sentinel-free encoding; the marker carries `Some(cur_bp)` for Class-5 and
  `Some(0)` for binder slots (the binder bp is unused — see (b)).
- **(b) the Pratt/binder distinction:** `is_binder_internal: bool`, added as a 4th element of the
  per-rule close lookup tuple (`(close, sep, kv_sep, is_binder_internal)`), keyed
  `(result_src_idx, rule_idx, slot_idx)`. `classify_collection` (Class-5) ⇒ `false`; `classify_binder`
  slots ⇒ `true`. The close branch is `if is_binder_internal { Unwinding } else { InfixLoop{cur_bp} }`.
  This keeps `CollectionLoop.outer_bp: u8` UNCHANGED (no Map/kv-phase reader churn or risk).

Rejected alternatives: reuse `bp` (holds slot_idx, read at `engine_impl.rs:627`); pack into
`rule_index_in_category` (true u16); `CollectionLoop.outer_bp: Option<u8>` (ripples to the Map
kv-phase readers — higher risk); a two-variant `SymbolKind` enum payload (keeps 8 bytes but doubles
variant handling at 14 match sites — more error-prone than the +2-byte field).

## Edits (ordered)

1. **`prattail/src/wpda_runtime.rs`** — add `coll_dispatch_bp: Option<u8>` field to `StackSymbolV2`;
   `collection_marker(result, rule, accumulator_id, dispatch_bp: u8)` sets
   `coll_dispatch_bp: Some(dispatch_bp)`; the 7 other ctors set `coll_dispatch_bp: None`
   (`with_kind_return` uses `..self`); `Display` shows `@d{bp}` for trace parity; the
   `stack_symbol_v2_size_is_compact` test asserts `≤10` (was `≤8`), with a rationale comment.
   (One raw `StackSymbolV2 { … }` literal in a `wpda_walker.rs` test also gains `coll_dispatch_bp: None`;
   the two `wpda_walker.rs` test ctor calls gain the 4th arg.)
2. **`macros/.../wpda_codegen/collection.rs`** (open) — pass `*cur_bp` as the 4th `collection_marker`
   arg (covers both synth-paren and direct-delimited open paths; `*cur_bp` is in scope — the
   synth-paren `new_state` reads it).
3. **`macros/.../wpda_codegen/binder.rs`** (3 sites) — pass `0u8` as the 4th arg (binder-internal
   collections; the bp is unused since `is_binder_internal` routes them to `Unwinding`).
4. **`macros/.../wpda_codegen/engine_impl.rs`** (reconstruction) — `outer_bp: 0` → `outer_bp: dispatch_bp`
   where `let dispatch_bp = node.symbol.coll_dispatch_bp.unwrap_or(0);` (`unwrap_or(0)` degrades safely).
5. **`macros/.../wpda_codegen/collection.rs`** (lookup + close) — extend the close lookup with
   `is_binder_internal` (Class-5 `false`, binder `true`); the two G1 (`kv_phase==0`) close branches
   become `new_state: if is_binder_internal { WpdaState::Unwinding } else { WpdaState::InfixLoop { cur_bp: *_outer_bp } }`.
   Leave G2 sep and G3 bare (`PrefixDispatch{cur_bp:0}`) UNCHANGED.

**Why no-loss:** after the `ConsumeAtAndPop` fork pops the `CollectionMarker`, the body-CategoryEntry
pop table's `if popped.kind == CategoryEntry` guard is FALSE (popped is the marker), so the fork's
`new_state` survives onto the body `CategoryEntry`. For Class-5, that is `InfixLoop{cur_bp:outer_bp}`,
mirroring the atomic Return path; it either attaches an op with `l_bp > outer_bp` or falls through to
`Unwinding` via the CollectionMarker frontier reroute (`engine_impl.rs:944-1011`). For binder slots it
is `Unwinding` — byte-identical to the pre-fix behavior. `str({a})`, empty collections, nested closes,
and all binder collections are unchanged.

**Why no-loss:** after the `ConsumeAtAndPop` fork pops the `CollectionMarker`, Site A's
`if popped.kind == CategoryEntry` guard is FALSE (popped is the marker), so the fork's
`InfixLoop{cur_bp:outer_bp}` survives onto the body `CategoryEntry`, mirroring the atomic Return path.
`InfixLoop` either attaches an op with `l_bp > outer_bp` or falls through to `Unwinding` via the
CollectionMarker frontier reroute (`engine_impl.rs:944-1011`) — `str({a})`, empty collections, nested
closes unchanged byte-for-byte.

## Precedence-inversion elimination

`InfixLoop{cur_bp:outer_bp}` attaches iff `op.l_bp > outer_bp` (standard Pratt). Worked:
- `str({a} <= {a})`: `{` dispatched at body bp `b₀`; on `}` close, `LtEq.l_bp > b₀` ⇒ attaches ⇒ `LtEq({a},{a})`. **FIXED.**
- `1 + {a} <= {b}`: `{a}` is Add's RHS, dispatched at `Add.r_bp`; on close `LtEq.l_bp <= Add.r_bp` ⇒ `<=` does NOT attach ⇒ Add completes `Add(1,{a})`, then `<=` attaches outer ⇒ `LtEq(Add(1,{a}),{b})`. **inversion eliminated.**
- `str({a} + {b} <= {c})` ⇒ `str(LtEq(Add({a},{b}),{c}))`. **FIXED.**

## Formal verification

`formal/rocq/prattail_wpda_runtime/theories/CollectionPrimaryInfix.v` (registered in `_CoqProject`),
**zero-admission — 12 theorems, all `Print Assumptions` = "Closed under the global context"** (verified
via `coqc -Q theories PrattailWpdaRuntime theories/CollectionPrimaryInfix.v`). Reuses `RuntimeModel.v`
(`category_entry_post_pop_state` = the InfixLoop-vs-Unwinding post-pop landing; `resolve_category_entry_post_pop`;
`PredOther`). Models the Pratt guard as `op_attaches l_bp b := Nat.ltb b l_bp`. Three obligations:
1. **Symmetry/completeness:** `collection_primary_landing = atomic_primary_landing` (both `PostPopInfixLoop`)
   and `collection_attaches l_bp b = atomic_attaches l_bp b`. Contrast lemmas document the bug:
   `prefix_breaks_symmetry` (pre-fix landing was `PostPopUnwinding`) and `prefix_collection_never_attaches`.
2. **No-loss/off-gate identity:** `off_gate_is_unwinding` (no candidate `l_bp > b` ⇒ `PostPopUnwinding`),
   `on_gate_is_infixloop` (some candidate ⇒ `PostPopInfixLoop`), and `str_predecessor_pop_is_unwinding`
   (`resolve_category_entry_post_pop PredOther _ = PostPopUnwinding` — the `str` RuleAt pop governs the
   POST-attach pop, so the existing table arm stays correct).
3. **Bp-soundness:** `no_attach_when_le` (`l_bp ≤ b ⇒ op_attaches = false`), `attach_when_gt`, and the
   `AddLtEqPrecedence` section's `lteq_does_not_attach_in_add_rhs` (for any grammar with `lteq_lbp ≤
   add_rbp`) + concrete witnesses (`op_attaches 10 0 = true` at the cast body; `op_attaches 10 20 = false`
   in the `+` RHS) — rejecting the `1 + ({a} <= {b})` inversion.

Build (full suite): `make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-prattail-wpda`.

## Regression

New tests (`languages/tests/rhocalc_tests.rs`, `mod collection_primary_infix`): `ppar_lteq_in_cast`
(`str({a} <= {a})` ⇒ `ToStr(LtEq(..))`), `collection_comparison_as_list_element` (`[{a} <= {a}]` ⇒
`CastList`), `precedence_lock_collection_in_add_rhs` (`1 + {a} <= {b}` ⇒ `LtEq(Add(..),..)`),
`precedence_lock_inside_cast` (`str({a} + {b} <= {c})` ⇒ `str(LtEq(Add(..),..))`). All 4 pass.

Verified vs the complete pre-str-cast baseline (`agent-a7430` worktree = `9e547da2` + the lazy lexer,
i.e. main minus the str-cast edits): **zero new failures**. `prattail --lib` 3766/0 (the
`stack_symbol_v2_size_is_compact` assertion was updated `≤8`→`≤10`), `rhocalc_tests` 10→14 (+4 new),
`calculator` 100/0 (RC-A/RC-B intact), `gen_calculator_unit` 169, `gen_rhocalc_unit` 86,
`collection_ghost_regression` 5, `wpda_parity_*` green.

## Pre-existing failures (NOT regressions — present at the baseline)

These fail identically at the pre-str-cast baseline and after the fix; they are out of scope for this
change and were not introduced by it:
- `class2_binder_with_collection_smoke::pred5_missing_close_paren_recovers` (binder error-recovery).
- `class2_multi_collection_smoke` + `class3_multi_collection_smoke` (`pred1..pred4` — multi-slot binder
  collections). NOTE: the `is_binder_internal` routing makes binder collections close to `Unwinding`,
  exactly matching this baseline behavior, so these are unchanged.
- The `*_display_parse_roundtrip` proptest NOISE BAND and the `simulation_integration` /
  `probe_neg_zero` eval-layer probes.

## Build order

1. Baseline capture at `ad08a9a8`.
2. Edit 1 (`wpda_runtime.rs`); `cargo build -p mettail-prattail` (compiler flags every missed struct
   literal — the safety net).
3. Edits 2–5 (codegen); `cargo build -p mettail-languages` (proc-macro re-expands).
4. Edit 6 (comments).
5. Add tests + `CollectionPrimaryInfix.v` + `_CoqProject`.
6. Run regression + FV; diff vs baseline; confirm 6 `Print Assumptions` closed.
