# Phase F.3 deferral: SPPF/builder desync at D8 sites blocks cursor.builder deletion

**Date**: 2026-05-18
**Status**: F.3 PARTIALLY deferred pending SPPF/builder sync fix.
**Branch tip at deferral**: post-F.2 (6e3725c).
**Replaces**: phase-f-cursor-builder-deletion.md §F.3.

## Summary

F.3's ~−480 LoC deletion of `cursor.builder` is BLOCKED on a real
SPPF/builder desync uncovered during F.2 verification: at the D8 fix
sites (`Return`-pop top_term_type_name and
`GroupingClosePreservingInner` resolve), the SPPF stack's top can be
a `Terminal` while the builder's top is a `Term` with a known
type_name. F.3 cannot complete until the SPPF mirror reliably
reflects the same top-cat as the builder at these sites.

## Empirical evidence

Diagnostic over the rholang cross-cat cast suite
(`cross_cat_rholang_castop_add_castfixed_smoke`, 2026-05-18):

```text
[F.3-DIAG] D8 divergence: bs=Some(0) (type_name=Some("...::Proc"))
           ss=None new_top_cat=5 stack_len=2 top_sid=Some(6)
           top_node=Some(Discriminant(0))   # Terminal
[F.3-DIAG] D8 divergence: bs=Some(6) (type_name=Some("...::Fixed"))
           ss=None new_top_cat=5 stack_len=2 top_sid=Some(3)
           top_node=Some(Discriminant(0))   # Terminal
```

`SppfNode::Terminal` has variant discriminant 0 (enum order:
`Terminal=0, Symbol=1, Packing=2, Epsilon=3, CollectionId=4,
OptAbsent=5, Predicate=6, BinderScope=7`).

So at the D8 site for cross-cat casts:
- `cursor.builder.top_term_type_name()` resolves to the post-action
  Rust type (Proc, Fixed) → `cat_of_type_name` returns `Some(cat)`.
- `cursor.sppf_stack.last()` points at a `Terminal` node.
- `cursor_top_non_terminal_tag` returns `None` because the top isn't
  a `Symbol`.

The two views disagree: builder reports a fired-action result; SPPF
reports a raw terminal token without the wrapping Symbol that should
have been pushed by the latest FireAction's SPPF mirror.

## Root cause hypothesis

`emit_fire_action` gates its SPPF mirror on `cursor.sppf_stack.len()
>= arity`. The `debug_assert!` above (Bug P) panics in debug mode if
the gate fails, but the `if` skips the Packing/Symbol intern silently
in release. For cross-cat cast paths, some emit_fire_action's gate
fails (sppf_stack underflow vs arity), the mirror skips, and the
SPPF lacks the Symbol that the builder side did push (via the
action_fn's `push_term`).

The bug predates F.1/F.2/F.3 — the SPPF/builder desync exists
independently of the deletion work. F.0 (realize_root_to_terms post-
pass) tolerates it via the cursor's fully-realized SPPF root; the
D8 fix paths consult builder.top because they need the post-action
TYPE NAME directly.

## Why F.3 is blocked

The plan's F.3 deletion (~−480 LoC) removes:
- 14 `Arc::make_mut(&mut cursor.builder).<m>()` mutation sites.
- 11 `Arc::clone(&cursor.builder)` Fork-fanout sites.
- 4 `Arc::new(SemanticBuilder::new())` reset sites.
- The field declaration.

The 14 mutation sites include `emit_push_term`, `emit_push_ident`,
`emit_fire_action`'s `Arc::make_mut(&mut cursor.builder).fire_action(...)`,
etc. These maintain `builder.stack` — the source-of-truth for
`top_term_type_name()`. Deleting them breaks the D8 reads at lines
7983 / 8025 of `wpda_walker.rs`.

## Resolution path (out of F.3 scope)

Three options for the future:

1. **Fix the SPPF/builder sync at FireAction**: identify why the
   sppf_stack underflow gate fails for cross-cat casts. Restore the
   missing Symbol pushes (or remove the gate / make it a hard
   error). Once SPPF top is always a Symbol when builder top is a
   Term, swap D8 reads to `cursor_top_non_terminal_tag` and proceed
   with F.3.

2. **Walker-maintained `last_action_output_cat` field**: store the
   latest emitted action's `output_cat` in a new cursor field after
   every successful `emit_fire_action`. D8 reads this field instead
   of builder.top_term_type_name. Requires care to clear/preserve
   the field across non-action pushes (emit_push_token,
   emit_push_ident).

3. **Walker-maintained `top_cat_stack: Vec<u16>` mirror**: track the
   builder's stack-top cat in a parallel Vec. Push on every emit_*
   that mutates builder.stack; pop in lockstep. Equivalent to
   builder.stack's type-name layer, without the builder.

Option 1 is most principled (no new field, fixes a latent bug).
Option 2 is smallest. Option 3 is most parallel to the existing
F.1 `collection_stack_depth` mirror pattern.

## What was retained from F.3 work

- F.2 parity-assert cleanup: the per-site `debug_assert_eq!` between
  builder and SPPF reads is dropped where the SPPF side is now the
  primary source. The merge_equivalent_cursors structural assert is
  retained (it's bucket-invariant, not parity-dependent).
- F.1 helper docstring caveat for `cursor_top_non_terminal_tag`
  noting the D8 limitation.

## State at deferral

- F.0: shipped (`c683ec7`).
- F.1: shipped (`b9e3a63`) — adds `collection_stack_depth` mirror + 3
  helpers + parity-asserted across the gauntlet.
- F.2: shipped (`6e3725c`) — swaps 6 of 8 read sites; 2 D8 reads
  retained.
- F.3: deferred; this doc replaces the original F.3 section.

The `cursor.builder` field remains; it is now read only by the 2
D8 paths. All collection_stack-related reads were swapped to the
SPPF-side mirror. The collection-counter parity invariant holds
across the gauntlet (verified during F.1, F.2).
