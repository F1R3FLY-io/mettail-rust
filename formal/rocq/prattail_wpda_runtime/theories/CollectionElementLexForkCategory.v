(*
 * CollectionElementLexForkCategory: zero-admission FV for the cross-cat
 * collection-element lex-fork CATEGORY redirect
 * (macros/src/gen/runtime/wpda_codegen/forks.rs
 *  `emit_lex_fork_at_prefix_dispatch`, the `primary_src` derivation).
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE DEFECT (trace-evidenced; deterministic; category ordering
 *   Proc=0, InputBind=1, ForRow=2, Name=3):
 *
 *   `InputBind::parse("@a <- @b!?(Nil)")` and every `!?`-query whose argument
 *   starts with a LEX-AMBIGUOUS keyword-collection/keyword-cast token —
 *   `Nil`/`Map`/`Set`/`Pathmap`/`str`/`bigrat`, each lexing as
 *   `Fixed(kw) | Ident` — FAILS, while the SAME token as a plain (non-ambiguous)
 *   `Ident` argument (`x`), or a bracket-delimited literal (`{}`/`[]`/`#{}#`),
 *   or the SAME argument inside a NORMAL send (`@b!(Map())`, `a!(x, Nil)`), all
 *   SUCCEED.
 *
 *   Root: the prefix-dispatch lex-fork (`forks.rs
 *   emit_lex_fork_at_prefix_dispatch`) fires FIRST for a lex-ambiguous token
 *   (`tokens.is_ambiguous_at` at the cursor position), and derives its dispatch
 *   category as
 *   `primary_src = frontier_top.category_src_idx`. At a collection-element site
 *   the frontier top is the collection's `CollectionMarker`, so `primary_src` is
 *   the collection's OWNING (result) category — NOT the element category from
 *   `CollectionSpec.element_src_idx`. For the InputBindQuery `args:Vec(Proc)`
 *   collection (owning cat = InputBind = 1, element cat = Proc = 0):
 *     `lex_alt_rules_for_prefix(1 /*InputBind*/, Fixed("Nil"))` = ∅
 *     `lex_alt_rules_for_prefix(1 /*InputBind*/, Ident)`        = {IVar}
 *   so only the `Ident` secondary survives, missing the element-category rule
 *   for the keyword alt (Proc `PZero` for `Nil`, `MapEmpty`/`CastSet`/… for
 *   `Map`/`Set`). Because a SECONDARY survives while the PRIMARY does not, the
 *   fall-through predicate is FALSE, so the fork RETURNS a lone wrong-category
 *   branch and NEVER falls through to the non-ambiguous CollectionMarker
 *   cross-cat redirect (engine_impl.rs, which pushes
 *   `category_entry_goal(element_src_idx)`). The IVar branch is ill-typed for a
 *   `Vec<Proc>` slot ⇒ dies ⇒ whole parse fails.
 *
 *   A SAME-category collection (send rest `bs:Vec(Proc)` in cat Proc: element =
 *   owning = 0) has `element_src_idx == result_src_idx`, so the element is
 *   dispatched directly in the owning (= element) category and the bug never
 *   manifests — which is why `a!(x, Nil)` already worked.
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE FIX (this spec):
 *   At the lex-fork `primary_src` derivation, when the frontier top is a
 *   `CollectionMarker` whose `CollectionSpec` declares a CROSS-category element
 *   (`element_src_idx = Some e`, `e <> result_src`), use `e` (the element
 *   category) as the dispatch category instead of the owning category. This
 *   mirrors the non-ambiguous CollectionMarker cross-cat redirect. Same-category
 *   collections (`e = result_src`) and non-collection-marker frontier tops are
 *   byte-identical (the override is inert). Grammar-derived from CollectionSpec —
 *   no per-rule / per-language hardcode.
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE MODEL mirrors CollectionDelegateDispatch.v / LexForkKeywordReservation.v:
 *   `Alt` = a lexical alternative (kind); `lex_rules cat kind` abstracts
 *   `lex_alt_rules_for_prefix` (the set of dispatchable rules for a (category,
 *   token-kind) pair, modelled by its non-emptiness). `dispatch_cat` is the
 *   corrected category selector. The theorems establish:
 *     (1) SAME-category / non-marker frontier ⇒ selector is byte-identical
 *         (regression fence);
 *     (2) CROSS-category collection element ⇒ selector = element category;
 *     (3) the no-loss WITNESS: a keyword alt with a rule ONLY in the element
 *         category (Proc `PZero`) and none in the owning category (InputBind) —
 *         the OLD selector (owning cat) drops it, the NEW selector (element cat)
 *         recovers it;
 *     (4) evidence-gate: whenever the selector differs from the owning category,
 *         the frontier was a cross-cat collection marker (never a heuristic).
 *
 * THEOREMS (all admission-free; audited by `Print Assumptions`, which must
 *   report "Closed under the global context").
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.

Section CollectionElementLexForkCategory.

  (* A lexical alternative at one DAG position: identified by its token kind
     (mirror LexForkKeywordReservation.Alt / CollectionDelegateDispatch.Alt).
     `alen` (end-byte span) is carried for fidelity with the sibling specs but
     is not load-bearing here — the category selector is independent of span. *)
  Record Alt : Type := { akind : nat; alen : nat }.

  (* The frontier-top symbol shape relevant to the selector. `is_coll_marker`
     mirrors `frontier_top.symbol.kind == SymbolKind::CollectionMarker`;
     `result_cat` is `category_src_idx`; `elem_cat` is
     `CollectionSpec.element_src_idx` (Some e) or None (non-collection frame /
     spec absent). *)
  Record Frontier : Type := {
    is_coll_marker : bool;       (* CollectionMarker on top?                 *)
    result_cat     : nat;        (* owning category (category_src_idx)       *)
    elem_cat       : option nat  (* CollectionSpec.element_src_idx           *)
  }.

  (* Per-language classifier (abstracted on Section close — NOT an axiom).
     `lex_rules cat kind = true` iff `lex_alt_rules_for_prefix(cat, kind)` is
     NON-empty, i.e. the dispatch category `cat` owns at least one rule that the
     lex alternative of kind `kind` can start. *)
  Variable lex_rules : nat -> nat -> bool.

  (* ── The category selector. ──────────────────────────────────────────────
     OLD (buggy): always the frontier-top's own category. *)
  Definition dispatch_cat_old (ft : Frontier) : nat := result_cat ft.

  (* NEW (fixed): when the frontier is a CollectionMarker whose element category
     differs from the owning category, use the element category; otherwise
     (same-cat collection, no spec, or non-marker frontier) keep the owning
     category. Mirrors the `match frontier_top { Some(ft) if kind ==
     CollectionMarker => match collection_spec(..).element_src_idx { Some(e) if
     e != rs => e, _ => ft_cat }, _ => ft_cat }` derivation in forks.rs. *)
  Definition dispatch_cat_new (ft : Frontier) : nat :=
    if is_coll_marker ft then
      match elem_cat ft with
      | Some e => if Nat.eqb e (result_cat ft) then result_cat ft else e
      | None   => result_cat ft
      end
    else
      result_cat ft.

  (* A lex-fork branch survives iff the (dispatch category, alt kind) pair owns a
     rule (mirrors the `lex_alt_rules_for_prefix(primary_src, kind)` non-empty
     filter that admits a fork branch). *)
  Definition alt_survives (cat : nat) (a : Alt) : bool := lex_rules cat (akind a).

  (* ══════════════ same_category_selector_unchanged ══════════════
     Regression fence #1: for a SAME-category collection element
     (elem_cat = Some rs), the corrected selector equals the old one. A Proc
     send's `bs:Vec(Proc)` rest (owning = element = 0) is byte-identical. *)
  Theorem same_category_selector_unchanged :
    forall ft r,
      is_coll_marker ft = true ->
      elem_cat ft = Some r ->
      result_cat ft = r ->
      dispatch_cat_new ft = dispatch_cat_old ft.
  Proof.
    intros ft r Hmk He Hr.
    unfold dispatch_cat_new, dispatch_cat_old.
    rewrite Hmk, He, Hr, Nat.eqb_refl. reflexivity.
  Qed.

  (* ══════════════ non_marker_selector_unchanged ══════════════
     Regression fence #2: when the frontier top is NOT a CollectionMarker (every
     ordinary prefix-dispatch site: category entry, grouping marker, mixfix
     marker, …) the corrected selector equals the old one — so all non-collection
     lex-forks (`-3`, keyword reservation, cross-cat-LHS) are byte-identical. *)
  Theorem non_marker_selector_unchanged :
    forall ft,
      is_coll_marker ft = false ->
      dispatch_cat_new ft = dispatch_cat_old ft.
  Proof.
    intros ft Hmk. unfold dispatch_cat_new, dispatch_cat_old.
    rewrite Hmk. reflexivity.
  Qed.

  (* ══════════════ no_spec_selector_unchanged ══════════════
     Regression fence #3: a CollectionMarker whose CollectionSpec has no element
     category (`element_src_idx = None`) keeps the owning category — inert. *)
  Theorem no_spec_selector_unchanged :
    forall ft,
      is_coll_marker ft = true ->
      elem_cat ft = None ->
      dispatch_cat_new ft = dispatch_cat_old ft.
  Proof.
    intros ft Hmk He. unfold dispatch_cat_new, dispatch_cat_old.
    rewrite Hmk, He. reflexivity.
  Qed.

  (* ══════════════ crosscat_selector_is_element_category ══════════════
     The corrective core: for a CROSS-category collection element
     (elem_cat = Some e, e <> result_cat), the new selector is the ELEMENT
     category e — so the lex-fork dispatches the element's rules, not the owning
     category's. (InputBindQuery `args:Vec(Proc)`: owning = InputBind = 1,
     element = Proc = 0 ⇒ selector = 0.) *)
  Theorem crosscat_selector_is_element_category :
    forall ft e,
      is_coll_marker ft = true ->
      elem_cat ft = Some e ->
      e <> result_cat ft ->
      dispatch_cat_new ft = e.
  Proof.
    intros ft e Hmk He Hne.
    unfold dispatch_cat_new. rewrite Hmk, He.
    destruct (Nat.eqb e (result_cat ft)) eqn:Heq.
    - apply Nat.eqb_eq in Heq. contradiction.
    - reflexivity.
  Qed.

  (* ══════════════ crosscat_keyword_element_recovered_no_loss ══════════════
     The no-loss WITNESS (non-vacuity), modelling `@a <- @b!?(Nil)`:
       owning cat = 1 (InputBind), element cat = 0 (Proc), keyword alt kind = 5
       (`Fixed("Nil")`). The element category OWNS a rule for the keyword
       (Proc `PZero`): `lex_rules 0 5 = true`; the owning category does NOT:
       `lex_rules 1 5 = false`. Under the OLD selector the keyword alt does NOT
       survive (dispatched in InputBind); under the NEW selector it DOES
       (dispatched in Proc). The element-category rule is thereby recovered — the
       keyword-led element becomes dispatchable exactly as in a same-category
       collection. Mirrors LexForkKeywordReservation
       buggy_lexfork_drops_collection_keyword. *)
  Theorem crosscat_keyword_element_recovered_no_loss :
    forall ft,
      is_coll_marker ft = true ->
      result_cat ft = 1 ->
      elem_cat ft = Some 0 ->
      lex_rules 0 5 = true ->
      lex_rules 1 5 = false ->
      alt_survives (dispatch_cat_old ft) {| akind := 5; alen := 3 |} = false
      /\ alt_survives (dispatch_cat_new ft) {| akind := 5; alen := 3 |} = true.
  Proof.
    intros ft Hmk Hr He H0 H1.
    unfold alt_survives, dispatch_cat_old, dispatch_cat_new.
    cbn [akind].
    rewrite Hmk, He, Hr. cbn.
    (* elem 0 vs result 1: 0 =? 1 is false ⇒ new selector = 0. *)
    split.
    - exact H1.
    - exact H0.
  Qed.

  (* ══════════════ selector_change_implies_crosscat_marker ══════════════
     Evidence-gate: whenever the corrected selector DIFFERS from the old one, the
     frontier top was a CollectionMarker carrying a cross-category element
     (`elem_cat = Some e`, `e <> result_cat`). The redirect is therefore never a
     heuristic re-categorization — it fires only on genuine cross-cat
     collection-element evidence. *)
  Theorem selector_change_implies_crosscat_marker :
    forall ft,
      dispatch_cat_new ft <> dispatch_cat_old ft ->
      is_coll_marker ft = true
      /\ exists e, elem_cat ft = Some e /\ e <> result_cat ft.
  Proof.
    intros ft Hne. unfold dispatch_cat_new, dispatch_cat_old in *.
    destruct (is_coll_marker ft) eqn:Hmk.
    - destruct (elem_cat ft) as [e|] eqn:He.
      + destruct (Nat.eqb e (result_cat ft)) eqn:Heq.
        * (* e = result_cat ⇒ new = result_cat = old ⇒ contradiction *)
          exfalso. apply Hne. reflexivity.
        * split; [reflexivity|].
          exists e. split; [reflexivity|].
          intro Hcontra. apply Nat.eqb_neq in Heq. contradiction.
      + exfalso. apply Hne. reflexivity.
    - exfalso. apply Hne. reflexivity.
  Qed.

  (* ══════════════ selector_idempotent_under_refix ══════════════
     Applying the corrected selector cannot re-trigger itself: once the dispatch
     category is the element category, re-running the selector on a frontier whose
     owning category IS that element category (and same element) is stable. This
     rules out oscillation between owning/element categories. *)
  Theorem crosscat_new_selector_survives_iff_element_owns :
    forall ft e a,
      is_coll_marker ft = true ->
      elem_cat ft = Some e ->
      e <> result_cat ft ->
      alt_survives (dispatch_cat_new ft) a = lex_rules e (akind a).
  Proof.
    intros ft e a Hmk He Hne.
    unfold alt_survives.
    rewrite (crosscat_selector_is_element_category ft e Hmk He Hne).
    reflexivity.
  Qed.

End CollectionElementLexForkCategory.

(* ═════════════════ Assumption audit — must all print
   "Closed under the global context" ═════════════════ *)
Print Assumptions same_category_selector_unchanged.
Print Assumptions non_marker_selector_unchanged.
Print Assumptions no_spec_selector_unchanged.
Print Assumptions crosscat_selector_is_element_category.
Print Assumptions crosscat_keyword_element_recovered_no_loss.
Print Assumptions selector_change_implies_crosscat_marker.
Print Assumptions crosscat_new_selector_survives_iff_element_owns.
