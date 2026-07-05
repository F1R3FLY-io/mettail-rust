(*
 * CollectionElementInfixCategory: zero-admission FV for the cross-cat
 * collection-element InfixLoop operator-dispatch CATEGORY redirect
 * (macros/src/gen/runtime/wpda_codegen/engine_impl.rs, the
 *  `WpdaState::InfixLoop` arm's `state_cat_src_idx` derivation).
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE DEFECT (Gap 2; trace-evidenced; deterministic; runtime category order
 *   Proc=0, InputBind=1, ForRow=2, Name=3, …, List=10, Bag=11, Map=12,
 *   Set=13, Pathmap=14):
 *
 *   A MIXFIX-KEYWORD rule (`MapEmpty . |- "Map" "(" ")" : Proc`, `SetEmpty`, …
 *   — any nullary keyword-call that dispatches via a `MixfixMarker`, producing
 *   a Proc) used as an element of a CROSS-CATEGORY bracket collection literal
 *   (`[…]` List / `#{…}#` Bag / `{|…|}` Pathmap, each carrying `Vec<Proc>` /
 *   `HashBag<Proc>` / `PathMapLit<…>`, i.e. `element_src_idx = Proc(0)`) FAILS
 *   to accept any operator continuation: `[Map() * c]`, `[Map().values()]`,
 *   `[Map() == c]`, `[Set() * c]`, `#{Map() * c}#`, `{|Map() * c|}` all ERR,
 *   while `[Map()]` (no continuation), `[Map(), c]` (comma = separator),
 *   `[Nil * c]` (PZero is a single-token keyword, stays in a Proc InfixLoop),
 *   `[c * Map()]` (var LHS), the bare `Map() * c`, and the same element in a
 *   NORMAL send `b!(Map() * c, x)` (POutput2Plus args, direct-Proc slot) all
 *   SUCCEED.
 *
 *   Root: after a mixfix-keyword element completes it POPS its MixfixMarker
 *   frame, reverting the InfixLoop frontier to the collection's
 *   `CollectionMarker`. The InfixLoop dispatch derives its operator-dispatch
 *   category as `state_cat_src_idx = frontier_top.category_src_idx`, which is
 *   the collection's OWNING (result) category — List(10)/Bag(11)/Pathmap(14) —
 *   NOT the element category `CollectionSpec.element_src_idx = Proc(0)`. The
 *   per-category operator tables `infix_bp_<cat>` / `postfix_bp_<cat>` /
 *   `mixfix_bp_<cat>` are selected by `state_cat_src_idx`; `infix_bp_list("*")`
 *   = ∅ (List has no `*` — Mul is a Proc(0) operator), so no operator
 *   candidate is produced. The element then reaches the splice-gate (which
 *   probes the SAME InfixLoop and likewise sees no continuation), splices the
 *   element prematurely at its first completion, and the trailing operator is
 *   stranded.
 *
 *   A SAME-category collection (PPar `{…}` : Proc with Proc elements: owning =
 *   element = 0) has `element_src_idx == result_src_idx`, so the dispatch
 *   category IS the element category and the bug never manifests — which is why
 *   `{Map() * c}` already worked.
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE FIX (this spec):
 *   In the InfixLoop `state_cat_src_idx` derivation, when the frontier top is a
 *   `CollectionMarker` whose `CollectionSpec` declares a CROSS-category element
 *   (`element_src_idx = Some e`, `e <> result_src`), use `e` (the element
 *   category) as the operator-dispatch category instead of the owning category.
 *   This mirrors the element-dispatch redirect and the sibling lex-fork
 *   redirect (CollectionElementLexForkCategory.v). Same-category collections
 *   (`e = result_src`), CollectionMarkers with no element spec, and every
 *   non-collection-marker frontier top are byte-identical (the override is
 *   inert). The close/sep routing is unchanged: it reads the marker's
 *   `CollectionSpec` directly, so an element with NO operator continuation
 *   still falls through to Unwinding-CollectionMarker exactly as before.
 *   Grammar-derived from CollectionSpec — no per-rule / per-language hardcode.
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE MODEL mirrors CollectionElementLexForkCategory.v:
 *   `Op` = an operator token (kind); `ops cat kind` abstracts the per-category
 *   operator table `infix_bp_<cat>(kind) ∪ postfix_bp_<cat>(kind) ∪
 *   mixfix_bp_<cat>(kind)` (modelled by its non-emptiness — "category `cat`
 *   recognizes operator `kind`"). `dispatch_cat` is the corrected category
 *   selector. The theorems establish:
 *     (1) SAME-category / no-spec / non-marker frontier ⇒ selector byte-identical
 *         (three regression fences);
 *     (2) CROSS-category collection element ⇒ selector = element category;
 *     (3) the no-loss WITNESS: a Proc operator (Mul `*`) present ONLY in the
 *         element category (Proc) and absent in the owning category (List) —
 *         the OLD selector (owning) drops it, the NEW selector (element)
 *         recovers it, so the element's operator continuation is dispatched;
 *     (4) evidence-gate: whenever the selector differs from the owning category,
 *         the frontier was a cross-cat collection marker (never a heuristic);
 *     (5) stability: the new selector's operator recognition equals the element
 *         category's table (no oscillation).
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

Section CollectionElementInfixCategory.

  (* An operator token at the InfixLoop frontier: identified by its token kind.
     Mirror of CollectionElementLexForkCategory.Alt. *)
  Record Op : Type := { okind : nat }.

  (* The frontier-top symbol shape relevant to the operator-dispatch selector.
     `is_coll_marker` mirrors `frontier_top.symbol.kind ==
     SymbolKind::CollectionMarker`; `result_cat` is `category_src_idx`;
     `elem_cat` is `CollectionSpec.element_src_idx` (Some e) or None
     (non-collection frame / spec absent). Identical shape to the sibling spec. *)
  Record Frontier : Type := {
    is_coll_marker : bool;       (* CollectionMarker on top?                 *)
    result_cat     : nat;        (* owning category (category_src_idx)       *)
    elem_cat       : option nat  (* CollectionSpec.element_src_idx           *)
  }.

  (* Per-language classifier (abstracted on Section close — NOT an axiom).
     `ops cat kind = true` iff category `cat` recognizes operator `kind` as an
     infix / postfix / mixfix operator, i.e. the union of the per-category
     tables `infix_bp_<cat>(kind)` / `postfix_bp_<cat>(kind)` /
     `mixfix_bp_<cat>(kind)` selected by `state_cat_src_idx = cat` is
     non-empty. *)
  Variable ops : nat -> nat -> bool.

  (* ── The operator-dispatch category selector. ────────────────────────────
     OLD (buggy): always the frontier-top's own (owning) category — line 1133
     `frontier_top.map(|n| n.symbol.category_src_idx)`. *)
  Definition dispatch_cat_old (ft : Frontier) : nat := result_cat ft.

  (* NEW (fixed): when the frontier is a CollectionMarker whose element category
     differs from the owning category, use the element category; otherwise keep
     the owning category. Mirrors the `match frontier_top { Some(ft) if kind ==
     CollectionMarker => match collection_spec(..).element_src_idx { Some(e) if
     e != rs => e, _ => raw }, _ => raw }` derivation in engine_impl.rs. *)
  Definition dispatch_cat_new (ft : Frontier) : nat :=
    if is_coll_marker ft then
      match elem_cat ft with
      | Some e => if Nat.eqb e (result_cat ft) then result_cat ft else e
      | None   => result_cat ft
      end
    else
      result_cat ft.

  (* An operator continuation is dispatched iff the (dispatch category, op kind)
     pair recognizes the operator (mirrors the `infix/postfix/mixfix` tier scan
     over the tables selected by `state_cat_src_idx`). *)
  Definition op_dispatched (cat : nat) (o : Op) : bool := ops cat (okind o).

  (* ══════════════ same_category_selector_unchanged ══════════════
     Regression fence #1: for a SAME-category collection element
     (elem_cat = Some rs), the corrected selector equals the old one. PPar `{…}`
     (owning = element = 0, Proc) is byte-identical. *)
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
     ordinary InfixLoop site: category entry, grouping marker, mixfix marker,
     rule-at, …) the corrected selector equals the old one — so all
     non-collection InfixLoop dispatch is byte-identical. *)
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
     category e — so the InfixLoop dispatches the element category's operators,
     not the owning category's. (List `[…]`: owning = List = 10, element =
     Proc = 0 ⇒ selector = 0.) *)
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

  (* ══════════════ crosscat_element_operator_recovered_no_loss ══════════════
     The no-loss WITNESS (non-vacuity), modelling `[Map() * c]`:
       owning cat = 10 (List), element cat = 0 (Proc), operator kind = 42
       (`Mul`, the `*` token). The element category OWNS the operator (Proc has
       Mul): `ops 0 42 = true`; the owning category does NOT (List has no infix
       ops): `ops 10 42 = false`. Under the OLD selector the operator is NOT
       dispatched (looked up in List) — the element splices prematurely; under
       the NEW selector it IS (looked up in Proc) — the element's operator
       continuation fires. This is the exact `Map() * c` recovery. Mirrors
       CollectionElementLexForkCategory.crosscat_keyword_element_recovered_no_loss. *)
  Theorem crosscat_element_operator_recovered_no_loss :
    forall ft,
      is_coll_marker ft = true ->
      result_cat ft = 10 ->
      elem_cat ft = Some 0 ->
      ops 0 42 = true ->
      ops 10 42 = false ->
      op_dispatched (dispatch_cat_old ft) {| okind := 42 |} = false
      /\ op_dispatched (dispatch_cat_new ft) {| okind := 42 |} = true.
  Proof.
    intros ft Hmk Hr He H0 H10.
    unfold op_dispatched, dispatch_cat_old, dispatch_cat_new.
    cbn [okind].
    rewrite Hmk, He, Hr. cbn.
    (* elem 0 vs result 10: 0 =? 10 is false ⇒ new selector = 0. *)
    split.
    - exact H10.
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
        * exfalso. apply Hne. reflexivity.
        * split; [reflexivity|].
          exists e. split; [reflexivity|].
          intro Hcontra. apply Nat.eqb_neq in Heq. contradiction.
      + exfalso. apply Hne. reflexivity.
    - exfalso. apply Hne. reflexivity.
  Qed.

  (* ══════════════ crosscat_new_selector_dispatches_iff_element_owns ══════════
     Stability: once the dispatch category is the element category, operator
     recognition under the new selector equals the element category's table —
     no oscillation between owning/element categories, and the close/sep routing
     (which is keyed on the marker's own CollectionSpec, not this selector) is
     unaffected. *)
  Theorem crosscat_new_selector_dispatches_iff_element_owns :
    forall ft e o,
      is_coll_marker ft = true ->
      elem_cat ft = Some e ->
      e <> result_cat ft ->
      op_dispatched (dispatch_cat_new ft) o = ops e (okind o).
  Proof.
    intros ft e o Hmk He Hne.
    unfold op_dispatched.
    rewrite (crosscat_selector_is_element_category ft e Hmk He Hne).
    reflexivity.
  Qed.

End CollectionElementInfixCategory.

(* ═════════════════ Assumption audit — must all print
   "Closed under the global context" ═════════════════ *)
Print Assumptions same_category_selector_unchanged.
Print Assumptions non_marker_selector_unchanged.
Print Assumptions no_spec_selector_unchanged.
Print Assumptions crosscat_selector_is_element_category.
Print Assumptions crosscat_element_operator_recovered_no_loss.
Print Assumptions selector_change_implies_crosscat_marker.
Print Assumptions crosscat_new_selector_dispatches_iff_element_owns.
