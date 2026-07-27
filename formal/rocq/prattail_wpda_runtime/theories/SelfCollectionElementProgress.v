(*
 * SelfCollectionElementProgress: the two flip-proven roots of the rholang
 * self-collection (PPar) parse failures, and the soundness of their fixes.
 *
 * GROUND TRUTH (agent investigation, 2026-06-10, all flip-proven at 82310a24):
 *   ROOT 1 — `ProjDescriptorKey {gss_node, sppf_stack, cat_src, cur_bp}`
 *   (wpda_walker.rs:3097) INTENTIONALLY dropped the input position on the
 *   premise that `sppf_stack` is a faithful progress proxy. The premise is
 *   FALSIFIED by self-collections: `emit_splice_into_collection` POPS the
 *   element's SppfId off the stack (restoring the exact pre-element StackId),
 *   and every element dispatches at the SAME CollectionMarker GSS node with
 *   `cur_bp:0` — so element k+1's descriptor is bit-identical to element 1's
 *   and the GLL cycle defense KILLS it (minimal reproducer `{1 | 2}` fails;
 *   `{1 | (2)}` passes — kill-side flip; `{1 | z!(0)}` silently MIS-PARSES via
 *   the branch-strip site). Scott & Johnstone's GLL descriptor is (L, u, i, w)
 *   — `i` (the input position) was the missing component.
 *   ROOT 2 — the collection splice gate treats a RuleAt pop directly above a
 *   CollectionMarker as UNCONDITIONAL element completion (case 1,
 *   wpda_walker.rs:15562); the justifying premise ("these only top a marker at
 *   element completion") is stale since in-collection infix extension: a
 *   literal-led PREFIX rule (PDrop) completes its RULE while the ELEMENT may
 *   continue with an infix (`{*(z) + 2}`) — the premature splice steals the
 *   infix LHS and the Add fires against the CollectionId (expected-cat reject).
 *
 * THE FIXES:
 *   F1 — add `pos` to the descriptor key. This theory proves the refinement
 *   sound: a FINER key kills a SUBSET (no new false kills), a genuine
 *   no-progress re-entry (same pos — consuming a token IS progress, so a true
 *   cycle cannot advance pos) is STILL caught, and the pos-advancing
 *   collection re-entry is ADMITTED (the flip-proven family lives).
 *   F2 — RuleAt pops above a marker take the SAME one-step probe as the other
 *   pop kinds (splice iff the engine yields no Pratt continuation): the
 *   element-completion contract becomes uniform; prefix-rule completions with
 *   a pending infix defer the splice exactly as atomic-head elements do.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Section DescriptorPosRefinement.

  (* The shipped key components and the input position. *)
  Record OldKey : Type := mkOld {
    ok_node : nat;
    ok_sppf : nat;
    ok_cat : nat;
    ok_bp : nat;
  }.

  Record NewKey : Type := mkNew {
    nk_node : nat;
    nk_sppf : nat;
    nk_cat : nat;
    nk_bp : nat;
    nk_pos : nat;        (* the GLL `i` component, restored *)
  }.

  Definition forget (k : NewKey) : OldKey :=
    mkOld (nk_node k) (nk_sppf k) (nk_cat k) (nk_bp k).

  (* The cycle defense kills a re-entry iff its descriptor EQUALS an already-
     visited descriptor. *)
  Definition old_kills (a b : NewKey) : Prop := forget a = forget b.
  Definition new_kills (a b : NewKey) : Prop := a = b.

  (* ── F1 SOUNDNESS 1: the finer key kills a SUBSET — adding a component can
        only separate entries, never newly collide them (no new false kills). ── *)
  Theorem finer_key_kills_subset :
    forall a b, new_kills a b -> old_kills a b.
  Proof.
    intros a b H. unfold new_kills in H. subst. reflexivity.
  Qed.

  (* ── F1 SOUNDNESS 2: a GENUINE no-progress re-entry — same node, sppf, cat,
        bp AND same pos — is still caught. (Premise, transcribed: the walker
        advances `pos` only by consuming input; a true cycle consumes nothing,
        so it re-enters at the same pos.) ── *)
  Theorem no_progress_still_caught :
    forall a b, old_kills a b -> nk_pos a = nk_pos b -> new_kills a b.
  Proof.
    intros [an as_ ac ab ap] [bn bs bc bb bp] H Hp.
    unfold old_kills, forget in H. simpl in *.
    injection H as <- <- <- <-. subst. reflexivity.
  Qed.

  (* ── F1 LIVENESS: the flip-proven collection family — element k+1 re-enters
        with IDENTICAL old-key components (the splice restored the sppf id; the
        marker node and bp are shared) but an ADVANCED pos — is ADMITTED by the
        new key while the old key killed it (the `{1 | 2}` reproducer). ── *)
  Theorem collection_reentry_admitted :
    forall a b, old_kills a b -> nk_pos a <> nk_pos b -> ~ new_kills a b.
  Proof.
    intros a b _ Hp Hk. apply Hp. unfold new_kills in Hk. subst. reflexivity.
  Qed.

  (* Non-vacuity witness: two descriptors equal on every old component,
     differing only in pos — old kills, new admits. *)
  Theorem shipped_killed_live_element :
    let e1 := mkNew 1 0 0 0 1 in
    let e2 := mkNew 1 0 0 0 5 in
    old_kills e1 e2 /\ ~ new_kills e1 e2.
  Proof.
    split.
    - reflexivity.
    - intro H. unfold new_kills in H. inversion H.
  Qed.

  (* ════════════════════════════════════════════════════════════════════════
     FLIP-DRIVEN REFINEMENT (2026-06-10, scientific ledger): keying pos
     GLOBALLY regressed rholang basics (`x!(0)` failed; suite 0.6s→133s) —
     the descriptor set serves a SECOND role beyond cycle defense: the
     cross-POSITION dispatch-suppression memo that keeps the cross-cat
     projection fan from re-firing at every input position. The sppf-restore
     aliasing that requires pos exists ONLY at CollectionMarker-node
     dispatches (the splice pops the element's SppfId at the SAME marker
     node). So the shipped key is ZONE-GATED: marker-node dispatches carry
     the real pos; all other dispatches carry the NO_POS sentinel — making
     their keys EXTENSIONALLY IDENTICAL to the pre-fix key (the memo role is
     preserved verbatim), while the marker zone enjoys the three theorems
     above.
     ════════════════════════════════════════════════════════════════════════ *)

  Definition NO_POS : nat := 0.   (* sentinel; real positions are 1-based here *)

  Definition gated_key (is_marker : bool) (k : NewKey) : NewKey :=
    if is_marker then k
    else mkNew (nk_node k) (nk_sppf k) (nk_cat k) (nk_bp k) NO_POS.

  (* Non-marker zone: two entries collide under the gated key IFF they collide
     under the OLD key — the suppression memo is preserved exactly. *)
  Theorem nonmarker_zone_is_old_key :
    forall a b,
      (gated_key false a = gated_key false b) <-> old_kills a b.
  Proof.
    intros a b. unfold gated_key, old_kills, forget. split.
    - intro H. injection H as H1 H2 H3 H4. rewrite H1, H2, H3, H4. reflexivity.
    - intro H. injection H as H1 H2 H3 H4. rewrite H1, H2, H3, H4. reflexivity.
  Qed.

  (* Marker zone: the gated key IS the pos-bearing key — the three theorems
     (finer_key_kills_subset / no_progress_still_caught /
     collection_reentry_admitted) apply verbatim. *)
  Theorem marker_zone_is_new_key :
    forall a b, (gated_key true a = gated_key true b) <-> new_kills a b.
  Proof. intros a b. unfold gated_key, new_kills. reflexivity. Qed.

End DescriptorPosRefinement.

Section SpliceGateProbe.

  (* Element state at a pop above the CollectionMarker: what the one-step
     InfixLoop probe would do next. *)
  Inductive ProbeOutcome : Type :=
    | NoContinuation       (* engine yields Advance(Unwinding): sep/close next *)
    | PrattContinuation.   (* an infix candidate exists: the element CONTINUES *)

  (* The element is COMPLETE iff no Pratt continuation exists. *)
  Definition element_complete (p : ProbeOutcome) : bool :=
    match p with
    | NoContinuation => true
    | PrattContinuation => false
    end.

  (* The shipped case-1 (RuleAt pops): splice UNCONDITIONALLY. *)
  Definition shipped_ruleat_splices (_ : ProbeOutcome) : bool := true.

  (* The fixed gate: RuleAt pops take the probe, like every other pop kind. *)
  Definition fixed_ruleat_splices (p : ProbeOutcome) : bool := element_complete p.

  (* The stale premise, witnessed: a prefix-rule completion with a PENDING
     INFIX (the `{*(z) + 2}` family) is spliced by the shipped gate although
     the element is NOT complete — the splice steals the infix LHS. *)
  Theorem shipped_splices_incomplete_element :
    shipped_ruleat_splices PrattContinuation = true
    /\ element_complete PrattContinuation = false.
  Proof. split; reflexivity. Qed.

  (* The fixed gate splices EXACTLY the complete elements. *)
  Theorem fixed_splices_iff_complete :
    forall p, fixed_ruleat_splices p = element_complete p.
  Proof. intro p. reflexivity. Qed.

  (* No loss for the working families: when the element IS complete (sep or
     close next — `{*(z) | …}`, `{*(z)}`), the fixed gate still splices. *)
  Theorem fixed_keeps_complete_splice :
    fixed_ruleat_splices NoContinuation = true.
  Proof. reflexivity. Qed.

End SpliceGateProbe.
