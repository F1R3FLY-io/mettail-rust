(*
 * PrefixCohortIsolationGeneral: SOUNDNESS of the recognizer pop FAN-OUT
 * (investigation a166789b, Stage-B mechanism).
 *
 * The architecture-native non-parseability RECOGNIZER runs the WFST walker with
 * `recognizer_mode = true`: `merge_equivalent_cursors` coarsens the merge key to
 * the GLL SLOT (keep-one), and — crucially — every pop FANS OUT over
 * `pop_all_predecessors(node)`, i.e. the targets of ALL out-edges the shared GSS
 * node accumulated. Edges are NODE-scoped: every cursor that pushed symbol@pos
 * onto a node recorded its predecessor edge on that node, and keep-one merge
 * discards cursors but NEVER removes edges. So a pop target that a discarded
 * cursor would have reached is still an out-edge of the shared node, and the
 * fan-out recovers it.
 *
 * This file discharges the load-bearing soundness obligation for that design:
 *
 *   FAN-OUT reachability  ⊇  SlotEdge reachability.
 *
 * SlotEdge (the fine key that RETAINS the edge-stack) keeps every cursor's
 * pop route distinct and is empirically 0-false-reject (the Stage-0 gate). If
 * fan-out reaches a superset, then keep-one-Slot + fan-out is ALSO 0-false-
 * reject: whenever a parse exists (some recorded edge-stack route reaches an
 * accept), fan-out finds it. Contrapositively, when the recognizer reports
 * Unreachable (fan-out reaches no accept), NO route reaches an accept, so the
 * span is genuinely non-parseable and rejecting it is sound. The recognizer
 * therefore NEVER false-rejects a parseable span.
 *
 * Model. A GSS is the list of accumulated out-edges (`src` node -> `tgt`
 * predecessor node). A cursor's `incoming_edge_stack` is a `path` of edges,
 * each an out-edge of the running node (the push/pop invariant
 * `stack.top.source = cursor.node`, maintained by push and
 * `replace_top_with_edge_id`), consecutive edges connected head-to-tail.
 * `reachable_in` is fan-out reachability (fan over `succ` at each pop step).
 * The key step (`succ_spec`): a recorded edge, being an out-edge of the current
 * node, has its target among that node's fan-out successors.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Section PrefixCohortIsolationGeneral.

  (* A GSS out-edge: from source node to a predecessor (pop-target) node. *)
  Record Edge : Type := { src : nat; tgt : nat }.

  (* The GSS = the list of all accumulated out-edges (node-scoped; keep-one
     merge never removes them). *)
  Definition Gss : Type := list Edge.

  (* pop_all_predecessors(n): the targets of EVERY out-edge of node n — the
     recognizer's fan-out pop routing. *)
  Definition succ (n : nat) (g : Gss) : list nat :=
    fold_right
      (fun e acc => if Nat.eqb (src e) n then tgt e :: acc else acc)
      [] g.

  (* The load-bearing step: any out-edge of n contributes its target to the
     fan-out successors of n. *)
  Lemma succ_spec : forall n g e,
    In e g -> src e = n -> In (tgt e) (succ n g).
  Proof.
    intros n g e Hin Hsrc.
    induction g as [| h rest IH].
    - contradiction.
    - simpl in Hin. simpl. destruct Hin as [Heq | Hrest].
      + subst h. rewrite Hsrc. rewrite Nat.eqb_refl. left. reflexivity.
      + destruct (Nat.eqb (src h) n).
        * right. apply IH. exact Hrest.
        * apply IH. exact Hrest.
  Qed.

  (* Structural edge-equality test + membership, to state "the recorded edge is
     in the GSS" decidably. *)
  Definition edge_eqb (a b : Edge) : bool :=
    Nat.eqb (src a) (src b) && Nat.eqb (tgt a) (tgt b).

  Definition edge_in (e : Edge) (g : Gss) : bool :=
    existsb (edge_eqb e) g.

  Lemma edge_eqb_eq : forall a b,
    edge_eqb a b = true -> src a = src b /\ tgt a = tgt b.
  Proof.
    intros a b H. unfold edge_eqb in H.
    apply Bool.andb_true_iff in H. destruct H as [Hs Ht].
    rewrite Nat.eqb_eq in Hs. rewrite Nat.eqb_eq in Ht. split; assumption.
  Qed.

  Lemma edge_in_spec : forall e g,
    edge_in e g = true ->
    exists e', In e' g /\ src e' = src e /\ tgt e' = tgt e.
  Proof.
    intros e g H. unfold edge_in in H. apply existsb_exists in H.
    destruct H as [e' [Hin Heq]]. apply edge_eqb_eq in Heq.
    destruct Heq as [Hs Ht]. exists e'.
    split; [exact Hin | split; symmetry; assumption].
  Qed.

  (* A recorded edge-stack path (a single cursor's incoming_edge_stack = the
     SlotEdge pop route): each edge is in the GSS AND is an out-edge of the
     running node, and consecutive edges connect head-to-tail. *)
  Fixpoint path_valid (g : Gss) (start : nat) (p : list Edge) : bool :=
    match p with
    | [] => true
    | e :: rest =>
        edge_in e g && Nat.eqb (src e) start && path_valid g (tgt e) rest
    end.

  Fixpoint path_end (start : nat) (p : list Edge) : nat :=
    match p with
    | [] => start
    | e :: rest => path_end (tgt e) rest
    end.

  (* Fan-out reachability: node reachable from start within `fuel` pop steps,
     fanning over `succ` at each step. *)
  Fixpoint reachable_in (fuel : nat) (g : Gss) (start node : nat) : Prop :=
    start = node \/
    match fuel with
    | 0 => False
    | S f => exists m, In m (succ start g) /\ reachable_in f g m node
    end.

  (* THE load-bearing lemma: a node reachable by a valid recorded edge-stack
     path is reachable by fan-out within that path's length. At each pop the
     recorded edge is an out-edge of the current node (`path_valid`), so its
     target is a fan-out successor (`succ_spec`) — fan-out subsumes the single
     recorded route, step by step. *)
  Theorem path_reaches_fanout : forall p g start,
    path_valid g start p = true ->
    reachable_in (length p) g start (path_end start p).
  Proof.
    induction p as [| e rest IH].
    - intros g start _. simpl. left. reflexivity.
    - intros g start Hv. simpl in Hv.
      apply Bool.andb_true_iff in Hv. destruct Hv as [Hv1 Hrest].
      apply Bool.andb_true_iff in Hv1. destruct Hv1 as [Hein Hsrc].
      rewrite Nat.eqb_eq in Hsrc.
      simpl. right. exists (tgt e). split.
      + apply edge_in_spec in Hein.
        destruct Hein as [e' [Hin [Hs Ht]]].
        rewrite <- Ht. apply succ_spec; [exact Hin | rewrite Hs; exact Hsrc].
      + apply IH. exact Hrest.
  Qed.

  (* SlotEdge reachability = existence of a valid recorded route. SlotEdge keeps
     every edge-stack distinct, so every cursor's route survives the merge; it
     is the empirically-0-false-reject reference. *)
  Definition reachable_slotedge (g : Gss) (start node : nat) : Prop :=
    exists p, path_valid g start p = true /\ path_end start p = node.

  (* fan-out ⊇ SlotEdge : fan-out reaches everything a recorded route reaches. *)
  Theorem fanout_covers_slotedge : forall g start node,
    reachable_slotedge g start node ->
    exists fuel, reachable_in fuel g start node.
  Proof.
    intros g start node [p [Hv He]].
    exists (length p). rewrite <- He. apply path_reaches_fanout. exact Hv.
  Qed.

  (* THE RECOGNIZER SOUNDNESS COROLLARY. If fan-out cannot reach `node` at any
     fuel (the recognizer reports Unreachable), then no recorded SlotEdge route
     reaches it either. With the empirically-validated `SlotEdge ⊇ true-parser`
     leg (Stage-0 G0-SOUND: SlotEdge 0 false-rejects), an Unreachable verdict
     means the span is genuinely non-parseable — so the recognizer's fast-reject
     is sound and NEVER false-rejects a parseable span. *)
  Corollary recognizer_reject_sound : forall g start node,
    (forall fuel, ~ reachable_in fuel g start node) ->
    ~ reachable_slotedge g start node.
  Proof.
    intros g start node Hun Hse.
    apply fanout_covers_slotedge in Hse.
    destruct Hse as [fuel Hf].
    exact (Hun fuel Hf).
  Qed.

  (* Concrete witness of the recovery. Keep-one-Slot MERGE discards a cursor,
     but its pop-target edge remains node-scoped on the shared node. Node 0 has
     TWO accumulated out-edges (to 1 and to 2) from two merged cursors. A single
     recorded stack that kept only 0->1 (the survivor) would miss node 2 — the
     keep-one Slot false-reject. Fan-out reaches BOTH: this is exactly the
     trailing-comma pop target (@Nil!(0,)) that keep-one Slot drops and fan-out
     recovers (Stage-0 gate: Slot 3 false-rejects, SlotFanout 0). *)
  Example fanout_recovers_dropped_pop_target :
    let g := [ {| src := 0; tgt := 1 |} ; {| src := 0; tgt := 2 |} ] in
    reachable_in 1 g 0 1 /\ reachable_in 1 g 0 2.
  Proof.
    split.
    - right. exists 1. split; [ simpl; left; reflexivity | left; reflexivity ].
    - right. exists 2. split; [ simpl; right; left; reflexivity | left; reflexivity ].
  Qed.

  (* And the SlotEdge route to the dropped target IS a valid recorded path, so
     `recognizer_reject_sound` would forbid rejecting a start from which it is
     reachable — the soundness bite. *)
  Example dropped_target_is_slotedge_reachable :
    let g := [ {| src := 0; tgt := 1 |} ; {| src := 0; tgt := 2 |} ] in
    reachable_slotedge g 0 2.
  Proof.
    exists [ {| src := 0; tgt := 2 |} ]. split.
    - simpl. reflexivity.
    - simpl. reflexivity.
  Qed.

End PrefixCohortIsolationGeneral.
