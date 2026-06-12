(*
 * CrossCatLhsParking: the AMENDED-P1 v2 spec (docs/design/evidence-
 * pruning/02-staged-implementation-plan.md §P1 amendment block,
 * 2026-06-11, user-approved; red-team ledger Round 5) — sharing the
 * CrossCatLhs delegate sub-parse by cohort-style PARKING is sound iff
 * the revive RE-DERIVES each member's post-pop tail from the MEMBER's
 * OWN predecessor frame; broadcasting the WORKER's tail is unsound
 * (the v1 design's mistake, fenced here as a negative theorem); and
 * parked members REQUIRE an EOI orphan re-drive or alternatives are
 * lost that the per-cursor flow keeps.
 *
 * Code grounding (wpda_walker.rs @ 477aef5c):
 *   - effective_new_state from the popped frame's PREDECESSOR kind
 *     (:16152-16184 — CategoryEntry→InfixLoop, GroupingMarker→
 *     Unwinding, NONE→InfixLoop, other→Unwinding);
 *   - the reentry guard (:16189-16194) requires pred ≠ NONE (the
 *     popped CrossCatLhs frame itself is always a CategoryEntry, and
 *     the state test is total over effective_new_state's codomain, so
 *     pred-presence is the live conjunct);
 *   - the source sub-parse is a pure function of (pos, source): the
 *     engine step reads only (state, gss-top, pos, tokens)
 *     (engine_impl.rs:197-208; the freshly pushed category_entry top +
 *     PrefixDispatch{pos, cur_bp:0} are DispatchKey-determined) —
 *     modeled as a parse function with a pointwise purity premise;
 *   - the measured duplicates are redundant-VIABLE cursors (ledger
 *     §P1 Step-0: 3504 spawns / 3500 dup on idx 4), so the sharing
 *     quotient must preserve the full member × body result multiset.
 *
 * THIS FILE's obligations (the amended-P1 v2 M-commit):
 *   T1 member_tail_depends_on_member — two members with different
 *      predecessors take DIFFERENT post-pop tails (non-vacuous basis
 *      for everything below; R5-1's root fact);
 *   T2 parking_v2_eq_percursor — parking with the member-tail revive
 *      reproduces the per-cursor configuration list EXACTLY (given
 *      sub-parse purity) — the broadcast-soundness crux;
 *   T3 worker_snapshot_broadcast_unsound — the v1 fence: a worker-
 *      snapshot revive yields a WRONG configuration for some member
 *      (concrete witness; both the state axis and the reentry axis);
 *   T4 parking_identity_when_singleton — one member ⇒ parking is the
 *      identity (the share_iff_duplicate analogue grounded in THIS
 *      model, mirroring EvidenceGatedDelegates.T5b);
 *   T5 parking_preserves_result_multiset — ambiguous sources (many
 *      bodies) lose nothing: count_occ equality per configuration;
 *   T6 orphan_loss_without_eoi_drain — a worker that never pops
 *      (source consumes to EOI) + NO orphan re-drive ⇒ parked members'
 *      EOI presences are LOST (strict inclusion witness), while the
 *      per-cursor flow keeps every member in the frontier;
 *   T7 orphan_drain_restores_eoi_presence — WITH the re-drive the
 *      EOI presence sets coincide (turns R5-6 into a requirement);
 *   T8 wrap_partition_refines_sharing — adding the host (wrap)
 *      discriminator to the sharing key only REFINES the groups:
 *      cross-host members never share (the M4 tombstone direction)
 *      and refinement can only shrink groups (over-discrimination is
 *      the safe direction).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import Permutation.
Import ListNotations.

(* ════════════════════════════════════════════════════════════════════
   Part 1 — the member tail (the post-pop continuation entry), as a
   function of the MEMBER's predecessor frame kind.
   ════════════════════════════════════════════════════════════════════ *)

(* The popped CrossCatLhs frame's PREDECESSOR symbol kind — the axis
   wpda_walker.rs:16152-16184 branches on. *)
Inductive PredKind : Type :=
  | PredCategoryEntry
  | PredGroupingMarker
  | PredNone
  | PredOther.

Definition predkind_eqb (a b : PredKind) : bool :=
  match a, b with
  | PredCategoryEntry, PredCategoryEntry => true
  | PredGroupingMarker, PredGroupingMarker => true
  | PredNone, PredNone => true
  | PredOther, PredOther => true
  | _, _ => false
  end.

(* The post-pop state (:16152-16184). *)
Inductive TailState : Type :=
  | TInfixLoop
  | TUnwinding.

Definition effective_state (p : PredKind) : TailState :=
  match p with
  | PredCategoryEntry => TInfixLoop
  | PredGroupingMarker => TUnwinding
  | PredNone => TInfixLoop
  | PredOther => TUnwinding
  end.

(* The reentry guard (:16189-16194): the popped CrossCatLhs frame is
   always a CategoryEntry and the state test is total over
   effective_state's codomain, so predecessor-presence is the live
   conjunct. *)
Definition reentry_fires (p : PredKind) : bool :=
  match p with
  | PredNone => false
  | _ => true
  end.

(* A parked member: its identity and its OWN predecessor kind (the
   return frame the cohort preserves). *)
Record Member : Type := MkMember {
  member_id : nat;
  member_pred : PredKind
}.

(* A source sub-parse result (one SPPF body): its identity and the
   position the parse consumed to. *)
Record Body : Type := MkBody {
  body_id : nat;
  body_hi : nat
}.

(* The post-pop CONFIGURATION a member ends in for one body — the
   observable the sharing quotient must preserve: which member, which
   body, the resume position, the tail state, and whether the reentry
   fired. *)
Record Config : Type := MkConfig {
  cfg_member : nat;
  cfg_body : nat;
  cfg_pos : nat;
  cfg_state : TailState;
  cfg_reentry : bool
}.

(* The PER-CURSOR tail: the member's own predecessor decides. *)
Definition member_tail_config (m : Member) (b : Body) : Config :=
  MkConfig (member_id m) (body_id b) (body_hi b)
           (effective_state (member_pred m))
           (reentry_fires (member_pred m)).

(* T1 — the tail genuinely depends on the member: two members with
   CategoryEntry vs GroupingMarker predecessors take different states;
   CategoryEntry vs NONE differ on the reentry axis. The non-vacuity
   basis: a "tail" cannot be a per-key constant. *)
Theorem member_tail_depends_on_member :
  exists p1 p2,
    effective_state p1 <> effective_state p2 /\
    exists p3 p4,
      reentry_fires p3 <> reentry_fires p4.
Proof.
  exists PredCategoryEntry, PredGroupingMarker. split.
  - simpl. discriminate.
  - exists PredCategoryEntry, PredNone. simpl. discriminate.
Qed.

(* ════════════════════════════════════════════════════════════════════
   Part 2 — parking vs per-cursor (T2-T5).

   The per-cursor flow: EVERY member re-runs the source sub-parse for
   itself, then takes its own tail per body.

   The parking flow: the WORKER runs the sub-parse ONCE; each parked
   member is revived per body. v2 revives with the MEMBER-tail; v1
   revived with the WORKER-tail (the refuted broadcast).

   Purity premise: the sub-parse is a function of the dispatch key
   alone — every member's own run returns the same body list. It is a
   Section premise discharged into the final theorems' hypotheses
   (engine-step purity is the code-grounded justification; see header).
   ════════════════════════════════════════════════════════════════════ *)

Section ParkingVsPerCursor.

  (* Each member's own source sub-parse run. *)
  Variable parse : Member -> list Body.
  (* Purity: the sub-parse depends only on the (pos, source) dispatch
     key, never on the member's return frame. *)
  Hypothesis parse_pure : forall m m', parse m = parse m'.

  (* The per-cursor flow: each member parses for itself. *)
  Definition percursor_flow (members : list Member) : list Config :=
    flat_map (fun m => map (member_tail_config m) (parse m)) members.

  (* The v2 parking flow: the worker parses once; every member is
     revived with its OWN tail over the worker's bodies. *)
  Definition parking_v2_flow (worker : Member) (members : list Member)
    : list Config :=
    flat_map (fun m => map (member_tail_config m) (parse worker)) members.

  (* The v1 parking flow (REFUTED design): every member is revived
     with the WORKER's tail — only the member/body identities vary. *)
  Definition v1_broadcast_config (worker m : Member) (b : Body) : Config :=
    MkConfig (member_id m) (body_id b) (body_hi b)
             (effective_state (member_pred worker))
             (reentry_fires (member_pred worker)).

  Definition parking_v1_flow (worker : Member) (members : list Member)
    : list Config :=
    flat_map (fun m => map (v1_broadcast_config worker m) (parse worker))
             members.

  (* T2 — broadcast soundness for the v2 (member-tail) revive: parking
     reproduces the per-cursor configuration list EXACTLY. *)
  Theorem parking_v2_eq_percursor :
    forall worker members,
      parking_v2_flow worker members = percursor_flow members.
  Proof.
    intros worker members.
    unfold parking_v2_flow, percursor_flow.
    induction members as [| m rest IH]; simpl.
    - reflexivity.
    - rewrite IH. rewrite (parse_pure worker m). reflexivity.
  Qed.

  (* T4 — singleton identity: with one member (the worker itself),
     parking IS the per-cursor flow. The share_iff_duplicate analogue
     grounded in this model. *)
  Theorem parking_identity_when_singleton :
    forall m, parking_v2_flow m [m] = percursor_flow [m].
  Proof.
    intro m. apply parking_v2_eq_percursor.
  Qed.

  (* T5 — multiset preservation under source ambiguity: for EVERY
     configuration, the v2 parking flow carries exactly the per-cursor
     occurrence count (no body of any member is lost or duplicated,
     however many bodies the source yields). Immediate from T2, stated
     as the count_occ form the no-loss mandate is phrased in. *)
  Theorem parking_preserves_result_multiset :
    forall worker members (cfg_eq_dec : forall a b : Config, {a = b} + {a <> b})
           (c : Config),
      count_occ cfg_eq_dec (parking_v2_flow worker members) c
        = count_occ cfg_eq_dec (percursor_flow members) c.
  Proof.
    intros worker members cfg_eq_dec c.
    rewrite parking_v2_eq_percursor. reflexivity.
  Qed.

  (* T3 — the v1 fence: broadcasting the WORKER's tail produces a
     configuration the per-cursor flow NEVER produces, on both axes:
     (a) the state axis — an InfixLoop-tailed worker forces a
         GroupingMarker-predecessor member (whose own tail is
         Unwinding) into InfixLoop;
     (b) the reentry axis — it forces a reentry on a NONE-predecessor
         member whose own guard refuses it.
     Concrete witnesses (the strongest non-vacuity form): the only
     premise is that the source category parses at all (≥1 body). *)
  Definition demo_worker : Member := MkMember 0 PredCategoryEntry.
  Definition demo_grouping_member : Member := MkMember 1 PredGroupingMarker.
  Definition demo_none_member : Member := MkMember 2 PredNone.

  Theorem worker_snapshot_broadcast_unsound :
    parse demo_worker <> [] ->
    parking_v1_flow demo_worker [demo_grouping_member]
      <> percursor_flow [demo_grouping_member].
  Proof.
    intros Hne Heq.
    destruct (parse demo_worker) as [| b bs] eqn:Hparse.
    - exact (Hne eq_refl).
    - unfold parking_v1_flow, percursor_flow in Heq.
      simpl in Heq.
      rewrite (parse_pure demo_grouping_member demo_worker) in Heq.
      rewrite Hparse in Heq. simpl in Heq.
      (* Head configs: state TInfixLoop (broadcast) vs TUnwinding
         (the member's own tail) — discriminable. *)
      discriminate Heq.
  Qed.

  (* The reentry-axis witness, separately (a NONE-predecessor member:
     its own guard refuses the reentry; the broadcast forces it). *)
  Theorem worker_snapshot_forces_refused_reentry :
    parse demo_worker <> [] ->
    parking_v1_flow demo_worker [demo_none_member]
      <> percursor_flow [demo_none_member].
  Proof.
    intros Hne Heq.
    destruct (parse demo_worker) as [| b bs] eqn:Hparse.
    - exact (Hne eq_refl).
    - unfold parking_v1_flow, percursor_flow in Heq.
      simpl in Heq.
      rewrite (parse_pure demo_none_member demo_worker) in Heq.
      rewrite Hparse in Heq. simpl in Heq.
      (* Head configs: reentry true (broadcast) vs false (the member's
         own refused guard) — discriminable. *)
      discriminate Heq.
  Qed.

End ParkingVsPerCursor.

(* ════════════════════════════════════════════════════════════════════
   Part 3 — EOI orphan parity (T6-T7).

   If the worker's source sub-parse never pops (it consumes to EOI),
   the per-cursor flow still has EVERY member alive in the frontier at
   EOI — each contributes its own presence to acceptance / longest-
   prefix salvage. Parked members are NOT in the frontier; without an
   orphan re-drive they contribute nothing. (R5-6 made a theorem.)
   ════════════════════════════════════════════════════════════════════ *)

Section EoiOrphan.

  (* EOI presence: the member ids alive in the frontier at EOI. *)

  (* Per-cursor: every member is its own cursor — all present. *)
  Definition percursor_eoi_presence (members : list Member) : list nat :=
    map member_id members.

  (* Parked, NO orphan re-drive: only the worker is in the frontier. *)
  Definition parked_eoi_presence_no_drain (worker : Member)
    (_ : list Member) : list nat :=
    [member_id worker].

  (* Parked, WITH the orphan re-drive: every parked member is re-driven
     into the frontier at the drain point. *)
  Definition parked_eoi_presence_with_drain (worker : Member)
    (members : list Member) : list nat :=
    map member_id members.

  (* T6 — loss without the drain: any second member's presence is
     dropped (concrete strict-loss witness: a member whose id differs
     from the worker's is present per-cursor and absent parked). *)
  Theorem orphan_loss_without_eoi_drain :
    forall worker m rest,
      member_id m <> member_id worker ->
      In (member_id m) (percursor_eoi_presence (m :: rest)) /\
      ~ In (member_id m)
          (parked_eoi_presence_no_drain worker (m :: rest)).
  Proof.
    intros worker m rest Hneq. split.
    - simpl. left. reflexivity.
    - simpl. intros [Heq | Hfalse].
      + apply Hneq. symmetry. exact Heq.
      + exact Hfalse.
  Qed.

  (* T7 — the re-drive restores parity exactly. *)
  Theorem orphan_drain_restores_eoi_presence :
    forall worker members,
      parked_eoi_presence_with_drain worker members
        = percursor_eoi_presence members.
  Proof.
    intros. reflexivity.
  Qed.

End EoiOrphan.

(* ════════════════════════════════════════════════════════════════════
   Part 4 — the wrap (host) discriminator only refines (T8).

   Sharing groups keyed (pos, source, host) partition each
   (pos, source) group; members in different host categories NEVER
   share a worker (the M4 tombstone direction), and adding the
   discriminator can only SHRINK groups — over-discrimination merely
   reduces sharing (safe); it never merges what was separate.
   ════════════════════════════════════════════════════════════════════ *)

Section WrapPartition.

  (* A dispatch instance: its (pos, source) key and its host category. *)
  Record Dispatch : Type := MkDispatch {
    d_pos : nat;
    d_source : nat;
    d_host : nat
  }.

  Definition same_pos_source (a b : Dispatch) : bool :=
    (Nat.eqb (d_pos a) (d_pos b)) && (Nat.eqb (d_source a) (d_source b)).

  Definition same_full_key (a b : Dispatch) : bool :=
    same_pos_source a b && Nat.eqb (d_host a) (d_host b).

  (* The sharing group of `a` within a dispatch population. *)
  Definition group_by (keyeq : Dispatch -> Dispatch -> bool)
    (pop : list Dispatch) (a : Dispatch) : list Dispatch :=
    filter (keyeq a) pop.

  (* T8a — refinement: the full-key group is contained in the
     (pos, source) group (adding the host discriminator only shrinks). *)
  Theorem wrap_partition_refines_sharing :
    forall pop a d,
      In d (group_by same_full_key pop a) ->
      In d (group_by same_pos_source pop a).
  Proof.
    intros pop a d Hin.
    unfold group_by in *.
    apply filter_In in Hin. destruct Hin as [Hd Hkey].
    apply filter_In. split; [exact Hd |].
    unfold same_full_key in Hkey.
    apply andb_true_iff in Hkey. destruct Hkey as [Hps _].
    exact Hps.
  Qed.

  (* T8b — cross-host members never share under the full key (the M4
     direction made positive: distinct hosts ⇒ distinct groups). *)
  Theorem cross_host_never_shares :
    forall pop a d,
      d_host a <> d_host d ->
      ~ In d (group_by same_full_key pop a).
  Proof.
    intros pop a d Hneq Hin.
    unfold group_by in Hin.
    apply filter_In in Hin. destruct Hin as [_ Hkey].
    unfold same_full_key in Hkey.
    apply andb_true_iff in Hkey. destruct Hkey as [_ Hhost].
    apply Nat.eqb_eq in Hhost.
    apply Hneq. exact Hhost.
  Qed.

End WrapPartition.

(* ════════════════════════════════════════════════════════════════════
   Closing note: T2/T3 together state the v2 contract precisely — the
   ONLY sound revive recomputes the tail from each member's own
   predecessor (T2 holds definitionally for that revive and T3 shows
   any worker-constant tail is wrong on concrete witnesses); T6/T7
   make the EOI orphan re-drive a REQUIREMENT, not an optimization;
   T8 fixes the key-discrimination direction (refine, never widen).
   The implementation obligations these discharge are recorded as
   R5-1, R5-6, R5-7/M4 in docs/design/evidence-pruning/
   03-red-team-ledger.md Round 5.
   ════════════════════════════════════════════════════════════════════ *)
