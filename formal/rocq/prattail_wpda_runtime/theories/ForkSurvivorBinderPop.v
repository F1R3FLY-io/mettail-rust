(*
 * ForkSurvivorBinderPop: FV-FIRST spec for the UNIFIED Fix A — routing a
 * Fork's cross-cat PROJECTION branch through the SINGLETON (uncached, non-cohort)
 * push so its delegate reconciles EXACTLY as the working Bag/List/Set singleton
 * projections do, bypassing the cohort register/park/broadcast that causes BOTH
 *   ROOT C (the Map `{` projection's binder-frame pop is broadcast the WORKER's
 *           tail and dropped — `for(@{1:2}<-c){Nil}` fails while `*@{1:2}` and
 *           the singleton Bag/List/Set binder pops succeed), and
 *   ROOT B (the Pathmap `{|` `CrossCatDelegate{14}` dies in the cohort
 *           register/snapshot layer — the SnapshotDuplicate storm — never
 *           reaching the cat-14 collection arm).
 *
 * ROOT CAUSE (re-diagnosed; same subsystem for B and C): a Fork-emitted
 * cross-cat projection branch is allocated via `allocate_fork_push_child`
 * (wpda_walker.rs:~22036), which REGISTERS the delegate in the dispatch cohort
 * (park / broadcast-revive / per-key snapshot cap). The revive BROADCASTS the
 * worker's post-pop tail to every parked member; a binder-frame survivor whose
 * OWN return frame differs from the worker's is reconciled against the WRONG
 * frame and dropped (ROOT C), and the per-key snapshot churn overflows the cap
 * (ROOT B). The SINGLETON projection (prefix.rs:1480 `WpdaStepAction::Push`)
 * instead uses `allocate_uncached_push_child` (wpda_walker.rs:~22288): no
 * register, no park, no broadcast — each delegate resolves inline against its
 * OWN frame. Bag/List/Set projections take the singleton path and reconcile
 * fine; Map (in ROOT A's collision Fork) and Pathmap (in the lex Fork) take the
 * cohort path and break. Fix A: a new `ForkActionKind::PushProjectionInline`
 * routes Fork-projection branches through the singleton uncached push.
 *
 * THE MODEL mirrors CrossCatLhsParking.v's ParkingVsPerCursor: a Section
 * `parse` with a pointwise PURITY premise (`parse_pure` — the source sub-parse
 * is a function of the (pos, source) dispatch key alone; engine.step reads only
 * (state, gss-top, pos, tokens), engine_impl.rs:213-221). A Fork-projection
 * SURVIVOR carries its OWN return frame; the SOUND pop reconciles against that
 * frame (the inline/singleton semantics), the cohort BROADCAST reconciles
 * against the worker's frame (the bug).
 *
 * THEOREMS (all admission-free; each audited by `Print Assumptions`, which must
 * report "Closed under the global context"):
 *   fork_survivor_pop_eq_singleton_pop  — CORE: the Fix-A inline pop of a
 *                                         Fork-projection survivor equals the
 *                                         per-cursor SINGLETON pop (given parse
 *                                         purity) — Fix A makes Fork-projections
 *                                         behave exactly like the working
 *                                         singleton projections.
 *   binder_pop_no_loss                  — every singleton (own-frame) config is
 *                                         produced by the inline fix (no valid
 *                                         binder-frame parse is lost).
 *   binder_pop_no_spurious              — the inline fix produces ONLY singleton
 *                                         configs (no fabricated parse).
 *   frontier_delta_le_one               — the inline push of one projection
 *                                         survivor adds at most one cursor (the
 *                                         uncached delegate child — no cohort
 *                                         fan-out / broadcast multiplication).
 *   current_broadcast_drops_matching_rule
 *                                       — BUG WITNESS (non-vacuity): the cohort
 *                                         broadcast reconciles a binder-frame
 *                                         survivor against the WORKER's frame, so
 *                                         its config differs from the sound
 *                                         own-frame config — the valid parse is
 *                                         dropped. (Mirrors CrossCatLhsParking
 *                                         worker_snapshot_forces_refused_reentry.)
 *   terminal_frame_broadcast_sound      — when every member's frame EQUALS the
 *                                         worker's (a terminal / single-member /
 *                                         same-tail chain — `*@{1:2}`, the
 *                                         passing corpus) the broadcast already
 *                                         equals the singleton pop: those parses
 *                                         are UNTOUCHED by Fix A.
 *   fixed_preserves_result_multiset     — Fix A preserves the per-cursor result
 *                                         multiset exactly (count_occ equality).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

(* A Fork-projection survivor: its identity and its OWN return frame. The frame
   distinguishes the enclosing context the delegate pops back into — a binder
   frame (`InputBindQuoted "@" pat "<-" n`, ROOT C) vs a non-binder frame
   (NQuote/PDrop/root). The cohort revive must reconcile against the member's OWN
   frame; broadcasting the worker's frame is the bug. *)
Record Member : Type := MkMember {
  member_id : nat;
  member_frame : nat
}.

(* A source sub-parse result (one SPPF body of the delegated source category):
   its identity and the position the parse consumed to. *)
Record Body : Type := MkBody {
  body_id : nat;
  body_hi : nat
}.

(* The post-pop CONFIGURATION a survivor ends in for one body — the observable
   the fix must preserve: which member, which body, the resume position, and the
   FRAME the pop reconciled against. A pop is SOUND iff `cfg_frame` is the
   member's OWN frame (the delegate's wrapped result attaches to the member's own
   binder/quote continuation). *)
Record Config : Type := MkConfig {
  cfg_member : nat;
  cfg_body : nat;
  cfg_pos : nat;
  cfg_frame : nat
}.

(* The SINGLETON / inline pop: reconcile against the member's OWN frame
   (allocate_uncached_push_child — the working Bag/List/Set path). *)
Definition singleton_pop_config (m : Member) (b : Body) : Config :=
  MkConfig (member_id m) (body_id b) (body_hi b) (member_frame m).

(* The cohort BROADCAST pop: reconcile against the WORKER's frame
   (allocate_fork_push_child → register → broadcast-revive). Only the member /
   body identities vary; the FRAME is the worker's (the bug). *)
Definition broadcast_pop_config (worker m : Member) (b : Body) : Config :=
  MkConfig (member_id m) (body_id b) (body_hi b) (member_frame worker).

Section ForkSurvivorBinderPop.

  (* Each survivor's own source sub-parse run. *)
  Variable parse : Member -> list Body.
  (* Purity: the sub-parse depends only on the (pos, source) dispatch key, never
     on the member's return frame (engine.step reads only (state, gss-top, pos,
     tokens)). Section premise discharged into the theorems' hypotheses. *)
  Hypothesis parse_pure : forall m m', parse m = parse m'.

  (* PER-CURSOR / SINGLETON flow: each survivor parses for itself and pops with
     its OWN frame (the inline semantics — also what Bag/List/Set singletons do). *)
  Definition inline_flow (members : list Member) : list Config :=
    flat_map (fun m => map (singleton_pop_config m) (parse m)) members.

  (* FIX-A flow: the worker parses once (shared body list); every survivor is
     revived with its OWN frame over those bodies (the inline uncached push,
     bypassing the cohort). *)
  Definition inline_fix_flow (worker : Member) (members : list Member)
    : list Config :=
    flat_map (fun m => map (singleton_pop_config m) (parse worker)) members.

  (* CURRENT (buggy) cohort BROADCAST flow: the worker parses once; every parked
     survivor is revived with the WORKER's frame. *)
  Definition broadcast_flow (worker : Member) (members : list Member)
    : list Config :=
    flat_map (fun m => map (broadcast_pop_config worker m) (parse worker))
             members.

  (* ══════════════ fork_survivor_pop_eq_singleton_pop ══════════════
     CORE: Fix A's inline pop reproduces the per-cursor singleton pop EXACTLY. *)
  Theorem fork_survivor_pop_eq_singleton_pop :
    forall worker members,
      inline_fix_flow worker members = inline_flow members.
  Proof.
    intros worker members. unfold inline_fix_flow, inline_flow.
    induction members as [| m rest IH]; simpl.
    - reflexivity.
    - rewrite IH. rewrite (parse_pure worker m). reflexivity.
  Qed.

  (* ══════════════ binder_pop_no_loss ══════════════
     No valid binder-frame parse is lost: every per-cursor (own-frame) config is
     produced by the Fix-A inline flow. *)
  Theorem binder_pop_no_loss :
    forall worker members c,
      In c (inline_flow members) -> In c (inline_fix_flow worker members).
  Proof.
    intros worker members c Hin.
    rewrite fork_survivor_pop_eq_singleton_pop. exact Hin.
  Qed.

  (* ══════════════ binder_pop_no_spurious ══════════════
     No fabricated parse: the Fix-A inline flow produces ONLY per-cursor configs. *)
  Theorem binder_pop_no_spurious :
    forall worker members c,
      In c (inline_fix_flow worker members) -> In c (inline_flow members).
  Proof.
    intros worker members c Hin.
    rewrite fork_survivor_pop_eq_singleton_pop in Hin. exact Hin.
  Qed.

  (* ══════════════ frontier_delta_le_one ══════════════
     The inline push of ONE projection survivor over a single-body source adds
     exactly one cursor — no cohort fan-out / broadcast multiplication. *)
  Theorem frontier_delta_le_one :
    forall worker m b,
      parse worker = [b] ->
      length (inline_fix_flow worker [m]) <= 1.
  Proof.
    intros worker m b Hp. unfold inline_fix_flow. simpl.
    rewrite Hp. simpl. apply Nat.le_refl.
  Qed.

  (* ══════════════ current_broadcast_drops_matching_rule ══════════════
     BUG WITNESS (non-vacuity): a binder-frame survivor (frame 1) under the
     worker (frame 0). The cohort broadcast reconciles it against the worker's
     frame (0), producing a config that DIFFERS from the sound own-frame (1)
     config — the valid binder-frame parse is dropped. The only premise is that
     the source category parses at all (≥ 1 body). Mirrors CrossCatLhsParking
     worker_snapshot_forces_refused_reentry. *)
  Definition demo_worker : Member := MkMember 0 0.          (* non-binder frame 0 *)
  Definition demo_binder_member : Member := MkMember 2 1.   (* binder frame 1     *)

  Theorem current_broadcast_drops_matching_rule :
    parse demo_worker <> [] ->
    broadcast_flow demo_worker [demo_binder_member]
      <> inline_flow [demo_binder_member].
  Proof.
    intros Hne Heq.
    destruct (parse demo_worker) as [| b bs] eqn:Hparse.
    - exact (Hne eq_refl).
    - unfold broadcast_flow, inline_flow in Heq. simpl in Heq.
      rewrite (parse_pure demo_binder_member demo_worker) in Heq.
      rewrite Hparse in Heq. simpl in Heq.
      (* Head configs: cfg_frame = 0 (worker, broadcast) vs 1 (binder member,
         own-frame) — discriminable. *)
      discriminate Heq.
  Qed.

  (* ══════════════ terminal_frame_broadcast_sound ══════════════
     When every member's frame EQUALS the worker's (a terminal / single-member /
     same-tail chain — `*@{1:2}`, single-member delegates, the entire passing
     corpus), the broadcast ALREADY equals the singleton pop: Fix A leaves these
     parses byte-identical. Mirrors CrossCatLhsParking parking_identity_when_singleton. *)
  Theorem terminal_frame_broadcast_sound :
    forall worker members,
      (forall m, In m members -> member_frame m = member_frame worker) ->
      broadcast_flow worker members = inline_flow members.
  Proof.
    intros worker members. unfold broadcast_flow, inline_flow.
    induction members as [| m rest IH]; intro Hsame; simpl.
    - reflexivity.
    - assert (Hm : member_frame m = member_frame worker).
      { apply Hsame. left. reflexivity. }
      f_equal.
      + (* head: rewrite parse_pure in THIS subgoal only, then map_ext. *)
        rewrite (parse_pure worker m). apply map_ext. intro b.
        unfold broadcast_pop_config, singleton_pop_config. rewrite Hm. reflexivity.
      + apply IH. intros x Hx. apply Hsame. right. exact Hx.
  Qed.

  (* Single-member specialisation (the `*@{1:2}` / one-delegate shape): broadcast
     IS the inline pop, unconditionally — one member is trivially same-frame as
     itself when it is the worker. *)
  Theorem singleton_member_broadcast_sound :
    forall m, broadcast_flow m [m] = inline_flow [m].
  Proof.
    intro m. apply terminal_frame_broadcast_sound.
    intros x Hx. simpl in Hx. destruct Hx as [<- | []]. reflexivity.
  Qed.

  (* ══════════════ fixed_preserves_result_multiset ══════════════
     Fix A preserves the per-cursor result MULTISET exactly: for every config,
     the inline-fix occurrence count equals the per-cursor count — no body of any
     survivor is lost or duplicated. *)
  Theorem fixed_preserves_result_multiset :
    forall worker members
           (cfg_eq_dec : forall a b : Config, {a = b} + {a <> b})
           (c : Config),
      count_occ cfg_eq_dec (inline_fix_flow worker members) c
        = count_occ cfg_eq_dec (inline_flow members) c.
  Proof.
    intros worker members cfg_eq_dec c.
    rewrite fork_survivor_pop_eq_singleton_pop. reflexivity.
  Qed.

  (* ═══════════════════════════════════════════════════════════════════
     CONTINUATION EXTENSION (the @{map} binder-overflow fix — inline_pop)

     The reconciliation above settles WHICH FRAME a survivor attaches to.
     The remaining failure mode — the one that overflows
     `for(@{1:2} <- c){z}` — is the COHORT RESOLVE fired at the projection
     pop while a CONTINUATION (the `{z}` body / parked `<-` join siblings)
     is still live. Each cohort resolve of an already-Resolved entry yields
     a no-op `SnapshotDuplicate` that does NOT consume the per-key snapshot
     cap, yet broadcast-revives every parked sibling → re-dispatch → re-push
     → re-pop → re-resolve: a non-terminating feedback loop (403,441
     SnapshotDuplicate vs 787 FirstResolve, trace-pinned on zz_complex_probe).

     Fix: the inline `{`-fork projection edge is tagged `inline_pop`; at pop
     it reconciles SOLELY in its OWN RuleAt frame
     (crosscat_projection_return_for_actual_body) and SKIPS the cohort
     resolve — so a live continuation is advanced exactly once, with zero
     cohort fan-out. The cohort (broadcast) path substitutes the WORKER's
     frame; when the worker's frame carries no continuation but the member's
     does, the member's continuation is refused (dropped) AND each re-resolve
     re-broadcasts (the loop).

     `continues f` = frame `f` carries a live post-pop RuleAt continuation
     (a binder body `{z}` / a parked join sibling). The config's surviving
     continuation is `continues (cfg_frame c)` — inline keeps the member's
     own frame (continuation preserved); broadcast keeps the worker's frame
     (the member's continuation refused). *)
  Variable continues : nat -> bool.

  (* The continuation a config still carries after the pop — a function of
     the frame it reconciled against. *)
  Definition cfg_continuation (c : Config) : bool := continues (cfg_frame c).

  (* ════ fork_survivor_reconciles_in_ruleat_frame_with_continuation ════
     The inline pop admits EVERY survivor's OWN-frame continuation: each
     config the inline fix produces for member `m` carries `m`'s own
     continuation (its RuleAt frame), never the worker's — the SOLE
     reconcile site is m's own frame. *)
  Theorem fork_survivor_reconciles_in_ruleat_frame_with_continuation :
    forall worker m c,
      In c (inline_fix_flow worker [m]) ->
      cfg_continuation c = continues (member_frame m).
  Proof.
    intros worker m c Hin. unfold inline_fix_flow in Hin. simpl in Hin.
    rewrite app_nil_r in Hin.
    apply in_map_iff in Hin. destruct Hin as [b [Hb _]].
    subst c. unfold cfg_continuation, singleton_pop_config. simpl. reflexivity.
  Qed.

  (* ════ continuation_frontier_delta_le_one ════
     With a continuation live, the inline pop STILL adds at most one cursor
     per body — the cohort resolve (and its broadcast-revive fan-out) is
     skipped entirely; the bound holds irrespective of the frame's
     continuation bit. *)
  Theorem continuation_frontier_delta_le_one :
    forall worker m b,
      parse worker = [b] ->
      length (inline_fix_flow worker [m]) <= 1.
  Proof.
    intros worker m b Hp. exact (frontier_delta_le_one worker m b Hp).
  Qed.

  (* ════ inline_continuation_no_loss / no_spurious ════
     Lift no-loss and no-spurious across the continuation observable: the
     inline-fix and per-cursor flows agree continuation-for-continuation
     (immediate from the config-level equality). *)
  Theorem inline_continuation_no_loss :
    forall worker members,
      map cfg_continuation (inline_flow members)
        = map cfg_continuation (inline_fix_flow worker members).
  Proof.
    intros worker members.
    rewrite fork_survivor_pop_eq_singleton_pop. reflexivity.
  Qed.

  Theorem inline_continuation_no_spurious :
    forall worker members,
      map cfg_continuation (inline_fix_flow worker members)
        = map cfg_continuation (inline_flow members).
  Proof.
    intros worker members.
    rewrite fork_survivor_pop_eq_singleton_pop. reflexivity.
  Qed.

  (* ════ broadcast_drops_continuation_survivor ════
     BUG WITNESS (non-vacuity) for the continuation dimension: a binder
     member whose frame CARRIES a continuation (continues (frame)=true),
     parked under a worker whose frame carries NONE (continues=false). The
     cohort broadcast reconciles the member against the worker's frame, so
     every resulting config reports NO continuation — the binder body `{z}`
     is dropped — whereas the sound inline pop keeps it. The two flows
     therefore disagree on continuation for the head body. Premise: the
     source parses (≥1 body) and the frames' continuation bits differ as
     described (the `for(@{1:2}<-c){z}` shape: binder frame continues, the
     `*`/root worker frame does not). Mirrors current_broadcast_drops_matching_rule
     lifted from frame-identity to continuation-survival. *)
  Theorem broadcast_drops_continuation_survivor :
    forall worker m,
      parse worker <> [] ->
      continues (member_frame m) = true ->
      continues (member_frame worker) = false ->
      map cfg_continuation (broadcast_flow worker [m])
        <> map cfg_continuation (inline_flow [m]).
  Proof.
    intros worker m Hne Hm Hw Heq.
    destruct (parse worker) as [| b bs] eqn:Hparse.
    - exact (Hne eq_refl).
    - unfold broadcast_flow, inline_flow in Heq. simpl in Heq.
      rewrite (parse_pure m worker) in Heq.
      rewrite Hparse in Heq. simpl in Heq.
      unfold cfg_continuation, broadcast_pop_config, singleton_pop_config in Heq.
      simpl in Heq.
      rewrite Hm, Hw in Heq.
      discriminate Heq.
  Qed.

  (* ═══════════════════════════════════════════════════════════════════
     REALIZE-ANCHOR EXTENSION (the SURVIVING @{map} defect — the CrossCatLhs
     binder-cohort consumer, 2026-06-30, deep-dive+plan-agent converged)

     The projection-cohort instance of ROOT C is already fixed (the landed
     "Fix A": the `{`-collision projection branch takes the singleton uncached
     push, so it never registers in the projection cohort). The SURVIVING
     instance of the SAME principle lives in the UPSTREAM CrossCatLhs(Name)
     binder cohort: when its drain consumes the bracket body, the owning
     prefix/binder rule (NQuoteShort `@ p`) is realized on a lineage whose
     reconciliation frame is the cohort WORKER's (a trigger-LESS source parse)
     rather than the binder MEMBER's OWN frame — so the interned Symbol's
     left anchor `lo` is the body's position (degenerate) instead of the
     member's `@`-trigger position. `Name[8,8]` vs `Name[2,8]`.

     `anchor_lo f` = the realize `lo` a config reconciled against frame `f`
     receives — the member's own frame carries its `@`-trigger anchor; the
     worker's frame carries only the body anchor. The fix (reconcile every
     consumed member against its OWN frame = `singleton_pop_config`) makes
     the realize observe `anchor_lo (member_frame m)`; the bug
     (`broadcast_pop_config`, worker frame) observes
     `anchor_lo (member_frame worker)`. This is the EXACT realize-observable
     instantiation of `current_broadcast_drops_matching_rule` (frame identity)
     lifted to the span anchor. *)
  Variable anchor_lo : nat -> nat.

  (* The realize left-anchor a config receives — a function of the frame it
     reconciled against. *)
  Definition cfg_lo (c : Config) : nat := anchor_lo (cfg_frame c).

  (* ════ crosscat_consumer_realize_eq_singleton ════
     The own-frame consumer realize anchors EVERY consumed member's owning-rule
     Symbol at the MEMBER's own anchor (its `@`-trigger pos), never the
     worker's — the SOLE reconcile site is the member's own frame. *)
  Theorem crosscat_consumer_realize_eq_singleton :
    forall worker m c,
      In c (inline_fix_flow worker [m]) ->
      cfg_lo c = anchor_lo (member_frame m).
  Proof.
    intros worker m c Hin. unfold inline_fix_flow in Hin. simpl in Hin.
    rewrite app_nil_r in Hin.
    apply in_map_iff in Hin. destruct Hin as [b [Hb _]].
    subst c. unfold cfg_lo, singleton_pop_config. simpl. reflexivity.
  Qed.

  (* ════ realize_anchor_no_loss / no_spurious ════
     The own-frame consumer realize and the per-cursor flow agree
     anchor-for-anchor (immediate from the config-level equality). *)
  Theorem realize_anchor_no_loss :
    forall worker members,
      map cfg_lo (inline_flow members)
        = map cfg_lo (inline_fix_flow worker members).
  Proof.
    intros worker members.
    rewrite fork_survivor_pop_eq_singleton_pop. reflexivity.
  Qed.

  Theorem realize_anchor_no_spurious :
    forall worker members,
      map cfg_lo (inline_fix_flow worker members)
        = map cfg_lo (inline_flow members).
  Proof.
    intros worker members.
    rewrite fork_survivor_pop_eq_singleton_pop. reflexivity.
  Qed.

  (* ════ crosscat_consumer_broadcast_drops_anchor ════
     BUG WITNESS (non-vacuity) for the realize-anchor: a binder member whose
     OWN frame anchors at a DIFFERENT lo than the worker's frame (the
     `@{1:2}<-c` shape: member anchor = `@`-pos, worker anchor = degenerate
     body pos). The worker-frame (broadcast) realize anchors at the worker's
     lo, which differs from the sound member-frame (own) lo — the `@`-trigger
     anchor is dropped. Premise: the source parses (≥1 body) and the two
     frames' anchors differ. Mirrors broadcast_drops_continuation_survivor,
     lifted from the continuation bit to the span anchor. *)
  Theorem crosscat_consumer_broadcast_drops_anchor :
    forall worker m,
      parse worker <> [] ->
      anchor_lo (member_frame m) <> anchor_lo (member_frame worker) ->
      map cfg_lo (broadcast_flow worker [m])
        <> map cfg_lo (inline_flow [m]).
  Proof.
    intros worker m Hne Hdiff Heq.
    destruct (parse worker) as [| b bs] eqn:Hparse.
    - exact (Hne eq_refl).
    - unfold broadcast_flow, inline_flow in Heq. simpl in Heq.
      rewrite (parse_pure m worker) in Heq.
      rewrite Hparse in Heq. simpl in Heq.
      unfold cfg_lo, broadcast_pop_config, singleton_pop_config in Heq.
      simpl in Heq.
      injection Heq as Hhead _.
      apply Hdiff. symmetry. exact Hhead.
  Qed.

  (* ════ crosscat_consumer_same_frame_anchor_sound ════
     When every member's frame EQUALS the worker's (the `*@{1:2}` / non-
     colliding singleton path, where the `@`-cursor itself realizes), the
     worker-frame realize ALREADY anchors at the member's own lo — those
     parses are byte-identical (untouched by the fix). Specialization of
     terminal_frame_broadcast_sound to the anchor observable. *)
  Theorem crosscat_consumer_same_frame_anchor_sound :
    forall worker members,
      (forall m, In m members -> member_frame m = member_frame worker) ->
      map cfg_lo (broadcast_flow worker members)
        = map cfg_lo (inline_flow members).
  Proof.
    intros worker members Hsame.
    rewrite (terminal_frame_broadcast_sound worker members Hsame).
    reflexivity.
  Qed.

End ForkSurvivorBinderPop.

(* ═════════════════ Assumption audit — must all print
   "Closed under the global context" ═════════════════ *)
Print Assumptions fork_survivor_pop_eq_singleton_pop.
Print Assumptions binder_pop_no_loss.
Print Assumptions binder_pop_no_spurious.
Print Assumptions frontier_delta_le_one.
Print Assumptions current_broadcast_drops_matching_rule.
Print Assumptions terminal_frame_broadcast_sound.
Print Assumptions singleton_member_broadcast_sound.
Print Assumptions fixed_preserves_result_multiset.
Print Assumptions fork_survivor_reconciles_in_ruleat_frame_with_continuation.
Print Assumptions continuation_frontier_delta_le_one.
Print Assumptions inline_continuation_no_loss.
Print Assumptions inline_continuation_no_spurious.
Print Assumptions broadcast_drops_continuation_survivor.
Print Assumptions crosscat_consumer_realize_eq_singleton.
Print Assumptions realize_anchor_no_loss.
Print Assumptions realize_anchor_no_spurious.
Print Assumptions crosscat_consumer_broadcast_drops_anchor.
Print Assumptions crosscat_consumer_same_frame_anchor_sound.
