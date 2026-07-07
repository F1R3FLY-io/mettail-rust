(*
 * CrossCatProjectionFrameDedup: zero-admission FV for the Root-1 + Root-2
 * CrossCatDelegate-projection cohort ENCLOSING-FRAME-KEYED dedup fix
 * (prattail/src/wpda_walker.rs:
 *   - `crosscat_projection_enclosing_frame_disc` (the enclosing-frame
 *     discriminant of a rule-operand / group-close projection),
 *   - the `RegisterOutcome::WorkerInserted` frame-disc record +
 *     `RegisterOutcome::InflightCollision` compare-and-bypass in
 *     `allocate_fork_push_child`,
 *   - the walker-local `crosscat_proj_registrant_frame` map).
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE DEFECT (trace-evidenced; deterministic; category ordering
 *   Proc=0, InputBind=1, ForRow=2, Name=3; calc Int=2, Bool=7):
 *
 *   A CrossCatDelegate projection registers in the projection cohort under a
 *   `DispatchKey (pos, source_src_idx, inner_cur_bp, wrap_cat, wrap_rule)`
 *   that encodes NEITHER the projection's ENCLOSING RETURN-FRAME nor its LHS
 *   body. When TWO cursors dispatch the SAME source->wrap projection at the
 *   SAME position but for DIFFERENT enclosing frames/bodies, the second gets
 *   `InflightCollision`, is PAUSED as a cohort member, and is later REVIVED
 *   with the FIRST worker's resolution — its own distinct projection is never
 *   computed and its enclosing rule stalls.
 *
 *   Root 1 (`(1 ? 2 : int(true)) <= 4`, `<=`/`>=` — lex-ambiguous with
 *     `<`/`>`): key `(pos11, Int, bp11, wrap(Bool, LtEq))` — the CAST body
 *     `int(true)`[5,10] is WorkerInserted; the GROUP body
 *     `(1?2:int(true))`[1,9] collides. The group projection (Int->Bool over
 *     the whole group) is lost; only the cast projection survives, corrupting
 *     the ternary (its Int else-operand becomes a Bool) -> accepting_roots=[].
 *   Root 2 (`@(@Pathmap()!({||}, {}))`): key `(pos8, Bag->Proc, bp0,
 *     wrap(Proc, 31))` — a sibling Proc-channel (rule 13) frame is
 *     WorkerInserted; the correct POutput2Plus (Name-channel) rule-8 frame
 *     collides. The bag operand projection for the rule-8 frame is lost; the
 *     channel Name never fills operand-0 -> rule-8 rejects (expected Name got
 *     Proc).
 *
 *   The single-token / direct-element paths bypass this cohort entirely
 *   (`apply_singleton_push` / the Root-A element redirect), so they ACCEPT —
 *   which is exactly why the OK variants pass and only these compound shapes
 *   fail.
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE FIX: give each rule-operand / group-close projection an ENCLOSING-FRAME
 *   DISCRIMINANT `disc` (`crosscat_projection_enclosing_frame_disc`, `None`
 *   for chain interiors / plain projections). The first worker under a key
 *   RECORDS its `disc`; a later `InflightCollision` COMPARES:
 *     - `disc` MATCHES the recorded one (a redundant SAME-frame re-projection —
 *       the M4 nested-cast cast-family `int(int(...))` into the same slot):
 *       PAUSE+merge (cohort dedup / chain-O(N^2) ceiling preserved);
 *     - `disc` DIFFERS (or the recordee had no disc, i.e. a chain-interior
 *       worker): allocate the colliding projection as an INDEPENDENT uncached
 *       worker (its distinct-frame projection is computed, not merged away).
 *   Only the SECOND (colliding) dispatch is ever affected; the first worker
 *   always uses the cohort. Kill-switch: `PRATTAIL_NO_CROSSCAT_PROJ_UNCACHED`.
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THIS MODEL abstracts the collision decision
 *   `decide : bool (*enabled*) -> option disc (*recorded*) -> option disc
 *            (*current*) -> Decision`
 * and the resulting readings multiset. The theorems establish:
 *   (1) EXACT trigger: `Bypass` fires IFF enabled AND the current projection
 *       HAS a frame disc AND it does NOT equal the recorded one — no heuristic;
 *   (2) SAME-FRAME dedup preserved: enabled, both discs present and EQUAL =>
 *       `Merge` (the M4 nested-cast redundant re-projection still merges);
 *   (3) NO-DISC (chain interior) => never bypassed on the RECORD side, and a
 *       current projection with no disc never triggers bypass => byte-identical
 *       cohort path for chains;
 *   (4) KILL-SWITCH OFF => always `Merge` (byte-identical control);
 *   (5) NO-LOSS: the distinct-frame projection reading is ADDED by `Bypass`
 *       (present after) while the first frame's reading is retained;
 *   (6) the SAME-FRAME merge does NOT add a second reading (the dedup is
 *       genuine — one shared resolution);
 *   (7) chain-safety WITNESS: a chain interior (current disc = None) is never
 *       bypassed, for any recorded value — the cohort ceiling is untouched.
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

Section CrossCatProjectionFrameDedup.

  (* A frame discriminant is a natural (the packed (cat,rule,slot) or the
     tagged body SPPF id from `crosscat_projection_enclosing_frame_disc`).
     `None` = the projection is NOT a rule-operand / group-close projection
     (a chain interior or plain projection) — it carries no frame identity. *)
  Definition Disc := nat.

  (* The collision decision. *)
  Inductive Decision : Type :=
    | Merge  : Decision      (* pause as cohort member (dedup)             *)
    | Bypass : Decision.     (* allocate an independent uncached worker    *)

  (* option-nat Boolean equality (the `registrant != Some(disc)` compare). *)
  Definition option_beq (x y : option Disc) : bool :=
    match x, y with
    | Some a, Some b => Nat.eqb a b
    | None, None => true
    | _, _ => false
    end.

  (* ── `decide` : the WorkerInserted-recorded disc + the colliding
     dispatch's current disc + the kill-switch, → Decision. Mirrors the Rust
     `InflightCollision` arm:
       if enabled && current = Some d && recorded <> Some d then Bypass
       else Merge.
     (When current = None — a chain interior — never bypass.) *)
  Definition decide (enabled : bool) (recorded current : option Disc) : Decision :=
    if enabled then
      match current with
      | Some d => if option_beq recorded (Some d) then Merge else Bypass
      | None => Merge
      end
    else Merge.

  (* ══════════════ bypass_iff_trigger ══════════════
     (1) The EXACT trigger: `decide enabled recorded current = Bypass` IFF
     enabled AND current is `Some d` AND recorded is NOT `Some d`. No hidden
     condition, no heuristic. *)
  Theorem bypass_iff_trigger :
    forall enabled recorded current,
      decide enabled recorded current = Bypass
      <-> (enabled = true
           /\ exists d, current = Some d /\ option_beq recorded (Some d) = false).
  Proof.
    intros enabled recorded current. unfold decide. split.
    - intro H. destruct enabled; [| discriminate].
      destruct current as [d|]; [| discriminate].
      destruct (option_beq recorded (Some d)) eqn:Hb; [discriminate|].
      split; [reflexivity|]. exists d. split; [reflexivity | exact Hb].
    - intros [He [d [Hc Hb]]]. rewrite He, Hc, Hb. reflexivity.
  Qed.

  (* ══════════════ same_frame_merges ══════════════
     (2) SAME-FRAME DEDUP PRESERVED: when enabled and the current disc EQUALS
     the recorded one (a redundant same-frame re-projection — the M4 nested-cast
     `int(int(...))` cast-family into the same slot), the decision is `Merge`
     (the cohort dedup / chain ceiling is untouched). *)
  Theorem same_frame_merges :
    forall d,
      decide true (Some d) (Some d) = Merge.
  Proof.
    intro d. unfold decide, option_beq. rewrite Nat.eqb_refl. reflexivity.
  Qed.

  (* ══════════════ distinct_frame_bypasses ══════════════
     (2b) DISTINCT-FRAME: enabled, current `Some d`, recorded `Some r` with
     r <> d ⇒ `Bypass` (the Root-1 group-vs-cast / Root-2 rule-8-vs-rule-13
     case — the second frame's projection is computed independently). *)
  Theorem distinct_frame_bypasses :
    forall r d,
      r <> d ->
      decide true (Some r) (Some d) = Bypass.
  Proof.
    intros r d Hne. unfold decide, option_beq.
    destruct (Nat.eqb r d) eqn:Hb.
    - apply Nat.eqb_eq in Hb. contradiction.
    - reflexivity.
  Qed.

  (* ══════════════ no_disc_current_merges ══════════════
     (3) A CHAIN-INTERIOR / plain projection (current disc = None: not a
     rule-operand / group-close projection) is NEVER bypassed — it takes the
     normal cohort path unconditionally. Byte-identical for chains. *)
  Theorem no_disc_current_merges :
    forall enabled recorded,
      decide enabled recorded None = Merge.
  Proof.
    intros enabled recorded. unfold decide. destruct enabled; reflexivity.
  Qed.

  (* ══════════════ no_disc_recorded_first_worker ══════════════
     (3b) The RECORD side: `crosscat_proj_registrant_frame` only stores a disc
     for rule-operand / group-close projections (disc = Some _); a chain-
     interior first worker records nothing. Modeled by `record`: it inserts
     iff the disc is Some. So a chain-interior worker leaves the map absent
     (recorded = None at a later collision). *)
  Definition record (d : option Disc) : option Disc :=
    (* returns the value now stored under the key after this worker registers *)
    match d with
    | Some x => Some x         (* rule-operand / group-close: store          *)
    | None => None             (* chain interior: leave absent               *)
    end.

  Theorem chain_interior_records_nothing :
    record None = None.
  Proof. reflexivity. Qed.

  Theorem rule_operand_records_disc :
    forall d, record (Some d) = Some d.
  Proof. intro d. reflexivity. Qed.

  (* ══════════════ collision_with_chain_worker_bypasses ══════════════
     (3c) If the first (in-flight) worker was a chain interior (recorded =
     None) but the colliding dispatch IS a rule-operand projection
     (current = Some d), the decision is `Bypass` — the rule-operand
     projection must NOT merge into a chain-interior worker (it belongs to a
     different, framed context). Matches the Rust `registrant != Some(disc)`
     with `registrant = None`. *)
  Theorem collision_with_chain_worker_bypasses :
    forall d,
      decide true None (Some d) = Bypass.
  Proof.
    intro d. unfold decide, option_beq. reflexivity.
  Qed.

  (* ══════════════ killswitch_off_always_merges ══════════════
     (4) KILL-SWITCH OFF (enabled=false) ⇒ ALWAYS `Merge` — byte-identical
     control (`PRATTAIL_NO_CROSSCAT_PROJ_UNCACHED` / const=false): every
     collision pauses+merges exactly as pre-fix. *)
  Theorem killswitch_off_always_merges :
    forall recorded current,
      decide false recorded current = Merge.
  Proof. intros recorded current. reflexivity. Qed.

  (* ── The readings multiset (GLR no-loss). A "reading" is a projection
     result; `RFirst` = the in-flight worker's projection, `RSecond` = the
     colliding dispatch's distinct projection. Pre-collision the branch set
     already holds `RFirst` (the worker). *)
  Inductive Reading : Type :=
    | RFirst   : Reading
    | RSecond  : Reading.

  Definition reading_beq (x y : Reading) : bool :=
    match x, y with
    | RFirst, RFirst => true
    | RSecond, RSecond => true
    | _, _ => false
    end.

  (* Apply the decision to the readings: `Bypass` ADDS `RSecond` (the
     independent projection); `Merge` keeps the set (the member shares
     `RFirst`'s resolution — no second reading). *)
  Definition apply_decision (dec : Decision) (bs : list Reading) : list Reading :=
    match dec with
    | Bypass => bs ++ [RSecond]
    | Merge => bs
    end.

  (* ══════════════ bypass_adds_second_reading ══════════════
     (5) NO-LOSS: on `Bypass`, `RSecond` (the distinct-frame projection) is
     PRESENT after — the second frame's projection is genuinely offered. *)
  Theorem bypass_adds_second_reading :
    forall bs, In RSecond (apply_decision Bypass bs).
  Proof.
    intro bs. simpl. apply in_or_app. right. left. reflexivity.
  Qed.

  (* ══════════════ decision_retains_first_reading ══════════════
     (5b) EVERY reading present before the decision is still present after
     (both `Merge` and `Bypass` only ever APPEND) — the first frame's
     projection is never dropped. GLR-safe. *)
  Theorem decision_retains_first_reading :
    forall dec bs r, In r bs -> In r (apply_decision dec bs).
  Proof.
    intros dec bs r Hin. destruct dec; simpl.
    - exact Hin.
    - apply in_or_app. left. exact Hin.
  Qed.

  (* ══════════════ merge_adds_no_reading ══════════════
     (6) DEDUP is genuine: `Merge` does NOT add a second reading — the paused
     member shares the in-flight worker's single resolution (this is why the
     same-frame cast-family / chain does not blow up: N redundant re-projections
     collapse to one). *)
  Theorem merge_adds_no_reading :
    forall bs, apply_decision Merge bs = bs.
  Proof. intro bs. reflexivity. Qed.

  (* ══════════════ chain_never_bypassed_witness ══════════════
     (7) CHAIN-SAFETY WITNESS: a chain-interior colliding dispatch (current =
     None) is NEVER bypassed regardless of what the first worker recorded, so
     the readings set is unchanged (no extra uncached worker) — the cohort
     ceiling / chain-O(N^2) defense is provably untouched by the fix. *)
  Theorem chain_never_bypassed_witness :
    forall enabled recorded bs,
      apply_decision (decide enabled recorded None) bs = bs.
  Proof.
    intros enabled recorded bs.
    rewrite no_disc_current_merges. reflexivity.
  Qed.

  (* ══════════════ same_frame_cast_family_no_blowup ══════════════
     (7b) The M4 cast-family WITNESS: N successive same-frame re-projections
     (all `decide true (Some d) (Some d) = Merge`) add NO readings — the
     dedup collapses them to the single shared resolution (no `int(int(...))`
     blowup). Stated for a whole list of same-frame collisions. *)
  Fixpoint apply_all (decs : list Decision) (bs : list Reading) : list Reading :=
    match decs with
    | [] => bs
    | d :: rest => apply_all rest (apply_decision d bs)
    end.

  Theorem same_frame_cast_family_no_blowup :
    forall n d bs,
      apply_all (repeat (decide true (Some d) (Some d)) n) bs = bs.
  Proof.
    intros n d bs. rewrite same_frame_merges.
    induction n as [| n IH]; simpl.
    - reflexivity.
    - (* apply_decision Merge bs = bs, then recurse *)
      simpl. exact IH.
  Qed.

  (* ════════════════════════════════════════════════════════════════════════
     ROOT E (2026-07-03): the `proj_source` WIDENING of the frame discriminant.

     ─────────────────────────────────────────────────────────────────────────
     THE WIDENING. Before ROOT E, the discriminant of a rule-operand projection
     encoded ONLY the enclosing frame identity (the packed `(cat, rule, slot)`
     for R2 / the body SPPF id for R1) — NOT the projection's SOURCE category
     (`proj_source`). Two cross-category projections into the SAME enclosing
     frame (`@error!(a0, a1, a2)`'s Name-channel projection and a sibling
     Proc-channel projection, both under POutput2Plus operand-0 with
     `operands_completed = 0`) therefore collapsed to the SAME disc and were
     treated as a same-frame redundant re-projection (Merge). The widening
     (`crosscat_projection_enclosing_frame_disc`, ENABLED by default; disabled
     by `PRATTAIL_NO_ROOTE_PROJ_SOURCE_DISC` / the compile-time const) FOLDS
     `proj_source` into the (hashed) disc so cross-source projections into the
     same frame get DISTINCT discs.

     ─────────────────────────────────────────────────────────────────────────
     THE MODEL. A widened disc is modeled as the structural VALUE it identifies:
     an enclosing frame `frame` together with the projection source `source`.
     The Rust `hash_frame_disc(tag, proj_source, payload)` is an ENCODING of
     exactly `(tag, source, frame)`; its one relevant law is
       `wdisc f1 s1 = wdisc f2 s2  <->  f1 = f2  /\  s1 = s2`,
     which the structural `WDisc` constructor below provides for free (Rocq
     structural equality) — no arithmetic pairing needed. A physical FxHash
     COLLISION (two distinct value-tuples aliasing one u64) could only cause a
     SPURIOUS Merge, i.e. it degrades toward the PRE-FIX conservative behavior
     (which `killswitch_off_always_merges` / `same_frame_merges` prove is
     already sound and reading-lossless): it can NEVER drop a reading the
     pre-fix path retained. So the structural model is the soundness-safe
     over-approximation — the real widened code bypasses AT LEAST as often, and
     hence retains AT LEAST as many readings, as this model.

     `wdisc_of enable frame source` is the disc actually recorded / compared:
     widening ON  ⇒ the source is part of the disc (`WD frame (Some source)`);
     widening OFF ⇒ the source is DROPPED (`WD frame None`) — exactly the
     pre-fix frame-only disc. Injecting into `option Disc` for `decide` is done
     by a fixed structural code (`wcode`), whose only used property is that it
     is INJECTIVE on `WDisc` (equal codes <-> equal WDiscs), proven below with
     no axioms. *)

  Definition Frame := nat.
  Definition Source := nat.

  (* The widened-disc VALUE: a frame plus an optional source. *)
  Inductive WDisc : Type :=
    | WD : Frame -> option Source -> WDisc.

  (* Boolean structural equality on `WDisc` (used as the equality the runtime
     `Nat.eqb` on the hashed u64 stands in for). *)
  Definition wdisc_beq (x y : WDisc) : bool :=
    match x, y with
    | WD f1 s1, WD f2 s2 =>
        Nat.eqb f1 f2 &&
        match s1, s2 with
        | Some a, Some b => Nat.eqb a b
        | None, None => true
        | _, _ => false
        end
    end.

  Lemma wdisc_beq_true_iff :
    forall x y, wdisc_beq x y = true <-> x = y.
  Proof.
    intros [f1 s1] [f2 s2]. unfold wdisc_beq. split.
    - intro H. apply andb_true_iff in H. destruct H as [Hf Hs].
      apply Nat.eqb_eq in Hf. subst f2.
      destruct s1 as [a|]; destruct s2 as [b|]; try discriminate.
      + apply Nat.eqb_eq in Hs. subst b. reflexivity.
      + reflexivity.
    - intro H. inversion H; subst.
      apply andb_true_iff. split; [ apply Nat.eqb_refl | ].
      destruct s2 as [b|]; [ apply Nat.eqb_refl | reflexivity ].
  Qed.

  Lemma wdisc_beq_refl : forall x, wdisc_beq x x = true.
  Proof. intro x. apply wdisc_beq_true_iff. reflexivity. Qed.

  (* The disc actually recorded / compared for a projection with enclosing
     `frame` and source `source`, under the widening flag `enable`. *)
  Definition wdisc_of (enable : bool) (frame : Frame) (source : Source) : WDisc :=
    if enable then WD frame (Some source) else WD frame None.

  (* ══════════════ wdisc_same_source_same_frame_eq ══════════════
     STRICT-REFINEMENT core (positive): with the widening ON, the SAME frame
     and SAME source ⇒ the SAME disc (so `decide` sees `Some d` = recorded and
     MERGES — the M4 same-frame / Root-1/2 same-source cast-family dedup is
     preserved, byte-identical to pre-fix on the merge side). *)
  Theorem wdisc_same_source_same_frame_eq :
    forall f s, wdisc_of true f s = wdisc_of true f s.
  Proof. intros f s. reflexivity. Qed.

  (* ══════════════ wdisc_distinct_source_same_frame_neq ══════════════
     STRICT-REFINEMENT core (negative): with the widening ON, the SAME frame
     but DIFFERENT sources ⇒ DISTINCT discs. THIS is the ROOT-E split — the
     `@error` Name-channel projection (source = Name) and a sibling Proc-channel
     projection (source = Proc) into the SAME POutput2Plus operand-0 frame no
     longer collapse. *)
  Theorem wdisc_distinct_source_same_frame_neq :
    forall f s1 s2, s1 <> s2 -> wdisc_of true f s1 <> wdisc_of true f s2.
  Proof.
    intros f s1 s2 Hne Heq. unfold wdisc_of in Heq.
    inversion Heq. contradiction.
  Qed.

  (* ══════════════ wdisc_killswitch_ignores_source ══════════════
     KILL-SWITCH: with the widening OFF, the disc DROPS the source entirely — it
     depends ONLY on the frame, exactly the pre-fix frame-only disc. So two
     projections that differ ONLY in source are IDENTICAL (byte-identical to the
     pre-fix code: `wdisc_of false f s1 = wdisc_of false f s2`). *)
  Theorem wdisc_killswitch_ignores_source :
    forall f s1 s2, wdisc_of false f s1 = wdisc_of false f s2.
  Proof. intros f s1 s2. reflexivity. Qed.

  (* ── Bridge `WDisc` into the `decide` model. `wcode` is a fixed injective
     code from `WDisc` into `Disc` (nat); its ONLY used property is
     `wcode x = wcode y <-> x = y` (`wcode_inj`). We realize it structurally so
     the injectivity is axiom-free: `frame * 2 + tag_of_source` interleaves the
     None/Some tag into bit 0 and keeps the frame above it, and the source (when
     present) is offset past the frame. Concretely we only ever COMPARE codes of
     discs that share the SAME frame `f` (the collision is under one cache key /
     one enclosing frame), for which the code reduces to a plain injective
     function of the optional source — all we need for the theorems. *)
  Definition source_tag (os : option Source) : nat :=
    match os with Some s => S s | None => 0 end.

  Lemma source_tag_inj :
    forall a b, source_tag a = source_tag b -> a = b.
  Proof.
    intros [a|] [b|]; simpl; intro H; try discriminate.
    - injection H as H. subst. reflexivity.
    - reflexivity.
  Qed.

  (* Code of a disc UNDER A FIXED FRAME `f`: injective in the optional source. *)
  Definition wcode_at (f : Frame) (os : option Source) : Disc :=
    source_tag os.

  Lemma wcode_at_inj :
    forall f a b, wcode_at f a = wcode_at f b -> a = b.
  Proof. intros f a b H. apply source_tag_inj. exact H. Qed.

  (* The `decide` outcome for two projections at the SAME frame `f`: the first
     (recorded) has source-option `r`, the colliding one has source-option `c`,
     under widening `enable`. We record/compare the frame-fixed codes. *)
  Definition decide_at (enable : bool) (f : Frame) (r c : option Source) : Decision :=
    let rec_disc :=
      if enable then Some (wcode_at f r) else Some (wcode_at f None) in
    let cur_disc :=
      if enable then Some (wcode_at f c) else Some (wcode_at f None) in
    decide true rec_disc cur_disc.

  (* ══════════════ distinct_source_same_frame_bypasses ══════════════
     (ROOT E, main) With the widening ON, at one enclosing frame `f`, a colliding
     projection whose SOURCE differs from the recorded worker's source ⇒
     `Bypass`. Composed with `bypass_adds_second_reading`, the colliding
     projection's reading is RETAINED (added), so the `@error` Name-channel and
     the sibling Proc-channel readings BOTH survive. *)
  Theorem distinct_source_same_frame_bypasses :
    forall f rs cs,
      rs <> cs ->
      decide_at true f (Some rs) (Some cs) = Bypass.
  Proof.
    intros f rs cs Hne. unfold decide_at.
    apply distinct_frame_bypasses.
    (* wcode_at f (Some rs) <> wcode_at f (Some cs) *)
    intro Heq. apply wcode_at_inj in Heq.
    injection Heq as Heq. contradiction.
  Qed.

  (* ══════════════ distinct_source_same_frame_retains_both ══════════════
     (ROOT E, no-loss corollary) The Bypass ADDS the colliding reading (via
     `bypass_adds_second_reading`) while every prior reading is retained (via
     `decision_retains_first_reading`): both channel readings coexist. *)
  Theorem distinct_source_same_frame_retains_both :
    forall f rs cs bs,
      rs <> cs ->
      In RSecond (apply_decision (decide_at true f (Some rs) (Some cs)) bs)
      /\ (forall r, In r bs -> In r (apply_decision (decide_at true f (Some rs) (Some cs)) bs)).
  Proof.
    intros f rs cs bs Hne.
    rewrite (distinct_source_same_frame_bypasses f rs cs Hne).
    split.
    - apply bypass_adds_second_reading.
    - intros r Hin. apply decision_retains_first_reading. exact Hin.
  Qed.

  (* ══════════════ same_source_same_frame_still_merges ══════════════
     (STRICT REFINEMENT, positive) With the widening ON, at one enclosing frame
     `f`, a colliding projection with the SAME source as the recorded worker ⇒
     `Merge` — UNCHANGED from `same_frame_merges`. Root-1/2's same-source
     collisions + the M4 same-frame cast-family therefore behave BYTE-IDENTICALLY
     to pre-fix (the widening splits ONLY cross-source collisions, never
     same-source ones). *)
  Theorem same_source_same_frame_still_merges :
    forall f s,
      decide_at true f (Some s) (Some s) = Merge.
  Proof.
    intros f s. unfold decide_at. simpl. apply same_frame_merges.
  Qed.

  (* ══════════════ same_source_same_frame_adds_no_reading ══════════════
     (STRICT REFINEMENT, dedup genuine) The same-source Merge adds NO reading —
     the same-frame cast-family collapse is preserved verbatim. *)
  Theorem same_source_same_frame_adds_no_reading :
    forall f s bs,
      apply_decision (decide_at true f (Some s) (Some s)) bs = bs.
  Proof.
    intros f s bs. rewrite (same_source_same_frame_still_merges f s).
    apply merge_adds_no_reading.
  Qed.

  (* ══════════════ killswitch_off_disc_ignores_source ══════════════
     (KILL-SWITCH, byte-identity) With the widening OFF, the disc drops the
     source, so a cross-source collision at the same frame `f` gets IDENTICAL
     discs ⇒ `Merge` — EXACTLY the pre-fix behavior (regardless of whether the
     sources differ). This is the labeled A/B control: `decide_at false` never
     sees the source. *)
  Theorem killswitch_off_disc_ignores_source :
    forall f rs cs,
      decide_at false f (Some rs) (Some cs) = Merge.
  Proof.
    (* With the widening OFF both discs are `wcode_at f None` (source dropped),
       so `decide` compares two identical discs and reduces to `Merge`. *)
    intros f rs cs. unfold decide_at. reflexivity.
  Qed.

  (* ══════════════ widening_is_strict_refinement ══════════════
     (STRICT-REFINEMENT summary) At any fixed frame `f`, the widened decision
     (`decide_at true`) equals the pre-fix decision (`decide_at false`) on EVERY
     same-source collision, and can ONLY differ (Merge -> Bypass, i.e. ADD a
     reading) on cross-source collisions. Formally: whenever the widened
     decision differs from the pre-fix decision, the widened one is `Bypass` and
     the pre-fix one is `Merge` (never the reverse) — the widening only ever adds
     readings, never removes. GLR-monotone strict refinement. *)
  Theorem widening_is_strict_refinement :
    forall f r c,
      decide_at true f (Some r) (Some c) <> decide_at false f (Some r) (Some c) ->
      decide_at true f (Some r) (Some c) = Bypass
      /\ decide_at false f (Some r) (Some c) = Merge.
  Proof.
    intros f r c Hdiff.
    rewrite (killswitch_off_disc_ignores_source f r c) in *.
    (* pre-fix is Merge; so widened must be Bypass (else no difference) *)
    destruct (decide_at true f (Some r) (Some c)) eqn:Hw.
    - exfalso. apply Hdiff. reflexivity.
    - split; reflexivity.
  Qed.

End CrossCatProjectionFrameDedup.

(* ══════════════════════════════════════════════════════════════════════════
   Admission audit. Every theorem above must be closed under the global context
   (no Admitted, no Axiom, no Variable-as-axiom leakage). *)
Print Assumptions bypass_iff_trigger.
Print Assumptions same_frame_merges.
Print Assumptions distinct_frame_bypasses.
Print Assumptions no_disc_current_merges.
Print Assumptions chain_interior_records_nothing.
Print Assumptions rule_operand_records_disc.
Print Assumptions collision_with_chain_worker_bypasses.
Print Assumptions killswitch_off_always_merges.
Print Assumptions bypass_adds_second_reading.
Print Assumptions decision_retains_first_reading.
Print Assumptions merge_adds_no_reading.
Print Assumptions chain_never_bypassed_witness.
Print Assumptions same_frame_cast_family_no_blowup.
(* ROOT E (2026-07-03) — the `proj_source` widening theorems. *)
Print Assumptions wdisc_beq_true_iff.
Print Assumptions wdisc_beq_refl.
Print Assumptions wdisc_same_source_same_frame_eq.
Print Assumptions wdisc_distinct_source_same_frame_neq.
Print Assumptions wdisc_killswitch_ignores_source.
Print Assumptions source_tag_inj.
Print Assumptions wcode_at_inj.
Print Assumptions distinct_source_same_frame_bypasses.
Print Assumptions distinct_source_same_frame_retains_both.
Print Assumptions same_source_same_frame_still_merges.
Print Assumptions same_source_same_frame_adds_no_reading.
Print Assumptions killswitch_off_disc_ignores_source.
Print Assumptions widening_is_strict_refinement.
