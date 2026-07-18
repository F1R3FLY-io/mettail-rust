(*
 * ReplayIdentityIntegrity: S1-FACTORING F5-2 FV — THE NEW SURFACE (flagged
 * by the implementation leg beyond the plan's original §5 list; ledger
 * s2_stageA_ledger.md §"S1 F5-2" residual (1)): the pure D2-class
 * (LHS-join) create-after-pop REPLAY channel and its POP-TIME rule
 * identity, root-caused and fixed in commit 8df26fbe.
 *
 * THE BUG CLASS (round-1 window RED, logs_s1f5_2/round1/): the D2 replay
 * reconstructed a popped constituent's rule packing with an identity
 * DERIVED FROM THE FRAME's pushed symbol — exact only while pop identity
 * always equalled the frame symbol, which was EVERY case before spine
 * commits existed. A COMMITTED mixfix-spine frame pops with the MEMBER's
 * identity while its frame symbol keeps the spine id, so the old
 * derivation minted a spine-keyed packing that bypassed the intern-site
 * H9 asserts and died at realize ("S1 H9: spine id 0xf803 reached
 * realize" on the @(...)-quoted send family, where the @-lattice's second
 * calling context replays the popped send frame).
 *
 * THE FIX (the AV6/A8 doctrine — "the slot label may keep SPINE; the
 * packing/fire identity may not" — applied to the replay channel): carry
 * the pop-time rule identity `(cat << 16) | rule` through
 * `RecordedPop`/`GllReturn` (`u32::MAX` when the popping site carries
 * none); the replay PREFERS the recorded identity, falling back to the
 * frame-symbol derivation when none; the P-set dedup key widens to
 * (pos, result_w, rule_id).
 *
 * WHAT IS PROVED (the mandate's (a)-(d)):
 *   (a) REPLAY-FAITHFULNESS — for every pre-F5-2-class pop (recorded
 *       identity absent, or equal to the frame-derived identity — the
 *       committed-state invariant "pop identity always equalled the frame
 *       symbol"), the new replay is EXTENSIONALLY IDENTICAL to the old
 *       derivation (the byte-identity claim as a theorem, pointwise and
 *       over pop streams).
 *   (b) SPINE-EXCLUSION — a committed member pop replays with the MEMBER
 *       identity: chaining the machine's pop_key_below_base (the popping
 *       coordinate's rule is a real member rule) through the D2 record
 *       function and the replay preference, NO replay-constructed packing
 *       carries a spine id in its low 16 bits when the recorded identity
 *       is a member rule — for EVERY frame-pushed symbol, spine frames
 *       included (the H9 assert transported to the replay channel). The
 *       COUNTERFACTUAL is also a theorem: the old derivation from a
 *       spine-pushed frame yields a spine-keyed low16 (the round-1 RED as
 *       arithmetic), discharged concretely on the mx_table r4 lineage.
 *   (c) THE WIDENED DEDUP KEY — two pops at equal (pos, result_w) with
 *       DISTINCT member identities BOTH enter P and BOTH replay (the
 *       narrow pre-F5-2 key would silently drop the second — modeled as
 *       the counterfactual); duplicate pops remain idempotent (no state
 *       change, no double-emit); and under the pre-F5-2 frame-constant-
 *       identity invariant the wide and narrow keys build IDENTICAL
 *       P-sets ("never splits pre-F5-2 sets", gss.rs @1512-1536).
 *   (d) THE WEIGHT LAW TIE (PureCommitFoldIntegrity's ReplacePreservesUW /
 *       PackingWeightMemberDetermined neighborhood) — the replay intern is
 *       gated by `packing_exists` (STAGE C: "Exists ⇒ no-op" — a replay
 *       re-intern with `one` would ⊕-corrupt the pop-time weight, lex-min
 *       pulls toward one): existing packings are NEVER overwritten, key
 *       uniqueness is preserved, the fallback-interned weight is w_one
 *       (identity-like) under the member-determined key, and the
 *       member-determined packing weight law (`fold_prefix_washes` /
 *       `packing_weight_member_determined`) survives every replay —
 *       stated as `replay_preserves_member_determined_weight`.
 *
 * HONEST SCOPE: static value/coordinate models of the replay channel's
 * identity and store disciplines — NOT a runtime GSS bisimulation (the
 * runtime side is the F5-2 round-2 battery: H9 = 0 across all logs,
 * ladders byte-exact, the counterfactual legs' receipts in
 * scratchpad/zz_probes/logs_s1f5_2/). The u32 identity space is modeled
 * in nat with `(cat << 16) | rule` as `cat * 65536 + rule` (exact for
 * rule < 65536, which A9 pins: every rule id and spine id is a u16) and
 * `u32::MAX` ("none") as `None`.
 *
 * ── CROSS-REFERENCE TABLE (model ↔ the Rust it transcribes; commit
 *    8df26fbe) ──
 *
 *   `recorded_pop`             ↔ gss.rs `RecordedPop { pos, result_w,
 *                                rule_id }` (@885-903); `rp_rule = None`
 *                                ↔ `rule_id == u32::MAX` =
 *                                `CGLL_PURE_RULE_NONE`
 *                                (wpda_walker.rs @4748)
 *   `same_key_wide`/`add_pop`  ↔ gss.rs `gll_pop`'s widened P-set guard
 *                                `p.pos == pos && p.result_w == result_w
 *                                && p.rule_id == rule_id` (@1525-1533);
 *                                duplicate ⇒ `return Vec::new()` (no
 *                                returns emitted, no P entry)
 *   `same_key_narrow`          ↔ the PRE-F5-2 guard (pos, result_w) —
 *                                the counterfactual
 *   `gll_pop_model`            ↔ gll_pop (@1505-1557): gate, record, one
 *                                return per current edge, every return
 *                                carrying THIS pop's `rule_id`
 *   `create_replay`            ↔ gll_create's replay of EVERY recorded
 *                                pop into a fresh edge, `rule_id:
 *                                p.rule_id` (@1480-1497)
 *   `frame_derived`            ↔ the pushed-symbol derivation:
 *                                `pushed_rule` = NONE for CategoryEntry
 *                                frames else `(cat << 16) | rule`
 *                                (wpda_walker.rs @26873-26879); the
 *                                NONE-frame fallback `cat << 16`
 *                                (@27080-27081)
 *   `replay_rule`              ↔ the fixed replay preference
 *                                (@27078-27084): `if rep.rule_id != NONE
 *                                { rep.rule_id } else { <old derivation> }`
 *   `d2_recorded_id`           ↔ the D2 pop site (@28133-28134, @28209):
 *                                `rule_id = (cat << 16) |
 *                                d.cur_sym.rule_index_in_category` — the
 *                                POP-TIME identity (post-commit = the
 *                                member marker, by the D-3 fork-CAR
 *                                `cur_sym := branch.symbol`); all OTHER
 *                                gll_pop callers record
 *                                `CGLL_PURE_RULE_NONE`
 *   `replay_intern`/`plookup`  ↔ the STAGE C replay packing gate
 *                                (@27129-27141): `if !packing_exists(
 *                                rule_id, children) { intern_packing(
 *                                rule_id, children, W::one_ref()) }` —
 *                                counted in `replay_weight_drops`
 *   the machine premises       ↔ MixfixSpineCommit's mx_table (the
 *                                emitted !-cohort prelude) + the shipped
 *                                PureCommitFoldIntegrity machine
 *
 * `Print Assumptions` on every theorem must report
 * "Closed under the global context" (zero admission / axiom / parameter;
 * Rocq 9.1).
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From PrattailWpdaRuntime Require Import PureCommitFoldIntegrity.
From PrattailWpdaRuntime Require Import MixfixSpineCommit.
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════
   THE IDENTITY SPACE — `(cat << 16) | rule` over nat.
   ═══════════════════════════════════════════════════════════════════════ *)

Definition pack (cat rk : nat) : nat := cat * 65536 + rk.

Definition low16 (n : nat) : nat := n mod 65536.

Definition is_spine_low16 (n : nat) : bool := SPINE_RULE_BASE <=? low16 n.

Lemma low16_pack :
  forall cat rk, rk < 65536 -> low16 (pack cat rk) = rk.
Proof.
  intros cat rk H.
  unfold low16, pack.
  rewrite Nat.add_comm.
  rewrite Nat.Div0.mod_add.
  apply Nat.mod_small. exact H.
Qed.

Lemma base_below_u16 : SPINE_RULE_BASE < 65536.
Proof. apply Nat.ltb_lt. vm_compute. reflexivity. Qed.

Lemma member_rule_fits_u16 :
  forall rk, rk < SPINE_RULE_BASE -> rk < 65536.
Proof.
  intros rk H.
  apply (Nat.lt_trans _ SPINE_RULE_BASE); [exact H | exact base_below_u16].
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   THE REPLAY IDENTITY — recorded-preferred, frame-derived fallback.
   ═══════════════════════════════════════════════════════════════════════ *)

(* The frame's pushed symbol as an identity source: None for CategoryEntry
   frames (no rule component), Some ((cat<<16)|rule) otherwise. *)
Definition frame_derived (cat : nat) (pushed : option nat) : nat :=
  match pushed with
  | None => pack cat 0      (* the `cat << 16` CategoryEntry fallback *)
  | Some pr => pr
  end.

(* THE FIXED REPLAY (@27078-27084): prefer the recorded pop-time identity;
   fall back to the old frame derivation when none was recorded. *)
Definition replay_rule (rec : option nat) (cat : nat) (pushed : option nat)
  : nat :=
  match rec with
  | Some r => r
  | None => frame_derived cat pushed
  end.

Theorem replay_prefers_recorded :
  forall r cat pushed, replay_rule (Some r) cat pushed = r.
Proof. reflexivity. Qed.

Theorem replay_fallback_is_old_derivation :
  forall cat pushed, replay_rule None cat pushed = frame_derived cat pushed.
Proof. reflexivity. Qed.

(* ── (a) REPLAY-FAITHFULNESS — the byte-identity claim as a theorem: on
      the PRE-F5-2 CLASS (no recorded identity, or recorded = derived —
      the committed-state invariant "pop identity always equalled the
      frame symbol"), the new replay computes EXACTLY the old value. ── *)

Definition pre_f52_class (cat : nat) (pushed : option nat)
  (rec : option nat) : Prop :=
  rec = None \/ rec = Some (frame_derived cat pushed).

Theorem replay_faithful_pointwise :
  forall cat pushed rec,
    pre_f52_class cat pushed rec ->
    replay_rule rec cat pushed = frame_derived cat pushed.
Proof.
  intros cat pushed rec [H | H]; subst rec; reflexivity.
Qed.

(* Stream form: every replay in a pre-F5-2-class pop stream constructs the
   identical rule key the old derivation did. *)
Theorem replay_faithful_stream :
  forall cat pushed recs,
    Forall (pre_f52_class cat pushed) recs ->
    Forall (fun rid => rid = frame_derived cat pushed)
      (map (fun rec => replay_rule rec cat pushed) recs).
Proof.
  intros cat pushed recs Hall.
  induction recs as [| rec rest IH]; simpl.
  - constructor.
  - inversion Hall; subst.
    constructor.
    + apply replay_faithful_pointwise. exact H1.
    + apply IH. exact H2.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (b) SPINE-EXCLUSION — the committed member pop replays with the MEMBER
   identity for EVERY frame-pushed symbol (spine frames included), chained
   from the machine: the D2 record function reads the POPPING coordinate
   (the descriptor's cur_sym after the D-3 commit), and pop_key_below_base
   pins that rule below the spine id space.
   ═══════════════════════════════════════════════════════════════════════ *)

(* The D2 pop-site record (@28133-28134, @28209): the popping descriptor's
   coordinate rule, packed with its category — None from a spine
   coordinate (no pop fires there; packings exist only at member Pops). *)
Definition d2_recorded_id (cat : nat) (c : cfg) : option nat :=
  match g_coord c with
  | CMember r _ => Some (pack cat r)
  | CSpine _ => None
  end.

(* The record function reads the POP-TIME identity: at a Pop coordinate it
   records exactly the packing key's rule. *)
Theorem d2_records_pop_time_identity :
  forall T c rk pw cat,
    packing_of T c = Some (rk, pw) ->
    d2_recorded_id cat c = Some (pack cat rk).
Proof.
  intros T c rk pw cat Hpack.
  unfold packing_of in Hpack.
  unfold d2_recorded_id.
  destruct (g_coord c) as [n | r p] eqn:Ec; [discriminate |].
  destruct (member_final T (r, p)); [| discriminate].
  inversion Hpack; subst.
  reflexivity.
Qed.

(* THE SPINE-EXCLUSION THEOREM: for any pop reached from a spine descent
   (hence committed — commit_precedes_final_pop) the recorded identity is
   the member's, and the replay-constructed packing key carries NO spine
   id in its low 16 bits — REGARDLESS of the frame's pushed symbol. *)
Theorem committed_pop_replay_member_keyed :
  forall T c c' k rk pw cat pushed,
    wf_table T ->
    wf_member_rules T ->
    steps T c c' k ->
    is_spine (g_coord c) = true ->
    packing_of T c' = Some (rk, pw) ->
    replay_rule (d2_recorded_id cat c') cat pushed = pack cat rk
    /\ low16 (pack cat rk) = rk
    /\ is_spine_low16 (pack cat rk) = false.
Proof.
  intros T c c' k rk pw cat pushed Hwf Hwfm Hsteps Hs Hpack.
  assert (Hlt : rk < SPINE_RULE_BASE).
  { eapply pop_key_below_base;
      [exact Hwf | exact Hwfm | exact Hsteps | exact Hs | exact Hpack]. }
  assert (Hfit : rk < 65536).
  { apply member_rule_fits_u16. exact Hlt. }
  rewrite (d2_records_pop_time_identity T c' rk pw cat Hpack).
  split; [reflexivity |].
  split.
  - apply low16_pack. exact Hfit.
  - unfold is_spine_low16.
    rewrite (low16_pack cat rk Hfit).
    apply Nat.leb_gt. exact Hlt.
Qed.

(* THE COUNTERFACTUAL (the round-1 RED as arithmetic): the OLD derivation
   from a spine-pushed frame yields a spine-keyed low16 — exactly the
   poisoned packing the realize H9 receipt caught ("spine id 0xf803
   reached realize"). *)
Theorem old_derivation_poisons_spine_frames :
  forall cat sid,
    SPINE_RULE_BASE <= sid ->
    sid < 65536 ->
    is_spine_low16 (frame_derived cat (Some (pack cat sid))) = true.
Proof.
  intros cat sid Hbase Hfit.
  unfold frame_derived, is_spine_low16.
  rewrite (low16_pack cat sid Hfit).
  apply Nat.leb_le. exact Hbase.
Qed.

(* The CategoryEntry-frame fallback (`cat << 16`) is spine-free — the
   pre-existing NONE-frame branch never minted a spine key either. *)
Theorem category_entry_fallback_member_class :
  forall cat, is_spine_low16 (frame_derived cat None) = false.
Proof.
  intro cat.
  unfold frame_derived, is_spine_low16.
  rewrite (low16_pack cat 0); [| apply Nat.ltb_lt; vm_compute; reflexivity].
  reflexivity.
Qed.

(* ── The CONCRETE mx_table instance: the r4 (POutput) commit lineage from
      MixfixSpineCommit pops at (4, 1); the frame keeps the SPINE id
      0xF803 = 63491. The fixed replay keys the packing by the member
      (low16 = 4); the old derivation would key it by the spine
      (low16 = 63491 ≥ SPINE_RULE_BASE) — the H9 receipt's exact shape.
      Category Proc = src 0, so pack 0 r = r. ── *)

Theorem mx_r4_replay_receipt :
  replay_rule (d2_recorded_id 0 (MkCfg 0 [w_one; w_one] (CMember 4 1) []))
    0 (Some (pack 0 63491))
  = pack 0 4
  /\ is_spine_low16 (pack 0 4) = false
  /\ is_spine_low16 (frame_derived 0 (Some (pack 0 63491))) = true.
Proof. vm_compute. repeat split. Qed.

(* The same receipt derived THROUGH the machine (not just computed): the
   scalar lineage's steps derivation + the generic theorem. *)
Theorem mx_r4_replay_via_machine :
  forall pushed,
    replay_rule
      (d2_recorded_id 0 (MkCfg 0 [w_one; w_one] (CMember 4 1) []))
      0 pushed
    = pack 0 4
    /\ is_spine_low16 (pack 0 4) = false.
Proof.
  intro pushed.
  destruct mx_scalar_lineage_receipt as [Hsteps Hpack].
  destruct (committed_pop_replay_member_keyed mx_table
              (MkCfg 0 [] (CSpine 1) [])
              (MkCfg 0 [w_one; w_one] (CMember 4 1) [])
              1 4 w_one 0 pushed
              mx_table_wf mx_table_wf_member_rules Hsteps eq_refl Hpack)
    as [Hrep [_ Hns]].
  split; [exact Hrep | exact Hns].
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (c) THE WIDENED DEDUP KEY — the P-set model.
   ═══════════════════════════════════════════════════════════════════════ *)

Record recorded_pop : Type := MkRecordedPop {
  rp_pos  : nat;
  rp_w    : nat;              (* result_w *)
  rp_rule : option nat        (* None ↔ u32::MAX = CGLL_PURE_RULE_NONE *)
}.

Definition oeqb (a b : option nat) : bool :=
  match a, b with
  | None, None => true
  | Some x, Some y => x =? y
  | _, _ => false
  end.

Lemma oeqb_refl : forall a, oeqb a a = true.
Proof.
  intros [x |]; simpl; [apply Nat.eqb_refl | reflexivity].
Qed.

(* The WIDENED key (gss.rs @1525-1533). *)
Definition same_key_wide (a b : recorded_pop) : bool :=
  (rp_pos a =? rp_pos b) && (rp_w a =? rp_w b)
  && oeqb (rp_rule a) (rp_rule b).

(* The PRE-F5-2 key — the counterfactual. *)
Definition same_key_narrow (a b : recorded_pop) : bool :=
  (rp_pos a =? rp_pos b) && (rp_w a =? rp_w b).

Definition add_pop_wide (ps : list recorded_pop) (p : recorded_pop)
  : list recorded_pop :=
  if existsb (same_key_wide p) ps then ps else ps ++ [p].

Definition add_pop_narrow (ps : list recorded_pop) (p : recorded_pop)
  : list recorded_pop :=
  if existsb (same_key_narrow p) ps then ps else ps ++ [p].

(* gll_pop, both halves: gate + record + one return per current edge, every
   return carrying THIS pop's identity; a duplicate emits NOTHING. *)
Definition gll_pop_model (ps : list recorded_pop) (p : recorded_pop)
  (edges : list nat) : list recorded_pop * list (nat * recorded_pop) :=
  if existsb (same_key_wide p) ps
  then (ps, [])
  else (ps ++ [p], map (fun e => (e, p)) edges).

(* gll_create's replay of a fresh edge: EVERY recorded pop replays, each
   with its OWN recorded identity. *)
Definition create_replay (e : nat) (ps : list recorded_pop)
  : list (nat * recorded_pop) :=
  map (fun p => (e, p)) ps.

(* Duplicate pops are IDEMPOTENT: no state change and no double-emit. *)
Theorem gll_pop_duplicate_idempotent :
  forall ps p edges,
    existsb (same_key_wide p) ps = true ->
    gll_pop_model ps p edges = (ps, []).
Proof.
  intros ps p edges H.
  unfold gll_pop_model. rewrite H. reflexivity.
Qed.

(* Inserting a pop makes its key present; re-inserting is the identity. *)
Theorem add_pop_wide_contains :
  forall ps p,
    existsb (same_key_wide p) (add_pop_wide ps p) = true.
Proof.
  intros ps p.
  unfold add_pop_wide.
  destruct (existsb (same_key_wide p) ps) eqn:E.
  - exact E.
  - rewrite existsb_app. rewrite E. simpl.
    rewrite orb_false_r.
    unfold same_key_wide.
    rewrite !Nat.eqb_refl, oeqb_refl.
    reflexivity.
Qed.

Theorem add_pop_wide_idempotent :
  forall ps p,
    add_pop_wide (add_pop_wide ps p) p = add_pop_wide ps p.
Proof.
  intros ps p.
  unfold add_pop_wide at 1.
  rewrite add_pop_wide_contains.
  reflexivity.
Qed.

(* THE NO-LOSS THEOREM: two pops at equal (pos, result_w) with DISTINCT
   member identities BOTH enter P under the wide key... *)
Theorem wide_key_no_loss :
  forall pos w r1 r2,
    r1 <> r2 ->
    let p1 := MkRecordedPop pos w (Some r1) in
    let p2 := MkRecordedPop pos w (Some r2) in
    add_pop_wide (add_pop_wide [] p1) p2 = [p1; p2].
Proof.
  intros pos w r1 r2 Hneq p1 p2.
  subst p1 p2.
  unfold add_pop_wide.
  simpl.
  unfold same_key_wide. simpl.
  rewrite !Nat.eqb_refl. simpl.
  destruct (r2 =? r1) eqn:E.
  - apply Nat.eqb_eq in E. symmetry in E. contradiction.
  - reflexivity.
Qed.

(* ... and BOTH replay into a fresh caller, each under its own identity. *)
Theorem wide_key_both_replay :
  forall pos w r1 r2 e,
    r1 <> r2 ->
    create_replay e
      (add_pop_wide (add_pop_wide [] (MkRecordedPop pos w (Some r1)))
         (MkRecordedPop pos w (Some r2)))
    = [(e, MkRecordedPop pos w (Some r1));
       (e, MkRecordedPop pos w (Some r2))].
Proof.
  intros pos w r1 r2 e Hneq.
  rewrite (wide_key_no_loss pos w r1 r2 Hneq).
  reflexivity.
Qed.

(* THE COUNTERFACTUAL: the narrow key DROPS the second identity (its P-set
   never holds both, so the second member's constituent never replays into
   a later calling context — the reading loss the widened key prevents). *)
Theorem narrow_key_drops_second :
  forall pos w r1 r2,
    add_pop_narrow (add_pop_narrow [] (MkRecordedPop pos w (Some r1)))
      (MkRecordedPop pos w (Some r2))
    = [MkRecordedPop pos w (Some r1)].
Proof.
  intros pos w r1 r2.
  unfold add_pop_narrow.
  simpl.
  unfold same_key_narrow. simpl.
  rewrite !Nat.eqb_refl.
  reflexivity.
Qed.

(* The second pop's RETURNS are also silenced under the narrow gate (the
   Rust duplicate branch returns Vec::new()). *)
Theorem narrow_gate_silences_returns :
  forall pos w r1 r2 edges,
    (if existsb (same_key_narrow (MkRecordedPop pos w (Some r2)))
          [MkRecordedPop pos w (Some r1)]
     then ([MkRecordedPop pos w (Some r1)], [])
     else ([MkRecordedPop pos w (Some r1); MkRecordedPop pos w (Some r2)],
           map (fun e => (e, MkRecordedPop pos w (Some r2))) edges))
    = ([MkRecordedPop pos w (Some r1)], @nil (nat * recorded_pop)).
Proof.
  intros pos w r1 r2 edges.
  simpl.
  unfold same_key_narrow. simpl.
  rewrite !Nat.eqb_refl.
  reflexivity.
Qed.

(* The wide gate EMITS the second pop's returns (one per edge). *)
Theorem wide_gate_emits_second :
  forall pos w r1 r2 edges,
    r1 <> r2 ->
    snd (gll_pop_model [MkRecordedPop pos w (Some r1)]
           (MkRecordedPop pos w (Some r2)) edges)
    = map (fun e => (e, MkRecordedPop pos w (Some r2))) edges.
Proof.
  intros pos w r1 r2 edges Hneq.
  unfold gll_pop_model.
  simpl.
  unfold same_key_wide. simpl.
  rewrite !Nat.eqb_refl. simpl.
  destruct (r2 =? r1) eqn:E.
  - apply Nat.eqb_eq in E. symmetry in E. contradiction.
  - reflexivity.
Qed.

(* ── PRE-F5-2 EQUIVALENCE ("never splits pre-F5-2 sets since identity was
      constant per frame", gss.rs): when every pop of a frame carries the
      SAME identity — which the faithfulness class guarantees (pop
      identity always equalled the frame symbol) — the wide and narrow
      keys agree pointwise, so the two insertions build IDENTICAL P-sets
      over any pop stream. ── *)

Lemma wide_eq_narrow_on_constant :
  forall rho p q,
    rp_rule p = rho ->
    rp_rule q = rho ->
    same_key_wide p q = same_key_narrow p q.
Proof.
  intros rho p q Hp Hq.
  unfold same_key_wide, same_key_narrow.
  rewrite Hp, Hq, oeqb_refl.
  apply andb_true_r.
Qed.

Lemma existsb_ext_in :
  forall (A : Type) (f g : A -> bool) (l : list A),
    (forall x, In x l -> f x = g x) ->
    existsb f l = existsb g l.
Proof.
  intros A f g l H.
  induction l as [| x rest IH]; simpl.
  - reflexivity.
  - rewrite (H x (or_introl eq_refl)).
    rewrite IH; [reflexivity |].
    intros y Hy. apply H. right. exact Hy.
Qed.

Theorem pre_f52_wide_narrow_agree :
  forall rho stream acc,
    Forall (fun q => rp_rule q = rho) stream ->
    Forall (fun q => rp_rule q = rho) acc ->
    fold_left add_pop_wide stream acc = fold_left add_pop_narrow stream acc.
Proof.
  intros rho stream.
  induction stream as [| p rest IH]; intros acc Hstream Hacc; simpl.
  - reflexivity.
  - apply Forall_cons_iff in Hstream.
    destruct Hstream as [H1 H2].
    (* FAILED STRATEGY (do not re-attempt): `inversion Hstream; subst` —
       subst rewrites rho := rp_rule p away, breaking the explicit rho
       reference below; Forall_cons_iff destructs without substituting. *)
    assert (Hgate : existsb (same_key_wide p) acc
                    = existsb (same_key_narrow p) acc).
    { apply existsb_ext_in.
      intros q Hq.
      rewrite Forall_forall in Hacc.
      exact (wide_eq_narrow_on_constant rho p q H1 (Hacc q Hq)). }
    assert (Hins : add_pop_wide acc p = add_pop_narrow acc p).
    { unfold add_pop_wide, add_pop_narrow.
      rewrite Hgate. reflexivity. }
    (* FAILED STRATEGY (do not re-attempt): `unfold add_pop_wide at 1` —
       occurrence 1 is the FUNCTION argument inside fold_left, not the
       applied insertion; rewriting the whole insertion equality avoids
       occurrence counting. *)
    rewrite Hins.
    apply IH; [exact H2 |].
    unfold add_pop_narrow.
    destruct (existsb (same_key_narrow p) acc).
    + exact Hacc.
    + apply Forall_app.
      split; [exact Hacc | constructor; [exact H1 | constructor]].
Qed.

(* The concrete two-pop instance (member identities 4 and 6 at the same
   (pos, result_w) — the mx divergence-2 shape): wide keeps both, both
   replay; narrow drops the second. *)
Theorem dedup_instance_r4_r6 :
  add_pop_wide (add_pop_wide [] (MkRecordedPop 5 9 (Some (pack 0 4))))
    (MkRecordedPop 5 9 (Some (pack 0 6)))
  = [MkRecordedPop 5 9 (Some (pack 0 4));
     MkRecordedPop 5 9 (Some (pack 0 6))]
  /\ add_pop_narrow (add_pop_narrow [] (MkRecordedPop 5 9 (Some (pack 0 4))))
       (MkRecordedPop 5 9 (Some (pack 0 6)))
     = [MkRecordedPop 5 9 (Some (pack 0 4))]
  /\ create_replay 7
       [MkRecordedPop 5 9 (Some (pack 0 4));
        MkRecordedPop 5 9 (Some (pack 0 6))]
     = [(7, MkRecordedPop 5 9 (Some (pack 0 4)));
        (7, MkRecordedPop 5 9 (Some (pack 0 6)))].
Proof. vm_compute. repeat split. Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (d) THE WEIGHT LAW TIE — the replay packing store discipline (STAGE C):
   exists ⇒ no-op; absent ⇒ intern (member key, w_one). The pop-time
   member-determined weight is NEVER overwritten and key uniqueness is
   preserved, so `packing_weight_member_determined`'s conclusion survives
   every replay.
   ═══════════════════════════════════════════════════════════════════════ *)

Definition pk_key : Type := nat * nat.  (* (rule_id, children fingerprint) *)

Definition key_eqb (a b : pk_key) : bool :=
  (fst a =? fst b) && (snd a =? snd b).

Lemma key_eqb_eq : forall a b, key_eqb a b = true <-> a = b.
Proof.
  intros [a1 a2] [b1 b2].
  unfold key_eqb. simpl.
  rewrite andb_true_iff, !Nat.eqb_eq.
  split.
  - intros [H1 H2]. subst. reflexivity.
  - intro H. inversion H; subst. split; reflexivity.
Qed.

Definition pstore : Type := list (pk_key * w).

Definition packing_exists (st : pstore) (k : pk_key) : bool :=
  existsb (fun e => key_eqb (fst e) k) st.

Fixpoint plookup (st : pstore) (k : pk_key) : option w :=
  match st with
  | [] => None
  | (k', v) :: rest => if key_eqb k' k then Some v else plookup rest k
  end.

(* The replay intern (@27129-27141): gate on existence, fall back to
   `W::one_ref()` — "the pop weight is genuinely unknowable at replay
   time", counted in replay_weight_drops. *)
Definition replay_intern (st : pstore) (k : pk_key) : pstore :=
  if packing_exists st k then st else st ++ [(k, w_one)].

(* Exists ⇒ no-op: the pop-time weight is untouched (the ⊕-corruption
   guard — "a replay re-intern with one would ⊕-corrupt it: lex-min pulls
   toward one"). *)
Theorem replay_no_overwrite :
  forall st k,
    packing_exists st k = true ->
    replay_intern st k = st.
Proof.
  intros st k H.
  unfold replay_intern. rewrite H. reflexivity.
Qed.

(* Append-only: every existing entry survives every replay (the
   no_carrier_write shape on the replay channel). *)
Theorem replay_preserves_entries :
  forall st k e, In e st -> In e (replay_intern st k).
Proof.
  intros st k e Hin.
  unfold replay_intern.
  destruct (packing_exists st k).
  - exact Hin.
  - apply in_or_app. left. exact Hin.
Qed.

Lemma plookup_app_l :
  forall st tail k v,
    plookup st k = Some v ->
    plookup (st ++ tail) k = Some v.
Proof.
  intros st tail k v.
  induction st as [| [k' v'] rest IH]; intro H; simpl in *.
  - discriminate.
  - destruct (key_eqb k' k) eqn:E.
    + exact H.
    + apply IH. exact H.
Qed.

(* Lookup stability at PRESENT keys — the member-determined weight remains
   the binding for its key. *)
Theorem replay_lookup_stable :
  forall st k k' v,
    plookup st k' = Some v ->
    plookup (replay_intern st k) k' = Some v.
Proof.
  intros st k k' v H.
  unfold replay_intern.
  destruct (packing_exists st k) eqn:E.
  - exact H.
  - apply plookup_app_l. exact H.
Qed.

Lemma packing_exists_false_lookup_none :
  forall st k,
    packing_exists st k = false ->
    plookup st k = None.
Proof.
  intros st k.
  induction st as [| [k' v'] rest IH]; intro H; simpl in *.
  - reflexivity.
  - apply orb_false_iff in H.
    destruct H as [H1 H2].
    rewrite H1.
    apply IH. exact H2.
Qed.

Lemma plookup_app_absent :
  forall st k v,
    plookup st k = None ->
    plookup (st ++ [(k, v)]) k = Some v.
Proof.
  intros st k v.
  induction st as [| [k' v'] rest IH]; intro H; simpl in *.
  - rewrite (proj2 (key_eqb_eq k k) eq_refl). reflexivity.
  - destruct (key_eqb k' k) eqn:E.
    + discriminate.
    + apply IH. exact H.
Qed.

(* The fallback intern binds the key to w_one — IDENTITY-LIKE, so it can
   never contribute cost (idlike w_one = true is definitional). *)
Theorem replay_added_weight_is_identity_like :
  forall st k,
    packing_exists st k = false ->
    plookup (replay_intern st k) k = Some w_one
    /\ idlike w_one = true.
Proof.
  intros st k H.
  unfold replay_intern. rewrite H.
  split.
  - apply plookup_app_absent.
    apply packing_exists_false_lookup_none. exact H.
  - reflexivity.
Qed.

(* Key uniqueness is preserved: a replay never creates a SECOND binding
   under an existing key (with no-overwrite above, the pop-time weight is
   the ONE binding its key ever has). *)
Definition unique_keys (st : pstore) : Prop := NoDup (map fst st).

Lemma nodup_snoc :
  forall (A : Type) (l : list A) (x : A),
    NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
  intros A l x.
  induction l as [| y rest IH]; intros Hnd Hnin; simpl.
  - constructor; [intro H; exact H | constructor].
  - inversion Hnd; subst.
    constructor.
    + intro Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | [Heq | []]].
      * contradiction.
      * apply Hnin. left. symmetry. exact Heq.
    + apply IH; [assumption |].
      intro Hin. apply Hnin. right. exact Hin.
Qed.

Theorem replay_intern_preserves_unique_keys :
  forall st k,
    unique_keys st ->
    unique_keys (replay_intern st k).
Proof.
  intros st k Hu.
  unfold replay_intern.
  destruct (packing_exists st k) eqn:E.
  - exact Hu.
  - unfold unique_keys.
    rewrite map_app. simpl.
    apply nodup_snoc; [exact Hu |].
    intro Hin.
    apply in_map_iff in Hin.
    destruct Hin as [[k' v'] [Hk Hin]].
    simpl in Hk; subst k'.
    assert (Hex : packing_exists st k = true).
    { unfold packing_exists.
      apply existsb_exists.
      exists (k, v').
      split; [exact Hin | apply key_eqb_eq; reflexivity]. }
    congruence.
Qed.

(* THE MEMBER-DETERMINATION TIE: a packing interned at pop time with the
   member-determined fold (all-identity-like pre-commit segment — the
   shipped fold_prefix_washes premise) keeps EXACTLY the post-commit-
   determined value through any replay — PureCommitFoldIntegrity's law
   transported to the replay channel. *)
Corollary replay_preserves_member_determined_weight :
  forall st k rk ch pre post,
    plookup st (rk, ch) = Some (fold_left wtimes (pre ++ post) w_one) ->
    (forall x, In x pre -> idlike x = true) ->
    post <> [] ->
    plookup (replay_intern st k) (rk, ch)
    = Some (fold_left wtimes post w_one).
Proof.
  intros st k rk ch pre post Hlk Hpre Hpost.
  rewrite (fold_prefix_washes pre post Hpre Hpost) in Hlk.
  apply replay_lookup_stable.
  exact Hlk.
Qed.

(* The replay-key member-correctness composition: when the recorded
   identity is a committed member's (the (b) chain), the key the fallback
   intern binds is member-keyed — no spine-keyed packing enters the store
   through the replay channel. *)
Theorem replay_intern_key_member_when_recorded :
  forall st ch cat rk,
    rk < SPINE_RULE_BASE ->
    forall k' v,
      In (k', v)
        (replay_intern st (replay_rule (Some (pack cat rk)) cat None, ch)) ->
      In (k', v) st \/ (fst k' = pack cat rk /\ is_spine_low16 (fst k') = false).
Proof.
  intros st ch cat rk Hlt k' v Hin.
  unfold replay_intern in Hin.
  destruct (packing_exists st (replay_rule (Some (pack cat rk)) cat None, ch))
    eqn:E.
  - left. exact Hin.
  - apply in_app_or in Hin.
    destruct Hin as [Hin | [Heq | []]].
    + left. exact Hin.
    + right.
      inversion Heq; subst.
      simpl.
      split; [reflexivity |].
      unfold is_spine_low16.
      rewrite low16_pack; [| apply member_rule_fits_u16; exact Hlt].
      apply Nat.leb_gt. exact Hlt.
Qed.

(* ── Assumption audit — every line must print "Closed under the global
      context". ── *)
Print Assumptions low16_pack.
Print Assumptions replay_prefers_recorded.
Print Assumptions replay_fallback_is_old_derivation.
Print Assumptions replay_faithful_pointwise.
Print Assumptions replay_faithful_stream.
Print Assumptions d2_records_pop_time_identity.
Print Assumptions committed_pop_replay_member_keyed.
Print Assumptions old_derivation_poisons_spine_frames.
Print Assumptions category_entry_fallback_member_class.
Print Assumptions mx_r4_replay_receipt.
Print Assumptions mx_r4_replay_via_machine.
Print Assumptions gll_pop_duplicate_idempotent.
Print Assumptions add_pop_wide_contains.
Print Assumptions add_pop_wide_idempotent.
Print Assumptions wide_key_no_loss.
Print Assumptions wide_key_both_replay.
Print Assumptions narrow_key_drops_second.
Print Assumptions narrow_gate_silences_returns.
Print Assumptions wide_gate_emits_second.
Print Assumptions pre_f52_wide_narrow_agree.
Print Assumptions dedup_instance_r4_r6.
Print Assumptions replay_no_overwrite.
Print Assumptions replay_preserves_entries.
Print Assumptions replay_lookup_stable.
Print Assumptions replay_added_weight_is_identity_like.
Print Assumptions replay_intern_preserves_unique_keys.
Print Assumptions replay_preserves_member_determined_weight.
Print Assumptions replay_intern_key_member_when_recorded.
