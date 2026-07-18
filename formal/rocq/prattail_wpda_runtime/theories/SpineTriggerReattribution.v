(*
 * SpineTriggerReattribution: S1-FACTORING FV-3a (classic-arm claim
 * re-attribution) — extends the model of TriggerOwnershipLeadGate.v
 * (shipped, untouched) with the S1 `group_owner_match` disjunct landed at
 * prattail/src/wpda_walker.rs @38160-38205 (HEAD ff5209ee):
 *
 *   owner_match       := owner_cat = fire_cat  &&  owner_rule = fire_rule
 *   group_owner_match := owner_cat = fire_cat
 *                        && trigger_spine_owner(fire_cat, fire_rule)
 *                           = Some owner_rule            (@38172-38176)
 *   pos_gated         := at_frame_start
 *                        && (has_lead_trigger || killswitch)  (@38196-38204)
 *   claim''           := owner_match || group_owner_match || pos_gated
 *                                                            (@38205)
 *
 * `trigger_spine_owner` is the grammar-derived engine table
 * (macros/src/gen/runtime/wpda_codegen/factoring.rs @1346-1357: one row
 * per GROUPED member mapping it to its group's SPINE_ID; trait default
 * None @wpda_walker.rs:1735). It is modeled here as the first-match
 * lookup over a per-category partition (spine_id, member list) — the SAME
 * partition FV-1 (TrieLeafBijection.bucket_partition_disjoint) proves
 * disjoint, which is the well-formedness premise used below.
 *
 * THE THEOREMS (per the F3 plan §3 as amended by §RED-TEAM item 4):
 *   (a) COMPLETENESS — a member firing over its own group's spine-owned
 *       trigger claims via group_owner_match ALONE (owner_match is false
 *       on a spine-owned node — spine ids are synthetic; pos_match is an
 *       incidental second net and may be false: AV3, Replace mints a NEW
 *       GSS node);
 *   (b1) NON-THEFT VIA group_owner_match ONLY — a rule outside the group
 *       cannot claim THROUGH group_owner_match (injectivity of the owner
 *       rows over spine_members). Stated exactly at the gom channel: the
 *       pre-existing pos_match fallback legitimately admits genuine-
 *       prefix non-members (owner-blind, stance-identical — shipped
 *       behavior, TriggerOwnershipLeadGate theorem (3)); "non-theft" is
 *       NOT claimed for that channel (red-team F4 correction);
 *   (b2) the SHIPPED PHANTOM stays refuted under claim'' — both readings:
 *       (i) an UNFACTORED operand-leading rule (owner lookup None — e.g.
 *       the Name-led PPersistOutput2Plus family, rules 4-9, F5 territory)
 *       in the phantom configuration (foreign owner, positioned, no lead
 *       trigger, no killswitch) is refused; (ii) the rhocalc instance:
 *       rule 24 = PPersistOutputShort2Plus (Short-group member) firing
 *       against a QUOTED-spine-owned trigger has
 *       trigger_spine_owner(Proc, 24) = Some SHORT_SPINE <> QUOTED_SPINE;
 *   (c) CONSERVATIVITY BRIDGE — with group_owner_match's channel closed
 *       (owner lookup None: every unfactored rule; equivalently the OFF
 *       stance's EMPTY partition) claim'' IS the shipped claim_new
 *       (TriggerOwnershipLeadGate), and with the killswitch it is
 *       claim_old — so all six shipped lead-gate theorems transport.
 *
 * The concrete partition instance is the rhocalc Proc-@ cohort pinned by
 * F0 (factoring.rs test rhocalc_proc_at_cohort_pins_three_groups_6_3_6):
 * Nil = 0xF800 {10,11,15,16,20,21}, Quoted = 0xF801 {12,17,22},
 * Short = 0xF802 {13,14,18,19,23,24}.
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
From PrattailWpdaRuntime Require Import TriggerOwnershipLeadGate.
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════
   The owner table as a first-match lookup over a partition.
   ═══════════════════════════════════════════════════════════════════════ *)

(* One category's factored partition: (spine_id, member rule indices). *)
Definition partition : Type := list (nat * list nat).

Fixpoint owner_of (p : partition) (r : nat) : option nat :=
  match p with
  | [] => None
  | (sid, ms) :: rest =>
      if existsb (Nat.eqb r) ms then Some sid else owner_of rest r
  end.

(* Well-formedness — exactly what FV-1's bucket partition provides:
   distinct spine ids and pairwise-disjoint member lists. *)
Definition wf_partition (p : partition) : Prop :=
  NoDup (map fst p)
  /\ (forall s1 ms1 s2 ms2 r,
        In (s1, ms1) p -> In (s2, ms2) p ->
        In r ms1 -> In r ms2 -> s1 = s2).

(* ── owner_of soundness/completeness under wf ── *)

Lemma owner_of_sound :
  forall p r s,
    owner_of p r = Some s ->
    exists ms, In (s, ms) p /\ In r ms.
Proof.
  induction p as [| [sid ms] rest IH]; intros r s H; simpl in H.
  - discriminate.
  - destruct (existsb (Nat.eqb r) ms) eqn:E.
    + inversion H; subst.
      apply existsb_exists in E.
      destruct E as [x [HinX Heq]].
      apply Nat.eqb_eq in Heq; subst x.
      exists ms. split; [left; reflexivity | exact HinX].
    + destruct (IH r s H) as [ms' [Hin1 Hin2]].
      exists ms'. split; [right; exact Hin1 | exact Hin2].
Qed.

Lemma owner_of_complete :
  forall p r s ms,
    wf_partition p ->
    In (s, ms) p ->
    In r ms ->
    owner_of p r = Some s.
Proof.
  induction p as [| [sid ms0] rest IH]; intros r s ms Hwf HinP HinM.
  - simpl in HinP. contradiction.
  - destruct Hwf as [Hnd Hdisj].
    simpl.
    destruct (existsb (Nat.eqb r) ms0) eqn:E.
    + (* r is in the head group: disjointness pins s = sid *)
      apply existsb_exists in E.
      destruct E as [x [HinX Heq]].
      apply Nat.eqb_eq in Heq; subst x.
      f_equal.
      symmetry.
      exact (Hdisj s ms sid ms0 r HinP (or_introl eq_refl) HinM HinX).
    + (* r not in the head group: (s, ms) must live in the tail *)
      destruct HinP as [Heq | HinP'].
      * inversion Heq; subst sid ms0.
        exfalso.
        assert (Hex : existsb (Nat.eqb r) ms = true).
        { apply existsb_exists. exists r. split; [exact HinM |].
          apply Nat.eqb_refl. }
        congruence.
      * eapply IH; [| exact HinP' | exact HinM].
        split.
        -- inversion Hnd; assumption.
        -- intros s1 ms1 s2 ms2 r0 H1 H2 H3 H4.
           eapply (Hdisj s1 ms1 s2 ms2 r0);
             [right; exact H1 | right; exact H2 | exact H3 | exact H4].
Qed.

(* Non-membership: the owner table maps a rule ONLY to its own group's
   spine id (injectivity over spine_members). *)
Lemma owner_of_only_own_group :
  forall p r s ms,
    wf_partition p ->
    In (s, ms) p ->
    ~ In r ms ->
    owner_of p r <> Some s.
Proof.
  intros p r s ms Hwf HinP HnotIn Hown.
  destruct (owner_of_sound p r s Hown) as [ms' [HinP' HinM']].
  destruct Hwf as [Hnd Hdisj].
  (* NoDup on fst forces ms' = ms for the same key s *)
  assert (Hms : ms' = ms).
  { clear Hdisj Hown HnotIn HinM'.
    induction p as [| [j js] rest IH].
    - simpl in HinP. contradiction.
    - simpl in *.
      inversion Hnd; subst.
      destruct HinP as [HeqP | HinPr]; destruct HinP' as [HeqP' | HinP'r].
      + inversion HeqP; inversion HeqP'; subst. reflexivity.
      + inversion HeqP; subst.
        exfalso. apply H1.
        apply in_map with (f := fst) in HinP'r. exact HinP'r.
      + inversion HeqP'; subst.
        exfalso. apply H1.
        apply in_map with (f := fst) in HinPr. exact HinPr.
      + exact (IH H2 HinPr HinP'r). }
  subst ms'. contradiction.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   The landed gate (wpda_walker.rs @38160-38205, field-faithful).
   ═══════════════════════════════════════════════════════════════════════ *)

Definition owner_match_b (owner_cat fire_cat owner_rule fire_rule : nat)
  : bool :=
  (owner_cat =? fire_cat) && (owner_rule =? fire_rule).

Definition group_owner_match_b (p : partition)
  (owner_cat fire_cat owner_rule fire_rule : nat) : bool :=
  (owner_cat =? fire_cat)
  && match owner_of p fire_rule with
     | Some s => s =? owner_rule
     | None => false
     end.

Definition pos_gated_b (at_frame_start has_lead_trigger killswitch : bool)
  : bool :=
  at_frame_start && (has_lead_trigger || killswitch).

Definition claim2 (p : partition)
  (owner_cat fire_cat owner_rule fire_rule : nat)
  (at_frame_start has_lead_trigger killswitch : bool) : bool :=
  owner_match_b owner_cat fire_cat owner_rule fire_rule
  || group_owner_match_b p owner_cat fire_cat owner_rule fire_rule
  || pos_gated_b at_frame_start has_lead_trigger killswitch.

(* ═══════════════════════════════════════════════════════════════════════
   (a) COMPLETENESS — a member fires over its own group's spine-owned
   trigger via group_owner_match ALONE (any pos/lead/killswitch state,
   including all-false; owner_match false because the spine id is
   synthetic, s <> r).
   ═══════════════════════════════════════════════════════════════════════ *)

Theorem spine_claim_completeness :
  forall p c s ms r pm hlt ks,
    wf_partition p ->
    In (s, ms) p ->
    In r ms ->
    claim2 p c c s r pm hlt ks = true.
Proof.
  intros p c s ms r pm hlt ks Hwf HinP HinM.
  unfold claim2, group_owner_match_b.
  rewrite (owner_of_complete p r s ms Hwf HinP HinM).
  rewrite !Nat.eqb_refl. simpl.
  rewrite orb_true_r. reflexivity.
Qed.

(* The claim is via gom specifically: with a synthetic spine id (s <> r)
   and no positional net, owner_match and pos_gated are BOTH false yet
   the claim still succeeds. *)
Theorem spine_claim_via_gom_only :
  forall p c s ms r,
    wf_partition p ->
    In (s, ms) p ->
    In r ms ->
    s <> r ->
    owner_match_b c c s r = false
    /\ pos_gated_b false false false = false
    /\ claim2 p c c s r false false false = true.
Proof.
  intros p c s ms r Hwf HinP HinM Hneq.
  split; [| split].
  - unfold owner_match_b.
    rewrite Nat.eqb_refl. simpl.
    apply Nat.eqb_neq. exact Hneq.
  - reflexivity.
  - apply spine_claim_completeness with (ms := ms); assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (b1) NON-THEFT VIA group_owner_match — a rule OUTSIDE the group never
   claims through the gom channel (the only S1-added channel).
   ═══════════════════════════════════════════════════════════════════════ *)

Theorem gom_non_theft :
  forall p c s ms r,
    wf_partition p ->
    In (s, ms) p ->
    ~ In r ms ->
    group_owner_match_b p c c s r = false.
Proof.
  intros p c s ms r Hwf HinP HnotIn.
  unfold group_owner_match_b.
  destruct (owner_of p r) as [s' |] eqn:E.
  - rewrite Nat.eqb_refl. simpl.
    apply Nat.eqb_neq.
    intro Heq. subst s'.
    exact (owner_of_only_own_group p r s ms Hwf HinP HnotIn E).
  - now rewrite andb_false_r.
Qed.

(* Cross-category triggers never match the gom channel either
   (the owner_cat = fire_cat conjunct, @38172). *)
Theorem gom_cat_fenced :
  forall p oc fc s r,
    oc <> fc ->
    group_owner_match_b p oc fc s r = false.
Proof.
  intros p oc fc s r Hneq.
  unfold group_owner_match_b.
  apply Nat.eqb_neq in Hneq. rewrite Hneq. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (c) CONSERVATIVITY BRIDGE — gom's channel closed ⇒ claim'' IS the
   shipped predicate; the six TriggerOwnershipLeadGate theorems transport.
   ═══════════════════════════════════════════════════════════════════════ *)

(* An unfactored firing rule (no owner row — the trait default None,
   wpda_walker.rs @1735) reduces claim'' to the shipped claim_new. *)
Theorem bridge_unfactored_is_claim_new :
  forall p oc fc s r pm hlt,
    owner_of p r = None ->
    claim2 p oc fc s r pm hlt false
    = claim_new (owner_match_b oc fc s r) pm hlt.
Proof.
  intros p oc fc s r pm hlt Hnone.
  unfold claim2, group_owner_match_b, pos_gated_b, claim_new.
  rewrite Hnone. rewrite andb_false_r, orb_false_r, orb_false_r.
  destruct pm; destruct hlt; reflexivity.
Qed.

(* The OFF stance globally: the EMPTY partition (no groups emitted) makes
   claim'' equal claim_new for EVERY rule. *)
Theorem bridge_off_stance :
  forall oc fc s r pm hlt,
    claim2 [] oc fc s r pm hlt false
    = claim_new (owner_match_b oc fc s r) pm hlt.
Proof.
  intros. apply bridge_unfactored_is_claim_new. reflexivity.
Qed.

(* The killswitch (PRATTAIL_NO_TRIGGER_LEAD_GATE) restores claim_old on
   the unfactored channel — exactly TriggerOwnershipLeadGate theorem (5)
   transported through the bridge. *)
Theorem bridge_killswitch_is_claim_old :
  forall p oc fc s r pm hlt,
    owner_of p r = None ->
    claim2 p oc fc s r pm hlt true
    = claim_old (owner_match_b oc fc s r) pm.
Proof.
  intros p oc fc s r pm hlt Hnone.
  unfold claim2, group_owner_match_b, pos_gated_b, claim_old.
  rewrite Hnone. rewrite andb_false_r, orb_false_r.
  destruct pm; destruct hlt; reflexivity.
Qed.

(* Transported refinement (TriggerOwnershipLeadGate theorem (1)): an
   unfactored claim'' still never claims more than the pre-lead-gate
   predicate. *)
Theorem bridge_refines_old :
  forall p oc fc s r pm hlt,
    owner_of p r = None ->
    claim2 p oc fc s r pm hlt false = true ->
    claim_old (owner_match_b oc fc s r) pm = true.
Proof.
  intros p oc fc s r pm hlt Hnone H.
  rewrite (bridge_unfactored_is_claim_new p oc fc s r pm hlt Hnone) in H.
  exact (claim_new_refines_old _ _ _ H).
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (b2) THE SHIPPED PHANTOM STAYS REFUTED — abstract + concrete.
   ═══════════════════════════════════════════════════════════════════════ *)

(* Abstract: the phantom configuration (foreign owner: om computes false;
   positioned: pm true; operand-leading: hlt false; no killswitch) with an
   UNFACTORED firing rule is refused by claim''. *)
Theorem phantom_refuted_unfactored :
  forall p oc fc s r,
    owner_of p r = None ->
    owner_match_b oc fc s r = false ->
    claim2 p oc fc s r true false false = false.
Proof.
  intros p oc fc s r Hnone Hom.
  rewrite (bridge_unfactored_is_claim_new p oc fc s r true false Hnone).
  unfold claim_new. rewrite Hom. reflexivity.
Qed.

(* ── The rhocalc Proc-@ instance (F0 pins: 3 groups 6/3/6) ── *)

Definition NIL_SPINE : nat := 63488.     (* 0xF800 *)
Definition QUOTED_SPINE : nat := 63489.  (* 0xF801 *)
Definition SHORT_SPINE : nat := 63490.   (* 0xF802 *)

Definition rho_proc_at_partition : partition :=
  [ (NIL_SPINE,    [10; 11; 15; 16; 20; 21]);
    (QUOTED_SPINE, [12; 17; 22]);
    (SHORT_SPINE,  [13; 14; 18; 19; 23; 24]) ].

(* Well-formedness of the instance, by decidable computation lifted to the
   Prop-level wf (the disjointness quantifier is discharged by enumerating
   the 15 concrete membership cases through owner_of determinism). *)
Lemma rho_partition_nodup : NoDup (map fst rho_proc_at_partition).
Proof.
  simpl.
  constructor.
  - intro H.
    destruct H as [H | [H | []]]; vm_compute in H; discriminate H.
  - constructor.
    + intro H.
      destruct H as [H | []]; vm_compute in H; discriminate H.
    + constructor; [intro H; exact H | constructor].
Qed.

Lemma rho_partition_wf : wf_partition rho_proc_at_partition.
Proof.
  split; [exact rho_partition_nodup |].
  intros s1 ms1 s2 ms2 r H1 H2 H3 H4.
  simpl in H1, H2.
  destruct H1 as [E1 | [E1 | [E1 | []]]];
    destruct H2 as [E2 | [E2 | [E2 | []]]];
    inversion E1; inversion E2; subst; try reflexivity;
    simpl in H3, H4; intuition lia.
Qed.

(* trigger_spine_owner(Proc, PPersistOutputShort2Plus = 24)
   = Some SHORT_SPINE (the generated row). *)
Theorem rho_owner_of_24 :
  owner_of rho_proc_at_partition 24 = Some SHORT_SPINE.
Proof. vm_compute. reflexivity. Qed.

(* Firing rule 24 against a QUOTED-spine-owned trigger cannot claim via
   gom (Some SHORT_SPINE <> QUOTED_SPINE), and in the full phantom
   configuration (foreign owner, positioned, operand-leading tail beyond
   its own trigger, no killswitch) the whole claim'' refuses. *)
Theorem rho_phantom_instance_refuted :
  group_owner_match_b rho_proc_at_partition 0 0 QUOTED_SPINE 24 = false
  /\ claim2 rho_proc_at_partition 0 0 QUOTED_SPINE 24 true false false
     = false.
Proof. vm_compute. split; reflexivity. Qed.

(* The positive control: the SAME rule over its OWN group's trigger claims
   with everything else false. *)
Theorem rho_own_spine_claims :
  claim2 rho_proc_at_partition 0 0 SHORT_SPINE 24 false false false = true.
Proof. vm_compute. reflexivity. Qed.

(* The unfactored-rule instance: a Name-led send (rules 4-9 — F5
   territory, e.g. rule 5) has NO owner row; the original lead-gate
   phantom configuration stays refuted through the bridge. *)
Theorem rho_unfactored_phantom_refuted :
  owner_of rho_proc_at_partition 5 = None
  /\ claim2 rho_proc_at_partition 0 0 QUOTED_SPINE 5 true false false
     = false.
Proof. vm_compute. split; reflexivity. Qed.

(* ── Assumption audit — every line must print "Closed under the global
      context". ── *)
Print Assumptions owner_of_sound.
Print Assumptions owner_of_complete.
Print Assumptions owner_of_only_own_group.
Print Assumptions spine_claim_completeness.
Print Assumptions spine_claim_via_gom_only.
Print Assumptions gom_non_theft.
Print Assumptions gom_cat_fenced.
Print Assumptions bridge_unfactored_is_claim_new.
Print Assumptions bridge_off_stance.
Print Assumptions bridge_killswitch_is_claim_old.
Print Assumptions bridge_refines_old.
Print Assumptions phantom_refuted_unfactored.
Print Assumptions rho_partition_wf.
Print Assumptions rho_owner_of_24.
Print Assumptions rho_phantom_instance_refuted.
Print Assumptions rho_own_spine_claims.
Print Assumptions rho_unfactored_phantom_refuted.
