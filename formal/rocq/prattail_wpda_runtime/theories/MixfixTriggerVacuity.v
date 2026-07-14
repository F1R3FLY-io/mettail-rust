(*
 * MixfixTriggerVacuity: S1-FACTORING F5-2 FV-3a extension (plan
 * f5_mixfix_cohorts_plan.md §5 "FV-3a ... extends with mixfix owner rows
 * into the injectivity theorem PLUS the new MixfixTriggerVacuity lemma" +
 * the A-M5 lex-alt group-entry identity bundle), over the SHIPPED
 * SpineTriggerReattribution model (imported verbatim, never restated).
 *
 * WHAT IS PROVED:
 *   (1) THE ENLARGED OWNER DOMAIN — the F5-2 `trigger_spine_owner` table
 *       gains the two mixfix rows ((Proc, 4/6/8) -> 0xF803,
 *       (Proc, 5/7/9) -> 0xF804; factoring.rs: mixfix rows join the
 *       owner/members streams — emitted for table symmetry although
 *       unreachable at the gate). The enlarged rhocalc Proc partition
 *       (3 prefix groups + 2 mixfix cohorts) is well-formed, owner-row
 *       injectivity holds over it (each member maps to EXACTLY its own
 *       cohort's spine id), the shipped non-theft theorems transport,
 *       and the FV-3a (b2) phantom refutation SURVIVES the enlargement —
 *       rule 5's refutation now flows through owner MISMATCH
 *       (Some 0xF804 <> QUOTED_SPINE) instead of owner-None.
 *   (2) MIXFIX-TRIGGER VACUITY — no branch the mixfix surface emits
 *       interns a trigger node (classic: plain `Push` fork branches carry
 *       `trigger_terminal = None`, wpda_walker.rs @17345-17362 — only
 *       `PushWithTriggerTerminal` mirrors; pure: the Push fork-branch arm
 *       descends with `SPPF_ID_NONE` @31038+; the prelude's divergence
 *       branches are ConsumeAtAndReplace commits + Advance descents; the
 *       singleton fast-path is `TriggerMode::Discard`; the OFF per-member
 *       fan is plain Push too — the vacuity is STANCE-UNIFORM). Hence the
 *       claim gate's candidate set on a mixfix fire is EMPTY and claim''
 *       is EXTENSIONALLY the shipped claim there — conservativity for
 *       free; the mixfix owner rows are unreachable at the gate.
 *   (3) THE OPERAND-LEADING GATE FACT (A-M5's A7 flip) — mixfix members
 *       are operand-leading, so `rule_has_leading_structural_trigger` has
 *       NO mixfix spine rows (all-false); with `has_lead_trigger = false`
 *       and no killswitch the positional net `pos_gated_b` is closed on
 *       this surface regardless of position.
 *   (4) THE A-M5 LEX-ALT GROUP-ENTRY IDENTITY — the `__s1_spine_weight_
 *       rule` redirect (forks.rs: BOTH MixfixFirstTrigger sites route the
 *       `lex_w_alt` weight rule AND the `LexAltMixfixOp.rule_idx`
 *       action-kind field through ONE redirect): spine ids map to the MIN
 *       member (0xF803 -> 4, 0xF804 -> 5 — vm-pinned, AV5-mirrored,
 *       min-member = fold_min of the cohort rules, and a REAL member of
 *       the cohort); every id below the spine space is the IDENTITY
 *       (byte-identity for ungrouped languages/rules); and the group
 *       entry's l_bp = cohort min mirrors the lex-fork site's FLOOR-ONLY
 *       admission predicate exactly (site admission at the min ⟺ every
 *       member's own floor admission — MixfixSpineCommit's
 *       full_admission_iff through the kind_dispatch group entry).
 *
 * HONEST SCOPE: static gate/table-level statements. The runtime side —
 * that mixfix fires actually present zero trigger candidates — is the
 * walker receipt pair cited above plus the F5-2 battery (H9 = 0; the
 * fire collects LHS + operands through the marker frame, the trigger
 * token is span-consumed only, plan §3(c)).
 *
 * ── CROSS-REFERENCE TABLE (model ↔ Rust; commit 8df26fbe) ──
 *
 *   enlarged partition       ↔ factoring.rs spine_members/owner rows:
 *                              prefix pins (Nil 0xF800 {10,11,15,16,20,21},
 *                              Quoted 0xF801 {12,17,22}, Short 0xF802
 *                              {13,14,18,19,23,24} — the F0 test pin) +
 *                              the F5-2 pins `(0,63491)=>&[4,6,8]` /
 *                              `(0,63492)=>&[5,7,9]` (@5234-5236)
 *   `branch_trigger`         ↔ classic fork apply: plain Push branches
 *                              never intern a trigger (@17345-17362);
 *                              pure Push arm SPPF_ID_NONE; the emitted
 *                              mixfix fan is ForkActionKind::Push
 *                              (factoring.rs @2636-2637), the prelude
 *                              divergences are ConsumeAtAndReplace +
 *                              Advance (@2852-2875), the singleton
 *                              fast-path is ConsumeAndPush{Discard}
 *                              (engine_impl tail dispatch)
 *   A7 absence               ↔ the committed pin: `lead_arms` contain
 *                              neither 63491 nor 63492 (@5247-5249);
 *                              members are operand-leading (the shipped
 *                              lead-gate doc cites PPersistOutput2Plus)
 *   `redirect`               ↔ forks.rs `__s1_spine_weight_rule` (emitted
 *                              only for grouped languages); the committed
 *                              pins: weights `(0,63491)=>4` (@5243), the
 *                              4x infix-site redirects covering BOTH the
 *                              weight and the LexAltMixfixOp.rule_idx
 *                              action-kind channels (2 sites x 2 fields)
 *   floor-only admission     ↔ kind_dispatch.rs group entries: ONE spine
 *                              entry per cohort at l_bp = cohort min
 *                              (l_bp >= cur_bp is the site's whole
 *                              admission predicate, forks.rs @2190)
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
From PrattailWpdaRuntime Require Import SpineTriggerReattribution.
From PrattailWpdaRuntime Require Import PureCommitFoldIntegrity.
From PrattailWpdaRuntime Require Import MixfixSpineCommit.
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════
   (1) THE ENLARGED OWNER DOMAIN.
   ═══════════════════════════════════════════════════════════════════════ *)

Definition BANG_SPINE : nat := 63491.      (* 0xF803 *)
Definition BANGBANG_SPINE : nat := 63492.  (* 0xF804 *)

Definition rho_proc_partition_f52 : partition :=
  [ (NIL_SPINE,      [10; 11; 15; 16; 20; 21]);
    (QUOTED_SPINE,   [12; 17; 22]);
    (SHORT_SPINE,    [13; 14; 18; 19; 23; 24]);
    (BANG_SPINE,     [4; 6; 8]);
    (BANGBANG_SPINE, [5; 7; 9]) ].

Lemma rho_f52_partition_nodup : NoDup (map fst rho_proc_partition_f52).
Proof.
  simpl.
  constructor.
  - intro H.
    destruct H as [H | [H | [H | [H | []]]]]; vm_compute in H; discriminate H.
  - constructor.
    + intro H.
      destruct H as [H | [H | [H | []]]]; vm_compute in H; discriminate H.
    + constructor.
      * intro H.
        destruct H as [H | [H | []]]; vm_compute in H; discriminate H.
      * constructor.
        -- intro H.
           destruct H as [H | []]; vm_compute in H; discriminate H.
        -- constructor; [intro H; exact H | constructor].
Qed.

Lemma rho_f52_partition_wf : wf_partition rho_proc_partition_f52.
Proof.
  split; [exact rho_f52_partition_nodup |].
  intros s1 ms1 s2 ms2 r H1 H2 H3 H4.
  simpl in H1, H2.
  destruct H1 as [E1 | [E1 | [E1 | [E1 | [E1 | []]]]]];
    destruct H2 as [E2 | [E2 | [E2 | [E2 | [E2 | []]]]]];
    inversion E1; inversion E2; subst; try reflexivity;
    simpl in H3, H4; intuition lia.
Qed.

(* Owner-row injectivity over the ENLARGED domain — each mixfix member maps
   to exactly its own cohort's spine id (the generated
   `trigger_spine_owner` rows, emitted for table symmetry). *)
Theorem rho_f52_owner_rows :
  owner_of rho_proc_partition_f52 4 = Some BANG_SPINE
  /\ owner_of rho_proc_partition_f52 6 = Some BANG_SPINE
  /\ owner_of rho_proc_partition_f52 8 = Some BANG_SPINE
  /\ owner_of rho_proc_partition_f52 5 = Some BANGBANG_SPINE
  /\ owner_of rho_proc_partition_f52 7 = Some BANGBANG_SPINE
  /\ owner_of rho_proc_partition_f52 9 = Some BANGBANG_SPINE.
Proof. vm_compute. repeat split. Qed.

(* The prefix rows are UNCHANGED by the enlargement (rule 24's Short row —
   the shipped (b2) witness — survives verbatim). *)
Theorem rho_f52_prefix_rows_unchanged :
  owner_of rho_proc_partition_f52 24 = Some SHORT_SPINE
  /\ owner_of rho_proc_partition_f52 12 = Some QUOTED_SPINE
  /\ owner_of rho_proc_partition_f52 10 = Some NIL_SPINE.
Proof. vm_compute. repeat split. Qed.

(* Non-theft transported: a rule outside a cohort never claims through the
   gom channel over the enlarged table (the generic theorem + the wf
   instance). Concrete cross-cohort pin: rule 4 (a `!` member) cannot
   claim a `!!`-spine-owned trigger. *)
Theorem rho_f52_gom_non_theft_generic :
  forall c r,
    ~ In r [4; 6; 8] ->
    group_owner_match_b rho_proc_partition_f52 c c BANG_SPINE r = false.
Proof.
  intros c r Hnot.
  apply (gom_non_theft rho_proc_partition_f52 c BANG_SPINE [4; 6; 8] r
           rho_f52_partition_wf).
  - right. right. right. left. reflexivity.
  - exact Hnot.
Qed.

Theorem rho_f52_cross_cohort_refused :
  group_owner_match_b rho_proc_partition_f52 0 0 BANGBANG_SPINE 4 = false
  /\ group_owner_match_b rho_proc_partition_f52 0 0 BANG_SPINE 5 = false.
Proof. vm_compute. split; reflexivity. Qed.

(* Completeness transported (table symmetry; UNREACHABLE at the gate by
   the vacuity below — the row exists and is correct anyway): a member
   over its own cohort's spine id claims with everything else false. *)
Theorem rho_f52_own_spine_claims :
  claim2 rho_proc_partition_f52 0 0 BANG_SPINE 4 false false false = true
  /\ claim2 rho_proc_partition_f52 0 0 BANGBANG_SPINE 7 false false false
     = true.
Proof. vm_compute. split; reflexivity. Qed.

(* THE (b2) PHANTOM SURVIVES THE ENLARGEMENT: the shipped instance used
   rule 5 with owner-None (rho_unfactored_phantom_refuted, the F1-era
   partition); under the F5-2 table rule 5 HAS an owner row, and the
   refutation now flows through owner MISMATCH — the phantom configuration
   (foreign owner, positioned, operand-leading, no killswitch) is still
   refused. *)
Theorem rho_f52_phantom_still_refuted :
  owner_of rho_proc_partition_f52 5 = Some BANGBANG_SPINE
  /\ group_owner_match_b rho_proc_partition_f52 0 0 QUOTED_SPINE 5 = false
  /\ claim2 rho_proc_partition_f52 0 0 QUOTED_SPINE 5 true false false
     = false.
Proof. vm_compute. repeat split. Qed.

(* The mixfix spine ids are DISJOINT from the prefix spine ids and from
   every member rule (the A9 ordinal-continuation receipt at the owner
   table: 0xF800-0xF802 prefix, 0xF803-0xF804 mixfix). *)
Theorem rho_f52_spine_id_disjointness :
  (NIL_SPINE <? QUOTED_SPINE) = true
  /\ (QUOTED_SPINE <? SHORT_SPINE) = true
  /\ (SHORT_SPINE <? BANG_SPINE) = true
  /\ (BANG_SPINE <? BANGBANG_SPINE) = true
  /\ (SPINE_RULE_BASE <=? NIL_SPINE) = true.
Proof. vm_compute. repeat split. Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (2) MIXFIX-TRIGGER VACUITY — the mixfix surface interns no trigger
   nodes, hence claim'' ≡ the shipped claim there (conservativity for
   free).
   ═══════════════════════════════════════════════════════════════════════ *)

(* The fork-branch kinds the mixfix surface emits, by trigger provenance:
   only PushWithTriggerTerminal ever mirrors a trigger node (classic
   @17348-17362); everything else — plain Push (the ON spine fan AND the
   OFF per-member fan), the prelude's ConsumeAtAndReplace commits and
   Advance descents, and the singleton fast-path's Discard — interns
   nothing. *)
Inductive fan_branch : Type :=
| FbPushPlain                  (* trigger_terminal = None / SPPF_ID_NONE *)
| FbPushWithTrigger (t : nat)  (* the ONLY trigger-interning kind *)
| FbCARBranch                  (* ConsumeAtAndReplace (commit) *)
| FbAdvanceBranch              (* Advance (operand descent) *)
| FbConsumeDiscard.            (* ConsumeAndPush { TriggerMode::Discard } *)

Definition branch_trigger (b : fan_branch) : option nat :=
  match b with
  | FbPushWithTrigger t => Some t
  | _ => None
  end.

Definition triggers_of (bs : list fan_branch) : list nat :=
  flat_map (fun b => match branch_trigger b with
                     | Some t => [t]
                     | None => []
                     end) bs.

(* The emitted mixfix branch inventory (§2.2/§2.3 of the plan, the ledger
   "emitted ON shape"): the ON fan (one plain Push), divergence 1
   (descent-Advance FIRST + commit CAR), divergence 2 (two commit CARs),
   the singleton fast-path, and the OFF per-member fan (three plain
   Pushes) — the vacuity is stance-uniform. *)
Definition mixfix_on_fan : list fan_branch := [FbPushPlain].
Definition mixfix_div1 : list fan_branch := [FbAdvanceBranch; FbCARBranch].
Definition mixfix_div2 : list fan_branch := [FbCARBranch; FbCARBranch].
Definition mixfix_singleton_path : list fan_branch := [FbConsumeDiscard].
Definition mixfix_off_fan : list fan_branch :=
  [FbPushPlain; FbPushPlain; FbPushPlain].

Definition mixfix_surface : list fan_branch :=
  mixfix_on_fan ++ mixfix_div1 ++ mixfix_div2
  ++ mixfix_singleton_path ++ mixfix_off_fan.

Theorem mixfix_surface_interns_no_trigger :
  triggers_of mixfix_surface = [].
Proof. vm_compute. reflexivity. Qed.

(* Generic: a branch list free of PushWithTriggerTerminal contributes an
   EMPTY trigger candidate set. *)
Theorem no_trigger_kind_no_candidates :
  forall bs,
    Forall (fun b => branch_trigger b = None) bs ->
    triggers_of bs = [].
Proof.
  intros bs Hall.
  induction bs as [| b rest IH]; simpl.
  - reflexivity.
  - apply Forall_cons_iff in Hall.
    destruct Hall as [Hb Hrest].
    rewrite Hb.
    apply IH. exact Hrest.
Qed.

(* THE VACUITY: the claim gate filters trigger candidates; over an EMPTY
   candidate set EVERY claim predicate yields the same (empty) fire set —
   claim'' and the shipped claim (and claim_old, and anything else) are
   EXTENSIONALLY EQUAL on the mixfix surface. *)
Definition gate_fires (claim : nat -> bool) (cands : list nat) : list nat :=
  filter claim cands.

Theorem claim_gate_vacuous_on_empty :
  forall c1 c2 : nat -> bool,
    gate_fires c1 [] = gate_fires c2 [].
Proof. reflexivity. Qed.

Corollary mixfix_claim2_equals_shipped_claim :
  forall p oc fc s r pm hlt ks,
    gate_fires (fun _ => claim2 p oc fc s r pm hlt ks)
      (triggers_of mixfix_surface)
    = gate_fires (fun _ => claim_new (owner_match_b oc fc s r) pm hlt)
        (triggers_of mixfix_surface).
Proof.
  intros p oc fc s r pm hlt ks.
  rewrite mixfix_surface_interns_no_trigger.
  apply claim_gate_vacuous_on_empty.
Qed.

(* The mixfix owner rows are therefore UNREACHABLE at the gate: adding
   them changes no gate outcome on the mixfix surface (both tables filter
   an empty candidate set), while the prefix surface — where triggers DO
   exist — sees IDENTICAL owner rows in both tables
   (rho_f52_prefix_rows_unchanged). *)
Corollary mixfix_owner_rows_gate_inert :
  forall oc fc s r pm hlt ks,
    gate_fires
      (fun _ => claim2 rho_proc_partition_f52 oc fc s r pm hlt ks)
      (triggers_of mixfix_surface)
    = gate_fires
        (fun _ => claim2 rho_proc_at_partition oc fc s r pm hlt ks)
        (triggers_of mixfix_surface).
Proof.
  intros oc fc s r pm hlt ks.
  rewrite mixfix_surface_interns_no_trigger.
  apply claim_gate_vacuous_on_empty.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (3) THE OPERAND-LEADING GATE FACT (A-M5's A7 flip: mixfix spine rows
   are all-FALSE/omitted from `rule_has_leading_structural_trigger` — the
   committed pin asserts neither 63491 nor 63492 appears in lead_arms).
   With has_lead_trigger = false and no killswitch, the positional net is
   closed at ANY position — pos_match cannot mis-claim on this surface
   (the shipped lead-gate doc cites exactly this family,
   PPersistOutput2Plus).
   ═══════════════════════════════════════════════════════════════════════ *)

Theorem operand_leading_positional_net_closed :
  forall pm, pos_gated_b pm false false = false.
Proof.
  intro pm.
  unfold pos_gated_b.
  apply andb_false_r.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (4) THE A-M5 LEX-ALT GROUP-ENTRY IDENTITY — `__s1_spine_weight_rule`.
   ═══════════════════════════════════════════════════════════════════════ *)

(* The redirect table: spine id -> MIN member. First-match lookup;
   identity off the table. *)
Definition spine_min_table : Type := list (nat * nat).

Fixpoint redirect (tbl : spine_min_table) (r : nat) : nat :=
  match tbl with
  | [] => r
  | (sid, m) :: rest => if r =? sid then m else redirect rest r
  end.

Definition rho_spine_min : spine_min_table :=
  [ (BANG_SPINE, 4); (BANGBANG_SPINE, 5) ].

(* Identity below the spine space: every REAL rule id passes through
   untouched — the emitted redirect changes nothing for ungrouped rules
   (byte-identity for ungrouped languages, which don't even emit the
   helper). *)
Theorem redirect_member_identity :
  forall tbl r,
    Forall (fun e => SPINE_RULE_BASE <= fst e) tbl ->
    r < SPINE_RULE_BASE ->
    redirect tbl r = r.
Proof.
  intros tbl r Hall Hr.
  induction tbl as [| [sid m] rest IH]; simpl.
  - reflexivity.
  - apply Forall_cons_iff in Hall.
    destruct Hall as [Hsid Hrest].
    simpl in Hsid.
    destruct (r =? sid) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + apply IH. exact Hrest.
Qed.

Lemma rho_spine_min_keys_in_spine_space :
  Forall (fun e => SPINE_RULE_BASE <= fst e) rho_spine_min.
Proof.
  repeat apply Forall_cons; try apply Forall_nil;
    simpl; apply Nat.leb_le; vm_compute; reflexivity.
Qed.

Theorem rho_redirect_identity_on_members :
  forall r, r < SPINE_RULE_BASE -> redirect rho_spine_min r = r.
Proof.
  intros r Hr.
  apply redirect_member_identity;
    [exact rho_spine_min_keys_in_spine_space | exact Hr].
Qed.

(* The spine redirects, vm-pinned: 0xF803 -> 4, 0xF804 -> 5 (the committed
   weight pin `(0,63491)=>4u16` + the 4x infix-site redirects). *)
Theorem rho_redirect_spine_pins :
  redirect rho_spine_min BANG_SPINE = 4
  /\ redirect rho_spine_min BANGBANG_SPINE = 5.
Proof. vm_compute. split; reflexivity. Qed.

(* AV5-mirrored: the redirected value IS the cohort MIN member and a REAL
   member of the cohort (never the spine id — the identity-channel fix
   covers BOTH consumers, the lex_w_alt weight rule and the
   LexAltMixfixOp.rule_idx action-kind field, because both consume THIS
   one redirect). *)
Theorem rho_redirect_is_min_member :
  redirect rho_spine_min BANG_SPINE = fold_min 4 [6; 8]
  /\ In (redirect rho_spine_min BANG_SPINE) [4; 6; 8]
  /\ redirect rho_spine_min BANGBANG_SPINE = fold_min 5 [7; 9]
  /\ In (redirect rho_spine_min BANGBANG_SPINE) [5; 7; 9].
Proof.
  split; [vm_compute; reflexivity |].
  split; [left; vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |].
  left. vm_compute. reflexivity.
Qed.

(* Both identity channels receive the SAME value — one redirect, two
   consumers (the A-M5 fix's shape: fixing only the weight channel would
   leave the action-kind field spine-stamped; the emitted code routes
   both through `__s1_spine_weight_rule`). *)
Definition lex_alt_entry_channels (tbl : spine_min_table) (r : nat)
  : nat * nat :=
  (redirect tbl r, redirect tbl r).  (* (weight rule, action rule_idx) *)

Theorem lex_alt_channels_agree :
  forall tbl r,
    fst (lex_alt_entry_channels tbl r) = snd (lex_alt_entry_channels tbl r).
Proof. reflexivity. Qed.

(* The FLOOR-ONLY admission mirror (the lex-fork sites' whole admission
   predicate is `l_bp >= cur_bp`, forks.rs @2190): the group entry carries
   l_bp = cohort min, so the site admits the spine entry iff EVERY
   member's own entry would be admitted — MixfixSpineCommit's
   full_admission_iff through the kind_dispatch group entry. No
   floor-blocked member's lex-alt route is ever resurrected. *)
Theorem lex_alt_group_entry_gate :
  forall cur,
    cur <= fold_min 2 [6; 10]
    <-> (cur <= 2 /\ Forall (fun l => cur <= l) [6; 10]).
Proof.
  intro cur.
  apply full_admission_iff.
Qed.

Theorem lex_alt_group_entry_gate_bb :
  forall cur,
    cur <= fold_min 4 [8; 12]
    <-> (cur <= 4 /\ Forall (fun l => cur <= l) [8; 12]).
Proof.
  intro cur.
  apply full_admission_iff.
Qed.

(* ── Assumption audit — every line must print "Closed under the global
      context". ── *)
Print Assumptions rho_f52_partition_nodup.
Print Assumptions rho_f52_partition_wf.
Print Assumptions rho_f52_owner_rows.
Print Assumptions rho_f52_prefix_rows_unchanged.
Print Assumptions rho_f52_gom_non_theft_generic.
Print Assumptions rho_f52_cross_cohort_refused.
Print Assumptions rho_f52_own_spine_claims.
Print Assumptions rho_f52_phantom_still_refuted.
Print Assumptions rho_f52_spine_id_disjointness.
Print Assumptions mixfix_surface_interns_no_trigger.
Print Assumptions no_trigger_kind_no_candidates.
Print Assumptions claim_gate_vacuous_on_empty.
Print Assumptions mixfix_claim2_equals_shipped_claim.
Print Assumptions mixfix_owner_rows_gate_inert.
Print Assumptions operand_leading_positional_net_closed.
Print Assumptions redirect_member_identity.
Print Assumptions rho_redirect_identity_on_members.
Print Assumptions rho_redirect_spine_pins.
Print Assumptions rho_redirect_is_min_member.
Print Assumptions lex_alt_channels_agree.
Print Assumptions lex_alt_group_entry_gate.
Print Assumptions lex_alt_group_entry_gate_bb.
