(*
 * RhoLoweringTotalOrRejects: the M-RHO.0.3 spec→Rholang AST lowering
 * (`rholang-codegen` `lower_language_def`) MISSES NOTHING at the codegen
 * layer — every rule of a `LanguageDef` is accounted for: each is EITHER lowered
 * to a normalized Rho contract artifact OR explicitly recorded as rejected (out
 * of the supported scalar-operator subset). No rule is ever silently dropped, and none is
 * fabricated.
 *
 * Model: a rule classifier `supported : Rule -> bool` (the Rust `lower_rule`
 * returning `Some`/`None` — `Some` iff the rule's concrete syntax is a supported
 * infix/prefix operator AND its operands are Rholang-native scalars). The Rust
 * `lower_language_def` partitions `def.terms` into `lowered` (supported) and
 * `rejected` (the rest). We model that partition as `filter` and prove:
 *   - lowering_total    : every rule is in lowered ∪ rejected (nothing dropped),
 *   - lowering_sound    : lowered ∪ rejected ⊆ the rules (nothing fabricated),
 *   - lowering_disjoint : lowered ∩ rejected = ∅ (each rule classified once),
 *   - lowering_count    : |lowered| + |rejected| = |rules| (exact partition),
 *   - lowered/rejected characterized by `supported`.
 *
 * This is the codegen-layer instance of the engine's governing "MISS NOTHING"
 * invariant (cf. dovetail NBestExtraction.v / EnumerationCompleteness.v at the
 * extraction layer): an alternative leaves only by EVIDENCE (here: an explicit
 * "no Rholang equivalent" rejection), never by silent omission.
 *
 * `Section RhoNetInstallBoundary` (Epic 4 #2011) carries the SAME invariant to the
 * σ-receiver INSTALL boundary (`rholang-codegen` `RhoNetLowered::installed_program_par`
 * → `Result<Par, RhoNetInstallError>`): the installed program admits a rule only if
 * it materialized a contract or is legitimately inline; any unlowered/deferred rule
 * (`Comm`/`NativeSystemProcess`/`Unsupported`) fails the install CLOSED — by
 * evidence (an install error, at install time), never a silent runtime no-op after
 * partial execution on the Rho machine.
 *
 * `Section CongruenceExemptInstallBoundary` (A-S5.1, leg i) refines that boundary
 * with the CONGRUENCE-EXEMPT disposition (`RhoNetLoweredRule::CongruenceExemptRewrite`):
 * a contextual rewrite whose lowering FAILS but whose premise set is non-empty and
 * all-congruence (`congruence_only_premises`, mirrored 1:1 from
 * `rholang-codegen/src/rho_net_lower.rs`) is RECORDED-exempt — it never blocks the
 * install (its context closure is carried by the locate-all/driver descent in Rho
 * and the e-graph congruence closure on host paths) — while a mixed-premise or
 * premise-free lowering failure keeps the fail-closed behavior byte-identically.
 * Headline: `install_admits_iff_no_nonexempt_unlowered`.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

Section RhoLoweringTotalOrRejects.

  Variable Rule : Type.
  (* `supported r = true` iff `lower_rule r` returns `Some` (a normalized Rho contract). *)
  Variable supported : Rule -> bool.

  (* The Rust `lower_language_def` partition, modelled as filters over `def.terms`. *)
  Definition lowered (rules : list Rule) : list Rule := filter supported rules.
  Definition rejected (rules : list Rule) : list Rule :=
    filter (fun r => negb (supported r)) rules.

  (* TOTAL: every rule is classified — lowered or rejected. Nothing dropped. *)
  Theorem lowering_total : forall rules r,
    In r rules -> In r (lowered rules) \/ In r (rejected rules).
  Proof.
    intros rules r Hin. unfold lowered, rejected.
    destruct (supported r) eqn:Hs.
    - left. apply filter_In. split; [exact Hin | exact Hs].
    - right. apply filter_In. split; [exact Hin | rewrite Hs; reflexivity].
  Qed.

  (* SOUND: only real rules are classified — nothing fabricated. *)
  Theorem lowering_sound : forall rules r,
    In r (lowered rules) \/ In r (rejected rules) -> In r rules.
  Proof.
    intros rules r [H | H]; unfold lowered, rejected in H;
      apply filter_In in H; destruct H as [Hin _]; exact Hin.
  Qed.

  (* DISJOINT: no rule is both lowered and rejected (classified exactly once). *)
  Theorem lowering_disjoint : forall rules r,
    In r (lowered rules) -> In r (rejected rules) -> False.
  Proof.
    intros rules r Hl Hr. unfold lowered, rejected in *.
    apply filter_In in Hl. apply filter_In in Hr.
    destruct Hl as [_ Hs]. destruct Hr as [_ Hns].
    rewrite Hs in Hns. simpl in Hns. discriminate Hns.
  Qed.

  (* EXACT PARTITION: the two parts' sizes sum to the whole. *)
  Theorem lowering_count : forall rules,
    length (lowered rules) + length (rejected rules) = length rules.
  Proof.
    induction rules as [| r rs IH].
    - reflexivity.
    - unfold lowered, rejected in *. simpl. destruct (supported r); simpl; lia.
  Qed.

  (* CHARACTERIZATION: lowered = exactly the supported rules; rejected = the rest. *)
  Theorem lowered_iff_supported : forall rules r,
    In r (lowered rules) <-> (In r rules /\ supported r = true).
  Proof.
    intros rules r. unfold lowered. apply filter_In.
  Qed.

  Theorem rejected_iff_unsupported : forall rules r,
    In r (rejected rules) <-> (In r rules /\ supported r = false).
  Proof.
    intros rules r. unfold rejected. rewrite filter_In.
    split; intros [Hin Hb].
    - split; [exact Hin | apply negb_true_iff in Hb; exact Hb].
    - split; [exact Hin | apply negb_true_iff; exact Hb].
  Qed.

End RhoLoweringTotalOrRejects.

Section RhoNetInstallBoundary.

  (* Epic 4 #2011: the σ-receiver INSTALL boundary
     (`RhoNetLowered::installed_program_par`) is fail-closed. A lowered rule either
     MATERIALIZES an installed contract / is legitimately inline (`blocks_install =
     false`), or it is a diagnostic / deferred family that installing would SILENTLY
     DROP (`blocks_install = true`). The Rust boundary returns `Ok` iff no rule
     blocks — otherwise `Err(RhoNetInstallError)`. This is the runtime-facing dual of
     the codegen partition above: nothing is silently dropped from the installed
     program; an incomplete lowering leaves only by EVIDENCE, at install time. *)

  Variable Rule : Type.
  (* `blocks_install r = true` iff installing would silently omit unlowered work —
     Rust `Comm | NativeSystemProcess | Unsupported`, or any recorded
     `RhoNetLoweringError`. `false` for the materialized contract families
     (`NativeFold`/`BaseRewrite`/`AcRewrite`/`CommRewrite`/`StructuralAcRewrite`/
     `NestedStructuralAcRewrite`/`ContextualRewrite`/`SubstRewrite`/
     `NativeSystemProcessRewrite`), the legitimately-inline `StructuralConstructor`/
     `CongruenceClosure`, and (A-S5.1) the recorded-exempt
     `CongruenceExemptRewrite` — see `Section CongruenceExemptInstallBoundary`. *)
  Variable blocks_install : Rule -> bool.

  (* `installed_program_par` returns Ok iff no rule blocks the install. *)
  Definition install_ok (rules : list Rule) : bool :=
    forallb (fun r => negb (blocks_install r)) rules.

  (* FAIL-CLOSED: a successful install proves NO rule was silently dropped. *)
  Theorem install_ok_drops_nothing : forall rules r,
    install_ok rules = true -> In r rules -> blocks_install r = false.
  Proof.
    intros rules r Hok Hin. unfold install_ok in Hok.
    rewrite forallb_forall in Hok. specialize (Hok r Hin).
    rewrite negb_true_iff in Hok. exact Hok.
  Qed.

  (* VISIBLE AT INSTALL TIME: any blocking rule fails the install closed — the
     error surfaces at the boundary, never after partial execution. *)
  Theorem blocking_rule_fails_install_closed : forall rules r,
    In r rules -> blocks_install r = true -> install_ok rules = false.
  Proof.
    intros rules r Hin Hblock. unfold install_ok.
    destruct (forallb (fun r => negb (blocks_install r)) rules) eqn:E; [| reflexivity].
    rewrite forallb_forall in E. specialize (E r Hin).
    rewrite Hblock in E. simpl in E. discriminate E.
  Qed.

  (* CHARACTERIZATION: install succeeds exactly when every rule is non-blocking. *)
  Theorem install_ok_iff : forall rules,
    install_ok rules = true <-> (forall r, In r rules -> blocks_install r = false).
  Proof.
    intros rules. unfold install_ok. rewrite forallb_forall.
    split; intros H r Hin; specialize (H r Hin).
    - rewrite negb_true_iff in H. exact H.
    - rewrite negb_true_iff. exact H.
  Qed.

End RhoNetInstallBoundary.

(* The Rust `Vec::is_empty` mirror — the non-empty conjunct of
   `congruence_only_premises` below. *)
Definition is_empty {A : Type} (l : list A) : bool :=
  match l with
  | [] => true
  | _ :: _ => false
  end.

Section CongruenceExemptInstallBoundary.

  (* A-S5.1 (leg i): the congruence-exempt refinement of the install boundary.

     Rust seam (`rholang-codegen/src/rho_net_lower.rs`): `lower_contextual_rewrite`
     routes BOTH of its lowering-failure sites through `exempt_or_record` — if the
     source rewrite's premises are NON-EMPTY and ALL `Premise::Congruence`
     (`congruence_only_premises`), the failure is disposed
     `RhoNetLoweredRule::CongruenceExemptRewrite { rule_id, family }` (RECORDED:
     surfaced by `RhoNetLowered::congruence_exempt_rules`; no diagnostic pushed;
     joins the `continue` arm of `installed_program_par`) — otherwise
     `record_unsupported` runs byte-identically to pre-A-S5.1 (an `Unsupported`
     rule + a fail-closed `RhoNetLoweringError`).

     Model: a rule is dispositioned by the TOTAL function `dispose` —
       - `Materialized` : the lowering produced a contract `Par`;
       - `Inline`       : legitimately par-free (`StructuralConstructor` /
                          `CongruenceClosure`);
       - `Exempt`       : lowering FAILED, premises all-congruence + non-empty
                          (the A-S5.1 disposition — recorded, never blocks);
       - `Blocked`      : lowering FAILED, premises mixed or empty (fail-closed).
     Only `Blocked` blocks the install. The side condition
     `congruence_only_premises` is mirrored 1:1 from the Rust predicate
     `!premises.is_empty() && premises.iter().all(|p| matches!(p,
     Premise::Congruence { .. }))`. *)

  Variable Rule : Type.
  Variable Premise : Type.
  (* `is_congruence p = true` iff the premise is a `Premise::Congruence { .. }`. *)
  Variable is_congruence : Premise -> bool.
  (* The rewrite's declared premise list (`RewriteRule::premises`). *)
  Variable premises : Rule -> list Premise.
  (* `materializes r = true` iff the lowering produced a contract `Par` for `r`. *)
  Variable materializes : Rule -> bool.
  (* `inline_rule r = true` iff `r` is legitimately par-free
     (`StructuralConstructor` / `CongruenceClosure`). *)
  Variable inline_rule : Rule -> bool.

  (* The SHARED exemption predicate — the 1:1 mirror of the Rust
     `congruence_only_premises` (also the A-S2 static gate's hardened exemption
     basis, `rho_net_ruleset::in_rho_static_gate`). *)
  Definition congruence_only_premises (r : Rule) : bool :=
    negb (is_empty (premises r)) && forallb is_congruence (premises r).

  (* The four A-S5.1 dispositions. TOTAL and mutually exclusive by construction
     (`dispose` is a function) — every rule is accounted for, recorded, never
     silently dropped. *)
  Inductive Disposition : Type :=
    | Materialized
    | Inline
    | Exempt
    | Blocked.

  (* The disposition seam: materialized and inline rules as before; a lowering
     FAILURE forks on the exemption predicate — exactly `exempt_or_record`. *)
  Definition dispose (r : Rule) : Disposition :=
    if materializes r then Materialized
    else if inline_rule r then Inline
    else if congruence_only_premises r then Exempt
    else Blocked.

  (* Only `Blocked` blocks: `CongruenceExemptRewrite` joins the `continue` arm of
     `installed_program_par` alongside the inline families. *)
  Definition blocks_install_leg_i (r : Rule) : bool :=
    match dispose r with
    | Blocked => true
    | Materialized | Inline | Exempt => false
    end.

  (* `installed_program_par` returns Ok iff no rule blocks (post-A-S5.1). *)
  Definition install_admits (rules : list Rule) : bool :=
    forallb (fun r => negb (blocks_install_leg_i r)) rules.

  (* HEADLINE (A-S5.1): the install admits IFF every unlowered, non-inline rule
     is congruence-exempt — an unmaterialized rule passes the boundary exactly
     when its premise set is non-empty all-congruence, and every OTHER
     unmaterialized rule still fails the install closed. *)
  Theorem install_admits_iff_no_nonexempt_unlowered : forall rules,
    install_admits rules = true <->
    (forall r, In r rules ->
       materializes r = false -> inline_rule r = false ->
       congruence_only_premises r = true).
  Proof.
    intros rules. unfold install_admits. rewrite forallb_forall.
    split.
    - intros H r Hin Hm Hi.
      specialize (H r Hin). rewrite negb_true_iff in H.
      unfold blocks_install_leg_i, dispose in H.
      rewrite Hm, Hi in H.
      destruct (congruence_only_premises r) eqn:Hc; [reflexivity | discriminate H].
    - intros H r Hin. rewrite negb_true_iff.
      unfold blocks_install_leg_i, dispose.
      destruct (materializes r) eqn:Hm; [reflexivity |].
      destruct (inline_rule r) eqn:Hi; [reflexivity |].
      rewrite (H r Hin Hm Hi). reflexivity.
  Qed.

  (* THE `all(..)` HALF OF THE HARDENING: one non-congruence premise anywhere in
     the list defeats the exemption — a mixed-premise rewrite is NEVER exempt,
     so its side condition can never be silently dropped. *)
  Theorem mixed_premise_never_exempt : forall r p,
    In p (premises r) -> is_congruence p = false ->
    congruence_only_premises r = false.
  Proof.
    intros r p Hin Hp. unfold congruence_only_premises.
    destruct (forallb is_congruence (premises r)) eqn:Hall.
    - rewrite forallb_forall in Hall. specialize (Hall p Hin).
      rewrite Hp in Hall. discriminate Hall.
    - apply andb_false_iff. right. reflexivity.
  Qed.

  (* THE NON-EMPTY HALF OF THE HARDENING: a premise-free rewrite (a base rewrite)
     is never exempt — `all` alone would be vacuously true on `[]`; the non-empty
     conjunct closes that hole. *)
  Theorem empty_premises_never_exempt : forall r,
    premises r = [] -> congruence_only_premises r = false.
  Proof.
    intros r Heq. unfold congruence_only_premises. rewrite Heq. reflexivity.
  Qed.

  (* Composition: an unlowered, non-inline rule with a mixed premise set FAILS
     the install closed — the pre-A-S5.1 behavior, preserved exactly. *)
  Theorem mixed_premise_unlowered_blocks : forall r p,
    materializes r = false -> inline_rule r = false ->
    In p (premises r) -> is_congruence p = false ->
    blocks_install_leg_i r = true.
  Proof.
    intros r p Hm Hi Hin Hp.
    unfold blocks_install_leg_i, dispose.
    rewrite Hm, Hi, (mixed_premise_never_exempt r p Hin Hp).
    reflexivity.
  Qed.

  (* RECORDED, AND ONLY AT THE SEAM: the `Exempt` disposition occurs exactly for
     an unmaterialized, non-inline rule whose premises pass the hardened
     predicate — an exemption always carries its evidence. *)
  Theorem exempt_only_at_the_seam : forall r,
    dispose r = Exempt ->
    materializes r = false /\ inline_rule r = false /\
    congruence_only_premises r = true.
  Proof.
    intros r. unfold dispose.
    destruct (materializes r) eqn:Hm.
    - intros H. discriminate H.
    - destruct (inline_rule r) eqn:Hi.
      + intros H. discriminate H.
      + destruct (congruence_only_premises r) eqn:Hc.
        * intros _. repeat split.
        * intros H. discriminate H.
  Qed.

  (* An exempt rule never blocks the install (the `continue`-arm membership). *)
  Theorem exempt_never_blocks : forall r,
    dispose r = Exempt -> blocks_install_leg_i r = false.
  Proof.
    intros r H. unfold blocks_install_leg_i. rewrite H. reflexivity.
  Qed.

  (* TOTALITY (recorded-never-silent): every rule receives exactly one of the
     four dispositions — nothing leaves the partition. *)
  Theorem dispose_total : forall r,
    dispose r = Materialized \/ dispose r = Inline \/
    dispose r = Exempt \/ dispose r = Blocked.
  Proof.
    intros r. unfold dispose.
    destruct (materializes r); [left; reflexivity |].
    destruct (inline_rule r); [right; left; reflexivity |].
    destruct (congruence_only_premises r);
      [right; right; left; reflexivity | right; right; right; reflexivity].
  Qed.

  (* CONSERVATIVITY: the A-S5.1 boundary only ever WIDENS admission (install
     results move `Err → Ok` only): anything it blocks, the pre-leg-i boundary
     (`unmaterialized ∧ non-inline` blocks) blocked too. *)
  Theorem exemption_never_blocks_previously_admitted : forall r,
    blocks_install_leg_i r = true ->
    materializes r = false /\ inline_rule r = false.
  Proof.
    intros r. unfold blocks_install_leg_i, dispose.
    destruct (materializes r) eqn:Hm; [intros H; discriminate H |].
    destruct (inline_rule r) eqn:Hi; [intros H; discriminate H |].
    destruct (congruence_only_premises r);
      [intros H; discriminate H | intros _; split; reflexivity].
  Qed.

  (* BYTE-IDENTITY OFF THE SEAM: for every rule OUTSIDE the exemption predicate,
     the leg-i boundary computes exactly the pre-A-S5.1 blocking condition. *)
  Theorem non_congruence_only_behavior_unchanged : forall r,
    congruence_only_premises r = false ->
    blocks_install_leg_i r = negb (materializes r) && negb (inline_rule r).
  Proof.
    intros r Hc. unfold blocks_install_leg_i, dispose. rewrite Hc.
    destruct (materializes r); [reflexivity |].
    destruct (inline_rule r); reflexivity.
  Qed.

  (* The leg-i boundary is the SAME `install_ok` shape as `Section
     RhoNetInstallBoundary`, instantiated at `blocks_install_leg_i` — so its
     fail-closed theorems (`install_ok_drops_nothing`,
     `blocking_rule_fails_install_closed`, `install_ok_iff`) transfer verbatim. *)
  Theorem install_admits_is_install_ok : forall rules,
    install_admits rules = install_ok Rule blocks_install_leg_i rules.
  Proof. reflexivity. Qed.

  (* Transfer instance: a successful post-A-S5.1 install still proves NO rule
     was silently dropped — the Epic-4 #2011 invariant survives the refinement. *)
  Corollary install_admits_drops_nothing : forall rules r,
    install_admits rules = true -> In r rules -> blocks_install_leg_i r = false.
  Proof.
    intros rules r H Hin.
    rewrite install_admits_is_install_ok in H.
    exact (install_ok_drops_nothing Rule blocks_install_leg_i rules r H Hin).
  Qed.

End CongruenceExemptInstallBoundary.

Print Assumptions install_ok_drops_nothing.
Print Assumptions blocking_rule_fails_install_closed.
Print Assumptions install_ok_iff.
Print Assumptions install_admits_iff_no_nonexempt_unlowered.
Print Assumptions mixed_premise_never_exempt.
Print Assumptions empty_premises_never_exempt.
Print Assumptions mixed_premise_unlowered_blocks.
Print Assumptions exempt_only_at_the_seam.
Print Assumptions exempt_never_blocks.
Print Assumptions dispose_total.
Print Assumptions exemption_never_blocks_previously_admitted.
Print Assumptions non_congruence_only_behavior_unchanged.
Print Assumptions install_admits_drops_nothing.
