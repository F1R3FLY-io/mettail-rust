(*
 * CostTraceFundingTransport: abstract transport of an already checked
 * CheckedTraceV2 normalization receipt to complete host-demand rosters.
 *
 * This is not a proof of the Rust kernel, the projection verifier, or native
 * supply.  In particular, roster_complete and proof_verified are inputs that
 * only the respective trusted finite verifiers may mint.  No Axioms/Admitted.
 *)

From Stdlib Require Import Bool Lists.List PeanoNat Lia.
From RhoBridge Require Import FiniteCostGradeFold CostGradeFundingBoundary.
Import ListNotations.

Section CostGradeTraceTransport.

  Variable exact_grade_key : Grade -> nat.

  Record TraceOwner := {
    owner_language : nat;
    owner_theory : nat;
    owner_base_image : nat;
    owner_cost_image : nat;
    owner_grade_sort : nat;
    owner_projected_image : nat;
    owner_relation : nat;
    owner_host_handle : nat
  }.

  (* One source-graded proof can itself have multiple distinct host
     interpretations.  This is a nested roster, not one chosen host result
     per normalization hop.  The candidate bytes and receipts are retained by
     prepare_host_demand_roster from CostGradeFundingBoundary. *)
  Record TraceProof := {
    proof_identity : nat;
    proof_grade : Grade;
    proof_base_image : nat;
    proof_cost_image : nat;
    proof_grade_sort : nat;
    proof_binding : DemandBinding;
    proof_candidates : list DemandCandidate;
    proof_roster_complete : bool
  }.

  Record TraceHop := {
    hop_before : nat;
    hop_after : nat;
    hop_charged_work : nat;
    hop_exhaustive_proofs : list TraceProof;
    hop_selected_proof : nat;
    hop_roster_complete : bool
  }.

  Record CheckedTrace := {
    trace_language : nat;
    trace_theory : nat;
    trace_base_image : nat;
    trace_cost_image : nat;
    trace_grade_sort : nat;
    trace_input : nat;
    trace_output : nat;
    trace_entry_proof_identity : nat;
    trace_entry_grade : Grade;
    trace_final_grade : Grade;
    trace_hops : list TraceHop
  }.

  Definition trace_owner_checked (owner : TraceOwner) (trace : CheckedTrace)
      : bool :=
    (Nat.eqb (trace_language trace) (owner_language owner) &&
     Nat.eqb (trace_theory trace) (owner_theory owner) &&
     Nat.eqb (trace_base_image trace) (owner_base_image owner) &&
     Nat.eqb (trace_cost_image trace) (owner_cost_image owner) &&
     Nat.eqb (trace_grade_sort trace) (owner_grade_sort owner))%bool.

  Definition proof_owner_checked (owner : TraceOwner) (proof : TraceProof)
      : bool :=
    (Nat.eqb (proof_base_image proof) (owner_base_image owner) &&
     Nat.eqb (proof_cost_image proof) (owner_cost_image owner) &&
     Nat.eqb (proof_grade_sort proof) (owner_grade_sort owner) &&
     Nat.eqb (demand_base_image (proof_binding proof))
             (owner_base_image owner) &&
     Nat.eqb (demand_projected_image (proof_binding proof))
             (owner_projected_image owner) &&
     Nat.eqb (demand_relation (proof_binding proof))
             (owner_relation owner) &&
     Nat.eqb (demand_host_handle (proof_binding proof))
             (owner_host_handle owner) &&
     Nat.eqb (demand_grade_key (proof_binding proof))
             (exact_grade_key (proof_grade proof)))%bool.

  Record ProofCertificate := {
    certified_proof_identity : nat;
    certified_grade : Grade;
    certified_candidates : list (nat * nat)
  }.

  Definition prepare_proof (owner : TraceOwner) (proof : TraceProof)
      (work_budget : nat) : option ProofCertificate :=
    if proof_owner_checked owner proof then
      option_map (fun outputs =>
        {| certified_proof_identity := proof_identity proof;
           certified_grade := proof_grade proof;
           certified_candidates := outputs |})
        (prepare_host_demand_roster (proof_binding proof)
          (proof_candidates proof) work_budget (proof_roster_complete proof))
    else None.

  Lemma prepare_proof_exact_fields : forall owner proof budget certificate,
      prepare_proof owner proof budget = Some certificate ->
      proof_owner_checked owner proof = true /\
      certified_proof_identity certificate = proof_identity proof /\
      certified_grade certificate = proof_grade proof /\
      certified_candidates certificate = map candidate_output (proof_candidates proof) /\
      proof_roster_complete proof = true /\
      proof_candidates proof <> [] /\
      Forall (fun candidate => candidate_checks (proof_binding proof) candidate = true)
        (proof_candidates proof).
  Proof.
    intros owner proof budget certificate H. unfold prepare_proof in H.
    destruct (proof_owner_checked owner proof) eqn:Howner; [|discriminate].
    destruct (prepare_host_demand_roster (proof_binding proof)
      (proof_candidates proof) budget (proof_roster_complete proof))
      as [outputs|] eqn:Houtputs; [|discriminate].
    simpl in H. inversion H; subst certificate; simpl.
    apply prepared_roster_exact_length_order_receipts_and_meter in Houtputs
      as [Hcomplete [Hnonempty [Hout [_ [Hchecks _]]]]].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact Hout|]. split; [exact Hcomplete|]. auto.
  Qed.

  Fixpoint prepare_proofs (owner : TraceOwner) (proofs : list TraceProof)
      (work_budget : nat) : option (list ProofCertificate) :=
    match proofs with
    | [] => Some []
    | proof :: rest =>
        match prepare_proof owner proof work_budget with
        | None => None
        | Some prepared =>
            option_map (cons prepared) (prepare_proofs owner rest work_budget)
        end
    end.

  Record HopCertificate := {
    certified_before : nat;
    certified_after : nat;
    certified_charged_work : nat;
    certified_selected_proof : nat;
    certified_selected_grade : Grade;
    certified_proofs : list ProofCertificate
  }.

  Definition prepare_hop (owner : TraceOwner) (expected_before : nat)
      (hop : TraceHop) (work_budget : nat) : option HopCertificate :=
    if (hop_roster_complete hop &&
        Nat.eqb (hop_before hop) expected_before)%bool then
      match nth_error (hop_exhaustive_proofs hop) (hop_selected_proof hop) with
      | None => None
      | Some selected =>
          match prepare_proofs owner (hop_exhaustive_proofs hop) work_budget with
          | None => None
          | Some prepared =>
              Some {| certified_before := hop_before hop;
                      certified_after := hop_after hop;
                      certified_charged_work := hop_charged_work hop;
                      certified_selected_proof := hop_selected_proof hop;
                      certified_selected_grade := proof_grade selected;
                      certified_proofs := prepared |}
          end
      end
    else None.

  Fixpoint prepare_hops (owner : TraceOwner) (before : nat)
      (accumulated : Grade) (hops : list TraceHop) (work_budget : nat)
      : option (Grade * list HopCertificate) :=
    match hops with
    | [] => Some (accumulated, [])
    | hop :: rest =>
        match prepare_hop owner before hop work_budget with
        | None => None
        | Some head =>
            match prepare_hops owner (hop_after hop)
                    (GradeProduct accumulated (certified_selected_grade head))
                    rest work_budget with
            | None => None
            | Some (final_grade, tail) => Some (final_grade, head :: tail)
            end
        end
    end.

  (* `charged_work` is retained exactly as a kernel receipt field.  The
     abstract transport charge below is the sum of all candidate-roster work;
     actual Rust ReflectedCodecBudget charges include bytes and allocations
     and require a separate source-level refinement test. *)
  Definition proof_roster_work (proof : TraceProof) : nat :=
    roster_work (proof_candidates proof).

  Definition hop_rosters_work (hop : TraceHop) : nat :=
    fold_right (fun proof total => proof_roster_work proof + total) 0
      (hop_exhaustive_proofs hop).

  Definition trace_rosters_work (trace : CheckedTrace) : nat :=
    fold_right (fun hop total => hop_rosters_work hop + total) 0
      (trace_hops trace).

  Fixpoint end_key (before : nat) (hops : list TraceHop) : nat :=
    match hops with
    | [] => before
    | hop :: rest => end_key (hop_after hop) rest
    end.

  Lemma grade_eq_dec : forall left right : Grade, {left = right} + {left <> right}.
  Proof. decide equality; apply Nat.eq_dec. Defined.

  Definition grade_eqb (left right : Grade) : bool :=
    if grade_eq_dec left right then true else false.

  Lemma grade_eqb_eq : forall left right,
      grade_eqb left right = true <-> left = right.
  Proof.
    intros left right. unfold grade_eqb.
    destruct (grade_eq_dec left right); split; intros H;
      try reflexivity; try discriminate; congruence.
  Qed.

  Definition certify_trace (owner : TraceOwner) (trace : CheckedTrace)
      (work_budget : nat) (cancelled : bool)
      : option (list HopCertificate) :=
    if (trace_owner_checked owner trace &&
        Nat.leb (trace_rosters_work trace) work_budget &&
        negb cancelled &&
        Nat.eqb (end_key (trace_input trace) (trace_hops trace))
                (trace_output trace))%bool then
      match prepare_hops owner (trace_input trace)
              (trace_entry_grade trace) (trace_hops trace) work_budget with
      | None => None
      | Some (folded_grade, certificates) =>
          if grade_eqb folded_grade (trace_final_grade trace)
          then Some certificates else None
      end
    else None.

  Lemma prepare_proofs_exact_order :
    forall owner proofs budget prepared,
      prepare_proofs owner proofs budget = Some prepared ->
      length prepared = length proofs /\
      map certified_grade prepared = map proof_grade proofs /\
      Forall2 (fun proof certificate =>
                 prepare_proof owner proof budget = Some certificate)
              proofs prepared.
  Proof.
    intros owner proofs. induction proofs as [|proof rest IH];
      intros budget prepared Hprepared.
    - simpl in Hprepared. inversion Hprepared; subst.
      repeat split; constructor.
    - simpl in Hprepared.
      destruct (prepare_proof owner proof budget) as [head|] eqn:Hhead;
        [|discriminate].
      destruct (prepare_proofs owner rest budget) as [tail|] eqn:Htail;
        [|discriminate].
      simpl in Hprepared. inversion Hprepared; subst prepared.
      destruct (IH _ _ Htail) as [Hlen [Hgrades Hrel]].
      assert (Hgrade : certified_grade head = proof_grade proof).
      { unfold prepare_proof in Hhead.
      destruct (proof_owner_checked owner proof); [|discriminate].
      destruct (prepare_host_demand_roster (proof_binding proof)
                  (proof_candidates proof) budget (proof_roster_complete proof))
        as [outputs|] eqn:Houtputs;
        [|discriminate].
      simpl in Hhead. inversion Hhead. reflexivity. }
      split; [simpl; congruence |]. split; [simpl; congruence |].
      constructor; assumption.
  Qed.

  Lemma prepare_hop_exact_roster :
    forall owner before hop budget certificate,
      prepare_hop owner before hop budget = Some certificate ->
      hop_roster_complete hop = true /\
      hop_before hop = before /\
      certified_before certificate = hop_before hop /\
      certified_after certificate = hop_after hop /\
      certified_charged_work certificate = hop_charged_work hop /\
      length (certified_proofs certificate) =
        length (hop_exhaustive_proofs hop) /\
      map certified_grade (certified_proofs certificate) =
        map proof_grade (hop_exhaustive_proofs hop) /\
      exists selected,
        nth_error (hop_exhaustive_proofs hop) (hop_selected_proof hop) =
          Some selected /\
        certified_selected_grade certificate = proof_grade selected.
  Proof.
    intros owner before hop budget certificate H.
    unfold prepare_hop in H.
    destruct (hop_roster_complete hop && Nat.eqb (hop_before hop) before)%bool
      eqn:Hhead; [|discriminate].
    destruct (nth_error (hop_exhaustive_proofs hop) (hop_selected_proof hop))
      as [selected|] eqn:Hselected; [|discriminate].
    destruct (prepare_proofs owner (hop_exhaustive_proofs hop) budget)
      as [prepared|] eqn:Hprepared; [|discriminate].
    inversion H; subst certificate.
    apply andb_true_iff in Hhead as [Hcomplete Hbefore].
    apply Nat.eqb_eq in Hbefore.
    apply prepare_proofs_exact_order in Hprepared as [Hlen [Hgrades _]].
    repeat split; try assumption; try reflexivity; eauto.
  Qed.

  Lemma prepare_proofs_identity_order : forall owner proofs budget prepared,
      prepare_proofs owner proofs budget = Some prepared ->
      map certified_proof_identity prepared = map proof_identity proofs.
  Proof.
    intros owner proofs. induction proofs as [|proof rest IH];
      intros budget prepared H.
    - inversion H. reflexivity.
    - simpl in H.
      destruct (prepare_proof owner proof budget) as [head|] eqn:Hhead;
        [|discriminate].
      destruct (prepare_proofs owner rest budget) as [tail|] eqn:Htail;
        [|discriminate].
      inversion H; subst prepared; simpl.
      apply prepare_proof_exact_fields in Hhead as [_ [Hidentity _]].
      rewrite Hidentity, (IH _ _ Htail). reflexivity.
  Qed.

  Lemma prepare_hop_preserves_proof_identity : forall owner before hop budget certificate,
      prepare_hop owner before hop budget = Some certificate ->
      certified_selected_proof certificate = hop_selected_proof hop /\
      map certified_proof_identity (certified_proofs certificate) =
        map proof_identity (hop_exhaustive_proofs hop) /\
      Forall2 (fun proof prepared => prepare_proof owner proof budget = Some prepared)
        (hop_exhaustive_proofs hop) (certified_proofs certificate).
  Proof.
    intros owner before hop budget certificate H. unfold prepare_hop in H.
    destruct (hop_roster_complete hop && Nat.eqb (hop_before hop) before)%bool;
      [|discriminate].
    destruct (nth_error (hop_exhaustive_proofs hop) (hop_selected_proof hop));
      [|discriminate].
    destruct (prepare_proofs owner (hop_exhaustive_proofs hop) budget)
      as [prepared|] eqn:Hprepared; [|discriminate].
    inversion H; subst certificate; simpl.
    split; [reflexivity|]. split.
    - exact (prepare_proofs_identity_order owner _ budget _ Hprepared).
    - apply prepare_proofs_exact_order in Hprepared. tauto.
  Qed.

  Lemma prepare_hops_exact_fold : forall owner hops before entry budget folded certificates,
      prepare_hops owner before entry hops budget = Some (folded, certificates) ->
      folded = fold_left
        (fun accumulated hop => GradeProduct accumulated (certified_selected_grade hop))
        certificates entry /\
      Forall2 (fun hop certificate =>
        prepare_hop owner (hop_before hop) hop budget = Some certificate)
        hops certificates.
  Proof.
    intros owner hops. induction hops as [|hop rest IH];
      intros before entry budget folded certificates H.
    - inversion H; subst. split; [reflexivity |constructor].
    - simpl in H.
      destruct (prepare_hop owner before hop budget) as [head|] eqn:Hhead;
        [|discriminate].
      destruct (prepare_hops owner (hop_after hop)
        (GradeProduct entry (certified_selected_grade head)) rest budget)
        as [[tail_grade tail]|] eqn:Htail; [|discriminate].
      inversion H; subst folded certificates.
      destruct (IH _ _ _ _ _ Htail) as [Hfold Hrest].
      split; [exact Hfold |constructor; [|exact Hrest]].
      pose proof Hhead as Hchecked.
      apply prepare_hop_exact_roster in Hchecked as [_ [Hbefore _]].
      now rewrite Hbefore.
  Qed.

  Lemma prepare_hops_exact_order :
    forall owner before entry hops budget folded certificates,
      prepare_hops owner before entry hops budget =
        Some (folded, certificates) ->
      length certificates = length hops /\
      map certified_before certificates = map hop_before hops /\
      map certified_after certificates = map hop_after hops /\
      map certified_charged_work certificates = map hop_charged_work hops.
  Proof.
    intros owner before entry hops. revert before entry.
    induction hops as [|hop rest IH];
      intros before entry budget folded certificates H.
    - simpl in H. inversion H; subst. repeat split; reflexivity.
    - simpl in H.
      destruct (prepare_hop owner before hop budget) as [head|] eqn:Hhead;
        [|discriminate].
      destruct (prepare_hops owner (hop_after hop)
                  (GradeProduct entry (certified_selected_grade head))
                  rest budget) as [[tail_grade tail]|] eqn:Htail;
        [|discriminate].
      inversion H; subst folded certificates.
      apply prepare_hop_exact_roster in Hhead
        as [_ [_ [Hbefore [Hafter [Hwork _]]]]].
      destruct (IH _ _ _ _ _ Htail) as [Hlen [Hbs [Has Hws]]].
      repeat split; simpl; congruence.
  Qed.

  Theorem certified_trace_preserves_order_and_multiplicity :
    forall owner trace budget cancelled certificates,
      certify_trace owner trace budget cancelled = Some certificates ->
      length certificates = length (trace_hops trace) /\
      map certified_before certificates = map hop_before (trace_hops trace) /\
      map certified_after certificates = map hop_after (trace_hops trace) /\
      map certified_charged_work certificates =
        map hop_charged_work (trace_hops trace).
  Proof.
    intros owner trace budget cancelled certificates H.
    unfold certify_trace in H.
    destruct (trace_owner_checked owner trace &&
      Nat.leb (trace_rosters_work trace) budget && negb cancelled &&
      Nat.eqb (end_key (trace_input trace) (trace_hops trace))
              (trace_output trace))%bool; [|discriminate].
    destruct (prepare_hops owner (trace_input trace) (trace_entry_grade trace)
                (trace_hops trace) budget) as [[folded prepared]|] eqn:Hprepared;
      [|discriminate].
    destruct (grade_eqb folded (trace_final_grade trace)); [|discriminate].
    inversion H; subst certificates.
    eapply prepare_hops_exact_order; eassumption.
  Qed.

  Theorem cancellation_has_no_partial_certificate :
    forall owner trace budget,
      certify_trace owner trace budget true = None.
  Proof.
    intros owner trace budget. unfold certify_trace.
    destruct (trace_owner_checked owner trace);
      destruct (Nat.leb (trace_rosters_work trace) budget); reflexivity.
  Qed.

  Theorem certified_trace_has_complete_checked_proofs_and_exact_fold :
    forall owner trace budget cancelled certificates,
      certify_trace owner trace budget cancelled = Some certificates ->
      trace_owner_checked owner trace = true /\
      cancelled = false /\ trace_rosters_work trace <= budget /\
      trace_final_grade trace = fold_left
        (fun accumulated hop => GradeProduct accumulated (certified_selected_grade hop))
        certificates (trace_entry_grade trace) /\
      Forall2 (fun hop certificate =>
        prepare_hop owner (hop_before hop) hop budget = Some certificate)
        (trace_hops trace) certificates.
  Proof.
    intros owner trace budget cancelled certificates H. unfold certify_trace in H.
    destruct (trace_owner_checked owner trace &&
      Nat.leb (trace_rosters_work trace) budget && negb cancelled &&
      Nat.eqb (end_key (trace_input trace) (trace_hops trace)) (trace_output trace))%bool
      eqn:Hgate; [|discriminate].
    destruct (prepare_hops owner (trace_input trace) (trace_entry_grade trace)
      (trace_hops trace) budget) as [[folded prepared]|] eqn:Hprepared;
      [|discriminate].
    destruct (grade_eqb folded (trace_final_grade trace)) eqn:Hgrade;
      [|discriminate].
    inversion H; subst certificates.
    repeat rewrite andb_true_iff in Hgate.
    destruct Hgate as [[[Howner Hbudget] Hcancelled] _].
    apply Nat.leb_le in Hbudget. apply negb_true_iff in Hcancelled.
    apply grade_eqb_eq in Hgrade.
    apply prepare_hops_exact_fold in Hprepared as [Hfold Hall].
    rewrite <- Hgrade. auto.
  Qed.

  Theorem insufficient_cumulative_work_has_no_certificate :
    forall owner trace budget cancelled,
      budget < trace_rosters_work trace ->
      certify_trace owner trace budget cancelled = None.
  Proof.
    intros owner trace budget cancelled Htoo_small.
    unfold certify_trace.
    apply Nat.leb_gt in Htoo_small. rewrite Htoo_small.
    destruct (trace_owner_checked owner trace); reflexivity.
  Qed.

  Theorem zero_step_preserves_entry_without_minting_unit :
    forall owner trace budget,
      trace_hops trace = [] ->
      trace_owner_checked owner trace = true ->
      trace_output trace = trace_input trace ->
      trace_final_grade trace = trace_entry_grade trace ->
      certify_trace owner trace budget false = Some [].
  Proof.
    intros owner trace budget Hhops Howner Houtput Hgrade.
    unfold certify_trace, trace_rosters_work. rewrite Hhops, Howner, Houtput, Hgrade.
    simpl. rewrite Nat.eqb_refl.
    unfold grade_eqb. destruct (grade_eq_dec (trace_entry_grade trace)
                                             (trace_entry_grade trace));
      [reflexivity|congruence].
  Qed.

  Theorem wrong_trace_cost_digest_refuses :
    forall owner trace budget cancelled,
      trace_cost_image trace <> owner_cost_image owner ->
      certify_trace owner trace budget cancelled = None.
  Proof.
    intros owner trace budget cancelled Hwrong.
    unfold certify_trace, trace_owner_checked.
    apply Nat.eqb_neq in Hwrong. rewrite Hwrong.
    repeat destruct (Nat.eqb _ _); reflexivity.
  Qed.

  Theorem wrong_trace_grade_sort_refuses :
    forall owner trace budget cancelled,
      trace_grade_sort trace <> owner_grade_sort owner ->
      certify_trace owner trace budget cancelled = None.
  Proof.
    intros owner trace budget cancelled Hwrong.
    unfold certify_trace, trace_owner_checked.
    apply Nat.eqb_neq in Hwrong. rewrite Hwrong.
    repeat destruct (Nat.eqb _ _); reflexivity.
  Qed.

  Theorem exact_grade_product_retains_noncommutative_receipt_order :
    forall entry first second,
      first <> second ->
      GradeProduct (GradeProduct entry first) second <>
      GradeProduct (GradeProduct entry second) first.
  Proof.
    intros entry first second Hdistinct Hequal.
    inversion Hequal. congruence.
  Qed.

  Record TraceCertificate := {
    certified_entry : ProofCertificate;
    certified_normalization : list HopCertificate
  }.

  Definition certify_trace_with_entry (owner : TraceOwner) (trace : CheckedTrace)
      (entry : option TraceProof) (work_budget : nat) (cancelled : bool)
      : option TraceCertificate :=
    match entry with
    | None => None
    | Some proof =>
        if (Nat.eqb (proof_identity proof) (trace_entry_proof_identity trace) &&
            grade_eqb (proof_grade proof) (trace_entry_grade trace) &&
            Nat.leb (proof_roster_work proof + trace_rosters_work trace) work_budget)%bool then
          match prepare_proof owner proof work_budget with
          | None => None
          | Some prepared =>
              option_map (fun hops =>
                {| certified_entry := prepared; certified_normalization := hops |})
                (certify_trace owner trace work_budget cancelled)
          end
        else None
    end.

  Theorem certified_trace_with_entry_has_complete_evidence :
    forall owner trace entry budget cancelled certificate,
      certify_trace_with_entry owner trace entry budget cancelled = Some certificate ->
      exists proof,
        entry = Some proof /\
        proof_identity proof = trace_entry_proof_identity trace /\
        proof_grade proof = trace_entry_grade trace /\
        proof_roster_work proof + trace_rosters_work trace <= budget /\
        prepare_proof owner proof budget = Some (certified_entry certificate) /\
        certify_trace owner trace budget cancelled =
          Some (certified_normalization certificate).
  Proof.
    intros owner trace entry budget cancelled certificate H.
    unfold certify_trace_with_entry in H.
    destruct entry as [proof|]; [|discriminate].
    destruct (Nat.eqb (proof_identity proof) (trace_entry_proof_identity trace) &&
      grade_eqb (proof_grade proof) (trace_entry_grade trace) &&
      Nat.leb (proof_roster_work proof + trace_rosters_work trace) budget)%bool
      eqn:Hgate; [|discriminate].
    destruct (prepare_proof owner proof budget) as [prepared|] eqn:Hentry;
      [|discriminate].
    destruct (certify_trace owner trace budget cancelled) as [hops|] eqn:Hhops;
      [|discriminate].
    inversion H; subst certificate; simpl.
    repeat rewrite andb_true_iff in Hgate.
    destruct Hgate as [[Hidentity Hgrade] Hbudget].
    apply Nat.eqb_eq in Hidentity. apply grade_eqb_eq in Hgrade.
    apply Nat.leb_le in Hbudget.
    exists proof. repeat split; assumption || reflexivity.
  Qed.

  Theorem certified_entry_retains_exact_roster :
    forall owner trace entry budget cancelled certificate,
      certify_trace_with_entry owner trace entry budget cancelled = Some certificate ->
      certified_proof_identity (certified_entry certificate) = trace_entry_proof_identity trace /\
      certified_grade (certified_entry certificate) = trace_entry_grade trace /\
      exists proof,
        entry = Some proof /\ proof_owner_checked owner proof = true /\
        proof_roster_complete proof = true /\ proof_candidates proof <> [] /\
        certified_candidates (certified_entry certificate) =
          map candidate_output (proof_candidates proof) /\
        Forall (fun candidate => candidate_checks (proof_binding proof) candidate = true)
          (proof_candidates proof).
  Proof.
    intros owner trace entry budget cancelled certificate H.
    apply certified_trace_with_entry_has_complete_evidence in H
      as [proof [Hentry [Hidentity [Hgrade [_ [Hprepared _]]]]]].
    apply prepare_proof_exact_fields in Hprepared
      as [Howner [Hproof [Hcertgrade [Houtputs [Hcomplete [Hnonempty Hchecks]]]]]].
    split; [congruence|]. split; [congruence|].
    exists proof. repeat split; assumption.
  Qed.

  Theorem missing_entry_has_no_complete_certificate : forall owner trace budget cancelled,
    certify_trace_with_entry owner trace None budget cancelled = None.
  Proof. reflexivity. Qed.

  Theorem wrong_entry_identity_has_no_complete_certificate :
    forall owner trace proof budget cancelled,
      proof_identity proof <> trace_entry_proof_identity trace ->
      certify_trace_with_entry owner trace (Some proof) budget cancelled = None.
  Proof.
    intros owner trace proof budget cancelled Hidentity.
    unfold certify_trace_with_entry.
    apply Nat.eqb_neq in Hidentity. now rewrite Hidentity.
  Qed.

  Theorem wrong_entry_grade_has_no_complete_certificate :
    forall owner trace proof budget cancelled,
      proof_grade proof <> trace_entry_grade trace ->
      certify_trace_with_entry owner trace (Some proof) budget cancelled = None.
  Proof.
    intros owner trace proof budget cancelled Hgrade.
    unfold certify_trace_with_entry, grade_eqb.
    destruct (grade_eq_dec (proof_grade proof) (trace_entry_grade trace));
      [contradiction|].
    now destruct (Nat.eqb (proof_identity proof) (trace_entry_proof_identity trace)).
  Qed.

  Theorem entry_and_hops_share_one_work_bound :
    forall owner trace proof budget cancelled,
      budget < proof_roster_work proof + trace_rosters_work trace ->
      certify_trace_with_entry owner trace (Some proof) budget cancelled = None.
  Proof.
    intros owner trace proof budget cancelled Hbudget.
    unfold certify_trace_with_entry.
    apply Nat.leb_gt in Hbudget. rewrite Hbudget.
    destruct (Nat.eqb (proof_identity proof) (trace_entry_proof_identity trace));
      destruct (grade_eqb (proof_grade proof) (trace_entry_grade trace)); reflexivity.
  Qed.

  Theorem cancellation_has_no_complete_certificate : forall owner trace entry budget,
    certify_trace_with_entry owner trace entry budget true = None.
  Proof.
    intros owner trace [proof|] budget; [|reflexivity].
    unfold certify_trace_with_entry.
    rewrite cancellation_has_no_partial_certificate.
    destruct (Nat.eqb (proof_identity proof) (trace_entry_proof_identity trace) &&
      grade_eqb (proof_grade proof) (trace_entry_grade trace) &&
      Nat.leb (proof_roster_work proof + trace_rosters_work trace) budget)%bool;
      [|reflexivity].
    now destruct (prepare_proof owner proof budget).
  Qed.

End CostGradeTraceTransport.

Module TraceTransportExamples.

Definition owner : TraceOwner :=
  {| owner_language := 1; owner_theory := 2; owner_base_image := 3;
     owner_cost_image := 4; owner_grade_sort := 5; owner_projected_image := 6;
     owner_relation := 7; owner_host_handle := 8 |}.

Definition key (grade : Grade) : nat :=
  match grade with GradeUnit => 0 | GradeGenerator n => S n | GradeProduct _ _ => 100 end.

Definition candidate (n : nat) : DemandCandidate :=
  {| output_base_image := 3; output_projected_image := 6; output_relation := 7;
     output_host_handle := 8; output_grade_key := S n; output_host_term := n;
     output_receipt := 90 + n; output_work := 1; output_typed_inverse_checked := true |}.

Definition proof (identity n : nat) : TraceProof :=
  {| proof_identity := identity; proof_grade := GradeGenerator n;
     proof_base_image := 3; proof_cost_image := 4; proof_grade_sort := 5;
     proof_binding := {| demand_base_image := 3; demand_projected_image := 6;
       demand_relation := 7; demand_host_handle := 8; demand_grade_key := S n;
       demand_proof_verified := true |};
     proof_candidates := [candidate n; candidate n]; proof_roster_complete := true |}.

Definition first_hop : TraceHop :=
  {| hop_before := 10; hop_after := 11; hop_charged_work := 17;
     hop_exhaustive_proofs := [proof 21 1; proof 22 1];
     hop_selected_proof := 1; hop_roster_complete := true |}.

Definition second_hop : TraceHop :=
  {| hop_before := 11; hop_after := 12; hop_charged_work := 19;
     hop_exhaustive_proofs := [proof 23 2];
     hop_selected_proof := 0; hop_roster_complete := true |}.

Definition trace (output : nat) (final : Grade) (hops : list TraceHop) : CheckedTrace :=
  {| trace_language := 1; trace_theory := 2; trace_base_image := 3;
     trace_cost_image := 4; trace_grade_sort := 5; trace_input := 10;
     trace_output := output; trace_entry_proof_identity := 20;
     trace_entry_grade := GradeGenerator 9;
     trace_final_grade := final; trace_hops := hops |}.

Definition final_grade := GradeProduct (GradeProduct (GradeGenerator 9)
  (GradeGenerator 1)) (GradeGenerator 2).

Example two_hops_keep_equal_grade_proofs_and_duplicate_host_receipts :
  option_map (fun certificates =>
    (map (fun hop => map certified_proof_identity (certified_proofs hop)) certificates,
     map (fun hop => map certified_candidates (certified_proofs hop)) certificates,
     map certified_selected_proof certificates))
    (certify_trace key owner (trace 12 final_grade [first_hop; second_hop]) 6 false) =
  Some ([[21; 22]; [23]],
    [[[(1, 91); (1, 91)]; [(1, 91); (1, 91)]]; [[(2, 92); (2, 92)]]], [1; 0]).
Proof. vm_compute. reflexivity. Qed.

Example dropped_hop_refuses :
  certify_trace key owner (trace 12 final_grade [second_hop]) 6 false = None.
Proof. vm_compute. reflexivity. Qed.

Example reordered_hops_refuse :
  certify_trace key owner (trace 12 final_grade [second_hop; first_hop]) 6 false = None.
Proof. vm_compute. reflexivity. Qed.

Example forged_unit_refuses :
  certify_trace key owner (trace 10 GradeUnit []) 0 false = None.
Proof. vm_compute. reflexivity. Qed.

Example authentic_zero_hop_nonunit_is_accepted :
  certify_trace key owner (trace 10 (GradeGenerator 9) []) 0 false = Some [].
Proof. vm_compute. reflexivity. Qed.

Example later_roster_budget_failure_has_no_prefix :
  certify_trace key owner (trace 12 final_grade [first_hop; second_hop]) 5 false = None.
Proof. vm_compute. reflexivity. Qed.

Example cancellation_has_no_prefix :
  certify_trace key owner (trace 12 final_grade [first_hop; second_hop]) 6 true = None.
Proof. vm_compute. reflexivity. Qed.

Example zero_hop_keeps_nonunit_entry_candidates :
  option_map (fun certificate =>
    (certified_proof_identity (certified_entry certificate),
     certified_grade (certified_entry certificate),
     certified_candidates (certified_entry certificate),
     certified_normalization certificate))
    (certify_trace_with_entry key owner (trace 10 (GradeGenerator 9) [])
      (Some (proof 20 9)) 2 false) =
  Some (20, GradeGenerator 9, [(9, 99); (9, 99)], []).
Proof. vm_compute. reflexivity. Qed.

Example nonunit_zero_hop_without_entry_refuses :
  certify_trace_with_entry key owner (trace 10 (GradeGenerator 9) []) None 2 false = None.
Proof. vm_compute. reflexivity. Qed.

Example substituted_entry_identity_refuses :
  certify_trace_with_entry key owner (trace 10 (GradeGenerator 9) [])
    (Some (proof 99 9)) 2 false = None.
Proof. vm_compute. reflexivity. Qed.

Example substituted_entry_grade_refuses :
  certify_trace_with_entry key owner (trace 10 (GradeGenerator 9) [])
    (Some (proof 20 1)) 2 false = None.
Proof. vm_compute. reflexivity. Qed.

Example entry_work_cannot_reuse_hop_budget :
  certify_trace_with_entry key owner (trace 12 final_grade [first_hop; second_hop])
    (Some (proof 20 9)) 6 false = None.
Proof. vm_compute. reflexivity. Qed.

Example complete_entry_and_hops_preserve_all_proof_identities :
  option_map (fun certificate =>
    (certified_proof_identity (certified_entry certificate),
     map (fun hop => map certified_proof_identity (certified_proofs hop))
       (certified_normalization certificate)))
    (certify_trace_with_entry key owner (trace 12 final_grade [first_hop; second_hop])
      (Some (proof 20 9)) 8 false) = Some (20, [[21; 22]; [23]]).
Proof. vm_compute. reflexivity. Qed.

End TraceTransportExamples.

Print Assumptions certified_trace_preserves_order_and_multiplicity.
Print Assumptions prepare_proof_exact_fields.
Print Assumptions prepare_proofs_identity_order.
Print Assumptions prepare_hop_preserves_proof_identity.
Print Assumptions certified_trace_has_complete_checked_proofs_and_exact_fold.
Print Assumptions cancellation_has_no_partial_certificate.
Print Assumptions insufficient_cumulative_work_has_no_certificate.
Print Assumptions zero_step_preserves_entry_without_minting_unit.
Print Assumptions wrong_trace_cost_digest_refuses.
Print Assumptions wrong_trace_grade_sort_refuses.
Print Assumptions exact_grade_product_retains_noncommutative_receipt_order.
Print Assumptions certified_trace_with_entry_has_complete_evidence.
Print Assumptions certified_entry_retains_exact_roster.
Print Assumptions missing_entry_has_no_complete_certificate.
Print Assumptions wrong_entry_identity_has_no_complete_certificate.
Print Assumptions wrong_entry_grade_has_no_complete_certificate.
Print Assumptions entry_and_hops_share_one_work_bound.
Print Assumptions cancellation_has_no_complete_certificate.
Print Assumptions TraceTransportExamples.two_hops_keep_equal_grade_proofs_and_duplicate_host_receipts.
Print Assumptions TraceTransportExamples.dropped_hop_refuses.
Print Assumptions TraceTransportExamples.reordered_hops_refuse.
Print Assumptions TraceTransportExamples.forged_unit_refuses.
Print Assumptions TraceTransportExamples.authentic_zero_hop_nonunit_is_accepted.
Print Assumptions TraceTransportExamples.later_roster_budget_failure_has_no_prefix.
Print Assumptions TraceTransportExamples.cancellation_has_no_prefix.
Print Assumptions TraceTransportExamples.zero_hop_keeps_nonunit_entry_candidates.
Print Assumptions TraceTransportExamples.nonunit_zero_hop_without_entry_refuses.
Print Assumptions TraceTransportExamples.substituted_entry_identity_refuses.
Print Assumptions TraceTransportExamples.substituted_entry_grade_refuses.
Print Assumptions TraceTransportExamples.entry_work_cannot_reuse_hop_budget.
Print Assumptions TraceTransportExamples.complete_entry_and_hops_preserve_all_proof_identities.
