(*
 * CostGradeFundingBoundary: the narrow Cost(G) to host-funding trust boundary.
 *
 * This is a refinement model of the service seam, not a proof of the Rust
 * matcher. FreshStep carries the kernel's two obligations: successor and grade
 * use the SAME rule and substitution. The service may expose that grade only
 * under the installed image, cost-image, and grade-sort identities. A separate
 * explicitly selected host projection and authenticated supply are required
 * before a demand can be called funded. No receipt or work counter is a purse.
 *
 * No Axioms and no Admitted.
 *)

From Stdlib Require Import Bool Lists.List PeanoNat.
Import ListNotations.

Section CostGradeFundingBoundary.

  Variable successor_of grade_of_rule : nat -> nat -> nat.

  Record InstalledCostImage : Type := {
    installed_semantic : nat;
    installed_cost : nat;
    installed_grade_sort : nat
  }.

  (* Abstracts an immediate, kernel-produced step, not a decoded wire receipt.
     The equations are precisely the same-substitution obligations checked by
     the existing costed rewrite executor. *)
  Record FreshStep : Type := {
    step_semantic : nat;
    step_cost : nat;
    step_grade_sort : nat;
    step_rule : nat;
    step_substitution : nat;
    step_successor : nat;
    step_grade : nat;
    successor_sound : step_successor = successor_of step_rule step_substitution;
    grade_sound : step_grade = grade_of_rule step_rule step_substitution
  }.

  Definition checked_grade (image : InstalledCostImage) (step : FreshStep)
      : option nat :=
    if (Nat.eqb (step_semantic step) (installed_semantic image)
        && Nat.eqb (step_cost step) (installed_cost image)
        && Nat.eqb (step_grade_sort step) (installed_grade_sort image))%bool
    then Some (step_grade step)
    else None.

  Theorem checked_grade_has_installed_provenance :
    forall image step grade,
      checked_grade image step = Some grade ->
      step_semantic step = installed_semantic image /\
      step_cost step = installed_cost image /\
      step_grade_sort step = installed_grade_sort image /\
      grade = grade_of_rule (step_rule step) (step_substitution step) /\
      step_successor step = successor_of (step_rule step) (step_substitution step).
  Proof.
    intros image step grade H.
    unfold checked_grade in H.
    destruct (Nat.eqb (step_semantic step) (installed_semantic image)
      && Nat.eqb (step_cost step) (installed_cost image)
      && Nat.eqb (step_grade_sort step) (installed_grade_sort image))%bool
      eqn:Hids; try discriminate.
    inversion H; subst grade.
    apply andb_true_iff in Hids as [Hboth Hsort].
    apply andb_true_iff in Hboth as [Hsemantic Hcost].
    repeat rewrite Nat.eqb_eq in *.
    repeat split; try assumption; [apply grade_sound | apply successor_sound].
  Qed.

  Theorem wrong_cost_image_has_no_grade :
    forall image step,
      step_cost step <> installed_cost image ->
      checked_grade image step = None.
  Proof.
    intros image step Hwrong.
    unfold checked_grade.
    apply Nat.eqb_neq in Hwrong. rewrite Hwrong.
    destruct (Nat.eqb (step_semantic step) (installed_semantic image)); reflexivity.
  Qed.

  Theorem wrong_grade_sort_has_no_grade :
    forall image step,
      step_grade_sort step <> installed_grade_sort image ->
      checked_grade image step = None.
  Proof.
    intros image step Hwrong.
    unfold checked_grade.
    apply Nat.eqb_neq in Hwrong. rewrite Hwrong.
    repeat destruct (Nat.eqb _ _); reflexivity.
  Qed.

  (* The projection is a separately installed interpretation of the guest
     grade, not a conversion inferred from its bytes. It may refuse a grade. *)
  Record HostProjection : Type := {
    projected_cost : nat;
    projected_grade_sort : nat;
    project_demand : nat -> option nat
  }.

  Definition checked_demand (image : InstalledCostImage) (step : FreshStep)
      (projection : option HostProjection) : option nat :=
    match checked_grade image step, projection with
    | Some grade, Some p =>
        if (Nat.eqb (projected_cost p) (installed_cost image)
            && Nat.eqb (projected_grade_sort p) (installed_grade_sort image))%bool
        then project_demand p grade
        else None
    | _, _ => None
    end.

  Definition funded (image : InstalledCostImage) (step : FreshStep)
      (projection : option HostProjection) (supply : nat)
      (authenticated : bool) : bool :=
    match checked_demand image step projection with
    | Some demand => authenticated && Nat.leb demand supply
    | None => false
    end.

  Theorem missing_projection_cannot_fund :
    forall image step supply authenticated,
      funded image step None supply authenticated = false.
  Proof.
    intros image step supply authenticated.
    unfold funded, checked_demand.
    destruct (checked_grade image step); reflexivity.
  Qed.

  Theorem unauthenticated_supply_cannot_fund :
    forall image step projection supply,
      funded image step projection supply false = false.
  Proof.
    intros image step projection supply.
    unfold funded. destruct (checked_demand image step projection); reflexivity.
  Qed.

  Theorem funding_requires_both_checked_axes :
    forall image step projection supply authenticated,
      funded image step projection supply authenticated = true ->
      exists grade p demand,
        checked_grade image step = Some grade /\
        projection = Some p /\
        projected_cost p = installed_cost image /\
        projected_grade_sort p = installed_grade_sort image /\
        project_demand p grade = Some demand /\
        authenticated = true /\ demand <= supply.
  Proof.
    intros image step projection supply authenticated Hfund.
    unfold funded, checked_demand in Hfund.
    destruct (checked_grade image step) as [grade|] eqn:Hgrade;
      try discriminate.
    destruct projection as [p|] eqn:Hprojection; try discriminate.
    destruct (Nat.eqb (projected_cost p) (installed_cost image)
      && Nat.eqb (projected_grade_sort p) (installed_grade_sort image))%bool
      eqn:Hids; try discriminate.
    destruct (project_demand p grade) as [demand|] eqn:Hdemand;
      try discriminate.
    apply andb_true_iff in Hfund as [Hauth Hsupply].
    apply Nat.leb_le in Hsupply.
    apply andb_true_iff in Hids as [Hcost Hsort].
    apply Nat.eqb_eq in Hcost. apply Nat.eqb_eq in Hsort.
    exists grade, p, demand. repeat split; assumption.
  Qed.

  Section ExactProjectedGrade.
    Variable key_of_grade : nat -> nat.
    Variable verify_projection : nat -> nat -> nat -> nat -> bool.
    Variable host_demand_bound : nat -> option (list (nat * nat)).
    Variable verify_host_bound : nat -> list (nat * nat) -> bool.

    (* A retained e-class root is projected by the same e-graph projector as
       the successor. Its exact key is computed from that root once; no parser
       or decoder reconstructs a grade from the key. *)
    Record RetainedGradeRoot : Type := {
      retained_step : FreshStep;
      retained_root : nat;
      retained_key : nat;
      retained_is_substituted_grade :
        retained_root = step_grade retained_step;
      retained_key_is_exact : retained_key = key_of_grade retained_root
    }.

    Theorem retained_grade_uses_successor_substitution :
      forall retained,
        retained_root retained =
          grade_of_rule (step_rule (retained_step retained))
                        (step_substitution (retained_step retained)) /\
        retained_key retained =
          key_of_grade
            (grade_of_rule (step_rule (retained_step retained))
                           (step_substitution (retained_step retained))).
    Proof.
      intro retained.
      pose proof (retained_key_is_exact retained) as Hkey.
      rewrite (retained_is_substituted_grade retained) in Hkey.
      rewrite (grade_sound (retained_step retained)) in Hkey.
      split.
      - rewrite (retained_is_substituted_grade retained).
        apply grade_sound.
      - exact Hkey.
    Qed.

    (* The base cost image and the host projection image have separate
       fingerprints. The verifier must certify that the projected image keeps
       the base rules as an exact prefix; a mere common sort name is not a
       composition proof. *)
    Record VerifiedComposition : Type := {
      composed_base_semantic : nat;
      composed_projected_semantic : nat;
      composed_cost : nat;
      composed_grade_sort : nat;
      composed_host_codec : nat;
      composed_relation : nat;
      base_rule_prefix_verified : bool
    }.

    Record HostCandidate : Type := {
      candidate_input_key : nat;
      candidate_host_term : nat;
      candidate_projected_semantic : nat;
      candidate_host_codec : nat;
      candidate_relation : nat;
      candidate_proof : nat
    }.

    Definition composition_matches (image : VerifiedComposition)
        (retained : RetainedGradeRoot) : bool :=
      (base_rule_prefix_verified image &&
       Nat.eqb (step_semantic (retained_step retained))
               (composed_base_semantic image) &&
       Nat.eqb (step_cost (retained_step retained))
               (composed_cost image) &&
       Nat.eqb (step_grade_sort (retained_step retained))
               (composed_grade_sort image))%bool.

    (* A host candidate is checked against the exact grade key and the exact
       installed images, relation, and codec. The projection verifier receives
       the relation, input key, host term, and proof. The host demand verifier
       remains a separate authority; neither proof grants supply. *)
    Definition candidate_identity_checked (image : VerifiedComposition)
        (retained : RetainedGradeRoot) (candidate : HostCandidate) : bool :=
      (Nat.eqb (candidate_input_key candidate) (retained_key retained) &&
       Nat.eqb (candidate_projected_semantic candidate)
               (composed_projected_semantic image) &&
       Nat.eqb (candidate_host_codec candidate)
               (composed_host_codec image) &&
       Nat.eqb (candidate_relation candidate)
               (composed_relation image) &&
       verify_projection (candidate_relation candidate)
                         (candidate_input_key candidate)
                         (candidate_host_term candidate)
                         (candidate_proof candidate))%bool.

    (* Identity and projection proof are checked before invoking the host's
       potentially expensive demand-bound computation. A malformed candidate
       must not obtain host work merely by entering an ambiguous roster. *)
    Definition candidate_is_funded (image : VerifiedComposition)
        (retained : RetainedGradeRoot) (supply : nat -> nat)
        (candidate : HostCandidate) : bool :=
      if candidate_identity_checked image retained candidate then
        match host_demand_bound (candidate_host_term candidate) with
        | None => false
        | Some bound =>
            (verify_host_bound (candidate_host_term candidate) bound &&
             forallb (fun lane_quantity =>
                        Nat.leb (snd lane_quantity) (supply (fst lane_quantity)))
                     bound)%bool
        end
      else false.

    (* A nonempty COMPLETE ambiguous set is retained. A top-k truncation or
       work-limit interruption is not completeness evidence and cannot fund
       even if every visible candidate passes. The actual host still owns
       authentication and supply. *)
    Definition all_candidates_funded (image : VerifiedComposition)
        (retained : RetainedGradeRoot) (candidates : list HostCandidate)
        (supply : nat -> nat) (authenticated roster_complete : bool) : bool :=
      match candidates with
      | [] => false
      | _ =>
          (authenticated && roster_complete &&
           composition_matches image retained &&
           forallb (candidate_is_funded image retained supply) candidates)%bool
      end.

    Theorem no_projection_candidate_cannot_fund :
      forall image retained supply authenticated complete,
        all_candidates_funded image retained [] supply authenticated complete = false.
    Proof. reflexivity. Qed.

    Theorem unauthenticated_projected_grade_cannot_fund :
      forall image retained candidates supply complete,
        all_candidates_funded image retained candidates supply false complete = false.
    Proof.
      intros image retained candidates supply complete.
      destruct candidates; reflexivity.
    Qed.

    Theorem incomplete_roster_cannot_fund :
      forall image retained candidates supply authenticated,
        all_candidates_funded image retained candidates supply authenticated false = false.
    Proof.
      intros image retained candidates supply authenticated.
      destruct candidates; destruct authenticated; reflexivity.
    Qed.

    Theorem any_unfunded_candidate_refutes_the_whole_set :
      forall image retained candidates supply authenticated complete candidate,
        In candidate candidates ->
        candidate_is_funded image retained supply candidate = false ->
        all_candidates_funded image retained candidates supply authenticated complete = false.
    Proof.
      intros image retained candidates supply authenticated complete candidate Hin Hfalse.
      destruct candidates as [|first rest]; [contradiction|].
      unfold all_candidates_funded.
      destruct authenticated, complete, (composition_matches image retained); simpl;
        try reflexivity.
      change (forallb (candidate_is_funded image retained supply)
                      (first :: rest) = false).
      destruct (forallb (candidate_is_funded image retained supply)
                        (first :: rest)) eqn:Hall; [|reflexivity].
      apply forallb_forall with (x := candidate) in Hall; [|assumption].
      rewrite Hfalse in Hall. discriminate.
    Qed.

    Theorem funded_candidate_has_exact_checked_bound :
      forall image retained candidates supply authenticated complete candidate,
        all_candidates_funded image retained candidates supply authenticated complete = true ->
        In candidate candidates ->
        exists bound,
          candidate_input_key candidate = retained_key retained /\
          candidate_projected_semantic candidate =
            composed_projected_semantic image /\
          candidate_host_codec candidate = composed_host_codec image /\
          candidate_relation candidate = composed_relation image /\
          verify_projection (candidate_relation candidate)
                            (candidate_input_key candidate)
                            (candidate_host_term candidate)
                            (candidate_proof candidate) = true /\
          host_demand_bound (candidate_host_term candidate) = Some bound /\
          verify_host_bound (candidate_host_term candidate) bound = true /\
          Forall (fun lane_quantity =>
                    snd lane_quantity <= supply (fst lane_quantity)) bound.
    Proof.
      intros image retained candidates supply authenticated complete candidate Hfund Hin.
      destruct candidates as [|first rest]; [contradiction|].
      unfold all_candidates_funded in Hfund.
      apply andb_true_iff in Hfund as [_ Hall].
      apply forallb_forall with (x := candidate) in Hall; [|assumption].
      unfold candidate_is_funded in Hall.
      destruct (candidate_identity_checked image retained candidate)
        eqn:Hidentity; [|discriminate].
      destruct (host_demand_bound (candidate_host_term candidate)) as [bound|]
        eqn:Hbound; [|discriminate].
      apply andb_true_iff in Hall as [Hhost Hlanes].
      unfold candidate_identity_checked in Hidentity.
      apply andb_true_iff in Hidentity as [Hprefix Hprojection].
      apply andb_true_iff in Hprefix as [Hprefix Hrelation].
      apply andb_true_iff in Hprefix as [Hprefix Hcodec].
      apply andb_true_iff in Hprefix as [Hkey Himage].
      apply Nat.eqb_eq in Hkey.
      apply Nat.eqb_eq in Himage.
      apply Nat.eqb_eq in Hcodec.
      apply Nat.eqb_eq in Hrelation.
      exists bound. repeat split; try assumption.
      apply Forall_forall. intros lane_quantity Hlane.
      apply forallb_forall with (x := lane_quantity) in Hlanes;
        [apply Nat.leb_le in Hlanes; exact Hlanes | exact Hlane].
    Qed.

    Theorem funded_set_requires_verified_base_composition :
      forall image retained candidates supply authenticated complete,
        all_candidates_funded image retained candidates supply authenticated complete = true ->
        authenticated = true /\
        complete = true /\
        base_rule_prefix_verified image = true /\
        step_semantic (retained_step retained) = composed_base_semantic image /\
        step_cost (retained_step retained) = composed_cost image /\
        step_grade_sort (retained_step retained) = composed_grade_sort image.
    Proof.
      intros image retained candidates supply authenticated complete Hfund.
      destruct candidates as [|first rest]; [discriminate|].
      unfold all_candidates_funded in Hfund.
      apply andb_true_iff in Hfund as [Hauthcomposition _].
      apply andb_true_iff in Hauthcomposition as [Hauthcomplete Hcomposition].
      apply andb_true_iff in Hauthcomplete as [Hauth Hcomplete].
      unfold composition_matches in Hcomposition.
      apply andb_true_iff in Hcomposition as [Hprefix Hsort].
      apply andb_true_iff in Hprefix as [Hprefix Hcost].
      apply andb_true_iff in Hprefix as [Hverified Hsemantic].
      apply Nat.eqb_eq in Hsort.
      apply Nat.eqb_eq in Hcost.
      apply Nat.eqb_eq in Hsemantic.
      repeat split; assumption.
    Qed.
  End ExactProjectedGrade.

  Section SelectedFundingProjectionOperation.
    (* A costed guest action still needs a rule grade. The one exception is
       not an ungraded guest action: it is a distinct interpretation operation
       over an already checked grade, selecting one installed GuestToHost
       relation. Its host work is independently metered. *)
    Inductive CostedOperation : Type :=
    | OrdinaryCostedAction
    | SelectedFundingInterpretation.

    Record ExecutableFundingSelector : Type := {
      selector_base : nat;
      selector_projected : nat;
      selector_relation : nat;
      selector_host_codec : nat;
      selector_profile : nat;
      selector_guest_to_host : bool;
      selector_proof_checked : bool
    }.

    Definition admit_projection_operation (operation : CostedOperation)
        (selector : option ExecutableFundingSelector)
        (base projected relation codec profile : nat)
        (host_work_used host_work_budget : nat) : bool :=
      match operation, selector with
      | SelectedFundingInterpretation, Some selected =>
          (selector_guest_to_host selected &&
           selector_proof_checked selected &&
           Nat.eqb (selector_base selected) base &&
           Nat.eqb (selector_projected selected) projected &&
           Nat.eqb (selector_relation selected) relation &&
           Nat.eqb (selector_host_codec selected) codec &&
           Nat.eqb (selector_profile selected) profile &&
           Nat.leb host_work_used host_work_budget)%bool
      | _, _ => false
      end.

    Theorem ordinary_costed_action_cannot_use_projection_exception :
      forall selector base projected relation codec profile used budget,
        admit_projection_operation OrdinaryCostedAction selector
          base projected relation codec profile used budget = false.
    Proof. reflexivity. Qed.

    Theorem declarative_v1_without_selector_cannot_project_funding :
      forall base projected relation codec profile used budget,
        admit_projection_operation SelectedFundingInterpretation None
          base projected relation codec profile used budget = false.
    Proof. reflexivity. Qed.

    Theorem selected_projection_is_exact_and_metered :
      forall selected base projected relation codec profile used budget,
        admit_projection_operation SelectedFundingInterpretation
          (Some selected) base projected relation codec profile used budget = true ->
        selector_guest_to_host selected = true /\
        selector_proof_checked selected = true /\
        selector_base selected = base /\
        selector_projected selected = projected /\
        selector_relation selected = relation /\
        selector_host_codec selected = codec /\
        selector_profile selected = profile /\
        used <= budget.
    Proof.
      intros selected base projected relation codec profile used budget Hadmit.
      unfold admit_projection_operation in Hadmit.
      apply andb_true_iff in Hadmit as [Hprefix Hwork].
      apply andb_true_iff in Hprefix as [Hprefix Hprofile].
      apply andb_true_iff in Hprefix as [Hprefix Hcodec].
      apply andb_true_iff in Hprefix as [Hprefix Hrelation].
      apply andb_true_iff in Hprefix as [Hprefix Hprojected].
      apply andb_true_iff in Hprefix as [Hprefix Hbase].
      apply andb_true_iff in Hprefix as [Hdirection Hproof].
      apply Nat.eqb_eq in Hbase.
      apply Nat.eqb_eq in Hprojected.
      apply Nat.eqb_eq in Hrelation.
      apply Nat.eqb_eq in Hcodec.
      apply Nat.eqb_eq in Hprofile.
      apply Nat.leb_le in Hwork.
      repeat split; assumption.
    Qed.
  End SelectedFundingProjectionOperation.

  Section SealedInstalledCostImage.
    Variable full_source_image_validator : nat -> nat -> nat -> nat -> bool.
    Variable checked_projected_prefix : nat -> nat -> bool.

    (* A private immutable installation witness is minted only after the full
       source/semantic/cost/profile validator succeeds. Borrowing it at runtime
       checks the exact profile and committed cost identity, not the full graph
       again. The checker is abstract here; the Rust constructor must call the
       existing CostImageV1 compiler/validator before building this record. *)
    Record SealedCostInstallation : Type := {
      sealed_source : nat;
      sealed_semantic : nat;
      sealed_cost : nat;
      sealed_profile : nat;
      sealed_projected : option nat;
      sealed_validation :
        full_source_image_validator sealed_source sealed_semantic
                                    sealed_cost sealed_profile = true;
      sealed_prefix_validation :
        match sealed_projected with
        | Some projected => checked_projected_prefix sealed_semantic projected = true
        | None => True
        end
    }.

    Definition borrow_installed_cost (sealed : SealedCostInstallation)
        (requested_profile committed_cost : nat) : option nat :=
      if (Nat.eqb requested_profile (sealed_profile sealed)
          && Nat.eqb committed_cost (sealed_cost sealed))%bool
      then Some (sealed_cost sealed)
      else None.

    Theorem borrowed_cost_was_fully_validated_at_install :
      forall sealed requested_profile committed_cost borrowed,
        borrow_installed_cost sealed requested_profile committed_cost = Some borrowed ->
        requested_profile = sealed_profile sealed /\
        committed_cost = sealed_cost sealed /\
        borrowed = sealed_cost sealed /\
        full_source_image_validator
          (sealed_source sealed) (sealed_semantic sealed)
          (sealed_cost sealed) (sealed_profile sealed) = true /\
        match sealed_projected sealed with
        | Some projected =>
            checked_projected_prefix (sealed_semantic sealed) projected = true
        | None => True
        end.
    Proof.
      intros sealed requested_profile committed_cost borrowed Hborrow.
      unfold borrow_installed_cost in Hborrow.
      destruct (Nat.eqb requested_profile (sealed_profile sealed)
        && Nat.eqb committed_cost (sealed_cost sealed))%bool eqn:Hids;
        try discriminate.
      inversion Hborrow; subst borrowed.
      apply andb_true_iff in Hids as [Hprofile Hcost].
      apply Nat.eqb_eq in Hprofile. apply Nat.eqb_eq in Hcost.
      repeat split; try assumption; try apply sealed_validation;
        apply sealed_prefix_validation.
    Qed.

    Theorem wrong_install_profile_cannot_borrow :
      forall sealed requested_profile committed_cost,
        requested_profile <> sealed_profile sealed ->
        borrow_installed_cost sealed requested_profile committed_cost = None.
    Proof.
      intros sealed requested_profile committed_cost Hwrong.
      unfold borrow_installed_cost.
      apply Nat.eqb_neq in Hwrong. rewrite Hwrong. reflexivity.
    Qed.
  End SealedInstalledCostImage.

  Section AccountedProjectedImageValidation.
    (* The implementation feeds the canonical image encoder into one hash
       sink. Each emitted chunk must be charged before it reaches the hasher;
       an exhausted budget never publishes a verified image fingerprint. The
       model counts chunk lengths, not a second serialization algorithm. *)
    Fixpoint charge_fingerprint_chunks (chunks : list nat)
        (budget used : nat) : option nat :=
      match chunks with
      | [] => Some used
      | chunk :: rest =>
          let next := used + chunk in
          if Nat.leb next budget
          then charge_fingerprint_chunks rest budget next
          else None
      end.

    Theorem successful_fingerprint_is_metered :
      forall chunks budget used final,
        used <= budget ->
        charge_fingerprint_chunks chunks budget used = Some final ->
        final <= budget.
    Proof.
      induction chunks as [|chunk rest IH]; intros budget used final Hused Hcharge.
      - simpl in Hcharge. inversion Hcharge; subst. assumption.
      - simpl in Hcharge.
        destruct (Nat.leb (used + chunk) budget) eqn:Hnext;
          try discriminate.
        apply Nat.leb_le in Hnext.
        eapply IH; eassumption.
    Qed.

    Theorem unaffordable_first_chunk_is_refused :
      forall chunk rest budget used,
        budget < used + chunk ->
        charge_fingerprint_chunks (chunk :: rest) budget used = None.
    Proof.
      intros chunk rest budget used Htoo_large. simpl.
      apply Nat.leb_gt in Htoo_large. rewrite Htoo_large. reflexivity.
    Qed.
  End AccountedProjectedImageValidation.

  Section InstalledProjectedImageWitness.
    (* An immutable installed image may reuse its installation-time checked
       fingerprint. The fast path is available only for the SAME Arc-owned
       image token and matching commitment. Generic caller-supplied images
       still pass through accounted canonical hashing. *)
    Record SealedProjectedImage : Type := {
      projected_owned_image : nat;
      projected_execution_fingerprint : nat;
      projected_commitment : nat;
      projected_install_check :
        projected_execution_fingerprint = projected_commitment
    }.

    Definition may_skip_rehash (sealed : SealedProjectedImage)
        (requested_image requested_fingerprint : nat) : bool :=
      (Nat.eqb requested_image (projected_owned_image sealed)
       && Nat.eqb requested_fingerprint (projected_commitment sealed))%bool.

    Theorem rehash_skip_requires_same_installed_image :
      forall sealed image fingerprint,
        may_skip_rehash sealed image fingerprint = true ->
        image = projected_owned_image sealed /\
        fingerprint = projected_execution_fingerprint sealed.
    Proof.
      intros sealed image fingerprint Hskip.
      unfold may_skip_rehash in Hskip.
      apply andb_true_iff in Hskip as [Himage Hfingerprint].
      apply Nat.eqb_eq in Himage.
      apply Nat.eqb_eq in Hfingerprint.
      split; try assumption.
      rewrite projected_install_check. assumption.
    Qed.
  End InstalledProjectedImageWitness.

End CostGradeFundingBoundary.
