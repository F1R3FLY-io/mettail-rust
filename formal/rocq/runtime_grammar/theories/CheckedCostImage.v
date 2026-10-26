(**
  CheckedCostImage: the provenance boundary for a Cost(G) transition grade.

  A cost image is a separately verified, fingerprint-bound projection of a
  theory's directed rewrite rules.  Its grade expression uses only signature
  keys bound by the very rule match that produces the successor.  This model
  deliberately does not infer cost from effects, parser rank, elapsed work, or
  an untrusted caller's receipt.  The existing semantic-kernel proof supplies
  the validity of the match and its substitution; this file proves the
  additional grade-publication boundary.  Signatures form a multiset, whereas
  the temporal stack is an ordered list of those multisets.  This is an
  abstraction of the R1--R3 consumed-cell rule, not a proof of the full
  Cost(G) monad or host settlement.

  Rocq 9.1 compatible. No admitted results, axioms, or assumptions.
*)

From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.

Module CheckedCostImage.

Definition Fingerprint := list nat.
Definition SignatureKey := nat.
Definition VariableId := nat.
Definition RuleId := nat.
Definition Grade := list SignatureKey.

(** A declared cost unit and product are source constructors, not opaque
    strings that the runtime may interpret as fuel. This is the constructor
    typing boundary checked by LanguageCoreV1 before an image is compiled. *)
Record ConstructorSignature := {
  constructor_domain : list nat;
  constructor_codomain : nat
}.

Definition well_typed_cost_algebra (signature_sort : nat)
    (unit product : ConstructorSignature) : bool :=
  match constructor_domain unit with
  | [] => Nat.eqb (constructor_codomain unit) signature_sort
  | _ => false
  end &&
  match constructor_domain product with
  | [lhs_sort; rhs_sort] =>
      Nat.eqb lhs_sort signature_sort &&
      Nat.eqb rhs_sort signature_sort &&
      Nat.eqb (constructor_codomain product) signature_sort
  | _ => false
  end.

Theorem checked_cost_algebra_has_exact_signature_types :
  forall signature_sort unit product,
    well_typed_cost_algebra signature_sort unit product = true ->
    constructor_domain unit = [] /\
    constructor_codomain unit = signature_sort /\
    constructor_domain product = [signature_sort; signature_sort] /\
    constructor_codomain product = signature_sort.
Proof.
  intros signature_sort [unit_domain unit_codomain]
    [product_domain product_codomain] Htyped.
  destruct unit_domain as [|unit_head unit_tail]; simpl in Htyped;
    try discriminate.
  apply andb_true_iff in Htyped as [Hunit Hproduct].
  apply Nat.eqb_eq in Hunit.
  destruct product_domain as [|lhs_sort [|rhs_sort [|third tail]]];
    simpl in Hproduct; try discriminate.
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  end.
  repeat match goal with
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  end.
  simpl. repeat split; subst; reflexivity.
Qed.

Inductive GradeExpr : Type :=
| GradeUnit
| GradeKey (key : SignatureKey)
| GradeBound (variable : VariableId)
| GradeProduct (lhs rhs : GradeExpr).

Fixpoint lookup_binding (variable : VariableId)
    (bindings : list (VariableId * SignatureKey)) : option SignatureKey :=
  match bindings with
  | [] => None
  | (candidate, key) :: rest =>
      if Nat.eqb candidate variable then Some key
      else lookup_binding variable rest
  end.

Fixpoint evaluate_grade (bindings : list (VariableId * SignatureKey))
    (expression : GradeExpr) : option Grade :=
  match expression with
  | GradeUnit => Some []
  | GradeKey key => Some [key]
  | GradeBound variable =>
      match lookup_binding variable bindings with
      | Some key => Some [key]
      | None => None
      end
  | GradeProduct lhs rhs =>
      match evaluate_grade bindings lhs, evaluate_grade bindings rhs with
      | Some lhs_grade, Some rhs_grade => Some (lhs_grade ++ rhs_grade)
      | _, _ => None
      end
  end.

(** List order is only a representation: the signature product is a
    commutative multiset with multiplicity.  The temporal stack below retains
    its order and is not quotiented by this relation. *)
Definition grade_equivalent (left right : Grade) : Prop :=
  forall key, count_occ Nat.eq_dec left key = count_occ Nat.eq_dec right key.

Record CostRule := {
  cost_rule_id : RuleId;
  cost_rule_grade : GradeExpr
}.

Fixpoint find_cost_rule (rule : RuleId) (rules : list CostRule)
    : option CostRule :=
  match rules with
  | [] => None
  | row :: rest =>
      if Nat.eqb (cost_rule_id row) rule then Some row
      else find_cost_rule rule rest
  end.

Record CostImage := {
  cost_language : Fingerprint;
  cost_theory : Fingerprint;
  cost_semantic_image : Fingerprint;
  cost_fingerprint : Fingerprint;
  cost_grade_sort : nat;
  cost_unit_constructor : nat;
  cost_product_constructor : nat;
  cost_rules : list CostRule
}.

Record KernelMatch := {
  match_language : Fingerprint;
  match_theory : Fingerprint;
  match_semantic_image : Fingerprint;
  match_installed_cost_image : Fingerprint;
  match_rule : RuleId;
  match_output : Fingerprint;
  match_bindings : list (VariableId * SignatureKey)
}.

Record GradeReceipt := {
  receipt_language : Fingerprint;
  receipt_theory : Fingerprint;
  receipt_semantic_image : Fingerprint;
  receipt_cost_image : Fingerprint;
  receipt_rule : RuleId;
  receipt_output : Fingerprint;
  receipt_sort : nat;
  receipt_grade : Grade
}.

Fixpoint fingerprints_equal (left right : Fingerprint) : bool :=
  match left, right with
  | [], [] => true
  | x :: xs, y :: ys => Nat.eqb x y && fingerprints_equal xs ys
  | _, _ => false
  end.

Definition image_owner_matches (image : CostImage) (matched : KernelMatch) : bool :=
  fingerprints_equal (cost_language image) (match_language matched) &&
  fingerprints_equal (cost_theory image) (match_theory matched) &&
  fingerprints_equal (cost_semantic_image image) (match_semantic_image matched) &&
  fingerprints_equal (cost_fingerprint image) (match_installed_cost_image matched).

(** [image] is admitted only after the independent cost-image verifier checks
    its theory fingerprint, rule IDs, sort, and grade-term well-formedness.
    [matched] is produced by the semantic transition kernel, not by a client.
    This function is the last fail-closed publication gate. *)
Definition publish_grade (image : CostImage) (matched : KernelMatch)
    : option GradeReceipt :=
  if image_owner_matches image matched
  then
    match find_cost_rule (match_rule matched) (cost_rules image) with
    | None => None
    | Some row =>
        match evaluate_grade (match_bindings matched) (cost_rule_grade row) with
        | None => None
        | Some grade =>
            Some {| receipt_language := cost_language image;
                    receipt_theory := cost_theory image;
                    receipt_semantic_image := cost_semantic_image image;
                    receipt_cost_image := cost_fingerprint image;
                    receipt_rule := match_rule matched;
                    receipt_output := match_output matched;
                    receipt_sort := cost_grade_sort image;
                    receipt_grade := grade |}
        end
    end
  else None.

Lemma fingerprints_equal_sound : forall left right,
  fingerprints_equal left right = true -> left = right.
Proof.
  induction left as [|x xs IH]; destruct right as [|y ys]; simpl;
    try discriminate; auto.
  intros H. apply andb_true_iff in H as [Hhead Htail].
  apply Nat.eqb_eq in Hhead. apply IH in Htail. now subst.
Qed.

Lemma image_owner_matches_sound : forall image matched,
  image_owner_matches image matched = true ->
  cost_language image = match_language matched /\
  cost_theory image = match_theory matched /\
  cost_semantic_image image = match_semantic_image matched /\
  cost_fingerprint image = match_installed_cost_image matched.
Proof.
  intros image matched Howner.
  unfold image_owner_matches in Howner.
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  end.
  repeat split; eapply fingerprints_equal_sound; eassumption.
Qed.

Theorem published_grade_is_exactly_the_matched_rule_grade :
  forall image matched receipt,
    publish_grade image matched = Some receipt ->
    cost_language image = match_language matched /\
    cost_theory image = match_theory matched /\
    cost_semantic_image image = match_semantic_image matched /\
    cost_fingerprint image = match_installed_cost_image matched /\
    receipt_language receipt = cost_language image /\
    receipt_theory receipt = cost_theory image /\
    receipt_semantic_image receipt = cost_semantic_image image /\
    receipt_cost_image receipt = cost_fingerprint image /\
    receipt_output receipt = match_output matched /\
    receipt_sort receipt = cost_grade_sort image /\
    exists row,
      find_cost_rule (match_rule matched) (cost_rules image) = Some row /\
      evaluate_grade (match_bindings matched) (cost_rule_grade row) =
        Some (receipt_grade receipt) /\
      receipt_rule receipt = match_rule matched.
Proof.
  intros image matched receipt Hpublish.
  unfold publish_grade in Hpublish.
  destruct (image_owner_matches image matched) eqn:Howner;
    try discriminate.
  destruct (find_cost_rule (match_rule matched) (cost_rules image))
    as [row|] eqn:Hrow; try discriminate.
  destruct (evaluate_grade (match_bindings matched) (cost_rule_grade row))
    as [grade|] eqn:Hgrade; try discriminate.
  inversion Hpublish; subst receipt; simpl.
  apply image_owner_matches_sound in Howner as
      [Hlanguage [Htheory [Hsemantic Hcost]]].
  repeat split; try reflexivity.
  - exact Hlanguage.
  - exact Htheory.
  - exact Hsemantic.
  - exact Hcost.
  - exists row. repeat split; assumption || reflexivity.
Qed.

Theorem absent_cost_rule_never_publishes :
  forall image matched,
    find_cost_rule (match_rule matched) (cost_rules image) = None ->
    publish_grade image matched = None.
Proof.
  intros image matched Hmissing.
  unfold publish_grade.
  destruct (image_owner_matches image matched);
    [now rewrite Hmissing | reflexivity].
Qed.

Theorem unresolved_grade_binding_never_publishes :
  forall image matched row,
    find_cost_rule (match_rule matched) (cost_rules image) = Some row ->
    evaluate_grade (match_bindings matched) (cost_rule_grade row) = None ->
    publish_grade image matched = None.
Proof.
  intros image matched row Hrow Hmissing.
  unfold publish_grade.
  destruct (image_owner_matches image matched);
    [now rewrite Hrow, Hmissing | reflexivity].
Qed.

Theorem wrong_language_fingerprint_never_publishes :
  forall image matched,
    cost_language image <> match_language matched ->
    publish_grade image matched = None.
Proof.
  intros image matched Hwrong.
  unfold publish_grade.
  destruct (image_owner_matches image matched) eqn:Howner;
    [| reflexivity].
  apply image_owner_matches_sound in Howner as [Hlanguage _].
  contradiction.
Qed.

Theorem wrong_theory_fingerprint_never_publishes :
  forall image matched,
    cost_theory image <> match_theory matched ->
    publish_grade image matched = None.
Proof.
  intros image matched Hwrong.
  unfold publish_grade.
  destruct (image_owner_matches image matched) eqn:Howner;
    [| reflexivity].
  apply image_owner_matches_sound in Howner as [_ [Htheory _]].
  contradiction.
Qed.

Theorem wrong_semantic_image_fingerprint_never_publishes :
  forall image matched,
    cost_semantic_image image <> match_semantic_image matched ->
    publish_grade image matched = None.
Proof.
  intros image matched Hwrong.
  unfold publish_grade.
  destruct (image_owner_matches image matched) eqn:Howner;
    [| reflexivity].
  apply image_owner_matches_sound in Howner as [_ [_ [Hsemantic _]]].
  contradiction.
Qed.

Theorem wrong_installed_cost_image_fingerprint_never_publishes :
  forall image matched,
    cost_fingerprint image <> match_installed_cost_image matched ->
    publish_grade image matched = None.
Proof.
  intros image matched Hwrong.
  unfold publish_grade.
  destruct (image_owner_matches image matched) eqn:Howner;
    [| reflexivity].
  apply image_owner_matches_sound in Howner as [_ [_ [_ Hcost]]].
  contradiction.
Qed.

(** A compound transition retains one source-bound receipt for every rule
    match. The monoid product is represented by concatenation here; the
    concrete image constructs the declared product term instead. Neither
    representation permits a missing premise to become the unit grade. *)
Fixpoint publish_all (image : CostImage) (matches : list KernelMatch)
    : option (list GradeReceipt) :=
  match matches with
  | [] => Some []
  | matched :: rest =>
      match publish_grade image matched, publish_all image rest with
      | Some receipt, Some receipts => Some (receipt :: receipts)
      | _, _ => None
      end
  end.

Fixpoint combined_grade (receipts : list GradeReceipt) : Grade :=
  match receipts with
  | [] => []
  | receipt :: rest => receipt_grade receipt ++ combined_grade rest
  end.

Record CompositeGradeReceipt := {
  composite_parts : list GradeReceipt;
  composite_grade : Grade
}.

Definition publish_composite (image : CostImage)
    (matches : list KernelMatch) : option CompositeGradeReceipt :=
  match publish_all image matches with
  | None => None
  | Some receipts =>
      Some {| composite_parts := receipts;
              composite_grade := combined_grade receipts |}
  end.

Theorem published_composite_retains_every_source_grade :
  forall image matches composite,
    publish_composite image matches = Some composite ->
    Forall2
      (fun matched receipt => publish_grade image matched = Some receipt)
      matches (composite_parts composite) /\
    composite_grade composite = combined_grade (composite_parts composite).
Proof.
  intros image matches composite Hpublished.
  unfold publish_composite in Hpublished.
  destruct (publish_all image matches) as [receipts|] eqn:Hall;
    try discriminate.
  inversion Hpublished; subst composite; clear Hpublished; simpl.
  split; [| reflexivity].
  revert receipts Hall.
  induction matches as [|matched rest IH]; intros receipts Hall;
    simpl in Hall.
  - inversion Hall; constructor.
  - destruct (publish_grade image matched) as [receipt|] eqn:Hhead;
      try discriminate.
    destruct (publish_all image rest) as [tail|] eqn:Htail;
      try discriminate.
    inversion Hall; subst receipts.
    constructor; [exact Hhead | now apply IH].
Qed.

Lemma missing_component_grade_prevents_complete_roster :
  forall image matches matched,
    In matched matches ->
    publish_grade image matched = None ->
    publish_all image matches = None.
Proof.
  intros image matches matched Hmember Hmissing.
  induction matches as [|head rest IH]; simpl in *.
  - contradiction.
  - destruct Hmember as [Heq | Htail].
    + subst head. rewrite Hmissing.
      destruct (publish_all image rest); reflexivity.
    + destruct (publish_grade image head) as [receipt|] eqn:Hhead;
        [now rewrite (IH Htail) | destruct (publish_all image rest); reflexivity].
Qed.

Theorem missing_component_grade_prevents_composite_publication :
  forall image matches matched,
    In matched matches ->
    publish_grade image matched = None ->
    publish_composite image matches = None.
Proof.
  intros image matches matched Hmember Hmissing.
  unfold publish_composite.
  now rewrite (missing_component_grade_prevents_complete_roster
                 image matches matched Hmember Hmissing).
Qed.

Theorem combined_grade_respects_composition :
  forall left right,
    combined_grade (left ++ right) =
      combined_grade left ++ combined_grade right.
Proof.
  induction left as [|receipt rest IH]; intros right; simpl.
  - reflexivity.
  - rewrite IH. now rewrite app_assoc.
Qed.

(** A normalization forest is a roster of alternative proof paths, not a
    conjunction. Every path must retain its own composite grade. Failure to
    grade one path makes the whole bounded roster undetermined; it cannot be
    hidden by publishing only the other paths. *)
Fixpoint publish_alternatives (image : CostImage)
    (paths : list (list KernelMatch)) : option (list CompositeGradeReceipt) :=
  match paths with
  | [] => Some []
  | path :: rest =>
      match publish_composite image path, publish_alternatives image rest with
      | Some receipt, Some receipts => Some (receipt :: receipts)
      | _, _ => None
      end
  end.

Theorem published_alternatives_preserve_every_path :
  forall image paths receipts,
    publish_alternatives image paths = Some receipts ->
    Forall2
      (fun path receipt => publish_composite image path = Some receipt)
      paths receipts.
Proof.
  intros image paths.
  induction paths as [|path rest IH]; intros receipts Hpublished;
    simpl in Hpublished.
  - inversion Hpublished. constructor.
  - destruct (publish_composite image path) as [receipt|] eqn:Hhead;
      try discriminate.
    destruct (publish_alternatives image rest) as [tail|] eqn:Htail;
      try discriminate.
    inversion Hpublished; subst receipts.
    constructor; [exact Hhead | now apply IH].
Qed.

Theorem published_alternatives_preserve_roster_length :
  forall image paths receipts,
    publish_alternatives image paths = Some receipts ->
    length paths = length receipts.
Proof.
  intros image paths.
  induction paths as [|path rest IH]; intros receipts Hpublished;
    simpl in Hpublished.
  - inversion Hpublished. reflexivity.
  - destruct (publish_composite image path) as [receipt|];
      try discriminate.
    destruct (publish_alternatives image rest) as [tail|] eqn:Htail;
      try discriminate.
    inversion Hpublished; subst receipts. simpl.
    f_equal. now apply IH.
Qed.

(** Equal successor keys do not turn distinct proof paths into one cost
    candidate. Both alternatives retain their own source-grade witnesses. *)
Theorem equal_output_alternatives_keep_both_proofs :
  forall image left right receipts,
    match_output left = match_output right ->
    publish_alternatives image [[left]; [right]] = Some receipts ->
    length receipts = 2 /\
    Forall2
      (fun path receipt => publish_composite image path = Some receipt)
      [[left]; [right]] receipts.
Proof.
  intros image left right receipts _ Hpublished.
  split.
  - apply published_alternatives_preserve_roster_length in Hpublished.
    simpl in Hpublished. symmetry. exact Hpublished.
  - now apply published_alternatives_preserve_every_path.
Qed.

(** A normalization hop publishes the complete proof roster and a selected
    ordinal. The selected grade must be one of those checked proofs. This is
    the refinement target for the separate graded-hop V2 receipt; the older
    ungraded hop format keeps its original four-field wire shape. *)
Record HopInput := {
  hop_proofs : list KernelMatch;
  hop_selected : nat
}.

Record CheckedHopReceipt := {
  checked_hop_roster : CompositeGradeReceipt;
  checked_hop_selected : nat;
  checked_hop_grade : GradeReceipt
}.

Definition publish_hop (image : CostImage) (hop : HopInput)
    : option CheckedHopReceipt :=
  match publish_composite image (hop_proofs hop) with
  | None => None
  | Some roster =>
      match nth_error (composite_parts roster) (hop_selected hop) with
      | None => None
      | Some grade =>
          Some {| checked_hop_roster := roster;
                  checked_hop_selected := hop_selected hop;
                  checked_hop_grade := grade |}
      end
  end.

Theorem published_hop_selects_from_complete_checked_roster :
  forall image hop receipt,
    publish_hop image hop = Some receipt ->
    Forall2
      (fun matched grade => publish_grade image matched = Some grade)
      (hop_proofs hop)
      (composite_parts (checked_hop_roster receipt)) /\
    nth_error (composite_parts (checked_hop_roster receipt))
              (checked_hop_selected receipt) = Some (checked_hop_grade receipt) /\
    checked_hop_selected receipt = hop_selected hop.
Proof.
  intros image hop receipt Hpublished.
  unfold publish_hop in Hpublished.
  destruct (publish_composite image (hop_proofs hop)) as [roster|]
    eqn:Hroster; try discriminate.
  destruct (nth_error (composite_parts roster) (hop_selected hop))
    as [grade|] eqn:Hselected; try discriminate.
  inversion Hpublished; subst receipt; simpl.
  repeat split; try assumption; try reflexivity.
  pose proof (published_composite_retains_every_source_grade
                image (hop_proofs hop) roster Hroster) as [Hproofs _].
  exact Hproofs.
Qed.

Theorem missing_hop_grade_prevents_publication :
  forall image hop matched,
    In matched (hop_proofs hop) ->
    publish_grade image matched = None ->
    publish_hop image hop = None.
Proof.
  intros image hop matched Hmember Hmissing.
  unfold publish_hop, publish_composite.
  now rewrite (missing_component_grade_prevents_complete_roster
                 image (hop_proofs hop) matched Hmember Hmissing).
Qed.

Theorem missing_alternative_grade_prevents_roster_publication :
  forall image paths path matched,
    In path paths ->
    In matched path ->
    publish_grade image matched = None ->
    publish_alternatives image paths = None.
Proof.
  intros image paths path matched Hpath Hmatched Hmissing.
  induction paths as [|head rest IH]; simpl in *.
  - contradiction.
  - destruct Hpath as [Heq | Htail].
    + subst head.
      rewrite (missing_component_grade_prevents_composite_publication
                 image path matched Hmatched Hmissing).
      destruct (publish_alternatives image rest); reflexivity.
    + destruct (publish_composite image head) as [receipt|];
        [now rewrite (IH Htail) | destruct (publish_alternatives image rest); reflexivity].
Qed.

(** A work budget gates whether the complete privately constructed result can
    be published. It cannot substitute for a missing grade or alter the grade
    of a proven result. [Undetermined] is not a zero-grade transition. *)
Inductive GradedDecision :=
| Proven (receipt : GradeReceipt)
| Undetermined.

Definition publish_with_budget (work_needed work_limit : nat)
    (image : CostImage) (matched : KernelMatch) : GradedDecision :=
  if Nat.leb work_needed work_limit then
    match publish_grade image matched with
    | Some receipt => Proven receipt
    | None => Undetermined
    end
  else Undetermined.

Theorem a_proven_budgeted_grade_has_exact_evidence :
  forall work_needed work_limit image matched receipt,
    publish_with_budget work_needed work_limit image matched = Proven receipt ->
    work_needed <= work_limit /\
    publish_grade image matched = Some receipt.
Proof.
  intros work_needed work_limit image matched receipt Hproven.
  unfold publish_with_budget in Hproven.
  destruct (Nat.leb work_needed work_limit) eqn:Hbudget;
    [| discriminate].
  apply Nat.leb_le in Hbudget.
  destruct (publish_grade image matched) eqn:Hevidence;
    [| discriminate].
  inversion Hproven; subst. split.
  - exact Hbudget.
  - reflexivity.
Qed.

Theorem an_absent_grade_remains_unavailable_at_every_budget :
  forall work_needed work_limit image matched,
    publish_grade image matched = None ->
    publish_with_budget work_needed work_limit image matched = Undetermined.
Proof.
  intros work_needed work_limit image matched Hmissing.
  unfold publish_with_budget.
  destruct (Nat.leb work_needed work_limit);
    [now rewrite Hmissing | reflexivity].
Qed.

(** An authored GuestToHost projection is an interpretation rule, not a
    costed guest transition. It may execute without creating another guest
    grade only under the exact selected projected image and appended rule
    roster. In particular, ordinary base guest actions cannot invoke this
    exception or turn an absent grade into the cost unit. *)
Record ProjectionDispatch := {
  projection_image : Fingerprint;
  projection_expected_image : Fingerprint;
  projection_selected : bool;
  projection_base_rule_count : nat;
  projection_rule : RuleId;
  projection_roster : list RuleId
}.

Definition ungraded_projection_allowed (dispatch : ProjectionDispatch) : bool :=
  fingerprints_equal (projection_image dispatch)
                     (projection_expected_image dispatch) &&
  projection_selected dispatch &&
  Nat.leb (projection_base_rule_count dispatch) (projection_rule dispatch) &&
  existsb (Nat.eqb (projection_rule dispatch)) (projection_roster dispatch).

Theorem ungraded_projection_requires_selected_appended_rule :
  forall dispatch,
    ungraded_projection_allowed dispatch = true ->
    projection_image dispatch = projection_expected_image dispatch /\
    projection_selected dispatch = true /\
    projection_base_rule_count dispatch <= projection_rule dispatch /\
    In (projection_rule dispatch) (projection_roster dispatch).
Proof.
  intros dispatch Hallowed.
  unfold ungraded_projection_allowed in Hallowed.
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  end.
  repeat split.
  - eapply fingerprints_equal_sound; eassumption.
  - assumption.
  - apply Nat.leb_le. assumption.
  - match goal with
    | H : existsb _ _ = true |- _ =>
        apply existsb_exists in H as [rule [Hmember Heq]]
    end.
    apply Nat.eqb_eq in Heq. subst rule. exact Hmember.
Qed.

Theorem base_guest_rule_cannot_use_ungraded_projection :
  forall dispatch,
    projection_rule dispatch < projection_base_rule_count dispatch ->
    ungraded_projection_allowed dispatch = false.
Proof.
  intros dispatch Hbase.
  destruct (ungraded_projection_allowed dispatch) eqn:Hallowed;
    [| reflexivity].
  apply ungraded_projection_requires_selected_appended_rule in Hallowed
    as [_ [_ [Happended _]]].
  lia.
Qed.

Theorem unselected_projection_cannot_use_ungraded_dispatch :
  forall dispatch,
    projection_selected dispatch = false ->
    ungraded_projection_allowed dispatch = false.
Proof.
  intros dispatch Hselected.
  unfold ungraded_projection_allowed.
  now rewrite Hselected, andb_false_r.
Qed.

(** V2 installation binds three independent identities. The selector alone is
    authored data; a compiled projected image, live host profile, and trusted
    proof implementation must all match before the selector is retained. *)
Record FundingInstallEvidence := {
  funding_authored_projected : Fingerprint;
  funding_compiled_projected : Fingerprint;
  funding_selected_host : Fingerprint;
  funding_installed_host : Fingerprint;
  funding_claimed_proof : Fingerprint;
  funding_trusted_proof : Fingerprint
}.

Definition funding_install_checks (evidence : FundingInstallEvidence) : bool :=
  fingerprints_equal (funding_authored_projected evidence)
                     (funding_compiled_projected evidence) &&
  fingerprints_equal (funding_selected_host evidence)
                     (funding_installed_host evidence) &&
  fingerprints_equal (funding_claimed_proof evidence)
                     (funding_trusted_proof evidence).

Theorem installed_funding_binding_has_exact_three_owners :
  forall evidence,
    funding_install_checks evidence = true ->
    funding_authored_projected evidence = funding_compiled_projected evidence /\
    funding_selected_host evidence = funding_installed_host evidence /\
    funding_claimed_proof evidence = funding_trusted_proof evidence.
Proof.
  intros evidence Hchecks.
  unfold funding_install_checks in Hchecks.
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  end.
  repeat split; eapply fingerprints_equal_sound; eassumption.
Qed.

Theorem wrong_trusted_projection_proof_refuses_install :
  forall evidence,
    funding_claimed_proof evidence <> funding_trusted_proof evidence ->
    funding_install_checks evidence = false.
Proof.
  intros evidence Hwrong.
  destruct (funding_install_checks evidence) eqn:Hchecks;
    [| reflexivity].
  apply installed_funding_binding_has_exact_three_owners in Hchecks
    as [_ [_ Hproof]]. contradiction.
Qed.

(** A host vector field needs its own positional algebra. Encoding it as one
    child of the element sort loses the empty case and every length above one.
    The installed compound profile therefore names distinct Nil and Cons
    constructors of a sequence sort; the typed inverse accepts only this
    algebra and reconstructs the original ordered vector. This theorem covers
    shape and order, not the separate fingerprint/constructor-ID check. *)
Inductive HostSequence (A : Type) : Type :=
| HostNil : HostSequence A
| HostCons : A -> HostSequence A -> HostSequence A.

Arguments HostNil {A}.
Arguments HostCons {A} _ _.

Fixpoint encode_host_sequence {A : Type} (items : list A) : HostSequence A :=
  match items with
  | [] => HostNil
  | item :: tail => HostCons item (encode_host_sequence tail)
  end.

Fixpoint decode_host_sequence {A : Type} (encoded : HostSequence A) : list A :=
  match encoded with
  | HostNil => []
  | HostCons item tail => item :: decode_host_sequence tail
  end.

Theorem host_sequence_round_trip_preserves_empty_length_and_order :
  forall (A : Type) (items : list A),
    decode_host_sequence (encode_host_sequence items) = items.
Proof.
  intros A items. induction items as [| item tail IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Theorem host_sequence_encoding_is_injective :
  forall (A : Type) (left right : list A),
    encode_host_sequence left = encode_host_sequence right -> left = right.
Proof.
  intros A left right Hequal.
  apply (f_equal decode_host_sequence) in Hequal.
  now repeat rewrite host_sequence_round_trip_preserves_empty_length_and_order
    in Hequal.
Qed.

End CheckedCostImage.
