(** Structural category admission for native token values.

    TokenCategoryNormalization already proves that category-tagged tokens
    contribute a category derivation without a synthetic constructor. This
    model supplies the missing structural-admission boundary. It distinguishes
    a known successful output shape, an impossible evaluation, and an absent
    callback output contract. No decoder/evaluator is executed by admission.

    Payload decoding, UTF-8/canonical-integer validation and host capability
    authorization remain the existing implementations' obligations. The finite
    evaluator relation below projects only their actual output-kind cases; it
    does not claim that every value of the output kind is a lexical image.
    Constructor branch judgments are supplied by the existing structural
    automaton. The combination laws retain them, not assume their correctness.
*)
From Stdlib Require Import List Bool PeanoNat Lia.
From RuntimeGrammar Require Import TokenCategoryNormalization.
Import ListNotations.

Module DynamicCategoryAdmission.

Inductive ValueKind :=
| Text | Integer | Boolean | Bytes | Unit | Sequence | Collection | Term | Hole.

Definition kind_eqb (left right : ValueKind) : bool :=
  match left, right with
  | Text, Text | Integer, Integer | Boolean, Boolean | Bytes, Bytes
  | Unit, Unit | Sequence, Sequence | Collection, Collection | Term, Term
  | Hole, Hole => true
  | _, _ => false
  end.

Lemma kind_eqb_exact : forall left right,
  kind_eqb left right = true <-> left = right.
Proof. destruct left, right; simpl; split; intros; congruence. Qed.

Inductive OutputContract :=
| Known (kind : ValueKind)
| NoSuccessfulOutput
| UnavailableContract.

Definition describes (contract : OutputContract) (kind : ValueKind) : Prop :=
  match contract with
  | Known expected => kind = expected
  | NoSuccessfulOutput => False
  | UnavailableContract => True
  end.

Inductive Decoder :=
| DecodeText | DecodeInteger | DecodeBoolean | DecodeBytes | DecodeUnit
| DecodeCapability.

Definition decoder_contract (decoder : Decoder) : OutputContract :=
  match decoder with
  | DecodeText => Known Text | DecodeInteger => Known Integer
  | DecodeBoolean => Known Boolean | DecodeBytes => Known Bytes
  | DecodeUnit => Known Unit | DecodeCapability => UnavailableContract
  end.

Inductive Decodes : Decoder -> ValueKind -> Prop :=
| DecodesText : Decodes DecodeText Text
| DecodesInteger : Decodes DecodeInteger Integer
| DecodesBoolean : Decodes DecodeBoolean Boolean
| DecodesBytes : Decodes DecodeBytes Bytes
| DecodesUnit : Decodes DecodeUnit Unit
| DecodesCapability : forall kind, Decodes DecodeCapability kind.

Lemma decoder_success_has_its_contract : forall decoder kind,
  Decodes decoder kind -> describes (decoder_contract decoder) kind.
Proof. intros decoder kind H. inversion H; subst; simpl; auto. Qed.

(** Tokens supply one input. Rat/fixed/float currently return Text, not a
    rational or floating native value. Binary operators have no unary case. *)
Inductive Evaluation :=
| Identity | CarrierInteger | CarrierBoolean | CarrierText | CarrierNumericText
| Negate | BooleanNot | Length | BinaryOperator | Handler | ForbiddenOrUnknown.

Inductive Evaluates : Evaluation -> ValueKind -> ValueKind -> Prop :=
| EvalIdentity : forall kind, Evaluates Identity kind kind
| EvalIntegerInteger : Evaluates CarrierInteger Integer Integer
| EvalIntegerText : Evaluates CarrierInteger Text Integer
| EvalBooleanBoolean : Evaluates CarrierBoolean Boolean Boolean
| EvalBooleanText : Evaluates CarrierBoolean Text Boolean
| EvalText : Evaluates CarrierText Text Text
| EvalNumericText : Evaluates CarrierNumericText Text Text
| EvalNegate : Evaluates Negate Integer Integer
| EvalNot : Evaluates BooleanNot Boolean Boolean
| EvalLengthText : Evaluates Length Text Integer
| EvalLengthBytes : Evaluates Length Bytes Integer
| EvalLengthSequence : Evaluates Length Sequence Integer
| EvalLengthCollection : Evaluates Length Collection Integer
| EvalHandler : forall input output, Evaluates Handler input output.

Definition narrow (input : OutputContract) (accepted : list ValueKind)
    (output : ValueKind) : OutputContract :=
  match input with
  | Known kind => if existsb (kind_eqb kind) accepted
                  then Known output else NoSuccessfulOutput
  | NoSuccessfulOutput => NoSuccessfulOutput
  | UnavailableContract => Known output
  end.

Definition evaluation_contract (evaluation : Evaluation)
    (input : OutputContract) : OutputContract :=
  match evaluation with
  | Identity => input
  | CarrierInteger => narrow input [Integer; Text] Integer
  | CarrierBoolean => narrow input [Boolean; Text] Boolean
  | CarrierText | CarrierNumericText => narrow input [Text] Text
  | Negate => narrow input [Integer] Integer
  | BooleanNot => narrow input [Boolean] Boolean
  | Length => narrow input [Text; Bytes; Sequence; Collection] Integer
  | Handler => match input with
      | NoSuccessfulOutput => NoSuccessfulOutput
      | _ => UnavailableContract end
  | BinaryOperator | ForbiddenOrUnknown => NoSuccessfulOutput
  end.

Theorem evaluation_success_preserves_the_computed_contract :
  forall evaluation input output contract,
    Evaluates evaluation input output -> describes contract input ->
    describes (evaluation_contract evaluation contract) output.
Proof.
  intros evaluation input output contract Heval Hinput.
  inversion Heval; subst; destruct contract as [kind| |]; simpl in *;
    try contradiction; try exact I; try assumption;
    subst; simpl; auto.
Qed.

Definition token_contract (decoder : Decoder) (evaluation : Evaluation) :=
  evaluation_contract evaluation (decoder_contract decoder).

Theorem known_token_output_is_sound : forall decoder evaluation input output expected,
  Decodes decoder input -> Evaluates evaluation input output ->
  token_contract decoder evaluation = Known expected -> output = expected.
Proof.
  intros decoder evaluation input output expected Hdecode Heval Hcontract.
  pose proof (decoder_success_has_its_contract decoder input Hdecode) as Hinput.
  pose proof (evaluation_success_preserves_the_computed_contract
    evaluation input output (decoder_contract decoder) Heval Hinput) as Houtput.
  unfold token_contract in Hcontract. rewrite Hcontract in Houtput. exact Houtput.
Qed.

Theorem no_success_contract_really_has_no_output : forall decoder evaluation input output,
  token_contract decoder evaluation = NoSuccessfulOutput ->
  Decodes decoder input -> ~ Evaluates evaluation input output.
Proof.
  intros decoder evaluation input output Hcontract Hdecode Heval.
  pose proof (decoder_success_has_its_contract decoder input Hdecode) as Hinput.
  pose proof (evaluation_success_preserves_the_computed_contract
    evaluation input output (decoder_contract decoder) Heval Hinput) as Houtput.
  unfold token_contract in Hcontract. rewrite Hcontract in Houtput. exact Houtput.
Qed.

Inductive Judgment := Accepted | Rejected | Unknown.

Definition alternative (left right : Judgment) : Judgment :=
  match left, right with
  | Accepted, _ | _, Accepted => Accepted
  | Unknown, _ | _, Unknown => Unknown
  | Rejected, Rejected => Rejected
  end.

Definition conjunction (left right : Judgment) : Judgment :=
  match left, right with
  | Rejected, _ | _, Rejected => Rejected
  | Unknown, _ | _, Unknown => Unknown
  | Accepted, Accepted => Accepted
  end.

Definition any_branch (branches : list Judgment) : Judgment :=
  fold_right alternative Rejected branches.

Lemma alternative_rejected_identity : forall value,
  alternative value Rejected = value.
Proof. destruct value; reflexivity. Qed.

Definition all_fields (fields : list Judgment) : Judgment :=
  fold_right conjunction Accepted fields.

Lemma any_branch_accepted_exact : forall branches,
  any_branch branches = Accepted <-> In Accepted branches.
Proof.
  induction branches as [|branch rest IH]; simpl.
  - split; [discriminate|contradiction].
  - destruct branch; destruct (any_branch rest); simpl in *; intuition congruence.
Qed.

Lemma conjunction_accepted_exact : forall left right,
  conjunction left right = Accepted <-> left = Accepted /\ right = Accepted.
Proof. destruct left, right; simpl; intuition discriminate. Qed.

Lemma all_fields_accepted_exact : forall fields,
  all_fields fields = Accepted <-> Forall (fun field => field = Accepted) fields.
Proof.
  induction fields as [|field rest IH]; simpl.
  - split; [intro; constructor|intro; reflexivity].
  - rewrite conjunction_accepted_exact, IH. split.
    + intros [Hfield Hrest]. constructor; assumption.
    + intro H. inversion H; subst. auto.
Qed.

Theorem category_union_keeps_every_accepted_constructor : forall constructors natives,
  any_branch constructors = Accepted ->
  any_branch (constructors ++ natives) = Accepted.
Proof.
  intros constructors natives H. apply any_branch_accepted_exact in H.
  apply any_branch_accepted_exact. apply in_or_app. auto.
Qed.

Theorem category_union_accepts_only_a_justified_branch : forall constructors natives,
  any_branch (constructors ++ natives) = Accepted ->
  In Accepted constructors \/ In Accepted natives.
Proof.
  intros constructors natives H. apply any_branch_accepted_exact in H.
  now apply in_app_iff in H.
Qed.

Definition native_branch (contract : OutputContract) (kind : ValueKind) : Judgment :=
  match contract with
  | Known expected => if kind_eqb expected kind then Accepted else Rejected
  | NoSuccessfulOutput => Rejected
  | UnavailableContract => Unknown
  end.

Theorem native_acceptance_requires_an_exact_known_kind : forall contract kind,
  native_branch contract kind = Accepted <-> contract = Known kind.
Proof.
  intros [expected| |] kind; simpl; try (split; discriminate).
  destruct (kind_eqb expected kind) eqn:Hkind; split; intro H; try discriminate.
  - apply kind_eqb_exact in Hkind. now subst.
  - reflexivity.
  - inversion H; subst. rewrite (proj2 (kind_eqb_exact kind kind) eq_refl) in Hkind.
    discriminate.
Qed.

Theorem unavailable_native_contract_is_not_rejection_or_acceptance : forall kind,
  native_branch UnavailableContract kind = Unknown /\
  native_branch UnavailableContract kind <> Rejected /\
  native_branch UnavailableContract kind <> Accepted.
Proof. intros. repeat split; discriminate. Qed.

(** A declared canonical carrier is independent of source-token existence.
    Dynamic syntax categories instead use their known token output contracts.
    Captured token fields use [token_contract] directly, not this policy. *)
Inductive CategoryCarrier :=
| DynamicCarrier
| DeclaredNative (kind : ValueKind)
| UnsupportedCarrier.

Definition category_native_contracts (carrier : CategoryCarrier)
    (tokens : list OutputContract) : list OutputContract :=
  match carrier with
  | DynamicCarrier => tokens
  | DeclaredNative kind => [Known kind]
  | UnsupportedCarrier => [UnavailableContract]
  end.

Definition category_native_branch (carrier : CategoryCarrier)
    (tokens : list OutputContract) (kind : ValueKind) : Judgment :=
  any_branch (map (fun contract => native_branch contract kind)
    (category_native_contracts carrier tokens)).

Theorem declared_carrier_cannot_be_widened_by_token_outputs :
  forall expected tokens kind,
    category_native_branch (DeclaredNative expected) tokens kind = Accepted <->
    kind = expected.
Proof.
  intros expected tokens kind.
  change (alternative (native_branch (Known expected) kind) Rejected = Accepted <->
    kind = expected).
  rewrite alternative_rejected_identity.
  rewrite native_acceptance_requires_an_exact_known_kind. split; congruence.
Qed.

Theorem declared_carrier_needs_no_lexical_token : forall kind,
  category_native_branch (DeclaredNative kind) [] kind = Accepted.
Proof. intro kind. apply declared_carrier_cannot_be_widened_by_token_outputs. reflexivity. Qed.

(** Exact fingerprint is an independent rejection gate. Nullary shape is
    required only by a known native-leaf contract. An unrestricted callback
    may return a nonnullary value, so an unavailable contract uses the existing
    structural automaton's envelope judgment: rejection stays rejection;
    either other result stays unknown. It never grants native-kind evidence.
    Canonical payload validation remains the existing native validators' job. *)
Definition unavailable_branch (envelope : Judgment) : Judgment :=
  match envelope with Rejected => Rejected | _ => Unknown end.

Definition checked_native_branch (expected actual child_count : nat)
    (envelope : Judgment) (contract : OutputContract) (kind : ValueKind) : Judgment :=
  if Nat.eqb expected actual then
    match contract with
    | Known _ => if Nat.eqb child_count 0
                 then native_branch contract kind else Rejected
    | NoSuccessfulOutput => Rejected
    | UnavailableContract => unavailable_branch envelope
    end
  else Rejected.

Theorem foreign_fingerprint_is_rejected_even_without_a_contract :
  forall expected actual children envelope contract kind,
    expected <> actual ->
    checked_native_branch expected actual children envelope contract kind = Rejected.
Proof.
  intros expected actual children envelope contract kind Hforeign.
  unfold checked_native_branch. apply Nat.eqb_neq in Hforeign.
  rewrite Hforeign. reflexivity.
Qed.

Theorem nonnullary_shape_is_rejected_by_a_known_native_contract :
  forall expected actual children envelope native_kind kind,
    children <> 0 ->
    checked_native_branch expected actual children envelope (Known native_kind) kind = Rejected.
Proof.
  intros expected actual children envelope native_kind kind Hchildren.
  unfold checked_native_branch. apply Nat.eqb_neq in Hchildren.
  rewrite Hchildren. destruct (Nat.eqb expected actual); reflexivity.
Qed.

Theorem unavailable_contract_preserves_structural_rejection :
  forall expected actual children kind,
    checked_native_branch expected actual children Rejected UnavailableContract kind = Rejected.
Proof. intros. unfold checked_native_branch. destruct (Nat.eqb expected actual); reflexivity. Qed.

Theorem unavailable_contract_cannot_supply_positive_evidence : forall envelope,
  unavailable_branch envelope <> Accepted.
Proof. destruct envelope; discriminate. Qed.

Example valid_nonnullary_callback_output_is_unknown :
  checked_native_branch 7 7 1 Accepted UnavailableContract Sequence = Unknown.
Proof. reflexivity. Qed.

(** Logical work for checking already scheduled branches. Exhaustion stops
    the request; it cannot turn the unvisited suffix into an empty disjunction.
    This is not a proof of byte allocation bounds in the existing reflector. *)
Fixpoint bounded_any (fuel : nat) (pending : list Judgment) (private : Judgment)
    {struct pending} : Judgment :=
  match pending with
  | [] => private
  | branch :: rest => match fuel with
      | 0 => Unknown
      | S fuel => bounded_any fuel rest (alternative private branch)
      end
  end.

Lemma alternative_associative : forall a b c,
  alternative (alternative a b) c = alternative a (alternative b c).
Proof. destruct a, b, c; reflexivity. Qed.

Theorem sufficient_budget_preserves_the_complete_branch_union :
  forall pending fuel private,
    length pending <= fuel ->
    bounded_any fuel pending private = alternative private (any_branch pending).
Proof.
  induction pending as [|branch rest IH]; intros fuel private Hfuel; simpl.
  - symmetry. apply alternative_rejected_identity.
  - destruct fuel; [simpl in Hfuel; lia|].
    rewrite IH by (simpl in Hfuel; lia). apply alternative_associative.
Qed.

Theorem exhaustion_is_unknown_not_empty_rejection : forall pending fuel private,
  fuel < length pending -> bounded_any fuel pending private = Unknown.
Proof.
  induction pending as [|branch rest IH]; intros fuel private Hfuel;
    destruct fuel; simpl in *; try lia; auto.
  apply IH. lia.
Qed.

Lemma alternative_rejected_left_identity : forall value,
  alternative Rejected value = value.
Proof. destruct value; reflexivity. Qed.

Lemma bounded_success_has_complete_evidence : forall branches fuel,
  bounded_any fuel branches Rejected = Accepted -> any_branch branches = Accepted.
Proof.
  intros branches fuel Hsuccess.
  destruct (Nat.lt_ge_cases fuel (length branches)) as [Hshort|Henough].
  - rewrite exhaustion_is_unknown_not_empty_rejection in Hsuccess by exact Hshort.
    discriminate.
  - rewrite sufficient_budget_preserves_the_complete_branch_union in Hsuccess
      by exact Henough.
    now rewrite alternative_rejected_left_identity in Hsuccess.
Qed.

Lemma checked_native_acceptance_is_bound : forall expected actual children envelope contract kind,
  checked_native_branch expected actual children envelope contract kind = Accepted ->
  expected = actual /\ children = 0 /\ contract = Known kind.
Proof.
  intros expected actual children envelope contract kind H.
  unfold checked_native_branch in H.
  destruct (Nat.eqb expected actual) eqn:Hfp; try discriminate.
  destruct contract as [native_kind| |]; try discriminate.
  2: { destruct envelope; discriminate. }
  destruct (Nat.eqb children 0) eqn:Hchildren; try discriminate.
  apply Nat.eqb_eq in Hfp. apply Nat.eqb_eq in Hchildren.
  apply native_acceptance_requires_an_exact_known_kind in H. auto.
Qed.

(** [tokens] is the already category-selected list, not all grammar tokens.
    Compilation selects it using TokenDefinition.category, whose recognition
    meaning is established by TokenCategoryNormalization. This model proves
    the following operation for that selected list; cross-category selection
    must also be checked by the concrete compiler's two-category regression. *)
Definition checked_category_branches (carrier : CategoryCarrier)
    (tokens : list OutputContract) (expected actual children : nat)
    (envelope : Judgment) (kind : ValueKind) (constructors : list Judgment) : list Judgment :=
  constructors ++ map (fun contract =>
    checked_native_branch expected actual children envelope contract kind)
    (category_native_contracts carrier tokens).

Definition check_category (fuel : nat) (carrier : CategoryCarrier)
    (tokens : list OutputContract) (expected actual children : nat)
    (envelope : Judgment) (kind : ValueKind) (constructors : list Judgment) : Judgment :=
  if Nat.eqb expected actual then
    bounded_any fuel
      (checked_category_branches carrier tokens expected actual children envelope kind constructors)
      Rejected
  else Rejected.

Theorem composed_category_acceptance_has_justified_bound_evidence :
  forall fuel carrier tokens expected actual children envelope kind constructors,
    check_category fuel carrier tokens expected actual children envelope kind constructors = Accepted ->
    expected = actual /\
    (In Accepted constructors \/
      (In (Known kind) (category_native_contracts carrier tokens) /\ children = 0)).
Proof.
  intros fuel carrier tokens expected actual children envelope kind constructors Hsuccess.
  unfold check_category in Hsuccess.
  destruct (Nat.eqb expected actual) eqn:Hfp; try discriminate.
  apply Nat.eqb_eq in Hfp. split; [exact Hfp|].
  apply bounded_success_has_complete_evidence in Hsuccess.
  apply any_branch_accepted_exact in Hsuccess.
  unfold checked_category_branches in Hsuccess.
  apply in_app_iff in Hsuccess as [Hconstructor|Hnative]; [now left|right].
  apply in_map_iff in Hnative as [contract [Haccepted Hin]].
  apply checked_native_acceptance_is_bound in Haccepted.
  destruct Haccepted as [_ [Hchildren Hcontract]]. now subst.
Qed.

Theorem composed_category_complete_with_sufficient_fuel :
  forall fuel carrier tokens expected actual children envelope kind constructors,
    expected = actual ->
    length (checked_category_branches carrier tokens expected actual children envelope kind constructors)
      <= fuel ->
    check_category fuel carrier tokens expected actual children envelope kind constructors =
      any_branch (checked_category_branches carrier tokens expected actual children envelope kind constructors).
Proof.
  intros fuel carrier tokens expected actual children envelope kind constructors Hfp Hfuel.
  unfold check_category. subst actual. rewrite Nat.eqb_refl.
  rewrite sufficient_budget_preserves_the_complete_branch_union by exact Hfuel.
  apply alternative_rejected_left_identity.
Qed.

Theorem composed_category_exhaustion_is_unknown :
  forall fuel carrier tokens expected actual children envelope kind constructors,
    expected = actual ->
    fuel < length (checked_category_branches carrier tokens expected actual children envelope kind constructors) ->
    check_category fuel carrier tokens expected actual children envelope kind constructors = Unknown.
Proof.
  intros fuel carrier tokens expected actual children envelope kind constructors Hfp Hfuel.
  unfold check_category. subst actual. rewrite Nat.eqb_refl.
  now apply exhaustion_is_unknown_not_empty_rejection.
Qed.

Theorem composed_category_rejects_foreign_fingerprint_before_branches :
  forall fuel carrier tokens expected actual children envelope kind constructors,
    expected <> actual ->
    check_category fuel carrier tokens expected actual children envelope kind constructors = Rejected.
Proof.
  intros fuel carrier tokens expected actual children envelope kind constructors Hforeign.
  unfold check_category. apply Nat.eqb_neq in Hforeign. now rewrite Hforeign.
Qed.

Example mixed_category_preserves_constructor_and_native_evidence :
  any_branch [Accepted; native_branch (Known Text) Integer] = Accepted /\
  any_branch [Rejected; native_branch (Known Text) Text] = Accepted.
Proof. split; reflexivity. Qed.

Example unknown_callback_does_not_admit_an_arbitrary_constructor :
  native_branch (token_contract DecodeCapability Identity) Term = Unknown.
Proof. reflexivity. Qed.

Example closed_evaluator_narrows_a_callback_output :
  token_contract DecodeCapability CarrierText = Known Text.
Proof. reflexivity. Qed.

Example incompatible_unary_input_cannot_produce_a_value :
  token_contract DecodeText Negate = NoSuccessfulOutput.
Proof. reflexivity. Qed.

Example numeric_text_does_not_become_a_native_number :
  token_contract DecodeText CarrierNumericText = Known Text.
Proof. reflexivity. Qed.

Print Assumptions evaluation_success_preserves_the_computed_contract.
Print Assumptions known_token_output_is_sound.
Print Assumptions no_success_contract_really_has_no_output.
Print Assumptions any_branch_accepted_exact.
Print Assumptions all_fields_accepted_exact.
Print Assumptions category_union_keeps_every_accepted_constructor.
Print Assumptions category_union_accepts_only_a_justified_branch.
Print Assumptions native_acceptance_requires_an_exact_known_kind.
Print Assumptions unavailable_native_contract_is_not_rejection_or_acceptance.
Print Assumptions declared_carrier_cannot_be_widened_by_token_outputs.
Print Assumptions declared_carrier_needs_no_lexical_token.
Print Assumptions foreign_fingerprint_is_rejected_even_without_a_contract.
Print Assumptions nonnullary_shape_is_rejected_by_a_known_native_contract.
Print Assumptions unavailable_contract_preserves_structural_rejection.
Print Assumptions unavailable_contract_cannot_supply_positive_evidence.
Print Assumptions sufficient_budget_preserves_the_complete_branch_union.
Print Assumptions exhaustion_is_unknown_not_empty_rejection.
Print Assumptions composed_category_acceptance_has_justified_bound_evidence.
Print Assumptions composed_category_complete_with_sufficient_fuel.
Print Assumptions composed_category_exhaustion_is_unknown.
Print Assumptions composed_category_rejects_foreign_fingerprint_before_branches.

End DynamicCategoryAdmission.
