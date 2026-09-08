(** The complete neutral receipt order, tied to the existing wire schema.

    Views are fixed products and finite tagged sums. Their nesting only
    represents the lexicographic field order in this proof; Rust can compare
    borrowed fields without allocating any view. Variable evidence rosters
    retain order and multiplicity. Opcode/effect numbers are projected from
    the existing encoder, so this module does not introduce alternative tags.

    Equality is receipt equality, not equality of an arbitrary attached Par.
    The separate whole-record permutation and pairing models preserve that
    attachment. Logical comparison work is not asserted to be invariant under
    permutations of the input roster. *)
From Stdlib Require Import List Arith.PeanoNat Sorting.Permutation Sorting.Sorted.
From RuntimeGrammar Require Import SemanticComparisonLaws SemanticReceiptWire SemanticResultMerge.
Import ListNotations.

Module SemanticReceiptOrder.
Module L := SemanticComparisonLaws.SemanticComparisonLaws.
Module W := SemanticReceiptWire.SemanticReceiptWire.
Module R := W.R.
Module M := SemanticResultMerge.SemanticResultMerge.

Local Infix "<+>" := L.pair_compare (at level 50, left associativity).
Local Infix "<|>" := L.sum_compare (at level 60, right associativity).

Definition bytes_compare := list_compare Nat.compare.
Lemma bytes_laws : L.Laws bytes_compare.
Proof. apply L.list_laws. exact L.natural_laws. Qed.

Definition uint_atom value := match value with W.UInt n => n | _ => 0 end.
Definition opcode_key opcode := uint_atom (W.encode_opcode opcode).
Definition effect_key effect := uint_atom (W.encode_effect effect).

Lemma opcode_shape : forall opcode, W.encode_opcode opcode = W.UInt (opcode_key opcode).
Proof. destruct opcode; reflexivity. Qed.
Lemma effect_shape : forall effect, W.encode_effect effect = W.UInt (effect_key effect).
Proof. destruct effect; reflexivity. Qed.

Lemma opcode_key_injective : forall a b, opcode_key a = opcode_key b -> a = b.
Proof.
  intros a b H. assert (E : W.encode_opcode a = W.encode_opcode b)
    by (rewrite !opcode_shape; congruence).
  apply (f_equal W.decode_opcode) in E. rewrite !W.opcode_inverse in E. congruence.
Qed.
Lemma effect_key_injective : forall a b, effect_key a = effect_key b -> a = b.
Proof.
  intros a b H. assert (E : W.encode_effect a = W.encode_effect b)
    by (rewrite !effect_shape; congruence).
  apply (f_equal W.decode_effect) in E. rewrite !W.effect_inverse in E. congruence.
Qed.

Definition FreshFields := (nat * nat)%type.
Definition TransitionFields := (nat * nat * nat)%type.
Definition JudgmentFields := (nat * nat * nat * nat * nat)%type.
Definition ForAllFields := (nat * nat * nat)%type.
Definition IntrinsicFields := (nat * nat * nat * list R.Bytes * list R.Bytes * nat)%type.
Definition GuardFields := (nat * nat * R.Bytes * R.Bytes)%type.
Definition PremiseFields :=
  (FreshFields + (TransitionFields + (JudgmentFields + (ForAllFields +
    (IntrinsicFields + GuardFields)))))%type.

Definition premise_view premise : PremiseFields := match premise with
  | R.Freshness rule index => inl (rule, index)
  | R.Transition rule index child => inr (inl (rule, index, child))
  | R.Judgment rule index judgment proofs steps => inr (inr (inl (rule, index, judgment, proofs, steps)))
  | R.ForAll rule index elements => inr (inr (inr (inl (rule, index, elements))))
  | R.Intrinsic rule index opcode inputs outputs work =>
      inr (inr (inr (inr (inl (rule, index, opcode_key opcode, inputs, outputs, work)))))
  | R.Guard rule index guard evidence => inr (inr (inr (inr (inr (rule, index, guard, evidence)))))
  end.

Definition premise_fields_compare :=
  (Nat.compare <+> Nat.compare) <|>
  (Nat.compare <+> Nat.compare <+> Nat.compare) <|>
  (Nat.compare <+> Nat.compare <+> Nat.compare <+> Nat.compare <+> Nat.compare) <|>
  (Nat.compare <+> Nat.compare <+> Nat.compare) <|>
  (Nat.compare <+> Nat.compare <+> Nat.compare <+> list_compare bytes_compare <+>
    list_compare bytes_compare <+> Nat.compare) <|>
  (Nat.compare <+> Nat.compare <+> bytes_compare <+> bytes_compare).

Lemma premise_fields_laws : L.Laws premise_fields_compare.
Proof.
  unfold premise_fields_compare, bytes_compare.
  repeat first [apply L.sum_laws | apply L.pair_laws | apply L.list_laws | exact L.natural_laws].
Qed.

Lemma premise_view_preserves_wire : forall a b,
  premise_view a = premise_view b -> W.encode_premise a = W.encode_premise b.
Proof.
  destruct a, b; cbn [premise_view]; intro H; try discriminate;
    inversion H; subst; cbn [W.encode_premise]; try reflexivity.
  match goal with E : opcode_key _ = opcode_key _ |- _ =>
    apply opcode_key_injective in E; subst end. reflexivity.
Qed.

Lemma premise_view_injective : forall a b, premise_view a = premise_view b -> a = b.
Proof.
  intros a b E. apply premise_view_preserves_wire in E.
  apply (f_equal W.decode_premise) in E. rewrite !W.premise_inverse in E. congruence.
Qed.

Definition premise_compare a b := premise_fields_compare (premise_view a) (premise_view b).
Theorem premise_laws : L.Laws premise_compare.
Proof.
  apply (L.injective_view_laws R.Premise PremiseFields premise_view premise_fields_compare);
    [exact premise_fields_laws | exact premise_view_injective].
Qed.

Definition unit_compare (_ _ : unit) := Eq.
Lemma unit_laws : L.Laws unit_compare.
Proof.
  constructor.
  - intros [] []; split; reflexivity.
  - intros [] []; reflexivity.
  - intros [] [] [] c H1 H2; exact H1.
Qed.

Definition resource_view resource : (unit + (nat * R.Bytes * R.Bytes))%type :=
  match resource with
  | R.NoGrade => inl tt
  | R.CheckedGrade sort grade image => inr (sort, grade, image)
  end.
Definition resource_fields_compare := unit_compare <|> (Nat.compare <+> bytes_compare <+> bytes_compare).
Definition resource_compare a b := resource_fields_compare (resource_view a) (resource_view b).
Lemma resource_view_injective : forall a b, resource_view a = resource_view b -> a = b.
Proof. destruct a, b; cbn [resource_view]; intro H; inversion H; subst; reflexivity. Qed.
Theorem resource_laws : L.Laws resource_compare.
Proof.
  apply (L.injective_view_laws R.Resource _ resource_view resource_fields_compare);
    [| exact resource_view_injective].
  unfold resource_fields_compare, bytes_compare.
  repeat first [apply L.sum_laws | apply L.pair_laws | apply L.list_laws |
    exact L.natural_laws | exact unit_laws].
Qed.

Definition step_view s := (R.step_rule s, R.step_before s, R.step_after s, R.step_premises s).
Definition step_fields_compare := Nat.compare <+> bytes_compare <+> bytes_compare <+> list_compare premise_compare.
Definition step_compare a b := step_fields_compare (step_view a) (step_view b).
Lemma step_view_injective : forall a b, step_view a = step_view b -> a = b.
Proof. destruct a, b; cbn [step_view]; intro H; inversion H; subst; reflexivity. Qed.
Theorem step_laws : L.Laws step_compare.
Proof.
  apply (L.injective_view_laws R.Step _ step_view step_fields_compare); [| exact step_view_injective].
  unfold step_fields_compare, bytes_compare.
  repeat first [apply L.pair_laws | apply L.list_laws | exact L.natural_laws | exact premise_laws].
Qed.

Definition hop_view h := (R.hop_before h, R.hop_after h, R.hop_proofs h, R.hop_work h).
Definition hop_fields_compare := bytes_compare <+> bytes_compare <+> list_compare step_compare <+> Nat.compare.
Definition hop_compare a b := hop_fields_compare (hop_view a) (hop_view b).
Lemma hop_view_injective : forall a b, hop_view a = hop_view b -> a = b.
Proof. destruct a, b; cbn [hop_view]; intro H; inversion H; subst; reflexivity. Qed.
Theorem hop_laws : L.Laws hop_compare.
Proof.
  apply (L.injective_view_laws R.Hop _ hop_view hop_fields_compare); [| exact hop_view_injective].
  unfold hop_fields_compare, bytes_compare.
  repeat first [apply L.pair_laws | apply L.list_laws | exact L.natural_laws | exact step_laws].
Qed.

Definition receipt_view r :=
  (R.language r, R.theory r, R.image r, R.action r, R.rule r, R.input r, R.output r,
   R.effect r, effect_key (R.effect_class r), R.resource r, R.premises r, R.hops r, R.work r).
Definition receipt_fields_compare :=
  bytes_compare <+> bytes_compare <+> bytes_compare <+> Nat.compare <+> Nat.compare <+>
  bytes_compare <+> bytes_compare <+> Nat.compare <+> Nat.compare <+> resource_compare <+>
  list_compare premise_compare <+> list_compare hop_compare <+> Nat.compare.

Lemma receipt_view_preserves_wire : forall a b,
  receipt_view a = receipt_view b -> W.encode_receipt a = W.encode_receipt b.
Proof.
  destruct a, b; cbn [receipt_view]; intro H; inversion H; subst.
  match goal with E : effect_key _ = effect_key _ |- _ =>
    apply effect_key_injective in E; subst end. reflexivity.
Qed.
Lemma receipt_view_injective : forall a b, receipt_view a = receipt_view b -> a = b.
Proof.
  intros a b E. apply W.receipt_encoding_is_injective.
  apply receipt_view_preserves_wire; exact E.
Qed.
Definition receipt_compare a b := receipt_fields_compare (receipt_view a) (receipt_view b).
Theorem receipt_laws : L.Laws receipt_compare.
Proof.
  apply (L.injective_view_laws R.Receipt _ receipt_view receipt_fields_compare);
    [| exact receipt_view_injective].
  unfold receipt_fields_compare, bytes_compare.
  repeat first [apply L.pair_laws | apply L.list_laws | exact L.natural_laws |
    exact resource_laws | exact premise_laws | exact hop_laws].
Qed.

Definition result_key_compare a b := (bytes_compare <+> receipt_compare) (R.output a, a) (R.output b, b).
Theorem result_key_laws : L.Laws result_key_compare.
Proof.
  apply (L.injective_view_laws R.Receipt _ (fun r => (R.output r, r))
    (bytes_compare <+> receipt_compare)).
  - apply L.pair_laws; [exact bytes_laws | exact receipt_laws].
  - intros a b E. exact (f_equal (@snd R.Bytes R.Receipt) E).
Qed.

Theorem result_key_equality_is_complete_receipt_equality : forall a b,
  result_key_compare a b = Eq <-> a = b.
Proof. apply (L.comparison_eq result_key_laws). Qed.

Theorem result_key_has_a_total_transitive_order :
  (forall a b, result_key_compare a b <> Gt \/ result_key_compare b a <> Gt) /\
  (forall a b c, result_key_compare a b <> Gt -> result_key_compare b c <> Gt ->
    result_key_compare a c <> Gt).
Proof.
  split; [apply L.not_greater_is_total | apply L.not_greater_is_transitive]; exact result_key_laws.
Qed.

Definition result_le a b := result_key_compare a b <> Gt.

Lemma result_le_antisymmetric : forall a b, result_le a b -> result_le b a -> a = b.
Proof.
  intros a b AB BA. unfold result_le in *.
  rewrite (L.comparison_opposite result_key_laws a b) in BA.
  destruct (result_key_compare a b) eqn:E; cbn in BA; try contradiction.
  apply (L.comparison_eq result_key_laws); exact E.
Qed.

(** The standard sorted-permutation uniqueness proof, adapted from the node's
    rb_strongly_sorted_perm_eq. This concerns the complete neutral receipt
    sequence, not arbitrary mutable attached records or their usage counters. *)
Theorem sorted_receipt_permutation_is_unique : forall left right,
  StronglySorted result_le left -> StronglySorted result_le right ->
  Permutation left right -> left = right.
Proof.
  induction left as [|a left IH]; intros right SL SR P.
  - apply Permutation_nil in P. symmetry; exact P.
  - destruct right as [|b right].
    { apply Permutation_sym in P. apply Permutation_nil in P. discriminate. }
    destruct (StronglySorted_inv SL) as [SLT LA].
    destruct (StronglySorted_inv SR) as [SRT LB].
    assert (B : In b (a :: left)).
    { eapply Permutation_in; [apply Permutation_sym; exact P | left; reflexivity]. }
    assert (A : In a (b :: right)).
    { eapply Permutation_in; [exact P | left; reflexivity]. }
    assert (E : a = b).
    { destruct B as [E | B]; [exact E |].
      destruct A as [E | A]; [symmetry; exact E |].
      rewrite Forall_forall in LA, LB. apply result_le_antisymmetric;
        [apply LA; exact B | apply LB; exact A]. }
    subst b. apply Permutation_cons_inv in P. f_equal. apply IH; assumption.
Qed.

Theorem successful_receipt_sorts_are_canonical : forall (State : Type)
  (compare : R.Receipt -> R.Receipt -> State -> option comparison * State),
  (forall a b state decision next, compare a b state = (Some decision, next) ->
    result_key_compare a b = decision) ->
  forall left right state_left state_right output_left output_right final_left final_right,
  Permutation left right ->
  M.sort compare left state_left = (Some output_left, final_left) ->
  M.sort compare right state_right = (Some output_right, final_right) ->
  output_left = output_right.
Proof.
  intros State compare faithful left right state_left state_right output_left output_right
    final_left final_right P LSort RSort.
  assert (trans : forall a b c, result_le a b -> result_le b c -> result_le a c).
  { apply (L.not_greater_is_transitive R.Receipt result_key_compare result_key_laws). }
  assert (sound : forall a b state decision next,
    compare a b state = (Some decision, next) ->
    match decision with Gt => result_le b a | _ => result_le a b end).
  { apply (M.exact_key_comparison_is_sound compare R.Receipt (fun r => r) result_key_compare
      (L.comparison_opposite result_key_laws) faithful). }
  apply sorted_receipt_permutation_is_unique.
  - eapply M.sort_is_sorted; [exact trans | exact sound | exact LSort].
  - eapply M.sort_is_sorted; [exact trans | exact sound | exact RSort].
  - eapply Permutation_trans; [apply Permutation_sym; eapply M.sort_preserves_occurrences; exact LSort |].
    eapply Permutation_trans; [exact P | eapply M.sort_preserves_occurrences; exact RSort].
Qed.

End SemanticReceiptOrder.

Print Assumptions SemanticReceiptOrder.premise_view_preserves_wire.
Print Assumptions SemanticReceiptOrder.premise_laws.
Print Assumptions SemanticReceiptOrder.resource_laws.
Print Assumptions SemanticReceiptOrder.step_laws.
Print Assumptions SemanticReceiptOrder.hop_laws.
Print Assumptions SemanticReceiptOrder.receipt_view_preserves_wire.
Print Assumptions SemanticReceiptOrder.receipt_laws.
Print Assumptions SemanticReceiptOrder.result_key_laws.
Print Assumptions SemanticReceiptOrder.result_key_equality_is_complete_receipt_equality.
Print Assumptions SemanticReceiptOrder.result_key_has_a_total_transitive_order.
Print Assumptions SemanticReceiptOrder.sorted_receipt_permutation_is_unique.
Print Assumptions SemanticReceiptOrder.successful_receipt_sorts_are_canonical.
