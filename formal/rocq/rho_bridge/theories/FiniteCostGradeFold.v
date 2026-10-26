(*
 * A finite generator roster is enough to interpret arbitrarily long Cost(G)
 * product trees only when the selected interpretation also supplies a checked
 * unit and product operation.  This model intentionally keeps the signature
 * product distinct from both process parallel composition and stack cons.
 *
 * The Rust checker must establish the premises of this model from exact
 * compiled constructor/rule IDs.  It does not establish the host Delta/Sigma
 * bound; that remains a separate checked template law.
 *)

From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.

Inductive Grade : Type :=
| GradeUnit
| GradeGenerator (id : nat)
| GradeProduct (left right : Grade).

(* Guest constructor identities certify roster coverage. This finite fragment
   interprets every such constructor as the SAME fixed host #Nil lane; none
   of the guest IDs is a host signature. Lists retain occurrence order, while
   equivalence of host signatures is pointwise multiplicity. *)
Fixpoint grade_generators (grade : Grade) : list nat :=
  match grade with
  | GradeUnit => []
  | GradeGenerator id => [id]
  | GradeProduct lhs rhs => grade_generators lhs ++ grade_generators rhs
  end.

Definition nil_lane : nat := 0.

Fixpoint signature_atoms (grade : Grade) : list nat :=
  match grade with
  | GradeUnit => []
  | GradeGenerator _ => [nil_lane]
  | GradeProduct lhs rhs => signature_atoms lhs ++ signature_atoms rhs
  end.

Theorem every_certified_generator_uses_nil_lane : forall grade lane,
    In lane (signature_atoms grade) -> lane = nil_lane.
Proof.
  induction grade as [|id|lhs IHlhs rhs IHrhs]; intros lane Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hnone]; [symmetry; exact Heq | contradiction].
  - apply in_app_or in Hin. destruct Hin as [Hleft | Hright].
    + exact (IHlhs lane Hleft).
    + exact (IHrhs lane Hright).
Qed.

Theorem no_guest_generator_occurrence_is_lost : forall grade,
    length (signature_atoms grade) = length (grade_generators grade).
Proof.
  induction grade as [|id|lhs IHlhs rhs IHrhs]; simpl; try reflexivity.
  repeat rewrite length_app. lia.
Qed.

Definition signature_count (id : nat) (grade : Grade) : nat :=
  count_occ Nat.eq_dec (signature_atoms grade) id.

Theorem signature_unit_identity : forall grade id,
    signature_count id (GradeProduct GradeUnit grade) =
    signature_count id grade /\
    signature_count id (GradeProduct grade GradeUnit) =
    signature_count id grade.
Proof.
  intros grade id; unfold signature_count; simpl.
  rewrite app_nil_r; auto.
Qed.

Theorem signature_product_adds : forall left right id,
    signature_count id (GradeProduct left right) =
    signature_count id left + signature_count id right.
Proof.
  intros left right id; unfold signature_count; simpl.
  apply count_occ_app.
Qed.

Theorem fixed_lane_multiplicity_equals_generator_occurrences : forall grade,
    signature_count nil_lane grade = length (grade_generators grade).
Proof.
  induction grade as [|id|lhs IHlhs rhs IHrhs].
  - reflexivity.
  - unfold signature_count; simpl.
    destruct (Nat.eq_dec nil_lane nil_lane) as [_ | Hneq].
    + reflexivity.
    + exfalso; apply Hneq; reflexivity.
  - rewrite signature_product_adds. simpl.
    rewrite length_app. lia.
Qed.

Theorem signature_product_commutative_by_count : forall left right id,
    signature_count id (GradeProduct left right) =
    signature_count id (GradeProduct right left).
Proof.
  intros left right id.
  repeat rewrite signature_product_adds.
  apply Nat.add_comm.
Qed.

Theorem signature_product_associative_by_count : forall a b c id,
    signature_count id (GradeProduct (GradeProduct a b) c) =
    signature_count id (GradeProduct a (GradeProduct b c)).
Proof.
  intros a b c id.
  repeat rewrite signature_product_adds.
  symmetry; apply Nat.add_assoc.
Qed.

Theorem product_keeps_every_generator_occurrence : forall lhs rhs,
    length (signature_atoms (GradeProduct lhs rhs)) =
    length (signature_atoms lhs) + length (signature_atoms rhs).
Proof.
  intros lhs rhs; simpl; apply length_app.
Qed.

Fixpoint grade_nodes (grade : Grade) : nat :=
  match grade with
  | GradeUnit | GradeGenerator _ => 1
  | GradeProduct lhs rhs => 1 + grade_nodes lhs + grade_nodes rhs
  end.

Theorem flat_signature_count_bounded_by_tree_work : forall grade,
    length (signature_atoms grade) <= grade_nodes grade.
Proof.
  induction grade as [|id|lhs IHlhs rhs IHrhs]; simpl; try lia.
  rewrite length_app; lia.
Qed.

Theorem flat_signature_backing_bounded_by_tree_work : forall grade cell_bytes,
    length (signature_atoms grade) * cell_bytes <= grade_nodes grade * cell_bytes.
Proof.
  intros grade cell_bytes.
  pose proof (flat_signature_count_bounded_by_tree_work grade).
  nia.
Qed.

(* The fixed host Proc template has one signed empty region on the canonical
   compound signature lane. This is not the same operation as parallelizing
   one signed region per generator: product changes the lane, not the number
   of signed regions. The native Delta/Sigma differential test checks this
   abstract law against the real Rholang resource logic. *)
Definition template_demand_lanes (grade : Grade) : list (list nat) :=
  match signature_atoms grade with
  | [] => []
  | atoms => [atoms]
  end.

Theorem unit_template_has_no_demand :
    template_demand_lanes GradeUnit = [].
Proof. reflexivity. Qed.

Theorem product_template_uses_one_compound_lane : forall lhs rhs,
    signature_atoms lhs ++ signature_atoms rhs <> [] ->
    template_demand_lanes (GradeProduct lhs rhs) =
      [signature_atoms lhs ++ signature_atoms rhs].
Proof.
  intros lhs rhs Hnonempty.
  unfold template_demand_lanes; simpl.
  destruct (signature_atoms lhs ++ signature_atoms rhs) as [|atom rest] eqn:Hatoms.
  - exfalso; apply Hnonempty; reflexivity.
  - reflexivity.
Qed.

(* The finite certificate checks that every source rewrite grade is a listed
   nullary generator or the unit.  The inductive fold then covers every tree
   that Dovetail can make by its product constructor, at any finite depth. *)
Definition generator_covered (roster : list nat) (id : nat) : Prop :=
  In id roster.

Fixpoint grade_covered (roster : list nat) (grade : Grade) : Prop :=
  match grade with
  | GradeUnit => True
  | GradeGenerator id => generator_covered roster id
  | GradeProduct lhs rhs =>
      grade_covered roster lhs /\ grade_covered roster rhs
  end.

Theorem covered_product_closed : forall roster left right,
    grade_covered roster left ->
    grade_covered roster right ->
    grade_covered roster (GradeProduct left right).
Proof. intros roster left right Hleft Hright; simpl; auto. Qed.

Theorem listed_generators_cover_all_compositions : forall roster grade,
    (forall id, In id (grade_generators grade) -> In id roster) ->
    grade_covered roster grade.
Proof.
  intros roster grade.
  induction grade as [|id|left IHleft right IHright]; simpl; auto.
  - intro H; apply H; simpl; auto.
  - intro H; split.
    + apply IHleft. intros id Hin. apply H. apply in_or_app. left; exact Hin.
    + apply IHright. intros id Hin. apply H. apply in_or_app. right; exact Hin.
Qed.

(* The runtime can re-admit only an owner-borrowed token produced by following
   a child edge of the exact admitted grade. Raw e-class numbers are never
   accepted as subroots: their numeric values can alias across inputs. *)
Inductive Reachable : Grade -> Grade -> Prop :=
| reachable_here : forall root, Reachable root root
| reachable_left : forall lhs rhs sub,
    Reachable lhs sub -> Reachable (GradeProduct lhs rhs) sub
| reachable_right : forall lhs rhs sub,
    Reachable rhs sub -> Reachable (GradeProduct lhs rhs) sub.

Fixpoint follow_child_path (root : Grade) (path : list bool) {struct path} : option Grade :=
  match path with
  | [] => Some root
  | false :: tail =>
      match root with
      | GradeProduct lhs _ => follow_child_path lhs tail
      | _ => None
      end
  | true :: tail =>
      match root with
      | GradeProduct _ rhs => follow_child_path rhs tail
      | _ => None
      end
  end.

Theorem borrowed_child_path_is_reachable : forall path root sub,
    follow_child_path root path = Some sub -> Reachable root sub.
Proof.
  induction path as [|direction tail IH]; intros root sub H.
  - simpl in H. injection H as Hroot. subst. apply reachable_here.
  - destruct direction; destruct root as [|id|lhs rhs]; simpl in H;
      try discriminate.
    + apply reachable_right. eapply IH; eauto.
    + apply reachable_left. eapply IH; eauto.
Qed.

Print Assumptions signature_product_adds.
Print Assumptions signature_product_commutative_by_count.
Print Assumptions product_keeps_every_generator_occurrence.
Print Assumptions flat_signature_count_bounded_by_tree_work.
Print Assumptions flat_signature_backing_bounded_by_tree_work.
Print Assumptions unit_template_has_no_demand.
Print Assumptions product_template_uses_one_compound_lane.
Print Assumptions listed_generators_cover_all_compositions.
Print Assumptions borrowed_child_path_is_reachable.
