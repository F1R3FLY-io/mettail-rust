(** Source-local ACU admission over the existing typed equation arenas.

    The input roles come from the separately validated source signature.
    This checker recognizes a sufficient set of unconditional equation
    schemas, not all presentations of a commutative monoid. The bounded shape
    projection below reads at most depth three; it does not normalize terms,
    execute rewrites, evaluate grades, or interpret legacy witness strings.
    Equation indices refer to the supplied source-order equation list.

    The final theorem uses a generated congruence whose axiom rule is actual
    source-equation instantiation. In particular, no ACU law or checker
    soundness assumption is used to construct that congruence. Its small
    signature fragment embeds in any full source congruence with the same
    instantiation closure; unrelated source equations can add equalities.
    This does not certify a section, a faithful interpretation, or Cost(G).
*)

From Stdlib Require Import List Bool PeanoNat Lia.
From RuntimeGrammar Require Import ExecutableTheoryCore.
Import ListNotations.

Module SourceSignatureMonoidAdmission.
Import ExecutableTheoryCore.

Record SignatureRoles := {
  signature_sort : SortId;
  signature_unit : ConstructorId;
  signature_product : ConstructorId
}.

Inductive SchemaTerm :=
| SchemaVariable (variable : VariableId)
| SchemaUnit
| SchemaProduct (left right : SchemaTerm).

Fixpoint schema_eqb (left right : SchemaTerm) : bool :=
  match left, right with
  | SchemaVariable x, SchemaVariable y => Nat.eqb x y
  | SchemaUnit, SchemaUnit => true
  | SchemaProduct a b, SchemaProduct c d => schema_eqb a c && schema_eqb b d
  | _, _ => false
  end.

Lemma schema_eqb_sound : forall left right,
  schema_eqb left right = true -> left = right.
Proof.
  induction left as [x| |a IHa b IHb]; destruct right; simpl; try discriminate.
  - intros H. apply Nat.eqb_eq in H. now subst.
  - reflexivity.
  - intros H. apply andb_true_iff in H as [Ha Hb].
    apply IHa in Ha. apply IHb in Hb. now subst.
Qed.

Definition input_variableb roles rule variable : bool :=
  match nth_error (rule_variables rule) variable with
  | Some {| variable_sort := sort; variable_role := InputVariable |} =>
      Nat.eqb sort (signature_sort roles)
  | _ => false
  end.

Fixpoint read_schema_term (depth : nat) roles rule root : option SchemaTerm :=
  match depth with
  | 0 => None
  | S rest =>
      match nth_error (rule_terms rule) root with
      | Some node =>
          if Nat.eqb (term_sort node) (signature_sort roles) then
            match term_form node with
            | VariableTerm variable =>
                if input_variableb roles rule variable
                then Some (SchemaVariable variable) else None
            | ConstructorTerm constructor [] =>
                if Nat.eqb constructor (signature_unit roles)
                then Some SchemaUnit else None
            | ConstructorTerm constructor [child_left; child_right] =>
                if Nat.eqb constructor (signature_product roles) then
                  match read_schema_term rest roles rule child_left,
                        read_schema_term rest roles rule child_right with
                  | Some a, Some b => Some (SchemaProduct a b)
                  | _, _ => None
                  end
                else None
            | _ => None
            end
          else None
      | None => None
      end
  end.

Inductive SourceShape roles rule : TermId -> SchemaTerm -> Prop :=
| shape_variable : forall root variable,
    nth_error (rule_terms rule) root =
      Some {| term_sort := signature_sort roles; term_form := VariableTerm variable |} ->
    nth_error (rule_variables rule) variable =
      Some {| variable_sort := signature_sort roles; variable_role := InputVariable |} ->
    SourceShape roles rule root (SchemaVariable variable)
| shape_unit : forall root,
    nth_error (rule_terms rule) root =
      Some {| term_sort := signature_sort roles;
              term_form := ConstructorTerm (signature_unit roles) [] |} ->
    SourceShape roles rule root SchemaUnit
| shape_product : forall root left right a b,
    nth_error (rule_terms rule) root =
      Some {| term_sort := signature_sort roles;
              term_form := ConstructorTerm (signature_product roles) [left; right] |} ->
    SourceShape roles rule left a -> SourceShape roles rule right b ->
    SourceShape roles rule root (SchemaProduct a b).

Lemma input_variableb_sound : forall roles rule variable,
  input_variableb roles rule variable = true ->
  nth_error (rule_variables rule) variable =
    Some {| variable_sort := signature_sort roles; variable_role := InputVariable |}.
Proof.
  intros roles rule variable H. unfold input_variableb in H.
  destruct (nth_error (rule_variables rule) variable) as [[sort role]|] eqn:E;
    [destruct role|]; try discriminate.
  apply Nat.eqb_eq in H. now subst.
Qed.

Theorem read_schema_term_retains_actual_source_shape :
  forall depth roles rule root term,
    read_schema_term depth roles rule root = Some term ->
    SourceShape roles rule root term.
Proof.
  induction depth as [|depth IH]; intros roles rule root term H; [discriminate|].
  simpl in H.
  destruct (nth_error (rule_terms rule) root) as [[sort form]|] eqn:E;
    [|discriminate]. simpl in H.
  destruct (Nat.eqb sort (signature_sort roles)) eqn:S; [|discriminate].
  apply Nat.eqb_eq in S. subst sort.
  destruct form; try discriminate.
  - destruct (input_variableb roles rule variable) eqn:V; [|discriminate].
    inversion H; subst. eapply shape_variable; [exact E|].
    now apply input_variableb_sound.
  - destruct arguments as [|left tail].
    + destruct (Nat.eqb constructor (signature_unit roles)) eqn:U; [|discriminate].
      apply Nat.eqb_eq in U. subst constructor. inversion H; subst.
      now apply shape_unit.
    + destruct tail as [|right tail]; [discriminate|].
      destruct tail; [|discriminate].
      destruct (Nat.eqb constructor (signature_product roles)) eqn:P; [|discriminate].
      apply Nat.eqb_eq in P. subst constructor.
      destruct (read_schema_term depth roles rule left) as [a|] eqn:A; [|discriminate].
      destruct (read_schema_term depth roles rule right) as [b|] eqn:B; [|discriminate].
      inversion H; subst. eapply shape_product; [exact E| |]; eauto.
Qed.

Inductive Law :=
| Associativity (x y z : VariableId)
| Commutativity (x y : VariableId)
| LeftUnit (x : VariableId)
| RightUnit (x : VariableId).

Inductive Obligation := Associate | Commute | Unital.
Inductive Orientation := Forward | Reverse.

Definition law_left law :=
  match law with
  | Associativity x y z => SchemaProduct
      (SchemaProduct (SchemaVariable x) (SchemaVariable y)) (SchemaVariable z)
  | Commutativity x y => SchemaProduct (SchemaVariable x) (SchemaVariable y)
  | LeftUnit x => SchemaProduct SchemaUnit (SchemaVariable x)
  | RightUnit x => SchemaProduct (SchemaVariable x) SchemaUnit
  end.

Definition law_right law :=
  match law with
  | Associativity x y z => SchemaProduct (SchemaVariable x)
      (SchemaProduct (SchemaVariable y) (SchemaVariable z))
  | Commutativity x y => SchemaProduct (SchemaVariable y) (SchemaVariable x)
  | LeftUnit x | RightUnit x => SchemaVariable x
  end.

Definition law_distinct law : Prop :=
  match law with
  | Associativity x y z => x <> y /\ x <> z /\ y <> z
  | Commutativity x y => x <> y
  | LeftUnit _ | RightUnit _ => True
  end.

Definition law_distinctb law : bool :=
  match law with
  | Associativity x y z => negb (Nat.eqb x y) && negb (Nat.eqb x z) && negb (Nat.eqb y z)
  | Commutativity x y => negb (Nat.eqb x y)
  | LeftUnit _ | RightUnit _ => true
  end.

Lemma law_distinctb_sound : forall law,
  law_distinctb law = true -> law_distinct law.
Proof.
  destruct law; simpl; intros H; try exact I;
    repeat match goal with
    | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
    | H : negb _ = true |- _ => apply negb_true_iff in H; apply Nat.eqb_neq in H
    end; auto.
Qed.

Definition law_kind_matches kind law :=
  match kind, law with
  | Associate, Associativity _ _ _ | Commute, Commutativity _ _
  | Unital, LeftUnit _ | Unital, RightUnit _ => true
  | _, _ => false
  end.

Definition candidate_law left : option Law :=
  match left with
  | SchemaProduct (SchemaProduct (SchemaVariable x) (SchemaVariable y))
      (SchemaVariable z) => Some (Associativity x y z)
  | SchemaProduct (SchemaVariable x) (SchemaVariable y) => Some (Commutativity x y)
  | SchemaProduct SchemaUnit (SchemaVariable x) => Some (LeftUnit x)
  | SchemaProduct (SchemaVariable x) SchemaUnit => Some (RightUnit x)
  | _ => None
  end.

Definition recognize_terms kind left right : option Law :=
  match candidate_law left with
  | Some law =>
      if law_kind_matches kind law && law_distinctb law &&
         schema_eqb left (law_left law) && schema_eqb right (law_right law)
      then Some law else None
  | None => None
  end.

Lemma recognize_terms_sound : forall kind left right law,
  recognize_terms kind left right = Some law ->
  law_kind_matches kind law = true /\ law_distinct law /\
  left = law_left law /\ right = law_right law.
Proof.
  intros kind left right law H. unfold recognize_terms in H.
  destruct (candidate_law left) as [found|]; [|discriminate].
  destruct (law_kind_matches kind found && law_distinctb found &&
    schema_eqb left (law_left found) && schema_eqb right (law_right found)) eqn:B;
    [|discriminate]. inversion H; subst found.
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  end.
  repeat split; auto using law_distinctb_sound, schema_eqb_sound.
Qed.

Definition oriented_roots rule orientation :=
  match orientation with
  | Forward => (rule_lhs rule, rule_rhs rule)
  | Reverse => (rule_rhs rule, rule_lhs rule)
  end.

Definition check_direction roles kind rule orientation : option Law :=
  let '(lhs, rhs) := oriented_roots rule orientation in
  match read_schema_term 3 roles rule lhs, read_schema_term 3 roles rule rhs with
  | Some a, Some b => recognize_terms kind a b
  | _, _ => None
  end.

Definition check_equation roles kind rule : option (Orientation * Law) :=
  match rule_premises rule, rule_premise_roots rule with
  | [], [] =>
      match check_direction roles kind rule Forward with
      | Some law => Some (Forward, law)
      | None =>
          match check_direction roles kind rule Reverse with
          | Some law => Some (Reverse, law)
          | None => None
          end
      end
  | _, _ => None
  end.

Definition EquationWitness roles kind rule orientation law : Prop :=
  rule_premises rule = [] /\ rule_premise_roots rule = [] /\
  law_kind_matches kind law = true /\ law_distinct law /\
  SourceShape roles rule (fst (oriented_roots rule orientation)) (law_left law) /\
  SourceShape roles rule (snd (oriented_roots rule orientation)) (law_right law).

Lemma check_direction_sound : forall roles kind rule orientation law,
  check_direction roles kind rule orientation = Some law ->
  law_kind_matches kind law = true /\ law_distinct law /\
  SourceShape roles rule (fst (oriented_roots rule orientation)) (law_left law) /\
  SourceShape roles rule (snd (oriented_roots rule orientation)) (law_right law).
Proof.
  intros roles kind rule orientation law H. unfold check_direction in H.
  destruct (oriented_roots rule orientation) as [left right] eqn:O; simpl.
  destruct (read_schema_term 3 roles rule left) as [a|] eqn:A; [|discriminate].
  destruct (read_schema_term 3 roles rule right) as [b|] eqn:B; [|discriminate].
  destruct (recognize_terms_sound _ _ _ _ H) as [K [D [Ha Hb]]].
  subst a b. split; [exact K|]. split; [exact D|]. split.
  - exact (read_schema_term_retains_actual_source_shape 3 roles rule left (law_left law) A).
  - exact (read_schema_term_retains_actual_source_shape 3 roles rule right (law_right law) B).
Qed.

Theorem checked_equation_has_exact_source_schema : forall roles kind rule orientation law,
  check_equation roles kind rule = Some (orientation, law) ->
  EquationWitness roles kind rule orientation law.
Proof.
  intros roles kind rule orientation law H. unfold check_equation in H.
  destruct (rule_premises rule) eqn:P; [|discriminate].
  destruct (rule_premise_roots rule) eqn:R; [|discriminate].
  destruct (check_direction roles kind rule Forward) as [found|] eqn:F.
  - inversion H; subst. unfold EquationWitness. repeat split; auto.
    all: destruct (check_direction_sound _ _ _ _ _ F) as [? [? [? ?]]]; assumption.
  - destruct (check_direction roles kind rule Reverse) as [found|] eqn:B;
      [|discriminate]. inversion H; subst. unfold EquationWitness. repeat split; auto.
    all: destruct (check_direction_sound _ _ _ _ _ B) as [? [? [? ?]]]; assumption.
Qed.

Record SourceWitness := {
  equation_index : nat;
  equation_orientation : Orientation;
  equation_law : Law
}.

Fixpoint find_source_law roles kind (equations : list RuleArena) : option SourceWitness :=
  match equations with
  | [] => None
  | rule :: rest =>
      match check_equation roles kind rule with
      | Some (orientation, law) =>
          Some {| equation_index := 0; equation_orientation := orientation; equation_law := law |}
      | None =>
          match find_source_law roles kind rest with
          | Some witness => Some {| equation_index := S (equation_index witness);
              equation_orientation := equation_orientation witness;
              equation_law := equation_law witness |}
          | None => None
          end
      end
  end.

Definition WitnessInSource roles kind equations witness : Prop :=
  exists rule,
    nth_error equations (equation_index witness) = Some rule /\
    EquationWitness roles kind rule (equation_orientation witness) (equation_law witness).

Theorem found_law_retains_source_equation_and_orientation : forall roles kind equations witness,
  find_source_law roles kind equations = Some witness ->
  WitnessInSource roles kind equations witness.
Proof.
  intros roles kind equations. induction equations as [|rule rest IH];
    intros witness H; simpl in H; [discriminate|].
  destruct (check_equation roles kind rule) as [[orientation law]|] eqn:C.
  - inversion H; subst. exists rule. split; [reflexivity|].
    now apply checked_equation_has_exact_source_schema.
  - destruct (find_source_law roles kind rest) as [found|] eqn:F; [|discriminate].
    inversion H; subst. specialize (IH found eq_refl).
    destruct IH as [source [N W]]. exists source. simpl. auto.
Qed.

Record AcuEvidence := {
  associativity_witness : SourceWitness;
  commutativity_witness : SourceWitness;
  unit_witness : SourceWitness
}.

Definition check_source_signature_acu roles equations : option AcuEvidence :=
  match find_source_law roles Associate equations,
        find_source_law roles Commute equations,
        find_source_law roles Unital equations with
  | Some a, Some c, Some u => Some {| associativity_witness := a;
      commutativity_witness := c; unit_witness := u |}
  | _, _, _ => None
  end.

Theorem admitted_acu_retains_three_exact_source_witnesses : forall roles equations evidence,
  check_source_signature_acu roles equations = Some evidence ->
  WitnessInSource roles Associate equations (associativity_witness evidence) /\
  WitnessInSource roles Commute equations (commutativity_witness evidence) /\
  WitnessInSource roles Unital equations (unit_witness evidence).
Proof.
  intros roles equations evidence H. unfold check_source_signature_acu in H.
  destruct (find_source_law roles Associate equations) as [a|] eqn:A; [|discriminate].
  destruct (find_source_law roles Commute equations) as [c|] eqn:C; [|discriminate].
  destruct (find_source_law roles Unital equations) as [u|] eqn:U; [|discriminate].
  inversion H; subst. repeat split; now apply found_law_retains_source_equation_and_orientation.
Qed.

(** Declarative source instantiation, not a runtime term or grade evaluator.
    [A] may be the interacting source's signature terms, including arbitrary
    opaque generators. The valuation substitutes those values for input slots. *)
Section SourceCongruence.
Context {A : Type} (unit : A) (product : A -> A -> A).

Inductive SchemaInstance (valuation : VariableId -> A) : SchemaTerm -> A -> Prop :=
| instance_variable : forall x, SchemaInstance valuation (SchemaVariable x) (valuation x)
| instance_unit : SchemaInstance valuation SchemaUnit unit
| instance_product : forall a b av bv,
    SchemaInstance valuation a av -> SchemaInstance valuation b bv ->
    SchemaInstance valuation (SchemaProduct a b) (product av bv).

Definition SourceInstance roles rule valuation root value : Prop :=
  exists shape, SourceShape roles rule root shape /\ SchemaInstance valuation shape value.

Inductive GeneratedCongruence roles (equations : list RuleArena) : A -> A -> Prop :=
| source_equation_instance : forall index rule valuation left right,
    nth_error equations index = Some rule ->
    rule_premises rule = [] -> rule_premise_roots rule = [] ->
    SourceInstance roles rule valuation (rule_lhs rule) left ->
    SourceInstance roles rule valuation (rule_rhs rule) right ->
    GeneratedCongruence roles equations left right
| congruence_refl : forall x, GeneratedCongruence roles equations x x
| congruence_sym : forall x y,
    GeneratedCongruence roles equations x y -> GeneratedCongruence roles equations y x
| congruence_trans : forall x y z,
    GeneratedCongruence roles equations x y -> GeneratedCongruence roles equations y z ->
    GeneratedCongruence roles equations x z
| congruence_product : forall x x' y y',
    GeneratedCongruence roles equations x x' -> GeneratedCongruence roles equations y y' ->
    GeneratedCongruence roles equations (product x y) (product x' y').

Definition law_left_value law (valuation : VariableId -> A) :=
  match law with
  | Associativity x y z => product (product (valuation x) (valuation y)) (valuation z)
  | Commutativity x y => product (valuation x) (valuation y)
  | LeftUnit x => product unit (valuation x)
  | RightUnit x => product (valuation x) unit
  end.

Definition law_right_value law (valuation : VariableId -> A) :=
  match law with
  | Associativity x y z => product (valuation x) (product (valuation y) (valuation z))
  | Commutativity x y => product (valuation y) (valuation x)
  | LeftUnit x | RightUnit x => valuation x
  end.

Lemma law_sides_are_universal_instances : forall law valuation,
  SchemaInstance valuation (law_left law) (law_left_value law valuation) /\
  SchemaInstance valuation (law_right law) (law_right_value law valuation).
Proof. destruct law; intros; split; simpl; repeat constructor. Qed.

Theorem source_witness_establishes_every_substitution :
  forall roles kind equations witness valuation,
    WitnessInSource roles kind equations witness ->
    GeneratedCongruence roles equations
      (law_left_value (equation_law witness) valuation)
      (law_right_value (equation_law witness) valuation).
Proof.
  intros roles kind equations witness valuation [rule [N [P [R [K [D [L H]]]]]]].
  destruct (law_sides_are_universal_instances (equation_law witness) valuation) as [IL IR].
  destruct (equation_orientation witness); simpl in L, H.
  - eapply source_equation_instance; [exact N|exact P|exact R| |];
      eexists; split; eassumption.
  - apply congruence_sym. eapply source_equation_instance;
      [exact N|exact P|exact R| |]; eexists; split; eassumption.
Qed.

Definition UniversalLaw roles equations law : Prop :=
  match law with
  | Associativity _ _ _ => forall x y z,
      GeneratedCongruence roles equations (product (product x y) z) (product x (product y z))
  | Commutativity _ _ => forall x y,
      GeneratedCongruence roles equations (product x y) (product y x)
  | LeftUnit _ => forall x, GeneratedCongruence roles equations (product unit x) x
  | RightUnit _ => forall x, GeneratedCongruence roles equations (product x unit) x
  end.

Theorem distinct_source_variables_give_universal_law : forall roles kind equations witness,
  WitnessInSource roles kind equations witness ->
  UniversalLaw roles equations (equation_law witness).
Proof.
  intros roles kind equations witness W.
  assert (D : law_distinct (equation_law witness)).
  { destruct W as [rule [_ [_ [_ [_ [D _]]]]]]. exact D. }
  pose proof (source_witness_establishes_every_substitution roles kind equations witness) as H.
  destruct (equation_law witness) as [i j k|i j|i|i] eqn:L; simpl in D |- *.
  - destruct D as [Dij [Dik Djk]]. intros x y z.
    specialize (H (fun n => if Nat.eqb n i then x else if Nat.eqb n j then y else z) W).
    simpl in H.
    assert (Ji : Nat.eqb j i = false) by (apply Nat.eqb_neq; lia).
    assert (Ki : Nat.eqb k i = false) by (apply Nat.eqb_neq; lia).
    assert (Kj : Nat.eqb k j = false) by (apply Nat.eqb_neq; lia).
    now rewrite Nat.eqb_refl, Ji, Ki, Kj, Nat.eqb_refl in H.
  - intros x y. specialize (H (fun n => if Nat.eqb n i then x else y) W).
    simpl in H.
    assert (Ji : Nat.eqb j i = false) by (apply Nat.eqb_neq; lia).
    now rewrite Nat.eqb_refl, Ji in H.
  - intros x. exact (H (fun _ => x) W).
  - intros x. exact (H (fun _ => x) W).
Qed.

Theorem admitted_source_equations_generate_acu : forall roles equations evidence,
  check_source_signature_acu roles equations = Some evidence ->
  (forall x y z, GeneratedCongruence roles equations
    (product (product x y) z) (product x (product y z))) /\
  (forall x y, GeneratedCongruence roles equations (product x y) (product y x)) /\
  (forall x, GeneratedCongruence roles equations (product unit x) x) /\
  (forall x, GeneratedCongruence roles equations (product x unit) x).
Proof.
  intros roles equations evidence H.
  destruct (admitted_acu_retains_three_exact_source_witnesses _ _ _ H) as [WA [WC WU]].
  pose proof (distinct_source_variables_give_universal_law _ _ _ _ WA) as LA.
  pose proof (distinct_source_variables_give_universal_law _ _ _ _ WC) as LC.
  pose proof (distinct_source_variables_give_universal_law _ _ _ _ WU) as LU.
  destruct WA as [ra [_ [_ [_ [KA _]]]]].
  destruct WC as [rc [_ [_ [_ [KC _]]]]].
  destruct WU as [ru [_ [_ [_ [KU _]]]]].
  destruct (equation_law (associativity_witness evidence)); try discriminate KA.
  destruct (equation_law (commutativity_witness evidence)); try discriminate KC.
  simpl in LA, LC. split; [exact LA|]. split; [exact LC|].
  destruct (equation_law (unit_witness evidence)); try discriminate KU; simpl in LU.
  - split; [exact LU|]. intros value. eapply congruence_trans; [apply LC|apply LU].
  - split; [|exact LU]. intros value. eapply congruence_trans; [apply LC|apply LU].
Qed.

(** Any full source congruence reuses this result by accepting source-equation
    instances and the usual congruence closure. No ACU laws occur as premises. *)
Theorem generated_congruence_is_least : forall roles equations (relation : A -> A -> Prop),
  (forall index rule valuation left right,
    nth_error equations index = Some rule ->
    rule_premises rule = [] -> rule_premise_roots rule = [] ->
    SourceInstance roles rule valuation (rule_lhs rule) left ->
    SourceInstance roles rule valuation (rule_rhs rule) right -> relation left right) ->
  (forall x, relation x x) ->
  (forall x y, relation x y -> relation y x) ->
  (forall x y z, relation x y -> relation y z -> relation x z) ->
  (forall x x' y y', relation x x' -> relation y y' -> relation (product x y) (product x' y')) ->
  forall x y, GeneratedCongruence roles equations x y -> relation x y.
Proof.
  intros roles equations relation HE HR HS HT HP x y H.
  induction H; eauto.
Qed.
End SourceCongruence.

Definition example_roles := {| signature_sort := 0; signature_unit := 7; signature_product := 9 |}.
Definition example_variable x := {| term_sort := 0; term_form := VariableTerm x |}.
Definition example_product x y := {| term_sort := 0; term_form := ConstructorTerm 9 [x; y] |}.
Definition example_unit := {| term_sort := 0; term_form := ConstructorTerm 7 [] |}.
Definition example_rule terms left right :=
  {| rule_variables := repeat {| variable_sort := 0; variable_role := InputVariable |} 3;
     rule_terms := terms; rule_premises := []; rule_premise_roots := [];
     rule_allows_transition := false; rule_lhs := left; rule_rhs := right;
     rule_lhs_variables := []; rule_rhs_variables := [] |}.
Definition example_assoc := example_rule
  [example_variable 0; example_variable 1; example_variable 2;
   example_product 0 1; example_product 3 2; example_product 1 2; example_product 0 5] 4 6.
Definition example_comm_duplicated_nodes := example_rule
  [example_variable 0; example_variable 1; example_variable 0; example_variable 1;
   example_product 0 1; example_product 3 2] 4 5.
Definition example_reverse_right_unit := example_rule
  [example_variable 2; example_unit; example_product 0 1] 0 2.

Example renamed_roles_and_duplicated_nodes_are_accepted :
  check_source_signature_acu example_roles
    [example_reverse_right_unit; example_comm_duplicated_nodes; example_assoc] =
  Some {| associativity_witness := {| equation_index := 2; equation_orientation := Forward;
                                     equation_law := Associativity 0 1 2 |};
          commutativity_witness := {| equation_index := 1; equation_orientation := Forward;
                                    equation_law := Commutativity 0 1 |};
          unit_witness := {| equation_index := 0; equation_orientation := Reverse;
                            equation_law := RightUnit 2 |} |}.
Proof. reflexivity. Qed.

Example missing_commutativity_is_not_certified :
  check_source_signature_acu example_roles [example_assoc; example_reverse_right_unit] = None.
Proof. reflexivity. Qed.

Example repeated_variables_cannot_supply_universal_commutativity :
  check_equation example_roles Commute
    (example_rule [example_variable 0; example_product 0 0] 1 1) = None.
Proof. reflexivity. Qed.

Example wrong_constructor_is_not_a_signature_law :
  check_source_signature_acu
    {| signature_sort := 0; signature_unit := 7; signature_product := 8 |}
    [example_assoc; example_comm_duplicated_nodes; example_reverse_right_unit] = None.
Proof. reflexivity. Qed.

Theorem premise_bearing_equations_are_refused : forall roles kind rule,
  rule_premises rule <> [] \/ rule_premise_roots rule <> [] ->
  check_equation roles kind rule = None.
Proof.
  intros roles kind rule H. unfold check_equation.
  destruct (rule_premises rule); destruct (rule_premise_roots rule); auto.
  destruct H; contradiction.
Qed.

Print Assumptions read_schema_term_retains_actual_source_shape.
Print Assumptions checked_equation_has_exact_source_schema.
Print Assumptions found_law_retains_source_equation_and_orientation.
Print Assumptions admitted_acu_retains_three_exact_source_witnesses.
Print Assumptions source_witness_establishes_every_substitution.
Print Assumptions distinct_source_variables_give_universal_law.
Print Assumptions admitted_source_equations_generate_acu.
Print Assumptions generated_congruence_is_least.
Print Assumptions renamed_roles_and_duplicated_nodes_are_accepted.
Print Assumptions missing_commutativity_is_not_certified.
Print Assumptions repeated_variables_cannot_supply_universal_commutativity.
Print Assumptions wrong_constructor_is_not_a_signature_law.
Print Assumptions premise_bearing_equations_are_refused.

End SourceSignatureMonoidAdmission.
