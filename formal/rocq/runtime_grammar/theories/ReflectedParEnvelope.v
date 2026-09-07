(** * A reflected envelope cannot hide executable Par components

    These are all nine executable component families in the node's Par
    schema.  An expression envelope contains exactly one expression and no
    other component; a private-tag envelope contains exactly one unforgeable;
    a send envelope permits any number of sends and no other component.

    This model covers component cardinalities, not expression variants,
    private-name framing, locally-free annotations or protobuf byte equality.
    Those checks remain in the existing recognizers.  In particular,
    conditionals are executable content, not ignorable annotation data. *)

From Stdlib Require Import List Bool Arith.PeanoNat.
Import ListNotations.

Module ReflectedParEnvelope.

Inductive Component :=
| Sends | Receives | News | Expressions | Matches | Unforgeables
| Bundles | Connectives | Conditionals.

Definition component_eq_dec : forall first second : Component,
  {first = second} + {first <> second}.
Proof. decide equality. Defined.

Definition components :=
  [Sends; Receives; News; Expressions; Matches; Unforgeables;
   Bundles; Connectives; Conditionals].

Lemma every_executable_component_is_enumerated : forall component,
  In component components.
Proof. intros []; cbn; tauto. Qed.

Inductive Shape := ExpressionEnvelope | PrivateTagEnvelope | SendEnvelope.

Definition payload_component shape :=
  match shape with
  | ExpressionEnvelope => Expressions
  | PrivateTagEnvelope => Unforgeables
  | SendEnvelope => Sends
  end.

Definition empty_except (payload : Component) (counts : Component -> nat) :=
  forallb (fun component =>
    if component_eq_dec component payload then true else Nat.eqb (counts component) 0)
    components.

Definition admissible shape counts :=
  empty_except (payload_component shape) counts &&
    match shape with
    | ExpressionEnvelope | PrivateTagEnvelope => Nat.eqb (counts (payload_component shape)) 1
    | SendEnvelope => true
    end.

Theorem empty_except_is_exact : forall payload counts,
  empty_except payload counts = true <->
  forall component, component <> payload -> counts component = 0.
Proof.
  intros payload counts. unfold empty_except. rewrite forallb_forall. split.
  - intros H component Hdifferent.
    specialize (H component (every_executable_component_is_enumerated component)).
    destruct (component_eq_dec component payload); [contradiction|now apply Nat.eqb_eq].
  - intros H component Hmember.
    destruct (component_eq_dec component payload); [reflexivity|].
    apply Nat.eqb_eq. now apply H.
Qed.

Theorem accepted_envelope_has_no_other_executable_component : forall shape counts,
  admissible shape counts = true ->
  forall component, component <> payload_component shape -> counts component = 0.
Proof.
  intros shape counts H. unfold admissible in H. apply andb_true_iff in H.
  apply empty_except_is_exact. exact (proj1 H).
Qed.

Corollary accepted_envelope_has_no_conditionals : forall shape counts,
  admissible shape counts = true -> counts Conditionals = 0.
Proof.
  intros shape counts H.
  eapply accepted_envelope_has_no_other_executable_component; [exact H|].
  destruct shape; discriminate.
Qed.

Theorem expression_and_tag_envelopes_have_one_payload : forall shape counts,
  shape <> SendEnvelope -> admissible shape counts = true ->
  counts (payload_component shape) = 1.
Proof.
  intros shape counts Hshape H. unfold admissible in H.
  apply andb_true_iff in H. destruct H as [_ Harity].
  destruct shape; [now apply Nat.eqb_eq|now apply Nat.eqb_eq|contradiction].
Qed.

Definition expression_with_conditional component :=
  match component with Expressions | Conditionals => 1 | _ => 0 end.

Example conditional_sidecar_is_not_an_expression_envelope :
  admissible ExpressionEnvelope expression_with_conditional = false.
Proof. reflexivity. Qed.

Definition singleton_payload shape component :=
  if component_eq_dec component (payload_component shape) then 1 else 0.

Example unchanged_canonical_envelopes_still_pass : forall shape,
  admissible shape (singleton_payload shape) = true.
Proof. intros []; reflexivity. Qed.

End ReflectedParEnvelope.

Print Assumptions ReflectedParEnvelope.empty_except_is_exact.
Print Assumptions ReflectedParEnvelope.accepted_envelope_has_no_other_executable_component.
Print Assumptions ReflectedParEnvelope.accepted_envelope_has_no_conditionals.
Print Assumptions ReflectedParEnvelope.expression_and_tag_envelopes_have_one_payload.
