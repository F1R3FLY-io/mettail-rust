From Stdlib Require Import List PeanoNat.
Import ListNotations.

(** A completed language is an immutable object.  [payload] abstracts the
    complete [LanguageCoreV1] tree; it is deliberately not projected back to
    an open presentation before installation. *)
Record Core : Type := {
  core_name : nat;
  payload : list nat
}.

Definition core_eq_dec : forall left right : Core, {left = right} + {left <> right}.
Proof.
  intros [left_name left_payload] [right_name right_payload].
  destruct (Nat.eq_dec left_name right_name) as [Hname | Hname];
    destruct (list_eq_dec Nat.eq_dec left_payload right_payload) as [Hpayload | Hpayload].
  - subst. left. reflexivity.
  - right. intros Heq. inversion Heq. contradiction.
  - right. intros Heq. inversion Heq. contradiction.
  - right. intros Heq. inversion Heq. contradiction.
Defined.

(** Greg/Mike builders act on open presentations.  The exact-core form of
    [Data(v)] crosses from the presentation category into its completed-object
    image and is therefore admitted only at the empty presentation. *)
Inductive Presentation : Type :=
| Open (fields : list nat)
| Completed (core : Core).

Inductive DataFragment : Type :=
| Partial (fields : list nat)
| Exact (core : Core).

Definition apply_data
    (presentation : Presentation)
    (fragment : DataFragment) : option Presentation :=
  match presentation, fragment with
  | Open fields, Partial extension => Some (Open (fields ++ extension))
  | Open [], Exact core => Some (Completed core)
  | Open (_ :: _), Exact _ => None
  | Completed _, _ => None
  end.

Definition apply_builder
    (presentation : Presentation)
    (field : nat) : option Presentation :=
  match presentation with
  | Open fields => Some (Open (fields ++ [field]))
  | Completed _ => None
  end.

(** The initial open presentation is the identity of join.  Completed objects
    have only their equality-induced idempotent join; unlike open
    presentations, distinct completed objects have no implicit pushout. *)
Definition join
    (left right : Presentation) : option Presentation :=
  match left, right with
  | Completed core, Open []
  | Open [], Completed core => Some (Completed core)
  | Completed left_core, Completed right_core =>
      if core_eq_dec left_core right_core
      then Some (Completed left_core)
      else None
  | Open left_fields, Open right_fields =>
      Some (Open (left_fields ++ right_fields))
  | _, _ => None
  end.

(** Finishing reattaches the declaration name.  An exact core already commits
    to its name, so a wrapper may neither rename it nor weaken the check. *)
Definition finish
    (declared_name : nat)
    (presentation : Presentation) : option Core :=
  match presentation with
  | Open fields => Some {| core_name := declared_name; payload := fields |}
  | Completed core =>
      if Nat.eq_dec declared_name (core_name core)
      then Some core
      else None
  end.

Theorem exact_data_embedding_left_inverse :
  forall core,
    finish (core_name core)
      (match apply_data (Open []) (Exact core) with
       | Some presentation => presentation
       | None => Open []
       end) = Some core.
Proof.
  intros core. simpl.
  destruct (Nat.eq_dec (core_name core) (core_name core)); congruence.
Qed.

Theorem exact_data_rejects_nonempty_presentation :
  forall field rest core,
    apply_data (Open (field :: rest)) (Exact core) = None.
Proof. reflexivity. Qed.

Theorem completed_data_rejects_every_further_data :
  forall core fragment,
    apply_data (Completed core) fragment = None.
Proof. reflexivity. Qed.

Theorem completed_value_rejects_every_further_builder :
  forall core field,
    apply_builder (Completed core) field = None.
Proof. reflexivity. Qed.

Theorem completed_join_is_idempotent :
  forall core,
    join (Completed core) (Completed core) = Some (Completed core).
Proof.
  intros core. simpl.
  destruct (core_eq_dec core core); congruence.
Qed.

Theorem empty_is_left_identity_for_completed_join :
  forall core,
    join (Open []) (Completed core) = Some (Completed core).
Proof. reflexivity. Qed.

Theorem empty_is_right_identity_for_completed_join :
  forall core,
    join (Completed core) (Open []) = Some (Completed core).
Proof. reflexivity. Qed.

Theorem distinct_completed_join_fails_closed :
  forall left right,
    left <> right ->
    join (Completed left) (Completed right) = None.
Proof.
  intros left right Hneq. simpl.
  destruct (core_eq_dec left right); congruence.
Qed.

Theorem completed_name_commitment :
  forall declared_name core,
    declared_name <> core_name core ->
    finish declared_name (Completed core) = None.
Proof.
  intros declared_name core Hneq. simpl.
  destruct (Nat.eq_dec declared_name (core_name core)); congruence.
Qed.

Print Assumptions exact_data_embedding_left_inverse.
Print Assumptions exact_data_rejects_nonempty_presentation.
Print Assumptions completed_data_rejects_every_further_data.
Print Assumptions completed_value_rejects_every_further_builder.
Print Assumptions completed_join_is_idempotent.
Print Assumptions empty_is_left_identity_for_completed_join.
Print Assumptions empty_is_right_identity_for_completed_join.
Print Assumptions distinct_completed_join_fails_closed.
Print Assumptions completed_name_commitment.
