(** Authored term suffixes refine the existing canonical precedence metadata.
    The unadorned Greg/Mike judgment retains the old default: left-associative
    with no explicit binding power. The two optional fields are independent,
    and duplicate declarations reject instead of silently replacing evidence.
    The Rust adapter must also validate that powers fit the canonical u16
    domain; this model treats powers as already checked finite values. *)
From Stdlib Require Import List.
Import ListNotations.

Module TermAttributeProjection.

Inductive Association := Left | Right | NonAssociative.
Inductive Attribute := SetAssociation (value : Association)
                   | SetPower (value : nat).

Record Partial := {
  authored_association : option Association;
  authored_power : option nat
}.

Record Precedence := {
  association : Association;
  binding_power : option nat
}.

Definition empty : Partial :=
  {| authored_association := None; authored_power := None |}.

Definition insert (state : Partial) (attribute : Attribute) : option Partial :=
  match attribute with
  | SetAssociation value =>
      match authored_association state with
      | Some _ => None
      | None => Some {| authored_association := Some value;
                      authored_power := authored_power state |}
      end
  | SetPower value =>
      match authored_power state with
      | Some _ => None
      | None => Some {| authored_association := authored_association state;
                      authored_power := Some value |}
      end
  end.

Definition gather (attributes : list Attribute) : option Partial :=
  fold_left (fun state attribute =>
    match state with
    | None => None
    | Some current => insert current attribute
    end) attributes (Some empty).

Definition finish (state : Partial) : Precedence :=
  {| association := match authored_association state with
                    | Some value => value
                    | None => Left
                    end;
     binding_power := authored_power state |}.

Definition project (attributes : list Attribute) : option Precedence :=
  match gather attributes with
  | Some state => Some (finish state)
  | None => None
  end.

Theorem plain_judgment_retains_old_default :
  project [] = Some {| association := Left; binding_power := None |}.
Proof. reflexivity. Qed.

Theorem explicit_metadata_is_order_independent :
  forall assoc power,
    project [SetAssociation assoc; SetPower power] =
    project [SetPower power; SetAssociation assoc].
Proof. intros; reflexivity. Qed.

Theorem explicit_metadata_projects_to_existing_precedence :
  forall assoc power,
    project [SetAssociation assoc; SetPower power] =
    Some {| association := assoc; binding_power := Some power |}.
Proof. intros; reflexivity. Qed.

Theorem duplicate_association_rejects :
  forall first second,
    project [SetAssociation first; SetAssociation second] = None.
Proof. intros; reflexivity. Qed.

Theorem duplicate_power_rejects :
  forall first second,
    project [SetPower first; SetPower second] = None.
Proof. intros; reflexivity. Qed.

End TermAttributeProjection.
