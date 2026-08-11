(*
 * CrossLanguageSeparation: FLT Phase 3 Track A.
 *
 * This file models the finite ownership boundary implemented by
 * `rho_net_coinstall.rs`, the generated drive/subst/shift/float receivers, and
 * the multiple-ledger RSpace observation API.  It proves five properties used
 * by the two-language conformance test:
 *
 *   1. distinct fingerprints select exactly one language owner;
 *   2. an explicit root request never silently changes drivers, while nested
 *      descent and contractum re-entry route to the actual owner;
 *   3. subst/shift/float are identity functions at a declared foreign root;
 *   4. co-installed steps are exactly owner-indexed local steps and their
 *      observation ledgers form a disjoint partition; and
 *   5. AC peeling removes one POSITION, rather than every structurally equal
 *      value, so a nonempty soup strictly decreases even with duplicates.
 *
 * The last property is the termination obligation behind the generated
 * `^float`/`^drive` soup worklists.  It also rules out the implementation bug
 * in which rebuilding a remainder with value-membership duplicated every
 * equal target occurrence.
 *
 * Rocq 9.1 compatible. No admissions or global logical extensions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Sorting.Permutation.
Import ListNotations.

(* ========================================================================== *)
(* 1.  The finite co-install manifest and fingerprint separation.             *)
(* ========================================================================== *)

Inductive Language : Type :=
  | Lambda
  | Ambient.

Definition language_eq_dec : forall (left right : Language), {left = right} + {left <> right}.
Proof. decide equality. Defined.

Definition fingerprint (language : Language) : nat :=
  match language with
  | Lambda => 0
  | Ambient => 1
  end.

Theorem fingerprint_injective : forall left right,
  fingerprint left = fingerprint right -> left = right.
Proof.
  intros left right H.
  destruct left, right; cbn in H; try reflexivity; discriminate.
Qed.

Corollary distinct_languages_have_distinct_fingerprints : forall left right,
  left <> right -> fingerprint left <> fingerprint right.
Proof.
  intros left right Hneq Heq.
  apply Hneq. now apply fingerprint_injective.
Qed.

(* A reflected value records ownership only at its root.  Children may belong
   to either language; the boundary machine decides whether to descend.  TNil
   is the fingerprint-free empty AC value shared by the installed union. *)
Inductive Term : Type :=
  | TNode (owner : Language) (constructor : nat) (children : list Term)
  | TBag (owner : Language) (operator : nat) (elements : list Term)
  | TBinder (owner : Language) (body : Term)
  | TNil.

Definition root_owner (term : Term) : option Language :=
  match term with
  | TNode owner _ _ => Some owner
  | TBag owner _ _ => Some owner
  | TBinder owner _ => Some owner
  | TNil => None
  end.

Theorem root_owner_is_functional : forall term left right,
  root_owner term = Some left -> root_owner term = Some right -> left = right.
Proof.
  intros term left right Hleft Hright.
  rewrite Hleft in Hright. now injection Hright.
Qed.

Theorem a_root_cannot_be_owned_by_both_languages : forall term,
  root_owner term = Some Lambda -> root_owner term <> Some Ambient.
Proof.
  intros term Hlambda Hambient.
  pose proof (root_owner_is_functional term Lambda Ambient Hlambda Hambient).
  discriminate.
Qed.

(* ========================================================================== *)
(* 2.  Explicit-root veto and owner-directed nested/re-entry routing.           *)
(* ========================================================================== *)

Inductive Route : Type :=
  | Routed (language : Language)
  | WrongRoot
  | NeutralNil.

(* The public/root call is intentionally strict.  Supplying Lambda's driver for
   an Ambient root is a typed refusal; it does not auto-correct the request. *)
Definition root_route (requested : Language) (term : Term) : Route :=
  match root_owner term with
  | None => NeutralNil
  | Some actual =>
      if language_eq_dec actual requested then Routed requested else WrongRoot
  end.

(* Structural descent and a rewrite contractum are different: their root may
   legitimately change ownership, so the manifest dispatches by fingerprint. *)
Definition nested_route (term : Term) : Route :=
  match root_owner term with
  | None => NeutralNil
  | Some actual => Routed actual
  end.

Theorem requested_owner_is_routed : forall language term,
  root_owner term = Some language -> root_route language term = Routed language.
Proof.
  intros language term Howner.
  unfold root_route. rewrite Howner.
  destruct (language_eq_dec language language) as [_ | Hneq]; [reflexivity | contradiction].
Qed.

Theorem wrong_root_is_rejected : forall actual requested term,
  root_owner term = Some actual -> actual <> requested ->
  root_route requested term = WrongRoot.
Proof.
  intros actual requested term Howner Hneq.
  unfold root_route. rewrite Howner.
  destruct (language_eq_dec actual requested) as [Heq | _]; [contradiction | reflexivity].
Qed.

Theorem a_successful_root_route_has_the_requested_owner : forall requested term routed,
  root_route requested term = Routed routed ->
  routed = requested /\ root_owner term = Some requested.
Proof.
  intros requested term routed Hroute.
  unfold root_route in Hroute.
  destruct (root_owner term) as [actual |] eqn:Howner; [| discriminate].
  destruct (language_eq_dec actual requested) as [Heq | Hneq]; [| discriminate].
  injection Hroute as Hrouted. subst actual routed.
  split; reflexivity.
Qed.

Theorem nested_descent_routes_to_the_unique_owner : forall term language,
  root_owner term = Some language -> nested_route term = Routed language.
Proof.
  intros term language Howner.
  unfold nested_route. now rewrite Howner.
Qed.

Corollary contractum_reentry_routes_to_the_unique_owner : forall contractum language,
  root_owner contractum = Some language -> nested_route contractum = Routed language.
Proof. exact nested_descent_routes_to_the_unique_owner. Qed.

Theorem nil_has_no_fabricated_owner :
  root_owner TNil = None /\
  nested_route TNil = NeutralNil /\
  forall requested, root_route requested TNil = NeutralNil.
Proof. repeat split; reflexivity. Qed.

(* ========================================================================== *)
(* 3.  Foreign-root opacity for subst, shift, and float.                       *)
(* ========================================================================== *)

(* `local` abstracts one host machine's recursive body.  It is invoked only at
   a host-owned root; a declared foreign root and Nil return byte-for-byte. *)
Definition boundary_transform
    (host : Language) (local : Term -> Term) (term : Term) : Term :=
  match root_owner term with
  | None => term
  | Some actual =>
      if language_eq_dec actual host then local term else term
  end.

Theorem owned_boundary_invokes_the_local_machine : forall host local term,
  root_owner term = Some host -> boundary_transform host local term = local term.
Proof.
  intros host local term Howner.
  unfold boundary_transform. rewrite Howner.
  destruct (language_eq_dec host host) as [_ | Hneq]; [reflexivity | contradiction].
Qed.

Theorem foreign_boundary_is_opaque : forall host foreign local term,
  root_owner term = Some foreign -> foreign <> host ->
  boundary_transform host local term = term.
Proof.
  intros host foreign local term Howner Hneq.
  unfold boundary_transform. rewrite Howner.
  destruct (language_eq_dec foreign host) as [Heq | _]; [contradiction | reflexivity].
Qed.

Theorem nil_boundary_is_identity : forall host local,
  boundary_transform host local TNil = TNil.
Proof. reflexivity. Qed.

(* The three generated families share this same boundary theorem. *)
Corollary foreign_substitution_is_opaque : forall host foreign subst term,
  root_owner term = Some foreign -> foreign <> host ->
  boundary_transform host subst term = term.
Proof. exact foreign_boundary_is_opaque. Qed.

Corollary foreign_shift_is_opaque : forall host foreign shift term,
  root_owner term = Some foreign -> foreign <> host ->
  boundary_transform host shift term = term.
Proof. exact foreign_boundary_is_opaque. Qed.

Corollary foreign_float_is_opaque : forall host foreign float term,
  root_owner term = Some foreign -> foreign <> host ->
  boundary_transform host float term = term.
Proof. exact foreign_boundary_is_opaque. Qed.

(* ========================================================================== *)
(* 4.  Co-installed operational correspondence and ledger separation.         *)
(* ========================================================================== *)

Section OperationalCorrespondence.
  Variable local_step : Language -> Term -> Term -> Prop.

  Inductive CoInstallStep : Term -> Language -> Term -> Prop :=
    | coinstall_step : forall source language target,
        root_owner source = Some language ->
        local_step language source target ->
        CoInstallStep source language target.

  Theorem coinstall_step_iff_owner_local_step : forall source language target,
    CoInstallStep source language target <->
    root_owner source = Some language /\ local_step language source target.
  Proof.
    intros source language target. split.
    - intros H. inversion H; subst. now split.
    - intros [Howner Hstep]. now constructor.
  Qed.

  Theorem every_owned_local_step_is_coinstall_complete : forall source language target,
    root_owner source = Some language -> local_step language source target ->
    CoInstallStep source language target.
  Proof. intros. now constructor. Qed.

  Theorem every_coinstall_step_is_owner_sound : forall source language target,
    CoInstallStep source language target ->
    root_owner source = Some language /\ local_step language source target.
  Proof. intros. now apply coinstall_step_iff_owner_local_step. Qed.

  Theorem a_foreign_rule_cannot_fire_for_the_root : forall source actual claimed target,
    root_owner source = Some actual -> actual <> claimed ->
    ~ CoInstallStep source claimed target.
  Proof.
    intros source actual claimed target Howner Hneq Hstep.
    apply coinstall_step_iff_owner_local_step in Hstep as [Hclaimed _].
    apply Hneq. eapply root_owner_is_functional; eauto.
  Qed.
End OperationalCorrespondence.

Record Event : Type := {
  event_language : Language;
  event_rule : nat
}.

Fixpoint lambda_ledger (events : list Event) : list Event :=
  match events with
  | [] => []
  | event :: rest =>
      match event_language event with
      | Lambda => event :: lambda_ledger rest
      | Ambient => lambda_ledger rest
      end
  end.

Fixpoint ambient_ledger (events : list Event) : list Event :=
  match events with
  | [] => []
  | event :: rest =>
      match event_language event with
      | Lambda => ambient_ledger rest
      | Ambient => event :: ambient_ledger rest
      end
  end.

Theorem observation_ledgers_partition_the_trace : forall events,
  Permutation events (lambda_ledger events ++ ambient_ledger events).
Proof.
  induction events as [| event rest IH]; [constructor |].
  destruct event as [language rule].
  destruct language; cbn.
  - now apply perm_skip.
  - now apply Permutation_cons_app.
Qed.

Lemma lambda_ledger_contains_only_lambda_events : forall events event,
  In event (lambda_ledger events) -> event_language event = Lambda.
Proof.
  induction events as [| head rest IH]; intros event Hin; cbn in Hin.
  - contradiction.
  - destruct (event_language head) eqn:Hhead.
    + destruct Hin as [Heq | Hin]; [now subst | now apply IH].
    + now apply IH.
Qed.

Lemma ambient_ledger_contains_only_ambient_events : forall events event,
  In event (ambient_ledger events) -> event_language event = Ambient.
Proof.
  induction events as [| head rest IH]; intros event Hin; cbn in Hin.
  - contradiction.
  - destruct (event_language head) eqn:Hhead.
    + now apply IH.
    + destruct Hin as [Heq | Hin]; [now subst | now apply IH].
Qed.

Theorem observation_ledgers_are_disjoint : forall events event,
  In event (lambda_ledger events) ->
  In event (ambient_ledger events) -> False.
Proof.
  intros events event Hlambda Hambient.
  pose proof (lambda_ledger_contains_only_lambda_events events event Hlambda) as HL.
  pose proof (ambient_ledger_contains_only_ambient_events events event Hambient) as HA.
  rewrite HL in HA. discriminate.
Qed.

(* ========================================================================== *)
(* 5.  Positional AC remainder reconstruction and strict worklist decrease.    *)
(* ========================================================================== *)

Fixpoint remove_at {A : Type} (index : nat) (values : list A) : list A :=
  match index, values with
  | _, [] => []
  | 0, _ :: rest => rest
  | S next, value :: rest => value :: remove_at next rest
  end.

Lemma remove_at_deletes_exactly_one_position : forall (A : Type) index (values : list A),
  index < length values -> length (remove_at index values) + 1 = length values.
Proof.
  intros A index values.
  revert index.
  induction values as [| value rest IH]; intros [| index] Hlt;
    cbn in *; try lia.
  assert (Hrest : index < length rest) by lia.
  specialize (IH index Hrest). lia.
Qed.

Definition soup_size (term : Term) : nat :=
  match term with
  | TBag _ _ elements => length elements
  | _ => 0
  end.

Definition soup_remainder_at (index : nat) (term : Term) : Term :=
  match term with
  | TBag language operator elements => TBag language operator (remove_at index elements)
  | _ => term
  end.

Theorem every_valid_soup_peel_strictly_decreases : forall language operator elements index,
  index < length elements ->
  soup_size (soup_remainder_at index (TBag language operator elements)) + 1 =
  soup_size (TBag language operator elements).
Proof.
  intros language operator elements index Hlt. cbn.
  now apply remove_at_deletes_exactly_one_position.
Qed.

Definition ambient_zero : Term := TNode Ambient 0 [].

Example duplicate_nullary_peel_preserves_one_remaining_occurrence :
  soup_remainder_at 0 (TBag Ambient 0 [ambient_zero; ambient_zero]) =
  TBag Ambient 0 [ambient_zero].
Proof. reflexivity. Qed.

Example duplicate_nullary_peel_has_strict_measure_descent :
  soup_size (soup_remainder_at 0 (TBag Ambient 0 [ambient_zero; ambient_zero])) + 1 =
  soup_size (TBag Ambient 0 [ambient_zero; ambient_zero]).
Proof. reflexivity. Qed.

(* Concrete non-vacuity witnesses for the Track A routes. *)
Definition lambda_value : Term := TNode Lambda 0 [].
Definition ambient_value : Term := TNode Ambient 0 [].

Example lambda_root_uses_lambda_driver :
  root_route Lambda lambda_value = Routed Lambda.
Proof. reflexivity. Qed.

Example ambient_root_uses_ambient_driver :
  root_route Ambient ambient_value = Routed Ambient.
Proof. reflexivity. Qed.

Example wrong_driver_is_a_veto :
  root_route Lambda ambient_value = WrongRoot.
Proof. reflexivity. Qed.

Example lambda_contractum_may_reenter_ambient :
  nested_route ambient_value = Routed Ambient.
Proof. reflexivity. Qed.

Example lambda_shift_does_not_enter_ambient : forall local,
  boundary_transform Lambda local ambient_value = ambient_value.
Proof. intros local. reflexivity. Qed.
