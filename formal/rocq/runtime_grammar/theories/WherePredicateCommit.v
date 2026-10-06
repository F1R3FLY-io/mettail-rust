(** The narrow where adapter connector. Keys are produced by the existing
    checked native worker, never by a second evaluator. A complete roster is
    supplied only after the existing service has validated every receipt.
    Authority and host funding are inputs to the existing atomic mutation gate;
    these laws do not prove Rust locks, kernel completeness, or funding policy. *)
From Stdlib Require Import List Bool Arith.PeanoNat.
Import ListNotations.
Module WherePredicateCommit.

Inductive Verdict := Yes | No | Unknown.
Definition negate (v : Verdict) :=
  match v with Yes => No | No => Yes | Unknown => Unknown end.

Definition classify (complete : bool) (results : list Verdict) :=
  if complete then
    match results with
    | [] => Unknown
    | first :: rest =>
        match first with
        | Yes => if forallb (fun v => match v with Yes => true | _ => false end) rest
                 then Yes else Unknown
        | No => if forallb (fun v => match v with No => true | _ => false end) rest
                then No else Unknown
        | Unknown => Unknown
        end
    end
  else Unknown.

Lemma incomplete_unknown : forall results, classify false results = Unknown.
Proof. reflexivity. Qed.
Lemma empty_unknown : forall complete, classify complete [] = Unknown.
Proof. intros []; reflexivity. Qed.
Lemma negated_unknown : negate Unknown = Unknown.
Proof. reflexivity. Qed.
Lemma classified_yes_sound : forall results,
  classify true results = Yes -> results <> [] /\ Forall (fun v => v = Yes) results.
Proof.
  intros [|first rest]; cbn; [discriminate|].
  destruct first; cbn.
  - destruct (forallb _ rest) eqn:H; [|discriminate]. intros _.
    split; [discriminate|constructor; [reflexivity|]].
    apply Forall_forall. intros v Hv. apply forallb_forall with (x:=v) in H; auto.
    destruct v; congruence.
  - destruct (forallb _ rest); discriminate.
  - discriminate.
Qed.
Lemma classified_no_sound : forall results,
  classify true results = No -> results <> [] /\ Forall (fun v => v = No) results.
Proof.
  intros [|first rest]; cbn; [discriminate|]. destruct first; cbn.
  - destruct (forallb _ rest); discriminate.
  - destruct (forallb _ rest) eqn:H; [|discriminate]. intros _.
    split; [discriminate|constructor; [reflexivity|]].
    apply Forall_forall. intros v Hv. apply forallb_forall with (x:=v) in H; auto.
    destruct v; congruence.
  - discriminate.
Qed.

(** Explicit capture coordinates use exactly the receive environment's reverse
    de Bruijn roster. Repeated slots are occurrences, not deduplicated names. *)
Definition capture {A : Type} (bindings : list A) (slot : nat) :=
  nth_error (rev bindings) slot.
Definition captures {A : Type} (bindings : list A) (slots : list nat) :=
  map (capture bindings) slots.
Lemma capture_occurrence_order : forall A (bindings : list A) left right,
  captures bindings (left ++ right) = captures bindings left ++ captures bindings right.
Proof. intros; apply map_app. Qed.
Lemma repeated_capture_identity : forall A (bindings : list A) slot,
  captures bindings [slot;slot] = [capture bindings slot;capture bindings slot].
Proof. reflexivity. Qed.

Definition commit {S : Type} (verdict : Verdict) (authority funded : bool)
    (mutation : S -> S) (state : S) :=
  match verdict with
  | Yes => if authority && funded then mutation state else state
  | _ => state
  end.
Lemma refusal_preserves_state : forall S verdict authority funded mutation (state : S),
  verdict <> Yes \/ authority = false \/ funded = false ->
  commit verdict authority funded mutation state = state.
Proof. intros S [] [] [] mutation state H; cbn in *; intuition congruence. Qed.
Lemma admitted_single_mutation : forall S mutation (state : S),
  commit Yes true true mutation state = mutation state.
Proof. reflexivity. Qed.

(** Each prepared atom may rely on a distinct host profile. The installation
    table checks all guest and optional host handles under one read lock before
    invoking the mutation callback; this model states the resulting Boolean
    admission law independently of the Rust lock implementation. *)
Record AuthorityCheck := authority_check {
  guest_live : bool;
  host_required : bool;
  host_live : bool
}.

Definition atom_authorized (check : AuthorityCheck) : bool :=
  guest_live check && (negb (host_required check) || host_live check).

Definition batch_authorized (checks : list AuthorityCheck) : bool :=
  forallb atom_authorized checks.

Definition batch_commit {S : Type} (verdict : Verdict) (checks : list AuthorityCheck)
    (funded : bool) (mutation : S -> S) (state : S) :=
  commit verdict (batch_authorized checks) funded mutation state.

Lemma revoked_required_host_refuses_atom : forall check,
  host_required check = true -> host_live check = false ->
  atom_authorized check = false.
Proof.
  intros check Required Revoked.
  unfold atom_authorized. rewrite Required, Revoked.
  now destruct (guest_live check).
Qed.

Lemma refused_atom_refuses_whole_batch : forall prefix check suffix,
  atom_authorized check = false ->
  batch_authorized (prefix ++ check :: suffix) = false.
Proof.
  intros prefix check suffix Refused.
  unfold batch_authorized.
  rewrite forallb_app. simpl. rewrite Refused.
  now destruct (forallb atom_authorized prefix).
Qed.

Lemma revoked_required_host_preserves_comm : forall S verdict prefix check suffix funded
    mutation (state : S),
  host_required check = true -> host_live check = false ->
  batch_commit verdict (prefix ++ check :: suffix) funded mutation state = state.
Proof.
  intros S verdict prefix check suffix funded mutation state Required Revoked.
  unfold batch_commit.
  rewrite (refused_atom_refuses_whole_batch prefix check suffix
    (revoked_required_host_refuses_atom check Required Revoked)).
  apply refusal_preserves_state. now right; left.
Qed.
End WherePredicateCommit.
