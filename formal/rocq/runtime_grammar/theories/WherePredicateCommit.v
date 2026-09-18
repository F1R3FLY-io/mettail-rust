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
End WherePredicateCommit.
