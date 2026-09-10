(** Shared recipe for runtime/src/binding.rs::Scope::with_closing.

    Source: moniker-0.5.0/src/scope.rs::Scope::new:
      body.close_term(ScopeState::new(), &pattern.binders());
      Scope { unsafe_pattern: pattern, unsafe_body: body }

    The iterative constructor changes only closing dispatch. Natural zero
    represents ScopeState::new().depth(), not a new lexical-index calculus.
    [roster_of] denotes the existing BoundPattern::binders operation; [close]
    denotes a functional interpretation of closing. No axiom asserts their
    implementation correctness. The later generated engine must discharge
    the pointwise correspondence premise below for its actual operations.

    The trace describes the constructor's dispatch schedule, not arbitrary
    Rust callback effects, borrow checking, allocation, temporary destruction,
    or panic behavior. Opening and freshening are outside this increment. *)

From Stdlib Require Import List Arith.
Import ListNotations.

Module ScopeConstructionRecipe.

Record ScopeResult (Pattern Body : Type) := {
  saved_pattern : Pattern;
  saved_body : Body
}.

Arguments saved_pattern {Pattern Body} _.
Arguments saved_body {Pattern Body} _.

Inductive RecipeEvent (Binder : Type) :=
| ObserveRoster (roster : list Binder)
| InvokeClose (depth : nat)
| ConstructScope.

Arguments ObserveRoster {Binder} _.
Arguments InvokeClose {Binder} _.
Arguments ConstructScope {Binder}.

Section Recipe.

Context {Pattern Body Binder : Type}.

Definition with_closing
    (roster_of : Pattern -> list Binder)
    (close : Body -> nat -> list Binder -> Body)
    (pattern : Pattern) (body : Body)
    : ScopeResult Pattern Body :=
  let roster := roster_of pattern in
  let closed := close body 0 roster in
  {| saved_pattern := pattern; saved_body := closed |}.

(** Direct transcription of the existing Moniker constructor. *)
Definition moniker_new
    (roster_of : Pattern -> list Binder)
    (moniker_close : Body -> nat -> list Binder -> Body)
    (pattern : Pattern) (body : Body)
    : ScopeResult Pattern Body :=
  {| saved_pattern := pattern;
     saved_body := moniker_close body 0 (roster_of pattern) |}.

Definition traced_with_closing
    (roster_of : Pattern -> list Binder)
    (close : Body -> nat -> list Binder -> Body)
    (pattern : Pattern) (body : Body)
    : ScopeResult Pattern Body * list (RecipeEvent Binder) :=
  let roster := roster_of pattern in
  let closed := close body 0 roster in
  ({| saved_pattern := pattern; saved_body := closed |},
   [ObserveRoster roster; InvokeClose 0; ConstructScope]).

Theorem shared_recipe_is_existing_constructor :
  forall roster_of close pattern body,
  with_closing roster_of close pattern body =
  moniker_new roster_of close pattern body.
Proof. reflexivity. Qed.

Theorem constructor_preserves_pattern :
  forall roster_of close pattern body,
  saved_pattern (with_closing roster_of close pattern body) = pattern.
Proof. reflexivity. Qed.

Theorem constructor_returns_exact_zero_depth_close :
  forall roster_of close pattern body,
  saved_body (with_closing roster_of close pattern body) =
  close body 0 (roster_of pattern).
Proof. reflexivity. Qed.

Theorem tracing_preserves_constructor_result :
  forall roster_of close pattern body,
  fst (traced_with_closing roster_of close pattern body) =
  with_closing roster_of close pattern body.
Proof. reflexivity. Qed.

Theorem recipe_preserves_roster_and_dispatch_order :
  forall roster_of close pattern body,
  snd (traced_with_closing roster_of close pattern body) =
  [ObserveRoster (roster_of pattern); InvokeClose 0; ConstructScope].
Proof. reflexivity. Qed.

Fixpoint closing_depths (events : list (RecipeEvent Binder)) : list nat :=
  match events with
  | [] => []
  | InvokeClose depth :: rest => depth :: closing_depths rest
  | _ :: rest => closing_depths rest
  end.

Theorem recipe_closes_exactly_once_at_zero :
  forall roster_of close pattern body,
  closing_depths
    (snd (traced_with_closing roster_of close pattern body)) = [0].
Proof. reflexivity. Qed.

(** This theorem exposes, rather than discharges, the engine obligation. *)
Theorem matching_closers_produce_identical_scopes :
  forall roster_of moniker_close iterative_close pattern body,
  iterative_close body 0 (roster_of pattern) =
    moniker_close body 0 (roster_of pattern) ->
  with_closing roster_of iterative_close pattern body =
    moniker_new roster_of moniker_close pattern body.
Proof.
  intros roster_of moniker_close iterative_close pattern body H.
  unfold with_closing, moniker_new.
  now rewrite H.
Qed.

Theorem recipe_schedule_is_independent_of_closing_dispatch :
  forall roster_of first_close second_close pattern body,
  snd (traced_with_closing roster_of first_close pattern body) =
  snd (traced_with_closing roster_of second_close pattern body).
Proof. reflexivity. Qed.

(** [wrap] denotes Arc::new functionally, not allocation or pointer sharing. *)
Theorem wrapping_closed_body_preserves_recipe :
  forall (Wrapped : Type) (wrap : Body -> Wrapped)
    roster_of close pattern body,
  wrap (saved_body (with_closing roster_of close pattern body)) =
  wrap (close body 0 (roster_of pattern)).
Proof. reflexivity. Qed.

End Recipe.

Print Assumptions shared_recipe_is_existing_constructor.
Print Assumptions constructor_preserves_pattern.
Print Assumptions constructor_returns_exact_zero_depth_close.
Print Assumptions tracing_preserves_constructor_result.
Print Assumptions recipe_preserves_roster_and_dispatch_order.
Print Assumptions recipe_closes_exactly_once_at_zero.
Print Assumptions matching_closers_produce_identical_scopes.
Print Assumptions recipe_schedule_is_independent_of_closing_dispatch.
Print Assumptions wrapping_closed_body_preserves_recipe.

End ScopeConstructionRecipe.
