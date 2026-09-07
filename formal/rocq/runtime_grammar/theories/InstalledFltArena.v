(** * Realizing converted occurrences in a fresh add-only egraph

    During FLT input conversion there are no merges or rebuilds.  Each fresh
    class is a singleton with a self-representative, and insertion changes
    existing parent metadata but not existing node observations.  Therefore
    the observable store is an append-only arena of exact nodes.

    [find_existing] specifies an exact memo lookup by its observable result;
    its reference list scan is NOT a proposed runtime implementation.  The
    existing hash-cons table remains the production implementation.  Native
    values and constructor labels denote complete checked heads, not hashes.

    Child coordinates are checked before lookup/canonicalization.  Capacity is
    the effective minimum of the node ceiling and representable class-count
    ceiling.  Exact duplicate nodes still succeed at capacity.  The existing
    [EGraphBudgetDedup] contract supplies key membership/budget guarantees;
    this module adds returned-coordinate and whole-occurrence realization.

    Rust memo/union-find correspondence and physical operator framing remain
    implementation obligations.  Nothing here proves arbitrary graph merges,
    rewrite correctness, resource charging, or byte-level serialization. *)

From Stdlib Require Import List Arith Lia.
From EGraph Require Import EGraphBudgetDedup.
From RuntimeGrammar Require Import BorrowedOccurrenceExecution.
From PrattailWpdaRuntime Require Import SelectedOccurrencePlan.
Import ListNotations.
Set Implicit Arguments.

Module InstalledFltArena.
Module Borrowed := BorrowedOccurrenceExecution.BorrowedOccurrenceExecution.

Section AddOnlyArena.
Context {Value Label : Type}.
Variable value_eq_dec : forall first second : Value, {first = second} + {first <> second}.
Variable label_eq_dec : forall first second : Label, {first = second} + {first <> second}.

Definition Node := @Borrowed.Node nat Value Label.
Definition Arena := list Node.

Definition node_eq_dec : forall first second : Node, {first = second} + {first <> second}.
Proof.
  decide equality; auto using value_eq_dec, label_eq_dec, list_eq_dec, Nat.eq_dec.
Defined.

Definition child_references (node : Node) :=
  match node with Borrowed.NativeNode _ => [] | Borrowed.ConstructorNode _ children => children end.

Definition valid_children size node :=
  forallb (fun child => child <? size) (child_references node).

Fixpoint find_existing (node : Node) (arena : Arena) : option nat :=
  match arena with
  | [] => None
  | head :: rest => if node_eq_dec node head then Some 0
      else option_map S (find_existing node rest)
  end.

Lemma existing_coordinate_has_exact_node : forall arena node reference,
  find_existing node arena = Some reference -> nth_error arena reference = Some node.
Proof.
  induction arena as [|head rest IH]; intros node reference H; [discriminate|].
  cbn [find_existing] in H. destruct (node_eq_dec node head) as [E|E].
  - subst head. inversion H. reflexivity.
  - destruct (find_existing node rest) as [index|] eqn:Eindex; try discriminate.
    inversion H; subst reference. cbn [nth_error]. now apply IH.
Qed.

Lemma missing_coordinate_has_no_exact_node : forall arena node,
  find_existing node arena = None -> ~ In node arena.
Proof.
  induction arena as [|head rest IH]; intros node H; [tauto|].
  cbn [find_existing] in H. destruct (node_eq_dec node head) as [E|E]; [discriminate|].
  destruct (find_existing node rest) as [index|] eqn:Eindex; [discriminate|].
  intros [Hhead|Hrest]; [symmetry in Hhead; contradiction|].
  exact (IH node Eindex Hrest).
Qed.
Arguments missing_coordinate_has_no_exact_node {arena node} _.

Definition checked_intern capacity node arena : option (Arena * nat) :=
  if valid_children (length arena) node then
    match find_existing node arena with
    | Some reference => Some (arena, reference)
    | None => if length arena <? capacity then Some (arena ++ [node], length arena) else None
    end
  else None.

Lemma successful_intern_is_exact_hit_or_fresh_append :
  forall capacity node arena next reference,
  checked_intern capacity node arena = Some (next, reference) ->
  valid_children (length arena) node = true /\
  ((next = arena /\ nth_error arena reference = Some node) \/
   (find_existing node arena = None /\ length arena < capacity /\
    next = arena ++ [node] /\ reference = length arena)).
Proof.
  intros capacity node arena next reference H. unfold checked_intern in H.
  destruct (valid_children (length arena) node) eqn:Evalid; [|discriminate].
  split; [reflexivity|].
  destruct (find_existing node arena) as [existing|] eqn:Eexisting.
  - inversion H; subst. left. split; [reflexivity|now apply existing_coordinate_has_exact_node].
  - destruct (length arena <? capacity) eqn:Ecapacity; [|discriminate].
    inversion H; subst. right. repeat split; try assumption; try reflexivity.
    now apply Nat.ltb_lt.
Qed.
Arguments successful_intern_is_exact_hit_or_fresh_append {capacity node arena next reference} _.

Definition Extends (before after : Arena) :=
  forall reference node, nth_error before reference = Some node ->
    nth_error after reference = Some node.

Lemma appended_arena_preserves_existing_nodes : forall arena node,
  Extends arena (arena ++ [node]).
Proof.
  intros arena node reference old H. rewrite nth_error_app1; [exact H|].
  apply nth_error_Some. rewrite H. discriminate.
Qed.

Theorem successful_intern_preserves_old_nodes_and_returns_exact_node :
  forall capacity node arena next reference,
  checked_intern capacity node arena = Some (next, reference) ->
  Extends arena next /\ nth_error next reference = Some node.
Proof.
  intros capacity node arena next reference H.
  destruct (successful_intern_is_exact_hit_or_fresh_append H)
    as [Hvalid [[Earena Hnode]|[Hmissing [Hcapacity [Earena Ereference]]]]]; subst.
  - split; [intros old_reference old_node Hlookup; exact Hlookup|exact Hnode].
  - split; [apply appended_arena_preserves_existing_nodes|].
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
Arguments successful_intern_preserves_old_nodes_and_returns_exact_node
  {capacity node arena next reference} _.

Theorem successful_intern_refines_existing_budget_contract :
  forall capacity node arena next reference,
  checked_intern capacity node arena = Some (next, reference) ->
  snd (@budget_add Node node_eq_dec capacity node arena) = false /\
  @exact_equiv Node next (fst (@budget_add Node node_eq_dec capacity node arena)).
Proof.
  intros capacity node arena next reference H.
  destruct (successful_intern_is_exact_hit_or_fresh_append H)
    as [Hvalid [[Earena Hnode]|[Hmissing [Hcapacity [Earena Ereference]]]]]; subst.
  - unfold budget_add. destruct (in_dec node_eq_dec node arena) as [Hin|Hnot].
    + split; [reflexivity|intro key; reflexivity].
    + exfalso. apply Hnot. eapply nth_error_In; exact Hnode.
  - unfold budget_add. destruct (in_dec node_eq_dec node arena) as [Hin|Hnot].
    + exfalso. exact (missing_coordinate_has_no_exact_node Hmissing Hin).
    + assert (Ecapacity : (length arena <? capacity) = true) by now apply Nat.ltb_lt.
      rewrite Ecapacity. split; [reflexivity|].
      intro key. cbn [fst]. rewrite in_app_iff. cbn. tauto.
Qed.
Arguments successful_intern_refines_existing_budget_contract {capacity node arena next reference} _.

Corollary successful_intern_has_no_spurious_key : forall capacity node arena next reference key,
  checked_intern capacity node arena = Some (next, reference) ->
  In key next -> key = node \/ In key arena.
Proof.
  intros capacity node arena next reference key H Hin.
  destruct (successful_intern_refines_existing_budget_contract H) as [_ Hequiv].
  eapply (@budget_add_no_spurious_key Node node_eq_dec capacity node arena key).
  apply (proj1 (Hequiv key)). exact Hin.
Qed.

Theorem successful_intern_stays_within_capacity : forall capacity node arena next reference,
  length arena <= capacity ->
  checked_intern capacity node arena = Some (next, reference) ->
  length next <= capacity /\ reference < length next.
Proof.
  intros capacity node arena next reference Hcapacity H.
  pose proof (successful_intern_preserves_old_nodes_and_returns_exact_node H) as [_ Hnode].
  assert (Hreference : reference < length next).
  { apply nth_error_Some. rewrite Hnode. discriminate. }
  split; [|exact Hreference].
  destruct (successful_intern_is_exact_hit_or_fresh_append H)
    as [Hvalid [[Earena Hexisting]|[Hmissing [Hfresh [Earena Ereference]]]]]; subst;
    [exact Hcapacity|rewrite length_app; cbn; lia].
Qed.

Theorem lookup_extension_preserves_finite_occurrences : forall before after,
  Extends before after ->
  (forall reference occurrence, Borrowed.Unfolds (nth_error before) reference occurrence ->
    Borrowed.Unfolds (nth_error after) reference occurrence) /\
  (forall references occurrences, Borrowed.UnfoldChildren (nth_error before) references occurrences ->
    Borrowed.UnfoldChildren (nth_error after) references occurrences).
Proof.
  intros before after Hextends. apply Borrowed.unfold_mutual.
  - intros reference value Hlookup. constructor. now apply Hextends.
  - intros reference label children occurrences Hlookup Hchildren IH.
    econstructor.
    + exact (Hextends reference (Borrowed.ConstructorNode label children) Hlookup).
    + exact IH.
  - constructor.
  - intros reference references occurrence occurrences Hfirst IHfirst Hlater IHlater.
    constructor; assumption.
Qed.
Arguments lookup_extension_preserves_finite_occurrences {before after} _.

Theorem interned_constructor_realizes_all_ordered_child_occurrences :
  forall capacity arena next reference label children occurrences,
  Borrowed.UnfoldChildren (nth_error arena) children occurrences ->
  checked_intern capacity (Borrowed.ConstructorNode label children) arena = Some (next, reference) ->
  Borrowed.Unfolds (nth_error next) reference (SelectedBranch label occurrences).
Proof.
  intros capacity arena next reference label children occurrences Hchildren H.
  destruct (successful_intern_preserves_old_nodes_and_returns_exact_node H) as [Hextends Hnode].
  econstructor; [exact Hnode|].
  exact (proj2 (lookup_extension_preserves_finite_occurrences Hextends) _ _ Hchildren).
Qed.

Theorem interned_native_realizes_its_exact_value : forall capacity arena next reference value,
  checked_intern capacity (Borrowed.NativeNode value) arena = Some (next, reference) ->
  Borrowed.Unfolds (nth_error next) reference (SelectedLeaf value).
Proof.
  intros capacity arena next reference value H. constructor.
  exact (proj2 (successful_intern_preserves_old_nodes_and_returns_exact_node H)).
Qed.

(** Every child in a fresh arena predates its parent.  This is stronger than
    mere coordinate validity and gives finite unfolding without an assumed
    acyclicity oracle.  It is restricted to the no-merge construction phase. *)
Definition Topological (arena : Arena) :=
  forall reference node, nth_error arena reference = Some node ->
    Forall (fun child => child < reference) (child_references node).

Lemma empty_arena_is_topological : Topological [].
Proof. intros [|reference] node H; discriminate. Qed.

Theorem successful_intern_preserves_topological_layout :
  forall capacity node arena next reference,
  Topological arena ->
  checked_intern capacity node arena = Some (next, reference) -> Topological next.
Proof.
  intros capacity node arena next reference Htopological H.
  destruct (successful_intern_is_exact_hit_or_fresh_append H)
    as [Hvalid [[Earena Hnode]|[Hmissing [Hcapacity [Earena Ereference]]]]]; subst;
    [exact Htopological|].
  intros index stored Hlookup.
  destruct (lt_dec index (length arena)) as [Hbefore|Hfresh].
  - rewrite nth_error_app1 in Hlookup by exact Hbefore.
    exact (Htopological index stored Hlookup).
  - assert (Hbound : index < length (arena ++ [node])).
    { apply nth_error_Some. rewrite Hlookup. discriminate. }
    rewrite length_app in Hbound. cbn in Hbound.
    assert (Eindex : index = length arena) by lia. subst index.
    rewrite nth_error_app2 in Hlookup by lia. rewrite Nat.sub_diag in Hlookup.
    inversion Hlookup; subst stored.
    unfold valid_children in Hvalid. rewrite forallb_forall in Hvalid.
    apply Forall_forall. intros child Hchild. apply Nat.ltb_lt. now apply Hvalid.
Qed.

Lemma finite_children_supply_an_ordered_unfolding : forall (arena : Arena) references,
  Forall (fun reference => exists occurrence,
    Borrowed.Unfolds (nth_error arena) reference occurrence) references ->
  exists occurrences, Borrowed.UnfoldChildren (nth_error arena) references occurrences.
Proof.
  intros arena references H.
  induction H as [|reference references [occurrence Hfirst] Hlater [occurrences Hrest]].
  - exists NoChildren. constructor.
  - exists (MoreChildren occurrence occurrences). constructor; assumption.
Qed.
Arguments finite_children_supply_an_ordered_unfolding {arena references} _.

Theorem topological_arena_supplies_finite_occurrences : forall arena,
  Topological arena -> forall reference,
  reference < length arena ->
  exists occurrence, Borrowed.Unfolds (nth_error arena) reference occurrence.
Proof.
  intros arena Htopological reference.
  induction reference using lt_wf_ind. intro Hbound.
  destruct (nth_error arena reference) as [node|] eqn:Hnode.
  - destruct node as [value|label children].
    + exists (SelectedLeaf value). constructor. exact Hnode.
    + pose proof (Htopological reference (Borrowed.ConstructorNode label children) Hnode)
        as Hchildren. cbn [child_references] in Hchildren.
      assert (Hfinite : Forall (fun child => exists occurrence,
        Borrowed.Unfolds (nth_error arena) child occurrence) children).
      { apply Forall_forall. intros child Hin.
        rewrite Forall_forall in Hchildren. specialize (Hchildren child Hin).
        apply H; lia. }
      destruct (finite_children_supply_an_ordered_unfolding Hfinite)
        as [occurrences Hunfold].
      exists (SelectedBranch label occurrences). econstructor; eassumption.
  - apply nth_error_Some in Hbound. rewrite Hnode in Hbound. contradiction.
Qed.

Theorem exact_duplicate_succeeds_even_at_capacity : forall capacity arena node reference,
  valid_children (length arena) node = true -> find_existing node arena = Some reference ->
  checked_intern capacity node arena = Some (arena, reference).
Proof.
  intros capacity arena node reference Hvalid Hexisting.
  unfold checked_intern. now rewrite Hvalid, Hexisting.
Qed.

Example missing_child_coordinate_is_refused : forall label,
  checked_intern 2 (Borrowed.ConstructorNode label [0]) [] = None.
Proof. intro label. reflexivity. Qed.

Example zero_capacity_refuses_a_fresh_native : forall value,
  checked_intern 0 (Borrowed.NativeNode value) [] = None.
Proof. intro value. reflexivity. Qed.

Example shared_child_is_realized_at_both_positions : forall (value : Value) (label : Label),
  let leaf : Node := Borrowed.NativeNode value in
  let parent : Node := Borrowed.ConstructorNode label [0; 0] in
  Borrowed.Unfolds (nth_error [leaf; parent]) 1
    (SelectedBranch label
      (MoreChildren (SelectedLeaf value) (MoreChildren (SelectedLeaf value) NoChildren))).
Proof.
  intros value label leaf parent.
  eapply interned_constructor_realizes_all_ordered_child_occurrences
    with (capacity := 2) (arena := [leaf]) (children := [0; 0]).
  - repeat constructor; reflexivity.
  - reflexivity.
Qed.

End AddOnlyArena.
End InstalledFltArena.

Print Assumptions InstalledFltArena.successful_intern_preserves_old_nodes_and_returns_exact_node.
Print Assumptions InstalledFltArena.successful_intern_refines_existing_budget_contract.
Print Assumptions InstalledFltArena.successful_intern_has_no_spurious_key.
Print Assumptions InstalledFltArena.successful_intern_stays_within_capacity.
Print Assumptions InstalledFltArena.lookup_extension_preserves_finite_occurrences.
Print Assumptions InstalledFltArena.interned_constructor_realizes_all_ordered_child_occurrences.
Print Assumptions InstalledFltArena.interned_native_realizes_its_exact_value.
Print Assumptions InstalledFltArena.successful_intern_preserves_topological_layout.
Print Assumptions InstalledFltArena.topological_arena_supplies_finite_occurrences.
Print Assumptions InstalledFltArena.exact_duplicate_succeeds_even_at_capacity.
Print Assumptions InstalledFltArena.shared_child_is_realized_at_both_positions.
