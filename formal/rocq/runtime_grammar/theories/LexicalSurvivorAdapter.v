(** Shared lexical survivor adapter.

    PraTTaIL already orders accepting endpoints longest-first and retains the
    first candidate of each token kind. This file specifies that existing
    operation, relates its iterative accumulator to the ordered specification,
    and connects a selected context-indexed edge to the existing RTN scan law.
    This is not a new lexer policy: shorter matches of the same kind are
    excluded by the existing lexical contract, not by semantic evidence.

    Payloads are opaque. Selection must preserve their exact identity, order,
    and endpoint; decoding and mode transitions remain in their adapters.
    These laws do not assert unrestricted token-segmentation completeness,
    mode-stack confluence, or operational completeness of the chart machine.
*)
From Stdlib Require Import List PeanoNat Lia.
From RuntimeGrammar Require Import LexerMaximalMunch ImageAdmission RtnChart.
Import ListNotations.

Section OrderedSelection.
  Context {Entry : Type}.
  Variable key : Entry -> nat.

  Fixpoint select_first (seen : list nat) (entries : list Entry) : list Entry :=
    match entries with
    | [] => []
    | entry :: rest =>
        if in_dec Nat.eq_dec (key entry) seen then select_first seen rest
        else entry :: select_first (key entry :: seen) rest
    end.

  (** The emitted accumulator is reversed so the implementation model is
      tail-recursive. Reversing once restores the generated edge order. *)
  Fixpoint select_loop (entries : list Entry)
      (seen : list nat) (emitted : list Entry) : list Entry :=
    match entries with
    | [] => emitted
    | entry :: rest =>
        if in_dec Nat.eq_dec (key entry) seen then select_loop rest seen emitted
        else select_loop rest (key entry :: seen) (entry :: emitted)
    end.

  Theorem loop_refines_ordered_selection : forall entries seen emitted,
    select_loop entries seen emitted = rev (select_first seen entries) ++ emitted.
  Proof.
    induction entries as [|entry rest IH]; intros seen emitted; cbn.
    - reflexivity.
    - destruct (in_dec Nat.eq_dec (key entry) seen); rewrite IH; cbn.
      + reflexivity.
      + now rewrite <- app_assoc.
  Qed.

  Theorem selected_entry_is_exact_and_unseen : forall entries seen entry,
    In entry (select_first seen entries) ->
    In entry entries /\ ~ In (key entry) seen.
  Proof.
    induction entries as [|head rest IH]; intros seen entry Hin; cbn in Hin.
    - contradiction.
    - destruct (in_dec Nat.eq_dec (key head) seen) as [Hseen|Hfresh].
      + destruct (IH seen entry Hin) as [Hmember Hnew]. split; auto.
        now right.
      + destruct Hin as [Heq|Hin].
        * subst entry. split; auto. now left.
        * destruct (IH (key head :: seen) entry Hin) as [Hmember Hnew].
          split; [now right|]. intro H. apply Hnew. now right.
  Qed.

  Theorem every_unseen_kind_has_a_survivor : forall entries seen kind,
    In kind (map key entries) -> ~ In kind seen ->
    exists entry, In entry (select_first seen entries) /\ key entry = kind.
  Proof.
    induction entries as [|head rest IH]; intros seen kind Hin Hfresh; cbn in *.
    - contradiction.
    - destruct (in_dec Nat.eq_dec (key head) seen) as [Hseen|Hnew].
      + apply IH; [|exact Hfresh]. destruct Hin as [Heq|Hin]; auto.
        subst kind. contradiction.
      + destruct (Nat.eq_dec (key head) kind) as [Heq|Hneq].
        * exists head. split; [now left|exact Heq].
        * assert (Htail : In kind (map key rest)).
          { destruct Hin as [Heq|Hin]; [contradiction|exact Hin]. }
          assert (Hfresh' : ~ In kind (key head :: seen)).
          { intros [Heq|H]; [contradiction|now apply Hfresh]. }
          destruct (IH (key head :: seen) kind Htail Hfresh')
            as [entry [Hentry Hkey]].
          exists entry. split; [now right|exact Hkey].
  Qed.

  Theorem selected_kinds_are_unique : forall entries seen,
    NoDup (map key (select_first seen entries)).
  Proof.
    induction entries as [|head rest IH]; intro seen; cbn; [constructor|].
    destruct (in_dec Nat.eq_dec (key head) seen); [apply IH|].
    cbn. constructor; [|apply IH].
    intro Hin. apply in_map_iff in Hin.
    destruct Hin as [entry [Hkey Hentry]].
    destruct (selected_entry_is_exact_and_unseen rest (key head :: seen)
      entry Hentry) as [_ Hnew].
    apply Hnew. left. symmetry. exact Hkey.
  Qed.

  Theorem selection_preserves_every_entry_property : forall entries seen property,
    Forall property entries -> Forall property (select_first seen entries).
  Proof.
    intros entries seen property Hall. rewrite Forall_forall in *.
    intros entry Hin. apply Hall.
    now apply (selected_entry_is_exact_and_unseen entries seen entry) in Hin.
  Qed.
End OrderedSelection.

Section Endpoints.
  Context {Payload : Type}.
  Record Candidate := {
    candidate_kind : nat;
    candidate_end : nat;
    candidate_payload : Payload
  }.

  Fixpoint descending (entries : list Candidate) : Prop :=
    match entries with
    | [] => True
    | head :: rest =>
        Forall (fun entry => candidate_end entry <= candidate_end head) rest /\
        descending rest
    end.

  Theorem every_survivor_is_maximal_for_its_kind : forall entries seen selected,
    descending entries ->
    In selected (select_first candidate_kind seen entries) ->
    forall other, In other entries -> candidate_kind other = candidate_kind selected ->
      candidate_end other <= candidate_end selected.
  Proof.
    induction entries as [|head rest IH]; intros seen selected Hordered Hselected
      other Hother Hkind; cbn in Hselected; [contradiction|].
    destruct Hordered as [Hbounds Hordered].
    destruct (in_dec Nat.eq_dec (candidate_kind head) seen) as [Hseen|Hfresh].
    - destruct Hother as [Heq|Hother].
      + subst other.
        destruct (selected_entry_is_exact_and_unseen candidate_kind rest seen
          selected Hselected) as [_ Hnew].
        exfalso. apply Hnew. now rewrite <- Hkind.
      + eapply IH; eauto.
    - destruct Hselected as [Heq|Hselected].
      + subst selected. destruct Hother as [Heq|Hother].
        * subst other. lia.
        * now apply (proj1 (Forall_forall _ _) Hbounds).
      + destruct Hother as [Heq|Hother].
        * subst other.
          destruct (selected_entry_is_exact_and_unseen candidate_kind rest
            (candidate_kind head :: seen) selected Hselected) as [_ Hnew].
          exfalso. apply Hnew. left. exact Hkind.
        * eapply IH; eauto.
  Qed.

  Definition survivors (entries : list Candidate) :=
    select_first candidate_kind [] entries.

  Definition successors (entries : list Candidate) : list nat :=
    map candidate_end (select_first candidate_end [] (survivors entries)).

  Theorem successor_iff_surviving_endpoint : forall entries endpoint,
    In endpoint (successors entries) <->
    exists entry, In entry (survivors entries) /\ candidate_end entry = endpoint.
  Proof.
    intros entries endpoint. unfold successors. split.
    - intro Hin. apply in_map_iff in Hin. destruct Hin as [entry [Hend Hin]].
      apply (selected_entry_is_exact_and_unseen candidate_end _ [] entry) in Hin.
      exists entry. split; [exact (proj1 Hin)|exact Hend].
    - intros [entry [Hin Hend]].
      assert (Hmapped : In endpoint (map candidate_end (survivors entries))).
      { apply in_map_iff. exists entry. split; assumption. }
      destruct (every_unseen_kind_has_a_survivor candidate_end _ [] endpoint
        Hmapped ltac:(cbn; tauto)) as [selected [Hselected Hend']].
      apply in_map_iff. exists selected. split; assumption.
  Qed.

  Theorem successor_endpoints_are_unique : forall entries,
    NoDup (successors entries).
  Proof. intro entries. apply selected_kinds_are_unique. Qed.
End Endpoints.

(** Token-specific maximality reuses the existing DFA model and theorem. *)
Definition for_token (dfa : LexerMaximalMunch.Dfa) (token : nat)
    : LexerMaximalMunch.Dfa :=
  {| LexerMaximalMunch.start_state := LexerMaximalMunch.start_state dfa;
     LexerMaximalMunch.transition := LexerMaximalMunch.transition dfa;
     LexerMaximalMunch.accepting := fun state =>
       filter (Nat.eqb token) (LexerMaximalMunch.accepting dfa state) |}.

Theorem maximal_endpoint_for_one_kind_is_unique : forall dfa token input left right,
  LexerMaximalMunch.maximal_accepting_length (for_token dfa token) input left ->
  LexerMaximalMunch.maximal_accepting_length (for_token dfa token) input right ->
  left = right.
Proof. intros. eapply LexerMaximalMunch.maximal_accepting_length_unique; eauto. Qed.

(** Context is an exact interned full-stack identity, not merely the top mode.
    Logical offsets count bytes and width-one structural holes. *)
Record Position := { logical_offset : nat; mode_context : nat }.
Record Edge := { edge_from : Position; edge_token : nat; edge_to : Position }.

Inductive Path (edges : list Edge) : Position -> list nat -> Position -> Prop :=
| PathEmpty : forall position, Path edges position [] position
| PathStep : forall edge word finish,
    In edge edges -> Path edges (edge_to edge) word finish ->
    Path edges (edge_from edge) (edge_token edge :: word) finish.

Lemma path_append_edge : forall edges start word current,
  Path edges start word current -> forall edge,
  In edge edges -> edge_from edge = current ->
  Path edges start (word ++ [edge_token edge]) (edge_to edge).
Proof.
  intros edges start word current Hpath. induction Hpath; intros next Hin Hfrom.
  - cbn. rewrite <- Hfrom. econstructor; [exact Hin|constructor].
  - cbn. econstructor; [exact H|]. now apply IHHpath.
Qed.

Theorem selected_edge_scan_preserves_item_and_path :
  forall grammar edges start current item edge rest,
    RtnChart.item_sound grammar item ->
    Path edges start (RtnChart.consumed item) current ->
    In edge edges -> edge_from edge = current ->
    RtnChart.after_dot item = ImageAdmission.Scan (edge_token edge) :: rest ->
    RtnChart.item_sound grammar
      (RtnChart.advance_scan_item item (edge_token edge) rest) /\
    Path edges start
      (RtnChart.consumed (RtnChart.advance_scan_item item (edge_token edge) rest))
      (edge_to edge).
Proof.
  intros grammar edges start current item edge rest Hsound Hpath Hin Hfrom Hafter.
  split.
  - now apply RtnChart.scan_preserves_item_soundness.
  - cbn. eapply path_append_edge; eauto.
Qed.

Theorem unequal_contexts_are_distinct_positions : forall offset left right,
  left <> right ->
  {| logical_offset := offset; mode_context := left |} <>
  {| logical_offset := offset; mode_context := right |}.
Proof. intros offset left right Hneq Heq. inversion Heq. contradiction. Qed.

Lemma path_append : forall edges start left middle,
  Path edges start left middle -> forall right finish,
  Path edges middle right finish -> Path edges start (left ++ right) finish.
Proof.
  intros edges start left middle Hleft. induction Hleft; intros right destination Hright.
  - exact Hright.
  - cbn. econstructor; [exact H|]. now apply IHHleft.
Qed.

Theorem completed_child_preserves_exact_connection_context :
  forall grammar edges start middle finish waiting child nonterminal rest,
    RtnChart.item_sound grammar waiting ->
    RtnChart.after_dot waiting = ImageAdmission.Call nonterminal :: rest ->
    RtnChart.item_sound grammar child -> RtnChart.complete_item child ->
    ImageAdmission.lhs (RtnChart.item_rule child) = nonterminal ->
    Path edges start (RtnChart.consumed waiting) middle ->
    Path edges middle (RtnChart.consumed child) finish ->
    RtnChart.item_sound grammar
      (RtnChart.advance_call_item waiting nonterminal rest (RtnChart.consumed child)) /\
    Path edges start
      (RtnChart.consumed
        (RtnChart.advance_call_item waiting nonterminal rest (RtnChart.consumed child))) finish.
Proof.
  intros grammar edges start middle finish waiting child nonterminal rest
    Hwaiting Hafter Hchild Hcomplete Hlhs Hleft Hright.
  split.
  - eapply RtnChart.completion_preserves_item_soundness; eauto.
  - cbn. eapply path_append; eauto.
Qed.

(** Exact runtime mode policy: pop before push; the root cannot be popped.
    The list is top-first. A runtime interner must faithfully represent this
    whole list, including the tail that a later pop reveals. *)
Inductive ModeResult := ModeSuccess (stack : list nat) | ModeUnderflow | ModeDepth.

Definition pop_mode (pop : bool) (stack : list nat) : ModeResult :=
  if pop then
    match stack with
    | _ :: next :: rest => ModeSuccess (next :: rest)
    | _ => ModeUnderflow
    end
  else ModeSuccess stack.

Definition transition_mode (limit : nat) (pop : bool) (push : option nat)
    (stack : list nat) : ModeResult :=
  match pop_mode pop stack with
  | ModeSuccess rest =>
      match push with
      | None => ModeSuccess rest
      | Some mode =>
          if Nat.ltb (length rest) limit then ModeSuccess (mode :: rest) else ModeDepth
      end
  | failure => failure
  end.

Lemma pop_preserves_nonempty_and_does_not_grow : forall pop stack rest,
  stack <> [] -> pop_mode pop stack = ModeSuccess rest ->
  rest <> [] /\ length rest <= length stack.
Proof.
  intros pop [|top tail] rest Hnonempty Hstep; [contradiction|].
  destruct pop; cbn in Hstep.
  - destruct tail as [|next tail]; [discriminate|]. inversion Hstep; subst.
    split; [discriminate|cbn; lia].
  - inversion Hstep; subst. split; [discriminate|lia].
Qed.

Theorem successful_mode_transition_preserves_root_and_depth : forall limit pop push stack rest,
  stack <> [] -> length stack <= limit ->
  transition_mode limit pop push stack = ModeSuccess rest ->
  rest <> [] /\ length rest <= limit.
Proof.
  intros limit pop push stack rest Hnonempty Hbound Hstep.
  unfold transition_mode in Hstep.
  destruct (pop_mode pop stack) as [after| |] eqn:Hpop; try discriminate.
  destruct (pop_preserves_nonempty_and_does_not_grow pop stack after Hnonempty Hpop)
    as [Hafter Hsize].
  destruct push as [mode|].
  - destruct (Nat.ltb (length after) limit) eqn:Hdepth; [|discriminate].
    apply Nat.ltb_lt in Hdepth. inversion Hstep; subst. split; [discriminate|cbn; lia].
  - inversion Hstep; subst. split; [exact Hafter|lia].
Qed.

Theorem pushing_after_root_pop_does_not_mask_underflow : forall limit mode root,
  transition_mode limit true (Some mode) [root] = ModeUnderflow.
Proof. reflexivity. Qed.

Inductive FailureClass := StructuralFailure | ResourceFailure.
Inductive FailureDisposition := RefutedBranch | AbortRequest.

Definition classify_failure (primary : bool) (failure : FailureClass) : FailureDisposition :=
  match failure with
  | ResourceFailure => AbortRequest
  | StructuralFailure => if primary then AbortRequest else RefutedBranch
  end.

Theorem resource_exhaustion_never_refutes_a_branch : forall primary,
  classify_failure primary ResourceFailure = AbortRequest.
Proof. reflexivity. Qed.

Theorem only_secondary_structural_failure_is_refuted : forall primary failure,
  classify_failure primary failure = RefutedBranch <->
  primary = false /\ failure = StructuralFailure.
Proof. intros [] []; cbn; split; intros H; try discriminate; intuition congruence. Qed.

Theorem locally_primary_does_not_promote_secondary : forall local,
  andb false local = false.
Proof. reflexivity. Qed.

(** A successful debit reserves space/work before mutation. Exhaustion is an
    explicit failure, never an empty candidate collection. *)
Definition reserve (limit used amount : nat) : option nat :=
  if Nat.leb amount (limit - used) then Some (used + amount) else None.

Theorem successful_reservation_is_bounded : forall limit used amount next,
  used <= limit -> reserve limit used amount = Some next ->
  next = used + amount /\ next <= limit.
Proof.
  intros limit used amount next Hbound Hstep. unfold reserve in Hstep.
  destruct (Nat.leb amount (limit - used)) eqn:Hspace; [|discriminate].
  apply Nat.leb_le in Hspace. inversion Hstep; subst. split; lia.
Qed.

Theorem insufficient_reservation_is_explicit : forall limit used amount,
  used <= limit -> limit < used + amount -> reserve limit used amount = None.
Proof.
  intros limit used amount Hbound Hshort. unfold reserve.
  destruct (Nat.leb amount (limit - used)) eqn:Hspace; auto.
  apply Nat.leb_le in Hspace. lia.
Qed.

Print Assumptions loop_refines_ordered_selection.
Print Assumptions selected_entry_is_exact_and_unseen.
Print Assumptions every_unseen_kind_has_a_survivor.
Print Assumptions selected_kinds_are_unique.
Print Assumptions every_survivor_is_maximal_for_its_kind.
Print Assumptions successor_iff_surviving_endpoint.
Print Assumptions maximal_endpoint_for_one_kind_is_unique.
Print Assumptions selected_edge_scan_preserves_item_and_path.
Print Assumptions unequal_contexts_are_distinct_positions.
Print Assumptions completed_child_preserves_exact_connection_context.
Print Assumptions successful_mode_transition_preserves_root_and_depth.
Print Assumptions pushing_after_root_pop_does_not_mask_underflow.
Print Assumptions only_secondary_structural_failure_is_refuted.
Print Assumptions resource_exhaustion_never_refutes_a_branch.
Print Assumptions successful_reservation_is_bounded.
Print Assumptions insufficient_reservation_is_explicit.
