(** Source-scope resolution before construction.

    Moniker identities and named FLT holes are distinct lookup domains. The
    association-list model represents map lookup and last insertion, not a
    replacement Rust environment implementation. Identity encoding into nat
    must preserve equality; a pretty name is never a moniker identity.

    Ordered slots shift existing indices by the full width, then insert formal
    slot i at width - 1 - i. Later duplicate keys shadow earlier ones, matching
    the existing map insertion. Caller URI injections are an immutable context
    component, not lexical keys. Their enrollment and source-New interpretation
    are separate obligations, not asserted by context preservation here.

    Checked target indices reuse the existing signed-32-bit protocol check.
    Resource precharge and strict evaluation ordering before node bit-vector
    allocation still require concrete source correspondence. *)
From Stdlib Require Import List String Bool Arith Lia ZArith.
From RhoBridge Require Import RholangConstructionProtocol.
Import ListNotations.

Inductive ScopeKey := MonikerKey (identity : nat) | HoleKey (name : string).
Definition key_eqb (lhs rhs : ScopeKey) : bool :=
  match lhs, rhs with
  | MonikerKey a, MonikerKey b => Nat.eqb a b
  | HoleKey a, HoleKey b => String.eqb a b
  | _, _ => false
  end.
Lemma key_eqb_refl : forall key, key_eqb key key = true.
Proof. intros [identity|name]; cbn; [apply Nat.eqb_refl|apply String.eqb_refl]. Qed.
Lemma key_eqb_exact : forall lhs rhs, key_eqb lhs rhs = true <-> lhs = rhs.
Proof.
  intros [a|a] [b|b]; cbn; try (split; discriminate).
  - rewrite Nat.eqb_eq. split; [intro; now subst|intro H; now inversion H].
  - rewrite String.eqb_eq. split; [intro; now subst|intro H; now inversion H].
Qed.

Definition Scope := list (ScopeKey * nat).
Fixpoint lookup_scope (key : ScopeKey) (scope : Scope) : option nat :=
  match scope with
  | [] => None
  | (candidate, index) :: rest =>
    if key_eqb key candidate then Some index else lookup_scope key rest
  end.
Definition shift_scope (width : nat) (scope : Scope) : Scope :=
  map (fun entry => (fst entry, snd entry + width)) scope.
Fixpoint install_slots (slots : list ScopeKey) (scope : Scope) : Scope :=
  match slots with
  | [] => scope
  | key :: rest => install_slots rest ((key, List.length rest) :: scope)
  end.
Definition extend_scope (scope : Scope) (slots : list ScopeKey) : Scope :=
  install_slots slots (shift_scope (List.length slots) scope).

(** The final occurrence is selected, not the first pretty-name match. *)
Fixpoint assigned_index (slots : list ScopeKey) (key : ScopeKey) : option nat :=
  match slots with
  | [] => None
  | candidate :: rest => match assigned_index rest key with
    | Some index => Some index
    | None => if key_eqb key candidate then Some (List.length rest) else None
    end
  end.

Theorem shifting_preserves_lookup_exactly : forall scope key width,
  lookup_scope key (shift_scope width scope) =
  option_map (fun index => index + width) (lookup_scope key scope).
Proof.
  induction scope as [|[candidate index] rest IH]; intros; cbn; [reflexivity|].
  destruct (key_eqb key candidate); cbn; [reflexivity|exact (IH key width)].
Qed.

Theorem ordered_insertion_selects_last_slot : forall slots scope key,
  lookup_scope key (install_slots slots scope) =
  match assigned_index slots key with
  | Some index => Some index
  | None => lookup_scope key scope
  end.
Proof.
  induction slots as [|candidate rest IH]; intros; cbn; [reflexivity|].
  rewrite IH. destruct (assigned_index rest key); [reflexivity|].
  cbn. destruct (key_eqb key candidate); reflexivity.
Qed.

Theorem extension_preserves_selected_slot_or_shifted_outer_lookup : forall scope slots key,
  lookup_scope key (extend_scope scope slots) =
  match assigned_index slots key with
  | Some index => Some index
  | None => option_map (fun index => index + List.length slots) (lookup_scope key scope)
  end.
Proof.
  intros; unfold extend_scope. rewrite ordered_insertion_selects_last_slot.
  destruct (assigned_index slots key); [reflexivity|apply shifting_preserves_lookup_exactly].
Qed.

Theorem assigned_slot_is_inside_its_width : forall slots key index,
  assigned_index slots key = Some index -> index < List.length slots.
Proof.
  induction slots as [|candidate rest IH]; intros key index H; cbn in H; [discriminate|].
  destruct (assigned_index rest key) eqn:HR.
  - inversion H; subst. specialize (IH key index HR). cbn; lia.
  - destruct (key_eqb key candidate); [|discriminate]. inversion H; subst. cbn; lia.
Qed.

Theorem final_duplicate_shadows_every_earlier_slot : forall prefix key,
  assigned_index (prefix ++ [key]) key = Some 0.
Proof.
  induction prefix; intros; cbn.
  - now rewrite key_eqb_refl.
  - now rewrite IHprefix.
Qed.

Theorem surviving_outer_reference_cannot_alias_new_slots : forall scope slots key old,
  assigned_index slots key = None -> lookup_scope key scope = Some old ->
  lookup_scope key (extend_scope scope slots) = Some (old + List.length slots) /\
  List.length slots <= old + List.length slots.
Proof.
  intros. rewrite extension_preserves_selected_slot_or_shifted_outer_lookup, H, H0.
  cbn. split; [reflexivity|lia].
Qed.

Definition lexical_lookup (scope : Scope) (identity : nat) (pretty : option string) : option nat :=
  match lookup_scope (MonikerKey identity) scope with
  | Some index => Some index
  | None => match pretty with
    | Some name => lookup_scope (HoleKey name) scope
    | None => None
    end
  end.

Theorem moniker_identity_precedes_hole_name : forall scope identity pretty index,
  lookup_scope (MonikerKey identity) scope = Some index ->
  lexical_lookup scope identity pretty = Some index.
Proof. intros; unfold lexical_lookup; now rewrite H. Qed.

Theorem hole_fallback_requires_missing_moniker : forall scope identity name index,
  lookup_scope (MonikerKey identity) scope = None ->
  lexical_lookup scope identity (Some name) = Some index <->
  lookup_scope (HoleKey name) scope = Some index.
Proof. intros; unfold lexical_lookup; now rewrite H. Qed.

Inductive AdmissionMode := PublicSource | HarnessSource.
Inductive ReferenceRole := NameReference | ProcessReference.
Inductive ScopeResolution :=
| BoundReference (index : nat)
| FormulaWildcard
| UnresolvedReference (role : ReferenceRole)
| HarnessMarker (role : ReferenceRole) (name : string)
| NamelessHarnessReference
| TargetIndexRejected.

Definition resolve_free (mode : AdmissionMode) (pattern : bool) (role : ReferenceRole)
    (scope : Scope) (identity : nat) (pretty : option string) : ScopeResolution :=
  match lexical_lookup scope identity pretty with
  | Some index => if fits_target_index index then BoundReference index else TargetIndexRejected
  | None => if pattern then FormulaWildcard else
    match mode with
    | PublicSource => UnresolvedReference role
    | HarnessSource => match pretty with
      | Some name => HarnessMarker role name
      | None => NamelessHarnessReference
      end
    end
  end.

Theorem public_resolution_cannot_create_a_harness_marker :
  forall pattern role scope identity pretty marker_role name,
  resolve_free PublicSource pattern role scope identity pretty <> HarnessMarker marker_role name.
Proof.
  intros. unfold resolve_free. destruct (lexical_lookup scope identity pretty).
  - destruct (fits_target_index n); discriminate.
  - destruct pattern; discriminate.
Qed.

Theorem unresolved_public_terms_reject_by_role : forall role scope identity pretty,
  lexical_lookup scope identity pretty = None ->
  resolve_free PublicSource false role scope identity pretty = UnresolvedReference role.
Proof. intros; unfold resolve_free; now rewrite H. Qed.

Theorem unresolved_formula_variable_remains_a_wildcard : forall mode role scope identity pretty,
  lexical_lookup scope identity pretty = None ->
  resolve_free mode true role scope identity pretty = FormulaWildcard.
Proof. intros; unfold resolve_free; now rewrite H. Qed.

Theorem successful_bound_resolution_preserves_checked_index :
  forall mode pattern role scope identity pretty index,
  resolve_free mode pattern role scope identity pretty = BoundReference index ->
  lexical_lookup scope identity pretty = Some index /\
  (0 <= Z.of_nat index <= 2147483647)%Z.
Proof.
  intros mode pattern role scope identity pretty index H.
  unfold resolve_free in H. destruct (lexical_lookup scope identity pretty) eqn:HL.
  - destruct (fits_target_index n) eqn:HF; [|discriminate]. inversion H; subst.
    apply target_index_check_exact in HF. split; [reflexivity|].
    split; [apply Nat2Z.is_nonneg|exact HF].
  - destruct pattern; [discriminate|]. destruct mode; [discriminate|].
    destruct pretty; discriminate.
Qed.

Print Assumptions key_eqb_exact.
Print Assumptions shifting_preserves_lookup_exactly.
Print Assumptions ordered_insertion_selects_last_slot.
Print Assumptions extension_preserves_selected_slot_or_shifted_outer_lookup.
Print Assumptions assigned_slot_is_inside_its_width.
Print Assumptions final_duplicate_shadows_every_earlier_slot.
Print Assumptions surviving_outer_reference_cannot_alias_new_slots.
Print Assumptions moniker_identity_precedes_hole_name.
Print Assumptions hole_fallback_requires_missing_moniker.
Print Assumptions public_resolution_cannot_create_a_harness_marker.
Print Assumptions unresolved_public_terms_reject_by_role.
Print Assumptions unresolved_formula_variable_remains_a_wildcard.
Print Assumptions successful_bound_resolution_preserves_checked_index.

(** Context transport does not reconstruct options or substitute a resolver.
    The parameter types stand for unchanged caller values, not propositions
    asserting their correctness. Imports remain opaque here: transporting an
    input is not validating it or enrolling a provider capability. *)
Section ContextTransport.
Context {Options Resolver Imports : Type}.
Record SourceContext := {
  context_scope : Scope;
  context_options : Options;
  context_resolver : Resolver;
  context_imports : Imports;
  context_mode : AdmissionMode;
  context_pattern : bool
}.
Definition replace_scope (context : SourceContext) (scope : Scope) : SourceContext :=
  {| context_scope := scope;
     context_options := context_options context;
     context_resolver := context_resolver context;
     context_imports := context_imports context;
     context_mode := context_mode context;
     context_pattern := context_pattern context |}.
Definition context_inputs (context : SourceContext) :=
  (context_options context, context_resolver context, context_imports context,
   context_mode context, context_pattern context).
Theorem replacing_lexical_scope_preserves_every_context_input : forall context scope,
  context_inputs (replace_scope context scope) = context_inputs context.
Proof. reflexivity. Qed.
Theorem context_extension_uses_the_same_selected_lookup : forall context slots key,
  lookup_scope key (context_scope
    (replace_scope context (extend_scope (context_scope context) slots))) =
  match assigned_index slots key with
  | Some index => Some index
  | None => option_map (fun index => index + List.length slots)
      (lookup_scope key (context_scope context))
  end.
Proof. intros; apply extension_preserves_selected_slot_or_shifted_outer_lookup. Qed.
End ContextTransport.

(** Finite machine arithmetic is checked separately from the mathematical
    indices. The maximum is supplied by the concrete integer representation;
    it is not an assumption that input indices are in range. A successful
    result is the exact mathematical sum, never modular addition. *)
Definition checked_sum (maximum lhs rhs : nat) : option nat :=
  if lhs + rhs <=? maximum then Some (lhs + rhs) else None.
Theorem checked_sum_success_is_exact_and_bounded : forall maximum lhs rhs sum,
  checked_sum maximum lhs rhs = Some sum <-> sum = lhs + rhs /\ sum <= maximum.
Proof.
  intros. unfold checked_sum. destruct (lhs + rhs <=? maximum) eqn:H.
  - apply Nat.leb_le in H. split; [intro E; inversion E; subst; auto|intros [E _]; now subst].
  - apply Nat.leb_gt in H. split; [discriminate|intros [E Hbound]; subst; lia].
Qed.
Theorem overflowing_sum_produces_no_index : forall maximum lhs rhs,
  maximum < lhs + rhs -> checked_sum maximum lhs rhs = None.
Proof. intros; unfold checked_sum. apply Nat.leb_gt in H. now rewrite H. Qed.

Fixpoint checked_shift_scope (maximum width : nat) (scope : Scope) : option Scope :=
  match scope with
  | [] => Some []
  | (key, index) :: rest =>
    match checked_sum maximum index width with
    | None => None
    | Some shifted => match checked_shift_scope maximum width rest with
      | None => None
      | Some tail => Some ((key, shifted) :: tail)
      end
    end
  end.
Theorem checked_shift_success_is_exact_and_bounded : forall scope maximum width shifted,
  checked_shift_scope maximum width scope = Some shifted ->
  shifted = shift_scope width scope /\
  Forall (fun entry => snd entry <= maximum) shifted.
Proof.
  induction scope as [|[key index] rest IH]; intros maximum width shifted H; cbn in H.
  - inversion H; subst. split; [reflexivity|constructor].
  - destruct (checked_sum maximum index width) as [sum|] eqn:HS; [|discriminate].
    destruct (checked_shift_scope maximum width rest) as [tail|] eqn:HT; [|discriminate].
    inversion H; subst shifted. apply checked_sum_success_is_exact_and_bounded in HS.
    specialize (IH maximum width tail HT). destruct HS as [HS HB], IH as [IH HTB].
    subst sum tail. split; [reflexivity|constructor; assumption].
Qed.
Theorem checked_shift_preserves_lookup_on_success : forall scope maximum width shifted key,
  checked_shift_scope maximum width scope = Some shifted ->
  lookup_scope key shifted =
    option_map (fun index => index + width) (lookup_scope key scope).
Proof.
  intros. apply checked_shift_success_is_exact_and_bounded in H.
  destruct H as [H _]; subst. apply shifting_preserves_lookup_exactly.
Qed.

(** A residual moniker Bound node has not been opened into the lexical
    environment. Its embedded coordinates are never accepted as a target
    de-Bruijn index; rejection applies in formula and harness modes too. *)
Inductive SourceReference :=
| FreeSourceReference (identity : nat) (pretty : option string)
| UnopenedSourceReference (scope_offset binder_offset : nat).
Inductive ReferenceDecision :=
| ResolvedFree (resolution : ScopeResolution)
| UnopenedReferenceRejected (role : ReferenceRole).
Definition resolve_reference mode pattern role scope reference : ReferenceDecision :=
  match reference with
  | FreeSourceReference identity pretty =>
    ResolvedFree (resolve_free mode pattern role scope identity pretty)
  | UnopenedSourceReference _ _ => UnopenedReferenceRejected role
  end.
Theorem unopened_reference_never_becomes_a_bound_value :
  forall mode pattern role scope offset binder resolution,
  resolve_reference mode pattern role scope (UnopenedSourceReference offset binder)
    <> ResolvedFree resolution.
Proof. discriminate. Qed.

Print Assumptions replacing_lexical_scope_preserves_every_context_input.
Print Assumptions context_extension_uses_the_same_selected_lookup.
Print Assumptions checked_sum_success_is_exact_and_bounded.
Print Assumptions overflowing_sum_produces_no_index.
Print Assumptions checked_shift_success_is_exact_and_bounded.
Print Assumptions checked_shift_preserves_lookup_on_success.
Print Assumptions unopened_reference_never_becomes_a_bound_value.

(** Width counts declared slots, including unused and shadowed occurrences.
    It is not the cardinality of either lookup map. A full enclosing width is
    a machine-sized index-space bound, not an emitted signed-32-bit field. *)
Record LexicalEnvironment := {
  lexical_width : nat;
  lexical_bindings : Scope
}.
Definition empty_lexical_environment : LexicalEnvironment :=
  {| lexical_width := 0; lexical_bindings := [] |}.
Definition extend_lexical_environment (env : LexicalEnvironment) (slots : list ScopeKey)
    : LexicalEnvironment :=
  {| lexical_width := lexical_width env + List.length slots;
     lexical_bindings := extend_scope (lexical_bindings env) slots |}.
Definition selected_indices_are_in_scope (env : LexicalEnvironment) : Prop :=
  forall key index, lookup_scope key (lexical_bindings env) = Some index ->
    index < lexical_width env.

Theorem empty_environment_has_no_selected_index :
  selected_indices_are_in_scope empty_lexical_environment.
Proof. intros key index H; discriminate. Qed.

Theorem extension_preserves_every_selected_index_in_scope : forall env slots,
  selected_indices_are_in_scope env ->
  selected_indices_are_in_scope (extend_lexical_environment env slots).
Proof.
  intros env slots Hscope key index Hlookup.
  change (lookup_scope key (extend_scope (lexical_bindings env) slots) = Some index) in Hlookup.
  rewrite extension_preserves_selected_slot_or_shifted_outer_lookup in Hlookup.
  destruct (assigned_index slots key) as [assigned|] eqn:HA.
  - inversion Hlookup; subst index. apply assigned_slot_is_inside_its_width in HA.
    cbn [lexical_width extend_lexical_environment]; lia.
  - destruct (lookup_scope key (lexical_bindings env)) as [outer|] eqn:HO; [|discriminate].
    inversion Hlookup; subst index. specialize (Hscope key outer HO).
    cbn [lexical_width extend_lexical_environment]; lia.
Qed.

Definition checked_extend_environment maximum env slots : option LexicalEnvironment :=
  match checked_sum maximum (lexical_width env) (List.length slots) with
  | None => None
  | Some width =>
    match checked_shift_scope maximum (List.length slots) (lexical_bindings env) with
    | None => None
    | Some shifted => Some
      {| lexical_width := width; lexical_bindings := install_slots slots shifted |}
    end
  end.
Theorem checked_environment_extension_preserves_exact_width_and_bindings :
  forall maximum env slots extended,
  checked_extend_environment maximum env slots = Some extended ->
  extended = extend_lexical_environment env slots /\ lexical_width extended <= maximum.
Proof.
  intros maximum env slots extended H. unfold checked_extend_environment in H.
  destruct (checked_sum maximum (lexical_width env) (List.length slots)) as [width|] eqn:HW;
    [|discriminate].
  destruct (checked_shift_scope maximum (List.length slots) (lexical_bindings env))
    as [shifted|] eqn:HS; [|discriminate].
  inversion H; subst extended.
  apply checked_sum_success_is_exact_and_bounded in HW.
  apply checked_shift_success_is_exact_and_bounded in HS.
  destruct HW as [HW HB], HS as [HS _]. subst width shifted.
  split; [reflexivity|exact HB].
Qed.

Inductive ReachableLexicalEnvironment (maximum : nat) : LexicalEnvironment -> Prop :=
| LexicalRoot : ReachableLexicalEnvironment maximum empty_lexical_environment
| LexicalExtension : forall env slots extended,
    ReachableLexicalEnvironment maximum env ->
    checked_extend_environment maximum env slots = Some extended ->
    ReachableLexicalEnvironment maximum extended.

Theorem reachable_environment_lookup_is_in_scope : forall maximum env,
  ReachableLexicalEnvironment maximum env -> selected_indices_are_in_scope env.
Proof.
  intros maximum env H. induction H.
  - apply empty_environment_has_no_selected_index.
  - apply checked_environment_extension_preserves_exact_width_and_bindings in H0.
    destruct H0 as [H0 _]. subst.
    now apply extension_preserves_every_selected_index_in_scope.
Qed.

Theorem reachable_enclosing_hole_fallback_is_in_scope : forall maximum env identity pretty index,
  ReachableLexicalEnvironment maximum env ->
  lexical_lookup (lexical_bindings env) identity pretty = Some index ->
  index < lexical_width env.
Proof.
  intros maximum env identity pretty index Hreachable Hlookup.
  pose proof (reachable_environment_lookup_is_in_scope _ _ Hreachable) as Hscope.
  unfold lexical_lookup in Hlookup.
  destruct (lookup_scope (MonikerKey identity) (lexical_bindings env)) eqn:HM.
  - inversion Hlookup; subst. now apply (Hscope (MonikerKey identity)).
  - destruct pretty as [name|]; [now apply (Hscope (HoleKey name))|discriminate].
Qed.

Theorem adding_unused_slots_still_increases_width : forall env slots,
  lexical_width (extend_lexical_environment env slots) =
  lexical_width env + List.length slots.
Proof. reflexivity. Qed.

Example repeated_named_slots_do_not_shrink_the_scope : forall name,
  let env := extend_lexical_environment empty_lexical_environment [HoleKey name; HoleKey name] in
  lexical_width env = 2 /\ lookup_scope (HoleKey name) (lexical_bindings env) = Some 0.
Proof. intros. cbn. rewrite String.eqb_refl. auto. Qed.

Print Assumptions empty_environment_has_no_selected_index.
Print Assumptions extension_preserves_every_selected_index_in_scope.
Print Assumptions checked_environment_extension_preserves_exact_width_and_bindings.
Print Assumptions reachable_environment_lookup_is_in_scope.
Print Assumptions reachable_enclosing_hole_fallback_is_in_scope.
Print Assumptions adding_unused_slots_still_increases_width.
Print Assumptions repeated_named_slots_do_not_shrink_the_scope.
