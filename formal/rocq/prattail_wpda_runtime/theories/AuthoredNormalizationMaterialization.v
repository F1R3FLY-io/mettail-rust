(** Private owned materialization of the ORIGINAL legacy normalizer's outputs.

    Intended Rust boundary: prattail/wpda_rule_analysis/authored_normalization.rs.
    A session consumes an already validated AuthoredRuleStore once, remembers
    original_len, and exposes no mutable store. Only original Rule IDs may be
    normalized. The existing try_normalize_legacy_rule_with runs exactly once;
    its admitted constructors produce fixed shallow recipes with String names.
    No arena mutation occurs inside these infallible recipe constructors.

    Fresh strings are formatted at the ORIGINAL FreshName/ElemsName callbacks,
    not reparsed or formatted during arena traversal. Original Name IDs remain
    unchanged. After Some recipes only, a lazy name index checks the concrete
    source-profile relation spelling iff equality class. This is NOT a generic
    AuthoredRuleStore invariant: arbitrary stores may distinguish those facts.
    Locked proc-macro2 1.0.107 wrapper.rs719--727 and fallback.rs890--915 justify
    this relation for same-backend Ident values (including raw r# spelling);
    the schema producer uses original String equality. Mixed proc-macro backends
    are not a comparison domain of the original implementation.

    The index below is an ordered mathematical map model, not a proposed linear
    runtime lookup. Rust uses spelling->class and class->representative NameId.
    Hits reuse the representative NameId; misses preserve all old class numbers
    and append max+1, with the existing u32 check. Existing MAX-class hits remain
    legal. This proves derived name observation/equality, NOT identical derived
    occurrence IDs or byte identity with a separately recaptured AST arena.

    Fixed constructor batches below use the EXISTING node vocabulary and checked
    append loop. No recursive AST, new normalizer, or source reconstruction is
    introduced. Mathematical batch lists describe finite append executions;
    runtime gates receive borrowed recipes/counts before payload copies, vector
    growth, indexing, formatting and append capacity reservation. No runtime
    preflight plan vector is required. Explicit admission/reservation booleans
    are results of those checks, not an allocator or arbitrary callback proof.

    A failed consuming call returns no session; successful handles become visible
    only after Params, Syntax and the new Rule are present. The original prefix,
    header and associated external rule metadata are immutable. Capacity/copy
    admission for any one initial clone by a borrowed-Core caller is external;
    no clone occurs inside the session and never one clone per rule.
*)
From Stdlib Require Import List String Bool Arith Lia Numbers.DecimalString.
From PrattailWpdaRuntime Require Import LegacyRuleNormalizationProjection
  LegacyNormalizationAdmission AuthoredRuleStoreProjection AuthoredRuleCaptureProjection.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

Module AuthoredNormalizationMaterialization.
Module L := LegacyRuleNormalizationProjection.LegacyRuleNormalizationProjection.
Module I := LegacyNormalizationAdmission.LegacyNormalizationAdmission.
Module A := AuthoredRuleStoreProjection.AuthoredRuleStoreProjection.
Module C := AuthoredRuleCaptureProjection.AuthoredRuleCaptureProjection.

Definition fresh_spelling index :=
  String.append "p" (NilZero.string_of_uint (Nat.to_uint index)).
Definition generated_spelling name := match name with
| L.OriginalName ident => L.ident_text ident
| L.PName index => fresh_spelling index
| L.ElemsName => "elems"%string end.
Example original_generated_spelling_is_not_raw :
  fresh_spelling 0 = "p0"%string /\ fresh_spelling 12 = "p12"%string /\
  generated_spelling L.ElemsName = "elems"%string /\
  fresh_spelling 0 <> "r#p0"%string.
Proof. vm_compute; repeat split; try reflexivity; discriminate. Qed.

Record NameEntry := { payload : A.NamePayload; representative : A.Handle A.NameTag }.
Definition text entry := A.spelling (payload entry).
Definition class entry := A.equality_class (payload entry).
Fixpoint by_text spelling entries := match entries with
| [] => None
| entry :: rest => if String.eqb spelling (text entry) then Some entry else by_text spelling rest end.
Fixpoint by_class number entries := match entries with
| [] => None
| entry :: rest => if Nat.eqb number (class entry) then Some entry else by_class number rest end.
Definition Profile entries := forall lhs rhs,
  In lhs entries -> In rhs entries -> (text lhs = text rhs <-> class lhs = class rhs).
Definition IndexReads arena entries := forall entry, In entry entries ->
  A.name_payload arena (representative entry) = Some (payload entry).

Definition insert_original entry entries := match by_text (text entry) entries with
| Some old => if Nat.eqb (class entry) (class old) then Some entries else None
| None => match by_class (class entry) entries with
    | Some _ => None | None => Some (entries ++ [entry]) end end.
Fixpoint index_names position arena entries := match arena with
| [] => Some entries
| A.NameNode name :: rest =>
    match insert_original {| payload := name; representative := A.Ref position |} entries with
    | None => None | Some next => index_names (S position) rest next end
| _ :: rest => index_names (S position) rest entries end.

Lemma by_text_sound : forall entries spelling found,
  by_text spelling entries = Some found -> In found entries /\ text found = spelling.
Proof.
  induction entries as [|entry rest IH]; intros spelling found H; cbn in H; [discriminate|].
  destruct (String.eqb spelling (text entry)) eqn:E.
  - apply String.eqb_eq in E; inversion H; subst; split; [left; reflexivity|reflexivity].
  - apply IH in H; destruct H; split; [right; assumption|assumption].
Qed.
Lemma by_text_absent : forall entries spelling entry,
  by_text spelling entries = None -> In entry entries -> text entry <> spelling.
Proof.
  induction entries as [|first rest IH]; intros spelling entry H Member; [contradiction|].
  cbn in H; destruct (String.eqb spelling (text first)) eqn:E; [discriminate|].
  destruct Member as [<-|Member].
  - apply String.eqb_neq in E; congruence.
  - eapply IH; eauto.
Qed.
Lemma by_class_absent : forall entries number entry,
  by_class number entries = None -> In entry entries -> class entry <> number.
Proof.
  induction entries as [|first rest IH]; intros number entry H Member; [contradiction|].
  cbn in H; destruct (Nat.eqb number (class first)) eqn:E; [discriminate|].
  destruct Member as [<-|Member].
  - apply Nat.eqb_neq in E; congruence.
  - eapply IH; eauto.
Qed.
Theorem source_index_insertion_never_renumbers : forall entry entries next,
  insert_original entry entries = Some next -> next = entries \/ next = entries ++ [entry].
Proof.
  intros; unfold insert_original in H; destruct (by_text (text entry) entries) as [old|].
  - destruct (Nat.eqb (class entry) (class old)); inversion H; auto.
  - destruct (by_class (class entry) entries); inversion H; auto.
Qed.
Theorem source_index_checks_the_concrete_profile : forall entries entry next,
  Profile entries -> insert_original entry entries = Some next -> Profile next.
Proof.
  intros entries entry next P H; unfold insert_original in H.
  destruct (by_text (text entry) entries) as [old|] eqn:T.
  - destruct (Nat.eqb (class entry) (class old)); inversion H; subst; exact P.
  - destruct (by_class (class entry) entries) as [old|] eqn:K; [discriminate|].
    inversion H; subst next. intros lhs rhs Left Right.
    apply in_app_or in Left; apply in_app_or in Right.
    destruct Left as [Left|[<-|[]]]; destruct Right as [Right|[<-|[]]].
    + apply P; assumption.
    + pose proof (@by_text_absent entries (text entry) lhs T Left).
      pose proof (@by_class_absent entries (class entry) lhs K Left). tauto.
    + pose proof (@by_text_absent entries (text entry) rhs T Right).
      pose proof (@by_class_absent entries (class entry) rhs K Right). split; congruence.
    + tauto.
Qed.
Theorem checked_name_index_establishes_profile : forall arena position entries result,
  Profile entries -> index_names position arena entries = Some result -> Profile result.
Proof.
  induction arena as [|node rest IH]; intros position entries result P H; cbn in H.
  - inversion H; subst; exact P.
  - destruct node; try solve [eapply IH; eauto].
    destruct (insert_original {| payload := name; representative := A.Ref position |} entries)
      as [next|] eqn:E; [|discriminate].
    eapply IH; [eapply source_index_checks_the_concrete_profile; eauto|exact H].
Qed.

Definition EntryFrom position nodes entry := exists offset,
  nth_error nodes offset = Some (A.NameNode (payload entry)) /\
  A.index (representative entry) = position + offset.
Lemma entry_from_tail : forall position node nodes entry,
  EntryFrom (S position) nodes entry -> EntryFrom position (node :: nodes) entry.
Proof.
  intros position node nodes entry [offset [Found Position]].
  exists (S offset); split; [exact Found|lia].
Qed.
Lemma index_names_retains_actual_occurrence : forall nodes position entries result entry,
  index_names position nodes entries = Some result -> In entry result ->
  In entry entries \/ EntryFrom position nodes entry.
Proof.
  induction nodes as [|node rest IH]; intros position entries result entry H Member.
  - cbn in H; inversion H; subst; left; exact Member.
  - destruct node as [name|ns|ty|param|params|syntax|operation|rule]; cbn in H;
      try solve [destruct (IH _ _ _ _ H Member) as [Old|Tail];
        [left; exact Old|right; apply entry_from_tail; exact Tail]].
    + destruct (insert_original {| payload := name; representative := A.Ref position |} entries)
        as [next|] eqn:Insert; [|discriminate].
      destruct (IH _ _ _ _ H Member) as [Old|Tail].
      * apply source_index_insertion_never_renumbers in Insert.
        destruct Insert as [Same|Extended]; subst next.
        -- left; exact Old.
        -- apply in_app_or in Old; destruct Old as [Old|[<-|[]]].
           ++ left; exact Old.
           ++ right; exists 0; split; [reflexivity|cbn; lia].
      * right; apply entry_from_tail; exact Tail.
Qed.
Theorem successful_lazy_index_establishes_concrete_name_reads : forall nodes entries,
  index_names 0 nodes [] = Some entries -> IndexReads nodes entries.
Proof.
  intros nodes entries H entry Member.
  destruct (@index_names_retains_actual_occurrence nodes 0 [] entries entry H Member)
    as [Impossible|[offset [Found Position]]]; [contradiction|].
  unfold A.name_payload; cbn in Position; rewrite Position, Found; reflexivity.
Qed.

(** Rust's stored classes are u32 independently of node-index validation. This
    premise is explicit: the older store model intentionally used nat payloads. *)
Definition ClassesFit entries := forall entry, In entry entries -> A.index_fits_u32 (class entry) = true.
Definition SourceClassesFit nodes := forall position name,
  nth_error nodes position = Some (A.NameNode name) -> A.index_fits_u32 (A.equality_class name) = true.
Theorem index_retains_source_class_width_without_inventing_it : forall nodes entries,
  SourceClassesFit nodes -> index_names 0 nodes [] = Some entries -> ClassesFit entries.
Proof.
  intros nodes entries Width Checked entry Member.
  destruct (@index_names_retains_actual_occurrence nodes 0 [] entries entry Checked Member)
    as [Impossible|[offset [Found Position]]]; [contradiction|].
  unfold class; eapply Width; exact Found.
Qed.

Fixpoint greatest_class entries := match entries with
| [] => 0 | entry :: rest => Nat.max (class entry) (greatest_class rest) end.
Definition next_class entries := match entries with [] => 0 | _ => S (greatest_class entries) end.
Lemma member_class_at_most_greatest : forall entries entry,
  In entry entries -> class entry <= greatest_class entries.
Proof. induction entries; intros entry H; [contradiction|]. cbn; destruct H as [<-|H]; [lia|specialize (IHentries _ H); lia]. Qed.
Theorem fresh_class_is_distinct_without_renumbering : forall entries entry,
  In entry entries -> class entry < next_class entries.
Proof.
  intros entries entry H; pose proof (@member_class_at_most_greatest entries entry H).
  destruct entries; [contradiction|]. cbn [next_class]; lia.
Qed.
Lemma by_class_sound : forall entries number found,
  by_class number entries = Some found -> In found entries /\ class found = number.
Proof.
  induction entries as [|entry rest IH]; intros number found H; cbn in H; [discriminate|].
  destruct (Nat.eqb number (class entry)) eqn:E.
  - apply Nat.eqb_eq in E; inversion H; subst; split; [left; reflexivity|reflexivity].
  - apply IH in H; destruct H; split; [right; assumption|assumption].
Qed.
Lemma fresh_class_lookup_is_absent : forall entries,
  by_class (next_class entries) entries = None.
Proof.
  intros entries; destruct (by_class (next_class entries) entries) as [entry|] eqn:E; [|reflexivity].
  apply by_class_sound in E; destruct E as [Member Number].
  pose proof (@fresh_class_is_distinct_without_renumbering entries entry Member); lia.
Qed.

Record State := { arena : list A.Node; names : list NameEntry }.
Definition state nodes entries := {| arena := nodes; names := entries |}.
(** Admission covers actual formatting/copies/index insertion; reservation covers
    one new arena slot and both map entries. A hit does neither new allocation. *)
Definition enroll (admit : string -> nat -> bool) (reserved : bool) spelling st :=
  match by_text spelling (names st) with
  | Some entry => Some (st, representative entry)
  | None => let number := next_class (names st) in
      if admit spelling number && reserved && A.index_fits_u32 number then
        let name := {| A.spelling := spelling; A.equality_class := number |} in
        match A.append_checked (arena st) (A.NameNode name) with
        | None => None
        | Some nodes =>
            let id := A.Ref (List.length (arena st)) in
            let entry := {| payload := name; representative := id |} in
            Some (state nodes (names st ++ [entry]), id)
        end
      else None
  end.
Theorem generated_name_hit_reuses_existing_representative_even_at_max :
  forall admit reserved spelling st entry,
  by_text spelling (names st) = Some entry ->
  enroll admit reserved spelling st = Some (st, representative entry).
Proof. intros; unfold enroll; now rewrite H. Qed.
Theorem generated_name_hit_preserves_exact_read : forall (admit : string -> nat -> bool) (reserved : bool) spelling st entry,
  IndexReads (arena st) (names st) -> by_text spelling (names st) = Some entry ->
  A.name_payload (arena st) (representative entry) = Some (payload entry) /\ text entry = spelling.
Proof.
  intros; apply by_text_sound in H0; destruct H0; split; [apply H; assumption|assumption].
Qed.
Theorem missing_generated_class_refuses_only_when_extension_is_needed : forall admit reserved spelling st,
  by_text spelling (names st) = None -> A.index_fits_u32 (next_class (names st)) = false ->
  enroll admit reserved spelling st = None.
Proof. intros; unfold enroll; rewrite H, H0, andb_false_r; reflexivity. Qed.
Theorem denied_generated_name_has_no_append : forall admit reserved spelling st,
  by_text spelling (names st) = None -> admit spelling (next_class (names st)) = false ->
  enroll admit reserved spelling st = None.
Proof. intros; unfold enroll; rewrite H, H0; reflexivity. Qed.
Theorem generated_extension_keeps_original_nodes_and_numbers : forall admit reserved spelling before after id,
  enroll admit reserved spelling before = Some (after, id) ->
  (after = before /\ exists entry, by_text spelling (names before) = Some entry /\ id = representative entry) \/
  exists name, arena after = arena before ++ [A.NameNode name] /\
    A.spelling name = spelling /\ A.equality_class name = next_class (names before) /\
    names after = names before ++ [{| payload := name; representative := id |}] /\
    A.index id = List.length (arena before).
Proof.
  intros admit reserved spelling before after id H; unfold enroll in H.
  destruct (by_text spelling (names before)) as [entry|] eqn:E.
  - inversion H; subst. left; split; [reflexivity|]. exists entry; auto.
  - destruct (admit spelling (next_class (names before)) && reserved &&
      A.index_fits_u32 (next_class (names before))) eqn:G; [|discriminate].
    destruct (A.append_checked (arena before)
      (A.NameNode {| A.spelling := spelling; A.equality_class := next_class (names before) |}))
      as [nodes|] eqn:Append; [|discriminate].
    apply A.append_checked_exact in Append; destruct Append as [Nodes _].
    inversion H; subst. right; eexists; repeat split; eauto.
Qed.

Theorem generated_enrollment_preserves_profile_reads_width_and_exact_spelling :
  forall admit reserved spelling before after id,
  Profile (names before) -> IndexReads (arena before) (names before) -> ClassesFit (names before) ->
  enroll admit reserved spelling before = Some (after, id) ->
  Profile (names after) /\ IndexReads (arena after) (names after) /\ ClassesFit (names after) /\
  exists name, A.name_payload (arena after) id = Some name /\ A.spelling name = spelling.
Proof.
  intros admit reserved spelling before after id ProfileBefore Reads Width H; unfold enroll in H.
  destruct (by_text spelling (names before)) as [entry|] eqn:Text.
  - inversion H; subst. apply by_text_sound in Text; destruct Text as [Member Spelling].
    split; [exact ProfileBefore|]. split; [exact Reads|]. split; [exact Width|].
    exists (payload entry); split; [apply Reads; exact Member|exact Spelling].
  - destruct (admit spelling (next_class (names before)) && reserved &&
      A.index_fits_u32 (next_class (names before))) eqn:Gate; [|discriminate].
    apply andb_true_iff in Gate; destruct Gate as [_ Fits].
    set (name := {| A.spelling := spelling; A.equality_class := next_class (names before) |}) in *.
    destruct (A.append_checked (arena before) (A.NameNode name)) as [nodes|] eqn:Append; [|discriminate].
    apply A.append_checked_exact in Append; destruct Append as [Nodes _].
    inversion H; subst after id nodes; cbn [state arena names].
    assert (ReadNew : A.name_payload (arena before ++ [A.NameNode name])
        (A.Ref (List.length (arena before))) = Some name).
    { unfold A.name_payload; cbn [A.index]. rewrite nth_error_app2 by lia.
      rewrite Nat.sub_diag; reflexivity. }
    split.
    + eapply (@source_index_checks_the_concrete_profile (names before)
        {| payload := name; representative := A.Ref (List.length (arena before)) |});
        [exact ProfileBefore|].
      unfold insert_original; change
        (match by_text spelling (names before) with
        | Some old => if Nat.eqb (next_class (names before)) (class old) then Some (names before) else None
        | None => match by_class (next_class (names before)) (names before) with
          | Some _ => None | None => Some (names before ++
            [{| payload := name; representative := A.Ref (List.length (arena before)) |}]) end end =
          Some (names before ++ [{| payload := name; representative := A.Ref (List.length (arena before)) |}])).
      rewrite Text, fresh_class_lookup_is_absent; reflexivity.
    + split.
      * intros known Member; apply in_app_or in Member; destruct Member as [Old|[<-|[]]].
        -- specialize (Reads known Old). unfold A.name_payload in *.
           destruct (nth_error (arena before) (A.index (representative known))) as [node|] eqn:E; [|discriminate].
           rewrite (@A.lookup_append_stable _ _ _ _ E); exact Reads.
        -- exact ReadNew.
      * split.
        -- intros known Member; apply in_app_or in Member; destruct Member as [Old|[<-|[]]].
           ++ apply Width; exact Old.
           ++ exact Fits.
        -- exists name; split; [exact ReadNew|reflexivity].
Qed.

(** NameLookup is paid even on a hit; enrollment's miss-only admission pays the
    new index entry/key copy and append. These are separate original-site gates.
    Likewise VisitNameNode and index-entry reservations are paid by the caller
    while executing the concrete index_names fold, not by a second name scan. *)
Definition enroll_after_lookup (lookup_paid : bool) admit reserved spelling st :=
  if lookup_paid then enroll admit reserved spelling st else None.
Theorem unpaid_lookup_cannot_probe_or_extend_names : forall admit reserved spelling st,
  enroll_after_lookup false admit reserved spelling st = None.
Proof. reflexivity. Qed.
Theorem admitted_lookup_reuses_exact_enrollment : forall admit reserved spelling st,
  enroll_after_lookup true admit reserved spelling st = enroll admit reserved spelling st.
Proof. reflexivity. Qed.

(** Only these fixed shallow recipes are constructed. Original category handles
    are not rendered then re-resolved. Strings are the already generated names. *)
Inductive ParamRecipe :=
| SimpleRecipe (name : string) (category : A.Handle A.NameTag)
| AbstractionRecipe (binder body : string) (domain codomain : A.Handle A.NameTag)
| CollectionRecipe (name : string) (kind : L.S.CollectionKind) (element : A.Handle A.NameTag).
Inductive SyntaxRecipe := LiteralRecipe (text : string) | ParamRecipeRef (name : string)
| SepRecipe (name separator : string).
Definition kind_code kind := match kind with
| L.S.ListKind => 0 | L.S.BagKind => 1 | L.S.MapKind => 2
| L.S.SetKind => 3 | L.S.PathmapKind => 4 end.

(** Projection used only to state source correspondence, not a Rust post-walk. *)
Definition project_param (original : L.OriginalIdent -> A.Handle A.NameTag) p := match p with
| L.Simple name (L.Base category) => Some (SimpleRecipe (generated_spelling name) (original category))
| L.Abstraction binder body (L.Arrow (L.Base domain) (L.Base codomain)) =>
    Some (AbstractionRecipe (generated_spelling binder) (generated_spelling body)
      (original domain) (original codomain))
| L.Simple name (L.Collection kind (L.Base element)) =>
    Some (CollectionRecipe (generated_spelling name) kind (original element))
| _ => None end.
Definition project_syntax syntax := match syntax with
| L.Literal text => Some (LiteralRecipe text)
| L.ParamRef name => Some (ParamRecipeRef (generated_spelling name))
| L.Sep name separator None => Some (SepRecipe (generated_spelling name) separator)
| _ => None end.
Theorem original_param_constructors_project_to_exact_recipes : forall original name binder body category domain kind,
  project_param original (L.make_simple L.original_constructors name category) =
    Some (SimpleRecipe (generated_spelling name) (original category)) /\
  project_param original (L.make_abstraction L.original_constructors binder body domain category) =
    Some (AbstractionRecipe (generated_spelling binder) (generated_spelling body) (original domain) (original category)) /\
  project_param original (L.make_collection L.original_constructors name kind category) =
    Some (CollectionRecipe (generated_spelling name) kind (original category)).
Proof. repeat split; reflexivity. Qed.
Theorem original_syntax_constructors_project_to_exact_recipes : forall name text,
  project_syntax (L.make_literal L.original_constructors text) = Some (LiteralRecipe text) /\
  project_syntax (L.make_param L.original_constructors name) = Some (ParamRecipeRef (generated_spelling name)) /\
  project_syntax (L.make_sep L.original_constructors name text) = Some (SepRecipe (generated_spelling name) text).
Proof. repeat split; reflexivity. Qed.

(** Resolved names are obtained only by enroll above. Each batch is the exact
    field construction of the original constructor, in child-before-owner order. *)
Inductive ResolvedParam :=
| ResolvedSimple (name category : A.Handle A.NameTag)
| ResolvedAbstraction (binder body domain codomain : A.Handle A.NameTag)
| ResolvedCollection (name : A.Handle A.NameTag) (kind : L.S.CollectionKind) (element : A.Handle A.NameTag).
Definition parameter_batch start recipe := match recipe with
| ResolvedSimple name category =>
    [A.TypeNode (A.Base category); A.ParamNode (A.Simple name (A.Ref start))]
| ResolvedAbstraction binder body domain codomain =>
    [A.TypeNode (A.Base domain); A.TypeNode (A.Base codomain);
     A.TypeNode (A.Arrow (A.Ref start) (A.Ref (start + 1)));
     A.ParamNode (A.Abstraction binder body (A.Ref (start + 2)))]
| ResolvedCollection name kind element =>
    [A.TypeNode (A.Base element); A.TypeNode (A.Collection (kind_code kind) (A.Ref start));
     A.ParamNode (A.Simple name (A.Ref (start + 1)))] end.
Definition parameter_offset recipe := match recipe with
| ResolvedSimple _ _ => 1 | ResolvedAbstraction _ _ _ _ => 3 | ResolvedCollection _ _ _ => 2 end.
Definition parameter_handle start recipe : A.Handle A.ParamTag := A.Ref (start + parameter_offset recipe).
Definition parameter_payload start recipe := match recipe with
| ResolvedSimple name _ => A.Simple name (A.Ref start)
| ResolvedAbstraction binder body _ _ => A.Abstraction binder body (A.Ref (start + 2))
| ResolvedCollection name _ _ => A.Simple name (A.Ref (start + 1)) end.
Theorem fixed_parameter_batch_lengths : forall start recipe,
  List.length (parameter_batch start recipe) = S (parameter_offset recipe).
Proof. intros start []; reflexivity. Qed.
Theorem fixed_parameter_batch_has_exact_final_payload : forall start recipe,
  nth_error (parameter_batch start recipe) (parameter_offset recipe) = Some (A.ParamNode (parameter_payload start recipe)).
Proof. intros start []; reflexivity. Qed.

Definition append_paid (admitted reserved : bool) prefix nodes :=
  if admitted && reserved then A.validate_into prefix nodes else None.
Theorem unpaid_or_unreserved_batch_returns_no_store : forall admitted reserved prefix nodes,
  admitted = false \/ reserved = false -> append_paid admitted reserved prefix nodes = None.
Proof. intros [] [] prefix nodes H; cbn; try reflexivity; destruct H; discriminate. Qed.
Theorem paid_batch_is_exact_existing_checked_append : forall admitted reserved prefix nodes result,
  append_paid admitted reserved prefix nodes = Some result ->
  admitted = true /\ reserved = true /\ result = prefix ++ nodes.
Proof.
  intros [] [] prefix nodes result H; try discriminate.
  repeat split; try reflexivity. eapply A.validation_retains_exact_nodes; exact H.
Qed.
Theorem paid_batch_preserves_prior_typed_handles : forall admitted reserved prefix nodes result position node,
  append_paid admitted reserved prefix nodes = Some result -> nth_error prefix position = Some node ->
  nth_error result position = Some node.
Proof.
  intros; apply paid_batch_is_exact_existing_checked_append in H; destruct H as [_ [_ ->]].
  apply A.lookup_append_stable; exact H0.
Qed.
Theorem paid_batch_preserves_existing_store_validation : forall admitted reserved prefix nodes result,
  A.ValidArena prefix -> append_paid admitted reserved prefix nodes = Some result -> A.ValidArena result.
Proof.
  intros [] [] prefix nodes result V H; try discriminate.
  eapply A.validation_establishes_validity; eauto.
Qed.
Lemma batch_position : forall (prefix nodes : list A.Node) offset node,
  nth_error nodes offset = Some node -> nth_error (prefix ++ nodes) (List.length prefix + offset) = Some node.
Proof. intros; rewrite nth_error_app2 by lia; replace (List.length prefix + offset - List.length prefix) with offset by lia; assumption. Qed.
Theorem parameter_materialization_is_read_by_existing_reader : forall admitted reserved prefix recipe result,
  append_paid admitted reserved prefix (parameter_batch (List.length prefix) recipe) = Some result ->
  A.parameter result (parameter_handle (List.length prefix) recipe) =
    Some (A.read_param (parameter_payload (List.length prefix) recipe)).
Proof.
  intros; apply paid_batch_is_exact_existing_checked_append in H; destruct H as [_ [_ ->]].
  unfold A.parameter, parameter_handle; cbn [A.index].
  rewrite batch_position with (node := A.ParamNode (parameter_payload (List.length prefix) recipe));
    [reflexivity|apply fixed_parameter_batch_has_exact_final_payload].
Qed.
Theorem abstraction_batch_keeps_both_original_category_handles : forall start binder body domain codomain,
  parameter_batch start (ResolvedAbstraction binder body domain codomain) =
    [A.TypeNode (A.Base domain); A.TypeNode (A.Base codomain);
     A.TypeNode (A.Arrow (A.Ref start) (A.Ref (start + 1)));
     A.ParamNode (A.Abstraction binder body (A.Ref (start + 2)))] /\
  A.read_arrow (A.Arrow (A.Ref start) (A.Ref (start + 1))) = Some (start, start + 1).
Proof. split; reflexivity. Qed.
Theorem collection_batch_is_original_collection_not_map_type : forall start name kind element,
  nth_error (parameter_batch start (ResolvedCollection name kind element)) 1 =
    Some (A.TypeNode (A.Collection (kind_code kind) (A.Ref start))).
Proof. reflexivity. Qed.

Inductive ResolvedSyntax := ResolvedLiteral (text : string)
| ResolvedParamRef (name : A.Handle A.NameTag)
| ResolvedSep (name : A.Handle A.NameTag) (separator : string).
Definition syntax_batch recipe := match recipe with
| ResolvedSep name separator => [A.OperationNode (A.Sep name separator None)] | _ => [] end.
Definition syntax_payload start recipe := match recipe with
| ResolvedLiteral text => A.Literal text
| ResolvedParamRef name => A.ParamRef name
| ResolvedSep _ _ => A.OperationRef (A.Ref start) end.
Theorem separator_materializes_original_source_none : forall admitted reserved prefix name separator result,
  append_paid admitted reserved prefix (syntax_batch (ResolvedSep name separator)) = Some result ->
  A.operation result (A.Ref (List.length prefix)) = Some (A.B.Sep (A.index name) separator None).
Proof.
  intros; apply paid_batch_is_exact_existing_checked_append in H; destruct H as [_ [_ ->]].
  unfold A.operation; cbn [A.index].
  replace (List.length prefix) with (List.length prefix + 0) at 1 by lia.
  rewrite batch_position with (node := A.OperationNode (A.Sep name separator None)); reflexivity.
Qed.
Theorem literal_and_parameter_syntax_need_no_operation_node : forall text name start,
  syntax_batch (ResolvedLiteral text) = [] /\ syntax_batch (ResolvedParamRef name) = [] /\
  syntax_payload start (ResolvedLiteral text) = A.Literal text /\
  syntax_payload start (ResolvedParamRef name) = A.ParamRef name.
Proof. repeat split; reflexivity. Qed.

(** Final commit uses one new Rule node, never a partially edited original. *)
Definition replacement original params syntax : A.RulePayload :=
  {| A.label := A.label original; A.category := A.category original;
     A.term_context := Some params; A.syntax_pattern := Some syntax;
     A.legacy_items := A.legacy_items original |}.
Definition commit_batch start original params syntax :=
  [A.ParamsNode params; A.SyntaxNode syntax;
   A.RuleNode (replacement original (A.Ref start) (A.Ref (start + 1)))].
Definition commit_handle start : A.Handle A.RuleTag := A.Ref (start + 2).
Theorem replacement_preserves_every_retained_original_field : forall original params syntax,
  A.label (replacement original params syntax) = A.label original /\
  A.category (replacement original params syntax) = A.category original /\
  A.legacy_items (replacement original params syntax) = A.legacy_items original /\
  A.term_context (replacement original params syntax) = Some params /\
  A.syntax_pattern (replacement original params syntax) = Some syntax.
Proof. repeat split; reflexivity. Qed.
Theorem successful_commit_has_both_sequences_before_rule : forall admitted reserved prefix original params syntax result,
  append_paid admitted reserved prefix (commit_batch (List.length prefix) original params syntax) = Some result ->
  nth_error result (List.length prefix) = Some (A.ParamsNode params) /\
  nth_error result (List.length prefix + 1) = Some (A.SyntaxNode syntax) /\
  nth_error result (List.length prefix + 2) =
    Some (A.RuleNode (replacement original (A.Ref (List.length prefix)) (A.Ref (List.length prefix + 1)))).
Proof.
  intros; apply paid_batch_is_exact_existing_checked_append in H; destruct H as [_ [_ ->]].
  split.
  - rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity.
  - split; apply batch_position; reflexivity.
Qed.
Theorem successful_commit_exposes_exact_existing_rule_reader : forall admitted reserved prefix original params syntax result,
  append_paid admitted reserved prefix (commit_batch (List.length prefix) original params syntax) = Some result ->
  A.authored_rule result (commit_handle (List.length prefix)) =
    Some (A.read_rule (replacement original (A.Ref (List.length prefix)) (A.Ref (List.length prefix + 1))),
      map A.read_legacy (A.legacy_items original)).
Proof.
  intros; pose proof (@successful_commit_has_both_sequences_before_rule _ _ _ _ _ _ _ H) as [_ [_ Found]].
  unfold A.authored_rule, commit_handle; cbn [A.index]; rewrite Found; reflexivity.
Qed.

Record Session := { private_store : list A.Node; original_len : nat; name_index : option (list NameEntry) }.
Definition consume nodes := {| private_store := nodes; original_len := List.length nodes; name_index := None |}.
Definition original_rule session (id : A.Handle A.RuleTag) :=
  if Nat.ltb (A.index id) (original_len session) then
    match nth_error (private_store session) (A.index id) with
    | Some (A.RuleNode rule) => Some rule | _ => None end else None.
Theorem session_consumes_store_without_copy_or_index : forall nodes,
  private_store (consume nodes) = nodes /\ original_len (consume nodes) = List.length nodes /\
  name_index (consume nodes) = None.
Proof. repeat split; reflexivity. Qed.
Theorem appended_rule_cannot_be_readmitted_as_original : forall session id,
  original_len session <= A.index id -> original_rule session id = None.
Proof.
  intros; unfold original_rule. assert (E : Nat.ltb (A.index id) (original_len session) = false)
    by (apply Nat.ltb_ge; exact H). rewrite E; reflexivity.
Qed.
Theorem accepted_original_handle_has_the_actual_rule_tag : forall session id rule,
  original_rule session id = Some rule ->
  A.index id < original_len session /\ nth_error (private_store session) (A.index id) = Some (A.RuleNode rule).
Proof.
  intros; unfold original_rule in H; destruct (Nat.ltb (A.index id) (original_len session)) eqn:E; [|discriminate].
  apply Nat.ltb_lt in E. destruct (nth_error (private_store session) (A.index id)) as [node|] eqn:R; [|discriminate].
  destruct node; try discriminate; inversion H; subst; auto.
Qed.

(** This gate is used at a reached PreflightItem after the original presence
    gates, never as a new initial grammar scan. Both absent delimiters remain
    an admitted original view and later semantic None; a half pair is unsupported. *)
Definition delimiter_view item := match item with
| A.LegacyCollection _ _ _ open close => A.legacy_delimiter_view open close
| _ => Some None end.
Theorem half_delimiter_is_not_erased : forall kind element separator open,
  delimiter_view (A.LegacyCollection kind element separator (Some open) None) = None.
Proof. reflexivity. Qed.
Theorem both_absent_delimiters_remain_an_original_view : forall kind element separator,
  delimiter_view (A.LegacyCollection kind element separator None None) = Some None.
Proof. reflexivity. Qed.
Theorem already_normalized_rules_never_reach_delimiter_admission : forall source rule tc,
  L.term_context rule = Some tc ->
  I.shared_schedule source rule = [I.observation L.HasTermContext].
Proof. intros; eapply I.present_context_has_no_item_or_constructor_admission; exact H. Qed.

(** A consuming call has one public Result boundary. On error no private store,
    class table, recipe prefix or normalized handle escapes. The successful
    receipt is constructed only from an actual checked terminal commit. *)
Definition publish_commit session entries admitted reserved original params syntax :=
  match append_paid admitted reserved (private_store session)
    (commit_batch (List.length (private_store session)) original params syntax) with
  | None => None
  | Some nodes => Some
      ({| private_store := nodes; original_len := original_len session; name_index := Some entries |},
       commit_handle (List.length (private_store session)))
  end.
Theorem failed_commit_returns_no_session_or_handle : forall session entries admitted reserved original params syntax,
  append_paid admitted reserved (private_store session)
    (commit_batch (List.length (private_store session)) original params syntax) = None ->
  publish_commit session entries admitted reserved original params syntax = None.
Proof. intros; unfold publish_commit; now rewrite H. Qed.
Theorem successful_session_preserves_original_bound_and_entire_prefix :
  forall session entries admitted reserved original params syntax next id,
  publish_commit session entries admitted reserved original params syntax = Some (next, id) ->
  original_len next = original_len session /\
  private_store next = private_store session ++ commit_batch (List.length (private_store session)) original params syntax /\
  id = commit_handle (List.length (private_store session)).
Proof.
  intros; unfold publish_commit in H.
  destruct (append_paid admitted reserved (private_store session)
    (commit_batch (List.length (private_store session)) original params syntax)) as [nodes|] eqn:E; [|discriminate].
  apply paid_batch_is_exact_existing_checked_append in E; destruct E as [_ [_ Nodes]].
  inversion H; subst; repeat split; reflexivity.
Qed.
Theorem shared_normalization_is_reused_not_rederived : forall source rule,
  L.shared_normalize (fun index => L.project_item (source index)) L.original_constructors rule =
  L.source_normalize source rule.
Proof. apply L.original_normalization_relocated_exactly. Qed.
Theorem original_admission_refusal_has_no_materializable_pair :
  forall cost maximum available budget source out accepted next suffix reason remaining,
  I.run cost maximum available 0 budget (I.instrument source (L.trace out)) =
    I.Stopped accepted next suffix reason remaining ->
  I.publish cost maximum available budget source out = I.Failed reason.
Proof. apply I.error_never_publishes_a_partial_normalized_pair. Qed.

Print Assumptions original_generated_spelling_is_not_raw.
Print Assumptions source_index_insertion_never_renumbers.
Print Assumptions source_index_checks_the_concrete_profile.
Print Assumptions checked_name_index_establishes_profile.
Print Assumptions successful_lazy_index_establishes_concrete_name_reads.
Print Assumptions index_retains_source_class_width_without_inventing_it.
Print Assumptions fresh_class_is_distinct_without_renumbering.
Print Assumptions generated_name_hit_reuses_existing_representative_even_at_max.
Print Assumptions generated_name_hit_preserves_exact_read.
Print Assumptions missing_generated_class_refuses_only_when_extension_is_needed.
Print Assumptions denied_generated_name_has_no_append.
Print Assumptions generated_extension_keeps_original_nodes_and_numbers.
Print Assumptions generated_enrollment_preserves_profile_reads_width_and_exact_spelling.
Print Assumptions unpaid_lookup_cannot_probe_or_extend_names.
Print Assumptions original_param_constructors_project_to_exact_recipes.
Print Assumptions original_syntax_constructors_project_to_exact_recipes.
Print Assumptions unpaid_or_unreserved_batch_returns_no_store.
Print Assumptions paid_batch_is_exact_existing_checked_append.
Print Assumptions paid_batch_preserves_prior_typed_handles.
Print Assumptions paid_batch_preserves_existing_store_validation.
Print Assumptions parameter_materialization_is_read_by_existing_reader.
Print Assumptions abstraction_batch_keeps_both_original_category_handles.
Print Assumptions collection_batch_is_original_collection_not_map_type.
Print Assumptions separator_materializes_original_source_none.
Print Assumptions literal_and_parameter_syntax_need_no_operation_node.
Print Assumptions replacement_preserves_every_retained_original_field.
Print Assumptions successful_commit_has_both_sequences_before_rule.
Print Assumptions successful_commit_exposes_exact_existing_rule_reader.
Print Assumptions session_consumes_store_without_copy_or_index.
Print Assumptions appended_rule_cannot_be_readmitted_as_original.
Print Assumptions accepted_original_handle_has_the_actual_rule_tag.
Print Assumptions half_delimiter_is_not_erased.
Print Assumptions both_absent_delimiters_remain_an_original_view.
Print Assumptions already_normalized_rules_never_reach_delimiter_admission.
Print Assumptions failed_commit_returns_no_session_or_handle.
Print Assumptions successful_session_preserves_original_bound_and_entire_prefix.
Print Assumptions shared_normalization_is_reused_not_rederived.
Print Assumptions original_admission_refusal_has_no_materializable_pair.
End AuthoredNormalizationMaterialization.
