(** Source-admission protocol, before neutral target construction.

    This closed model checks a finite retained forest, not completeness of the
    parser that produced it. Exact source-constructor translation, lexical
    resolution, typed graph validation, canonical Par emission, resource
    accounting and host authorization remain distinct refinement obligations.
    In particular, ClassifiedSource is NOT PreparedProgram.

    Semantic payloads and ordered occurrence rosters are structural data, not
    hashes or executable blobs. Only diagnostic origins are erased. The scan
    uses a reverse accumulator. Coverage reuses Stdlib's merge-stack sort; it
    never sorts or prunes the retained candidate/provenance roster. *)

From Stdlib Require Import String List ZArith PeanoNat Bool Lia
  Sorting.Permutation Sorting.Mergesort.
Import ListNotations.

Inductive Position := Term | Name | Pattern | Guard | Declaration.
Inductive Form :=
| Zero | Parallel | Send | Fresh | Receive | VariableForm | Quote | Drop
| Scalar | ListValue | MapValue | Method | Ddl | Flt | BooleanOp
| Unsupported (category constructor : string).

Inductive Obligation :=
| ResolveScope | ValidateStructure | BindProvider | ConstructGuest
| MatchGuest | ObserveGuest | CheckLiveAuthority | ProjectResources | FundCommit.

Inductive FormResult :=
| Supported (pending : list Obligation)
| UnsupportedForm (position : Position) (form : Form).

(** This is a concrete classification of the closed source-family vocabulary,
    not an externally supplied [is_supported] Boolean. Mapping each pinned
    generated constructor and its child positions into this vocabulary is a
    required source-correspondence gate; Ddl is not a bypass for its children. *)
Definition classify_form (p : Position) (f : Form) : FormResult :=
  match f with
  | Unsupported _ _ => UnsupportedForm p f
  | _ =>
    match p, f with
    | Term, Zero | Term, Parallel | Term, Send | Term, Fresh | Term, Receive
    | Term, VariableForm | Term, Drop | Term, Scalar | Term, ListValue
    | Term, MapValue | Term, Method | Term, BooleanOp
    | Name, VariableForm | Name, Quote | Name, Scalar
    | Pattern, VariableForm | Pattern, Quote | Pattern, Scalar
    | Pattern, ListValue | Pattern, MapValue
    | Guard, VariableForm | Guard, Scalar | Guard, Method | Guard, BooleanOp =>
        Supported [ResolveScope; ValidateStructure]
    | Term, Ddl | Declaration, Ddl =>
        Supported [ResolveScope; ValidateStructure; BindProvider]
    | Term, Flt => Supported
        [ResolveScope; ValidateStructure; BindProvider; ConstructGuest;
         CheckLiveAuthority; ProjectResources; FundCommit]
    | Pattern, Flt => Supported
        [ResolveScope; ValidateStructure; BindProvider; MatchGuest;
         CheckLiveAuthority; ProjectResources; FundCommit]
    | Guard, Flt => Supported
        [ResolveScope; ValidateStructure; BindProvider; ConstructGuest;
         ObserveGuest; CheckLiveAuthority; ProjectResources; FundCommit]
    | _, _ => UnsupportedForm p f
    end
  end.

Theorem form_classification_total : forall p f,
  (exists obligations, classify_form p f = Supported obligations) \/
  classify_form p f = UnsupportedForm p f.
Proof. intros p f; destruct p, f; cbn; eauto. Qed.

Theorem unsupported_constructor_rejected : forall p category constructor,
  classify_form p (Unsupported category constructor) =
    UnsupportedForm p (Unsupported category constructor).
Proof. reflexivity. Qed.

Inductive Reference := Bound (index : nat) | External (name : string).
Inductive Atom := IntegerAtom (value : Z) | TextAtom (value : string)
  | BooleanAtom (value : bool) | IndexAtom (value : nat).
Inductive HolePolarity := Construction | Capture.
Inductive GuestPiece := GuestText (text : string)
  | GuestHole (polarity : HolePolarity) (category : string) (reference : Reference).

Record SemanticOccurrence := {
  occurrence_position : Position;
  occurrence_form : Form;
  source_category : string;
  source_constructor : string;
  scalar_payload : list Atom;
  lexical_references : list Reference;
  ordered_children : list nat;
  guest_selector : option Reference;
  guest_category : option string;
  guest_pieces : list GuestPiece;
  capture_telescope : list (Reference * string)
}.

Record Origin := {
  diagnostic_id : nat;
  source_span : option (nat * nat);
  generated_parent : option (nat * string)
}.

Record Candidate := {
  candidate_root : nat;
  candidate_occurrences : list (SemanticOccurrence * Origin)
}.

Definition SemanticGraph := (nat * list SemanticOccurrence)%type.
Definition erase_origins (candidate : Candidate) : SemanticGraph :=
  (candidate_root candidate, map fst (candidate_occurrences candidate)).

Definition semantic_graph_eq_dec : forall x y : SemanticGraph, {x = y} + {x <> y}.
Proof.
  decide equality; decide equality; decide equality;
    repeat decide equality; try apply string_dec; try apply Z.eq_dec;
    try apply Nat.eq_dec.
Defined.

Definition annotate (root : nat) (nodes : list SemanticOccurrence)
    (origin : SemanticOccurrence -> Origin) : Candidate :=
  {| candidate_root := root;
     candidate_occurrences := map (fun node => (node, origin node)) nodes |}.

Theorem erasure_retains_semantic_structure : forall root nodes origin,
  erase_origins (annotate root nodes origin) = (root, nodes).
Proof.
  intros. unfold erase_origins, annotate; cbn.
  rewrite map_map. cbn. now rewrite map_id.
Qed.

Theorem annotation_invariance : forall root nodes first second,
  erase_origins (annotate root nodes first) =
    erase_origins (annotate root nodes second).
Proof. intros; now rewrite !erasure_retains_semantic_structure. Qed.

Theorem erasure_retains_occurrence_multiplicity : forall candidate,
  length (snd (erase_origins candidate)) =
    length (candidate_occurrences candidate).
Proof. intros []; cbn; apply length_map. Qed.

Theorem erasure_retains_child_order_and_references : forall root nodes origin,
  map (fun n => (ordered_children n, lexical_references n))
    (snd (erase_origins (annotate root nodes origin))) =
  map (fun n => (ordered_children n, lexical_references n)) nodes.
Proof. intros; now rewrite erasure_retains_semantic_structure. Qed.

Definition classify_occurrence (n : SemanticOccurrence) :=
  classify_form (occurrence_position n) (occurrence_form n).

Inductive ScanResult :=
| Scanned (pending_by_occurrence : list (list Obligation))
| ScanRejected (ordinal : nat) (occurrence : SemanticOccurrence).

Fixpoint scan (nodes : list SemanticOccurrence)
    (reversed : list (list Obligation)) : ScanResult :=
  match nodes with
  | [] => Scanned (rev reversed)
  | node :: rest =>
    match classify_occurrence node with
    | Supported obligations => scan rest (obligations :: reversed)
    | UnsupportedForm _ _ => ScanRejected (length reversed) node
    end
  end.

Definition CoversOccurrences :=
  Forall2 (fun node obligations => classify_occurrence node = Supported obligations).

Theorem scan_preserves_all_obligations : forall nodes reversed result,
  scan nodes reversed = Scanned result ->
  exists pending, CoversOccurrences nodes pending /\ result = rev reversed ++ pending.
Proof.
  induction nodes as [|node rest IH]; intros reversed result H.
  - cbn in H. inversion H; subst. exists []. split; [constructor | now rewrite app_nil_r].
  - cbn in H. destruct (classify_occurrence node) as [obligations|p f] eqn:E;
      try discriminate.
    destruct (IH _ _ H) as [pending [Hcoverage Hresult]].
    exists (obligations :: pending). split.
    + constructor; assumption.
    + rewrite Hresult. cbn. now rewrite <- app_assoc.
Qed.

Theorem empty_accumulator_scan_covers_every_occurrence : forall nodes result,
  scan nodes [] = Scanned result -> CoversOccurrences nodes result.
Proof.
  intros nodes result H. destruct (scan_preserves_all_obligations _ _ _ H)
    as [pending [Hcover Heq]]. cbn in Heq. now subst.
Qed.

Theorem scan_rejection_identifies_first_unsupported_occurrence :
  forall nodes reversed ordinal rejected,
  scan nodes reversed = ScanRejected ordinal rejected ->
  exists prefix suffix,
    nodes = prefix ++ rejected :: suffix /\
    ordinal = length reversed + length prefix /\
    Forall (fun node => exists obligations,
      classify_occurrence node = Supported obligations) prefix /\
    classify_occurrence rejected =
      UnsupportedForm (occurrence_position rejected) (occurrence_form rejected).
Proof.
  induction nodes as [|node rest IH]; intros reversed ordinal rejected H; cbn in H;
    try discriminate.
  destruct (classify_occurrence node) as [obligations|p f] eqn:E.
  - destruct (IH _ _ _ H) as [prefix [suffix [Hnodes [Hordinal [Hprefix Hreject]]]]].
    exists (node :: prefix), suffix. split; [cbn; now rewrite Hnodes |].
    split; [cbn in *; lia |]. split; [constructor; [eauto | exact Hprefix] | exact Hreject].
  - inversion H; subst. exists [], rest. split; [reflexivity |].
    split; [cbn; lia |]. split; [constructor |].
    destruct (form_classification_total (occurrence_position rejected)
      (occurrence_form rejected)) as [[obligations Hok]|Hreject].
    + unfold classify_occurrence in E. rewrite Hok in E. discriminate.
    + exact Hreject.
Qed.

(** Root coordinates are checked against the complete retained finite roster.
    Outstanding work means unfinished enumeration. These are inspectable data,
    not a caller-supplied completeness Boolean. Parser-to-forest coverage is
    deliberately NOT claimed by this local protocol theorem. *)
Definition check_coverage (enumerated : list nat) (forest_size : nat) : bool :=
  if list_eq_dec Nat.eq_dec (NatSort.sort enumerated)
       (NatSort.sort (seq 0 forest_size)) then true else false.

Theorem checked_coverage_is_exact_permutation : forall enumerated size,
  check_coverage enumerated size = true ->
  Permutation enumerated (seq 0 size).
Proof.
  intros enumerated size. unfold check_coverage.
  destruct (list_eq_dec Nat.eq_dec _ _) as [Heq|Hneq]; try discriminate.
  intros _. eapply Permutation_trans; [apply NatSort.Permuted_sort |].
  rewrite Heq. apply Permutation_sym, NatSort.Permuted_sort.
Qed.

Theorem canonical_roster_passes_coverage : forall size,
  check_coverage (seq 0 size) size = true.
Proof.
  intros size. unfold check_coverage.
  destruct (list_eq_dec Nat.eq_dec _ _); congruence.
Qed.

Fixpoint agree_with (graph : SemanticGraph) (forest : list Candidate) : bool :=
  match forest with
  | [] => true
  | candidate :: rest =>
      if semantic_graph_eq_dec (erase_origins candidate) graph
      then agree_with graph rest else false
  end.

Theorem agreement_checks_every_candidate : forall forest graph,
  agree_with graph forest = true <->
  Forall (fun candidate => erase_origins candidate = graph) forest.
Proof.
  induction forest as [|candidate rest IH]; intros graph; cbn [agree_with].
  - split; intros; constructor.
  - destruct (semantic_graph_eq_dec (erase_origins candidate) graph) as [E|E].
    + rewrite IH. split; intro H; [now constructor | now inversion H].
    + split; intro H; [discriminate | inversion H; contradiction].
Qed.

Definition forest_occurrences (forest : list Candidate) : list SemanticOccurrence :=
  flat_map (fun candidate => snd (erase_origins candidate)) forest.

Inductive AdmissionResult :=
| IncompleteParse
| NoParse
| AmbiguousSource
| RejectedSource (ordinal : nat) (occurrence : SemanticOccurrence)
| ClassifiedSource (retained : list Candidate)
    (pending_by_occurrence : list (list Obligation)).

Definition classify_forest (outstanding enumerated : list nat)
    (forest : list Candidate) : AdmissionResult :=
  match outstanding with
  | _ :: _ => IncompleteParse
  | [] =>
    if check_coverage enumerated (length forest) then
      match forest with
      | [] => NoParse
      | candidate :: _ =>
        if agree_with (erase_origins candidate) forest then
          match scan (forest_occurrences forest) [] with
          | Scanned pending => ClassifiedSource forest pending
          | ScanRejected ordinal node => RejectedSource ordinal node
          end
        else AmbiguousSource
      end
    else IncompleteParse
  end.

Theorem outstanding_work_is_incomplete : forall work rest enumerated forest,
  classify_forest (work :: rest) enumerated forest = IncompleteParse.
Proof. reflexivity. Qed.

Theorem classified_source_retains_complete_original_roster :
  forall outstanding enumerated forest retained pending,
  classify_forest outstanding enumerated forest = ClassifiedSource retained pending ->
  outstanding = [] /\
  Permutation enumerated (seq 0 (length forest)) /\
  retained = forest /\
  exists candidate rest,
    forest = candidate :: rest /\
    Forall (fun other => erase_origins other = erase_origins candidate) forest /\
    CoversOccurrences (forest_occurrences forest) pending.
Proof.
  intros outstanding enumerated forest retained pending H.
  destruct outstanding as [|work tail]; [|discriminate].
  cbn [classify_forest] in H.
  destruct (check_coverage enumerated (length forest)) eqn:Hcoverage;
    [|discriminate].
  destruct forest as [|candidate rest]; [discriminate|].
  destruct (agree_with (erase_origins candidate) (candidate :: rest)) eqn:Hagree;
    [|discriminate].
  destruct (scan (forest_occurrences (candidate :: rest)) []) eqn:Hscan;
    inversion H; subst.
  split; [reflexivity|]. split.
  - now apply checked_coverage_is_exact_permutation.
  - split; [reflexivity|]. exists candidate, rest. split; [reflexivity|]. split.
    + now apply agreement_checks_every_candidate.
    + now apply empty_accumulator_scan_covers_every_occurrence.
Qed.

Theorem disagreement_is_not_filtered_by_support : forall enumerated candidate rest,
  check_coverage enumerated (length (candidate :: rest)) = true ->
  agree_with (erase_origins candidate) (candidate :: rest) = false ->
  classify_forest [] enumerated (candidate :: rest) = AmbiguousSource.
Proof. intros. cbn [classify_forest]. now rewrite H, H0. Qed.

Theorem no_parse_requires_complete_empty_forest : forall outstanding enumerated forest,
  classify_forest outstanding enumerated forest = NoParse ->
  outstanding = [] /\ forest = [] /\ enumerated = [].
Proof.
  intros outstanding enumerated forest H.
  destruct outstanding; [|discriminate]. cbn [classify_forest] in H.
  destruct (check_coverage enumerated (length forest)) eqn:E; [|discriminate].
  destruct forest as [|candidate rest].
  - apply checked_coverage_is_exact_permutation in E. cbn in E.
    apply Permutation_sym in E. apply Permutation_nil in E. auto.
  - destruct (agree_with (erase_origins candidate) (candidate :: rest));
      [destruct (scan (forest_occurrences (candidate :: rest)) [])|]; discriminate.
Qed.

(** The ordinal is a coordinate in the original ordered annotated roster, not
    a shared semantic-node id. Even identical nodes retain distinct origins. *)
Definition forest_annotated_occurrences (forest : list Candidate) :=
  flat_map candidate_occurrences forest.

Lemma forest_erasure_is_occurrence_map : forall forest,
  forest_occurrences forest = map fst (forest_annotated_occurrences forest).
Proof.
  induction forest as [|candidate rest IH]; cbn [forest_occurrences
    forest_annotated_occurrences flat_map erase_origins]; [reflexivity |].
  rewrite map_app. f_equal. exact IH.
Qed.

Theorem rejected_source_identifies_original_origin :
  forall work enumerated forest ordinal node,
  classify_forest work enumerated forest = RejectedSource ordinal node ->
  exists origin,
    nth_error (forest_annotated_occurrences forest) ordinal = Some (node, origin) /\
    Forall (fun prior => exists obligations,
      classify_occurrence prior = Supported obligations)
      (firstn ordinal (forest_occurrences forest)).
Proof.
  intros work enumerated forest ordinal node H.
  destruct work; [|discriminate]. cbn [classify_forest] in H.
  destruct (check_coverage enumerated (length forest)); [|discriminate].
  destruct forest as [|candidate rest]; [discriminate |].
  destruct (agree_with (erase_origins candidate) (candidate :: rest)); [|discriminate].
  destruct (scan (forest_occurrences (candidate :: rest)) []) eqn:E;
    inversion H; subst.
  destruct (scan_rejection_identifies_first_unsupported_occurrence _ _ _ _ E)
    as [prefix [suffix [Hnodes [Hordinal [Hprefix Hreject]]]]].
  cbn in Hordinal. subst ordinal.
  assert (Hnth : nth_error (forest_occurrences (candidate :: rest))
    (length prefix) = Some node).
  { rewrite Hnodes, nth_error_app2; [now rewrite Nat.sub_diag | lia]. }
  rewrite forest_erasure_is_occurrence_map, nth_error_map in Hnth.
  destruct (nth_error (forest_annotated_occurrences (candidate :: rest))
    (length prefix)) as [[found origin]|] eqn:Horigin; [|discriminate].
  cbn in Hnth. inversion Hnth; subst found. exists origin. split; [reflexivity |].
  rewrite Hnodes, firstn_app, firstn_all, Nat.sub_diag. cbn. now rewrite app_nil_r.
Qed.

(** Forget only the intentionally retained origins when comparing outcomes. *)
Inductive ClassificationView :=
| ViewIncomplete | ViewNoParse | ViewAmbiguous
| ViewRejected (ordinal : nat) (node : SemanticOccurrence)
| ViewClassified (graphs : list SemanticGraph) (pending : list (list Obligation)).

Definition classification_view (result : AdmissionResult) :=
  match result with
  | IncompleteParse => ViewIncomplete
  | NoParse => ViewNoParse
  | AmbiguousSource => ViewAmbiguous
  | RejectedSource ordinal node => ViewRejected ordinal node
  | ClassifiedSource forest pending => ViewClassified (map erase_origins forest) pending
  end.

Lemma same_graphs_same_agreement : forall left right graph,
  map erase_origins left = map erase_origins right ->
  agree_with graph left = agree_with graph right.
Proof.
  induction left as [|candidate rest IH]; intros right graph H;
    destruct right as [|other tail]; try discriminate; [reflexivity |].
  pose proof (f_equal (hd (erase_origins candidate)) H) as Heq.
  change (erase_origins candidate = erase_origins other) in Heq.
  pose proof (f_equal (@tl SemanticGraph) H) as Htail.
  change (map erase_origins rest = map erase_origins tail) in Htail.
  cbn [agree_with]. rewrite Heq. destruct (semantic_graph_eq_dec _ _);
    [now apply IH | reflexivity].
Qed.

Lemma same_graphs_same_occurrences : forall left right,
  map erase_origins left = map erase_origins right ->
  forest_occurrences left = forest_occurrences right.
Proof.
  induction left as [|candidate rest IH]; intros right H;
    destruct right as [|other tail]; try discriminate; [reflexivity |].
  pose proof (f_equal (hd (erase_origins candidate)) H) as Heq.
  change (erase_origins candidate = erase_origins other) in Heq.
  pose proof (f_equal (@tl SemanticGraph) H) as Htail.
  change (map erase_origins rest = map erase_origins tail) in Htail.
  change (snd (erase_origins candidate) ++ forest_occurrences rest =
    snd (erase_origins other) ++ forest_occurrences tail).
  rewrite Heq. now rewrite (IH _ Htail).
Qed.

Theorem origins_do_not_change_classification : forall work enumerated left right,
  map erase_origins left = map erase_origins right ->
  classification_view (classify_forest work enumerated left) =
  classification_view (classify_forest work enumerated right).
Proof.
  intros work enumerated left right Hgraphs.
  assert (Hlength : length left = length right).
  { apply (f_equal (@length SemanticGraph)) in Hgraphs.
    now rewrite !length_map in Hgraphs. }
  pose proof (same_graphs_same_occurrences _ _ Hgraphs) as Hnodes.
  destruct work; [|reflexivity]. cbn [classify_forest]. rewrite Hlength.
  destruct (check_coverage enumerated (length right)); [|reflexivity].
  destruct left as [|candidate rest], right as [|other tail];
    try discriminate; [reflexivity |].
  pose proof (f_equal (hd (erase_origins candidate)) Hgraphs) as Heq.
  change (erase_origins candidate = erase_origins other) in Heq.
  rewrite (same_graphs_same_agreement _ _ (erase_origins candidate) Hgraphs), Heq.
  destruct (agree_with (erase_origins other) (other :: tail)); [|reflexivity].
  rewrite Hnodes. destruct (scan (forest_occurrences (other :: tail)) []);
    cbn [classification_view]; [now rewrite Hgraphs | reflexivity].
Qed.

(** No result variant carries discharged authority/funding evidence. The
    substantive boundary law below is that every classified guest guard still
    has its semantic and host obligations in the output. It does not model a
    host provider as an always-false flag or an uninhabited certificate type. *)
Lemma covered_occurrence_has_pending_entry : forall nodes pending node,
  CoversOccurrences nodes pending -> In node nodes ->
  exists obligations, In obligations pending /\
    classify_occurrence node = Supported obligations.
Proof.
  intros nodes pending node Hcover. induction Hcover; intro Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst. exists y. split; [now left | assumption].
    + destruct (IHHcover Hin) as [obligations [Hin' Hsupported]].
      exists obligations. split; [now right | assumption].
Qed.

Theorem classified_guard_retains_pending_host_checks :
  forall work enumerated forest retained pending node,
  classify_forest work enumerated forest = ClassifiedSource retained pending ->
  In node (forest_occurrences forest) ->
  occurrence_position node = Guard -> occurrence_form node = Flt ->
  In [ResolveScope; ValidateStructure; BindProvider; ConstructGuest;
      ObserveGuest; CheckLiveAuthority; ProjectResources; FundCommit] pending.
Proof.
  intros work enumerated forest retained pending node Hclass Hin Hp Hf.
  destruct (classified_source_retains_complete_original_roster _ _ _ _ _ Hclass)
    as [_ [_ [_ [candidate [rest [_ [_ Hcover]]]]]]].
  destruct (covered_occurrence_has_pending_entry _ _ _ Hcover Hin)
    as [obligations [Hpending Hsupported]].
  unfold classify_occurrence in Hsupported. rewrite Hp, Hf in Hsupported.
  cbn [classify_form] in Hsupported. inversion Hsupported; subst. exact Hpending.
Qed.

Theorem classified_source_contains_no_unsupported_occurrence :
  forall work enumerated forest retained pending node category constructor,
  classify_forest work enumerated forest = ClassifiedSource retained pending ->
  In node (forest_occurrences forest) ->
  occurrence_form node <> Unsupported category constructor.
Proof.
  intros work enumerated forest retained pending node category constructor Hclass Hin Hform.
  destruct (classified_source_retains_complete_original_roster _ _ _ _ _ Hclass)
    as [_ [_ [_ [candidate [rest [_ [_ Hcover]]]]]]].
  destruct (covered_occurrence_has_pending_entry _ _ _ Hcover Hin)
    as [obligations [_ Hsupported]].
  unfold classify_occurrence in Hsupported. rewrite Hform in Hsupported.
  rewrite unsupported_constructor_rejected in Hsupported. discriminate.
Qed.

Definition example_node (f : Form) (refs : list Reference) : SemanticOccurrence :=
  {| occurrence_position := Term; occurrence_form := f;
     source_category := "Proc"; source_constructor := "example";
     scalar_payload := []; lexical_references := refs; ordered_children := [];
     guest_selector := None; guest_category := None; guest_pieces := [];
     capture_telescope := [] |}.
Definition example_origin (id : nat) : Origin :=
  {| diagnostic_id := id; source_span := Some (id, S id); generated_parent := None |}.
Definition example_candidate (f : Form) (refs : list Reference) (id : nat) :=
  annotate 0 [example_node f refs] (fun _ => example_origin id).

Example incomplete_singleton_is_not_unique :
  classify_forest [1] [0] [example_candidate Zero [] 0] = IncompleteParse.
Proof. reflexivity. Qed.

Example missing_root_is_not_unique :
  classify_forest [] [0]
    [example_candidate Zero [] 0; example_candidate Zero [] 1] = IncompleteParse.
Proof. vm_compute. reflexivity. Qed.

Example unequal_readings_are_ambiguous :
  classify_forest [] [0;1]
    [example_candidate Zero [] 0; example_candidate Scalar [] 1] = AmbiguousSource.
Proof. vm_compute. reflexivity. Qed.

Example equal_readings_retain_both_origins :
  let forest := [example_candidate Zero [] 0; example_candidate Zero [] 1] in
  classify_forest [] [1;0] forest =
    ClassifiedSource forest [[ResolveScope; ValidateStructure];
                             [ResolveScope; ValidateStructure]].
Proof. vm_compute. reflexivity. Qed.

Example unsupported_alternative_is_not_discarded :
  classify_forest [] [0;1] [example_candidate Zero [] 0;
    example_candidate (Unsupported "Proc" "unknown") [] 1] = AmbiguousSource.
Proof. vm_compute. reflexivity. Qed.

Example unsupported_singleton_is_rejected :
  classify_forest [] [0] [example_candidate (Unsupported "Proc" "unknown") [] 0] =
    RejectedSource 0 (example_node (Unsupported "Proc" "unknown") []).
Proof. vm_compute. reflexivity. Qed.

Example binder_change_is_not_origin_change :
  erase_origins (example_candidate VariableForm [Bound 0] 0) <>
  erase_origins (example_candidate VariableForm [Bound 1] 0).
Proof. discriminate. Qed.

Example direct_guest_guard_keeps_semantic_and_host_obligations :
  classify_form Guard Flt = Supported
    [ResolveScope; ValidateStructure; BindProvider; ConstructGuest; ObserveGuest;
     CheckLiveAuthority; ProjectResources; FundCommit].
Proof. reflexivity. Qed.

Print Assumptions form_classification_total.
Print Assumptions unsupported_constructor_rejected.
Print Assumptions erasure_retains_semantic_structure.
Print Assumptions annotation_invariance.
Print Assumptions erasure_retains_occurrence_multiplicity.
Print Assumptions erasure_retains_child_order_and_references.
Print Assumptions scan_preserves_all_obligations.
Print Assumptions empty_accumulator_scan_covers_every_occurrence.
Print Assumptions scan_rejection_identifies_first_unsupported_occurrence.
Print Assumptions checked_coverage_is_exact_permutation.
Print Assumptions canonical_roster_passes_coverage.
Print Assumptions agreement_checks_every_candidate.
Print Assumptions outstanding_work_is_incomplete.
Print Assumptions classified_source_retains_complete_original_roster.
Print Assumptions disagreement_is_not_filtered_by_support.
Print Assumptions no_parse_requires_complete_empty_forest.
Print Assumptions forest_erasure_is_occurrence_map.
Print Assumptions rejected_source_identifies_original_origin.
Print Assumptions same_graphs_same_agreement.
Print Assumptions same_graphs_same_occurrences.
Print Assumptions origins_do_not_change_classification.
Print Assumptions covered_occurrence_has_pending_entry.
Print Assumptions classified_guard_retains_pending_host_checks.
Print Assumptions classified_source_contains_no_unsupported_occurrence.
Print Assumptions incomplete_singleton_is_not_unique.
Print Assumptions missing_root_is_not_unique.
Print Assumptions unequal_readings_are_ambiguous.
Print Assumptions equal_readings_retain_both_origins.
Print Assumptions unsupported_alternative_is_not_discarded.
Print Assumptions unsupported_singleton_is_rejected.
Print Assumptions binder_change_is_not_origin_change.
Print Assumptions direct_guest_guard_keeps_semantic_and_host_obligations.
