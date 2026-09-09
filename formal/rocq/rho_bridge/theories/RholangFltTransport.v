(** Exact FLT descriptor transport at the neutral frontend boundary.

    Source owners: runtime/src/flt_node.rs (FltNode::validate and stage),
    rholang-runtime/src/rholang_ast.rs (runtime_template_parts), and
    language_install.rs (NamedRuntimeTemplateHole). This models their data
    projection, not another validator, parser, reflector, or evaluator.

    In contrast to StructuralTemplate.v's abstract numeric guest chunks,
    payloads here retain the actual strings and optional category spellings.
    Existing structural-template theorems remain responsible for their stated
    abstract lexical/graft laws. Transport preservation does not establish the
    input validator, lexical resolution, provider authority, or full publication. *)

From Stdlib Require Import List String PeanoNat.
From RhoBridge Require RholangFrontendAdmission.
Import ListNotations.
Module Admission := RholangFrontendAdmission.

Definition BodyRange := (nat * nat)%type.
Inductive PiecePayload := ExactGuestText (text : string) | TelescopeHole (id : nat).
Record LocatedPayload := {
  piece_payload : PiecePayload;
  piece_body_range : BodyRange
}.
Record NamedHole := {
  hole_id : nat;
  hole_name : string;
  hole_category : option string
}.
Record LocatedHole := {
  hole_declaration : NamedHole;
  first_body_range : BodyRange
}.
Record StructuralExtent := {
  source_bytes : nat;
  body_bytes : nat;
  piece_count : nat;
  hole_declarations : nat;
  hole_occurrences : nat
}.
Record CapturedTemplate := {
  lexical_selector : Admission.Reference;
  selector_spelling : string;
  root_category : string;
  captured_opener : string;
  captured_body : string;
  captured_closer : string;
  captured_holes : list LocatedHole;
  captured_pieces : list LocatedPayload;
  captured_extent : StructuralExtent;
  opener_position : nat
}.
Record StagedTemplate := {
  staged_capture : CapturedTemplate;
  use_site_polarity : Admission.HolePolarity
}.
Definition stage (capture : CapturedTemplate) (polarity : Admission.HolePolarity)
    : StagedTemplate :=
  {| staged_capture := capture; use_site_polarity := polarity |}.

(** Only diagnostic ranges/spellings are erased. The exact structural text,
    repeated hole IDs, declared names/categories and checked extent survive.
    The spelling field is not the lexical reference and cannot confer authority. *)
Record SemanticTemplate := {
  retained_selector : Admission.Reference;
  retained_category : string;
  retained_polarity : Admission.HolePolarity;
  retained_holes : list NamedHole;
  retained_pieces : list PiecePayload;
  retained_extent : StructuralExtent
}.
Definition runtime_parts (template : StagedTemplate) : list PiecePayload * list NamedHole :=
  (map piece_payload (captured_pieces (staged_capture template)),
   map hole_declaration (captured_holes (staged_capture template))).
Definition erase_diagnostics (template : StagedTemplate) : SemanticTemplate :=
  let capture := staged_capture template in
  {| retained_selector := lexical_selector capture;
     retained_category := root_category capture;
     retained_polarity := use_site_polarity template;
     retained_holes := snd (runtime_parts template);
     retained_pieces := fst (runtime_parts template);
     retained_extent := captured_extent capture |}.

(** The host use site determines variance. A predicate first constructs a
    guest term and retains an observation obligation; it is not a negative
    receive pattern, nor does staging prove the predicate true or funded. *)
Inductive UseRole := ConstructionSite | ReceivePatternSite | PredicateSite.
Definition role_position (role : UseRole) : Admission.Position :=
  match role with
  | ConstructionSite => Admission.Term
  | ReceivePatternSite => Admission.Pattern
  | PredicateSite => Admission.Guard
  end.
Definition role_polarity (role : UseRole) : Admission.HolePolarity :=
  match role with
  | ReceivePatternSite => Admission.Capture
  | ConstructionSite | PredicateSite => Admission.Construction
  end.
Definition role_obligations (role : UseRole) : Admission.FormResult :=
  Admission.classify_form (role_position role) Admission.Flt.

Record ConstructionBinding := {
  filled_hole_id : nat;
  filled_hole_name : string;
  filled_reference : Admission.Reference
}.
Record DeclaredCaptureAssociation := {
  declared_hole_id : nat;
  enclosing_capture_slot : nat
}.
Record ForeignUse := {
  use_occurrence : nat;
  use_role : UseRole;
  use_capture : CapturedTemplate;
  construction_bindings : list ConstructionBinding;
  declared_capture_associations : list DeclaredCaptureAssociation
}.
Record SemanticUse := {
  semantic_occurrence : nat;
  semantic_role : UseRole;
  semantic_template : SemanticTemplate;
  semantic_bindings : list ConstructionBinding;
  semantic_captures : list DeclaredCaptureAssociation;
  semantic_obligations : Admission.FormResult
}.
Definition retain_use (use : ForeignUse) : SemanticUse :=
  {| semantic_occurrence := use_occurrence use;
     semantic_role := use_role use;
     semantic_template := erase_diagnostics
       (stage (use_capture use) (role_polarity (use_role use)));
     semantic_bindings := construction_bindings use;
     semantic_captures := declared_capture_associations use;
     semantic_obligations := role_obligations (use_role use) |}.

Theorem predicate_retains_construction_observation_and_host_obligations :
  role_obligations PredicateSite = Admission.Supported
    [Admission.ResolveScope; Admission.ValidateStructure; Admission.BindProvider;
     Admission.ConstructGuest; Admission.ObserveGuest; Admission.CheckLiveAuthority;
     Admission.ProjectResources; Admission.FundCommit] /\
  role_polarity PredicateSite = Admission.Construction.
Proof. split; reflexivity. Qed.

Theorem pattern_retains_matching_and_host_obligations :
  role_obligations ReceivePatternSite = Admission.Supported
    [Admission.ResolveScope; Admission.ValidateStructure; Admission.BindProvider;
     Admission.MatchGuest; Admission.CheckLiveAuthority;
     Admission.ProjectResources; Admission.FundCommit] /\
  role_polarity ReceivePatternSite = Admission.Capture.
Proof. split; reflexivity. Qed.

Theorem use_transport_retains_occurrence_and_associations : forall use,
  semantic_occurrence (retain_use use) = use_occurrence use /\
  semantic_bindings (retain_use use) = construction_bindings use /\
  semantic_captures (retain_use use) = declared_capture_associations use /\
  semantic_obligations (retain_use use) = role_obligations (use_role use).
Proof. intros; repeat split; reflexivity. Qed.

Theorem stage_retains_capture_and_host_polarity : forall capture polarity,
  staged_capture (stage capture polarity) = capture /\
  use_site_polarity (stage capture polarity) = polarity.
Proof. intros; split; reflexivity. Qed.

Theorem runtime_projection_retains_exact_payloads : forall capture polarity,
  runtime_parts (stage capture polarity) =
    (map piece_payload (captured_pieces capture), map hole_declaration (captured_holes capture)).
Proof. reflexivity. Qed.

Theorem runtime_projection_does_not_merge_pieces : forall capture polarity,
  List.length (fst (runtime_parts (stage capture polarity))) = List.length (captured_pieces capture).
Proof. intros; unfold runtime_parts, stage; cbn; apply length_map. Qed.

Theorem runtime_projection_retains_telescope_order : forall capture polarity index declaration,
  nth_error (captured_holes capture) index = Some declaration ->
  nth_error (snd (runtime_parts (stage capture polarity))) index = Some (hole_declaration declaration).
Proof. intros; unfold runtime_parts, stage; cbn. now rewrite nth_error_map, H. Qed.

Theorem runtime_projection_retains_each_occurrence : forall capture polarity index piece,
  nth_error (captured_pieces capture) index = Some piece ->
  nth_error (fst (runtime_parts (stage capture polarity))) index = Some (piece_payload piece).
Proof. intros; unfold runtime_parts, stage; cbn. now rewrite nth_error_map, H. Qed.

Theorem diagnostic_erasure_keeps_selector_category_polarity : forall capture polarity,
  retained_selector (erase_diagnostics (stage capture polarity)) = lexical_selector capture /\
  retained_category (erase_diagnostics (stage capture polarity)) = root_category capture /\
  retained_polarity (erase_diagnostics (stage capture polarity)) = polarity.
Proof. intros; repeat split; reflexivity. Qed.

Theorem diagnostic_erasure_keeps_exact_extent : forall capture polarity,
  retained_extent (erase_diagnostics (stage capture polarity)) = captured_extent capture.
Proof. reflexivity. Qed.

(** Locate by occurrence index, not by payload equality: two occurrences of
    the same hole or text may have different ranges. This mathematical helper
    states an annotation law and is not a new production traversal. *)
Fixpoint locate_items {A : Type} (items : list A) (next : nat)
    (location : nat -> BodyRange) : list (A * BodyRange) :=
  match items with
  | [] => []
  | item :: rest => (item, location next) :: locate_items rest (S next) location
  end.

Lemma locating_items_preserves_each_occurrence : forall A (items : list A) next location,
  map fst (locate_items items next location) = items.
Proof.
  intros A items; induction items as [|item rest IH]; intros next location; cbn;
    [reflexivity|now rewrite IH].
Qed.

(** Locate a semantic capture without altering any parsing input. Bounds are
    kept explicit: arbitrary new ranges need not validate, and this theorem
    makes no such claim. It is solely an erasure/retention law. *)
Definition locate_capture (selector : Admission.Reference) (category : string)
    (holes : list NamedHole) (pieces : list PiecePayload) (extent : StructuralExtent)
    (spelling opener body closer : string) (position : nat)
    (hole_location piece_location : nat -> BodyRange)
    : CapturedTemplate :=
  {| lexical_selector := selector; selector_spelling := spelling;
     root_category := category; captured_opener := opener; captured_body := body;
     captured_closer := closer;
     captured_holes := map (fun located =>
       {| hole_declaration := fst located; first_body_range := snd located |})
       (locate_items holes 0 hole_location);
     captured_pieces := map (fun located =>
       {| piece_payload := fst located; piece_body_range := snd located |})
       (locate_items pieces 0 piece_location);
     captured_extent := extent; opener_position := position |}.

Theorem locating_preserves_semantic_capture :
  forall selector category holes pieces extent spelling opener body closer position hl pl polarity,
  erase_diagnostics (stage
    (locate_capture selector category holes pieces extent spelling opener body closer position hl pl)
    polarity) =
  {| retained_selector := selector; retained_category := category; retained_polarity := polarity;
     retained_holes := holes; retained_pieces := pieces; retained_extent := extent |}.
Proof.
  intros; unfold erase_diagnostics, stage, locate_capture, runtime_parts; cbn.
  rewrite !map_map. cbn. now rewrite !locating_items_preserves_each_occurrence.
Qed.

Theorem optional_category_is_not_inferred_by_transport : forall hole range,
  hole_declaration {| hole_declaration := hole; first_body_range := range |} = hole.
Proof. reflexivity. Qed.

Example repeated_hole_ids_and_text_boundaries_survive : forall first middle last,
  map piece_payload
    [{| piece_payload := ExactGuestText "a"; piece_body_range := first |};
     {| piece_payload := TelescopeHole 0; piece_body_range := middle |};
     {| piece_payload := TelescopeHole 0; piece_body_range := last |}] =
    [ExactGuestText "a"; TelescopeHole 0; TelescopeHole 0].
Proof. reflexivity. Qed.

Print Assumptions stage_retains_capture_and_host_polarity.
Print Assumptions predicate_retains_construction_observation_and_host_obligations.
Print Assumptions pattern_retains_matching_and_host_obligations.
Print Assumptions use_transport_retains_occurrence_and_associations.
Print Assumptions runtime_projection_retains_exact_payloads.
Print Assumptions runtime_projection_does_not_merge_pieces.
Print Assumptions runtime_projection_retains_telescope_order.
Print Assumptions runtime_projection_retains_each_occurrence.
Print Assumptions diagnostic_erasure_keeps_selector_category_polarity.
Print Assumptions diagnostic_erasure_keeps_exact_extent.
Print Assumptions locating_preserves_semantic_capture.
Print Assumptions locating_items_preserves_each_occurrence.
Print Assumptions optional_category_is_not_inferred_by_transport.
Print Assumptions repeated_hole_ids_and_text_boundaries_survive.
