(**
  CanonicalLanguageCoreCodec: the closed structural [language/3] core envelope.

  The authoring presentation accepted by [language/2] is intentionally not the
  wire image of [GrammarCoreV1]. A complete migration therefore needs a second,
  closed [language/3] arm whose fields are a one-to-one structural image of
  [LanguageCoreV1]. This model enumerates every field of the Rust
  [GrammarCoreV1] record, so a field cannot disappear unnoticed.

  Lists of naturals stand for already-canonical typed child encodings. Their
  internal tagged-sum codecs have local left-inverse tests; this module proves
  the enclosing product, language-name commitment, ABI rejection, and the
  separation of GrammarCore from TheoryCore.

  Rocq 9.1 compatible. No admitted results, axioms, or assumptions.
*)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Module CanonicalLanguageCoreCodec.

Definition grammar_core_abi_v1 : nat := 1.
Definition language_core_abi_v1 : nat := 1.
Definition language3_core_schema_v1 : nat := 1.

(** Mirrors [grammar-core/src/core.rs::GrammarCoreV1] field for field and in
    declaration order. Diagnostic provenance is retained even though the
    semantic fingerprint intentionally clears it. *)
Record GrammarCoreV1Model := {
  grammar_abi : nat;
  grammar_name : nat;
  grammar_canonical_specification : option (list nat);
  grammar_backend_context : option (list nat);
  grammar_documentation : option (list nat);
  grammar_categories : list nat;
  grammar_tokens : list nat;
  grammar_modes : list nat;
  grammar_productions : list nat;
  grammar_reductions : list nat;
  grammar_semantic_dependencies : list (list nat);
  grammar_semantic_program : list nat;
  grammar_parser_configuration : list nat;
  grammar_synchronization : list nat;
  grammar_tree_invariants : list nat;
  grammar_refinement_types : list nat;
  grammar_guard_configuration : option (list nat);
  grammar_capabilities : list nat;
  grammar_requested_rights : list nat;
  grammar_provenance : list nat;
  grammar_limits : list nat;
  grammar_weight_profile : list nat
}.

(** A distinct record makes omission visible: encoding is not a type alias and
    does not appeal to opaque binary serialization. *)
Record GrammarCoreValueV1 := {
  value_grammar_abi : nat;
  value_grammar_name : nat;
  value_canonical_specification : option (list nat);
  value_backend_context : option (list nat);
  value_documentation : option (list nat);
  value_categories : list nat;
  value_tokens : list nat;
  value_modes : list nat;
  value_productions : list nat;
  value_reductions : list nat;
  value_semantic_dependencies : list (list nat);
  value_semantic_program : list nat;
  value_parser_configuration : list nat;
  value_synchronization : list nat;
  value_tree_invariants : list nat;
  value_refinement_types : list nat;
  value_guard_configuration : option (list nat);
  value_capabilities : list nat;
  value_requested_rights : list nat;
  value_provenance : list nat;
  value_limits : list nat;
  value_weight_profile : list nat
}.

Definition encode_grammar (core : GrammarCoreV1Model) : GrammarCoreValueV1 :=
  {| value_grammar_abi := grammar_abi core;
     value_grammar_name := grammar_name core;
     value_canonical_specification := grammar_canonical_specification core;
     value_backend_context := grammar_backend_context core;
     value_documentation := grammar_documentation core;
     value_categories := grammar_categories core;
     value_tokens := grammar_tokens core;
     value_modes := grammar_modes core;
     value_productions := grammar_productions core;
     value_reductions := grammar_reductions core;
     value_semantic_dependencies := grammar_semantic_dependencies core;
     value_semantic_program := grammar_semantic_program core;
     value_parser_configuration := grammar_parser_configuration core;
     value_synchronization := grammar_synchronization core;
     value_tree_invariants := grammar_tree_invariants core;
     value_refinement_types := grammar_refinement_types core;
     value_guard_configuration := grammar_guard_configuration core;
     value_capabilities := grammar_capabilities core;
     value_requested_rights := grammar_requested_rights core;
     value_provenance := grammar_provenance core;
     value_limits := grammar_limits core;
     value_weight_profile := grammar_weight_profile core |}.

Definition decode_grammar (value : GrammarCoreValueV1) : GrammarCoreV1Model :=
  {| grammar_abi := value_grammar_abi value;
     grammar_name := value_grammar_name value;
     grammar_canonical_specification := value_canonical_specification value;
     grammar_backend_context := value_backend_context value;
     grammar_documentation := value_documentation value;
     grammar_categories := value_categories value;
     grammar_tokens := value_tokens value;
     grammar_modes := value_modes value;
     grammar_productions := value_productions value;
     grammar_reductions := value_reductions value;
     grammar_semantic_dependencies := value_semantic_dependencies value;
     grammar_semantic_program := value_semantic_program value;
     grammar_parser_configuration := value_parser_configuration value;
     grammar_synchronization := value_synchronization value;
     grammar_tree_invariants := value_tree_invariants value;
     grammar_refinement_types := value_refinement_types value;
     grammar_guard_configuration := value_guard_configuration value;
     grammar_capabilities := value_capabilities value;
     grammar_requested_rights := value_requested_rights value;
     grammar_provenance := value_provenance value;
     grammar_limits := value_limits value;
     grammar_weight_profile := value_weight_profile value |}.

Theorem grammar_structural_codec_is_left_inverse :
  forall core, decode_grammar (encode_grammar core) = core.
Proof.
  intros [abi name specification context documentation categories tokens modes
          productions reductions dependencies program parser synchronization
          invariants refinements guards capabilities rights provenance limits
          weights].
  reflexivity.
Qed.

Record LanguageCoreV1Model := {
  language_abi : nat;
  language_grammar : GrammarCoreV1Model;
  language_theory : list nat
}.

Record Language3CoreEnvelopeV1 := {
  envelope_schema : nat;
  envelope_name : nat;
  envelope_language_abi : nat;
  envelope_grammar : GrammarCoreValueV1;
  envelope_theory : list nat
}.

Definition encode_language (core : LanguageCoreV1Model) :
    Language3CoreEnvelopeV1 :=
  {| envelope_schema := language3_core_schema_v1;
     envelope_name := grammar_name (language_grammar core);
     envelope_language_abi := language_abi core;
     envelope_grammar := encode_grammar (language_grammar core);
     envelope_theory := language_theory core |}.

(** The Rust decoder additionally performs closed-map and typed child-codec
    gates. A record value is closed by construction here. *)
Definition decode_language (value : Language3CoreEnvelopeV1) :
    option LanguageCoreV1Model :=
  if Nat.eqb (envelope_schema value) language3_core_schema_v1 then
    if Nat.eqb (envelope_language_abi value) language_core_abi_v1 then
      let grammar := decode_grammar (envelope_grammar value) in
      if Nat.eqb (grammar_abi grammar) grammar_core_abi_v1 then
        if Nat.eqb (envelope_name value) (grammar_name grammar) then
          Some {| language_abi := envelope_language_abi value;
                  language_grammar := grammar;
                  language_theory := envelope_theory value |}
        else None
      else None
    else None
  else None.

Definition well_versioned (core : LanguageCoreV1Model) : Prop :=
  language_abi core = language_core_abi_v1 /\
  grammar_abi (language_grammar core) = grammar_core_abi_v1.

Theorem language_structural_codec_is_left_inverse :
  forall core,
    well_versioned core ->
    decode_language (encode_language core) = Some core.
Proof.
  intros [language_abi0 grammar theory] [Hlanguage Hgrammar].
  destruct grammar as
    [grammar_abi0 name specification context documentation categories tokens
     modes productions reductions dependencies program parser synchronization
     invariants refinements guards capabilities rights provenance limits weights].
  simpl in Hlanguage, Hgrammar |- *.
  subst language_abi0 grammar_abi0.
  unfold decode_language, encode_language, encode_grammar, decode_grammar.
  cbn.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem envelope_name_mismatch_is_rejected :
  forall schema name language_abi0 grammar theory,
    schema = language3_core_schema_v1 ->
    language_abi0 = language_core_abi_v1 ->
    value_grammar_abi grammar = grammar_core_abi_v1 ->
    Nat.eqb name (value_grammar_name grammar) = false ->
    decode_language
      {| envelope_schema := schema;
         envelope_name := name;
         envelope_language_abi := language_abi0;
         envelope_grammar := grammar;
         envelope_theory := theory |} = None.
Proof.
  intros schema name language_abi0 grammar theory
         Hschema Hlanguage Hgrammar Hname.
  subst schema language_abi0.
  unfold decode_language.
  simpl.
  rewrite Hgrammar, Nat.eqb_refl, Hname.
  reflexivity.
Qed.

Theorem theory_change_does_not_change_encoded_grammar :
  forall abi grammar left_theory right_theory,
    envelope_grammar
      (encode_language
        {| language_abi := abi;
           language_grammar := grammar;
           language_theory := left_theory |}) =
    envelope_grammar
      (encode_language
        {| language_abi := abi;
           language_grammar := grammar;
           language_theory := right_theory |}).
Proof.
  reflexivity.
Qed.

End CanonicalLanguageCoreCodec.
