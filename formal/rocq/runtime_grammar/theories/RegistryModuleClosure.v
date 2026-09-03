From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.

(** A Registry module is authoritative canonical content, not source text.
    This model isolates the obligations discharged by the iterative production
    resolver: exact commitments, trust, finite resource bounds, Registry-only
    dependencies, strictly descending acyclicity ranks, and atomic publication.

    Natural numbers abstract fixed-width hashes and Registry references.  Their
    cryptographic realization is outside this transition model; equality here
    is the exact byte equality performed by the Rust adapter. *)

Inductive ModuleReference : Type :=
| RegistryReference : nat -> ModuleReference
| FileReference : nat -> ModuleReference.

Record Dependency : Type := {
  dependency_reference : ModuleReference;
  dependency_commitment : nat
}.

Record CanonicalRecord : Type := {
  record_reference : nat;
  record_commitment : nat;
  record_trusted : bool;
  record_canonical_bytes : nat;
  record_oracle_source : nat;
  record_cache_image : nat;
  record_dependencies : list Dependency
}.

Record ResolvedNode : Type := {
  resolved_record : CanonicalRecord;
  resolved_expected_commitment : nat;
  resolved_depth : nat;
  resolved_rank : nat
}.

Record ClosurePolicy : Type := {
  policy_max_modules : nat;
  policy_max_depth : nat;
  policy_max_record_bytes : nat;
  policy_max_total_bytes : nat
}.

Definition node_reference (node : ResolvedNode) : nat :=
  record_reference (resolved_record node).

Fixpoint lookup_node
    (reference : nat) (nodes : list ResolvedNode) : option ResolvedNode :=
  match nodes with
  | [] => None
  | node :: rest =>
      if Nat.eqb reference (node_reference node)
      then Some node
      else lookup_node reference rest
  end.

Definition locally_admitted
    (policy : ClosurePolicy) (node : ResolvedNode) : Prop :=
  record_trusted (resolved_record node) = true /\
  resolved_expected_commitment node = record_commitment (resolved_record node) /\
  resolved_depth node <= policy_max_depth policy /\
  record_canonical_bytes (resolved_record node) <= policy_max_record_bytes policy.

Definition dependency_admitted
    (nodes : list ResolvedNode) (parent : ResolvedNode)
    (dependency : Dependency) : Prop :=
  match dependency_reference dependency with
  | FileReference _ => False
  | RegistryReference reference =>
      exists child,
        lookup_node reference nodes = Some child /\
        record_commitment (resolved_record child) = dependency_commitment dependency /\
        resolved_rank child < resolved_rank parent
  end.

Definition closure_admitted
    (policy : ClosurePolicy) (nodes : list ResolvedNode) : Prop :=
  nodes <> [] /\
  length nodes <= policy_max_modules policy /\
  fold_right
    (fun node total => record_canonical_bytes (resolved_record node) + total)
    0 nodes <= policy_max_total_bytes policy /\
  NoDup (map node_reference nodes) /\
  Forall (locally_admitted policy) nodes /\
  Forall
    (fun parent =>
       Forall (dependency_admitted nodes parent)
         (record_dependencies (resolved_record parent)))
    nodes.

Theorem admitted_closure_is_nonempty_and_module_bounded :
  forall policy nodes,
    closure_admitted policy nodes ->
    nodes <> [] /\ length nodes <= policy_max_modules policy.
Proof.
  intros policy nodes [Hnonempty [Hcount _]]. auto.
Qed.

Theorem admitted_node_is_trusted_exact_and_locally_bounded :
  forall policy nodes node,
    closure_admitted policy nodes ->
    In node nodes ->
    record_trusted (resolved_record node) = true /\
    resolved_expected_commitment node = record_commitment (resolved_record node) /\
    resolved_depth node <= policy_max_depth policy /\
    record_canonical_bytes (resolved_record node) <= policy_max_record_bytes policy.
Proof.
  intros policy nodes node [_ [_ [_ [_ [Hall _]]]]] Hin.
  apply Forall_forall with (x := node) in Hall; assumption.
Qed.

Theorem admitted_closure_is_total_byte_bounded :
  forall policy nodes,
    closure_admitted policy nodes ->
    fold_right
      (fun node total => record_canonical_bytes (resolved_record node) + total)
      0 nodes <= policy_max_total_bytes policy.
Proof.
  intros policy nodes [_ [_ [Hbytes _]]]. exact Hbytes.
Qed.

Theorem admitted_dependency_is_registry_exact_and_rank_decreasing :
  forall policy nodes parent dependency,
    closure_admitted policy nodes ->
    In parent nodes ->
    In dependency (record_dependencies (resolved_record parent)) ->
    exists reference child,
      dependency_reference dependency = RegistryReference reference /\
      lookup_node reference nodes = Some child /\
      record_commitment (resolved_record child) = dependency_commitment dependency /\
      resolved_rank child < resolved_rank parent.
Proof.
  intros policy nodes parent dependency
    [_ [_ [_ [_ [_ Hall]]]]] Hparent Hdependency.
  apply Forall_forall with (x := parent) in Hall; [| exact Hparent].
  apply Forall_forall with (x := dependency) in Hall; [| exact Hdependency].
  unfold dependency_admitted in Hall.
  destruct (dependency_reference dependency) as [reference | path].
  - destruct Hall as [child [Hlookup [Hexact Hrank]]].
    exists reference, child. auto.
  - contradiction.
Qed.

Theorem admitted_closure_rejects_filesystem_dependencies :
  forall policy nodes parent dependency path,
    closure_admitted policy nodes ->
    In parent nodes ->
    In dependency (record_dependencies (resolved_record parent)) ->
    dependency_reference dependency = FileReference path ->
    False.
Proof.
  intros policy nodes parent dependency path Hadmitted Hparent Hdependency Hfile.
  destruct (admitted_dependency_is_registry_exact_and_rank_decreasing
    policy nodes parent dependency Hadmitted Hparent Hdependency)
    as [reference [child [Hregistry _]]].
  rewrite Hfile in Hregistry. discriminate.
Qed.

Theorem conflicting_commitments_for_one_reference_are_rejected :
  forall policy nodes left_parent right_parent left right reference,
    closure_admitted policy nodes ->
    In left_parent nodes ->
    In right_parent nodes ->
    In left (record_dependencies (resolved_record left_parent)) ->
    In right (record_dependencies (resolved_record right_parent)) ->
    dependency_reference left = RegistryReference reference ->
    dependency_reference right = RegistryReference reference ->
    dependency_commitment left = dependency_commitment right.
Proof.
  intros policy nodes left_parent right_parent left right reference
    Hadmitted Hleft_parent Hright_parent Hleft Hright Hleft_ref Hright_ref.
  destruct (admitted_dependency_is_registry_exact_and_rank_decreasing
    policy nodes left_parent left Hadmitted Hleft_parent Hleft)
    as [left_reference [left_child [Lref [Llookup [Lexact _]]]]].
  destruct (admitted_dependency_is_registry_exact_and_rank_decreasing
    policy nodes right_parent right Hadmitted Hright_parent Hright)
    as [right_reference [right_child [Rref [Rlookup [Rexact _]]]]].
  rewrite Hleft_ref in Lref. inversion Lref; subst left_reference.
  rewrite Hright_ref in Rref. inversion Rref; subst right_reference.
  rewrite Llookup in Rlookup. inversion Rlookup; subst right_child.
  lia.
Qed.

Lemma lookup_node_finds_a_unique_member :
  forall nodes node,
    NoDup (map node_reference nodes) ->
    In node nodes ->
    lookup_node (node_reference node) nodes = Some node.
Proof.
  intros nodes node Hnodup Hin.
  induction nodes as [| head rest IH]; [contradiction|].
  inversion Hnodup as [| mapped rest_mapped Hnotin Hrest];
    subst mapped rest_mapped.
  simpl in Hin. destruct Hin as [Heq | Hin].
  - subst head. simpl. rewrite Nat.eqb_refl. reflexivity.
  - simpl. destruct (Nat.eqb (node_reference node) (node_reference head)) eqn:Heq.
    + apply Nat.eqb_eq in Heq. exfalso. apply Hnotin.
      rewrite <- Heq. apply in_map. exact Hin.
    + apply IH; assumption.
Qed.

Theorem admitted_dependency_cannot_be_a_self_cycle :
  forall policy nodes parent dependency,
    closure_admitted policy nodes ->
    In parent nodes ->
    In dependency (record_dependencies (resolved_record parent)) ->
    dependency_reference dependency = RegistryReference (node_reference parent) ->
    False.
Proof.
  intros policy nodes parent dependency Hadmitted Hparent Hdependency Hself.
  destruct (admitted_dependency_is_registry_exact_and_rank_decreasing
    policy nodes parent dependency Hadmitted Hparent Hdependency)
    as [reference [child [Hreference [Hlookup [_ Hrank]]]]].
  rewrite Hself in Hreference. inversion Hreference; subst reference.
  assert (Hparent_lookup : lookup_node (node_reference parent) nodes = Some parent).
  { apply lookup_node_finds_a_unique_member; [| exact Hparent].
    destruct Hadmitted as [_ [_ [_ [Hnodup _]]]]. exact Hnodup. }
  rewrite Hparent_lookup in Hlookup. inversion Hlookup; subst child. lia.
Qed.

(** Source text is an optional development oracle.  Replacing it leaves the
    semantic projection used by resolution and installation unchanged. *)
Definition semantic_record (record : CanonicalRecord) :=
  (record_reference record,
   record_commitment record,
   record_trusted record,
   record_canonical_bytes record,
   record_dependencies record).

Definition replace_oracle_source
    (source : nat) (record : CanonicalRecord) : CanonicalRecord :=
  {| record_reference := record_reference record;
     record_commitment := record_commitment record;
     record_trusted := record_trusted record;
     record_canonical_bytes := record_canonical_bytes record;
     record_oracle_source := source;
     record_cache_image := record_cache_image record;
     record_dependencies := record_dependencies record |}.

Theorem oracle_source_is_not_semantic_authority :
  forall source record,
    semantic_record (replace_oracle_source source record) = semantic_record record.
Proof. reflexivity. Qed.

(** Parser images are derived, unsigned cache artifacts. Replacing even a
    malformed cache leaves the authoritative semantic record unchanged; the
    implementation either verifies the selected image or recompiles it from
    canonical content. *)
Definition replace_cache_image
    (cache : nat) (record : CanonicalRecord) : CanonicalRecord :=
  {| record_reference := record_reference record;
     record_commitment := record_commitment record;
     record_trusted := record_trusted record;
     record_canonical_bytes := record_canonical_bytes record;
     record_oracle_source := record_oracle_source record;
     record_cache_image := cache;
     record_dependencies := record_dependencies record |}.

Theorem parser_cache_is_not_semantic_authority :
  forall cache record,
    semantic_record (replace_cache_image cache record) = semantic_record record.
Proof. reflexivity. Qed.

Inductive PreparedBatch (Export : Type) : Type :=
| BatchRejected : PreparedBatch Export
| BatchPrepared : list Export -> PreparedBatch Export.

Inductive PublishedBatch (Export : Type) : Type :=
| NothingPublished : PublishedBatch Export
| EntireBatchPublished : list Export -> PublishedBatch Export.

Arguments BatchRejected {Export}.
Arguments BatchPrepared {Export} _.
Arguments NothingPublished {Export}.
Arguments EntireBatchPublished {Export} _.

Definition commit_batch {Export : Type}
    (prepared : PreparedBatch Export) : PublishedBatch Export :=
  match prepared with
  | BatchRejected => NothingPublished
  | BatchPrepared exports => EntireBatchPublished exports
  end.

Theorem rejected_batch_publishes_no_prefix :
  forall (Export : Type),
    commit_batch (@BatchRejected Export) = NothingPublished.
Proof. reflexivity. Qed.

Theorem prepared_batch_publishes_exactly_all_exports :
  forall (Export : Type) (exports : list Export),
    commit_batch (BatchPrepared exports) = EntireBatchPublished exports.
Proof. reflexivity. Qed.

Print Assumptions admitted_closure_is_nonempty_and_module_bounded.
Print Assumptions admitted_node_is_trusted_exact_and_locally_bounded.
Print Assumptions admitted_closure_is_total_byte_bounded.
Print Assumptions admitted_dependency_is_registry_exact_and_rank_decreasing.
Print Assumptions admitted_closure_rejects_filesystem_dependencies.
Print Assumptions conflicting_commitments_for_one_reference_are_rejected.
Print Assumptions admitted_dependency_cannot_be_a_self_cycle.
Print Assumptions oracle_source_is_not_semantic_authority.
Print Assumptions parser_cache_is_not_semantic_authority.
Print Assumptions rejected_batch_publishes_no_prefix.
Print Assumptions prepared_batch_publishes_exactly_all_exports.
