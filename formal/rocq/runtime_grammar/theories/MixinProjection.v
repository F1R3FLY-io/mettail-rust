From Stdlib Require Import Bool List.
Import ListNotations.

(** Runtime [mixins] must implement the same grammar-fragment projection as
    compile-time [language_fragment!].  A mixin contributes declarations that
    affect recognition and construction; it contributes neither semantic
    programs nor requested authority. *)
Inductive Field : Type :=
| Options
| Rights
| Semantics
| Types
| Literals
| Tokens
| Modes
| Synchronization
| TreeInvariants
| Guards
| Terms
| Equations
| Rewrites
| Relations
| Oslf
| Exports
| Context
| Documentation.

Definition field_eq_dec : forall left right : Field, {left = right} + {left <> right}.
Proof. decide equality. Defined.

(** [Literals] are lexer declarations in the canonical data form.  The Rust
    fragment surface spells the same contribution through token declarations,
    but retaining this field makes the projection representation-independent. *)
Definition is_mixin_grammar_field (field : Field) : bool :=
  match field with
  | Types | Literals | Tokens | Modes | Terms => true
  | _ => false
  end.

Definition project_mixin {A : Type} (fields : list (Field * A)) : list (Field * A) :=
  filter (fun entry => is_mixin_grammar_field (fst entry)) fields.

Theorem projection_retains_every_grammar_field :
  forall (A : Type) (field : Field) (value : A) fields,
    is_mixin_grammar_field field = true ->
    In (field, value) fields ->
    In (field, value) (project_mixin fields).
Proof.
  intros A field value fields Hfield Hin.
  unfold project_mixin.
  apply filter_In. split; assumption.
Qed.

Theorem projection_excludes_every_non_grammar_field :
  forall (A : Type) (field : Field) (value : A) fields,
    is_mixin_grammar_field field = false ->
    ~ In (field, value) (project_mixin fields).
Proof.
  intros A field value fields Hfield Hin.
  unfold project_mixin in Hin.
  apply filter_In in Hin.
  destruct Hin as [_ Hkept].
  cbn in Hkept.
  rewrite Hfield in Hkept. discriminate.
Qed.

Theorem projection_never_retains_requested_rights :
  forall (A : Type) (value : A) fields,
    ~ In (Rights, value) (project_mixin fields).
Proof.
  intros. eapply projection_excludes_every_non_grammar_field; reflexivity.
Qed.

Theorem projection_retains_custom_tokens :
  forall (A : Type) (value : A) fields,
    In (Tokens, value) fields ->
    In (Tokens, value) (project_mixin fields).
Proof.
  intros. eapply projection_retains_every_grammar_field; [reflexivity | assumption].
Qed.

Theorem projection_retains_lexer_modes :
  forall (A : Type) (value : A) fields,
    In (Modes, value) fields ->
    In (Modes, value) (project_mixin fields).
Proof.
  intros. eapply projection_retains_every_grammar_field; [reflexivity | assumption].
Qed.

Theorem projection_is_idempotent :
  forall (A : Type) (fields : list (Field * A)),
    project_mixin (project_mixin fields) = project_mixin fields.
Proof.
  intros A fields.
  unfold project_mixin.
  induction fields as [| [field value] rest IH]; simpl; [reflexivity |].
  destruct (is_mixin_grammar_field field) eqn:Hkeep.
  - simpl. rewrite Hkeep, IH. reflexivity.
  - simpl. exact IH.
Qed.

Theorem projection_preserves_declaration_order :
  forall (A : Type) (left right : list (Field * A)),
    project_mixin (left ++ right) = project_mixin left ++ project_mixin right.
Proof.
  intros A left right.
  unfold project_mixin.
  apply filter_app.
Qed.

Print Assumptions projection_retains_every_grammar_field.
Print Assumptions projection_excludes_every_non_grammar_field.
Print Assumptions projection_never_retains_requested_rights.
Print Assumptions projection_retains_custom_tokens.
Print Assumptions projection_retains_lexer_modes.
Print Assumptions projection_is_idempotent.
Print Assumptions projection_preserves_declaration_order.
