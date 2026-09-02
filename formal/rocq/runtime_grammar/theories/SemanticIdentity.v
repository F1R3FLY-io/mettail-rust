From Stdlib Require Import List PeanoNat.
Import ListNotations.

Inductive CollectionKind : Type :=
| ListKind
| BagKind
| SetKind
| MapKind
| PathMapKind.

Inductive Value : Type :=
| Atom : nat -> Value
| Term : nat -> nat -> list Value -> nat -> nat -> Value
| Sequence : list Value -> Value
| Collection : CollectionKind -> list Value -> Value.

Fixpoint erase_source_spans (value : Value) : Value :=
  match value with
  | Atom atom => Atom atom
  | Term category constructor fields _ _ =>
      Term category constructor (map erase_source_spans fields) 0 0
  | Sequence values => Sequence (map erase_source_spans values)
  | Collection kind entries =>
      Collection kind (map erase_source_spans entries)
  end.

Definition semantic_key (value : Value) : Value := erase_source_spans value.

Theorem term_semantic_key_ignores_source_span :
  forall category constructor fields start_a end_a start_b end_b,
    semantic_key (Term category constructor fields start_a end_a) =
    semantic_key (Term category constructor fields start_b end_b).
Proof. reflexivity. Qed.

Definition map_keys_unique (entries : list (Value * Value)) : Prop :=
  NoDup (map (fun entry => semantic_key (fst entry)) entries).

Theorem duplicate_semantic_map_keys_are_rejected :
  forall key_a value_a key_b value_b,
    semantic_key key_a = semantic_key key_b ->
    ~ map_keys_unique [(key_a, value_a); (key_b, value_b)].
Proof.
  intros key_a value_a key_b value_b Hequal Hunique.
  unfold map_keys_unique in Hunique. simpl in Hunique.
  inversion Hunique as [| key rest Hnotin Htail].
  apply Hnotin. simpl. left. symmetry. exact Hequal.
Qed.

Print Assumptions term_semantic_key_ignores_source_span.
Print Assumptions duplicate_semantic_map_keys_are_rejected.
