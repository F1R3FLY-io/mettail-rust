(** An optional authored carrier is a category attribute, orthogonal to
    variable admission. The bare legacy type value is retained exactly when
    there is no carrier annotation and variables remain admitted. Any richer
    declaration uses the existing canonical type map; it does not introduce a
    new grammar-core carrier or a second authoring schema.

    This is the declaration-to-value law. Rust tests must additionally check
    the generated host AST, structural wire, schema validation, and core
    lowering against the accepted native-carrier vocabulary. *)
From Stdlib Require Import Bool String.

Module TypeCarrierProjection.

Inductive Carrier :=
| Native (spelling : string)
| Collection (kind key : string) (value : option string)
| External (urn : string).

(** Most carrier spellings arrive as identifiers. The host language already
    reserves [bool] for its conversion operator, so the same spelling has an
    explicit fixed-token route in the DDL grammar. Both routes project to the
    existing native-carrier string without introducing a new carrier kind. *)
Inductive CarrierToken :=
| IdentifierCarrier (spelling : string)
| BoolKeywordCarrier.

Definition carrier_token_spelling (token : CarrierToken) : string :=
  match token with
  | IdentifierCarrier spelling => spelling
  | BoolKeywordCarrier => "bool"
  end.

Record Declaration := {
  name : string;
  admits_variables : bool;
  carrier : option Carrier
}.

Inductive CanonicalType :=
| Bare (name : string)
| Detailed (name : string) (admits_variables : bool)
    (carrier : option Carrier).

Definition encode (declaration : Declaration) : CanonicalType :=
  match admits_variables declaration, carrier declaration with
  | true, None => Bare (name declaration)
  | admitted, selected => Detailed (name declaration) admitted selected
  end.

Definition decode (value : CanonicalType) : Declaration :=
  match value with
  | Bare category => {| name := category; admits_variables := true;
                        carrier := None |}
  | Detailed category admitted selected =>
      {| name := category; admits_variables := admitted;
         carrier := selected |}
  end.

Theorem declaration_round_trip : forall declaration,
  decode (encode declaration) = declaration.
Proof.
  intros [category admitted selected].
  destruct admitted, selected; reflexivity.
Qed.

Theorem legacy_bare_form_is_unchanged : forall category,
  encode {| name := category; admits_variables := true;
            carrier := None |} = Bare category.
Proof. reflexivity. Qed.

Theorem closed_native_category_preserves_both_attributes :
  forall category spelling,
    decode (encode {| name := category; admits_variables := false;
                      carrier := Some (Native spelling) |}) =
    {| name := category; admits_variables := false;
       carrier := Some (Native spelling) |}.
Proof. reflexivity. Qed.

Theorem fixed_bool_token_projects_to_existing_native_carrier :
  forall category admitted,
    encode {| name := category; admits_variables := admitted;
              carrier := Some (Native (carrier_token_spelling BoolKeywordCarrier)) |} =
    Detailed category admitted (Some (Native "bool")).
Proof. intros category admitted; destruct admitted; reflexivity. Qed.

Theorem carrier_annotation_does_not_change_variable_admission :
  forall category admitted selected,
    admits_variables
      (decode (encode {| name := category; admits_variables := admitted;
                         carrier := selected |})) = admitted.
Proof. intros; rewrite declaration_round_trip; reflexivity. Qed.

Theorem noadmit_does_not_change_carrier :
  forall category selected,
    carrier
      (decode (encode {| name := category; admits_variables := false;
                         carrier := selected |})) = selected.
Proof. intros; rewrite declaration_round_trip; reflexivity. Qed.

End TypeCarrierProjection.
