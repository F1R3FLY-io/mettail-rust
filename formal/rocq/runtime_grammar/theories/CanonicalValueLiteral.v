From Stdlib Require Import List Bool PeanoNat.
Import ListNotations.

(** Lists and maps use explicit cons constructors so Rocq's kernel can see the
    same decreasing spine that the Rust emitter stores in its heap worklist. *)
Inductive Value : Type :=
| VNil
| VBool (value : bool)
| VInteger (value : nat)
| VString (value : list nat)
| VBytes (value : list nat)
| VListNil
| VListCons (head tail : Value)
| VMapNil
| VMapCons (key : list nat) (value rest : Value).

Inductive Surface : Type :=
| SNil
| SBool (value : bool)
| SInteger (value : nat)
| SString (escaped : list nat)
| SBytes (hex_pairs : list nat)
| SListNil
| SListCons (head tail : Surface)
| SMapNil
| SMapCons (escaped_key : list nat) (value rest : Surface).

(** Quote and backslash escaping is proven at the character level in
    [StringLiteralTransducer.v].  Here [escape] is its injective framing at the
    structural surface boundary. *)
Definition escape (value : list nat) : list nat := 0 :: value.

Definition unescape (value : list nat) : option (list nat) :=
  match value with
  | 0 :: rest => Some rest
  | _ => None
  end.

Fixpoint render (value : Value) : Surface :=
  match value with
  | VNil => SNil
  | VBool value => SBool value
  | VInteger value => SInteger value
  | VString value => SString (escape value)
  | VBytes value => SBytes value
  | VListNil => SListNil
  | VListCons head tail => SListCons (render head) (render tail)
  | VMapNil => SMapNil
  | VMapCons key value rest =>
      SMapCons (escape key) (render value) (render rest)
  end.

Fixpoint parse (surface : Surface) : option Value :=
  match surface with
  | SNil => Some VNil
  | SBool value => Some (VBool value)
  | SInteger value => Some (VInteger value)
  | SString value =>
      match unescape value with
      | Some decoded => Some (VString decoded)
      | None => None
      end
  | SBytes value => Some (VBytes value)
  | SListNil => Some VListNil
  | SListCons head tail =>
      match parse head, parse tail with
      | Some decoded_head, Some decoded_tail =>
          Some (VListCons decoded_head decoded_tail)
      | _, _ => None
      end
  | SMapNil => Some VMapNil
  | SMapCons key value rest =>
      match unescape key, parse value, parse rest with
      | Some decoded_key, Some decoded_value, Some decoded_rest =>
          Some (VMapCons decoded_key decoded_value decoded_rest)
      | _, _, _ => None
      end
  end.

Lemma unescape_escape :
  forall value, unescape (escape value) = Some value.
Proof. reflexivity. Qed.

Theorem parse_render_round_trip :
  forall value, parse (render value) = Some value.
Proof.
  intros value. induction value; simpl; try reflexivity;
    rewrite ?IHvalue1, ?IHvalue2; reflexivity.
Qed.

Theorem list_source_order_is_preserved :
  forall head tail,
    render (VListCons head tail) = SListCons (render head) (render tail).
Proof. reflexivity. Qed.

Theorem map_source_order_is_preserved :
  forall key value rest,
    render (VMapCons key value rest) =
      SMapCons (escape key) (render value) (render rest).
Proof. reflexivity. Qed.

Print Assumptions unescape_escape.
Print Assumptions parse_render_round_trip.
Print Assumptions list_source_order_is_preserved.
Print Assumptions map_source_order_is_preserved.
