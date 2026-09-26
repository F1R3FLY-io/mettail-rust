(** Runtime image compilation selects Unicode atom semantics already required
    by the independent image verifier. The original macro entry selects Bytes.

    Rust reuses the original parser/Thompson driver and the existing UTF-8
    range emitters: there is no new lexer, source rewrite, or grammar reparse.
    Scalar shorthand ranges are supplied by the same regex_syntax class
    resolver used for Unicode properties, from fixed shorthand patterns.

    This boundary model proves profile selection and unchanged worker calls,
    not correctness of regex_syntax or Utf8Sequences. Output may include state
    and an observation trace. Independent full-language image verification and
    original-byte regression tests are the concrete correspondence obligations.
*)
From Stdlib Require Import List Bool Arith.
Import ListNotations.
Module RegexCharacterProfile.

Inductive Profile := Bytes | Unicode.
Definition class_uses_scalar profile original_unicode :=
  match profile with Bytes => original_unicode | Unicode => true end.

Section WorkerSubstitution.
Context {Input Output : Type}.
Variables byte_worker scalar_worker : Input -> Output.
Definition emit_atom profile input :=
  match profile with
  | Bytes => byte_worker input
  | Unicode => scalar_worker input
  end.
Definition emit_class profile original_unicode input :=
  if class_uses_scalar profile original_unicode
  then scalar_worker input else byte_worker input.

Theorem original_entry_is_unchanged : forall input,
  emit_atom Bytes input = byte_worker input.
Proof. reflexivity. Qed.
Theorem runtime_calls_existing_scalar_worker : forall input,
  emit_atom Unicode input = scalar_worker input.
Proof. reflexivity. Qed.
Theorem original_class_choice_is_unchanged : forall flag input,
  emit_class Bytes flag input =
  (if flag then scalar_worker input else byte_worker input).
Proof. reflexivity. Qed.
Theorem runtime_class_uses_existing_scalar_path : forall flag input,
  emit_class Unicode flag input = scalar_worker input.
Proof. reflexivity. Qed.
Theorem explicit_unicode_class_is_profile_independent : forall profile input,
  emit_class profile true input = scalar_worker input.
Proof. intros []; reflexivity. Qed.
End WorkerSubstitution.

(** A byte atom consumes one byte. A scalar atom consumes one supplied UTF-8
    encoding. This witness explains why valid-input restriction alone cannot
    repair the original verifier mismatch: e-acute is a two-byte encoding. *)
Definition byte_atom (bytes : list nat) := Nat.eqb (length bytes) 1.
Definition supplied_scalar_atom (encoding bytes : list nat) := bytes = encoding.
Example dot_profiles_differ_on_valid_utf8 :
  byte_atom [195;169] = false /\ supplied_scalar_atom [195;169] [195;169].
Proof. split; reflexivity. Qed.

Print Assumptions original_entry_is_unchanged.
Print Assumptions runtime_calls_existing_scalar_worker.
Print Assumptions original_class_choice_is_unchanged.
Print Assumptions runtime_class_uses_existing_scalar_path.
Print Assumptions explicit_unicode_class_is_profile_independent.
Print Assumptions dot_profiles_differ_on_valid_utf8.
End RegexCharacterProfile.
