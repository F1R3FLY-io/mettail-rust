(*
 * RhoLoweringTotalOrRejects: the M-RHO.0.3 spec→Rholang AST lowering
 * (`rholang-codegen` `lower_language_def`) MISSES NOTHING at the codegen
 * layer — every rule of a `LanguageDef` is accounted for: each is EITHER lowered
 * to a normalized Rho contract artifact OR explicitly recorded as rejected (out
 * of the supported scalar-operator subset). No rule is ever silently dropped, and none is
 * fabricated.
 *
 * Model: a rule classifier `supported : Rule -> bool` (the Rust `lower_rule`
 * returning `Some`/`None` — `Some` iff the rule's concrete syntax is a supported
 * infix/prefix operator AND its operands are Rholang-native scalars). The Rust
 * `lower_language_def` partitions `def.terms` into `lowered` (supported) and
 * `rejected` (the rest). We model that partition as `filter` and prove:
 *   - lowering_total    : every rule is in lowered ∪ rejected (nothing dropped),
 *   - lowering_sound    : lowered ∪ rejected ⊆ the rules (nothing fabricated),
 *   - lowering_disjoint : lowered ∩ rejected = ∅ (each rule classified once),
 *   - lowering_count    : |lowered| + |rejected| = |rules| (exact partition),
 *   - lowered/rejected characterized by `supported`.
 *
 * This is the codegen-layer instance of the engine's governing "MISS NOTHING"
 * invariant (cf. dovetail NBestExtraction.v / EnumerationCompleteness.v at the
 * extraction layer): an alternative leaves only by EVIDENCE (here: an explicit
 * "no Rholang equivalent" rejection), never by silent omission.
 *
 * `Section RhoNetInstallBoundary` (Epic 4 #2011) carries the SAME invariant to the
 * σ-receiver INSTALL boundary (`rholang-codegen` `RhoNetLowered::installed_program_par`
 * → `Result<Par, RhoNetInstallError>`): the installed program admits a rule only if
 * it materialized a contract or is legitimately inline; any unlowered/deferred rule
 * (`ContextualRewrite`/`Comm`/`NativeSystemProcess`/`Unsupported`) fails the install
 * CLOSED — by evidence (an install error, at install time), never a silent runtime
 * no-op after partial execution on the Rho machine.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

Section RhoLoweringTotalOrRejects.

  Variable Rule : Type.
  (* `supported r = true` iff `lower_rule r` returns `Some` (a normalized Rho contract). *)
  Variable supported : Rule -> bool.

  (* The Rust `lower_language_def` partition, modelled as filters over `def.terms`. *)
  Definition lowered (rules : list Rule) : list Rule := filter supported rules.
  Definition rejected (rules : list Rule) : list Rule :=
    filter (fun r => negb (supported r)) rules.

  (* TOTAL: every rule is classified — lowered or rejected. Nothing dropped. *)
  Theorem lowering_total : forall rules r,
    In r rules -> In r (lowered rules) \/ In r (rejected rules).
  Proof.
    intros rules r Hin. unfold lowered, rejected.
    destruct (supported r) eqn:Hs.
    - left. apply filter_In. split; [exact Hin | exact Hs].
    - right. apply filter_In. split; [exact Hin | rewrite Hs; reflexivity].
  Qed.

  (* SOUND: only real rules are classified — nothing fabricated. *)
  Theorem lowering_sound : forall rules r,
    In r (lowered rules) \/ In r (rejected rules) -> In r rules.
  Proof.
    intros rules r [H | H]; unfold lowered, rejected in H;
      apply filter_In in H; destruct H as [Hin _]; exact Hin.
  Qed.

  (* DISJOINT: no rule is both lowered and rejected (classified exactly once). *)
  Theorem lowering_disjoint : forall rules r,
    In r (lowered rules) -> In r (rejected rules) -> False.
  Proof.
    intros rules r Hl Hr. unfold lowered, rejected in *.
    apply filter_In in Hl. apply filter_In in Hr.
    destruct Hl as [_ Hs]. destruct Hr as [_ Hns].
    rewrite Hs in Hns. simpl in Hns. discriminate Hns.
  Qed.

  (* EXACT PARTITION: the two parts' sizes sum to the whole. *)
  Theorem lowering_count : forall rules,
    length (lowered rules) + length (rejected rules) = length rules.
  Proof.
    induction rules as [| r rs IH].
    - reflexivity.
    - unfold lowered, rejected in *. simpl. destruct (supported r); simpl; lia.
  Qed.

  (* CHARACTERIZATION: lowered = exactly the supported rules; rejected = the rest. *)
  Theorem lowered_iff_supported : forall rules r,
    In r (lowered rules) <-> (In r rules /\ supported r = true).
  Proof.
    intros rules r. unfold lowered. apply filter_In.
  Qed.

  Theorem rejected_iff_unsupported : forall rules r,
    In r (rejected rules) <-> (In r rules /\ supported r = false).
  Proof.
    intros rules r. unfold rejected. rewrite filter_In.
    split; intros [Hin Hb].
    - split; [exact Hin | apply negb_true_iff in Hb; exact Hb].
    - split; [exact Hin | apply negb_true_iff; exact Hb].
  Qed.

End RhoLoweringTotalOrRejects.

Section RhoNetInstallBoundary.

  (* Epic 4 #2011: the σ-receiver INSTALL boundary
     (`RhoNetLowered::installed_program_par`) is fail-closed. A lowered rule either
     MATERIALIZES an installed contract / is legitimately inline (`blocks_install =
     false`), or it is a diagnostic / deferred family that installing would SILENTLY
     DROP (`blocks_install = true`). The Rust boundary returns `Ok` iff no rule
     blocks — otherwise `Err(RhoNetInstallError)`. This is the runtime-facing dual of
     the codegen partition above: nothing is silently dropped from the installed
     program; an incomplete lowering leaves only by EVIDENCE, at install time. *)

  Variable Rule : Type.
  (* `blocks_install r = true` iff installing would silently omit unlowered work —
     Rust `ContextualRewrite | Comm | NativeSystemProcess | Unsupported`, or any
     recorded `RhoNetLoweringError`. `false` for materialized `NativeFold`/
     `BaseRewrite` and legitimately-inline `StructuralConstructor`/
     `CongruenceClosure`. *)
  Variable blocks_install : Rule -> bool.

  (* `installed_program_par` returns Ok iff no rule blocks the install. *)
  Definition install_ok (rules : list Rule) : bool :=
    forallb (fun r => negb (blocks_install r)) rules.

  (* FAIL-CLOSED: a successful install proves NO rule was silently dropped. *)
  Theorem install_ok_drops_nothing : forall rules r,
    install_ok rules = true -> In r rules -> blocks_install r = false.
  Proof.
    intros rules r Hok Hin. unfold install_ok in Hok.
    rewrite forallb_forall in Hok. specialize (Hok r Hin).
    rewrite negb_true_iff in Hok. exact Hok.
  Qed.

  (* VISIBLE AT INSTALL TIME: any blocking rule fails the install closed — the
     error surfaces at the boundary, never after partial execution. *)
  Theorem blocking_rule_fails_install_closed : forall rules r,
    In r rules -> blocks_install r = true -> install_ok rules = false.
  Proof.
    intros rules r Hin Hblock. unfold install_ok.
    destruct (forallb (fun r => negb (blocks_install r)) rules) eqn:E; [| reflexivity].
    rewrite forallb_forall in E. specialize (E r Hin).
    rewrite Hblock in E. simpl in E. discriminate E.
  Qed.

  (* CHARACTERIZATION: install succeeds exactly when every rule is non-blocking. *)
  Theorem install_ok_iff : forall rules,
    install_ok rules = true <-> (forall r, In r rules -> blocks_install r = false).
  Proof.
    intros rules. unfold install_ok. rewrite forallb_forall.
    split; intros H r Hin; specialize (H r Hin).
    - rewrite negb_true_iff in H. exact H.
    - rewrite negb_true_iff. exact H.
  Qed.

End RhoNetInstallBoundary.

Print Assumptions install_ok_drops_nothing.
Print Assumptions blocking_rule_fails_install_closed.
Print Assumptions install_ok_iff.
