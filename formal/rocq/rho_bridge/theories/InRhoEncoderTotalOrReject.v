(*
 * InRhoEncoderTotalOrReject.v — FV (ix) for the Stage 3 in-Rho matching encoder.
 *
 * The Stage 3 encoder (`compile_in_rho_matching_ruleset`, rholang-codegen
 * `rho_net_ruleset.rs`) partitions a language's rewrites: a rewrite is MATCHED in Rho
 * (an automaton entry) iff it is a base rewrite with a σ-receiver site AND its LHS
 * converts structurally AND compiles AC-free; every other rewrite is DEFERRED with a
 * reason (NotBaseRewrite / Convert / Ac). This theory proves that partition is TOTAL
 * (nothing dropped), SOUND (nothing fabricated), DISJOINT (classified exactly once),
 * and that the capability GATE admits in-Rho matching iff every FIRED rule is
 * matchable — the companion, at the in-Rho encoder, to RhoLoweringTotalOrRejects's
 * `RhoNetInstallBoundary` (which carries the same invariant to the σ-receiver install).
 *
 * It also proves PERSISTENCE: the per-firing (network ‖ spread) call is transient
 * (single-shot receives, zero persistent inputs), so appending it to the installed
 * σ-receiver program preserves the program's persistent-input count — the installed
 * contracts stay the only persistent state (in_rho_match_call_par, Stage 3 piece 3).
 *
 * Boundary (doc 16 sect 2.1): this is the RULE-CLASSIFICATION layer — the encoder
 * misses nothing and admits closed. It does NOT re-prove matching correctness (that is
 * (i)/(ii)/(iii), Phases A-C); it proves the WIRING around them is fail-closed and
 * persistence-preserving, which is Stage 3's new surface.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

Section InRhoEncoderTotalOrReject.

  Variable Rewrite : Type.

  (* The three encoder predicates (rholang-codegen `rho_net_ruleset.rs`):
     - `has_site r`  : the rewrite lowered to a base-rewrite σ-receiver, so
       `rho_net_injection_sites` surfaces an injection site (congruence / unsafe-premise
       / AC / binder rules have none → `DeferReason::NotBaseRewrite`).
     - `converts r`  : `convert_lhs_pattern` returns `Ok` (Var/Apply only — no
       binder/subst/search → `DeferReason::Convert`).
     - `compiles_free r` : `compile_structural` accepts it (not an `AcApp` →
       `DeferReason::Ac`). *)
  Variable has_site : Rewrite -> bool.
  Variable converts : Rewrite -> bool.
  Variable compiles_free : Rewrite -> bool.

  (* Matched in Rho iff all three hold — an `InRhoMatchingRuleset` automaton entry. *)
  Definition in_rho (r : Rewrite) : bool :=
    has_site r && converts r && compiles_free r.

  (* The encoder's partition (mirrors compile_in_rho_matching_ruleset's automaton
     entries vs its `deferred` list). *)
  Definition matched (rules : list Rewrite) : list Rewrite := filter in_rho rules.
  Definition deferred (rules : list Rewrite) : list Rewrite :=
    filter (fun r => negb (in_rho r)) rules.

  (* TOTAL: every rewrite is matched in Rho or deferred. Nothing dropped. *)
  Theorem encoder_total : forall rules r,
    In r rules -> In r (matched rules) \/ In r (deferred rules).
  Proof.
    intros rules r Hin. unfold matched, deferred.
    destruct (in_rho r) eqn:Hr.
    - left. apply filter_In. split; [exact Hin | exact Hr].
    - right. apply filter_In. split; [exact Hin | rewrite Hr; reflexivity].
  Qed.

  (* SOUND: only real rewrites are classified — nothing fabricated. *)
  Theorem encoder_sound : forall rules r,
    In r (matched rules) \/ In r (deferred rules) -> In r rules.
  Proof.
    intros rules r [H | H]; unfold matched, deferred in H;
      apply filter_In in H; destruct H as [Hin _]; exact Hin.
  Qed.

  (* DISJOINT: no rewrite is both matched and deferred (classified exactly once). *)
  Theorem encoder_disjoint : forall rules r,
    In r (matched rules) -> In r (deferred rules) -> False.
  Proof.
    intros rules r Hm Hd. unfold matched, deferred in *.
    apply filter_In in Hm. apply filter_In in Hd.
    destruct Hm as [_ Hr]. destruct Hd as [_ Hnr].
    rewrite Hr in Hnr. simpl in Hnr. discriminate Hnr.
  Qed.

  (* EXACT PARTITION: the two parts' sizes sum to the whole (the FV form of piece 2's
     `every rewrite appears exactly once` property test). *)
  Theorem encoder_count : forall rules,
    length (matched rules) + length (deferred rules) = length rules.
  Proof.
    unfold matched, deferred.
    induction rules as [| r rules IH]; simpl; [reflexivity |].
    destruct (in_rho r); simpl; lia.
  Qed.

  (* CHARACTERIZATION: matched iff in the input and `in_rho` (the gate is decidable and
     complete). *)
  Theorem matched_iff_in_rho : forall rules r,
    In r (matched rules) <-> (In r rules /\ in_rho r = true).
  Proof. intros. unfold matched. apply filter_In. Qed.

  (* The capability gate (Stage 3 piece 5): a language admits in-Rho matching iff no
     FIRED rule is deferred — equivalently, every fired rule is matchable in Rho. *)
  Variable fires : Rewrite -> bool.
  Definition install_admits (rules : list Rewrite) : bool :=
    forallb (fun r => negb (fires r && negb (in_rho r))) rules.

  Theorem gate_admits_iff_all_fired_matchable : forall rules,
    install_admits rules = true <->
      (forall r, In r rules -> fires r = true -> in_rho r = true).
  Proof.
    intros rules. unfold install_admits. rewrite forallb_forall. split.
    - intros Hall r Hin Hf.
      specialize (Hall r Hin).
      apply negb_true_iff in Hall.
      apply andb_false_iff in Hall.
      destruct Hall as [Hf' | Hnr].
      + rewrite Hf in Hf'. discriminate.
      + apply negb_false_iff in Hnr. exact Hnr.
    - intros Hall r Hin.
      apply negb_true_iff. apply andb_false_iff.
      destruct (fires r) eqn:Hf.
      + right. apply negb_false_iff. apply Hall; [exact Hin | exact Hf].
      + left. reflexivity.
  Qed.

End InRhoEncoderTotalOrReject.

(* Zero-admission witnesses (the section variables become explicit theorem arguments,
   not axioms — each is "Closed under the global context"). *)
Print Assumptions encoder_total.
Print Assumptions encoder_count.
Print Assumptions gate_admits_iff_all_fired_matchable.

Section InRhoCallPersistence.

  (* The installed σ-receiver program and the per-firing call are processes; a process
     has a count of PERSISTENT inputs (persistent `for`/contract receives). *)
  Variable Process : Type.
  Variable persistent_inputs : Process -> nat.
  Variable par : Process -> Process -> Process.

  (* Parallel composition sums persistent inputs (the process-algebra `‖`). *)
  Hypothesis par_sums_persistent_inputs :
    forall p q, persistent_inputs (par p q) = persistent_inputs p + persistent_inputs q.

  (* The per-firing (network ‖ spread) call is TRANSIENT: the M2a receivers are
     single-shot (`for_receive` is a non-persistent `Receive`) and the spread is a
     one-shot scaffold, so it introduces zero persistent inputs. *)
  Variable call : Process.
  Hypothesis call_is_transient : persistent_inputs call = 0.

  (* PERSISTENCE: appending the per-firing call to the installed program preserves the
     program's persistent-input count — the installed σ-receivers stay the ONLY
     persistent state (no in-Rho matching receiver leaks into the persistent install,
     which is why the network correctly rides the call, not `installed_program_par`). *)
  Theorem appending_the_call_preserves_persistent_inputs : forall installed,
    persistent_inputs (par installed call) = persistent_inputs installed.
  Proof.
    intros installed. rewrite par_sums_persistent_inputs, call_is_transient.
    apply Nat.add_0_r.
  Qed.

End InRhoCallPersistence.

Print Assumptions appending_the_call_preserves_persistent_inputs.
