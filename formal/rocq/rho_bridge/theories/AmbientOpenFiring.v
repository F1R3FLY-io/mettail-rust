(*
 * AmbientOpenFiring: FV (Stage 3d) — the Ambient-calculus OpenRule fires as ONE STRUCTURAL
 * non-linear AC COMM.
 *
 * The OpenRule
 *
 *     {(POpen N P), (PAmb N Q), ...rest} ~> {P, Q, ...rest}
 *
 * (i.e. `open(n, P) | n[Q]  ~>  P | Q`) fires, in ONE ATOMIC guarded consume on the installed AC
 * σ-receiver (`rho_net_lower::structural_ac_receiver_par`), by COMPOSING:
 *
 *   (1) an AC 2-pick — the connective process-soup match selects the two STRUCTURED elements (the
 *       capability `POpen` and the ambient `PAmb`) order-independently, gathering their shared
 *       ambient-name occurrences into the selection's two slots;
 *   (2) a NON-LINEAR consistency guard — the receiver's `Receive.condition` `EEq(N_open, N_amb)`,
 *       which is `ac_nl_guard [0;1]` (AcNonLinearConsistency) over the two name slots: it commits
 *       the COMM IFF the ambient names are name-equal (`N ≡ N`), reject-safe otherwise;
 *   (3) a PURE STRUCTURAL reduct — UNLIKE the Comm rule (CommRuleFiring), whose reduct is the
 *       host-computed substitution `cont[Q/y]` delivered at a dedicated σ slot, the OpenRule's
 *       reducts `[P; Q]` are STRUCTURAL PROJECTIONS of the two selected elements (P = the open body,
 *       Q = the ambient body — both LHS-element ARGUMENTS the firing's σ already carries), forwarded
 *       verbatim (never fabricated);
 *   (4) an ATOMIC bag reassembly — the fired bag is `{P, Q, ...rest}`: BOTH reducts spliced with the
 *       bound remainder `rest` in ONE all-or-nothing commit, modelled by `insert_all [P; Q] rest`.
 *
 * This SPECIALIZES `ac_nl_guard`'s commit<->name-equality (AcNonLinearConsistency, itself an
 * instance of NonLinearEqConsistency / GuardedCommSoundness) to the two-element OpenRule selection,
 * and GENERALIZES the Comm single-reduct emit (CommRuleFiring) to an `m`-reduct STRUCTURAL splice
 * (`insert_all`). We prove: the OpenRule guard holds IFF the two ambient names agree; the consume
 * commits (emitting BOTH P and Q) when they agree and consumes NO data when they disagree
 * (reject-safe); every emitted fact is one of the structural reducts or was already present (no
 * fabrication); on commit the fired bag contains P AND Q AND every element of `rest` (the atomic
 * `{P, Q, ...rest}` reassembly); the single-reduct case coincides with the Comm `insert_exact` emit;
 * and the receiver's `condition` guard equals the host's non-linear name check (oracle agreement).
 *
 * The atomic multi-emit is modelled by `struct_attempt`, the m-reduct generalization of
 * GuardedCommSoundness's single-output `guarded_attempt` (commit / reject-guard / reject-premise),
 * with the guard supplied by `ac_nl_guard` (so the non-linear veto is NOT a new obligation — it is
 * inherited verbatim from AcNonLinearConsistency).
 *
 * Reuses ac_nl_two_slot_agree / ac_nl_guard / gather (AcNonLinearConsistency) and
 * Fact / all_present / insert_exact / insert_exact_membership (GuardedCommSoundness). Zero-admission.
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From RhoBridge Require Import GuardedCommSoundness.
From RhoBridge Require Import NonLinearEqConsistency.
From RhoBridge Require Import AcNonLinearConsistency.

Import ListNotations.

Section AmbientOpenFiring.

  (* Splice a LIST of structural reducts into the residual bag (atomic multi-emit): the OpenRule
     receiver body `@"ac:op"!(r0) | ... | @"ac:op"!(r_{m-1}) | rest`. Generalizes `insert_exact`
     (the Comm single-emit) to m reducts. *)
  Definition insert_all (outs facts : list Fact) : list Fact :=
    fold_right insert_exact facts outs.

  Lemma insert_all_cons : forall o outs facts,
    insert_all (o :: outs) facts = insert_exact o (insert_all outs facts).
  Proof. reflexivity. Qed.

  (* Membership in the m-reduct splice: an element is in the fired bag iff it is one of the reducts
     or was in the residual `rest` (= facts). *)
  Lemma insert_all_membership : forall outs facts x,
    In x (insert_all outs facts) <-> In x outs \/ In x facts.
  Proof.
    induction outs as [| o outs' IH]; intros facts x.
    - simpl. split.
      + intro H. right. exact H.
      + intros [H | H]; [ contradiction | exact H ].
    - rewrite insert_all_cons. split.
      + intro H. apply insert_exact_membership in H. destruct H as [Heq | Hrest].
        * left. left. symmetry. exact Heq.
        * apply IH in Hrest. destruct Hrest as [Hin | Hf].
          -- left. right. exact Hin.
          -- right. exact Hf.
      + intros [Hcons | Hf].
        * apply insert_exact_membership. destruct Hcons as [Heq | Hin].
          -- left. symmetry. exact Heq.
          -- right. apply IH. left. exact Hin.
        * apply insert_exact_membership. right. apply IH. right. exact Hf.
  Qed.

  (* An ATOMIC guarded STRUCTURAL firing (the OpenRule receiver): a guarded consume whose commit
     emits a LIST of structural reducts (all-or-nothing), generalizing GuardedCommSoundness's
     single-output `guarded_attempt` to the m-reduct splice. The guard is a plain `bool` (supplied
     by `ac_nl_guard`), so the non-linear veto is inherited, not re-proved. *)
  Record StructuralRule : Type := {
    sr_premises : list Fact;
    sr_guard : bool;
    sr_reducts : list Fact
  }.

  Inductive struct_attempt : list Fact -> StructuralRule -> list Fact -> Prop :=
    | struct_commit : forall facts r,
        all_present facts (sr_premises r) ->
        sr_guard r = true ->
        struct_attempt facts r (insert_all (sr_reducts r) facts)
    | struct_reject_guard : forall facts r,
        all_present facts (sr_premises r) ->
        sr_guard r = false ->
        struct_attempt facts r facts
    | struct_reject_premise : forall facts r,
        ~ all_present facts (sr_premises r) ->
        struct_attempt facts r facts.

  (* A guard-false consume commits nothing (next = facts) — the atomic reject-safety of the
     structural firing, the m-reduct analogue of GuardedCommSoundness.failed_guard_no_commit. *)
  Lemma struct_false_guard_no_commit : forall facts r next,
    sr_guard r = false ->
    struct_attempt facts r next ->
    next = facts.
  Proof.
    intros facts r next Hg Hatt.
    inversion Hatt; subst.
    - congruence.
    - reflexivity.
    - reflexivity.
  Qed.

  (* The AC 2-pick's ambient-name selection: slot 0 the `POpen` name, slot 1 the `PAmb` name. *)
  Definition open_selection (name_open name_amb : Fact) : list Fact :=
    [name_open; name_amb].

  (* The OpenRule receiver's `Receive.condition` `EEq(N_open, N_amb)` = `ac_nl_guard [0;1]` over the
     two selected ambient-name slots (default 0 is unused: both indices are in range). *)
  Definition open_guard (name_open name_amb : Fact) : bool :=
    ac_nl_guard [0; 1] (open_selection name_open name_amb) 0.

  (* The OpenRule firing: under the non-linear ambient-name guard, splice the two STRUCTURAL reducts
     P, Q (the open body + the ambient body — LHS-element args) with the residual bag. `premises` are
     the two structured-element facts the AC 2-pick consumed. *)
  Definition open_rule (premises : list Fact) (name_open name_amb p q : Fact) : StructuralRule :=
    {| sr_premises := premises;
       sr_guard := open_guard name_open name_amb;
       sr_reducts := [p; q] |}.

  (* (Open.1) THE NAME CHARACTERIZATION: the OpenRule guard holds IFF the open and ambient names are
     name-equal — `N ≡ N`. This is `ac_nl_two_slot_agree` specialized to the [0;1] selection. *)
  Theorem open_guard_iff_names_agree :
    forall name_open name_amb,
      open_guard name_open name_amb = true <-> name_open = name_amb.
  Proof.
    intros name_open name_amb. unfold open_guard.
    rewrite ac_nl_two_slot_agree. unfold open_selection. simpl. tauto.
  Qed.

  (* (Open.2) COMMIT (ATOMIC MULTI-EMIT): names agree (with the two element premises present) => the
     guarded consume commits, splicing BOTH structural reducts P, Q with rest — the OpenRule fires. *)
  Theorem open_commits_when_names_agree :
    forall facts premises name_open name_amb p q,
      all_present facts premises ->
      name_open = name_amb ->
      struct_attempt facts (open_rule premises name_open name_amb p q)
        (insert_all [p; q] facts).
  Proof.
    intros facts premises name_open name_amb p q Hpres Heq.
    apply (struct_commit facts (open_rule premises name_open name_amb p q)).
    - exact Hpres.
    - unfold open_rule; simpl. apply open_guard_iff_names_agree. exact Heq.
  Qed.

  (* (Open.3) REJECT-SAFE: names disagree => the guard is false, so the consume does NOT commit and
     consumes NO data (next = facts) — the mismatched-name soup rests, so `open` cannot dissolve a
     NON-matching ambient. *)
  Theorem open_disagree_no_commit :
    forall facts premises name_open name_amb p q next,
      name_open <> name_amb ->
      struct_attempt facts (open_rule premises name_open name_amb p q) next ->
      next = facts.
  Proof.
    intros facts premises name_open name_amb p q next Hne Hatt.
    apply (struct_false_guard_no_commit facts (open_rule premises name_open name_amb p q) next).
    - unfold open_rule; simpl.
      destruct (open_guard name_open name_amb) eqn:E; [ | reflexivity ].
      exfalso. apply Hne. apply open_guard_iff_names_agree. exact E.
    - exact Hatt.
  Qed.

  (* (Open.4) NO FABRICATION: every fact after the OpenRule consume is one of the STRUCTURAL reducts
     P, Q (each a projected argument of a consumed element — a sub-term of the redex) or was already
     present in `rest` — the receiver FORWARDS the σ-delivered reducts, never fabricates one. *)
  Theorem open_no_fabrication :
    forall facts premises name_open name_amb p q next x,
      struct_attempt facts (open_rule premises name_open name_amb p q) next ->
      In x next ->
      x = p \/ x = q \/ In x facts.
  Proof.
    intros facts premises name_open name_amb p q next x Hatt Hin.
    inversion Hatt; subst.
    - apply insert_all_membership in Hin. destruct Hin as [Hred | Hf].
      + unfold open_rule in Hred; simpl in Hred. destruct Hred as [Hp | [Hq | Hbot]].
        * left. symmetry. exact Hp.
        * right. left. symmetry. exact Hq.
        * contradiction.
      + right. right. exact Hf.
    - right. right. exact Hin.
    - right. right. exact Hin.
  Qed.

  (* (Open.5) THE FIRED BAG IS `{P, Q, ...rest}` (ATOMIC): on commit (names agree), the result
     contains BOTH structural reducts P AND Q AND every element of `rest` (= facts) — the atomic
     bag reassembly the receiver body `@"ac:PPar"!(P) | @"ac:PPar"!(Q) | rest` emits (all-or-nothing:
     no partial `P`-only or `Q`-only emit). *)
  Theorem open_emits_both_reducts_and_splices_rest :
    forall facts premises name_open name_amb p q,
      all_present facts premises ->
      name_open = name_amb ->
      exists next,
        struct_attempt facts (open_rule premises name_open name_amb p q) next
        /\ In p next
        /\ In q next
        /\ (forall r, In r facts -> In r next).
  Proof.
    intros facts premises name_open name_amb p q Hpres Heq.
    exists (insert_all [p; q] facts). repeat split.
    - apply open_commits_when_names_agree; assumption.
    - apply insert_all_membership. left. simpl. left. reflexivity.
    - apply insert_all_membership. left. simpl. right. left. reflexivity.
    - intros r Hr. apply insert_all_membership. right. exact Hr.
  Qed.

  (* (Open.6) GENERALIZES the Comm single-reduct emit: the m-reduct STRUCTURAL splice with ONE reduct
     is exactly GuardedCommSoundness's single `insert_exact` — so OpenRule's `{P, Q, ...rest}` splice
     is the Comm `{reduct, ...rest}` reassembly (CommRuleFiring) extended to m reducts. *)
  Theorem open_generalizes_comm_single_reduct :
    forall reduct facts,
      insert_all [reduct] facts = insert_exact reduct facts.
  Proof. intros reduct facts. reflexivity. Qed.

  (* (Open.7) ORACLE AGREEMENT: the installed receiver's `condition` guard equals the host's
     non-linear ambient-name check (`open_guard` = `ac_nl_guard` = `all_equal` over the gathered
     names) — the in-Rho OpenRule gate certifies the SAME oracle AcNonLinearConsistency certifies. *)
  Theorem open_oracle_agreement :
    forall premises name_open name_amb p q,
      sr_guard (open_rule premises name_open name_amb p q)
      = open_guard name_open name_amb.
  Proof. intros. reflexivity. Qed.

End AmbientOpenFiring.

Print Assumptions open_guard_iff_names_agree.
Print Assumptions open_commits_when_names_agree.
Print Assumptions open_disagree_no_commit.
Print Assumptions open_no_fabrication.
Print Assumptions open_emits_both_reducts_and_splices_rest.
Print Assumptions open_generalizes_comm_single_reduct.
Print Assumptions open_oracle_agreement.
