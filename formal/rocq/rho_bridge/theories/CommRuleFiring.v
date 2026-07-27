(*
 * CommRuleFiring: FV (Stage 3b) — the canonical single-receive Rholang COMMUNICATION rule fires
 * as ONE non-linear AC COMM.
 *
 * SCOPE (D10): this theory models the ASYNCHRONOUS communication, whose reduct is the SINGLE
 * host-computed substitution. That is the shape Rholang / `CommDemo` declare and the shape the typed
 * COMM lane was first written for. The lane now admits a reduct of ARITY m >= 1 — one substitution
 * plus m-1 sigma-delivered elements — so that the GSLT omnibus's SYNCHRONOUS pi `Comm`
 * (omnibus.tex:1988-1989), whose output `n!m.q` carries a continuation, is realized too. The
 * m-reduct firing is proved in `SynchronousCommFiring.v`, which reuses this file's `comm_guard`
 * VERBATIM (the reduct arity never touches the non-linear channel gate) and proves the two models
 * AGREE at m = 1 (`sync_comm_generalizes_the_asynchronous_comm`,
 * `sync_comm_agrees_with_the_asynchronous_model`). Everything below therefore remains exactly true
 * of the code — as the m = 1 instance, which the generator still emits byte-identically.
 *
 * The Comm rule
 *
 *     {(PFor N cont), (POutput N Q), ...rest} ~> {(cont[Q/y]), ...rest}
 *
 * (i.e. `for(y <- N){ cont } | N!(Q)  ~>  cont[Q/y]`) fires, in ONE atomic guarded consume on the
 * installed AC σ-receiver (`rho_net_lower::comm_receiver_par`), by COMPOSING four already-verified
 * pieces:
 *
 *   (1) an AC 2-pick — the connective process-soup match selects the two STRUCTURED elements (the
 *       `PFor` receive and the `POutput` send) order-independently, GATHERING their shared channel
 *       occurrences into the selection's two slots (`ac_bag_pattern` shape / `sub_pars`);
 *   (2) a NON-LINEAR consistency guard — the receiver's `Receive.condition` `EEq(N_recv, N_send)`,
 *       which is `ac_nl_guard [0;1]` (AcNonLinearConsistency) over the two channel slots: it commits
 *       the COMM IFF the channels are name-equal (`N ≡ N`), reject-safe otherwise;
 *   (3) host substitution — the emitted contractum is the host-computed reduct `cont[Q/y]`,
 *       delivered at a dedicated σ slot the receiver FORWARDS (never fabricates), exactly as the
 *       Stage 3c binder path;
 *   (4) bag reassembly — the fired bag is `{reduct, ...rest}`: the reduct spliced with the bound
 *       remainder `rest` (modelled by `insert_exact reduct rest`).
 *
 * This is NOT a new proof obligation: it is `ac_nl_guard`'s commit<->name-equality
 * (AcNonLinearConsistency — itself an instance of NonLinearEqConsistency / GuardedCommSoundness)
 * SPECIALIZED to the two-element Comm selection, with the guarded output being the host reduct. We
 * prove: the Comm guard holds IFF the two channels agree; the consume commits (emitting the reduct)
 * when they agree and consumes NO data when they disagree (reject-safe); the emitted fact is the
 * host reduct or was already present (no fabrication); and, on commit, the fired bag contains the
 * reduct AND every element of `rest` (the `{reduct, ...rest}` reassembly).
 *
 * Reuses ac_nl_two_slot_agree / ac_nl_commits_iff_slots_agree / ac_nl_disagree_no_commit
 * (AcNonLinearConsistency), eq_rule / gather / all_equal (NonLinearEqConsistency), and
 * insert_exact / guarded_attempt (GuardedCommSoundness). Zero-admission. Rocq 9.1 compatible.
 * No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From RhoBridge Require Import GuardedCommSoundness.
From RhoBridge Require Import NonLinearEqConsistency.
From RhoBridge Require Import AcNonLinearConsistency.

Import ListNotations.

Section CommRuleFiring.

  (* The AC 2-pick's channel selection: slot 0 is the `PFor` receive channel `N_recv`, slot 1 the
     `POutput` send channel `N_send` — the two structured elements the order-independent AC match
     selected (Fact = nat channel-name identity). *)
  Definition comm_selection (chan_recv chan_send : Fact) : list Fact :=
    [chan_recv; chan_send].

  (* The Comm receiver's `Receive.condition` `EEq(N_recv, N_send)` = `ac_nl_guard [0;1]` over the
     two selected channel slots (default 0 is unused: both indices are in range). *)
  Definition comm_guard (chan_recv chan_send : Fact) : bool :=
    ac_nl_guard [0; 1] (comm_selection chan_recv chan_send) 0.

  (* The Comm rule fires the host-computed reduct `cont[Q/y]` from the receive+send premises, under
     the non-linear channel guard — the eq: consistency rule over the GATHERED channel occurrences.
     `reduct` is the SUBSTITUTION result the host delivers; `premises` are the receive+send facts. *)
  Definition comm_rule (premises : list Fact) (chan_recv chan_send reduct : Fact) : GuardedRule :=
    eq_rule premises (gather [0; 1] (comm_selection chan_recv chan_send) 0) reduct.

  (* (Comm.1) THE CHANNEL CHARACTERIZATION: the Comm guard holds IFF the receive and send channels
     are name-equal — `N ≡ N`. This is `ac_nl_two_slot_agree` specialized to the [0;1] selection. *)
  Theorem comm_guard_iff_channels_agree :
    forall chan_recv chan_send,
      comm_guard chan_recv chan_send = true <-> chan_recv = chan_send.
  Proof.
    intros chan_recv chan_send. unfold comm_guard.
    rewrite ac_nl_two_slot_agree. unfold comm_selection. simpl. tauto.
  Qed.

  (* (Comm.2) COMMIT: channels agree (with the receive+send premises present) => the guarded consume
     commits, adding the reduct `cont[Q/y]` — the COMM fires. `ac_nl_commits_iff_slots_agree`. *)
  Theorem comm_commits_when_channels_agree :
    forall facts premises chan_recv chan_send reduct,
      all_present facts premises ->
      chan_recv = chan_send ->
      guarded_attempt facts
        (comm_rule premises chan_recv chan_send reduct)
        (insert_exact reduct facts).
  Proof.
    intros facts premises chan_recv chan_send reduct Hpres Heq.
    unfold comm_rule.
    apply ac_nl_commits_iff_slots_agree.
    - exact Hpres.
    - subst chan_send. rewrite ac_nl_two_slot_agree. unfold comm_selection. simpl. reflexivity.
  Qed.

  (* (Comm.3) REJECT-SAFE: channels disagree => the guard is false, so the consume does NOT commit
     and consumes NO data (next = facts) — the mismatched-channel soup rests
     (`merge_substs -> None`). `ac_nl_disagree_no_commit`. *)
  Theorem comm_disagree_no_commit :
    forall facts premises chan_recv chan_send reduct next,
      chan_recv <> chan_send ->
      guarded_attempt facts (comm_rule premises chan_recv chan_send reduct) next ->
      next = facts.
  Proof.
    intros facts premises chan_recv chan_send reduct next Hne Hatt.
    unfold comm_rule in Hatt.
    apply (ac_nl_disagree_no_commit facts premises [0; 1]
             (comm_selection chan_recv chan_send) 0 reduct next).
    - destruct (ac_nl_guard [0; 1] (comm_selection chan_recv chan_send) 0) eqn:E.
      + exfalso. apply Hne.
        apply ac_nl_two_slot_agree in E. unfold comm_selection in E. simpl in E. exact E.
      + reflexivity.
    - exact Hatt.
  Qed.

  (* (Comm.4) NO FABRICATION: every fact after the Comm consume is the host reduct or was already
     present — the receiver FORWARDS the delivered reduct, never fabricates one. `eq_no_fabrication`. *)
  Theorem comm_no_fabrication :
    forall facts premises chan_recv chan_send reduct next x,
      guarded_attempt facts (comm_rule premises chan_recv chan_send reduct) next ->
      In x next ->
      x = reduct \/ In x facts.
  Proof.
    intros facts premises chan_recv chan_send reduct next x Hatt Hin.
    unfold comm_rule in Hatt.
    apply (eq_no_fabrication facts premises
             (gather [0; 1] (comm_selection chan_recv chan_send) 0) reduct next x);
      assumption.
  Qed.

  (* (Comm.5) THE FIRED BAG IS `{reduct, ...rest}`: on commit (channels agree), the result contains
     the substituted element `cont[Q/y]` (the reduct) AND every element of `rest` (= facts) — the
     bag reassembly the receiver body `@"ac:op"!(reduct) | rest` emits. *)
  Theorem comm_emits_reduct_and_splices_rest :
    forall facts premises chan_recv chan_send reduct,
      all_present facts premises ->
      chan_recv = chan_send ->
      exists next,
        guarded_attempt facts (comm_rule premises chan_recv chan_send reduct) next
        /\ In reduct next
        /\ (forall r, In r facts -> In r next).
  Proof.
    intros facts premises chan_recv chan_send reduct Hpres Heq.
    exists (insert_exact reduct facts). repeat split.
    - apply comm_commits_when_channels_agree; assumption.
    - apply insert_exact_membership. left. reflexivity.
    - intros r Hr. apply insert_exact_membership. right. exact Hr.
  Qed.

  (* (Comm.6) ORACLE AGREEMENT: the installed receiver's `condition` guard equals the host's
     non-linear channel check (both `ac_nl_guard` = `all_equal` over the gathered channels) — the
     in-Rho Comm gate certifies the SAME oracle vi certifies, over the AC 2-pick. *)
  Theorem comm_oracle_agreement :
    forall premises chan_recv chan_send reduct,
      guarded_guard (comm_rule premises chan_recv chan_send reduct)
      = comm_guard chan_recv chan_send.
  Proof.
    intros premises chan_recv chan_send reduct. reflexivity.
  Qed.

End CommRuleFiring.

Print Assumptions comm_guard_iff_channels_agree.
Print Assumptions comm_commits_when_channels_agree.
Print Assumptions comm_disagree_no_commit.
Print Assumptions comm_no_fabrication.
Print Assumptions comm_emits_reduct_and_splices_rest.
Print Assumptions comm_oracle_agreement.
