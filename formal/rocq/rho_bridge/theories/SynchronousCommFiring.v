(*
 * SynchronousCommFiring: FV (D10) — the COMMUNICATION rule fires as ONE non-linear AC COMM for a
 * reduct of ARITY m >= 1, so the SYNCHRONOUS pi-calculus Comm is realized, not just the
 * asynchronous one.
 *
 * CommRuleFiring models the ASYNCHRONOUS communication
 *
 *     {(PFor N cont), (POutput N Q), ...rest} ~> {(cont[Q/y]), ...rest}
 *
 * whose reduct is the SINGLE host-computed substitution (`insert_exact`). The GSLT omnibus's
 * SYNCHRONOUS pi Comm (omnibus.tex:1988-1989)
 *
 *     {(PIn n ^x.p), (POut n m q), ...rest} ~> {(eval ^x.p m), q, ...rest}
 *
 * carries an output CONTINUATION `q`, so its reduct has TWO elements: the host-computed
 * substitution `p[m/x]` AND the sigma-delivered `q`. Their parallel composition is exactly pi's
 *
 *     c!x.P | c?y.Q  =>  P | Q{x/y}
 *
 * and it is exactly what the reduct BAG `op{...}` denotes, `op` being the AC (HashBag) parallel
 * operator the LHS already matched over. The arity-1 restriction the lane carried was therefore
 * never a constraint on the contractum; it was the shape the lane was first written for.
 *
 * This theory proves the m-reduct COMM firing by COMPOSING two already-verified pieces, adding no
 * new primitive:
 *
 *   (1) the guard is CommRuleFiring's VERBATIM `comm_guard` — `ac_nl_guard [0;1]` over the two
 *       selected channel slots (AcNonLinearConsistency), so the non-linear channel veto `N == N`
 *       and its reject-safety are INHERITED, not re-proved;
 *   (2) the emit is AmbientOpenFiring's ATOMIC m-reduct splice `struct_attempt` / `insert_all`
 *       (all-or-nothing: never a partial "substitution-only" or "continuation-only" emit), which
 *       that theory already proved generalizes GuardedCommSoundness's single `insert_exact`
 *       (`open_generalizes_comm_single_reduct`).
 *
 * The ONE piece that is genuinely new here is the SPLIT of the reduct list into the ONE
 * HOST-COMPUTED substitution and the m-1 SIGMA-DELIVERED elements — the distinction the injection
 * seam makes (`RhoNetCommInjectionSite::reduct_slots`: `None` for the substitution slot, recovered
 * from the firing's contractum by multiset difference; `Some(var)` for a slot read straight out of
 * sigma). We prove the receiver FORWARDS both kinds without fabricating either, and that the fired
 * bag is `{cont[Q/y], q_0, ..., q_{m-2}, ...rest}`.
 *
 * NOT modelled here (deliberately, and stated rather than hidden): the side condition that a
 * sigma-delivered reduct element may never be a binder SCOPE — splicing a raw binder body beside
 * the substitution would let its bound variable escape. `Fact` is an opaque name (nat) with no
 * binder structure, so that condition is not expressible in this abstraction. It is a SYNTACTIC
 * classifier obligation, discharged where the classifiers run and pinned by
 * `dovetail_report::tests::is_comm_rewrite_rejects_a_binder_scope_as_a_bare_reduct_element` and
 * `rho_net_lower::tests::an_unconsumed_abstraction_scope_is_not_a_comm_shape`. Capture-avoidance of
 * the substitution ITSELF is the host's (model-b) and is verified in DeBruijnSubstTRS.
 *
 * Reuses comm_guard / comm_selection (CommRuleFiring), insert_all / insert_all_membership /
 * StructuralRule / struct_attempt / struct_false_guard_no_commit (AmbientOpenFiring),
 * ac_nl_two_slot_agree (AcNonLinearConsistency), and Fact / all_present / insert_exact
 * (GuardedCommSoundness). Zero-admission. Rocq 9.1 compatible.
 * No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From RhoBridge Require Import GuardedCommSoundness.
From RhoBridge Require Import NonLinearEqConsistency.
From RhoBridge Require Import AcNonLinearConsistency.
From RhoBridge Require Import CommRuleFiring.
From RhoBridge Require Import AmbientOpenFiring.

Import ListNotations.

Section SynchronousCommFiring.

  (* The m >= 1 reduct elements of a COMMUNICATION firing, in RHS order: the ONE host-computed
     substitution `cont[Q/y]` FIRST, then the m-1 sigma-delivered elements (the output's
     continuation, for the synchronous pi Comm). The order is the RHS bag's; because the carrier is
     an AC HashBag it is immaterial to the semantics, and every theorem below is stated by
     MEMBERSHIP rather than by position. *)
  Definition comm_reducts (subst_reduct : Fact) (sigma_reducts : list Fact) : list Fact :=
    subst_reduct :: sigma_reducts.

  (* The m-reduct COMMUNICATION firing: under CommRuleFiring's VERBATIM non-linear channel guard,
     atomically splice every reduct element with the residual bag. `premises` are the receive+send
     facts the AC 2-pick consumed. *)
  Definition sync_comm_rule
      (premises : list Fact)
      (chan_recv chan_send subst_reduct : Fact)
      (sigma_reducts : list Fact) : StructuralRule :=
    {| sr_premises := premises;
       sr_guard := comm_guard chan_recv chan_send;
       sr_reducts := comm_reducts subst_reduct sigma_reducts |}.

  (* (Sync.1) THE CHANNEL CHARACTERIZATION IS UNCHANGED: the m-reduct rule's guard holds IFF the
     receive and send channels are name-equal. The reduct arity does not touch the guard — this is
     CommRuleFiring's `comm_guard_iff_channels_agree`, re-exposed at the generalized rule. *)
  Theorem sync_comm_guard_iff_channels_agree :
    forall premises chan_recv chan_send subst_reduct sigma_reducts,
      sr_guard (sync_comm_rule premises chan_recv chan_send subst_reduct sigma_reducts) = true
      <-> chan_recv = chan_send.
  Proof.
    intros premises chan_recv chan_send subst_reduct sigma_reducts.
    unfold sync_comm_rule; simpl.
    apply comm_guard_iff_channels_agree.
  Qed.

  (* (Sync.2) COMMIT (ATOMIC MULTI-EMIT): channels agree (with the receive+send premises present)
     => the guarded consume commits, splicing EVERY reduct element with rest — the synchronous COMM
     fires as ONE atomic step. *)
  Theorem sync_comm_commits_when_channels_agree :
    forall facts premises chan_recv chan_send subst_reduct sigma_reducts,
      all_present facts premises ->
      chan_recv = chan_send ->
      struct_attempt facts
        (sync_comm_rule premises chan_recv chan_send subst_reduct sigma_reducts)
        (insert_all (comm_reducts subst_reduct sigma_reducts) facts).
  Proof.
    intros facts premises chan_recv chan_send subst_reduct sigma_reducts Hpres Heq.
    apply (struct_commit facts
             (sync_comm_rule premises chan_recv chan_send subst_reduct sigma_reducts)).
    - exact Hpres.
    - unfold sync_comm_rule; simpl.
      apply comm_guard_iff_channels_agree. exact Heq.
  Qed.

  (* (Sync.3) REJECT-SAFE: channels disagree => the guard is false, so the consume does NOT commit
     and consumes NO data (next = facts) — the mismatched-channel soup rests, for EVERY reduct
     arity. `struct_false_guard_no_commit`. *)
  Theorem sync_comm_disagree_no_commit :
    forall facts premises chan_recv chan_send subst_reduct sigma_reducts next,
      chan_recv <> chan_send ->
      struct_attempt facts
        (sync_comm_rule premises chan_recv chan_send subst_reduct sigma_reducts) next ->
      next = facts.
  Proof.
    intros facts premises chan_recv chan_send subst_reduct sigma_reducts next Hne Hatt.
    apply (struct_false_guard_no_commit facts
             (sync_comm_rule premises chan_recv chan_send subst_reduct sigma_reducts) next).
    - unfold sync_comm_rule; simpl.
      destruct (comm_guard chan_recv chan_send) eqn:E.
      + exfalso. apply Hne. apply comm_guard_iff_channels_agree. exact E.
      + reflexivity.
    - exact Hatt.
  Qed.

  (* (Sync.4) NO FABRICATION: every fact after the consume is one of the DELIVERED reduct elements
     — the host-computed substitution `cont[Q/y]` or a sigma-delivered element — or was already
     present in `rest`. The receiver FORWARDS each slot; it fabricates neither the substitution it
     recovers from the contractum nor the elements it reads from sigma. *)
  Theorem sync_comm_no_fabrication :
    forall facts premises chan_recv chan_send subst_reduct sigma_reducts next x,
      struct_attempt facts
        (sync_comm_rule premises chan_recv chan_send subst_reduct sigma_reducts) next ->
      In x next ->
      x = subst_reduct \/ In x sigma_reducts \/ In x facts.
  Proof.
    intros facts premises chan_recv chan_send subst_reduct sigma_reducts next x Hatt Hin.
    inversion Hatt; subst.
    - apply insert_all_membership in Hin.
      destruct Hin as [Hred | Hf].
      + unfold sync_comm_rule, comm_reducts in Hred; simpl in Hred.
        destruct Hred as [Hsub | Hsig].
        * left. symmetry. exact Hsub.
        * right. left. exact Hsig.
      + right. right. exact Hf.
    - right. right. exact Hin.
    - right. right. exact Hin.
  Qed.

  (* (Sync.5) THE FIRED BAG IS `{cont[Q/y], q_0, ..., q_{m-2}, ...rest}` (ATOMIC): on commit
     (channels agree), the result contains the host-computed substitution AND EVERY sigma-delivered
     reduct element AND every element of `rest` — the bag reassembly the receiver body
     `@"ac:op"!(r_0) | ... | @"ac:op"!(r_{m-1}) | rest` emits, all-or-nothing. For the synchronous
     pi Comm with `sigma_reducts = [q]` this is exactly `p[m/x] | q | rest`. *)
  Theorem sync_comm_emits_every_reduct_and_splices_rest :
    forall facts premises chan_recv chan_send subst_reduct sigma_reducts,
      all_present facts premises ->
      chan_recv = chan_send ->
      exists next,
        struct_attempt facts
          (sync_comm_rule premises chan_recv chan_send subst_reduct sigma_reducts) next
        /\ In subst_reduct next
        /\ (forall q, In q sigma_reducts -> In q next)
        /\ (forall r, In r facts -> In r next).
  Proof.
    intros facts premises chan_recv chan_send subst_reduct sigma_reducts Hpres Heq.
    exists (insert_all (comm_reducts subst_reduct sigma_reducts) facts).
    repeat split.
    - apply sync_comm_commits_when_channels_agree; assumption.
    - apply insert_all_membership. left. unfold comm_reducts. simpl. left. reflexivity.
    - intros q Hq. apply insert_all_membership. left.
      unfold comm_reducts. simpl. right. exact Hq.
    - intros r Hr. apply insert_all_membership. right. exact Hr.
  Qed.

  (* (Sync.6) CONSERVATIVE OVER THE ASYNCHRONOUS RULE: with NO sigma-delivered elements (m = 1) the
     fired bag is EXACTLY CommRuleFiring's single-emit `insert_exact reduct facts`. So the arity
     generalization does not change the asynchronous communication it subsumes — the same
     conservativity the code realizes as byte-identical emitted receivers/injections at m = 1. *)
  Theorem sync_comm_generalizes_the_asynchronous_comm :
    forall premises chan_recv chan_send reduct facts,
      insert_all
        (sr_reducts (sync_comm_rule premises chan_recv chan_send reduct []))
        facts
      = insert_exact reduct facts.
  Proof. intros. reflexivity. Qed.

  (* (Sync.7) ...and it commits to precisely CommRuleFiring's asynchronous result: at m = 1 the
     m-reduct COMM firing lands on the very bag `comm_commits_when_channels_agree` produces, so the
     two models AGREE on the shape they share rather than merely being isomorphic. *)
  Theorem sync_comm_agrees_with_the_asynchronous_model :
    forall facts premises chan_recv chan_send reduct,
      all_present facts premises ->
      chan_recv = chan_send ->
      struct_attempt facts
        (sync_comm_rule premises chan_recv chan_send reduct [])
        (insert_exact reduct facts)
      /\ guarded_attempt facts
           (comm_rule premises chan_recv chan_send reduct)
           (insert_exact reduct facts).
  Proof.
    intros facts premises chan_recv chan_send reduct Hpres Heq. split.
    - rewrite <- (sync_comm_generalizes_the_asynchronous_comm
                    premises chan_recv chan_send reduct facts).
      apply sync_comm_commits_when_channels_agree; assumption.
    - apply comm_commits_when_channels_agree; assumption.
  Qed.

  (* (Sync.8) ORACLE AGREEMENT: the installed m-slot receiver's `condition` guard is the SAME
     `ac_nl_guard` the asynchronous receiver installs — the extra reduct slots widen the receive
     frame but do not touch the non-linear channel gate, so the in-Rho synchronous COMM certifies
     the SAME oracle. *)
  Theorem sync_comm_oracle_agreement :
    forall premises chan_recv chan_send subst_reduct sigma_reducts,
      sr_guard (sync_comm_rule premises chan_recv chan_send subst_reduct sigma_reducts)
      = comm_guard chan_recv chan_send.
  Proof. intros. reflexivity. Qed.

End SynchronousCommFiring.

Print Assumptions sync_comm_guard_iff_channels_agree.
Print Assumptions sync_comm_commits_when_channels_agree.
Print Assumptions sync_comm_disagree_no_commit.
Print Assumptions sync_comm_no_fabrication.
Print Assumptions sync_comm_emits_every_reduct_and_splices_rest.
Print Assumptions sync_comm_generalizes_the_asynchronous_comm.
Print Assumptions sync_comm_agrees_with_the_asynchronous_model.
Print Assumptions sync_comm_oracle_agreement.
