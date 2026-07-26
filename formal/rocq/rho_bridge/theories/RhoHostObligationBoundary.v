(*
 * RhoHostObligationBoundary: the ONLY guard obligation a host/off-machine
 * disposition may discharge is a semantic (behavioral) predicate. Structural,
 * theory-registration, and Rho-native-join obligations are NEVER host-executed —
 * they stay on the Rho machine / substrate. This is the formal image of the
 * north-star boundary "execute ALL rewrites on Rholang SAVE semantic predicates"
 * (pgmcp #1956 Epic 8 #2048; the Rho side of Epic 4 #2008).
 *
 * Rust image (`rholang-codegen/src/backend.rs`):
 *   - `RhoGuardObligationKind` = { BehavioralPredicate, StructuralPattern,
 *     TheoryRegistration, RhoNativeJoin }.
 *   - `RhoGuardDispositionKind` = { DovetailCoreStructural, EffectiveBooleanAlgebra,
 *     ExternalContract, NativeHandler, RhoNativeJoin, SymbolicFiniteTransducer }.
 *   - `guard_disposition_covers(o, d)` (backend.rs:217) is the coverage relation,
 *     modeled here as `covers` verbatim.
 *   - The HOST dispositions are `NativeHandler` (a direct Rho wrapper's native
 *     handler) and `ExternalContract` (an external host contract) — `host_disposition`.
 *   - Rust test `host_guard_dispositions_are_semantic_predicate_only` (backend.rs:1621)
 *     is the executable witness of the two main theorems below.
 *
 * 2026-07-25 — T-HB4 added: the GUARD-SITE restriction of the coverage matrix and
 * its non-vacuity / exactness / shipped-default-preservation companions. See the
 * banner comment immediately above `guard_site_covers` for what this file did and
 * did NOT already say, and for the PROVED refutation showing why the restriction
 * is necessary. No `.rs` change is entailed: every shipped default is already
 * guard-site admissible (`default_disposition_is_guard_site_admissible`).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.

Section RhoHostObligationBoundary.

  Inductive ObligationKind : Type :=
    | BehavioralPredicate
    | StructuralPattern
    | TheoryRegistration
    | RhoNativeJoinObligation.

  Inductive DispositionKind : Type :=
    | DovetailCoreStructural
    | EffectiveBooleanAlgebra
    | ExternalContract
    | NativeHandler
    | RhoNativeJoin
    | SymbolicFiniteTransducer.

  (* Verbatim image of `guard_disposition_covers` (backend.rs:230-247). *)
  Definition covers (o : ObligationKind) (d : DispositionKind) : bool :=
    match o with
    | BehavioralPredicate =>
        match d with
        | EffectiveBooleanAlgebra | SymbolicFiniteTransducer | RhoNativeJoin
        | NativeHandler | ExternalContract => true
        | _ => false
        end
    | StructuralPattern =>
        match d with
        | DovetailCoreStructural | SymbolicFiniteTransducer | RhoNativeJoin => true
        | _ => false
        end
    | TheoryRegistration =>
        match d with
        | EffectiveBooleanAlgebra | SymbolicFiniteTransducer => true
        | _ => false
        end
    | RhoNativeJoinObligation =>
        match d with RhoNativeJoin => true | _ => false end
    end.

  (* A host / off-machine disposition: a direct Rho wrapper's native handler or an
     external host contract. Everything else is decided on the machine/substrate. *)
  Definition host_disposition (d : DispositionKind) : bool :=
    match d with
    | NativeHandler | ExternalContract => true
    | _ => false
    end.

  (* MAIN: a host disposition covers ONLY a semantic (behavioral) predicate. A direct
     Rho wrapper cannot discharge any structural / theory / native-join obligation. *)
  Theorem host_disposition_covers_only_semantic_predicate : forall o d,
    host_disposition d = true -> covers o d = true -> o = BehavioralPredicate.
  Proof.
    intros o d Hhost Hcov.
    destruct o; destruct d; simpl in *; try discriminate; reflexivity.
  Qed.

  (* CONTRAPOSITIVE: a non-predicate obligation is NEVER host-executed — it is never
     covered by any host disposition (so it must stay on the machine/substrate). *)
  Theorem non_predicate_obligation_never_host : forall o d,
    o <> BehavioralPredicate -> host_disposition d = true -> covers o d = false.
  Proof.
    intros o d Hne Hhost.
    destruct o; [ congruence | | | ];
      destruct d; simpl in *; try discriminate Hhost; reflexivity.
  Qed.

  (* CHARACTERIZATION: the set of host-coverable obligations is exactly the singleton
     { BehavioralPredicate }. *)
  Theorem host_coverable_iff_semantic_predicate : forall o,
    (exists d, host_disposition d = true /\ covers o d = true)
    <-> o = BehavioralPredicate.
  Proof.
    intro o. split.
    - intros [d [Hhost Hcov]].
      exact (host_disposition_covers_only_semantic_predicate o d Hhost Hcov).
    - intro Ho. subst o. exists NativeHandler. split; reflexivity.
  Qed.

  (* ==========================================================================
     T-HB4 — the GUARD-SITE restriction (INV-14b': at a guard site the substrate
     is the ONLY decider).

     WHAT THIS FILE DOES AND DOES NOT SAY (read before amending).
     -----------------------------------------------------------------------
     `covers` above is a VERBATIM image of the shipped Rust `guard_disposition_covers`
     (backend.rs:217-248), and it already keeps structural decision ON the substrate:
     `covers StructuralPattern d = true` holds exactly for
     { DovetailCoreStructural, SymbolicFiniteTransducer, RhoNativeJoin }, none of
     which is a `host_disposition`. So this file NEVER forbade substrate-side
     structural decision; what it forbids is routing a non-predicate obligation to
     an opaque HOST handler. The amendment below is therefore in the RESTRICTIVE
     direction, and it concerns one row only: `BehavioralPredicate`.

     THE PROBLEM WITH THAT ROW. `covers BehavioralPredicate d` lumps together two
     kinds of decider:
       - CLOSED-WORLD, deterministic, decided from the replayed state:
           EffectiveBooleanAlgebra, SymbolicFiniteTransducer (and RhoNativeJoin,
           whose verdict is a Rho join/observation contract on the machine — see
           `host_disposition`, which classifies exactly NativeHandler and
           ExternalContract as off-machine and everything else as on-machine);
       - OPEN-WORLD, not replay-safe: NativeHandler (a direct Rho wrapper's native
           handler) and ExternalContract (an external host contract). Their verdicts
           are not functions of the replayed state.
     At an INSTALL site the second kind is admissible evidence. At a GUARD SITE it
     is not, because INV-14b' fixes a single decider there and Substrate-as-Definition
     makes the substrate's denotation the specification of the guard atom.
     (See docs/architecture/rho-native-integration/13-knotted-topoi-operational-invariants.md
     section 5.2.)

     HONESTY. The theorem "for every obligation o, covers o d = true -> host_disposition
     d = false" is FALSE over the UNRESTRICTED `covers`, and that is PROVED below
     (`unrestricted_covers_does_not_exclude_host_dispositions`) rather than asserted.
     It is exactly why the guard-site relation is introduced as a separate, explicitly
     tabulated matrix instead of the statement being weakened into vacuity.
     ========================================================================== *)

  (* REFUTATION (proved, not asserted): the unrestricted install-time coverage matrix
     does NOT exclude host dispositions. Witness: BehavioralPredicate / NativeHandler. *)
  Theorem unrestricted_covers_does_not_exclude_host_dispositions :
    ~ (forall o d, covers o d = true -> host_disposition d = false).
  Proof.
    intro H.
    specialize (H BehavioralPredicate NativeHandler eq_refl).
    discriminate H.
  Qed.

  (* The GUARD-SITE coverage matrix. Written out row by row — NOT as a conjunction
     with `host_disposition` — so that T-HB4 below is a real case analysis over the
     table and would FAIL if any row readmitted a host disposition. That the table
     is nevertheless EXACTLY the host-free part of `covers` is a separate theorem
     (`guard_site_covers_is_exactly_covers_minus_host`), which pins down that this
     restriction removes the host entries and nothing else. *)
  Definition guard_site_covers (o : ObligationKind) (d : DispositionKind) : bool :=
    match o with
    | BehavioralPredicate =>
        match d with
        | EffectiveBooleanAlgebra | SymbolicFiniteTransducer | RhoNativeJoin => true
        | _ => false
        end
    | StructuralPattern =>
        match d with
        | DovetailCoreStructural | SymbolicFiniteTransducer | RhoNativeJoin => true
        | _ => false
        end
    | TheoryRegistration =>
        match d with
        | EffectiveBooleanAlgebra | SymbolicFiniteTransducer => true
        | _ => false
        end
    | RhoNativeJoinObligation =>
        match d with RhoNativeJoin => true | _ => false end
    end.

  (* T-HB4 (MAIN): a guard obligation is covered ONLY by a substrate disposition.
     For every obligation arising at a guard site, coverage entails the covering
     disposition is not a host disposition. *)
  Theorem guard_site_coverage_excludes_host_dispositions : forall o d,
    guard_site_covers o d = true -> host_disposition d = false.
  Proof.
    intros o d Hcov.
    destruct o; destruct d; simpl in *; try discriminate; reflexivity.
  Qed.

  (* CONTRAPOSITIVE: a host disposition covers NOTHING at a guard site. *)
  Theorem host_disposition_covers_nothing_at_a_guard_site : forall o d,
    host_disposition d = true -> guard_site_covers o d = false.
  Proof.
    intros o d Hhost.
    destruct o; destruct d; simpl in *; try discriminate Hhost; reflexivity.
  Qed.

  (* CONSERVATIVITY: the guard-site matrix admits nothing the shipped install-time
     matrix does not. Restricting to guard sites can only remove admissible
     dispositions, never invent one. *)
  Theorem guard_site_covers_is_a_restriction_of_covers : forall o d,
    guard_site_covers o d = true -> covers o d = true.
  Proof.
    intros o d Hcov.
    destruct o; destruct d; simpl in *; try discriminate; reflexivity.
  Qed.

  (* EXACTNESS / MINIMALITY: the restriction removes the host entries and NOTHING
     else. This is what rules out over-restriction: the guard-site table is not an
     independent invention, it is `covers` minus the two open-world dispositions. *)
  Theorem guard_site_covers_is_exactly_covers_minus_host : forall o d,
    guard_site_covers o d = covers o d && negb (host_disposition d).
  Proof.
    intros o d. destruct o; destruct d; reflexivity.
  Qed.

  (* NON-VACUITY: every obligation kind still has at least one admissible decider at
     a guard site. The restriction strands no obligation kind, so it cannot be
     satisfied by refusing to decide. *)
  Theorem every_obligation_kind_has_a_guard_site_decider : forall o,
    exists d, guard_site_covers o d = true.
  Proof.
    intro o. destruct o.
    - exists EffectiveBooleanAlgebra. reflexivity.
    - exists DovetailCoreStructural. reflexivity.
    - exists EffectiveBooleanAlgebra. reflexivity.
    - exists RhoNativeJoin. reflexivity.
  Qed.

  (* The substrate's DEFAULT disposition per obligation kind — the verbatim image of
     the `disposition_kind` projection of `default_classification`
     (rholang-codegen/src/guard_quality.rs:259-290):
       StructuralPattern      -> DovetailCoreStructural   (:265-267)
       TheoryRegistration     -> EffectiveBooleanAlgebra  (:268-271)
       BehavioralPredicate    -> EffectiveBooleanAlgebra  (:272-280)
       RhoNativeJoin          -> RhoNativeJoin            (:281-288)
     No production path in the workspace emits NativeHandler or ExternalContract as a
     `RhoGuardDispositionKind`; the only occurrences are this coverage matrix and its
     unit tests. *)
  Definition default_disposition (o : ObligationKind) : DispositionKind :=
    match o with
    | StructuralPattern => DovetailCoreStructural
    | TheoryRegistration => EffectiveBooleanAlgebra
    | BehavioralPredicate => EffectiveBooleanAlgebra
    | RhoNativeJoinObligation => RhoNativeJoin
    end.

  (* SHIPPED-DEFAULT PRESERVATION: every default the substrate emits is still
     admissible at a guard site, so imposing INV-14b' changes NO shipped language's
     disposition. This is the theorem that makes T-HB4 free of migration cost. *)
  Theorem default_disposition_is_guard_site_admissible : forall o,
    guard_site_covers o (default_disposition o) = true.
  Proof. intro o. destruct o; reflexivity. Qed.

  Theorem default_disposition_is_never_host : forall o,
    host_disposition (default_disposition o) = false.
  Proof. intro o. destruct o; reflexivity. Qed.

  (* The two readings agree on every default: what the install-time gate accepts and
     what a guard site accepts coincide on the substrate's own output. *)
  Corollary guard_site_restriction_preserves_every_shipped_default : forall o,
    covers o (default_disposition o) = true
    /\ guard_site_covers o (default_disposition o) = true.
  Proof. intro o. destruct o; split; reflexivity. Qed.

End RhoHostObligationBoundary.

Print Assumptions host_disposition_covers_only_semantic_predicate.
Print Assumptions non_predicate_obligation_never_host.
Print Assumptions host_coverable_iff_semantic_predicate.
Print Assumptions unrestricted_covers_does_not_exclude_host_dispositions.
Print Assumptions guard_site_coverage_excludes_host_dispositions.
Print Assumptions host_disposition_covers_nothing_at_a_guard_site.
Print Assumptions guard_site_covers_is_a_restriction_of_covers.
Print Assumptions guard_site_covers_is_exactly_covers_minus_host.
Print Assumptions every_obligation_kind_has_a_guard_site_decider.
Print Assumptions default_disposition_is_guard_site_admissible.
Print Assumptions default_disposition_is_never_host.
Print Assumptions guard_site_restriction_preserves_every_shipped_default.
