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

End RhoHostObligationBoundary.

Print Assumptions host_disposition_covers_only_semantic_predicate.
Print Assumptions non_predicate_obligation_never_host.
Print Assumptions host_coverable_iff_semantic_predicate.
