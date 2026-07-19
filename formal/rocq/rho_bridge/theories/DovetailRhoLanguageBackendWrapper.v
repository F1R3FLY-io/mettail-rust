(*
 * DovetailRhoLanguageBackendWrapper: production wrapper shape for replacing
 * the legacy runtime backend with a Dovetail-checked, Rho-executed path.
 *
 * Rust image:
 *   - `DovetailRhoRuntimeBackedLanguage<L, D, F>` (eager) and
 *     `LazyDovetailRhoRuntimeBackedLanguage<L, D, F2, F>` (A-S2) delegate
 *     parsing, environments, and type inference to the generated language `L`.
 *   - The wrapper selects `RuntimeBackend::RhoMachine` as its default backend.
 *   - `RuntimeBackend::Dovetail` is exposed only as the checked intermediate
 *     report for diagnostics/query tooling; it is not the default runtime.
 *   - The wrapper can be constructed only when the planned Rho backend, the
 *     Dovetail compiler stage, and every Rho invocation compiler stage
 *     (report-free F2 and report-carrying F alike) were all derived from the
 *     same macro-expanded generated `LanguageDef`.
 *   - A-S2 (D-stage demotion): the default Rho path compiles the invocation
 *     REPORT-FREE first (`invocation_report_free` — the F2 compile admitted
 *     the term).  An admitted term executes on the Rho machine with ZERO
 *     Dovetail work: no report is built, so no report field can gate it.
 *   - The Dovetail report is built and checked LAZILY, exactly on the
 *     DEFERRAL path (`invocation_report_free = false`):  REPORT CHECKED ⟺
 *     DEFERRAL PATH TAKEN.  On that path the pre-A-S2 pipeline is reproduced
 *     verbatim: the checked report feeds the report-carrying invocation
 *     builder; when that builder lowers the term
 *     (`invocation_total_after_dovetail`) the default observes Rho output,
 *     and when it instead DEFERS a native-handler op (a fold / generated
 *     normalization not lowerable to a Rho contract) the wrapper returns the
 *     checked Dovetail report itself.  A flipped language therefore runs
 *     every op end-to-end: report-free terms and Rho-lowerable terms on Rho,
 *     native-fold terms via their lazily checked Dovetail report.
 *   - The legacy Ascent runtime and Ascent-shaped seeded facts are rejected
 *     through the production wrapped value.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool List PeanoNat.

Import ListNotations.

Section DovetailRhoLanguageBackendWrapper.

  Inductive Backend : Type :=
  | Ascent
  | Dovetail
  | RhoMachine.

  Inductive ReportShape : Type :=
  | AscentShape
  | DovetailReportShape
  | ObservationShape.

  Inductive ExtractionCompleteness : Type :=
  | Complete
  | BoundedByCycleCut.

  Inductive SeedFactsState : Type :=
  | NoSeedFacts
  | SeedFactsPresent.

  Record RuntimeBackendCapability : Type := {
    capability_backend : Backend;
    capability_is_default : bool
  }.

  Record DovetailRhoWrapper : Type := {
    generated_definition_id : nat;
    rho_plan_definition_id : nat;
    dovetail_compiler_definition_id : nat;
    invocation_compiler_definition_id : nat;
    planned_rho_backend : bool;
    dovetail_report_available : bool;
    dovetail_report_completeness : ExtractionCompleteness;
    dovetail_report_well_formed : bool;
    invocation_total_after_dovetail : bool;
    (* A-S2 (D-stage demotion): the REPORT-FREE invocation compile (F2)
       admitted the term — the default path executes on the Rho machine with
       NO Dovetail report.  When false, the term took the DEFERRAL path (a
       semantic predicate or a gate reject), which is the ONLY place the
       report fields above are built and consulted (lazily). *)
    invocation_report_free : bool
  }.

  Definition backend_eqb (left right : Backend) : bool :=
    match left, right with
    | Ascent, Ascent => true
    | Dovetail, Dovetail => true
    | RhoMachine, RhoMachine => true
    | _, _ => false
    end.

  Definition completeness_is_complete
      (status : ExtractionCompleteness) : bool :=
    match status with
    | Complete => true
    | BoundedByCycleCut => false
    end.

  Definition plan_matches_language (wrapper : DovetailRhoWrapper) : bool :=
    Nat.eqb
      (rho_plan_definition_id wrapper)
      (generated_definition_id wrapper).

  Definition dovetail_compiler_matches_language
      (wrapper : DovetailRhoWrapper) : bool :=
    Nat.eqb
      (dovetail_compiler_definition_id wrapper)
      (generated_definition_id wrapper).

  Definition invocation_compiler_matches_language
      (wrapper : DovetailRhoWrapper) : bool :=
    Nat.eqb
      (invocation_compiler_definition_id wrapper)
      (generated_definition_id wrapper).

  Definition wrapper_installs_rho (wrapper : DovetailRhoWrapper) : bool :=
    planned_rho_backend wrapper &&
    plan_matches_language wrapper &&
    dovetail_compiler_matches_language wrapper &&
    invocation_compiler_matches_language wrapper.

  Definition dovetail_report_checked (wrapper : DovetailRhoWrapper) : bool :=
    dovetail_report_available wrapper &&
    completeness_is_complete (dovetail_report_completeness wrapper) &&
    dovetail_report_well_formed wrapper.

  (* A-S2: the default path CONSULTS (builds + checks) the Dovetail report
     exactly on the deferral path — the boolean form of "report checked ⟺
     deferral path taken". *)
  Definition wrapper_default_checks_report
      (wrapper : DovetailRhoWrapper) : bool :=
    wrapper_installs_rho wrapper && negb (invocation_report_free wrapper).

  Definition wrapper_default_backend (_wrapper : DovetailRhoWrapper) : Backend :=
    RhoMachine.

  Definition wrapper_runtime_capabilities
      (wrapper : DovetailRhoWrapper) : list RuntimeBackendCapability :=
    if wrapper_installs_rho wrapper
    then [{| capability_backend := RhoMachine;
            capability_is_default := true |};
          {| capability_backend := Dovetail;
            capability_is_default := false |}]
    else [].

  Definition capabilities_support
      (capabilities : list RuntimeBackendCapability) (backend : Backend) : bool :=
    existsb
      (fun capability =>
         backend_eqb (capability_backend capability) backend)
      capabilities.

  Definition wrapper_supports
      (wrapper : DovetailRhoWrapper) (backend : Backend) : bool :=
    match backend with
    | RhoMachine => wrapper_installs_rho wrapper
    | Dovetail => wrapper_installs_rho wrapper
    | Ascent => false
    end.

  (* A-S2: the default RhoMachine path runs when the report-free compile
     admitted the term (NO report obligation), or — on the deferral path —
     when the lazily built report checked and the report-carrying builder
     lowered the term (the pre-A-S2 condition). *)
  Definition wrapper_rho_report_runs (wrapper : DovetailRhoWrapper) : bool :=
    wrapper_installs_rho wrapper &&
    (invocation_report_free wrapper ||
     (dovetail_report_checked wrapper &&
      invocation_total_after_dovetail wrapper)).

  Definition wrapper_dovetail_report_runs (wrapper : DovetailRhoWrapper) : bool :=
    wrapper_installs_rho wrapper && dovetail_report_checked wrapper.

  Definition wrapper_report_shape
      (wrapper : DovetailRhoWrapper) (backend : Backend) : option ReportShape :=
    match backend with
    | RhoMachine =>
        (* A flipped language routes per term-disposition under the RhoMachine
           default.  A-S2: when the report-free compile admits the term
           (`invocation_report_free`) the default observes Rho output with NO
           report obligation — no report field appears on this branch.  On the
           DEFERRAL path the report is built lazily and the pre-A-S2 routing
           applies verbatim: a checked report plus a lowering invocation
           mapper (`invocation_total_after_dovetail`) observes Rho output; a
           checked report whose mapper DEFERS a native-handler op returns the
           checked Dovetail report itself; a bounded or malformed lazy report
           blocks the deferral path (and only that path). *)
        if wrapper_installs_rho wrapper
        then
          if invocation_report_free wrapper
          then Some ObservationShape
          else
            if dovetail_report_checked wrapper
            then if invocation_total_after_dovetail wrapper
                 then Some ObservationShape
                 else Some DovetailReportShape
            else None
        else None
    | Dovetail =>
        if wrapper_dovetail_report_runs wrapper
        then Some DovetailReportShape
        else None
    | Ascent => None
    end.

  Definition wrapper_default_ascent_compat
      (wrapper : DovetailRhoWrapper) : bool :=
    match wrapper_report_shape wrapper (wrapper_default_backend wrapper) with
    | Some AscentShape => true
    | Some DovetailReportShape => false
    | Some ObservationShape => false
    | None => false
    end.

  Definition wrapper_report_with_facts
      (wrapper : DovetailRhoWrapper)
      (backend : Backend)
      (facts : SeedFactsState) : bool :=
    match facts with
    | SeedFactsPresent => false
    | NoSeedFacts =>
        match backend with
        | RhoMachine => wrapper_rho_report_runs wrapper
        | Dovetail => wrapper_dovetail_report_runs wrapper
        | Ascent => false
        end
    end.

  Theorem wrapper_default_backend_is_rho : forall wrapper,
    wrapper_default_backend wrapper = RhoMachine.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_supports_rho : forall wrapper,
    wrapper_supports wrapper RhoMachine = wrapper_installs_rho wrapper.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_supports_dovetail_intermediate : forall wrapper,
    wrapper_supports wrapper Dovetail = wrapper_installs_rho wrapper.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_rejects_ascent_support : forall wrapper,
    wrapper_supports wrapper Ascent = false.
  Proof. intros wrapper. reflexivity. Qed.

  Theorem wrapper_capabilities_support_matches_wrapper_supports :
    forall wrapper backend,
      capabilities_support
        (wrapper_runtime_capabilities wrapper) backend =
      wrapper_supports wrapper backend.
  Proof.
    intros [definition_id plan_id dovetail_id invocation_id planned available
              completeness well_formed invocation report_free] backend.
    unfold wrapper_runtime_capabilities, wrapper_supports,
      wrapper_installs_rho, plan_matches_language,
      dovetail_compiler_matches_language,
      invocation_compiler_matches_language, capabilities_support,
      backend_eqb.
    destruct backend;
      destruct planned;
      simpl;
      destruct (plan_id =? definition_id);
      destruct (dovetail_id =? definition_id);
      destruct (invocation_id =? definition_id);
      reflexivity.
  Qed.

  Theorem wrapper_capabilities_are_rho_default_then_dovetail_intermediate :
    forall wrapper,
      wrapper_installs_rho wrapper = true ->
      wrapper_runtime_capabilities wrapper =
      [{| capability_backend := RhoMachine;
          capability_is_default := true |};
       {| capability_backend := Dovetail;
          capability_is_default := false |}].
  Proof.
    intros wrapper Hinstall.
    unfold wrapper_runtime_capabilities.
    rewrite Hinstall.
    reflexivity.
  Qed.

  Theorem failed_wrapper_exposes_no_runtime_backend : forall wrapper,
    wrapper_installs_rho wrapper = false ->
    wrapper_runtime_capabilities wrapper = [].
  Proof.
    intros wrapper Hfail.
    unfold wrapper_runtime_capabilities.
    rewrite Hfail.
    reflexivity.
  Qed.

  Theorem mismatched_plan_blocks_installation : forall wrapper,
    plan_matches_language wrapper = false ->
    wrapper_installs_rho wrapper = false.
  Proof.
    intros wrapper Hmismatch.
    unfold wrapper_installs_rho.
    rewrite Hmismatch.
    destruct (planned_rho_backend wrapper); reflexivity.
  Qed.

  Theorem mismatched_dovetail_compiler_blocks_installation : forall wrapper,
    dovetail_compiler_matches_language wrapper = false ->
    wrapper_installs_rho wrapper = false.
  Proof.
    intros wrapper Hmismatch.
    unfold wrapper_installs_rho.
    rewrite Hmismatch.
    destruct (planned_rho_backend wrapper);
      destruct (plan_matches_language wrapper);
      reflexivity.
  Qed.

  Theorem mismatched_invocation_compiler_blocks_installation : forall wrapper,
    invocation_compiler_matches_language wrapper = false ->
    wrapper_installs_rho wrapper = false.
  Proof.
    intros wrapper Hmismatch.
    unfold wrapper_installs_rho.
    rewrite Hmismatch.
    destruct (planned_rho_backend wrapper);
      destruct (plan_matches_language wrapper);
      destruct (dovetail_compiler_matches_language wrapper);
      reflexivity.
  Qed.

  Theorem wrapper_rho_report_requires_planned_backend : forall wrapper,
    wrapper_rho_report_runs wrapper = true ->
    planned_rho_backend wrapper = true.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_rho_report_runs, wrapper_installs_rho in Hrun.
    destruct (planned_rho_backend wrapper); simpl in Hrun.
    - reflexivity.
    - discriminate Hrun.
  Qed.

  Theorem wrapper_rho_report_requires_matching_language : forall wrapper,
    wrapper_rho_report_runs wrapper = true ->
    plan_matches_language wrapper = true.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_rho_report_runs, wrapper_installs_rho in Hrun.
    destruct (planned_rho_backend wrapper);
      destruct (plan_matches_language wrapper);
      simpl in Hrun;
      try reflexivity;
      discriminate Hrun.
  Qed.

  Theorem wrapper_dovetail_report_requires_installation : forall wrapper,
    wrapper_dovetail_report_runs wrapper = true ->
    wrapper_installs_rho wrapper = true.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_dovetail_report_runs in Hrun.
    apply andb_true_iff in Hrun as [Hinstall _].
    exact Hinstall.
  Qed.

  Theorem wrapper_rho_report_requires_dovetail_compiler_match : forall wrapper,
    wrapper_rho_report_runs wrapper = true ->
    dovetail_compiler_matches_language wrapper = true.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_rho_report_runs, wrapper_installs_rho in Hrun.
    destruct (planned_rho_backend wrapper);
      destruct (plan_matches_language wrapper);
      destruct (dovetail_compiler_matches_language wrapper);
      simpl in Hrun;
      try reflexivity;
      discriminate Hrun.
  Qed.

  Theorem wrapper_rho_report_requires_invocation_compiler_match : forall wrapper,
    wrapper_rho_report_runs wrapper = true ->
    invocation_compiler_matches_language wrapper = true.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_rho_report_runs, wrapper_installs_rho in Hrun.
    destruct (planned_rho_backend wrapper);
      destruct (plan_matches_language wrapper);
      destruct (dovetail_compiler_matches_language wrapper);
      destruct (invocation_compiler_matches_language wrapper);
      simpl in Hrun;
      try reflexivity;
      discriminate Hrun.
  Qed.

  (* A-S2: the report-field obligations of the default path hold ON THE
     DEFERRAL PATH (`invocation_report_free = false`) — exactly where the
     lazy report is built.  Pre-A-S2 these theorems were unconditional
     because EVERY exec built the report; the report-free path discharges
     them by never constructing a report at all
     (`report_free_default_ignores_report_fields`). *)

  Theorem wrapper_rho_report_requires_dovetail_available : forall wrapper,
    invocation_report_free wrapper = false ->
    wrapper_rho_report_runs wrapper = true ->
    dovetail_report_available wrapper = true.
  Proof.
    intros wrapper Hdefer Hrun.
    unfold wrapper_rho_report_runs in Hrun.
    rewrite Hdefer in Hrun.
    simpl in Hrun.
    apply andb_true_iff in Hrun as [_ Hchecked_total].
    apply andb_true_iff in Hchecked_total as [Hchecked _].
    unfold dovetail_report_checked in Hchecked.
    destruct (dovetail_report_available wrapper); simpl in Hchecked.
    - reflexivity.
    - discriminate Hchecked.
  Qed.

  Theorem wrapper_rho_report_requires_complete_dovetail : forall wrapper,
    invocation_report_free wrapper = false ->
    wrapper_rho_report_runs wrapper = true ->
    dovetail_report_completeness wrapper = Complete.
  Proof.
    intros wrapper Hdefer Hrun.
    unfold wrapper_rho_report_runs in Hrun.
    rewrite Hdefer in Hrun.
    simpl in Hrun.
    apply andb_true_iff in Hrun as [_ Hchecked_total].
    apply andb_true_iff in Hchecked_total as [Hchecked _].
    unfold dovetail_report_checked in Hchecked.
    destruct (dovetail_report_available wrapper); simpl in Hchecked;
      try discriminate Hchecked.
    destruct (dovetail_report_completeness wrapper); simpl in Hchecked.
    - reflexivity.
    - discriminate Hchecked.
  Qed.

  Theorem wrapper_rho_report_requires_well_formed_dovetail : forall wrapper,
    invocation_report_free wrapper = false ->
    wrapper_rho_report_runs wrapper = true ->
    dovetail_report_well_formed wrapper = true.
  Proof.
    intros wrapper Hdefer Hrun.
    unfold wrapper_rho_report_runs in Hrun.
    rewrite Hdefer in Hrun.
    simpl in Hrun.
    apply andb_true_iff in Hrun as [_ Hchecked_total].
    apply andb_true_iff in Hchecked_total as [Hchecked _].
    unfold dovetail_report_checked in Hchecked.
    destruct (dovetail_report_available wrapper); simpl in Hchecked;
      try discriminate Hchecked.
    destruct (dovetail_report_completeness wrapper); simpl in Hchecked;
      try discriminate Hchecked.
    destruct (dovetail_report_well_formed wrapper); simpl in Hchecked.
    - reflexivity.
    - discriminate Hchecked.
  Qed.

  Theorem wrapper_rho_report_requires_total_invocation_after_dovetail :
    forall wrapper,
    invocation_report_free wrapper = false ->
    wrapper_rho_report_runs wrapper = true ->
    invocation_total_after_dovetail wrapper = true.
  Proof.
    intros wrapper Hdefer Hrun.
    unfold wrapper_rho_report_runs in Hrun.
    rewrite Hdefer in Hrun.
    simpl in Hrun.
    apply andb_true_iff in Hrun as [_ Hchecked_total].
    apply andb_true_iff in Hchecked_total as [_ Htotal].
    exact Htotal.
  Qed.

  Theorem wrapper_rho_report_requires_checked_dovetail : forall wrapper,
    invocation_report_free wrapper = false ->
    wrapper_rho_report_runs wrapper = true ->
    dovetail_report_checked wrapper = true.
  Proof.
    intros wrapper Hdefer Hrun.
    unfold wrapper_rho_report_runs in Hrun.
    rewrite Hdefer in Hrun.
    simpl in Hrun.
    apply andb_true_iff in Hrun as [_ Hchecked_total].
    apply andb_true_iff in Hchecked_total as [Hchecked _].
    exact Hchecked.
  Qed.

  Theorem checked_dovetail_report_shape_is_dovetail_report : forall wrapper,
    wrapper_dovetail_report_runs wrapper = true ->
    wrapper_report_shape wrapper Dovetail = Some DovetailReportShape.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_report_shape.
    rewrite Hrun. reflexivity.
  Qed.

  Theorem rho_default_report_shape_is_observation : forall wrapper,
    wrapper_rho_report_runs wrapper = true ->
    wrapper_report_shape wrapper (wrapper_default_backend wrapper) =
      Some ObservationShape.
  Proof.
    intros wrapper Hrun.
    unfold wrapper_default_backend, wrapper_report_shape.
    unfold wrapper_rho_report_runs in Hrun.
    destruct (wrapper_installs_rho wrapper);
      destruct (invocation_report_free wrapper);
      destruct (dovetail_report_checked wrapper);
      destruct (invocation_total_after_dovetail wrapper);
      simpl in Hrun |- *;
      try discriminate Hrun;
      reflexivity.
  Qed.

  (* ————————————————————————————————————————————————————————————————————
     A-S2 (D-stage demotion): REPORT CHECKED ⟺ DEFERRAL PATH TAKEN.
     The four theorems below are the two directions of the coupling, stated
     over the observable default-path shape:
       (⇐, report-free admits ⇒ no report obligation)
         `report_free_default_shape_is_observation`   — the admitted term
             observes Rho output whatever the report fields hold, and
         `report_free_default_ignores_report_fields`  — the default shape is
             INVARIANT under every report field, i.e. no report was consulted;
       (⇒, deferral taken ⇒ the lazy report gates)
         `deferred_default_requires_checked_report`   — any successful
             deferred default checked the (lazily built) report, and
         `report_checked_iff_deferral_taken`          — the boolean coupling
             of `wrapper_default_checks_report` to the deferral bit.
     ———————————————————————————————————————————————————————————————————— *)

  Theorem report_free_default_shape_is_observation : forall wrapper,
    wrapper_installs_rho wrapper = true ->
    invocation_report_free wrapper = true ->
    wrapper_report_shape wrapper (wrapper_default_backend wrapper) =
      Some ObservationShape.
  Proof.
    intros wrapper Hinstalls Hfree.
    unfold wrapper_default_backend, wrapper_report_shape.
    rewrite Hinstalls, Hfree. reflexivity.
  Qed.

  Theorem report_free_default_ignores_report_fields :
    forall definition_id plan_id dovetail_id invocation_id planned invocation
      available completeness well_formed
      available' completeness' well_formed',
      let wrapper :=
        {| generated_definition_id := definition_id;
           rho_plan_definition_id := plan_id;
           dovetail_compiler_definition_id := dovetail_id;
           invocation_compiler_definition_id := invocation_id;
           planned_rho_backend := planned;
           dovetail_report_available := available;
           dovetail_report_completeness := completeness;
           dovetail_report_well_formed := well_formed;
           invocation_total_after_dovetail := invocation;
           invocation_report_free := true |} in
      let wrapper' :=
        {| generated_definition_id := definition_id;
           rho_plan_definition_id := plan_id;
           dovetail_compiler_definition_id := dovetail_id;
           invocation_compiler_definition_id := invocation_id;
           planned_rho_backend := planned;
           dovetail_report_available := available';
           dovetail_report_completeness := completeness';
           dovetail_report_well_formed := well_formed';
           invocation_total_after_dovetail := invocation;
           invocation_report_free := true |} in
      wrapper_report_shape wrapper RhoMachine =
      wrapper_report_shape wrapper' RhoMachine.
  Proof.
    intros definition_id plan_id dovetail_id invocation_id planned invocation
      available completeness well_formed available' completeness' well_formed'.
    unfold wrapper_report_shape, wrapper_installs_rho, plan_matches_language,
      dovetail_compiler_matches_language, invocation_compiler_matches_language.
    simpl.
    destruct planned;
      destruct (plan_id =? definition_id);
      destruct (dovetail_id =? definition_id);
      destruct (invocation_id =? definition_id);
      reflexivity.
  Qed.

  Theorem deferred_default_requires_checked_report : forall wrapper shape,
    invocation_report_free wrapper = false ->
    wrapper_report_shape wrapper RhoMachine = Some shape ->
    dovetail_report_checked wrapper = true.
  Proof.
    intros wrapper shape Hdefer Hshape.
    unfold wrapper_report_shape in Hshape.
    destruct (wrapper_installs_rho wrapper).
    - rewrite Hdefer in Hshape.
      destruct (dovetail_report_checked wrapper).
      + reflexivity.
      + discriminate Hshape.
    - discriminate Hshape.
  Qed.

  Theorem report_checked_iff_deferral_taken : forall wrapper,
    wrapper_installs_rho wrapper = true ->
    (wrapper_default_checks_report wrapper = true <->
     invocation_report_free wrapper = false).
  Proof.
    intros wrapper Hinstalls.
    unfold wrapper_default_checks_report.
    rewrite Hinstalls. simpl.
    split.
    - intros Hneg.
      destruct (invocation_report_free wrapper).
      + discriminate Hneg.
      + reflexivity.
    - intros Hdefer. rewrite Hdefer. reflexivity.
  Qed.

  (* A bounded (or otherwise unchecked) lazy report cannot block a
     report-free admitted exec — the report was never built on that path. *)
  Theorem report_free_default_runs_with_unchecked_report : forall wrapper,
    wrapper_installs_rho wrapper = true ->
    invocation_report_free wrapper = true ->
    dovetail_report_checked wrapper = false ->
    wrapper_report_shape wrapper RhoMachine = Some ObservationShape.
  Proof.
    intros wrapper Hinstalls Hfree Hunchecked.
    unfold wrapper_report_shape.
    rewrite Hinstalls, Hfree. reflexivity.
  Qed.

  (* A native-handler op on the DEFERRAL path (the report-carrying invocation
     mapper defers because the term is not Rho-lowerable) executes via the
     lazily checked Dovetail report, so the RhoMachine default surfaces a
     Dovetail-report shape rather than failing closed. This is what lets a
     flipped language run every op end-to-end: report-free and Rho-lowerable
     terms on Rho, native-fold terms via their lazily checked Dovetail
     report. *)
  Theorem rho_default_deferred_report_shape_is_dovetail_report : forall wrapper,
    wrapper_installs_rho wrapper = true ->
    invocation_report_free wrapper = false ->
    dovetail_report_checked wrapper = true ->
    invocation_total_after_dovetail wrapper = false ->
    wrapper_report_shape wrapper (wrapper_default_backend wrapper) =
      Some DovetailReportShape.
  Proof.
    intros wrapper Hinstalls Hdefer Hchecked Hnative.
    unfold wrapper_default_backend, wrapper_report_shape.
    rewrite Hinstalls, Hdefer, Hchecked, Hnative. reflexivity.
  Qed.

  Theorem wrapper_default_is_not_ascent_compat : forall wrapper,
    wrapper_default_ascent_compat wrapper = false.
  Proof.
    intros wrapper.
    unfold wrapper_default_ascent_compat, wrapper_default_backend,
      wrapper_report_shape.
    destruct (wrapper_installs_rho wrapper);
      [destruct (invocation_report_free wrapper);
       [|destruct (dovetail_report_checked wrapper);
         [destruct (invocation_total_after_dovetail wrapper)|]]|];
      reflexivity.
  Qed.

  (* A bounded lazy report blocks the Dovetail diagnostic surface and the
     DEFERRAL path of the RhoMachine default (`invocation_report_free :=
     false`) — exactly the pre-A-S2 blocking behavior, now scoped to the only
     path that builds a report. *)
  Theorem bounded_dovetail_blocks_dovetail_and_deferred_rho :
    forall definition_id plan_id dovetail_id invocation_id planned
      available well_formed invocation,
      let wrapper :=
        {| generated_definition_id := definition_id;
           rho_plan_definition_id := plan_id;
           dovetail_compiler_definition_id := dovetail_id;
           invocation_compiler_definition_id := invocation_id;
           planned_rho_backend := planned;
           dovetail_report_available := available;
           dovetail_report_completeness := BoundedByCycleCut;
           dovetail_report_well_formed := well_formed;
           invocation_total_after_dovetail := invocation;
           invocation_report_free := false |} in
      wrapper_dovetail_report_runs wrapper = false /\
      wrapper_rho_report_runs wrapper = false.
  Proof.
    intros definition_id plan_id dovetail_id invocation_id planned
      available well_formed invocation.
    unfold wrapper_dovetail_report_runs, wrapper_rho_report_runs,
      wrapper_installs_rho, plan_matches_language,
      dovetail_compiler_matches_language,
      invocation_compiler_matches_language, dovetail_report_checked,
      completeness_is_complete.
    simpl.
    destruct planned;
      destruct (plan_id =? definition_id);
      destruct (dovetail_id =? definition_id);
      destruct (invocation_id =? definition_id);
      destruct available;
      destruct well_formed;
      destruct invocation;
      split;
      reflexivity.
  Qed.

  (* The A-S2 counterpart: the SAME bounded report leaves a REPORT-FREE
     admitted exec untouched — the default runs iff the wrapper installs,
     independent of every report field (ZERO D-stage on the admitted path). *)
  Theorem bounded_dovetail_does_not_block_report_free_rho :
    forall definition_id plan_id dovetail_id invocation_id planned
      available well_formed invocation,
      let wrapper :=
        {| generated_definition_id := definition_id;
           rho_plan_definition_id := plan_id;
           dovetail_compiler_definition_id := dovetail_id;
           invocation_compiler_definition_id := invocation_id;
           planned_rho_backend := planned;
           dovetail_report_available := available;
           dovetail_report_completeness := BoundedByCycleCut;
           dovetail_report_well_formed := well_formed;
           invocation_total_after_dovetail := invocation;
           invocation_report_free := true |} in
      wrapper_rho_report_runs wrapper = wrapper_installs_rho wrapper.
  Proof.
    intros definition_id plan_id dovetail_id invocation_id planned
      available well_formed invocation.
    unfold wrapper_rho_report_runs.
    simpl.
    apply andb_true_r.
  Qed.

  Theorem malformed_dovetail_blocks_dovetail_and_deferred_rho :
    forall definition_id plan_id dovetail_id invocation_id planned
      available completeness invocation,
      let wrapper :=
        {| generated_definition_id := definition_id;
           rho_plan_definition_id := plan_id;
           dovetail_compiler_definition_id := dovetail_id;
           invocation_compiler_definition_id := invocation_id;
           planned_rho_backend := planned;
           dovetail_report_available := available;
           dovetail_report_completeness := completeness;
           dovetail_report_well_formed := false;
           invocation_total_after_dovetail := invocation;
           invocation_report_free := false |} in
      wrapper_dovetail_report_runs wrapper = false /\
      wrapper_rho_report_runs wrapper = false.
  Proof.
    intros definition_id plan_id dovetail_id invocation_id planned
      available completeness invocation.
    unfold wrapper_dovetail_report_runs, wrapper_rho_report_runs,
      wrapper_installs_rho, plan_matches_language,
      dovetail_compiler_matches_language,
      invocation_compiler_matches_language, dovetail_report_checked.
    simpl.
    destruct planned;
      destruct (plan_id =? definition_id);
      destruct (dovetail_id =? definition_id);
      destruct (invocation_id =? definition_id);
      destruct available;
      destruct completeness;
      destruct invocation;
      split;
      reflexivity.
  Qed.

  Theorem empty_seeded_facts_match_selected_backend : forall wrapper backend,
    wrapper_report_with_facts wrapper backend NoSeedFacts =
      match backend with
      | RhoMachine => wrapper_rho_report_runs wrapper
      | Dovetail => wrapper_dovetail_report_runs wrapper
      | Ascent => false
      end.
  Proof. intros wrapper backend. destruct backend; reflexivity. Qed.

  Theorem seeded_facts_block_production_backends : forall wrapper backend,
    wrapper_report_with_facts wrapper backend SeedFactsPresent = false.
  Proof. intros wrapper backend. destruct backend; reflexivity. Qed.

End DovetailRhoLanguageBackendWrapper.
