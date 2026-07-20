(*
 * AmbientInOutFiring: FV (Stage 4 S-binder SLICE 3) — the Ambient-calculus In/Out rules fire as
 * ONE DEPTH-2 NESTED structural non-linear AC COMM. The DEPTH-2 analogue of AmbientOpenFiring.
 *
 * The Ambient `InRule`
 *
 *     { n[{ in(m,P), ...rest1 }], m[R], ...rest2 } ~> { m[{ n[{ P, ...rest1 }], R }], ...rest2 }
 *
 * (an ambient `n` carrying an `in(m,·)` capability MOVES INTO the sibling ambient `m`) and its dual
 * `OutRule` — A-S5.4b (AM-1, USER approved) REDECLARED to Cardelli-Gordon (Red Out), the residual
 * KEPT INSIDE `m`:
 *
 *     m[{ n[{ out(m,P), ...rest1 }], ...rest2 }] ~> { n[{ P, ...rest1 }], m[{ ...rest2 }] }
 *
 * (the ambient `n` carrying `out(m,·)` MOVES OUT of `m`; the whole residual `...rest2` rides the
 * rest-only inner bag of the emitted `m[...]` — the TEMPLATE-CONSUMED rest placement; empty rest
 * legal, so the singleton `m[{n[{out(m,p)}]}]` FIRES to `{n[{p}], m[{}]}`. The pre-A-S5.4b
 * declaration's ejection shape — `R` + a top-spliced `...rest2` — remains InOutDemo's demo
 * declaration, its two-level splice equation retained as InRhoAcMatchMultiset's
 * `outrule_reduct_ids_two_level`) fire, in ONE ATOMIC guarded consume on the
 * installed nested AC σ-receiver (`rho_net_lower::nested_structural_ac_match_receiver_par`), by
 * COMPOSING — EXACTLY as AmbientOpenFiring does for the flat OpenRule, but one nesting level deeper:
 *
 *   (1) a DEPTH-2 AC match — the connective process-soup match selects, in the SAME atomic consume,
 *       the two OUTER structured elements (the moving ambient `A = n[{…}]` and the sibling `m[R]`)
 *       order-independently, AND, one level down via the reducer's recursive `SpatialMatcher`, the
 *       capability `in(m,P)`/`out(m,P)` inside `A`'s inner bag — the two-level partition witness
 *       `InRhoAcMatchMultiset.nested_match` (NS.1/NS.2), each level an
 *       `ac_match_iff_partition` (AC-i);
 *   (2) a CROSS-LEVEL NON-LINEAR consistency guard — the receiver's `Receive.condition`
 *       `EEq(M_outer, M_inner)`, which is `ac_nl_guard [i;j]` (AcNonLinearConsistency) over the two
 *       ambient-name slots that live at DIFFERENT nesting levels (one bound at the OUTER `m[R]`, one
 *       ONE LEVEL DOWN inside the `in(m,·)`/`out(m,·)` capability). Because `gather` reads the
 *       selection at SLOT POSITIONS, not depth levels, obligation (vi) — and its Stage-AC slot-gather
 *       composition — applies VERBATIM (`ac_nl_cross_level_two_slot` /
 *       `ac_nl_cross_level_commits` / `ac_nl_cross_level_reject_safe`): it commits the COMM IFF the
 *       two `M` occurrences are name-equal (`M ≡ M`), reject-safe otherwise;
 *   (3) a PURE STRUCTURAL NESTED reduct — the reducts are STRUCTURAL PROJECTIONS of the selected
 *       elements re-assembled NESTED: `P` (the capability body), `R` (the sibling body), and the two
 *       remainders `rest1`/`rest2`; the fired bag is `⟦R⟧σ`, the SUBJECT's depth-2 reduct, never
 *       fabricated (`InRhoAcMatchMultiset.nested_structural_ac_spread_is_report_faithful`);
 *   (4) an ATOMIC two-level bag reassembly — the fired bag splices `...rest1` INLINE at the INNER bag
 *       and `...rest2` INLINE at the OUTER bag, multiplicity-preserving at BOTH, neither nesting into
 *       the other, in ONE all-or-nothing commit
 *       (`InRhoAcMatchMultiset.inrule_reduct_ids_two_level` / `outrule_reduct_ids_two_level`, each two
 *       independent `fired_bag_is_reducts_splice_rest`).
 *
 * This SPECIALIZES `ac_nl_guard`'s commit<->name-equality to the CROSS-LEVEL In/Out selection and
 * REUSES AmbientOpenFiring's atomic m-reduct `struct_attempt` firing at the OUTER level (the InRule
 * emits ONE outer reduct — the reassembled `m[…]`; the OutRule emits TWO — `n[…]` and `m[R]`), with
 * the INNER `...rest1` splice certified by the depth-2 reduct-id equations. So the In/Out firing is
 * NOT a new proof obligation: it inherits the guard from AcNonLinearConsistency verbatim, the outer
 * atomic splice from AmbientOpenFiring, and the depth-2 match/σ/reduct correspondence from
 * InRhoAcMatchMultiset — assembled here into an OPERATIONAL firing lemma + a source<->in-Rho
 * step-correspondence, putting the Stage-5 capstone's `FAcNested` (In/Out) arm on EQUAL FOOTING with
 * `FAcStructural` (OpenRule <- AmbientOpenFiring): a landed operational firing FV that directly
 * matches the arm shape.
 *
 * We prove: the cross-level guard holds IFF the two `M` slots agree (`inout_guard_iff_M_agrees`); the
 * consume commits (splicing the nested reduct) when they agree and consumes NO data when they
 * disagree (`inout_commits_when_M_agrees` / `inout_disagree_no_commit`, reject-safe); every emitted
 * fact is a structural reduct or was already present (`inout_no_fabrication`); the fired bag
 * reassembles NESTED — the InRule with `rest1` inner + `rest2` outer
 * (`inrule_emits_nested_reduct_and_splices_both_rests`), the REDECLARED OutRule with `rest1`
 * inside `n[...]` AND `rest2` inside `m[...]`, nothing at the top
 * (`outrule_emits_residual_kept_inside_and_splices_both_rests`, its reduct-id equation
 * `outrule_residual_kept_inside_reduct_ids`, and the empty-rest singleton firing
 * `outrule_singleton_fires`); the InRule single-top-reduct outer splice
 * coincides with the Comm `insert_exact` emit (`inrule_single_top_reduct_is_insert_exact`); the
 * receiver's `condition` guard equals the host's cross-level non-linear name check
 * (`inout_oracle_agreement`); the guarded-attempt form of the commit/reject is inherited VERBATIM
 * from AcNonLinearConsistency (`inout_cross_level_guarded_commit` /
 * `inout_cross_level_guarded_reject_safe`, <- `ac_nl_cross_level_commits` /
 * `ac_nl_cross_level_reject_safe`); the source In/Out reduction step corresponds to the lowered
 * In/Out COMM with EQUAL BARBS, both directions (`inout_step_complete` / `inout_step_sound` /
 * `inout_lower_preserves_barbs` — the operational step-correspondence the capstone's
 * `fwd_/bwd_acnested` consume); and, on a located depth-2 match, the fired OUT is the SUBJECT's
 * nested reduct `⟦R⟧σ` (`inout_out_is_report_faithful`, <-
 * `nested_structural_ac_spread_is_report_faithful`, reusing the FV's `outer/inner_located_is_spread`
 * pair-Hypothesis verbatim).
 *
 * Reuses AmbientOpenFiring (`insert_all` / `struct_attempt` / `StructuralRule` / `struct_commit` /
 * `struct_false_guard_no_commit` / `insert_all_membership`), AcNonLinearConsistency
 * (`ac_nl_guard` / `gather` / `ac_nl_cross_level_two_slot` / `ac_nl_cross_level_commits` /
 * `ac_nl_cross_level_reject_safe`), NonLinearEqConsistency (`eq_rule`), GuardedCommSoundness
 * (`Fact` / `all_present` / `insert_exact`), and InRhoAcMatchMultiset (`nested_match` /
 * `delivered_nested_sigma` / `inrule_reduct_ids_two_level` / `outrule_reduct_ids_two_level` /
 * `nested_structural_ac_spread_is_report_faithful`) + AcRestReconstruction (`flatten` / `Leaf` /
 * `Sub`). Zero-admission. Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions (Section
 * Variable/Hypothesis only — the sanctioned spread idiom, universally quantified on Section close).
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Permutation.
From RhoBridge Require Import GuardedCommSoundness.
From RhoBridge Require Import NonLinearEqConsistency.
From RhoBridge Require Import AcNonLinearConsistency.
From RhoBridge Require Import AmbientOpenFiring.
From AdvancedAutomata Require Import AcRestReconstruction.
From AdvancedAutomata Require Import InRhoAcMatchMultiset.

Import ListNotations.

Section AmbientInOutFiring.

  (* ========================================================================================= *)
  (* 1. THE CROSS-LEVEL GUARD (EEq(M_outer, M_inner)) — the depth-2 analogue of `open_guard`.    *)
  (* ========================================================================================= *)

  (* The In/Out cross-level 2-slot selection: slot 0 the OUTER `M` occurrence (bound at the sibling
     `m[R]`, or the root wrapper `m[{…}]` for OutRule), slot 1 the INNER `M` occurrence (bound one
     level down inside the `in(m,·)`/`out(m,·)` capability). The depth-2 twin of `open_selection`;
     `gather` reads these at SLOT positions, so the two levels are indistinguishable to the guard. *)
  Definition inout_selection (m_outer m_inner : Fact) : list Fact := [m_outer; m_inner].

  (* The In/Out receiver's `Receive.condition` `EEq(M_outer, M_inner)` = `ac_nl_guard [0;1]` over the
     two cross-level ambient-name slots (default 0 is unused: both indices are in range). The depth-2
     analogue of `open_guard`, with the two occurrences at DIFFERENT nesting levels. *)
  Definition inout_guard (m_outer m_inner : Fact) : bool :=
    ac_nl_guard [0; 1] (inout_selection m_outer m_inner) 0.

  (* (InOut.1) THE CROSS-LEVEL NAME CHARACTERIZATION: the In/Out guard holds IFF the outer-`M` and
     inner-`M` occurrences are name-equal — `M ≡ M` across nesting levels. This is
     `ac_nl_cross_level_two_slot` (AcNonLinearConsistency, the depth-agnostic restatement of vi's
     `ac_nl_two_slot_agree`) specialized to the [0;1] cross-level selection. *)
  Theorem inout_guard_iff_M_agrees :
    forall m_outer m_inner,
      inout_guard m_outer m_inner = true <-> m_outer = m_inner.
  Proof.
    intros m_outer m_inner. unfold inout_guard.
    rewrite ac_nl_cross_level_two_slot. unfold inout_selection. simpl. tauto.
  Qed.

  (* The In/Out guard IS the cross-level `ac_nl_guard` (AcNonLinearConsistency), made explicit: the
     receiver's condition is the SAME oracle vi certifies, over the cross-level selection. *)
  Theorem inout_guard_is_cross_level_ac_nl_guard :
    forall m_outer m_inner,
      inout_guard m_outer m_inner = ac_nl_guard [0; 1] (inout_selection m_outer m_inner) 0.
  Proof. intros. reflexivity. Qed.

  (* ========================================================================================= *)
  (* 2. THE DEPTH-2 FIRING (atomic outer m-reduct splice under the cross-level guard).           *)
  (*                                                                                             *)
  (* REUSES AmbientOpenFiring's `struct_attempt` (the atomic m-reduct STRUCTURAL firing) at the   *)
  (* OUTER bag level: `sr_reducts` are the OUTER-level reassembled top elements (InRule: the one   *)
  (* moving `m[…]`; the REDECLARED OutRule: `n[…]` and the residual-keeping `m[{...rest2}]`),      *)
  (* `sr_guard` is the cross-level `inout_guard`, and the commit inserts those outer reducts.      *)
  (* The rest splices are certified by the reduct-id equations: the InRule's `rest1`-inner +        *)
  (* `rest2`-outer by `inrule_reduct_ids_two_level` (InRhoAcMatchMultiset), the redeclared          *)
  (* OutRule's rest1-inside-`n` + rest2-inside-`m` (NOTHING at the top — the residual never         *)
  (* crosses the membrane) by the LOCAL `outrule_residual_kept_inside_reduct_ids` below.            *)
  (* ========================================================================================= *)

  (* The In/Out firing rule: under the cross-level ambient-name guard, splice the OUTER STRUCTURAL
     reducts `top_reducts` (the reassembled top-level elements, each carrying its inner `...rest1`
     splice) with the outer residual bag `...rest2`. `premises` are the outer structured-element facts
     the depth-2 AC match consumed. The depth-2 twin of `open_rule`. *)
  Definition inout_rule (premises : list Fact) (m_outer m_inner : Fact) (top_reducts : list Fact)
    : StructuralRule :=
    {| sr_premises := premises;
       sr_guard := inout_guard m_outer m_inner;
       sr_reducts := top_reducts |}.

  (* (InOut.2) COMMIT (ATOMIC NESTED EMIT): the two `M` occurrences agree (with the outer element
     premises present) => the guarded consume commits, splicing the OUTER structural reducts with
     `...rest2` — the In/Out COMM fires. The depth-2 twin of `open_commits_when_names_agree`. *)
  Theorem inout_commits_when_M_agrees :
    forall facts premises m_outer m_inner top_reducts,
      all_present facts premises ->
      m_outer = m_inner ->
      struct_attempt facts (inout_rule premises m_outer m_inner top_reducts)
        (insert_all top_reducts facts).
  Proof.
    intros facts premises m_outer m_inner top_reducts Hpres Heq.
    apply (struct_commit facts (inout_rule premises m_outer m_inner top_reducts)).
    - exact Hpres.
    - unfold inout_rule; simpl. apply inout_guard_iff_M_agrees. exact Heq.
  Qed.

  (* (InOut.3) REJECT-SAFE: the `M` occurrences disagree => the guard is false, so the consume does
     NOT commit and consumes NO data (next = facts) — the mismatched-name Ambient soup rests, so
     `in`/`out` cannot enter/leave a NON-matching ambient. The depth-2 twin of
     `open_disagree_no_commit`; the cross-LEVEL `check_commit` rollback. *)
  Theorem inout_disagree_no_commit :
    forall facts premises m_outer m_inner top_reducts next,
      m_outer <> m_inner ->
      struct_attempt facts (inout_rule premises m_outer m_inner top_reducts) next ->
      next = facts.
  Proof.
    intros facts premises m_outer m_inner top_reducts next Hne Hatt.
    apply (struct_false_guard_no_commit facts (inout_rule premises m_outer m_inner top_reducts) next).
    - unfold inout_rule; simpl.
      destruct (inout_guard m_outer m_inner) eqn:E; [ | reflexivity ].
      exfalso. apply Hne. apply inout_guard_iff_M_agrees. exact E.
    - exact Hatt.
  Qed.

  (* (InOut.4) NO FABRICATION: every fact after the In/Out consume is one of the STRUCTURAL top
     reducts (each a re-assembled projection of a consumed element — a sub-term of the redex) or was
     already present in `...rest2` — the receiver FORWARDS the σ-delivered reducts, never fabricates
     one. The depth-2 twin of `open_no_fabrication`. *)
  Theorem inout_no_fabrication :
    forall facts premises m_outer m_inner top_reducts next x,
      struct_attempt facts (inout_rule premises m_outer m_inner top_reducts) next ->
      In x next ->
      In x top_reducts \/ In x facts.
  Proof.
    intros facts premises m_outer m_inner top_reducts next x Hatt Hin.
    inversion Hatt; subst.
    - apply insert_all_membership in Hin. exact Hin.
    - right. exact Hin.
    - right. exact Hin.
  Qed.

  (* (InOut.5-In) THE FIRED BAG IS THE In-REDUCT `{ m[{ n[{P, ...rest1}], R }], ...rest2 }` (ATOMIC,
     TWO-LEVEL): on commit (`M` agree), the result contains the reassembled moving ambient
     `m[{ n[{P, ...rest1}], R }]` AND every element of `...rest2` (= facts) — the OUTER splice — and,
     multiplicity-preserving, the INNER `...rest1` splices inside the innermost bag (the depth-2
     reduct-id equation `inrule_reduct_ids_two_level`). The depth-2 twin of
     `open_emits_both_reducts_and_splices_rest`, with the emit reproducing the host `instantiate`
     NESTED re-assembly (rest1 inner, rest2 outer, DISJOINT levels, no cross-absorption). *)
  Theorem inrule_emits_nested_reduct_and_splices_both_rests :
    forall facts premises m_outer m_inner
           (wrap_ambient : list nat -> nat) (P_id R_id : nat) (rest1_ids rest2_ids : list nat),
      all_present facts premises ->
      m_outer = m_inner ->
      exists next,
        struct_attempt facts
          (inout_rule premises m_outer m_inner
             [wrap_ambient (wrap_ambient (P_id :: rest1_ids) :: R_id :: nil)]) next
        /\ In (wrap_ambient (wrap_ambient (P_id :: rest1_ids) :: R_id :: nil)) next
        /\ (forall r, In r facts -> In r next)
        /\ flatten (map Leaf
                      (wrap_ambient (wrap_ambient (flatten (map Leaf (P_id :: nil) ++ (Sub rest1_ids :: nil)))
                                     :: R_id :: nil) :: nil)
                    ++ (Sub rest2_ids :: nil))
           = wrap_ambient (wrap_ambient (P_id :: rest1_ids) :: R_id :: nil) :: rest2_ids.
  Proof.
    intros facts premises m_outer m_inner wrap_ambient P_id R_id rest1_ids rest2_ids Hpres Heq.
    exists (insert_all [wrap_ambient (wrap_ambient (P_id :: rest1_ids) :: R_id :: nil)] facts).
    split; [| split; [| split ] ].
    - apply inout_commits_when_M_agrees; assumption.
    - apply insert_all_membership. left. simpl. left. reflexivity.
    - intros r Hr. apply insert_all_membership. right. exact Hr.
    - apply inrule_reduct_ids_two_level.
  Qed.

  (* The REDECLARED-Out two-level reduct-id equation, proved LOCALLY (the ejection-shaped
     NS.4-Out `outrule_reduct_ids_two_level` remains in InRhoAcMatchMultiset as the InOutDemo demo
     family's equation): the fired bag is EXACTLY the two outer reducts — NO top-level `Sub`
     splice — with `rest1` spliced inside the moving `n[…]` AND `rest2` spliced inside the
     residual-keeping `m[…]` (the A-S5.4b TEMPLATE-CONSUMED rest placement; `map Leaf nil` is the
     rest-only inner bag's empty fixed-element list). Each bag level is an independent
     `fired_bag_is_reducts_splice_rest`; the top level is a pure `flatten_map_leaf` (two Leaf
     reducts, nothing spliced). *)
  Lemma outrule_residual_kept_inside_reduct_ids :
    forall (wrap_ambient : list nat -> nat) (P_id : nat) (rest1_ids rest2_ids : list nat),
      flatten (map Leaf
                 (wrap_ambient (flatten (map Leaf (P_id :: nil) ++ (Sub rest1_ids :: nil)))
                  :: wrap_ambient (flatten (map Leaf nil ++ (Sub rest2_ids :: nil))) :: nil))
      = wrap_ambient (P_id :: rest1_ids) :: wrap_ambient rest2_ids :: nil.
  Proof.
    intros wrap_ambient P_id rest1_ids rest2_ids.
    rewrite !fired_bag_is_reducts_splice_rest. rewrite flatten_map_leaf. reflexivity.
  Qed.

  (* (InOut.5-Out) THE FIRED BAG IS THE REDECLARED (Red Out) REDUCT `{ n[{P, ...rest1}],
     m[{...rest2}] }` (ATOMIC, TWO-LEVEL, RESIDUAL KEPT INSIDE): on commit, the result contains
     BOTH outer reducts — the moving ambient `n[{P, ...rest1}]` AND the residual-keeping
     `m[{...rest2}]` — and every prior fact is preserved; the reduct-id equation certifies the
     TEMPLATE-CONSUMED placement (rest1 inside `n[…]`, rest2 inside `m[…]`, NOTHING at the top —
     the residual never crosses the ambient membrane, per C-G (Red Out) / AM-1). The dual
     two-level splice; the OutRule emits TWO outer reducts exactly as `OpenRule` emits P and Q. *)
  Theorem outrule_emits_residual_kept_inside_and_splices_both_rests :
    forall facts premises m_outer m_inner
           (wrap_ambient : list nat -> nat) (P_id : nat) (rest1_ids rest2_ids : list nat),
      all_present facts premises ->
      m_outer = m_inner ->
      exists next,
        struct_attempt facts
          (inout_rule premises m_outer m_inner
             [wrap_ambient (P_id :: rest1_ids); wrap_ambient rest2_ids]) next
        /\ In (wrap_ambient (P_id :: rest1_ids)) next
        /\ In (wrap_ambient rest2_ids) next
        /\ (forall r, In r facts -> In r next)
        /\ flatten (map Leaf
                      (wrap_ambient (flatten (map Leaf (P_id :: nil) ++ (Sub rest1_ids :: nil)))
                       :: wrap_ambient (flatten (map Leaf nil ++ (Sub rest2_ids :: nil))) :: nil))
           = wrap_ambient (P_id :: rest1_ids) :: wrap_ambient rest2_ids :: nil.
  Proof.
    intros facts premises m_outer m_inner wrap_ambient P_id rest1_ids rest2_ids Hpres Heq.
    exists (insert_all [wrap_ambient (P_id :: rest1_ids); wrap_ambient rest2_ids] facts).
    split; [| split; [| split; [| split ] ] ].
    - apply inout_commits_when_M_agrees; assumption.
    - apply insert_all_membership. left. simpl. left. reflexivity.
    - apply insert_all_membership. left. simpl. right. left. reflexivity.
    - intros r Hr. apply insert_all_membership. right. exact Hr.
    - apply outrule_residual_kept_inside_reduct_ids.
  Qed.

  (* (InOut.5-Out-singleton) THE SINGLETON FIRES: the empty-rest instantiation
     `rest1 = rest2 = []` is the C-G singleton `m[{n[{out(m,p)}]}] → {n[{p}], m[{}]}` — the redex
     the pre-A-S5.4b ejection shape could NEVER fire (C-G reaches it via (Struct Zero Par); the
     redeclaration's empty-rest legality discharges it directly; the emitted `m[{}]` vs C-G's
     `m[0]` is the documented `{}`/`0` fragment deviation). *)
  Corollary outrule_singleton_fires :
    forall facts premises m_outer m_inner (wrap_ambient : list nat -> nat) (P_id : nat),
      all_present facts premises ->
      m_outer = m_inner ->
      exists next,
        struct_attempt facts
          (inout_rule premises m_outer m_inner
             [wrap_ambient (P_id :: nil); wrap_ambient nil]) next
        /\ In (wrap_ambient (P_id :: nil)) next
        /\ In (wrap_ambient nil) next.
  Proof.
    intros facts premises m_outer m_inner wrap_ambient P_id Hpres Heq.
    destruct (outrule_emits_residual_kept_inside_and_splices_both_rests
                facts premises m_outer m_inner wrap_ambient P_id nil nil Hpres Heq)
      as (next & Hatt & Hmoving & Hresidual & _).
    exists next. split; [exact Hatt | split; [exact Hmoving | exact Hresidual]].
  Qed.

  (* (InOut.6) GENERALIZES the Comm single-reduct emit: the InRule fires ONE outer reduct (the
     reassembled `m[…]`), so its outer splice is EXACTLY GuardedCommSoundness's single `insert_exact`
     — the InRule `{ m[…], ...rest2 }` outer reassembly IS the Comm `{reduct, ...rest}` reassembly,
     lifted to a nested top element. The depth-2 twin of `open_generalizes_comm_single_reduct`. *)
  Theorem inrule_single_top_reduct_is_insert_exact :
    forall inrule_top facts,
      insert_all [inrule_top] facts = insert_exact inrule_top facts.
  Proof. intros inrule_top facts. reflexivity. Qed.

  (* (InOut.7) ORACLE AGREEMENT: the installed receiver's `condition` guard equals the host's
     cross-level non-linear ambient-name check (`inout_guard` = `ac_nl_guard` over the two `M` slots)
     — the in-Rho In/Out gate certifies the SAME oracle AcNonLinearConsistency certifies. The depth-2
     twin of `open_oracle_agreement`. *)
  Theorem inout_oracle_agreement :
    forall premises m_outer m_inner top_reducts,
      sr_guard (inout_rule premises m_outer m_inner top_reducts)
      = inout_guard m_outer m_inner.
  Proof. intros. reflexivity. Qed.

  (* ========================================================================================= *)
  (* 3. THE CROSS-LEVEL GUARD, GUARDED-ATTEMPT FORM — inherited VERBATIM from AcNonLinearConsistency. *)
  (*                                                                                             *)
  (* AmbientOpenFiring's `struct_attempt` firing (above) supplies the guard as the plain bool       *)
  (* `inout_guard`; here we ALSO exhibit the commit/reject in AcNonLinearConsistency's own            *)
  (* `guarded_attempt` shape (`eq_rule` over the `gather`ed cross-level occurrences), so the veto is  *)
  (* demonstrably `ac_nl_cross_level_commits` / `ac_nl_cross_level_reject_safe` — not re-proved.       *)
  (* ========================================================================================= *)

  (* (InOut.8) CROSS-LEVEL GUARDED COMMIT: with the two structured-element premises present and the
     outer/inner `M` slots equal, the depth-2 COMM commits (adds the reassembled output) — the
     `guarded_attempt` form, <- `ac_nl_cross_level_commits`. *)
  Theorem inout_cross_level_guarded_commit :
    forall facts premises m_outer m_inner output,
      all_present facts premises ->
      m_outer = m_inner ->
      guarded_attempt facts
        (eq_rule premises (gather [0; 1] (inout_selection m_outer m_inner) 0) output)
        (insert_exact output facts).
  Proof.
    intros facts premises m_outer m_inner output Hpres Heq.
    apply (ac_nl_cross_level_commits facts premises 0 1 (inout_selection m_outer m_inner) 0 output).
    - exact Hpres.
    - unfold inout_selection. simpl. exact Heq.
  Qed.

  (* (InOut.9) CROSS-LEVEL GUARDED REJECT-SAFE: disagreeing outer/inner `M` slots => NO commit and NO
     data consumed (next = facts) — the `guarded_attempt` form, <- `ac_nl_cross_level_reject_safe`. *)
  Theorem inout_cross_level_guarded_reject_safe :
    forall facts premises m_outer m_inner output next,
      m_outer <> m_inner ->
      guarded_attempt facts
        (eq_rule premises (gather [0; 1] (inout_selection m_outer m_inner) 0) output) next ->
      next = facts.
  Proof.
    intros facts premises m_outer m_inner output next Hne Hatt.
    apply (ac_nl_cross_level_reject_safe facts premises 0 1 (inout_selection m_outer m_inner) 0 output next).
    - unfold inout_selection. simpl. exact Hne.
    - exact Hatt.
  Qed.

  (* ========================================================================================= *)
  (* 4. THE OPERATIONAL STEP-CORRESPONDENCE (source In/Out reduction <=> lowered In/Out COMM).    *)
  (*                                                                                             *)
  (* The In/Out configuration is modeled — as `LinearCommCorrespondence` models the linear COMM —  *)
  (* by a source state and its lowered in-Rho image, IDENTICAL in fields (the lowering is a         *)
  (* field-copy) so completeness/soundness are field-copy proofs; the DEPTH-2 CONTENT lives in the  *)
  (* FIRING (the cross-level `inout_guard` GATES the step; the fired `OUT` is the nested reduct       *)
  (* certified above and by `inout_out_is_report_faithful` below). This is the operational firing     *)
  (* FV in the shape the Stage-5 capstone's `fwd_/bwd_acnested` Hypotheses consume — the depth-2      *)
  (* analogue of `comm_step_complete` / `comm_step_sound`, guarded by the cross-level name check.     *)
  (* ========================================================================================= *)

  (* The source In/Out configuration: the two cross-level ambient names to be checked, the one-shot
     nested receiver's armed flag, and the resting-send barb (the fired OUT bag). *)
  Record InOutSrcState : Type := {
    ios_m_outer : Fact;
    ios_m_inner : Fact;
    ios_armed : bool;
    ios_outputs : list Fact
  }.

  (* The lowered in-Rho In/Out configuration — the SAME fields (the σ-receiver install is a
     field-copy of the source redex's cross-level names + armed receiver + outputs). *)
  Record InOutRhoState : Type := {
    ior_m_outer : Fact;
    ior_m_inner : Fact;
    ior_armed : bool;
    ior_outputs : list Fact
  }.

  Definition lower_inout (s : InOutSrcState) : InOutRhoState :=
    {| ior_m_outer := ios_m_outer s;
       ior_m_inner := ios_m_inner s;
       ior_armed := ios_armed s;
       ior_outputs := ios_outputs s |}.

  (* One source In/Out reduction step: the nested receiver is armed AND the cross-level guard commits
     (`inout_guard M_outer M_inner = true`, i.e. `M_outer ≡ M_inner`); the fired OUT reduct rests in
     the barb and the one-shot receiver disarms. The datum is the fired top reduct (the reassembled
     `m[…]`/`n[…]`, whose depth-2 structure is certified by section 2's emit lemmas). *)
  Definition source_inout_comm (s : InOutSrcState) (fired : Fact) (s' : InOutSrcState) : Prop :=
    ios_armed s = true
    /\ inout_guard (ios_m_outer s) (ios_m_inner s) = true
    /\ s' =
       {| ios_m_outer := ios_m_outer s;
          ios_m_inner := ios_m_inner s;
          ios_armed := false;
          ios_outputs := fired :: ios_outputs s |}.

  (* The lowered in-Rho In/Out COMM — the SAME guarded consume over the lowered state. *)
  Definition rho_inout_comm (r : InOutRhoState) (fired : Fact) (r' : InOutRhoState) : Prop :=
    ior_armed r = true
    /\ inout_guard (ior_m_outer r) (ior_m_inner r) = true
    /\ r' =
       {| ior_m_outer := ior_m_outer r;
          ior_m_inner := ior_m_inner r;
          ior_armed := false;
          ior_outputs := fired :: ior_outputs r |}.

  Definition inout_barb_equiv (r : InOutRhoState) (s : InOutSrcState) : Prop :=
    forall x, In x (ior_outputs r) <-> In x (ios_outputs s).

  (* The lowering preserves barbs — the field-copy image has the same resting sends. The depth-2
     twin of `lower_preserves_barbs`. *)
  Theorem inout_lower_preserves_barbs : forall s,
    inout_barb_equiv (lower_inout s) s.
  Proof. intros s x. split; intro H; exact H. Qed.

  (* (InOut.STEP-complete) COMPLETENESS: every source In/Out reduction step has a corresponding
     lowered In/Out COMM step with the same observable barbs. The depth-2 twin of
     `comm_step_complete`; the cross-level guard is preserved by the lowering (it copies the names). *)
  Theorem inout_step_complete : forall s fired s',
    source_inout_comm s fired s' ->
    exists r',
      rho_inout_comm (lower_inout s) fired r'
      /\ inout_barb_equiv r' s'.
  Proof.
    intros s fired s' Hstep. destruct Hstep as [Harmed [Hguard Hs']].
    exists {| ior_m_outer := ios_m_outer s;
              ior_m_inner := ios_m_inner s;
              ior_armed := false;
              ior_outputs := fired :: ios_outputs s |}.
    split.
    - unfold rho_inout_comm, lower_inout. cbn.
      split; [exact Harmed | split; [exact Hguard | reflexivity]].
    - subst s'. unfold inout_barb_equiv. cbn. intros x. split; intro H; exact H.
  Qed.

  (* (InOut.STEP-sound) SOUNDNESS: every lowered In/Out COMM step has a source In/Out reduct with the
     same observable barbs. The depth-2 twin of `comm_step_sound`. *)
  Theorem inout_step_sound : forall s fired r',
    rho_inout_comm (lower_inout s) fired r' ->
    exists s',
      source_inout_comm s fired s'
      /\ inout_barb_equiv r' s'.
  Proof.
    intros s fired r' Hstep. destruct Hstep as [Harmed [Hguard Hr']].
    exists {| ios_m_outer := ios_m_outer s;
              ios_m_inner := ios_m_inner s;
              ios_armed := false;
              ios_outputs := fired :: ios_outputs s |}.
    split.
    - unfold source_inout_comm. cbn.
      split; [exact Harmed | split; [ exact Hguard | reflexivity]].
    - subst r'. unfold inout_barb_equiv, lower_inout. cbn. intros x. split; intro H; exact H.
  Qed.

  (* The operational step FIRES under the cross-level guard: whenever a source In/Out step commits,
     the two `M` occurrences agreed (`M_outer ≡ M_inner`) and the fired reduct rests in the barb —
     tying the step-correspondence (section 4) to the cross-level firing semantics (sections 1-2). *)
  Theorem inout_step_fires_under_cross_level_guard : forall s fired s',
    source_inout_comm s fired s' ->
    ios_m_outer s = ios_m_inner s /\ In fired (ios_outputs s').
  Proof.
    intros s fired s' Hstep. destruct Hstep as [_ [Hguard Hs']]. split.
    - apply inout_guard_iff_M_agrees. exact Hguard.
    - subst s'. cbn. left. reflexivity.
  Qed.

  (* A source In/Out step CAN fire with the concrete InRule nested reduct
     `m[{ n[{P, ...rest1}], R }]` as its emitted OUT, which then rests in the barb — the operational
     step instantiated at the depth-2 reduct the emit lemma (InOut.5-In) certifies. Ties the abstract
     `fired` datum to the concrete In/Out contractum. *)
  Corollary inout_step_emits_inrule_nested_reduct :
    forall s (wrap_ambient : list nat -> nat) (P_id R_id : nat) (rest1_ids : list nat),
      ios_armed s = true ->
      ios_m_outer s = ios_m_inner s ->
      exists s',
        source_inout_comm s (wrap_ambient (wrap_ambient (P_id :: rest1_ids) :: R_id :: nil)) s'
        /\ In (wrap_ambient (wrap_ambient (P_id :: rest1_ids) :: R_id :: nil)) (ios_outputs s').
  Proof.
    intros s wrap_ambient P_id R_id rest1_ids Harmed Hagree.
    eexists. split.
    - unfold source_inout_comm. split; [ exact Harmed | split ].
      + apply inout_guard_iff_M_agrees. exact Hagree.
      + reflexivity.
    - cbn. left. reflexivity.
  Qed.

End AmbientInOutFiring.

(* ============================================================================================= *)
(* 5. OUT = ⟦R⟧σ — the fired In/Out OUT is the SUBJECT's depth-2 nested reduct.                    *)
(*                                                                                                 *)
(* Reusing the In/Out FV's `outer/inner_located_is_spread` pair-Hypothesis VERBATIM (the sanctioned *)
(* `..._is_spread_of_subject` Section idiom), the fired OUT bag on a LOCATED depth-2 match is the    *)
(* SUBJECT's nested reduct: located = subject at BOTH nesting levels, the connective-bound σ is a    *)
(* report delivery, and the reduct reassembles NESTED (rest1 inner, rest2 outer). Directly           *)
(* `InRhoAcMatchMultiset.nested_structural_ac_spread_is_report_faithful`, so the In/Out firing's      *)
(* payload is the depth-2 `⟦R⟧σ`, never a corrupted report decoy.                                    *)
(* ============================================================================================= *)

Section AmbientInOutReductFaithful.

  (* The SUBJECT outer operand bag (read off the SAME subtree the host oracle reconstructs from σ) and
     the LOCATED outer bag the nested MATCH receiver picks from the spread — order-independent, so a
     PERMUTATION of the subject. The sanctioned depth-2 spread pair-Hypothesis, verbatim from the FV. *)
  Variable subject_outer_bag located_outer_bag : list NestedElem.
  Hypothesis outer_located_is_spread :
    Permutation located_outer_bag subject_outer_bag.

  (* The moving-ambient's INNER bag: the SUBJECT inner bag (one level down) and the LOCATED inner bag
     the SAME receiver's connective pattern picks ONE LEVEL DOWN — also a spread permutation. *)
  Variable subject_inner_bag located_inner_bag : list StructElem.
  Hypothesis inner_located_is_spread :
    Permutation located_inner_bag subject_inner_bag.

  (* (InOut.OUT) OUT = ⟦R⟧σ (In AND Out): for a LOCATED depth-2 match (the spread MATCH), (a) the SAME
     depth-2 partition is a SUBJECT-bag partition at BOTH levels (located = subject), (b) the σ bound
     (cross-level names, both remainders, inner reducts) is exactly a report delivery from the subject,
     and (c) the fired reduct reassembles NESTED, splicing `rest1` at the inner level and `rest2` at
     the outer level, multiplicity-preserving at BOTH. So the fired In/Out OUT = `⟦R⟧σ`, sourced from
     the SUBJECT, never the report. Directly `nested_structural_ac_spread_is_report_faithful`. *)
  Theorem inout_out_is_report_faithful :
    forall outer_sel rest2 inner_sel rest1
           (wrap_ambient : list nat -> nat) (P_id R_id : nat) (rest1_ids rest2_ids : list nat),
      nested_match outer_sel rest2 inner_sel rest1 located_outer_bag located_inner_bag ->
      nested_match outer_sel rest2 inner_sel rest1 subject_outer_bag subject_inner_bag
      /\ (exists osel r2 isel r1,
            nested_match osel r2 isel r1 subject_outer_bag subject_inner_bag
            /\ delivered_nested_sigma osel r2 isel r1
               = delivered_nested_sigma outer_sel rest2 inner_sel rest1)
      /\ flatten (map Leaf
                    (wrap_ambient (wrap_ambient (flatten (map Leaf (P_id :: nil) ++ (Sub rest1_ids :: nil)))
                                   :: R_id :: nil) :: nil)
                  ++ (Sub rest2_ids :: nil))
         = wrap_ambient (wrap_ambient (P_id :: rest1_ids) :: R_id :: nil) :: rest2_ids.
  Proof.
    intros outer_sel rest2 inner_sel rest1 wrap_ambient P_id R_id rest1_ids rest2_ids Hmatch.
    exact (nested_structural_ac_spread_is_report_faithful
             subject_outer_bag located_outer_bag outer_located_is_spread
             subject_inner_bag located_inner_bag inner_located_is_spread
             outer_sel rest2 inner_sel rest1
             wrap_ambient P_id R_id rest1_ids rest2_ids Hmatch).
  Qed.

End AmbientInOutReductFaithful.

(* Zero-admission confirmation. *)
Print Assumptions inout_guard_iff_M_agrees.
Print Assumptions inout_guard_is_cross_level_ac_nl_guard.
Print Assumptions inout_commits_when_M_agrees.
Print Assumptions inout_disagree_no_commit.
Print Assumptions inout_no_fabrication.
Print Assumptions inrule_emits_nested_reduct_and_splices_both_rests.
Print Assumptions outrule_residual_kept_inside_reduct_ids.
Print Assumptions outrule_emits_residual_kept_inside_and_splices_both_rests.
Print Assumptions outrule_singleton_fires.
Print Assumptions inrule_single_top_reduct_is_insert_exact.
Print Assumptions inout_oracle_agreement.
Print Assumptions inout_cross_level_guarded_commit.
Print Assumptions inout_cross_level_guarded_reject_safe.
Print Assumptions inout_lower_preserves_barbs.
Print Assumptions inout_step_complete.
Print Assumptions inout_step_sound.
Print Assumptions inout_step_fires_under_cross_level_guard.
Print Assumptions inout_step_emits_inrule_nested_reduct.
Print Assumptions inout_out_is_report_faithful.
