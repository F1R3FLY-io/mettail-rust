(*
 * WholeGsltInRhoOpCorrespondenceOptimalViaSameClts: BUILD-WIRING OPTION (a) for the
 * Stage 5 capstone's (iii) thread — the LITERAL cross-project discharge.
 *
 * WholeGsltInRhoOpCorrespondence.v threads obligation (iii) — the `rem:nonopt`
 * discharge that the SOUND (location-keyed) and OPTIMAL (StateId-trace-keyed) in-Rho
 * channel schemes induce the same CLTS — as three cited Section Hypotheses
 * (`matching_locus_barb` / `matching_locus_fwd` / `matching_locus_bwd`), so the main
 * harness carries no cross-project dependency (option (b), interim). THIS file closes
 * the loop: it imports the landed obligation (iii),
 * `advanced_automata/InRhoSameCLTSWeakBisim.same_clts_weak_bisim`, and proves that
 * the SAME theorem discharges the two step hypotheses' EXACT shapes — witnessing that
 * the option-(b) hypotheses are backed by the real (iii) theorem, not fictional.
 *
 * The two `matching_locus_*` step hypotheses ARE the two clauses of
 * `same_clts_weak_bisim` (a weak bisimulation), read with the harness's orientation
 * `Rso s t := R t s` (the sound config `s` relates to its optimal image `t`; the (iii)
 * relation `R` equates the fired-redex sets and is stated optimal-first):
 *   - matching_locus_fwd (SOUND fires => OPTIMAL matches) = the bisimulation's SECOND
 *     clause;
 *   - matching_locus_bwd (OPTIMAL fires => SOUND matches) = the bisimulation's FIRST
 *     clause.
 *
 * The barb hypothesis is NOT reproduced here: `InRhoSameCLTSWeakBisim` is explicitly a
 * SCHEDULE / labelled-transition-level result (its header, model boundary: it does NOT
 * model Par/RSpace, so it defines no resting-send barb). In the whole-⟦G⟧ setting the
 * barb is the resting-send multiset — a function of the fired-redex set that `R`
 * equates — so `matching_locus_barb` is discharged downstream of (iii), not inside it.
 * The two STEP clauses are the load-bearing content of the `rem:nonopt` discharge, and
 * they compose in `WholeGsltInRhoOpCorrespondence.whole_gslt_opcorr_over_optimal_matching`.
 *
 * This file exists to VALIDATE build-wiring option (a): a RhoBridge theory importing
 * `From AdvancedAutomata Require Import ...` compiles under the capped target with the
 * `-Q ../advanced_automata/theories AdvancedAutomata` edge added to
 * rho_bridge/_CoqProject (advanced_automata is built before rho_bridge in the Makefile
 * `rocq-support` prerequisite order).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions, no Parameters.
 *)

From Stdlib Require Import List.
Import ListNotations.
From AdvancedAutomata Require Import PositionalSetAutomatonSound.
From AdvancedAutomata Require Import SymbolOnceInjective.
From AdvancedAutomata Require Import InRhoSameCLTSWeakBisim.

(* ---- generic extraction: EITHER clause of a weak bisimulation has a matching_locus
   shape (orientation `Rso s t := Rel t s`) ---- *)

(* SOUND fires => OPTIMAL matches, from the bisimulation's SECOND clause. Here `T_sound`
   is the second (sound) transition system and `T_opt` the first (optimal). *)
Lemma matching_locus_fwd_from_bisim :
  forall (Rel : Cfg -> Cfg -> Prop) (T_opt T_sound : Cfg -> Obs -> Cfg -> Prop),
    is_weak_bisimulation Rel T_opt T_sound ->
    forall s t l s', Rel t s -> T_sound s l s' -> exists t', T_opt t l t' /\ Rel t' s'.
Proof.
  intros Rel T_opt T_sound Hbisim s t l s' Hrel Hstep.
  destruct Hbisim as [_ Hclause2].
  exact (Hclause2 t s l s' Hrel Hstep).
Qed.

(* OPTIMAL fires => SOUND matches, from the bisimulation's FIRST clause. *)
Lemma matching_locus_bwd_from_bisim :
  forall (Rel : Cfg -> Cfg -> Prop) (T_opt T_sound : Cfg -> Obs -> Cfg -> Prop),
    is_weak_bisimulation Rel T_opt T_sound ->
    forall s t l t', Rel t s -> T_opt t l t' -> exists s', T_sound s l s' /\ Rel t' s'.
Proof.
  intros Rel T_opt T_sound Hbisim s t l t' Hrel Hstep.
  destruct Hbisim as [Hclause1 _].
  exact (Hclause1 t s l t' Hrel Hstep).
Qed.

Section OptimalViaSameClts.
  (* The (iii) firing context: the enabled redexes, their matched M1 contexts, and
     runtime locations — the same Section interface `InRhoSameCLTSWeakBisim` exposes. *)
  Variable rs : list Redex.
  Variable K : Redex -> Pat.
  Variable site : Redex -> nat.
  Hypothesis K_M1 : forall r, In r rs -> m1_pattern (K r) = true.
  Hypothesis site_inj :
    forall r r', In r rs -> In r' rs -> site r = site r' -> r = r'.

  (* The landed obligation (iii): the sound and optimal in-Rho schemes are weakly
     bisimilar (same CLTS). *)
  Definition iii_bisim := same_clts_weak_bisim rs K site K_M1 site_inj.

  (* matching_locus_fwd, discharged LITERALLY by (iii): every SOUND matching COMM
     `weak_step rs K Channel (sound_ch K site) (sound_key K site)` is matched,
     label-for-label, by an OPTIMAL matching COMM
     `weak_step rs K (option (nat*nat)) (opt_ch K) (optimal_key K)` under `R`. This is
     exactly WholeGsltInRhoOpCorrespondence's `matching_locus_fwd` Section hypothesis,
     with Rso := (fun s t => R t s), gstep := weak_step sound, gstep_opt := weak_step
     opt (types inferred from `iii_bisim`). *)
  Definition matching_locus_fwd_holds := matching_locus_fwd_from_bisim R _ _ iii_bisim.

  (* matching_locus_bwd, discharged LITERALLY by (iii): every OPTIMAL matching COMM is
     matched by a SOUND matching COMM. *)
  Definition matching_locus_bwd_holds := matching_locus_bwd_from_bisim R _ _ iii_bisim.

End OptimalViaSameClts.

(* Zero-admission confirmation. *)
Print Assumptions matching_locus_fwd_from_bisim.
Print Assumptions matching_locus_bwd_from_bisim.
Print Assumptions matching_locus_fwd_holds.
Print Assumptions matching_locus_bwd_holds.
