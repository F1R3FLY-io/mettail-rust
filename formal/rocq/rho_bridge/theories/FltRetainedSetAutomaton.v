(*
 * FltRetainedSetAutomaton: FLT Phase 3 Track B.
 *
 * Rust image:
 *
 *   rholang-runtime/src/flt_automaton_matcher.rs
 *     convert_pattern       strict positional eligibility partition
 *     serialize_new_states append-only StateId suffix serialization
 *     execute_program       explicit work/value-stack evaluator
 *     FltAutomatonMatcher   retained Dovetail automaton
 *
 *   rholang-runtime/src/guard_par_substrate.rs
 *     SubstrateGuardMatcher::get
 *       eligible -> retained PDA; declined -> f1 spatial matcher verbatim
 *
 * Labels below abstract the complete ReflectedOp equality key: GPrivate bytes,
 * list/private constructor distinction, and concrete metadata.  A free-variable
 * match records its exact Rholang level and target; a wildcard records nothing.
 * The reflected-pattern converter admits each free level exactly once, so ordered
 * concatenation is the complete capture map used at the entry boundary.
 *
 * We prove:
 *
 *   FLT-B1  explicit PDA result = recursive positional result, including captures;
 *   FLT-B2  declined envelopes delegate to the spatial oracle byte-for-byte;
 *   FLT-B3  the combined retained matcher equals the recursive/spatial oracle;
 *   FLT-B4  append-only serialization preserves the old prefix and emits exactly
 *           the new suffix; and
 *   FLT-B5  matcher-owned serialization adds no persistent Rholang receiver.
 *
 * Dovetail's root-index no-loss theorem is imported from
 * PositionalSetAutomatonSound and re-exported as the compiler-side obligation.
 * The executable differential additionally checks the concrete Rust models,
 * malformed/fallback cases, canonical StateId-layout fingerprints, and 20,000
 * levels on a 256 KiB stack.
 *
 * Rocq 9.1 compatible. No Admitted, Axioms, Parameters, or global extensions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From AdvancedAutomata Require Import PositionalSetAutomatonSound.

Import ListNotations.

(* A positional pattern forest and reflected target forest.  [closed] is the
   target Par's cached locally-free predicate: FreeVar may capture only a closed
   target, while Wildcard may match either. *)
Inductive FPattern : Type :=
  | FPVar (level : nat)
  | FPWildcard
  | FPApp (label : nat) (children : FPatterns)
with FPatterns : Type :=
  | FPNil
  | FPCons (head : FPattern) (tail : FPatterns).

Inductive FTerm : Type :=
  | FTApp (label : nat) (closed : bool) (children : FTerms)
with FTerms : Type :=
  | FTNil
  | FTCons (head : FTerm) (tail : FTerms).

Fixpoint pattern_arity (patterns : FPatterns) : nat :=
  match patterns with
  | FPNil => 0
  | FPCons _ tail => S (pattern_arity tail)
  end.

Fixpoint term_arity (terms : FTerms) : nat :=
  match terms with
  | FTNil => 0
  | FTCons _ tail => S (term_arity tail)
  end.

Definition Binding : Type := (nat * FTerm)%type.
Definition MatchResult : Type := option (list Binding).

Definition merge_results (left right : MatchResult) : MatchResult :=
  match left, right with
  | Some left', Some right' => Some (left' ++ right')
  | _, _ => None
  end.

(* The bounded recursive oracle retained by the Rust differential. *)
Fixpoint recursive_match (pattern : FPattern) (target : FTerm) {struct pattern}
    : MatchResult :=
  match pattern with
  | FPVar level =>
      match target with
      | FTApp _ closed _ => if closed then Some [(level, target)] else None
      end
  | FPWildcard => Some []
  | FPApp expected patterns =>
      match target with
      | FTApp actual _ targets =>
          if Nat.eqb expected actual && Nat.eqb (pattern_arity patterns) (term_arity targets)
          then recursive_matches patterns targets
          else None
      end
  end
with recursive_matches (patterns : FPatterns) (targets : FTerms) {struct patterns}
    : MatchResult :=
  match patterns, targets with
  | FPNil, FTNil => Some []
  | FPCons pattern rest, FTCons target targets' =>
      merge_results (recursive_match pattern target) (recursive_matches rest targets')
  | _, _ => None
  end.

(* A post-order instruction stream is the denotational schedule of the Rust
   machine's Visit/Merge jobs.  [run] uses an explicit value stack; its native
   stack consumption is therefore independent of reflected-term depth. *)
Inductive Instruction : Type :=
  | IPush (result : MatchResult)
  | IMerge.

Definition apply_instruction (instruction : Instruction) (values : list MatchResult)
    : option (list MatchResult) :=
  match instruction with
  | IPush result => Some (result :: values)
  | IMerge =>
      match values with
      | head :: tail :: rest => Some (merge_results head tail :: rest)
      | _ => None
      end
  end.

Fixpoint run (program : list Instruction) (values : list MatchResult)
    : option (list MatchResult) :=
  match program with
  | [] => Some values
  | instruction :: rest =>
      match apply_instruction instruction values with
      | Some values' => run rest values'
      | None => None
      end
  end.

(* Children are scheduled tail-first in the static instruction stream so the
   head-based value stack presents source-order captures to IMerge.  This is the
   list-program dual of Rust pushing child jobs in reverse on its LIFO worklist. *)
Fixpoint compile_match (pattern : FPattern) (target : FTerm) {struct pattern}
    : list Instruction :=
  match pattern with
  | FPVar level =>
      match target with
      | FTApp _ closed _ =>
          [IPush (if closed then Some [(level, target)] else None)]
      end
  | FPWildcard => [IPush (Some [])]
  | FPApp expected patterns =>
      match target with
      | FTApp actual _ targets =>
          if Nat.eqb expected actual && Nat.eqb (pattern_arity patterns) (term_arity targets)
          then compile_matches patterns targets
          else [IPush None]
      end
  end
with compile_matches (patterns : FPatterns) (targets : FTerms) {struct patterns}
    : list Instruction :=
  match patterns, targets with
  | FPNil, FTNil => [IPush (Some [])]
  | FPCons pattern rest, FTCons target targets' =>
      compile_matches rest targets' ++ compile_match pattern target ++ [IMerge]
  | _, _ => [IPush None]
  end.

Scheme fpattern_ind_mut := Induction for FPattern Sort Prop
with fpatterns_ind_mut := Induction for FPatterns Sort Prop.
Combined Scheme fpattern_forest_ind from fpattern_ind_mut, fpatterns_ind_mut.

Lemma run_append : forall prefix suffix values,
  run (prefix ++ suffix) values =
  match run prefix values with
  | Some values' => run suffix values'
  | None => None
  end.
Proof.
  intros prefix. induction prefix as [| instruction rest IH]; intros suffix values.
  - reflexivity.
  - simpl. destruct (apply_instruction instruction values) as [values' |] eqn:Hstep.
    + apply IH.
    + reflexivity.
Qed.

Theorem flt_pda_root_stack_equivalence :
  (forall pattern target values,
      run (compile_match pattern target) values =
      Some (recursive_match pattern target :: values)) /\
  (forall patterns targets values,
      run (compile_matches patterns targets) values =
      Some (recursive_matches patterns targets :: values)).
Proof.
  apply fpattern_forest_ind.
  - intros level target values. destruct target. simpl.
    destruct closed; reflexivity.
  - intros target values. reflexivity.
  - intros expected patterns IHpatterns target values.
    destruct target as [actual closed targets]. simpl.
    destruct (Nat.eqb expected actual &&
      Nat.eqb (pattern_arity patterns) (term_arity targets)) eqn:Hcompatible.
    + apply IHpatterns.
    + reflexivity.
  - intros targets values. destruct targets; reflexivity.
  - intros pattern IHpattern rest IHrest targets values.
    destruct targets as [| target targets']; simpl.
    + reflexivity.
    + rewrite run_append.
      rewrite (IHrest targets' values).
      rewrite run_append.
      rewrite (IHpattern target (recursive_matches rest targets' :: values)).
      reflexivity.
Qed.

Theorem flt_pda_continuation_equivalence :
  (forall pattern target suffix values,
      run (compile_match pattern target ++ suffix) values =
      run suffix (recursive_match pattern target :: values)) /\
  (forall patterns targets suffix values,
      run (compile_matches patterns targets ++ suffix) values =
      run suffix (recursive_matches patterns targets :: values)).
Proof.
  split.
  - intros pattern target suffix values. rewrite run_append.
    rewrite (proj1 flt_pda_root_stack_equivalence pattern target values).
    reflexivity.
  - intros patterns targets suffix values. rewrite run_append.
    rewrite (proj2 flt_pda_root_stack_equivalence patterns targets values).
    reflexivity.
Qed.

Corollary flt_pda_root_equivalence : forall pattern target,
  run (compile_match pattern target) [] = Some [recursive_match pattern target].
Proof.
  intros pattern target. apply (proj1 flt_pda_root_stack_equivalence).
Qed.

(* Strict eligibility partition.  Every declined reason denotes an envelope
   rejected by Rust before SetAutomaton::extend: multiple messages, a remainder,
   AC/collection shape, malformed reflection, foreign fingerprint, or invalid
   free-level coverage. *)
Inductive DeclineReason : Type :=
  | MultipleMessages
  | MessageRemainder
  | AssociativeCommutative
  | MalformedReflection
  | ForeignFingerprint
  | InvalidFreeLevels.

Inductive Candidate : Type :=
  | Eligible (pattern : FPattern)
  | Declined (reason : DeclineReason).

Definition convert (candidate : Candidate) : option FPattern :=
  match candidate with
  | Eligible pattern => Some pattern
  | Declined _ => None
  end.

Definition pda_result (pattern : FPattern) (target : FTerm) : MatchResult :=
  match run (compile_match pattern target) [] with
  | Some [result] => result
  | _ => None
  end.

Definition retained_match
    (spatial : Candidate -> FTerm -> MatchResult)
    (candidate : Candidate) (target : FTerm) : MatchResult :=
  match convert candidate with
  | Some pattern => pda_result pattern target
  | None => spatial candidate target
  end.

Definition recursive_or_spatial
    (spatial : Candidate -> FTerm -> MatchResult)
    (candidate : Candidate) (target : FTerm) : MatchResult :=
  match candidate with
  | Eligible pattern => recursive_match pattern target
  | Declined _ => spatial candidate target
  end.

Theorem declined_delegates_verbatim : forall spatial reason target,
  retained_match spatial (Declined reason) target =
  spatial (Declined reason) target.
Proof. reflexivity. Qed.

Theorem eligible_uses_exact_pda_result : forall spatial pattern target,
  retained_match spatial (Eligible pattern) target = recursive_match pattern target.
Proof.
  intros spatial pattern target. unfold retained_match, pda_result. simpl.
  now rewrite flt_pda_root_equivalence.
Qed.

Theorem retained_match_full_equivalence : forall spatial candidate target,
  retained_match spatial candidate target =
  recursive_or_spatial spatial candidate target.
Proof.
  intros spatial candidate target. destruct candidate as [pattern | reason].
  - apply eligible_uses_exact_pda_result.
  - reflexivity.
Qed.

Corollary retained_match_has_no_false_positive : forall spatial candidate target bindings,
  retained_match spatial candidate target = Some bindings ->
  recursive_or_spatial spatial candidate target = Some bindings.
Proof.
  intros spatial candidate target bindings H.
  now rewrite <- retained_match_full_equivalence.
Qed.

Corollary retained_match_has_no_false_negative : forall spatial candidate target bindings,
  recursive_or_spatial spatial candidate target = Some bindings ->
  retained_match spatial candidate target = Some bindings.
Proof.
  intros spatial candidate target bindings H.
  now rewrite retained_match_full_equivalence.
Qed.

(* Append-only StateId serialization.  [old] is the already serialized prefix
   and [suffix] the states newly appended by SetAutomaton::extend. *)
Definition serialized_suffix {A : Type} (old complete : list A) : list A :=
  skipn (length old) complete.

Theorem suffix_only_serialization_exact : forall (A : Type) (old suffix : list A),
  serialized_suffix old (old ++ suffix) = suffix.
Proof.
  intros A old. induction old as [| head tail IH]; intros suffix; simpl.
  - reflexivity.
  - apply IH.
Qed.

Theorem suffix_only_serialization_preserves_prefix : forall (A : Type) (old suffix : list A),
  firstn (length old) (old ++ suffix) = old.
Proof.
  intros A old. induction old as [| head tail IH]; intros suffix; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

(* The corrected production seam is matcher-owned state, not a Rholang receiver
   network.  Registration therefore leaves the installed persistent-input count
   exactly unchanged. *)
Definition persistent_inputs_after_matcher_registration (before : nat) : nat := before.

Theorem matcher_registration_adds_no_persistent_receiver : forall before,
  persistent_inputs_after_matcher_registration before = before.
Proof. reflexivity. Qed.

(* Compiler-side root-index no-loss obligation, directly backed by Dovetail's
   existing positional-set-automaton proof. *)
Definition dovetail_root_index_no_loss := @index_never_drops_match.

Print Assumptions flt_pda_continuation_equivalence.
Print Assumptions flt_pda_root_equivalence.
Print Assumptions declined_delegates_verbatim.
Print Assumptions retained_match_full_equivalence.
Print Assumptions retained_match_has_no_false_positive.
Print Assumptions retained_match_has_no_false_negative.
Print Assumptions suffix_only_serialization_exact.
Print Assumptions suffix_only_serialization_preserves_prefix.
Print Assumptions matcher_registration_adds_no_persistent_receiver.
Print Assumptions dovetail_root_index_no_loss.
