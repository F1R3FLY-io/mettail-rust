(*
 * FormulaPdaEquivalence: recursive Rholang formula semantics = explicit PDA.
 *
 * The proof models every reduction performed by
 * languages/src/rholang/formula.rs::analyze_formula: static-false/static-true facts,
 * strong-Kleene host verdicts, implication, and arbitrary-arity separating conjunction.
 * `compile_formula` defunctionalizes the recursive specification into a post-order
 * instruction stream; `run` is its explicit value-stack machine. The main theorem is
 * suffix-parametric, so it proves each compiled subtree preserves its continuation.
 *
 * The production Rust traversal constructs the same post-order schedule dynamically with
 * Visit/Build work items and additionally memoizes pure node results by address. The executable
 * test runtime/tests/formula_pda_source_equivalence.rs imports that exact Rust source and checks
 * its memoized implementation against the old recursive equations. This proof establishes the
 * unbounded semantic argument underneath that source-level differential.
 *
 * Rocq 9.1 compatible. No axioms and no proof holes.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Record static_facts : Type := mkStaticFacts {
  statically_false : bool;
  statically_true : bool
}.

Record formula_facts : Type := mkFormulaFacts {
  static_result : static_facts;
  host_result : option bool
}.

Definition settle (sf : static_facts) (otherwise : option bool) : option bool :=
  if statically_false sf then Some false
  else if statically_true sf then Some true
  else otherwise.

Definition kleene_and (left right : option bool) : option bool :=
  match left, right with
  | Some false, _ => Some false
  | _, Some false => Some false
  | Some true, Some true => Some true
  | _, _ => None
  end.

Definition kleene_or (left right : option bool) : option bool :=
  match left, right with
  | Some true, _ => Some true
  | _, Some true => Some true
  | Some false, Some false => Some false
  | _, _ => None
  end.

Definition conjunction_facts (left right : formula_facts) : formula_facts :=
  let sf := mkStaticFacts
    (statically_false (static_result left) || statically_false (static_result right))
    (statically_true (static_result left) && statically_true (static_result right)) in
  mkFormulaFacts sf (settle sf (kleene_and (host_result left) (host_result right))).

Definition disjunction_facts (left right : formula_facts) : formula_facts :=
  let sf := mkStaticFacts
    (statically_false (static_result left) && statically_false (static_result right))
    (statically_true (static_result left) || statically_true (static_result right)) in
  mkFormulaFacts sf (settle sf (kleene_or (host_result left) (host_result right))).

Definition negation_facts (inner : formula_facts) : formula_facts :=
  let sf := mkStaticFacts
    (statically_true (static_result inner))
    (statically_false (static_result inner)) in
  mkFormulaFacts sf (settle sf (option_map negb (host_result inner))).

Definition implication_facts (antecedent consequent : formula_facts) : formula_facts :=
  let sf := mkStaticFacts
    (statically_true (static_result antecedent) &&
      statically_false (static_result consequent))
    (statically_false (static_result antecedent) ||
      statically_true (static_result consequent)) in
  mkFormulaFacts sf
    (settle sf
      (kleene_or (option_map negb (host_result antecedent)) (host_result consequent))).

Fixpoint any_statically_false (children : list formula_facts) : bool :=
  match children with
  | [] => false
  | child :: rest =>
      statically_false (static_result child) || any_statically_false rest
  end.

Definition separation_facts (children : list formula_facts) : formula_facts :=
  let sf := mkStaticFacts (any_statically_false children) false in
  mkFormulaFacts sf (settle sf None).

(* Mutually inductive forests represent generated PPar's arbitrary child vector without imposing
   a binary-only simplification on the proof. *)
Inductive formula : Type :=
  | FVerum
  | FFalsum
  | FTerm (positive_match : bool)
  | FConjunction (left right : formula)
  | FDisjunction (left right : formula)
  | FNegation (inner : formula)
  | FImplication (antecedent consequent : formula)
  | FSeparation (children : formulas)
with formulas : Type :=
  | FsNil
  | FsCons (head : formula) (tail : formulas).

Fixpoint recursive_eval (input : formula) : formula_facts :=
  match input with
  | FVerum => mkFormulaFacts (mkStaticFacts false true) (Some true)
  | FFalsum => mkFormulaFacts (mkStaticFacts true false) (Some false)
  | FTerm positive_match =>
      mkFormulaFacts (mkStaticFacts false false)
        (if positive_match then Some true else None)
  | FConjunction lhs rhs => conjunction_facts (recursive_eval lhs) (recursive_eval rhs)
  | FDisjunction lhs rhs => disjunction_facts (recursive_eval lhs) (recursive_eval rhs)
  | FNegation inner => negation_facts (recursive_eval inner)
  | FImplication antecedent consequent =>
      implication_facts (recursive_eval antecedent) (recursive_eval consequent)
  | FSeparation children => separation_facts (recursive_evals children)
  end
with recursive_evals (inputs : formulas) : list formula_facts :=
  match inputs with
  | FsNil => []
  | FsCons head tail => recursive_eval head :: recursive_evals tail
  end.

Fixpoint formulas_length (inputs : formulas) : nat :=
  match inputs with
  | FsNil => 0
  | FsCons _ tail => S (formulas_length tail)
  end.

Inductive instruction : Type :=
  | IPush (value : formula_facts)
  | IConjunction
  | IDisjunction
  | INegation
  | IImplication
  | ISeparation (arity : nat).

Fixpoint split_prefix {A : Type} (count : nat) (values : list A)
  : option (list A * list A) :=
  match count, values with
  | 0, _ => Some ([], values)
  | S count', value :: rest =>
      match split_prefix count' rest with
      | Some (prefix, suffix) => Some (value :: prefix, suffix)
      | None => None
      end
  | S _, [] => None
  end.

Definition apply_instruction (next : instruction) (stack : list formula_facts)
  : option (list formula_facts) :=
  match next with
  | IPush value => Some (value :: stack)
  | IConjunction =>
      match stack with
      | lhs :: rhs :: tail => Some (conjunction_facts lhs rhs :: tail)
      | _ => None
      end
  | IDisjunction =>
      match stack with
      | lhs :: rhs :: tail => Some (disjunction_facts lhs rhs :: tail)
      | _ => None
      end
  | INegation =>
      match stack with
      | inner :: tail => Some (negation_facts inner :: tail)
      | _ => None
      end
  | IImplication =>
      match stack with
      | antecedent :: consequent :: tail =>
          Some (implication_facts antecedent consequent :: tail)
      | _ => None
      end
  | ISeparation arity =>
      match split_prefix arity stack with
      | Some (children, tail) => Some (separation_facts children :: tail)
      | None => None
      end
  end.

Fixpoint run (program : list instruction) (stack : list formula_facts)
  : option (list formula_facts) :=
  match program with
  | [] => Some stack
  | next :: rest =>
      match apply_instruction next stack with
      | Some stack' => run rest stack'
      | None => None
      end
  end.

(* Children are compiled right-to-left so a head-based proof stack presents operands in source
   order to each Build instruction. This is the list analogue of Rust pushing children in reverse
   onto its LIFO work stack and visiting them left-to-right. *)
Fixpoint compile_formula (input : formula) : list instruction :=
  match input with
  | FVerum => [IPush (mkFormulaFacts (mkStaticFacts false true) (Some true))]
  | FFalsum => [IPush (mkFormulaFacts (mkStaticFacts true false) (Some false))]
  | FTerm positive_match =>
      [IPush (mkFormulaFacts (mkStaticFacts false false)
        (if positive_match then Some true else None))]
  | FConjunction lhs rhs =>
      compile_formula rhs ++ compile_formula lhs ++ [IConjunction]
  | FDisjunction lhs rhs =>
      compile_formula rhs ++ compile_formula lhs ++ [IDisjunction]
  | FNegation inner => compile_formula inner ++ [INegation]
  | FImplication antecedent consequent =>
      compile_formula consequent ++ compile_formula antecedent ++ [IImplication]
  | FSeparation children =>
      compile_formulas children ++ [ISeparation (formulas_length children)]
  end
with compile_formulas (inputs : formulas) : list instruction :=
  match inputs with
  | FsNil => []
  | FsCons head tail => compile_formulas tail ++ compile_formula head
  end.

Lemma split_prefix_exact :
  forall (A : Type) (prefix suffix : list A),
    split_prefix (length prefix) (prefix ++ suffix) = Some (prefix, suffix).
Proof.
  intros A prefix.
  induction prefix as [| value rest IH].
  - intros suffix. reflexivity.
  - intros suffix. simpl. rewrite IH. reflexivity.
Qed.

Lemma recursive_evals_length :
  forall inputs, length (recursive_evals inputs) = formulas_length inputs.
Proof.
  intro inputs.
  induction inputs as [| head tail IHtail].
  - reflexivity.
  - simpl. rewrite IHtail. reflexivity.
Qed.

Scheme formula_ind_mut := Induction for formula Sort Prop
with formulas_ind_mut := Induction for formulas Sort Prop.

Combined Scheme formula_formulas_ind from formula_ind_mut, formulas_ind_mut.

Theorem formula_pda_equivalence :
  (forall input suffix stack,
    run (compile_formula input ++ suffix) stack =
    run suffix (recursive_eval input :: stack)) /\
  (forall inputs suffix stack,
    run (compile_formulas inputs ++ suffix) stack =
    run suffix (recursive_evals inputs ++ stack)).
Proof.
  apply formula_formulas_ind.
  - intros suffix stack. reflexivity.
  - intros suffix stack. reflexivity.
  - intros positive_match suffix stack. destruct positive_match; reflexivity.
  - intros lhs IHlhs rhs IHrhs suffix stack.
    simpl. repeat rewrite <- app_assoc.
    rewrite IHrhs. rewrite IHlhs. reflexivity.
  - intros lhs IHlhs rhs IHrhs suffix stack.
    simpl. repeat rewrite <- app_assoc.
    rewrite IHrhs. rewrite IHlhs. reflexivity.
  - intros inner IHinner suffix stack.
    simpl. rewrite <- app_assoc. rewrite IHinner. reflexivity.
  - intros antecedent IHantecedent consequent IHconsequent suffix stack.
    simpl. repeat rewrite <- app_assoc.
    rewrite IHconsequent. rewrite IHantecedent. reflexivity.
  - intros children IHchildren suffix stack.
    simpl. rewrite <- app_assoc. rewrite IHchildren.
    rewrite <- recursive_evals_length.
    simpl. rewrite split_prefix_exact. reflexivity.
  - intros suffix stack. reflexivity.
  - intros head IHhead tail IHtail suffix stack.
    simpl. rewrite <- app_assoc. rewrite IHtail. rewrite IHhead. reflexivity.
Qed.

Corollary formula_pda_root_result :
  forall input,
    run (compile_formula input) [] = Some [recursive_eval input].
Proof.
  intro input.
  destruct formula_pda_equivalence as [Hformula _].
  specialize (Hformula input [] []).
  rewrite app_nil_r in Hformula.
  exact Hformula.
Qed.

Corollary formula_pda_never_underflows :
  forall input, exists result, run (compile_formula input) [] = Some result.
Proof.
  intro input.
  exists [recursive_eval input].
  apply formula_pda_root_result.
Qed.
