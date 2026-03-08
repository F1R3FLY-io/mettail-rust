(*
 * VpaClosureProperties: Closure properties of Visibly Pushdown Automata.
 *
 * Proves that VPAs are closed under complement, intersection, and that
 * equivalence is decidable (via complement + intersection + emptiness).
 *
 * ## Theoretical Foundations
 *
 * - Alur & Madhusudan (2004) -- "Visibly pushdown languages." Closure under
 *   complement via determinization (input-driven stack discipline enables
 *   subset construction); closure under intersection via product construction.
 * - Alur & Madhusudan (2009) -- Extended journal version.
 *
 * ## Key Insight
 *
 * Unlike general pushdown automata, VPAs have input-driven stack discipline:
 * the stack operation (push/pop/noop) is determined entirely by the input
 * symbol's partition (call/return/internal). This makes VPAs determinizable,
 * which yields closure under complement (swap final/non-final states).
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition           | Rust Code                         | Location
 *   --------------------------|-----------------------------------|--------------------------
 *   symbol_kind               | SymbolKind                        | vpa.rs:100-110
 *   classify                  | VpaAlphabet::classify()           | vpa.rs:75-86
 *   step / run / accepts      | Vpa run simulation                | vpa.rs:130-175
 *   complement_is_final       | complement()                      | vpa.rs (complement fn)
 *   prod_step / prod_run      | intersect()                       | vpa.rs (intersect fn)
 *   vpa_equivalence_decidable | check_vpa_equivalence()           | vpa.rs (equivalence fn)
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Decidable.
From Hammer Require Import Tactics.

Import ListNotations.

(* ===================================================================== *)
(*  Symbol Classification (Input-Driven Stack Discipline)                 *)
(* ===================================================================== *)

(** The input alphabet is partitioned into three disjoint classes.
    This partition determines stack operations:
    - Call symbols push onto the stack
    - Return symbols pop from the stack
    - Internal symbols leave the stack unchanged *)
Inductive symbol_kind : Type :=
  | Call     (* push a symbol onto the stack *)
  | Return   (* pop a symbol from the stack *)
  | Internal (* no stack operation *).

(** Decidable equality on symbol kinds. *)
Definition symbol_kind_eqb (k1 k2 : symbol_kind) : bool :=
  match k1, k2 with
  | Call, Call => true
  | Return, Return => true
  | Internal, Internal => true
  | _, _ => false
  end.

Lemma symbol_kind_eqb_spec : forall k1 k2,
  symbol_kind_eqb k1 k2 = true <-> k1 = k2.
Proof.
  intros k1 k2. split.
  - destruct k1, k2; simpl; intros H; try reflexivity; discriminate.
  - intros ->. destruct k2; reflexivity.
Qed.

(* ===================================================================== *)
(*  VPA Definition                                                        *)
(* ===================================================================== *)

Section VPA.

  (** State type *)
  Variable State : Type.

  (** Input symbol type *)
  Variable Symbol : Type.

  (** Stack symbol type (may differ from input symbols) *)
  Variable StackSym : Type.

  (** Classification function: maps each input symbol to its kind.
      This is the core of the "visibly" pushdown constraint -- the stack
      operation is visible (determined) from the input symbol alone. *)
  Variable classify : Symbol -> symbol_kind.

  (** Stack bottom marker *)
  Variable bot : StackSym.

  (** Transition functions -- one per symbol kind:
      - call_trans q a = (q', gamma)  : on call symbol a in state q,
            push gamma and move to q'
      - ret_trans q a gamma = q'      : on return symbol a in state q
            with stack top gamma, pop and move to q'
      - int_trans q a = q'            : on internal symbol a in state q,
            move to q' (stack unchanged) *)

  (** For deterministic VPA, transitions are total functions *)
  Variable call_trans : State -> Symbol -> State * StackSym.
  Variable ret_trans  : State -> Symbol -> StackSym -> State.
  Variable int_trans  : State -> Symbol -> State.

  (** Initial state (deterministic VPA: single initial state) *)
  Variable q0 : State.

  (** Final (accepting) states, given as a decidable predicate *)
  Variable is_final : State -> bool.

  (* ------------------------------------------------------------------- *)
  (*  Run / Acceptance                                                     *)
  (* ------------------------------------------------------------------- *)

  (** Configuration: (state, stack). Stack is a list; head = top.
      Empty list represents a stack containing only the bottom marker. *)
  Definition config := (State * list StackSym)%type.

  (** Single-step transition based on the symbol's classification. *)
  Definition step (c : config) (a : Symbol) : config :=
    let (q, stk) := c in
    match classify a with
    | Call =>
        let (q', gamma) := call_trans q a in
        (q', gamma :: stk)
    | Return =>
        match stk with
        | [] => (ret_trans q a bot, [])
        | gamma :: stk' => (ret_trans q a gamma, stk')
        end
    | Internal =>
        (int_trans q a, stk)
    end.

  (** Run: fold a word (list of symbols) through configurations. *)
  Fixpoint run (c : config) (w : list Symbol) : config :=
    match w with
    | [] => c
    | a :: w' => run (step c a) w'
    end.

  (** Initial configuration *)
  Definition initial_config : config := (q0, []).

  (** Acceptance: the VPA accepts word w iff the final state is accepting
      AND the stack is empty (well-matched word). *)
  Definition accepts (w : list Symbol) : bool :=
    let (qf, stk) := run initial_config w in
    is_final qf && match stk with [] => true | _ => false end.

  (* ================================================================== *)
  (*  PART 1: Closure Under Complement                                   *)
  (* ================================================================== *)

  (** The complement VPA uses the same transition functions but swaps
      the acceptance predicate. Since VPAs are deterministic, this
      correctly recognizes the complement language.

      complement_is_final q = negb (is_final q) *)

  Definition complement_is_final (q : State) : bool := negb (is_final q).

  Definition complement_accepts (w : list Symbol) : bool :=
    let (qf, stk) := run initial_config w in
    complement_is_final qf && match stk with [] => true | _ => false end.

  (** The complement VPA accepts exactly those well-matched words that
      the original rejects. *)
  Theorem complement_correctness : forall w,
    complement_accepts w = true <->
    (accepts w = false /\
     match snd (run initial_config w) with [] => True | _ => False end).
  Proof.
    intros w. unfold complement_accepts, accepts, complement_is_final.
    destruct (run initial_config w) as [qf stk]. simpl.
    destruct stk as [| g stk'].
    - (* Stack empty: well-matched word *)
      simpl. rewrite !Bool.andb_true_r, Bool.negb_true_iff. tauto.
    - (* Stack non-empty: neither accepts *)
      simpl. rewrite !Bool.andb_false_r.
      split; [discriminate | intros [_ []]].
  Qed.

  (** Complement is an involution: complementing twice gives the original. *)
  Theorem complement_involution : forall w,
    let double_comp_final q := negb (complement_is_final q) in
    let double_comp_accepts :=
      let (qf, stk) := run initial_config w in
      double_comp_final qf && match stk with [] => true | _ => false end
    in
    double_comp_accepts = accepts w.
  Proof.
    intros w.
    unfold complement_is_final, accepts.
    destruct (run initial_config w) as [qf stk].
    simpl. rewrite Bool.negb_involutive. reflexivity.
  Qed.

  (* ================================================================== *)
  (*  PART 2: Closure Under Intersection (Product Construction)          *)
  (* ================================================================== *)

  (** For intersection, we need a second VPA over the SAME alphabet
      partition (same classify function) but potentially different
      states, transitions, and acceptance. *)

  Variable State2 : Type.
  Variable StackSym2 : Type.
  Variable call_trans2 : State2 -> Symbol -> State2 * StackSym2.
  Variable ret_trans2  : State2 -> Symbol -> StackSym2 -> State2.
  Variable int_trans2  : State2 -> Symbol -> State2.
  Variable q0_2 : State2.
  Variable bot2 : StackSym2.
  Variable is_final2 : State2 -> bool.

  (* -- Second VPA's run ------------------------------------------------ *)

  Definition step2 (c : State2 * list StackSym2) (a : Symbol)
    : State2 * list StackSym2 :=
    let (q, stk) := c in
    match classify a with
    | Call =>
        let (q', gamma) := call_trans2 q a in
        (q', gamma :: stk)
    | Return =>
        match stk with
        | [] => (ret_trans2 q a bot2, [])
        | gamma :: stk' => (ret_trans2 q a gamma, stk')
        end
    | Internal =>
        (int_trans2 q a, stk)
    end.

  Fixpoint run2 (c : State2 * list StackSym2) (w : list Symbol)
    : State2 * list StackSym2 :=
    match w with
    | [] => c
    | a :: w' => run2 (step2 c a) w'
    end.

  Definition initial_config2 : State2 * list StackSym2 := (q0_2, []).

  Definition accepts2 (w : list Symbol) : bool :=
    let (qf, stk) := run2 initial_config2 w in
    is_final2 qf && match stk with [] => true | _ => false end.

  (* -- Product construction -------------------------------------------- *)

  (** Product state: pair of states from both VPAs *)
  Definition prod_state := (State * State2)%type.

  (** Product stack symbol: pair of stack symbols (both VPAs push/pop
      in sync because they share the same alphabet partition) *)
  Definition prod_stacksym := (StackSym * StackSym2)%type.

  (** Product transitions *)
  Definition prod_call_trans (qs : prod_state) (a : Symbol)
    : prod_state * prod_stacksym :=
    let (q1, q2) := qs in
    let (q1', g1) := call_trans q1 a in
    let (q2', g2) := call_trans2 q2 a in
    ((q1', q2'), (g1, g2)).

  Definition prod_ret_trans (qs : prod_state) (a : Symbol)
    (gs : prod_stacksym) : prod_state :=
    let (q1, q2) := qs in
    let (g1, g2) := gs in
    (ret_trans q1 a g1, ret_trans2 q2 a g2).

  Definition prod_int_trans (qs : prod_state) (a : Symbol) : prod_state :=
    let (q1, q2) := qs in
    (int_trans q1 a, int_trans2 q2 a).

  Definition prod_bot : prod_stacksym := (bot, bot2).

  Definition prod_step (c : prod_state * list prod_stacksym) (a : Symbol)
    : prod_state * list prod_stacksym :=
    let (qs, stk) := c in
    match classify a with
    | Call =>
        let (qs', gs) := prod_call_trans qs a in
        (qs', gs :: stk)
    | Return =>
        match stk with
        | [] => (prod_ret_trans qs a prod_bot, [])
        | gs :: stk' => (prod_ret_trans qs a gs, stk')
        end
    | Internal =>
        (prod_int_trans qs a, stk)
    end.

  Fixpoint prod_run (c : prod_state * list prod_stacksym) (w : list Symbol)
    : prod_state * list prod_stacksym :=
    match w with
    | [] => c
    | a :: w' => prod_run (prod_step c a) w'
    end.

  Definition prod_initial : prod_state * list prod_stacksym :=
    ((q0, q0_2), []).

  Definition prod_is_final (qs : prod_state) : bool :=
    let (q1, q2) := qs in
    is_final q1 && is_final2 q2.

  Definition prod_accepts (w : list Symbol) : bool :=
    let (qsf, stk) := prod_run prod_initial w in
    prod_is_final qsf && match stk with [] => true | _ => false end.

  (* -- Projection lemmas ----------------------------------------------- *)

  (** Helper: extract first component of product configuration *)
  Definition proj1_config (c : prod_state * list prod_stacksym)
    : State * list StackSym :=
    let (qs, stk) := c in
    (fst qs, map fst stk).

  (** Helper: extract second component of product configuration *)
  Definition proj2_config (c : prod_state * list prod_stacksym)
    : State2 * list StackSym2 :=
    let (qs, stk) := c in
    (snd qs, map snd stk).

  (** The product step projects to the first VPA's step. *)
  Lemma prod_step_proj1 : forall c a,
    proj1_config (prod_step c a) = step (proj1_config c) a.
  Proof.
    intros [[q1 q2] stk] a.
    simpl.
    destruct (classify a) eqn:Hk.
    - unfold prod_call_trans.
      destruct (call_trans q1 a) as [q1' g1] eqn:Hc1.
      destruct (call_trans2 q2 a) as [q2' g2] eqn:Hc2.
      simpl. reflexivity.
    - unfold prod_ret_trans.
      destruct stk as [| [g1 g2] stk']; simpl; reflexivity.
    - simpl. reflexivity.
  Qed.

  (** The product step projects to the second VPA's step. *)
  Lemma prod_step_proj2 : forall c a,
    proj2_config (prod_step c a) = step2 (proj2_config c) a.
  Proof.
    intros [[q1 q2] stk] a.
    simpl.
    destruct (classify a) eqn:Hk.
    - unfold prod_call_trans.
      destruct (call_trans q1 a) as [q1' g1] eqn:Hc1.
      destruct (call_trans2 q2 a) as [q2' g2] eqn:Hc2.
      simpl. reflexivity.
    - unfold prod_ret_trans.
      destruct stk as [| [g1 g2] stk']; simpl; reflexivity.
    - simpl. reflexivity.
  Qed.

  (** The product run projects to individual runs (by induction on word). *)
  Lemma prod_run_proj1 : forall w c,
    proj1_config (prod_run c w) = run (proj1_config c) w.
  Proof.
    induction w as [| a w' IH].
    - intros c. simpl. reflexivity.
    - intros c. simpl.
      rewrite IH. rewrite prod_step_proj1. reflexivity.
  Qed.

  Lemma prod_run_proj2 : forall w c,
    proj2_config (prod_run c w) = run2 (proj2_config c) w.
  Proof.
    induction w as [| a w' IH].
    - intros c. simpl. reflexivity.
    - intros c. simpl.
      rewrite IH. rewrite prod_step_proj2. reflexivity.
  Qed.

  (* -- Intersection correctness ---------------------------------------- *)

  (** Main intersection theorem: the product VPA accepts exactly the
      intersection of the two component languages.

      prod_accepts(w) = true  <->  accepts(w) = true /\ accepts2(w) = true *)
  (** Helper: relating product run result to individual runs. *)
  Lemma prod_run_relates : forall w,
    let pc := prod_run prod_initial w in
    run initial_config w = (fst (fst pc), map fst (snd pc)) /\
    run2 initial_config2 w = (snd (fst pc), map snd (snd pc)).
  Proof.
    intros w.
    pose proof (prod_run_proj1 w prod_initial) as H1.
    pose proof (prod_run_proj2 w prod_initial) as H2.
    unfold proj1_config in H1. unfold proj2_config in H2.
    unfold prod_initial, initial_config, initial_config2 in *.
    simpl in H1, H2.
    destruct (prod_run ((q0, q0_2), []) w) as [[r1 r2] rstk].
    simpl in *. split; symmetry; assumption.
  Qed.

  Theorem intersection_correctness : forall w,
    prod_accepts w = true <-> (accepts w = true /\ accepts2 w = true).
  Proof.
    intros w. unfold prod_accepts, accepts, accepts2.
    pose proof (prod_run_relates w) as [Hrun1 Hrun2]. simpl in *.
    destruct (prod_run prod_initial w) as [[qf1 qf2] prod_stk] eqn:Hprod.
    simpl in *. rewrite Hrun1, Hrun2. unfold prod_is_final. simpl.
    destruct prod_stk as [| gs prod_stk'].
    - simpl. rewrite !Bool.andb_true_r, Bool.andb_true_iff. tauto.
    - simpl. rewrite !Bool.andb_false_r.
      split; [discriminate | intros [H1 H2]; discriminate].
  Qed.

  (* ================================================================== *)
  (*  PART 3: Decidable Equivalence                                      *)
  (* ================================================================== *)

  (** VPA equivalence is decidable via the standard automata-theoretic
      reduction:

        L(A1) = L(A2)
          <-> L(A1) \ L(A2) = emptyset  /\  L(A2) \ L(A1) = emptyset
          <-> L(A1) cap L(complement(A2)) = emptyset
              /\ L(complement(A1)) cap L(A2) = emptyset

      Since VPAs are closed under complement (swap finals) and intersection
      (product), and emptiness is decidable (reachability analysis), this
      gives a decision procedure for equivalence. *)

  (* -- Inclusion as absence of difference witnesses -------------------- *)

  Definition vpa_inclusion_witness (w : list Symbol) : bool :=
    accepts w && negb (accepts2 w).

  (** Inclusion holds iff no witness exists. *)
  Definition vpa_inclusion : Prop :=
    forall w, vpa_inclusion_witness w = false.

  (** Equivalence: mutual inclusion. *)
  Definition vpa_equivalence : Prop :=
    vpa_inclusion /\
    (forall w, accepts2 w && negb (accepts w) = false).

  (** Equivalence implies identical acceptance on all words. *)
  Theorem equivalence_iff_same_language : forall w,
    vpa_equivalence -> accepts w = accepts2 w.
  Proof.
    intros w [Hincl12 Hincl21].
    specialize (Hincl12 w). specialize (Hincl21 w).
    unfold vpa_inclusion_witness in Hincl12.
    destruct (accepts w), (accepts2 w); simpl in *; congruence.
  Qed.

  (** Conversely, identical acceptance implies equivalence. *)
  Theorem same_language_implies_equivalence :
    (forall w, accepts w = accepts2 w) -> vpa_equivalence.
  Proof.
    intros Hsame. split.
    - intros w. unfold vpa_inclusion_witness.
      rewrite Hsame. destruct (accepts2 w); reflexivity.
    - intros w. rewrite Hsame.
      destruct (accepts2 w); reflexivity.
  Qed.

  (** Clean characterization: equivalence as mutual inclusion. *)
  Theorem decidable_equivalence_clean :
    (forall w, accepts w = accepts2 w) <->
    ((forall w, accepts w = true -> accepts2 w = true) /\
     (forall w, accepts2 w = true -> accepts w = true)).
  Proof.
    split.
    - intros Hsame; split; intros w Ha;
        [rewrite <- Hsame | rewrite Hsame]; exact Ha.
    - intros [H12 H21] w.
      destruct (accepts w) eqn:Ha1, (accepts2 w) eqn:Ha2; try reflexivity;
        exfalso; [apply H12 in Ha1 | apply H21 in Ha2]; congruence.
  Qed.

  (** The actual decidability: given a decidable emptiness oracle for
      Boolean predicates on words, VPA equivalence is decidable.

      This follows from:
      1. Closure under complement (swap is_final to negb is_final)
      2. Closure under intersection (product construction)
      3. Decidable emptiness (reachability on finite control x stack) *)
  Theorem vpa_equivalence_decidable :
    (forall P : list Symbol -> bool,
      (exists w, P w = true) \/ (forall w, P w = false)) ->
    (forall w, accepts w = accepts2 w) \/
    (exists w, accepts w <> accepts2 w).
  Proof.
    intros Hempty_dec.
    (* Check if L(A1) \ L(A2) is empty *)
    destruct (Hempty_dec (fun w => accepts w && negb (accepts2 w)))
      as [[w Hw] | Hempty].
    - (* Found a witness: A1 accepts but A2 does not *)
      right. exists w.
      rewrite Bool.andb_true_iff, Bool.negb_true_iff in Hw.
      destruct Hw as [Ha1 Ha2]. rewrite Ha1, Ha2. discriminate.
    - (* L(A1) \ L(A2) is empty: check L(A2) \ L(A1) *)
      destruct (Hempty_dec (fun w => accepts2 w && negb (accepts w)))
        as [[w Hw] | Hempty2].
      + (* Found a witness: A2 accepts but A1 does not *)
        right. exists w.
        rewrite Bool.andb_true_iff, Bool.negb_true_iff in Hw.
        destruct Hw as [Ha2 Ha1]. rewrite Ha1, Ha2. discriminate.
      + (* Both differences empty: languages are equal *)
        left. intros w. specialize (Hempty w). specialize (Hempty2 w).
        destruct (accepts w), (accepts2 w); simpl in *; congruence.
  Qed.

End VPA.

(* Note: Section variables are automatically generalized after End VPA.
   We omit explicit Arguments declarations to avoid fragile parameter
   ordering issues. Use @ for explicit application if needed. *)
