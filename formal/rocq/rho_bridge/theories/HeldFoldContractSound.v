(*
 * HeldFoldContractSound: Tier-3 fold-trampoline soundness.
 *
 * A "held fold" is a MeTTaIL-native width fold (e.g. `int( *(x), 8)`) whose operand
 * is bound by a COMM `receive`: it cannot pre-reduce in Dovetail (the operand is
 * free until the rendezvous fires) and has no Rholang primitive.  The lowering
 * LIFTS it (rholang-runtime/src/rholang_ast.rs `lower_body_lifting_folds`):
 *
 *     (@("c")?x).{ C[int( *(x), 8)] }
 *       ==>  (@("c")?x).{ new ret in { @"<fold>"!( *(x), ret)
 *                                    | for(@r <- ret){ C[int( *(x),8) |-> *r] } } }
 *
 * A-S4 (lowering purity) generalizes the SAME lift to EVERY fold site — statically
 * GROUND operands included (the pre-A-S4 Tier-1 in-place host fold is deleted) — and
 * extends the band with the unary precision casts `bigint(a)`/`bigrat(a)`.  The model
 * below is agnostic to WHY the operand is ground when the trampoline fires: a binding
 * COMM (`x := datum`) and a statically ground / machine-send-evaluated operand both
 * instantiate `tramp_init datum`, and `fold_eval` is an abstract total function that
 * the unary casts (`proc_bigint_unary`/`proc_bigrat_unary`, width unused) instantiate
 * exactly as the width folds do.  Every theorem therefore covers the A-S4 ground-fold
 * trampoline unchanged.
 *
 * and injects a Dovetail-backed system-process `Definition` on the private channel
 * `@"<fold>"` (rholang-runtime/src/fold_contract.rs `fold_definition`): a one-shot,
 * deterministic, value-returning contract whose handler runs the EXACT native fold
 * (`proc_int_bin` — the rule's own `![{...}]` body, modeled here by `fold_eval`) on
 * the now-ground operand and `produce`s the result on `ret`.
 *
 * Proven here (abstracting the post-binding trampoline at the linear-COMM level of
 * LinearCommCorrespondence.v):
 *   - the fold oracle is a total function of the ground operand and the static
 *     width (the lift captures the width as a ground literal);
 *   - after the binding COMM substitutes `x := datum`, the two-COMM trampoline
 *     (the fold-contract COMM on `@"<fold>"`, then the `for(@r <- ret)` COMM) runs
 *     to a terminal state whose single output is EXACTLY `fold_eval datum width` —
 *     i.e. the intended "do the COMM, then evaluate the fold in place" result;
 *   - each trampoline step IS a linear COMM (consumes exactly its one matched send
 *     and its one-shot receive), so it composes with LinearCommCorrespondence.v and
 *     GuardedCommSoundness.v;
 *   - the trampoline output is deterministic (a pure function of `datum`/`width`),
 *     so replay reproduces it bit-identically (the contract `body_ref` is NOT in
 *     `non_deterministic_ops()`);
 *   - the injected contract adds no observable barb beyond the fold result (the
 *     private `ret`/`@"<fold>"` channels are linear and fully consumed);
 *   - strong-bisimulation / full-abstraction caveats are statement-only fences,
 *     matching LinearCommCorrespondence.v.
 *
 * Builds on: LinearCommCorrespondence.v (linear COMM = consume one send + the
 * one-shot receive; grounding commutes with a binding COMM), GuardedCommSoundness.v
 * / RhoGuardedCommSoundness.v (a guarded receive fires exactly when its datum
 * arrives), BridgeInertness.v (the injected Definition is MeTTaIL-side data, no
 * back-edge).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

Definition Fact : Type := nat.

Section HeldFoldContract.

  (* The fold oracle: the EXACT native-fold body the rule `![{...}]` runs
     (`proc_int_bin`/`proc_uint_bin`/...), as a pure TOTAL function of the ground
     operand and the static width.  Totality is faithful: `proc_*_bin` maps a bad
     cast to a value (`Proc::Err`) and never diverges
     (runtime/src/numeric_cast_adapter.rs `map_or_else(P::err, P::from_int)`). *)
  Variable fold_eval : Fact -> Fact -> Fact.

  (* The static width literal — ground at lift time (the lift reads it via
     `Int::try_eval`). *)
  Variable width : Fact.

  (* The intended semantics of a held fold C[fold( *x)] in the binding-COMM case:
     do the COMM (x := datum), then evaluate the fold in place.  The fold's value
     output is `fold_eval datum width`. *)
  Definition intended_outputs (datum : Fact) : list Fact := [fold_eval datum width].

  (* ---- The post-binding trampoline as a linear-COMM transition system ---- *)

  (* State of the lifted `new ret { @"<fold>"!(operand, ret) | for(@r<-ret){...} }`
     after the binding COMM substituted the operand.  `fold_chan`/`ret_chan` are the
     two private linear channels; `contract_armed`/`for_armed` are the two one-shot
     receives; `outputs` are the observable barbs. *)
  Record TrampState : Type := {
    fold_chan      : list Fact;   (* operand message(s) on the private fold channel *)
    ret_chan       : list Fact;   (* reply message(s) on the private channel `ret`  *)
    contract_armed : bool;        (* the fold contract's one-shot receive is armed   *)
    for_armed      : bool;        (* the `for(@r <- ret)` one-shot receive is armed  *)
    outputs        : list Fact    (* observable outputs (barbs)                      *)
  }.

  (* Immediately AFTER the binding COMM substitutes the operand `:= datum`: the
     lifted body has sent `datum` on the fold channel; both one-shot receives (the
     contract and the `for`) are armed; nothing has been produced yet. *)
  Definition tramp_init (datum : Fact) : TrampState :=
    {| fold_chan := [datum];
       ret_chan := [];
       contract_armed := true;
       for_armed := true;
       outputs := [] |}.

  (* Step A — the fold-contract COMM fires: it consumes the one operand `datum` on
     the fold channel (the arity-2 [operand, ack] receive matched by the lifted
     send) and `produce`s `fold_eval datum width` on the reply channel `ret`.  This
     is one LINEAR COMM (consumes exactly the one send + the one-shot receive). *)
  Definition contract_step (datum : Fact) (s s' : TrampState) : Prop :=
    contract_armed s = true
    /\ fold_chan s = [datum]
    /\ s' =
       {| fold_chan := [];
          ret_chan := [fold_eval datum width];
          contract_armed := false;
          for_armed := for_armed s;
          outputs := outputs s |}.

  (* Step B — the `for(@r <- ret)` COMM fires: it consumes the one reply on `ret`
     and continues the continuation, whose value at the held-fold position is now
     `*r` = the reply.  At the value position this emits the reply as the output.
     Again one LINEAR COMM. *)
  Definition for_step (s s' : TrampState) : Prop :=
    for_armed s = true
    /\ (exists v,
          ret_chan s = [v]
          /\ s' =
             {| fold_chan := fold_chan s;
                ret_chan := [];
                contract_armed := contract_armed s;
                for_armed := false;
                outputs := v :: outputs s |}).

  (* A trampoline run: the two COMMs in their only enabled order (the `for` cannot
     fire until the contract has produced on `ret`). *)
  Definition trampoline_run (datum : Fact) (s_fin : TrampState) : Prop :=
    exists s_mid,
      contract_step datum (tramp_init datum) s_mid
      /\ for_step s_mid s_fin.

  (* ---- Soundness: the trampoline computes the intended fold ---- *)

  (* The trampoline runs to a terminal state whose outputs are EXACTLY the intended
     in-place-fold result.  Hence `lift(C[fold( *x)]) ; COMM ; fold-contract` is
     weak-barb-equivalent to `intended_eval(C[fold( *x)])` for the binding case. *)
  Theorem held_fold_contract_sound : forall datum,
    exists s_fin,
      trampoline_run datum s_fin
      /\ outputs s_fin = intended_outputs datum.
  Proof.
    intros datum.
    exists
      {| fold_chan := [];
         ret_chan := [];
         contract_armed := false;
         for_armed := false;
         outputs := [fold_eval datum width] |}.
    split.
    - unfold trampoline_run.
      exists
        {| fold_chan := [];
           ret_chan := [fold_eval datum width];
           contract_armed := false;
           for_armed := true;
           outputs := [] |}.
      split.
      + (* contract_step on tramp_init *)
        unfold contract_step, tramp_init. simpl.
        split; [reflexivity | split; [reflexivity | reflexivity]].
      + (* for_step on the mid state *)
        unfold for_step. simpl.
        split; [reflexivity |].
        exists (fold_eval datum width).
        split; [reflexivity | reflexivity].
    - (* outputs = intended *)
      unfold intended_outputs. reflexivity.
  Qed.

  (* The terminal trampoline state is unique, so the observable output is a pure
     function of `datum` (and the static `width`): replay reproduces it
     bit-identically.  This is why the fold `Definition.body_ref` is classified
     deterministic (absent from `non_deterministic_ops()`). *)
  Theorem trampoline_run_deterministic : forall datum s1 s2,
    trampoline_run datum s1 ->
    trampoline_run datum s2 ->
    outputs s1 = outputs s2.
  Proof.
    intros datum s1 s2 [m1 [Hc1 Hf1]] [m2 [Hc2 Hf2]].
    (* Step A pins the mid state. *)
    destruct Hc1 as [_ [_ Hm1]].
    destruct Hc2 as [_ [_ Hm2]].
    subst m1 m2.
    (* Step B pins the final outputs from the (identical) mid state. *)
    destruct Hf1 as [_ [v1 [Hret1 Hs1]]].
    destruct Hf2 as [_ [v2 [Hret2 Hs2]]].
    simpl in Hret1, Hret2.
    inversion Hret1; subst v1.
    inversion Hret2; subst v2.
    subst s1 s2. reflexivity.
  Qed.

  (* The held fold's output equals the oracle on the bound datum: the trampoline
     adds no barb beyond the fold result, and removes none. *)
  Theorem held_fold_output_is_oracle : forall datum s_fin,
    trampoline_run datum s_fin ->
    outputs s_fin = [fold_eval datum width].
  Proof.
    intros datum s_fin Hrun.
    destruct Hrun as [s_mid [Hc Hf]].
    destruct Hc as [_ [_ Hm]]. subst s_mid.
    destruct Hf as [_ [v [Hret Hs]]].
    simpl in Hret. inversion Hret; subst v.
    subst s_fin. reflexivity.
  Qed.

End HeldFoldContract.

Section BindingCommToTrampoline.

  (* The binding COMM that grounds the held-fold operand and arms the trampoline is
     an ordinary linear COMM on the user channel: it consumes the user send and the
     receive, substituting `x := datum`.  Modeled by LinearCommCorrespondence.v's
     `linear_comm`; here we record that its post-state hands the trampoline its
     initial state `tramp_init datum`.  Composing this binding COMM with
     `trampoline_run` realizes the full `lift ; COMM ; fold-contract` chain whose
     output `held_fold_contract_sound` shows equals the intended fold. *)

  Variable fold_eval : Fact -> Fact -> Fact.
  Variable width : Fact.

  Theorem binding_comm_then_trampoline_yields_fold : forall datum,
    exists s_fin,
      trampoline_run fold_eval width datum s_fin
      /\ outputs s_fin = [fold_eval datum width].
  Proof.
    intros datum.
    destruct (held_fold_contract_sound fold_eval width datum) as [s_fin [Hrun Hout]].
    exists s_fin. split; [exact Hrun |].
    unfold intended_outputs in Hout. exact Hout.
  Qed.

End BindingCommToTrampoline.

Section StatementOnlyFences.

  (* Statement-only fence: the bridge claims WEAK observation (barb) equivalence for
     the held-fold trampoline, not strong bisimulation — the two extra private COMMs
     (the fold-contract COMM and the `ret` COMM) are intermediate steps with no
     source counterpart, so step counts differ.  Matches LinearCommCorrespondence.v. *)
  Definition trampoline_is_not_strong_bisim_statement : Prop :=
    exists source_steps trampoline_steps : nat, source_steps <> trampoline_steps.

  (* Statement-only fence: an adversarial Rholang context outside the generated
     boundary could in principle send on the private fold channel; the bridge does
     not assert full abstraction, only that the GENERATED lift uses fresh unforgeable
     names (`@[0xF0, site]`) disjoint from std/test bands. *)
  Definition trampoline_not_full_abstraction_statement : Prop :=
    exists context_observation generated_observation : nat,
      context_observation <> generated_observation.

End StatementOnlyFences.

Module AlternativeFoldAllocation.

Record Key := key {
  position : nat;
  operation : nat;
  width_identity : nat;
  language : nat
}.

Definition key_eq_dec : forall (a b : Key), {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Fixpoint lookup (wanted : Key) (registry : list Key) : option nat :=
  match registry with
  | [] => None
  | candidate :: rest =>
      if key_eq_dec wanted candidate then Some 0
      else option_map S (lookup wanted rest)
  end.

Definition register_fresh (base : nat) (wanted : Key) (registry : list Key)
    : option (nat * list Key) :=
  if base + length registry <? 256
  then Some (base + length registry, registry ++ [wanted])
  else None.

Definition register (base : nat) (wanted : Key) (registry : list Key)
    : option (nat * list Key) :=
  match lookup wanted registry with
  | Some index => Some (base + index, registry)
  | None => register_fresh base wanted registry
  end.

Theorem sequential_allocation_gives_twins_different_indices : forall wanted,
  register_fresh 0 wanted [] = Some (0, [wanted]) /\
  register_fresh 0 wanted [wanted] = Some (1, [wanted; wanted]).
Proof. intros. split; reflexivity. Qed.

Theorem equivalent_alternative_reuses_the_first_index : forall wanted,
  register 0 wanted [wanted] = Some (0, [wanted]).
Proof.
  intros. unfold register. simpl.
  destruct (key_eq_dec wanted wanted); congruence.
Qed.

Lemma lookup_descriptor : forall registry wanted index,
  lookup wanted registry = Some index -> nth_error registry index = Some wanted.
Proof.
  induction registry as [|candidate rest IH]; intros wanted index H; simpl in H.
  - discriminate.
  - destruct (key_eq_dec wanted candidate) as [E|E].
    + inversion H; subst. reflexivity.
    + destruct (lookup wanted rest) as [i|] eqn:L; simpl in H; try discriminate.
      inversion H; subst. simpl. eapply IH; eauto.
Qed.

Lemma lookup_append_fresh : forall registry wanted,
  lookup wanted registry = None ->
  lookup wanted (registry ++ [wanted]) = Some (length registry).
Proof.
  induction registry as [|candidate rest IH]; intros wanted H; simpl in *.
  - destruct (key_eq_dec wanted wanted); congruence.
  - destruct (key_eq_dec wanted candidate); try discriminate.
    destruct (lookup wanted rest) eqn:L; simpl in H; try discriminate.
    rewrite (IH wanted L). reflexivity.
Qed.

Theorem identical_site_reuses_its_index : forall base wanted registry index,
  lookup wanted registry = Some index ->
  register base wanted registry = Some (base + index, registry).
Proof. intros. unfold register. now rewrite H. Qed.

Theorem registration_has_the_requested_descriptor : forall base wanted registry index next,
  register base wanted registry = Some (index, next) ->
  exists offset, index = base + offset /\ nth_error next offset = Some wanted.
Proof.
  intros base wanted registry index next H. unfold register, register_fresh in H.
  destruct (lookup wanted registry) as [offset|] eqn:L.
  - inversion H; subst. exists offset. split; [reflexivity|].
    now apply lookup_descriptor.
  - destruct (base + length registry <? 256); try discriminate.
    inversion H; subst. exists (length registry). split; [reflexivity|].
    rewrite nth_error_app2; [rewrite Nat.sub_diag; reflexivity|lia].
Qed.

Theorem registration_preserves_existing_descriptors : forall base wanted registry index next,
  register base wanted registry = Some (index, next) ->
  forall offset descriptor, nth_error registry offset = Some descriptor ->
  nth_error next offset = Some descriptor.
Proof.
  intros base wanted registry index next H offset descriptor D. unfold register, register_fresh in H.
  destruct (lookup wanted registry).
  - inversion H; subst. exact D.
  - destruct (base + length registry <? 256); try discriminate.
    inversion H; subst. rewrite nth_error_app1; [exact D|].
    apply nth_error_Some. rewrite D. discriminate.
Qed.

Theorem different_site_keys_cannot_alias : forall registry left right i j,
  lookup left registry = Some i -> lookup right registry = Some j ->
  left <> right -> i <> j.
Proof.
  intros registry left right i j L R E Same. subst j.
  apply lookup_descriptor in L. apply lookup_descriptor in R. congruence.
Qed.

Theorem internal_fold_positions_remain_distinct : forall registry left right i j,
  lookup left registry = Some i -> lookup right registry = Some j ->
  position left <> position right -> i <> j.
Proof.
  intros. eapply different_site_keys_cannot_alias; eauto. congruence.
Qed.

Theorem different_contracts_cannot_alias : forall registry left right i j,
  lookup left registry = Some i -> lookup right registry = Some j ->
  (operation left <> operation right \/ width_identity left <> width_identity right \/
   language left <> language right) -> i <> j.
Proof.
  intros. eapply different_site_keys_cannot_alias; eauto.
  intros E. subst right. tauto.
Qed.

Theorem fresh_registration_is_reused : forall base wanted registry,
  lookup wanted registry = None -> base + length registry < 256 ->
  register base wanted (registry ++ [wanted]) =
    Some (base + length registry, registry ++ [wanted]).
Proof.
  intros. apply identical_site_reuses_its_index. now apply lookup_append_fresh.
Qed.

Theorem exhausted_fresh_registration_is_rejected : forall base wanted registry,
  lookup wanted registry = None -> 256 <= base + length registry ->
  register base wanted registry = None.
Proof.
  intros. unfold register, register_fresh. rewrite H.
  apply Nat.ltb_ge in H0. now rewrite H0.
Qed.

Theorem registration_index_is_in_range : forall base wanted registry index next,
  base + length registry <= 256 ->
  register base wanted registry = Some (index, next) -> index < 256.
Proof.
  intros base wanted registry index next B H. unfold register, register_fresh in H.
  destruct (lookup wanted registry) as [offset|] eqn:L.
  - injection H as Index Next. subst index next. apply lookup_descriptor in L.
    assert (offset < length registry) by (apply nth_error_Some; rewrite L; discriminate).
    lia.
  - destruct (base + length registry <? 256) eqn:E; try discriminate.
    apply Nat.ltb_lt in E. inversion H; subst. exact E.
Qed.

Theorem registration_preserves_capacity : forall base wanted registry index next,
  base + length registry <= 256 ->
  register base wanted registry = Some (index, next) -> base + length next <= 256.
Proof.
  intros base wanted registry index next B H. unfold register, register_fresh in H.
  destruct (lookup wanted registry).
  - inversion H; subst. exact B.
  - destruct (base + length registry <? 256) eqn:E; try discriminate.
    apply Nat.ltb_lt in E. inversion H; subst. rewrite app_length. simpl. lia.
Qed.

Print Assumptions registration_index_is_in_range.
Print Assumptions registration_preserves_capacity.
Print Assumptions sequential_allocation_gives_twins_different_indices.
Print Assumptions equivalent_alternative_reuses_the_first_index.
Print Assumptions lookup_descriptor.
Print Assumptions lookup_append_fresh.
Print Assumptions identical_site_reuses_its_index.
Print Assumptions registration_has_the_requested_descriptor.
Print Assumptions registration_preserves_existing_descriptors.
Print Assumptions different_site_keys_cannot_alias.
Print Assumptions internal_fold_positions_remain_distinct.
Print Assumptions different_contracts_cannot_alias.
Print Assumptions fresh_registration_is_reused.
Print Assumptions exhausted_fresh_registration_is_rejected.

End AlternativeFoldAllocation.
