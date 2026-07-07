(*
 * SymbolOnceInjective: the O1 "symbol-once" property of the Stage-1 M1 in-Rho
 * set-automaton serializer (`rholang-codegen/src/rho_net_automaton.rs`,
 * `automaton_receiver_network_par`). Verifies obligation (ii) of the in-Rho
 * matching verification plan (docs 16): the map from a pattern's surface positions
 * to the `sa:` for-receives that inspect them is TOTAL and INJECTIVE — a bijection
 * (paper phi(s,p)=p.L(s), P1 Cor 6.6 = P2 Thm 1).
 *
 * For M1 the serializer emits exactly ONE for-receive per surface position (the
 * root App's head tag on `loc:{site}`, then one child for-receive per argument on
 * `{parent}/{op}.{i}`), so "symbol-once" is: #for-receives = #positions, and
 * distinct positions map to distinct channels.
 *
 * Abstraction boundary (plan 16, section 0): this models the serializer's
 * position->channel MAP structurally (the emitted `for` skeleton), NOT the
 * operational Rho `Par`/RSpace reduction. The runtime tests
 * (`rho_net_equivalence.rs` `m1_matches_*`) are the executable witness of the
 * emitted `Par`'s faithfulness; the channel STRING injectivity is obligation
 * (viii)'s `tc(K)` naming, a later phase.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions (this file
 * introduces no Section variables; the reused `Pat` comes from
 * PositionalSetAutomatonSound, whose statements are assumption-free).
 *)

From Stdlib Require Import Bool PeanoNat List.
Import ListNotations.
From AdvancedAutomata Require Import PositionalSetAutomatonSound.

(* ---- M1 scope predicate (mirrors the AutomatonUnsupported guards) ---- *)
(* An App root over nullary Var leaves is the only shape M1 serializes:
   VariableRootPattern => must be PApp; NonNullaryVarSubtree => every arg a leaf.
   (Linearity/NonLinearVariable is a sigma-extraction guard that does not affect
   the boolean accept relation, so it is intentionally omitted — see (i).) Reused
   by InRhoMatchPositional (i) and InRhoReuseDeterminism (x). *)
Definition is_leaf (a : Pat) : bool := match a with PVar => true | _ => false end.
Definition all_leaves (args : list Pat) : bool := forallb is_leaf args.
Definition m1_pattern (p : Pat) : bool :=
  match p with PApp _ args => all_leaves args | _ => false end.

(* ---- surface positions and the channel-naming map phi ---- *)
(* A surface position is a Dewey address; the M1 skeleton has the root [] plus one
   [i] per argument (mirroring spread_root_location / spread_child_location). *)
Definition Position := list nat.
Definition positions (p : Pat) : list Position :=
  match p with
  | PApp _ args => [] :: map (fun i => [i]) (seq 0 (length args))
  | _ => []
  end.

(* The channel-naming map phi (mirrors the location channels the serializer
   receives on) and its left inverse, modeled structurally (an injective
   constructor), not the concrete string. *)
Inductive Channel := RootChan (site : nat) | ChildChan (site op idx : nat).
Definition chan (site op : nat) (pos : Position) : Channel :=
  match pos with [] => RootChan site | i :: _ => ChildChan site op i end.
Definition pos_of_chan (c : Channel) : Position :=
  match c with RootChan _ => [] | ChildChan _ _ i => [i] end.

(* A self-contained "injective map preserves NoDup" (avoids stdlib name drift). *)
Lemma nodup_map_inj {A B} (f : A -> B) (l : list A) :
  (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros Hinj Hnd. induction Hnd as [| x l Hx Hnd IH]; simpl; constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Heq Hiny]].
    apply Hinj in Heq. subst y. contradiction.
  - exact IH.
Qed.

(* ---- TOTAL: one for-receive per position (count = 1 + arity) ---- *)
Theorem positions_count : forall op args,
  length (positions (PApp op args)) = S (length args).
Proof.
  intros op args. simpl. rewrite length_map, length_seq. reflexivity.
Qed.

(* ---- phi has a left inverse on the pattern's positions (=> injective there) ---- *)
Theorem chan_left_inverse : forall site op pos p,
  m1_pattern p = true -> In pos (positions p) ->
  pos_of_chan (chan site op pos) = pos.
Proof.
  intros site op pos p Hp Hin.
  destruct p as [| pop pargs | pop pargs]; try discriminate Hp.
  simpl in Hin. destruct Hin as [Heq | Hin].
  - subst pos. reflexivity.
  - apply in_map_iff in Hin. destruct Hin as [i [Heq _]]. subst pos. reflexivity.
Qed.

(* ---- the positions are duplicate-free (each surface symbol addressed once) ---- *)
Theorem positions_nodup : forall p, m1_pattern p = true -> NoDup (positions p).
Proof.
  intros p Hp. destruct p as [| op args | op args]; try discriminate Hp.
  simpl. constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [i [Heq _]]. discriminate Heq.
  - apply nodup_map_inj.
    + intros x y Heq. injection Heq. auto.
    + apply seq_NoDup.
Qed.

(* ---- INJECTIVE: distinct positions map to distinct channels ---- *)
Theorem chan_injective_on_positions : forall op args site,
  NoDup (map (chan site op) (positions (PApp op args))).
Proof.
  intros op args site. simpl. constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [pos [Heq Hin]].
    apply in_map_iff in Hin. destruct Hin as [i [Hi _]]. subst pos.
    cbn in Heq. discriminate Heq.
  - rewrite map_map. apply nodup_map_inj.
    + intros x y Heq. cbn in Heq. injection Heq. auto.
    + apply seq_NoDup.
Qed.

Print Assumptions positions_count.
Print Assumptions chan_left_inverse.
Print Assumptions positions_nodup.
Print Assumptions chan_injective_on_positions.
