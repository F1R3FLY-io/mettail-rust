(*
 * AmbientBinderHandler: the capture-safety model for the Inc 1 moniker
 * binder-congruence NativeHandler (`Proc::binder_congruence_nf`), which floats
 * `new`s outward via moniker `unbind`->reassemble->`Scope::new`.
 *
 * The handler's `unbind` FRESHENS the floated binder (capture-avoiding
 * alpha-renaming), so floating a `new` out of a prefix `C(N, new^x.P)` produces
 * `new^x'.(C(N, P[x:=x']))` with `x'` fresh. The load-bearing property is that
 * this does NOT capture any name free in `N`: the channel/name stays free. This
 * is exactly what the Rust test `prefix_float_does_not_capture_a_shared_name`
 * checks empirically (via `free_vars`).
 *
 * Two obligations, both zero-admission, over a named single-binder process model
 * (a `NVar n` is a name/variable identified by a `nat`; `free_vars` removes the
 * binder, mirroring moniker `free_vars`):
 *
 * 1. CAPTURE-SAFETY (`float_preserves_name_free_vars`). Floating with a binder
 *    FRESH in the name keeps every name-free variable free — no capture.
 *
 * 2. THE CONTRAST (`naive_float_can_capture`). Reusing the ORIGINAL binder
 *    (no freshening — `from_parts_unsafe`, run_ascent's bug) CAN capture a name
 *    that is free in `N`. This is the formal twin of the verified run_ascent
 *    capture-unsoundness, and it is why the handler must `unbind` (freshen).
 *
 * Plus the freshness lemmas the ScopeExtrusion multiset gate relies on (T2).
 *
 * No `Admitted`, no `Axiom`, no `admit`. `Require`s only the Coq Stdlib.
 *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* A named single-binder process term, faithful to the Ambient process fragment
   the handler floats:
   - NVar n: a variable/name, identified by a nat (the moniker FreeVar id).
   - NPrefix nm b: a prefix C(N, P) carrying a name sub-term and a body
     (models PIn/POut/POpen/PAmb uniformly).
   - NNew x b: a single binder `new^x.b` (x is the binder's name id).
   - NPar ts: the parallel bag (PPar). *)
Inductive nterm : Type :=
  | NVar : nat -> nterm
  | NPrefix : nterm -> nterm -> nterm
  | NNew : nat -> nterm -> nterm
  | NPar : list nterm -> nterm.

(* Free variables, mirroring moniker `free_vars`: a binder removes its name. *)
Fixpoint free_vars (t : nterm) : list nat :=
  match t with
  | NVar n => [n]
  | NPrefix nm b => free_vars nm ++ free_vars b
  | NNew x b => remove Nat.eq_dec x (free_vars b)
  | NPar ts => flat_map free_vars ts
  end.

Definition fresh (x : nat) (t : nterm) : Prop := ~ In x (free_vars t).

(* ----------------------------------------------------------------------- *)
(* T1 — capture-safety of the float with a FRESH binder.                    *)
(*                                                                          *)
(* The handler floats `C(N, new^x.P)` to `new^x'.(C(N, P[x:=x']))` with x'  *)
(* fresh. `b'` abstracts the opened+renamed body `P[x:=x']`; what matters   *)
(* for capture-safety is the prefix shape and the freshness of x' in N.     *)
(* ----------------------------------------------------------------------- *)

Definition float_prefix (nm b' : nterm) (x' : nat) : nterm :=
  NNew x' (NPrefix nm b').

(* Every variable free in the prefix's NAME stays free after the float:
   the fresh binder x' cannot capture it. *)
Theorem float_preserves_name_free_vars :
  forall nm b' x' v,
    fresh x' nm ->
    In v (free_vars nm) ->
    In v (free_vars (float_prefix nm b' x')).
Proof.
  intros nm b' x' v Hfresh Hv.
  unfold float_prefix, fresh in *. simpl.
  (* free_vars (NNew x' (NPrefix nm b')) = remove x' (free_vars nm ++ free_vars b') *)
  apply in_in_remove.
  - (* v <> x' : v is free in nm, but x' is not *)
    intro Heq. subst v. apply Hfresh. exact Hv.
  - (* In v (free_vars nm ++ free_vars b') *)
    apply in_or_app. left. exact Hv.
Qed.

(* The dual direction: nothing free in the body (other than the new binder) is
   lost either — the float neither captures nor drops free names of the body. *)
Theorem float_preserves_body_free_vars :
  forall nm b' x' v,
    fresh x' b' ->
    In v (free_vars b') ->
    In v (free_vars (float_prefix nm b' x')).
Proof.
  intros nm b' x' v Hfresh Hv.
  unfold float_prefix, fresh in *. simpl.
  apply in_in_remove.
  - intro Heq. subst v. apply Hfresh. exact Hv.
  - apply in_or_app. right. exact Hv.
Qed.

(* ----------------------------------------------------------------------- *)
(* T1' (contrast) — reusing the ORIGINAL binder (no freshening) CAN capture. *)
(* This is `from_parts_unsafe` / run_ascent's bug: a name free in N becomes  *)
(* bound when N moves under the (non-freshened) binder. The witness is the   *)
(* prefix on the very name the binder restricts.                            *)
(* ----------------------------------------------------------------------- *)

Definition naive_float (nm b : nterm) (x : nat) : nterm :=
  NNew x (NPrefix nm b).

Theorem naive_float_can_capture :
  exists nm b x v,
    In v (free_vars nm) /\
    ~ In v (free_vars (naive_float nm b x)).
Proof.
  (* nm = NVar 0 (a name `x`), binder x = 0 (the SAME name), body = NPar [].
     The name 0 is free in nm but captured by `new^0` in the naive float. *)
  exists (NVar 0), (NPar []), 0, 0.
  unfold naive_float. split.
  - simpl. left. reflexivity.
  - (* ~ In 0 (remove 0 (free_vars (NPrefix (NVar 0) (NPar [])))) by remove_In;
       no `simpl` first, which would collapse the `remove` and break unification. *)
    apply remove_In.
Qed.

(* And the float-with-fresh-binder does NOT exhibit that capture — for the same
   witness the name stays free, because the fresh binder differs from it. *)
Theorem fresh_float_avoids_that_capture :
  In 0 (free_vars (float_prefix (NVar 0) (NPar []) 1)).
Proof.
  unfold float_prefix. (* In 0 (remove 1 (free_vars (NPrefix (NVar 0) (NPar [])))) *)
  apply in_in_remove.
  - discriminate.
  - simpl. left. reflexivity.
Qed.

(* ----------------------------------------------------------------------- *)
(* T2 — freshness lemmas for the ScopeExtrusion multiset gate.              *)
(* ----------------------------------------------------------------------- *)

Theorem free_vars_prefix :
  forall nm b, free_vars (NPrefix nm b) = free_vars nm ++ free_vars b.
Proof. reflexivity. Qed.

Theorem fresh_prefix_iff :
  forall x nm b, fresh x (NPrefix nm b) <-> fresh x nm /\ fresh x b.
Proof.
  intros x nm b. unfold fresh. simpl. split.
  - intro H. split; intro Hin; apply H; apply in_or_app; [left | right]; exact Hin.
  - intros [Hnm Hb] Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply Hnm; exact Hin.
    + apply Hb; exact Hin.
Qed.

(* The full-multiset freshness the handler's `is_fresh(_, residual_bag)` gate
   computes: a name is fresh in a parallel bag iff it is fresh in EVERY member
   (no representative shortcut). *)
Theorem fresh_par_iff :
  forall x ts, fresh x (NPar ts) <-> Forall (fresh x) ts.
Proof.
  intros x ts. unfold fresh. simpl. rewrite Forall_forall. split.
  - intros H t Ht Hin. apply H. apply in_flat_map. exists t. split; assumption.
  - intros H Hin. apply in_flat_map in Hin. destruct Hin as [t [Ht Hin]].
    apply (H t Ht Hin).
Qed.

(* The binder removes its own name: `new^x.b` is always fresh in x. This is why
   the float's `is_fresh` check against the FRESHENED binder is vacuously true
   (the freshened binder cannot occur free), so capture-avoidance comes from the
   re-close, not from a blocking guard. *)
Theorem new_is_fresh_in_its_binder :
  forall x b, fresh x (NNew x b).
Proof.
  intros x b. unfold fresh. simpl. apply remove_In.
Qed.
