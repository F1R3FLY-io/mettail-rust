(*
 * LexForkKeywordReservation: the lex-fork at PrefixDispatch must not drop the
 * EXPLICITLY-DECLARED keyword interpretation of a token that is also lexable as
 * an identifier.
 *
 * Rust site: `emit_lex_fork_at_prefix_dispatch`
 * (macros/src/gen/runtime/wpda_codegen/forks.rs). A lex-ambiguous position
 * surfaces a PRIMARY lexical alternative (maximal-munch / keyword winner) plus
 * SECONDARY alternatives. The lex-fork rebuilds dispatch from
 * `lex_alt_rules_for_prefix`, whose `LexAltRuleKind` only represents
 * `Atomic | PrefixOp | CrossCatProjection` — it CANNOT represent collection-
 * literal rules (ListLit/BagLit/MapLit) nor multi-token keyword-prefix rules
 * (ElemList `at(...)`, …). For a keyword that ALSO matches the ident regex
 * (`list`/`at`/`error`/`int`/…) the lattice emits a SAME-LENGTH
 * `{Fixed("kw"), Ident}` ambiguity, so the buggy lex-fork forked only the
 * secondary `Ident -> Var` branch and the keyword parsed as a bare variable.
 *
 * Fix: wire the long-generated-but-never-called `prefix_primary_has_dispatch_rule`
 * into the fall-through decision, guarded by SAME-LENGTH (so genuine multi-length
 * disambiguation such as `-3` = {Minus@1, Integer@2} keeps forking both).
 *
 * Model. A lexical alternative carries a `kind` and a `len` (its end-byte span).
 * Two abstract per-language classifiers (Section variables, NOT axioms — they are
 * universally quantified at Section close):
 *   - `representable k` : the lex-alt table can build a branch for kind `k`
 *     (= `LexAltRuleKind` Atomic/PrefixOp/CrossCatProjection).
 *   - `has_dispatch k`  : the normal PrefixDispatch has an arm for kind `k`
 *     (= `prefix_primary_has_dispatch_rule`).
 * `num_branches` mirrors the Rust branch vector (primary if representable, plus
 * each representable secondary); `fall_through_old`/`fall_through_new` mirror the
 * `__fall_through` disjunction before/after the fix.
 *
 * Proven (zero-admission):
 *   - fix_preserves_keyword : a primary keyword with a normal dispatch arm and
 *     only same-length alternatives ALWAYS falls through to the normal dispatch
 *     (its declared interpretation is taken, never replaced by a lone Var).
 *   - multilength_guard : when some alternative differs in length, the NEW
 *     fall-through equals the OLD one — the fix never perturbs genuine
 *     multi-length disambiguation (regression-safety for `-3` & friends).
 *   - dropped_secondary_is_same_length : whenever the fix's new disjunct fires,
 *     every dropped secondary is a SAME-LENGTH lexical tie with the grammar-
 *     declared keyword — keyword-reservation is evidence (the grammar declares
 *     the literal), not a heuristic prune.
 *   - buggy_lexfork_drops_collection_keyword : the negative fence — a witness
 *     (collection keyword, `representable=false`, `has_dispatch=true`, one
 *     same-length representable Var secondary) where the OLD decision FORKS only
 *     the Var (keyword lost) while the NEW decision falls through (keyword kept).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Import ListNotations.

Section LexForkKeywordReservation.

  (* A lexical alternative at one DAG position: a token kind and an end-byte span. *)
  Record Alt : Type := { akind : nat; alen : nat }.

  (* Per-language classifiers (abstracted on Section close — not axioms). *)
  Variable representable : nat -> bool.   (* LexAltRuleKind-representable      *)
  Variable has_dispatch  : nat -> bool.   (* prefix_primary_has_dispatch_rule  *)

  (* The lex-fork branch vector: the primary contributes a branch iff its kind is
     representable; each representable secondary contributes one. (Mirrors the
     `__branches` Vec and `__primary_survived` flag.) *)
  Definition primary_survived (primary : Alt) : bool := representable (akind primary).

  Definition num_branches (primary : Alt) (secs : list Alt) : nat :=
    (if representable (akind primary) then 1 else 0)
    + length (filter (fun s => representable (akind s)) secs).

  (* `__all_alts_same_length`: every secondary ends at the same byte as the primary. *)
  Definition all_same_length (primary : Alt) (secs : list Alt) : bool :=
    forallb (fun s => Nat.eqb (alen s) (alen primary)) secs.

  (* `__fall_through` BEFORE the fix. *)
  Definition fall_through_old (primary : Alt) (secs : list Alt) : bool :=
    Nat.eqb (num_branches primary secs) 0
    || (Nat.eqb (num_branches primary secs) 1 && primary_survived primary).

  (* `__fall_through` AFTER the fix (the new third disjunct). *)
  Definition fall_through_new (primary : Alt) (secs : list Alt) : bool :=
    fall_through_old primary secs
    || (has_dispatch (akind primary) && all_same_length primary secs).

  (* When the lex-fork falls through, the normal `match peek` dispatch runs on the
     PRIMARY token's kind — which (when `has_dispatch` holds) owns the
     collection / keyword-prefix / terminal arm. So "fall through" ≡ "the declared
     keyword interpretation is dispatched", and "Fork" ≡ "branch over the lex-alt
     vector". This is the decision the theorems below pin down. *)

  (* (1) The fix: a primary keyword that owns a normal dispatch arm and has only
     same-length alternatives ALWAYS falls through — its declared interpretation
     is taken, never replaced by the lone secondary Var branch. *)
  Theorem fix_preserves_keyword :
    forall (primary : Alt) (secs : list Alt),
      has_dispatch (akind primary) = true ->
      all_same_length primary secs = true ->
      fall_through_new primary secs = true.
  Proof.
    intros primary secs Hdisp Hlen.
    unfold fall_through_new.
    rewrite Hdisp, Hlen. simpl.
    apply orb_true_r.
  Qed.

  (* (2) Regression-safety: when SOME alternative differs in length, the new
     fall-through is byte-identical to the old one. The same-length guard makes
     the fix inert on genuine multi-length disambiguation (`-3`, etc.). *)
  Theorem multilength_guard :
    forall (primary : Alt) (secs : list Alt),
      all_same_length primary secs = false ->
      fall_through_new primary secs = fall_through_old primary secs.
  Proof.
    intros primary secs Hlen.
    unfold fall_through_new.
    rewrite Hlen.
    rewrite andb_false_r.
    apply orb_false_r.
  Qed.

  (* A length-distinct alternative makes `all_same_length` false (the hypothesis of
     `multilength_guard`), so the two results coincide for it. *)
  Theorem length_distinct_alt_makes_guard :
    forall (primary : Alt) (secs : list Alt) (s : Alt),
      In s secs ->
      alen s <> alen primary ->
      all_same_length primary secs = false.
  Proof.
    intros primary secs s Hin Hneq.
    apply not_true_is_false. intro Hall.
    unfold all_same_length in Hall.
    rewrite forallb_forall in Hall.
    specialize (Hall s Hin).
    apply Nat.eqb_eq in Hall.
    contradiction.
  Qed.

  (* (3) Evidence, not heuristic: whenever the fix's new disjunct is what makes the
     position fall through, every secondary it drops is a SAME-LENGTH lexical tie
     with the grammar-declared keyword. *)
  Theorem dropped_secondary_is_same_length :
    forall (primary : Alt) (secs : list Alt) (s : Alt),
      has_dispatch (akind primary) = true ->
      all_same_length primary secs = true ->
      In s secs ->
      alen s = alen primary.
  Proof.
    intros primary secs s Hdisp Hlen Hin.
    unfold all_same_length in Hlen.
    rewrite forallb_forall in Hlen.
    specialize (Hlen s Hin).
    apply Nat.eqb_eq in Hlen. exact Hlen.
  Qed.

  (* (4) Negative fence: a collection-literal keyword (NOT lex-alt representable but
     WITH a normal dispatch arm) followed by exactly one same-length representable
     `Var` secondary. The OLD lex-fork FORKS only the Var (the keyword is lost) but
     the NEW lex-fork FALLS THROUGH (the keyword's collection dispatch is kept).
     This is precisely the `list(5)` / `at(...)` / `error op error` bug. *)
  (* kind 0 = collection keyword: dispatchable, NOT lex-alt-representable;
     kind 1 = Ident/Var: lex-alt-representable. *)
  Theorem buggy_lexfork_drops_collection_keyword :
    representable 0 = false ->
    representable 1 = true ->
    has_dispatch 0 = true ->
    fall_through_old {| akind := 0; alen := 4 |} [{| akind := 1; alen := 4 |}] = false /\
    fall_through_new {| akind := 0; alen := 4 |} [{| akind := 1; alen := 4 |}] = true.
  Proof.
    intros Hr0 Hr1 Hd0.
    unfold fall_through_new, fall_through_old, num_branches,
           primary_survived, all_same_length.
    cbn [akind alen filter length].
    rewrite Hr0, Hr1, Hd0.
    cbn.
    split; reflexivity.
  Qed.

End LexForkKeywordReservation.
