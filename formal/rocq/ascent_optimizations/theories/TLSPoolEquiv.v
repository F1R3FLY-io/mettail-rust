(*
 * TLSPoolEquiv: Opt 2 — TLS Vec Pool Iteration Equivalence.
 *
 * Correctness claim: The thread-local-storage pool pattern
 *   (take → clear → push → take iter_buf → return)
 * produces the exact same list of elements as the original vec![] pattern,
 * for any input term and any prior pool contents.
 *
 * Proof strategy: Definitional equality. After clear, the pool's prior
 * contents are discarded. The push operations build exactly the same list
 * as the vec![] literal. The proof is by unfolding definitions and
 * case analysis on `classify t`.
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition          | Rust / Ascent Code                | Location
 *   -------------------------|-----------------------------------|--------------------------
 *   vec_pattern              | vec![...] in old subterm rules    | helpers.rs (pre-Opt2)
 *   pool_pattern             | generate_tls_pool_iter            | common.rs:448-482
 *   classify                 | match on term variant             | generated match arms
 *   clear                    | buf.clear()                       | common.rs:475
 *   push                     | buf.push(...)                     | common.rs (match arms)
 *   take / return            | p.take() / p.set(buf)             | common.rs:474, 479
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.

From AscentOptimizations Require Import Prelude.

Import ListNotations.

(* ===================================================================== *)
(*  Abstract Model                                                        *)
(* ===================================================================== *)

Section TLSPoolEquivalence.

  (* Term type and value type *)
  Variable T : Type.
  Variable V : Type.

  (* Classification function: maps a term to its constructor variant.
     Each variant determines which subterms (values) are extracted. *)
  Variable K : Type.
  Variable classify : T -> option K.

  (* Extraction: given a kind and a term, produce the list of subterm values.
     Returns [] if the term does not match the kind. *)
  Variable extract_values : K -> T -> list V.

  (* All constructor kinds *)
  Variable all_kinds : list K.

  (* ------------------------------------------------------------------- *)
  (*  vec![] pattern (original, pre-Opt2)                                 *)
  (* ------------------------------------------------------------------- *)

  (* The original pattern: for each constructor arm, produce a vec literal
     containing the extracted subterms. This is modeled as: classify the
     term, then extract the values for that kind. *)
  Definition vec_pattern (t : T) : list V :=
    match classify t with
    | Some k => extract_values k t
    | None => []
    end.

  (* ------------------------------------------------------------------- *)
  (*  Pool pattern (Opt 2: TLS Vec reuse)                                 *)
  (* ------------------------------------------------------------------- *)

  (* The pool pattern:
     1. Take buffer from TLS pool (has arbitrary prior contents)
     2. Clear the buffer (discards prior contents)
     3. Match on the term and push extracted values
     4. Take iter_buf = std::mem::take(&mut buf) (moves elements out)
     5. Return empty buf to pool

     After step 2 (clear), the prior contents are gone. Steps 3-4 build
     the same list as vec_pattern. We model this as: *)

  Definition pool_pattern (pool_contents : list V) (t : T) : list V :=
    (* Step 1: take — we receive pool_contents *)
    (* Step 2: clear — discard pool_contents, start fresh *)
    let buf := @nil V in
    (* Step 3: match and push — same extraction as vec_pattern *)
    let buf' := buf ++ match classify t with
                       | Some k => extract_values k t
                       | None => []
                       end in
    (* Step 4: take iter_buf = buf' *)
    (* Step 5: return empty buf to pool (not modeled, irrelevant to output) *)
    buf'.

  (* ================================================================= *)
  (*  Main Theorem: Pool pattern produces same elements as vec pattern  *)
  (* ================================================================= *)

  (* T1: For any term t and any prior pool contents, the pool pattern
     yields the exact same list as the vec![] pattern. *)
  Theorem pool_equiv :
    forall (t : T) (pool_contents : list V),
      pool_pattern pool_contents t = vec_pattern t.
  Proof.
    intros t pool_contents.
    unfold pool_pattern, vec_pattern.
    (* After clear, buf = []. Appending to [] is identity. *)
    destruct (classify t) as [k |].
    - (* Some k: both produce extract_values k t *)
      simpl. reflexivity.
    - (* None: both produce [] *)
      simpl. reflexivity.
  Qed.

  (* Corollary: The pool pattern is independent of prior pool contents *)
  Corollary pool_contents_irrelevant :
    forall (t : T) (c1 c2 : list V),
      pool_pattern c1 t = pool_pattern c2 t.
  Proof.
    intros t c1 c2.
    rewrite pool_equiv. rewrite pool_equiv. reflexivity.
  Qed.

  (* Corollary: Pool pattern with empty pool = vec pattern (special case) *)
  Corollary pool_empty_equiv :
    forall (t : T),
      pool_pattern [] t = vec_pattern t.
  Proof.
    intro t. apply pool_equiv.
  Qed.

End TLSPoolEquivalence.
