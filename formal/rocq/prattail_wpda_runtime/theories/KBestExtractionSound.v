(*
 * KBestExtractionSound: Phase-3 formal verification of the ROOT-P k-best
 * extraction campaign (DESIGN OF RECORD v2,
 * scratchpad/zz_probes/kbest_extraction_plan.md, red-teamed 2026-07-17;
 * verdicts: kbest_extraction_redteam.md).  The spec's §2 THE EXTRACTOR and
 * §3 EXACTNESS are binding; the model below is the closed-world finite
 * transcription of exactly the semantics the spec pins:
 *
 *   - FOREST (spec §2.1/§2.2): a finite DAG of OR-nodes 0..num_nodes-1;
 *     `packings_of v` lists node v's AND-alternatives in STORED INSERTION
 *     ORDER (the `priority_ordered_packings` no-reorder contract,
 *     wpda_walker.rs:7381-7420); each packing is its list of OR-children.
 *     Non-OR children (Terminal/TriggerTerminal/Epsilon/OptAbsent/...,
 *     spec §2.1) contribute fixed singleton values and are NOT j-indexed
 *     (spec §2.2) — they are absorbed into the abstract per-(node,packing)
 *     action `act` and key composition `kcomp`, so packing children here
 *     are the OR-children only.
 *   - DERIVATIONS: finite trees `mkD v e ds` — "choose packing e at node v,
 *     with sub-derivation ds_i for the i-th OR-child".  `dval` realizes a
 *     derivation through `act : node -> packing -> list Val -> option Val`;
 *     `act ... = None` IS the abstract per-candidate feasibility predicate
 *     (spec §2.5's empty-realize condition set, OBSERVED at candidate
 *     evaluation).  `dkey` composes the mode order key through
 *     `kcomp : node -> packing -> list K -> K` (spec §2.4: both keys
 *     compose from child entries without firing actions).
 *   - THE PER-NODE LOOP RESULT (spec §2.3): candidates cand(v,e,j) range
 *     over the packings × the product of the children's extracted lists;
 *     they are examined in nondecreasing key order (heap = the sort below;
 *     the deterministic (pk_idx, j) tie-break refines the key preorder, so
 *     every theorem here — all are minimality/completeness/set statements,
 *     robust to tie order — holds a fortiori for the refined comparator);
 *     infeasible candidates are skipped; observational dedup keeps the
 *     first candidate of each fingerprint class (`scan` below).  The min-W
 *     "strictly-less replaces, ties keep first" representative fold
 *     (dedup_push_realized :7484-7501) is modeled by keep-first: under
 *     nondecreasing pops a strictly smaller same-class weight never
 *     arrives later, so the fold is a no-op — proven as
 *     `w_dedup_fold_noop` in the WeightMode section rather than assumed.
 *   - SESSION ON-STACK RULE (amendment A2, spec §2.3/§2.5 item 6): the
 *     extractor is stack-parameterized; a demand of an on-stack node
 *     returns the empty list, so the demanding candidate is never seeded
 *     and there is no retry — the FAMILY provisional-empty analog
 *     (memo.insert(sym, Vec::new()) before descending, :10577-10580),
 *     per-DEMAND and sibling-preserving: cyclic-but-productive nodes keep
 *     exactly their acyclic readings.  The model recomputes per demand
 *     (each demand instance sees its own stack); the implementation
 *     memoizes the FIRST demand.  On acyclic forests the stack never
 *     blocks, so the two coincide and the model is exact; on cyclic
 *     forests the modeled rule is the per-demand ideal, which is the rule
 *     T2 is stated (and contracted) for: the enumerated set at stack S is
 *     precisely the S-AVOIDING derivations (`Avoid` below) — at the root,
 *     the ACYCLIC-WITNESSED derivations (no node repeats along any
 *     root-to-leaf path).
 *   - PER-NODE DISTINCT-k LISTS + TRUNCATION FLAG (amendments A3/A4, spec
 *     §3.2): the BoundedEnumeration session caps every node's delivered
 *     list at k (`xcap` = firstn k of the full scan `xscan`); the node's
 *     truncated flag abstracts to "the full scan exceeded k" (the
 *     operational flag — reached k with a non-empty frontier — is
 *     conservative: operational-flag-false implies the frontier drained,
 *     hence every candidate over the delivered child lists was examined,
 *     hence the model flag is false; theorems conditioned on the model
 *     flag therefore cover every operational no-flag run).  `no_trunc` is
 *     the demanded-set OR of amendment A4: it walks EVERY demand instance
 *     of the session (a node demanded from two parents appears under both
 *     — the "memo-hits included" half of the A4 rule).
 *   - TWO ORDER KEYS (spec §2.3 session-mode table): the development is
 *     over an abstract key carrier K with a boolean total preorder `kleb`
 *     (Election = CgllKTuple's strict-weak order `lt` :469-487 completed
 *     by the (pk_idx, j) tie-break — a total preorder is exactly what
 *     survives abstraction; Weight = LexicographicWeight's `lex_cmp`
 *     :419-429, total).  The WeightMode section at the end instantiates
 *     the stated ⊕/⊗ hypotheses: ⊕ = selection of the kleb-min
 *     (selective, hence a total-order semiring sum, spec §3.4 Q3) and ⊗
 *     weakly monotone on both sides, and DERIVES the composition-
 *     monotonicity hypothesis `kcomp_mono` used by the order-exactness
 *     theorems (Goodman / Huang-Chiang superiority).
 *
 * THEOREMS (contract numbering; zero admissions, audited at EOF):
 *   T1 t1_elect_soundness_all_feasible / t1_elect_soundness_feasible_subset
 *      — on an acyclic forest, the root's list head is a (feasible)
 *        derivation of the root whose key is <= the key of EVERY (feasible)
 *        derivation of the root: list[0] is an argmin of the mode order
 *        over the root's derivation set (resp. its feasible subset).
 *   T2 t2_exhaustion_iff (+ _acyclic, + t2_capped_pass_sound,
 *      t2_capped_empty_no_trunc, t2_driver_terminates)
 *      — the root list is empty iff no feasible stack-avoiding
 *        (acyclic-witnessed) derivation exists; the capped passes and the
 *        A4(iii) grow-and-re-extract driver's exit cases are each covered:
 *        a non-empty capped pass witnesses a feasible derivation, an empty
 *        no-trunc pass refutes all of them, and k >= maxlen forces
 *        no_trunc (driver termination witness).
 *   T3 t3_invariant / t3_k_exactness (+ t3_all_classes_when_short)
 *      — under the stated hypotheses (total preorder; kcomp monotone —
 *        the weak-⊗ lift; class-congruent actions = observational-dedup
 *        soundness; slot-injective composition = spec §3.3; total actions
 *        = the spec's I=0/constructor-builder audit regime, see
 *        obstruction note (2)), the delivered k-list is sorted, class-
 *        distinct, and IS the top-k: every entry's key is its class's
 *        minimum over the node's feasible derivations, and every feasible
 *        derivation's class is either present or dominated by a full list
 *        of k entries with keys <= its key.
 *   T4 t4_pop_count / t4_work_bound_node / t4_work_bound_total
 *      (+ t4_append_bound, t4_push_bound, t4_pops_le_pushed,
 *      t4_pop_universe, t4_pop_polynomial, t4_loop_done_or_step,
 *      cand_list_length_bound, t4_candidate_space_binary)
 *      — the Huang-Chiang loop skeleton (pop; classify append/infeasible/
 *        dup; push <= arity successors, pushed-set dedup; stop at k or
 *        empty frontier) satisfies pops = appends + I + D <= k + I + D,
 *        pushes <= |seeds| + arity*pops, hence the contracted
 *        total pops <= Σ_v (|packings(v)| + 2*(k + I_v + D_v)); and
 *        pops <= |candidate universe| <= |packings| * k^arity
 *        (k² on the binary getNodeP spine) — the O(|forest|·k²) corollary
 *        (spec §2.8, amendment A9's k^arity wording).
 *   T5 t5_truncation_completeness
 *      — if NO demanded node's truncated flag is set (the A4 demanded-set
 *        OR over every demand instance, memo-hits included), the delivered
 *        root list contains EVERY distinct class of the root's feasible
 *        stack-avoiding derivations (and has <= k entries): complete, a
 *        fortiori "complete up to k".
 *
 * OBSTRUCTION ADJUDICATIONS (stated per the contract; nothing weakened
 * silently, strongest true variants proven):
 *   (1) T1 as contracted ("list[0] = the argmin over the derivation set")
 *       is FALSE for a fully abstract order with no composition
 *       hypothesis: with one child C carrying derivations d1 < d2 and a
 *       parent key composition inverting them, the child's k=1 list
 *       retains only d1 and the parent elects through d1 although the
 *       global argmin routes through d2.  The claim requires composition
 *       monotonicity (kcomp_mono) — exactly Goodman's superiority, which
 *       the Weight key satisfies (w_kcompW_mono) and which is therefore
 *       stated as the mode-order precondition.  Without it the true
 *       statement is the spec's own §5.3 Phase-3 wording ("elected =
 *       per-node-argmin fixpoint over feasible candidates") — the local
 *       fixpoint is what `xfull` computes BY CONSTRUCTION, so the
 *       fixpoint reading holds definitionally here and the theorems add
 *       the global-argmin content under kcomp_mono.
 *   (2) T3's class-injectivity premise is productive only alongside
 *       act-TOTALITY (all candidates feasible): with partial actions the
 *       k dominating same-slot exchange candidates that force a hidden
 *       class out of the top-k can themselves be infeasible, and the
 *       hidden class may truly belong in the top-k while unreachable
 *       (child truncated) — that regime is exactly what the A4 truncation
 *       flag + T5 govern.  The spec's §3.3 injectivity audit is itself an
 *       audit of TOTAL constructor-builder actions on the green corpus
 *       (measured I = 0), so act_total is stated as a T3 hypothesis, and
 *       T5 (no truncation ⇒ completeness, no injectivity/totality needed)
 *       carries the load for partial actions.
 *   (3) T2/T5's completeness direction and T1's feasible-subset variant
 *       need dedup to be OBSERVATIONALLY SOUND: fingerprint-equal child
 *       values must be interchangeable for definedness and class of the
 *       parent action (`act_class_congruent`).  This is the formal
 *       content of "observational dedup" plus the spec's R-11 exclusion
 *       (fingerprint collisions out of scope: fp is intended semantic
 *       identity); with an injective fp the hypothesis is trivial.
 *
 * WHAT IS NOT CLAIMED (out of the Phase-3 contract's model list; covered
 * by the campaign's S1-S3 A/B receipts instead): the lazy-frontier
 * heap-order operational bridge (that the Huang-Chiang successor lattice
 * enumerates the sorted candidate stream — the standard Alg.-3 invariant;
 * the T4 section models the loop's counting skeleton and the denotational
 * layer models its RESULT); bit-parity of the CgllKTuple internals
 * (fdepth/Decisions/Scan, amendments A1/A8 — receipt-gated, R-1/R-4);
 * the FIRST-RAW third demand kind (amendment A10 — a key override for
 * collection items/optional inners, orthogonal to these theorems); the
 * A4(ii) facade padding carrier (facade-mechanical).
 *
 * FAILED / REJECTED STRATEGIES (documented so they are never re-attempted):
 *   - Proving T1-global with kleb abstract and NO kcomp_mono: refuted by
 *     the order-inversion counterexample of adjudication (1).  Do not
 *     retry; the hypothesis is necessary.
 *   - Proving T3 top-k dominance from slot-injectivity WITHOUT act_total:
 *     refuted — the dominating exchange candidates alter a slot class, so
 *     congruence cannot transport their feasibility (adjudication (2)).
 *   - Modeling per-node lists with a HARD k-cap that also refuses the
 *     election-mode feasibility hunt: falsifies T1 (a parent hunting past
 *     an infeasible best would be cut off at the child's cap and elect a
 *     non-argmin without any flag).  The spec's own mode table pins k=1 as
 *     "demand-grown past 1 ... while hunting feasibility" and §7-Q4 pins
 *     full-product successor reachability, so Election mode is modeled
 *     uncapped (`xfull`) and the capped `xcap`/`xscan` model the
 *     BoundedEnumeration session where the A4 flag machinery governs.
 *   - A fuel-stability lemma ("xfull fuel = xfull (S num_nodes) for fuel
 *     large enough"): unnecessary — threading the invariant
 *     S num_nodes <= fuel + |stack| with NoDup/bounded stacks makes every
 *     recursive call self-sufficient (`ctx` below); on-stack refusal
 *     keeps demand stacks duplicate-free, so depth num_nodes+1 suffices
 *     even on cyclic forests.
 *   - Storing realized values/keys inside list entries: rejected — with
 *     entries AS derivations, value/key/class correctness is definitional
 *     (dval/dkey/dcls) and every soundness invariant collapses to
 *     membership facts.
 *   - Counting the T3 dominators by list POSITIONS (pigeonhole on nth):
 *     replaced by the count/filter argument (`ssorted_count_firstn`) plus
 *     NoDup_incl_length — no positional reasoning anywhere.
 *   - `nia` and stdlib-name roulette: nonlinear steps are done with
 *     explicit Nat.mul lemmas; small list lemmas with unstable stdlib
 *     names (Forall2_app/length, skipn_length, NoDup_filter, remove
 *     lemmas, ...) are self-provided.
 *
 * Rocq 9.1 compatible.  No Admitted, no admit, no Axiom, no Parameter —
 * section Variables/Hypotheses become explicit premises of the closed
 * theorems (house style, cf. PurePackingPreservation.v).
 *
 * ★ DIVERGENCE-I RE-CHECK (2026-07-25). Closing divergence I partitioned
 * Rholang's/Calculator's integer LITERAL domains (`BigInt`'s eval was a
 * universal acceptor of every integer spelling). That STRICTLY SHRINKS the
 * literal cohort at every token shape — proved, not assumed, as
 * `LiteralCarrierContextIndependence.T_CohortShrinks`, with the a-fortiori step
 * for any cohort-size-monotone bound as `T_CohortBoundsHoldAFortiori`. The
 * bounds below are cohort-size monotone, so they hold A FORTIORI; nothing in
 * this file needed to change. ⚠ Note what does NOT hold and is deliberately not
 * claimed: per-CATEGORY containment. The new `Int` domain accepts `5u32`, which
 * the old one refused outright (`parse_int_lit(text, Some(I64))` rejects a
 * mismatched fixed suffix); it is the cohort's SIZE that is non-increasing.
 *)

From Stdlib Require Import List Bool PeanoNat Arith Lia.
Import ListNotations.

(* ════════════════════════════════════════════════════════════════════════
   Part 0 — generic list infrastructure (self-provided where stdlib names
   are unstable across versions).
   ════════════════════════════════════════════════════════════════════════ *)

Lemma nodup_app_disjoint :
  forall (A : Type) (l1 l2 : list A),
    NoDup l1 -> NoDup l2 ->
    (forall x, In x l1 -> ~ In x l2) ->
    NoDup (l1 ++ l2).
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros l2 Hnd1 Hnd2 Hdisj.
  - exact Hnd2.
  - cbn [app]. inversion Hnd1 as [|? ? Hnin Hnd1']; subst.
    constructor.
    + intro Hin. apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
      * exact (Hnin Hin).
      * exact (Hdisj a (or_introl eq_refl) Hin).
    + apply IH; [exact Hnd1' | exact Hnd2 |].
      intros x Hx. exact (Hdisj x (or_intror Hx)).
Qed.

Lemma NoDup_map_same :
  forall (A B : Type) (f : A -> B) (l : list A) x y,
    NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  intros A B f l. induction l as [|a l IH]; intros x y Hnd Hx Hy Hfxy.
  - destruct Hx.
  - cbn in Hnd. inversion Hnd as [|? ? Hnin Hnd']; subst.
    destruct Hx as [-> | Hx]; destruct Hy as [-> | Hy].
    + reflexivity.
    + exfalso. apply Hnin. rewrite Hfxy. apply in_map. exact Hy.
    + exfalso. apply Hnin. rewrite <- Hfxy. apply in_map. exact Hx.
    + apply IH; assumption.
Qed.

Lemma nd_map_inv :
  forall (A B : Type) (f : A -> B) (l : list A), NoDup (map f l) -> NoDup l.
Proof.
  intros A B f l. induction l as [|a l IH]; intro H; cbn in H.
  - constructor.
  - inversion H as [|? ? Hnin Hnd]; subst. constructor.
    + intro Hin. apply Hnin. apply in_map. exact Hin.
    + apply IH. exact Hnd.
Qed.

Lemma In_firstn :
  forall (A : Type) n (l : list A) x, In x (firstn n l) -> In x l.
Proof.
  intros A n l. revert n. induction l as [|a l IH]; intros n x H.
  - destruct n; cbn in H; destruct H.
  - destruct n; cbn in H; [destruct H|].
    destruct H as [-> | H]; [left; reflexivity | right; eapply IH; eauto].
Qed.

Lemma In_skipn :
  forall (A : Type) n (l : list A) x, In x (skipn n l) -> In x l.
Proof.
  intros A n. induction n as [|n IH]; intros l x H.
  - exact H.
  - destruct l as [|a l]; cbn in H; [destruct H|]. right. apply IH. exact H.
Qed.

Lemma NoDup_firstn :
  forall (A : Type) n (l : list A), NoDup l -> NoDup (firstn n l).
Proof.
  intros A n l. revert n. induction l as [|a l IH]; intros n H.
  - destruct n; constructor.
  - destruct n; cbn; [constructor|].
    inversion H as [|? ? Hnin Hnd]; subst. constructor.
    + intro Hin. apply Hnin. eapply In_firstn; eauto.
    + apply IH. exact Hnd.
Qed.

Lemma firstn_map :
  forall (A B : Type) (f : A -> B) n (l : list A),
    firstn n (map f l) = map f (firstn n l).
Proof.
  intros A B f n. induction n as [|n IH]; intros l.
  - reflexivity.
  - destruct l; cbn; [reflexivity|]. f_equal. apply IH.
Qed.

Lemma skipn_len :
  forall (A : Type) n (l : list A), length (skipn n l) = length l - n.
Proof.
  intros A n. induction n as [|n IH]; intros l.
  - cbn. lia.
  - destruct l; cbn; [reflexivity | apply IH].
Qed.

Lemma firstn_le_len :
  forall (A : Type) n (l : list A), length (firstn n l) <= n.
Proof. intros; rewrite length_firstn; lia. Qed.

Lemma flt_len_le :
  forall (A : Type) (f : A -> bool) (l : list A), length (filter f l) <= length l.
Proof.
  intros A f l; induction l as [|a l IH]; cbn; [lia|].
  destruct (f a); cbn; lia.
Qed.

Lemma nodup_len_le :
  forall (A : Type) (dec : forall x y : A, {x = y} + {x <> y}) (l : list A),
    length (nodup dec l) <= length l.
Proof.
  intros A dec l; induction l as [|a l IH]; cbn; [lia|].
  destruct (in_dec dec a l); cbn; lia.
Qed.

Lemma nd_filter :
  forall (A : Type) (f : A -> bool) (l : list A), NoDup l -> NoDup (filter f l).
Proof.
  intros A f l H; induction H as [|x l Hnin Hnd IH]; cbn.
  - constructor.
  - destruct (f x) eqn:E; [|exact IH].
    constructor; [|exact IH]. intro Hin. apply Hnin.
    apply filter_In in Hin. tauto.
Qed.

Lemma f2_app :
  forall (A B : Type) (R : A -> B -> Prop) l1 m1 l2 m2,
    Forall2 R l1 m1 -> Forall2 R l2 m2 -> Forall2 R (l1 ++ l2) (m1 ++ m2).
Proof.
  intros A B R l1 m1 l2 m2 H1 H2.
  induction H1; cbn; [exact H2 | constructor; assumption].
Qed.

Lemma f2_length :
  forall (A B : Type) (R : A -> B -> Prop) l m, Forall2 R l m -> length l = length m.
Proof. intros A B R l m H; induction H; cbn; auto. Qed.

Lemma f2_impl :
  forall (A B : Type) (R1 R2 : A -> B -> Prop) l m,
    (forall a b, R1 a b -> R2 a b) -> Forall2 R1 l m -> Forall2 R2 l m.
Proof. intros A B R1 R2 l m Hi H; induction H; constructor; auto. Qed.

Lemma f2_in_l :
  forall (A B : Type) (R : A -> B -> Prop) l m,
    Forall2 R l m -> Forall2 (fun a b => R a b /\ In a l) l m.
Proof.
  intros A B R l m H; induction H as [|a b l' m' Hab H IH]; constructor.
  - split; [assumption | left; reflexivity].
  - eapply f2_impl; [|exact IH]. cbn. intros x y [Hr Hin].
    split; [assumption | right; assumption].
Qed.

Lemma f2_map_r :
  forall (A B : Type) (R : A -> B -> Prop) (g : B -> A) l m,
    Forall2 R l m -> (forall a b, R a b -> g b = a) -> map g m = l.
Proof.
  intros A B R g l m H Hg; induction H; cbn; [reflexivity|].
  f_equal; eauto.
Qed.

Lemma f2_forall_r :
  forall (A B : Type) (R : A -> B -> Prop) (P : B -> Prop) l m,
    Forall2 R l m -> (forall a b, R a b -> P b) -> Forall P m.
Proof. intros A B R P l m H Hp; induction H; constructor; eauto. Qed.

Lemma f2_forall_l :
  forall (A B : Type) (R : A -> B -> Prop) l m,
    Forall2 R l m -> Forall (fun a => exists b, R a b) l.
Proof. intros A B R l m H; induction H; constructor; eauto. Qed.

Lemma forall_ex_list :
  forall (A B : Type) (Q : A -> B -> Prop) (l : list A),
    Forall (fun a => exists b, Q a b) l -> exists bs, Forall2 Q l bs.
Proof.
  intros A B Q l H. induction H as [|a l Ha _ IH].
  - exists []. constructor.
  - destruct Ha as [b Hb]. destruct IH as [bs Hbs].
    exists (b :: bs). constructor; assumption.
Qed.

Lemma forall_or_split :
  forall (A : Type) (P Q : A -> Prop) (l : list A),
    Forall (fun a => P a \/ Q a) l ->
    Forall P l \/ exists pre x post, l = pre ++ x :: post /\ Q x.
Proof.
  intros A P Q l H. induction H as [|a l Ha _ IH].
  - left; constructor.
  - destruct Ha as [Hp | Hq].
    + destruct IH as [Hall | (pre & x & post & -> & Hx)].
      * left; constructor; assumption.
      * right. exists (a :: pre), x, post. split; [reflexivity | exact Hx].
    + right. exists [], a, l. split; [reflexivity | exact Hq].
Qed.

Lemma Forall2_map_l_intro :
  forall (A B C : Type) (f : A -> B) (R : B -> C -> Prop) l m,
    Forall2 (fun a c => R (f a) c) l m -> Forall2 R (map f l) m.
Proof. intros A B C f R l m H; induction H; cbn; constructor; assumption. Qed.

Lemma Forall2_map_l_elim :
  forall (A B C : Type) (f : A -> B) (R : B -> C -> Prop) l m,
    Forall2 R (map f l) m -> Forall2 (fun a c => R (f a) c) l m.
Proof.
  intros A B C f R l. induction l as [|a l IH]; intros m H; cbn in H.
  - inversion H; constructor.
  - inversion H; subst. constructor; [assumption | apply IH; assumption].
Qed.

Definition inb (x : nat) (l : list nat) : bool := existsb (Nat.eqb x) l.

Lemma inb_true_iff : forall x l, inb x l = true <-> In x l.
Proof.
  intros x l. unfold inb. rewrite existsb_exists. split.
  - intros (y & Hy & He). apply Nat.eqb_eq in He. subst. exact Hy.
  - intro H. exists x. split; [exact H | apply Nat.eqb_refl].
Qed.

Lemma inb_false_iff : forall x l, inb x l = false <-> ~ In x l.
Proof.
  intros x l. split.
  - intros Hf Hin. apply inb_true_iff in Hin. rewrite Hin in Hf. discriminate.
  - intro Hnin. destruct (inb x l) eqn:E; [|reflexivity].
    apply inb_true_iff in E. contradiction.
Qed.

(* ════════════════════════════════════════════════════════════════════════
   Part 1 — boolean total preorders: insertion sort, sortedness, and the
   sorted-prefix bounds used by the top-k dominance arguments.
   ════════════════════════════════════════════════════════════════════════ *)

Section BoolOrder.
  Variable A : Type.
  Variable leb : A -> A -> bool.
  Hypothesis leb_total : forall a b, leb a b = true \/ leb b a = true.
  Hypothesis leb_trans : forall a b c,
      leb a b = true -> leb b c = true -> leb a c = true.

  Lemma leb_refl : forall a, leb a a = true.
  Proof. intro a. destruct (leb_total a a); assumption. Qed.

  Inductive SSorted : list A -> Prop :=
  | SS_nil : SSorted []
  | SS_cons : forall x l,
      Forall (fun y => leb x y = true) l -> SSorted l -> SSorted (x :: l).

  Lemma ssorted_head_min :
    forall x l y, SSorted (x :: l) -> In y (x :: l) -> leb x y = true.
  Proof.
    intros x l y Hs Hin. inversion Hs as [|? ? Hf Hs']; subst.
    destruct Hin as [-> | Hin]; [apply leb_refl|].
    rewrite Forall_forall in Hf. apply Hf. exact Hin.
  Qed.

  Fixpoint insort (x : A) (l : list A) : list A :=
    match l with
    | [] => [x]
    | h :: t => if leb x h then x :: h :: t else h :: insort x t
    end.

  Definition sortby (l : list A) : list A := fold_right insort [] l.

  Lemma insort_in_iff : forall x l y, In y (insort x l) <-> y = x \/ In y l.
  Proof.
    intros x l. induction l as [|h t IH]; intro y; cbn.
    - intuition congruence.
    - destruct (leb x h); cbn; [intuition congruence|].
      rewrite IH. intuition congruence.
  Qed.

  Lemma insort_length : forall x l, length (insort x l) = S (length l).
  Proof.
    intros x l; induction l as [|h t IH]; cbn; [reflexivity|].
    destruct (leb x h); cbn; [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma insort_forall :
    forall (P : A -> Prop) x l, P x -> Forall P l -> Forall P (insort x l).
  Proof.
    intros P x l Hx Hl. induction Hl as [|h t Hh Ht IH]; cbn.
    - constructor; [exact Hx | constructor].
    - destruct (leb x h).
      + constructor; [exact Hx | constructor; assumption].
      + constructor; [exact Hh | exact IH].
  Qed.

  Lemma insort_ssorted : forall x l, SSorted l -> SSorted (insort x l).
  Proof.
    intros x l H. induction H as [|h t Hf Hs IH]; cbn.
    - constructor; constructor.
    - destruct (leb x h) eqn:E.
      + constructor.
        * constructor; [exact E|].
          eapply Forall_impl; [|exact Hf]. cbn. intros y Hy.
          eapply leb_trans; eauto.
        * constructor; assumption.
      + assert (Hhx : leb h x = true).
        { destruct (leb_total x h) as [H1 | H1];
            [rewrite H1 in E; discriminate | exact H1]. }
        constructor.
        * apply insort_forall; [exact Hhx | exact Hf].
        * exact IH.
  Qed.

  Lemma sortby_in_iff : forall l y, In y (sortby l) <-> In y l.
  Proof.
    intros l; induction l as [|h t IH]; intro y; cbn.
    - tauto.
    - rewrite insort_in_iff, IH. intuition congruence.
  Qed.

  Lemma sortby_length : forall l, length (sortby l) = length l.
  Proof.
    unfold sortby.
    induction l as [|h t IH]; cbn; [reflexivity|].
    rewrite insort_length, IH. reflexivity.
  Qed.

  Lemma sortby_ssorted : forall l, SSorted (sortby l).
  Proof.
    induction l as [|h t IH]; cbn;
      [constructor | apply insort_ssorted; exact IH].
  Qed.

  (* Sorted-prefix bound 1: any delivered (firstn) element precedes any
     residual (skipn) element — "delivered keys <= beyond-cap keys". *)
  Lemma ssorted_firstn_skipn :
    forall n l x y,
      SSorted l -> In x (firstn n l) -> In y (skipn n l) -> leb x y = true.
  Proof.
    intros n. induction n as [|n IH]; intros l x y Hs Hx Hy.
    - cbn in Hx. destruct Hx.
    - destruct l as [|h t]; cbn in Hx; [destruct Hx|].
      cbn in Hy. destruct Hx as [-> | Hx].
      + eapply ssorted_head_min; [exact Hs|]. right. eapply In_skipn; eauto.
      + inversion Hs; subst. eapply IH; eauto.
  Qed.

  (* Sorted-prefix bound 2: if at least n elements of a sorted list are
     <= B, then EVERY element of its length-n prefix is <= B (the count
     route that replaces positional pigeonhole reasoning). *)
  Lemma ssorted_count_firstn :
    forall l (B : A) n x,
      SSorted l ->
      n <= length (filter (fun y => leb y B) l) ->
      In x (firstn n l) ->
      leb x B = true.
  Proof.
    intros l. induction l as [|h t IH]; intros B n x Hs Hn Hx.
    - destruct n; cbn in Hx; destruct Hx.
    - destruct n as [|n]; cbn in Hx; [destruct Hx|].
      cbn in Hn. destruct (leb h B) eqn:E.
      + cbn in Hn. destruct Hx as [-> | Hx]; [exact E|].
        inversion Hs; subst.
        apply (IH B n x); [assumption | lia | exact Hx].
      + exfalso.
        assert (Hne : 1 <= length (filter (fun y => leb y B) t)) by lia.
        destruct (filter (fun y => leb y B) t) as [|w ws] eqn:Ef;
          cbn in Hne; [lia|].
        assert (Hw : In w (filter (fun y => leb y B) t))
          by (rewrite Ef; left; reflexivity).
        apply filter_In in Hw. destruct Hw as [Hwt HwB].
        assert (Hhw : leb h w = true)
          by (eapply ssorted_head_min; [exact Hs | right; exact Hwt]).
        rewrite (leb_trans _ _ _ Hhw HwB) in E. discriminate.
  Qed.

  Lemma ssorted_firstn : forall n l, SSorted l -> SSorted (firstn n l).
  Proof.
    intros n. induction n as [|n IH]; intros l Hs; cbn; [constructor|].
    destruct l as [|h t]; [constructor|].
    inversion Hs as [|? ? Hf Hs']; subst. constructor.
    - rewrite Forall_forall. intros y Hy.
      rewrite Forall_forall in Hf. apply Hf. eapply In_firstn; eauto.
    - apply IH. assumption.
  Qed.

End BoolOrder.

(* ════════════════════════════════════════════════════════════════════════
   Part 2 — the candidate product space (the j-vector lattice of
   cand(v, e, j), spec §2.2, materialized over the children's lists).
   ════════════════════════════════════════════════════════════════════════ *)

Fixpoint product {A : Type} (ls : list (list A)) : list (list A) :=
  match ls with
  | [] => [[]]
  | l :: rest => flat_map (fun x => map (cons x) (product rest)) l
  end.

Lemma product_in :
  forall (A : Type) (ls : list (list A)) (xs : list A),
    In xs (product ls) <-> Forall2 (fun l x => In x l) ls xs.
Proof.
  intros A ls. induction ls as [|l rest IH]; intro xs; cbn.
  - split.
    + intros [<- | []]. constructor.
    + intro H. inversion H; subst. left; reflexivity.
  - rewrite in_flat_map. split.
    + intros (x & Hx & Hxs). apply in_map_iff in Hxs.
      destruct Hxs as (ys & <- & Hys).
      constructor; [exact Hx | apply IH; exact Hys].
    + intro H. inversion H as [|? x ? ys Hx Hys]; subst.
      exists x. split; [exact Hx|].
      apply in_map_iff. exists ys.
      split; [reflexivity | apply IH; exact Hys].
Qed.

Lemma flat_map_map_cons_length :
  forall (A : Type) (l : list A) (L : list (list A)),
    length (flat_map (fun x => map (cons x) L) l) = length l * length L.
Proof.
  intros A l L. induction l as [|a l IH]; cbn; [reflexivity|].
  rewrite length_app, length_map, IH. reflexivity.
Qed.

Lemma pow_pos : forall k a, 1 <= k -> 1 <= k ^ a.
Proof.
  intros k a Hk. induction a as [|a IH]; cbn; [lia|].
  replace 1 with (1 * 1) by lia.
  apply Nat.mul_le_mono; assumption.
Qed.

Lemma product_length_bound :
  forall (A : Type) (ls : list (list A)) (k a : nat),
    1 <= k -> length ls <= a -> Forall (fun l => length l <= k) ls ->
    length (product ls) <= k ^ a.
Proof.
  intros A ls. induction ls as [|l rest IH]; intros k a Hk Hlen Hall; cbn.
  - apply pow_pos. exact Hk.
  - destruct a as [|a]; cbn in Hlen; [lia|].
    rewrite flat_map_map_cons_length.
    inversion Hall; subst. cbn.
    apply Nat.mul_le_mono; [assumption|].
    apply IH; [exact Hk | lia | assumption].
Qed.

(* ════════════════════════════════════════════════════════════════════════
   Part 3 — the forest model, derivations, and the extractor.
   ════════════════════════════════════════════════════════════════════════ *)

(* A derivation: node id, packing index at that node, sub-derivations for
   the packing's OR-children in order.  A rose tree; the strong induction
   principle threads a Forall over the children. *)
Inductive D : Type := mkD : nat -> nat -> list D -> D.

Definition dnode (d : D) : nat := match d with mkD v _ _ => v end.

Fixpoint D_ind_strong (P : D -> Prop)
    (H : forall v e ds, Forall P ds -> P (mkD v e ds)) (d : D) : P d :=
  match d with
  | mkD v e ds =>
      H v e ds
        ((fix go (l : list D) : Forall P l :=
            match l with
            | [] => Forall_nil P
            | x :: l' => @Forall_cons D P x l' (D_ind_strong P H x) (go l')
            end) ds)
  end.

Section KBest.

  Variable Val : Type.   (* realized values (ActionArg/Term at Symbols)   *)
  Variable K : Type.     (* the mode order-key carrier (W or CgllKTuple)  *)
  Variable Cls : Type.   (* fingerprint classes (semantic_fingerprint)    *)
  Variable fp : Val -> Cls.
  Variable cls_eqb : Cls -> Cls -> bool.
  Hypothesis cls_eqb_spec : forall a b, cls_eqb a b = true <-> a = b.

  Variable kleb : K -> K -> bool.
  Hypothesis kleb_total : forall a b, kleb a b = true \/ kleb b a = true.
  Hypothesis kleb_trans : forall a b c,
      kleb a b = true -> kleb b c = true -> kleb a c = true.

  Definition kle (a b : K) : Prop := kleb a b = true.

  Lemma kle_refl : forall a, kle a a.
  Proof. intro a. unfold kle. destruct (kleb_total a a); assumption. Qed.

  Lemma kle_trans : forall a b c, kle a b -> kle b c -> kle a c.
  Proof. unfold kle. eauto. Qed.

  Variable num_nodes : nat.
  Variable packings_of : nat -> list (list nat).
  Hypothesis children_bounded :
    forall v ch c, v < num_nodes -> In ch (packings_of v) -> In c ch ->
      c < num_nodes.

  Variable act : nat -> nat -> list Val -> option Val.
  Variable kcomp : nat -> nat -> list K -> K.

  (* ── Derivation valuation and key. ── *)

  Fixpoint dval (d : D) {struct d} : option Val :=
    match d with
    | mkD v e ds =>
        match
          (fix go (xs : list D) : option (list Val) :=
             match xs with
             | [] => Some []
             | x :: xs' =>
                 match dval x with
                 | Some a =>
                     match go xs' with
                     | Some r => Some (a :: r)
                     | None => None
                     end
                 | None => None
                 end
             end) ds
        with
        | Some vs => act v e vs
        | None => None
        end
    end.

  Fixpoint dvals (xs : list D) : option (list Val) :=
    match xs with
    | [] => Some []
    | x :: xs' =>
        match dval x with
        | Some a =>
            match dvals xs' with
            | Some r => Some (a :: r)
            | None => None
            end
        | None => None
        end
    end.

  Lemma dvals_fix_eq :
    forall ds,
      (fix go (xs : list D) : option (list Val) :=
         match xs with
         | [] => Some []
         | x :: xs' =>
             match dval x with
             | Some a =>
                 match go xs' with
                 | Some r => Some (a :: r)
                 | None => None
                 end
             | None => None
             end
         end) ds = dvals ds.
  Proof.
    induction ds as [|x xs IH]; [reflexivity|].
    cbn. rewrite IH. reflexivity.
  Qed.

  Lemma dval_mkD :
    forall v e ds,
      dval (mkD v e ds) =
      match dvals ds with Some vs => act v e vs | None => None end.
  Proof. intros. cbn. rewrite dvals_fix_eq. reflexivity. Qed.

  Fixpoint dkey (d : D) {struct d} : K :=
    match d with
    | mkD v e ds =>
        kcomp v e
          ((fix go (xs : list D) : list K :=
              match xs with
              | [] => []
              | x :: xs' => dkey x :: go xs'
              end) ds)
    end.

  Fixpoint dkeys (xs : list D) : list K :=
    match xs with
    | [] => []
    | x :: xs' => dkey x :: dkeys xs'
    end.

  Lemma dkeys_fix_eq :
    forall ds,
      (fix go (xs : list D) : list K :=
         match xs with
         | [] => []
         | x :: xs' => dkey x :: go xs'
         end) ds = dkeys ds.
  Proof.
    induction ds as [|x xs IH]; [reflexivity|]. cbn. rewrite IH. reflexivity.
  Qed.

  Lemma dkey_mkD :
    forall v e ds, dkey (mkD v e ds) = kcomp v e (dkeys ds).
  Proof. intros. cbn. rewrite dkeys_fix_eq. reflexivity. Qed.

  Lemma dkeys_app :
    forall xs ys, dkeys (xs ++ ys) = dkeys xs ++ dkeys ys.
  Proof.
    induction xs as [|x xs IH]; intro ys; cbn; [reflexivity|].
    rewrite IH. reflexivity.
  Qed.

  Lemma dvals_forall2_of :
    forall xs vs, dvals xs = Some vs ->
      Forall2 (fun x v => dval x = Some v) xs vs.
  Proof.
    induction xs as [|x xs IH]; intros vs H; cbn in H.
    - inversion H; constructor.
    - destruct (dval x) eqn:Ex; [|discriminate].
      destruct (dvals xs) eqn:Exs; [|discriminate].
      inversion H; subst. constructor; [exact Ex | apply IH; reflexivity].
  Qed.

  Lemma dvals_of_forall :
    forall xs, Forall (fun x => exists w, dval x = Some w) xs ->
      exists ws, dvals xs = Some ws
                 /\ Forall2 (fun x w => dval x = Some w) xs ws.
  Proof.
    intros xs H. induction H as [|x xs [w Hw] _ (ws & Hws & Hf)].
    - exists []. split; [reflexivity | constructor].
    - exists (w :: ws). cbn. rewrite Hw, Hws.
      split; [reflexivity | constructor; assumption].
  Qed.

  Lemma dvals_app_some :
    forall xs ys vs ws,
      dvals xs = Some vs -> dvals ys = Some ws ->
      dvals (xs ++ ys) = Some (vs ++ ws).
  Proof.
    induction xs as [|x xs IH]; intros ys vs ws Hx Hy; cbn in *.
    - inversion Hx; subst. exact Hy.
    - destruct (dval x) eqn:Ex; [|discriminate].
      destruct (dvals xs) eqn:Exs; [|discriminate].
      inversion Hx; subst. rewrite (IH _ _ _ eq_refl Hy). reflexivity.
  Qed.

  Lemma dvals_app_split :
    forall xs ys us,
      dvals (xs ++ ys) = Some us ->
      exists vs ws, dvals xs = Some vs /\ dvals ys = Some ws /\ us = vs ++ ws.
  Proof.
    induction xs as [|x xs IH]; intros ys us H; cbn in H.
    - exists [], us. auto.
    - destruct (dval x) eqn:Ex; [|discriminate].
      destruct (dvals (xs ++ ys)) eqn:Exy; [|discriminate].
      inversion H; subst.
      destruct (IH _ _ Exy) as (vs & ws & Hvs & Hws & ->).
      exists (v :: vs), ws. cbn. rewrite Ex, Hvs. auto.
  Qed.

  (* ── Stack-avoiding wellformed derivations (the A2 on-stack rule's
        enumerated set) and plain wellformed derivations. ── *)

  Inductive Avoid : list nat -> D -> Prop :=
  | Avoid_mk : forall stack v e ds ch,
      ~ In v stack ->
      nth_error (packings_of v) e = Some ch ->
      map dnode ds = ch ->
      Forall (Avoid (v :: stack)) ds ->
      Avoid stack (mkD v e ds).

  Inductive Wf : D -> Prop :=
  | Wf_mk : forall v e ds ch,
      nth_error (packings_of v) e = Some ch ->
      map dnode ds = ch ->
      Forall Wf ds ->
      Wf (mkD v e ds).

  Lemma avoid_wf : forall d stack, Avoid stack d -> Wf d.
  Proof.
    intro d. induction d as [v e ds IH] using D_ind_strong.
    intros stack H. inversion H; subst.
    econstructor; eauto.
    rewrite Forall_forall in *. intros x Hx.
    eapply IH; eauto.
  Qed.

  (* ── Observational dedup scan (spec §2.3's evaluate/dedup/append step,
        over an already key-ordered candidate stream). ── *)

  Definition clsmem (c : Cls) (seen : list Cls) : bool :=
    existsb (cls_eqb c) seen.

  Lemma clsmem_true_iff : forall c seen, clsmem c seen = true <-> In c seen.
  Proof.
    intros c seen. unfold clsmem. rewrite existsb_exists. split.
    - intros (y & Hy & He). apply cls_eqb_spec in He. subst. exact Hy.
    - intro H. exists c. split; [exact H | apply cls_eqb_spec; reflexivity].
  Qed.

  Lemma clsmem_false_iff : forall c seen, clsmem c seen = false <-> ~ In c seen.
  Proof.
    intros c seen. split.
    - intros Hf Hin. apply clsmem_true_iff in Hin.
      rewrite Hin in Hf. discriminate.
    - intro Hnin. destruct (clsmem c seen) eqn:E; [|reflexivity].
      apply clsmem_true_iff in E. contradiction.
  Qed.

  Section Scan.
    Variable A : Type.
    Variable fv : A -> option Val.

    Definition clsf (x : A) : option Cls :=
      match fv x with Some v => Some (fp v) | None => None end.

    Fixpoint scan (cs : list A) (seen : list Cls) : list A :=
      match cs with
      | [] => []
      | h :: t =>
          match fv h with
          | None => scan t seen                       (* infeasible pop *)
          | Some v =>
              if clsmem (fp v) seen
              then scan t seen                        (* duplicate pop  *)
              else h :: scan t (fp v :: seen)         (* append         *)
          end
      end.

    Lemma scan_incl : forall cs seen x, In x (scan cs seen) -> In x cs.
    Proof.
      induction cs as [|h t IH]; intros seen x H; cbn in H; [destruct H|].
      destruct (fv h) eqn:E.
      - destruct (clsmem (fp v) seen).
        + right; eapply IH; eauto.
        + destruct H as [-> | H];
            [left; reflexivity | right; eapply IH; eauto].
      - right; eapply IH; eauto.
    Qed.

    Lemma scan_feasible :
      forall cs seen x, In x (scan cs seen) -> exists v, fv x = Some v.
    Proof.
      induction cs as [|h t IH]; intros seen x H; cbn in H; [destruct H|].
      destruct (fv h) eqn:E.
      - destruct (clsmem (fp v) seen).
        + eapply IH; eauto.
        + destruct H as [-> | H]; [exists v; exact E | eapply IH; eauto].
      - eapply IH; eauto.
    Qed.

    Lemma scan_disjoint :
      forall cs seen x c,
        In x (scan cs seen) -> clsf x = Some c -> ~ In c seen.
    Proof.
      induction cs as [|h t IH]; intros seen x c H Hc; cbn in H; [destruct H|].
      destruct (fv h) eqn:E.
      - destruct (clsmem (fp v) seen) eqn:Em.
        + eapply IH; eauto.
        + destruct H as [-> | H].
          * unfold clsf in Hc. rewrite E in Hc. inversion Hc; subst.
            apply clsmem_false_iff in Em. exact Em.
          * intro Hin. apply (IH _ _ _ H Hc). right. exact Hin.
      - eapply IH; eauto.
    Qed.

    Lemma scan_classes_nodup :
      forall cs seen, NoDup (map clsf (scan cs seen)).
    Proof.
      induction cs as [|h t IH]; intros seen; cbn; [constructor|].
      destruct (fv h) eqn:E; [|apply IH].
      destruct (clsmem (fp v) seen) eqn:Em; [apply IH|].
      cbn. constructor; [|apply IH].
      intro Hin. apply in_map_iff in Hin.
      destruct Hin as (y & Hy & Hyin).
      assert (Hcy : clsf y = Some (fp v)).
      { rewrite Hy. unfold clsf. rewrite E. reflexivity. }
      apply (scan_disjoint _ _ _ _ Hyin Hcy). left. reflexivity.
    Qed.

    Lemma scan_nodup : forall cs seen, NoDup (scan cs seen).
    Proof.
      intros cs seen. eapply nd_map_inv. apply scan_classes_nodup.
    Qed.

    Lemma scan_complete :
      forall cs seen c v,
        In c cs -> fv c = Some v -> ~ In (fp v) seen ->
        exists y, In y (scan cs seen) /\ clsf y = Some (fp v).
    Proof.
      induction cs as [|h t IH]; intros seen c v Hc Hv Hnin; [destruct Hc|].
      cbn. destruct (fv h) eqn:E.
      - destruct (clsmem (fp v0) seen) eqn:Em.
        + destruct Hc as [-> | Hc].
          * rewrite E in Hv. inversion Hv; subst.
            apply clsmem_true_iff in Em. contradiction.
          * eapply IH; eauto.
        + destruct Hc as [-> | Hc].
          * rewrite E in Hv. inversion Hv; subst.
            exists c. split; [left; reflexivity|].
            unfold clsf. rewrite E. reflexivity.
          * destruct (cls_eqb (fp v) (fp v0)) eqn:Ecls.
            -- apply cls_eqb_spec in Ecls.
               exists h. split; [left; reflexivity|].
               unfold clsf. rewrite E, Ecls. reflexivity.
            -- assert (Hne : fp v <> fp v0).
               { intro Habs.
                 assert (Ht : cls_eqb (fp v) (fp v0) = true)
                   by (apply cls_eqb_spec; exact Habs).
                 rewrite Ht in Ecls. discriminate. }
               destruct (IH (fp v0 :: seen) c v Hc Hv) as (y & Hy & Hcy).
               { intro Hin. destruct Hin as [Heq | Hin];
                   [apply Hne; symmetry; exact Heq | exact (Hnin Hin)]. }
               exists y. split; [right; exact Hy | exact Hcy].
      - destruct Hc as [-> | Hc]; [rewrite E in Hv; discriminate|].
        eapply IH; eauto.
    Qed.

    Variable aleb : A -> A -> bool.
    Hypothesis aleb_total : forall a b, aleb a b = true \/ aleb b a = true.
    Hypothesis aleb_trans : forall a b c,
        aleb a b = true -> aleb b c = true -> aleb a c = true.

    Lemma scan_sorted :
      forall cs seen, SSorted A aleb cs -> SSorted A aleb (scan cs seen).
    Proof.
      intros cs. induction cs as [|h t IH]; intros seen Hs; cbn; [constructor|].
      inversion Hs as [|? ? Hf Hs']; subst.
      destruct (fv h) eqn:E; [|apply IH; exact Hs'].
      destruct (clsmem (fp v) seen); [apply IH; exact Hs'|].
      constructor; [|apply IH; exact Hs'].
      rewrite Forall_forall. intros y Hy.
      rewrite Forall_forall in Hf. apply Hf. eapply scan_incl; eauto.
    Qed.

    (* The first appended member of a class precedes every same-class
       candidate in the stream: entry key = class-min over the candidate
       space (spec §3.2 "MIN-W per class"). *)
    Lemma scan_min :
      forall cs seen,
        SSorted A aleb cs ->
        forall x, In x (scan cs seen) ->
        forall y, In y cs -> clsf y = clsf x -> aleb x y = true.
    Proof.
      induction cs as [|h t IH]; intros seen Hs x Hx y Hy Hcls;
        [cbn in Hx; destruct Hx|].
      inversion Hs as [|? ? Hf Hs']; subst.
      cbn in Hx. destruct (fv h) eqn:E.
      - destruct (clsmem (fp v) seen) eqn:Em.
        + destruct Hy as [-> | Hy]; [|eapply IH; eauto].
          exfalso.
          assert (Hcx : clsf x = Some (fp v)).
          { rewrite <- Hcls. unfold clsf. rewrite E. reflexivity. }
          apply (scan_disjoint _ _ _ _ Hx Hcx).
          apply clsmem_true_iff. exact Em.
        + destruct Hx as [-> | Hx].
          * destruct Hy as [-> | Hy].
            { destruct (aleb_total y y); assumption. }
            { rewrite Forall_forall in Hf. apply Hf. exact Hy. }
          * destruct Hy as [-> | Hy]; [|eapply IH; eauto].
            exfalso.
            assert (Hcx : clsf x = Some (fp v)).
            { rewrite <- Hcls. unfold clsf. rewrite E. reflexivity. }
            apply (scan_disjoint _ _ _ _ Hx Hcx). left. reflexivity.
      - destruct Hy as [-> | Hy]; [|eapply IH; eauto].
        exfalso.
        destruct (scan_feasible _ _ _ Hx) as (vx & Hvx).
        unfold clsf in Hcls. rewrite E, Hvx in Hcls. discriminate.
    Qed.

  End Scan.

  Definition dcls : D -> option Cls := clsf D dval.


  (* ── The per-node candidate list: packings in stored order × the
        product of the children's delivered lists (spec §2.2/§2.3). ── *)

  Fixpoint cand_list_from (v e0 : nat) (pks : list (list nat))
      (childf : nat -> list D) : list D :=
    match pks with
    | [] => []
    | ch :: rest =>
        map (mkD v e0) (product (map childf ch))
        ++ cand_list_from v (S e0) rest childf
    end.

  Definition cand_list (v : nat) (childf : nat -> list D) : list D :=
    cand_list_from v 0 (packings_of v) childf.

  Lemma cand_list_from_in_iff :
    forall v pks e0 childf d,
      In d (cand_list_from v e0 pks childf) <->
      exists i ch choice,
        nth_error pks i = Some ch /\ d = mkD v (e0 + i) choice /\
        Forall2 (fun c x => In x (childf c)) ch choice.
  Proof.
    intros v pks. induction pks as [|ch rest IH]; intros e0 childf d; cbn.
    - split; [intros []|].
      intros (i & ch & choice & Hn & _). destruct i; discriminate.
    - rewrite in_app_iff, in_map_iff. split.
      + intros [(choice & <- & Hchoice) | Hrest].
        * exists 0, ch, choice.
          rewrite Nat.add_0_r.
          split; [reflexivity|]. split; [reflexivity|].
          apply product_in in Hchoice.
          apply Forall2_map_l_elim in Hchoice. exact Hchoice.
        * apply IH in Hrest.
          destruct Hrest as (i & ch' & choice & Hn & -> & Hf).
          exists (S i), ch', choice.
          rewrite Nat.add_succ_r.
          split; [exact Hn|]. split; [reflexivity | exact Hf].
      + intros (i & ch' & choice & Hn & -> & Hf).
        destruct i as [|i]; cbn in Hn.
        * inversion Hn; subst ch'.
          left. exists choice.
          rewrite Nat.add_0_r.
          split; [reflexivity|].
          apply product_in. apply Forall2_map_l_intro. exact Hf.
        * right. apply IH.
          exists i, ch', choice.
          rewrite Nat.add_succ_r.
          split; [exact Hn|]. split; [reflexivity | exact Hf].
  Qed.

  Lemma cand_list_in :
    forall v childf e ch choice,
      nth_error (packings_of v) e = Some ch ->
      Forall2 (fun c x => In x (childf c)) ch choice ->
      In (mkD v e choice) (cand_list v childf).
  Proof.
    intros v childf e ch choice Hn Hf.
    unfold cand_list. apply cand_list_from_in_iff.
    exists e, ch, choice. cbn. auto.
  Qed.

  Lemma cand_list_in_inv :
    forall v childf d,
      In d (cand_list v childf) ->
      exists e ch choice,
        d = mkD v e choice /\ nth_error (packings_of v) e = Some ch /\
        Forall2 (fun c x => In x (childf c)) ch choice.
  Proof.
    intros v childf d H.
    unfold cand_list in H. apply cand_list_from_in_iff in H.
    destruct H as (i & ch & choice & Hn & -> & Hf).
    exists i, ch, choice. cbn. auto.
  Qed.

  Lemma cand_list_from_ext :
    forall v pks e0 f1 f2,
      (forall ch c, In ch pks -> In c ch -> f1 c = f2 c) ->
      cand_list_from v e0 pks f1 = cand_list_from v e0 pks f2.
  Proof.
    intros v pks. induction pks as [|ch rest IH]; intros e0 f1 f2 Hext; cbn;
      [reflexivity|].
    f_equal.
    - do 2 f_equal. apply map_ext_in.
      intros c Hc. apply (Hext ch c); [left; reflexivity | exact Hc].
    - apply IH. intros ch' c Hch' Hc.
      apply (Hext ch' c); [right; exact Hch' | exact Hc].
  Qed.

  Lemma cand_list_from_length :
    forall v pks e0 childf,
      length (cand_list_from v e0 pks childf)
      = fold_right (fun ch n => length (product (map childf ch)) + n) 0 pks.
  Proof.
    intros v pks. induction pks as [|ch rest IH]; intros e0 childf; cbn;
      [reflexivity|].
    rewrite length_app, length_map, IH. reflexivity.
  Qed.

  (* T4 instantiation witness: with arities <= a and delivered child lists
     <= kk, one node's candidate universe is <= |packings| * kk^a
     (spec §2.8 / amendment A9's k^arity wording). *)
  Lemma cand_list_length_bound :
    forall v childf kk a,
      1 <= kk ->
      (forall ch, In ch (packings_of v) -> length ch <= a) ->
      (forall c, length (childf c) <= kk) ->
      length (cand_list v childf) <= length (packings_of v) * kk ^ a.
  Proof.
    intros v childf kk a Hk Har Hcf.
    unfold cand_list. rewrite cand_list_from_length.
    induction (packings_of v) as [|ch rest IH].
    - cbn. lia.
    - cbn.
      assert (Hch : length (product (map childf ch)) <= kk ^ a).
      { apply product_length_bound; [exact Hk| |].
        - rewrite length_map. apply Har. left. reflexivity.
        - rewrite Forall_forall. intros l Hl.
          apply in_map_iff in Hl. destruct Hl as (c & <- & _). apply Hcf. }
      assert (Hrest : fold_right
                        (fun ch0 n => length (product (map childf ch0)) + n)
                        0 rest
                      <= length rest * kk ^ a).
      { apply IH. intros ch' Hch'. apply Har. right. exact Hch'. }
      lia.
  Qed.

  (* On the binarized getNodeP spine (arity <= 2) the per-node candidate
     universe is <= |packings| * k².  The delivered child lists of a
     BoundedEnumeration session satisfy the length bound by construction
     (xcap = firstn k, `firstn_le_len`). *)
  Corollary t4_candidate_space_binary :
    forall v childf kk,
      1 <= kk ->
      (forall ch, In ch (packings_of v) -> length ch <= 2) ->
      (forall c, length (childf c) <= kk) ->
      length (cand_list v childf) <= length (packings_of v) * (kk * kk).
  Proof.
    intros v childf kk Hk Har Hcf.
    assert (Hpow : kk ^ 2 = kk * kk) by (cbn; rewrite Nat.mul_1_r; reflexivity).
    rewrite <- Hpow.
    apply cand_list_length_bound; assumption.
  Qed.

  (* ── The per-node combine: sort by key, dedup-scan (spec §2.3). ── *)

  Definition keyleb (a b : D) : bool := kleb (dkey a) (dkey b).

  Lemma keyleb_total : forall a b, keyleb a b = true \/ keyleb b a = true.
  Proof. intros. apply kleb_total. Qed.

  Lemma keyleb_trans : forall a b c,
      keyleb a b = true -> keyleb b c = true -> keyleb a c = true.
  Proof. unfold keyleb. eauto. Qed.

  Definition node_scan (v : nat) (childf : nat -> list D) : list D :=
    scan D dval (sortby D keyleb (cand_list v childf)) [].

  Lemma node_scan_ext :
    forall v f1 f2,
      (forall ch c, In ch (packings_of v) -> In c ch -> f1 c = f2 c) ->
      node_scan v f1 = node_scan v f2.
  Proof.
    intros v f1 f2 Hext. unfold node_scan, cand_list.
    rewrite (cand_list_from_ext v (packings_of v) 0 f1 f2 Hext).
    reflexivity.
  Qed.

  (* ── The extractor sessions (see header for the mode mapping). ── *)

  Fixpoint xfull (fuel : nat) (stack : list nat) (v : nat) : list D :=
    match fuel with
    | 0 => []
    | S f =>
        if inb v stack then []
        else node_scan v (fun c => xfull f (v :: stack) c)
    end.

  Fixpoint xscan (k fuel : nat) (stack : list nat) (v : nat) : list D :=
    match fuel with
    | 0 => []
    | S f =>
        if inb v stack then []
        else node_scan v (fun c => firstn k (xscan k f (v :: stack) c))
    end.

  Definition xcap (k fuel : nat) (stack : list nat) (v : nat) : list D :=
    firstn k (xscan k fuel stack v).

  Fixpoint no_trunc (k fuel : nat) (stack : list nat) (v : nat) : Prop :=
    match fuel with
    | 0 => True
    | S f =>
        if inb v stack then True
        else
          length (xscan k (S f) stack v) <= k
          /\ (forall ch c, In ch (packings_of v) -> In c ch ->
                no_trunc k f (v :: stack) c)
    end.

  Fixpoint maxlen (fuel : nat) (stack : list nat) (v : nat) : nat :=
    match fuel with
    | 0 => 0
    | S f =>
        if inb v stack then 0
        else
          Nat.max (length (xfull (S f) stack v))
            (fold_right
               (fun ch acc =>
                  Nat.max
                    (fold_right
                       (fun c acc2 => Nat.max (maxlen f (v :: stack) c) acc2)
                       0 ch) acc)
               0 (packings_of v))
    end.

  Lemma xfull_S :
    forall f stack v,
      xfull (S f) stack v
      = if inb v stack then []
        else node_scan v (fun c => xfull f (v :: stack) c).
  Proof. reflexivity. Qed.

  Lemma xscan_S :
    forall k f stack v,
      xscan k (S f) stack v
      = if inb v stack then []
        else node_scan v (fun c => firstn k (xscan k f (v :: stack) c)).
  Proof. reflexivity. Qed.

  Lemma no_trunc_S :
    forall k f stack v,
      no_trunc k (S f) stack v
      = if inb v stack then True
        else
          (length (xscan k (S f) stack v) <= k
           /\ (forall ch c, In ch (packings_of v) -> In c ch ->
                 no_trunc k f (v :: stack) c)).
  Proof. reflexivity. Qed.

  Lemma maxlen_S :
    forall f stack v,
      maxlen (S f) stack v
      = if inb v stack then 0
        else
          Nat.max (length (xfull (S f) stack v))
            (fold_right
               (fun ch acc =>
                  Nat.max
                    (fold_right
                       (fun c acc2 => Nat.max (maxlen f (v :: stack) c) acc2)
                       0 ch) acc)
               0 (packings_of v)).
  Proof. reflexivity. Qed.

  Lemma fold_max_in :
    forall (f : nat -> nat) (l : list nat) x,
      In x l -> f x <= fold_right (fun c acc => Nat.max (f c) acc) 0 l.
  Proof.
    intros f l. induction l as [|a l IH]; intros x Hx; [destruct Hx|].
    cbn. destruct Hx as [-> | Hx]; [lia|].
    specialize (IH _ Hx). lia.
  Qed.

  Lemma fold_max_ch_in :
    forall (g : list nat -> nat) (pks : list (list nat)) ch,
      In ch pks ->
      g ch <= fold_right (fun ch' acc => Nat.max (g ch') acc) 0 pks.
  Proof.
    intros g pks. induction pks as [|a pks IH]; intros ch Hch; [destruct Hch|].
    cbn. destruct Hch as [-> | Hch]; [lia|].
    specialize (IH _ Hch). lia.
  Qed.

  (* ── The fuel/stack sufficiency context. ── *)

  Definition ctx (fuel : nat) (stack : list nat) (v : nat) : Prop :=
    S num_nodes <= fuel + length stack
    /\ NoDup stack
    /\ (forall s, In s stack -> s < num_nodes)
    /\ v < num_nodes.

  Lemma stack_le :
    forall stack,
      NoDup stack -> (forall s, In s stack -> s < num_nodes) ->
      length stack <= num_nodes.
  Proof.
    intros stack Hnd Hb.
    replace num_nodes with (length (seq 0 num_nodes)) by apply length_seq.
    apply NoDup_incl_length; [exact Hnd|].
    intros s Hs. apply in_seq. cbn. split; [lia | apply Hb; exact Hs].
  Qed.

  Lemma ctx_fuel_S :
    forall fuel stack v, ctx fuel stack v -> exists f, fuel = S f.
  Proof.
    intros fuel stack v (Hle & Hnd & Hb & _).
    destruct fuel as [|f]; [|eauto].
    exfalso. cbn in Hle. pose proof (stack_le stack Hnd Hb). lia.
  Qed.

  Lemma ctx_child :
    forall f stack v c,
      ctx (S f) stack v -> ~ In v stack -> c < num_nodes ->
      ctx f (v :: stack) c.
  Proof.
    intros f stack v c (Hle & Hnd & Hb & Hv) Hnin Hc.
    repeat split.
    - cbn. cbn in Hle. lia.
    - constructor; assumption.
    - intros s Hs. destruct Hs as [<- | Hs]; [exact Hv | apply Hb; exact Hs].
    - exact Hc.
  Qed.

  Lemma ctx_root : forall root, root < num_nodes -> ctx (S num_nodes) [] root.
  Proof.
    intros root H. repeat split.
    - cbn. lia.
    - constructor.
    - intros s [].
    - exact H.
  Qed.

  (* ── Base invariants: soundness, key-sortedness, class-distinctness. ── *)

  Lemma node_scan_sound :
    forall stack v childf,
      ~ In v stack ->
      (forall ch c x, In ch (packings_of v) -> In c ch -> In x (childf c) ->
         dnode x = c /\ Avoid (v :: stack) x /\ exists val, dval x = Some val) ->
      forall x, In x (node_scan v childf) ->
        dnode x = v /\ Avoid stack x /\ exists val, dval x = Some val.
  Proof.
    intros stack v childf Hnin Hcf x Hx.
    unfold node_scan in Hx.
    pose proof (scan_feasible D dval _ _ _ Hx) as Hfeas.
    apply scan_incl in Hx.
    rewrite (sortby_in_iff D keyleb) in Hx.
    apply cand_list_in_inv in Hx.
    destruct Hx as (e & ch & choice & -> & Hn & Hf).
    assert (Hch : In ch (packings_of v)) by (eapply nth_error_In; eauto).
    apply f2_in_l in Hf.
    split; [reflexivity|]. split; [|exact Hfeas].
    apply Avoid_mk with (ch := ch); [exact Hnin | exact Hn | |].
    - eapply f2_map_r; [exact Hf|].
      intros c x0 [Hin Hc]. exact (proj1 (Hcf ch c x0 Hch Hc Hin)).
    - eapply f2_forall_r; [exact Hf|].
      intros c x0 [Hin Hc].
      exact (proj1 (proj2 (Hcf ch c x0 Hch Hc Hin))).
  Qed.

  Lemma xfull_sound :
    forall fuel stack v,
      ctx fuel stack v ->
      forall x, In x (xfull fuel stack v) ->
        dnode x = v /\ Avoid stack x /\ exists val, dval x = Some val.
  Proof.
    induction fuel as [|f IH]; intros stack v Hctx x Hx.
    - cbn in Hx. destruct Hx.
    - rewrite xfull_S in Hx.
      destruct (inb v stack) eqn:Hin; [destruct Hx|].
      apply inb_false_iff in Hin.
      revert x Hx. apply node_scan_sound; [exact Hin|].
      intros ch c x0 Hch Hc Hx0.
      apply (IH (v :: stack) c); [|exact Hx0].
      apply ctx_child; [exact Hctx | exact Hin |].
      eapply children_bounded; [|exact Hch | exact Hc].
      destruct Hctx as (_ & _ & _ & Hv). exact Hv.
  Qed.

  Lemma xscan_sound :
    forall k fuel stack v,
      ctx fuel stack v ->
      forall x, In x (xscan k fuel stack v) ->
        dnode x = v /\ Avoid stack x /\ exists val, dval x = Some val.
  Proof.
    intros k. induction fuel as [|f IH]; intros stack v Hctx x Hx.
    - cbn in Hx. destruct Hx.
    - rewrite xscan_S in Hx.
      destruct (inb v stack) eqn:Hin; [destruct Hx|].
      apply inb_false_iff in Hin.
      revert x Hx. apply node_scan_sound; [exact Hin|].
      intros ch c x0 Hch Hc Hx0.
      apply In_firstn in Hx0.
      apply (IH (v :: stack) c); [|exact Hx0].
      apply ctx_child; [exact Hctx | exact Hin |].
      eapply children_bounded; [|exact Hch | exact Hc].
      destruct Hctx as (_ & _ & _ & Hv). exact Hv.
  Qed.

  Lemma xcap_sound :
    forall k fuel stack v,
      ctx fuel stack v ->
      forall x, In x (xcap k fuel stack v) ->
        dnode x = v /\ Avoid stack x /\ exists val, dval x = Some val.
  Proof.
    intros k fuel stack v Hctx x Hx.
    unfold xcap in Hx. apply In_firstn in Hx.
    eapply xscan_sound; eauto.
  Qed.

  Lemma xfull_sorted :
    forall fuel stack v, SSorted D keyleb (xfull fuel stack v).
  Proof.
    intros. destruct fuel; cbn; [constructor|].
    destruct (inb v stack); [constructor|].
    unfold node_scan.
    apply scan_sorted.
    apply sortby_ssorted; [exact keyleb_total | exact keyleb_trans].
  Qed.

  Lemma xscan_sorted :
    forall k fuel stack v, SSorted D keyleb (xscan k fuel stack v).
  Proof.
    intros. destruct fuel; cbn; [constructor|].
    destruct (inb v stack); [constructor|].
    unfold node_scan.
    apply scan_sorted.
    apply sortby_ssorted; [exact keyleb_total | exact keyleb_trans].
  Qed.

  Lemma xcap_sorted :
    forall k fuel stack v, SSorted D keyleb (xcap k fuel stack v).
  Proof.
    intros. unfold xcap. apply ssorted_firstn. apply xscan_sorted.
  Qed.

  Lemma xscan_classes_nodup :
    forall k fuel stack v, NoDup (map dcls (xscan k fuel stack v)).
  Proof.
    intros. destruct fuel; cbn; [constructor|].
    destruct (inb v stack); [constructor|].
    apply (scan_classes_nodup D dval).
  Qed.

  Lemma xcap_classes_nodup :
    forall k fuel stack v, NoDup (map dcls (xcap k fuel stack v)).
  Proof.
    intros. unfold xcap.
    rewrite <- firstn_map. apply NoDup_firstn. apply xscan_classes_nodup.
  Qed.

  (* ── The A4 driver lemmas (hypothesis-free). ── *)

  Lemma no_trunc_xcap_eq :
    forall k fuel stack v,
      no_trunc k fuel stack v -> xcap k fuel stack v = xfull fuel stack v.
  Proof.
    intros k. induction fuel as [|f IH]; intros stack v Hnt.
    - unfold xcap. cbn. now destruct k.
    - rewrite no_trunc_S in Hnt. unfold xcap.
      rewrite xscan_S, xfull_S.
      destruct (inb v stack) eqn:Hin.
      + now destruct k.
      + destruct Hnt as [Hlen Hch].
        assert (Heq : node_scan v (fun c => firstn k (xscan k f (v :: stack) c))
                      = node_scan v (fun c => xfull f (v :: stack) c)).
        { apply node_scan_ext. intros ch c Hch' Hc.
          change (firstn k (xscan k f (v :: stack) c))
            with (xcap k f (v :: stack) c).
          apply IH. apply (Hch ch c Hch' Hc). }
        rewrite Heq.
        apply firstn_all2.
        rewrite xscan_S, Hin in Hlen. rewrite Heq in Hlen. exact Hlen.
  Qed.

  (* T2 driver termination witness: any k >= the session's largest full
     list forces the A4 flag OR to be false, so the grow-and-re-extract
     loop of amendment A4(iii) terminates and converges on xfull. *)
  Theorem t2_driver_terminates :
    forall fuel stack v k, maxlen fuel stack v <= k -> no_trunc k fuel stack v.
  Proof.
    induction fuel as [|f IH]; intros stack v k Hk.
    - cbn. exact I.
    - rewrite no_trunc_S. rewrite maxlen_S in Hk.
      destruct (inb v stack) eqn:Hin; [exact I|].
      assert (Hch : forall ch c, In ch (packings_of v) -> In c ch ->
                      no_trunc k f (v :: stack) c).
      { intros ch c Hch Hc. apply IH.
        assert (H1 : maxlen f (v :: stack) c
                     <= fold_right
                          (fun c0 acc2 => Nat.max (maxlen f (v :: stack) c0) acc2)
                          0 ch)
          by (apply fold_max_in; exact Hc).
        assert (H2 : fold_right
                       (fun c0 acc2 => Nat.max (maxlen f (v :: stack) c0) acc2)
                       0 ch
                     <= fold_right
                          (fun ch' acc =>
                             Nat.max
                               (fold_right
                                  (fun c0 acc2 =>
                                     Nat.max (maxlen f (v :: stack) c0) acc2)
                                  0 ch') acc)
                          0 (packings_of v))
          by (apply (fold_max_ch_in
                       (fun ch' =>
                          fold_right
                            (fun c0 acc2 =>
                               Nat.max (maxlen f (v :: stack) c0) acc2)
                            0 ch')); exact Hch).
        lia. }
      split; [|exact Hch].
      assert (Heq : xscan k (S f) stack v = xfull (S f) stack v).
      { rewrite xscan_S, xfull_S, Hin.
        apply node_scan_ext. intros ch c Hch' Hc.
        change (firstn k (xscan k f (v :: stack) c))
          with (xcap k f (v :: stack) c).
        apply no_trunc_xcap_eq. eapply Hch; eauto. }
      rewrite Heq. lia.
  Qed.

  (* Capped-pass soundness (a driver rung that returns a non-empty list
     has witnessed a feasible acyclic-witnessed derivation) — needs no
     dedup-congruence hypothesis. *)
  Theorem t2_capped_pass_sound :
    forall k fuel stack v,
      ctx fuel stack v ->
      xcap k fuel stack v <> [] ->
      exists d val, Avoid stack d /\ dnode d = v /\ dval d = Some val.
  Proof.
    intros k fuel stack v Hctx Hne.
    destruct (xcap k fuel stack v) as [|x rest] eqn:E; [congruence|].
    assert (Hx : In x (xcap k fuel stack v)) by (rewrite E; left; reflexivity).
    destruct (xcap_sound k fuel stack v Hctx x Hx) as (Hn & Hav & (val & Hval)).
    exists x, val. auto.
  Qed.

  (* ══ Observational-dedup soundness (adjudication (3)): fingerprint-
        equal child values are interchangeable for definedness and class
        of the parent action.  Trivial when fp is injective (R-11). ══ *)

  Hypothesis act_class_congruent :
    forall v e vs1 vs2,
      map fp vs1 = map fp vs2 ->
      option_map fp (act v e vs1) = option_map fp (act v e vs2).

  Lemma reps_close :
    forall (childf : nat -> list D) ds vs,
      Forall2 (fun x v => dval x = Some v) ds vs ->
      Forall (fun s => exists r, In r (childf (dnode s))
                                 /\ dnode r = dnode s /\ dcls r = dcls s) ds ->
      exists rs ws,
        Forall2 (fun s r => In r (childf (dnode s))) ds rs
        /\ map dnode rs = map dnode ds
        /\ dvals rs = Some ws
        /\ map fp ws = map fp vs.
  Proof.
    intros childf ds vs Hdv Hw. revert vs Hdv.
    induction Hw as [|s ds' Hs Hw IH]; intros vs Hdv.
    - inversion Hdv; subst. exists [], [].
      split; [constructor|]. split; [reflexivity|].
      split; reflexivity.
    - inversion Hdv as [|? v0 ? vs' Hsv Hdv']; subst.
      destruct Hs as (r & Hrin & Hrn & Hrc).
      destruct (IH _ Hdv') as (rs & ws & H1 & H2 & H3 & H4).
      assert (Hrv : exists w, dval r = Some w /\ fp w = fp v0).
      { unfold dcls, clsf in Hrc. rewrite Hsv in Hrc.
        destruct (dval r) as [w|] eqn:Er; [|discriminate].
        inversion Hrc; subst. eauto. }
      destruct Hrv as (w & Hw' & Hfw).
      exists (r :: rs), (w :: ws).
      split; [constructor; assumption|].
      split; [cbn; rewrite Hrn, H2; reflexivity|].
      split; [cbn; rewrite Hw', H3; reflexivity|].
      cbn. rewrite Hfw, H4. reflexivity.
  Qed.

  (* Representative-composed completeness: every feasible stack-avoiding
     derivation's class is reached by the uncapped extractor. *)
  Lemma xfull_complete :
    forall fuel stack v d val,
      ctx fuel stack v ->
      Avoid stack d -> dnode d = v -> dval d = Some val ->
      exists x, In x (xfull fuel stack v) /\ dcls x = Some (fp val).
  Proof.
    induction fuel as [|f IH]; intros stack v d val Hctx Hav Hn Hv.
    - destruct (ctx_fuel_S _ _ _ Hctx) as (? & Hf). discriminate.
    - destruct d as [v' e ds]. cbn in Hn. subst v'.
      inversion Hav as [? ? ? ? ch Hnin Hnth Hmap Hkids]; subst.
      rewrite xfull_S.
      rewrite (proj2 (inb_false_iff _ _) Hnin).
      rewrite dval_mkD in Hv.
      destruct (dvals ds) as [vs|] eqn:Hdvs; [|discriminate].
      pose proof (dvals_forall2_of _ _ Hdvs) as Hf2.
      assert (Hvnum : v < num_nodes)
        by (destruct Hctx as (_ & _ & _ & Hvn); exact Hvn).
      assert (Hchin : In (map dnode ds) (packings_of v))
        by (eapply nth_error_In; eauto).
      assert (Hctxc : forall s, In s ds -> ctx f (v :: stack) (dnode s)).
      { intros s Hs. apply ctx_child; [exact Hctx | exact Hnin |].
        eapply children_bounded; [exact Hvnum | exact Hchin |].
        apply in_map. exact Hs. }
      assert (Hwit : Forall (fun s => exists r,
          In r (xfull f (v :: stack) (dnode s))
          /\ dnode r = dnode s /\ dcls r = dcls s) ds).
      { rewrite Forall_forall. intros s Hs.
        assert (Hsv : exists w, dval s = Some w).
        { pose proof (f2_forall_l _ _ _ _ _ Hf2) as Hall.
          rewrite Forall_forall in Hall. apply Hall. exact Hs. }
        destruct Hsv as (w & Hw).
        assert (Havs : Avoid (v :: stack) s)
          by (rewrite Forall_forall in Hkids; apply Hkids; exact Hs).
        destruct (IH (v :: stack) (dnode s) s w (Hctxc s Hs) Havs eq_refl Hw)
          as (r & Hr & Hrc).
        exists r. split; [exact Hr|]. split.
        - destruct (xfull_sound f (v :: stack) (dnode s) (Hctxc s Hs) r Hr)
            as (Hrn & _ & _). exact Hrn.
        - rewrite Hrc. unfold dcls, clsf. rewrite Hw. reflexivity. }
      destruct (reps_close _ _ _ Hf2 Hwit) as (rs & ws & Hin2 & Hmap2 & Hdws & Hfpw).
      assert (Hcandin : In (mkD v e rs)
                          (cand_list v (fun c => xfull f (v :: stack) c))).
      { apply cand_list_in with (ch := map dnode ds); [exact Hnth|].
        apply Forall2_map_l_intro. exact Hin2. }
      assert (Hcandval : exists val', act v e ws = Some val' /\ fp val' = fp val).
      { pose proof (act_class_congruent v e ws vs Hfpw) as Hc.
        rewrite Hv in Hc. cbn in Hc.
        destruct (act v e ws) as [val'|] eqn:Ea; cbn in Hc; [|discriminate].
        inversion Hc; subst. eauto. }
      destruct Hcandval as (val' & Hact' & Hfp').
      assert (Hcv : dval (mkD v e rs) = Some val').
      { rewrite dval_mkD, Hdws. exact Hact'. }
      unfold node_scan.
      destruct (scan_complete D dval
                  (sortby D keyleb (cand_list v (fun c => xfull f (v :: stack) c)))
                  [] (mkD v e rs) val') as (y & Hy & Hcy).
      { apply (sortby_in_iff D keyleb). exact Hcandin. }
      { exact Hcv. }
      { cbn. tauto. }
      exists y. split; [exact Hy|].
      unfold dcls. rewrite Hcy, Hfp'. reflexivity.
  Qed.

  (* T2 — feasibility/exhaustion for the modeled on-stack rule: the
     uncapped (Election-mode / driver-limit) root list is empty iff no
     feasible stack-avoiding derivation exists. *)
  Theorem t2_exhaustion_iff :
    forall fuel stack v,
      ctx fuel stack v ->
      (xfull fuel stack v = []
       <-> ~ (exists d val, Avoid stack d /\ dnode d = v /\ dval d = Some val)).
  Proof.
    intros fuel stack v Hctx. split.
    - intros Hempty (d & val & Hav & Hn & Hv).
      destruct (xfull_complete fuel stack v d val Hctx Hav Hn Hv)
        as (x & Hx & _).
      rewrite Hempty in Hx. destruct Hx.
    - intro Hno.
      destruct (xfull fuel stack v) as [|x rest] eqn:E; [reflexivity|].
      exfalso. apply Hno.
      assert (Hx : In x (xfull fuel stack v)) by (rewrite E; left; reflexivity).
      destruct (xfull_sound fuel stack v Hctx x Hx)
        as (Hn & Hav & (val & Hval)).
      exists x, val. auto.
  Qed.

  (* T2, capped-pass empty case: an empty rung with the A4 flag OR false
     soundly reports exhaustion. *)
  Theorem t2_capped_empty_no_trunc :
    forall k fuel stack v,
      ctx fuel stack v ->
      no_trunc k fuel stack v ->
      xcap k fuel stack v = [] ->
      ~ (exists d val, Avoid stack d /\ dnode d = v /\ dval d = Some val).
  Proof.
    intros k fuel stack v Hctx Hnt Hempty.
    apply (t2_exhaustion_iff fuel stack v Hctx).
    rewrite <- (no_trunc_xcap_eq k fuel stack v Hnt). exact Hempty.
  Qed.

  (* T5 — truncation-completeness (amendment A4): if no demanded node's
     flag is set, the delivered root list carries EVERY distinct class of
     the feasible stack-avoiding derivations, within its <= k entries. *)
  Theorem t5_truncation_completeness :
    forall k fuel stack v,
      ctx fuel stack v ->
      no_trunc k fuel stack v ->
      (forall d val,
          Avoid stack d -> dnode d = v -> dval d = Some val ->
          exists x, In x (xcap k fuel stack v) /\ dcls x = Some (fp val))
      /\ length (xcap k fuel stack v) <= k.
  Proof.
    intros k fuel stack v Hctx Hnt. split.
    - intros d val Hav Hn Hv.
      rewrite (no_trunc_xcap_eq k fuel stack v Hnt).
      eapply xfull_complete; eauto.
    - apply firstn_le_len.
  Qed.

  (* ══ Composition monotonicity (Goodman superiority; obstruction (1)).
        Discharged for the Weight key by w_kcompW_mono below. ══ *)

  Hypothesis kcomp_mono :
    forall v e ks1 ks2,
      Forall2 kle ks1 ks2 -> kle (kcomp v e ks1) (kcomp v e ks2).

  Lemma reps_close_key :
    forall (childf : nat -> list D) ds vs,
      Forall2 (fun x v => dval x = Some v) ds vs ->
      Forall (fun s => exists r, In r (childf (dnode s))
                                 /\ dnode r = dnode s /\ dcls r = dcls s
                                 /\ kle (dkey r) (dkey s)) ds ->
      exists rs ws,
        Forall2 (fun s r => In r (childf (dnode s))) ds rs
        /\ map dnode rs = map dnode ds
        /\ dvals rs = Some ws
        /\ map fp ws = map fp vs
        /\ Forall2 kle (dkeys rs) (dkeys ds).
  Proof.
    intros childf ds vs Hdv Hw. revert vs Hdv.
    induction Hw as [|s ds' Hs Hw IH]; intros vs Hdv.
    - inversion Hdv; subst. exists [], [].
      split; [constructor|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity | constructor].
    - inversion Hdv as [|? v0 ? vs' Hsv Hdv']; subst.
      destruct Hs as (r & Hrin & Hrn & Hrc & Hrk).
      destruct (IH _ Hdv') as (rs & ws & H1 & H2 & H3 & H4 & H5).
      assert (Hrv : exists w, dval r = Some w /\ fp w = fp v0).
      { unfold dcls, clsf in Hrc. rewrite Hsv in Hrc.
        destruct (dval r) as [w|] eqn:Er; [|discriminate].
        inversion Hrc; subst. eauto. }
      destruct Hrv as (w & Hw' & Hfw).
      exists (r :: rs), (w :: ws).
      split; [constructor; assumption|].
      split; [cbn; rewrite Hrn, H2; reflexivity|].
      split; [cbn; rewrite Hw', H3; reflexivity|].
      split; [cbn; rewrite Hfw, H4; reflexivity|].
      cbn. constructor; assumption.
  Qed.

  (* Representative domination: every feasible stack-avoiding derivation
     is class-matched by an extractor entry with a key <= its key — the
     exchange argument at the heart of T1/T3. *)
  Lemma xfull_dominates :
    forall fuel stack v d val,
      ctx fuel stack v ->
      Avoid stack d -> dnode d = v -> dval d = Some val ->
      exists x, In x (xfull fuel stack v)
                /\ dcls x = Some (fp val) /\ kle (dkey x) (dkey d).
  Proof.
    induction fuel as [|f IH]; intros stack v d val Hctx Hav Hn Hv.
    - destruct (ctx_fuel_S _ _ _ Hctx) as (? & Hf). discriminate.
    - destruct d as [v' e ds]. cbn in Hn. subst v'.
      inversion Hav as [? ? ? ? ch Hnin Hnth Hmap Hkids]; subst.
      rewrite xfull_S.
      rewrite (proj2 (inb_false_iff _ _) Hnin).
      rewrite dval_mkD in Hv.
      destruct (dvals ds) as [vs|] eqn:Hdvs; [|discriminate].
      pose proof (dvals_forall2_of _ _ Hdvs) as Hf2.
      assert (Hvnum : v < num_nodes)
        by (destruct Hctx as (_ & _ & _ & Hvn); exact Hvn).
      assert (Hchin : In (map dnode ds) (packings_of v))
        by (eapply nth_error_In; eauto).
      assert (Hctxc : forall s, In s ds -> ctx f (v :: stack) (dnode s)).
      { intros s Hs. apply ctx_child; [exact Hctx | exact Hnin |].
        eapply children_bounded; [exact Hvnum | exact Hchin |].
        apply in_map. exact Hs. }
      assert (Hwit : Forall (fun s => exists r,
          In r (xfull f (v :: stack) (dnode s))
          /\ dnode r = dnode s /\ dcls r = dcls s
          /\ kle (dkey r) (dkey s)) ds).
      { rewrite Forall_forall. intros s Hs.
        assert (Hsv : exists w, dval s = Some w).
        { pose proof (f2_forall_l _ _ _ _ _ Hf2) as Hall.
          rewrite Forall_forall in Hall. apply Hall. exact Hs. }
        destruct Hsv as (w & Hw).
        assert (Havs : Avoid (v :: stack) s)
          by (rewrite Forall_forall in Hkids; apply Hkids; exact Hs).
        destruct (IH (v :: stack) (dnode s) s w (Hctxc s Hs) Havs eq_refl Hw)
          as (r & Hr & Hrc & Hrk).
        exists r. split; [exact Hr|]. split.
        - destruct (xfull_sound f (v :: stack) (dnode s) (Hctxc s Hs) r Hr)
            as (Hrn & _ & _). exact Hrn.
        - split; [|exact Hrk].
          rewrite Hrc. unfold dcls, clsf. rewrite Hw. reflexivity. }
      destruct (reps_close_key _ _ _ Hf2 Hwit)
        as (rs & ws & Hin2 & Hmap2 & Hdws & Hfpw & Hkeys).
      assert (Hcandin : In (mkD v e rs)
                          (cand_list v (fun c => xfull f (v :: stack) c))).
      { apply cand_list_in with (ch := map dnode ds); [exact Hnth|].
        apply Forall2_map_l_intro. exact Hin2. }
      assert (Hcandval : exists val', act v e ws = Some val' /\ fp val' = fp val).
      { pose proof (act_class_congruent v e ws vs Hfpw) as Hc.
        rewrite Hv in Hc. cbn in Hc.
        destruct (act v e ws) as [val'|] eqn:Ea; cbn in Hc; [|discriminate].
        inversion Hc; subst. eauto. }
      destruct Hcandval as (val' & Hact' & Hfp').
      assert (Hcv : dval (mkD v e rs) = Some val').
      { rewrite dval_mkD, Hdws. exact Hact'. }
      assert (Hck : kle (dkey (mkD v e rs)) (dkey (mkD v e ds))).
      { rewrite !dkey_mkD. apply kcomp_mono. exact Hkeys. }
      unfold node_scan.
      set (cs := sortby D keyleb
                   (cand_list v (fun c => xfull f (v :: stack) c))).
      destruct (scan_complete D dval cs [] (mkD v e rs) val') as (y & Hy & Hcy).
      { apply (sortby_in_iff D keyleb). exact Hcandin. }
      { exact Hcv. }
      { cbn. tauto. }
      exists y. split; [exact Hy|]. split.
      + unfold dcls. rewrite Hcy, Hfp'. reflexivity.
      + assert (Hyx : keyleb y (mkD v e rs) = true).
        { eapply (scan_min D dval keyleb keyleb_total cs []).
          - apply sortby_ssorted; [exact keyleb_total | exact keyleb_trans].
          - exact Hy.
          - apply (sortby_in_iff D keyleb). exact Hcandin.
          - rewrite Hcy. unfold clsf. rewrite Hcv. reflexivity. }
        unfold keyleb in Hyx.
        eapply kle_trans; [exact Hyx | exact Hck].
  Qed.

  (* ══ All-candidates-feasible regime (spec §3.1's zero-tabu green
        corpus; obstruction (2)): actions total.  Under it, domination
        holds without any dedup-congruence hypothesis. ══ *)

  Hypothesis act_total : forall v e vs, act v e vs <> None.

  Lemma wf_dval_some : forall d, Wf d -> exists val, dval d = Some val.
  Proof.
    intro d; induction d as [v e ds IH] using D_ind_strong; intro Hwf.
    inversion Hwf as [? ? ? ch Hnth Hmap Hkids]; subst.
    assert (Hall : Forall (fun x => exists w, dval x = Some w) ds).
    { rewrite Forall_forall in *. intros x Hx. apply IH; auto. }
    destruct (dvals_of_forall _ Hall) as (ws & Hws & _).
    rewrite dval_mkD, Hws.
    destruct (act v e ws) as [w|] eqn:Ea; [eauto|].
    exfalso. exact (act_total v e ws Ea).
  Qed.

  Lemma xfull_dominates_total :
    forall fuel stack v d,
      ctx fuel stack v ->
      Avoid stack d -> dnode d = v ->
      exists x, In x (xfull fuel stack v) /\ kle (dkey x) (dkey d).
  Proof.
    induction fuel as [|f IH]; intros stack v d Hctx Hav Hn.
    - destruct (ctx_fuel_S _ _ _ Hctx) as (? & Hf). discriminate.
    - destruct d as [v' e ds]. cbn in Hn. subst v'.
      inversion Hav as [? ? ? ? ch Hnin Hnth Hmap Hkids]; subst.
      rewrite xfull_S.
      rewrite (proj2 (inb_false_iff _ _) Hnin).
      assert (Hvnum : v < num_nodes)
        by (destruct Hctx as (_ & _ & _ & Hvn); exact Hvn).
      assert (Hchin : In (map dnode ds) (packings_of v))
        by (eapply nth_error_In; eauto).
      assert (Hctxc : forall s, In s ds -> ctx f (v :: stack) (dnode s)).
      { intros s Hs. apply ctx_child; [exact Hctx | exact Hnin |].
        eapply children_bounded; [exact Hvnum | exact Hchin |].
        apply in_map. exact Hs. }
      assert (Hwit : Forall (fun s => exists r,
          In r (xfull f (v :: stack) (dnode s))
          /\ dnode r = dnode s /\ (exists w, dval r = Some w)
          /\ kle (dkey r) (dkey s)) ds).
      { rewrite Forall_forall. intros s Hs.
        assert (Havs : Avoid (v :: stack) s)
          by (rewrite Forall_forall in Hkids; apply Hkids; exact Hs).
        destruct (IH (v :: stack) (dnode s) s (Hctxc s Hs) Havs eq_refl)
          as (r & Hr & Hrk).
        destruct (xfull_sound f (v :: stack) (dnode s) (Hctxc s Hs) r Hr)
          as (Hrn & _ & Hrf).
        exists r. auto. }
      apply forall_ex_list in Hwit. destruct Hwit as (rs & Hrs).
      assert (Hin2 : Forall2 (fun s r => In r (xfull f (v :: stack) (dnode s))) ds rs)
        by (eapply f2_impl; [|exact Hrs]; cbn; tauto).
      assert (Hmap2 : map dnode rs = map dnode ds).
      { clear - Hrs. induction Hrs as [|s r ds' rs' Hsr Hrs' IHm]; cbn;
          [reflexivity|].
        destruct Hsr as (_ & Hrn & _). rewrite Hrn. f_equal. exact IHm. }
      assert (Hfeas : Forall (fun r => exists w, dval r = Some w) rs)
        by (eapply f2_forall_r; [exact Hrs|]; cbn; tauto).
      destruct (dvals_of_forall _ Hfeas) as (ws & Hws & _).
      assert (Hkeys : Forall2 kle (dkeys rs) (dkeys ds)).
      { clear - Hrs. induction Hrs as [|s r ds' rs' Hsr Hrs' IHk]; cbn;
          [constructor|].
        destruct Hsr as (_ & _ & _ & Hk). constructor; assumption. }
      assert (Hcandin : In (mkD v e rs)
                          (cand_list v (fun c => xfull f (v :: stack) c))).
      { apply cand_list_in with (ch := map dnode ds); [exact Hnth|].
        apply Forall2_map_l_intro. exact Hin2. }
      assert (Hcv : exists val', dval (mkD v e rs) = Some val').
      { rewrite dval_mkD, Hws.
        destruct (act v e ws) as [w|] eqn:Ea; [eauto|].
        exfalso. exact (act_total v e ws Ea). }
      destruct Hcv as (val' & Hcv).
      assert (Hck : kle (dkey (mkD v e rs)) (dkey (mkD v e ds))).
      { rewrite !dkey_mkD. apply kcomp_mono. exact Hkeys. }
      unfold node_scan.
      set (cs := sortby D keyleb
                   (cand_list v (fun c => xfull f (v :: stack) c))).
      destruct (scan_complete D dval cs [] (mkD v e rs) val') as (y & Hy & Hcy).
      { apply (sortby_in_iff D keyleb). exact Hcandin. }
      { exact Hcv. }
      { cbn. tauto. }
      exists y. split; [exact Hy|].
      assert (Hyx : keyleb y (mkD v e rs) = true).
      { eapply (scan_min D dval keyleb keyleb_total cs []).
        - apply sortby_ssorted; [exact keyleb_total | exact keyleb_trans].
        - exact Hy.
        - apply (sortby_in_iff D keyleb). exact Hcandin.
        - rewrite Hcy. unfold clsf. rewrite Hcv. reflexivity. }
      unfold keyleb in Hyx.
      eapply kle_trans; [exact Hyx | exact Hck].
  Qed.

  (* ══ Class-injective composition at a slot, others fixed (spec §3.3;
        contrapositive form on values). ══ *)

  Hypothesis act_slot_injective :
    forall v e pre post a1 a2 r1 r2,
      act v e (pre ++ a1 :: post) = Some r1 ->
      act v e (pre ++ a2 :: post) = Some r2 ->
      fp r1 = fp r2 -> fp a1 = fp a2.

  (* From one truncated slot, k pairwise-distinct-class dominating entries
     of the parent scan (the exchange family that forces hidden classes
     out of the top-k). *)
  Lemma dominators_from_slot :
    forall (v e : nat) (ws1 ws2 : list Val) (Lscan : list D) (Bd : D)
           (Lstar : list D),
      NoDup (map dcls Lstar) ->
      Forall (fun r => exists wr valr y,
          dval r = Some wr
          /\ act v e (ws1 ++ wr :: ws2) = Some valr
          /\ In y Lscan /\ dcls y = Some (fp valr)
          /\ keyleb y Bd = true) Lstar ->
      exists ys,
        length ys = length Lstar /\ NoDup ys
        /\ (forall y, In y ys -> In y Lscan)
        /\ Forall (fun y => keyleb y Bd = true) ys
        /\ (forall y, In y ys -> exists r wr valr,
              In r Lstar /\ dval r = Some wr
              /\ act v e (ws1 ++ wr :: ws2) = Some valr
              /\ dcls y = Some (fp valr)).
  Proof.
    intros v e ws1 ws2 Lscan Bd Lstar.
    induction Lstar as [|r rest IH]; intros Hnd Hall.
    - exists []. split; [reflexivity|]. split; [constructor|].
      split; [intros y []|]. split; [constructor | intros y []].
    - inversion Hall as [|? ? Hr Hrest]; subst.
      cbn in Hnd. inversion Hnd as [|? ? Hnin Hnd']; subst.
      destruct (IH Hnd' Hrest) as (ys & Hlen & Hndys & Hincl & Hkeys & Hys).
      destruct Hr as (wr & valr & y & Hdw & Hact & Hyin & Hycls & Hykey).
      exists (y :: ys).
      split; [cbn; rewrite Hlen; reflexivity|].
      split.
      { constructor; [|exact Hndys].
        intro Hin.
        destruct (Hys y Hin) as (r' & wr' & valr' & Hr'in & Hdw' & Hact' & Hycls').
        assert (Hfp : fp valr = fp valr').
        { rewrite Hycls in Hycls'. inversion Hycls'. reflexivity. }
        pose proof (act_slot_injective v e ws1 ws2 wr wr' valr valr'
                      Hact Hact' Hfp) as Hfpw.
        apply Hnin.
        assert (Hc : dcls r = dcls r').
        { unfold dcls, clsf. rewrite Hdw, Hdw', Hfpw. reflexivity. }
        rewrite Hc. apply in_map. exact Hr'in. }
      split.
      { intros z Hz. destruct Hz as [<- | Hz];
          [exact Hyin | apply Hincl; exact Hz]. }
      split.
      { constructor; [exact Hykey | exact Hkeys]. }
      intros z Hz. destruct Hz as [<- | Hz].
      + exists r, wr, valr. split; [left; reflexivity|]. auto.
      + destruct (Hys z Hz) as (r' & wr' & valr' & H1 & H2 & H3 & H4).
        exists r', wr', valr'. split; [right; exact H1|]. auto.
  Qed.

  (* ── T3: the k-exactness invariant. ── *)

  Lemma t3_invariant :
    forall k fuel stack v,
      ctx fuel stack v ->
      (forall x valx d val,
          In x (xcap k fuel stack v) -> dval x = Some valx ->
          Avoid stack d -> dnode d = v -> dval d = Some val ->
          fp valx = fp val ->
          kle (dkey x) (dkey d))
      /\ (forall d val,
          Avoid stack d -> dnode d = v -> dval d = Some val ->
          (exists x, In x (xcap k fuel stack v) /\ dcls x = Some (fp val))
          \/ (length (xcap k fuel stack v) = k
              /\ forall x, In x (xcap k fuel stack v) -> kle (dkey x) (dkey d))).
  Proof.
    intros k. destruct k as [|k0].
    { intros fuel stack v Hctx. split.
      - intros x valx d val Hx. unfold xcap in Hx. cbn in Hx. destruct Hx.
      - intros d val _ _ _. right. split.
        + unfold xcap. cbn. reflexivity.
        + intros x Hx. unfold xcap in Hx. cbn in Hx. destruct Hx. }
    induction fuel as [|f IH]; intros stack v Hctx.
    { destruct (ctx_fuel_S _ _ _ Hctx) as (? & Hf). discriminate. }
    (* The shared core: for every feasible stack-avoiding derivation d of
       v, EITHER a same-class scan entry with key <= dkey d exists, OR the
       delivered list is full with every entry key <= dkey d. *)
    assert (CORE : forall d val,
        Avoid stack d -> dnode d = v -> dval d = Some val ->
        (exists y, In y (xscan (S k0) (S f) stack v)
                   /\ dcls y = Some (fp val) /\ kle (dkey y) (dkey d))
        \/ (S k0 <= length (xscan (S k0) (S f) stack v)
            /\ forall x, In x (xcap (S k0) (S f) stack v) ->
                 kle (dkey x) (dkey d))).
    { intros d val Hav Hn Hv.
      destruct d as [v' e ds]. cbn in Hn. subst v'.
      inversion Hav as [? ? ? ? ch Hnin Hnth Hmap Hkids]; subst.
      rewrite dval_mkD in Hv.
      destruct (dvals ds) as [vs|] eqn:Hdvs; [|discriminate].
      pose proof (dvals_forall2_of _ _ Hdvs) as Hf2.
      assert (Hvnum : v < num_nodes)
        by (destruct Hctx as (_ & _ & _ & Hvn); exact Hvn).
      assert (Hchin : In (map dnode ds) (packings_of v))
        by (eapply nth_error_In; eauto).
      assert (Hctxc : forall s, In s ds -> ctx f (v :: stack) (dnode s)).
      { intros s Hs. apply ctx_child; [exact Hctx | exact Hnin |].
        eapply children_bounded; [exact Hvnum | exact Hchin |].
        apply in_map. exact Hs. }
      (* xscan at v, unfolded. *)
      set (childf := fun c => xcap (S k0) f (v :: stack) c).
      assert (Hxs : xscan (S k0) (S f) stack v = node_scan v childf).
      { rewrite xscan_S. rewrite (proj2 (inb_false_iff _ _) Hnin).
        reflexivity. }
      assert (Hsorted : SSorted D keyleb (node_scan v childf)).
      { rewrite <- Hxs. apply xscan_sorted. }
      (* Per-slot dichotomy from the fuel IH. *)
      assert (Hslots : Forall (fun s =>
          (exists r, In r (childf (dnode s)) /\ dnode r = dnode s
                     /\ dcls r = dcls s /\ kle (dkey r) (dkey s))
          \/ (length (childf (dnode s)) = S k0
              /\ forall r, In r (childf (dnode s)) -> kle (dkey r) (dkey s)))
          ds).
      { rewrite Forall_forall. intros s Hs.
        assert (Hsv : exists w, dval s = Some w).
        { pose proof (f2_forall_l _ _ _ _ _ Hf2) as Hall.
          rewrite Forall_forall in Hall. apply Hall. exact Hs. }
        destruct Hsv as (w & Hw).
        assert (Havs : Avoid (v :: stack) s)
          by (rewrite Forall_forall in Hkids; apply Hkids; exact Hs).
        destruct (IH (v :: stack) (dnode s) (Hctxc s Hs)) as (IH4 & IH5).
        destruct (IH5 s w Havs eq_refl Hw) as [(r & Hr & Hrc) | (Hfull & Hdom)].
        - left.
          destruct (xcap_sound (S k0) f (v :: stack) (dnode s)
                      (Hctxc s Hs) r Hr) as (Hrn & _ & (wr & Hwr)).
          exists r. split; [exact Hr|]. split; [exact Hrn|].
          split.
          + rewrite Hrc. unfold dcls, clsf. rewrite Hw. reflexivity.
          + eapply IH4; [exact Hr | exact Hwr | exact Havs | reflexivity
                        | exact Hw |].
            unfold dcls, clsf in Hrc. rewrite Hwr in Hrc.
            inversion Hrc. reflexivity.
        - right. split; [exact Hfull | exact Hdom]. }
      apply forall_or_split in Hslots.
      destruct Hslots as [Hallslots | (ds1 & sstar & ds2 & Hsplit & Hqstar)].
      + (* CASE ALL-DELIVERED: the fully representative-composed candidate. *)
        assert (Hwit : Forall (fun s => exists r,
            In r (childf (dnode s)) /\ dnode r = dnode s
            /\ dcls r = dcls s /\ kle (dkey r) (dkey s)) ds)
          by exact Hallslots.
        destruct (reps_close_key _ _ _ Hf2 Hwit)
          as (rs & ws & Hin2 & Hmap2 & Hdws & Hfpw & Hkeys).
        assert (Hcandin : In (mkD v e rs) (cand_list v childf)).
        { apply cand_list_in with (ch := map dnode ds); [exact Hnth|].
          apply Forall2_map_l_intro. exact Hin2. }
        assert (Hcandval : exists val', act v e ws = Some val'
                                        /\ fp val' = fp val).
        { pose proof (act_class_congruent v e ws vs Hfpw) as Hc.
          rewrite Hv in Hc. cbn in Hc.
          destruct (act v e ws) as [val'|] eqn:Ea; cbn in Hc; [|discriminate].
          inversion Hc; subst. eauto. }
        destruct Hcandval as (val' & Hact' & Hfp').
        assert (Hcv : dval (mkD v e rs) = Some val').
        { rewrite dval_mkD, Hdws. exact Hact'. }
        assert (Hck : kle (dkey (mkD v e rs)) (dkey (mkD v e ds))).
        { rewrite !dkey_mkD. apply kcomp_mono. exact Hkeys. }
        left.
        rewrite Hxs. unfold node_scan.
        set (cs := sortby D keyleb (cand_list v childf)).
        destruct (scan_complete D dval cs [] (mkD v e rs) val')
          as (y & Hy & Hcy).
        { apply (sortby_in_iff D keyleb). exact Hcandin. }
        { exact Hcv. }
        { cbn. tauto. }
        exists y. split; [exact Hy|]. split.
        * unfold dcls. rewrite Hcy, Hfp'. reflexivity.
        * assert (Hyx : keyleb y (mkD v e rs) = true).
          { eapply (scan_min D dval keyleb keyleb_total cs []).
            - apply sortby_ssorted; [exact keyleb_total | exact keyleb_trans].
            - exact Hy.
            - apply (sortby_in_iff D keyleb). exact Hcandin.
            - rewrite Hcy. unfold clsf. rewrite Hcv. reflexivity. }
          unfold keyleb in Hyx.
          eapply kle_trans; [exact Hyx | exact Hck].
      + (* CASE TRUNCATED SLOT: the k-dominator exchange family. *)
        right.
        subst ds.
        (* Sub-derivation feasibility per part. *)
        pose proof Hdvs as Hdvs'.
        apply dvals_app_split in Hdvs'.
        destruct Hdvs' as (vs1 & vsr & Hvs1 & Hvsr & Hvssplit).
        cbn in Hvsr.
        destruct (dval sstar) as [vstar|] eqn:Hvstar; [|discriminate].
        destruct (dvals ds2) as [vs2|] eqn:Hvs2; [|discriminate].
        inversion Hvsr; subst vsr.
        (* Slot-star child list. *)
        destruct Hqstar as (Hfullstar & Hdomstar).
        set (Lstar := childf (dnode sstar)).
        (* Uniform witnesses for the OTHER slots (delivered rep or head of
           a full dominated list — both give In + dnode + feasible + kle). *)
        assert (Hother : forall s, In s (ds1 ++ ds2) ->
            Avoid (v :: stack) s ->
            (exists r, In r (childf (dnode s)) /\ dnode r = dnode s
                       /\ dcls r = dcls s /\ kle (dkey r) (dkey s))
            \/ (length (childf (dnode s)) = S k0
                /\ forall r, In r (childf (dnode s)) -> kle (dkey r) (dkey s)) ->
            exists w, In w (childf (dnode s)) /\ dnode w = dnode s
                      /\ (exists vw, dval w = Some vw)
                      /\ kle (dkey w) (dkey s)).
        { intros s Hsin Havs Hdisj.
          assert (Hctxs : ctx f (v :: stack) (dnode s)).
          { apply Hctxc. apply in_app_iff in Hsin.
            apply in_app_iff. destruct Hsin as [Hl | Hr];
              [left; exact Hl | right; right; exact Hr]. }
          destruct Hdisj as [(r & Hr & Hrn & Hrc & Hrk) | (Hfull & Hdom)].
          - exists r. split; [exact Hr|]. split; [exact Hrn|]. split; [|exact Hrk].
            destruct (xcap_sound (S k0) f (v :: stack) (dnode s) Hctxs r Hr)
              as (_ & _ & Hf'). exact Hf'.
          - destruct (childf (dnode s)) as [|w rest] eqn:EL;
              [cbn in Hfull; discriminate|].
            assert (Hw : In w (childf (dnode s)))
              by (rewrite EL; left; reflexivity).
            destruct (xcap_sound (S k0) f (v :: stack) (dnode s) Hctxs w Hw)
              as (Hwn & _ & Hwf).
            exists w. split; [left; reflexivity|]. split; [exact Hwn|].
            split; [exact Hwf | apply Hdom; left; reflexivity]. }
        (* Build the fixed witness lists for ds1 / ds2. *)
        assert (Hkids1 : Forall (Avoid (v :: stack)) ds1
                /\ Avoid (v :: stack) sstar
                /\ Forall (Avoid (v :: stack)) ds2).
        { apply Forall_app in Hkids. destruct Hkids as [H1 H2].
          inversion H2; subst. auto. }
        destruct Hkids1 as (Hkds1 & Havstar & Hkds2).
        assert (Hd1wit : exists w1s,
            Forall2 (fun s w => In w (childf (dnode s)) /\ dnode w = dnode s
                                /\ (exists vw, dval w = Some vw)
                                /\ kle (dkey w) (dkey s)) ds1 w1s).
        { apply forall_ex_list. rewrite Forall_forall. intros s Hs.
          assert (Hsv : exists w, dval s = Some w).
          { pose proof (dvals_forall2_of _ _ Hvs1) as Hf1.
            pose proof (f2_forall_l _ _ _ _ _ Hf1) as Hall.
            rewrite Forall_forall in Hall. apply Hall. exact Hs. }
          destruct Hsv as (w0 & Hw0).
          assert (Havs : Avoid (v :: stack) s)
            by (rewrite Forall_forall in Hkds1; apply Hkds1; exact Hs).
          apply (Hother s); [apply in_app_iff; left; exact Hs | exact Havs |].
          destruct (IH (v :: stack) (dnode s)) as (IH4 & IH5).
          { apply Hctxc. apply in_app_iff. left. exact Hs. }
          destruct (IH5 s w0 Havs eq_refl Hw0)
            as [(r & Hr & Hrc) | (Hfull & Hdom)].
          - left.
            destruct (xcap_sound (S k0) f (v :: stack) (dnode s)
                        (Hctxc s ltac:(apply in_app_iff; left; exact Hs)) r Hr)
              as (Hrn & _ & (wr & Hwr)).
            exists r. split; [exact Hr|]. split; [exact Hrn|]. split.
            + rewrite Hrc. unfold dcls, clsf. rewrite Hw0. reflexivity.
            + eapply IH4; [exact Hr | exact Hwr | exact Havs | reflexivity
                          | exact Hw0 |].
              unfold dcls, clsf in Hrc. rewrite Hwr in Hrc.
              inversion Hrc. reflexivity.
          - right. auto. }
        destruct Hd1wit as (w1s & Hw1s).
        assert (Hd2wit : exists w2s,
            Forall2 (fun s w => In w (childf (dnode s)) /\ dnode w = dnode s
                                /\ (exists vw, dval w = Some vw)
                                /\ kle (dkey w) (dkey s)) ds2 w2s).
        { apply forall_ex_list. rewrite Forall_forall. intros s Hs.
          assert (Hsv : exists w, dval s = Some w).
          { pose proof (dvals_forall2_of _ _ Hvs2) as Hf1.
            pose proof (f2_forall_l _ _ _ _ _ Hf1) as Hall.
            rewrite Forall_forall in Hall. apply Hall. exact Hs. }
          destruct Hsv as (w0 & Hw0).
          assert (Havs : Avoid (v :: stack) s)
            by (rewrite Forall_forall in Hkds2; apply Hkds2; exact Hs).
          apply (Hother s); [apply in_app_iff; right; exact Hs | exact Havs |].
          destruct (IH (v :: stack) (dnode s)) as (IH4 & IH5).
          { apply Hctxc. apply in_app_iff. right. right. exact Hs. }
          destruct (IH5 s w0 Havs eq_refl Hw0)
            as [(r & Hr & Hrc) | (Hfull & Hdom)].
          - left.
            destruct (xcap_sound (S k0) f (v :: stack) (dnode s)
                        (Hctxc s ltac:(apply in_app_iff; right; right; exact Hs))
                        r Hr)
              as (Hrn & _ & (wr & Hwr)).
            exists r. split; [exact Hr|]. split; [exact Hrn|]. split.
            + rewrite Hrc. unfold dcls, clsf. rewrite Hw0. reflexivity.
            + eapply IH4; [exact Hr | exact Hwr | exact Havs | reflexivity
                          | exact Hw0 |].
              unfold dcls, clsf in Hrc. rewrite Hwr in Hrc.
              inversion Hrc. reflexivity.
          - right. auto. }
        destruct Hd2wit as (w2s & Hw2s).
        (* Fixed value lists for the witness slots. *)
        assert (Hw1feas : Forall (fun w => exists vw, dval w = Some vw) w1s)
          by (eapply f2_forall_r; [exact Hw1s|]; cbn; tauto).
        assert (Hw2feas : Forall (fun w => exists vw, dval w = Some vw) w2s)
          by (eapply f2_forall_r; [exact Hw2s|]; cbn; tauto).
        destruct (dvals_of_forall _ Hw1feas) as (ws1 & Hws1 & _).
        destruct (dvals_of_forall _ Hw2feas) as (ws2 & Hws2 & _).
        (* The per-r exchange candidates and their scan entries. *)
        assert (Hstar_sound : forall r, In r Lstar ->
            dnode r = dnode sstar /\ (exists wr, dval r = Some wr)).
        { intros r Hr.
          assert (Hctxs : ctx f (v :: stack) (dnode sstar)).
          { apply Hctxc. apply in_app_iff. right. left. reflexivity. }
          destruct (xcap_sound (S k0) f (v :: stack) (dnode sstar) Hctxs r Hr)
            as (Hrn & _ & Hrf). auto. }
        assert (Hchsplit : map dnode (ds1 ++ sstar :: ds2)
                           = map dnode ds1 ++ dnode sstar :: map dnode ds2).
        { rewrite map_app. reflexivity. }
        assert (Hcand_r : forall r, In r Lstar ->
            exists wr valr,
              dval r = Some wr
              /\ act v e (ws1 ++ wr :: ws2) = Some valr
              /\ In (mkD v e (w1s ++ r :: w2s)) (cand_list v childf)
              /\ dval (mkD v e (w1s ++ r :: w2s)) = Some valr
              /\ kle (dkey (mkD v e (w1s ++ r :: w2s)))
                     (dkey (mkD v e (ds1 ++ sstar :: ds2)))).
        { intros r Hr.
          destruct (Hstar_sound r Hr) as (Hrn & (wr & Hwr)).
          assert (Hdvcand : dvals (w1s ++ r :: w2s) = Some (ws1 ++ wr :: ws2)).
          { apply dvals_app_some; [exact Hws1|].
            cbn. rewrite Hwr, Hws2. reflexivity. }
          assert (Hactr : exists valr, act v e (ws1 ++ wr :: ws2) = Some valr).
          { destruct (act v e (ws1 ++ wr :: ws2)) as [w|] eqn:Ea; [eauto|].
            exfalso. exact (act_total v e (ws1 ++ wr :: ws2) Ea). }
          destruct Hactr as (valr & Hactr).
          exists wr, valr.
          split; [exact Hwr|]. split; [exact Hactr|].
          split.
          { apply cand_list_in with (ch := map dnode (ds1 ++ sstar :: ds2));
              [exact Hnth|].
            rewrite Hchsplit.
            apply f2_app.
            - apply Forall2_map_l_intro.
              eapply f2_impl; [|exact Hw1s]. cbn. tauto.
            - constructor.
              + exact Hr.
              + apply Forall2_map_l_intro.
                eapply f2_impl; [|exact Hw2s]. cbn. tauto. }
          split.
          { rewrite dval_mkD, Hdvcand. exact Hactr. }
          { rewrite !dkey_mkD. apply kcomp_mono.
            rewrite !dkeys_app. cbn.
            apply f2_app.
            - clear - Hw1s. induction Hw1s as [|s w l1 l2 Hsw H IHk]; cbn;
                [constructor|].
              destruct Hsw as (_ & _ & _ & Hk).
              constructor; assumption.
            - constructor.
              + apply Hdomstar. exact Hr.
              + clear - Hw2s. induction Hw2s as [|s w l1 l2 Hsw H IHk]; cbn;
                  [constructor|].
                destruct Hsw as (_ & _ & _ & Hk).
                constructor; assumption. } }
        (* Scan entries per r. *)
        assert (Hentry_r : Forall (fun r => exists wr valr y,
            dval r = Some wr
            /\ act v e (ws1 ++ wr :: ws2) = Some valr
            /\ In y (node_scan v childf) /\ dcls y = Some (fp valr)
            /\ keyleb y (mkD v e (ds1 ++ sstar :: ds2)) = true) Lstar).
        { rewrite Forall_forall. intros r Hr.
          destruct (Hcand_r r Hr)
            as (wr & valr & Hwr & Hactr & Hcin & Hcval & Hckey).
          unfold node_scan.
          set (cs := sortby D keyleb (cand_list v childf)).
          destruct (scan_complete D dval cs [] (mkD v e (w1s ++ r :: w2s)) valr)
            as (y & Hy & Hcy).
          { apply (sortby_in_iff D keyleb). exact Hcin. }
          { exact Hcval. }
          { cbn. tauto. }
          exists wr, valr, y.
          split; [exact Hwr|]. split; [exact Hactr|].
          split; [exact Hy|]. split.
          { unfold dcls. exact Hcy. }
          assert (Hyx : keyleb y (mkD v e (w1s ++ r :: w2s)) = true).
          { eapply (scan_min D dval keyleb keyleb_total cs []).
            - apply sortby_ssorted; [exact keyleb_total | exact keyleb_trans].
            - exact Hy.
            - apply (sortby_in_iff D keyleb). exact Hcin.
            - rewrite Hcy. unfold clsf. rewrite Hcval. reflexivity. }
          unfold keyleb in *.
          eapply kleb_trans; [exact Hyx | exact Hckey]. }
        (* The dominator family. *)
        assert (Hndstar : NoDup (map dcls Lstar))
          by apply xcap_classes_nodup.
        destruct (dominators_from_slot v e ws1 ws2 (node_scan v childf)
                    (mkD v e (ds1 ++ sstar :: ds2)) Lstar Hndstar Hentry_r)
          as (ys & Hyslen & Hysnd & Hysin & Hyskeys & _).
        assert (Hyslen' : length ys = S k0).
        { rewrite Hyslen. exact Hfullstar. }
        (* Count: at least S k0 sorted-scan elements are <= dkey d. *)
        assert (Hcount : S k0 <=
            length (filter
                      (fun y => keyleb y (mkD v e (ds1 ++ sstar :: ds2)))
                      (node_scan v childf))).
        { rewrite <- Hyslen'.
          apply NoDup_incl_length; [exact Hysnd|].
          intros y Hy. apply filter_In.
          split; [apply Hysin; exact Hy|].
          rewrite Forall_forall in Hyskeys. apply Hyskeys. exact Hy. }
        split.
        * (* length (xscan ...) >= S k0 *)
          rewrite Hxs.
          etransitivity; [exact Hcount|]. apply flt_len_le.
        * (* every delivered entry is dominated *)
          intros x Hx.
          assert (Hxk : keyleb x (mkD v e (ds1 ++ sstar :: ds2)) = true).
          { eapply (ssorted_count_firstn D keyleb keyleb_total keyleb_trans
                      (node_scan v childf)
                      (mkD v e (ds1 ++ sstar :: ds2)) (S k0) x).
            - exact Hsorted.
            - exact Hcount.
            - unfold xcap in Hx. rewrite Hxs in Hx. exact Hx. }
          unfold keyleb in Hxk. exact Hxk. }
    (* Assemble (4) and (5) from CORE. *)
    assert (Hxs : xcap (S k0) (S f) stack v
                  = firstn (S k0) (xscan (S k0) (S f) stack v))
      by reflexivity.
    split.
    - (* (4): entry-key class-minimality *)
      intros x valx d val Hx Hvx Hav Hn Hv Hfp.
      destruct (CORE d val Hav Hn Hv) as
          [(y & Hy & Hcy & Hky) | (Hlen & Hdom)].
      + assert (Hxin : In x (xscan (S k0) (S f) stack v)).
        { rewrite Hxs in Hx. eapply In_firstn. exact Hx. }
        assert (Hcx : dcls x = Some (fp val)).
        { unfold dcls, clsf. rewrite Hvx, Hfp. reflexivity. }
        assert (Hxy : x = y).
        { eapply NoDup_map_same with (f := dcls);
            [apply xscan_classes_nodup | exact Hxin | exact Hy |].
          rewrite Hcx, Hcy. reflexivity. }
        subst y. exact Hky.
      + apply Hdom. exact Hx.
    - (* (5): covered-or-dominated *)
      intros d val Hav Hn Hv.
      destruct (CORE d val Hav Hn Hv) as
          [(y & Hy & Hcy & Hky) | (Hlen & Hdom)].
      + (* the class entry either survives the cap or dominates through it *)
        rewrite <- (firstn_skipn (S k0) (xscan (S k0) (S f) stack v)) in Hy.
        apply in_app_iff in Hy. destruct Hy as [Hy | Hy].
        * left. exists y. split; [rewrite Hxs; exact Hy | exact Hcy].
        * right.
          assert (Hlong : S k0 < length (xscan (S k0) (S f) stack v)).
          { pose proof (skipn_len D (S k0) (xscan (S k0) (S f) stack v)) as Hsl.
            destruct (skipn (S k0) (xscan (S k0) (S f) stack v)) eqn:Esk;
              [destruct Hy|].
            try rewrite Esk in Hsl. cbn [length] in Hsl. lia. }
          split.
          { rewrite Hxs, length_firstn. lia. }
          intros x Hx.
          assert (Hxy : keyleb x y = true).
          { eapply (ssorted_firstn_skipn D keyleb keyleb_total
                      (S k0) (xscan (S k0) (S f) stack v)).
            - apply xscan_sorted.
            - rewrite Hxs in Hx. exact Hx.
            - exact Hy. }
          unfold keyleb in Hxy.
          eapply kle_trans; [exact Hxy | exact Hky].
      + right. split; [|exact Hdom].
        rewrite Hxs, length_firstn. lia.
  Qed.

  (* T3 packaged at the root: sortedness, class-distinctness, soundness,
     class-min weights, and top-k dominance — "the node's k-list = the
     top-k distinct classes by the order, each with its class-min weight"
     (ties resolved by the loop's deterministic (pk_idx, j) refinement,
     under which the top-k set is unique; the statements here are the
     tie-robust content). *)
  Theorem t3_k_exactness :
    forall k root, root < num_nodes ->
      (forall x, In x (xcap k (S num_nodes) [] root) ->
         dnode x = root /\ Avoid [] x /\ exists val, dval x = Some val)
      /\ SSorted D keyleb (xcap k (S num_nodes) [] root)
      /\ NoDup (map dcls (xcap k (S num_nodes) [] root))
      /\ (forall x valx d val,
            In x (xcap k (S num_nodes) [] root) -> dval x = Some valx ->
            Avoid [] d -> dnode d = root -> dval d = Some val ->
            fp valx = fp val ->
            kle (dkey x) (dkey d))
      /\ (forall d val,
            Avoid [] d -> dnode d = root -> dval d = Some val ->
            (exists x, In x (xcap k (S num_nodes) [] root)
                       /\ dcls x = Some (fp val))
            \/ (length (xcap k (S num_nodes) [] root) = k
                /\ forall x, In x (xcap k (S num_nodes) [] root) ->
                     kle (dkey x) (dkey d))).
  Proof.
    intros k root Hroot.
    pose proof (ctx_root root Hroot) as Hctx.
    destruct (t3_invariant k (S num_nodes) [] root Hctx) as (H4 & H5).
    split;
      [intros x Hx; exact (xcap_sound k (S num_nodes) [] root Hctx x Hx)|].
    split; [apply xcap_sorted|].
    split; [apply xcap_classes_nodup|].
    split; [exact H4 | exact H5].
  Qed.

  (* If the delivered list is strictly shorter than k, it is CLASS-
     COMPLETE (the top-k covers everything). *)
  Corollary t3_all_classes_when_short :
    forall k root, root < num_nodes ->
      length (xcap k (S num_nodes) [] root) < k ->
      forall d val,
        Avoid [] d -> dnode d = root -> dval d = Some val ->
        exists x, In x (xcap k (S num_nodes) [] root) /\ dcls x = Some (fp val).
  Proof.
    intros k root Hroot Hshort d val Hav Hn Hv.
    pose proof (ctx_root root Hroot) as Hctx.
    destruct (t3_invariant k (S num_nodes) [] root Hctx) as (_ & H5).
    destruct (H5 d val Hav Hn Hv) as [Hcov | (Hlen & _)];
      [exact Hcov | lia].
  Qed.

  (* ══ Acyclic forests (T1's stated habitat; the stack never blocks, so
        the per-demand model and the memoizing implementation coincide,
        and stack-avoiding = plainly wellformed). ══ *)

  Section Acyclic.
    Variable rank : nat -> nat.
    Hypothesis rank_dec :
      forall v ch c, In ch (packings_of v) -> In c ch -> rank c < rank v.

    Lemma wf_avoid :
      forall d, Wf d ->
      forall stack, (forall s, In s stack -> rank (dnode d) < rank s) ->
      Avoid stack d.
    Proof.
      intro d. induction d as [v e ds IH] using D_ind_strong.
      intros Hwf stack Hstack.
      inversion Hwf as [? ? ? ch Hnth Hmap Hkids]; subst.
      cbn in Hstack.
      assert (Hchin : In (map dnode ds) (packings_of v))
        by (eapply nth_error_In; eauto).
      apply Avoid_mk with (ch := map dnode ds);
        [| exact Hnth | reflexivity |].
      - intro Hin. specialize (Hstack v Hin). lia.
      - rewrite Forall_forall in *.
        intros s Hs.
        assert (Hrs : rank (dnode s) < rank v).
        { eapply rank_dec; [exact Hchin|].
          apply in_map. exact Hs. }
        apply (IH s Hs); [apply Hkids; exact Hs|].
        intros t Ht. destruct Ht as [<- | Ht]; [exact Hrs|].
        specialize (Hstack t Ht). lia.
    Qed.

    (* T1, all candidates feasible: the root's head is a wellformed
       derivation of the root whose key is minimal over the ENTIRE
       derivation set — list[0] is an argmin of the mode order. *)
    Theorem t1_elect_soundness_all_feasible :
      forall root, root < num_nodes ->
      forall d0, Wf d0 -> dnode d0 = root ->
      exists x rest,
        xfull (S num_nodes) [] root = x :: rest
        /\ Wf x /\ dnode x = root /\ (exists val, dval x = Some val)
        /\ (forall d, Wf d -> dnode d = root -> kle (dkey x) (dkey d)).
    Proof.
      intros root Hroot d0 Hwf0 Hn0.
      pose proof (ctx_root root Hroot) as Hctx.
      assert (Hav0 : Avoid [] d0)
        by (apply wf_avoid; [exact Hwf0 | intros s []]).
      destruct (xfull_dominates_total (S num_nodes) [] root d0 Hctx Hav0 Hn0)
        as (x0 & Hx0 & _).
      destruct (xfull (S num_nodes) [] root) as [|x rest] eqn:E;
        [destruct Hx0|].
      exists x, rest. split; [reflexivity|].
      assert (Hxin : In x (xfull (S num_nodes) [] root))
        by (rewrite E; left; reflexivity).
      destruct (xfull_sound (S num_nodes) [] root Hctx x Hxin)
        as (Hxn & Hxav & Hxfeas).
      split; [eapply avoid_wf; eauto|].
      split; [exact Hxn|]. split; [exact Hxfeas|].
      intros d Hwf Hn.
      assert (Hav : Avoid [] d)
        by (apply wf_avoid; [exact Hwf | intros s []]).
      destruct (xfull_dominates_total (S num_nodes) [] root d Hctx Hav Hn)
        as (y & Hy & Hkey).
      eapply kle_trans; [|exact Hkey].
      pose proof (xfull_sorted (S num_nodes) [] root) as Hsorted.
      rewrite E in Hsorted.
      assert (Hhead : keyleb x y = true).
      { eapply (ssorted_head_min D keyleb keyleb_total x rest y Hsorted).
        rewrite <- E. exact Hy. }
      unfold keyleb in Hhead. exact Hhead.
    Qed.

    (* T1, feasible subset: with infeasible candidates present, the head
       is an argmin over the FEASIBLE derivation subset. *)
    Theorem t1_elect_soundness_feasible_subset :
      forall root, root < num_nodes ->
      forall d0 val0, Wf d0 -> dnode d0 = root -> dval d0 = Some val0 ->
      exists x rest,
        xfull (S num_nodes) [] root = x :: rest
        /\ Wf x /\ dnode x = root /\ (exists val, dval x = Some val)
        /\ (forall d val, Wf d -> dnode d = root -> dval d = Some val ->
              kle (dkey x) (dkey d)).
    Proof.
      intros root Hroot d0 val0 Hwf0 Hn0 Hv0.
      pose proof (ctx_root root Hroot) as Hctx.
      assert (Hav0 : Avoid [] d0)
        by (apply wf_avoid; [exact Hwf0 | intros s []]).
      destruct (xfull_complete (S num_nodes) [] root d0 val0 Hctx Hav0 Hn0 Hv0)
        as (x0 & Hx0 & _).
      destruct (xfull (S num_nodes) [] root) as [|x rest] eqn:E;
        [destruct Hx0|].
      exists x, rest. split; [reflexivity|].
      assert (Hxin : In x (xfull (S num_nodes) [] root))
        by (rewrite E; left; reflexivity).
      destruct (xfull_sound (S num_nodes) [] root Hctx x Hxin)
        as (Hxn & Hxav & Hxfeas).
      split; [eapply avoid_wf; eauto|].
      split; [exact Hxn|]. split; [exact Hxfeas|].
      intros d val Hwf Hn Hv.
      assert (Hav : Avoid [] d)
        by (apply wf_avoid; [exact Hwf | intros s []]).
      destruct (xfull_dominates (S num_nodes) [] root d val Hctx Hav Hn Hv)
        as (y & Hy & _ & Hkey).
      eapply kle_trans; [|exact Hkey].
      pose proof (xfull_sorted (S num_nodes) [] root) as Hsorted.
      rewrite E in Hsorted.
      assert (Hhead : keyleb x y = true).
      { eapply (ssorted_head_min D keyleb keyleb_total x rest y Hsorted).
        rewrite <- E. exact Hy. }
      unfold keyleb in Hhead. exact Hhead.
    Qed.

    (* T2 restated on acyclic forests over plainly wellformed derivations. *)
    Theorem t2_exhaustion_iff_acyclic :
      forall root, root < num_nodes ->
        (xfull (S num_nodes) [] root = []
         <-> ~ (exists d val, Wf d /\ dnode d = root /\ dval d = Some val)).
    Proof.
      intros root Hroot.
      pose proof (ctx_root root Hroot) as Hctx.
      rewrite (t2_exhaustion_iff (S num_nodes) [] root Hctx).
      split; intros Hno (d & val & H1 & H2 & H3); apply Hno.
      - exists d, val. split; [|auto].
        apply wf_avoid; [exact H1 | intros s []].
      - exists d, val. split; [|auto].
        eapply avoid_wf; eauto.
    Qed.

  End Acyclic.

End KBest.

(* ════════════════════════════════════════════════════════════════════════
   Part 4 — T4: the Huang-Chiang loop skeleton and its work accounting
   (spec §2.3 loop, §2.8 bound, amendment A9).  One node's session: the
   frontier holds candidate descriptors; each step pops one, classifies
   it (append / infeasible / duplicate — spec §2.3's three evaluate
   outcomes), and pushes its <= arity successors, suppressed by the
   pushed-set ((pk, j) admitted at most once).  The loop runs only while
   the list is short of k and the frontier is non-empty.
   ════════════════════════════════════════════════════════════════════════ *)

Section WorkBound.
  Variable Cand : Type.
  Hypothesis cand_eq_dec : forall x y : Cand, {x = y} + {x <> y}.
  Variable univ seeds : list Cand.
  Hypothesis seeds_nodup : NoDup seeds.
  Hypothesis seeds_univ : incl seeds univ.
  Variable succs : Cand -> list Cand.
  Variable amax : nat.
  Hypothesis succs_bound : forall c, length (succs c) <= amax.
  Hypothesis succs_univ : forall c x, In x (succs c) -> In x univ.
  Variable k : nat.

  Definition push_new (pushed cs : list Cand) : list Cand :=
    filter (fun x => if in_dec cand_eq_dec x pushed then false else true)
      (nodup cand_eq_dec cs).

  Lemma push_new_nodup : forall pushed cs, NoDup (push_new pushed cs).
  Proof. intros. apply nd_filter. apply NoDup_nodup. Qed.

  Lemma push_new_fresh :
    forall pushed cs x, In x (push_new pushed cs) -> ~ In x pushed.
  Proof.
    intros pushed cs x H. apply filter_In in H. destruct H as [_ Ht].
    destruct (in_dec cand_eq_dec x pushed); [discriminate | assumption].
  Qed.

  Lemma push_new_incl :
    forall pushed cs x, In x (push_new pushed cs) -> In x cs.
  Proof.
    intros pushed cs x H. apply filter_In in H. destruct H as [Hn _].
    apply nodup_In in Hn. exact Hn.
  Qed.

  Lemma push_new_len :
    forall pushed cs, length (push_new pushed cs) <= length cs.
  Proof.
    intros. etransitivity; [apply flt_len_le | apply nodup_len_le].
  Qed.

  Lemma rm_in :
    forall (l : list Cand) x y,
      In y (remove cand_eq_dec x l) -> In y l /\ y <> x.
  Proof.
    induction l as [|a l IH]; intros x y H; cbn in H; [destruct H|].
    destruct (cand_eq_dec x a).
    - subst. destruct (IH _ _ H). split; [right; assumption | assumption].
    - destruct H as [<- | H].
      + split; [left; reflexivity|].
        intro He. subst. exact (n eq_refl).
      + destruct (IH _ _ H). split; [right; assumption | assumption].
  Qed.

  Lemma rm_notin :
    forall (l : list Cand) x, ~ In x l -> remove cand_eq_dec x l = l.
  Proof.
    induction l as [|a l IH]; intros x Hn; cbn; [reflexivity|].
    destruct (cand_eq_dec x a).
    - subst. exfalso. apply Hn. left. reflexivity.
    - f_equal. apply IH. intro H. apply Hn. right. exact H.
  Qed.

  Lemma rm_len :
    forall (l : list Cand) x,
      NoDup l -> In x l ->
      S (length (remove cand_eq_dec x l)) = length l.
  Proof.
    induction l as [|a l IH]; intros x Hnd Hin; [destruct Hin|].
    inversion Hnd as [|? ? Hnin Hnd']; subst. cbn.
    destruct (cand_eq_dec x a).
    - subst. rewrite rm_notin; [reflexivity | assumption].
    - destruct Hin as [Heq | Hin]; [exfalso; apply n; symmetry; exact Heq|].
      cbn. f_equal. apply IH; assumption.
  Qed.

  Lemma rm_nodup :
    forall (l : list Cand) x, NoDup l -> NoDup (remove cand_eq_dec x l).
  Proof.
    induction l as [|a l IH]; intros x H; cbn; [constructor|].
    inversion H as [|? ? Hnin Hnd]; subst.
    destruct (cand_eq_dec x a).
    - apply IH. assumption.
    - constructor.
      + intro Hin. apply rm_in in Hin. destruct Hin. contradiction.
      + apply IH. assumption.
  Qed.

  Record LoopState := mkLoop {
    l_frontier : list Cand;
    l_pushed : list Cand;
    l_app : nat;
    l_inf : nat;
    l_dup : nat
  }.

  Definition l_pops (s : LoopState) : nat := l_app s + l_inf s + l_dup s.

  Inductive PopClass := PAppend | PInfeasible | PDup.

  Definition class_app (c : PopClass) : nat :=
    match c with PAppend => 1 | _ => 0 end.
  Definition class_inf (c : PopClass) : nat :=
    match c with PInfeasible => 1 | _ => 0 end.
  Definition class_dup (c : PopClass) : nat :=
    match c with PDup => 1 | _ => 0 end.

  Inductive loop_step : LoopState -> LoopState -> Prop :=
  | loop_pop : forall s c cls,
      In c (l_frontier s) ->
      l_app s < k ->
      loop_step s
        (mkLoop
           (remove cand_eq_dec c (l_frontier s)
              ++ push_new (l_pushed s) (succs c))
           (l_pushed s ++ push_new (l_pushed s) (succs c))
           (l_app s + class_app cls)
           (l_inf s + class_inf cls)
           (l_dup s + class_dup cls)).

  Definition loop_init : LoopState := mkLoop seeds seeds 0 0 0.

  Inductive loop_run : LoopState -> LoopState -> Prop :=
  | loop_run_refl : forall s, loop_run s s
  | loop_run_step : forall s t u, loop_step s t -> loop_run t u -> loop_run s u.

  Definition loop_inv (s : LoopState) : Prop :=
    NoDup (l_pushed s)
    /\ incl (l_pushed s) univ
    /\ NoDup (l_frontier s)
    /\ incl (l_frontier s) (l_pushed s)
    /\ l_pops s + length (l_frontier s) = length (l_pushed s)
    /\ length (l_pushed s) <= length seeds + amax * l_pops s
    /\ l_app s <= k.

  Lemma class_sum_one :
    forall cls, class_app cls + class_inf cls + class_dup cls = 1.
  Proof. destruct cls; reflexivity. Qed.

  Lemma loop_step_preserves :
    forall s t, loop_step s t -> loop_inv s -> loop_inv t.
  Proof.
    intros s t Hstep (Hpnd & Hpu & Hfnd & Hfp & Hcount & Hpush & Happ).
    inversion Hstep as [s' c cls Hc Hlt]; subst. cbn.
    set (new := push_new (l_pushed s) (succs c)).
    assert (Hnnd : NoDup new) by apply push_new_nodup.
    assert (Hnfresh : forall x, In x new -> ~ In x (l_pushed s))
      by (intros; eapply push_new_fresh; eauto).
    assert (Hnuniv : forall x, In x new -> In x univ).
    { intros x Hx. eapply succs_univ. eapply push_new_incl. exact Hx. }
    assert (Hnlen : length new <= amax).
    { etransitivity; [apply push_new_len | apply succs_bound]. }
    assert (Hrmlen : S (length (remove cand_eq_dec c (l_frontier s)))
                     = length (l_frontier s))
      by (apply rm_len; assumption).
    repeat split.
    - apply nodup_app_disjoint; [exact Hpnd | exact Hnnd |].
      intros x Hx Hnew. exact (Hnfresh x Hnew Hx).
    - intros x Hx. apply in_app_iff in Hx.
      destruct Hx as [Hx | Hx]; [apply Hpu; exact Hx | apply Hnuniv; exact Hx].
    - apply nodup_app_disjoint; [apply rm_nodup; exact Hfnd | exact Hnnd |].
      intros x Hx Hnew.
      apply rm_in in Hx. destruct Hx as [Hx _].
      exact (Hnfresh x Hnew (Hfp x Hx)).
    - intros x Hx. apply in_app_iff in Hx. apply in_app_iff.
      destruct Hx as [Hx | Hx].
      + left. apply Hfp. apply rm_in in Hx. tauto.
      + right. exact Hx.
    - unfold l_pops in *. cbn.
      rewrite length_app. rewrite length_app.
      pose proof (class_sum_one cls). lia.
    - unfold l_pops in *. cbn.
      rewrite length_app.
      pose proof (class_sum_one cls).
      assert (Hm : amax * (l_app s + class_app cls
                           + (l_inf s + class_inf cls)
                           + (l_dup s + class_dup cls))
                   = amax * (l_app s + l_inf s + l_dup s) + amax * 1).
      { rewrite <- Nat.mul_add_distr_l. f_equal. lia. }
      rewrite Hm. lia.
    - cbn.
      assert (class_app cls <= 1) by (destruct cls; cbn; lia).
      lia.
  Qed.

  Lemma loop_init_inv : loop_inv loop_init.
  Proof.
    repeat split; cbn.
    - exact seeds_nodup.
    - intros x Hx. apply seeds_univ. exact Hx.
    - exact seeds_nodup.
    - intros x Hx. exact Hx.
    - lia.
    - lia.
  Qed.

  Lemma loop_run_inv : forall s t, loop_run s t -> loop_inv s -> loop_inv t.
  Proof.
    intros s t H. induction H as [s | s t u Hst H IH]; intro Hs.
    - exact Hs.
    - apply IH. eapply loop_step_preserves; eauto.
  Qed.

  (* T4: the loop's stop condition is exactly "list full or frontier
     drained" — no other stuck states exist. *)
  Theorem t4_loop_done_or_step :
    forall s, loop_run loop_init s ->
      (l_app s = k \/ l_frontier s = []) \/ exists t, loop_step s t.
  Proof.
    intros s Hr.
    destruct (l_frontier s) as [|c fr] eqn:E.
    - left. right. reflexivity.
    - destruct (Nat.eq_dec (l_app s) k) as [He | Hne].
      + left. left. exact He.
      + right.
        pose proof (loop_run_inv _ _ Hr loop_init_inv)
          as (_ & _ & _ & _ & _ & _ & Happ).
        eexists. apply (loop_pop s c PAppend).
        * rewrite E. left. reflexivity.
        * lia.
  Qed.

  Theorem t4_append_bound :
    forall s, loop_run loop_init s -> l_app s <= k.
  Proof.
    intros s H.
    pose proof (loop_run_inv _ _ H loop_init_inv)
      as (_ & _ & _ & _ & _ & _ & Happ).
    exact Happ.
  Qed.

  (* T4 pop-count identity + bound: pops = appends + I + D <= k + I + D. *)
  Theorem t4_pop_count :
    forall s, loop_run loop_init s -> l_pops s <= k + l_inf s + l_dup s.
  Proof.
    intros s H. unfold l_pops.
    pose proof (t4_append_bound s H). lia.
  Qed.

  (* The contracted per-node form: pops <= |packings| + 2*(k + I + D)
     (seeds = one all-ones candidate per packing, so |seeds| stands for
     |packings(v)|; the 2* slack absorbs the push-side work term). *)
  Theorem t4_work_bound_node :
    forall s, loop_run loop_init s ->
      l_pops s <= length seeds + 2 * (k + l_inf s + l_dup s).
  Proof.
    intros s H. pose proof (t4_pop_count s H). lia.
  Qed.

  Theorem t4_push_bound :
    forall s, loop_run loop_init s ->
      length (l_pushed s) <= length seeds + amax * l_pops s.
  Proof.
    intros s H.
    pose proof (loop_run_inv _ _ H loop_init_inv)
      as (_ & _ & _ & _ & _ & Hpush & _).
    exact Hpush.
  Qed.

  Theorem t4_pops_le_pushed :
    forall s, loop_run loop_init s -> l_pops s <= length (l_pushed s).
  Proof.
    intros s H.
    pose proof (loop_run_inv _ _ H loop_init_inv)
      as (_ & _ & _ & _ & Hcount & _ & _).
    lia.
  Qed.

  (* Pushed-set dedup makes every pop a DISTINCT candidate: pops are
     bounded by the finite candidate universe. *)
  Theorem t4_pop_universe :
    forall s, loop_run loop_init s -> l_pops s <= length univ.
  Proof.
    intros s H.
    pose proof (loop_run_inv _ _ H loop_init_inv)
      as (Hnd & Hincl & _ & _ & Hcount & _ & _).
    assert (length (l_pushed s) <= length univ)
      by (apply NoDup_incl_length; assumption).
    lia.
  Qed.

  (* With |univ| <= P * k^a (cand_list_length_bound), pops are polynomial:
     O(|packings| * k^arity) per node — k² on the binary spine. *)
  Theorem t4_pop_polynomial :
    forall s (P a : nat),
      loop_run loop_init s ->
      length univ <= P * k ^ a ->
      l_pops s <= P * k ^ a.
  Proof.
    intros s P a Hr Hu.
    etransitivity; [apply t4_pop_universe; exact Hr | exact Hu].
  Qed.

End WorkBound.

(* The contracted Σ_v form: summing the per-node bound over the demanded
   nodes of a session (nw_packings v = |packings(v)| = the per-node seed
   count; discharged per node by t4_work_bound_node). *)
Record NodeWork := mkNodeWork {
  nw_packings : nat;
  nw_pops : nat;
  nw_inf : nat;
  nw_dup : nat
}.

Theorem t4_work_bound_total :
  forall (k : nat) (ws : list NodeWork),
    Forall (fun w => nw_pops w <= nw_packings w + 2 * (k + nw_inf w + nw_dup w))
      ws ->
    fold_right (fun w acc => nw_pops w + acc) 0 ws
    <= fold_right
         (fun w acc => nw_packings w + 2 * (k + nw_inf w + nw_dup w) + acc)
         0 ws.
Proof.
  intros k ws H. induction H as [|w ws Hw H IH]; cbn [fold_right]; lia.
Qed.

(* ════════════════════════════════════════════════════════════════════════
   Part 5 — the Weight mode's stated ⊕/⊗ hypotheses (spec §3.4):
   ⊕ = kleb-min is SELECTIVE (hence the order is the semiring's natural
   total order) and idempotently keeps the first of ties (the
   dedup_push_realized fold contract); ⊗ weakly monotone on both sides
   lifts to the composition-monotonicity `kcomp_mono` (Goodman
   superiority) used by T1/T3 — instantiate kcomp := kcompW.
   ════════════════════════════════════════════════════════════════════════ *)

Section WeightMode.
  Variable K : Type.
  Variable kleb : K -> K -> bool.
  Hypothesis kleb_total : forall a b, kleb a b = true \/ kleb b a = true.
  Hypothesis kleb_trans : forall a b c,
      kleb a b = true -> kleb b c = true -> kleb a c = true.

  Definition kleW (a b : K) : Prop := kleb a b = true.

  Lemma kleW_refl : forall a, kleW a a.
  Proof. intro a. unfold kleW. destruct (kleb_total a a); assumption. Qed.

  Variable otimes : K -> K -> K.
  Hypothesis otimes_mono_l :
    forall c a b, kleW a b -> kleW (otimes c a) (otimes c b).
  Hypothesis otimes_mono_r :
    forall c a b, kleW a b -> kleW (otimes a c) (otimes b c).

  Definition oplus (a b : K) : K := if kleb a b then a else b.

  (* ⊕ is SELECTIVE: it returns one of its operands — the §3.4 "⊕ = plus
     is exactly lex-min under this order" precondition. *)
  Lemma w_oplus_selective : forall a b, oplus a b = a \/ oplus a b = b.
  Proof. intros; unfold oplus; destruct (kleb a b); auto. Qed.

  Lemma w_oplus_min : forall a b, kleW (oplus a b) a /\ kleW (oplus a b) b.
  Proof.
    intros a b. unfold oplus. destruct (kleb a b) eqn:E.
    - split; [apply kleW_refl | exact E].
    - split; [|apply kleW_refl].
      destruct (kleb_total a b) as [H | H];
        [rewrite H in E; discriminate | exact H].
  Qed.

  (* The min-W dedup fold ("strictly-less replaces, ties keep first",
     dedup_push_realized :7484-7501) is a NO-OP against a first-popped
     incumbent under key-ordered popping: keep-first models it exactly. *)
  Lemma w_dedup_fold_noop :
    forall first later, kleW first later -> oplus first later = first.
  Proof.
    intros f l H. unfold oplus. unfold kleW in H. rewrite H. reflexivity.
  Qed.

  Variable wpk : nat -> nat -> K.
  Definition kcompW (v e : nat) (ks : list K) : K :=
    fold_left otimes ks (wpk v e).

  Lemma fold_left_otimes_mono :
    forall ks1 ks2 acc1 acc2,
      Forall2 kleW ks1 ks2 -> kleW acc1 acc2 ->
      kleW (fold_left otimes ks1 acc1) (fold_left otimes ks2 acc2).
  Proof.
    intros ks1 ks2 acc1 acc2 H. revert acc1 acc2.
    induction H as [|a b ks1' ks2' Hab H IH]; intros acc1 acc2 Hacc; cbn.
    - exact Hacc.
    - apply IH.
      unfold kleW in *.
      eapply kleb_trans.
      + exact (otimes_mono_r a _ _ Hacc).
      + exact (otimes_mono_l acc2 _ _ Hab).
  Qed.

  (* Discharges the main development's kcomp_mono hypothesis for the
     Weight key (weak ⊗-monotonicity ⇒ composition monotonicity). *)
  Theorem w_kcompW_mono :
    forall v e ks1 ks2,
      Forall2 kleW ks1 ks2 -> kleW (kcompW v e ks1) (kcompW v e ks2).
  Proof.
    intros. apply fold_left_otimes_mono; [assumption | apply kleW_refl].
  Qed.

End WeightMode.

(* ── ADMISSION AUDIT — every theorem must print
      "Closed under the global context". ── *)
Print Assumptions t1_elect_soundness_all_feasible.
Print Assumptions t1_elect_soundness_feasible_subset.
Print Assumptions t2_exhaustion_iff.
Print Assumptions t2_exhaustion_iff_acyclic.
Print Assumptions t2_capped_pass_sound.
Print Assumptions t2_capped_empty_no_trunc.
Print Assumptions t2_driver_terminates.
Print Assumptions t3_invariant.
Print Assumptions t3_k_exactness.
Print Assumptions t3_all_classes_when_short.
Print Assumptions t4_loop_done_or_step.
Print Assumptions t4_append_bound.
Print Assumptions t4_pop_count.
Print Assumptions t4_work_bound_node.
Print Assumptions t4_push_bound.
Print Assumptions t4_pops_le_pushed.
Print Assumptions t4_pop_universe.
Print Assumptions t4_pop_polynomial.
Print Assumptions t4_work_bound_total.
Print Assumptions t5_truncation_completeness.
Print Assumptions cand_list_length_bound.
Print Assumptions t4_candidate_space_binary.
Print Assumptions w_oplus_selective.
Print Assumptions w_oplus_min.
Print Assumptions w_dedup_fold_noop.
Print Assumptions w_kcompW_mono.
