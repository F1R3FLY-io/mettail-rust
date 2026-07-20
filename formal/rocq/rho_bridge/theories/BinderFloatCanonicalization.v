(*
 * BinderFloatCanonicalization: FV (A-S5.4a) — the UNCONDITIONAL unbind-first binder float
 * (macros/src/gen/runtime/binder_congruence.rs, gates dropped) canonicalizes Ambient-shaped
 * terms so that every bag/nested redex that exists MODULO the Cardelli–Gordon structural-
 * congruence subset is SYNTACTICALLY present in the float normal form.
 *
 * ---------------------------------------------------------------------------------------
 * THEORY CONTEXT (scratchpad a_s5_design/ma_theory_alignment.md, USER MA mandate)
 * ---------------------------------------------------------------------------------------
 *
 * The C-G subset that is load-bearing for MATCH COMPLETENESS is exactly
 *
 *   (Struct Res Par)   (n)(P | Q) == P | (n)Q      if n not in fn(P)
 *   (Struct Res Amb)   (n)(m[P])  == m[(n)P]       if n <> m
 *   (Struct Res Res)   (n)(m)P    == (m)(n)P
 *   + (Struct Par Comm/Assoc), absorbed REPRESENTATIONALLY by the HashBag
 *
 * because all three rewrite LHS patterns (InRule/OutRule/OpenRule) bind capability
 * continuations as pattern VARIABLES — a `new` under a capability never blocks a match
 * (the MA strengthening).  Alpha-conversion is DEFINITIONAL IDENTITY in C-G, so the
 * amended canonicalizer's freshen-then-float (moniker `unbind` = process-global gensym,
 * delta-verified) is one free alpha step followed by a Res Par / Res Amb instance whose
 * side condition holds BY CONSTRUCTION.  This file therefore models the equivalence in
 * the alpha-quotient: the hoist axioms carry no freshness side conditions, and the
 * dischargeability of those side conditions is exactly Part 1 (`freshening_totality` —
 * the freshening supply never exhausts, so the unconditional float NEVER stalls; the
 * pre-A-S5.4a conditional float DID stall, the refuted F1 behavior).
 *
 * ---------------------------------------------------------------------------------------
 * WHAT IS MODELED (and at what level — the abstraction split)
 * ---------------------------------------------------------------------------------------
 *
 *  Part 1  Freshening totality over names-as-nat: a fresh name exists over any finite
 *          used set.  Models the moniker gensym supply; discharges the alpha side
 *          conditions of every hoist below.
 *
 *  Part 2  Bag flatness over an UNBOUNDED-DEPTH element algebra (`Elem`): the generated
 *          `insert_into_<label>` auto-flatten helper (macros/src/gen/term_ops/
 *          normalize.rs — the host mirror of `add_flattened_bag`, an iterative
 *          work-stack peel) is modeled by `flatten_elem`/`splice_insert`, and the AM-2
 *          obligation `float_preserves_bag_flatness` is proven at ALL nesting depths
 *          (the work-stack peels every same-constructor layer, witnessed down to the
 *          double-nested example).
 *
 *  Part 3  Redex EXPOSURE over the DEPTH-2 fragment the rewrite patterns actually
 *          inspect (`nested_structural_ac_rule_shape` is depth-2; continuations under
 *          capabilities are opaque pattern variables): configurations are a nu-prefix
 *          over an outer bag whose members are nu-prefixed cores (ambient-with-inner-bag,
 *          capability, opaque, or a one-level nested bag — the AM-2 extrusion seam;
 *          deeper nesting is dissolved by Part 2's helper before this fragment is
 *          reached).  The C-G subset acts through five documented composite axioms
 *          (`cstep`), the float is the canonicalizer `float`, and
 *          `float_nf_exposes_redexes_{in,open,out}` is the iff of design v2 section 3.3.
 *          The In and Open families read the configuration as a TOP-LEVEL bag; the Out
 *          family (A-S5.4b — the rule is now REDECLARED to (Red Out) per AM-1, the
 *          residual kept inside `m`) reads it as the ENCLOSING AMBIENT `m`'s BODY bag,
 *          with `m` a parameter: `out_redex m body` holds when some member is an ambient
 *          `n[...]` whose inner bag carries the prefix-free `out(m)` capability — exactly
 *          the sub-configuration the redeclared LHS `m[{ n[{out(m,P),...}], ... }]`
 *          inspects below its root.  The per-level reading is FAITHFUL to the
 *          implementation: the generated float recurses bottom-up (children normalize
 *          first), so every bag level — the top level AND each ambient body — is
 *          float-canonicalized by the SAME canonicalizer, and the hoist through `m`'s own
 *          wall into the level above is that level's (E-hoist-amb) step.  The Out FIRING
 *          (commit/reject/reduct shape) lives in AmbientInOutFiring.v's re-proof; here we
 *          prove EXPOSURE.
 *
 *  Part 4  `newcomm_permutation_redex_invariance`: redex exposure is invariant under
 *          ANY permutation of the nu-prefix (Struct Res Res).  The implementation's
 *          <=6-binder canonical-run cap (binder_congruence.rs, Heap-permutation display
 *          ordering) therefore affects DISPLAY canonicality only, never exposure.
 *
 * Rocq 9.1 compatible.  No Admitted, no Axioms, no Assumptions, no Parameters.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Permutation.

Import ListNotations.

(* =====================================================================================
   Part 1 — Freshening totality: the gensym supply never exhausts.
   ===================================================================================== *)

Section FresheningTotality.

  (* The canonical fresh name over a finite used set: one past the maximum. *)
  Definition fresh_name (used : list nat) : nat :=
    S (fold_right Nat.max 0 used).

  Lemma in_le_fold_max : forall used x,
    In x used -> x <= fold_right Nat.max 0 used.
  Proof.
    induction used as [| u used' IH]; intros x Hin.
    - contradiction.
    - simpl. destruct Hin as [-> | Hin].
      + apply Nat.le_max_l.
      + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
  Qed.

  Theorem fresh_name_is_fresh : forall used, ~ In (fresh_name used) used.
  Proof.
    intros used Hin. apply in_le_fold_max in Hin. unfold fresh_name in Hin.
    exact (Nat.nle_succ_diag_l _ Hin).
  Qed.

  (* THE TOTALITY: over ANY finite set of used names a fresh name exists, so the
     unconditional unbind-first float NEVER stalls on freshness — the alpha side
     condition of every hoist below is dischargeable by construction (moniker
     `unbind` is a process-global gensym; AM-6d records the u32-recycling honest
     premise on the implementation side). *)
  Theorem freshening_totality : forall used : list nat, exists x, ~ In x used.
  Proof.
    intros used. exists (fresh_name used). apply fresh_name_is_fresh.
  Qed.

End FresheningTotality.

(* =====================================================================================
   Part 2 — Bag flatness at the extrusion seam (AM-2): the generated
   `insert_into_<label>` helper (work-stack peel) preserves flatness at ALL depths.
   ===================================================================================== *)

(* An element of a same-constructor collection: an opaque atom (any non-bag member —
   ambients, capabilities, leaves) or a nested same-constructor bag. Unbounded depth. *)
Inductive Elem : Type :=
  | EAtom : nat -> Elem
  | EBag : list Elem -> Elem.

(* The deep induction principle the nested `list Elem` requires (the auto-generated
   principle gives no hypothesis on bag members). *)
Section ElemDeepInd.
  Variable P : Elem -> Prop.
  Hypothesis Hatom : forall n, P (EAtom n).
  Hypothesis Hbag : forall l, Forall P l -> P (EBag l).

  Fixpoint Elem_deep_ind (e : Elem) : P e :=
    match e with
    | EAtom n => Hatom n
    | EBag l =>
        Hbag l
          ((fix elems_ind (l : list Elem) : Forall P l :=
              match l with
              | [] => Forall_nil P
              | x :: xs => Forall_cons x (Elem_deep_ind x) (elems_ind xs)
              end) l)
    end.
End ElemDeepInd.

(* The work-stack peel: every same-constructor layer dissolves, at every depth —
   the model of the generated `insert_into_<label>` loop (normalize.rs), which pushes
   a bag element's members back onto the stack and inserts only non-bag elements. *)
Fixpoint flatten_elem (e : Elem) : list Elem :=
  match e with
  | EAtom n => [EAtom n]
  | EBag l =>
      (fix flatten_list (l : list Elem) : list Elem :=
         match l with
         | [] => []
         | x :: xs => flatten_elem x ++ flatten_list xs
         end) l
  end.

Lemma flatten_ebag_eq : forall l,
  flatten_elem (EBag l) = flat_map flatten_elem l.
Proof.
  induction l as [| x xs IH]; simpl.
  - reflexivity.
  - simpl in IH. rewrite IH. reflexivity.
Qed.

Definition is_atom (e : Elem) : bool :=
  match e with
  | EAtom _ => true
  | EBag _ => false
  end.

(* A bag is FLAT iff no direct member is itself a same-constructor bag. *)
Definition flat (l : list Elem) : Prop :=
  forall e, In e l -> is_atom e = true.

Lemma flat_app : forall l1 l2, flat l1 -> flat l2 -> flat (l1 ++ l2).
Proof.
  intros l1 l2 H1 H2 e Hin. apply in_app_or in Hin.
  destruct Hin as [Hin | Hin]; [apply H1 | apply H2]; exact Hin.
Qed.

(* The peel is total: its output is flat, whatever the input depth. *)
Lemma flatten_elem_flat : forall e, flat (flatten_elem e).
Proof.
  intros e. induction e using Elem_deep_ind.
  - intros x Hin. destruct Hin as [<- | []]. reflexivity.
  - rewrite flatten_ebag_eq. intros x Hin.
    apply in_flat_map in Hin. destruct Hin as [y [Hy Hx]].
    rewrite Forall_forall in H. exact (H y Hy x Hx).
Qed.

(* The extrusion-seam insert: the opened nu-body `e` joins the residual bag through
   the auto-flatten helper — a same-constructor body SPLICES (its members join
   directly), any other body inserts as one member. *)
Definition splice_insert (e : Elem) (residual : list Elem) : list Elem :=
  flatten_elem e ++ residual.

(* A non-bag body inserts as ONE member (the helper's else-branch). *)
Lemma splice_insert_atom : forall n residual,
  splice_insert (EAtom n) residual = EAtom n :: residual.
Proof. reflexivity. Qed.

(* A same-constructor body SPLICES — no bag element is ever pushed (AM-2). *)
Lemma splice_insert_bag_splices : forall l residual,
  splice_insert (EBag l) residual = flat_map flatten_elem l ++ residual.
Proof. intros l residual. unfold splice_insert. rewrite flatten_ebag_eq. reflexivity. Qed.

(* THE AM-2 OBLIGATION: the unconditional float's extrusion seam preserves bag
   flatness — a flat residual stays flat after the opened body joins it. *)
Theorem float_preserves_bag_flatness : forall (body : Elem) (residual : list Elem),
  flat residual -> flat (splice_insert body residual).
Proof.
  intros body residual Hres. unfold splice_insert.
  apply flat_app; [apply flatten_elem_flat | exact Hres].
Qed.

(* The AM-3-strengthened depth witness: a DOUBLE-nested body peels completely in one
   insert — the work-stack loop is depth-agnostic (never one-level-only). *)
Example double_nested_body_flattens :
  splice_insert (EBag [EAtom 1; EBag [EAtom 2; EBag [EAtom 3; EAtom 4]]]) [EAtom 0]
  = [EAtom 1; EAtom 2; EAtom 3; EAtom 4; EAtom 0].
Proof. reflexivity. Qed.

(* =====================================================================================
   Part 3 — Redex exposure over the depth-2 fragment (the shape the Ambient rewrite
   patterns inspect).
   ===================================================================================== *)

Inductive Cap : Type := CIn | COut | COpen.

(* An inner (ambient-body-bag) element core: a capability prefix over an OPAQUE
   continuation (bound as a pattern variable — the MA strengthening), or opaque. *)
Inductive ICore : Type :=
  | ICap : Cap -> nat -> ICore
  | IOpq : nat -> ICore.

(* An inner member: a nu-prefix (list of restricted names) over an inner core. *)
Definition IMem : Type := (list nat) * ICore.

(* An outer element BASE core: an ambient with an inner bag, a capability, or opaque. *)
Inductive BCore : Type :=
  | KAmb : nat -> list IMem -> BCore
  | KCap : Cap -> nat -> BCore
  | KOpq : nat -> BCore.

(* An outer element core: a base core, or a ONE-LEVEL nested same-constructor bag of
   nu-prefixed base cores — the AM-2 extrusion seam (a bag-bodied nu extrudes to
   exactly this shape; deeper nesting is dissolved by Part 2's helper first). *)
Inductive OCore : Type :=
  | OBase : BCore -> OCore
  | OBag : list ((list nat) * BCore) -> OCore.

(* An outer member: a nu-prefix over an outer core. *)
Definition OMem : Type := (list nat) * OCore.

(* A configuration: the hoisted nu-prefix over the outer bag — float-canonical form
   has ALL nus here and every member/inner prefix empty. *)
Record Config : Type := mkCfg { c_nus : list nat; c_body : list OMem }.

(* ------------------------------------------------------------------------------------
   The canonicalizer (the unconditional float, in the alpha-quotient).
   ------------------------------------------------------------------------------------ *)

Definition strip_imem (im : IMem) : IMem := ([], snd im).

(* Hoist every inner nu through the ambient wall (inner Res Par then Res Amb). *)
Definition float_bcore (b : BCore) : (list nat) * BCore :=
  match b with
  | KAmb n inner => (flat_map fst inner, KAmb n (map strip_imem inner))
  | KCap c n => ([], KCap c n)
  | KOpq k => ([], KOpq k)
  end.

(* Float one nested-bag member: hoist its own prefix and its core's inner nus. *)
Definition float_bmem (p : (list nat) * BCore) : (list nat) * OMem :=
  (fst p ++ fst (float_bcore (snd p)), ([], OBase (snd (float_bcore (snd p))))).

(* Float one outer member: hoisted nus (left) and the resulting FLAT members (right).
   A base core keeps one member; a nested bag SPLICES (AM-2) — its members join the
   outer bag directly, never as one bag element. *)
Definition float_omem (m : OMem) : (list nat) * (list OMem) :=
  match snd m with
  | OBase b =>
      (fst m ++ fst (float_bcore b), [([], OBase (snd (float_bcore b)))])
  | OBag l =>
      (fst m ++ flat_map (fun p => fst (float_bmem p)) l,
       map (fun p => snd (float_bmem p)) l)
  end.

Definition float (cfg : Config) : Config :=
  mkCfg (c_nus cfg ++ flat_map (fun m => fst (float_omem m)) (c_body cfg))
        (flat_map (fun m => snd (float_omem m)) (c_body cfg)).

(* ------------------------------------------------------------------------------------
   Float-canonical form: all nus outermost, all bags flat.
   ------------------------------------------------------------------------------------ *)

Definition imem_canonical (im : IMem) : Prop := fst im = [].

Definition omem_canonical (m : OMem) : Prop :=
  fst m = [] /\
  match snd m with
  | OBase (KAmb _ inner) => Forall imem_canonical inner
  | OBase _ => True
  | OBag _ => False
  end.

Definition canonical (cfg : Config) : Prop := Forall omem_canonical (c_body cfg).

Lemma float_bmem_canonical : forall p, omem_canonical (snd (float_bmem p)).
Proof.
  intros [ks b]. unfold float_bmem, omem_canonical. simpl.
  destruct b as [n inner | c n | k]; simpl; [split | split | split];
    try reflexivity; try exact I.
  apply Forall_forall. intros im Hin. apply in_map_iff in Hin.
  destruct Hin as [im0 [<- _]]. reflexivity.
Qed.

Lemma float_omem_canonical : forall m x,
  In x (snd (float_omem m)) -> omem_canonical x.
Proof.
  intros [ks c] x Hin. destruct c as [b | l]; simpl in Hin.
  - destruct Hin as [<- | []].
    unfold omem_canonical. simpl.
    destruct b as [n inner | c n | k]; simpl; [split | split | split];
      try reflexivity; try exact I.
    apply Forall_forall. intros im Him. apply in_map_iff in Him.
    destruct Him as [im0 [<- _]]. reflexivity.
  - apply in_map_iff in Hin. destruct Hin as [p [<- _]].
    apply float_bmem_canonical.
Qed.

(* The float CANONICALIZES: its output is always in float-canonical form — every nu
   outermost, every member prefix empty, every bag flat (no OBag member survives). *)
Theorem float_canonicalizes : forall cfg, canonical (float cfg).
Proof.
  intros cfg. unfold canonical, float. simpl.
  apply Forall_forall. intros x Hin.
  apply in_flat_map in Hin. destruct Hin as [m [_ Hx]].
  exact (float_omem_canonical m x Hx).
Qed.

(* ------------------------------------------------------------------------------------
   The syntactic redexes (prefix-free = not hidden under any nu).
   ------------------------------------------------------------------------------------ *)

(* The InRule LHS shape at the top bag: { n[{ in(m).-, ...}], m[...], ...rest } —
   two distinct member occurrences (multiset selection via Permutation), the inner
   capability prefix-free inside the first ambient's body bag. *)
Definition in_redex (body : list OMem) : Prop :=
  exists n m inner1 inner2 rest,
    Permutation body
      (([], OBase (KAmb n inner1)) :: ([], OBase (KAmb m inner2)) :: rest)
    /\ In ([], ICap CIn m) inner1.

(* The OpenRule LHS shape: { open(n).-, n[...], ...rest }. *)
Definition open_redex (body : list OMem) : Prop :=
  exists n inner rest,
    Permutation body
      (([], OBase (KCap COpen n)) :: ([], OBase (KAmb n inner)) :: rest).

(* The REDECLARED (Red Out) OutRule LHS shape BELOW ITS ROOT (A-S5.4b, AM-1): the configuration
   is the enclosing ambient `m`'s BODY bag (`m` a parameter — the redeclared LHS
   `m[{ n[{out(m,P), ...rest1}], ...rest2 }]` binds the root name `m` and inspects exactly this
   bag), and the redex is ONE member `n[...]` whose inner bag carries the prefix-free `out(m)`
   capability; `rest` is the whole residual `...rest2` (EMPTY rest legal — the singleton fires,
   the redeclaration's discharge of C-G (Struct Zero Par)). *)
Definition out_redex (m : nat) (body : list OMem) : Prop :=
  exists n inner rest,
    Permutation body (([], OBase (KAmb n inner)) :: rest)
    /\ In ([], ICap COut m) inner.

Lemma in_redex_perm : forall body body',
  Permutation body body' -> in_redex body -> in_redex body'.
Proof.
  intros body body' Hperm (n & m & i1 & i2 & rest & Hp & Hin).
  exists n, m, i1, i2, rest. split; [| exact Hin].
  eapply Permutation_trans; [apply Permutation_sym; exact Hperm | exact Hp].
Qed.

Lemma open_redex_perm : forall body body',
  Permutation body body' -> open_redex body -> open_redex body'.
Proof.
  intros body body' Hperm (n & inner & rest & Hp).
  exists n, inner, rest.
  eapply Permutation_trans; [apply Permutation_sym; exact Hperm | exact Hp].
Qed.

Lemma out_redex_perm : forall m body body',
  Permutation body body' -> out_redex m body -> out_redex m body'.
Proof.
  intros m body body' Hperm (n & inner & rest & Hp & Hin).
  exists n, inner, rest. split; [| exact Hin].
  eapply Permutation_trans; [apply Permutation_sym; exact Hperm | exact Hp].
Qed.

(* ------------------------------------------------------------------------------------
   The C-G subset as composite step axioms (alpha-quotient; each documented).
   ------------------------------------------------------------------------------------ *)

Inductive cstep : Config -> Config -> Prop :=
  (* (E-hoist-member) — iterated (Struct Res Par) + alpha at the outer bag seam:
     one member's whole nu-prefix hoists to the configuration prefix.  The alpha
     freshening that discharges `x not in fn(siblings)` is Part 1's supply. *)
  | cs_hoist_member : forall nus pre ks c post,
      cstep (mkCfg nus (pre ++ (ks, c) :: post))
            (mkCfg (nus ++ ks) (pre ++ ([], c) :: post))
  (* (E-hoist-amb) — iterated inner (Struct Res Par) then (Struct Res Amb) + alpha:
     one inner member's nu-prefix hoists through the ambient wall into the outer
     member's prefix. *)
  | cs_hoist_amb : forall nus pre ks n ipre js ic ipost post,
      cstep
        (mkCfg nus (pre ++ (ks, OBase (KAmb n (ipre ++ (js, ic) :: ipost))) :: post))
        (mkCfg nus
           (pre ++ (ks ++ js, OBase (KAmb n (ipre ++ ([], ic) :: ipost))) :: post))
  (* (E-splice) — representational (Struct Par Comm/Assoc): a prefix-free nested-bag
     member dissolves into the outer bag (the HashBag absorbs Par Comm/Assoc, so the
     nested bag is pure representation — AM-2's obligation is that the float NEVER
     produces one, Part 2 + float_canonicalizes). *)
  | cs_splice : forall nus pre l post,
      cstep (mkCfg nus (pre ++ ([], OBag l) :: post))
            (mkCfg nus (pre ++ map (fun p => (fst p, OBase (snd p))) l ++ post))
  (* (E-perm-body) — representational (Struct Par Comm). *)
  | cs_perm_body : forall nus body body',
      Permutation body body' -> cstep (mkCfg nus body) (mkCfg nus body')
  (* (E-perm-nus) — (Struct Res Res). *)
  | cs_perm_nus : forall nus nus' body,
      Permutation nus nus' -> cstep (mkCfg nus body) (mkCfg nus' body).

(* The equivalence closure (refl + trans + both step directions). *)
Inductive cequiv : Config -> Config -> Prop :=
  | ce_refl : forall a, cequiv a a
  | ce_step : forall a b c, cstep a b -> cequiv b c -> cequiv a c
  | ce_back : forall a b c, cstep b a -> cequiv b c -> cequiv a c.

Lemma cequiv_trans : forall a b c, cequiv a b -> cequiv b c -> cequiv a c.
Proof.
  intros a b c Hab. revert c. induction Hab as [a | a x b Hs Hab IH | a x b Hs Hab IH];
    intros c Hbc.
  - exact Hbc.
  - eapply ce_step; [exact Hs | apply IH; exact Hbc].
  - eapply ce_back; [exact Hs | apply IH; exact Hbc].
Qed.

Lemma cequiv_step_1 : forall a b, cstep a b -> cequiv a b.
Proof. intros a b Hs. eapply ce_step; [exact Hs | apply ce_refl]. Qed.

Lemma cequiv_back_1 : forall a b, cstep b a -> cequiv a b.
Proof. intros a b Hs. eapply ce_back; [exact Hs | apply ce_refl]. Qed.

Lemma cequiv_sym : forall a b, cequiv a b -> cequiv b a.
Proof.
  intros a b Hab. induction Hab as [a | a x b Hs Hab IH | a x b Hs Hab IH].
  - apply ce_refl.
  - eapply cequiv_trans; [exact IH | apply cequiv_back_1; exact Hs].
  - eapply cequiv_trans; [exact IH | apply cequiv_step_1; exact Hs].
Qed.

(* ------------------------------------------------------------------------------------
   flat_map respects Permutation (the transport workhorse).
   ------------------------------------------------------------------------------------ *)

Lemma Permutation_flat_map :
  forall (A B : Type) (f : A -> list B) (l l' : list A),
    Permutation l l' -> Permutation (flat_map f l) (flat_map f l').
Proof.
  intros A B f l l' Hperm.
  induction Hperm as [| x l1 l2 Hp IH | x y l1 | l1 l2 l3 H12 IH12 H23 IH23].
  - apply Permutation_refl.
  - simpl. apply Permutation_app_head. exact IH.
  - simpl. rewrite !app_assoc. apply Permutation_app_tail.
    apply Permutation_app_comm.
  - eapply Permutation_trans; [exact IH12 | exact IH23].
Qed.

(* ------------------------------------------------------------------------------------
   Step invariance: every cstep permutes the FLOATED body (usually leaves it equal).
   ------------------------------------------------------------------------------------ *)

(* The floated members of one outer member do not depend on its own nu-prefix. *)
Lemma float_omem_snd_prefix_irrelevant : forall ks ks' c,
  snd (float_omem (ks, c)) = snd (float_omem (ks', c)).
Proof. intros ks ks' c. destruct c; reflexivity. Qed.

(* Floating the spliced (OBase-wrapped) bag members yields exactly the bag's own
   per-member floats: singleton flat_map collapses to map. *)
Lemma flat_map_float_of_based : forall l,
  flat_map (fun m => snd (float_omem m)) (map (fun p => (fst p, OBase (snd p))) l)
  = map (fun p => snd (float_bmem p)) l.
Proof.
  induction l as [| p l' IH]; cbn.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma step_float_body_perm : forall a b,
  cstep a b -> Permutation (c_body (float a)) (c_body (float b)).
Proof.
  intros a b Hs. destruct Hs as
    [nus pre ks c post
    | nus pre ks n ipre js ic ipost post
    | nus pre l post
    | nus body body' Hp
    | nus nus' body Hp]; simpl.
  - (* hoist-member: floated bodies are EQUAL (prefixes are discarded rightward). *)
    rewrite !flat_map_app. cbn [flat_map].
    rewrite (float_omem_snd_prefix_irrelevant ks [] c).
    apply Permutation_refl.
  - (* hoist-amb: the stripped inner cores agree. *)
    rewrite !flat_map_app. cbn.
    rewrite !map_app. cbn.
    apply Permutation_refl.
  - (* splice: singleton flat_map over the mapped members = the bag's own floats. *)
    rewrite !flat_map_app. cbn [flat_map].
    rewrite flat_map_float_of_based. cbn.
    apply Permutation_refl.
  - (* perm-body *)
    apply Permutation_flat_map. exact Hp.
  - (* perm-nus *)
    apply Permutation_refl.
Qed.

Lemma cequiv_float_body_perm : forall a b,
  cequiv a b -> Permutation (c_body (float a)) (c_body (float b)).
Proof.
  intros a b Hab. induction Hab as [a | a x b Hs Hab IH | a x b Hs Hab IH].
  - apply Permutation_refl.
  - eapply Permutation_trans; [apply step_float_body_perm; exact Hs | exact IH].
  - eapply Permutation_trans;
      [apply Permutation_sym; apply step_float_body_perm; exact Hs | exact IH].
Qed.

(* ------------------------------------------------------------------------------------
   Monotone exposure: the float never destroys a syntactically present redex.
   ------------------------------------------------------------------------------------ *)

Lemma float_body_of : forall nus body,
  c_body (float (mkCfg nus body)) = flat_map (fun m => snd (float_omem m)) body.
Proof. reflexivity. Qed.

Lemma in_redex_monotone : forall nus body,
  in_redex body -> in_redex (c_body (float (mkCfg nus body))).
Proof.
  intros nus body (n & m & i1 & i2 & rest & Hp & Hin).
  rewrite float_body_of.
  exists n, m, (map strip_imem i1), (map strip_imem i2),
         (flat_map (fun x => snd (float_omem x)) rest).
  split.
  - eapply Permutation_trans;
      [apply Permutation_flat_map; exact Hp |].
    simpl. apply Permutation_refl.
  - change ([], ICap CIn m) with (strip_imem ([], ICap CIn m)).
    apply in_map. exact Hin.
Qed.

Lemma open_redex_monotone : forall nus body,
  open_redex body -> open_redex (c_body (float (mkCfg nus body))).
Proof.
  intros nus body (n & inner & rest & Hp).
  rewrite float_body_of.
  exists n, (map strip_imem inner),
         (flat_map (fun x => snd (float_omem x)) rest).
  eapply Permutation_trans; [apply Permutation_flat_map; exact Hp |].
  simpl. apply Permutation_refl.
Qed.

Lemma out_redex_monotone : forall m nus body,
  out_redex m body -> out_redex m (c_body (float (mkCfg nus body))).
Proof.
  intros m nus body (n & inner & rest & Hp & Hin).
  rewrite float_body_of.
  exists n, (map strip_imem inner),
         (flat_map (fun x => snd (float_omem x)) rest).
  split.
  - eapply Permutation_trans;
      [apply Permutation_flat_map; exact Hp |].
    simpl. apply Permutation_refl.
  - change ([], ICap COut m) with (strip_imem ([], ICap COut m)).
    apply in_map. exact Hin.
Qed.

(* ------------------------------------------------------------------------------------
   Reachability: the float is a cequiv chain (each move a documented subset axiom).
   ------------------------------------------------------------------------------------ *)

Lemma reach_amb_inners : forall inner nus pre ks n ipre post,
  cequiv
    (mkCfg nus (pre ++ (ks, OBase (KAmb n (ipre ++ inner))) :: post))
    (mkCfg nus
       (pre ++ (ks ++ flat_map fst inner,
                OBase (KAmb n (ipre ++ map strip_imem inner))) :: post)).
Proof.
  induction inner as [| [js ic] inner' IH]; intros nus pre ks n ipre post; simpl.
  - rewrite !app_nil_r. apply ce_refl.
  - eapply cequiv_trans.
    + apply cequiv_step_1.
      apply (cs_hoist_amb nus pre ks n ipre js ic inner' post).
    + specialize (IH nus pre (ks ++ js) n (ipre ++ [([], ic)]) post).
      rewrite <- !app_assoc in IH. simpl in IH.
      exact IH.
Qed.

Lemma reach_base_member : forall nus pre ks b post,
  cequiv
    (mkCfg nus (pre ++ (ks, OBase b) :: post))
    (mkCfg (nus ++ ks ++ fst (float_bcore b))
           (pre ++ ([], OBase (snd (float_bcore b))) :: post)).
Proof.
  intros nus pre ks b post. destruct b as [n inner | c n | k].
  - (* KAmb: hoist the inner prefixes into the member prefix, then hoist it. *)
    eapply cequiv_trans.
    + exact (reach_amb_inners inner nus pre ks n [] post).
    + simpl. apply cequiv_step_1.
      exact (cs_hoist_member nus pre (ks ++ flat_map fst inner)
               (OBase (KAmb n (map strip_imem inner))) post).
  - simpl. rewrite app_nil_r. apply cequiv_step_1.
    exact (cs_hoist_member nus pre ks (OBase (KCap c n)) post).
  - simpl. rewrite app_nil_r. apply cequiv_step_1.
    exact (cs_hoist_member nus pre ks (OBase (KOpq k)) post).
Qed.

Lemma reach_bag_members : forall l nus pre post,
  cequiv
    (mkCfg nus (pre ++ map (fun p => (fst p, OBase (snd p))) l ++ post))
    (mkCfg (nus ++ flat_map (fun p => fst (float_bmem p)) l)
           (pre ++ map (fun p => snd (float_bmem p)) l ++ post)).
Proof.
  induction l as [| [ks b] l' IH]; intros nus pre post; simpl.
  - rewrite app_nil_r. apply ce_refl.
  - eapply cequiv_trans.
    + exact (reach_base_member nus pre ks b (map (fun p => (fst p, OBase (snd p))) l' ++ post)).
    + specialize (IH (nus ++ ks ++ fst (float_bcore b))
                     (pre ++ [([], OBase (snd (float_bcore b)))]) post).
      rewrite <- !app_assoc in IH. simpl in IH.
      rewrite <- !app_assoc.
      exact IH.
Qed.

Lemma reach_member : forall nus pre m post,
  cequiv
    (mkCfg nus (pre ++ m :: post))
    (mkCfg (nus ++ fst (float_omem m)) (pre ++ snd (float_omem m) ++ post)).
Proof.
  intros nus pre [ks c] post. destruct c as [b | l].
  - simpl. eapply cequiv_trans.
    + exact (reach_base_member nus pre ks b post).
    + rewrite app_assoc. apply ce_refl.
  - (* OBag: hoist own prefix, splice, then process the spliced members. *)
    simpl. eapply cequiv_trans.
    + apply cequiv_step_1. exact (cs_hoist_member nus pre ks (OBag l) post).
    + eapply cequiv_trans.
      * apply cequiv_step_1. exact (cs_splice (nus ++ ks) pre l post).
      * eapply cequiv_trans.
        -- exact (reach_bag_members l (nus ++ ks) pre post).
        -- rewrite <- app_assoc. apply ce_refl.
Qed.

Lemma reach_body : forall body nus done,
  cequiv
    (mkCfg nus (done ++ body))
    (mkCfg (nus ++ flat_map (fun m => fst (float_omem m)) body)
           (done ++ flat_map (fun m => snd (float_omem m)) body)).
Proof.
  induction body as [| m body' IH]; intros nus done; simpl.
  - rewrite !app_nil_r. apply ce_refl.
  - eapply cequiv_trans.
    + exact (reach_member nus done m body').
    + specialize (IH (nus ++ fst (float_omem m)) (done ++ snd (float_omem m))).
      rewrite <- !app_assoc in IH.
      exact IH.
Qed.

(* The float is reachable through the subset: cfg == float cfg. *)
Theorem float_reachable : forall cfg, cequiv cfg (float cfg).
Proof.
  intros [nus body]. unfold float. simpl.
  exact (reach_body body nus []).
Qed.

(* ------------------------------------------------------------------------------------
   THE EXPOSURE THEOREMS (design v2 section 3.3): in float-canonical flat form, a
   bag/nested redex exists modulo the C-G subset IFF it exists syntactically.
   ------------------------------------------------------------------------------------ *)

Theorem float_nf_exposes_redexes_in : forall cfg,
  (exists cfg', cequiv cfg cfg' /\ in_redex (c_body cfg'))
  <-> in_redex (c_body (float cfg)).
Proof.
  intros cfg. split.
  - intros (cfg' & Heq & Hred).
    destruct cfg' as [nus' body']. simpl in Hred.
    apply (in_redex_perm _ _ (Permutation_sym
             (cequiv_float_body_perm _ _ Heq))).
    exact (in_redex_monotone nus' body' Hred).
  - intros Hred. exists (float cfg). split.
    + apply float_reachable.
    + exact Hred.
Qed.

Theorem float_nf_exposes_redexes_open : forall cfg,
  (exists cfg', cequiv cfg cfg' /\ open_redex (c_body cfg'))
  <-> open_redex (c_body (float cfg)).
Proof.
  intros cfg. split.
  - intros (cfg' & Heq & Hred).
    destruct cfg' as [nus' body']. simpl in Hred.
    apply (open_redex_perm _ _ (Permutation_sym
             (cequiv_float_body_perm _ _ Heq))).
    exact (open_redex_monotone nus' body' Hred).
  - intros Hred. exists (float cfg). split.
    + apply float_reachable.
    + exact Hred.
Qed.

(* A-S5.4b: the Out-redex exposure — over the ENCLOSING AMBIENT `m`'s body configuration (the
   per-level reading documented at `out_redex`): an Out-redex below `m`'s root exists modulo the
   C-G subset IFF it is syntactically present in the float normal form of `m`'s body. With the
   In and Open exposures this completes design v2 section 3.3 over all three rewrite families of
   the REDECLARED (Red Out) rule set. *)
Theorem float_nf_exposes_redexes_out : forall m cfg,
  (exists cfg', cequiv cfg cfg' /\ out_redex m (c_body cfg'))
  <-> out_redex m (c_body (float cfg)).
Proof.
  intros m cfg. split.
  - intros (cfg' & Heq & Hred).
    destruct cfg' as [nus' body']. simpl in Hred.
    apply (out_redex_perm m _ _ (Permutation_sym
             (cequiv_float_body_perm _ _ Heq))).
    exact (out_redex_monotone m nus' body' Hred).
  - intros Hred. exists (float cfg). split.
    + apply float_reachable.
    + exact Hred.
Qed.

(* =====================================================================================
   Part 4 — NewComm (Struct Res Res) permutation invariance: the nu-prefix order never
   affects exposure, so the implementation's <=6-binder canonical-run DISPLAY cap
   (binder_congruence.rs Heap-permutation ordering; encounter order beyond) is
   display-only — it cannot hide or reveal a redex.
   ===================================================================================== *)

Theorem newcomm_permutation_redex_invariance : forall nus nus' body,
  Permutation nus nus' ->
  cequiv (mkCfg nus body) (mkCfg nus' body)
  /\ (in_redex (c_body (float (mkCfg nus body)))
      <-> in_redex (c_body (float (mkCfg nus' body))))
  /\ (open_redex (c_body (float (mkCfg nus body)))
      <-> open_redex (c_body (float (mkCfg nus' body))))
  /\ (forall m,
        out_redex m (c_body (float (mkCfg nus body)))
        <-> out_redex m (c_body (float (mkCfg nus' body)))).
Proof.
  intros nus nus' body Hp. split; [| split; [| split]].
  - apply cequiv_step_1. apply cs_perm_nus. exact Hp.
  - rewrite !float_body_of. tauto.
  - rewrite !float_body_of. tauto.
  - intros m. rewrite !float_body_of. tauto.
Qed.

(* =====================================================================================
   Non-vacuity witnesses: the two mandatory A-S5.4a pin subjects, as model instances.
   ===================================================================================== *)

(* The F1 counterexample subject `{ new(x, n[{in(m,0)}]) | m[x[0]] }`: the nu hides the
   In-redex syntactically (member 0 is nu-prefixed), and the float exposes it. *)
Definition f1_cfg : Config :=
  mkCfg []
    [ ([7], OBase (KAmb 1 [([], ICap CIn 2)]))   (* new(x=7, n=1[{in(m=2).0}]) *)
    ; ([],  OBase (KAmb 2 [([], IOpq 0)])) ].    (* m=2[ x[0] — opaque here ] *)

Example f1_subject_exposes_in_redex_after_float :
  in_redex (c_body (float f1_cfg)).
Proof.
  unfold f1_cfg. rewrite float_body_of. simpl.
  exists 1, 2, [([], ICap CIn 2)], [([], IOpq 0)], [].
  split.
  - apply Permutation_refl.
  - left. reflexivity.
Qed.

(* The AM-2 bag-bodied-nu subject `{ new(x, { n[{in(m,0)}] | q }) | m[0] }`: the nu body
   is ITSELF a bag; the float SPLICES it (never a nested element), exposing the
   In-redex against the sibling m[0] — and by float_canonicalizes the result is FLAT. *)
Definition am2_cfg : Config :=
  mkCfg []
    [ ([7], OBag [ ([], KAmb 1 [([], ICap CIn 2)])  (* n[{in(m,0)}] *)
                 ; ([], KOpq 9) ])                   (* q *)
    ; ([], OBase (KAmb 2 [])) ].                     (* m[0] *)

Example am2_subject_exposes_in_redex_after_float :
  in_redex (c_body (float am2_cfg)).
Proof.
  unfold am2_cfg. rewrite float_body_of. simpl.
  exists 1, 2, [([], ICap CIn 2)], [], [([], OBase (KOpq 9))].
  split.
  - (* [amb1; opq; amb2] ~ [amb1; amb2; opq] *)
    apply perm_skip. apply perm_swap.
  - left. reflexivity.
Qed.

Example am2_subject_floats_flat : canonical (float am2_cfg).
Proof. apply float_canonicalizes. Qed.

(* The A-S5.4b Out-redex witness — the SINGLETON body of the enclosing ambient `m = 2`:
   `m[{ new(x, n[{out(m).-}]) }]`.  The nu hides the moving ambient `n[...]` syntactically
   (member 0 is nu-prefixed), the float hoists it, and the exposed redex has EMPTY rest —
   exactly the redeclaration's empty-rest-legal singleton `m[{n[{out(m,p)}]}]`, which the
   pre-A-S5.4b ejection-shaped rule could never fire. *)
Definition out_singleton_cfg : Config :=
  mkCfg [] [ ([7], OBase (KAmb 1 [([], ICap COut 2)])) ].  (* new(x=7, n=1[{out(m=2).-}]) *)

Example out_singleton_subject_exposes_out_redex_after_float :
  out_redex 2 (c_body (float out_singleton_cfg)).
Proof.
  unfold out_singleton_cfg. rewrite float_body_of. simpl.
  exists 1, [([], ICap COut 2)], [].
  split.
  - apply Permutation_refl.
  - left. reflexivity.
Qed.

(* Zero-admission confirmation. *)
Print Assumptions freshening_totality.
Print Assumptions float_preserves_bag_flatness.
Print Assumptions float_canonicalizes.
Print Assumptions float_nf_exposes_redexes_in.
Print Assumptions float_nf_exposes_redexes_open.
Print Assumptions float_nf_exposes_redexes_out.
Print Assumptions newcomm_permutation_redex_invariance.
Print Assumptions f1_subject_exposes_in_redex_after_float.
Print Assumptions am2_subject_exposes_in_redex_after_float.
Print Assumptions out_singleton_subject_exposes_out_redex_after_float.
