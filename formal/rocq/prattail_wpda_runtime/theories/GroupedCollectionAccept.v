(*
 * GroupedCollectionAccept: the model + soundness for the grouped-collection
 * EOI-accept fix (`WpdaWalker::semantic_root_accepts_at_cursor` +
 * `structural_group_open_pos`, prattail/src/wpda_walker.rs, 2026-07-08).
 *
 * GROUND TRUTH (trace-proven, `Proc::parse_via_wpda("([3])")` on a LINEAR token
 * source):
 *   A COLLECTION root (List/Bag/Map/Set/Pathmap and its transparent cast wrapper)
 *   carries a DEGENERATE zero-width SPPF span `[p, p]` where `p` is the position
 *   right AFTER its closing delimiter — its sole child is the arena-backed,
 *   span-less `CollectionId`, so the fire-site span derivation
 *   `lo = children[0].span_lo().unwrap_or(hi)` collapses `lo` onto `hi = cursor.pos`.
 *   The delimiter-window obligation `semantic_root_accepts_at_cursor` then treats
 *   the collection's OWN content tokens (`[`, `3`, `]`) as a "prefix that must be
 *   all open-delimiters" and REJECTS the valid grouped collection `([3])`.
 *   (`([Nil])` "worked" only by the accident of routing through a
 *   `LatticeTokenSource`, where the check short-circuits to `true`.)
 *
 * THE FIX: when the root is zero-width (`root_lo = root_hi`, the collection-root
 * convention), recover its TRUE left boundary by matching the balanced
 * structural-delimiter group that terminates at `root_hi` (`structural_group_open_pos`,
 * a backward depth-counting scan over the SAME grammar-derived
 * `is_structural_{open,close}_delimiter` classification), then validate the window
 * against that recovered boundary.
 *
 * This file models the token stream around the root as a `list Delim`
 * (Open/Close/Content = the structural-open / structural-close / interior
 * classification), transcribes the backward matcher `bmatch` (= the Rust loop) as
 * it scans the reversed prefix, and proves:
 *
 * THEOREMS (all admission-free; audited by `Print Assumptions`, each must print
 * "Closed under the global context"):
 *   T1 bmatch_complete       — a genuinely wrapped group `Grp grp` (in token order)
 *      is MATCHED by the backward scan for ANY following suffix, recovering exactly
 *      `length grp`. So the fix ACCEPTS real grouped collections — the bug it fixes.
 *   T2 bmatch_balanced       — SOUNDNESS of the matcher: if the scan returns
 *      `Some k` (starting from a closing delimiter at depth 0), the recovered
 *      `k`-token region is net-BALANCED (`net = 0`, equal opens and closes). The
 *      recovered `[lo, root_hi)` really is a delimiter-balanced region — the scan
 *      never fabricates a spurious boundary that would let loose brackets through.
 *   T3 leading_content_rejected / trailing_content_rejected — a prefix / suffix
 *      carrying a loose `Content` token FAILS `all_open` / `all_close`: the window
 *      checks reject any non-delimiter garbage outside the group (no false-accept).
 *   T4 grp_nonempty + all_open_prefix + relaxation_monotone — the recovered
 *      boundary `lo` satisfies `lo <= root_hi` (a `Grp` is nonempty) and the
 *      all-open window over the SHORTER recovered prefix is IMPLIED by the pre-fix
 *      full-prefix window: the fix only ever RELAXES (never turns a prior accept
 *      into a reject).
 *
 * TOGETHER: the fix accepts exactly the delimiter-wrapped balanced-collection
 * streams (T1 completeness + T2 matcher-soundness) and rejects any stream with a
 * loose non-delimiter outside the group (T3), while never regressing a
 * previously-accepted parse (T4).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Section GroupedCollectionAccept.

  (* ── The grammar-derived structural classification of a token: a structural
        OPEN delimiter (`(` `[` `{` `{|` `#{` …), a structural CLOSE delimiter
        (`)` `]` `}` `|}` `}#`), or interior CONTENT (a number, ident, `,`, `*`,
        a keyword atom …). Exactly what `is_structural_{open,close}_delimiter`
        decide; the two are disjoint. ── *)
  Inductive Delim : Type := Open | Close | Content.

  Definition is_open  (d : Delim) : bool := match d with Open  => true | _ => false end.
  Definition is_close (d : Delim) : bool := match d with Close => true | _ => false end.

  Definition all_open  (l : list Delim) : bool := forallb is_open  l.
  Definition all_close (l : list Delim) : bool := forallb is_close l.

  (* ── A well-bracketed GROUP: an `Open`, a body of interior content and nested
        groups, then a `Close` — the token shape of a collection literal `[ … ]`
        (and of a `( … )` grouping). `Body` is the interior: any interleaving of
        `Content` tokens and nested `Grp`s. ── *)
  Inductive Grp  : list Delim -> Prop :=
    | Grp_mk : forall body, Body body -> Grp (Open :: body ++ [Close])
  with Body : list Delim -> Prop :=
    | Body_nil     : Body []
    | Body_content : forall b, Body b -> Body (Content :: b)
    | Body_grp     : forall g b, Grp g -> Body b -> Body (g ++ b).

  Scheme Grp_ind'  := Induction for Grp  Sort Prop
  with   Body_ind' := Induction for Body Sort Prop.

  (* ── THE BACKWARD MATCHER (`structural_group_open_pos`, transcribed).
        `rl` is the scanned prefix REVERSED (so `rl`'s head is the token at
        `root_hi - 1`, which the caller guards to be a `Close`). `depth` counts the
        still-open closes seen from the right. Returns the LENGTH of the matched
        group (tokens consumed from the right to return `depth` to 0) — the caller
        sets `effective_lo = root_hi - k`. `Close` pushes depth; `Open` pops (a pop
        to 0 CLOSES the match); `Content` is depth-neutral. A pop at `depth = 0`
        (the Rust `checked_sub` underflow) and running off the left edge yield
        `None`. ── *)
  Fixpoint bmatch (rl : list Delim) (depth : nat) : option nat :=
    match rl with
    | [] => None
    | d :: rest =>
        match d with
        | Close   => option_map S (bmatch rest (S depth))
        | Content => option_map S (bmatch rest depth)
        | Open =>
            match depth with
            | 0 => None
            | S d' =>
                match d' with
                | 0 => Some 1
                | S _ => option_map S (bmatch rest d')
                end
            end
        end
    end.

  (* ═══════════════════════════════════════════════════════════════════════════
     T1 — COMPLETENESS: a `Grp` (token order) is matched by the backward scan.
     ═══════════════════════════════════════════════════════════════════════════ *)

  Lemma rev_grp :
    forall body, rev (Open :: body ++ [Close]) = Close :: (rev body ++ [Open]).
  Proof.
    intros body. simpl. rewrite rev_app_distr. reflexivity.
  Qed.

  (* Kernel: scanning `rev b` (b : Body, net-zero) at a pending depth `S depth`
     over any `tail` leaves the pending depth unchanged and prepends `length b` to
     the consumed count. Mutual structural induction on `Body` (with the `Grp`
     motive supplied for nested groups). *)
  Lemma bmatch_rev_body :
    forall b, Body b ->
      forall depth tail,
        bmatch (rev b ++ tail) (S depth)
          = option_map (fun k => (length b + k)%nat) (bmatch tail (S depth)).
  Proof.
    intros b HB.
    induction HB using Body_ind' with
      (P := fun g (_ : Grp g) =>
              forall depth tail,
                bmatch (rev g ++ tail) (S depth)
                  = option_map (fun k => (length g + k)%nat) (bmatch tail (S depth))).
    - (* Grp: g = Open :: body ++ [Close] *)
      intros depth tail.
      rewrite rev_grp.                       (* (Close :: (rev body ++ [Open])) ++ tail *)
      rewrite <- app_comm_cons.              (* Close :: ((rev body ++ [Open]) ++ tail) *)
      rewrite <- app_assoc.                  (* Close :: (rev body ++ ([Open] ++ tail)) *)
      cbn [bmatch].                          (* head Close: S depth -> S (S depth) *)
      rewrite IHHB.                          (* scan rev body at S (S depth) *)
      cbn [app bmatch].                      (* Open :: tail at S (S depth) -> pop to S depth *)
      destruct (bmatch tail (S depth)) as [k|]; cbn [option_map]; [ | reflexivity ].
      f_equal. cbn [length]. rewrite length_app. cbn [length]. lia.
    - (* Body_nil *)
      intros depth tail. cbn [rev app length].
      destruct (bmatch tail (S depth)) as [k|]; cbn [option_map]; reflexivity.
    - (* Body_content: Content :: b0 *)
      intros depth tail. cbn [rev].         (* (rev b0 ++ [Content]) ++ tail *)
      rewrite <- app_assoc.                  (* rev b0 ++ ([Content] ++ tail) = rev b0 ++ (Content :: tail) *)
      rewrite IHHB.                          (* scan rev b0 at S depth *)
      cbn [app bmatch].                      (* Content :: tail at S depth -> tail at S depth *)
      destruct (bmatch tail (S depth)) as [k|]; cbn [option_map]; [ | reflexivity ].
      f_equal. cbn [length]. lia.
    - (* Body_grp: g0 ++ b0 ; rev (g0 ++ b0) = rev b0 ++ rev g0 *)
      intros depth tail. rewrite rev_app_distr, <- app_assoc.
      rewrite IHHB0.                         (* outer rev b0 (Body IH) *)
      rewrite IHHB.                          (* inner rev g0 (Grp IH) *)
      destruct (bmatch tail (S depth)) as [k|]; cbn [option_map]; [ | reflexivity ].
      f_equal. rewrite length_app. lia.
  Qed.

  Theorem bmatch_complete :
    forall grp, Grp grp ->
      forall suffix, bmatch (rev grp ++ suffix) 0 = Some (length grp).
  Proof.
    intros grp HG suffix. destruct HG as [body HB].
    rewrite rev_grp.                    (* (Close :: (rev body ++ [Open])) ++ suffix *)
    rewrite <- app_comm_cons.           (* Close :: ((rev body ++ [Open]) ++ suffix) *)
    rewrite <- app_assoc.               (* Close :: (rev body ++ ([Open] ++ suffix)) *)
    cbn [bmatch].                       (* head Close: 0 -> 1 *)
    rewrite (bmatch_rev_body body HB 0 ([Open] ++ suffix)).
    (* Open :: suffix at depth 1 -> Some 1 (independent of suffix). *)
    cbn [app bmatch option_map].
    f_equal. cbn [length]. rewrite length_app. cbn [length]. lia.
  Qed.

  (* ═══════════════════════════════════════════════════════════════════════════
     T2 — MATCHER SOUNDNESS: a successful match recovers a BALANCED region. `rdepth`
     is the reverse depth-counter the scan itself maintains (Close pushes, Open
     pops, Content neutral, `pred` never underflows within a live match): the
     matched region drives it back to 0, i.e. every close is matched by an open —
     the region is a balanced bracketing, so the recovered boundary is real.
     ═══════════════════════════════════════════════════════════════════════════ *)

  (* Reverse depth step (mirrors the `bmatch` depth transitions exactly). *)
  Definition rstep (acc : nat) (d : Delim) : nat :=
    match d with
    | Close   => S acc
    | Open    => pred acc
    | Content => acc
    end.

  Definition rdepth (l : list Delim) (init : nat) : nat := fold_left rstep l init.

  Lemma rdepth_cons :
    forall d l init, rdepth (d :: l) init = rdepth l (rstep init d).
  Proof. reflexivity. Qed.

  (* Invariant of the scan: `bmatch rl (S depth) = Some k` means the first `k`
     tokens of `rl` drive the pending depth `S depth` back to exactly 0. Strong
     induction on `length rl`. *)
  Lemma bmatch_rdepth_firstn :
    forall n rl depth k,
      (length rl <= n)%nat ->
      bmatch rl (S depth) = Some k ->
      rdepth (firstn k rl) (S depth) = 0%nat.
  Proof.
    induction n as [|n IHn]; intros rl depth k Hlen Hm.
    - destruct rl; [ cbn in Hm; discriminate | cbn in Hlen; lia ].
    - destruct rl as [|d rest]; [ cbn in Hm; discriminate | ].
      cbn [length] in Hlen.
      destruct d.
      + (* Open *)
        cbn [bmatch] in Hm. destruct depth as [|d'].
        * (* depth = S 0 : Some 1 — one Open cancels the single pending close *)
          injection Hm as <-. cbn [firstn]. rewrite rdepth_cons. reflexivity.
        * (* depth = S (S d') : recurse at S d' *)
          destruct (bmatch rest (S d')) as [k'|] eqn:Hr; cbn [option_map] in Hm;
            [ injection Hm as <- | discriminate ].
          cbn [firstn]. rewrite rdepth_cons. cbn [rstep].
          (* pred (S (S d')) = S d' *)
          eapply IHn; [ lia | exact Hr ].
      + (* Close *)
        cbn [bmatch] in Hm.
        destruct (bmatch rest (S (S depth))) as [k'|] eqn:Hr; cbn [option_map] in Hm;
          [ injection Hm as <- | discriminate ].
        cbn [firstn]. rewrite rdepth_cons. cbn [rstep].
        eapply IHn; [ lia | exact Hr ].
      + (* Content *)
        cbn [bmatch] in Hm.
        destruct (bmatch rest (S depth)) as [k'|] eqn:Hr; cbn [option_map] in Hm;
          [ injection Hm as <- | discriminate ].
        cbn [firstn]. rewrite rdepth_cons. cbn [rstep].
        eapply IHn; [ lia | exact Hr ].
  Qed.

  (* T2: the ENTRY scan (`bmatch rl 0`, guarded so `rl`'s head is the `Close` at
     `root_hi - 1`) returns `Some k` only for a BALANCED matched region — the
     reverse depth-counter, seeded at 0 and pushed to 1 by that head `Close`,
     returns to 0 across the `k` matched tokens. So the recovered `[lo, root_hi)`
     is a genuine balanced bracketing, never a fabricated boundary. *)
  Theorem bmatch_balanced :
    forall rest k,
      bmatch (Close :: rest) 0 = Some k ->
      rdepth (firstn k (Close :: rest)) 0 = 0%nat.
  Proof.
    intros rest k Hm.
    cbn [bmatch] in Hm.
    destruct (bmatch rest 1) as [k'|] eqn:Hr; cbn [option_map] in Hm;
      [ injection Hm as <- | discriminate ].
    cbn [firstn]. rewrite rdepth_cons. cbn [rstep].
    (* head Close: rstep 0 Close = 1; then the first k' tokens of rest drive 1 -> 0 *)
    eapply bmatch_rdepth_firstn; [ reflexivity | exact Hr ].
  Qed.

  (* ═══════════════════════════════════════════════════════════════════════════
     T3 — ANTI-GARBAGE SAFETY: the window checks reject loose non-delimiters.
     ═══════════════════════════════════════════════════════════════════════════ *)

  Theorem leading_content_rejected :
    forall pre, In Content pre -> all_open pre = false.
  Proof.
    intros pre Hin. unfold all_open. apply Bool.not_true_is_false. intro Hall.
    rewrite forallb_forall in Hall. specialize (Hall Content Hin). discriminate.
  Qed.

  Theorem trailing_content_rejected :
    forall suf, In Content suf -> all_close suf = false.
  Proof.
    intros suf Hin. unfold all_close. apply Bool.not_true_is_false. intro Hall.
    rewrite forallb_forall in Hall. specialize (Hall Content Hin). discriminate.
  Qed.

  (* ═══════════════════════════════════════════════════════════════════════════
     T4 — RELAXATION: nonempty group + prefix-closed all-open ⇒ the fix only relaxes.
     ═══════════════════════════════════════════════════════════════════════════ *)

  Lemma grp_nonempty : forall grp, Grp grp -> (1 <= length grp)%nat.
  Proof.
    intros grp HG. destruct HG as [body HB].
    cbn [length]. rewrite length_app. cbn [length]. lia.
  Qed.

  Lemma all_open_prefix :
    forall l1 l2, all_open (l1 ++ l2) = true -> all_open l1 = true.
  Proof.
    intros l1 l2 H. unfold all_open in *. rewrite forallb_app in H.
    apply andb_true_iff in H. tauto.
  Qed.

  (* The recovered prefix `firstn lo pre` (lo <= root_hi) is all-open whenever the
     full pre-fix prefix `pre` was — so any stream the pre-fix check accepted the
     fixed check also accepts (monotone relaxation). *)
  Theorem relaxation_monotone :
    forall pre lo, all_open pre = true -> all_open (firstn lo pre) = true.
  Proof.
    intros pre lo H. rewrite <- (firstn_skipn lo pre) in H.
    eapply all_open_prefix. exact H.
  Qed.

End GroupedCollectionAccept.

(* ── ADMISSION AUDIT — every theorem must print "Closed under the global context". *)
Print Assumptions bmatch_complete.
Print Assumptions bmatch_balanced.
Print Assumptions leading_content_rejected.
Print Assumptions trailing_content_rejected.
Print Assumptions grp_nonempty.
Print Assumptions relaxation_monotone.
