(** Exact bounded grouping-source descriptor relocation.

    Source: macros/src/gen/runtime/wpda_codegen/prefix.rs, the complete
    grouping_source_infix_hop, grouping_source_projection_hop, and
    grouping_source_categories_for_result bodies. Despite older prose, this
    is NOT a transitive closure: seed I(R) and P(R), call P(R) again, and only
    when that deduplicated u16 roster has length < 4 call I once for each P.
    Direct infix seeds and the resulting second-hop sources are never expanded.

    Existing infix/atomic classification and public BNF normalization remain
    callbacks. Reuse their InfixClassifierProjection, AtomicClassifierProjection,
    and LegacyRuleNormalizationProjection boundaries; this file does not
    reimplement any classifier or reconstruct source grammar. The InfixInfo
    observations reuse ParikhDescriptorProjection and casts reuse the checked
    CategoryCensusProjection model. Rule handles are original ordered indices.

    Events expose category gating, lazy classifier calls, name-position lookup,
    repeated projection calls, and missing-row/index behavior. Callback return
    equality is an explicit adapter obligation; arbitrary effectful/mutating
    callbacks are not certified. All finite source slices/positions fit usize.
    u16 casts deliberately remain modulo 65536, including collisions. Checked
    runtime category-width admission is a separate downstream obligation.
    No allocator/resource policy, parser completeness, or transition-body claim.
*)
From Stdlib Require Import List String Bool Arith Lia Sorting.Sorted.
From PrattailWpdaRuntime Require Import CategoryCensusProjection ParikhDescriptorProjection.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Set Implicit Arguments.

Module GroupingSourceDescriptorProjection.
Module C := CategoryCensusProjection.CategoryCensusProjection.
Module P := ParikhDescriptorProjection.ParikhDescriptorProjection.

Definition cast_u16 := C.cast_u16.

(** BTreeSet<u16>'s mathematical sorted, duplicate-free insertion. *)
Fixpoint insert (value : nat) (values : list nat) := match values with
| [] => [value]
| head :: rest => match Nat.compare value head with
  | Eq => values | Lt => value :: values | Gt => head :: insert value rest end end.
Definition insert_all values into := fold_left (fun acc value => insert value acc) values into.

Fixpoint first_position name names : option nat := match names with
| [] => None
| head :: rest => if String.eqb head name then Some 0
  else option_map S (first_position name rest) end.

Inductive Event :=
| CategoryAt (index : nat) | CategoryOf (rule : nat)
| ClassifyInfix (rule : nat) | ClassifyAtomic (rule : nat)
| SourcePosition (name : string) | PerCategoryAt (index : nat).
Record Reader := {
  category_of : nat -> string;
  classify_infix : nat -> option P.InfixInfo;
  projection_source : nat -> option string
}.
Definition ReaderLaw old new :=
  (forall h, category_of new h = category_of old h) /\
  (forall h, classify_infix new h = classify_infix old h) /\
  (forall h, projection_source new h = projection_source old h).

Record Acc := { members : list nat; observations : list Event }.
Definition acc values trace := {| members := values; observations := trace |}.
Definition observe event st := acc (members st) (observations st ++ [event]).
Inductive Outcome (A : Type) := Done (value : A) | IndexFault (index : nat) (trace : list Event).
Arguments Done {A} _.
Arguments IndexFault {A} _ _.

(** Position comparison is BEFORE narrowing. A distinct large index may wrap
    to the hop's current category and is nevertheless inserted. *)
Definition retain_index current found values :=
  if Nat.eqb found current then values else insert (cast_u16 found) values.
Definition retain_source cats current name st :=
  let traced := observe (SourcePosition name) st in
  match first_position name cats with
  | None => traced
  | Some found => acc (retain_index current found (members traced)) (observations traced)
  end.

Fixpoint infix_scan reader cats current result rules st := match rules with
| [] => st
| rule :: rest =>
  let gated := observe (CategoryOf rule) st in
  if negb (String.eqb (category_of reader rule) result)
  then infix_scan reader cats current result rest gated
  else let called := observe (ClassifyInfix rule) gated in
    let next := match classify_infix reader rule with
    | None => called
    | Some info => if P.cross_category info &&
        negb (String.eqb (P.operand_category info) (P.result_category info))
      then retain_source cats current (P.operand_category info) called else called end in
    infix_scan reader cats current result rest next end.

Definition infix_hop reader cats rules current st :=
  let traced := observe (CategoryAt current) st in
  match nth_error cats current with
  | None => IndexFault current (observations traced)
  | Some result => Done (infix_scan reader cats current result rules traced) end.

Fixpoint projection_scan reader cats current rules st := match rules with
| [] => st
| rule :: rest =>
  let called := observe (ClassifyAtomic rule) st in
  let next := match projection_source reader rule with
    | None => called | Some name => retain_source cats current name called end in
  projection_scan reader cats current rest next end.

Definition projection_hop reader cats rows current st :=
  let traced := observe (PerCategoryAt current) st in
  match nth_error rows current with
  | None => traced
  | Some rules => projection_scan reader cats current rules traced end.

Record State := {
  closure : list nat;
  visited : list nat;
  emitted : list Event
}.
Definition state reached seen trace := {| closure := reached; visited := seen; emitted := trace |}.
Definition merge_hop hop st := state
  (insert_all (members hop) (closure st))
  (insert_all (members hop) (visited st)) (observations hop).

(** A finite fold over the already computed projection roster. No newly found
    member is enqueued; visited is written, but is NEVER used as a guard. *)
Fixpoint expand_projection_sources reader cats rules sources st := match sources with
| [] => Done st
| source :: rest => match infix_hop reader cats rules source (acc [] (emitted st)) with
  | IndexFault index trace => IndexFault index trace
  | Done hop => expand_projection_sources reader cats rules rest (merge_hop hop st)
  end end.

Record Result := { sources : list nat; final_visited : list nat; trace : list Event }.
Definition finish result st := {| sources := cast_u16 result :: closure st;
  final_visited := visited st; trace := emitted st |}.

Definition derive reader cats rules rows result : Outcome Result :=
  match infix_hop reader cats rules result (acc [] []) with
  | IndexFault index trace => IndexFault index trace
  | Done infix_seed =>
    let seed := projection_hop reader cats rows result infix_seed in
    let projections := projection_hop reader cats rows result (acc [] (observations seed)) in
    let initialized := state (insert_all (members seed) [])
      (insert_all (members seed) (insert (cast_u16 result) [])) (observations projections) in
    if Nat.ltb (List.length (members projections)) 4 then
      match expand_projection_sources reader cats rules (members projections) initialized with
      | IndexFault index trace => IndexFault index trace
      | Done final => Done (finish result final) end
    else Done (finish result initialized)
  end.

Lemma insert_membership : forall value values item,
  In item (insert value values) <-> item = value \/ In item values.
Proof.
  intros value values; induction values as [|head rest IH]; intros item; cbn.
  - intuition congruence.
  - destruct (Nat.compare value head) eqn:E; cbn.
    + apply Nat.compare_eq_iff in E; subst; intuition congruence.
    + intuition congruence.
    + rewrite IH; intuition congruence.
Qed.

Lemma insert_sorted : forall value values,
  StronglySorted Nat.lt values -> StronglySorted Nat.lt (insert value values).
Proof.
  intros value values Sorted; induction Sorted as [|head rest Tail IH All]; cbn.
  - repeat constructor.
  - destruct (Nat.compare value head) eqn:E.
    + constructor; assumption.
    + apply Nat.compare_lt_iff in E. constructor.
      * constructor; assumption.
      * constructor; [exact E|]. eapply Forall_impl; [|exact All]. intros; lia.
    + apply Nat.compare_gt_iff in E. constructor; [exact IH|].
      apply Forall_forall; intros item Member. apply insert_membership in Member.
      destruct Member as [->|Member]; [exact E|]. now apply (proj1 (Forall_forall _ _) All).
Qed.

Lemma insert_all_sorted : forall values initial,
  StronglySorted Nat.lt initial -> StronglySorted Nat.lt (insert_all values initial).
Proof.
  induction values as [|value rest IH]; intros initial Sorted; cbn; [exact Sorted|].
  apply IH, insert_sorted; exact Sorted.
Qed.

Lemma first_position_head : forall name rest, first_position name (name :: rest) = Some 0.
Proof. intros; cbn; now rewrite String.eqb_refl. Qed.

Lemma infix_scan_substitution : forall old new,
  ReaderLaw old new -> forall cats current result rules st,
  infix_scan new cats current result rules st = infix_scan old cats current result rules st.
Proof.
  intros old new [Category [Infix Projection]] cats current result rules.
  induction rules as [|rule rest IH]; intros st; cbn; [reflexivity|].
  rewrite Category. destruct (negb (String.eqb (category_of old rule) result)); [apply IH|].
  rewrite Infix. apply IH.
Qed.
Lemma infix_hop_substitution : forall old new,
  ReaderLaw old new -> forall cats rules current st,
  infix_hop new cats rules current st = infix_hop old cats rules current st.
Proof.
  intros old new Law cats rules current st; unfold infix_hop.
  destruct (nth_error cats current); [rewrite (infix_scan_substitution Law)|]; reflexivity.
Qed.
Lemma projection_scan_substitution : forall old new,
  ReaderLaw old new -> forall cats current rules st,
  projection_scan new cats current rules st = projection_scan old cats current rules st.
Proof.
  intros old new [Category [Infix Projection]] cats current rules.
  induction rules as [|rule rest IH]; intros st; cbn; [reflexivity|].
  rewrite Projection. apply IH.
Qed.
Lemma projection_hop_substitution : forall old new,
  ReaderLaw old new -> forall cats rows current st,
  projection_hop new cats rows current st = projection_hop old cats rows current st.
Proof.
  intros old new Law cats rows current st; unfold projection_hop.
  destruct (nth_error rows current); [apply projection_scan_substitution|reflexivity]; exact Law.
Qed.
Lemma expansion_substitution : forall old new,
  ReaderLaw old new -> forall cats rules roster st,
  expand_projection_sources new cats rules roster st =
  expand_projection_sources old cats rules roster st.
Proof.
  intros old new Law cats rules roster; induction roster as [|source rest IH]; intros st; cbn.
  - reflexivity.
  - rewrite (infix_hop_substitution Law).
    destruct (infix_hop old cats rules source (acc [] (emitted st))); [apply IH|reflexivity].
Qed.

Theorem source_accessor_relocation_preserves_descriptors_faults_and_callback_order :
  forall old new, ReaderLaw old new -> forall cats rules rows result,
  derive new cats rules rows result = derive old cats rules rows result.
Proof.
  intros old new Law cats rules rows result; unfold derive.
  rewrite (infix_hop_substitution Law).
  destruct (infix_hop old cats rules result (acc [] [])); [|reflexivity].
  rewrite ! (projection_hop_substitution Law).
  cbn zeta.
  match goal with |- context [if ?test then _ else _] => destruct test end;
    [rewrite (expansion_substitution Law)|]; reflexivity.
Qed.

Theorem rejected_result_rule_skips_infix_callback : forall reader cats current result rule rest st,
  category_of reader rule <> result ->
  infix_scan reader cats current result (rule :: rest) st =
  infix_scan reader cats current result rest (observe (CategoryOf rule) st).
Proof.
  intros reader cats current result rule rest st Different; cbn.
  apply String.eqb_neq in Different. now rewrite Different.
Qed.
Theorem absent_per_category_row_does_not_index_categories : forall reader cats rows current st,
  nth_error rows current = None ->
  projection_hop reader cats rows current st = observe (PerCategoryAt current) st.
Proof. intros; unfold projection_hop; now rewrite H. Qed.
Theorem missing_category_faults_before_rule_classification : forall reader cats rules current st,
  nth_error cats current = None -> infix_hop reader cats rules current st =
  IndexFault current (observations st ++ [CategoryAt current]).
Proof. intros; unfold infix_hop; now rewrite H. Qed.
Theorem hop_self_exclusion_is_before_cast : forall current values,
  retain_index current current values = values.
Proof. intros; unfold retain_index; now rewrite Nat.eqb_refl. Qed.
Theorem result_is_always_first_on_success : forall reader cats rules rows current output,
  derive reader cats rules rows current = Done output ->
  exists tail, sources output = cast_u16 current :: tail.
Proof.
  intros reader cats rules rows current output H; unfold derive in H.
  destruct (infix_hop reader cats rules current (acc [] [])); [|discriminate].
  cbn zeta in H.
  match type of H with context [if ?test then _ else _] => destruct test end.
  - match type of H with context [expand_projection_sources ?r ?c ?rules ?roster ?st] =>
      destruct (expand_projection_sources r c rules roster st) end;
      inversion H; subst; eexists; reflexivity.
  - inversion H; subst; eexists; reflexivity.
Qed.
Theorem cast_domain : forall index, cast_u16 index < 65536.
Proof. apply C.cast_always_u16. Qed.

(** Concrete schedule witnesses; handles retain classifier identity. *)
Definition info operand result := {| P.cross_category := true; P.operand_category := operand;
  P.result_category := result; P.terminal := "+" |}.
Definition example_reader := {| category_of := fun rule =>
    match rule with 0 => "R" | 1 => "D" | 2 => "P" | 3 => "Q" | _ => "R" end;
  classify_infix := fun rule => match rule with
    | 0 => Some (info "D" "R") | 1 => Some (info "E" "D")
    | 2 => Some (info "Q" "P") | 3 => Some (info "F" "Q") | _ => None end;
  projection_source := fun rule => match rule with 4 => Some "P" | 5 => Some "U" | _ => None end |}.
Definition observe_sources outcome := match outcome with Done output => Some (sources output)
  | IndexFault _ _ => None end.

Example bounded_schedule_is_not_transitive :
  observe_sources (derive example_reader ["R";"P";"Q";"D";"E";"F";"U"]
    [0;1;2;3] [[4];[5]] 0) = Some [0;1;2;3].
Proof. vm_compute; reflexivity. Qed.
Example both_projection_passes_are_observed :
  match derive example_reader ["R";"P";"Q";"D";"E";"F";"U"] [0;1;2;3] [[4];[5]] 0 with
  | Done output => trace output =
    [CategoryAt 0; CategoryOf 0; ClassifyInfix 0; SourcePosition "D";
     CategoryOf 1; CategoryOf 2; CategoryOf 3;
     PerCategoryAt 0; ClassifyAtomic 4; SourcePosition "P";
     PerCategoryAt 0; ClassifyAtomic 4; SourcePosition "P";
     CategoryAt 1; CategoryOf 0; CategoryOf 1; CategoryOf 2;
     ClassifyInfix 2; SourcePosition "Q"; CategoryOf 3]
  | _ => False end.
Proof. vm_compute; reflexivity. Qed.
Definition cyclic_reader := {| category_of := fun _ => "P";
  classify_infix := fun _ => Some (info "R" "P");
  projection_source := fun _ => Some "P" |}.
Example primary_can_repeat_despite_visited :
  observe_sources (derive cyclic_reader ["R";"P"] [0] [[1]] 0) = Some [0;0;1].
Proof. vm_compute; reflexivity. Qed.
Example distinct_large_source_wraps_to_primary : retain_index 0 65536 [] = [0].
Proof. vm_compute; reflexivity. Qed.
Example first_duplicate_name_wins : first_position "P" ["R";"P";"P"] = Some 1.
Proof. reflexivity. Qed.
Definition hub_reader := {| category_of := fun _ => "P";
  classify_infix := fun _ => Some (info "U" "P");
  projection_source := fun rule => match rule with
    | 0 => Some "P" | 1 => Some "Q" | 2 => Some "S" | 3 => Some "T" | _ => None end |}.
Example three_distinct_projection_sources_expand :
  observe_sources (derive hub_reader ["R";"P";"Q";"S";"T";"U"]
    [4] [[0;1;2;0;0]] 0) = Some [0;1;2;3;5].
Proof. vm_compute; reflexivity. Qed.
Example four_distinct_projection_sources_do_not_expand :
  observe_sources (derive hub_reader ["R";"P";"Q";"S";"T";"U"]
    [4] [[0;1;2;3]] 0) = Some [0;1;2;3;4].
Proof. vm_compute; reflexivity. Qed.

Print Assumptions insert_sorted.
Print Assumptions insert_all_sorted.
Print Assumptions source_accessor_relocation_preserves_descriptors_faults_and_callback_order.
Print Assumptions rejected_result_rule_skips_infix_callback.
Print Assumptions absent_per_category_row_does_not_index_categories.
Print Assumptions missing_category_faults_before_rule_classification.
Print Assumptions hop_self_exclusion_is_before_cast.
Print Assumptions result_is_always_first_on_success.
Print Assumptions cast_domain.
Print Assumptions bounded_schedule_is_not_transitive.
Print Assumptions both_projection_passes_are_observed.
Print Assumptions primary_can_repeat_despite_visited.
Print Assumptions distinct_large_source_wraps_to_primary.
Print Assumptions three_distinct_projection_sources_expand.
Print Assumptions four_distinct_projection_sources_do_not_expand.
End GroupingSourceDescriptorProjection.
