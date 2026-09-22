(** Exact relocation of the remaining mixfix DESCRIPTOR loops, not a new
    operator classifier, trie, emitter, or runtime election mechanism.

    Source ledger (original macro infix.rs / factoring.rs):
    - group_ops_by_cat_terminal visits the supplied binding-power table in its
      existing order. First category position (then u16 cast) is resolved BEFORE
      the result-category/label map lookup. Missing either skips. ALL operator
      kinds enter the BTreeMap; vectors retain original operator occurrences.
    - mixfix_member_items starts with coordinate (2,0,0). Nullary literals use
      (2,0,(d+1) as u8). Repetition stops BEFORE preceding literals; capture stops
      AFTER them. Only then call the original category resolver at the operand
      site. Failure returns the accumulated prefix, truncated=true. A later
      part's preceding literal uses ((part_i as u8)-1), not (part_i-1) as u8.
      The subtraction is executed only when such a preceding literal exists.
    - Enabled construction first observes every grouped key as the absorbability
      set (before kind filtering/capping), then initializes ordinals from prefix
      group counts. Each count is computed even for an out-of-range category;
      repeated category rows overwrite the ordinal slot. Groups visit sorted
      (dispatch category, terminal) keys; filter is_mixfix BEFORE take(max_slice).
    - Build ALL candidates before cast exclusions. Member-items runs before the
      second, complete parts pass for action-entry categories. That pass includes
      parts beyond a truncated member prefix, uses ANY_CAT for repetition/capture,
      and drops the candidate on the first resolver error. total_positions is
      the returned item-prefix length. Fix-B checks only repetition, not capture.
    - Optional rule indexing precedes the cast callback; absent rule means false
      without a callback. Cast exclusion precedes empty-items exclusion. Partition
      remaining candidates by FULL first SpineItem equality, first-seen order.
      Only one root containing the entire original slice of at least two rows
      can form a group. Degraded root members follow initial exclusions.
    - build_mixfix_group keeps first-seen distinct result categories and rejects
      nonuniformity before tree construction. Absorbability tracks the LAST
      operand category, resetting for each candidate, and rejects before Fix-B.
      Fix-B mismatches append diagnostics and CONTINUE. Minima and expected-cat
      union precede the original build_tree(1,...,accept_continue=false) call.
      Interior accepts reject AFTER tree effects. Leaf/root-count diagnostics
      continue; roots[0] indexing follows them. The original coordinate walk
      decides collision rejection before any ordinal lookup or increment.
    - Ending ceilings run after all buckets, recovery collision before u16
      ceiling, over EVERY ordinal slot. The global sink is moved onto the first
      sorted output entry, or a category-zero empty sentinel if necessary.
    - Disabled construction groups/filters/caps identically but invokes no member
      resolver, cast callback, tree, coordinate walk, or ordinal checks. Presence
      rows visit facts, buckets, then groups and retain result-category ownership.

    Full operator/part/repetition records below mirror already-shared Rust
    descriptors. An ordinal handle preserves the borrowed operator occurrence;
    equal field values do not identify two occurrences. Stdlib finite maps model
    ordered BTreeMap observations and HashMap lookup followed by sorted keys;
    this does not replace the Rust containers or equate their allocations.
    The agreed shared Rust destination is wpda_rule_analysis/mixfix.rs.
    Original build_bp_table, build_label_index and feature-gate preparation stay
    in the macro wrapper, at their existing sites. Resolver and cast callbacks
    are the SAME supplied operations, with lazy calls and error/state prefixes
    recorded; their internals are not axiomatized as a new recognizer.

    Direct composition uses PrefixFactoringProjection.tree_call and its proved
    FactoringTreeRelocation bridge, and FactoringForestWalkRelocation's concrete
    coordinate entry theorem. Older MixfixSpineCommit coordinates are already
    connected inside that walk model; its abstract items are not substituted for
    the full descriptors here. Prefix category and ineligible types are reused.

    Scope: identity relocation plus finite imported executions. Rust casts are
    modeled modulo their widths, and arithmetic_ok records executed usize/u16
    additions and the cast-THEN-subtract domain. It is not a blanket part-count
    bound or dynamic admission. On an invalid domain the natural transcription
    is diagnostic only, not a claim about debug panic versus release wrapping.
    Index/expect faults and imported fuel stops retain modeled effect prefixes.
    Original vector lengths/field widths must be representable; allocator,
    reserve failure, Drop, Rust transcription checking, callback panic/unwind,
    UTF-8 encoding/formatting implementation, and termination are outside scope.
    Refusals retain every varying formatting argument. Original LIMIT_REFUSAL
    strings and formatters must move unchanged. No general accounting, safety,
    classifier equivalence, or downstream election theorem is asserted.
*)
From Stdlib Require Import List String Bool Arith FSets.FMapAVL Structures.OrderedTypeEx.
From PrattailWpdaRuntime Require Import PrefixFactoringProjection
  PrefixMemberDescriptorRelocation FactoringForestWalkRelocation.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

Module MixfixDescriptorProjection.
Module P := PrefixFactoringProjection.PrefixFactoringProjection.
Module H := PrefixMemberDescriptorRelocation.PrefixMemberDescriptorRelocation.
Module F := FactoringTreeRelocation.FactoringTreeRelocation.
Module W := FactoringForestWalkRelocation.FactoringForestWalkRelocation.
Module TriggerKey := PairOrderedType Nat_as_OT String_as_OT.
Module TriggerMap := FMapAVL.Make TriggerKey.
Module DispatchMap := FMapAVL.Make Nat_as_OT.

Record MixfixRep := { separator : string; rep_min : nat; rep_close : list string }.
Record MixfixPart := {
  operand_category : string; param_name : string;
  preceding_terminals : list string; following_terminals : list string;
  repetition : option MixfixRep; capture_kind : option string
}.
Record InfixOperator := {
  terminal : string; category : string; result_category : string;
  left_bp : nat; right_bp : nat; label : string;
  is_cross_category : bool; is_postfix : bool; is_mixfix : bool;
  mixfix_parts : list MixfixPart; nullary_literals : list string
}.
Record OperatorRef := { operator_occurrence : nat; operator : InfixOperator }.
Record GroupedOp := { op_ref : OperatorRef; result_src_idx : nat; rule_idx : nat }.
Definition op g := operator (op_ref g).
Definition Grouped := TriggerMap.t (list GroupedOp).
Definition LabelIndex := (string * string) -> option (nat * nat).
Definition append_group key row (grouped : Grouped) :=
  let previous := match TriggerMap.find key grouped with Some xs => xs | None => [] end in
  TriggerMap.add key (previous ++ [row])%list grouped.
Fixpoint group_ops_loop (operators : list InfixOperator) occurrence categories
  (label_index : LabelIndex) (grouped : Grouped) := match operators with
| [] => grouped
| operator :: rest =>
  let next := match H.lookup_src_idx (category operator) categories with
  | None => grouped
  | Some dispatch => match label_index (result_category operator, label operator) with
    | None => grouped
    | Some (result, rule) => append_group (dispatch,terminal operator)
        {| op_ref := {| operator_occurrence := occurrence; operator := operator |};
           result_src_idx := result; rule_idx := rule |} grouped end end in
  group_ops_loop rest (S occurrence) categories label_index next
end.
Definition group_ops_by_cat_terminal operators categories index :=
  group_ops_loop operators 0 categories index (TriggerMap.empty (list GroupedOp)).
Definition original_group_ops := group_ops_by_cat_terminal.
Definition relocated_group_ops := group_ops_by_cat_terminal.

Record MixfixCandidate := {
  member : F.CandidateMember; l_bp : nat; candidate_result_src : nat;
  expected_cats : list nat; fixb_literal : option string
}.
Record MixfixGroup := {
  spine_id : nat; group_result_src : nat; min_l_bp : nat; min_member_rule_idx : nat;
  member_l_bps : list (nat * nat); expected_cats_union : list nat;
  group_fixb_literal : option string; roots : list F.SpineTree
}.
Record MixfixBucket := {
  trigger : string; slice : list (nat * nat * nat); groups : list MixfixGroup;
  ineligible : list P.IneligibleGroup; singletons : list P.SingletonMember
}.
Inductive Refusal :=
| TreeRefusal (event : F.Refusal)
| FixBMismatch (dispatch : nat) (trigger : string) (candidate_fixb : option string)
    (rule : nat) (cohort_fixb : option string)
| LeafMismatch (dispatch : nat) (trigger : string) (leaf_count member_count : nat)
| RootMismatch (dispatch : nat) (trigger : string) (root_count : nat)
| RecoveryCollision (category ending recovery_base : nat)
| RuleIndexCeiling (category ending : nat).
Record MixfixFactoring := {
  dispatch_cat_src_idx : nat; buckets : list MixfixBucket; refusals : list Refusal
}.
Definition u8_cast n := n mod 256.
Definition u16_cast n := n mod 65536.
Definition selected cap ops := firstn cap (filter (fun g => is_mixfix (op g)) ops).
Definition slice_rows ops := List.map (fun g => (left_bp (op g),result_src_idx g,rule_idx g)) ops.
Definition op_first_nullary_literal operator := hd_error (nullary_literals operator).
Definition first_literal_evidence operator := match mixfix_parts operator with
| [] => op_first_nullary_literal operator
| part :: _ => match repetition part with
  | None => hd_error (preceding_terminals part) | Some _ => None end end.
Definition option_string_eqb lhs rhs := match lhs,rhs with
| None,None => true | Some a,Some b => String.eqb a b | _,_ => false end.
Definition singleton reason candidate :=
 {| P.singleton_rule := F.candidate_rule (member candidate); P.singleton_reason := reason |}.
Definition bad reason part :=
 {| P.ineligible_reason := reason;
    P.member_rule_idxs := List.map (fun c => F.candidate_rule (member c)) part |}.
Fixpoint unique_nats values seen := match values with
| [] => seen | n :: rest => unique_nats rest
    (if existsb (Nat.eqb n) seen then seen else (seen ++ [n])%list) end.
Fixpoint update_slot index value (slots : list nat) := match slots,index with
| [],_ => [] | _ :: rest,0 => value :: rest
| n :: rest,S k => n :: update_slot k value rest end.

Definition coordinate_call mode fuel root := match mode with
| P.Original => W.original_execute fuel
    {| W.original_state := W.Coordinates (W.mix_initial root) |}
| P.Relocated => W.relocated_execute fuel
    {| W.relocated_state := W.Coordinates (W.mix_initial root) |} end.
Theorem imported_coordinate_call_correspondence : forall fuel root,
  coordinate_call P.Relocated fuel root = coordinate_call P.Original fuel root.
Proof. intros; apply W.coordinate_entry_relocation. Qed.

Section Callbacks.
Context {Rule Error State : Type}.
Record Callbacks := {
  resolve : string -> list string -> string -> string -> State -> (nat + Error) * State;
  cast : Rule -> State -> bool * State
}.
Inductive Event :=
| ResolveCall (name : string) (categories : list string) (site rule_label : string)
    (result : nat + Error)
| CastCall (rule : Rule) (result : bool)
| TreeCall (root : F.SpineItem) (members : list F.CandidateMember) (result : F.OriginalOutcome)
| CoordinateCall (root : F.SpineTree) (result : W.WalkOutcome).
Record Effects := {
  callback_state : State; trace : list Event; diagnostics : list Refusal;
  arithmetic_ok : bool; debug_ok : bool
}.
Definition effect state events refusals valid debug :=
 {| callback_state := state; trace := events; diagnostics := refusals;
    arithmetic_ok := valid; debug_ok := debug |}.
Definition initial state := effect state [] [] true true.
Definition event ev e := effect (callback_state e) (trace e ++ [ev])%list
  (diagnostics e) (arithmetic_ok e) (debug_ok e).
Definition diagnostic refusal e := effect (callback_state e) (trace e)
  (diagnostics e ++ [refusal])%list (arithmetic_ok e) (debug_ok e).
Definition check_arithmetic holds e := effect (callback_state e) (trace e)
  (diagnostics e) (arithmetic_ok e && holds) (debug_ok e).
Definition resolve_call callbacks name categories site rule_label e :=
  let '(result,state) := resolve callbacks name categories site rule_label (callback_state e) in
  (result,effect state (trace e ++ [ResolveCall name categories site rule_label result])%list
    (diagnostics e) (arithmetic_ok e) (debug_ok e)).
Definition cast_call callbacks rule e :=
  let '(result,state) := cast callbacks rule (callback_state e) in
  (result,effect state (trace e ++ [CastCall rule result])%list
    (diagnostics e) (arithmetic_ok e) (debug_ok e)).
Definition tree_effects after e := effect (callback_state e) (trace e)
  (diagnostics e ++ List.map TreeRefusal (F.refusals after))%list
  (arithmetic_ok e && F.arithmetic_ok after) (debug_ok e && F.debug_ok after).

Record MemberProgress := {
  items : list F.SpineItem; coords : list F.Coordinate; item_effects : Effects
}.
Definition item_progress xs cs e := {| items := xs; coords := cs; item_effects := e |}.
Definition append_item item coord p := item_progress (items p ++ [item])%list
  (coords p ++ [coord])%list (item_effects p).
Inductive LiteralSite := Nullary | Preceding (part_index : nat) | Following (part_index : nat).
Definition literal_coordinate site index := match site with
| Nullary => (2,0,u8_cast (S index))
| Preceding 0 => (2,0,u8_cast (S index))
| Preceding part => (1,Nat.pred (u8_cast part),u8_cast (S index))
| Following part => (0,u8_cast part,u8_cast (S index)) end.
Definition literal_domain usize_max site index :=
  Nat.leb (S index) usize_max && match site with
  | Preceding (S k) => negb (Nat.eqb (u8_cast (S k)) 0)
  | _ => true end.
Fixpoint literal_run usize_max site index texts progress := match texts with
| [] => progress
| text :: rest =>
  let next := append_item (F.Literal text None) (literal_coordinate site index) progress in
  literal_run usize_max site (S index) rest
    (item_progress (items next) (coords next)
      (check_arithmetic (literal_domain usize_max site index) (item_effects next))) end.
Fixpoint member_parts callbacks usize_max categories rule_label part_index parts progress :=
  match parts with
  | [] => (progress,false)
  | part :: rest => match repetition part with
    | Some _ => (progress,true)
    | None =>
      let preceding := literal_run usize_max (Preceding part_index) 0
        (preceding_terminals part) progress in
      match capture_kind part with
      | Some _ => (preceding,true)
      | None =>
        let '(resolved,e) := resolve_call callbacks (operand_category part) categories
          "a mixfix cohort's operand position" rule_label (item_effects preceding) in
        let called := item_progress (items preceding) (coords preceding) e in
        match resolved with
        | inr _ => (called,true)
        | inl cat =>
          let operand := append_item (F.ParamParse cat 0) (0,u8_cast part_index,0) called in
          let following := literal_run usize_max (Following part_index) 0
            (following_terminals part) operand in
          member_parts callbacks usize_max categories rule_label (S part_index) rest following
        end end end end.
Definition mixfix_member_items callbacks usize_max categories operator e :=
  let progress := item_progress [] [(2,0,0)] e in
  match mixfix_parts operator with
  | [] => (literal_run usize_max Nullary 0 (nullary_literals operator) progress,false)
  | parts => member_parts callbacks usize_max categories (label operator) 0 parts progress end.
Fixpoint expected_parts callbacks categories rule_label parts previous e := match parts with
| [] => (Some previous,e)
| part :: rest => match repetition part,capture_kind part with
  | None,None =>
    let '(result,called) := resolve_call callbacks (operand_category part) categories
      "a mixfix cohort's action entry" rule_label e in
    match result with
    | inr _ => (None,called)
    | inl cat => expected_parts callbacks categories rule_label rest (previous ++ [cat])%list called
    end
  | _,_ => expected_parts callbacks categories rule_label rest (previous ++ [P.u16_max])%list e
  end end.
Definition discover_candidate callbacks usize_max categories dispatch g e :=
  let '(progress,truncated) := mixfix_member_items callbacks usize_max categories (op g) e in
  let prepared := check_arithmetic (Nat.leb (S (List.length (mixfix_parts (op g)))) usize_max)
    (item_effects progress) in
  let '(expected,after) := expected_parts callbacks categories (label (op g))
    (mixfix_parts (op g)) [dispatch] prepared in
  (match expected with
   | None => None
   | Some cats => Some
     {| member := {| F.candidate_kind := F.Mixfix; F.candidate_rule := rule_idx g;
        F.candidate_items := items progress; F.candidate_truncated := truncated;
        F.candidate_total_positions := List.length (items progress);
        F.candidate_body_src_idx := None; F.candidate_mixfix_coords := coords progress |};
        l_bp := left_bp (op g); candidate_result_src := result_src_idx g;
        expected_cats := cats; fixb_literal := first_literal_evidence (op g) |}
   end,after).
Fixpoint discover_candidates callbacks usize_max categories dispatch ops previous e := match ops with
| [] => (previous,e)
| g :: rest => let '(candidate,after) := discover_candidate callbacks usize_max categories dispatch g e in
    discover_candidates callbacks usize_max categories dispatch rest
      (match candidate with Some c => (previous ++ [c])%list | None => previous end) after end.
Definition rule_at (per_cat : list (list Rule)) candidate :=
  match nth_error per_cat (candidate_result_src candidate) with
  | None => None | Some rules => nth_error rules (F.candidate_rule (member candidate)) end.
Fixpoint exclude_candidates callbacks per_cat candidates rejected retained e := match candidates with
| [] => (rejected,retained,e)
| c :: rest =>
  let '(is_cast,after) := match rule_at per_cat c with
    | None => (false,e) | Some rule => cast_call callbacks rule e end in
  if is_cast then exclude_candidates callbacks per_cat rest
    (rejected ++ [singleton P.CastMachinery c])%list retained after
  else match F.candidate_items (member c) with
  | [] => exclude_candidates callbacks per_cat rest
      (rejected ++ [singleton P.EmptySequence c])%list retained after
  | _ => exclude_candidates callbacks per_cat rest rejected (retained ++ [c])%list after end end.

Definition RootParts := list (F.SpineItem * list MixfixCandidate).
Fixpoint insert_root root candidate (parts : RootParts) := match parts with
| [] => [(root,[candidate])]
| (item,members) :: rest => if F.item_eqb item root
    then (item,(members ++ [candidate])%list) :: rest
    else (item,members) :: insert_root root candidate rest end.
Fixpoint partition_roots candidates parts := match candidates with
| [] => Some parts
| c :: rest => match F.candidate_items (member c) with
  | [] => None (* exact unchecked items[0] fault; excluded on the normal path *)
  | root :: _ => partition_roots rest (insert_root root c parts) end end.
Definition degrade_parts (parts : RootParts) := flat_map (fun entry =>
  let reason := if Nat.eqb (List.length (snd entry)) 1
    then P.LoneRootChild else P.PartialSliceCohort in
  List.map (singleton reason) (snd entry)) parts.
Fixpoint absorb_items trigger_keys items operand_cat previous := match items with
| [] => previous
| F.ParamParse cat _ :: rest => absorb_items trigger_keys rest (Some cat) previous
| F.Literal text _ :: rest =>
  let next := match operand_cat with
  | None => previous
  | Some cat => if trigger_keys (cat,text) && negb (existsb (String.eqb text) previous)
    then (previous ++ [text])%list else previous end in
  absorb_items trigger_keys rest operand_cat next end.
Definition absorbable trigger_keys part := fold_left (fun previous c =>
  absorb_items trigger_keys (F.candidate_items (member c)) None previous) part [].
Definition fixb_diagnostics dispatch trigger evidence part e := fold_left (fun after c =>
  if option_string_eqb (fixb_literal c) evidence then after else diagnostic
    (FixBMismatch dispatch trigger (fixb_literal c) (F.candidate_rule (member c)) evidence) after) part e.
Definition union_expected part := fold_left (fun previous c => unique_nats (expected_cats c) previous) part [].
Definition minimum values := match values with
| [] => None | x :: xs => Some (fold_left Nat.min xs x) end.
Inductive Stop :=
| MissingResultSource | MissingFixBMember | MissingMinimum | MissingRootPartItem
| MissingBuiltRoot | MissingOrdinal (result_category : nat)
| TreeDidNotReturn (outcome : F.OriginalOutcome)
| CoordinatesDidNotReturn (outcome : W.WalkOutcome).
Inductive GroupResult :=
| Eligible (group : MixfixGroup) (ordinals : list nat) (after : Effects)
| Ineligible (reason : P.IneligibleGroup) (ordinals : list nat) (after : Effects)
| GroupStopped (reason : Stop) (ordinals : list nat) (after : Effects).
Definition finish_group result_src min_bp min_rule bp_rows expected evidence forest ordinals e :=
  match nth_error ordinals result_src with
  | None => GroupStopped (MissingOrdinal result_src) ordinals e
  | Some ordinal =>
    let after := check_arithmetic
      (Nat.leb (P.SPINE_RULE_BASE + ordinal) P.u16_max && Nat.leb (S ordinal) P.u16_max) e in
    Eligible {| spine_id := P.SPINE_RULE_BASE + ordinal; group_result_src := result_src;
      min_l_bp := min_bp; min_member_rule_idx := min_rule; member_l_bps := bp_rows;
      expected_cats_union := expected; group_fixb_literal := evidence; roots := forest |}
      (update_slot result_src (S ordinal) ordinals) after end.
Definition validate_coordinates mode coordinate_fuel root part result_src min_bp min_rule bp_rows
  expected evidence forest ordinals e :=
  let outcome := coordinate_call mode coordinate_fuel root in
  let called := event (CoordinateCall root outcome) e in
  match outcome with
  | W.CoordinatesReturned _ valid => finish_group result_src min_bp min_rule bp_rows
      expected evidence forest ordinals (check_arithmetic valid called)
  | W.CoordinatesCollided _ partial => Ineligible (bad P.MultiOperandSharedSpine part)
      ordinals (check_arithmetic (W.mix_arithmetic_ok partial) called)
  | W.CoordinatePanicked _ partial => GroupStopped (CoordinatesDidNotReturn outcome)
      ordinals (check_arithmetic (W.mix_arithmetic_ok partial) called)
  | W.Running (W.Coordinates partial) => GroupStopped (CoordinatesDidNotReturn outcome)
      ordinals (check_arithmetic (W.mix_arithmetic_ok partial) called)
  | _ => GroupStopped (CoordinatesDidNotReturn outcome) ordinals called end.
Definition after_tree mode coordinate_fuel usize_max dispatch trigger part result_src min_bp min_rule
  bp_rows expected evidence ordinals outcome e := match outcome with
| F.OriginalFinished forest after =>
  let built := tree_effects after e in
  match F.interior_accepts after with
  | _ :: _ => Ineligible (bad (P.InteriorAccept (F.interior_accepts after)) part) ordinals built
  | [] =>
    let count := W.forest_leaf_count forest in
    let counted := check_arithmetic (Nat.leb count usize_max) built in
    let checked_leaves := if Nat.eqb count (List.length part) then counted
      else diagnostic (LeafMismatch dispatch trigger count (List.length part)) counted in
    let checked_roots := if Nat.eqb (List.length forest) 1 then checked_leaves
      else diagnostic (RootMismatch dispatch trigger (List.length forest)) checked_leaves in
    match forest with
    | [] => GroupStopped MissingBuiltRoot ordinals checked_roots
    | root :: _ => validate_coordinates mode coordinate_fuel root part result_src min_bp min_rule
        bp_rows expected evidence forest ordinals checked_roots end end
| F.OriginalContinue suspended => GroupStopped (TreeDidNotReturn outcome) ordinals
    (tree_effects (F.effects (F.original_configuration suspended)) e)
| F.OriginalFailed _ failed => GroupStopped (TreeDidNotReturn outcome) ordinals
    (tree_effects (F.effects (F.original_configuration failed)) e) end.
Definition build_mixfix_group mode tree_fuel coordinate_fuel usize_max dispatch trigger root_item part
  trigger_keys ordinals e :=
  let results := unique_nats (List.map candidate_result_src part) [] in
  if Nat.ltb 1 (List.length results) then
    Ineligible (bad (P.NonUniformResultSrc results) part) ordinals e
  else match results with
  | [] => GroupStopped MissingResultSource ordinals e
  | result_src :: _ =>
    let absorbing := absorbable trigger_keys part in
    match absorbing with
    | _ :: _ => Ineligible (bad (P.OperandAbsorbableDivergence absorbing) part) ordinals e
    | [] => match part with
      | [] => GroupStopped MissingFixBMember ordinals e
      | first :: _ =>
        let evidence := fixb_literal first in
        let checked := fixb_diagnostics dispatch trigger evidence part e in
        match minimum (List.map l_bp part),
          minimum (List.map (fun c => F.candidate_rule (member c)) part) with
        | Some min_bp,Some min_rule =>
          let bp_rows := List.map (fun c => (l_bp c,F.candidate_rule (member c))) part in
          let expected := union_expected part in
          let members := List.map member part in
          let outcome := P.tree_call mode tree_fuel usize_max false root_item members in
          after_tree mode coordinate_fuel usize_max dispatch trigger part result_src min_bp min_rule
            bp_rows expected evidence ordinals outcome (event (TreeCall root_item members outcome) checked)
        | _,_ => GroupStopped MissingMinimum ordinals checked end end end end.

Definition PerDispatch := DispatchMap.t (list MixfixBucket).
Definition append_bucket dispatch bucket (entries : PerDispatch) :=
  let previous := match DispatchMap.find dispatch entries with Some xs => xs | None => [] end in
  DispatchMap.add dispatch (previous ++ [bucket])%list entries.
Definition bucket trigger rows groups bads singles :=
 {| trigger := trigger; slice := rows; groups := groups; ineligible := bads; singletons := singles |}.
Inductive BucketResult :=
| BucketBuilt (value : MixfixBucket) (ordinals : list nat) (after : Effects)
| BucketStopped (reason : Stop) (ordinals : list nat) (after : Effects).
Definition build_bucket mode callbacks tree_fuel coordinate_fuel usize_max categories per_cat
  dispatch trigger ops trigger_keys ordinals e :=
  let rows := slice_rows ops in
  let '(candidates,discovered) := discover_candidates callbacks usize_max categories dispatch ops [] e in
  let '(singles,retained,excluded) := exclude_candidates callbacks per_cat candidates [] [] discovered in
  match partition_roots retained [] with
  | None => BucketStopped MissingRootPartItem ordinals excluded
  | Some parts =>
    let whole := match singles,parts with
      | [],[(_,part)] => Nat.eqb (List.length part) (List.length rows) && Nat.leb 2 (List.length rows)
      | _,_ => false end in
    if whole then match parts with
    | (root,part) :: _ =>
      match build_mixfix_group mode tree_fuel coordinate_fuel usize_max dispatch trigger root part
        trigger_keys ordinals excluded with
      | Eligible group next after => BucketBuilt (bucket trigger rows [group] [] singles) next after
      | Ineligible bad next after => BucketBuilt (bucket trigger rows [] [bad] singles) next after
      | GroupStopped reason next after => BucketStopped reason next after end
    | [] => BucketStopped MissingRootPartItem ordinals excluded end
    else BucketBuilt (bucket trigger rows [] [] (singles ++ degrade_parts parts)%list) ordinals excluded
  end.
Fixpoint initialize_ordinals usize_max prefix ordinals e := match prefix with
| [] => (ordinals,e)
| fact :: rest =>
  let count := fold_left (fun count b => count + List.length (P.groups b)) (P.buckets fact) 0 in
  initialize_ordinals usize_max rest (update_slot (P.category_src_idx fact) (u16_cast count) ordinals)
    (check_arithmetic (Nat.leb count usize_max) e) end.
Inductive BuilderResult :=
| Built (entries : PerDispatch) (ordinals : list nat) (after : Effects)
| BuilderStopped (reason : Stop) (entries : PerDispatch) (ordinals : list nat) (after : Effects).
Fixpoint build_entries mode callbacks tree_fuel coordinate_fuel usize_max cap categories per_cat
  trigger_keys entries output ordinals e := match entries with
| [] => Built output ordinals e
| ((dispatch,terminal),ops) :: rest =>
  match selected cap ops with
  | [] => build_entries mode callbacks tree_fuel coordinate_fuel usize_max cap categories per_cat
      trigger_keys rest output ordinals e
  | chosen => match build_bucket mode callbacks tree_fuel coordinate_fuel usize_max categories per_cat
      dispatch terminal chosen trigger_keys ordinals e with
    | BucketBuilt value next after =>
      build_entries mode callbacks tree_fuel coordinate_fuel usize_max cap categories per_cat trigger_keys
        rest (append_bucket dispatch value output) next after
    | BucketStopped reason next after => BuilderStopped reason output next after end end end.
Fixpoint ending_checks recovery_base category_index ordinals e := match ordinals with
| [] => e
| ordinal :: rest =>
  let ending := P.SPINE_RULE_BASE + ordinal in
  let added := check_arithmetic (Nat.leb ending 4294967295) e in
  let recovery := if Nat.leb recovery_base ending then
    diagnostic (RecoveryCollision category_index ending recovery_base) added else added in
  let ceiling := if Nat.leb P.u16_max ending then
    diagnostic (RuleIndexCeiling category_index ending) recovery else recovery in
  ending_checks recovery_base (S category_index) rest ceiling end.
Definition sorted_output (entries : PerDispatch) := List.map (fun entry =>
 {| dispatch_cat_src_idx := fst entry; buckets := snd entry; refusals := [] |}) (DispatchMap.elements entries).
Definition drain_refusals previous output := match previous with
| [] => output
| _ => match output with
  | [] => [{| dispatch_cat_src_idx := 0; buckets := []; refusals := previous |}]
  | first :: rest => {| dispatch_cat_src_idx := dispatch_cat_src_idx first;
      buckets := buckets first; refusals := previous |} :: rest end end.
Inductive PartitionResult :=
| PartitionReturned (output : list MixfixFactoring) (ordinals : list nat) (after : Effects)
| PartitionStopped (reason : Stop) (entries : PerDispatch) (ordinals : list nat) (after : Effects).
Definition build_mixfix_factoring mode callbacks tree_fuel coordinate_fuel usize_max cap recovery_base
  categories (per_cat : list (list Rule)) prefix (grouped : Grouped) state :=
  let trigger_keys := fun key => TriggerMap.mem key grouped in
  let '(ordinals,prepared) := initialize_ordinals usize_max prefix
    (repeat 0 (List.length per_cat)) (initial state) in
  match build_entries mode callbacks tree_fuel coordinate_fuel usize_max cap categories per_cat
    trigger_keys (TriggerMap.elements grouped) (DispatchMap.empty (list MixfixBucket)) ordinals prepared with
  | BuilderStopped reason entries next after => PartitionStopped reason entries next after
  | Built entries next after =>
    let checked := ending_checks recovery_base 0 next after in
    PartitionReturned (drain_refusals (diagnostics checked) (sorted_output entries)) next checked end.

(** The following finite-run proofs substitute only the TWO imported concrete
    executors. All grouping, fields, callbacks, gates and outer loops above are
    the common original source body; there is no arbitrary-parser equality premise. *)
Lemma validate_coordinates_relocation : forall fuel root part result min_bp min_rule bp_rows
  expected evidence forest ordinals e,
  validate_coordinates P.Relocated fuel root part result min_bp min_rule bp_rows expected evidence forest ordinals e =
  validate_coordinates P.Original fuel root part result min_bp min_rule bp_rows expected evidence forest ordinals e.
Proof. intros; unfold validate_coordinates; rewrite imported_coordinate_call_correspondence; reflexivity. Qed.
Lemma after_tree_relocation : forall fuel usize_max dispatch trigger part result min_bp min_rule
  bp_rows expected evidence ordinals outcome e,
  after_tree P.Relocated fuel usize_max dispatch trigger part result min_bp min_rule bp_rows expected evidence ordinals outcome e =
  after_tree P.Original fuel usize_max dispatch trigger part result min_bp min_rule bp_rows expected evidence ordinals outcome e.
Proof.
  intros; destruct outcome as [suspended|forest after|reason failed]; cbn [after_tree]; try reflexivity.
  destruct (F.interior_accepts after); [|reflexivity].
  destruct forest; [reflexivity|apply validate_coordinates_relocation].
Qed.
Lemma group_relocation : forall tree_fuel coordinate_fuel usize_max dispatch trigger root part keys ordinals e,
  build_mixfix_group P.Relocated tree_fuel coordinate_fuel usize_max dispatch trigger root part keys ordinals e =
  build_mixfix_group P.Original tree_fuel coordinate_fuel usize_max dispatch trigger root part keys ordinals e.
Proof.
  intros; unfold build_mixfix_group.
  destruct (Nat.ltb 1 (List.length (unique_nats (List.map candidate_result_src part) []))); [reflexivity|].
  destruct (unique_nats (List.map candidate_result_src part) []); [reflexivity|].
  destruct (absorbable keys part); [|reflexivity].
  destruct part as [|first rest]; [reflexivity|].
  destruct (minimum (List.map l_bp (first :: rest))); [|reflexivity].
  destruct (minimum (List.map (fun c => F.candidate_rule (member c)) (first :: rest))); [|reflexivity].
  rewrite P.imported_tree_call_correspondence; apply after_tree_relocation.
Qed.
Lemma bucket_relocation : forall callbacks tree_fuel coordinate_fuel usize_max categories per_cat
  dispatch trigger ops keys ordinals e,
  build_bucket P.Relocated callbacks tree_fuel coordinate_fuel usize_max categories per_cat dispatch trigger ops keys ordinals e =
  build_bucket P.Original callbacks tree_fuel coordinate_fuel usize_max categories per_cat dispatch trigger ops keys ordinals e.
Proof.
  intros; unfold build_bucket.
  destruct (discover_candidates callbacks usize_max categories dispatch ops [] e) as [candidates discovered].
  destruct (exclude_candidates callbacks per_cat candidates [] [] discovered) as [[singles retained] excluded].
  destruct (partition_roots retained []) as [parts|]; [|reflexivity].
  destruct (match singles,parts with
    | [],[(_,part)] => Nat.eqb (List.length part) (List.length (slice_rows ops)) && Nat.leb 2 (List.length (slice_rows ops))
    | _,_ => false end); [|reflexivity].
  destruct parts as [|[root part] rest]; [reflexivity|].
  rewrite group_relocation; reflexivity.
Qed.
Theorem finite_bucket_schedule_relocation : forall callbacks tree_fuel coordinate_fuel usize_max cap categories per_cat
  keys entries output ordinals e,
  build_entries P.Relocated callbacks tree_fuel coordinate_fuel usize_max cap categories per_cat keys entries output ordinals e =
  build_entries P.Original callbacks tree_fuel coordinate_fuel usize_max cap categories per_cat keys entries output ordinals e.
Proof.
  intros callbacks tree_fuel coordinate_fuel usize_max cap categories per_cat keys entries.
  induction entries as [|[[dispatch terminal] ops] rest IH]; intros; [reflexivity|].
  cbn [build_entries]. destruct (selected cap ops) as [|chosen tail]; [apply IH|].
  rewrite bucket_relocation.
  destruct (build_bucket P.Original callbacks tree_fuel coordinate_fuel usize_max categories per_cat
    dispatch terminal (chosen :: tail) keys ordinals e); [apply IH|reflexivity].
Qed.
Theorem enabled_partition_preserves_full_outputs_callbacks_refusals_and_failures :
  forall callbacks tree_fuel coordinate_fuel usize_max cap recovery_base categories per_cat prefix grouped state,
  build_mixfix_factoring P.Relocated callbacks tree_fuel coordinate_fuel usize_max cap recovery_base categories per_cat prefix grouped state =
  build_mixfix_factoring P.Original callbacks tree_fuel coordinate_fuel usize_max cap recovery_base categories per_cat prefix grouped state.
Proof.
  intros; unfold build_mixfix_factoring.
  destruct (initialize_ordinals usize_max prefix (repeat 0 (List.length per_cat)) (initial state)).
  rewrite finite_bucket_schedule_relocation; reflexivity.
Qed.

Theorem missing_rule_invokes_no_cast : forall callbacks per_cat candidate e,
  rule_at per_cat candidate = None ->
  (match rule_at per_cat candidate with None => (false,e) | Some rule => cast_call callbacks rule e end) = (false,e).
Proof. intros callbacks per_cat candidate e Hmissing; rewrite Hmissing; reflexivity. Qed.
Theorem repeated_part_stops_before_preceding : forall callbacks usize_max categories rule_label i part rest progress rep,
  repetition part = Some rep ->
  member_parts callbacks usize_max categories rule_label i (part :: rest) progress = (progress,true).
Proof. intros callbacks usize_max categories rule_label i part rest progress rep Hrep;
  cbn [member_parts]; rewrite Hrep; reflexivity. Qed.
Theorem capture_stops_after_preceding : forall callbacks usize_max categories rule_label i part rest progress kind,
  repetition part = None -> capture_kind part = Some kind ->
  member_parts callbacks usize_max categories rule_label i (part :: rest) progress =
  (literal_run usize_max (Preceding i) 0 (preceding_terminals part) progress,true).
Proof. intros callbacks usize_max categories rule_label i part rest progress kind Hrep Hcapture;
  cbn [member_parts]; rewrite Hrep,Hcapture; reflexivity. Qed.
Theorem refusal_sentinel_retains_complete_ordered_sink : forall first rest,
  drain_refusals (first :: rest) [] =
  [{| dispatch_cat_src_idx := 0; buckets := []; refusals := first :: rest |}].
Proof. reflexivity. Qed.
End Callbacks.

(** The disabled branch has no callback argument at all. Metadata preparation
    remains the same macro wrapper; no enabled builder work is eager here. *)
Fixpoint identity_entries cap entries (output : DispatchMap.t (list MixfixBucket)) := match entries with
| [] => output
| ((dispatch,terminal),ops) :: rest =>
  let chosen := selected cap ops in
  match chosen with
  | [] => identity_entries cap rest output
  | _ => let singles := List.map (fun g =>
      {| P.singleton_rule := rule_idx g; P.singleton_reason := P.FactoringDisabled |}) chosen in
    let value := {| trigger := terminal; slice := slice_rows chosen; groups := [];
      ineligible := []; singletons := singles |} in
    let previous := match DispatchMap.find dispatch output with Some xs => xs | None => [] end in
    identity_entries cap rest (DispatchMap.add dispatch (previous ++ [value])%list output) end end.
Definition mixfix_identity_partition cap (grouped : Grouped) :=
  List.map (fun entry => {| dispatch_cat_src_idx := fst entry; buckets := snd entry; refusals := [] |})
    (DispatchMap.elements (identity_entries cap (TriggerMap.elements grouped)
      (DispatchMap.empty (list MixfixBucket)))).
Definition original_identity_partition := mixfix_identity_partition.
Definition relocated_identity_partition := mixfix_identity_partition.
Definition mixfix_spine_parts_len_rows partition := flat_map (fun fact =>
  flat_map (fun bucket => List.map (fun group => (group_result_src group,spine_id group))
    (groups bucket)) (buckets fact)) partition.
Definition group_member_rule_idxs group := List.map snd (member_l_bps group).

Theorem grouping_keeps_complete_operator_occurrences_and_order : forall table categories index,
  relocated_group_ops table categories index = original_group_ops table categories index.
Proof. reflexivity. Qed.
Theorem unresolved_dispatch_skips_before_label_index : forall operator rest occurrence categories index grouped,
  H.lookup_src_idx (category operator) categories = None ->
  group_ops_loop (operator :: rest) occurrence categories index grouped =
  group_ops_loop rest (S occurrence) categories index grouped.
Proof. intros operator rest occurrence categories index grouped Hmissing;
  cbn [group_ops_loop]; rewrite Hmissing; reflexivity. Qed.
Theorem kind_filter_precedes_cap : forall cap ops,
  selected cap ops = firstn cap (filter (fun g => is_mixfix (op g)) ops).
Proof. reflexivity. Qed.
Theorem identity_partition_exact_relocation : forall cap grouped,
  relocated_identity_partition cap grouped = original_identity_partition cap grouped.
Proof. reflexivity. Qed.
Theorem presence_rows_keep_result_category_and_group_order : forall group rest,
  List.map (fun g => (group_result_src g,spine_id g)) (group :: rest) =
  (group_result_src group,spine_id group) :: List.map (fun g => (group_result_src g,spine_id g)) rest.
Proof. reflexivity. Qed.
Theorem later_preceding_subtraction_domain_is_cast_then_subtract : forall usize_max index part,
  literal_domain usize_max (Preceding (S part)) index =
  Nat.leb (S index) usize_max && negb (Nat.eqb (u8_cast (S part)) 0).
Proof. reflexivity. Qed.

Print Assumptions imported_coordinate_call_correspondence.
Print Assumptions validate_coordinates_relocation.
Print Assumptions after_tree_relocation.
Print Assumptions group_relocation.
Print Assumptions bucket_relocation.
Print Assumptions finite_bucket_schedule_relocation.
Print Assumptions enabled_partition_preserves_full_outputs_callbacks_refusals_and_failures.
Print Assumptions missing_rule_invokes_no_cast.
Print Assumptions repeated_part_stops_before_preceding.
Print Assumptions capture_stops_after_preceding.
Print Assumptions refusal_sentinel_retains_complete_ordered_sink.
Print Assumptions grouping_keeps_complete_operator_occurrences_and_order.
Print Assumptions unresolved_dispatch_skips_before_label_index.
Print Assumptions kind_filter_precedes_cap.
Print Assumptions identity_partition_exact_relocation.
Print Assumptions presence_rows_keep_result_category_and_group_order.
Print Assumptions later_preceding_subtraction_domain_is_cast_then_subtract.
End MixfixDescriptorProjection.
