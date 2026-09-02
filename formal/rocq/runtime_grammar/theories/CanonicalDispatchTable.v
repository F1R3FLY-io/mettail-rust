(** * Canonical checked tables for generated WPDA dispatch

    Generated Rust match arms denote a finite partial map.  Emitting the same
    key twice is wasteful even when both values agree, and silently accepting
    two different values would make source order an accidental semantic
    authority.  This model specifies the checked insertion used by code
    generation: identical discoveries are idempotent, conflicting discoveries
    are rejected, and successful insertion preserves lookup and key uniqueness.

    The result applies to every generated dispatch table, including the
    collection-spec table keyed by (result category, rule, slot). *)

From Stdlib Require Import List Bool.
Import ListNotations.
Set Implicit Arguments.

Section CanonicalDispatchTable.
  Context {Key Action : Type}.
  Variable key_eqb : Key -> Key -> bool.
  Variable action_eqb : Action -> Action -> bool.
  Hypothesis key_eqb_spec :
    forall left right, key_eqb left right = true <-> left = right.
  Hypothesis action_eqb_spec :
    forall left right, action_eqb left right = true <-> left = right.

  Definition Rule : Type := (Key * Action)%type.

  Fixpoint lookup_table (key : Key) (table : list Rule) : option Action :=
    match table with
    | [] => None
    | (stored_key, action) :: tail =>
        if key_eqb key stored_key then Some action else lookup_table key tail
    end.

  (** [None] is a conflicting duplicate.  [Some table'] is a canonical
      insertion: a same-key/same-action discovery returns the original table,
      while a fresh key is inserted exactly once in discovery order. *)
  Fixpoint insert_checked (rule : Rule) (table : list Rule)
      : option (list Rule) :=
    match rule, table with
    | (key, action), [] => Some [(key, action)]
    | (key, action), (stored_key, stored_action) :: tail =>
        if key_eqb key stored_key then
          if action_eqb action stored_action then Some table else None
        else
          match insert_checked rule tail with
          | Some tail' => Some ((stored_key, stored_action) :: tail')
          | None => None
          end
    end.

  Lemma key_eqb_refl : forall key, key_eqb key key = true.
  Proof.
    intro key; apply (proj2 (key_eqb_spec key key)); reflexivity.
  Qed.

  Lemma action_eqb_refl : forall action, action_eqb action action = true.
  Proof.
    intro action; apply (proj2 (action_eqb_spec action action)); reflexivity.
  Qed.

  Lemma key_eqb_false_neq :
    forall left right, key_eqb left right = false -> left <> right.
  Proof.
    intros left right Hfalse Heq; subst right.
    rewrite key_eqb_refl in Hfalse; discriminate.
  Qed.

  Lemma insert_checked_membership :
    forall rule table table' member,
      insert_checked rule table = Some table' ->
      In member table' -> In member table \/ member = rule.
  Proof.
    intros [key action] table; induction table as [|[stored_key stored_action] tail IH];
      intros table' member Hinsert Hin; simpl in Hinsert.
    - inversion Hinsert; subst table'. simpl in Hin.
      destruct Hin as [Heq | Hnone]; [right; symmetry; assumption | contradiction].
    - destruct (key_eqb key stored_key) eqn:Hkey.
      + destruct (action_eqb action stored_action) eqn:Haction;
          try discriminate.
        inversion Hinsert; subst table'. left; exact Hin.
      + destruct (insert_checked (key, action) tail) as [tail'|] eqn:Htail;
          try discriminate.
        inversion Hinsert; subst table'. simpl in Hin.
        destruct Hin as [Hhead | Hmember].
        * left; simpl; left; exact Hhead.
        * specialize (IH tail' member eq_refl Hmember).
          destruct IH as [Hin_tail | Heq].
          -- left; simpl; right; exact Hin_tail.
          -- right; exact Heq.
  Qed.

  Theorem insert_checked_lookup_inserted :
    forall key action table table',
      insert_checked (key, action) table = Some table' ->
      lookup_table key table' = Some action.
  Proof.
    intros key action table; induction table as [|[stored_key stored_action] tail IH];
      intros table' Hinsert; simpl in Hinsert.
    - inversion Hinsert; subst table'. simpl. rewrite key_eqb_refl. reflexivity.
    - destruct (key_eqb key stored_key) eqn:Hkey.
      + apply key_eqb_spec in Hkey; subst stored_key.
        destruct (action_eqb action stored_action) eqn:Haction;
          try discriminate.
        apply action_eqb_spec in Haction; subst stored_action.
        inversion Hinsert; subst table'. simpl. rewrite key_eqb_refl. reflexivity.
      + destruct (insert_checked (key, action) tail) as [tail'|] eqn:Htail;
          try discriminate.
        inversion Hinsert; subst table'. simpl. rewrite Hkey.
        exact (IH tail' eq_refl).
  Qed.

  Theorem insert_checked_preserves_other_lookup :
    forall inserted_key action table table' query,
      key_eqb query inserted_key = false ->
      insert_checked (inserted_key, action) table = Some table' ->
      lookup_table query table' = lookup_table query table.
  Proof.
    intros inserted_key action table; induction table as
        [|[stored_key stored_action] tail IH];
      intros table' query Hother Hinsert; simpl in Hinsert.
    - inversion Hinsert; subst table'. simpl. rewrite Hother. reflexivity.
    - destruct (key_eqb inserted_key stored_key) eqn:Hstored.
      + destruct (action_eqb action stored_action); try discriminate.
        inversion Hinsert; reflexivity.
      + destruct (insert_checked (inserted_key, action) tail) as [tail'|]
          eqn:Htail; try discriminate.
        inversion Hinsert; subst table'. simpl.
        destruct (key_eqb query stored_key); [reflexivity |].
        exact (IH tail' query Hother eq_refl).
  Qed.

  Theorem insert_checked_preserves_unique_keys :
    forall rule table table',
      NoDup (map fst table) ->
      insert_checked rule table = Some table' ->
      NoDup (map fst table').
  Proof.
    intros [key action] table; induction table as [|[stored_key stored_action] tail IH];
      intros table' Hunique Hinsert; simpl in Hinsert.
    - inversion Hinsert; subst table'. simpl. constructor; [intro H; contradiction | constructor].
    - inversion Hunique as [|stored_key' keys Hfresh Htail_unique]; subst.
      destruct (key_eqb key stored_key) eqn:Hkey.
      + destruct (action_eqb action stored_action); try discriminate.
        inversion Hinsert; subst table'. constructor; assumption.
      + destruct (insert_checked (key, action) tail) as [tail'|] eqn:Htail;
          try discriminate.
        inversion Hinsert; subst table'. simpl. constructor.
        * intro Hin.
          apply in_map_iff in Hin.
          destruct Hin as [[member_key member_action] [Hfst Hentry]].
          simpl in Hfst; subst member_key.
          pose proof (@insert_checked_membership
                        (key, action) tail tail' (stored_key, member_action)
                        Htail Hentry) as Hmember.
          destruct Hmember as [Hin_tail | Heq].
          -- apply Hfresh. apply in_map with (f := fst) in Hin_tail. exact Hin_tail.
          -- inversion Heq; subst key action.
             rewrite key_eqb_refl in Hkey; discriminate.
        * exact (IH tail' Htail_unique eq_refl).
  Qed.

  Theorem insert_checked_conflict_has_disagreeing_witness :
    forall key action table,
      insert_checked (key, action) table = None ->
      exists stored_action,
        In (key, stored_action) table /\ stored_action <> action.
  Proof.
    intros key action table; induction table as [|[stored_key stored_action] tail IH];
      intro Hinsert; simpl in Hinsert; [discriminate |].
    destruct (key_eqb key stored_key) eqn:Hkey.
    - apply key_eqb_spec in Hkey; subst stored_key.
      destruct (action_eqb action stored_action) eqn:Haction;
        try discriminate.
      exists stored_action; split; [simpl; auto |].
      intro Heq; subst stored_action.
      rewrite action_eqb_refl in Haction; discriminate.
    - destruct (insert_checked (key, action) tail) eqn:Htail;
        try discriminate.
      destruct (IH eq_refl) as [witness [Hin Hneq]].
      exists witness; split; [simpl; auto | exact Hneq].
  Qed.
End CanonicalDispatchTable.

Print Assumptions insert_checked_lookup_inserted.
Print Assumptions insert_checked_preserves_other_lookup.
Print Assumptions insert_checked_preserves_unique_keys.
Print Assumptions insert_checked_conflict_has_disagreeing_witness.
