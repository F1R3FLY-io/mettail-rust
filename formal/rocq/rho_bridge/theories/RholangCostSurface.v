(** * Cost-accounted Rholang surface-to-wire obligations

    This model isolates the interface shared by the legacy syntax adapter and
    the MeTTaIL [language!] adapter.  Each adapter resolves a ground name to a
    bound level or canonical ground bytes and lowers a quoted process to a
    canonical [Par] before emitting the structural signature events modeled
    here.  The shared builder must not perform binder lookup or parse source.

    [direct_signature] is the tree semantics of fundable signatures.  [code]
    describes the postorder events consumed by an explicit-stack builder, and
    [run] is that builder.  A transfer capability is deliberately excluded
    from fundable signatures: it is legal only as the outer annotation on a
    signed receive, where [rewrite_signed] handles it locally.  The theorems
    establish value correspondence, rejection, and the no-synthetic-COMM
    property.  Source correspondence, byte canonicalization, and resource
    admission are separate Rust/property-test obligations; this file does not
    claim to prove those implementation details.
*)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Module RholangCostSurface.

(** A resolved ground principal or quote is represented by an opaque natural
    number.  Adapters must supply the exact canonical wire image for that
    number; the shared builder never changes its identity. *)
Inductive Signature : Type :=
| Ground (principal : nat)
| Quote (process : nat)
| Compound (lhs rhs : Signature)
| Transfer (source target : Signature).

Inductive WireSignature : Type :=
| WGround (principal : nat)
| WQuote (process : nat)
| WCompound (lhs rhs : WireSignature).

Fixpoint direct_signature (sig : Signature) : option WireSignature :=
  match sig with
  | Ground principal => Some (WGround principal)
  | Quote process => Some (WQuote process)
  | Compound lhs rhs =>
      match direct_signature lhs, direct_signature rhs with
      | Some l, Some r => Some (WCompound l r)
      | _, _ => None
      end
  | Transfer _ _ => None
  end.

(** An event stream is postorder.  [BuildCompound] consumes the right and then
    the left stack values, restoring the authored left-to-right operand order. *)
Inductive Event : Type :=
| PushGround (principal : nat)
| PushQuote (process : nat)
| BuildCompound.

Fixpoint code (sig : Signature) : option (list Event) :=
  match sig with
  | Ground principal => Some [PushGround principal]
  | Quote process => Some [PushQuote process]
  | Compound lhs rhs =>
      match code lhs, code rhs with
      | Some l, Some r => Some (l ++ r ++ [BuildCompound])
      | _, _ => None
      end
  | Transfer _ _ => None
  end.

Definition step (event : Event) (stack : list WireSignature)
    : option (list WireSignature) :=
  match event with
  | PushGround principal => Some (WGround principal :: stack)
  | PushQuote process => Some (WQuote process :: stack)
  | BuildCompound =>
      match stack with
      | rhs :: lhs :: rest => Some (WCompound lhs rhs :: rest)
      | _ => None
      end
  end.

Fixpoint run (events : list Event) (stack : list WireSignature)
    : option (list WireSignature) :=
  match events with
  | [] => Some stack
  | event :: rest =>
      match step event stack with
      | Some next => run rest next
      | None => None
      end
  end.

Lemma run_app : forall first second stack,
  run (first ++ second) stack =
    match run first stack with
    | Some next => run second next
    | None => None
    end.
Proof.
  induction first as [|event first IH]; intros second stack; cbn.
  - reflexivity.
  - destruct (step event stack) as [next|]; cbn; auto.
Qed.

Theorem fundable_code_is_exact : forall sig value events,
  direct_signature sig = Some value ->
  code sig = Some events ->
  forall stack, run events stack = Some (value :: stack).
Proof.
  induction sig as [principal|process|lhs IHl rhs IHr|source IHs target IHt];
    intros value events Hvalue Hcode stack; cbn in Hvalue, Hcode.
  - inversion Hvalue; inversion Hcode; subst; reflexivity.
  - inversion Hvalue; inversion Hcode; subst; reflexivity.
  - destruct (direct_signature lhs) as [left_value|] eqn:Hleft;
      try discriminate.
    destruct (direct_signature rhs) as [right_value|] eqn:Hright;
      try discriminate.
    destruct (code lhs) as [left_code|] eqn:Cleft; try discriminate.
    destruct (code rhs) as [right_code|] eqn:Cright; try discriminate.
    inversion Hvalue; inversion Hcode; subst; clear Hvalue Hcode.
    rewrite run_app.
    rewrite (IHl left_value left_code eq_refl eq_refl stack).
    rewrite run_app.
    rewrite (IHr right_value right_code eq_refl eq_refl
      (left_value :: stack)).
    reflexivity.
  - discriminate.
Qed.

Theorem transfer_is_not_fundable : forall source target,
  direct_signature (Transfer source target) = None /\
  code (Transfer source target) = None.
Proof. intros; split; reflexivity. Qed.

Theorem compound_events_preserve_authored_order : forall lhs rhs,
  run [PushGround lhs; PushGround rhs; BuildCompound] [] =
    Some [WCompound (WGround lhs) (WGround rhs)].
Proof. reflexivity. Qed.

(** Signed receives have one rendezvous.  Uniform signing annotates an
    unsigned continuation with the same authority; lollipop annotates the
    rendezvous with its source and the continuation with its target.  Neither
    transformation synthesizes a fuel-gate receive. *)
Inductive Process : Type :=
| Atom (payload : nat)
| Receive (channel : nat) (continuation : Process)
| Signed (sig : Signature) (body : Process).

Definition rewrite_signed (sig : Signature) (body : Process)
    : option Process :=
  match sig, body with
  | Transfer source target, Receive channel continuation =>
      Some (Signed source
        (Receive channel (Signed target continuation)))
  | Transfer _ _, _ => None
  | _, Receive channel continuation =>
      Some (Signed sig (Receive channel
        (match continuation with
         | Signed _ _ => continuation
         | _ => Signed sig continuation
         end)))
  | _, _ => Some (Signed sig body)
  end.

Fixpoint receive_count (body : Process) : nat :=
  match body with
  | Atom _ => 0
  | Receive _ continuation => S (receive_count continuation)
  | Signed _ inner => receive_count inner
  end.

Theorem signed_rewrite_never_adds_a_receive : forall sig body result,
  rewrite_signed sig body = Some result ->
  receive_count result = receive_count body.
Proof.
  intros sig body result H.
  destruct sig; destruct body; cbn in H;
    try (inversion H; subst; cbn; reflexivity);
    try discriminate;
    destruct body; inversion H; subst; cbn; reflexivity.
Qed.

Theorem lollipop_reassigns_only_the_continuation :
  forall source target channel continuation,
  rewrite_signed (Transfer source target)
    (Receive channel continuation) =
    Some (Signed source
      (Receive channel (Signed target continuation))).
Proof. reflexivity. Qed.

Theorem lollipop_without_receive_is_rejected :
  forall source target payload,
  rewrite_signed (Transfer source target) (Atom payload) = None.
Proof. reflexivity. Qed.

Theorem uniform_sign_keeps_an_already_signed_continuation :
  forall sig channel continuation_sig continuation,
  rewrite_signed sig
    (Receive channel (Signed continuation_sig continuation)) =
  match sig with
  | Transfer source target =>
      Some (Signed source
        (Receive channel (Signed target
          (Signed continuation_sig continuation))))
  | _ =>
      Some (Signed sig
        (Receive channel (Signed continuation_sig continuation)))
  end.
Proof. intros; destruct sig; reflexivity. Qed.

End RholangCostSurface.
