(** The authored `token Name ::= Reg;` boundary is a lexical-mode protocol.
    The model deliberately does not redefine PraTTaIL regex semantics: typed
    regex pieces render their exact source spelling, and the existing regex
    compiler is the sole validator of that pattern. The Rust refinement must
    establish that each generated token maps to the corresponding constructor
    and that `::=` has no accepting identifier co-reading. *)
From Stdlib Require Import List String.
Import ListNotations.
Open Scope string_scope.

Module AuthoredRegexBoundary.

Inductive Mode := Host | Regex | Class.

Inductive Piece :=
  | BeginRegex
  | EndRegex
  | OpenClass
  | CloseClass
  | HostIdentifier (spelling : string)
  | RegexPiece (spelling : string)
  | ClassPiece (spelling : string).

Definition advance (mode : Mode) (piece : Piece) : option Mode :=
  match mode, piece with
  | Host, BeginRegex => Some Regex
  | Host, HostIdentifier _ => Some Host
  | Regex, EndRegex => Some Host
  | Regex, OpenClass => Some Class
  | Regex, RegexPiece _ => Some Regex
  | Class, CloseClass => Some Regex
  | Class, ClassPiece _ => Some Class
  | _, _ => None
  end.

Fixpoint run (mode : Mode) (pieces : list Piece) : option Mode :=
  match pieces with
  | [] => Some mode
  | piece :: tail =>
      match advance mode piece with
      | Some next => run next tail
      | None => None
      end
  end.

Definition pattern_text (piece : Piece) : string :=
  match piece with
  | OpenClass => "["
  | CloseClass => "]"
  | RegexPiece s | ClassPiece s => s
  | _ => ""
  end.

Definition render (pieces : list Piece) : string :=
  String.concat "" (List.map pattern_text pieces).

Lemma append_empty_right : forall s : string, s ++ "" = s.
Proof. induction s; simpl; congruence. Qed.

Theorem host_identifier_cannot_enter_regex :
  forall s, advance Host (HostIdentifier s) = Some Host.
Proof. reflexivity. Qed.

Theorem delimiter_enters_regex : advance Host BeginRegex = Some Regex.
Proof. reflexivity. Qed.

Theorem regex_end_exits_regex : advance Regex EndRegex = Some Host.
Proof. reflexivity. Qed.

Theorem end_inside_class_is_not_a_declaration_end :
  advance Class EndRegex = None.
Proof. reflexivity. Qed.

Theorem class_semicolon_is_pattern_text :
  advance Class (ClassPiece ";") = Some Class /\
  pattern_text (ClassPiece ";") = ";".
Proof. split; reflexivity. Qed.

Theorem a_closed_class_preserves_its_delimiters :
  forall interior,
    render [OpenClass; ClassPiece interior; CloseClass] =
      "[" ++ interior ++ "]".
Proof. intros; reflexivity. Qed.

Theorem token_spelling_is_preserved :
  forall pieces,
    render pieces = String.concat "" (List.map pattern_text pieces).
Proof. reflexivity. Qed.

Theorem a_well_formed_declaration_returns_to_host :
  forall s,
    run Host [BeginRegex; RegexPiece s; EndRegex] = Some Host.
Proof. reflexivity. Qed.

Theorem a_class_does_not_terminate_at_semicolon :
  run Host [BeginRegex; OpenClass; ClassPiece ";"; CloseClass; EndRegex] =
    Some Host.
Proof. reflexivity. Qed.

End AuthoredRegexBoundary.
