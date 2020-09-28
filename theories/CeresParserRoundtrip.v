From Coq Require Import
  Ascii
  String
  List
  ZArith
  DecimalString.
From Ceres Require Import
  CeresS
  CeresString
  CeresParser.

Import ListNotations.

Module Token.

Inductive t : Type :=
| Open : t
| Close : t
| Atom (s : string) : t
| Str (s : string) : t
.

End Token.

(* * Lexer *)

Definition whitespaces (s : string) : Prop :=
  string_forall is_whitespace s = true.

Inductive comment : string -> Prop :=
| comment_mk s : comment (";" :: s ++ newline)
.

Definition atom_string (s : string) : Prop :=
  s <> ""%string /\ string_forall is_atom_char s = true.

Inductive after_atom_string : string -> bool -> Prop :=
| after_atom_nil : after_atom_string "" true
| after_atom_cons c s more : is_atom_char c = false -> after_atom_string (c :: s) more
.
Hint Constructors after_atom_string : ceres.

Definition string_string (s0 : string) (s1 : string) : Prop :=
  s1 = ("""" :: _escape_string "" s0 ++ """")%string.

(* Lexer relation: [token_string more ts s] if the string [s] can be split into tokens [ts].
   - Handling of spaces and comments.
   - Corner cases for spaces around atoms (["ab"] should not be parsed as ["a"] then ["b"]).
   - [more] is true if the last token is an [Token.Atom] and there are no more
     characters after it, in which case we need to be careful to append something.
 *)
Inductive token_string (more : bool) : list Token.t -> string -> Prop :=
| token_string_nil : token_string more [] ""
| token_string_open ts s
  : token_string more ts s -> token_string more (Token.Open :: ts) ("(" :: s)
| token_string_close ts s
  : token_string more ts s -> token_string more (Token.Close :: ts) (")" :: s)
| token_string_atom ts s1 s
  : atom_string s1 -> after_atom_string s more ->
    token_string more ts s -> token_string more (Token.Atom s1 :: ts) (s1 ++ s)
| token_string_string ts s0 s1 s
  : string_string s0 s1 -> token_string more ts s -> token_string more (Token.Str s0 :: ts) (s1 ++ s)
| token_string_spaces ts ws s
  : whitespaces ws -> token_string more ts s -> token_string more ts (ws ++ s)
| token_string_comment ts c s
  : comment c -> token_string more ts s -> token_string more ts (c ++ s)
.
Hint Constructors token_string : ceres.

Inductive more_ok : bool -> string -> Prop :=
| more_ok_false s : more_ok false s
| more_ok_true c s : is_atom_char c = false -> more_ok true (c :: s)
.
Hint Constructors more_ok : ceres.

Lemma more_ok_nil_inv more : more_ok more "" -> more = false.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma more_ok_cons more c s : is_atom_char c = false -> more_ok more (c :: s).
Proof.
  destruct more; auto with ceres.
Qed.

(* * Parser *)

Inductive list_tokens {A B} (tks : A -> list B -> Prop) : list A -> list B -> Prop :=
| list_tokens_nil : list_tokens tks [] []
| list_tokens_cons x xs y ys
  : tks x y -> list_tokens tks xs ys -> list_tokens tks (x :: xs) (y ++ ys)
.
Hint Constructors list_tokens : ceres.

Inductive atom_token : atom -> Token.t -> Prop :=
| atom_token_Raw s : atom_token (Raw s) (Token.Atom s)
| atom_token_Num s z
  : NilZero.int_of_string s = Some z ->
    atom_token (Num (Z.of_int z)) (Token.Atom s)
| atom_token_Str s : atom_token (Str s) (Token.Str s)
.
Hint Constructors atom_token : ceres.

Inductive sexp_tokens : sexp -> list Token.t -> Prop :=
| sexp_tokens_Atom a t : atom_token a t -> sexp_tokens (Atom_ a) [t]
| sexp_tokens_List es ts
  : list_tokens sexp_tokens es ts ->
    sexp_tokens (List es) (Token.Open :: ts ++ [Token.Close])
.
Hint Constructors sexp_tokens : ceres.

Notation list_sexp_tokens := (list_tokens sexp_tokens).

Definition on_right {A B} (x : A + B) (P : B -> Prop) : Prop :=
  match x with
  | inl _ => True
  | inr b => P b
  end.

(* If the parser succeeds, then the expressions relate to the input string. *)
Definition PARSE_SEXPS_SOUND : Prop :=
  forall (s : string) (es : list sexp),
    on_right (parse_sexps s) (fun es =>
      exists ts, list_sexp_tokens es ts /\ token_string false ts (s ++ newline)).

(* TODO: Completeness *)
