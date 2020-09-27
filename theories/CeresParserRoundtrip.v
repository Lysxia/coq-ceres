From Coq Require Import
  Ascii
  String
  List
  ZArith.
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

Inductive whitespaces : string -> Prop :=
(* TODO *)
.

Inductive comment : string -> Prop :=
(* TODO *)
.

Inductive atom_string (s1 s : string) : Prop :=
(* TODO: s1 is made of atom characters and s does not start with an atom character *)
.

Inductive string_string (s0 : string) (s1 : string) : Prop :=
(* TODO: s1 = "s0" *)
.

(* Lexer relation: [token_string ts s] if the string [s] can be split into tokens [ts].
   - Handling of spaces and comments.
   - Corner cases for spaces around atoms (["ab"] should not be parsed as ["a"] then ["b"]).
 *)
Inductive token_string : list Token.t -> string -> Prop :=
| token_string_nil : token_string [] ""
| token_string_spaces ts ws s : whitespaces ws -> token_string ts s -> token_string ts (ws ++ s)
| token_string_comment ts c s : comment c -> token_string ts s -> token_string ts (c ++ s)
| token_string_open ts s : token_string ts s -> token_string (Token.Open :: ts) ("(" :: s)
| token_string_close ts s : token_string ts s -> token_string (Token.Close :: ts) (")" :: s)
| token_string_atom ts s1 s
  : atom_string s1 s -> token_string ts s -> token_string (Token.Atom s1 :: ts) (s1 ++ s)
| token_string_string ts s0 s1 s
  : string_string s0 s1 -> token_string ts s -> token_string (Token.Str s0 :: ts) (s1 ++ s)
.

(* * Parser *)

Inductive list_tokens {A B} (tks : A -> list B -> Prop) : list A -> list B -> Prop :=
| list_tokens_nil : list_tokens tks [] []
| list_tokens_cons x xs y ys
  : tks x y -> list_tokens tks xs ys -> list_tokens tks (x :: xs) (y ++ ys)
.

Inductive atom_token : atom -> Token.t -> Prop :=
| atom_token_Raw s : atom_token (Raw s) (Token.Atom s)
| atom_token_Num z : atom_token (Num z) (Token.Atom (string_of_Z z))
| atom_token_Str s : atom_token (Str s) (Token.Str s)
.

Inductive sexp_tokens : sexp -> list Token.t -> Prop :=
| sexp_tokens_Atom a t : atom_token a t -> sexp_tokens (Atom_ a) [t]
| sexp_tokens_List es ts
  : list_tokens sexp_tokens es ts -> sexp_tokens (List es) (Token.Open :: ts ++ [Token.Close])
.

Definition list_sexp_tokens := list_tokens sexp_tokens.

(* If the parser succeeds, then the expressions relate to the above *)
Theorem parse_sexps_sound (s : string) (es : list sexp)
  : parse_sexps s = inr es ->
    exists ts,
      list_sexp_tokens es ts /\ token_string ts s.
Proof.
Abort.
