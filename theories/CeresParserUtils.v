From Coq Require Import Bool NArith String Ascii.

From Ceres Require Import CeresString.

Local Open Scope lazy_bool_scope.

(** Location in a string *)
Definition loc : Set := N.

Definition pretty_loc (p : loc) : string := string_of_N p.

(** Errors which may be raised by the parser. *)
Variant error :=
| UnmatchedClose : loc -> error
| UnmatchedOpen : loc -> error
| UnknownEscape : loc -> ascii -> error
| UnterminatedString : loc -> error
| EmptyInput : error
| InvalidChar : ascii -> loc -> error
| InvalidStringChar : ascii -> loc -> error
.

Definition pretty_error (e : error) :=
  match e with
  | UnmatchedClose p => "Unmatched close parenthesis at location " ++ pretty_loc p
  | UnmatchedOpen p => "Unmatched open parenthesis at location " ++ pretty_loc p
  | UnknownEscape p c => "Unknown escape code '\" ++ c :: "' at location " ++ pretty_loc p
  | UnterminatedString p => "Unterminated string starting at location " ++ pretty_loc p
  | EmptyInput => "Input is empty"
  | InvalidChar c p =>
    "Invalid character " ++ escape_string (c :: "") ++ " at location " ++ pretty_loc p
  | InvalidStringChar c p =>
    "Invalid character inside string " ++ escape_string (c :: "") ++ " at location " ++ pretty_loc p
  end%string.

Definition is_atom_char (c : ascii) : bool :=
  (is_alphanum c ||| string_elem c "'=-+*/:!?@#$%^&_<>.,|~").
