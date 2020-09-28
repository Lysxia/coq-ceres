(** * S-expression parser *)

(* begin hide *)
From Coq Require Import Bool List ZArith NArith Ascii String Decimal DecimalString.

From Ceres Require Import CeresS CeresString.

Import ListNotations.
Local Open Scope lazy_bool_scope.
(* end hide *)

(** Location in a string *)
Definition loc : Set := N.

Definition pretty_loc (p : loc) : string := string_of_N p.

(** Symbols on the stack *)
Variant symbol : Set :=
| Open : loc -> symbol
| Exp : sexp -> symbol
.

(** When parsing strings, whether we are parsing an escape character. *)
Variant escape : Set :=
| EscBackslash
| EscNone
.

(** Tokenizer state. *)
Variant partial_token : Set :=
| NoToken : partial_token
| SimpleToken : loc -> string -> partial_token
| StrToken : loc -> string -> escape -> partial_token
| Comment : partial_token
.

Record parser_state_ {T : Type} : Type :=
  { parser_done : list sexp
  ; parser_stack : list symbol
  ; parser_cur_token : T
  }.
Arguments parser_state_ : clear implicits.

Definition set_cur_token {T U} (i : parser_state_ T) (u : U) : parser_state_ U :=
  {| parser_done := parser_done i
   ; parser_stack := parser_stack i
   ; parser_cur_token := u
  |}.

Definition parser_state := parser_state_ partial_token.

Definition initial_state : parser_state :=
  {| parser_done := nil
   ; parser_stack := nil
   ; parser_cur_token := NoToken
  |}.

(** Errors which may be raised by the parser. *)
Variant error :=
| UnmatchedClose : loc -> error
| UnmatchedOpen : loc -> error
| UnknownEscape : loc -> ascii -> error
| UnterminatedString : loc -> error
| EmptyInput : error
| InvalidChar : ascii -> loc -> error
.

Definition pretty_error (e : error) :=
  match e with
  | UnmatchedClose p => "Unmatched close parenthesis at location " ++ pretty_loc p
  | UnmatchedOpen p => "Unmatched open parenthesis at location " ++ pretty_loc p
  | UnknownEscape p c => "Unknown escape code '\" ++ c :: "' at location " ++ pretty_loc p
  | UnterminatedString p => "Unterminated string starting at location " ++ pretty_loc p
  | EmptyInput => "Input is empty"
  | InvalidChar c p => "Invalid character " ++ "TODO" ++ " at location " ++ pretty_loc p
  end%string.

Definition is_atom_char (c : ascii) : bool :=
  (is_alphanum c ||| string_elem c "=-+*/:!@#$%^&_<>").

Definition new_sexp {T : Set} (d : list sexp) (s : list symbol) (e : sexp) (t : T)
  : parser_state_ T :=
  match s with
  | nil =>
    {| parser_done := e :: d
     ; parser_stack := nil
     ; parser_cur_token := t
    |}
  | (_ :: _)%list =>
    {| parser_done := d
     ; parser_stack := Exp e :: s
     ; parser_cur_token := t
    |}
  end.

(** Parse next character of a string literal. *)
Definition next_str (i : parser_state) (p0 : loc) (tok : string) (e : escape) (p : loc) (c : ascii)
  : error + parser_state :=
  let '{| parser_done := d; parser_stack := s |} := i in
  let ret (tok' : string) e' := inr
    {| parser_done := d
     ; parser_stack := s
     ; parser_cur_token := StrToken p0 tok' e'
    |} in
  match e, c with
  | EscBackslash, "n"%char => ret ("010" :: tok)%string EscNone
  | EscBackslash, "\"%char => ret ("\" :: tok)%string EscNone
  | EscBackslash, """"%char => ret ("""" :: tok)%string EscNone
  | EscBackslash, _ => inl (UnknownEscape p c)
  | EscNone, "\"%char => ret tok EscBackslash
  | EscNone, """"%char => inr (new_sexp d s (Atom (Str (string_reverse tok))) NoToken)
  | EscNone, c => ret (c :: tok)%string EscNone
  end.

(** Close parenthesis: build up a list expression. *)
Fixpoint _fold_stack (d : list sexp) (p : loc) (r : list sexp) (s : list symbol) : error + parser_state :=
  match s with
  | nil => inl (UnmatchedClose p)
  | Open _ :: s => inr (new_sexp d s (List r) NoToken)
  | Exp e :: s => _fold_stack d p (e :: r) s
  end%list.

(** Parse next character outside of a string literal. *)
Definition next' {T} (i : parser_state_ T) (p : loc) (c : ascii)
  : error + parser_state :=
  (if "(" =? c then inr
    {| parser_done := parser_done i
     ; parser_stack := Open p :: parser_stack i
     ; parser_cur_token := NoToken
    |}
  else if ")" =? c then
    _fold_stack (parser_done i) p nil (parser_stack i)
  else if """" =? c then
    inr (set_cur_token i (StrToken p "" EscNone))
  else if ";" =? c then
    inr (set_cur_token i Comment)
  else if is_whitespace c then
    inr (set_cur_token i NoToken)
  else inl (InvalidChar c p))%char2.

(** Parse next character in a comment. *)
Definition next_comment (i : parser_state) (c : ascii) : error + parser_state :=
  if eqb_ascii "010" c then inr
    {| parser_done := parser_done i
     ; parser_stack := parser_stack i
     ; parser_cur_token := NoToken
    |}
  else inr i.

(** Construct an atom. Make it a [Num] if it can be parsed as a number,
    [Raw] otherwise. *)
Definition raw_or_num (s : string) : atom :=
  let s := string_reverse s in
  match NilZero.int_of_string s with
  | None => Raw s
  | Some n => Num (Z.of_int n)
  end.

(** Consume one more character. *)
Definition next (i : parser_state) (p : loc) (c : ascii) : error + parser_state :=
  match parser_cur_token i with
  | StrToken p0 tok e => next_str i p0 tok e p c
  | NoToken =>
    if is_atom_char c
    then inr (set_cur_token i (SimpleToken p (c :: "")))
    else next' i p c
  | SimpleToken _ tok =>
    if is_atom_char c
    then inr (set_cur_token i (SimpleToken p (c :: tok)))
    else
      let i' := new_sexp (parser_done i) (parser_stack i) (Atom (raw_or_num tok)) tt in
      next' i' p c
  | Comment => next_comment i c
  end.

(** Return all toplevel S-expressions, or fail if there is still an unmatched open parenthesis. *)
Fixpoint _done_or_fail (r : list sexp) (s : list symbol) : error + list sexp :=
  match s with
  | nil => inr (List.rev' r)
  | Exp e :: s => _done_or_fail r s  (* Here the last symbol in [s] must be an [Open] *)
  | Open p :: _ => inl (UnmatchedOpen p)
  end%list.

(** End of the string/file, get the final result. *)
Definition eof (i : parser_state) (p : loc) : error + list sexp :=
  match parser_cur_token i with
  | StrToken p0 _ _ => inl (UnterminatedString p0)
  | (NoToken | Comment) => _done_or_fail (parser_done i) (parser_stack i)
  | SimpleToken _ tok =>
    let i := new_sexp (parser_done i) (parser_stack i) (Atom (raw_or_num tok)) tt
    in _done_or_fail (parser_done i) (parser_stack i)
  end.

(** Remove successfully parsed toplevel expressions from the parser state. *)
Definition get_done (i : parser_state) : list sexp * parser_state :=
  ( List.rev' (parser_done i)
  , {| parser_done := nil
     ; parser_stack := parser_stack i
     ; parser_cur_token := parser_cur_token i
    |}
  ).

Definition get_one (i : parser_state) : option sexp * parser_state :=
  match parser_done i with
  | nil => (None, i)
  | cons e _ as es =>
    (Some (List.last es e),
     {| parser_done      := List.removelast  es;
        parser_stack     := parser_stack     i;
        parser_cur_token := parser_cur_token i |})
  end.

(** Parse a string and return the location and state at the end if no error occured (to
    resume in another string, or finish with [eof]), or the last known good
    location and state in case of an error (to read toplevel valid
    S-expressions from). *)
Fixpoint parse_sexps_ (i : parser_state) (p : loc) (s : string) : option error * loc * parser_state :=
  match s with
  | "" => (None, p, i)
  | c :: s =>
    match next i p c with
    | inl e => (Some e, p, i)
    | inr i => parse_sexps_ i (N.succ p) s
    end
  end%string.

(** Parse a string into a list of S-expressions. *)
Definition parse_sexps (s : string) : error + list sexp :=
  match parse_sexps_ initial_state 0%N s with
  | (None, p, i) => eof i p
  | (Some e, _, _) => inl e
  end.

(** Parse a string into one S-expression. Subsequent expressions, if any, are ignored. *)
Definition parse_sexp (s : string) : error + sexp :=
  let '(e, p, i) := parse_sexps_ initial_state 0%N s in
  match List.rev' (parser_done i), e with
  | (r :: _)%list, _ => inr r
  | nil, Some e => inl e
  | nil, None =>
    match eof i p with
    | inl e => inl e
    | inr (r :: _)%list => inr r
    | inr nil => inl EmptyInput
    end
  end.
