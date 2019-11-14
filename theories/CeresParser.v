(** * S-expression parser *)

(* begin hide *)
From Coq Require Import ZArith NArith Ascii String Decimal DecimalString.

From Ceres Require Import CeresS CeresString.
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

Record parser_state : Set :=
  { parser_done : list sexp
  ; parser_stack : list symbol
  ; parser_cur_token : partial_token
  }.

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
.

Definition pretty_error (e : error) :=
  match e with
  | UnmatchedClose p => "Unmatched close parenthesis at location " ++ pretty_loc p
  | UnmatchedOpen p => "Unmatched open parenthesis at location " ++ pretty_loc p
  | UnknownEscape p c => "Unknown escape code '\" ++ c :: "' at location " ++ pretty_loc p
  | UnterminatedString p => "Unterminated string starting at location " ++ pretty_loc p
  | EmptyInput => "Input is empty"
  end%string.

Definition new_sexp (d : list sexp) (s : list symbol) (t : partial_token) (e : sexp)
  : parser_state :=
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
Definition next_str (s0 : parser_state) (p0 : loc) (tok : string) (e : escape) (p : loc) (c : ascii)
  : error + parser_state :=
  let '{| parser_done := d; parser_stack := s |} := s0 in
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
  | EscNone, """"%char => inr (new_sexp d s NoToken (Atom (Str (string_reverse tok))))
  | EscNone, c => ret (c :: tok)%string EscNone
  end.

(** Close parenthesis: build up a list expression. *)
Fixpoint _fold_stack (d : list sexp) (p : loc) (r : list sexp) (s : list symbol) : error + parser_state :=
  match s with
  | nil => inl (UnmatchedClose p)
  | Open _ :: s => inr (new_sexp d s NoToken (List r))
  | Exp e :: s => _fold_stack d p (e :: r) s
  end%list.

(** Parse next character outside of a string literal. *)
Definition next' (s0 : parser_state) (s' : partial_token -> parser_state) (tok : string) (p : loc) (c : ascii)
  : error + parser_state :=
  match c with
  | "("%char =>
    let s0 := s' NoToken in inr
    {| parser_done := parser_done s0
     ; parser_stack := Open p :: parser_stack s0
     ; parser_cur_token := NoToken
    |}
  | ")"%char =>
    let s0 := s' NoToken in
    _fold_stack (parser_done s0) p nil (parser_stack s0)
  | """"%char => inr (s' (StrToken p "" EscNone))
  | ";"%char => inr (s' Comment)
  | _ =>
    if is_whitespace c then inr (s' NoToken)
    else inr
      {| parser_done := parser_done s0
       ; parser_stack := parser_stack s0
       ; parser_cur_token := SimpleToken p (c :: tok)
      |}
  end.

(** Parse next character in a comment. *)
Definition next_comment (s : parser_state) (c : ascii) : error + parser_state :=
  match c with
  | "010"%char => inr
    {| parser_done := parser_done s
     ; parser_stack := parser_stack s
     ; parser_cur_token := NoToken
    |}
  | _ => inr s
  end.

(** Construct an atom. Make it a [Num] if it can be parsed as a number,
    [Raw] otherwise. *)
Definition raw_or_num (s : string) : atom :=
  let s := string_reverse s in
  match NilZero.int_of_string s with
  | None => Raw s
  | Some n => Num (Z.of_int n)
  end.

(** Consume one more character. *)
Definition next (s0 : parser_state) (p : loc) (c : ascii) : error + parser_state :=
  match parser_cur_token s0 with
  | StrToken p0 tok e => next_str s0 p0 tok e p c
  | NoToken =>
    let s' t :=
      {| parser_done := parser_done s0
       ; parser_stack := parser_stack s0
       ; parser_cur_token := t
      |}
    in next' s0 s' "" p c
  | SimpleToken _ tok =>
    let s' t := new_sexp (parser_done s0) (parser_stack s0) t (Atom (raw_or_num tok)) in
    next' s0 s' tok p c
  | Comment => next_comment s0 c
  end.

(** Return all toplevel S-expressions, or fail if there is still an unmatched open parenthesis. *)
Fixpoint _done_or_fail (r : list sexp) (s : list symbol) : error + list sexp :=
  match s with
  | nil => inr (List.rev' r)
  | Exp e :: s => _done_or_fail r s  (* Here the last symbol in [s] must be an [Open] *)
  | Open p :: _ => inl (UnmatchedOpen p)
  end%list.

(** End of the string/file, get the final result. *)
Definition eof (s0 : parser_state) (p : loc) : error + list sexp :=
  match parser_cur_token s0 with
  | StrToken p0 _ _ => inl (UnterminatedString p0)
  | (NoToken | Comment) => _done_or_fail (parser_done s0) (parser_stack s0)
  | SimpleToken _ tok =>
    let s0 := new_sexp (parser_done s0) (parser_stack s0) NoToken (Atom (raw_or_num tok))
    in _done_or_fail (parser_done s0) (parser_stack s0)
  end.

(** Remove successfully parsed toplevel expressions from the parser state. *)
Definition get_done (s0 : parser_state) : list sexp * parser_state :=
  ( List.rev' (parser_done s0)
  , {| parser_done := nil
     ; parser_stack := parser_stack s0
     ; parser_cur_token := parser_cur_token s0
    |}
  ).

Definition get_one (s0 : parser_state) : option sexp * parser_state :=
  match parser_done s0 with
  | nil => (None, s0)
  | cons e _ as es =>
    (Some (List.last es e),
     {| parser_done      := List.removelast  es;
        parser_stack     := parser_stack     s0;
        parser_cur_token := parser_cur_token s0 |})
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
