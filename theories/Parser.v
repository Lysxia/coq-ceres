(* begin hide *)
From Coq Require Import ZArith NArith Ascii String Decimal DecimalString.

From Ceres Require Import S String.
(* end hide *)

(** Position in a string *)
Definition pos : Set := N.

Definition pretty_pos (p : pos) : string := string_of_N p.

(** Symbols on the stack *)
Variant symbol : Set :=
| Open : pos -> symbol
| Exp : sexp atom -> symbol
.

Variant escape : Set :=
| EscBackslash
| EscNone
.

Variant partial_token : Set :=
| NoToken : partial_token
| SimpleToken : pos -> string -> partial_token
| StrToken : pos -> string -> escape -> partial_token
| Comment : partial_token
.

Record parser_state : Set :=
  { parser_stack : list symbol
  ; parser_cur_token : partial_token
  }.

Definition initial_state : parser_state :=
  {| parser_stack := nil
   ; parser_cur_token := NoToken
  |}.

Variant error :=
| UnmatchedClose : pos -> error
| UnmatchedOpen : pos -> error
| UnknownEscape : pos -> ascii -> error
| UnterminatedString : pos -> error
| EmptyInput : error
.

Definition pretty_error (e : error) :=
  match e with
  | UnmatchedClose p => "Unmatched close parenthesis at position " ++ pretty_pos p
  | UnmatchedOpen p => "Unmatched open parenthesis at position " ++ pretty_pos p
  | UnknownEscape p c => "Unknown escape code '\" ++ c :: "' at position " ++ pretty_pos p
  | UnterminatedString p => "Unterminated string starting at position " ++ pretty_pos p
  | EmptyInput => "Input is empty"
  end%string.

Definition next_str (s : list symbol) (p0 : pos) (tok : string) (e : escape) (p : pos) (c : ascii)
  : error + parser_state :=
  let ret (tok' : string) e' := inr
    {| parser_stack := s
     ; parser_cur_token := StrToken p0 tok' e'
    |} in
  match e, c with
  | EscBackslash, "n"%char => ret ("010" :: tok)%string EscNone
  | EscBackslash, "\"%char => ret ("\" :: tok)%string EscNone
  | EscBackslash, """"%char => ret ("""" :: tok)%string EscNone
  | EscBackslash, _ => inl (UnknownEscape p c)
  | EscNone, "\"%char => ret tok EscBackslash
  | EscNone, """"%char => inr
    {| parser_stack := Exp (Atom (Str (string_reverse tok))) :: s
     ; parser_cur_token := NoToken
    |}
  | EscNone, c => ret (c :: tok)%string EscNone
  end.

Fixpoint fold_stack (r : list (sexp atom)) (p : pos) (s : list symbol) : error + parser_state :=
  match s with
  | nil => inl (UnmatchedClose p)
  | Open _ :: s => inr
    {| parser_stack := Exp (List r) :: s
     ; parser_cur_token := NoToken
    |}
  | Exp e :: s => fold_stack (e :: r) p s
  end%list.

Definition next' (s : list symbol) (s' : unit -> list symbol) (tok : string) (p : pos) (c : ascii)
  : error + parser_state :=
  match c with
  | "("%char => inr
    {| parser_stack := Open p :: s' tt
     ; parser_cur_token := NoToken
    |}
  | ")"%char => fold_stack nil p (s' tt)
  | """"%char => inr
    {| parser_stack := s' tt
     ; parser_cur_token := StrToken p "" EscNone
    |}
  | ";"%char => inr
    {| parser_stack := s' tt
     ; parser_cur_token := Comment
    |}
  | _ =>
    if is_whitespace c then inr
      {| parser_stack := s' tt
       ; parser_cur_token := NoToken
      |}
    else inr
      {| parser_stack := s
       ; parser_cur_token := SimpleToken p (c :: tok)
      |}
  end.

Definition next_comment (s : parser_state) (c : ascii) : error + parser_state :=
  match c with
  | "010"%char => inr
    {| parser_stack := parser_stack s
     ; parser_cur_token := NoToken
    |}
  | _ => inr s
  end.

Definition raw_or_num (s : string) : atom :=
  match NilZero.int_of_string (string_reverse s) with
  | None => Raw s
  | Some n => Num (Z.of_int n)
  end.

(** Consume one more character. *)
Definition next (s : parser_state) (p : pos) (c : ascii) : error + parser_state :=
  match parser_cur_token s with
  | StrToken p0 tok e => next_str (parser_stack s) p0 tok e p c
  | NoToken => next' (parser_stack s) (fun _ => parser_stack s) "" p c
  | SimpleToken _ tok =>
    next' (parser_stack s) (fun _ => Exp (Atom (raw_or_num tok)) :: parser_stack s)%list tok p c
  | Comment => next_comment s c
  end.

Fixpoint stack_to_list (r : list (sexp atom)) (s : list symbol) : error + list (sexp atom) :=
  match s with
  | nil => inr r
  | Exp e :: s => stack_to_list (e :: r) s
  | Open p :: _ => inl (UnmatchedOpen p)
  end%list.

(** End of the string/file, get the final result. *)
Definition eof (s : parser_state) (p : pos) : error + list (sexp atom) :=
  match parser_cur_token s, parser_stack s with
  | StrToken p0 _ _, _ => inl (UnterminatedString p0)
  | (NoToken | Comment), s => stack_to_list nil s
  | SimpleToken _ tok, s => stack_to_list (Atom (raw_or_num tok) :: nil) s
  end.

Fixpoint _parse_string (i : parser_state) (p : pos) (s : string) : error + list (sexp atom) :=
  match s with
  | "" => eof i p
  | c :: s =>
    match next i p c with
    | inl e => inl e
    | inr i => _parse_string i (N.succ p) s
    end
  end%string.

(** Parse a string into a list of S-expressions. *)
Definition parse_string : string -> error + list (sexp atom) := _parse_string initial_state 0%N.

(** Parse a string into one S-expression. Subsequent expressions, if any, are ignored. *)
Definition parse_one (s : string) : error + sexp atom :=
  match parse_string s with
  | inl e => inl e
  | inr nil => inl EmptyInput
  | inr (e :: _)%list => inr e
  end.
