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

Inductive atom_string (s1 : string) : Prop :=
(* TODO: s1 is made of atom characters *)
.

Inductive after_atom_string (s : string) (more : bool) : Prop :=
 (* TODO: s does not start with an atom character *)
.

Inductive string_string (s0 : string) (s1 : string) : Prop :=
(* TODO: s1 = "s0" *)
.

(* Lexer relation: [token_string more ts s] if the string [s] can be split into tokens [ts].
   - Handling of spaces and comments.
   - Corner cases for spaces around atoms (["ab"] should not be parsed as ["a"] then ["b"]).
   - [more] is true if the last token is an [Token.Atom] and there are no more
     characters after it, in which case we need to be careful to append something.
 *)
Inductive token_string (more : bool) : list Token.t -> string -> Prop :=
| token_string_nil : token_string more [] ""
| token_string_spaces ts ws s
  : whitespaces ws -> token_string more ts s -> token_string more ts (ws ++ s)
| token_string_comment ts c s
  : comment c -> token_string more ts s -> token_string more ts (c ++ s)
| token_string_open ts s
  : token_string more ts s -> token_string more (Token.Open :: ts) ("(" :: s)
| token_string_close ts s
  : token_string more ts s -> token_string more (Token.Close :: ts) (")" :: s)
| token_string_atom ts s1 s
  : atom_string s1 -> after_atom_string s more ->
    token_string more ts s -> token_string more (Token.Atom s1 :: ts) (s1 ++ s)
| token_string_string ts s0 s1 s
  : string_string s0 s1 -> token_string more ts s -> token_string more (Token.Str s0 :: ts) (s1 ++ s)
.
Hint Constructors token_string : core.

Inductive more_ok : bool -> string -> Prop :=
| more_ok_false s : more_ok false s
| more_ok_true c s : (* TODO c is not an Atom character *) more_ok true (c :: s)
.
Hint Constructors more_ok : core.

Lemma more_ok_nil_inv more : more_ok more "" -> more = false.
Proof.
  inversion 1; reflexivity.
Qed.

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

(* * Lemmas *)

Lemma string_app_assoc (s0 s1 s2 : string)
  : ((s0 ++ s1) ++ s2 = s0 ++ (s1 ++ s2))%string.
Proof.
  induction s0; cbn; [ auto | rewrite IHs0; auto ].
Qed.

Lemma after_atom_string_open_app s more :
  after_atom_string (s ++ "(") more.
Proof.
Admitted.

Lemma token_string_open_app more ts s :
  token_string more ts s ->
  token_string false (ts ++ [Token.Open]) (s ++ "(").
Proof.
  induction 1; cbn; try rewrite (string_app_assoc _ _ "("%string); eauto.
  apply token_string_atom; auto.
  apply after_atom_string_open_app.
Qed.

(* * Parser state *)

Inductive stack_tokens : list symbol -> list Token.t -> Prop :=
| stack_tokens_nil : stack_tokens [] []
| stack_tokens_open p us ts
  : stack_tokens us ts ->
    stack_tokens (Open p :: us) (ts ++ [Token.Open])
| stack_tokens_sexp e us ts ts0
  : sexp_tokens e ts0 ->
    stack_tokens us ts ->
    stack_tokens (Exp e :: us) (ts ++ ts0)
.
Hint Constructors stack_tokens : core.

Definition escape_to_string (e : escape) : string :=
  match e with
  | EscBackslash => "\"
  | EscNone => ""
  end.

Definition nonewline (s : string) : Prop.
Admitted.

Inductive partial_token_string : partial_token -> string -> Prop :=
| partial_token_string_NoToken
  : partial_token_string NoToken ""
| partial_token_string_SimpleToken p s
  : partial_token_string (SimpleToken p s) s
| partial_token_string_StrToken p tok e
  : partial_token_string (StrToken p tok e) ("""" :: string_reverse tok ++ escape_to_string e)
| partial_token_string_Comment s
  : nonewline s ->
    partial_token_string Comment (";" :: s)
.
Hint Constructors partial_token_string : core.

(* Invariant on the parsed prefix *)
Inductive parser_state_string (i : parser_state) : string -> Prop :=
| parser_state_string_mk more ts00 ts01 s0 s1
  : token_string more (ts00 ++ ts01) s0 ->
    more_ok more s1 ->
    list_sexp_tokens (parser_done i) ts00 ->
    stack_tokens (parser_stack i) ts01 ->
    partial_token_string (parser_cur_token i) s1 ->
    parser_state_string i (s0 ++ s1)
.

Definition on_right {A B} (x : A + B) (P : B -> Prop) : Prop :=
  match x with
  | inl _ => True
  | inr b => P b
  end.

Ltac match_ascii :=
  repeat
    match goal with
    | [ |- context E [ eqb_ascii ?x ?y ] ] =>
      destruct (eqb_eq_ascii' x y)
    end.

Lemma string_app_nil_r (s : string) : (s ++ "")%string = s.
Proof.
  induction s; [ auto | cbn; rewrite IHs; auto ].
Qed.

Lemma next_sound i s p c
  : parser_state_string i s ->
    on_right (next i p c) (fun i' =>
      parser_state_string i' (s ++ c :: "")).
Proof.
  intros [more ts00 ts01 s0 s1 Hs0 Hmore Hdone Hstack Hcur].
  unfold next.
  destruct Hcur as [ | p1' s1' | p1 tok e | s1' Hs ].
  - (* NoToken *)
    unfold next'.
    apply more_ok_nil_inv in Hmore; subst more.
    rewrite string_app_nil_r.
    match_ascii; cbn.
    + (* "(" *)
      rewrite <- (string_app_nil_r (s0 ++ "(")).
      apply parser_state_string_mk
        with (more := false) (ts00 := ts00) (ts01 := ts01 ++ [Token.Open]);
        cbn; auto.
      rewrite app_assoc; eapply token_string_open_app; eauto.
    + (* ")" *)
      admit.
    + (* """" (double quote char) *)
      apply parser_state_string_mk
        with (more := false) (ts00 := ts00) (ts01 := ts01);
        cbn; auto.
      constructor.
    + (* ";" *)
      apply parser_state_string_mk
        with (more := false) (ts00 := ts00) (ts01 := ts01);
        cbn; auto.
      constructor.
      admit.
    + (* else *)
      destruct (is_whitespace _) eqn:Hws; cbn.
      * rewrite <- (string_app_nil_r (s0 ++ y :: "")).
        apply parser_state_string_mk
          with (more := false) (ts00 := ts00) (ts01 := ts01);
          cbn; auto.
        admit.
      * admit.
  - (* SimpleToken *)
    unfold next'.
    match_ascii; cbn.
    + (* "(" *)
      rewrite <- (string_app_nil_r (_ ++ "(")).
      apply parser_state_string_mk
        with (more := false) (ts00 := ts00) (ts01 := ts01 ++ [Token.Open]);
        cbn; auto.
      * rewrite app_assoc; apply token_string_open_app with (more := true); eauto.
        admit.
      * admit.
      * admit.
    + (* ")" *)
      admit.
    + (* """" *)
      admit.
    + (* ";" *)
      admit.
    + (* else *)
      admit.
  - (* StrToken *)
    admit.
  - (* Comment *)
    admit.
Abort.

(*
Lemma _parse_sexps_sound (s : string) (es : list sexp)
  : parse_sexps_ s = inr es ->
    exists ts,
      list_sexp_tokens es ts /\ token_string ts s.
Proof.
*)

(* If the parser succeeds, then the expressions relate to the above *)
Theorem parse_sexps_sound (s : string) (es : list sexp)
  : parse_sexps s = inr es ->
    exists more ts,
      list_sexp_tokens es ts /\ token_string more ts s.
Proof.
Abort.
