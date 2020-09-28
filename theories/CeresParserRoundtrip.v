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
Hint Constructors list_tokens : core.

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

Notation list_sexp_tokens := (list_tokens sexp_tokens).

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

Definition is_atom_string (s : string) : Prop.
Admitted.

Lemma is_atom_singleton (c : ascii)
  : is_atom_char c = true -> is_atom_string (c :: "").
Proof.
Admitted.
Hint Resolve is_atom_singleton : ceres.

Lemma is_atom_app (s : string) (c : ascii)
  : is_atom_string s -> is_atom_char c = true -> is_atom_string (s ++ c :: "").
Proof.
Admitted.
Hint Resolve is_atom_app : ceres.

Inductive str_token_string (tok : string) (e : escape) : string -> Prop :=
| str_token_string_mk : str_token_string tok e ("""" :: string_reverse tok ++ escape_to_string e)
.

Inductive partial_token_string : partial_token -> string -> Prop :=
| partial_token_string_NoToken
  : partial_token_string NoToken ""
| partial_token_string_SimpleToken p s s'
  : is_atom_string s' ->
    s' = string_reverse s ->
    partial_token_string (SimpleToken p s) s'
| partial_token_string_StrToken p tok e s'
  : str_token_string tok e s' ->
    partial_token_string (StrToken p tok e) s'
| partial_token_string_Comment s
  : nonewline s ->
    partial_token_string Comment (";" :: s)
.
Hint Constructors partial_token_string : core.

Inductive parser_state_string_
    (more : bool) (d : list sexp) (u : list symbol) (s0 : string) : Prop :=
| parser_state_string_mk_ ts00 ts01
  : token_string more (ts00 ++ ts01) s0 ->
    list_sexp_tokens d ts00 ->
    stack_tokens u ts01 ->
    parser_state_string_ more d u s0
.
Hint Constructors parser_state_string_.

(* Invariant on the parsed prefix *)
Inductive parser_state_string (i : parser_state) : string -> Prop :=
| parser_state_string_mk more s0 s1
  : parser_state_string_ more (parser_done i) (parser_stack i) s0 ->
    more_ok more s1 ->
    partial_token_string (parser_cur_token i) s1 ->
    parser_state_string i (s0 ++ s1)
.
Hint Constructors parser_state_string.

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

Lemma _fold_stack_sound_
    d
    (p : loc)
    (s0 : string)
    (more : bool)
    u
  : forall
    (es : list sexp)
    (ts00 ts01 ts02 : list Token.t)
    (Hs0 : token_string more (ts00 ++ ts01 ++ ts02) s0)
    (Hdone : list_sexp_tokens d ts00)
    (Hstack : stack_tokens u ts01)
    (Hes : list_sexp_tokens es ts02)
  , on_right (_fold_stack d p es u)
      (fun i' : parser_state => parser_state_string i' (s0 ++ ")")).
Proof.
  induction u; cbn; auto; intros.
  destruct a; cbn.
  - admit.
  - inversion Hstack; subst; clear Hstack.
    rewrite <- app_assoc in Hs0.
    specialize IHu with (1 := Hs0).
    apply IHu; auto.
Admitted.

Lemma _fold_stack_sound
    d
    (p : loc)
    (s0 : string)
    (more : bool)
    u
  : parser_state_string_ more d u s0 ->
    on_right (_fold_stack d p [] u)
      (fun i' : parser_state => parser_state_string i' (s0 ++ ")")).
Proof.
  intros [ts00 ts01 ? ?]; apply _fold_stack_sound_
    with (more := more) (ts00 := ts00) (ts01 := ts01) (ts02 := []); auto.
  rewrite app_nil_r; auto.
Qed.

Lemma next_sound' {T} (i : parser_state_ T) (more : bool) s0 p c
  : parser_state_string_ more (parser_done i) (parser_stack i) s0 ->
    on_right (next' i p c) (fun i' =>
      parser_state_string i' (s0 ++ c :: "")).
Proof.
  intros [ts00 ts01 Hs0 Hdone Hstack].
  unfold next'; match_ascii; cbn.
  + (* "(" *)
    rewrite <- (string_app_nil_r (_ ++ "(")).
    apply parser_state_string_mk with (more := false); auto.
    apply parser_state_string_mk_
      with (ts00 := ts00) (ts01 := ts01 ++ [Token.Open]);
      cbn; auto.
    rewrite app_assoc; apply token_string_open_app with (more := more); eauto.
  + (* ")" *)
    eauto using _fold_stack_sound.
  + (* """" *)
    eapply parser_state_string_mk; cbn; eauto.
    1,2: admit.
  + (* ";" *)
    eapply parser_state_string_mk; cbn; eauto.
    1,2: admit.
  + (* else *)
    destruct (is_whitespace y) eqn:Ews; cbn.
    * rewrite <- (string_app_nil_r (_ ++ y :: "")).
      eapply parser_state_string_mk; cbn; eauto.
      eapply parser_state_string_mk_; cbn; eauto.
      admit.
    * auto.
Admitted.

Lemma more_ok_atom more s c
  : more_ok more s ->
    is_atom_string s ->
    is_atom_char c = true ->
    more_ok more (s ++ c :: "").
Proof.
Admitted.
Hint Resolve more_ok_atom : ceres.

Lemma string_reverse_cons_ c s1 s'
  : forall s0,
    s' = _string_reverse s0 s1 ->
    (s' ++ c :: "")%string = _string_reverse (s0 ++ c :: "") s1.
Proof.
  induction s1; cbn; intros s0 Hs0.
  - f_equal; auto.
  - apply IHs1 in Hs0; auto.
Qed.

Lemma string_reverse_cons c s s'
  : s' = string_reverse s ->
    (s' ++ c :: "")%string = string_reverse (c :: s)%string.
Proof.
  apply string_reverse_cons_.
Qed.

Lemma new_sexp_Atom_sound d u s0 ts00 ts01 more
    (Hs0 : token_string more (ts00 ++ ts01) s0)
    (Hdone : list_sexp_tokens d ts00)
    (Hstack : stack_tokens u ts01)
    (s' : string)
    (Hmore : more_ok more s')
    (s1' : string)
    (H : is_atom_string s')
    (H0 : s' = string_reverse s1')
    (i' := new_sexp d u (Atom (raw_or_num s1')) tt)
  : parser_state_string_ true (parser_done i') (parser_stack i') (s0 ++ s').
Proof.
Admitted.

Lemma next_sound i s p c
  : parser_state_string i s ->
    on_right (next i p c) (fun i' =>
      parser_state_string i' (s ++ c :: "")).
Proof.
  intros [more s0 s1 Hi Hmore Hcur].
  unfold next.
  destruct Hcur as [ | p1' s1' | p1 tok e | s1' Hs ].
  - (* NoToken *)
    apply more_ok_nil_inv in Hmore; subst more.
    rewrite string_app_nil_r.
    destruct (is_atom_char c) eqn:IAC_c; cbn.
    + econstructor; cbn; eauto with ceres.
    + eauto using next_sound'.
  - (* SimpleToken *)
    destruct (is_atom_char c) eqn:IAC_c; cbn.
    + rewrite string_app_assoc.
      econstructor; cbn; eauto using string_reverse_cons with ceres.
    + destruct Hi as [ts00 ts01 Hs0 Hdone Hstack].
      eauto using next_sound', new_sexp_Atom_sound.
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
