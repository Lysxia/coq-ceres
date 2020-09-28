From Coq Require Import
  Ascii
  String
  List
  ZArith
  DecimalString.
From Ceres Require Import
  CeresUtils
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

Inductive sexp_tokens : sexp -> list Token.t -> Prop :=
| sexp_tokens_Atom a t : atom_token a t -> sexp_tokens (Atom_ a) [t]
| sexp_tokens_List es ts
  : list_tokens sexp_tokens es ts ->
    sexp_tokens (List es) (Token.Open :: ts ++ [Token.Close])
.
Hint Constructors sexp_tokens : ceres.

Notation list_sexp_tokens := (list_tokens sexp_tokens).

(* * Lemmas *)

Lemma atom_token_atom s
  : atom_string (string_reverse s) ->
    atom_token (raw_or_num s) (Token.Atom (string_reverse s)).
Proof.
  unfold raw_or_num. remember (string_reverse _) as s' eqn:E; clear E s.
  destruct NilZero.int_of_string eqn:Eios; intros H.
  - constructor. assumption.
  - constructor.
Qed.

Lemma whitespace_no_atom c
  : is_whitespace c = true -> is_atom_char c = false.
Proof.
  repeat match goal with
  | [ c : _ |- _ ] => destruct c; clear c; try discriminate
  end; cbn; reflexivity.
Qed.
Hint Resolve whitespace_no_atom : ceres.

Lemma list_sexp_tokens_singleton e ts
  : sexp_tokens e ts ->
    list_sexp_tokens [e] ts.
Proof.
  rewrite <- (app_nil_r ts) at 2.
  constructor; auto with ceres.
Qed.
Hint Resolve list_sexp_tokens_singleton : ceres.

Lemma list_sexp_tokens_app es1 es2 ts1 ts2
  : list_sexp_tokens es1 ts1 ->
    list_sexp_tokens es2 ts2 ->
    list_sexp_tokens (es1 ++ es2) (ts1 ++ ts2).
Proof.
  induction 1; cbn.
  - auto.
  - rewrite <- app_assoc; constructor; auto.
Qed.

Lemma string_app_assoc (s0 s1 s2 : string)
  : ((s0 ++ s1) ++ s2 = s0 ++ (s1 ++ s2))%string.
Proof.
  induction s0; cbn; [ auto | rewrite IHs0; auto ].
Qed.

Lemma after_atom_string_snoc c s s' more :
  is_atom_char c = false ->
  after_atom_string s more ->
  after_atom_string (s ++ c :: s') false.
Proof.
  intros Hc []; constructor; auto.
Qed.
Hint Resolve after_atom_string_snoc : ceres.

Lemma token_string_open_snoc more ts s :
  token_string more ts s ->
  token_string false (ts ++ [Token.Open]) (s ++ "(").
Proof.
  induction 1; cbn; try rewrite (string_app_assoc _ _ "("%string); auto with ceres.
  eauto using token_string_atom with ceres.
Qed.

Lemma token_string_close_snoc more ts s :
  token_string more ts s ->
  token_string false (ts ++ [Token.Close]) (s ++ ")").
Proof.
  induction 1; cbn; try rewrite (string_app_assoc _ _ ")"%string); auto with ceres.
  eauto using token_string_atom with ceres.
Qed.

Lemma token_string_atom_snoc ts s s1 :
  atom_string s1 ->
  token_string false ts s ->
  token_string true (ts ++ [Token.Atom s1]) (s ++ s1).
Proof.
  induction 2; cbn; try rewrite (string_app_assoc _ _ s1); auto with ceres.
  - rewrite <- string_app_nil_r at 2. apply token_string_atom; auto with ceres.
  - constructor; auto.
    inversion H1; cbn. constructor; auto.
Qed.

Lemma token_string_newline_snoc more s ts
  : token_string more ts s ->
    token_string false ts (s ++ newline).
Proof.
  induction 1; cbn; try rewrite (string_app_assoc _ _ newline); auto with ceres.
  - change newline with (newline ++ "")%string. apply token_string_spaces; constructor.
  - constructor; eauto with ceres.
Qed.

Lemma token_string_comment_snoc more s s_com ts
  : token_string more ts s ->
    token_string false ts (s ++ ";" ++ s_com ++ newline).
Proof.
  induction 1; cbn; try rewrite string_app_assoc; auto with ceres.
  - change newline with (newline ++ "")%string.
    change (?x :: ?y ++ ?z)%string with ((x :: y) ++ z)%string; rewrite <- string_app_assoc.
    apply token_string_comment; constructor.
  - constructor; eauto with ceres.
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
Hint Constructors stack_tokens : ceres.

Inductive stack_end_last : list symbol -> Prop :=
| stack_end_last_last p : stack_end_last [Open p]
| stack_end_last_cons u us : stack_end_last us -> stack_end_last (u :: us)
.

Inductive stack_end : list symbol -> Prop :=
| stack_end_nil : stack_end []
| stack_end_nonempty us : stack_end_last us -> stack_end us
.
Hint Constructors stack_end : ceres.

Lemma stack_end_cons v u us
  : stack_end (u :: us) ->
    stack_end (v :: u :: us).
Proof.
  inversion 1; do 2 constructor; auto.
Qed.
Hint Resolve stack_end_cons : ceres.

Lemma stack_end_cons_Open p us
  : stack_end us ->
    stack_end (Open p :: us).
Proof.
  inversion 1.
  - do 2 constructor.
  - inversion H0; do 3 (constructor; auto).
Qed.
Hint Resolve stack_end_cons_Open : ceres.

Lemma stack_end_inv u us
  : stack_end (u :: us) ->
    stack_end us.
Proof.
  inversion 1. inversion H0; auto with ceres.
Qed.
Hint Resolve stack_end_inv : ceres.

Definition escape_to_string (e : escape) : string :=
  match e with
  | EscBackslash => "\"
  | EscNone => ""
  end.

Definition no_newline (s : string) : Prop :=
  string_elem "010" s = false.

Lemma is_atom_singleton (c : ascii)
  : is_atom_char c = true -> atom_string (c :: "").
Proof. intros E; constructor; cbn; discriminate + rewrite E; reflexivity. Qed.
Hint Resolve is_atom_singleton : ceres.

Lemma is_atom_app (s : string) (c : ascii)
  : atom_string s -> is_atom_char c = true -> atom_string (s ++ c :: "").
Proof.
  intros [_ Hs] Hc; constructor.
  - destruct s; discriminate.
  - revert Hs; unfold atom_string; induction s; cbn; intros.
    + rewrite Hc; auto.
    + destruct (is_atom_char a); discriminate + rewrite IHs; auto.
Qed.
Hint Resolve is_atom_app : ceres.

Inductive str_token_string (tok : string) (e : escape) : string -> Prop :=
| str_token_string_mk : str_token_string tok e ("""" :: string_reverse tok ++ escape_to_string e)
.

Lemma str_token_string_new : str_token_string "" EscNone """".
Proof. constructor. Qed.

Inductive partial_token_string : partial_token -> string -> Prop :=
| partial_token_string_NoToken
  : partial_token_string NoToken ""
| partial_token_string_SimpleToken p s s'
  : atom_string s' ->
    s' = string_reverse s ->
    partial_token_string (SimpleToken p s) s'
| partial_token_string_StrToken p tok e s'
  : str_token_string tok e s' ->
    partial_token_string (StrToken p tok e) s'
| partial_token_string_Comment s
  : no_newline s ->
    partial_token_string Comment (";" :: s)
.
Hint Constructors partial_token_string : ceres.

Inductive parser_state_string_
    (more : bool) (d : list sexp) (u : list symbol) (s0 : string) : Prop :=
| parser_state_string_mk_ ts00 ts01
  : token_string more (ts00 ++ ts01) s0 ->
    list_sexp_tokens (rev d) ts00 ->
    stack_tokens u ts01 ->
    stack_end u ->
    parser_state_string_ more d u s0
.
Hint Constructors parser_state_string_ : ceres.

Lemma parser_state_string_map d u more more' s0 s0'
  : (forall ts, token_string more ts s0 -> token_string more' ts s0') ->
    parser_state_string_ more  d u s0 ->
    parser_state_string_ more' d u s0'.
Proof.
  intros f []; eauto with ceres.
Qed.

(* Invariant on the parsed prefix *)
Inductive parser_state_string (i : parser_state) : string -> Prop :=
| parser_state_string_mk more s0 s1
  : parser_state_string_ more (parser_done i) (parser_stack i) s0 ->
    more_ok more s1 ->
    partial_token_string (parser_cur_token i) s1 ->
    parser_state_string i (s0 ++ s1)
.
Hint Constructors parser_state_string : ceres.

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

Lemma more_ok_atom_inv more s
  : more_ok more s ->
    atom_string s ->
    more = false.
Proof.
  intros [| c s' Hc]; auto.
  intros [_ Hs]. cbn in Hs. rewrite Hc in Hs. discriminate.
Qed.

Lemma new_sexp_Atom_sound d u s0 more
    (Hdu : parser_state_string_ more d u s0)
    (s' : string)
    (Hmore : more_ok more s')
    (s1' : string)
    (H : atom_string s')
    (H0 : s' = string_reverse s1')
    (i' := new_sexp d u (Atom (raw_or_num s1')) tt)
  : parser_state_string_ true (parser_done i') (parser_stack i') (s0 ++ s').
Proof.
  unfold new_sexp in i'.
  assert (more = false) by eauto using more_ok_atom_inv; subst more.
  destruct Hdu as [ ts00 ts01 Hs0 Hts Hstack Hend ].
  destruct u; cbn; clear i'.
  - inversion Hstack; subst ts01; clear Hstack. rewrite app_nil_r in Hs0.
    apply parser_state_string_mk_
      with (ts00 := ts00 ++ [Token.Atom s']) (ts01 := []);
      cbn; auto with ceres.
    + rewrite app_nil_r.
      auto using token_string_atom_snoc.
    + subst s'; auto using list_sexp_tokens_app, atom_token_atom with ceres.
  - apply parser_state_string_mk_
      with (ts00 := ts00) (ts01 := ts01 ++ [Token.Atom s']);
      cbn; auto with ceres.
    + rewrite app_assoc.
      auto using token_string_atom_snoc.
    + subst s'; auto using atom_token_atom with ceres.
Qed.

Lemma new_sexp_List_sound d u s0 ts00 ts01 ts02 more
    (es : list sexp)
    (Hs0 : token_string more (ts00 ++ ts01 ++ [Token.Open] ++ ts02) s0)
    (Hdone : list_sexp_tokens (rev d) ts00)
    (Hstack : stack_tokens u ts01)
    (Hstackend : stack_end u)
    (Hes : list_sexp_tokens es ts02)
  : parser_state_string (new_sexp d u (List es) NoToken) (s0 ++ ")").
Proof.
  unfold new_sexp.
  destruct u.
  - inversion Hstack; subst; clear Hstack. cbn in Hs0.
    rewrite <- (string_app_nil_r (_ ++ ")")).
    apply parser_state_string_mk with (more := false); cbn; auto with ceres.
    apply parser_state_string_mk_
      with (ts00 := ts00 ++ [Token.Open] ++ ts02 ++ [Token.Close]) (ts01 := []);
      cbn; auto with ceres.
    + rewrite app_nil_r.
      change (?x :: ?y ++ ?z) with ((x :: y) ++ z).
      rewrite !(app_assoc _ _ [Token.Close]).
      eauto using token_string_close_snoc.
    + apply list_sexp_tokens_app; auto.
      rewrite <- (app_nil_r (_ :: _ ++ _)).
      auto with ceres.
  - rewrite <- (string_app_nil_r (_ ++ ")")).
    econstructor; cbn; auto with ceres.
    apply parser_state_string_mk_
      with (ts00 := ts00) (ts01 := ts01 ++ [Token.Open] ++ ts02 ++ [Token.Close]);
      cbn; auto with ceres.
    change (?x :: ?y ++ ?z) with ((x :: y) ++ z).
    rewrite !(app_assoc _ _ [Token.Close]).
    eauto using token_string_close_snoc.
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
    (Hdone : list_sexp_tokens (rev d) ts00)
    (Hstack : stack_tokens u ts01)
    (Hstackend : stack_end u)
    (Hes : list_sexp_tokens es ts02)
  , on_right (_fold_stack d p es u)
      (fun i' : parser_state => parser_state_string i' (s0 ++ ")")).
Proof.
  induction u; cbn; auto; intros.
  destruct a; cbn.
  - inversion Hstack; subst; clear Hstack.
    rewrite <- app_assoc in Hs0.
    eauto using new_sexp_List_sound with ceres.
  - inversion Hstack; subst; clear Hstack.
    rewrite <- app_assoc in Hs0.
    specialize IHu with (1 := Hs0).
    apply IHu; eauto with ceres.
Qed.

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
    with (more := more) (ts00 := ts00) (ts01 := ts01) (ts02 := []); auto with ceres.
  rewrite app_nil_r; auto with ceres.
Qed.

Lemma token_string_spaces_app more ts s c
  : is_whitespace c = true ->
    token_string more ts s ->
    token_string false ts (s ++ c :: "").
Proof.
  intros Hc; induction 1; cbn; try rewrite string_app_assoc; auto with ceres.
  - apply token_string_spaces with (ws := (c :: "")%string); auto with ceres.
    red; cbn; rewrite Hc; auto.
  - apply token_string_atom; auto with ceres.
    eauto using after_atom_string_snoc with ceres.
Qed.

Lemma next_sound' {T} (i : parser_state_ T) (more : bool) s0 p c
  : parser_state_string_ more (parser_done i) (parser_stack i) s0 ->
    is_atom_char c = false ->
    on_right (next' i p c) (fun i' =>
      parser_state_string i' (s0 ++ c :: "")).
Proof.
  intros [ts00 ts01 Hs0 Hdone Hstack] IAC_c.
  unfold next'; match_ascii; cbn.
  + (* "(" *)
    rewrite <- (string_app_nil_r (_ ++ "(")).
    apply parser_state_string_mk with (more := false); auto with ceres.
    apply parser_state_string_mk_
      with (ts00 := ts00) (ts01 := ts01 ++ [Token.Open]);
      cbn; eauto with ceres.
    rewrite app_assoc; apply token_string_open_snoc with (more := more); eauto with ceres.
  + (* ")" *)
    eauto using _fold_stack_sound with ceres.
  + (* """" *)
    eapply parser_state_string_mk; cbn; eauto using str_token_string_new, more_ok_cons with ceres.
  + (* ";" *)
    eapply parser_state_string_mk; cbn; eauto using more_ok_cons with ceres.
  + (* else *)
    destruct (is_whitespace y) eqn:Ews; cbn.
    * rewrite <- (string_app_nil_r (_ ++ y :: "")).
      eauto using token_string_spaces_app with ceres.
    * auto.
Qed.

Lemma more_ok_atom more s c
  : more_ok more s ->
    atom_string s ->
    is_atom_char c = true ->
    more_ok more (s ++ c :: "").
Proof.
  intros []; cbn; auto with ceres.
Qed.
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

Lemma next_comment_sound
    (i : parser_state)
    (c : ascii)
    (more : bool)
    (s0 : string)
    (Hi : parser_state_string_ more (parser_done i) (parser_stack i) s0)
    (Ei : parser_cur_token i = Comment)
    (s1 : string)
    (Hs : no_newline s1)
  : on_right (next_comment i c) (fun i' : parser_state =>
      parser_state_string i' (s0 ++ ";" :: s1 ++ c :: "")).
Proof.
  unfold next_comment.
  match_ascii; cbn.
  - rewrite <- (string_app_nil_r (_ ++ _ :: _)).
    econstructor; eauto using more_ok_cons with ceres.
    revert Hi.
    apply parser_state_string_map, token_string_comment_snoc.
  - econstructor; eauto using more_ok_cons with ceres.
    rewrite Ei; constructor.
    apply not_string_elem_app; auto.
    apply not_string_elem_singleton; assumption.
Qed.

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
      eauto using next_sound', new_sexp_Atom_sound with ceres.
  - (* StrToken *)
    admit.
  - (* Comment *)
    rewrite string_app_assoc; cbn.
    eauto using next_comment_sound.
Admitted.

Lemma _done_or_fail_sound d u
    (more : bool)
    (s0 : string)
    (H : parser_state_string_ more d u s0)
  : on_right (_done_or_fail d u)
      (fun es : list sexp =>
       exists ts : list Token.t,
         list_sexp_tokens es ts /\ token_string more ts s0).
Proof.
  destruct H.
  destruct H2 as [ | ? H2]; cbn.
  - inversion H1; subst; clear H1. rewrite app_nil_r in *.
    exists ts00. unfold rev'; rewrite <- rev_alt.
    eauto.
  - clear H1. induction H2; intros; cbn; auto.
    destruct u; cbn; auto.
Qed.

Lemma eof_sound
    (i : parser_state)
    (p : loc)
    (s : string)
    (H : parser_state_string i s)
  : on_right (eof i p) (fun es : list sexp =>
      exists (ts : list Token.t),
        list_sexp_tokens es ts /\ token_string false ts (s ++ newline)).
Proof.
  unfold eof.
  destruct H as [ more s0 s1 H Hmore Hpartial ].
  destruct Hpartial; cbn; auto.
  - rewrite string_app_nil_r.
    eauto using _done_or_fail_sound, parser_state_string_map, token_string_newline_snoc.
  - eauto using _done_or_fail_sound, new_sexp_Atom_sound, parser_state_string_map, token_string_newline_snoc.
  - rewrite string_app_assoc. eapply _done_or_fail_sound. cbn.
    revert H.
    apply parser_state_string_map, token_string_comment_snoc.
Qed.

Lemma _parse_sexps_sound i p (s0 s : string)
  : parser_state_string i s0 ->
    match parse_sexps_ i p s with
    | (None, p', i') =>
      on_right (eof i' p') (fun es =>
        exists ts,
          list_sexp_tokens es ts /\ token_string false ts (s0 ++ s ++ newline))
    | (Some _, _, _) => True
    end.
Proof.
  revert i p s0; induction s as [ | c s ]; intros; cbn.
  - apply eof_sound; auto.
  - pose proof next_sound as SOUND.
    specialize (SOUND i s0 p c H).
    destruct next as [ | i']; auto; cbn in SOUND.
    specialize (IHs i' (N.succ p) _ SOUND).
    destruct parse_sexps_ as [ [ [ | ] ] ? ]; auto.
    destruct eof; auto; cbn in *.
    destruct IHs as (ts & Hts & Hs0).
    rewrite string_app_assoc in Hs0.
    eauto.
Qed.

Lemma parser_state_empty : parser_state_string initial_state "".
Proof.
  change ""%string with ("" ++ "")%string.
  repeat econstructor; cbn; auto with ceres.
Qed.

(* If the parser succeeds, then the expressions relate to the input string. *)
Theorem parse_sexps_sound (s : string) (es : list sexp)
  : on_right (parse_sexps s) (fun es =>
      exists ts,
        list_sexp_tokens es ts /\ token_string false ts (s ++ newline)).
Proof.
  unfold parse_sexps.
  pose proof (_parse_sexps_sound initial_state 0%N "" s parser_state_empty) as SOUND.
  destruct parse_sexps_ as [ [ [ | ] ] ? ]; cbn; auto.
Qed.
