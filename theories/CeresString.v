(** * String utilities *)

(* begin hide *)
From Coq Require Import
  Setoid
  Bool DecidableClass List Arith ZArith NArith Ascii String Decimal DecimalString.
(* end hide *)

(* Booleans *)

Inductive reflect_eq {A} (x : A) : A -> bool -> Prop :=
| reflect_eq_true : reflect_eq x x true
| reflect_eq_false y : x <> y -> reflect_eq x y false
.

(* [Bool.eqb_spec], which doesn't exist on Coq 8.8 *)
Lemma eqb_eq_bool x y : reflect (x = y) (Bool.eqb x y).
Proof.
  destruct (Bool.eqb _ _) eqn:H;
    constructor; [ apply eqb_prop | apply eqb_false_iff ]; auto.
Defined.

Lemma eqb_eq_bool' x y : reflect_eq x y (Bool.eqb x y).
Proof.
  destruct x, y; constructor; discriminate.
Qed.

Definition compcomp (x y : comparison) : comparison :=
  match x with
  | Eq => y
  | Lt => Lt
  | Gt => Gt
  end.

Delimit Scope compare_scope with compare.
Infix "::" := compcomp : compare_scope.

Definition compb (x y : bool) : comparison :=
  match x, y with
  | false, false => Eq
  | false, true => Lt
  | true, false => Gt
  | true, true => Eq
  end.

(* Strings and characters *)

Infix "::" := String : string_scope.

Local Open Scope lazy_bool_scope.

(* Backport #8063 to Coq 8.8 *)
Definition eqb_ascii (a b : ascii) : bool :=
 match a, b with
 | Ascii a0 a1 a2 a3 a4 a5 a6 a7,
   Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Bool.eqb a0 b0 &&& Bool.eqb a1 b1 &&& Bool.eqb a2 b2 &&& Bool.eqb a3 b3
    &&& Bool.eqb a4 b4 &&& Bool.eqb a5 b5 &&& Bool.eqb a6 b6 &&& Bool.eqb a7 b7
 end.

(* Note: the most significant bit is on the right. *)
Definition ascii_compare (a b : ascii) : comparison :=
 match a, b with
 | Ascii a0 a1 a2 a3 a4 a5 a6 a7,
   Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    (  compb a7 b7 :: compb a6 b6 :: compb a5 b5 :: compb a4 b4
    :: compb a3 b3 :: compb a2 b2 :: compb a1 b1 :: compb a0 b0)%compare
 end.

Definition leb_ascii (a b : ascii) : bool :=
  match ascii_compare a b with
  | Gt => false
  | _ => true
  end.

Delimit Scope char2_scope with char2.
Infix "=?" := eqb_ascii : char2_scope.
Infix "<=?" := leb_ascii : char2_scope.

Definition eqb_eq {A} (eqb : A -> A -> bool) :=
  forall a b, eqb a b = true <-> a = b.

Lemma eqb_eq_ascii : eqb_eq eqb_ascii.
Proof with auto.
  split; intros.
  - destruct a, b; simpl in H.
    do 8 (
      match type of H with
      | context [ Bool.eqb ?x ?y ] => destruct (eqb_eq_bool x y); try discriminate; subst
      end)...
  - subst; destruct b; simpl.
    repeat rewrite eqb_reflx...
Defined.

Lemma eqb_eq_ascii' c0 c1 :
  reflect_eq c0 c1 (c0 =? c1)%char2.
Proof.
  destruct c0, c1; cbn.
  repeat
    match goal with
    | [ |- context E [ Bool.eqb ?x ?y ] ] =>
      destruct (eqb_eq_bool' x y); try (constructor; congruence)
    end.
Qed.

Lemma neqb_neq_ascii a b : eqb_ascii a b = false <-> a <> b.
Proof.
  etransitivity.
  - symmetry; apply not_true_iff_false.
  - apply not_iff_compat, eqb_eq_ascii.
Qed.

Instance Decidable_eq_ascii : forall (a b : ascii), Decidable (a = b).
Proof.
  exact (fun a b : ascii =>
           {| Decidable_witness := eqb_ascii a b;
              Decidable_spec := eqb_eq_ascii a b |}).
Defined.

Fixpoint eqb_string s1 s2 : bool :=
  match s1, s2 with
  | EmptyString, EmptyString => true
  | String c1 s1', String c2 s2' => eqb_ascii c1 c2 &&& eqb_string s1' s2'
  | _,_ => false
  end.

Lemma eqb_eq_string : eqb_eq eqb_string.
Proof with auto.
  intro s1.
  induction s1; intros []; split; intro H; try discriminate...
  - simpl in H.
    apply andb_prop in H.
    destruct H.
    apply eqb_eq_ascii in H.
    apply IHs1 in H0.
    f_equal...
  - inversion H; subst.
    simpl.
    apply andb_true_intro.
    split.
    + apply eqb_eq_ascii...
    + apply IHs1...
Defined.

Instance Decidable_eq_string : forall (s1 s2 : string), Decidable (s1 = s2).
Proof.
  exact (fun s1 s2 : string =>
           {| Decidable_witness := eqb_string s1 s2;
              Decidable_spec := eqb_eq_string s1 s2 |}).
Defined.

Fixpoint string_elem (c : ascii) (s : string) : bool :=
  match s with
  | "" => false
  | c' :: s => eqb_ascii c c' ||| string_elem c s
  end%string.

Fixpoint string_forall (f : ascii -> bool) (s : string) : bool :=
  match s with
  | "" => true
  | c :: s => f c &&& string_forall f s
  end%string.

Fixpoint _string_reverse (r s : string) : string :=
  match s with
  | "" => r
  | c :: s => _string_reverse (c :: r) s
  end%string.

Definition string_reverse : string -> string := _string_reverse "".

Lemma string_app_nil_r (s : string) : (s ++ "")%string = s.
Proof.
  induction s; [ auto | cbn; rewrite IHs; auto ].
Qed.

Lemma not_string_elem_app c s1 s2
  : string_elem c s1 = false ->
    string_elem c s2 = false ->
    string_elem c (s1 ++ s2) = false.
Proof.
  induction s1; cbn; auto.
  destruct (c =? a)%char2; try discriminate; auto.
Qed.

Lemma not_string_elem_head c c' s
  : string_elem c (c' :: s) = false -> c <> c'.
Proof.
  cbn; destruct (eqb_eq_ascii' c c'); discriminate + auto.
Qed.

Lemma not_string_elem_singleton c c'
  : c <> c' -> string_elem c (c' :: "") = false.
Proof.
  rewrite <- neqb_neq_ascii.
  intros H; cbn; rewrite H.
  reflexivity.
Qed.

(** Separate elements with commas. *)
Fixpoint comma_sep (xs : list string) : string :=
  match xs with
  | nil => ""
  | x :: nil => x
  | x :: xs => x ++ ", " ++ comma_sep xs
  end.

Notation newline := ("010" :: "")%string.

Section AsciiTest.

Local Open Scope char2_scope.

(** Is a character printable? The character is given by its ASCII code. *)
Definition is_printable (n : nat) : bool :=
  (  (n <? 32)%nat (* 32 = SPACE *)
  || (126 <? n)%nat (* 126 = ~ *)
  ).

Definition is_whitespace (c : ascii) : bool :=
  match c with
  | " " | "010" | "013" => true
  | _ => false
  end%char.

Definition is_digit (c : ascii) : bool :=
  ("0" <=? c) &&& (c <=? "9").

Definition is_upper (c : ascii) : bool :=
  ("A" <=? c) &&& (c <=? "Z").

Definition is_lower (c : ascii) : bool :=
  ("a" <=? c) &&& (c <=? "z").

Definition is_alphanum (c : ascii) : bool :=
  is_upper c |||
  is_lower c |||
  is_digit c.

End AsciiTest.

(** ** Escape string *)

(** The [ascii] units digit of a [nat]. *)
Local Definition _units_digit (n : nat) : ascii :=
  ascii_of_nat ((n mod 10) + 48 (* 0 *)).

(** The hundreds, tens, and units digits of a [nat]. *)
Local Definition _three_digit (n : nat) : string :=
  let n0 := _units_digit n in
  let n1 := _units_digit (n / 10) in
  let n2 := _units_digit (n / 100) in
  (n2 :: n1 :: n0 :: EmptyString).

(** Helper for [escape_string] *)
Fixpoint _escape_string (_end s : string) : string :=
  match s with
  | EmptyString => _end
  | (c :: s')%string =>
    let escaped_s' := _escape_string _end s' in
    if ascii_dec c "009" (* 9 = TAB *) then
      "\" :: "t" :: escaped_s'
    else if ascii_dec c "010" (* 10 = NEWLINE *) then
      "\" :: "n" :: escaped_s'
    else if ascii_dec c "013" (* 13 = CARRIAGE RETURN *) then
      "\" :: "r" :: escaped_s'
    else if ascii_dec c """" (* DOUBLEQUOTE *) then
      "\" :: """" :: escaped_s'
    else if ascii_dec c "\" (* BACKSLASH *) then
      "\" :: "\" :: escaped_s'
    else
      let n := nat_of_ascii c in
      if is_printable n then
        "\" :: _three_digit n ++ escaped_s'
      else
        String c escaped_s'
  end.

(** Escape a string so it can be shown in a terminal. *)
Definition escape_string (s : string) : string :=
  String """" (_escape_string """" s).

(** ** Unescape string *)

(** Read an [ascii] digit into a [nat]. *)
Definition digit_of_ascii (c : ascii) : option nat :=
  let n := nat_of_ascii c in
  if ((48 <=? n)%nat && (n <=? 57)%nat)%bool then
    Some (n - 48)
  else
    None.

(** The inverse of [three digit]. *)
Local Definition _unthree_digit (c2 c1 c0 : ascii) : option ascii :=
  let doa := digit_of_ascii in
  match doa c2, doa c1, doa c0 with
  | Some n2, Some n1, Some n0 =>
    Some (ascii_of_nat (n2 * 100 + n1 * 10 + n0))
  | _, _, _ => None
  end.

(** Helper for [unescape_string]. *)
Local Fixpoint _unescape_string (s : string) : option string :=
  match s with
  | String c s' =>
    if ascii_dec c """" then
      match s' with
      | EmptyString => Some EmptyString
      | _ => None
      end
    else if ascii_dec c "\" then
      match s' with
      | String c2 s'' =>
        if ascii_dec c2 "n" then
          option_map (String "010") (_unescape_string s'')
        else if ascii_dec c2 "r" then
          option_map (String "013") (_unescape_string s'')
        else if ascii_dec c2 "t" then
          option_map (String "009") (_unescape_string s'')
        else if ascii_dec c2 "\" then
          option_map (String "\") (_unescape_string s'')
        else if ascii_dec c2 """" then
          option_map (String """") (_unescape_string s'')
        else
          match s'' with
          | String c1 (String c0 s''') =>
            match _unthree_digit c2 c1 c0 with
            | Some c' => option_map (String c')
                                    (_unescape_string s''')
            | None => None
            end
          | _ => None
          end
      | _ => None
      end
    else
      option_map (String c) (_unescape_string s')
  | _ => None
  end.

(** The inverse of [escape_string]. *)
Definition unescape_string (s : string) : option string :=
  match s with
  | ("""" :: s')%string => _unescape_string s'
  | (_ :: _)%string => None
  | EmptyString => None
  end.

(** ** Convert numbers to string *)

Import NilEmpty.

Definition string_of_nat (n : nat) : string :=
  string_of_uint (Nat.to_uint n).

Definition string_of_Z (n : Z) : string :=
  string_of_int (Z.to_int n).

Definition string_of_N (n : N) : string :=
  string_of_Z (Z.of_N n).

Definition string_of_bool (b : bool) : string :=
  match b with
  | true => "true"
  | false => "false"
  end.

Module DString.

(** Difference lists for fast append. *)
Definition t : Type := string -> string.

Definition of_string (s : string) : t := fun s' => (s ++ s')%string.
Definition of_ascii (c : ascii) : t := fun s => (c :: s)%string.
Definition app_string : t -> string -> string := id.

End DString.

Coercion DString.of_string : string >-> DString.t.
Coercion DString.of_ascii : ascii >-> DString.t.

(* Declare Scope dstring_scope. *)
Delimit Scope dstring_scope with dstring.
Bind Scope dstring_scope with DString.t.
Notation "a ++ b" := (fun s => DString.app_string a (DString.app_string b s))
  : dstring_scope.

