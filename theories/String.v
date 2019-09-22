(** * String utilities *)

(* begin hide *)
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Decimal.
(* end hide *)

Infix "::" := String : string_scope.

Fixpoint _string_reverse (r s : string) : string :=
  match s with
  | "" => r
  | c :: s => _string_reverse (c :: r) s
  end%string.

Definition string_reverse : string -> string := _string_reverse "".

Notation newline := ("010" :: "")%string.

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

(** ** Escape string *)

(** The [ascii] units digit of a [nat]. *)
Local Definition units_digit (n : nat) : ascii :=
  ascii_of_nat ((n mod 10) + 48 (* 0 *)).

(** The hundreds, tens, and units digits of a [nat]. *)
Local Definition three_digit (n : nat) : string :=
  let n0 := units_digit n in
  let n1 := units_digit (n / 10) in
  let n2 := units_digit (n / 100) in
  (n2 :: n1 :: n0 :: EmptyString).

(** Helper for [escape_string] *)
Local Fixpoint _escape_string (s : string) : string :=
  match s with
  | EmptyString => """"
  | (c :: s')%string =>
    let escaped_s' := _escape_string s' in
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
        "\" :: three_digit n ++ escaped_s'
      else
        String c escaped_s'
  end.

(** Escape a string so it can be shown in a terminal. *)
Definition escape_string (s : string) : string :=
  String """" (_escape_string s).

(** ** Unescape string *)

(** Read an [ascii] digit into a [nat]. *)
Definition digit_of_ascii (c : ascii) : option nat :=
  let n := nat_of_ascii c in
  if ((48 <=? n)%nat && (n <=? 57)%nat)%bool then
    Some (n - 48)
  else
    None.

(** The inverse of [three digit]. *)
Local Definition unthree_digit (c2 c1 c0 : ascii) : option ascii :=
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
            match unthree_digit c2 c1 c0 with
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

Fixpoint string_of_uint (n : uint) : string :=
  match n with
  | Nil => ""
  | D0 n => "0" :: string_of_uint n
  | D1 n => "1" :: string_of_uint n
  | D2 n => "2" :: string_of_uint n
  | D3 n => "3" :: string_of_uint n
  | D4 n => "4" :: string_of_uint n
  | D5 n => "5" :: string_of_uint n
  | D6 n => "6" :: string_of_uint n
  | D7 n => "7" :: string_of_uint n
  | D8 n => "8" :: string_of_uint n
  | D9 n => "9" :: string_of_uint n
  end.

Definition string_of_int (n : int) : string :=
  match n with
  | Pos n => string_of_uint n
  | Neg n => "-" :: string_of_uint n
  end.

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

Declare Scope dstring_scope.
Delimit Scope dstring_scope with dstring.
Bind Scope dstring_scope with DString.t.
Notation "a ++ b" := (fun s => DString.app_string a (DString.app_string b s))
  : dstring_scope.

