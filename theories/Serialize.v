(** * Serialization to S-expressions *)

(* begin hide *)
From Coq Require Import
  List
  ZArith
  String.

From Ceres Require Import
  S
  Format
  String.
(* end hide *)

(** Serialization to S-expressions. *)
Class Serialize (A : Type) :=
  sexp_of : A -> sexp atom.

(** Serialize a value to a string. *)
Definition string_of {A} `{Serialize A} : A -> string :=
  fun a => string_of_sexpa (sexp_of a).

(** ** Serialize integers *)

(** Integer representations. *)
Class Integral (A : Type) :=
  Z_of : A -> Z.

(** Integers are serializable. *)
Instance Serialize_Integral {A : Type} `(Integral A) : Serialize A :=
  Z_of.

Instance Integral_nat : Integral nat := Z.of_nat.
Instance Integral_N : Integral N := Z.of_N.
Instance Integral_Z : Integral Z := id.

(** ** Serialize common types *)

Instance Serialize_bool : Serialize bool
  := fun b => Raw (string_of_bool b).

Instance Serialize_sum {A B} `(Serialize A) `(Serialize B)
  : Serialize (A + B)
  := fun ab =>
    match ab with
    | inl a => [ Raw "inl" ; sexp_of a ]%sexp
    | inr b => [ Raw "inr" ; sexp_of b ]%sexp
    end.

Instance Serialize_product {A B} `(Serialize A) `(Serialize B)
  : Serialize (A * B)
  := fun ab => [ sexp_of (fst ab) ; sexp_of (snd ab) ]%sexp.

Instance Serialize_Empty_set : Serialize Empty_set
  := fun v => match v with end.

Instance Serialize_unit : Serialize unit
  := fun _ => Raw "tt".

Instance Serialize_string : Serialize string := Str.
