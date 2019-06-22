(** * S-expressions *)

(* begin hide *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
(* end hide *)

(** S-expressions, parameterized by the type of atoms. *)
Inductive sexp (A : Type) :=
| Atom (a : A)
| List (xs : list (sexp A))
.

Arguments Atom {A} a.
Arguments List {A} xs.

Delimit Scope sexp_scope with sexp.
Bind Scope sexp_scope with sexp.

Notation "[]" := (List nil) : sexp_scope.
Notation "[ x ]" := (List (@cons (sexp _) x nil)) : sexp_scope.
Notation "[ x ; y ; .. ; z ]"
  := (List (@cons (sexp _) x (@cons (sexp _) y .. (@cons (sexp _) z nil) .. )))
  : sexp_scope.

(** Apply a function to every atom. *)
Fixpoint map_sexp {A B : Type} (f : A -> B) (x : sexp A) : sexp B :=
  match x with
  | Atom a => Atom (f a)
  | List xs => List (map (map_sexp f) xs)
  end.

(** Replace every atom with an S-expression. *)
Fixpoint subst_sexp {A B : Type} (f : A -> sexp B) (x : sexp A) : sexp B :=
  match x with
  | Atom a => f a
  | List xs => List (map (subst_sexp f) xs)
  end.

(** Construct an S-expression from a list of atoms. *)
Fixpoint sexp_of_atoms {A} (xs : list A) : sexp A :=
  List (map Atom xs).

(** * Default atoms *)

(** Internal representation of [atom]. *)
Local Variant _atom : Set :=
| _Num (n : Z)
| _Str (s : string)
| _Raw (s : string)
.

(** Default type of atoms. [sexp atom] thus provides a uniform format to
    store and exchange semi-structured data.

    This is an abstract type. It may be extended in the future with more
    constructors, so pattern-matching should not be used.
  *)
Definition atom : Set := _atom.

(** ** Constructors *)

(** - [Num : Z -> atom]. Integer atoms. *)
(** - [Str : string -> atom]. Strings (human-readable messages). *)
(** - [Raw : string -> atom]. Raw atoms (e.g., ADT tags) *)

Definition Num : Z -> atom := _Num.
Definition Str : string -> atom := _Str.
Definition Raw : string -> atom := _Raw.

(** Potential future extensions: binary strings, floating-point *)

(** *** Coercions and notations *)

Definition Atom_default : atom -> sexp atom := Atom.
Coercion Atom_default : atom >-> sexp.
Coercion Num : Z >-> atom.

Notation ANum x := (Atom (_Num x)).
Notation AStr x := (Atom (_Str x)).
Notation ARaw x := (Atom (_Raw x)).

(** ** Destructors *)

(** This interface deliberately lacks a way to exhaustively eliminate an
    [atom] to enable backward compatible extensions. *)

Definition get_Num (a : atom) : option Z :=
  match a with
  | _Num n => Some n
  | _ => None
  end.

Definition get_Str (a : atom) : option string :=
  match a with
  | _Str s => Some s
  | _ => None
  end.

Definition get_Raw (a : atom) : option string :=
  match a with
  | _Raw s => Some s
  | _ => None
  end.

(** ** Example *)
Section Example.
Import ListNotations.

(** This S-expression:

<<
(example
  (message "I'm a teapot")
  (code 418))
>>

corresponds to this [sexp atom] in Gallina:
*)

Let example_1 : sexp atom :=
  List [ Atom (Raw "example")
       ; List [ Atom (Raw "message") ; Atom (Str "I'm a teapot") ]
       ; List [ Atom (Raw "code") ; Atom (Num 418%Z) ]
       ].

Local Open Scope sexp.

(** Or, with [Atom] and [Num] as implicit coercions and overloading the list
    notation... *)

Let example_2 : sexp atom :=
  [ Raw "example"
  ; [ Raw "message" ; Str "I'm a teapot" ]
  ; [ Raw "code" ; Num 418%Z ]
  ].

End Example.
