(** * S-expressions *)

(* begin hide *)
From Coq Require Import
  List ZArith Ascii String.
(* end hide *)

(** S-expressions, parameterized by the type of atoms. *)
Inductive sexp_ (A : Type) :=
| Atom_ (a : A)
| List (xs : list (sexp_ A))
.

Arguments Atom_ {A} a.
Arguments List {A} xs.

(* Declare Scope sexp_scope. *)
Delimit Scope sexp_scope with sexp.
Bind Scope sexp_scope with sexp_.

Notation "[ ]" := (List nil) : sexp_scope.
Notation "[ x ]" := (List (@cons (sexp_ _) x nil)) : sexp_scope.
Notation "[ x ; y ; .. ; z ]"
  := (List (@cons (sexp_ _) x (@cons (sexp_ _) y .. (@cons (sexp_ _) z nil) .. )))
  : sexp_scope.

(** Apply a function to every atom. *)
Fixpoint map_sexp_ {A B : Type} (f : A -> B) (x : sexp_ A) : sexp_ B :=
  match x with
  | Atom_ a => Atom_ (f a)
  | List xs => List (map (map_sexp_ f) xs)
  end.

(** Replace every atom with an S-expression. *)
Fixpoint subst_sexp_ {A B : Type} (f : A -> sexp_ B) (x : sexp_ A) : sexp_ B :=
  match x with
  | Atom_ a => f a
  | List xs => List (map (subst_sexp_ f) xs)
  end.

(** Construct an S-expression from a list of atoms. *)
Fixpoint sexp_of_atoms {A} (xs : list A) : sexp_ A :=
  List (map Atom_ xs).

(** * Default atoms *)

(** Default type of atoms. [sexp_ atom] thus provides a uniform format to
    store and exchange semi-structured data. *)
Variant atom : Set :=
| Num (n : Z)       (* Integers. *)
| Str (s : string)  (* Literal strings. *)
| Raw (s : string)  (* Simple atoms (e.g., ADT tags). *)
                    (* Should fit in this alphabet: [A-Za-z0-9-_.']. *)
.

Notation sexp := (sexp_ atom).
Notation Atom := (@Atom_ atom).  (* This notation helps make coercions work. *)

(** Potential future extensions: binary strings, floating-point *)

(** *** Coercions and notations *)

Coercion Num : Z >-> atom.
Coercion Raw : string >-> atom.

(** ** Destructors *)

(** This interface deliberately lacks a way to exhaustively eliminate an
    [atom] to enable backward compatible extensions. *)

Definition get_Num (a : atom) : option Z :=
  match a with
  | Num n => Some n
  | _ => None
  end.

Definition get_Str (a : atom) : option string :=
  match a with
  | Str s => Some s
  | _ => None
  end.

Definition get_Raw (a : atom) : option string :=
  match a with
  | Raw s => Some s
  | _ => None
  end.

(** ** Example *)
Section Example.
Import ListNotations.

Local Open Scope string.

(** This S-expression:

<<
(example
  (message "I'm a teapot")
  (code 418))
>>

corresponds to this [sexp] in Gallina:
*)

Let example_1 : sexp :=
  List [ Atom "example"
       ; List [ Atom "message" ; Atom (Str "I'm a teapot") ]
       ; List [ Atom "code" ; Atom 418%Z ]
       ].

Local Open Scope sexp.

(** Or, overloading the list notation... *)

Let example_2 : sexp :=
  [ Atom "example"
  ; [ Atom "message" ; Atom (Str "I'm a teapot") ]
  ; [ Atom "code" ; Atom 418%Z ]
  ].

End Example.
