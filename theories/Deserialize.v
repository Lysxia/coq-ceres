(** * Deserialization from S-expressions *)

(* begin hide *)
From Coq Require Import
  List
  ZArith
  String.

From Ceres Require Import
  S
  Parser
  String.

Generalizable Variables A.

Set Implicit Arguments.
(* end hide *)

(** ** General-purpose internal helpers *)

(** Find an element by key in an association list. *)
Fixpoint _find_or {A B C} (eqb : A -> A -> bool) (a : A) (xs : list (A * B)) (f : B -> C) (b : C) : C :=
  match xs with
  | nil => b
  | (x, y) :: xs => if eqb a x then f y else _find_or eqb a xs f b
  end.

(** The bind of the [sum A] monad. *)
Definition _bind_sum {A B C} (x : A + B) (f : B -> A + C) : A + C :=
  match x with
  | inl a => inl a
  | inr b => f b
  end.

(** * Deserialization *)

(** ** Errors *)

(** Location inside an S-expression. *)
Definition loc : Set := list nat.

(** Error messages. *)
Inductive message : Set :=
| MsgApp : message -> message -> message
| MsgStr : string -> message
| MsgSexp : sexp atom -> message
.

(* Declare Scope s_msg_scope. *)
Bind Scope s_msg_scope with message.
Delimit Scope s_msg_scope with s_message.
Infix "++" := MsgApp : s_msg_scope.
Coercion MsgStr : string >-> message.

(** Prefix an error with some type information. *)
Definition type_error (tyname : string) (msg : message) : message :=
  "could not read type '"%string ++ tyname ++ "', "%string ++ msg.

(** Errors which may occur when deserializing S-expressions. *)
Variant error :=
| ParseError : Parser.error -> error     (* Errors from parsing [string -> sexp atom] *)
| DeserError : loc -> message -> error   (* Errors from deserializing [sexp atom -> A] *)
.

(** ** Deserialization context *)

(** Context for deserializing values of type [A], with implicit handling of error locations. *)
Definition FromSexp (A : Type) := loc -> sexp atom -> error + A.

(** ** The [Deserialize] class *)

(** Class of types which can be deserialized from S-expressions. *)
Class Deserialize (A : Type) :=
  _from_sexp : FromSexp A.

(** Deserialize from an S-expression. *)
Definition from_sexp `{Deserialize A} : sexp atom -> error + A :=
  _from_sexp nil.

(** Deserialize from a string containing an S-expression. *)
Definition from_string `{Deserialize A} : string -> error + A :=
  fun s =>
    match parse_sexp s with
    | inl e => inl (ParseError e)
    | inr x => from_sexp x
    end.


(** * Combinators for generic [Deserialize] instances *)

(** The generic format implemented here encodes a constructor [C x y z]
    as the expression [(C x y z)]. *)

(** Context for consuming lists of S-expressions. *)
Definition FromSexpList (A : Type) := loc -> (message -> message) -> list (sexp atom) -> error + A.

(** Context for consuming lists with a statically-known expected length. *)
Record FromSexpListN (m n : nat) (A : Type) := {
  _fields : FromSexpList A
}.

(* Declare Scope deser_scope. *)
Delimit Scope deser_scope with deser.

(** These combinators are meant to be used qualified. *)
Module Deser.

Definition _con {A : Type} (tyname : string)
    (g : string -> loc -> error + A) (f : string -> FromSexpList A)
  : FromSexp A :=
  fun l e =>
    match e with
    | List (ARaw c :: es) => f c l (type_error tyname) es
    | List (e0 :: es) => inl (DeserError (0 :: l) (type_error tyname "unexpected atom (expected constructor name)"%string))
    | List nil => inl (DeserError l (type_error tyname "unexpected empty list"%string))
    | ARaw c => g c l
    | Atom _ => inl (DeserError l (type_error tyname "unexpected atom (expected list or nullary constructor name)"%string))
    end.

(** Deserialize with a custom function. *)
Definition as_fun {A} (f : loc -> sexp atom -> error + A) : FromSexp A := f.

(** Deserialize an ADT based on the name of its constructor.
    The first argument [tyname : string] is the name of the type being parsed, for error messages.
    The second argument [c0 : list (string * A)] is a mapping of nullary constructors,
    which are encoded as a plain atom, associating a name to its value.
    The third argument [c1 : list (string * FromSexpList A)] is a mapping of
    non-nullary constructors, associating a name to a deserializer for the fields of
    the corresponding constructor.
  *)
Definition match_con {A} (tyname : string)
    (c0 : list (string * A)) (c1 : list (string * FromSexpList A))
  : FromSexp A :=
  _con tyname
    (fun c l =>
      let all_con := List.map fst c0 in
      _find_or String.eqb c c0 inr
        (let msg :=
           match all_con with
           | nil => MsgStr "unexpected atom (expected list)"%string
           | _ =>
             ("expected nullary constructor name, one of "%string ++ comma_sep all_con
               ++ ", found "%string ++ c)%s_message
           end
         in inl (DeserError l (type_error tyname msg))))
    (fun c =>
      let all_con := List.map fst c1 in
      _find_or String.eqb c c1 (fun x => x)
        (fun l _ _ =>
          let msg :=
            match all_con with
            | nil => MsgStr "unexpected atom"%string
            | _ =>
              ("expected constructor name, one of "%string ++ comma_sep all_con
                ++ ", found "%string ++ c)%s_message
            end
          in inl (DeserError l (type_error tyname msg)))).

(** Deserialize the fields of a constructor. *)
Definition fields {A} {n} : FromSexpListN 0 n A -> FromSexpList A := fun p => _fields p.

Definition ret {R} (r : R) {n : nat} : FromSexpListN n n R :=
  {| _fields := fun l mk_error es =>
      match es with
      | nil => inr r
      | _ =>
        let msg :=
          ("too many fields, expected "%string ++ string_of_nat n
            ++ ", got "%string ++ string_of_nat (n + List.length es))%s_message
        in inl (DeserError l (mk_error msg))
      end |}.

Definition bind_field {A B} (pa : FromSexp A)
    {n m : nat} (f : A -> FromSexpListN (S n) m B)
  : FromSexpListN n m B :=
  {| _fields := fun l mk_error es =>
      match es with
      | e :: es => _bind_sum (pa (n :: l) e) (fun a => _fields (f a) l mk_error es)
      | nil =>
        let msg :=
          ("not enough fields, expected "%string ++ string_of_nat m
            ++ ", got only "%string ++ string_of_nat n)%s_message
        in inl (DeserError l (mk_error msg))
      end |}.

Module Import Notations.
Notation "p >>= f" := (bind_field p f) (at level 50, left associativity) : deser_scope.
End Notations.

Local Open Scope deser_scope.

Definition con0 {R} (r : R) : FromSexpList R := fields (ret r).

Definition con1 {A R} (f : A -> R) : FromSexp A -> FromSexpList R := fun pa =>
  fields (pa >>= fun a => ret (f a)).

Definition con2 {A B R} (f : A -> B -> R) : FromSexp A -> FromSexp B -> FromSexpList R :=
  fun pa pb => fields (pa >>= fun a => pb >>= fun b => ret (f a b)).

Definition con3 {A B C R} (f : A -> B -> C -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexpList R :=
  fun pa pb pc => fields (pa >>= fun a => pb >>= fun b => pc >>= fun c => ret (f a b c)).

Definition con4 {A B C D R} (f : A -> B -> C -> D -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexpList R :=
  fun pa pb pc pd =>
    fields (pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d =>
    ret (f a b c d)).

Definition con5 {A B C D E R} (f : A -> B -> C -> D -> E -> R)
  : FromSexp A -> FromSexp B -> FromSexp C -> FromSexp D -> FromSexp E -> FromSexpList R :=
  fun pa pb pc pd pe =>
    fields (pa >>= fun a => pb >>= fun b => pc >>= fun c => pd >>= fun d => pe >>= fun e =>
    ret (f a b c d e)).

Definition con1_ {A R} (f : A -> R) : forall `{Deserialize A}, FromSexpList R := con1 f.
Definition con2_ {A B R} (f : A -> B -> R)
  : forall `{Deserialize A} `{Deserialize B}, FromSexpList R := con2 f.
Definition con3_ {A B C R} (f : A -> B -> C -> R)
  : forall `{Deserialize A} `{Deserialize B} `{Deserialize C}, FromSexpList R := con3 f.
Definition con4_ {A B C D R} (f : A -> B -> C -> D -> R)
  : forall `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D}, FromSexpList R := con4 f.
Definition con5_ {A B C D E R} (f : A -> B -> C -> D -> E -> R)
  : forall `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}, FromSexpList R :=
  con5 f.

Class DeserFromSexpList (A R : Type) (n m : nat) :=
  _from_sexp_list : A -> FromSexpListN n m R.

Instance DeserFromSexpList_0 R m : DeserFromSexpList R R m m := fun r => ret r.
Instance DeserFromSexpList_S A B R n m `{Deserialize A} `{DeserFromSexpList B R (S n) m}
  : DeserFromSexpList (A -> B) R n m :=
  fun f => _from_sexp >>= fun a => _from_sexp_list (f a).

Definition con_ (A R : Type) (m : nat) `{DeserFromSexpList A R 0 m} (a : A) : FromSexpList R :=
  fields (_from_sexp_list a).

End Deser.

Class SemiIntegral (A : Type) :=
  from_Z : Z -> option A.

Instance Deserialize_SemiIntegral `{SemiIntegral A} : Deserialize A :=
  fun l e =>
    match e with
    | ANum n =>
      match from_Z n with
      | Some a => inr a
      | None => inl (DeserError l ("could not read integral type, invalid value "%string ++ MsgSexp e))
      end
    | Atom _ => inl (DeserError l ("could not read integral type, got a non-Num atom "%string ++ MsgSexp e))
    | List _ => inl (DeserError l "could not read integral type, got a list"%string)
    end.

Instance SemiIntegral_Z : SemiIntegral Z := Some.
Instance SemiIntegral_N : SemiIntegral N :=
  fun n => if (n <? 0)%Z then None else Some (Z.to_N n).
Instance SemiIntegral_nat : SemiIntegral nat :=
  fun n => if (n <? 0)%Z then None else Some (Z.to_nat n).

(** ** Deserialize common types *)

Import ListNotations.

Instance Deserialize_bool : Deserialize bool :=
  Deser.match_con "bool"
    [ ("false", false)
    ; ("true" , true)
    ]%string [].

Instance Deserialize_sum {A B} `{Deserialize A} `{Deserialize B} : Deserialize (A + B) :=
  Deser.match_con "sum" []
    [ ("inl", Deser.con1_ inl)
    ; ("inr", Deser.con1_ inr)
    ]%string.

Instance Deserialize_prod {A B} `{Deserialize A} `{Deserialize B} : Deserialize (A * B) :=
  fun l e =>
    match e with
    | List (e1 :: e2 :: nil) =>
      _bind_sum (_from_sexp (0 :: l) e1) (fun a =>
      _bind_sum (_from_sexp (1 :: l) e2) (fun b =>
      inr (a, b)))
    | List _ => inl (DeserError l "could not read 'prod', expected list of length 2, got list of a different length"%string)
    | Atom _ => inl (DeserError l "could not read 'prod', expected list of length 2, got atom"%string)
    end.

Instance Deserialize_Empty_set : Deserialize Empty_set :=
  fun l _ => inl (DeserError l "Tried to deserialize Empty_set"%string).

Instance Deserialize_unit : Deserialize unit :=
  fun l e =>
    match e with
    | ARaw "tt" => inr tt
    | Atom _ => inl (DeserError l "could not read 'unit', expected atom ""tt"", got a different atom"%string)
    | List _ => inl (DeserError l "could not read 'unit', expected atom ""tt"", got a list"%string)
    end.

Instance Deserialize_string : Deserialize string :=
  fun l e =>
    match e with
    | AStr s => inr s
    | Atom _ => inl (DeserError l "could not read 'string', got non-string atom"%string)
    | List _ => inl (DeserError l "could not read 'string', got list"%string)
    end.

Fixpoint _sexp_to_list {A} (pa : FromSexp A) (xs : list A)
  (n : nat) (l : loc) (ys : list (sexp atom)) : error + list A :=
  match ys with
  | nil => inr (rev' xs)
  | y :: ys =>
    match pa (n :: l) y with
    | inl e => inl e
    | inr x => _sexp_to_list pa (x :: xs) (S n) l ys
    end
  end.

Instance Deserialize_list {A} `{Deserialize A} : Deserialize (list A) :=
  fun l e =>
    match e with
    | Atom _ => inl (DeserError l "could not read 'list', got atom"%string)
    | List es => _sexp_to_list _from_sexp nil 0 l es
    end.

Instance Deserialize_sexp : Deserialize (sexp atom) := fun _ => inr.
