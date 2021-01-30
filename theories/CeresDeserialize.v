(** * Deserialization from S-expressions *)

(* begin hide *)
From Coq Require Import
  List
  ZArith
  Ascii
  String.

From Ceres Require Import
  CeresUtils
  CeresS
  CeresParser
  CeresString.

Generalizable Variables A.

Set Implicit Arguments.
(* end hide *)

(** * Deserialization *)

(** ** Errors *)

(** Location inside an S-expression. *)
Definition loc : Set := list nat.

(** Error messages. *)
Inductive message : Set :=
| MsgApp : message -> message -> message
| MsgStr : string -> message
| MsgSexp : sexp -> message
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
| ParseError : CeresParserUtils.error -> error     (* Errors from parsing [string -> sexp] *)
| DeserError : loc -> message -> error   (* Errors from deserializing [sexp -> A] *)
.

(** ** Deserialization context *)

(** Context for deserializing values of type [A], with implicit handling of error locations. *)
Definition FromSexp (A : Type) := loc -> sexp -> error + A.

(** ** The [Deserialize] class *)

(** Class of types which can be deserialized from S-expressions. *)
Class Deserialize (A : Type) :=
  _from_sexp : FromSexp A.

(** Deserialize from an S-expression. *)
Definition from_sexp `{Deserialize A} : sexp -> error + A :=
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
Definition FromSexpList (A : Type) := loc -> (message -> message) -> list sexp -> error + A.

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
    | List (Atom_ (Raw c) :: es) => f c l (type_error tyname) es
    | List (_ :: _) => inl (DeserError (0 :: l) (type_error tyname "unexpected atom (expected constructor name)"%string))
    | List nil => inl (DeserError l (type_error tyname "unexpected empty list"%string))
    | Atom_ (Raw c) => g c l
    | Atom_ _ => inl (DeserError l (type_error tyname "unexpected atom (expected list or nullary constructor name)"%string))
    end.

(** Deserialize with a custom function. *)
Definition as_fun {A} (f : loc -> sexp -> error + A) : FromSexp A := f.

(** Deserialize an ADT based on the name of its constructor.
  - The first argument [tyname : string] is the name of the type being parsed, for error messages.
  - The second argument [c0 : list (string * A)] is a mapping of nullary constructors,
    which are encoded as a plain atom, associating a name to its value.
  - The third argument [c1 : list (string * FromSexpList A)] is a mapping of
    non-nullary constructors, associating a name to a deserializer for the fields of
    the corresponding constructor.
[[
(* Example type *)
Inductive example A : Type :=
| Ex0 : example A
| Ex1 : A -> example A
| Ex2 : A -> A -> example A
.

Instance Deserialize_example {A} `{Deserialize A} : Deserialize (example A) :=
  Deser.match_con "example"      (* Name of the type. *)
    [ ("Ex0", Ex0)               (* Nullary constructors in the first list: [("name", constructor)]. *)
    ]%string
    [ ("Ex1", Deser.con1_ Ex1)   (* In the second list, [("name", conN_ constructor)] *)
    , ("Ex2", Deser.con2_ Ex2)   (* where [N] is the arity of [constructor]. *)
    ]%string.
]]
  *)
Definition match_con {A} (tyname : string)
    (c0 : list (string * A)) (c1 : list (string * FromSexpList A))
  : FromSexp A :=
  _con tyname
    (fun c l =>
      let all_con := List.map fst c0 in
      _find_or CeresString.eqb_string c c0 inr
        (let msg :=
           match all_con with
           | nil => MsgStr "unexpected atom (expected list)"%string
           | _ =>
             ("expected nullary constructor name, one of "%string ++ comma_sep all_con
               ++ ", found "%string ++ c)%s_message
           end
         in inl (DeserError l (type_error tyname msg))))
    (fun c l err es =>
      let all_con := List.map fst c1 in
      _find_or CeresString.eqb_string c c1 (fun x (_ : unit) => x l err es)
        (fun (_ : unit) =>
          let msg :=
            match all_con with
            | nil => MsgStr "unexpected atom"%string
            | _ =>
              ("expected constructor name, one of "%string ++ comma_sep all_con
                ++ ", found "%string ++ c)%s_message
            end
          in inl (DeserError l (type_error tyname msg))) tt).

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

(** Note: prefer using the first list in [match_con] for nullary constructors. *)
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

Definition con1_ {A R} (f : A -> R) `{Deserialize A} : FromSexpList R :=
  con1 f _from_sexp.
Definition con2_ {A B R} (f : A -> B -> R) `{Deserialize A} `{Deserialize B} : FromSexpList R :=
  con2 f _from_sexp _from_sexp.
Definition con3_ {A B C R} (f : A -> B -> C -> R)
    `{Deserialize A} `{Deserialize B} `{Deserialize C} : FromSexpList R :=
  con3 f _from_sexp _from_sexp _from_sexp.
Definition con4_ {A B C D R} (f : A -> B -> C -> D -> R)
    `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} : FromSexpList R :=
  con4 f _from_sexp _from_sexp _from_sexp _from_sexp.
Definition con5_ {A B C D E R} (f : A -> B -> C -> D -> E -> R)
    `{Deserialize A} `{Deserialize B} `{Deserialize C} `{Deserialize D} `{Deserialize E}
  : FromSexpList R :=
  con5 f  _from_sexp _from_sexp _from_sexp _from_sexp _from_sexp.

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
    | Atom_ (Num n) =>
      match from_Z n with
      | Some a => inr a
      | None => inl (DeserError l ("could not read integral type, invalid value "%string ++ MsgSexp e))
      end
    | Atom_ _ => inl (DeserError l ("could not read integral type, got a non-Num atom "%string ++ MsgSexp e))
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

Instance Deserialize_option {A} `{Deserialize A} : Deserialize (option A) :=
  Deser.match_con "option"
    [ ("None", None) ]%string
    [ ("Some", Deser.con1_ Some) ]%string.

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
    | Atom_ _ => inl (DeserError l "could not read 'prod', expected list of length 2, got atom"%string)
    end.

Instance Deserialize_Empty_set : Deserialize Empty_set :=
  fun l _ => inl (DeserError l "Tried to deserialize Empty_set"%string).

Instance Deserialize_unit : Deserialize unit :=
  fun l e =>
    match e with
    | Atom_ (Raw "tt") => inr tt
    | Atom_ _ => inl (DeserError l "could not read 'unit', expected atom ""tt"", got a different atom"%string)
    | List _ => inl (DeserError l "could not read 'unit', expected atom ""tt"", got a list"%string)
    end.

Instance Deserialize_string : Deserialize string :=
  fun l e =>
    match e with
    | Atom_ (Str s) => inr s
    | Atom_ _ => inl (DeserError l "could not read 'string', got non-string atom"%string)
    | List _ => inl (DeserError l "could not read 'string', got list"%string)
    end.

Instance Deserialize_ascii : Deserialize ascii :=
  fun l e =>
    match e with
    | Atom_ (Str (c :: "")) => inr c
    | Atom_ (Str "") => inl (DeserError l "could not read 'ascii', got empty string")
    | Atom_ (Str (_ :: _ :: _)) =>
      inl (DeserError l "could not read 'ascii', got string of length greater than 1")
    | Atom_ _ => inl (DeserError l "could not read 'ascii', got non-string atom")
    | List _ => inl (DeserError l "could not read 'ascii', got lost")
    end%string.

Fixpoint _sexp_to_list {A} (pa : FromSexp A) (xs : list A)
  (n : nat) (l : loc) (ys : list sexp) : error + list A :=
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
    | Atom_ _ => inl (DeserError l "could not read 'list', got atom"%string)
    | List es => _sexp_to_list _from_sexp nil 0 l es
    end.

Instance Deserialize_sexp : Deserialize sexp := fun _ => inr.
