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

Fixpoint comma_sep (xs : list string) : string :=
  match xs with
  | nil => ""
  | x :: nil => x
  | x :: xs => x ++ ", " ++ comma_sep xs
  end.

Fixpoint find_or {A B C} (eqb : A -> A -> bool) (a : A) (xs : list (A * B)) (f : B -> C) (b : C) : C :=
  match xs with
  | nil => b
  | (x, y) :: xs => if eqb a x then f y else find_or eqb a xs f b
  end.

Definition bind_sum {A B C} (x : A + B) (f : B -> A + C) : A + C :=
  match x with
  | inl a => inl a
  | inr b => f b
  end.

(** Location inside an S-expression. *)
Definition loc : Set := list nat.

(** Error messages. *)
Inductive message : Set :=
| MsgApp : message -> message -> message
| MsgStr : string -> message
| MsgSexp : sexp atom -> message
.

Declare Scope s_msg_scope.
Bind Scope s_msg_scope with message.
Delimit Scope s_msg_scope with s_message.
Infix "++" := MsgApp : s_msg_scope.
Coercion MsgStr : string >-> message.

Variant error :=
| ParseError : Parser.error -> error
| DeserError : loc -> message -> error
.

(** Context for deserializing values of type [A], with implicit handling of error locations. *)
Definition FromSexp (A : Type) := loc -> sexp atom -> error + A.

(** Deserialization from S-expressions *)
Class Deserialize (A : Type) :=
  _from_sexp : FromSexp A.

(** Deserialize an S-expression. *)
Definition from_sexp `{Deserialize A} : sexp atom -> error + A :=
  _from_sexp nil.


(** Context for consuming lists of S-expressions. *)
Definition FromSexpList (A : Type) := loc -> list (sexp atom) -> error + A.

(** Context for consuming lists with a statically-known expected length. *)
Record FromSexpListN (m n : nat) (A : Type) := {
  _fields : FromSexpList A
}.

Module Deser.

Definition _con {A : Type} (g : string -> loc -> error + A) (f : string -> FromSexpList A) : FromSexp A :=
  fun l e =>
    match e with
    | List (ARaw c :: es) => f c l es
    | List (e0 :: es) => inl (DeserError (0 :: l) ("unexpected atom (expected constructor name)"%string))
    | List nil => inl (DeserError l "unexpected empty list"%string)
    | ARaw c => g c l
    | Atom _ => inl (DeserError l "unexpected atom (expected list or nullary constructor name)"%string)
    end.

(** Deserialize with a custom function. *)
Definition as_fun {A} (f : loc -> sexp atom -> error + A) : FromSexp A := f.

Definition match_con {A} (ys : list (string * A)) (xs : list (string * FromSexpList A)) : FromSexp A :=
  _con
    (fun c l =>
      let all_con := List.map fst ys in
      find_or String.eqb c ys inr
        (let msg :=
           match all_con with
           | nil => MsgStr "Unexpected atom (expected list)"%string
           | _ =>
             ("Expected nullary constructor name, one of "%string ++ comma_sep all_con
               ++ ", found "%string ++ c)%s_message
           end
         in inl (DeserError l msg)))
    (fun c =>
      let all_con := List.map fst xs in
      find_or String.eqb c xs (fun x => x)
        (fun l _ =>
          let msg :=
            match all_con with
            | nil => MsgStr "Unexpected atom"%string
            | _ =>
              ("Expected constructor name, one of "%string ++ comma_sep all_con
                ++ ", found "%string ++ c)%s_message
            end
          in inl (DeserError l msg))).

Definition fields {A} {n} : FromSexpListN 0 n A -> FromSexpList A := fun p => _fields p.

Definition ret {R} (r : R) {n : nat} : FromSexpListN n n R :=
  {| _fields := fun l es =>
      match es with
      | nil => inr r
      | _ =>
        let msg :=
          ("Too many fields. Expected "%string ++ string_of_nat n
            ++ ", got "%string ++ string_of_nat (n + List.length es))%s_message
        in inl (DeserError l msg)
      end |}.

Definition bind_field {A B} (pa : FromSexp A)
    {n m : nat} (f : A -> FromSexpListN (S n) m B)
  : FromSexpListN n m B :=
  {| _fields := fun l es =>
      match es with
      | e :: es => bind_sum (pa (n :: l) e) (fun a => _fields (f a) l es)
      | nil =>
        let msg :=
          ("Not enough fields. Expected "%string ++ string_of_nat m
            ++ ", got only "%string ++ string_of_nat n)%s_message
        in inl (DeserError l msg)
      end |}.

Module Import Notations.
Notation "p >>= f" := (bind_field p f) (at level 50, left associativity).
End Notations.

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
      | None => inl (DeserError l ("Invalid number "%string ++ MsgSexp e))
      end
    | Atom _ => inl (DeserError l ("Expected a number, got a non-Num atom "%string ++ MsgSexp e))
    | List _ => inl (DeserError l "Expected a number, got a list"%string)
    end.

Instance SemiIntegral_Z : SemiIntegral Z := Some.
Instance SemiIntegral_N : SemiIntegral N :=
  fun n => if (n <? 0)%Z then None else Some (Z.to_N n).
Instance SemiIntegral_nat : SemiIntegral nat :=
  fun n => if (n <? 0)%Z then None else Some (Z.to_nat n).

(** ** Deserialize common types *)

Import ListNotations.

Instance Deserialize_bool : Deserialize bool :=
  Deser.match_con
    [ ("false", false)
    ; ("true" , true)
    ]%string [].

Instance Deserialize_sum {A B} `{Deserialize A} `{Deserialize B} : Deserialize (A + B) :=
  Deser.match_con []
    [ ("inl", Deser.con1_ inl)
    ; ("inr", Deser.con1_ inr)
    ]%string.

Instance Deserialize_prod {A B} `{Deserialize A} `{Deserialize B} : Deserialize (A * B) :=
  fun l e =>
    match e with
    | List (e1 :: e2 :: nil) =>
      bind_sum (_from_sexp (0 :: l) e1) (fun a =>
      bind_sum (_from_sexp (1 :: l) e2) (fun b =>
      inr (a, b)))
    | List _ => inl (DeserError l "Expected list of length 2, got list of a different length"%string)
    | Atom _ => inl (DeserError l "Expected list of length 2, got atom"%string)
    end.

Instance Deserialize_Empty_set : Deserialize Empty_set :=
  fun l _ => inl (DeserError l "Tried to deserialize Empty_set"%string).

Instance Deserialize_unit : Deserialize unit :=
  fun l e =>
    match e with
    | ARaw "tt" => inr tt
    | _ => inl (DeserError l "Expected atom ""tt"""%string)
    end.

Instance Deserialize_string : Deserialize string :=
  fun l e =>
    match e with
    | AStr s => inr s
    | _ => inl (DeserError l "Expected string"%string)
    end.
