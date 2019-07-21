Require Import String.
Require Import Ceres.TemplateLib.
Require Import Ceres.Ceres Ceres.Derive.

Import TMNotations.

Variant my_unit : Type := MyTT.

Variant my_option (A : Type) : Type :=
| MySome : A -> my_option A
| MyNone : my_option A
.

Arguments MySome {A}.
Arguments MyNone {A}.

Variant my_sum (A B : Type) : Type :=
| MyInl : A -> my_sum A B
| MyInr : B -> my_sum A B
.

Arguments MyInl {A B}.
Arguments MyInr {A B}.

Record my_prod (A B : Type) : Type := MyPair
  { fst : A ; snd : B }.

Arguments MyPair {A B}.

Inductive my_list (A : Type) : Type :=
| MyNil : my_list A
| MyCons : A -> my_list A -> my_list A
.

Arguments MyNil {A}.
Arguments MyCons {A}.

Inductive my_fin : nat -> Type :=
| MyF1 n : my_fin (S n)
| MyFS n : my_fin n -> my_fin (S n)
.

Arguments MyF1 {n}.
Arguments MyFS {n}.

CoInductive my_stream : Type :=
  { next : nat
  ; step : my_stream
  }.

(**)

Run TemplateProgram
  (deriveSerialize (Serialize my_unit)).

Run TemplateProgram
  (deriveSerialize (forall A, Serialize A -> Serialize (my_option A))).

Run TemplateProgram
  (deriveSerialize
     (forall A B, Serialize A -> Serialize B -> Serialize (my_sum A B))).

Run TemplateProgram
  (deriveSerialize
     (forall A B, Serialize A -> Serialize B -> Serialize (my_prod A B))).

Run TemplateProgram
  (deriveSerialize (forall A, Serialize A -> Serialize (my_list A))).

(*
Run TemplateProgram
  (deriveSerializeWith (enable_debug o0) (forall n, Serialize (my_fin n))).
*)

Fact Serialize_MySome_OK
  : sexp_of (MySome tt)
  = [ARaw "MySome" ; ARaw "tt"]%sexp.
Proof. reflexivity. Qed.

Fact Serialize_MyNone_OK
  : sexp_of (@MyNone unit)
  = ARaw "MyNone".
Proof. reflexivity. Qed.

Fact Serialize_MyInl_OK
  : sexp_of (@MyInl unit unit tt)
  = [ARaw "MyInl" ; ARaw "tt"]%sexp.
Proof. reflexivity. Qed.

Fact Serialize_MyInr_OK
  : sexp_of (@MyInr unit unit tt)
  = [ARaw "MyInr" ; ARaw "tt"]%sexp.
Proof. reflexivity. Qed.

Fact Serialize_MyNil_OK
  : sexp_of (@MyNil unit)
  = ARaw "MyNil".
Proof. reflexivity. Qed.

Fact Serialize_MyCons_OK
  : sexp_of (MyCons tt MyNil)
  = [ARaw "MyCons" ; ARaw "tt" ; ARaw "MyNil"]%sexp.
Proof. reflexivity. Qed.

(**)

Require Import MetaCoq.Template.All.

Quote Definition q_unit := unit.
Quote Definition q_tt := tt.

Definition testMatch y : TM unit :=
  tMatch (tRel 0) y q_unit (fun _ _ _ => tmReturn q_tt) >>= fun t =>
  tmUnquote (tLambda nAnon y t) >>= fun _ => tmReturn tt.

Run TemplateProgram (tmQuote my_unit >>= testMatch).
Run TemplateProgram (tmQuote (my_option unit) >>= testMatch).
Run TemplateProgram (tmQuote (my_list unit) >>= testMatch).
Run TemplateProgram (tmQuote (my_sum unit unit) >>= testMatch).
Run TemplateProgram (tmQuote (my_prod unit unit) >>= testMatch).
Run TemplateProgram (tmQuote (my_fin 2) >>= testMatch).
Run TemplateProgram (tmQuote (my_stream) >>= testMatch).
