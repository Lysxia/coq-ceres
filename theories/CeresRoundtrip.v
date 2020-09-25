From Coq Require Import
  List
  String.
From Ceres Require Import
  CeresS
  CeresSerialize
  CeresDeserialize.

Import ListNotations.

Definition SerDe {A : Type} (ser : A -> sexp) (de : sexp -> error + A) : Prop :=
  forall (a : A), de (ser a) = inr a.

Definition map_sum {A B B' : Type} (f : B -> B') (x : A + B) : A + B' :=
  match x with
  | inl a => inl a
  | inr b => inr (f b)
  end.

Definition DeSer {A : Type} (ser : A -> sexp) (de : sexp -> error + A) : Prop :=
  forall (e : sexp) (a : A),
    de e = inr a ->
    ser a = e.

Class SerDeClass (A : Type) `{Serialize A} `{Deserialize A} : Prop :=
  ser_de_class : forall l, @SerDe A to_sexp (_from_sexp l).

Class DeSerClass (A : Type) `{Serialize A} `{Deserialize A} : Prop :=
  de_ser_class : forall l, @DeSer A to_sexp (_from_sexp l).

Lemma de__con {A} (tyname : string)
    (g : string -> loc -> error + A) (f : string -> FromSexpList A)
    l (e : sexp) (a : A)
  : Deser._con tyname g f l e = inr a ->
    (exists c, e = Atom (Raw c) /\ g c l = inr a) \/
    (exists c es, e = List (Atom (Raw c) :: es) /\ f c l (type_error tyname) es = inr a).
Proof.
  destruct e as [ [] | [ | [ [] | ] ] ]; cbn; try discriminate; eauto.
Qed.

Lemma _find_or_spec {A B C}
    (eqb : A -> A -> bool) (a : A) (xs : list (A * B)) (f : B -> C) (b : C)
    (P : C -> Prop)
  : P (_find_or eqb a xs f b) ->
    (List.Exists (fun p => eqb a (fst p) = true /\ P (f (snd p))) xs) \/
    (List.Forall (fun p => eqb a (fst p) = false) xs /\ P b).
Proof.
  induction xs as [ | xy xs IH ].
  - auto.
  - cbn. destruct xy as [x y].
    destruct (eqb a x) eqn:Eeqb.
    + left; left; auto.
    + intros H; specialize (IH H).
      destruct IH as [ | [] ].
      * left; right; assumption.
      * right; constructor; [ constructor; auto | auto ].
Qed.

Theorem de_match_con {A} (tyname : string)
    (c0 : list (string * A)) (c1 : list (string * FromSexpList A))
    l (e : sexp) (a : A)
  : Deser.match_con tyname c0 c1 l e = inr a ->
    List.Exists (fun p => e = Atom (Raw (fst p)) /\ a = snd p) c0
      \/ List.Exists (fun p => exists es,
           List (Atom (Raw (fst p)) :: es) = e /\
           inr a = snd p l (type_error tyname) es) c1.
Proof.
  unfold Deser.match_con.
  intros DESER. apply de__con in DESER. destruct DESER as [ (c & Ee & Ea ) | (c & es & Ee & Ea) ].
  - apply _find_or_spec in Ea. destruct Ea as [ Ea | [] ]; [ | discriminate ].
    left. revert Ea; apply List.Exists_impl.
    intros [] [Es Ea]; cbn in *.
    apply CeresString.eqb_eq_string in Es.
    injection Ea; intros.
    subst. auto.
  - apply _find_or_spec in Ea. destruct Ea as [ Ea | [] ]; [ | discriminate ].
    right. revert Ea; apply List.Exists_impl.
    intros [] [Es Ea]; cbn in *.
    apply CeresString.eqb_eq_string in Es.
    exists es.
    subst; auto.
Qed.

Ltac elim_Exists H :=
  match type of H with
  | (List.Exists _ nil) => apply List.Exists_nil in H; destruct H
  | (List.Exists _ (cons _ _)) => apply List.Exists_cons in H;
    destruct H as [ H | H ]; [ | elim_Exists H ]
  end.

Instance SerDeClass_bool : SerDeClass bool.
Proof.
  unfold SerDeClass, SerDe.
  intros l []; reflexivity.
Qed.

Instance DeSerClass_bool : DeSerClass bool.
Proof.
  intros l e a Ee; apply de_match_con in Ee.
  destruct Ee as [ Ee | Ee ]; elim_Exists Ee;
    destruct Ee as [Eatom Ea]; subst; try reflexivity.
Qed.

Instance SerDeClass_option {A} `{SerDeClass A} : SerDeClass (option A).
Proof.
  unfold SerDeClass, SerDe.
  intros l []; cbn; [ rewrite H1 | ]; reflexivity.
Qed.

Section DeRetField.

Context {R} (r : R) {n : nat}.

Inductive UnnilFields : R -> list sexp -> Prop :=
| MkUnnilFields : UnnilFields r nil
.

Lemma de_ret_field {a} l err es
  : inr a = _fields (@Deser.ret R r n) l err es ->
    UnnilFields a es.
Proof.
  destruct es; cbn.
  - intros H; injection H; intros J; rewrite J; constructor.
  - discriminate.
Qed.

End DeRetField.

Section DeBindField.

Context {A B} (pa : FromSexp A)
    {n m : nat} (f : A -> FromSexpListN (S n) m B).

Context (a : B) (es : list sexp) {l : loc} {err : message -> message}.

Inductive UnconsFields : list sexp -> Prop :=
| MkUnconsFields a' e' es'
  : pa (n :: l) e' = inr a' ->
    inr a = _fields (f a') l err es' ->
    UnconsFields (e' :: es')
.

Lemma de_bind_field
  : inr a = _fields (Deser.bind_field pa f) l err es ->
    UnconsFields es.
Proof.
  destruct es; cbn; try discriminate.
  destruct pa eqn:E1; cbn; try discriminate.
  apply MkUnconsFields. assumption.
Qed.

End DeBindField.

Ltac de_field Ea :=
  (apply de_ret_field in Ea; destruct Ea) +
  (let a1 := fresh "a" in
   let e1 := fresh "e" in
   let es := fresh "es" in
   let Ea1 := fresh "Ea1" in
   apply de_bind_field in Ea;
   destruct Ea as [a1 e1 es Ea1 Ea];
   de_field Ea).

Instance DeSerClass_option {A} `{DeSerClass A} : DeSerClass (option A).
Proof.
  intros l e a Ee; apply de_match_con in Ee.
  destruct Ee as [ Ee | Ee ]; elim_Exists Ee; cbn [fst snd] in *.
  - destruct Ee as [E1 E2]; subst; reflexivity.
  - destruct Ee as [es [Ee Ea]].
    de_field Ea. cbn.
    apply H1 in Ea1.
    rewrite Ea1; assumption.
Qed.
