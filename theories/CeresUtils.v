From Coq Require Import
  List.
Import ListNotations.

Definition map_sum {A B B' : Type} (f : B -> B') (x : A + B) : A + B' :=
  match x with
  | inl a => inl a
  | inr b => inr (f b)
  end.

Lemma app_cons_assoc {A} (xs : list A) (x : A) (ys : list A)
  : xs ++ x :: ys = (xs ++ [x]) ++ ys.
Proof.
  rewrite <- app_assoc; reflexivity.
Qed.
