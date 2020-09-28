From Coq Require Import
  List.
Import ListNotations.

Lemma app_cons_assoc {A} (xs : list A) (x : A) (ys : list A)
  : xs ++ x :: ys = (xs ++ [x]) ++ ys.
Proof.
  rewrite <- app_assoc; reflexivity.
Qed.
