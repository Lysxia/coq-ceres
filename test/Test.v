From Coq Require Import List NArith ZArith String.
From Ceres Require Import Ceres Parser.

Import ListNotations.

Definition s : unit + (nat * bool * unit) := inr (1, false, tt).
Definition test_to_string_s : to_string s = "(inr ((1 false) tt))"%string
  := eq_refl.

Definition roundtrip {A} `{Serialize A} `{Deserialize A} : A -> Prop :=
  fun a => from_sexp (to_sexp a) = inr a.

Lemma roundtrip_bool : Forall roundtrip [true; false].
Proof. repeat constructor. Qed.

Lemma roundtrip_nat : Forall roundtrip [0; 1; 2].
Proof. repeat constructor. Qed.

Lemma roundtrip_Z : Forall roundtrip [-2; -1; 0; 1; 2]%Z.
Proof. repeat constructor. Qed.

Lemma roundtrip_N : Forall roundtrip [0; 1; 2]%N.
Proof. repeat constructor. Qed.

Lemma roundtrip_pair : roundtrip (0, true).
Proof. reflexivity. Qed.

Lemma roundtrip_sum : Forall roundtrip [inl tt; inr 0].
Proof. repeat constructor. Qed.

Lemma roundtrip_list : Forall roundtrip [[]; [0]; [0;1]; [0;1;2]].
Proof. repeat constructor. Qed.

Lemma roundtrip_s : roundtrip s.
Proof. reflexivity. Qed.

Lemma parse_1 : parse_sexps "a" = inr [ARaw "a"].
Proof. reflexivity. Qed.

Lemma parse_2 : parse_sexps """a""" = inr [AStr "a"].
Proof. reflexivity. Qed.

Lemma parse_3 : parse_sexps "3" = inr [ANum 3].
Proof. reflexivity. Qed.

Lemma parse_4 : parse_sexps "-3" = inr [ANum (-3)].
Proof. reflexivity. Qed.

Lemma parse_5 : parse_sexps "(ab)" = inr [List [ARaw "ab"]].
Proof. reflexivity. Qed.

Lemma parse_6 : parse_sexps "(ab cd)" = inr [List [ARaw "ab"; ARaw "cd"]].
Proof. reflexivity. Qed.

Lemma parse_7 : parse_sexps "(a b c)" = inr [List [ARaw "a"; ARaw "b"; ARaw "c"]].
Proof. reflexivity. Qed.

Lemma parse_8 : parse_sexps "ab cd" = inr [ARaw "ab"; ARaw "cd"].
Proof. reflexivity. Qed.

Lemma parse_9 : parse_sexps "ab (cd (ef gh) ij) kl"
              = inr [ARaw "ab"; List [ARaw "cd"; List [ARaw "ef"; ARaw "gh"]; ARaw "ij"]; ARaw "kl"].
Proof. reflexivity. Qed.

Local Open Scope N_scope.
Local Open Scope sexp_scope.

Lemma parse_10 :
  let '(r1, p1, s0) := parse_sexps_ initial_state 0 "(1)(2)3" in
  let (e1, s1) := get_one s0 in
  let (e2, s2) := get_one s1 in
  let (e3, s3) := get_one s2 in
  let '(r2, p2, s4) := parse_sexps_ s2 p1 "4 )" in
  let (e4, s5) := get_one s4 in
  e1 = Some [ANum 1] /\
  e2 = Some [ANum 2] /\
  e3 = None /\
  e4 = Some (ANum 34).
Proof. split; split; split; reflexivity. Qed.
