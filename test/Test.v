From Coq Require Import List NArith ZArith String.
From Ceres Require Import Ceres Parser.

Import ListNotations.

Definition s : unit + (nat * bool * unit) := inr (1, false, tt).
Definition test_to_string_s : string_of s = "(inr ((1 false) tt))"%string
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

Lemma parse_1 : parse_string "a" = inr [ARaw "a"].
Proof. reflexivity. Qed.

Lemma parse_2 : parse_string """a""" = inr [AStr "a"].
Proof. reflexivity. Qed.

Lemma parse_3 : parse_string "3" = inr [ANum 3].
Proof. reflexivity. Qed.

Lemma parse_4 : parse_string "-3" = inr [ANum (-3)].
Proof. reflexivity. Qed.

Lemma parse_5 : parse_string "(a)" = inr [List [ARaw "a"]].
Proof. reflexivity. Qed.

Lemma parse_6 : parse_string "(a b)" = inr [List [ARaw "a"; ARaw "b"]].
Proof. reflexivity. Qed.

Lemma parse_7 : parse_string "(a b c)" = inr [List [ARaw "a"; ARaw "b"; ARaw "c"]].
Proof. reflexivity. Qed.

Lemma parse_8 : parse_string "(a (b c) d)" = inr [List [ARaw "a"; List [ARaw "b"; ARaw "c"]; ARaw "d"]].
Proof. reflexivity. Qed.
