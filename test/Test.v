From Coq Require Import List NArith ZArith String.
From Ceres Require Import Ceres.

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

Lemma roundtrip_s : roundtrip s.
Proof. reflexivity. Qed.
