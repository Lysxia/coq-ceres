Require Import Ceres.Ceres.
Require Import String.

Definition s : unit + (nat * bool * unit) := inr (1, false, tt).
Definition test_s
  : string_of s = "(inr ((1 false) tt))"%string
  := eq_refl.
