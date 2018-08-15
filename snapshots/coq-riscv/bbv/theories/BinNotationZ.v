Require Export bbv.BinNotation.
Require Import Coq.ZArith.BinInt.

Notation "'Ob' a" := (Z.of_N (bin a)) (at level 50).

Goal Ob"01000001" = 65%Z.
Proof. reflexivity. Qed.
