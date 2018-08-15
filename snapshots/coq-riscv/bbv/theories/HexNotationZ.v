Require Export bbv.HexNotation.
Require Import Coq.ZArith.BinInt.

Notation "'Ox' a" := (Z.of_N (hex a)) (at level 50).

Goal Ox"41" = 65%Z.
Proof. reflexivity. Qed.
