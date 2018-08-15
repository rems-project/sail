Require Export bbv.HexNotation.
Require Import bbv.WordScope.

Notation "'Ox' a" := (NToWord _ (hex a)) (at level 50).

Notation "sz ''h' a" := (NToWord sz (hex a)) (at level 50).

Goal 8'h"a" = WO~0~0~0~0~1~0~1~0.
Proof. reflexivity. Qed.

Goal Ox"41" = WO~1~0~0~0~0~0~1.
Proof. reflexivity. Qed.
