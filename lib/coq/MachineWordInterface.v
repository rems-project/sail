Require Import ZArith.

Module Type MachineWordInterface.

Parameter word : nat -> Type.
Parameter zeros : forall n, word n.
Parameter ones : forall n, word n.
Parameter get_bit : forall [n], word n -> nat -> bool.
Parameter set_bit : forall [n], word n -> nat -> bool -> word n.
Parameter word_to_bools : forall [n], word n -> list bool.
Parameter bools_to_word : forall l : list bool, word (List.length l).

Parameter word_to_Z : forall [n], word n -> Z.
Parameter word_to_N : forall [n], word n -> N.
Parameter Z_to_word : forall n, Z -> word n.
Parameter N_to_word : forall n, N -> word n.

Axiom word_to_N_range : forall [n] (w : word n), (word_to_N w < 2 ^ N.of_nat n)%N.
Axiom word_to_Z_range : forall [n] (w : word (S n)), (- 2 ^ Z.of_nat n <= word_to_Z w < 2 ^ Z.of_nat n)%Z.

Parameter slice : forall [m] n, word m -> nat -> word n.
Parameter update_slice : forall [m] [n], word m -> nat -> word n -> word m.
Parameter zero_extend : forall [m] n, word m -> word n.
Parameter sign_extend : forall [m] n, word m -> word n.
Parameter concat : forall [m] [n], word m -> word n -> word (m + n).

Parameter and : forall [n], word n -> word n -> word n.
Parameter  or : forall [n], word n -> word n -> word n.
Parameter xor : forall [n], word n -> word n -> word n.
Parameter not : forall [n], word n -> word n.

Parameter add : forall [n], word n -> word n -> word n.
Parameter sub : forall [n], word n -> word n -> word n.
Parameter mul : forall [n], word n -> word n -> word n.

Parameter logical_shift_left  : forall [n], word n -> nat -> word n.
Parameter logical_shift_right : forall [n], word n -> nat -> word n.
Parameter arith_shift_right  : forall [n], word n -> nat -> word n.

Parameter replicate : forall m [n], word n -> word (m * n).

Parameter eqb : forall [n], word n -> word n -> bool.
Axiom eqb_true_iff : forall {n} (w v : word n), eqb w v = true <-> w = v.

Parameter eq_dec : forall [n] (w v : word n), {w = v} + {w <> v}.

Parameter reverse_endian : forall [n], word n -> word n.
(*Parameter count_leading_zeros : forall {n}, word n -> nat.*)

Parameter word_to_binary_string : forall [n], word n -> String.string.
(*Parameter word_to_hex_string : forall [n], word n -> String.string.*)
End MachineWordInterface.
