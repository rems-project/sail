type nat = int
type natural = Big_int.big_int

val natural_monus : natural -> natural -> natural
val natural_pred : natural -> natural

val nat_pred  : nat -> nat
val nat_monus : nat -> nat -> nat
val int_div   : int -> int -> int
val int32_div : Int32.t -> Int32.t -> Int32.t
val int64_div : Int64.t -> Int64.t -> Int64.t
val int_mod   : int -> int -> int
val int32_mod : Int32.t -> Int32.t -> Int32.t
val int64_mod : Int64.t -> Int64.t -> Int64.t
