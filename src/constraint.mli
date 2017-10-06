type nexp
type t

type smt_result = Unknown | Sat | Unsat

val load_digests : unit -> unit
val save_digests : unit -> unit

val call_z3 : t -> smt_result

val string_of : t -> string

val implies : t -> t -> t
val conj : t -> t -> t
val disj : t -> t -> t
val negate : t -> t
val branch : t list -> t
val literal : bool -> t

val lt : nexp -> nexp -> t
val lteq : nexp -> nexp -> t
val gt : nexp -> nexp -> t
val gteq : nexp -> nexp -> t
val eq : nexp -> nexp -> t
val neq : nexp -> nexp -> t

val pow2 : nexp -> nexp
val add : nexp -> nexp -> nexp
val sub : nexp -> nexp -> nexp
val mult : nexp -> nexp -> nexp

val constant : Big_int.big_int -> nexp
val variable : int -> nexp
