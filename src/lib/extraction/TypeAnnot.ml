open Ast

module type S =
 sig
  type t

  val get_type : t -> typ

  val get_id_type : t -> id -> id_type

  val get_split : t -> vector_concat_split

  val is_bitvector : t -> bool

  val fallthrough : t pexp
 end
