open Ast

module Types =
 struct
  type id_type =
  | Local_variable
  | Global_register
  | Enum_member

  type vector_concat_split =
  | No_split
  | Split of Big_int_Z.big_int
 end

module type S =
 sig
  type t

  val get_type : t -> typ

  val get_id_type : t -> id -> Types.id_type

  val get_split : t -> Types.vector_concat_split

  val is_bitvector : t -> bool

  val fallthrough : t pexp
 end
