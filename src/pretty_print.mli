open Ast
open Type_internal

(* Prints the defs following source syntax *)
val pp_defs : out_channel -> tannot defs -> unit
val pp_exp : Buffer.t -> exp -> unit
val pat_to_string : tannot pat -> string

(* Prints on formatter the defs as Lem Ast nodes *)
val pp_lem_defs : Format.formatter -> tannot defs -> unit

val pp_defs_ocaml : out_channel -> tannot defs -> string -> string list -> unit
val pp_defs_lem : (out_channel * string list) -> (out_channel * string list) -> (out_channel * string list) -> tannot defs -> string -> unit
