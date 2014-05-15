open Ast
open Type_internal

(* Prints on formatter the defs following source syntax *)
val pp_defs : out_channel -> tannot defs -> unit
val pp_exp : out_channel -> exp -> unit

(* Prints on formatter the defs as Lem Ast nodes *)
val pp_lem_defs : Format.formatter -> tannot defs -> unit
