open Ast
open Type_internal
open Format

(* Prints on formatter the defs following source syntax *)
val pp_defs : Format.formatter -> tannot defs -> unit

(* Prints on formatter the defs as Lem Ast nodes *)
val pp_lem_defs : Format.formatter -> tannot defs -> unit
