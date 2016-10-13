open Ast
open Util
open Big_int
open Type_internal

type typ = Type_internal.t

(*Returns the declared default order of a set of definitions, defaulting to Inc if no default is provided *)
val default_order : tannot defs -> order

(*Determines if the first typ is within the range of the the second typ, 
  using the constraints provided when the first typ contains variables. 
  It is an error for second typ to be anything other than a range type
  If the first typ is a vector, then determines if the max representable 
  number is in the range of the second; it is an error for the first typ
  to be anything other than a vector, a range, an atom, or a bit (after
  suitable unwrapping of abbreviations, reg, and registers). 
*)
val is_within_range: typ -> typ -> nexp_range list -> triple
val is_within_machine64 : typ -> nexp_range list -> triple

(* free variables and dependencies *)

(*fv_of_def consider_ty_vars consider_scatter_as_one all_defs all_defs def -> (bound_by_def, free_in_def) *)
val fv_of_def: bool -> bool -> (tannot def) list -> tannot def -> Nameset.t * Nameset.t

(*group_defs consider_scatter_as_one all_defs -> ((bound_by_def, free_in_def), def) list *)
val group_defs : bool -> tannot defs -> ((Nameset.t * Nameset.t) * (tannot def)) list

(*reodering definitions, initial functions *)
(* produce a new ordering for defs, limiting to those listed in the list, which respects dependencies *)
val restrict_defs : tannot defs -> string list -> tannot defs

val top_sort_defs : tannot defs -> tannot defs
