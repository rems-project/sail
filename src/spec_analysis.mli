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
