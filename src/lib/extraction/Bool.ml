open Datatypes

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF
