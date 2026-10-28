[@@@warning "-a"]
open Ast
open Datatypes

type ('v, 'c, 'p, 'a) t =
| Pure of 'a
| Early_return of 'v
| Exit of 'v
| Exception of 'v
| Runtime_type_error of Parse_ast.l
| Match_failure of Parse_ast.l
| Assertion_failed of string
| Call of id * 'v list * ('c -> ('v, 'c, 'p, 'a) t)
| Read_var of 'p * ('v -> ('v, 'c, 'p, 'a) t)
| Write_var of 'p * 'v * (unit -> ('v, 'c, 'p, 'a) t)
| Get_config of Parse_ast.l * string list * typ * ('v -> ('v, 'c, 'p, 'a) t)
| Get_undefined of Parse_ast.l * typ * ('v -> ('v, 'c, 'p, 'a) t)

val bind :
  ('a1, 'a2, 'a3, 'a4) t -> ('a4 -> ('a1, 'a2, 'a3, 'a5) t) -> ('a1, 'a2,
  'a3, 'a5) t

val fmap : ('a4 -> 'a5) -> ('a1, 'a2, 'a3, 'a4) t -> ('a1, 'a2, 'a3, 'a5) t

val pure : 'a4 -> ('a1, 'a2, 'a3, 'a4) t

val lift_option : Parse_ast.l -> 'a4 option -> ('a1, 'a2, 'a3, 'a4) t

val lift_sum : (Parse_ast.l, 'a4) sum -> ('a1, 'a2, 'a3, 'a4) t

val sequence : ('a1, 'a2, 'a3, 'a4) t list -> ('a1, 'a2, 'a3, 'a4 list) t

val get_config : Parse_ast.l -> string list -> typ -> ('a1, 'a2, 'a3, 'a1) t

val get_undefined : Parse_ast.l -> typ -> ('a1, 'a2, 'a3, 'a1) t

val throw : 'a1 -> ('a1, 'a2, 'a3, 'a4) t

type ('v, 'a) caught =
| Continue of 'a
| Caught of 'v

val catch : ('a1, 'a2, 'a3, 'a4) t -> ('a1, 'a2, 'a3, ('a1, 'a4) caught) t
