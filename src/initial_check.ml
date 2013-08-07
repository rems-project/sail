open Type_internal
open Ast

type 'a envs = 'a * Nameset.t * kind Kindmap.t * t Typmap.t

let rec to_ast (bound_names : Nameset.t) (kind_env : kind Kindmap.t) (typ_env : t Typmap.t) partial_defs defs =
  (Defs [])
