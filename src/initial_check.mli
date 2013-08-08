
open Ast
open Type_internal
type kind = Type_internal.kind
type typ = Type_internal.t

type envs = Nameset.t * kind Envmap.t * typ Envmap.t
type 'a envs_out = 'a * envs

val to_ast : Nameset.t -> kind Envmap.t -> typ Envmap.t -> Parse_ast.defs -> tannot defs
