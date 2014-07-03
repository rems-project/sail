
open Ast
open Type_internal
type kind = Type_internal.kind
type typ = Type_internal.t

type envs = Nameset.t * kind Envmap.t * tannot Envmap.t
type 'a envs_out = 'a * envs

val to_ast : Nameset.t -> kind Envmap.t -> tannot Envmap.t -> Parse_ast.defs -> tannot defs * kind Envmap.t
val to_ast_exp : kind Envmap.t -> Parse_ast.exp -> Type_internal.tannot Ast.exp
