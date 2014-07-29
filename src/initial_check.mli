
open Ast
open Type_internal
type kind = Type_internal.kind
type typ = Type_internal.t

(*Envs is a tuple of used names (currently unused), map from id to kind, default order for vector types and literal vectors *)
type envs = Nameset.t * kind Envmap.t * Ast.order 
type 'a envs_out = 'a * envs

val to_ast : Nameset.t -> kind Envmap.t -> Ast.order -> Parse_ast.defs -> tannot defs * kind Envmap.t * Ast.order
val to_ast_exp : kind Envmap.t -> Ast.order -> Parse_ast.exp -> Type_internal.tannot Ast.exp
