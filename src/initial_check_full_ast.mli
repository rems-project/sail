
open Ast
open Type_internal

(*Envs is a tuple of used names (currently unused), map from id to kind, default order for vector types and literal vectors *)
type envs = Nameset.t * kind Envmap.t * Ast.order 
type 'a envs_out = 'a * envs

val to_checked_ast : Nameset.t -> kind Envmap.t -> Ast.order -> tannot defs -> tannot defs * kind Envmap.t * Ast.order
val to_exp : kind Envmap.t -> Ast.order -> exp -> exp
