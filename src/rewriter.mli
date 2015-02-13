open Big_int
open Ast
open Type_internal
type typ = Type_internal.t
type 'a exp = 'a Ast.exp
type 'a emap = 'a Envmap.t
type envs = Type_check.envs

val rewrite_exp : tannot exp -> tannot exp
val rewrite_defs : tannot defs -> tannot defs
