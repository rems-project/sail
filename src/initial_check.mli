
open Type_internal
open Ast

type 'a envs = 'a * Nameset.t * kind Kindmap.t * t Typmap.t

val to_ast : Nameset.t -> kind Kindmap.t -> t Typmap.t -> tannot def list -> Parse_ast.defs -> tannot defs
(*val to_ast_def : nameset -> kind kindmap -> t typmap -> tannot def list -> Parse_ast.defs -> (annot def) envs * annot def list
val to_ast_fun : nameset -> kind kindmap -> t typmap -> Parse_ast.fundef -> (annot fundef) envs
val to_ast_expr : nameset -> kind kindmap -> t typmap -> Parse_ast.exp -> (annot exp) envs
val to_ast_targ : nameset -> kind kindmap -> t typmap -> Parse_ast.atyp -> (annot typ_arg) envs
val to_ast_typ : nameset -> kind kindmap -> t typmap -> Parse_ast.atyp -> (annot typ) envs
val to_ast_nexp : nameset -> kind kindmap -> t typmap -> Parse_ast.atyp -> (annot nexp) envs
*)
