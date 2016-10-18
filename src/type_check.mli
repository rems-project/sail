open Ast
open Type_internal
type kind = Type_internal.kind
type typ = Type_internal.t
type 'a emap = 'a Envmap.t

type envs = Env of def_envs * tannot emap * bounds_env * t_arg emap
type 'a envs_out = 'a * envs


val check : envs -> tannot defs -> tannot defs * envs
