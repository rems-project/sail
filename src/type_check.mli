open Ast
open Type_internal
type kind = Type_internal.kind
type typ = Type_internal.t
type 'a emap = 'a Envmap.t

type rec_kind = Record | Register
type def_envs = { 
  k_env: kind emap; 
  abbrevs: tannot emap; 
  namesch : tannot emap; 
  enum_env : (string list) emap; 
  rec_env : (string * rec_kind * ((string * tannot) list)) list;
 }
type envs = Env of def_envs * tannot emap
type 'a envs_out = 'a * envs


val check : envs -> tannot defs -> tannot defs
