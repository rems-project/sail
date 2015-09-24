open Big_int
open Ast
open Type_internal
type typ = Type_internal.t
type 'a exp = 'a Ast.exp
type 'a emap = 'a Envmap.t
type envs = Type_check.envs

type 'a rewriters = { rewrite_exp : 'a rewriters -> nexp_map option -> 'a exp -> 'a exp;
                      rewrite_lexp : 'a rewriters -> nexp_map option -> 'a lexp -> 'a lexp;
                      rewrite_pat  : 'a rewriters -> nexp_map option -> 'a pat -> 'a pat;
                      rewrite_let  : 'a rewriters -> nexp_map option -> 'a letbind -> 'a letbind;
                      rewrite_fun  : 'a rewriters -> 'a fundef -> 'a fundef;
                      rewrite_def  : 'a rewriters -> 'a def -> 'a def;
                      rewrite_defs : 'a rewriters -> 'a defs -> 'a defs;
                    }

val rewrite_exp : tannot rewriters -> nexp_map option -> tannot exp -> tannot exp
val rewrite_defs : tannot defs -> tannot defs
