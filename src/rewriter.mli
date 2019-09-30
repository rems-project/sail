(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

(** General rewriting framework for Sail->Sail rewrites *)

module Big_int = Nat_big_num
open Ast
open Type_check

type 'a rewriters = { rewrite_exp     : 'a rewriters -> 'a exp -> 'a exp;
                      rewrite_lexp    : 'a rewriters -> 'a lexp -> 'a lexp;
                      rewrite_pat     : 'a rewriters -> 'a pat -> 'a pat;
                      rewrite_let     : 'a rewriters -> 'a letbind -> 'a letbind;
                      rewrite_fun     : 'a rewriters -> 'a fundef -> 'a fundef;
                      rewrite_mapping : 'a rewriters -> 'a mapdef -> 'a mapdef;
                      rewrite_def     : 'a rewriters -> 'a def -> 'a def;
                      rewrite_defs    : 'a rewriters -> 'a defs -> 'a defs;
                    }

val rewrite_exp : tannot rewriters -> tannot exp -> tannot exp

val rewriters_base : tannot rewriters

(** The identity re-writer *)
val rewrite_defs : tannot defs -> tannot defs

val rewrite_defs_base : tannot rewriters -> tannot defs -> tannot defs

val rewrite_defs_base_parallel : int -> tannot rewriters -> tannot defs -> tannot defs

(** Same as rewrite_defs_base but display a progress bar when verbosity >= 1 *)
val rewrite_defs_base_progress : string -> tannot rewriters -> tannot defs -> tannot defs

val rewrite_lexp : tannot rewriters -> tannot lexp -> tannot lexp

val rewrite_pat : tannot rewriters -> tannot pat -> tannot pat

val rewrite_pexp : tannot rewriters -> tannot pexp -> tannot pexp

val rewrite_let : tannot rewriters -> tannot letbind -> tannot letbind

val rewrite_def : tannot rewriters -> tannot def -> tannot def

val rewrite_fun : tannot rewriters -> tannot fundef -> tannot fundef

val rewrite_mapping : tannot rewriters -> tannot mapdef -> tannot mapdef

(* the type of interpretations of expressions *)
type ('a,'exp,'exp_aux,'lexp,'lexp_aux,'fexp,'fexp_aux,
      'guard,'guard_aux,'pexp,'pexp_aux,'letbind_aux,'letbind,
      'pat,'pat_aux) algebra =
 { e_block                  : 'exp list -> 'exp_aux
 ; e_id                     : id -> 'exp_aux
 ; e_ref                    : id -> 'exp_aux
 ; e_lit                    : lit -> 'exp_aux
 ; e_cast                   : Ast.typ * 'exp -> 'exp_aux
 ; e_app                    : id * 'exp list -> 'exp_aux
 ; e_app_infix              : 'exp * id * 'exp -> 'exp_aux
 ; e_tuple                  : 'exp list -> 'exp_aux
 ; e_if                     : 'exp * 'exp * 'exp -> 'exp_aux
 ; e_for                    : id * 'exp * 'exp * 'exp * Ast.order * 'exp -> 'exp_aux
 ; e_loop                   : loop * ('exp option * Parse_ast.l) * 'exp * 'exp -> 'exp_aux
 ; e_vector                 : 'exp list -> 'exp_aux
 ; e_vector_access          : 'exp * 'exp -> 'exp_aux
 ; e_vector_subrange        : 'exp * 'exp * 'exp -> 'exp_aux
 ; e_vector_update          : 'exp * 'exp * 'exp -> 'exp_aux
 ; e_vector_update_subrange : 'exp * 'exp * 'exp * 'exp -> 'exp_aux
 ; e_vector_append          : 'exp * 'exp -> 'exp_aux
 ; e_list                   : 'exp list -> 'exp_aux
 ; e_cons                   : 'exp * 'exp -> 'exp_aux
 ; e_record                 : 'fexp list -> 'exp_aux
 ; e_record_update          : 'exp * 'fexp list -> 'exp_aux
 ; e_field                  : 'exp * id -> 'exp_aux
 ; e_case                   : 'exp * 'pexp list -> 'exp_aux
 ; e_try                    : 'exp * 'pexp list -> 'exp_aux
 ; e_let                    : 'letbind * 'exp -> 'exp_aux
 ; e_assign                 : 'lexp * 'exp -> 'exp_aux
 ; e_sizeof                 : nexp -> 'exp_aux
 ; e_constraint             : n_constraint -> 'exp_aux
 ; e_exit                   : 'exp -> 'exp_aux
 ; e_throw                  : 'exp -> 'exp_aux
 ; e_return                 : 'exp -> 'exp_aux
 ; e_assert                 : 'exp * 'exp -> 'exp_aux
 ; e_var                    : 'lexp * 'exp * 'exp -> 'exp_aux
 ; e_internal_plet          : 'pat * 'exp * 'exp -> 'exp_aux
 ; e_internal_return        : 'exp -> 'exp_aux
 ; e_internal_cascade       : cascade_type * 'exp * (id * 'pexp list) list * 'pexp list -> 'exp_aux
 ; e_internal_value         : Value.value -> 'exp_aux
 ; e_aux                    : 'exp_aux * 'a annot -> 'exp
 ; lEXP_id                  : id -> 'lexp_aux
 ; lEXP_deref               : 'exp -> 'lexp_aux
 ; lEXP_memory              : id * 'exp list -> 'lexp_aux
 ; lEXP_cast                : Ast.typ * id -> 'lexp_aux
 ; lEXP_tup                 : 'lexp list -> 'lexp_aux
 ; lEXP_vector              : 'lexp * 'exp -> 'lexp_aux
 ; lEXP_vector_range        : 'lexp * 'exp * 'exp -> 'lexp_aux
 ; lEXP_vector_concat       : 'lexp list -> 'lexp_aux
 ; lEXP_field               : 'lexp * id -> 'lexp_aux
 ; lEXP_aux                 : 'lexp_aux * 'a annot -> 'lexp
 ; fE_Fexp                  : id * 'exp -> 'fexp_aux
 ; fE_aux                   : 'fexp_aux * l -> 'fexp
 ; g_aux                    : 'guard_aux * l -> 'guard
 ; g_if                     : 'exp -> 'guard_aux
 ; g_pattern                : 'pat * 'exp -> 'guard_aux
 ; pat_case                 : 'pat * 'guard list * 'exp -> 'pexp_aux
 ; pat_aux                  : 'pexp_aux * l -> 'pexp
 ; lB_val                   : 'pat * 'exp -> 'letbind_aux
 ; lB_aux                   : 'letbind_aux * 'a annot -> 'letbind
 ; p_lit                    : lit -> 'pat_aux
 ; p_wild                   : 'pat_aux
 ; p_or                     : 'pat * 'pat -> 'pat_aux
 ; p_not                    : 'pat -> 'pat_aux
 ; p_as                     : 'pat * id -> 'pat_aux
 ; p_typ                    : Ast.typ * 'pat -> 'pat_aux
 ; p_id                     : id -> 'pat_aux
 ; p_var                    : 'pat * typ_pat -> 'pat_aux
 ; p_app                    : id * 'pat list -> 'pat_aux
 ; p_vector                 : 'pat list -> 'pat_aux
 ; p_vector_concat          : 'pat list -> 'pat_aux
 ; p_tup                    : 'pat list -> 'pat_aux
 ; p_list                   : 'pat list -> 'pat_aux
 ; p_cons                   : 'pat * 'pat -> 'pat_aux
 ; p_string_append          : 'pat list -> 'pat_aux
 ; p_view                   : 'pat * id * 'exp list -> 'pat_aux
 ; p_aux                    : 'pat_aux * 'a annot -> 'pat
 }

(* fold over patterns *)
val fold_pat : ('a,'exp,'exp_aux,'lexp,'lexp_aux,'fexp,'fexp_aux,
      'guard,'guard_aux,'pexp,'pexp_aux,'letbind_aux,'letbind,
      'pat,'pat_aux) algebra -> 'a pat -> 'pat

(* fold over expressions *)
val fold_exp : ('a,'exp,'exp_aux,'lexp,'lexp_aux,'fexp,'fexp_aux,
      'guard,'guard_aux,'pexp,'pexp_aux,'letbind_aux,'letbind,
      'pat,'pat_aux) algebra -> 'a exp -> 'exp

val fold_letbind : ('a,'exp,'exp_aux,'lexp,'lexp_aux,'fexp,'fexp_aux,
      'guard,'guard_aux,'pexp,'pexp_aux,'letbind_aux,'letbind,
      'pat,'pat_aux) algebra -> 'a letbind -> 'letbind

val fold_pexp : ('a,'exp,'exp_aux,'lexp,'lexp_aux,'fexp,'fexp_aux,
      'guard,'guard_aux,'pexp,'pexp_aux,'letbind_aux,'letbind,
      'pat,'pat_aux) algebra -> 'a pexp -> 'pexp

val fold_funcl : ('a,'exp,'exp_aux,'lexp,'lexp_aux,'fexp,'fexp_aux,
      'guard,'guard_aux,'a pexp,'pexp_aux,'letbind_aux,'letbind,
      'pat,'pat_aux) algebra -> 'a funcl -> 'a funcl

val fold_function : ('a,'exp,'exp_aux,'lexp,'lexp_aux,'fexp,'fexp_aux,
      'guard,'guard_aux,'a pexp,'pexp_aux,'letbind_aux,'letbind,
      'pat,'pat_aux) algebra -> 'a fundef -> 'a fundef

val id_algebra :
  ('a,
   'a exp, 'a exp_aux,
   'a lexp,'a lexp_aux,
   'a fexp, 'a fexp_aux,
   'a guard, 'a guard_aux,
   'a pexp, 'a pexp_aux,
   'a letbind_aux, 'a letbind,
   'a pat, 'a pat_aux) algebra

val compute_algebra : 'b -> ('b -> 'b -> 'b) ->
  ('a,
   ('b * 'a exp), ('b * 'a exp_aux),
   ('b * 'a lexp), ('b * 'a lexp_aux),
   ('b * 'a fexp), ('b * 'a fexp_aux),
   ('b * 'a guard), ('b * 'a guard_aux),
   ('b * 'a pexp), ('b * 'a pexp_aux),
   ('b * 'a letbind_aux), ('b * 'a letbind),
   ('b * 'a pat), ('b * 'a pat_aux)) algebra

val pure_algebra : 'b -> ('b -> 'b -> 'b) ->
  ('a,'b,'b,'b,'b,'b,'b,'b,'b,'b,'b,'b,'b,'b,'b) algebra

val simple_annot : Parse_ast.l -> typ -> Parse_ast.l * tannot

val add_p_typ : typ -> tannot pat -> tannot pat

val add_e_cast : typ -> tannot exp -> tannot exp

val union_eff_exps : (tannot exp) list -> effect

val effect_of_pexp : tannot pexp -> effect

val fix_eff_exp : tannot exp -> tannot exp

val fix_eff_lexp : tannot lexp -> tannot lexp

val fix_eff_lb : tannot letbind -> tannot letbind

(* In-order fold over expressions *)
val foldin_exp : (('a -> 'b exp -> 'a * 'b exp) -> 'a -> 'b exp -> 'a * 'b exp) -> 'a -> 'b exp -> 'a * 'b exp
val foldin_pexp : (('a -> 'b exp -> 'a * 'b exp) -> 'a -> 'b exp -> 'a * 'b exp) -> 'a -> 'b pexp -> 'a * 'b pexp
