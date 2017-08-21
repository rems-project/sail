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
(*    Thomas Bauereiss                                                    *)
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

open Ast

val mk_nc : n_constraint_aux -> n_constraint
val mk_nexp : nexp_aux -> nexp
val mk_exp : unit exp_aux -> unit exp
val mk_lit : lit_aux -> lit

val unaux_exp : 'a exp -> 'a exp_aux

(* Functions to map over the annotations in sub-expressions *)
val map_exp_annot : ('a annot -> 'b annot) -> 'a exp -> 'b exp
val map_pat_annot : ('a annot -> 'b annot) -> 'a pat -> 'b pat
val map_lexp_annot : ('a annot -> 'b annot) -> 'a lexp -> 'b lexp
val map_letbind_annot : ('a annot -> 'b annot) -> 'a letbind -> 'b letbind

(* Extract locations from identifiers *)
val id_loc : id -> Parse_ast.l
val kid_loc : kid -> Parse_ast.l

(* For debugging and error messages only: Not guaranteed to produce
   parseable SAIL, or even print all language constructs! *)
(* TODO: replace with existing pretty-printer *)
val string_of_id : id -> string
val string_of_kid : kid -> string
val string_of_base_effect_aux : base_effect_aux -> string
val string_of_base_kind_aux : base_kind_aux -> string
val string_of_base_kind : base_kind -> string
val string_of_kind : kind -> string
val string_of_base_effect : base_effect -> string
val string_of_effect : effect -> string
val string_of_order : order -> string
val string_of_nexp : nexp -> string
val string_of_typ : typ -> string
val string_of_typ_arg : typ_arg -> string
val string_of_n_constraint : n_constraint -> string
val string_of_quant_item : quant_item -> string
val string_of_typquant : typquant -> string
val string_of_typschm : typschm -> string
val string_of_lit : lit -> string
val string_of_exp : 'a exp -> string
val string_of_pexp : 'a pexp -> string
val string_of_lexp : 'a lexp -> string
val string_of_pat : 'a pat -> string
val string_of_letbind : 'a letbind -> string
val string_of_index_range : index_range -> string

val id_of_fundef : 'a fundef -> id

val id_of_kid : kid -> id

module Id : sig
  type t = id
  val compare : id -> id -> int
end

module Kid : sig
  type t = kid
  val compare : kid -> kid -> int
end

module BE : sig
  type t = base_effect
  val compare : base_effect -> base_effect -> int
end

module IdSet : sig
  include Set.S with type elt = id
end

module KidSet : sig
  include Set.S with type elt = kid
end

module KBindings : sig
  include Map.S with type key = kid
end

module Bindings : sig
  include Map.S with type key = id
end

val nexp_frees : nexp -> KidSet.t
val nexp_identical : nexp -> nexp -> bool
val is_nexp_constant : nexp -> bool
val simplify_nexp : nexp -> nexp

val is_number : typ -> bool
val is_vector_typ : typ -> bool
val is_bit_typ : typ -> bool
val is_bitvector_typ : typ -> bool

val typ_app_args_of : typ -> string * typ_arg_aux list * Ast.l
val vector_typ_args_of : typ -> nexp * nexp * order * typ

val is_order_inc : order -> bool

val has_effect : effect -> base_effect_aux -> bool
