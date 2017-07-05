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

(* Functions to map over the annotations in sub-expressions *)
val map_exp_annot : ('a annot -> 'b annot) -> 'a exp -> 'b exp
val map_pat_annot : ('a annot -> 'b annot) -> 'a pat -> 'b pat
val map_lexp_annot : ('a annot -> 'b annot) -> 'a lexp -> 'b lexp

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
