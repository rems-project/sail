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

type mut = Immutable | Mutable

type lvar = Register of typ | Enum of typ | Local of mut * typ | Unbound

module Env : sig
  type t
  val get_val_spec : id -> t -> typquant * typ
  val add_val_spec : id -> typquant * typ -> t -> t
  (* val get_local : id -> t -> mut * typ *)
  val add_local : id -> mut * typ -> t -> t
  val get_register : id -> t -> typ
  val add_register : id -> typ -> t -> t
  val is_mutable : id -> t -> bool
  val get_constraints : t -> n_constraint list
  val add_constraint : n_constraint -> t -> t
  val get_typ_var : kid -> t -> base_kind_aux
  val add_typ_var : kid -> base_kind_aux -> t -> t
  val get_ret_typ : t -> typ option
  val add_ret_typ : typ -> t -> t
  val add_typ_synonym : id -> (typ_arg list -> typ) -> t -> t
  val get_typ_synonym : id -> t -> typ_arg list -> typ
  val lookup_id : id -> t -> lvar
  val fresh_kid : t -> kid
  val expand_synonyms : t -> typ -> typ
  val empty : t                                   
end

type tannot = (Env.t * typ) option

val check_exp : Env.t -> unit exp -> typ -> tannot exp
               
val check : Env.t -> 'a defs -> tannot defs * Env.t

val initial_env : Env.t
