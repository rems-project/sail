(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

open Ast

(** {1 Set and Map modules for various AST elements} *)

module Id : sig
  type t = id
  val compare : id -> id -> int
end

module Kid : sig
  type t = kid
  val compare : kid -> kid -> int
end

module Kind : sig
  type t = kind
  val compare : kind -> kind -> int
end

module KOpt : sig
  type t = kinded_id
  val compare : kinded_id -> kinded_id -> int
end

module Nexp : sig
  type t = nexp
  val compare : nexp -> nexp -> int
end

module NC : sig
  type t = n_constraint
  val compare : n_constraint -> n_constraint -> int
end

(* NB: the comparison function does not expand synonyms *)
module Typ : sig
  type t = typ
  val compare : typ -> typ -> int
end

module Lit : sig
  type t = lit
  val compare : lit -> lit -> int
end

module TypArg : sig
  type t = typ_arg
  val compare : typ_arg -> typ_arg -> int
end

module IdSet : sig
  include Set.S with type elt = id and type t = Set.Make(Id).t
end

module NexpSet : sig
  include Set.S with type elt = nexp
end

module NexpMap : sig
  include Map.S with type key = nexp
end

module KOptSet : sig
  include Set.S with type elt = kinded_id
end

module KOptMap : sig
  include Map.S with type key = kinded_id
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

module NCMap : sig
  include Map.S with type key = n_constraint
end

module TypMap : sig
  include Map.S with type key = typ
end

module LitSet : sig
  include Set.S with type elt = lit
end
