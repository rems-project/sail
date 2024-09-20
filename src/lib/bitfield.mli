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
open Ast_util

(** Create an L-expression for setting the bits of a bitfield defined by an index_range type. *)
val set_field_lexp : index_range -> uannot lexp -> uannot lexp

(** Create an L-expression for setting all the bits of a bitfield *)
val set_bits_field_lexp : uannot lexp -> uannot lexp

(** Create an expression converting the given expression from a bitfield to a bitvector *)
val get_bits_field : uannot exp -> uannot exp

(** Create an expression converting the given expression from a bitvector to a bitfield *)
val construct_bitfield_exp : id -> uannot exp -> uannot exp

(** Create an expression converting the given expression from a bitvector to a
    bitfield, but using a struct expression rather than a constructor function *)
val construct_bitfield_struct : id -> uannot exp -> uannot exp

type field_accessor_ids = { get : id; set : id; update : id; overload : id }

(** The [macro] function generates multiple definitions to get, set,
   and update fields, so we can use this function to find the names of
   those functions in a consistent way. *)
val field_accessor_ids : id -> id -> field_accessor_ids

(** Bitfields work a bit like a macro, which generate a struct wrapper
   around a simple bitvector type, along with a host of accessor
   functions. *)
val macro : id -> nexp -> order -> index_range Bindings.t -> untyped_def list
