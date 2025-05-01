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
(*    Louis-Emile Ploix                                                     *)
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

open Libsail

open Ast
open Ast_util
open Jib
open Jib_util

type footprint = {
  direct_reads : NameSet.t;
  direct_writes : NameSet.t;
  direct_throws : bool;
  all_reads : NameSet.t;
  all_writes : NameSet.t;
  throws : bool;
  need_stdout : bool;
  need_stderr : bool;
  reads_mem : bool;
  writes_mem : bool;
  contains_assert : bool;
  exits : bool;
}

val pure_footprint : footprint

type spec_info = {
  register_ctyp_map : NameSet.t CTMap.t;  (** A map from register types to all the registers with that type *)
  registers : (ctyp * unit def_annot) NameMap.t;  (** A map from register names to types *)
  initialized_registers : name list;  (** A list of registers with initial values *)
  constructors : IdSet.t;  (** A list of constructor functions *)
  global_lets : NameSet.t;  (** Global letbindings *)
  global_let_numbers : Ast.id list Util.IntMap.t;  (** Global let numbers *)
  footprints : footprint Bindings.t;  (** Function footprint information *)
  callgraph : Jib_compile.IdGraph.graph;  (** Specification callgraph *)
  exception_ctyp : ctyp;  (** The type of exceptions *)
}

val collect_spec_info : Jib_compile.ctx -> cdef list -> spec_info
