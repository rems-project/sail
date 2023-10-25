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
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

(** Utilities and helper functions for operating on Jib instructions and definitions *)

open Ast
open Ast_util
open Jib

(** {1 Instruction construction functions, and Jib names } *)

(** Create a generator that produces fresh names, paired with a
   function that resets the generator (allowing it to regenerate the
   same name). *)
val symbol_generator : string -> (unit -> id) * (unit -> unit)

val idecl : l -> ctyp -> name -> instr
val ireset : l -> ctyp -> name -> instr
val iinit : l -> ctyp -> name -> cval -> instr
val iif : l -> cval -> instr list -> instr list -> ctyp -> instr
val ifuncall : l -> clexp -> id * ctyp list -> cval list -> instr
val iextern : l -> clexp -> id * ctyp list -> cval list -> instr
val icopy : l -> clexp -> cval -> instr
val iclear : ?loc:l -> ctyp -> name -> instr
val ireturn : ?loc:l -> cval -> instr
val iend : l -> instr
val iblock : ?loc:l -> instr list -> instr
val itry_block : l -> instr list -> instr
val ithrow : l -> cval -> instr
val icomment : ?loc:l -> string -> instr
val ilabel : ?loc:l -> string -> instr
val igoto : ?loc:l -> string -> instr
val iundefined : ?loc:l -> ctyp -> instr
val imatch_failure : l -> instr
val iexit : l -> instr
val iraw : ?loc:l -> string -> instr
val ijump : l -> cval -> string -> instr

(** Create a new unique label by concatenating a string with a unique identifier *)
val label : string -> string

module Name : sig
  type t = name
  val compare : name -> name -> int
end

module NameSet : sig
  include Set.S with type elt = name
end

module NameMap : sig
  include Map.S with type key = name
end

val current_exception : name
val have_exception : name
val throw_location : name
val return : name

val name : id -> name
val global : id -> name

val cval_rename : name -> name -> cval -> cval
val clexp_rename : name -> name -> clexp -> clexp
val instr_rename : name -> name -> instr -> instr
val instrs_rename : name -> name -> instr list -> instr list

val string_of_name : ?deref_current_exception:bool -> ?zencode:bool -> name -> string
val string_of_op : op -> string
val string_of_ctyp : ctyp -> string
val string_of_uid : id * ctyp list -> string
val string_of_value : Value2.vl -> string
val string_of_cval : cval -> string
val string_of_clexp : clexp -> string
val string_of_instr : instr -> string

(** {1. Functions and modules for working with ctyps} *)

val map_ctyp : (ctyp -> ctyp) -> ctyp -> ctyp
val ctyp_equal : ctyp -> ctyp -> bool
val ctyp_compare : ctyp -> ctyp -> int

module CTSet : sig
  include Set.S with type elt = ctyp
end

module CTMap : sig
  include Map.S with type key = ctyp
end

module CTListSet : sig
  include Set.S with type elt = ctyp list
end

module NameCTSet : sig
  include Set.S with type elt = name * ctyp
end

module NameCTMap : sig
  include Map.S with type key = name * ctyp
end

(** {2 Operations for polymorphic Jib ctyps} *)

val ctyp_unify : l -> ctyp -> ctyp -> ctyp KBindings.t

val merge_unifiers : kid -> ctyp -> ctyp -> ctyp option

val ctyp_suprema : ctyp -> ctyp

val ctyp_vars : ctyp -> KidSet.t

val ctyp_ids : ctyp -> IdSet.t

val is_polymorphic : ctyp -> bool

val subst_poly : ctyp KBindings.t -> ctyp -> ctyp

(** {2 Infer types} *)

val cval_ctyp : cval -> ctyp
val clexp_ctyp : clexp -> ctyp
val cdef_ctyps : cdef -> CTSet.t

val cdef_ctyps_has : (ctyp -> bool) -> cdef -> bool

(** {1 Functions for mapping over and extracting information from instructions, values, and definitions} *)

val instr_ids : instr -> NameSet.t
val instr_reads : instr -> NameSet.t
val instr_writes : instr -> NameSet.t

val instr_typed_writes : instr -> NameCTSet.t

val map_cval : (cval -> cval) -> cval -> cval

(** Map over each instruction within an instruction, bottom-up *)
val map_instr : (instr -> instr) -> instr -> instr

val map_instrs : (instr list -> instr list) -> instr -> instr

(** Concat-map over each instruction within an instruction, bottom-up *)
val concatmap_instr : (instr -> instr list) -> instr -> instr list

(** Iterate over each instruction within an instruction, bottom-up *)
val iter_instr : (instr -> unit) -> instr -> unit

(** Map over each instruction in a cdef using map_instr *)
val cdef_map_instr : (instr -> instr) -> cdef -> cdef

val map_clexp_ctyp : (ctyp -> ctyp) -> clexp -> clexp
val map_cval_ctyp : (ctyp -> ctyp) -> cval -> cval
val map_instr_ctyp : (ctyp -> ctyp) -> instr -> instr
val cdef_map_ctyp : (ctyp -> ctyp) -> cdef -> cdef

val map_instr_cval : (cval -> cval) -> instr -> instr

val map_instr_list : (instr -> instr) -> instr list -> instr list

val filter_instrs : (instr -> bool) -> instr list -> instr list

val instr_split_at : (instr -> bool) -> instr list -> instr list * instr list

(** Map over function calls in an instruction sequence, including exception handler where present *)
val map_funcall : (instr -> instr list -> instr list) -> instr list -> instr list

(** Map over each function call in a cdef using map_funcall *)
val cdef_map_funcall : (instr -> instr list -> instr list) -> cdef -> cdef

val cdef_map_cval : (cval -> cval) -> cdef -> cdef

(** Map over each instruction in a cdef using concatmap_instr *)
val cdef_concatmap_instr : (instr -> instr list) -> cdef -> cdef

val c_ast_registers : cdef list -> (id * ctyp * instr list) list
