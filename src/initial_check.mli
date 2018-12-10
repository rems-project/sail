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

open Ast
open Ast_util

(* Generate undefined_T functions for every type T. False by
   default. *)
val opt_undefined_gen : bool ref

(* Generate faster undefined_T functions. Rather than generating
   functions that allow for the undefined values of enums and variants
   to be picked at runtime using a RNG or similar, this creates
   undefined_T functions for those types that simply return a specific
   member of the type chosen at compile time, which is much
   faster. These functions don't have the right effects, so the
   -no_effects flag may be needed if this is true. False by
   default. *)
val opt_fast_undefined : bool ref

(* Allow # in identifiers when set, like the GHC option of the same name *)
val opt_magic_hash : bool ref

(* When true enums can be automatically casted to range types and
   back.  Otherwise generated T_of_num and num_of_T functions must be
   manually used for each enum T *)
val opt_enum_casts : bool ref

(* This is a bit of a hack right now - it ensures that the undefiend
   builtins (undefined_vector etc), only get added to the ast
   once. The original assumption in sail is that the whole AST gets
   processed at once (therefore they could only get added once), and
   this isn't true any more with the interpreter. This needs to be
   public so the interpreter can set it back to false if it unloads
   all the loaded files. *)
val have_undefined_builtins : bool ref

val ast_of_def_string : order -> string -> unit defs
val process_ast : order -> Parse_ast.defs -> unit defs

val val_spec_ids : 'a defs -> IdSet.t

val extern_of_string : id -> string -> unit def
val val_spec_of_string : id -> string -> unit def

val exp_of_string : string -> unit exp
val typ_of_string : string -> typ
