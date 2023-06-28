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

open Libsail

let opt_includes_c : string list ref = ref []
let opt_specialize_c = ref false

let c_options =
  [
    ( "-c_include",
      Arg.String (fun i -> opt_includes_c := i :: !opt_includes_c),
      "<filename> provide additional include for C output"
    );
    ("-c_no_main", Arg.Set C_backend.opt_no_main, " do not generate the main() function");
    ("-c_no_rts", Arg.Set C_backend.opt_no_rts, " do not include the Sail runtime");
    ( "-c_no_lib",
      Arg.Tuple [Arg.Set C_backend.opt_no_lib; Arg.Set C_backend.opt_no_rts],
      " do not include the Sail runtime or library"
    );
    ("-c_prefix", Arg.String (fun prefix -> C_backend.opt_prefix := prefix), "<prefix> prefix generated C functions");
    ( "-c_extra_params",
      Arg.String (fun params -> C_backend.opt_extra_params := Some params),
      "<parameters> generate C functions with additional parameters"
    );
    ( "-c_extra_args",
      Arg.String (fun args -> C_backend.opt_extra_arguments := Some args),
      "<arguments> supply extra argument to every generated C function call"
    );
    ("-c_specialize", Arg.Set opt_specialize_c, " specialize integer arguments in C output");
    ( "-c_preserve",
      Arg.String (fun str -> Specialize.add_initial_calls (Ast_util.IdSet.singleton (Ast_util.mk_id str))),
      " make sure the provided function identifier is preserved in C output"
    );
    ( "-c_fold_unit",
      Arg.String (fun str -> Constant_fold.opt_fold_to_unit := Util.split_on_char ',' str),
      " remove comma separated list of functions from C output, replacing them with unit"
    );
    ( "-c_coverage",
      Arg.String (fun str -> C_backend.opt_branch_coverage := Some (open_out str)),
      "<file> Turn on coverage tracking and output information about all branches and functions to a file"
    );
    ( "-O",
      Arg.Tuple
        [
          Arg.Set C_backend.optimize_primops;
          Arg.Set C_backend.optimize_hoist_allocations;
          Arg.Set Initial_check.opt_fast_undefined;
          Arg.Set C_backend.optimize_struct_updates;
          Arg.Set C_backend.optimize_alias;
        ],
      " turn on optimizations for C compilation"
    );
    ( "-Ofixed_int",
      Arg.Set C_backend.optimize_fixed_int,
      " assume fixed size integers rather than GMP arbitrary precision integers"
    );
    ( "-Ofixed_bits",
      Arg.Set C_backend.optimize_fixed_bits,
      " assume fixed size bitvectors rather than arbitrary precision bitvectors"
    );
    ("-static", Arg.Set C_backend.opt_static, " make generated C functions static");
  ]

let c_rewrites =
  let open Rewrites in
  [
    ("instantiate_outcomes", [String_arg "c"]);
    ("realize_mappings", []);
    ("remove_vector_subrange_pats", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("truncate_hex_literals", []);
    ("mono_rewrites", [If_flag opt_mono_rewrites]);
    ("recheck_defs", [If_flag opt_mono_rewrites]);
    ("toplevel_nexps", [If_mono_arg]);
    ("monomorphise", [String_arg "c"; If_mono_arg]);
    ("atoms_to_singletons", [String_arg "c"; If_mono_arg]);
    ("recheck_defs", [If_mono_arg]);
    ("undefined", [Bool_arg false]);
    ("vector_string_pats_to_bit_list", []);
    ("remove_not_pats", []);
    ("remove_vector_concat", []);
    ("remove_bitvector_pats", []);
    ("pattern_literals", [Literal_arg "all"]);
    ("tuple_assignments", []);
    ("vector_concat_assignments", []);
    ("simple_struct_assignments", []);
    ("exp_lift_assign", []);
    ("merge_function_clauses", []);
    ("recheck_defs", []);
    ("constant_fold", [String_arg "c"]);
  ]

let c_target _ _ out_file ast effect_info env =
  let close, output_chan = match out_file with Some f -> (true, open_out (f ^ ".c")) | None -> (false, stdout) in
  Reporting.opt_warnings := true;
  C_backend.compile_ast env effect_info output_chan !opt_includes_c ast;
  flush output_chan;
  if close then close_out output_chan

let _ =
  Target.register ~name:"c" ~options:c_options
    ~pre_parse_hook:(fun () -> Initial_check.opt_undefined_gen := true)
    ~rewrites:c_rewrites c_target
