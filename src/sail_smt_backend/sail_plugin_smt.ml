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

open Jib_smt

let opt_smt_auto = ref false
let opt_smt_auto_solver = ref Smt_exp.Cvc5
let opt_smt_includes : string list ref = ref []
let opt_smt_ignore_overflow = ref false
let opt_smt_unknown_integer_width = ref 128
let opt_smt_unknown_bitvector_width = ref 64
let opt_smt_unknown_generic_vector_width = ref 32

let set_smt_auto_solver arg =
  let open Smt_exp in
  match counterexample_solver_from_name arg with Some solver -> opt_smt_auto_solver := solver | None -> ()

let smt_options =
  [
    ("-smt_auto", Arg.Tuple [Arg.Set opt_smt_auto], " automatically call the smt solver on generated SMT");
    ( "-smt_auto_solver",
      Arg.Tuple [Arg.Set opt_smt_auto; Arg.String set_smt_auto_solver],
      "<cvc4/cvc5/z3> set the solver to use for counterexample checks (default cvc5)"
    );
    ("-smt_ignore_overflow", Arg.Set opt_smt_ignore_overflow, " ignore integer overflow in generated SMT");
    ( "-smt_int_size",
      Arg.String (fun n -> opt_smt_unknown_integer_width := int_of_string n),
      "<n> set a bound of n on the maximum integer bitwidth for generated SMT (default 128)"
    );
    ("-smt_propagate_vars", Arg.Unit (fun () -> ()), " (deprecated) propgate variables through generated SMT");
    ( "-smt_bits_size",
      Arg.String (fun n -> opt_smt_unknown_bitvector_width := int_of_string n),
      "<n> set a size bound of n for unknown-length bitvectors in generated SMT (default 64)"
    );
    ( "-smt_vector_size",
      Arg.String (fun n -> opt_smt_unknown_generic_vector_width := int_of_string n),
      "<n> set a bound of 2 ^ n for generic vectors in generated SMT (default 5)"
    );
    ( "-smt_include",
      Arg.String (fun i -> opt_smt_includes := i :: !opt_smt_includes),
      "<filename> insert additional file in SMT output"
    );
  ]

let smt_rewrites =
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
    ("properties", []);
  ]

let smt_target _ _ out_file ast effect_info env =
  let open Ast_util in
  let properties = Property.find_properties ast in
  let prop_ids = Bindings.bindings properties |> List.map fst |> IdSet.of_list in
  let ast = Callgraph.filter_ast_ids prop_ids IdSet.empty ast in
  Specialize.add_initial_calls prop_ids;
  let ast_smt, env, effect_info = Specialize.(specialize typ_specialization env ast effect_info) in
  let ast_smt, env, effect_info =
    Specialize.(specialize_passes 2 int_specialization_with_externs env ast_smt effect_info)
  in
  let name_file =
    match out_file with Some f -> fun str -> f ^ "_" ^ str ^ ".smt2" | None -> fun str -> str ^ ".smt2"
  in
  Reporting.opt_warnings := true;
  let cdefs, ctx, register_map = Jib_smt.compile ~unroll_limit:10 env effect_info ast_smt in
  let module SMTGen = Jib_smt.Make (struct
    let max_unknown_integer_width = !opt_smt_unknown_integer_width
    let max_unknown_bitvector_width = !opt_smt_unknown_bitvector_width
    let max_unknown_generic_vector_length = !opt_smt_unknown_generic_vector_width
    let register_map = register_map
    let ignore_overflow = !opt_smt_ignore_overflow
  end) in
  let module Counterexample = Smt_exp.Counterexample (struct
    let max_unknown_integer_width = !opt_smt_unknown_integer_width
  end) in
  let generated_smt = SMTGen.generate_smt ~properties ~name_file ~smt_includes:!opt_smt_includes ctx cdefs in
  if !opt_smt_auto then
    List.iter
      (fun ({ file_name; function_id; args; arg_ctyps; arg_smt_names } : SMTGen.generated_smt_info) ->
        Counterexample.check ~env:ctx.tc_env ~ast ~solver:!opt_smt_auto_solver ~file_name ~function_id ~args ~arg_ctyps
          ~arg_smt_names
      )
      generated_smt;
  ()

let _ = Target.register ~name:"smt" ~options:smt_options ~rewrites:smt_rewrites smt_target
