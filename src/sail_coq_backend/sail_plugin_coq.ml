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

let opt_coq_output_dir : string option ref = ref None
let opt_libs_coq : string list ref = ref []
let opt_alt_modules_coq : string list ref = ref []
let opt_alt_modules2_coq : string list ref = ref []

let coq_options =
  [
    ( "-coq_output_dir",
      Arg.String (fun dir -> opt_coq_output_dir := Some dir),
      "<directory> set a custom directory to output generated Coq"
    );
    ( "-coq_lib",
      Arg.String (fun l -> opt_libs_coq := l :: !opt_libs_coq),
      "<filename> provide additional library to open in Coq output"
    );
    ( "-coq_alt_modules",
      Arg.String (fun l -> opt_alt_modules_coq := l :: !opt_alt_modules_coq),
      "<filename> provide alternative modules to open in Coq output"
    );
    ( "-coq_alt_modules2",
      Arg.String (fun l -> opt_alt_modules2_coq := l :: !opt_alt_modules2_coq),
      "<filename> provide additional alternative modules to open only in main (non-_types) Coq output, and suppress \
       default definitions of MR and M monads"
    );
    ( "-coq_extern_type",
      Arg.String Pretty_print_coq.(fun ty -> opt_extern_types := ty :: !opt_extern_types),
      "<typename> do not generate a definition for the type"
    );
    ( "-coq_generate_extern_types",
      Arg.Set Pretty_print_coq.opt_generate_extern_types,
      " generate only extern types rather than suppressing them"
    );
    ( "-dcoq_undef_axioms",
      Arg.Set Pretty_print_coq.opt_undef_axioms,
      " (debug) generate axioms for functions that are declared but not defined"
    );
    ( "-dcoq_warn_nonex",
      Arg.Set Rewrites.opt_coq_warn_nonexhaustive,
      " (debug) generate warnings for non-exhaustive pattern matches in the Coq backend"
    );
    ( "-dcoq_debug_on",
      Arg.String (fun f -> Pretty_print_coq.opt_debug_on := f :: !Pretty_print_coq.opt_debug_on),
      "<function> (debug) produce debug messages for Coq output on given function"
    );
  ]

let coq_rewrites =
  let open Rewrites in
  [
    ("prover_regstate", [Bool_arg true]);
    ("instantiate_outcomes", [String_arg "coq"]);
    ("realize_mappings", []);
    ("remove_vector_subrange_pats", []);
    ("remove_duplicate_valspecs", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("add_unspecified_rec", []);
    ("undefined", [Bool_arg true]);
    ("vector_string_pats_to_bit_list", []);
    ("remove_not_pats", []);
    ("remove_impossible_int_cases", []);
    ("tuple_assignments", []);
    ("vector_concat_assignments", []);
    ("simple_assignments", []);
    ("remove_vector_concat", []);
    ("remove_bitvector_pats", []);
    ("remove_numeral_pats", []);
    ("pattern_literals", [Literal_arg "lem"]);
    ("guarded_pats", []);
    (* ("register_ref_writes", rewrite_register_ref_writes); *)
    ("nexp_ids", []);
    ("split", [String_arg "execute"]);
    ("minimise_recursive_functions", []);
    ("recheck_defs", []);
    (* ("remove_assert", rewrite_ast_remove_assert); *)
    ("move_termination_measures", []);
    ("top_sort_defs", []);
    ("const_prop_mutrec", [String_arg "coq"]);
    ("exp_lift_assign", []);
    ("early_return", []);
    (* We need to do the exhaustiveness check before merging, because it may
       introduce new wildcard clauses *)
    ("recheck_defs", []);
    ("make_cases_exhaustive", []);
    (* merge funcls before adding the measure argument so that it doesn't
       disappear into an internal pattern match *)
    ("merge_function_clauses", []);
    ("recheck_defs", []);
    ("rewrite_explicit_measure", []);
    ("rewrite_loops_with_escape_effect", []);
    ("recheck_defs", []);
    ("remove_blocks", []);
    ("attach_effects", []);
    ("letbind_effects", []);
    ("remove_e_assign", []);
    ("attach_effects", []);
    ("internal_lets", []);
    ("remove_superfluous_letbinds", []);
    ("remove_superfluous_returns", []);
    ("bit_lists_to_lits", []);
    ("toplevel_let_patterns", []);
    ("recheck_defs", []);
    ("attach_effects", []);
  ]

let generated_line f = Printf.sprintf "Generated by Sail from %s." f

let output_coq opt_dir filename alt_modules alt_modules2 libs env effect_info ast =
  let generated_line = generated_line filename in
  let types_module = filename ^ "_types" in
  let concurrency_monad_params = Monad_params.find_monad_parameters env in
  let base_imports_default =
    if Option.is_some concurrency_monad_params then
      [
        "SailStdpp.Base";
        "SailStdpp.Real";
        "SailStdpp.ConcurrencyInterfaceTypes";
        "SailStdpp.ConcurrencyInterface";
        "SailStdpp.ConcurrencyInterfaceBuiltins";
      ]
    else ["Sail.Base"; "Sail.Real"]
  in
  let base_imports =
    match alt_modules with
    | [] -> base_imports_default
    | _ -> Str.split (Str.regexp "[ \t]+") (String.concat " " alt_modules)
  in
  let ((ot, _, _, _) as ext_ot) = Util.open_output_with_check_unformatted opt_dir (types_module ^ ".v") in
  let ((o, _, _, _) as ext_o) = Util.open_output_with_check_unformatted opt_dir (filename ^ ".v") in
  (Pretty_print_coq.pp_ast_coq (ot, base_imports)
     (o, base_imports @ (types_module :: libs) @ alt_modules2)
     types_module effect_info env ast concurrency_monad_params generated_line
  )
    (alt_modules2 <> []);
  (* suppress MR and M defns if alt_modules2 present*)
  Util.close_output_with_check ext_ot;
  Util.close_output_with_check ext_o

let output libs files =
  List.iter
    (fun (f, effect_info, env, ast) ->
      let f' = Filename.basename (Filename.remove_extension f) in
      output_coq !opt_coq_output_dir f' !opt_alt_modules_coq !opt_alt_modules2_coq libs env effect_info ast
    )
    files

let coq_target _ _ out_file ast effect_info env =
  let out_file = match out_file with Some f -> f | None -> "out" in
  output !opt_libs_coq [(out_file, effect_info, env, ast)]

let _ = Target.register ~name:"coq" ~options:coq_options ~rewrites:coq_rewrites ~asserts_termination:true coq_target
