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

open Ast_defs
open PPrint

let opt_libs_lem : string list ref = ref []
let opt_lem_output_dir : string option ref = ref None
let opt_isa_output_dir : string option ref = ref None

let lem_options =
  [
    ( "-lem_output_dir",
      Arg.String (fun dir -> opt_lem_output_dir := Some dir),
      "<directory> set a custom directory to output generated Lem"
    );
    ( "-isa_output_dir",
      Arg.String (fun dir -> opt_isa_output_dir := Some dir),
      "<directory> set a custom directory to output generated Isabelle auxiliary theories"
    );
    ( "-lem_lib",
      Arg.String (fun l -> opt_libs_lem := l :: !opt_libs_lem),
      "<filename> provide additional library to open in Lem output"
    );
    ("-lem_sequential", Arg.Set Pretty_print_lem.opt_sequential, " use sequential state monad for Lem output");
    ("-lem_mwords", Arg.Set Monomorphise.opt_mwords, " use native machine word library for Lem output");
    ( "-lem_extern_type",
      Arg.String Pretty_print_lem.(fun ty -> opt_extern_types := ty :: !opt_extern_types),
      "<typename> do not generate a definition for the type"
    );
  ]

let lem_rewrites =
  let open Rewrites in
  [
    ("prover_regstate", [Flag_arg Monomorphise.opt_mwords]);
    ("instantiate_outcomes", [String_arg "lem"]);
    ("realize_mappings", []);
    ("remove_vector_subrange_pats", []);
    ("remove_duplicate_valspecs", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("mono_rewrites", [If_flag opt_mono_rewrites]);
    ("recheck_defs", [If_flag opt_mono_rewrites]);
    ("undefined", [Bool_arg false]);
    ("toplevel_consts", [String_arg "lem"; If_mwords_arg]);
    ("complete_record_params", [If_mono_arg]);
    ("toplevel_nexps", [If_mono_arg]);
    ("monomorphise", [String_arg "lem"; If_mono_arg]);
    ("recheck_defs", [If_mwords_arg]);
    ("add_bitvector_casts", [If_mwords_arg]);
    ("atoms_to_singletons", [String_arg "lem"; If_mono_arg]);
    ("recheck_defs", [If_mwords_arg]);
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
    ("recheck_defs", []);
    ("top_sort_defs", []);
    ("const_prop_mutrec", [String_arg "lem"]);
    ("vector_string_pats_to_bit_list", []);
    ("exp_lift_assign", []);
    ("early_return", []);
    (* early_return currently breaks the types *)
    ("recheck_defs", []);
    ("remove_blocks", []);
    ("attach_effects", []);
    ("letbind_effects", []);
    ("remove_e_assign", []);
    ("attach_effects", []);
    ("internal_lets", []);
    ("remove_superfluous_letbinds", []);
    ("remove_superfluous_returns", []);
    ("merge_function_clauses", []);
    ("bit_lists_to_lits", []);
    ("recheck_defs", []);
    ("attach_effects", []);
  ]

let generated_line f = Printf.sprintf "Generated by Sail from %s." f

let output_lem filename libs effect_info type_env ast =
  let generated_line = generated_line filename in
  (* let seq_suffix = if !Pretty_print_lem.opt_sequential then "_sequential" else "" in *)
  let types_module = filename ^ "_types" in
  let concurrency_monad_params = Monad_params.find_monad_parameters type_env in
  let monad_modules, monad_undefined_gen =
    if Option.is_some concurrency_monad_params then
      (["Sail2_concurrency_interface"; "Sail2_monadic_combinators"], ["Sail2_undefined_concurrency_interface"])
    else (["Sail2_prompt_monad"; "Sail2_prompt"], ["Sail2_undefined"])
  in
  let undefined_modules = if !Initial_check.opt_undefined_gen then monad_undefined_gen else [] in
  let operators_module = if !Monomorphise.opt_mwords then "Sail2_operators_mwords" else "Sail2_operators_bitlists" in
  (* let libs = List.map (fun lib -> lib ^ seq_suffix) libs in *)
  let base_imports =
    ["Pervasives_extra"; "Sail2_instr_kinds"; "Sail2_values"; "Sail2_string"; operators_module]
    @ monad_modules @ undefined_modules
  in
  let isa_thy_name = String.capitalize_ascii filename ^ "_lemmas" in
  let isa_lemmas =
    separate hardline
      [
        string ("theory " ^ isa_thy_name);
        string "  imports";
        string "    Sail.Sail2_values_lemmas";
        string "    Sail.Sail2_state_lemmas";
        string ("    " ^ String.capitalize_ascii filename);
        string "begin";
        string "";
        State.generate_isa_lemmas type_env ast.defs;
        string "";
        string "end";
      ]
    ^^ hardline
  in
  let ((ot, _, _, _) as ext_ot) =
    Util.open_output_with_check_unformatted !opt_lem_output_dir (filename ^ "_types" ^ ".lem")
  in
  let ((o, _, _, _) as ext_o) = Util.open_output_with_check_unformatted !opt_lem_output_dir (filename ^ ".lem") in
  Pretty_print_lem.pp_ast_lem (ot, base_imports)
    (o, base_imports @ (String.capitalize_ascii types_module :: libs))
    effect_info type_env ast concurrency_monad_params generated_line;
  Util.close_output_with_check ext_ot;
  Util.close_output_with_check ext_o;
  let ((ol, _, _, _) as ext_ol) = Util.open_output_with_check_unformatted !opt_isa_output_dir (isa_thy_name ^ ".thy") in
  Pretty_print_common.print ol isa_lemmas;
  Util.close_output_with_check ext_ol

let output libs files =
  List.iter
    (fun (f, effect_info, env, ast) ->
      let f' = Filename.basename (Filename.remove_extension f) in
      output_lem f' libs effect_info env ast
    )
    files

let lem_target _ _ out_file ast effect_info env =
  let out_file = match out_file with Some f -> f | None -> "out" in
  output !opt_libs_lem [(out_file, effect_info, env, ast)]

let _ = Target.register ~name:"lem" ~options:lem_options ~rewrites:lem_rewrites lem_target

(* The code below and in gen_lem_monad.ml was used to generate a first version
   of the monad for the new concurrency interface, but that has since been
   edited manually *)
(*
let lem_monad_target _ out_file ast effect_info env =
  Gen_lem_monad.output_lem_monad effect_info env ast

let _ =
  Target.register
    ~name:"lem_monad"
    ~options:lem_options
    ~rewrites:[]
    lem_monad_target
 *)
