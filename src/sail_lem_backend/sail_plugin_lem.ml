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
open Interactive.State

let opt_libs_lem : string list ref = ref []
let opt_lem_output_dir : string option ref = ref None
let opt_isa_output_dir : string option ref = ref None
let opt_lem_split_files : bool ref = ref false

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
    ("-lem_split_files", Arg.Set opt_lem_split_files, " split output into multiple files, one per input file");
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
    ("remove_bitfield_records", []);
    ("recheck_defs", []);
    (* Put prover regstate generation after removing bitfield records,
       which has to be followed by type checking *)
    ("prover_regstate", [Flag_arg Monomorphise.opt_mwords]);
    ("move_termination_measures", []);
    ("top_sort_defs", []);
    ("const_prop_mutrec", [String_arg "lem"]);
    ("vector_string_pats_to_bit_list", []);
    ("exp_lift_assign", []);
    ("early_return", []);
    (* early_return currently breaks the types *)
    ("recheck_defs", []);
    (* merge funcls before adding the measure argument so that it doesn't
       disappear into an internal pattern match *)
    ("merge_function_clauses", []);
    ("recheck_defs", []);
    ("rewrite_explicit_measure", []);
    ("rewrite_loops_with_escape_effect", []);
    ("recheck_defs", []);
    ("infer_effects", [Bool_arg true]);
    ("attach_effects", []);
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

let write_doc dir filename doc =
  let ((chan, _, _, _) as o) = Util.open_output_with_check_unformatted dir filename in
  Pretty_print_common.print chan doc;
  Util.close_output_with_check o

let lem_target out_file { ctx; ast; effect_info; env = type_env; _ } =
  let out_filename = match out_file with Some f -> f | None -> "out" in
  let concurrency_monad_params = Monad_params.find_monad_parameters type_env in
  let monad_modules =
    if Option.is_some concurrency_monad_params then
      ["Sail2_concurrency_interface"; "Sail2_monadic_combinators"; "Sail2_undefined_concurrency_interface"]
    else ["Sail2_prompt_monad"; "Sail2_prompt"; "Sail2_undefined"]
  in
  let operators_module = if !Monomorphise.opt_mwords then "Sail2_operators_mwords" else "Sail2_operators_bitlists" in
  let base_imports =
    ["Pervasives_extra"; "Sail2_instr_kinds"; "Sail2_values"; "Sail2_string"; operators_module] @ monad_modules
  in
  let isa_thy_name = String.capitalize_ascii out_filename ^ "_lemmas" in
  let isa_lemmas =
    separate hardline
      [
        string ("theory " ^ isa_thy_name);
        string "  imports";
        string ("    " ^ String.capitalize_ascii out_filename);
        string "    Sail.Sail2_values_lemmas";
        ( if Option.is_some concurrency_monad_params then string "    Sail.Sail2_concurrency_interface_lemmas"
          else string "    Sail.Sail2_state_lemmas"
        );
        string "    Sail.Add_Cancel_Distinct";
        string "begin";
        string "";
        State.generate_isa_lemmas type_env ast.defs;
        string "";
        string "end";
      ]
    ^^ hardline
  in
  let lem_files =
    Pretty_print_lem.doc_ast_lem out_filename !opt_lem_split_files base_imports !opt_libs_lem ctx effect_info type_env
      ast
  in
  write_doc !opt_isa_output_dir (isa_thy_name ^ ".thy") isa_lemmas;
  List.iter (fun (filename, doc) -> write_doc !opt_lem_output_dir filename doc) lem_files

let _ = Target.register ~name:"lem" ~options:lem_options ~rewrites:lem_rewrites ~asserts_termination:true lem_target

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
