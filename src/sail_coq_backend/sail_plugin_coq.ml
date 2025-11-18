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

open Libsail

open Interactive.State

let opt_coq_output_dir : string option ref = ref None
let opt_libs_coq : string list ref = ref []
let opt_alt_modules_coq : string list ref = ref []
let opt_alt_modules2_coq : string list ref = ref []
let opt_coq_isla : string option ref = ref None

let opt_coq_lib_style : Pretty_print_coq.library_style option ref = ref None
let opt_separate_interface_file = ref false

let make_options prefix hide =
  [
    ( Flag.create ~prefix ~hide ~arg:"directory" "output_dir",
      Arg.String (fun dir -> opt_coq_output_dir := Some dir),
      "set a custom directory to output generated Rocq"
    );
    ( Flag.create ~prefix ~hide ~arg:"filename" "lib",
      Arg.String (fun l -> opt_libs_coq := l :: !opt_libs_coq),
      "provide additional library to open in Rocq output"
    );
    ( Flag.create ~prefix ~hide ~arg:"filename" "alt_modules",
      Arg.String (fun l -> opt_alt_modules_coq := l :: !opt_alt_modules_coq),
      "provide alternative modules to open in Rocq output"
    );
    ( Flag.create ~prefix ~hide ~arg:"filename" "alt_modules2",
      Arg.String (fun l -> opt_alt_modules2_coq := l :: !opt_alt_modules2_coq),
      "provide additional alternative modules to open only in main (non-_types) Rocq output, and suppress default \
       definitions of MR and M monads"
    );
    ( Flag.create ~prefix ~hide ~arg:"typename" "extern_type",
      Arg.String Pretty_print_coq.(fun ty -> opt_extern_types := ty :: !opt_extern_types),
      "do not generate a definition for the type"
    );
    ( Flag.create ~prefix ~hide "generate_extern_types",
      Arg.Set Pretty_print_coq.opt_generate_extern_types,
      "generate only extern types rather than suppressing them"
    );
    ( Flag.create ~prefix ~hide ~arg:"filename" "isla",
      Arg.String (fun fname -> opt_coq_isla := Some fname),
      "generate Rocq code for decoding Isla trace values"
    );
    ( Flag.create ~prefix ~hide "record_update",
      Arg.Set Pretty_print_coq.opt_coq_record_update,
      "use coq-record-update package's syntax for record updates"
    );
    ( Flag.create ~prefix ~hide "lib_style",
      Arg.Symbol
        ( ["bbv"; "stdpp"],
          fun s -> opt_coq_lib_style := match s with "bbv" -> Some BBV | "stdpp" -> Some Stdpp | _ -> assert false
        ),
      "select which style of Rocq library to use (default: stdpp when the concurrency interfaces is used, bbv \
       otherwise)"
    );
    ( Flag.create ~prefix ~hide "undef_axioms",
      Arg.Set Pretty_print_coq.opt_undef_axioms,
      "generate axioms for functions that are declared but not defined"
    );
    (* Old debug form of option *)
    (Flag.create ~prefix ~hide:true ~debug:true "undef_axioms", Arg.Set Pretty_print_coq.opt_undef_axioms, "");
    ( Flag.create ~prefix ~hide "minimal_eq_dec",
      Arg.Clear Pretty_print_coq.opt_coq_all_eq_dec,
      " generate decidable equality instances only when necessary"
    );
    ( Flag.create ~prefix ~hide ~arg:"function" ~debug:true "debug_on",
      Arg.String (fun f -> Pretty_print_coq.opt_debug_on := f :: !Pretty_print_coq.opt_debug_on),
      "produce debug messages for Rocq output on given function"
    );
    ( Flag.create ~prefix ~hide "separate_interface_file",
      Arg.Set opt_separate_interface_file,
      "create separate file for concurrency interface definitions"
    );
    ( Flag.create ~prefix ~hide "generic_value",
      Arg.Set Pretty_print_coq.opt_generic_values,
      "generate conversions to a generic value type (requires --rocq-record-update)"
    );
  ]

let rocq_options = make_options ["rocq"] false
let coq_options = make_options ["coq"] true |> List.map (fun (fl, arg, _desc) -> (fl, arg, ""))

let coq_rewrites =
  let open Rewrites in
  [
    ("move_termination_measures", []);
    ("instantiate_outcomes", [String_arg "coq"; Bool_arg true]);
    ("realize_mappings", []);
    ("remove_extern_defs", [String_arg "coq"]);
    ("remove_vector_subrange_pats", []);
    ("remove_duplicate_valspecs", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("add_unspecified_rec", []);
    ("undefined", [Bool_arg true]);
    ("remove_not_pats", []);
    ("remove_impossible_int_cases", []);
    ("tuple_assignments", []);
    ("vector_concat_assignments", []);
    ("simple_assignments", []);
    ("remove_vector_concat", []);
    ("remove_bitvector_pats", []);
    ("remove_numeral_pats", []);
    ("pattern_literals", [Literal_arg "lem"]);
    ("recheck_defs", []);
    ("guarded_pats", []);
    (* ("register_ref_writes", rewrite_register_ref_writes); *)
    ("nexp_ids", []);
    ("split", [String_arg "execute"]);
    ("minimise_recursive_functions", []);
    ("remove_bitfield_records", []);
    ("recheck_defs", []);
    (* ("remove_assert", rewrite_ast_remove_assert); *)
    ("top_sort_defs", []);
    ("add_register_init_function", []);
    ("const_prop_mutrec", [String_arg "coq"]);
    ("exp_lift_assign", []);
    ("early_return", []);
    (* We need to do the exhaustiveness check before merging, because it may
       introduce new wildcard clauses *)
    ("recheck_defs", []);
    ("pattern_exhaustivity_redundancy", []);
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
    ("bit_lists_to_lits", []);
    ("toplevel_let_patterns", []);
    ("recheck_defs", []);
    ("attach_effects", []);
  ]

let generated_line f = Printf.sprintf "Generated by Sail from %s." f

let output_coq opt_dir filename alt_modules alt_modules2 libs symbols ctx env effect_info ast =
  let generated_line = generated_line filename in
  let types_module = filename ^ "_types" in
  let interface_module = filename ^ "_interface" in
  (* NB: this is set up for v1 of the concurrency interface, we use Monad_params.find_instantiations for v2 *)
  let concurrency_monad_params = Monad_params.find_monad_parameters env in
  let library_style = Option.value ~default:Pretty_print_coq.Stdpp !opt_coq_lib_style in
  let base_imports_lib = match library_style with BBV -> "Sail." | Stdpp -> "SailStdpp." in
  let base_imports_default =
    if Preprocess.have_symbol "CONCURRENCY_INTERFACE_V2" symbols then
      ["Base"; "Real"; "ConcurrencyInterfaceTypesV2"; "ConcurrencyInterfaceV2"; "ConcurrencyInterfaceBuiltinsV2"]
    else if Option.is_some concurrency_monad_params then
      ["Base"; "Real"; "ConcurrencyInterfaceTypes"; "ConcurrencyInterface"; "ConcurrencyInterfaceBuiltins"]
    else ["Base"; "Real"]
  in
  let base_imports_default =
    if !Pretty_print_coq.opt_generic_values then base_imports_default @ ["GenericValue"] else base_imports_default
  in
  let base_imports_default = List.map (( ^ ) base_imports_lib) base_imports_default in
  let base_imports =
    match alt_modules with
    | [] -> base_imports_default
    | _ -> Str.split (Str.regexp "[ \t]+") (String.concat " " alt_modules)
  in
  let types_file_info = Util.open_output_with_check ?directory:opt_dir (types_module ^ ".v") in
  let interface_file_info =
    if !opt_separate_interface_file then Some (Util.open_output_with_check ?directory:opt_dir (interface_module ^ ".v"))
    else None
  in
  let types_imports = if !opt_separate_interface_file then base_imports @ [interface_module] else base_imports in
  let main_imports =
    if !opt_separate_interface_file then base_imports @ (interface_module :: types_module :: libs)
    else base_imports @ (types_module :: libs)
  in
  let file_info = Util.open_output_with_check ?directory:opt_dir (filename ^ ".v") in
  let isla_channel_opt, isla_file_info_opt =
    match !opt_coq_isla with
    | None -> (None, None)
    | Some fname ->
        let file_info = Util.open_output_with_check ?directory:opt_dir (fname ^ ".v") in
        (Some file_info.channel, Some file_info)
  in
  (Pretty_print_coq.pp_ast_coq library_style
     (types_file_info.channel, types_imports)
     (Option.map (fun (x : Util.checked_output) -> x.channel) interface_file_info, base_imports)
     (file_info.channel, main_imports @ alt_modules2)
     types_module isla_channel_opt symbols ctx effect_info env ast concurrency_monad_params generated_line
  )
    (alt_modules2 <> []);
  (* suppress MR and M defns if alt_modules2 present*)
  Util.close_output_with_check types_file_info;
  Option.iter Util.close_output_with_check interface_file_info;
  Util.close_output_with_check file_info;
  Option.iter (fun f -> Util.close_output_with_check f) isla_file_info_opt

let output libs files =
  List.iter
    (fun (f, symbols, ctx, effect_info, env, ast) ->
      let f' = Filename.basename (Filename.remove_extension f) in
      output_coq !opt_coq_output_dir f' !opt_alt_modules_coq !opt_alt_modules2_coq libs symbols ctx env effect_info ast
    )
    files

let check_flags () =
  if !Pretty_print_coq.opt_generic_values && not !Pretty_print_coq.opt_coq_record_update then
    raise (Reporting.err_general Parse_ast.Unknown "--rocq-generic-value requires --rocq-record-update");
  if !State.opt_type_grouped_regstate then (
    Reporting.simple_warn Version.v0_20_2 "-grouped-regstate option not supported in the Rocq back-end, ignoring";
    State.opt_type_grouped_regstate := false
  )

let coq_target out_file { symbols; ctx; ast; effect_info; env; _ } =
  let out_file = match out_file with Some f -> f | None -> "out" in
  output !opt_libs_coq [(out_file, symbols, ctx, effect_info, env, ast)]

let _ =
  ignore
    (Target.register ~name:"rocq" ~options:rocq_options ~pre_parse_hook:check_flags ~rewrites:coq_rewrites
       ~asserts_termination:true coq_target
    );
  ignore
    (Target.register ~name:"coq" ~options:coq_options ~pre_parse_hook:check_flags ~rewrites:coq_rewrites
       ~asserts_termination:true coq_target
    )
