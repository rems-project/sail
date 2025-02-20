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

let opt_branch_coverage = ref None
let opt_build = ref false
let opt_generate_header = ref false
let opt_includes_c : string list ref = ref []
let opt_includes_h : string list ref = ref []
let opt_no_lib = ref false
let opt_no_main = ref false
let opt_no_mangle = ref false
let opt_no_rts = ref false
let opt_specialize_c = ref false

let c_options =
  [
    (Flag.create ~prefix:["c"] "build", Arg.Set opt_build, "build the generated C output automatically");
    ( Flag.create ~prefix:["c"] ~arg:"filename" "include",
      Arg.String (fun i -> opt_includes_c := i :: !opt_includes_c),
      "provide additional include for C output"
    );
    ( Flag.create ~prefix:["c"] ~arg:"filename" "header_include",
      Arg.String (fun i -> opt_includes_c := i :: !opt_includes_h),
      "provide additional include for C header output"
    );
    (Flag.create ~prefix:["c"] "no_mangle", Arg.Set opt_no_mangle, "produce readable names");
    (Flag.create ~prefix:["c"] "no_main", Arg.Set opt_no_main, "do not generate the main() function");
    (Flag.create ~prefix:["c"] "no_rts", Arg.Set opt_no_rts, "do not include the Sail runtime");
    ( Flag.create ~prefix:["c"] "no_lib",
      Arg.Tuple [Arg.Set opt_no_lib; Arg.Set opt_no_rts],
      "do not include the Sail runtime or library"
    );
    ( Flag.create ~prefix:["c"] ~arg:"prefix" "prefix",
      Arg.String (fun prefix -> C_backend.opt_prefix := prefix),
      "prefix generated C functions"
    );
    (Flag.create ~prefix:["c"] "generate_header", Arg.Set opt_generate_header, "generate a separate header file");
    ( Flag.create ~prefix:["c"] ~arg:"parameters" "extra_params",
      Arg.String (fun params -> C_backend.opt_extra_params := Some params),
      "generate C functions with additional parameters"
    );
    ( Flag.create ~prefix:["c"] ~arg:"arguments" "extra_args",
      Arg.String (fun args -> C_backend.opt_extra_arguments := Some args),
      "supply extra argument to every generated C function call"
    );
    (Flag.create ~prefix:["c"] "specialize", Arg.Set opt_specialize_c, "specialize integer arguments in C output");
    ( Flag.create ~prefix:["c"] "preserve",
      Arg.String (fun str -> Specialize.add_initial_calls (Ast_util.IdSet.singleton (Ast_util.mk_id str))),
      "make sure the provided function identifier is preserved in C output"
    );
    ( Flag.create ~prefix:["c"] "fold_unit",
      Arg.String (fun str -> Constant_fold.opt_fold_to_unit := Util.split_on_char ',' str),
      "remove comma separated list of functions from C output, replacing them with unit"
    );
    ( Flag.create ~prefix:["c"] ~arg:"file" "coverage",
      Arg.String (fun str -> opt_branch_coverage := Some (open_out str)),
      "Turn on coverage tracking and output information about all branches and functions to a file"
    );
    ( Flag.create ~prefix:["c"] ~hide_prefix:true "O",
      Arg.Tuple
        [
          Arg.Set C_backend.optimize_primops;
          Arg.Set C_backend.optimize_hoist_allocations;
          Arg.Set Initial_check.opt_fast_undefined;
          Arg.Set C_backend.optimize_alias;
        ],
      "turn on optimizations for C compilation"
    );
    ( Flag.create ~prefix:["c"] ~hide_prefix:true "Ofixed_int",
      Arg.Set C_backend.optimize_fixed_int,
      "assume fixed size integers rather than GMP arbitrary precision integers"
    );
    ( Flag.create ~prefix:["c"] ~hide_prefix:true "Ofixed_bits",
      Arg.Set C_backend.optimize_fixed_bits,
      "assume fixed size bitvectors rather than arbitrary precision bitvectors"
    );
    ( Flag.create ~prefix:["c"] ~hide_prefix:true "static",
      Arg.Set C_backend.opt_static,
      "make generated C functions static"
    );
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

let collect_c_name_info ast =
  let open Ast in
  let open Ast_defs in
  let reserved = ref Util.StringSet.empty in
  let overrides = ref Name_generator.Overrides.empty in
  List.iter
    (function
      | DEF_aux (DEF_val (VS_aux (VS_val_spec (_, _, extern), _)), _) -> (
          match Ast_util.extern_assoc "c" extern with
          | Some name -> reserved := Util.StringSet.add name !reserved
          | None -> ()
        )
      | DEF_aux (DEF_pragma ("c_reserved", Pragma_line (name, _)), _) -> reserved := Util.StringSet.add name !reserved
      | DEF_aux (DEF_pragma ("c_override", Pragma_structured data), def_annot) -> (
          match Name_generator.parse_override data with
          | Some (from, target) -> overrides := Name_generator.Overrides.add from target !overrides
          | None -> raise (Reporting.err_general def_annot.loc "Failed to interpret $c_override directive")
        )
      | _ -> ()
      )
    ast.defs;
  (!reserved, !overrides)

let c_target out_file { ast; effect_info; env; default_sail_dir; _ } =
  let reserveds, overrides = collect_c_name_info ast in

  let module Codegen = C_backend.Codegen (struct
    let generate_header = !opt_generate_header
    let includes = !opt_includes_c
    let header_includes = !opt_includes_h
    let no_main = !opt_no_main
    let no_lib = !opt_no_lib
    let no_rts = !opt_no_rts
    let no_mangle = !opt_no_mangle
    let reserved_words = reserveds
    let overrides = overrides
    let branch_coverage = !opt_branch_coverage
  end) in
  Reporting.opt_warnings := true;
  let echo_output, basename = match out_file with Some f -> (false, f) | None -> (true, "out") in

  let header_opt, impl = Codegen.compile_ast env effect_info basename ast in

  let impl_out = Util.open_output_with_check (basename ^ ".c") in
  output_string impl_out.channel impl;
  flush impl_out.channel;
  Util.close_output_with_check impl_out;

  ( match header_opt with
  | None -> ()
  | Some header ->
      let header_out = Util.open_output_with_check (basename ^ ".h") in
      output_string header_out.channel header;
      flush header_out.channel;
      Util.close_output_with_check header_out
  );

  if echo_output then (
    Reporting.warn "Deprecated" Parse_ast.Unknown
      "The default behaviour of printing C output to stdout when no output file is specified is deprecated. use the -o \
       option to specify a file name";
    output_string stdout impl;
    flush stdout
  );

  if !opt_build then (
    let sail_dir = Reporting.get_sail_dir default_sail_dir in
    let cmd = Printf.sprintf "%s -lgmp -I '%s'/lib '%s'/lib/*.c %s.c -o %s" "gcc" sail_dir sail_dir basename basename in
    let _ = Unix.system cmd in
    ()
  )

let _ =
  Pragma.register "c_in_main";
  Pragma.register "c_reserved";
  Pragma.register "c_override";
  Target.register ~name:"c" ~options:c_options ~rewrites:c_rewrites ~supports_abstract_types:true c_target
