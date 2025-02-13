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

open Interactive.State

let opt_lean_output_dir : string option ref = ref None

let opt_lean_force_output : bool ref = ref false

let lean_version : string = "lean4:nightly-2025-02-05"

let lean_options =
  [
    ( Flag.create ~prefix:["lean"] ~arg:"directory" "output_dir",
      Arg.String (fun dir -> opt_lean_output_dir := Some dir),
      "set a custom directory to output generated Lean"
    );
    ( Flag.create ~prefix:["lean"] "force_output",
      Arg.Unit (fun () -> opt_lean_force_output := true),
      "removes the content of the output directory if it is non-empty"
    );
    ( Flag.create ~prefix:["lean"] ~arg:"typename" "extern_type",
      Arg.String Pretty_print_lean.(fun ty -> opt_extern_types := ty :: !opt_extern_types),
      "do not generate a definition for the type"
    );
  ]

(* TODO[javra]: Currently these are the same as the Coq rewrites, we might want to change them. *)
let lean_rewrites =
  let open Rewrites in
  [
    ("move_termination_measures", []);
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
    (* ("remove_numeral_pats", []); *)
    (* ("pattern_literals", [Literal_arg "lem"]); *)
    ("guarded_pats", []);
    (* ("register_ref_writes", rewrite_register_ref_writes); *)
    ("nexp_ids", []);
    ("split", [String_arg "execute"]);
    ("minimise_recursive_functions", []);
    ("remove_bitfield_records", []);
    ("recheck_defs", []);
    (* Put prover regstate generation after removing bitfield records,
       which has to be followed by type checking *)
    (* ("prover_regstate", [Bool_arg false]); *)
    (* ("remove_assert", rewrite_ast_remove_assert); *)
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
    ("infer_effects", [Bool_arg true]);
    ("attach_effects", []);
    ("remove_blocks", []);
    ("attach_effects", []);
    (* ("letbind_effects", []); *)
    ("remove_e_assign", []);
    (* ^^^^ replace loops by dummy function calls *)
    ("attach_effects", []);
    ("internal_lets", []);
    (* ^^^^ transforms var into let *)
    ("remove_superfluous_letbinds", []);
    ("remove_superfluous_returns", []);
    ("bit_lists_to_lits", []);
    ("toplevel_let_patterns", []);
    ("recheck_defs", []);
    ("attach_effects", []);
  ]

type lean_context = {
  out_name : string;
  out_name_camel : string;
  sail_dir : string;
  main_file : out_channel;
  lakefile : out_channel;
}

let start_lean_output (out_name : string) default_sail_dir =
  let base_dir = match !opt_lean_output_dir with Some dir -> dir | None -> "." in
  let project_dir = Filename.concat base_dir out_name in
  if !opt_lean_force_output && Sys.file_exists project_dir && Sys.is_directory project_dir then (
    let _ = Unix.system ("rm -r " ^ Filename.quote project_dir ^ "/*") in
    ()
  )
  else Unix.mkdir project_dir 0o775;
  let gitignore = open_out (Filename.concat project_dir ".gitignore") in
  (* Ignore the `z3_problems` file generated by Sail and the `.lake` directory generated by lake*)
  output_string gitignore "/.lake";
  close_out gitignore;
  let lean_toolchain = open_out (Filename.concat project_dir "lean-toolchain") in
  output_string lean_toolchain ("leanprover/" ^ lean_version);
  close_out lean_toolchain;
  let sail_dir = Reporting.get_sail_dir default_sail_dir in
  let out_name_camel = Libsail.Util.to_upper_camel_case out_name in
  let lean_src_dir = Filename.concat project_dir out_name_camel in
  if not (Sys.file_exists lean_src_dir) then Unix.mkdir lean_src_dir 0o775;
  let _ =
    Unix.system
      ("cp -r " ^ Filename.quote (sail_dir ^ "/src/sail_lean_backend/Sail") ^ " " ^ Filename.quote lean_src_dir)
  in
  let main_file = open_out (Filename.concat project_dir (out_name_camel ^ ".lean")) in
  output_string main_file ("import " ^ out_name_camel ^ ".Sail.Sail\n");
  output_string main_file ("import " ^ out_name_camel ^ ".Sail.BitVec\n\n");
  output_string main_file "open Sail\n\n";
  let lakefile = open_out (Filename.concat project_dir "lakefile.toml") in
  { out_name; out_name_camel; sail_dir; main_file; lakefile }

let close_context ctx =
  close_out ctx.main_file;
  close_out ctx.lakefile

let create_lake_project (ctx : lean_context) executable =
  (* Change the base directory if the option '--lean-output-dir' is set *)
  output_string ctx.lakefile
    ("name = \"" ^ ctx.out_name ^ "\"\ndefaultTargets = [\"" ^ ctx.out_name_camel ^ "\"]\n\n[[lean_lib]]\nname = \""
   ^ ctx.out_name_camel ^ "\""
    );
  if executable then (
    output_string ctx.lakefile "\n\n[[lean_exe]]\n";
    output_string ctx.lakefile "name = \"run\"\n";
    output_string ctx.lakefile ("root = \"" ^ ctx.out_name_camel ^ "\"\n")
  )

let output (out_name : string) env effect_info ast default_sail_dir =
  let ctx = start_lean_output out_name default_sail_dir in
  let executable = Pretty_print_lean.pp_ast_lean env effect_info ast ctx.main_file in
  create_lake_project ctx executable
(* Uncomment for debug output of the Sail code after the rewrite passes *)
(* Pretty_print_sail.output_ast stdout (Type_check.strip_ast ast) *)

let lean_target out_name { default_sail_dir; ctx; ast; effect_info; env; _ } =
  let out_name = match out_name with Some f -> f | None -> "out" in
  output out_name env effect_info ast default_sail_dir

let _ = Target.register ~name:"lean" ~options:lean_options ~rewrites:lean_rewrites ~asserts_termination:true lean_target
