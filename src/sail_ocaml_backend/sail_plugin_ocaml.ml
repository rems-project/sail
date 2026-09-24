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

let opt_ocaml_generators = ref ([] : string list)

let ocaml_options =
  [
    (Flag.create ~prefix:["ocaml"] "nobuild", Arg.Set Ocaml_backend.opt_ocaml_nobuild, "do not build generated OCaml");
    ( Flag.create ~prefix:["ocaml"] "trace",
      Arg.Set Ocaml_backend.opt_trace_ocaml,
      "output an OCaml translated version of the input with tracing instrumentation, implies -ocaml"
    );
    ( Flag.create ~prefix:["ocaml"] ~arg:"directory" "build_dir",
      Arg.String (fun dir -> Ocaml_backend.opt_ocaml_build_dir := dir),
      "set a custom directory to build generated OCaml"
    );
    ( Flag.create ~prefix:["ocaml"] ~arg:"types" "generators",
      Arg.String (fun s -> opt_ocaml_generators := s :: !opt_ocaml_generators),
      "produce random generators for the given types"
    );
  ]

let ocaml_generator_info : (Type_check.tannot Ast.type_def list * string list) option ref = ref None

let stash_pre_rewrite_info (ast : _ Ast_defs.ast) _ type_envs =
  ocaml_generator_info :=
    match !opt_ocaml_generators with
    | [] -> None
    | _ -> Some (Ocaml_backend.orig_types_for_ocaml_generator ast.defs, !opt_ocaml_generators)

let ocaml_rewrites =
  let open Rewrites in
  [
    ("instantiate_outcomes", [String_arg "ocaml"; Bool_arg false]);
    ("realize_mappings", []);
    ("remove_vector_subrange_pats", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("undefined", [Bool_arg false]);
    ("tuple_assignments", []);
    ("vector_concat_assignments", []);
    ("simple_assignments", []);
    ("remove_not_pats", []);
    ("remove_vector_concat", []);
    ("remove_bitvector_pats", []);
    ("pattern_literals", [Literal_arg "ocaml"]);
    ("remove_numeral_pats", []);
    ("exp_lift_assign", []);
    ("top_sort_defs", []);
    ("recheck_defs", []);
    ("simple_types", []);
  ]

let ocaml_target out_file { default_sail_dir; ast; effect_info; env; _ } =
  let out = match out_file with None -> "out" | Some s -> s in
  Ocaml_backend.ocaml_compile default_sail_dir out ast !ocaml_generator_info

let _ =
  Target.register ~name:"ocaml" ~options:ocaml_options ~pre_rewrites_hook:stash_pre_rewrite_info
    ~rewrites:ocaml_rewrites ocaml_target
