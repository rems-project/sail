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

let opt_ocaml_generators = ref ([] : string list)

let ocaml_options =
  [
    ("-ocaml_nobuild", Arg.Set Ocaml_backend.opt_ocaml_nobuild, " do not build generated OCaml");
    ( "-ocaml_trace",
      Arg.Set Ocaml_backend.opt_trace_ocaml,
      " output an OCaml translated version of the input with tracing instrumentation, implies -ocaml"
    );
    ( "-ocaml_build_dir",
      Arg.String (fun dir -> Ocaml_backend.opt_ocaml_build_dir := dir),
      "<directory> set a custom directory to build generated OCaml"
    );
    ( "-ocaml_coverage",
      Arg.Set Ocaml_backend.opt_ocaml_coverage,
      " build OCaml with bisect_ppx coverage reporting (requires opam packages bisect_ppx-ocamlbuild and bisect_ppx)."
    );
    ( "-ocaml_generators",
      Arg.String (fun s -> opt_ocaml_generators := s :: !opt_ocaml_generators),
      "<types> produce random generators for the given types"
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
    ("instantiate_outcomes", [String_arg "ocaml"]);
    ("realize_mappings", []);
    ("remove_vector_subrange_pats", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("undefined", [Bool_arg false]);
    ("vector_string_pats_to_bit_list", []);
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
    ("simple_types", []);
  ]

let ocaml_target _ default_sail_dir out_file ast effect_info env =
  let out = match out_file with None -> "out" | Some s -> s in
  Ocaml_backend.ocaml_compile default_sail_dir out ast !ocaml_generator_info

let _ =
  Target.register ~name:"ocaml" ~options:ocaml_options
    ~pre_parse_hook:(fun () -> Initial_check.opt_undefined_gen := true)
    ~pre_rewrites_hook:stash_pre_rewrite_info ~rewrites:ocaml_rewrites ocaml_target

let opt_tofrominterp_output_dir : string option ref = ref None

let tofrominterp_options =
  [
    ( "-tofrominterp_lem",
      Arg.Set ToFromInterp_backend.lem_mode,
      " output embedding translation for the Lem backend rather than the OCaml backend, implies -tofrominterp"
    );
    ( "-tofrominterp_mwords",
      Arg.Set ToFromInterp_backend.mword_mode,
      " output embedding translation in machine-word mode rather than bit-list mode, implies -tofrominterp"
    );
    ( "-tofrominterp_output_dir",
      Arg.String (fun dir -> opt_tofrominterp_output_dir := Some dir),
      "<directory> set a custom directory to output embedding translation OCaml"
    );
  ]

let tofrominterp_rewrites =
  let open Rewrites in
  [
    ("instantiate_outcomes", [String_arg "interpreter"]);
    ("realize_mappings", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("undefined", [Bool_arg false]);
    ("tuple_assignments", []);
    ("vector_concat_assignments", []);
    ("simple_assignments", []);
  ]

let tofrominterp_target _ _ out_file ast _ _ =
  let out = match out_file with None -> "out" | Some s -> s in
  ToFromInterp_backend.tofrominterp_output !opt_tofrominterp_output_dir out ast

let _ =
  Target.register ~name:"tofrominterp"
    ~description:"output OCaml functions to translate between shallow embedding and interpreter"
    ~options:tofrominterp_options ~rewrites:tofrominterp_rewrites tofrominterp_target

let marshal_target _ _ out_file ast _ env =
  let out_filename = match out_file with None -> "out" | Some s -> s in
  let f = open_out_bin (out_filename ^ ".defs") in
  let remove_prover (l, tannot) =
    if Type_check.is_empty_tannot tannot then (l, Type_check.empty_tannot)
    else (l, Type_check.replace_env (Type_check.Env.set_prover None (Type_check.env_of_tannot tannot)) tannot)
  in
  Marshal.to_string (Ast_util.map_ast_annot remove_prover ast, Type_check.Env.set_prover None env) [Marshal.Compat_32]
  |> Base64.encode_string |> output_string f;
  close_out f

let _ =
  Target.register ~name:"marshal" ~description:"OCaml-marshal out the rewritten AST to a file"
    ~rewrites:tofrominterp_rewrites marshal_target
