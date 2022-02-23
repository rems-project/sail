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

open Process_file

module Big_int = Nat_big_num
module Json = Yojson.Basic

let lib = ref ([] : string list)
let opt_interactive_script : string option ref = ref None
(* Note: May cause a deprecated warning for json type, but this cannot be
   fixed without breaking Ubuntu 18.04 CI *)
let opt_config : Json.t option ref = ref None
let opt_print_version = ref false
let opt_target = ref None
let opt_tofrominterp_output_dir : string option ref = ref None
let opt_sanity = ref false
let opt_includes_c = ref ([]:string list)
let opt_specialize_c = ref false
let opt_smt_serialize = ref false
let opt_libs_lem = ref ([]:string list)
let opt_libs_coq = ref ([]:string list)
let opt_file_arguments = ref ([]:string list)
let opt_process_elf : string option ref = ref None
let opt_ocaml_generators = ref ([]:string list)
let opt_splice = ref ([]:string list)
let opt_have_feature = ref None
let opt_infer_effects = ref false

let set_target name = Arg.Unit (fun _ -> opt_target := Some name)

let load_json_config file =
  try Json.from_file file with
  | Yojson.Json_error desc | Sys_error desc ->
     prerr_endline "Error when loading configuration file:";
     prerr_endline desc;
     exit 1
 
let options = Arg.align ([
  ( "-o",
    Arg.String (fun f -> opt_file_out := Some f),
    "<prefix> select output filename prefix");
  ( "-i",
    Arg.Tuple [Arg.Set Interactive.opt_interactive;
               Arg.Set Interactive.opt_auto_interpreter_rewrites;
               Arg.Set Initial_check.opt_undefined_gen],
    " start interactive interpreter");
  ( "-is",
    Arg.Tuple [Arg.Set Interactive.opt_interactive;
               Arg.Set Interactive.opt_auto_interpreter_rewrites;
               Arg.Set Initial_check.opt_undefined_gen;
               Arg.String (fun s -> opt_interactive_script := Some s)],
    "<filename> start interactive interpreter and execute commands in script");
  ( "-iout",
    Arg.String (fun file -> Value.output_redirect (open_out file)),
    "<filename> print interpreter output to file");
  ( "-interact_custom",
    Arg.Set Interactive.opt_interactive,
    " drop to an interactive session after running Sail. Differs from \
     -i in that it does not set up the interpreter in the interactive \
     shell.");
  ( "-emacs",
    Arg.Set Interactive.opt_emacs_mode,
    " run sail interactively as an emacs mode child process");
  ( "-no_warn",
    Arg.Clear Reporting.opt_warnings,
    " do not print warnings");
  ( "-config",
    Arg.String (fun file -> opt_config := Some (load_json_config file)),
    " JSON configuration file");
  ( "-tofrominterp",
    set_target "tofrominterp",
    " output OCaml functions to translate between shallow embedding and interpreter");
  ( "-tofrominterp_lem",
    Arg.Tuple [set_target "tofrominterp"; Arg.Set ToFromInterp_backend.lem_mode],
    " output embedding translation for the Lem backend rather than the OCaml backend, implies -tofrominterp");
  ( "-tofrominterp_mwords",
    Arg.Tuple [set_target "tofrominterp"; Arg.Set ToFromInterp_backend.mword_mode],
    " output embedding translation in machine-word mode rather than bit-list mode, implies -tofrominterp");
  ( "-tofrominterp_output_dir",
    Arg.String (fun dir -> opt_tofrominterp_output_dir := Some dir),
    " set a custom directory to output embedding translation OCaml");
  ( "-ocaml",
    Arg.Tuple [set_target "ocaml"; Arg.Set Initial_check.opt_undefined_gen],
    " output an OCaml translated version of the input");
  ( "-ocaml-nobuild",
    Arg.Set Ocaml_backend.opt_ocaml_nobuild,
    "");
  ( "-ocaml_nobuild",
    Arg.Set Ocaml_backend.opt_ocaml_nobuild,
    " do not build generated OCaml");
  ( "-ocaml_trace",
    Arg.Tuple [set_target "ocaml"; Arg.Set Initial_check.opt_undefined_gen; Arg.Set Ocaml_backend.opt_trace_ocaml],
    " output an OCaml translated version of the input with tracing instrumentation, implies -ocaml");
  ( "-ocaml_build_dir",
    Arg.String (fun dir -> Ocaml_backend.opt_ocaml_build_dir := dir),
    " set a custom directory to build generated OCaml");
  ( "-ocaml-coverage",
    Arg.Set Ocaml_backend.opt_ocaml_coverage,
    "");
  ( "-ocaml_coverage",
    Arg.Set Ocaml_backend.opt_ocaml_coverage,
    " build OCaml with bisect_ppx coverage reporting (requires opam packages bisect_ppx-ocamlbuild and bisect_ppx).");
  ( "-ocaml_generators",
    Arg.String (fun s -> opt_ocaml_generators := s::!opt_ocaml_generators),
    "<types> produce random generators for the given types");
  ( "-smt_solver",
    Arg.String (fun s -> Constraint.set_solver (String.trim s)),
    "<solver> choose SMT solver. Supported solvers are z3 (default), alt-ergo, cvc4, mathsat, vampire and yices.");
  ( "-smt_linearize",
    Arg.Set Type_check.opt_smt_linearize,
    "(experimental) force linearization for constraints involving exponentials");
  ( "-latex",
    Arg.Tuple [set_target "latex"; Arg.Clear Type_check.opt_expand_valspec; Arg.Set Type_check.opt_no_bitfield_expansion],
    " pretty print the input to LaTeX");
  ( "-latex_prefix",
    Arg.String (fun prefix -> Latex.opt_prefix := prefix),
    "<prefix> set a custom prefix for generated LaTeX labels and macro commands (default sail)");
  ( "-latex_full_valspecs",
    Arg.Clear Latex.opt_simple_val,
    " print full valspecs in LaTeX output");
  ( "-latex_abbrevs",
    Arg.String (fun s ->
      let abbrevs = String.split_on_char ';' s in
      let filtered = List.filter (fun abbrev -> not (String.equal "" abbrev)) abbrevs in
      match List.find_opt (fun abbrev -> not (String.equal "." (String.sub abbrev (String.length abbrev - 1) 1))) filtered with
      | None -> Latex.opt_abbrevs := filtered
      | Some abbrev -> raise (Arg.Bad (abbrev ^ " does not end in a '.'"))),
    " semicolon-separated list of abbreviations to fix spacing for in LaTeX output (default 'e.g.;i.e.')");
  ( "-marshal",
    Arg.Tuple [set_target "marshal"; Arg.Set Initial_check.opt_undefined_gen],
    " OCaml-marshal out the rewritten AST to a file");
  ( "-ir",
    set_target "ir",
    " print intermediate representation");
  ( "-smt",
    Arg.Tuple [set_target "smt"],
    " print SMT translated version of input");
  ( "-smt_auto",
    Arg.Tuple [set_target "smt"; Arg.Set Jib_smt.opt_auto],
    " generate SMT and automatically call the solver (implies -smt)");
  ( "-smt_ignore_overflow",
    Arg.Set Jib_smt.opt_ignore_overflow,
    " ignore integer overflow in generated SMT");
  ( "-smt_propagate_vars",
    Arg.Set Jib_smt.opt_propagate_vars,
    " propgate variables through generated SMT");
  ( "-smt_int_size",
    Arg.String (fun n -> Jib_smt.opt_default_lint_size := int_of_string n),
    "<n> set a bound of n on the maximum integer bitwidth for generated SMT (default 128)");
  ( "-smt_bits_size",
    Arg.String (fun n -> Jib_smt.opt_default_lbits_index := int_of_string n),
    "<n> set a bound of 2 ^ n for bitvector bitwidth in generated SMT (default 8)");
  ( "-smt_vector_size",
    Arg.String (fun n -> Jib_smt.opt_default_vector_index := int_of_string n),
    "<n> set a bound of 2 ^ n for generic vectors in generated SMT (default 5)");
  ( "-smt_serialize",
    Arg.Tuple [set_target "smt"; Arg.Set opt_smt_serialize],
    " compile Sail to IR suitable for sail-axiomatic tool");
  ( "-c",
    Arg.Tuple [set_target "c"; Arg.Set Initial_check.opt_undefined_gen],
    " output a C translated version of the input");
  ( "-c2",
    Arg.Tuple [set_target "c2"; Arg.Set Initial_check.opt_undefined_gen],
    " output a C translated version of the input (experimental code-generation)");
  ( "-c_include",
    Arg.String (fun i -> opt_includes_c := i::!opt_includes_c),
    "<filename> provide additional include for C output");
  ( "-c_no_main",
    Arg.Set C_backend.opt_no_main,
    " do not generate the main() function" );
  ( "-c_no_rts",
    Arg.Set C_backend.opt_no_rts,
    " do not include the Sail runtime" );
  ( "-c_no_lib",
    Arg.Tuple [Arg.Set C_backend.opt_no_lib; Arg.Set C_backend.opt_no_rts],
    " do not include the Sail runtime or library" );
  ( "-c_prefix",
    Arg.String (fun prefix -> C_backend.opt_prefix := prefix),
    "<prefix> prefix generated C functions" );
  ( "-c_extra_params",
    Arg.String (fun params -> C_backend.opt_extra_params := Some params),
    "<parameters> generate C functions with additional parameters" );
  ( "-c_extra_args",
    Arg.String (fun args -> C_backend.opt_extra_arguments := Some args),
    "<arguments> supply extra argument to every generated C function call" );
  ( "-c_specialize",
    Arg.Set opt_specialize_c,
    " specialize integer arguments in C output");
  ( "-c_preserve",
    Arg.String (fun str -> Specialize.add_initial_calls (Ast_util.IdSet.singleton (Ast_util.mk_id str))),
    " make sure the provided function identifier is preserved in C output");
  ( "-c_fold_unit",
    Arg.String (fun str -> Constant_fold.opt_fold_to_unit := Util.split_on_char ',' str),
    " remove comma separated list of functions from C output, replacing them with unit");
  ( "-c_coverage",
    Arg.String (fun str -> C_backend.opt_branch_coverage := Some (open_out str)),
    "<file> Turn on coverage tracking and output information about all branches and functions to a file");
  ( "-elf",
    Arg.String (fun elf -> opt_process_elf := Some elf),
    " process an ELF file so that it can be executed by compiled C code");
  ( "-D",
    Arg.String (fun symbol -> Process_file.add_symbol symbol),
    "<symbol> define a symbol for the preprocessor, as $define does in the source code");
  ( "-O",
    Arg.Tuple [Arg.Set C_backend.optimize_primops;
               Arg.Set C_backend.optimize_hoist_allocations;
               Arg.Set Initial_check.opt_fast_undefined;
               Arg.Set C_backend.optimize_struct_updates;
               Arg.Set C_backend.optimize_alias],
    " turn on optimizations for C compilation");
  ( "-Oconstant_fold",
    Arg.Set Constant_fold.optimize_constant_fold,
    " apply constant folding optimizations");
  ( "-Ofixed_int",
    Arg.Set C_backend.optimize_fixed_int,
    " assume fixed size integers rather than GMP arbitrary precision integers");
  ( "-Ofixed_bits",
    Arg.Set C_backend.optimize_fixed_bits,
    " assume fixed size bitvectors rather than arbitrary precision bitvectors");
  ( "-Oaarch64_fast",
    Arg.Set Jib_compile.optimize_aarch64_fast_struct,
    " apply ARMv8.5 specific optimizations (potentially unsound in general)");
  ( "-Ofast_undefined",
    Arg.Set Initial_check.opt_fast_undefined,
    " turn on fast-undefined mode");
  ( "-static",
    Arg.Set C_backend.opt_static,
    " make generated C functions static");
  ( "-trace",
    Arg.Tuple [Arg.Set Ocaml_backend.opt_trace_ocaml],
    " instrument output with tracing");
  ( "-lem",
    set_target "lem",
    " output a Lem translated version of the input");
  ( "-lem_output_dir",
    Arg.String (fun dir -> Process_file.opt_lem_output_dir := Some dir),
    " set a custom directory to output generated Lem");
  ( "-isa_output_dir",
    Arg.String (fun dir -> Process_file.opt_isa_output_dir := Some dir),
    " set a custom directory to output generated Isabelle auxiliary theories");
  ( "-lem_lib",
    Arg.String (fun l -> opt_libs_lem := l::!opt_libs_lem),
    "<filename> provide additional library to open in Lem output");
  ( "-lem_sequential",
    Arg.Set Pretty_print_lem.opt_sequential,
    " use sequential state monad for Lem output");
  ( "-lem_mwords",
    Arg.Set Pretty_print_lem.opt_mwords,
    " use native machine word library for Lem output");
  ( "-coq",
    set_target "coq",
    " output a Coq translated version of the input");
  ( "-coq_output_dir",
    Arg.String (fun dir -> Process_file.opt_coq_output_dir := Some dir),
    " set a custom directory to output generated Coq");
  ( "-coq_lib",
    Arg.String (fun l -> opt_libs_coq := l::!opt_libs_coq),
    "<filename> provide additional library to open in Coq output");
  ( "-coq_alt_modules",
    Arg.String (fun l -> opt_alt_modules_coq := l::!opt_alt_modules_coq),
    "<filename> provide alternative modules to open in Coq output");
  ( "-coq_alt_modules2",
    Arg.String (fun l -> opt_alt_modules2_coq := l::!opt_alt_modules2_coq),
    "<filename> provide additional alternative modules to open only in main (non-_types) Coq output, and suppress default definitions of MR and M monads");
  ( "-dcoq_undef_axioms",
    Arg.Set Pretty_print_coq.opt_undef_axioms,
    " generate axioms for functions that are declared but not defined");
  ( "-dcoq_warn_nonex",
    Arg.Set Rewrites.opt_coq_warn_nonexhaustive,
    " generate warnings for non-exhaustive pattern matches in the Coq backend");
  ( "-dcoq_debug_on",
    Arg.String (fun f -> Pretty_print_coq.opt_debug_on := f::!Pretty_print_coq.opt_debug_on),
    "<function> produce debug messages for Coq output on given function");
  ( "-mono_split",
    Arg.String (fun s ->
      let l = Util.split_on_char ':' s in
      match l with
      | [fname;line;var] ->
         Rewrites.opt_mono_split := ((fname,int_of_string line),var)::!Rewrites.opt_mono_split
      | _ -> raise (Arg.Bad (s ^ " not of form <filename>:<line>:<variable>"))),
      "<filename>:<line>:<variable> to case split for monomorphisation");
  ( "-memo_z3",
    Arg.Set opt_memo_z3,
    " memoize calls to z3, improving performance when typechecking repeatedly");
  ( "-no_memo_z3",
    Arg.Clear opt_memo_z3,
    " do not memoize calls to z3 (default)");
  ( "-memo",
    Arg.Tuple [Arg.Set opt_memo_z3; Arg.Set Jib_compile.opt_memo_cache],
    " memoize calls to z3, and intermediate compilation results");
  ( "-have_feature",
    Arg.String (fun symbol -> opt_have_feature := Some symbol),
    " check if a feature symbol is set by default");
  ( "-splice",
    Arg.String (fun s -> opt_splice := s :: !opt_splice),
    "<filename> add functions from file, replacing existing definitions where necessary");
  ( "-undefined_gen",
    Arg.Set Initial_check.opt_undefined_gen,
    " generate undefined_type functions for types in the specification");
  ( "-grouped_regstate",
    Arg.Set State.opt_type_grouped_regstate,
    " group registers with same type together in generated register state record");
  ( "-enum_casts",
    Arg.Set Initial_check.opt_enum_casts,
    " allow enumerations to be automatically casted to numeric range types");
  ( "-non_lexical_flow",
    Arg.Set Nl_flow.opt_nl_flow,
    " allow non-lexical flow typing");
  ( "-no_lexp_bounds_check",
    Arg.Set Type_check.opt_no_lexp_bounds_check,
    " turn off bounds checking for vector assignments in l-expressions");
  ( "-no_effects",
    Arg.Set Type_check.opt_no_effects,
    " (experimental) turn off effect checking");
  ( "-infer_effects",
    Arg.Set opt_infer_effects,
    " (experimental) infer effects");
  ( "-just_check",
    Arg.Set opt_just_check,
    " (experimental) terminate immediately after typechecking");
  ( "-dmono_analysis",
    Arg.Set_int Rewrites.opt_dmono_analysis,
    " (debug) dump information about monomorphisation analysis: 0 silent, 3 max");
  ( "-auto_mono",
    Arg.Set Rewrites.opt_auto_mono,
    " automatically infer how to monomorphise code");
  ( "-mono_rewrites",
    Arg.Set Rewrites.opt_mono_rewrites,
    " turn on rewrites for combining bitvector operations");
  ( "-dno_complex_nexps_rewrite",
    Arg.Clear Rewrites.opt_mono_complex_nexps,
    " do not move complex size expressions in function signatures into constraints (monomorphisation)");
  ( "-dall_split_errors",
    Arg.Set Rewrites.opt_dall_split_errors,
    " display all case split errors from monomorphisation, rather than one");
  ( "-dmono_continue",
    Arg.Set Rewrites.opt_dmono_continue,
    " continue despite monomorphisation errors");
  ( "-const_prop_mutrec",
    Arg.String (fun name -> Constant_propagation_mutrec.targets := Ast_util.mk_id name :: !Constant_propagation_mutrec.targets),
    " unroll function in a set of mutually recursive functions");
  ( "-verbose",
    Arg.Int (fun verbosity -> Util.opt_verbosity := verbosity),
    " produce verbose output");
  ( "-output_sail",
    set_target "sail",
    " print Sail code after type checking and initial rewriting");
  ( "-reformat",
    Arg.String (fun dir -> opt_reformat := Some dir),
    "<dir> reformat the input Sail code placing output into a separate directory");
  ( "-ddump_initial_ast",
    Arg.Set opt_ddump_initial_ast,
    " (debug) dump the initial ast to stdout");
  ( "-ddump_tc_ast",
    Arg.Set opt_ddump_tc_ast,
    " (debug) dump the typechecked ast to stdout");
  ( "-ddump_rewrite_ast",
    Arg.String (fun l -> opt_ddump_rewrite_ast := Some (l, 0); Specialize.opt_ddump_spec_ast := Some (l, 0)),
    "<prefix> (debug) dump the ast after each rewriting step to <prefix>_<i>.lem");
  ( "-ddump_smt_graphs",
    Arg.Set Jib_smt.opt_debug_graphs,
    " (debug) dump flow analysis for properties when generating SMT");
  ( "-dtc_verbose",
    Arg.Int (fun verbosity -> Type_check.opt_tc_debug := verbosity),
    "<verbosity> (debug) verbose typechecker output: 0 is silent");
  ( "-dsmt_verbose",
    Arg.Set Constraint.opt_smt_verbose,
    " (debug) print SMTLIB constraints sent to SMT solver");
  ( "-dno_cast",
    Arg.Set opt_dno_cast,
    " (debug) typecheck without any implicit casting");
  ( "-dsanity",
    Arg.Set opt_sanity,
    " (debug) sanity check the AST (slow)");
  ( "-dmagic_hash",
    Arg.Set Initial_check.opt_magic_hash,
    " (debug) allow special character # in identifiers");
  ( "-dprofile",
    Arg.Set Profile.opt_profile,
    " (debug) provide basic profiling information for rewriting passes within Sail");
  ( "-v",
    Arg.Set opt_print_version,
    " print version");
] )

let version =
  let open Manifest in
  let default = Printf.sprintf "Sail %s @ %s" branch commit in
  (* version is parsed from the output of git describe *)
  match String.split_on_char '-' version with
  | (vnum :: _) ->
     Printf.sprintf "Sail %s (%s @ %s)" vnum branch commit
  | _ -> default

let usage_msg =
  version
  ^ "\nusage: sail <options> <file1.sail> ... <fileN.sail>\n"

let _ =
  Arg.parse options
    (fun s ->
      opt_file_arguments := (!opt_file_arguments) @ [s])
    usage_msg

let prover_regstate tgt ast type_envs =
  match tgt with
  | Some "coq" ->
     State.add_regstate_defs true type_envs ast
  | Some "lem" ->
     State.add_regstate_defs !Pretty_print_lem.opt_mwords type_envs ast
  | _ ->
     type_envs, ast

let ocaml_generator_info : (Type_check.tannot Ast.type_def list * string list) option ref = ref None

let stash_pre_rewrite_info tgt (ast : _ Ast_defs.ast) type_envs =
  match tgt with
  | Some "ocaml" ->
     begin
       ocaml_generator_info :=
         match !opt_ocaml_generators with
         | [] -> None
         | _ -> Some (Ocaml_backend.orig_types_for_ocaml_generator ast.defs, !opt_ocaml_generators)
     end
  | _ -> ()

let target name out_name ast type_envs =
  match name with
  | None -> ()

  | Some "sail" ->
     Pretty_print_sail.pp_ast stdout ast

  | Some "ocaml" ->
     let out = match !opt_file_out with None -> "out" | Some s -> s in
     Ocaml_backend.ocaml_compile out ast !ocaml_generator_info

  | Some "tofrominterp" ->
     let out = match !opt_file_out with None -> "out" | Some s -> s in
     ToFromInterp_backend.tofrominterp_output !opt_tofrominterp_output_dir out ast

  | Some "marshal" ->
     let out_filename = match !opt_file_out with None -> "out" | Some s -> s in
     let f = open_out_bin (out_filename ^ ".defs") in
     let remove_prover (l, tannot) =
       if Type_check.is_empty_tannot tannot then
         (l, Type_check.empty_tannot)
       else
         (l, Type_check.replace_env (Type_check.Env.set_prover None (Type_check.env_of_tannot tannot)) tannot)
     in
     Marshal.to_string (Ast_util.map_ast_annot remove_prover ast, Type_check.Env.set_prover None type_envs) [Marshal.Compat_32]
     |> Base64.encode_string
     |> output_string f;
     close_out f

  | Some "c" ->
     let ast, type_envs = Type_error.check Type_check.initial_env ast in
     let close, output_chan = match !opt_file_out with Some f -> true, open_out (f ^ ".c") | None -> false, stdout in
     Reporting.opt_warnings := true;
     C_backend.compile_ast type_envs output_chan (!opt_includes_c) ast;
     flush output_chan;
     if close then close_out output_chan else ()

  | Some "c2" ->
     let module StringMap = Map.Make(String) in
     let ast_c, type_envs = Specialize.(specialize typ_ord_specialization type_envs ast) in
     let ast_c, type_envs =
       if !opt_specialize_c then
         Specialize.(specialize_passes 2 int_specialization type_envs ast_c)
       else
         ast_c, type_envs
     in
     let output_name = match !opt_file_out with Some f -> f | None -> "out" in
     Reporting.opt_warnings := true;
     let codegen ctx cdefs =
       let open Json.Util in
       let codegen_opts = match !opt_config with
         | Some config -> C_codegen.options_from_json (member "codegen" config) cdefs
         | None -> C_codegen.default_options cdefs
       in
       let module Codegen =
         C_codegen.Make(
             struct let opts = codegen_opts end
           )
       in
       Codegen.emulator ctx output_name cdefs
     in
     C_backend.compile_ast_clib type_envs ast_c codegen;
 
  | Some "ir" ->
     let ast, type_envs = Type_error.check Type_check.initial_env ast in
     let close, output_chan =
       match !opt_file_out with
       | Some f -> Util.opt_colors := false; (true, open_out (f ^ ".ir"))
       | None -> false, stdout
     in
     Reporting.opt_warnings := true;
     let cdefs, _ = C_backend.jib_of_ast type_envs ast in
     let buf = Buffer.create 256 in
     Jib_ir.Flat_ir_formatter.output_defs buf cdefs;
     output_string output_chan (Buffer.contents buf);
     flush output_chan;
     if close then close_out output_chan else ()

  | Some "smt" when !opt_smt_serialize ->
     let ast_smt, type_envs = Specialize.(specialize typ_ord_specialization type_envs ast) in
     let ast_smt, type_envs = Specialize.(specialize_passes 2 int_specialization_with_externs type_envs ast_smt) in
     let jib, _, ctx = Jib_smt.compile type_envs ast_smt in
     let name_file =
       match !opt_file_out with
       | Some f -> f ^ ".smt_model"
       | None -> "sail.smt_model"
     in
     Reporting.opt_warnings := true;
     Jib_smt.serialize_smt_model name_file type_envs ast_smt

  | Some "smt" ->
     let open Ast_util in
     let props = Property.find_properties ast in
     let prop_ids = Bindings.bindings props |> List.map fst |> IdSet.of_list in
     let ast = Slice.filter_ast_ids prop_ids IdSet.empty ast in
     Specialize.add_initial_calls prop_ids;
     let ast_smt, type_envs = Specialize.(specialize typ_ord_specialization type_envs ast) in
     let ast_smt, type_envs = Specialize.(specialize_passes 2 int_specialization_with_externs type_envs ast_smt) in
     let name_file =
       match !opt_file_out with
       | Some f -> fun str -> f ^ "_" ^ str ^ ".smt2"
       | None -> fun str -> str ^ ".smt2"
     in
     Reporting.opt_warnings := true;
     Jib_smt.generate_smt props name_file type_envs ast_smt;

  | Some "lem" ->
     output "" (Lem_out (!opt_libs_lem)) [(out_name, type_envs, ast)]

  | Some "coq" ->
     output "" (Coq_out (!opt_libs_coq)) [(out_name, type_envs, ast)]

  | Some "latex" ->
     Reporting.opt_warnings := true;
     let latex_dir = match !opt_file_out with None -> "sail_latex" | Some s -> s in
     begin
       try
         if not (Sys.is_directory latex_dir) then begin
             prerr_endline ("Failure: latex output location exists and is not a directory: " ^ latex_dir);
             exit 1
           end
       with Sys_error(_) -> Unix.mkdir latex_dir 0o755
     end;
     Latex.opt_directory := latex_dir;
     let chan = open_out (Filename.concat latex_dir "commands.tex") in
     output_string chan (Pretty_print_sail.to_string (Latex.defs ast));
     close_out chan

  | Some t ->
     raise (Reporting.err_unreachable Parse_ast.Unknown __POS__ ("Undefined target: " ^ t))

let feature_check () =
  match !opt_have_feature with
  | None -> ()
  | Some symbol ->
     if Process_file.have_symbol symbol then
       exit 0
     else
       exit 2

let main () =
  feature_check ();
  if !opt_print_version then
    print_endline version
  else
    begin
      let reset_effect_checking = !opt_infer_effects && not !Type_check.opt_no_effects in
      let () = if !opt_infer_effects then Type_check.opt_no_effects := true in
      let out_name, ast, type_envs = load_files !opt_target options Type_check.initial_env !opt_file_arguments in
      let ast, type_envs = descatter type_envs ast in
      let ast, type_envs =
        List.fold_right (fun file (ast,_) -> Splice.splice ast file)
          (!opt_splice) (ast, type_envs)
      in
      Reporting.opt_warnings := false; (* Don't show warnings during re-writing for now *)

      let ast, type_envs =
        if !opt_infer_effects then
          let ast = Spec_analysis.infer_effects ast in
          let _ = if reset_effect_checking then Type_check.opt_no_effects := true in
          Type_error.check Type_check.initial_env ast
        else ast, type_envs
      in

      begin match !opt_process_elf, !opt_file_out with
      | Some elf, Some out ->
         begin
           let open Elf_loader in
           let chan = open_out out in
           load_elf ~writer:(write_file chan) elf;
           output_string chan "elf_entry\n";
           output_string chan (Big_int.to_string !opt_elf_entry ^ "\n");
           close_out chan;
           exit 0
         end
      | Some _, None ->
         prerr_endline "Failure: No output file given for processed ELF (option -o).";
         exit 1
      | None, _ -> ()
      end;

      if !opt_sanity then
        ignore (rewrite_ast_check type_envs ast)
      else ();

      stash_pre_rewrite_info !opt_target ast type_envs;

      let type_envs, ast = prover_regstate !opt_target ast type_envs in
      let ast, type_envs = match !opt_target with Some tgt -> rewrite_ast_target tgt type_envs ast | None -> ast, type_envs in
      target !opt_target out_name ast type_envs;

      if !Interactive.opt_interactive then
        (Interactive.ast := ast; Interactive.env := type_envs)
      else ();

      if !opt_memo_z3 then Constraint.save_digests () else ()
    end

let _ = try
    begin
      try ignore (main ())
      with Failure s -> raise (Reporting.err_general Parse_ast.Unknown ("Failure " ^ s))
    end
  with Reporting.Fatal_error e ->
    Reporting.print_error e;
    Interactive.opt_suppress_banner := true;
    if !opt_memo_z3 then Constraint.save_digests () else ();
    if !Interactive.opt_interactive then () else exit 1
