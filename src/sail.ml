(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

open Process_file

module Big_int = Nat_big_num

let lib = ref ([] : string list)
let opt_file_out : string option ref = ref None
let opt_interactive_script : string option ref = ref None
let opt_print_version = ref false
let opt_target = ref None
let opt_memo_z3 = ref false
let opt_sanity = ref false
let opt_includes_c = ref ([]:string list)
let opt_specialize_c = ref false
let opt_libs_lem = ref ([]:string list)
let opt_libs_coq = ref ([]:string list)
let opt_file_arguments = ref ([]:string list)
let opt_process_elf : string option ref = ref None
let opt_ocaml_generators = ref ([]:string list)

let set_target name = Arg.Unit (fun _ -> opt_target := Some name)

let options = Arg.align ([
  ( "-o",
    Arg.String (fun f -> opt_file_out := Some f),
    "<prefix> select output filename prefix");
  ( "-i",
    Arg.Tuple [Arg.Set Interactive.opt_interactive],
    " start interactive interpreter");
  ( "-is",
    Arg.Tuple [Arg.Set Interactive.opt_interactive; Arg.String (fun s -> opt_interactive_script := Some s)],
    "<filename> start interactive interpreter and execute commands in script");
  ( "-iout",
    Arg.String (fun file -> Value.output_redirect (open_out file)),
    "<filename> print interpreter output to file");
  ( "-emacs",
    Arg.Set Interactive.opt_emacs_mode,
    " run sail interactively as an emacs mode child process");
  ( "-no_warn",
    Arg.Clear Util.opt_warnings,
    " do not print warnings");
  ( "-ocaml",
    Arg.Tuple [set_target "ocaml"; Arg.Set Initial_check.opt_undefined_gen],
    " output an OCaml translated version of the input");
  ( "-ocaml-nobuild",
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
    Arg.Tuple [set_target "latex"; Arg.Clear Type_check.opt_expand_valspec],
    " pretty print the input to LaTeX");
  ( "-latex_prefix",
    Arg.String (fun prefix -> Latex.opt_prefix := prefix),
    "<prefix> set a custom prefix for generated LaTeX macro command (default sail)");
  ( "-latex_full_valspecs",
    Arg.Clear Latex.opt_simple_val,
    " print full valspecs in LaTeX output");
  ( "-ir",
    set_target "ir",
    " print intermediate representation");
  ( "-smt",
    set_target "smt",
    " print SMT translated version of input");
  ( "-smt_ignore_overflow",
    Arg.Set Jib_smt.opt_ignore_overflow,
    " ignore integer overflow in generated SMT");
  ( "-smt_int_size",
    Arg.String (fun n -> Jib_smt.opt_default_lint_size := int_of_string n),
    "<n> set a bound of n on the maximum integer bitwidth for generated SMT (default 128)");
  ( "-smt_bits_size",
    Arg.String (fun n -> Jib_smt.opt_default_lbits_index := int_of_string n),
    "<n> set a bound of 2 ^ n for bitvector bitwidth in generated SMT (default 8)");
  ( "-smt_vector_size",
    Arg.String (fun n -> Jib_smt.opt_default_vector_index := int_of_string n),
    "<n> set a bound of 2 ^ n for generic vectors in generated SMT (default 5)");
  ( "-c",
    Arg.Tuple [set_target "c"; Arg.Set Initial_check.opt_undefined_gen],
    " output a C translated version of the input");
  ( "-c_include",
    Arg.String (fun i -> opt_includes_c := i::!opt_includes_c),
    "<filename> provide additional include for C output");
  ( "-c_no_main",
    Arg.Set C_backend.opt_no_main,
    " do not generate the main() function" );
  ( "-c_no_rts",
    Arg.Set C_backend.opt_no_rts,
    " do not include the Sail runtime" );
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
  ( "-c_fold_unit",
    Arg.String (fun str -> Constant_fold.opt_fold_to_unit := Util.split_on_char ',' str),
    " remove comma separated list of functions from C output, replacing them with unit");
  ( "-elf",
    Arg.String (fun elf -> opt_process_elf := Some elf),
    " process an ELF file so that it can be executed by compiled C code");
  ( "-O",
    Arg.Tuple [Arg.Set C_backend.optimize_primops;
               Arg.Set C_backend.optimize_hoist_allocations;
               Arg.Set Initial_check.opt_fast_undefined;
               Arg.Set Type_check.opt_no_effects;
               Arg.Set C_backend.optimize_struct_updates;
               Arg.Set C_backend.optimize_alias],
    " turn on optimizations for C compilation");
  ( "-Oconstant_fold",
    Arg.Set Constant_fold.optimize_constant_fold,
    " apply constant folding optimizations");
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
    " memoize calls to z3, improving performance when typechecking repeatedly (default)");
  ( "-no_memo_z3",
    Arg.Clear opt_memo_z3,
    " do not memoize calls to z3 (default)");
  ( "-memo",
    Arg.Tuple [Arg.Set opt_memo_z3; Arg.Set C_backend.opt_memo_cache],
    " memoize calls to z3, and intermediate compilation results");
  ( "-undefined_gen",
    Arg.Set Initial_check.opt_undefined_gen,
    " generate undefined_type functions for types in the specification");
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
  ( "-ddump_tc_ast",
    Arg.Set opt_ddump_tc_ast,
    " (debug) dump the typechecked ast to stdout");
  ( "-ddump_rewrite_ast",
    Arg.String (fun l -> opt_ddump_rewrite_ast := Some (l, 0); Specialize.opt_ddump_spec_ast := Some (l, 0)),
    "<prefix> (debug) dump the ast after each rewriting step to <prefix>_<i>.lem");
  ( "-ddump_flow_graphs",
    Arg.Set Jib_compile.opt_debug_flow_graphs,
    " (debug) dump flow analysis for Sail functions when compiling to C");
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
  ( "-dfunction",
    Arg.String (fun f -> Jib_compile.opt_debug_function := f),
    " (debug) print debugging output for a single function");
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

let load_files ?check:(check=false) type_envs files =
  if !opt_memo_z3 then Constraint.load_digests () else ();

  let t = Profile.start () in
  let parsed = List.map (fun f -> (f, parse_file f)) files in
  let ast =
    List.fold_right (fun (_, Parse_ast.Defs ast_nodes) (Parse_ast.Defs later_nodes)
                     -> Parse_ast.Defs (ast_nodes@later_nodes)) parsed (Parse_ast.Defs []) in
  let ast = Process_file.preprocess_ast options ast in
  let ast = Initial_check.process_ast ~generate:(not check) ast in
  Profile.finish "parsing" t;

  let t = Profile.start () in
  let (ast, type_envs) = check_ast type_envs ast in
  Profile.finish "type checking" t;

  if !opt_memo_z3 then Constraint.save_digests () else ();

  if check then
    ("out.sail", ast, type_envs)
  else
    let ast = Scattered.descatter ast in
    let ast = rewrite_ast_initial type_envs ast in

    let out_name = match !opt_file_out with
      | None when parsed = [] -> "out.sail"
      | None -> fst (List.hd parsed)
      | Some f -> f ^ ".sail" in

    (out_name, ast, type_envs)

let prover_regstate tgt ast type_envs =
  match tgt with
  | Some "coq" ->
     State.add_regstate_defs true type_envs ast
  | Some "lem" ->
     State.add_regstate_defs !Pretty_print_lem.opt_mwords type_envs ast
  | _ ->
     type_envs, ast

let target name out_name ast type_envs =
  match name with
  | None -> ()

  | Some "sail" ->
     Pretty_print_sail.pp_defs stdout ast

  | Some "ocaml" ->
     let ocaml_generator_info =
       match !opt_ocaml_generators with
       | [] -> None
       | _ -> Some (Ocaml_backend.orig_types_for_ocaml_generator ast, !opt_ocaml_generators)
     in
     let out = match !opt_file_out with None -> "out" | Some s -> s in
     Ocaml_backend.ocaml_compile out ast ocaml_generator_info

  | Some "c" ->
     let ast_c, type_envs = Specialize.(specialize typ_ord_specialization ast type_envs) in
     let ast_c, type_envs =
       if !opt_specialize_c then
         Specialize.(specialize' 2 int_specialization ast_c type_envs)
       else
         ast_c, type_envs
     in
     let close, output_chan = match !opt_file_out with Some f -> true, open_out (f ^ ".c") | None -> false, stdout in
     Util.opt_warnings := true;
     C_backend.compile_ast type_envs output_chan (!opt_includes_c) ast_c;
     flush output_chan;
     if close then close_out output_chan else ()

  | Some "ir" ->
     let ast_c, type_envs = Specialize.(specialize typ_ord_specialization ast type_envs) in
     (* let ast_c, type_envs = Specialize.(specialize' 2 int_specialization_with_externs ast_c type_envs) in *)
     let close, output_chan =
       match !opt_file_out with
       | Some f -> Util.opt_colors := false; (true, open_out (f ^ ".ir.sail"))
       | None -> false, stdout
     in
     Util.opt_warnings := true;
     let cdefs, _ = C_backend.jib_of_ast type_envs ast_c in
     (* let cdefs = List.map Jib_optimize.flatten_cdef cdefs in *)
     let str = Pretty_print_sail.to_string PPrint.(separate_map hardline Jib_util.pp_cdef cdefs) in
     output_string output_chan (str ^ "\n");
     flush output_chan;
     if close then close_out output_chan else ()

  | Some "smt" ->
     let open Ast_util in
     let props = Property.find_properties ast in
     Bindings.bindings props |> List.map fst |> IdSet.of_list |> Specialize.add_initial_calls;
     let ast_smt, type_envs = Specialize.(specialize typ_ord_specialization ast type_envs) in
     let ast_smt, type_envs = Specialize.(specialize' 2 int_specialization_with_externs ast_smt type_envs) in
     let name_file =
       match !opt_file_out with
       | Some f -> fun str -> f ^ "_" ^ str ^ ".smt2"
       | None -> fun str -> str ^ ".smt2"
     in
     Util.opt_warnings := true;
     Jib_smt.generate_smt props name_file type_envs ast_smt;

  | Some "lem" ->
     output "" (Lem_out (!opt_libs_lem)) [(out_name, type_envs, ast)]

  | Some "coq" ->
     output "" (Coq_out (!opt_libs_coq)) [(out_name, type_envs, ast)]

  | Some "latex" ->
     Util.opt_warnings := true;
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

let main () =
  if !opt_print_version then
    print_endline version
  else
    begin
      let out_name, ast, type_envs = load_files Type_check.initial_env !opt_file_arguments in
      Util.opt_warnings := false; (* Don't show warnings during re-writing for now *)

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

      let type_envs, ast = prover_regstate !opt_target ast type_envs in
      let ast = match !opt_target with Some tgt -> rewrite_ast_target tgt type_envs ast | None -> ast in
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
    if !Interactive.opt_interactive then () else exit 1
