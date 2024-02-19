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

let opt_new_cli = ref false
let opt_free_arguments : string list ref = ref []
let opt_file_out : string option ref = ref None
let opt_just_check : bool ref = ref false
let opt_auto_interpreter_rewrites : bool ref = ref false
let opt_interactive_script : string option ref = ref None
let opt_splice : string list ref = ref []
let opt_print_version = ref false
let opt_memo_z3 = ref true
let opt_have_feature = ref None
let opt_all_modules = ref false
let opt_show_sail_dir = ref false
let opt_project_files : string list ref = ref []
let opt_variable_assignments : string list ref = ref []
let opt_config_file : string option ref = ref None
let opt_format = ref false
let opt_format_backup : string option ref = ref None
let opt_format_only : string list ref = ref []
let opt_format_skip : string list ref = ref []

(* Allow calling all options as either -foo_bar, -foo-bar, or
   --foo-bar (for long options). The standard long-opt version
   --foo-bar is treated as the canonical choice. If !opt_new_cli is
   set we warn for any non-canonical options. *)
let rec fix_options = function
  | (flag, spec, doc) :: opts ->
      if flag = "-help" || flag = "--help" then (flag, spec, doc) :: fix_options opts
      else (
        let dash_flag = String.map (function '_' -> '-' | c -> c) flag in
        let canonical_flag = if String.length flag > 2 then "-" ^ dash_flag else dash_flag in
        let non_canonical spec =
          if !opt_new_cli then (
            let explanation =
              Printf.sprintf "Old style command line flag %s used, use %s instead" flag canonical_flag
            in
            Arg.Tuple [Arg.Unit (fun () -> Reporting.warn "Old style flag" Parse_ast.Unknown explanation); spec]
          )
          else spec
        in
        if canonical_flag = flag then (flag, spec, doc) :: fix_options opts
        else if dash_flag = flag then (flag, non_canonical spec, "") :: (canonical_flag, spec, doc) :: fix_options opts
        else
          (flag, non_canonical spec, "")
          :: (dash_flag, non_canonical spec, "")
          :: (canonical_flag, spec, doc) :: fix_options opts
      )
  | [] -> []

(* This function does roughly the same thing as Arg.align, except we
   can call it per target and it won't add additional -help
   options. *)
let target_align opts =
  let split_doc doc =
    if String.length doc > 0 then
      if doc.[0] = ' ' then ("", doc)
      else if doc.[0] = '\n' then ("", doc)
      else (
        match String.index_from_opt doc 0 ' ' with
        | Some n -> (String.sub doc 0 n, String.sub doc n (String.length doc - n))
        | None -> ("", doc)
      )
    else ("", "")
  in
  let opts = List.map (fun (flag, spec, doc) -> (flag, spec, split_doc doc)) opts in
  let alignment = List.fold_left (fun a (flag, _, (arg, _)) -> max a (String.length flag + String.length arg)) 0 opts in
  let opts =
    List.map
      (fun (flag, spec, (arg, doc)) ->
        if doc = "" then (flag, spec, arg)
        else (flag, spec, arg ^ String.make (max 0 (alignment - (String.length flag + String.length arg))) ' ' ^ doc)
      )
      opts
  in
  opts

(* Add a header to separate arguments from each plugin *)
let add_target_header plugin opts =
  let add_header (flag, spec, doc) =
    let desc =
      match Target.extract_registered () with
      | [] -> "plugin " ^ plugin
      | [name] -> "target " ^ name
      | names -> "targets " ^ Util.string_of_list ", " (fun x -> x) names
    in
    (flag, spec, doc ^ " \n\nOptions for " ^ desc)
  in
  Util.update_last add_header opts

let load_plugin opts plugin =
  try
    Dynlink.loadfile_private plugin;
    let plugin_opts = Target.extract_options () |> fix_options |> target_align in
    opts := add_target_header plugin !opts @ plugin_opts
  with Dynlink.Error msg -> prerr_endline ("Failed to load plugin " ^ plugin ^ ": " ^ Dynlink.error_message msg)

let version =
  let open Manifest in
  let default = Printf.sprintf "Sail %s @ %s" branch commit in
  (* version is parsed from the output of git describe *)
  match String.split_on_char '-' version with
  | vnum :: _ -> Printf.sprintf "Sail %s (%s @ %s)" vnum branch commit
  | _ -> default

let usage_msg = version ^ "\nusage: sail <options> <file1.sail> ... <fileN.sail>\n"

let help options = raise (Arg.Help (Arg.usage_string options usage_msg))

let rec options =
  ref
    [
      ("-o", Arg.String (fun f -> opt_file_out := Some f), "<prefix> select output filename prefix");
      ("-dir", Arg.Set opt_show_sail_dir, " show current Sail library directory");
      ( "-i",
        Arg.Tuple
          [
            Arg.Set Interactive.opt_interactive;
            Arg.Unit (fun () -> Preprocess.add_symbol "INTERACTIVE");
            Arg.Set opt_auto_interpreter_rewrites;
          ],
        " start interactive interpreter"
      );
      ( "-is",
        Arg.Tuple
          [
            Arg.Set Interactive.opt_interactive;
            Arg.Unit (fun () -> Preprocess.add_symbol "INTERACTIVE");
            Arg.Set opt_auto_interpreter_rewrites;
            Arg.String (fun s -> opt_interactive_script := Some s);
          ],
        "<filename> start interactive interpreter and execute commands in script"
      );
      ( "-iout",
        Arg.String (fun file -> Value.output_redirect (open_out file)),
        "<filename> print interpreter output to file"
      );
      ( "-interact_custom",
        Arg.Set Interactive.opt_interactive,
        " drop to an interactive session after running Sail. Differs from -i in that it does not set up the \
         interpreter in the interactive shell."
      );
      ( "-project",
        Arg.String (fun file -> opt_project_files := !opt_project_files @ [file]),
        "<file> sail project file defining module structure"
      );
      ( "-variable",
        Arg.String (fun assignment -> opt_variable_assignments := assignment :: !opt_variable_assignments),
        "<variable=value> assign a module variable to a value"
      );
      ("-all_modules", Arg.Set opt_all_modules, " use all modules in project file");
      ("-list_files", Arg.Set Frontend.opt_list_files, " list files used in all project files");
      ("-config", Arg.String (fun file -> opt_config_file := Some file), "<file> configuration file");
      ("-abstract_types", Arg.Set Initial_check.opt_abstract_types, " (experimental) allow abstract types");
      ("-fmt", Arg.Set opt_format, " format input source code");
      ( "-fmt_backup",
        Arg.String (fun suffix -> opt_format_backup := Some suffix),
        "<suffix> create backups of formated files as 'file.suffix'"
      );
      ("-fmt_only", Arg.String (fun file -> opt_format_only := file :: !opt_format_only), "<file> format only this file");
      ( "-fmt_skip",
        Arg.String (fun file -> opt_format_skip := file :: !opt_format_skip),
        "<file> skip formatting this file"
      );
      ( "-D",
        Arg.String (fun symbol -> Preprocess.add_symbol symbol),
        "<symbol> define a symbol for the preprocessor, as $define does in the source code"
      );
      ("-no_warn", Arg.Clear Reporting.opt_warnings, " do not print warnings");
      ("-all_warnings", Arg.Set Reporting.opt_all_warnings, " print all warning messages");
      ("-strict_var", Arg.Set Type_check.opt_strict_var, " require var expressions for variable declarations");
      ("-plugin", Arg.String (fun plugin -> load_plugin options plugin), "<file> load a Sail plugin");
      ("-just_check", Arg.Set opt_just_check, " terminate immediately after typechecking");
      ("-memo_z3", Arg.Set opt_memo_z3, " memoize calls to z3, improving performance when typechecking repeatedly");
      ("-no_memo_z3", Arg.Clear opt_memo_z3, " do not memoize calls to z3 (default)");
      ( "-have_feature",
        Arg.String (fun symbol -> opt_have_feature := Some symbol),
        "<symbol> check if a feature symbol is set by default"
      );
      ("-no_color", Arg.Clear Util.opt_colors, " do not use terminal color codes in output");
      ( "-string_literal_type",
        Arg.Set Type_env.opt_string_literal_type,
        " use a separate string_literal type for string literals"
      );
      ( "-grouped_regstate",
        Arg.Set State.opt_type_grouped_regstate,
        " group registers with same type together in generated register state record"
      );
      (* Casts have been removed, preserved for backwards compatibility *)
      ("-enum_casts", Arg.Unit (fun () -> ()), "");
      ("-non_lexical_flow", Arg.Set Nl_flow.opt_nl_flow, " allow non-lexical flow typing");
      ( "-no_lexp_bounds_check",
        Arg.Set Type_check.opt_no_lexp_bounds_check,
        " turn off bounds checking for vector assignments in l-expressions"
      );
      ("-auto_mono", Arg.Set Rewrites.opt_auto_mono, " automatically infer how to monomorphise code");
      ("-mono_rewrites", Arg.Set Rewrites.opt_mono_rewrites, " turn on rewrites for combining bitvector operations");
      ( "-mono_split",
        Arg.String
          (fun s ->
            let l = Util.split_on_char ':' s in
            match l with
            | [fname; line; var] ->
                Rewrites.opt_mono_split := ((fname, int_of_string line), var) :: !Rewrites.opt_mono_split
            | _ -> raise (Arg.Bad (s ^ " not of form <filename>:<line>:<variable>"))
          ),
        "<filename>:<line>:<variable> manually gives a case split for monomorphisation"
      );
      ( "-splice",
        Arg.String (fun s -> opt_splice := s :: !opt_splice),
        "<filename> add functions from file, replacing existing definitions where necessary"
      );
      ( "-smt_solver",
        Arg.String (fun s -> Constraint.set_solver (String.trim s)),
        "<solver> choose SMT solver. Supported solvers are z3 (default), alt-ergo, cvc4, mathsat, vampire and yices."
      );
      ( "-smt_linearize",
        Arg.Set Type_env.opt_smt_linearize,
        " (experimental) force linearization for constraints involving exponentials"
      );
      ("-Oconstant_fold", Arg.Set Constant_fold.optimize_constant_fold, " apply constant folding optimizations");
      ( "-Oaarch64_fast",
        Arg.Set Jib_compile.optimize_aarch64_fast_struct,
        " apply ARMv8.5 specific optimizations (potentially unsound in general)"
      );
      ("-Ofast_undefined", Arg.Set Initial_check.opt_fast_undefined, " turn on fast-undefined mode");
      ( "-const_prop_mutrec",
        Arg.String
          (fun name ->
            Constant_propagation_mutrec.targets := Ast_util.mk_id name :: !Constant_propagation_mutrec.targets
          ),
        " unroll function in a set of mutually recursive functions"
      );
      ("-ddump_initial_ast", Arg.Set Frontend.opt_ddump_initial_ast, " (debug) dump the initial ast to stdout");
      ("-ddump_tc_ast", Arg.Set Frontend.opt_ddump_tc_ast, " (debug) dump the typechecked ast to stdout");
      ("-dtc_verbose", Arg.Int Type_check.set_tc_debug, "<verbosity> (debug) verbose typechecker output: 0 is silent");
      ("-dsmt_verbose", Arg.Set Constraint.opt_smt_verbose, " (debug) print SMTLIB constraints sent to SMT solver");
      ("-dmagic_hash", Arg.Set Initial_check.opt_magic_hash, " (debug) allow special character # in identifiers");
      ("-dno_error_filenames", Arg.Set Error_format.opt_debug_no_filenames, " (debug) do not print filenames in errors");
      ( "-dprofile",
        Arg.Set Profile.opt_profile,
        " (debug) provide basic profiling information for rewriting passes within Sail"
      );
      ("-dno_cast", Arg.Unit (fun () -> ()), "");
      (* No longer does anything, preserved for backwards compatibility only *)
      ("-dallow_cast", Arg.Unit (fun () -> ()), "");
      ( "-ddump_rewrite_ast",
        Arg.String
          (fun l ->
            Rewrites.opt_ddump_rewrite_ast := Some (l, 0);
            Specialize.opt_ddump_spec_ast := Some (l, 0)
          ),
        "<prefix> (debug) dump the ast after each rewriting step to <prefix>_<i>.lem"
      );
      ( "-dmono_all_split_errors",
        Arg.Set Rewrites.opt_dall_split_errors,
        " (debug) display all case split errors from monomorphisation, rather than one"
      );
      ( "-dmono_analysis",
        Arg.Set_int Rewrites.opt_dmono_analysis,
        "<verbosity> (debug) dump information about monomorphisation analysis: 0 silent, 3 max"
      );
      ("-dmono_continue", Arg.Set Rewrites.opt_dmono_continue, " (debug) continue despite monomorphisation errors");
      ("-dmono_limit", Arg.Set_int Monomorphise.opt_size_set_limit, " (debug) adjust maximum size of split allowed");
      ("-dpattern_warning_no_literals", Arg.Set Pattern_completeness.opt_debug_no_literals, "");
      ( "-dbacktrace",
        Arg.Int (fun l -> Reporting.opt_backtrace_length := l),
        "<length> (debug) length of backtrace to show when reporting unreachable code"
      );
      ( "-infer_effects",
        Arg.Unit (fun () -> Reporting.simple_warn "-infer_effects option is deprecated"),
        " (deprecated) ignored for compatibility with older versions; effects are always inferred now"
      );
      ( "-undefined_gen",
        Arg.Unit (fun () -> ()),
        " (deprecated) ignored as undefined generation is now always the same for all Sail backends"
      );
      ("-v", Arg.Set opt_print_version, " print version");
      ("-version", Arg.Set opt_print_version, " print version");
      ("-verbose", Arg.Int (fun verbosity -> Util.opt_verbosity := verbosity), "<verbosity> produce verbose output");
      ( "-explain_all_variables",
        Arg.Set Type_error.opt_explain_all_variables,
        " explain all type variables in type error messages"
      );
      ("-explain_constraints", Arg.Set Type_error.opt_explain_constraints, " explain constraints in type error messages");
      ( "-explain_verbose",
        Arg.Tuple [Arg.Set Type_error.opt_explain_all_variables; Arg.Set Type_error.opt_explain_constraints],
        " add the maximum amount of explanation to type errors"
      );
      ("-h", Arg.Unit (fun () -> help !options), " display this list of options. Also available as -help or --help");
      ("-help", Arg.Unit (fun () -> help !options), " display this list of options");
      ("--help", Arg.Unit (fun () -> help !options), " display this list of options");
    ]

let register_default_target () = Target.register ~name:"default" Target.empty_action

let file_to_string filename =
  let chan = open_in filename in
  let buf = Buffer.create 4096 in
  try
    let rec loop () =
      let line = input_line chan in
      Buffer.add_string buf line;
      Buffer.add_char buf '\n';
      loop ()
    in
    loop ()
  with End_of_file ->
    close_in chan;
    Buffer.contents buf

let run_sail (config : Yojson.Basic.t option) tgt =
  Target.run_pre_parse_hook tgt ();

  let project_files, frees =
    List.partition (fun free -> Filename.check_suffix free ".sail_project") !opt_free_arguments
  in

  let ast, env, effect_info =
    match (project_files, !opt_project_files) with
    | [], [] ->
        (* If there are no provided project files, we concatenate all
           the free file arguments into one big blob like before *)
        Frontend.load_files ~target:tgt Manifest.dir !options Type_check.initial_env frees
    (* Allows project files from either free arguments via suffix, or
       from -project, but not both as the ordering between them would
       be unclear. *)
    | project_files, [] | [], project_files ->
        let t = Profile.start () in
        let defs =
          List.map
            (fun project_file ->
              let root_directory = Filename.dirname project_file in
              let contents = file_to_string project_file in
              Project.mk_root root_directory :: Initial_check.parse_project ~filename:project_file ~contents ()
            )
            project_files
          |> List.concat
        in
        let variables = ref Util.StringMap.empty in
        List.iter
          (fun assignment ->
            if not (Project.parse_assignment ~variables assignment) then
              raise (Reporting.err_general Parse_ast.Unknown ("Could not parse assignment " ^ assignment))
          )
          !opt_variable_assignments;
        let proj = Project.initialize_project_structure ~variables defs in
        let mod_ids =
          if !opt_all_modules then Project.all_modules proj
          else
            List.map
              (fun mod_name ->
                match Project.get_module_id proj mod_name with
                | Some id -> id
                | None -> raise (Reporting.err_general Parse_ast.Unknown ("Unknown module " ^ mod_name))
              )
              frees
        in
        Profile.finish "parsing project" t;
        let env = Type_check.initial_env_with_modules proj in
        Frontend.load_modules ~target:tgt Manifest.dir !options env proj mod_ids
    | _, _ ->
        raise
          (Reporting.err_general Parse_ast.Unknown
             "Module files (.sail_project) should either be specified with the appropriate option, or as free \
              arguments with the appropriate extension, but not both!"
          )
  in
  let ast, env = Frontend.initial_rewrite effect_info env ast in
  let ast, env = List.fold_right (fun file (ast, _) -> Splice.splice ast file) !opt_splice (ast, env) in
  let effect_info = Effects.infer_side_effects (Target.asserts_termination tgt) ast in

  (* Don't show warnings during re-writing for now *)
  Reporting.suppressed_warning_info ();
  Reporting.opt_warnings := false;

  Target.run_pre_rewrites_hook tgt ast effect_info env;
  let ast, effect_info, env = Rewrites.rewrite effect_info env (Target.rewrites tgt) ast in

  Target.action tgt config Manifest.dir !opt_file_out ast effect_info env;

  (ast, env, effect_info)

let run_sail_format (config : Yojson.Basic.t option) =
  let is_format_file f = match !opt_format_only with [] -> true | files -> List.exists (fun f' -> f = f') files in
  let is_skipped_file f = match !opt_format_skip with [] -> false | files -> List.exists (fun f' -> f = f') files in
  let module Config = struct
    let config =
      match config with
      | Some (`Assoc keys) ->
          List.assoc_opt "fmt" keys |> Option.map Format_sail.config_from_json
          |> Option.value ~default:Format_sail.default_config
      | Some _ -> raise (Reporting.err_general Parse_ast.Unknown "Invalid configuration file (must be a json object)")
      | None -> Format_sail.default_config
  end in
  let module Formatter = Format_sail.Make (Config) in
  let parsed_files = List.map (fun f -> (f, Initial_check.parse_file f)) !opt_free_arguments in
  List.iter
    (fun (f, (comments, parse_ast)) ->
      let source = file_to_string f in
      if is_format_file f && not (is_skipped_file f) then (
        let formatted = Formatter.format_defs ~debug:true f source comments parse_ast in
        begin
          match !opt_format_backup with
          | Some suffix ->
              let out_chan = open_out (f ^ "." ^ suffix) in
              output_string out_chan source;
              close_out out_chan
          | None -> ()
        end;
        let ((out_chan, _, _, _) as file_info) = Util.open_output_with_check_unformatted None f in
        output_string out_chan formatted;
        Util.close_output_with_check file_info
      )
    )
    parsed_files

let feature_check () =
  match !opt_have_feature with None -> () | Some symbol -> if Preprocess.have_symbol symbol then exit 0 else exit 2

let get_plugin_dir () =
  match Sys.getenv_opt "SAIL_PLUGIN_DIR" with
  | Some path -> path :: Libsail_sites.Sites.plugins
  | None -> Libsail_sites.Sites.plugins

let rec find_file_above ?prev_inode_opt dir file =
  try
    let inode = (Unix.stat dir).st_ino in
    if Option.fold ~none:true ~some:(( <> ) inode) prev_inode_opt then (
      let filepath = Filename.concat dir file in
      if Sys.file_exists filepath then Some filepath
      else find_file_above ~prev_inode_opt:inode (dir ^ Filename.dir_sep ^ Filename.parent_dir_name) file
    )
    else None
  with Unix.Unix_error _ -> None

let get_config_file () =
  let check_exists file =
    if Sys.file_exists file then Some file
    else (
      Reporting.warn "" Parse_ast.Unknown (Printf.sprintf "Configuration file %s does not exist" file);
      None
    )
  in
  match !opt_config_file with
  | Some file -> check_exists file
  | None -> (
      match Sys.getenv_opt "SAIL_CONFIG" with
      | Some file -> check_exists file
      | None -> find_file_above (Sys.getcwd ()) "sail_config.json"
    )

let parse_config_file file =
  try Some (Yojson.Basic.from_file ~fname:file ~lnum:0 file)
  with Yojson.Json_error message ->
    Reporting.warn "" Parse_ast.Unknown (Printf.sprintf "Failed to parse configuration file: %s" message);
    None

let main () =
  if Option.is_some (Sys.getenv_opt "SAIL_NEW_CLI") then opt_new_cli := true;

  options := Arg.align (fix_options !options);

  begin
    match Sys.getenv_opt "SAIL_NO_PLUGINS" with
    | Some _ -> ()
    | None -> (
        match get_plugin_dir () with
        | dir :: _ ->
            List.iter
              (fun plugin ->
                let path = Filename.concat dir plugin in
                if Filename.extension plugin = ".cmxs" then load_plugin options path
              )
              (Array.to_list (Sys.readdir dir))
        | [] -> ()
      )
  end;

  Arg.parse_dynamic options (fun s -> opt_free_arguments := !opt_free_arguments @ [s]) usage_msg;

  let config = Option.bind (get_config_file ()) parse_config_file in

  feature_check ();

  if !opt_print_version then (
    print_endline version;
    exit 0
  );

  if !opt_show_sail_dir then (
    print_endline (Reporting.get_sail_dir Manifest.dir);
    exit 0
  );

  if !opt_format then (
    run_sail_format config;
    exit 0
  );

  let default_target = register_default_target () in

  if !opt_memo_z3 then Constraint.load_digests ();

  let ast, env, effect_info =
    match Target.get_the_target () with
    | Some target when not !opt_just_check -> run_sail config target
    | _ -> run_sail config default_target
  in

  if !opt_memo_z3 then Constraint.save_digests ();

  if !Interactive.opt_interactive then (
    let script =
      match !opt_interactive_script with
      | None -> []
      | Some file -> (
          let chan = open_in file in
          let lines = ref [] in
          try
            while true do
              let line = input_line chan in
              lines := line :: !lines
            done;
            []
          with End_of_file -> List.rev !lines
        )
    in
    Repl.start_repl ~commands:script ~auto_rewrites:!opt_auto_interpreter_rewrites ~config ~options:!options env
      effect_info ast
  )

let () =
  try try main () with Failure s -> raise (Reporting.err_general Parse_ast.Unknown s)
  with Reporting.Fatal_error e ->
    Reporting.print_error e;
    if !opt_memo_z3 then Constraint.save_digests () else ();
    exit 1
