(**************************************************************************)
(*                        Lem                                             *)
(*                                                                        *)
(*          Dominic Mulligan, University of Cambridge                     *)
(*          Francesco Zappa Nardelli, INRIA Paris-Rocquencourt            *)
(*          Gabriel Kerneis, University of Cambridge                      *)
(*          Kathy Gray, University of Cambridge                           *)
(*          Peter Boehm, University of Cambridge (while working on Lem)   *)
(*          Peter Sewell, University of Cambridge                         *)
(*          Scott Owens, University of Kent                               *)
(*          Thomas Tuerk, University of Cambridge                         *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2013                               *)
(*  by the UK authors above and Institut National de Recherche en         *)
(*  Informatique et en Automatique (INRIA).                               *)
(*                                                                        *)
(*  All files except ocaml-lib/pmap.{ml,mli} and ocaml-libpset.{ml,mli}   *)
(*  are distributed under the license below.  The former are distributed  *)
(*  under the LGPLv2, as in the LICENSE file.                             *)
(*                                                                        *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(**************************************************************************)

open Process_file
(*open Debug

let backends = ref []
let opt_print_types = ref false
let opt_print_version = ref false
let opt_library = ref (Some (Build_directory.d^"/library"))
let lib = ref []
let ocaml_lib = ref []
let hol_lib = ref []
let coq_lib = ref []
let isa_lib = ref []
let isa_theory = ref None
let opt_file_arguments = ref ([]:string list)

let options = Arg.align ([
  ( "-i",
    Arg.String (fun l -> lib := l::!lib),
    " treat the file as input only and generate no output for it");
  ( "-tex",
    Arg.Unit (fun b -> if not (List.mem (Some(Typed_ast.Target_tex)) !backends) then
                backends := Some(Typed_ast.Target_tex)::!backends),
    " generate LaTeX");
  ( "-html",
    Arg.Unit (fun b -> if not (List.mem (Some(Typed_ast.Target_html)) !backends) then
                backends := Some(Typed_ast.Target_html)::!backends),
    " generate Html");
  ( "-hol",
    Arg.Unit (fun b -> if not (List.mem (Some(Typed_ast.Target_hol)) !backends) then
                backends := Some(Typed_ast.Target_hol)::!backends),
    " generate HOL");
  ( "-ocaml",
    Arg.Unit (fun b -> if not (List.mem (Some(Typed_ast.Target_ocaml)) !backends) then
                backends := Some(Typed_ast.Target_ocaml)::!backends),
    " generate OCaml");
  ( "-isa",
    Arg.Unit (fun b -> if not (List.mem (Some(Typed_ast.Target_isa)) !backends) then
                backends := Some(Typed_ast.Target_isa)::!backends),
    " generate Isabelle");
  ( "-coq",
    Arg.Unit (fun b -> if not (List.mem (Some(Typed_ast.Target_coq)) !backends) then
                backends := Some(Typed_ast.Target_coq)::!backends),
    " generate Coq");
  ( "-ident",
    Arg.Unit (fun b -> if not (List.mem None !backends) then
                backends := None::!backends),
    " generate input on stdout");
  ( "-print_types",
    Arg.Unit (fun b -> opt_print_types := true),
    " print types on stdout");
  ( "-lib",
    Arg.String (fun l -> opt_library := Some l),
    " library path"^match !opt_library with None->"" | Some s -> " (default "^s^")");
  ( "-ocaml_lib",
    Arg.String (fun l -> ocaml_lib := l::!ocaml_lib),
    " add to OCaml library");
  ( "-hol_lib",
    Arg.String (fun l -> hol_lib := l::!hol_lib),
    " add to HOL library");
  ( "-isa_lib",
    Arg.String (fun l -> isa_lib := l::!isa_lib),
    " add to Isabelle library");
  ( "-isa_theory",
    Arg.String (fun l -> isa_theory := Some l),
    " Isabelle Lem theory");
  ( "-coq_lib",
    Arg.String (fun l -> coq_lib := l::!coq_lib),
    " add to Coq library");
  ( "-v",
    Arg.Unit (fun b -> opt_print_version := true),
    " print version");
  ( "-ident_pat_compile",
    Arg.Unit (fun b -> Target_trans.ident_force_pattern_compile := true; Reporting.ignore_pat_compile_warnings()),
    " activates pattern compilation for the identity backend. This is used for debugging.");
  ( "-only_changed_output",
    Arg.Unit (fun b -> Process_file.always_replace_files := false),
    " generate only output files, whose content really changed compared to the existing file");
  ( "-extra_level",
    Arg.Symbol (["none"; "auto"; "all"], (fun s ->
     Backend.gen_extra_level := (match s with
       | "none" -> 0
       | "auto" -> 1
       | _ -> 2))),
    " generate no (none) extra-information, only extras that can be handled automatically (auto) or all (all) extra information")
] @ Reporting.warn_opts)

let usage_msg =
    ("Lem " ^ Version.v ^ "\n"
     ^ "example usage:       lem -hol -ocaml -lib ../lem/library test.lem\n"
    )

let _ =
  Arg.parse options
    (fun s ->
      opt_file_arguments := (!opt_file_arguments) @ [s])
    usage_msg


let check_modules (def_info,env) modules =
  (* The checks. Modify these lists to add more. *)
  let exp_checks env = [Patterns.check_match_exp_warn env] in
  let pat_checks env = [] in
  let def_checks env = [Patterns.check_match_def_warn env] in

  (* Use the Macro_expander to execute these checks *)
  let (d,_) = def_info in
  let module Ctxt = struct let avoid = None let check = Some(d) end in
  let module M = Macro_expander.Expander(Ctxt) in
  let exp_mac env = Macro_expander.list_to_mac (List.map (fun f e -> (let _ = f e in None)) (exp_checks env)) in
  let exp_ty env ty = ty in
  let exp_src_ty env src_t = src_t in
  let exp_pat env = Macro_expander.list_to_bool_mac (List.map (fun f x p -> (let _ = f x p in None)) (pat_checks env)) in
  let check_defs env defs = begin
    let _ = M.expand_defs (List.rev defs) (exp_mac env, exp_ty env, exp_src_ty env, exp_pat env) in
    let _ = List.map (fun d -> List.map (fun c -> c d) (def_checks env)) defs in
    ()
  end in
  let check_module m = (let (defs, _) = m.Typed_ast.typed_ast in check_defs env defs) in
  let _ = List.map check_module modules in
  ()


(* Do the transformations for a given target, and then generate the output files
 * *)
let per_target libpath isa_thy modules (def_info,env) consts alldoc_accum alldoc_inc_accum alldoc_inc_usage_accum targ =
  let consts = List.assoc targ consts in
  let module C = struct
    let (d,i) = def_info
  end
  in
  let module T = Target_trans.Make(C) in
  let (trans,avoid) = T.get_transformation targ consts in
    try
      let (_,transformed_m) =
        List.fold_left
          (fun (env,new_mods) old_mod ->
             let (env,m) = trans env old_mod in
               (env,m::new_mods))
          (env,[])
          modules
      in
      let consts' = T.extend_consts targ consts transformed_m in
      let transformed_m' = T.rename_def_params targ consts' transformed_m in
        output libpath isa_thy targ (avoid consts') def_info (List.rev transformed_m') alldoc_accum alldoc_inc_accum alldoc_inc_usage_accum
    with
      | Trans.Trans_error(l,msg) ->
          raise (Reporting_basic.Fatal_error (Reporting_basic.Err_trans (l, msg)))
      | Ident.No_type(l,msg) ->
          raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal (l, msg)))
      | Typed_ast.Renaming_error(ls,msg) ->
          raise (Reporting_basic.Fatal_error (Reporting_basic.Err_rename (ls, msg)))


let main () =
  let _ = if !opt_print_version then print_string ("Lem " ^ Version.v ^ "\n") in
  let lib_path =
    match !opt_library with
      | None -> (try
                let lp = Sys.getenv("LEMLIB") in
                if Filename.is_relative lp
                then Filename.concat (Sys.getcwd ()) lp
                else lp
            with
                | Not_found -> raise (Failure("must specify a -lib argument or have a LEMLIB environment variable")))
      | Some lp ->
          if Filename.is_relative lp then
            Filename.concat (Sys.getcwd ()) lp
          else
            lp
  in
  let isa_thy =
    match !isa_theory with
      | None -> Filename.concat lib_path "../isabelle-lib/Lem"
      | Some thy -> thy
  in
  let _ =
    List.iter
      (fun f ->
         try
           if String.compare ".lem" (String.sub f (String.length f - 4) 4) <> 0 then
             raise (Failure("Files must have .lem extension"))
         with
           | Invalid_argument _ ->
             raise (Failure("Files must have .lem extension")))
      (!opt_file_arguments @ !lib @ !ocaml_lib @ !hol_lib @ !isa_lib @ !coq_lib)
  in
  let _ =
    List.iter
      (fun f ->
         if not (Str.string_match (Str.regexp "[A-Za-z]") (Filename.basename f) 0) then
           raise (Failure(".lem filenames must start with a letter")))
      (!opt_file_arguments @ !lib @ !ocaml_lib @ !hol_lib @ !isa_lib @ !coq_lib)
  in
  let init =
    try
      let inchannel = open_in (Filename.concat lib_path "lib_cache") in
      let v = input_value inchannel in
        close_in inchannel;
        v
    with
      | Sys_error _ ->
          let module I = Initial_env.Initial_libs(struct let path = lib_path end) in
          let outchannel = open_out (Filename.concat lib_path "lib_cache") in
            output_value outchannel I.init;
            close_out outchannel;
            I.init
  in
  (* TODO: These should go into the sets of top-level constant names *)
  let init = List.fold_right (Initial_env.add_to_init Typed_ast.Target_hol) !hol_lib init in
  let init = List.fold_right (Initial_env.add_to_init Typed_ast.Target_ocaml) !ocaml_lib init in
  let init = List.fold_right (Initial_env.add_to_init Typed_ast.Target_isa) !isa_lib init in
  let init = List.fold_right (Initial_env.add_to_init Typed_ast.Target_coq) !coq_lib init in

  let consts =
    List.map
      (fun (targ,cL) ->
        let consts = List.fold_left
              (fun s c -> Typed_ast.NameSet.add (Name.from_rope c) s)
              Typed_ast.NameSet.empty
              cL in
         (targ,consts))
      (snd init)
  in
  let type_info : (Types.type_defs * instances) * Typed_ast.env = fst init in
  (* Parse and typecheck all of the .lem sources *)
  let (modules, type_info, _) =
    List.fold_left
      (fun (mods, (def_info,env), previously_processed_modules) (f, add_to_modules) ->
         let ast = parse_file f in
         let f' = Filename.basename (Filename.chop_extension f) in
         let mod_name = String.capitalize f' in
         let mod_name_name = Name.from_rope (Ulib.Text.of_latin1 mod_name) in
         let backend_set =
           List.fold_right
             (fun x s ->
                match x with
                  | None -> s
                  | Some(Typed_ast.Target_tex) -> s
                  | Some(Typed_ast.Target_html) -> s
                  | Some(t) -> Typed_ast.Targetset.add t s)
             !backends
             Typed_ast.Targetset.empty
         in
         let ((tdefs,instances,new_instances),new_env,tast) =
           check_ast backend_set [mod_name_name] (def_info,env) ast
         in
         let md = { Typed_ast.mod_env = new_env; Typed_ast.mod_binding = Path.mk_path [] mod_name_name } in
         let e = { env with Typed_ast.m_env = Typed_ast.Nfmap.insert env.Typed_ast.m_env (mod_name_name,md) } in
         let module_record =
           { Typed_ast.filename = f;
             Typed_ast.module_name = mod_name;
             Typed_ast.predecessor_modules = previously_processed_modules;
             Typed_ast.untyped_ast = ast;
             Typed_ast.typed_ast = tast; }
         in
           if !opt_print_types then
             begin
               (*
               Format.fprintf Format.std_formatter "%s@\nlibrary:@\n" f;
               Typed_ast.pp_env Format.std_formatter (snd type_info);
                *)
               Format.fprintf Format.std_formatter "%s@\nenvironment:@\n" f;
               Typed_ast.pp_env Format.std_formatter new_env;
               Format.fprintf Format.std_formatter "@\ninstances:@\n";
               Typed_ast.pp_instances Format.std_formatter new_instances;
               Format.fprintf Format.std_formatter "@\n@\n"
             end;
           ((if add_to_modules then
             module_record::mods
               else
             mods),
            ((tdefs,instances),e), mod_name::previously_processed_modules))
      ([],type_info,[])
      (* We don't want to add the files in !lib to the resulting module ASTs,
       * because we don't want to put them throught the back end *)
      (List.map (fun x -> (x, false)) (List.rev !lib) @
       List.map (fun x -> (x, true)) !opt_file_arguments)
  in

  (* Check the parsed source and produce warnings for various things. Currently:
     - non-exhaustive and redundant patterns
  *)
  let _ = check_modules type_info modules in

  let alldoc_accum = ref ([] : Ulib.Text.t list) in
  let alldoc_inc_accum = ref ([] : Ulib.Text.t list) in
  let alldoc_inc_usage_accum = ref ([] : Ulib.Text.t list) in
    ignore (List.iter (per_target lib_path isa_thy (List.rev modules) type_info consts alldoc_accum alldoc_inc_accum alldoc_inc_usage_accum) !backends);
    (if List.mem (Some(Typed_ast.Target_tex)) !backends then
       output_alldoc "alldoc" (String.concat " " !opt_file_arguments) alldoc_accum alldoc_inc_accum alldoc_inc_usage_accum)

let _ =
  try
    begin
      try ignore(main ())
      with  Failure(s) -> raise (Reporting_basic.err_general false Ast.Unknown ("Failure "^s))
    end
  with Reporting_basic.Fatal_error e -> Reporting_basic.report_error e

*)

let lib = ref []
let opt_print_version = ref false
let opt_print_verbose = ref false
let opt_print_lem = ref false
let opt_file_arguments = ref ([]:string list)
let options = Arg.align ([
  ( "-i",
    Arg.String (fun l -> lib := l::!lib),
    " treat the file as input only and generate no output for it");
  (*( "-tex",
    Arg.Unit (fun b -> if not (List.mem (Some(Typed_ast.Target_tex)) !backends) then
                backends := Some(Typed_ast.Target_tex)::!backends),
    " generate LaTeX");
  ( "-html",
    Arg.Unit (fun b -> if not (List.mem (Some(Typed_ast.Target_html)) !backends) then
                backends := Some(Typed_ast.Target_html)::!backends),
    " generate Html");
  ( "-ident",
    Arg.Unit (fun b -> if not (List.mem None !backends) then
                backends := None::!backends),
    " generate input on stdout");*)
  ( "-verbose",
    Arg.Unit (fun b -> opt_print_verbose := true),
    " pretty-print out the file");
  ( "-lem_ast",
    Arg.Unit (fun b -> opt_print_lem := true),
    " pretty-print a Lem AST representation of the file");
  ( "-skip_constraints",
    Arg.Clear Type_internal.do_resolve_constraints,
    " skip constraint resolution in type-checking");
  ( "-v",
    Arg.Unit (fun b -> opt_print_version := true),
    " print version");
] )

let usage_msg =
    ("L2 " ^ "pre alpha" ^ "\n"
     ^ "example usage:       l2 test.ltwo\n"
    )

let _ =
  Arg.parse options
    (fun s ->
      opt_file_arguments := (!opt_file_arguments) @ [s])
    usage_msg

let main() =
  if !(opt_print_version)
  then Printf.printf "L2 private release \n"
  else let parsed = (List.map (fun f -> (f,(parse_file f)))  !opt_file_arguments) in
       let merged_asts = 
	 List.fold_right (fun (_,(Parse_ast.Defs ast_nodes)) (Parse_ast.Defs later_nodes) 
	 -> Parse_ast.Defs (ast_nodes@later_nodes)) parsed (Parse_ast.Defs []) in
       let (ast,kenv,ord) = convert_ast merged_asts in
       let chkedast = check_ast ast kenv ord in 
       (*let _ = Printf.eprintf "Type checked, next to pretty print" in*)
       begin 
	 (if !(opt_print_verbose)
	  then ((Pretty_print.pp_defs stdout) chkedast)
	  else ());
	 (if !(opt_print_lem)
	  then output "" Lem_ast_out [(fst (List.hd parsed)),chkedast]
	  else ());
       end

let _ =  try
    begin
      try ignore(main ())
      with  Failure(s) -> raise (Reporting_basic.err_general Parse_ast.Unknown ("Failure "^s))
    end
  with Reporting_basic.Fatal_error e -> Reporting_basic.report_error e
