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

let lib = ref ([] : string list)
let opt_file_out : string option ref = ref None
let opt_print_version = ref false
let opt_print_initial_env = ref false
let opt_print_verbose = ref false
let opt_print_lem_ast = ref false
let opt_print_lem = ref false
let opt_print_ocaml = ref false
let opt_libs_lem = ref ([]:string list)
let opt_libs_ocaml = ref ([]:string list)
let opt_file_arguments = ref ([]:string list)
let opt_mono_split = ref ([]:((string * int) * string) list)
let options = Arg.align ([
  ( "-o",
    Arg.String (fun f -> opt_file_out := Some f),
    "<prefix> select output filename prefix");
  ( "-lem_ast",
    Arg.Set opt_print_lem_ast,
    " output a Lem AST representation of the input");
  ( "-lem",
    Arg.Set opt_print_lem,
    " output a Lem translated version of the input");
  ( "-ocaml",
    Arg.Tuple [Arg.Set opt_print_ocaml; Arg.Set Initial_check.opt_undefined_gen],
    " output an OCaml translated version of the input");
  ( "-lem_lib",
    Arg.String (fun l -> opt_libs_lem := l::!opt_libs_lem),
    "<filename> provide additional library to open in Lem output");
  ( "-ocaml_lib",
    Arg.String (fun l -> opt_libs_ocaml := l::!opt_libs_ocaml),
    "<filename> provide additional library to open in OCaml output");
  ( "-lem_sequential",
    Arg.Set Process_file.opt_lem_sequential,
    " use sequential state monad for Lem output");
  ( "-lem_mwords",
    Arg.Set Process_file.opt_lem_mwords,
    " use native machine word library for Lem output");
(*
  ( "-i",
    Arg.String (fun l -> lib := l::!lib),
    "<library_filename> treat this file as input only and generate no output for it");
*)
  ( "-verbose",
    Arg.Set opt_print_verbose,
    " (debug) pretty-print the input to standard output");
  ( "-mono-split",
    Arg.String (fun s ->
      let l = Util.split_on_char ':' s in
      match l with
      | [fname;line;var] -> opt_mono_split := ((fname,int_of_string line),var)::!opt_mono_split
      | _ -> raise (Arg.Bad (s ^ " not of form <filename>:<line>:<variable>"))),
      "<filename>:<line>:<variable> to case split for monomorphisation");
  ( "-new_parser",
    Arg.Set Process_file.opt_new_parser,
    " (experimental) use new parser");
  ( "-just_check",
    Arg.Set opt_just_check,
    " (experimental) terminate immediately after typechecking");
  ( "-ddump_tc_ast",
    Arg.Set opt_ddump_tc_ast,
    " (debug) dump the typechecked ast to stdout");
  ( "-ddump_rewrite_ast",
    Arg.String (fun l -> opt_ddump_rewrite_ast := Some (l, 0)),
    " <prefix> (debug) dump the ast after each rewriting step to <prefix>_<i>.lem");
  ( "-dtc_verbose",
    Arg.Int (fun verbosity -> Type_check.opt_tc_debug := verbosity),
    " (debug) verbose typechecker output: 0 is silent");
  ( "-dno_cast",
    Arg.Set opt_dno_cast,
    " (debug) typecheck without any implicit casting");
  ( "-no_effects",
    Arg.Set Type_check.opt_no_effects,
    " turn off effect checking");
  ( "-undefined_gen",
    Arg.Set Initial_check.opt_undefined_gen,
    " generate undefined_type functions for types in the specification");
  ( "-v",
    Arg.Set opt_print_version,
    " print version");
] )

let usage_msg =
    ("Sail " (*^ "pre beta"*) ^ "\n"
     ^ "usage:       sail <options> <file1.sail> .. <fileN.sail>\n"
    )

let _ =
  Arg.parse options
    (fun s ->
      opt_file_arguments := (!opt_file_arguments) @ [s])
    usage_msg


let main() =
  if !(opt_print_version)
  then Printf.printf "Sail private release \n"
  else

    let parsed = (List.map (fun f -> (f,(parse_file f)))  !opt_file_arguments) in
    let ast =
      List.fold_right (fun (_,(Parse_ast.Defs ast_nodes)) (Parse_ast.Defs later_nodes) 
                        -> Parse_ast.Defs (ast_nodes@later_nodes)) parsed (Parse_ast.Defs []) in
    let ast = convert_ast Ast_util.inc_ord ast in
    let (ast, type_envs) = check_ast ast in

    let (ast, type_envs) =
      match !opt_mono_split with
      | [] -> ast, type_envs
      | locs -> monomorphise_ast locs ast
    in

    let ast = rewrite_ast ast in
    let out_name = match !opt_file_out with
      | None -> fst (List.hd parsed)
      | Some f -> f ^ ".sail" in
    (*let _ = Printf.eprintf "Type checked, next to pretty print" in*)
    begin
      (if !(opt_print_verbose)
       then ((Pretty_print.pp_defs stdout) ast)
       else ());
      (if !(opt_print_lem_ast)
       then output "" Lem_ast_out [out_name,ast]
       else ());
      (if !(opt_print_ocaml)
       then
         let ast_ocaml = rewrite_ast_ocaml ast in
         let out = match !opt_file_out with None -> "out" | Some s -> s in
         Ocaml_backend.ocaml_compile out ast_ocaml
       else ());
      (if !(opt_print_lem)
       then let ast_lem = rewrite_ast_lem ast in
         if !(opt_libs_lem) = []
         then output "" (Lem_out None) [out_name,ast_lem]
         else output "" (Lem_out (Some (List.hd !opt_libs_lem))) [out_name,ast_lem]
       else ());
    end

let _ =  try
    begin
      try ignore(main ())
      with  Failure(s) -> raise (Reporting_basic.err_general Parse_ast.Unknown ("Failure "^s))
    end
  with Reporting_basic.Fatal_error e -> Reporting_basic.report_error e
