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
    Arg.Set opt_print_ocaml,
    " output an OCaml translated version of the input");
  ( "-lem_lib",
    Arg.String (fun l -> opt_libs_lem := l::!opt_libs_lem),
    "<filename> provide additional library to open in Lem output");
  ( "-ocaml_lib",
    Arg.String (fun l -> opt_libs_ocaml := l::!opt_libs_ocaml),
    "<filename> provide additional library to open in OCaml output");
(*
  ( "-i",
    Arg.String (fun l -> lib := l::!lib),
    "<library_filename> treat this file as input only and generate no output for it");
*)
  ( "-print_initial_env",
    Arg.Set opt_print_initial_env,
    " print the built-in initial type environment and terminate");
  ( "-verbose",
    Arg.Set opt_print_verbose,
    " (debug) pretty-print the input to standard output");
  ( "-skip_constraints",
    Arg.Clear Type_internal.do_resolve_constraints,
    " (debug) skip constraint resolution in type-checking");
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
  else if !(opt_print_initial_env) then
    let ppd_initial_typ_env = 
      String.concat "" 
        (List.map
           (function (comment,tenv) -> 
             "(* "^comment^" *)\n" ^ 
             String.concat ""
               (List.map 
                  (function (id,tannot) ->
                    id ^ " : " ^ 
                    Pretty_print.pp_format_annot_ascii tannot 
                    ^ "\n")
                  tenv))
           Type_internal.initial_typ_env_list) in
    Printf.printf "%s" ppd_initial_typ_env ;
  else    

    let parsed = (List.map (fun f -> (f,(parse_file f)))  !opt_file_arguments) in
    let ast = 
      List.fold_right (fun (_,(Parse_ast.Defs ast_nodes)) (Parse_ast.Defs later_nodes) 
                        -> Parse_ast.Defs (ast_nodes@later_nodes)) parsed (Parse_ast.Defs []) in
    let (ast,kenv,ord) = convert_ast ast in
    let (ast,type_envs) = check_ast ast kenv ord in 
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
       then let ast_ocaml = rewrite_ast_ocaml ast in
         if !(opt_libs_ocaml) = []
         then output "" (Ocaml_out None) [out_name,ast_ocaml]
         else output "" (Ocaml_out (Some (List.hd !opt_libs_ocaml))) [out_name,ast_ocaml]
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
