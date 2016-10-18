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

let lib = ref []
let opt_file_out : string option ref = ref None
let opt_print_version = ref false
let opt_print_verbose = ref false
let opt_print_lem_ast = ref false
let opt_print_lem = ref false
let opt_print_ocaml = ref false
let opt_libs_lem = ref ([]:string list)
let opt_libs_ocaml = ref ([]:string list)
let opt_file_arguments = ref ([]:string list)
let options = Arg.align ([
  ( "-i",
    Arg.String (fun l -> lib := l::!lib),
    " treat the file as input only and generate no output for it");
  ( "-verbose",
    Arg.Set opt_print_verbose,
    " pretty-print out the file");
  ( "-lem_ast",
    Arg.Set opt_print_lem_ast,
    " pretty-print a Lem AST representation of the file");
  ( "-lem",
    Arg.Set opt_print_lem,
    " print a Lem translated version of the specification");
  ( "-ocaml",
    Arg.Set opt_print_ocaml,
    " print an Ocaml translated version of the specification");
  ( "-skip_constraints",
    Arg.Clear Type_internal.do_resolve_constraints,
    " skip constraint resolution in type-checking");
  ( "-lem_lib",
    Arg.String (fun l -> opt_libs_lem := l::!opt_libs_lem),
    " provide additional library to open in Lem output");
  ( "-ocaml_lib",
    Arg.String (fun l -> opt_libs_ocaml := l::!opt_libs_ocaml),
    " provide additional library to open in Ocaml output");
  ( "-v",
    Arg.Set opt_print_version,
    " print version");
  ( "-o",
    Arg.String (fun f -> opt_file_out := Some f),
    " select output filename prefix";)
] )

let usage_msg =
    ("Sail " ^ "pre beta" ^ "\n"
     ^ "example usage:       sail test.sail\n"
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
       else ())
    end

let _ =  try
    begin
      try ignore(main ())
      with  Failure(s) -> raise (Reporting_basic.err_general Parse_ast.Unknown ("Failure "^s))
    end
  with Reporting_basic.Fatal_error e -> Reporting_basic.report_error e
