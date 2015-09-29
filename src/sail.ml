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
let opt_print_version = ref false
let opt_print_verbose = ref false
let opt_print_lem = ref false
let opt_print_ocaml = ref false
let opt_libs_ocaml = ref ([]:string list)
let opt_file_arguments = ref ([]:string list)
let options = Arg.align ([
  ( "-i",
    Arg.String (fun l -> lib := l::!lib),
    " treat the file as input only and generate no output for it");
  ( "-verbose",
    Arg.Unit (fun b -> opt_print_verbose := true),
    " pretty-print out the file");
  ( "-lem_ast",
    Arg.Unit (fun b -> opt_print_lem := true),
    " pretty-print a Lem AST representation of the file");
  ( "-ocaml",
    Arg.Unit (fun b -> opt_print_ocaml := true),
    " print an Ocaml translated version of the specification");
  ( "-skip_constraints",
    Arg.Clear Type_internal.do_resolve_constraints,
    " skip constraint resolution in type-checking");
  ( "-ocaml_lib",
    Arg.String (fun l -> opt_libs_ocaml := l::!opt_libs_ocaml),
    " provide additional library to open in Ocaml output");
  ( "-v",
    Arg.Unit (fun b -> opt_print_version := true),
    " print version");
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
    let ast = check_ast ast kenv ord in 
    let ast = rewrite_ast ast in
    (*let _ = Printf.eprintf "Type checked, next to pretty print" in*)
    begin 
      (if !(opt_print_verbose)
       then ((Pretty_print.pp_defs stdout) ast)
       else ());
      (if !(opt_print_lem)
       then output "" Lem_ast_out [(fst (List.hd parsed)),ast]
       else ());
      (if !(opt_print_ocaml)
       then let ast_ocaml = rewrite_ast_ocaml ast in
         if !(opt_libs_ocaml) = []
         then output "" (Ocaml_out None) [(fst (List.hd parsed)),ast_ocaml]
         else output "" (Ocaml_out (Some (List.hd !opt_libs_ocaml))) [(fst (List.hd parsed)),ast_ocaml]
       else ());
    end

let _ =  try
    begin
      try ignore(main ())
      with  Failure(s) -> raise (Reporting_basic.err_general Parse_ast.Unknown ("Failure "^s))
    end
  with Reporting_basic.Fatal_error e -> Reporting_basic.report_error e
