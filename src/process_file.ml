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

open PPrint
open Pretty_print_common

let opt_lem_output_dir = ref None
let opt_isa_output_dir = ref None
let opt_coq_output_dir = ref None

type out_type =
  | Lem_out of string list
  | Coq_out of string list

let get_lexbuf f =
  let in_chan = open_in f in
  let lexbuf = Lexing.from_channel in_chan in
  lexbuf.Lexing.lex_curr_p <- { Lexing.pos_fname = f;
                                Lexing.pos_lnum = 1;
                                Lexing.pos_bol = 0;
                                Lexing.pos_cnum = 0; };
  lexbuf, in_chan

let parse_file ?loc:(l=Parse_ast.Unknown) (f : string) : Parse_ast.defs =
  let open Reporting in
  try
    let lexbuf, in_chan = get_lexbuf f in
    begin
      try
        let ast = Parser.file Lexer.token lexbuf in
        close_in in_chan; ast
      with
      | Parser.Error ->
         let pos = Lexing.lexeme_start_p lexbuf in
         let tok = Lexing.lexeme lexbuf in
         raise (Fatal_error (Err_syntax (pos, "current token: " ^ tok)))
      | Lexer.LexError(s,p) ->
         raise (Fatal_error (Err_lex (p, s)))
    end
  with
  | Sys_error err -> raise (err_general l err)

(* Simple preprocessor features for conditional file loading *)
module StringSet = Set.Make(String)

let symbols = ref StringSet.empty

let cond_pragma l defs =
  let depth = ref 0 in
  let in_then = ref true in
  let then_defs = ref [] in
  let else_defs = ref [] in

  let push_def def =
    if !in_then then
      then_defs := (def :: !then_defs)
    else
      else_defs := (def :: !else_defs)
  in

  let rec scan = function
    | Parse_ast.DEF_pragma ("endif", _, _) :: defs when !depth = 0 ->
       (List.rev !then_defs, List.rev !else_defs, defs)
    | Parse_ast.DEF_pragma ("else", _, _) :: defs when !depth = 0 ->
       in_then := false; scan defs
    | (Parse_ast.DEF_pragma (p, _, _) as def) :: defs when p = "ifdef" || p = "ifndef" ->
       incr depth; push_def def; scan defs
    | (Parse_ast.DEF_pragma ("endif", _, _) as def) :: defs->
       decr depth; push_def def; scan defs
    | def :: defs ->
       push_def def; scan defs
    | [] -> raise (Reporting.err_general l "$ifdef or $ifndef never ended by $endif")
  in
  scan defs

let astid_to_string (Ast.Id_aux (id, _)) =
  match id with
  | Ast.Id x | Ast.DeIid x -> x

let parseid_to_string (Parse_ast.Id_aux (id, _)) =
  match id with
  | Parse_ast.Id x | Parse_ast.DeIid x -> x

let rec realise_union_anon_rec_types orig_union arms =
  match orig_union with
  | Parse_ast.TD_variant (union_id, name_scm_opt, typq, _, flag) ->
     begin match arms with
     | [] -> []
     | arm :: arms ->
        match arm with
        | (Parse_ast.Tu_aux ((Parse_ast.Tu_ty_id _), _)) -> (None, arm) :: realise_union_anon_rec_types orig_union arms
        | (Parse_ast.Tu_aux ((Parse_ast.Tu_ty_anon_rec (fields, id)), l)) ->
           let open Parse_ast in
           let record_str = "_" ^ parseid_to_string union_id ^ "_" ^ parseid_to_string id ^ "_record" in
           let record_id = Id_aux (Id record_str, Generated l) in
           let new_arm = Tu_aux ((Tu_ty_id ((ATyp_aux (ATyp_id record_id, Generated l)), id)), Generated l) in
           let new_rec_def = DEF_type (TD_aux (TD_record (record_id, name_scm_opt, typq, fields, flag), Generated l)) in
           (Some new_rec_def, new_arm) :: (realise_union_anon_rec_types orig_union arms)
     end
  | _ ->
     raise (Reporting.err_unreachable Parse_ast.Unknown __POS__ "Non union type-definition passed to realise_union_anon_rec_typs")

let rec preprocess opts = function
  | [] -> []
  | Parse_ast.DEF_pragma ("define", symbol, _) :: defs ->
     symbols := StringSet.add symbol !symbols;
     preprocess opts defs

  | Parse_ast.DEF_pragma ("option", command, l) :: defs ->
     begin
       try
         let args = Str.split (Str.regexp " +") command in
         Arg.parse_argv ~current:(ref 0) (Array.of_list ("sail" :: args)) opts (fun _ -> ()) "";
       with
       | Arg.Bad message | Arg.Help message -> raise (Reporting.err_general l message)
     end;
     preprocess opts defs

  | Parse_ast.DEF_pragma ("ifndef", symbol, l) :: defs ->
     let then_defs, else_defs, defs = cond_pragma l defs in
     if not (StringSet.mem symbol !symbols) then
       preprocess opts (then_defs @ defs)
     else
       preprocess opts (else_defs @ defs)

  | Parse_ast.DEF_pragma ("ifdef", symbol, l) :: defs ->
     let then_defs, else_defs, defs = cond_pragma l defs in
     if StringSet.mem symbol !symbols then
       preprocess opts (then_defs @ defs)
     else
       preprocess opts (else_defs @ defs)

  | Parse_ast.DEF_pragma ("include", file, l) :: defs ->
     let len = String.length file in
     if len = 0 then
       (Util.warn "Skipping bad $include. No file argument."; preprocess opts defs)
     else if file.[0] = '"' && file.[len - 1] = '"' then
       let relative = match l with
         | Parse_ast.Range (pos, _) -> Filename.dirname (Lexing.(pos.pos_fname))
         | _ -> failwith "Couldn't figure out relative path for $include. This really shouldn't ever happen."
       in
       let file = String.sub file 1 (len - 2) in
       let (Parse_ast.Defs include_defs) = parse_file ~loc:l (Filename.concat relative file) in
       let include_defs = preprocess opts include_defs in
       include_defs @ preprocess opts defs
     else if file.[0] = '<' && file.[len - 1] = '>' then
       let file = String.sub file 1 (len - 2) in
       let sail_dir =
         try Sys.getenv "SAIL_DIR" with
         | Not_found ->
            let share_dir = Share_directory.d in
            if Sys.file_exists share_dir then
              share_dir
            else
              (failwith ("Library directory " ^ share_dir ^ " does not exist. Make sure sail is installed or try setting environment variable SAIL_DIR so that I can find $include " ^ file))
       in
       let file = Filename.concat sail_dir ("lib/" ^ file) in
       let (Parse_ast.Defs include_defs) = parse_file ~loc:l file in
       let include_defs = preprocess opts include_defs in
       include_defs @ preprocess opts defs
     else
       let help = "Make sure the filename is surrounded by quotes or angle brackets" in
       (Util.warn ("Skipping bad $include " ^ file ^ ". " ^ help); preprocess opts defs)

  | Parse_ast.DEF_pragma (p, arg, l) :: defs ->
     Parse_ast.DEF_pragma (p, arg, l) :: preprocess opts defs

  (* realise any anonymous record arms of variants *)
  | Parse_ast.DEF_type (Parse_ast.TD_aux
                          (Parse_ast.TD_variant (id, name_scm_opt, typq, arms, flag) as union, l)
                       ) :: defs ->
     let records_and_arms = realise_union_anon_rec_types union arms in
     let rec filter_records = function [] -> []
                                 | Some x :: xs -> x :: filter_records xs
                                 | None :: xs -> filter_records xs
     in
     let generated_records = filter_records (List.map fst records_and_arms) in
     let rewritten_arms = List.map snd records_and_arms in
     let rewritten_union = Parse_ast.TD_variant (id, name_scm_opt, typq, rewritten_arms, flag) in
     generated_records @ (Parse_ast.DEF_type (Parse_ast.TD_aux (rewritten_union, l))) :: preprocess opts defs

  | (Parse_ast.DEF_default (Parse_ast.DT_aux (Parse_ast.DT_order (_, Parse_ast.ATyp_aux (atyp, _)), _)) as def) :: defs ->
     begin match atyp with
     | Parse_ast.ATyp_inc -> symbols := StringSet.add "_DEFAULT_INC" !symbols; def :: preprocess opts defs
     | Parse_ast.ATyp_dec -> symbols := StringSet.add "_DEFAULT_DEC" !symbols; def :: preprocess opts defs
     | _ -> def :: preprocess opts defs
     end

  | def :: defs -> def :: preprocess opts defs

let preprocess_ast opts (Parse_ast.Defs defs) = Parse_ast.Defs (preprocess opts defs)

let convert_ast (order : Ast.order) (defs : Parse_ast.defs) : unit Ast.defs = Initial_check.process_ast order defs

let load_file_no_check opts order f = convert_ast order (preprocess_ast opts (parse_file f))

let load_file opts order env f =
  let ast = convert_ast order (preprocess_ast opts (parse_file f)) in
  Type_error.check env ast

let opt_just_check = ref false
let opt_ddump_tc_ast = ref false
let opt_ddump_rewrite_ast = ref None
let opt_dno_cast = ref false

let check_ast (env : Type_check.Env.t) (defs : unit Ast.defs) : Type_check.tannot Ast.defs * Type_check.Env.t =
  let env = if !opt_dno_cast then Type_check.Env.no_casts env else env in
  let ast, env = Type_error.check env defs in
  let () = if !opt_ddump_tc_ast then Pretty_print_sail.pp_defs stdout ast else () in
  let () = if !opt_just_check then exit 0 else () in
  (ast, env)


let open_output_with_check opt_dir file_name =
  let (temp_file_name, o) = Filename.open_temp_file "ll_temp" "" in
  let o' = Format.formatter_of_out_channel o in
  (o', (o, temp_file_name, opt_dir, file_name))

let open_output_with_check_unformatted opt_dir file_name =
  let (temp_file_name, o) = Filename.open_temp_file "ll_temp" "" in
  (o, temp_file_name, opt_dir, file_name)

let always_replace_files = ref true

let close_output_with_check (o, temp_file_name, opt_dir, file_name) =
  let _ = close_out o in
  let file_name = match opt_dir with
                  | None     -> file_name
                  | Some dir -> if Sys.file_exists dir then ()
                                else Unix.mkdir dir 0o775;
                                Filename.concat dir file_name in
  let do_replace = !always_replace_files || (not (Util.same_content_files temp_file_name file_name)) in
  let _ = if (not do_replace) then Sys.remove temp_file_name
          else Util.move_file temp_file_name file_name in
  ()

let generated_line f =
  Printf.sprintf "Generated by Sail from %s." f

let output_lem filename libs defs =
  let generated_line = generated_line filename in
  (* let seq_suffix = if !Pretty_print_lem.opt_sequential then "_sequential" else "" in *)
  let types_module = (filename ^ "_types") in
  let monad_modules = ["Sail2_prompt_monad"; "Sail2_prompt"] in
  let operators_module =
    if !Pretty_print_lem.opt_mwords
    then "Sail2_operators_mwords"
    else "Sail2_operators_bitlists" in
  (* let libs = List.map (fun lib -> lib ^ seq_suffix) libs in *)
  let base_imports = [
      "Pervasives_extra";
      "Sail2_instr_kinds";
      "Sail2_values";
      "Sail2_string";
      operators_module
    ] @ monad_modules
  in
  let isa_thy_name = String.capitalize_ascii filename ^ "_lemmas" in
  let isa_lemmas =
    separate hardline [
      string ("theory " ^ isa_thy_name);
      string  "  imports";
      string  "    Sail.Sail2_values_lemmas";
      string  "    Sail.Sail2_state_lemmas";
      string ("    " ^ String.capitalize_ascii filename);
      string  "begin";
      string  "";
      State.generate_isa_lemmas !Pretty_print_lem.opt_mwords defs;
      string  "";
      string  "end"
    ] ^^ hardline
  in
  let ((ot,_,_,_) as ext_ot) =
    open_output_with_check_unformatted !opt_lem_output_dir (filename ^ "_types" ^ ".lem") in
  let ((o,_,_,_) as ext_o) =
    open_output_with_check_unformatted !opt_lem_output_dir (filename ^ ".lem") in
  (Pretty_print.pp_defs_lem
     (ot, base_imports)
     (o, base_imports @ (String.capitalize_ascii types_module :: libs))
     defs generated_line);
  close_output_with_check ext_ot;
  close_output_with_check ext_o;
  let ((ol,_,_,_) as ext_ol) =
    open_output_with_check_unformatted !opt_isa_output_dir (isa_thy_name ^ ".thy") in
  print ol isa_lemmas;
  close_output_with_check ext_ol

let output_coq opt_dir filename libs defs =
  let generated_line = generated_line filename in
  let types_module = (filename ^ "_types") in
  let monad_modules = ["Sail2_prompt_monad"; "Sail2_prompt"; "Sail2_state"] in
  let operators_module = "Sail2_operators_mwords" in
  let base_imports = [
      "Sail2_instr_kinds";
      "Sail2_values";
      "Sail2_string";
      "Sail2_real";
      operators_module
    ] @ monad_modules
  in
  let ((ot,_,_,_) as ext_ot) =
    open_output_with_check_unformatted opt_dir (filename ^ "_types" ^ ".v") in
  let ((o,_,_,_) as ext_o) =
    open_output_with_check_unformatted opt_dir (filename ^ ".v") in
  (Pretty_print_coq.pp_defs_coq
     (ot, base_imports)
     (o, base_imports @ (types_module :: libs))
     defs generated_line);
  close_output_with_check ext_ot;
  close_output_with_check ext_o

let rec iterate (f : int -> unit) (n : int) : unit =
  if n = 0 then ()
  else (f n; iterate f (n - 1))

let output1 libpath out_arg filename defs  =
  let f' = Filename.basename (Filename.chop_extension filename) in
  match out_arg with
  | Lem_out libs ->
     output_lem f' libs defs
  | Coq_out libs ->
     output_coq !opt_coq_output_dir f' libs defs

let output libpath out_arg files =
  List.iter
    (fun (f, defs) ->
      output1 libpath out_arg f defs)
    files

let rewrite_step defs (name, rewriter) =
  let t = Profile.start () in
  let defs = rewriter defs in
  Profile.finish ("rewrite " ^ name) t;
  let _ = match !(opt_ddump_rewrite_ast) with
    | Some (f, i) ->
      begin
        let filename = f ^ "_rewrite_" ^ string_of_int i ^ "_" ^ name ^ ".sail" in
        (* output "" Lem_ast_out [filename, defs]; *)
        let ((ot,_,_,_) as ext_ot) = open_output_with_check_unformatted None filename in
        Pretty_print_sail.pp_defs ot defs;
        close_output_with_check ext_ot;
        opt_ddump_rewrite_ast := Some (f, i + 1)
      end
    | _ -> () in
  defs

let rewrite rewriters defs =
  try List.fold_left rewrite_step defs rewriters with
  | Type_check.Type_error (l, err) ->
     raise (Reporting.err_typ l (Type_error.string_of_type_error err))

let rewrite_ast = rewrite [("initial", Rewriter.rewrite_defs)]
let rewrite_ast_lem = rewrite Rewrites.rewrite_defs_lem
let rewrite_ast_coq = rewrite Rewrites.rewrite_defs_coq
let rewrite_ast_ocaml = rewrite Rewrites.rewrite_defs_ocaml
let rewrite_ast_c ast =
  ast
  |> rewrite Rewrites.rewrite_defs_c
  |> rewrite [("constant_fold", Constant_fold.rewrite_constant_function_calls)]

let rewrite_ast_interpreter = rewrite Rewrites.rewrite_defs_interpreter
let rewrite_ast_check = rewrite Rewrites.rewrite_defs_check
