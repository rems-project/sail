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

open Sail

open Ast
open Ast_util
open Interpreter
open Pretty_print_sail2

type mode =
  | Evaluation of frame
  | Normal

let current_mode = ref Normal

let prompt () =
  match !current_mode with
  | Normal -> "sail> "
  | Evaluation _ -> "eval> "

let mode_clear () =
  match !current_mode with
  | Normal -> ()
  | Evaluation _ -> LNoise.clear_screen ()

let rec user_input callback =
  match LNoise.linenoise (prompt ()) with
  | None -> ()
  | Some v ->
     mode_clear ();
     callback v;
     user_input callback

let termcode n = "\x1B[" ^ string_of_int n ^ "m"
let bold str = termcode 1 ^ str
let red str = termcode 91 ^ str
let clear str = str ^ termcode 0

let sail_logo =
  let banner str = str |> bold |> red |> clear in
  [ "    ___       ___       ___       ___ ";
    "   /\\  \\     /\\  \\     /\\  \\     /\\__\\";
    "  /::\\  \\   /::\\  \\   _\\:\\  \\   /:/  /";
    " /\\:\\:\\__\\ /::\\:\\__\\ /\\/::\\__\\ /:/__/ ";
    " \\:\\:\\/__/ \\/\\::/  / \\::/\\/__/ \\:\\  \\ ";
    "  \\::/  /    /:/  /   \\:\\__\\    \\:\\__\\";
    "   \\/__/     \\/__/     \\/__/     \\/__/";
    ""
  ]
  |> List.map banner

let vs_ids = ref (Initial_check.val_spec_ids !interactive_ast)

let handle_input input =
  match !current_mode with
  | Normal ->
     begin
       LNoise.history_add input |> ignore;

       if input <> "" && input.[0] = ':' then
         let n = try String.index input ' ' with Not_found -> String.length input in
         let cmd = Str.string_before input n in
         let arg = String.trim (Str.string_after input n) in
         match cmd with
         | ":t" | ":type" ->
            let typq, typ = Type_check.Env.get_val_spec (mk_id arg) !interactive_env in
            pretty_sail stdout (doc_binding (typq, typ));
            print_newline ();
         | ":q" | ":quit" ->
            exit 0
         | ":i" | ":infer" ->
            let exp = Initial_check.exp_of_string dec_ord arg in
            let exp = Type_check.infer_exp !interactive_env exp in
            pretty_sail stdout (doc_typ (Type_check.typ_of exp));
            print_newline ()
         | ":v" | ":verbose" ->
            Type_check.opt_tc_debug := (!Type_check.opt_tc_debug + 1) mod 2

         | _ -> print_endline ("Unrecognised command " ^ input)
       else if input <> "" then
         let exp = Type_check.infer_exp !interactive_env (Initial_check.exp_of_string Ast_util.dec_ord input) in
         current_mode := Evaluation (eval_frame !interactive_ast (Step ("", initial_state !interactive_ast, return exp, [])))
       else ()
     end
  | Evaluation frame ->
     begin
       match frame with
       | Done (_, v) ->
          print_endline ("Result = " ^ Value.string_of_value v);
          current_mode := Normal
       | Step (out, _, _, stack) ->
          let sep = "-----------------------------------------------------" |> Util.blue |> Util.clear in
          List.map stack_string stack |> List.rev |> List.iter (fun code -> print_endline code; print_endline sep);
          print_endline out;
          current_mode := Evaluation (eval_frame !interactive_ast frame)
     end



let () =
  List.iter print_endline sail_logo;

  (* Auto complete function names based on val specs *)
  LNoise.set_completion_callback
    begin
      fun line_so_far ln_completions ->
      let line_so_far, last_id =
        try
          let p = Str.search_backward (Str.regexp "[^a-zA-Z0-9_]") line_so_far (String.length line_so_far - 1) in
          Str.string_before line_so_far (p + 1), Str.string_after line_so_far (p + 1)
        with
        | Not_found -> "", line_so_far
        | Invalid_argument _ -> line_so_far, ""
      in
      if last_id <> "" then
        IdSet.elements !vs_ids
        |> List.map string_of_id
        |> List.filter (fun id -> Str.string_match (Str.regexp_string last_id) id 0)
        |> List.map (fun completion -> line_so_far ^ completion)
        |> List.iter (LNoise.add_completion ln_completions)
      else ()
  end;

  LNoise.history_load ~filename:"sail_history" |> ignore;
  LNoise.history_set ~max_length:100 |> ignore;

  if !opt_interactive then
    user_input handle_input
  else ()
