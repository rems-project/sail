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
open Pretty_print_sail

type mode =
  | Evaluation of frame
  | Bytecode of Value2.vl Bytecode_interpreter.gstate * Value2.vl Bytecode_interpreter.stack
  | Normal

let current_mode = ref Normal

let prompt () =
  match !current_mode with
  | Normal -> "sail> "
  | Evaluation _ -> "eval> "
  | Bytecode _ -> "ir> "

let eval_clear = ref true

let mode_clear () =
  match !current_mode with
  | Normal -> ()
  | Evaluation _ -> if !eval_clear then LNoise.clear_screen () else ()
  | Bytecode _ -> () (* if !eval_clear then LNoise.clear_screen () else () *)

let rec user_input callback =
  match LNoise.linenoise (prompt ()) with
  | None -> ()
  | Some v ->
     mode_clear ();
     begin
       try callback v with
       | Reporting.Fatal_error e -> Reporting.report_error e
     end;
     user_input callback

let sail_logo =
  let banner str = str |> Util.bold |> Util.red |> Util.clear in
  let logo =
    [ {|    ___       ___       ___       ___ |};
      {|   /\  \     /\  \     /\  \     /\__\|};
      {|  /::\  \   /::\  \   _\:\  \   /:/  /|};
      {| /\:\:\__\ /::\:\__\ /\/::\__\ /:/__/ |};
      {| \:\:\/__/ \/\::/  / \::/\/__/ \:\  \ |};
      {|  \::/  /    /:/  /   \:\__\    \:\__\|};
      {|   \/__/     \/__/     \/__/     \/__/|} ]
  in
  let help =
    [ "Type :commands for a list of commands, and :help <command> for help.";
      "Type expressions to evaluate them." ]
  in
  List.map banner logo @ [""] @ help @ [""]

let vs_ids = ref (Initial_check.val_spec_ids !interactive_ast)

let interactive_state = ref (initial_state !interactive_ast Value.primops)

let interactive_bytecode = ref []

let sep = "-----------------------------------------------------" |> Util.blue |> Util.clear

let print_program () =
  match !current_mode with
  | Normal -> ()
  | Evaluation (Step (out, _, _, stack)) ->
     List.map stack_string stack |> List.rev |> List.iter (fun code -> print_endline (Lazy.force code); print_endline sep);
     print_endline (Lazy.force out)
  | Evaluation (Done (_, v)) ->
     print_endline (Value.string_of_value v |> Util.green |> Util.clear)
  | Evaluation _ -> ()
  | Bytecode (_, stack) ->
     let open Bytecode_interpreter in
     let open Bytecode_util in
     let pc = stack.top.pc in
     let instrs = stack.top.instrs in
     for i = 0 to stack.top.pc - 1 do
       print_endline ("  " ^ Pretty_print_sail.to_string (pp_instr instrs.(i)))
     done;
     print_endline (">>  " ^ Pretty_print_sail.to_string (pp_instr instrs.(stack.top.pc)));
     for i = stack.top.pc + 1 to Array.length instrs - 1 do
       print_endline ("  " ^ Pretty_print_sail.to_string (pp_instr instrs.(i)))
     done;
     print_endline sep;
     print_endline (Util.string_of_list ", "
                     (fun (id, vl) -> Printf.sprintf "%s = %s" (string_of_id id) (string_of_value vl))
                     (Bindings.bindings stack.top.locals))

let rec run () =
  match !current_mode with
  | Normal -> ()
  | Evaluation frame ->
     begin
       match frame with
       | Done (state, v) ->
          interactive_state := state;
          print_endline ("Result = " ^ Value.string_of_value v);
          current_mode := Normal
       | Step (out, state, _, stack) ->
          begin
            try
              current_mode := Evaluation (eval_frame frame)
            with
            | Failure str -> print_endline str; current_mode := Normal
          end;
          run ()
       | Break frame ->
          print_endline "Breakpoint";
          current_mode := Evaluation frame
     end
  | Bytecode _ -> ()

let rec run_steps n =
  print_endline ("step " ^ string_of_int n);
  match !current_mode with
  | _ when n <= 0 -> ()
  | Normal -> ()
  | Evaluation frame ->
     begin
       match frame with
       | Done (state, v) ->
          interactive_state := state;
          print_endline ("Result = " ^ Value.string_of_value v);
          current_mode := Normal
       | Step (out, state, _, stack) ->
          begin
            try
              current_mode := Evaluation (eval_frame frame)
            with
            | Failure str -> print_endline str; current_mode := Normal
          end;
          run_steps (n - 1)
       | Break frame ->
          print_endline "Breakpoint";
          current_mode := Evaluation frame
     end
  | Bytecode _ -> ()

let help = function
  | ":t" | ":type" ->
     "(:t | :type) <function name> - Print the type of a function."
  | ":q" | ":quit" ->
     "(:q | :quit) - Exit the interpreter."
  | ":i" | ":infer" ->
     "(:i | :infer) <expression> - Infer the type of an expression."
  | ":v" | ":verbose" ->
     "(:v | :verbose) - Increase the verbosity level, or reset to zero at max verbosity."
  | ":commands" ->
     ":commands - List all available commands."
  | ":help" ->
     ":help <command> - Get a description of <command>. Commands are prefixed with a colon, e.g. :help :type."
  | ":elf" ->
     ":elf <file> - Load an ELF file."
  | ":r" | ":run" ->
     "(:r | :run) - Completely evaluate the currently evaluating expression."
  | ":s" | ":step" ->
     "(:s | :step) <number> - Perform a number of evaluation steps."
  | ":n" | ":normal" ->
     "(:n | :normal) - Exit evaluation mode back to normal mode."
  | ":clear" ->
     ":clear (on|off) - Set whether to clear the screen or not in evaluation mode."
  | ":l" | ":load" -> String.concat "\n"
     [ "(:l | :load) <files> - Load sail files and add their definitions to the interactive environment.";
       "Files containing scattered definitions must be loaded together." ]
  | ":u" | ":unload" ->
     "(:u | :unload) - Unload all loaded files."
  | ":output" ->
     ":output <file> - Redirect evaluating expression output to a file."
  | ":option" ->
     ":option string - Parse string as if it was an option passed on the command line. Try :option -help."
  | cmd ->
     "Either invalid command passed to help, or no documentation for " ^ cmd ^ ". Try :help :help."


type input = Command of string * string | Expression of string | Empty

(* This function is called on every line of input passed to the interpreter *)
let handle_input' input =
  LNoise.history_add input |> ignore;

  (* Process the input and check if it's a command, a raw expression,
     or empty. *)
  let input =
    if input <> "" && input.[0] = ':' then
      let n = try String.index input ' ' with Not_found -> String.length input in
      let cmd = Str.string_before input n in
      let arg = String.trim (Str.string_after input n) in
      Command (cmd, arg)
    else if input <> "" then
      Expression input
    else
      Empty
  in

  let recognised = ref true in

  let unrecognised_command cmd =
    if !recognised = false then print_endline ("Command " ^ cmd ^ " is not a valid command in this mode.") else ()
  in

  (* First handle commands that are mode-independent *)
  begin
    match input with
    | Command (cmd, arg) ->
       begin
         match cmd with
         | ":n" | ":normal" ->
            current_mode := Normal
         | ":t" | ":type" ->
            let typq, typ = Type_check.Env.get_val_spec (mk_id arg) !interactive_env in
            pretty_sail stdout (doc_binding (typq, typ));
            print_newline ();
         | ":q" | ":quit" ->
            Value.output_close ();
            exit 0
         | ":i" | ":infer" ->
            let exp = Initial_check.exp_of_string arg in
            let exp = Type_check.infer_exp !interactive_env exp in
            pretty_sail stdout (doc_typ (Type_check.typ_of exp));
            print_newline ()
         | ":canon" ->
            let typ = Initial_check.typ_of_string arg in
            print_endline (string_of_typ (Type_check.canonicalize !interactive_env typ))
         | ":v" | ":verbose" ->
            Type_check.opt_tc_debug := (!Type_check.opt_tc_debug + 1) mod 3;
            print_endline ("Verbosity: " ^ string_of_int !Type_check.opt_tc_debug)
         | ":clear" ->
            if arg = "on" then
              eval_clear := true
            else if arg = "off" then
              eval_clear := false
            else print_endline "Invalid argument for :clear, expected either :clear on or :clear off"
         | ":commands" ->
            let commands =
              [ "Universal commands - :(t)ype :(i)nfer :(q)uit :(v)erbose :clear :commands :help :output :option";
                "Normal mode commands - :elf :(l)oad :(u)nload";
                "Evaluation mode commands - :(r)un :(s)tep :(n)ormal";
                "";
                ":(c)ommand can be called as either :c or :command." ]
            in
            List.iter print_endline commands
         | ":poly" ->
            let is_kopt = match arg with
              | "Int" -> is_nat_kopt
              | "Type" -> is_typ_kopt
              | "Order" -> is_order_kopt
              | _ -> failwith "Invalid kind"
            in
            let ids = Specialize.polymorphic_functions is_kopt !interactive_ast in
            List.iter (fun id -> print_endline (string_of_id id)) (IdSet.elements ids)
         | ":option" ->
            begin
              try
                let args = Str.split (Str.regexp " +") arg in
                Arg.parse_argv ~current:(ref 0) (Array.of_list ("sail" :: args)) Sail.options (fun _ -> ()) "";
              with
              | Arg.Bad message | Arg.Help message -> print_endline message
            end;
         | ":spec" ->
            let ast, env = Specialize.specialize !interactive_ast !interactive_env in
            interactive_ast := ast;
            interactive_env := env;
            interactive_state := initial_state !interactive_ast Value.primops
         | ":pretty" ->
            print_endline (Pretty_print_sail.to_string (Latex.defs !interactive_ast))
         | ":compile" ->
            let open PPrint in
            let open C_backend in
            let ast = Process_file.rewrite_ast_c !interactive_ast in
            let ast, env = Specialize.specialize ast !interactive_env in
            let ctx = initial_ctx env in
            interactive_bytecode := bytecode_ast ctx (List.map flatten_cdef) ast
         | ":ir" ->
            print_endline arg;
            let open Bytecode in
            let open Bytecode_util in
            let open PPrint in
            let is_cdef = function
              | CDEF_fundef (id, _, _, _) when Id.compare id (mk_id arg) = 0 -> true
              | CDEF_spec (id, _, _) when Id.compare id (mk_id arg) = 0 -> true
              | _ -> false
            in
            let cdefs = List.filter is_cdef !interactive_bytecode in
            print_endline (Pretty_print_sail.to_string (separate_map hardline pp_cdef cdefs))
         | ":ast" ->
            let chan = open_out arg in
            Pretty_print_sail.pp_defs chan !interactive_ast;
            close_out chan
         | ":output" ->
            let chan = open_out arg in
            Value.output_redirect chan
         | ":help" -> print_endline (help arg)
         | _ -> recognised := false
       end
    | _ -> ()
  end;

  match !current_mode with
  | Normal ->
     begin
       match input with
       | Command (cmd, arg) ->
          (* Normal mode commands *)
          begin
            match cmd with
            | ":elf" -> Elf_loader.load_elf arg
            | ":l" | ":load" ->
               let files = Util.split_on_char ' ' arg in
               let (_, ast, env) = load_files !interactive_env files in
               let ast = Process_file.rewrite_ast_interpreter ast in
               interactive_ast := append_ast !interactive_ast ast;
               interactive_state := initial_state !interactive_ast Value.primops;
               interactive_env := env;
               vs_ids := Initial_check.val_spec_ids !interactive_ast
            | ":u" | ":unload" ->
               interactive_ast := Ast.Defs [];
               interactive_env := Type_check.initial_env;
               interactive_state := initial_state !interactive_ast Value.primops;
               vs_ids := Initial_check.val_spec_ids !interactive_ast;
               (* See initial_check.mli for an explanation of why we need this. *)
               Initial_check.have_undefined_builtins := false
            | ":exec" ->
               let open Bytecode_interpreter in
               let exp = Type_check.infer_exp !interactive_env (Initial_check.exp_of_string arg) in
               let anf = Anf.anf exp in
               let ctx = C_backend.initial_ctx !interactive_env in
               let ctyp = C_backend.ctyp_of_typ ctx (Type_check.typ_of exp) in
               let setup, call, cleanup = C_backend.compile_aexp ctx anf in
               let instrs = C_backend.flatten_instrs (setup @ [call (CL_id (mk_id "interactive#", ctyp))] @ cleanup) in
               current_mode := Bytecode (new_gstate !interactive_bytecode, new_stack instrs);
               print_program ()
            | _ -> unrecognised_command cmd
          end
       | Expression str ->
          (* An expression in normal mode is type checked, then puts
             us in evaluation mode. *)
          let exp = Type_check.infer_exp !interactive_env (Initial_check.exp_of_string str) in
          current_mode := Evaluation (eval_frame (Step (lazy "", !interactive_state, return exp, [])));
          print_program ()
       | Empty -> ()
     end
  | Evaluation frame ->
     begin match input with
     | Command (cmd, arg) ->
        (* Evaluation mode commands *)
        begin
          match cmd with
          | ":r" | ":run" ->
             run ()
          | ":s" | ":step" ->
             run_steps (int_of_string arg)
          | _ -> unrecognised_command cmd
        end
     | Expression str ->
        print_endline "Already evaluating expression"
     | Empty ->
        (* Empty input will evaluate one step, or switch back to
             normal mode when evaluation is completed. *)
        begin match frame with
        | Done (state, v) ->
           interactive_state := state;
           print_endline ("Result = " ^ Value.string_of_value v);
           current_mode := Normal
        | Step (out, state, _, stack) ->
           begin
             try
               interactive_state := state;
               current_mode := Evaluation (eval_frame frame);
               print_program ()
             with
             | Failure str -> print_endline str; current_mode := Normal
           end
        | Break frame ->
           print_endline "Breakpoint";
           current_mode := Evaluation frame
        end
     end
  | Bytecode (gstate, stack) ->
     begin match input with
     | Command (cmd, arg) ->
        ()
     | Expression str ->
        print_endline "Evaluating IR, cannot evaluate expression"
     | Empty ->
        let gstate, stack = Bytecode_interpreter.step (gstate, stack) in
        current_mode := Bytecode (gstate, stack);
        print_program ()
     end

let handle_input input =
  try handle_input' input with
  | Type_check.Type_error (l, err) ->
     print_endline (Type_error.string_of_type_error err)
  | Reporting.Fatal_error err ->
     Reporting.print_error err
  | exn ->
     print_endline (Printexc.to_string exn)

let () =
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

  (* Read the script file if it is set with the -is option, and excute them *)
  begin
    match !opt_interactive_script with
    | None -> ()
    | Some file ->
       let chan = open_in file in
       try
         while true do
           let line = input_line chan in
           handle_input line;
         done;
       with
       | End_of_file -> ()
  end;

  LNoise.history_load ~filename:"sail_history" |> ignore;
  LNoise.history_set ~max_length:100 |> ignore;

  if !opt_interactive then
    begin
      List.iter print_endline sail_logo;
      user_input handle_input
    end
  else ()
