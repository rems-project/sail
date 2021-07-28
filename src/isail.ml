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
(*    Alastair Reid                                                         *)
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

open Sail

open Ast
open Ast_util
open Interpreter
open Pretty_print_sail

module Slice = Slice
module Gdbmi = Gdbmi

type mode =
  | Evaluation of frame
  | Normal
  | Emacs

let current_mode = ref Normal

let prompt () =
  match !current_mode with
  | Normal -> "sail> "
  | Evaluation _ -> "eval> "
  | Emacs -> ""

let eval_clear = ref true

let mode_clear () =
  match !current_mode with
  | Normal -> ()
  | Evaluation _ -> if !eval_clear then LNoise.clear_screen () else ()
  | Emacs -> ()

let rec user_input callback =
  match LNoise.linenoise (prompt ()) with
  | None -> ()
  | Some v ->
     mode_clear ();
     begin
       try callback v with
       | Reporting.Fatal_error e -> Reporting.print_error e
     end;
     user_input callback

let sail_logo =
  let banner str = str |> Util.bold |> Util.red |> Util.clear in
  let logo =
    if !Interactive.opt_suppress_banner then []
    else
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

let sep = "-----------------------------------------------------" |> Util.blue |> Util.clear

let vs_ids = ref (val_spec_ids !Interactive.ast.defs)

let interactive_state =
  ref (initial_state ~registers:false !Interactive.ast !Interactive.env !Value.primops)

(* We can't set up the elf commands in elf_loader.ml because it's used
   by Sail OCaml emulators at runtime, so set them up here. *)
let () =
  let open Interactive in
  let open Elf_loader in

  ArgString ("file", fun file -> Action (fun () -> load_elf file))
  |> register_command ~name:"elf" ~help:"Load an elf file";

  ArgString ("addr", fun addr_s -> ArgString ("file", fun filename -> Action (fun () ->
    let addr = Big_int.of_string addr_s in
    load_binary addr filename
  ))) |> register_command ~name:"bin" ~help:"Load a raw binary file at :0. Use :elf to load an ELF"

(* This is a feature that lets us take interpreter commands like :foo
   x, y and turn the into functions that can be called by sail as
   foo(x, y), which lets us use sail to script itself. The
   sail_scripting_primops_once variable ensures we only add the
   commands to the interpreter primops list once, although we may have
   to reset the AST and env changes when we :load and :unload
   files by calling this function multiple times. *)
let sail_scripting_primops_once = ref true

let setup_sail_scripting () =
  let open Interactive in

  let sail_command_name cmd = "sail_" ^ String.sub cmd 1 (String.length cmd - 1) in

  let val_specs =
    List.map (fun (cmd, (_, action)) ->
        let name = sail_command_name cmd in
        let typschm = mk_typschm (mk_typquant []) (reflect_typ action) in
        mk_val_spec (VS_val_spec (typschm, mk_id name, [("_", name)], false))
      ) !commands in
  let val_specs, env' = Type_check.check_defs !env val_specs in
  ast := append_ast_defs !ast val_specs;
  env := env';

  if !sail_scripting_primops_once then (
    List.iter (fun (cmd, (help, action)) ->
        let open Value in
        let name = sail_command_name cmd in
        let impl values =
          let rec call values action =
            match values, action with
            | (v :: vs), ArgString (_, next) ->
               call vs (next (coerce_string v))
            | (v :: vs), ArgInt (_, next) ->
               call vs (next (Big_int.to_int (coerce_int v)))
            | _, Action act ->
               act (); V_unit
            | _, _ ->
               failwith help
          in
          call values action
        in
        Value.add_primop name impl
      ) !commands;
    sail_scripting_primops_once := false
  )

let print_program () =
  match !current_mode with
  | Normal | Emacs -> ()
  | Evaluation (Step (out, _, _, stack))
    | Evaluation (Effect_request(out, _, stack,  _))
    | Evaluation (Fail (out, _, _, stack, _)) ->
     List.map stack_string stack |> List.rev |> List.iter (fun code -> print_endline (Lazy.force code); print_endline sep);
     print_endline (Lazy.force out)
  | Evaluation (Done (_, v)) ->
     print_endline (Value.string_of_value v |> Util.green |> Util.clear)
  | Evaluation _ -> ()

let rec run () =
  match !current_mode with
  | Normal | Emacs -> ()
  | Evaluation frame ->
     begin match frame with
     | Done (state, v) ->
        interactive_state := state;
        print_endline ("Result = " ^ Value.string_of_value v);
        current_mode := Normal
     | Fail (_, _, _, _, msg) ->
        print_endline ("Error: " ^ msg);
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
     | Effect_request (out, state, stack, eff) ->
        begin
          try
            current_mode := Evaluation (!Interpreter.effect_interp state eff)
          with
          | Failure str -> print_endline str; current_mode := Normal
        end;
        run ()
     end

let rec run_function depth =
  let run_function' stack =
    match depth with
    | None -> run_function (Some (List.length stack))
    | Some n ->
       if List.compare_length_with stack n >= 0 then
         run_function depth
       else
         ()
  in
  match !current_mode with
  | Normal | Emacs -> ()
  | Evaluation frame ->
     begin match frame with
     | Done (state, v) ->
        interactive_state := state;
        print_endline ("Result = " ^ Value.string_of_value v);
        current_mode := Normal
     | Fail (_, _, _, _, msg) ->
        print_endline ("Error: " ^ msg);
        current_mode := Normal
     | Step (out, state, _, stack) ->
        begin
          try
            current_mode := Evaluation (eval_frame frame)
          with
          | Failure str -> print_endline str; current_mode := Normal
        end;
        run_function' stack
     | Break frame ->
        print_endline "Breakpoint";
        current_mode := Evaluation frame
     | Effect_request (out, state, stack, eff) ->
        begin
          try
            current_mode := Evaluation (!Interpreter.effect_interp state eff)
          with
          | Failure str -> print_endline str; current_mode := Normal
        end;
        run_function' stack
     end

let rec run_steps n =
  match !current_mode with
  | _ when n <= 0 -> ()
  | Normal | Emacs -> ()
  | Evaluation frame ->
     begin match frame with
     | Done (state, v) ->
        interactive_state := state;
        print_endline ("Result = " ^ Value.string_of_value v);
        current_mode := Normal
     | Fail (_, _, _, _, msg) ->
        print_endline ("Error: " ^ msg);
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
     | Effect_request (out, state, stack, eff) ->
        begin
          try
            current_mode := Evaluation (!Interpreter.effect_interp state eff)
          with
          | Failure str -> print_endline str; current_mode := Normal
        end;
        run_steps (n - 1)
     end
 
let help =
  let open Printf in
  let open Util in
  let color c str = str |> c |> clear in
  function
  | ":t" | ":type" ->
     sprintf "(:t | :type) %s - Print the type of a function."
             (color yellow "<function name>")
  | ":q" | ":quit" ->
     "(:q | :quit) - Exit the interpreter."
  | ":i" | ":infer" ->
     sprintf "(:i | :infer) %s - Infer the type of an expression."
             (color yellow "<expression>")
  | ":v" | ":verbose" ->
     "(:v | :verbose) - Increase the verbosity level, or reset to zero at max verbosity."
  | ":b" | ":bind" ->
     sprintf "(:b | :bind) %s : %s - Declare a variable of a specific type"
             (color yellow "<id>") (color yellow "<type>")
  | ":let" ->
     sprintf ":let %s = %s - Bind a variable to expression"
             (color yellow "<id>") (color yellow "<expression>")
  | ":def" ->
     sprintf ":def %s - Evaluate a top-level definition"
             (color yellow "<definition>")
  | ":prove" ->
     sprintf ":prove %s - Try to prove a constraint in the top-level environment"
             (color yellow "<constraint>")
  | ":assume" ->
     sprintf ":assume %s - Add a constraint to the top-level environment"
             (color yellow "<constraint>")
  | ":commands" ->
     ":commands - List all available commands."
  | ":help" ->
     sprintf ":help %s - Get a description of <command>. Commands are prefixed with a colon, e.g. %s."
             (color yellow "<command>") (color green ":help :type")
  | ":r" | ":run" ->
     "(:r | :run) - Completely evaluate the currently evaluating expression."
  | ":s" | ":step" ->
     sprintf "(:s | :step) %s - Perform a number of evaluation steps."
             (color yellow "<number>")
  | ":f" | ":step_function" ->
     sprintf "(:f | :step_function) - Perform evaluation steps until the currently evaulating function returns."
  | ":n" | ":normal" ->
     "(:n | :normal) - Exit evaluation mode back to normal mode."
  | ":clear" ->
     sprintf ":clear %s - Set whether to clear the screen or not in evaluation mode."
             (color yellow "(on|off)")
  | ":l" | ":load" -> String.concat "\n"
     [ sprintf "(:l | :load) %s - Load sail files and add their definitions to the interactive environment."
               (color yellow "<files>");
       "Files containing scattered definitions must be loaded together." ]
  | ":u" | ":unload" ->
     "(:u | :unload) - Unload all loaded files."
  | ":output" ->
     sprintf ":output %s - Redirect evaluating expression output to a file."
             (color yellow "<file>")
  | ":option" ->
     sprintf ":option %s - Parse string as if it was an option passed on the command line. e.g. :option -help."
             (color yellow "<string>")
  | ":recheck" ->
     sprintf ":recheck - Re type-check the Sail AST, and synchronize the interpreters internal state to that AST."
  | ":rewrite" ->
     sprintf ":rewrite %s - Apply a rewrite to the AST. %s shows all possible rewrites. See also %s"
             (color yellow "<rewrite> <args>") (color green ":list_rewrites") (color green ":rewrites")
  | ":rewrites" ->
     sprintf ":rewrites %s - Apply all rewrites for a specific target, valid targets are lem, coq, ocaml, c, and interpreter"
             (color yellow "<target>")
  | ":compile" ->
     sprintf ":compile %s - Compile AST to a specified target, valid targets are lem, coq, ocaml, c, and ir (intermediate representation)"
             (color yellow "<target>")
  | "" ->
     sprintf "Type %s for a list of commands, and %s %s for information about a specific command"
             (color green ":commands") (color green ":help") (color yellow "<command>")
  | cmd ->
     match List.assoc_opt cmd !Interactive.commands with
     | Some (help_message, action) -> Interactive.generate_help cmd help_message action
     | None ->
        sprintf "Either invalid command passed to help, or no documentation for %s. Try %s."
                (color green cmd) (color green ":help :help")

let format_pos_emacs p1 p2 contents =
  let open Lexing in
  let b = Buffer.create 160 in
  Printf.sprintf "(sail-error %d %d %d %d \"%s\")"
                 p1.pos_lnum (p1.pos_cnum - p1.pos_bol)
                 p2.pos_lnum (p2.pos_cnum - p2.pos_bol)
                 contents

let rec emacs_error l contents =
  match l with
  | Parse_ast.Unknown -> "(error \"no location info: " ^ contents ^ "\")"
  | Parse_ast.Range (p1, p2) -> format_pos_emacs p1 p2 contents
  | Parse_ast.Unique (_, l) -> emacs_error l contents
  | Parse_ast.Documented (_, l) -> emacs_error l contents
  | Parse_ast.Generated l -> emacs_error l contents

let slice_roots = ref IdSet.empty
let slice_cuts = ref IdSet.empty

let rec describe_rewrite =
  let open Rewrites in
  function
  | String_rewriter rw -> "<string>" :: describe_rewrite (rw "")
  | Bool_rewriter rw -> "<bool>" :: describe_rewrite (rw false)
  | Literal_rewriter rw -> "(ocaml|lem|all)" :: describe_rewrite (rw (fun _ -> true))
  | Basic_rewriter _
  | Checking_rewriter _ -> []

type session = {
    id : string;
    files : string list
  }

let default_session = {
    id = "none";
    files = []
  }

let session = ref default_session

let parse_session file =
  let open Yojson.Basic.Util in
  if Sys.file_exists file then
    let json = Yojson.Basic.from_file file in
    let args = Str.split (Str.regexp " +") (json |> member "options" |> to_string) in
    Arg.parse_argv ~current:(ref 0) (Array.of_list ("sail" :: args)) Sail.options (fun _ -> ()) "";
    print_endline ("(message \"Using session " ^ file ^ "\")");
    {
      id = file;
      files = json |> member "files" |> convert_each to_string
    }
  else
    default_session

let load_session upto file =
  match upto with
  | None -> None
  | Some upto_file when Filename.basename upto_file = file -> None
  | Some upto_file ->
     let (_, ast, env) =
       Process_file.load_files ~check:true options !Interactive.env [Filename.concat (Filename.dirname upto_file) file]
     in
     Interactive.ast := append_ast !Interactive.ast ast;
     Interactive.env := env;
     print_endline ("(message \"Checked " ^ file ^ "...\")\n");
     Some upto_file

let load_into_session file =
  let session_file = Filename.concat (Filename.dirname file) "sail.json" in
  session := (if session_file = !session.id then !session else parse_session session_file);
  ignore (List.fold_left load_session (Some file) !session.files)

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
    else if String.length input >= 2 && input.[0] = '/' && input.[1] = '/' then
      (* Treat anything starting with // as a comment *)
      Empty
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
  begin match input with
  | Command (cmd, arg) ->
     begin match cmd with
     | ":n" | ":normal" ->
        current_mode := Normal
     | ":t" | ":type" ->
        let typq, typ = Type_check.Env.get_val_spec (mk_id arg) !Interactive.env in
        pretty_sail stdout (doc_binding (typq, typ));
        print_newline ();
     | ":q" | ":quit" ->
        Value.output_close ();
        exit 0
     | ":i" | ":infer" ->
        let exp = Initial_check.exp_of_string arg in
        let exp = Type_check.infer_exp !Interactive.env exp in
        pretty_sail stdout (doc_typ (Type_check.typ_of exp));
        print_newline ()
     | ":prove" ->
        let nc = Initial_check.constraint_of_string arg in
        print_endline (string_of_bool (Type_check.prove __POS__ !Interactive.env nc))
     | ":assume" ->
        let nc = Initial_check.constraint_of_string arg in
        Interactive.env := Type_check.Env.add_constraint nc !Interactive.env
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
        let more_commands = Util.string_of_list " " fst !Interactive.commands in
        let commands =
          [ "Universal commands - :(t)ype :(i)nfer :(q)uit :(v)erbose :prove :assume :clear :commands :help :output :option";
            "Normal mode commands - :elf :(l)oad :(u)nload :let :def :(b)ind :recheck :rewrite :rewrites :list_rewrites :compile " ^ more_commands;
            "Evaluation mode commands - :(r)un :(s)tep :step_(f)unction :(n)ormal";
            "";
            ":(c)ommand can be called as either :c or :command." ]
        in
        List.iter print_endline commands
     | ":option" ->
        begin
          try
            let args = Str.split (Str.regexp " +") arg in
            begin match args with
            | opt :: args ->
               Arg.parse_argv ~current:(ref 0) (Array.of_list ["sail"; opt; String.concat " " args]) Sail.options (fun _ -> ()) "";
            | [] -> print_endline "Must provide a valid option"
            end
          with
          | Arg.Bad message | Arg.Help message -> print_endline message
        end;
     | ":pretty" ->
        print_endline (Pretty_print_sail.to_string (Latex.defs !Interactive.ast))
     | ":ast" ->
        let chan = open_out arg in
        Pretty_print_sail.pp_ast chan !Interactive.ast;
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
     begin match input with
     | Command (cmd, arg) ->
        (* Normal mode commands *)
        begin match cmd with
        | ":l" | ":load" ->
           let files = Util.split_on_char ' ' arg in
           let (_, ast, env) = Process_file.load_files options !Interactive.env files in
           let ast, env =
             if !Interactive.opt_auto_interpreter_rewrites then
               Process_file.rewrite_ast_target "interpreter" env ast
             else
               ast, env
           in
           Interactive.ast := append_ast !Interactive.ast ast;
           Interactive.env := env;
           interactive_state := initial_state !Interactive.ast !Interactive.env !Value.primops;
           vs_ids := val_spec_ids !Interactive.ast.defs
        | ":u" | ":unload" ->
           Interactive.ast := Ast_defs.empty_ast;
           Interactive.env := Type_check.initial_env;
           interactive_state := initial_state !Interactive.ast !Interactive.env !Value.primops;
           vs_ids := val_spec_ids !Interactive.ast.defs;
           (* See initial_check.mli for an explanation of why we need this. *)
           Initial_check.have_undefined_builtins := false;
           Process_file.clear_symbols ()
        | ":b" | ":bind" ->
           let args = Str.split (Str.regexp " +") arg in
           begin match args with
           | v :: ":" :: args ->
              let typ = Initial_check.typ_of_string (String.concat " " args) in
              let _, env, _ = Type_check.bind_pat !Interactive.env (mk_pat (P_id (mk_id v))) typ in
              Interactive.env := env
           | _ -> print_endline "Invalid arguments for :bind"
           end
        | ":let" ->
           let args = Str.split (Str.regexp " +") arg in
           begin match args with
           | v :: "=" :: args ->
              let exp = Initial_check.exp_of_string (String.concat " " args) in
              let defs, env = Type_check.check_defs !Interactive.env [DEF_val (mk_letbind (mk_pat (P_id (mk_id v))) exp)] in
              Interactive.ast := append_ast_defs !Interactive.ast defs;
              Interactive.env := env;
              interactive_state := initial_state !Interactive.ast !Interactive.env !Value.primops;
           | _ -> print_endline "Invalid arguments for :let"
           end
        | ":def" ->
           let ast = Initial_check.ast_of_def_string_with (Process_file.preprocess options) arg in
           let ast, env = Type_check.check !Interactive.env ast in
           Interactive.ast := append_ast !Interactive.ast ast;
           Interactive.env := env;
           interactive_state := initial_state !Interactive.ast !Interactive.env !Value.primops;
        | ":list_rewrites" ->
           let print_rewrite (name, rw) =
             print_endline (name ^ " " ^ Util.(String.concat " " (describe_rewrite rw) |> yellow |> clear))
           in
           List.sort (fun a b -> String.compare (fst a) (fst b)) Rewrites.all_rewrites
           |> List.iter print_rewrite
        | ":rewrite" ->
           let open Rewrites in
           let args = Str.split (Str.regexp " +") arg in
           let rec parse_args rw args =
             match rw, args with
             | Basic_rewriter rw, [] -> rw
             | Bool_rewriter rw, arg :: args -> parse_args (rw (bool_of_string arg)) args
             | String_rewriter rw, arg :: args -> parse_args (rw arg) args
             | Literal_rewriter rw, arg :: args ->
                begin match arg with
                | "ocaml" -> parse_args (rw rewrite_lit_ocaml) args
                | "lem" -> parse_args (rw rewrite_lit_lem) args
                | "all" -> parse_args (rw (fun _ -> true)) args
                | _ -> failwith "target for literal rewrite must be one of ocaml/lem/all"
                end
             | _, _ -> failwith "Invalid arguments to rewrite"
           in
           begin match args with
           | rw :: args ->
              let rw = List.assoc rw Rewrites.all_rewrites in
              let rw = parse_args rw args in
              Interactive.ast := rw !Interactive.env !Interactive.ast;
           | [] ->
              failwith "Must provide the name of a rewrite, use :list_rewrites for a list of possible rewrites"
           end
        | ":rewrites" ->
           let new_ast, new_env = Process_file.rewrite_ast_target arg !Interactive.env !Interactive.ast in
           Interactive.ast := new_ast;
           Interactive.env := new_env;
           interactive_state := initial_state !Interactive.ast !Interactive.env !Value.primops
        | ":prover_regstate" ->
           let env, ast = prover_regstate (Some arg) !Interactive.ast !Interactive.env in
           Interactive.env := env;
           Interactive.ast := ast;
           interactive_state := initial_state !Interactive.ast !Interactive.env !Value.primops
        | ":recheck" ->
           let ast, env = Type_check.check Type_check.initial_env !Interactive.ast in
           Interactive.env := env;
           Interactive.ast := ast;
           interactive_state := initial_state !Interactive.ast !Interactive.env !Value.primops;
           vs_ids := val_spec_ids !Interactive.ast.defs
        | ":recheck_types" ->
           let ast, env = Type_check.check Type_check.initial_env !Interactive.ast in
           Interactive.env := env;
           Interactive.ast := ast;
           vs_ids := val_spec_ids !Interactive.ast.defs
        | ":compile" ->
           let out_name = match !Process_file.opt_file_out with
             | None -> "out.sail"
             | Some f -> f ^ ".sail"
           in
           target (Some arg) out_name !Interactive.ast !Interactive.env
        | _ ->
           match List.assoc_opt cmd !Interactive.commands with
           | Some (_, action) -> Interactive.run_action cmd arg action
           | None -> unrecognised_command cmd
        end
     | Expression str ->
        (* An expression in normal mode is type checked, then puts
             us in evaluation mode. *)
        let exp = Type_check.infer_exp !Interactive.env (Initial_check.exp_of_string str) in
        current_mode := Evaluation (eval_frame (Step (lazy "", !interactive_state, return exp, [])));
        print_program ()
     | Empty -> ()
     end

  | Emacs ->
     begin match input with
     | Command (cmd, arg) ->
        begin match cmd with
        | ":load" ->
           begin
             try
               load_into_session arg;
               let (_, ast, env) = Process_file.load_files ~check:true options !Interactive.env [arg] in
               Interactive.ast := append_ast !Interactive.ast ast;
               interactive_state := initial_state !Interactive.ast !Interactive.env !Value.primops;
               Interactive.env := env;
               vs_ids := val_spec_ids !Interactive.ast.defs;
               print_endline ("(message \"Checked " ^ arg ^ " done\")\n");
             with
             | Reporting.Fatal_error (Err_type (l, msg)) ->
                print_endline (emacs_error l (String.escaped msg))
           end
        | ":unload" ->
           Interactive.ast := Ast_defs.empty_ast;
           Interactive.env := Type_check.initial_env;
           interactive_state := initial_state !Interactive.ast !Interactive.env !Value.primops;
           vs_ids := val_spec_ids !Interactive.ast.defs;
           Initial_check.have_undefined_builtins := false;
           Process_file.clear_symbols ()
        | ":typeat" ->
           let args = Str.split (Str.regexp " +") arg in
           begin match args with
           | [file; pos] ->
              let open Lexing in
              let pos = int_of_string pos in
              let pos = { dummy_pos with pos_fname = file; pos_cnum = pos - 1 } in
              let sl = Some (pos, pos) in
              begin match find_annot_ast sl !Interactive.ast with
              | Some annot ->
                 let msg = String.escaped (string_of_typ (Type_check.typ_of_annot annot)) in
                 begin match Reporting.simp_loc (fst annot) with
                 | Some (p1, p2) ->
                    print_endline ("(sail-highlight-region "
                                   ^ string_of_int (p1.pos_cnum + 1) ^ " " ^ string_of_int (p2.pos_cnum + 1)
                                   ^ " \"" ^ msg ^ "\")")
                 | None ->
                    print_endline ("(message \"" ^ msg ^ "\")")
                 end
              | None ->
                 print_endline "(message \"No type here\")"
              end
           | _ ->
              print_endline "(error \"Bad arguments for type at cursor\")"
           end
        | _ -> ()
        end
     | Expression _ | Empty -> ()
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
             run_steps (int_of_string arg);
             print_program ()
          | ":f" | ":step_function" ->
             run_function None;
             print_program ()
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
        | Fail (_, _, _, _, msg) ->
           print_endline ("Error: " ^ msg);
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
        | Effect_request (out, state, stack, eff) ->
           begin
             try
               interactive_state := state;
               current_mode := Evaluation (!Interpreter.effect_interp state eff);
               print_program ()
             with
             | Failure str -> print_endline str; current_mode := Normal
           end
        end
     end

let handle_input input =
  try handle_input' input with
  | Failure str ->
     print_endline ("Error: " ^ str)
  | Type_check.Type_error (env, l, err) ->
     print_endline (Type_error.string_of_type_error err)
  | Reporting.Fatal_error err ->
     Reporting.print_error err
  | exn ->
     print_endline (Printexc.to_string exn)

let () =
  (* Auto complete function names based on val specs, directories if :load command, or rewrites if :rewrite command *)
  LNoise.set_completion_callback (
      fun line_so_far ln_completions ->
      let line_so_far, last_id =
        try
          let p = Str.search_backward (Str.regexp "[^a-zA-Z0-9_/-]") line_so_far (String.length line_so_far - 1) in
          Str.string_before line_so_far (p + 1), Str.string_after line_so_far (p + 1)
        with
        | Not_found -> "", line_so_far
        | Invalid_argument _ -> line_so_far, ""
      in
      let n = try String.index line_so_far ' ' with Not_found -> String.length line_so_far in
      let cmd = Str.string_before line_so_far n in
      if last_id <> "" then
        begin match cmd with
        | ":load" | ":l" ->
           let dirname, basename = Filename.dirname last_id, Filename.basename last_id in
           if Sys.file_exists last_id then
             LNoise.add_completion ln_completions (line_so_far ^ last_id);
           if (try Sys.is_directory dirname with Sys_error _ -> false) then
             let contents = Sys.readdir (Filename.concat (Sys.getcwd ()) dirname) in
             for i = 0 to Array.length contents - 1 do
               if Str.string_match (Str.regexp_string basename) contents.(i) 0 then
                 let is_dir = (try Sys.is_directory (Filename.concat dirname contents.(i)) with Sys_error _ -> false) in
                 LNoise.add_completion ln_completions
                   (line_so_far ^ Filename.concat dirname contents.(i) ^ (if is_dir then Filename.dir_sep else ""))
             done
        | ":rewrite" ->
           List.map fst Rewrites.all_rewrites
           |> List.filter (fun opt -> Str.string_match (Str.regexp_string last_id) opt 0)
           |> List.map (fun completion -> line_so_far ^ completion)
           |> List.iter (LNoise.add_completion ln_completions)
        | ":option" ->
           List.map (fun (opt, _, _) -> opt) options
           |> List.filter (fun opt -> Str.string_match (Str.regexp_string last_id) opt 0)
           |> List.map (fun completion -> line_so_far ^ completion)
           |> List.iter (LNoise.add_completion ln_completions)
        | _ ->
          IdSet.elements !vs_ids
          |> List.map string_of_id
          |> List.filter (fun id -> Str.string_match (Str.regexp_string last_id) id 0)
          |> List.map (fun completion -> line_so_far ^ completion)
          |> List.iter (LNoise.add_completion ln_completions)
        end
      else ()
    );

  LNoise.set_hints_callback (
      fun line_so_far ->
      let hint str = Some (" " ^ str, LNoise.Yellow, false) in
      match String.trim line_so_far with
      | _ when !Interactive.opt_emacs_mode -> None
      | ":load"  | ":l" -> hint "<sail file>"
      | ":bind"  | ":b" -> hint "<id> : <type>"
      | ":infer" | ":i" -> hint "<expression>"
      | ":type"  | ":t" -> hint "<function id>"
      | ":let" -> hint "<id> = <expression>"
      | ":def" -> hint "<definition>"
      | ":prove" -> hint "<constraint>"
      | ":assume" -> hint "<constraint>"
      | ":compile" -> hint "<target>"
      | ":rewrites" -> hint "<target>"
      | str ->
         let args = Str.split (Str.regexp " +") str in
         match args with
         | [":rewrite"] -> hint "<rewrite>"
         | ":rewrite" :: rw :: args ->
            begin match List.assoc_opt rw Rewrites.all_rewrites with
            | Some rw ->
               let hints = describe_rewrite rw in
               let hints = Util.drop (List.length args) hints in
               (match hints with [] -> None | _ ->  hint (String.concat " " hints))
            | None -> None
            end
         | [":option"] -> hint "<flag>"
         | [":option"; flag] ->
            begin match List.find_opt (fun (opt, _, _) -> flag = opt) options with
            | Some (_, _, help) -> hint (Str.global_replace (Str.regexp " +") " " help)
            | None -> None
            end
         | _ -> None
    );

  if !Interactive.opt_auto_interpreter_rewrites then (
    let new_ast, new_env = Process_file.rewrite_ast_target "interpreter" !Interactive.env !Interactive.ast in
    Interactive.ast := new_ast;
    Interactive.env := new_env;
    interactive_state := initial_state !Interactive.ast !Interactive.env !Value.primops
  );
  
  (* Read the script file if it is set with the -is option, and excute them *)
  begin match !opt_interactive_script with
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

  if !Interactive.opt_interactive then (
    if not !Interactive.opt_emacs_mode then
      List.iter print_endline sail_logo
    else (current_mode := Emacs; Util.opt_colors := false);
    setup_sail_scripting ();
    user_input handle_input
  )
