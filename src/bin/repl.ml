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

open Ast
open Ast_defs
open Ast_util
open Interpreter
open Pretty_print_sail

module Callgraph_commands = Callgraph_commands

type mode = Evaluation of frame | Normal

type istate = {
  ast : Type_check.tannot ast;
  effect_info : Effects.side_effect_info;
  env : Type_check.Env.t;
  ref_state : Interactive.istate ref;
  vs_ids : IdSet.t ref;
  options : (Arg.key * Arg.spec * Arg.doc) list;
  mode : mode;
  clear : bool;
  state : Interpreter.lstate * Interpreter.gstate;
  default_sail_dir : string;
  config : Yojson.Basic.t option;
}

let shrink_istate istate : Interactive.istate =
  {
    ast = istate.ast;
    effect_info = istate.effect_info;
    env = istate.env;
    default_sail_dir = istate.default_sail_dir;
    config = istate.config;
  }

let initial_istate config options env effect_info ast =
  {
    ast;
    effect_info;
    env;
    ref_state = ref (Interactive.initial_istate config Manifest.dir);
    vs_ids = ref (val_spec_ids ast.defs);
    options;
    mode = Normal;
    clear = true;
    state = initial_state ~registers:false empty_ast Type_check.initial_env !Value.primops;
    default_sail_dir = Manifest.dir;
    config;
  }

let setup_interpreter_state istate =
  istate.ref_state :=
    {
      ast = istate.ast;
      effect_info = istate.effect_info;
      env = istate.env;
      default_sail_dir = istate.default_sail_dir;
      config = istate.config;
    };
  { istate with state = initial_state istate.ast istate.env !Value.primops }

let prompt istate = match istate.mode with Normal -> "sail> " | Evaluation _ -> "eval> "

let mode_clear istate =
  match istate.mode with Normal -> () | Evaluation _ -> if istate.clear then LNoise.clear_screen () else ()

let rec user_input istate callback =
  match LNoise.linenoise (prompt istate) with
  | None -> ()
  | Some line ->
      mode_clear istate;
      user_input (callback istate line) callback

let sail_logo =
  let banner str = str |> Util.bold |> Util.red |> Util.clear in
  let logo =
    [
      {|    ___       ___       ___       ___ |};
      {|   /\  \     /\  \     /\  \     /\__\|};
      {|  /::\  \   /::\  \   _\:\  \   /:/  /|};
      {| /\:\:\__\ /::\:\__\ /\/::\__\ /:/__/ |};
      {| \:\:\/__/ \/\::/  / \::/\/__/ \:\  \ |};
      {|  \::/  /    /:/  /   \:\__\    \:\__\|};
      {|   \/__/     \/__/     \/__/     \/__/|};
    ]
  in
  let help =
    ["Type :commands for a list of commands, and :help <command> for help."; "Type expressions to evaluate them."]
  in
  List.map banner logo @ [""] @ help @ [""]

let sep = "-----------------------------------------------------" |> Util.blue |> Util.clear

(* We can't set up the elf commands in elf_loader.ml because it's used
   by Sail OCaml emulators at runtime, so set them up here. *)
let () =
  let open Interactive in
  let open Elf_loader in
  ArgString ("file", fun file -> ActionUnit (fun _ -> load_elf file))
  |> register_command ~name:"elf" ~help:"Load an elf file";

  ArgString
    ( "addr",
      fun addr_s ->
        ArgString
          ( "file",
            fun filename ->
              ActionUnit
                (fun _ ->
                  let addr = Big_int.of_string addr_s in
                  load_binary addr filename
                )
          )
    )
  |> register_command ~name:"bin" ~help:"Load a raw binary file at :0. Use :elf to load an ELF";

  ActionUnit (fun istate -> print_endline (Reporting.get_sail_dir istate.default_sail_dir))
  |> register_command ~name:"sail_dir" ~help:"print Sail directory location"

(* This is a feature that lets us take interpreter commands like :foo
   x, y and turn the into functions that can be called by sail as
   foo(x, y), which lets us use sail to script itself. *)
let setup_sail_scripting istate =
  let sail_command_name cmd = "sail_" ^ String.sub cmd 1 (String.length cmd - 1) in

  let cmds = Interactive.all_commands () in

  let val_specs =
    List.map
      (fun (cmd, (_, action)) ->
        let name = sail_command_name cmd in
        let typschm = mk_typschm (mk_typquant []) (Interactive.reflect_typ action) in
        mk_val_spec (VS_val_spec (typschm, mk_id name, Some { pure = false; bindings = [("_", name)] }))
      )
      cmds
  in
  let val_specs, env = Type_check.check_defs istate.env val_specs in

  List.iter
    (fun (cmd, (help, action)) ->
      let open Value in
      let name = sail_command_name cmd in
      let impl values =
        let rec call values action =
          match (values, action) with
          | v :: vs, Interactive.ArgString (_, next) -> call vs (next (coerce_string v))
          | v :: vs, Interactive.ArgInt (_, next) -> call vs (next (Big_int.to_int (coerce_int v)))
          | _, ActionUnit act ->
              act !(istate.ref_state);
              V_unit
          | _, Action act ->
              istate.ref_state := act !(istate.ref_state);
              V_unit
          | _, _ -> failwith help
        in
        call values action
      in
      Value.add_primop name impl
    )
    cmds;

  { istate with ast = append_ast_defs istate.ast val_specs; env }

let print_program istate =
  match istate.mode with
  | Normal -> ()
  | Evaluation (Step (out, _, _, stack))
  | Evaluation (Effect_request (out, _, stack, _))
  | Evaluation (Fail (out, _, _, stack, _)) ->
      List.map stack_string stack |> List.rev
      |> List.iter (fun code ->
             print_endline (Lazy.force code);
             print_endline sep
         );
      print_endline (Lazy.force out)
  | Evaluation (Done (_, v)) -> print_endline (Value.string_of_value v |> Util.green |> Util.clear)
  | Evaluation _ -> ()

let rec run istate =
  match istate.mode with
  | Normal -> istate
  | Evaluation frame -> begin
      match frame with
      | Done (state, v) ->
          print_endline ("Result = " ^ Value.string_of_value v);
          { istate with mode = Normal; state }
      | Fail (_, _, _, _, msg) ->
          print_endline ("Error: " ^ msg);
          { istate with mode = Normal }
      | Step _ ->
          let istate =
            try { istate with mode = Evaluation (eval_frame frame) }
            with Failure str ->
              print_endline str;
              { istate with mode = Normal }
          in
          run istate
      | Break frame ->
          print_endline "Breakpoint";
          { istate with mode = Evaluation frame }
      | Effect_request (_, state, _, eff) ->
          let istate =
            try { istate with mode = Evaluation (!Interpreter.effect_interp state eff) }
            with Failure str ->
              print_endline str;
              { istate with mode = Normal }
          in
          run istate
    end

let rec run_function istate depth =
  let run_function' istate stack =
    match depth with
    | None -> run_function istate (Some (List.length stack))
    | Some n -> if List.compare_length_with stack n >= 0 then run_function istate depth else istate
  in
  match istate.mode with
  | Normal -> istate
  | Evaluation frame -> begin
      match frame with
      | Done (state, v) ->
          print_endline ("Result = " ^ Value.string_of_value v);
          { istate with mode = Normal; state }
      | Fail (_, _, _, _, msg) ->
          print_endline ("Error: " ^ msg);
          { istate with mode = Normal }
      | Step (_, _, _, stack) ->
          let istate =
            try { istate with mode = Evaluation (eval_frame frame) }
            with Failure str ->
              print_endline str;
              { istate with mode = Normal }
          in
          run_function' istate stack
      | Break frame ->
          print_endline "Breakpoint";
          { istate with mode = Evaluation frame }
      | Effect_request (_, state, stack, eff) ->
          let istate =
            try { istate with mode = Evaluation (!Interpreter.effect_interp state eff) }
            with Failure str ->
              print_endline str;
              { istate with mode = Normal }
          in
          run_function' istate stack
    end

let rec run_steps istate n =
  match istate.mode with
  | _ when n <= 0 -> istate
  | Normal -> istate
  | Evaluation frame -> begin
      match frame with
      | Done (state, v) ->
          print_endline ("Result = " ^ Value.string_of_value v);
          { istate with mode = Normal; state }
      | Fail (_, _, _, _, msg) ->
          print_endline ("Error: " ^ msg);
          { istate with mode = Normal }
      | Step (_, _, _, _) ->
          let istate =
            try { istate with mode = Evaluation (eval_frame frame) }
            with Failure str ->
              print_endline str;
              { istate with mode = Normal }
          in
          run_steps istate (n - 1)
      | Break frame ->
          print_endline "Breakpoint";
          { istate with mode = Evaluation frame }
      | Effect_request (_, state, _, eff) ->
          let istate =
            try { istate with mode = Evaluation (!Interpreter.effect_interp state eff) }
            with Failure str ->
              print_endline str;
              { istate with mode = Normal }
          in
          run_steps istate (n - 1)
    end

let help =
  let open Printf in
  let open Util in
  let color c str = str |> c |> clear in
  function
  | ":t" | ":type" -> sprintf "(:t | :type) %s - Print the type of a function." (color yellow "<function name>")
  | ":q" | ":quit" -> "(:q | :quit) - Exit the interpreter."
  | ":i" | ":infer" -> sprintf "(:i | :infer) %s - Infer the type of an expression." (color yellow "<expression>")
  | ":v" | ":verbose" -> "(:v | :verbose) - Increase the verbosity level, or reset to zero at max verbosity."
  | ":b" | ":bind" ->
      sprintf "(:b | :bind) %s : %s - Declare a variable of a specific type" (color yellow "<id>")
        (color yellow "<type>")
  | ":let" -> sprintf ":let %s = %s - Bind a variable to expression" (color yellow "<id>") (color yellow "<expression>")
  | ":def" -> sprintf ":def %s - Evaluate a top-level definition" (color yellow "<definition>")
  | ":prove" ->
      sprintf ":prove %s - Try to prove a constraint in the top-level environment" (color yellow "<constraint>")
  | ":assume" -> sprintf ":assume %s - Add a constraint to the top-level environment" (color yellow "<constraint>")
  | ":commands" -> ":commands - List all available commands."
  | ":help" ->
      sprintf ":help %s - Get a description of <command>. Commands are prefixed with a colon, e.g. %s."
        (color yellow "<command>") (color green ":help :type")
  | ":r" | ":run" -> "(:r | :run) - Completely evaluate the currently evaluating expression."
  | ":s" | ":step" -> sprintf "(:s | :step) %s - Perform a number of evaluation steps." (color yellow "<number>")
  | ":f" | ":step_function" ->
      sprintf "(:f | :step_function) - Perform evaluation steps until the currently evaulating function returns."
  | ":n" | ":normal" -> "(:n | :normal) - Exit evaluation mode back to normal mode."
  | ":clear" ->
      sprintf ":clear %s - Set whether to clear the screen or not in evaluation mode." (color yellow "(on|off)")
  | ":output" -> sprintf ":output %s - Redirect evaluating expression output to a file." (color yellow "<file>")
  | ":option" ->
      sprintf ":option %s - Parse string as if it was an option passed on the command line. e.g. :option -help."
        (color yellow "<string>")
  | ":recheck" ->
      sprintf ":recheck - Re type-check the Sail AST, and synchronize the interpreters internal state to that AST."
  | ":rewrite" ->
      sprintf ":rewrite %s - Apply a rewrite to the AST. %s shows all possible rewrites. See also %s"
        (color yellow "<rewrite> <args>") (color green ":list_rewrites") (color green ":rewrites")
  | "" ->
      sprintf "Type %s for a list of commands, and %s %s for information about a specific command"
        (color green ":commands") (color green ":help") (color yellow "<command>")
  | cmd -> (
      match Interactive.get_command cmd with
      | Some (help_message, action) -> Interactive.generate_help cmd help_message action
      | None ->
          sprintf "Either invalid command passed to help, or no documentation for %s. Try %s." (color green cmd)
            (color green ":help :help")
    )

type input = Command of string * string | Expression of string | Empty

(* This function is called on every line of input passed to the interpreter *)
let handle_input' istate input =
  LNoise.history_add input |> ignore;

  (* Process the input and check if it's a command, a raw expression,
     or empty. *)
  let input =
    if input <> "" && input.[0] = ':' then (
      let n = try String.index input ' ' with Not_found -> String.length input in
      let cmd = Str.string_before input n in
      let arg = String.trim (Str.string_after input n) in
      Command (cmd, arg)
    )
    else if String.length input >= 2 && input.[0] = '/' && input.[1] = '/' then
      (* Treat anything starting with // as a comment *)
      Empty
    else if input <> "" then Expression input
    else Empty
  in

  let recognised = ref true in

  let unrecognised_command istate cmd =
    if !recognised = false then print_endline ("Command " ^ cmd ^ " is not a valid command in this mode.") else ();
    istate
  in

  (* First handle commands that are mode-independent *)
  let istate =
    match input with
    | Command (cmd, arg) -> begin
        match cmd with
        | ":n" | ":normal" -> { istate with mode = Normal }
        | ":t" | ":type" ->
            let typq, typ = Type_check.Env.get_val_spec (mk_id arg) istate.env in
            pretty_sail stdout (doc_binding (typq, typ));
            print_newline ();
            istate
        | ":q" | ":quit" ->
            Value.output_close ();
            exit 0
        | ":i" | ":infer" ->
            let exp = Initial_check.exp_of_string arg in
            let exp = Type_check.infer_exp istate.env exp in
            pretty_sail stdout (doc_typ (Type_check.typ_of exp));
            print_newline ();
            istate
        | ":prove" ->
            let nc = Initial_check.constraint_of_string arg in
            print_endline (string_of_bool (Type_check.prove __POS__ istate.env nc));
            istate
        | ":assume" ->
            let nc = Initial_check.constraint_of_string arg in
            { istate with env = Type_check.Env.add_constraint nc istate.env }
        | ":v" | ":verbose" ->
            Type_check.set_tc_debug (int_of_string arg);
            istate
        | ":clear" ->
            if arg = "on" || arg = "true" then { istate with clear = true }
            else if arg = "off" || arg = "false" then { istate with clear = false }
            else (
              print_endline "Invalid argument for :clear, expected either :clear on or :clear off";
              istate
            )
        | ":commands" ->
            let more_commands = Util.string_of_list " " fst (Interactive.all_commands ()) in
            let commands =
              [
                "Universal commands - :(t)ype :(i)nfer :(q)uit :(v)erbose :prove :assume :clear :commands :help \
                 :output :option";
                "Normal mode commands - :elf :(l)oad :(u)nload :let :def :(b)ind :recheck :compile " ^ more_commands;
                "Evaluation mode commands - :(r)un :(s)tep :step_(f)unction :(n)ormal";
                "";
                ":(c)ommand can be called as either :c or :command.";
              ]
            in
            List.iter print_endline commands;
            istate
        | ":option" ->
            begin
              try
                let args = Str.split (Str.regexp " +") arg in
                begin
                  match args with
                  | opt :: args ->
                      Arg.parse_argv ~current:(ref 0)
                        (Array.of_list ["sail"; opt; String.concat " " args])
                        istate.options
                        (fun _ -> ())
                        ""
                  | [] -> print_endline "Must provide a valid option"
                end
              with Arg.Bad message | Arg.Help message -> print_endline message
            end;
            istate
            (*
       | ":pretty" ->
          print_endline (Pretty_print_sail.to_string (Latex.defs istate.ast));
          istate
           *)
        | ":ast" ->
            let chan = open_out arg in
            Pretty_print_sail.pp_ast chan (Type_check.strip_ast istate.ast);
            close_out chan;
            istate
        | ":output" ->
            let chan = open_out arg in
            Value.output_redirect chan;
            istate
        | ":help" ->
            print_endline (help arg);
            istate
        | _ ->
            recognised := false;
            istate
      end
    | _ -> istate
  in

  match istate.mode with
  | Normal -> begin
      match input with
      | Command (cmd, arg) -> begin
          (* Normal mode commands *)
          match cmd with
          | ":b" | ":bind" ->
              let args = Str.split (Str.regexp " +") arg in
              begin
                match args with
                | v :: ":" :: args ->
                    let typ = Initial_check.typ_of_string (String.concat " " args) in
                    let _, env, _ = Type_check.bind_pat istate.env (mk_pat (P_id (mk_id v))) typ in
                    { istate with env }
                | _ -> failwith "Invalid arguments for :bind"
              end
          | ":let" ->
              let args = Str.split (Str.regexp " +") arg in
              begin
                match args with
                | v :: "=" :: args ->
                    let exp = Initial_check.exp_of_string (String.concat " " args) in
                    let defs, env =
                      Type_check.check_defs istate.env [mk_def (DEF_let (mk_letbind (mk_pat (P_id (mk_id v))) exp))]
                    in
                    { istate with ast = append_ast_defs istate.ast defs; env }
                | _ -> failwith "Invalid arguments for :let"
              end
          | ":def" ->
              let ast =
                Initial_check.ast_of_def_string_with __POS__
                  (Preprocess.preprocess istate.default_sail_dir None istate.options)
                  arg
              in
              let ast, env = Type_check.check istate.env ast in
              { istate with ast = append_ast istate.ast ast; env }
          | ":rewrite" ->
              let open Rewrites in
              let args = Str.split (Str.regexp " +") arg in
              let rec parse_args rw args =
                match (rw, args) with
                | Base_rewriter rw, [] -> rw
                | Bool_rewriter rw, arg :: args -> parse_args (rw (bool_of_string arg)) args
                | String_rewriter rw, arg :: args -> parse_args (rw arg) args
                | Literal_rewriter rw, arg :: args -> begin
                    match arg with
                    | "ocaml" -> parse_args (rw rewrite_lit_ocaml) args
                    | "lem" -> parse_args (rw rewrite_lit_lem) args
                    | "all" -> parse_args (rw (fun _ -> true)) args
                    | _ -> failwith "Target for literal rewrite must be one of ocaml/lem/all"
                  end
                | _, _ -> failwith "Invalid arguments to rewrite"
              in
              begin
                match args with
                | rw :: args ->
                    let rw = List.assoc rw Rewrites.all_rewriters in
                    let rw = parse_args rw args in
                    let ast', effect_info', env' = rw istate.effect_info istate.env istate.ast in
                    { istate with ast = ast'; effect_info = effect_info'; env = env' }
                | [] ->
                    failwith "Must provide the name of a rewrite, use :list_rewrites for a list of possible rewrites"
              end
          | ":sync_script" ->
              {
                istate with
                ast = !(istate.ref_state).ast;
                effect_info = !(istate.ref_state).effect_info;
                env = !(istate.ref_state).env;
              }
          | ":recheck" | ":recheck_types" ->
              let ast, env = Type_check.check Type_check.initial_env (Type_check.strip_ast istate.ast) in
              { istate with env; ast }
          | _ -> (
              match Interactive.get_command cmd with
              | Some (_, action) ->
                  let res = Interactive.run_action (shrink_istate istate) cmd arg action in
                  { istate with ast = res.ast; effect_info = res.effect_info; env = res.env }
              | None -> unrecognised_command istate cmd
            )
        end
      | Expression str ->
          (* An expression in normal mode is type checked, then puts
               us in evaluation mode. *)
          let exp = Type_check.infer_exp istate.env (Initial_check.exp_of_string str) in
          let istate = setup_interpreter_state istate in
          let istate = { istate with mode = Evaluation (eval_frame (Step (lazy "", istate.state, return exp, []))) } in
          print_program istate;
          istate
      | Empty -> istate
    end
  | Evaluation frame -> begin
      match input with
      | Command (cmd, arg) -> begin
          (* Evaluation mode commands *)
          match cmd with
          | ":r" | ":run" -> run istate
          | ":s" | ":step" ->
              let istate = run_steps istate (int_of_string arg) in
              print_program istate;
              istate
          | ":f" | ":step_function" ->
              let istate = run_function istate None in
              print_program istate;
              istate
          | _ -> unrecognised_command istate cmd
        end
      | Expression _ ->
          print_endline "Already evaluating expression";
          istate
      | Empty -> begin
          (* Empty input will evaluate one step, or switch back to
             normal mode when evaluation is completed. *)
          match frame with
          | Done (state, v) ->
              print_endline ("Result = " ^ Value.string_of_value v);
              { istate with mode = Normal; state }
          | Fail (_, _, _, _, msg) ->
              print_endline ("Error: " ^ msg);
              { istate with mode = Normal }
          | Step (_, state, _, _) -> begin
              try
                let istate = { istate with mode = Evaluation (eval_frame frame); state } in
                print_program istate;
                istate
              with Failure str ->
                print_endline str;
                { istate with mode = Normal }
            end
          | Break frame ->
              print_endline "Breakpoint";
              { istate with mode = Evaluation frame }
          | Effect_request (_, state, _, eff) -> begin
              try
                let istate = { istate with mode = Evaluation (!Interpreter.effect_interp state eff); state } in
                print_program istate;
                istate
              with Failure str ->
                print_endline str;
                { istate with mode = Normal }
            end
        end
    end

let handle_input istate input =
  try handle_input' istate input with
  | Failure str ->
      print_endline ("Error: " ^ str);
      istate
  | Type_error.Type_error (_, err) ->
      print_endline (Type_error.string_of_type_error err);
      istate
  | Reporting.Fatal_error err ->
      Reporting.print_error ~interactive:true err;
      istate
  | exn ->
      print_endline (Printexc.to_string exn);
      istate

let start_repl ?(banner = true) ?commands:(script = []) ?auto_rewrites:(rewrites = true) ~config ~options env
    effect_info ast =
  let istate =
    if rewrites then (
      let ast, effect_info, env =
        Rewrites.rewrite effect_info env (Rewrites.instantiate_rewrites Rewrites.rewrites_interpreter) ast
      in
      initial_istate config options env effect_info ast
    )
    else initial_istate config options env effect_info ast
  in

  LNoise.set_completion_callback (fun line_so_far ln_completions ->
      let line_so_far, last_id =
        try
          let p = Str.search_backward (Str.regexp "[^a-zA-Z0-9_/-]") line_so_far (String.length line_so_far - 1) in
          (Str.string_before line_so_far (p + 1), Str.string_after line_so_far (p + 1))
        with
        | Not_found -> ("", line_so_far)
        | Invalid_argument _ -> (line_so_far, "")
      in
      let n = try String.index line_so_far ' ' with Not_found -> String.length line_so_far in
      let cmd = Str.string_before line_so_far n in
      if last_id <> "" then begin
        match cmd with
        | ":rewrite" ->
            List.map fst Rewrites.all_rewriters
            |> List.filter (fun opt -> Str.string_match (Str.regexp_string last_id) opt 0)
            |> List.map (fun completion -> line_so_far ^ completion)
            |> List.iter (LNoise.add_completion ln_completions)
        | ":option" ->
            List.map (fun (opt, _, _) -> opt) options
            |> List.filter (fun opt -> Str.string_match (Str.regexp_string last_id) opt 0)
            |> List.map (fun completion -> line_so_far ^ completion)
            |> List.iter (LNoise.add_completion ln_completions)
        | _ ->
            IdSet.elements !(istate.vs_ids) |> List.map string_of_id
            |> List.filter (fun id -> Str.string_match (Str.regexp_string last_id) id 0)
            |> List.map (fun completion -> line_so_far ^ completion)
            |> List.iter (LNoise.add_completion ln_completions)
      end
      else ()
  );

  LNoise.set_hints_callback (fun line_so_far ->
      let hint str = Some (" " ^ str, LNoise.Yellow, false) in
      match String.trim line_so_far with
      | ":clear" -> hint "(on|off)"
      | ":bind" | ":b" -> hint "<id> : <type>"
      | ":infer" | ":i" -> hint "<expression>"
      | ":type" | ":t" -> hint "<function id>"
      | ":let" -> hint "<id> = <expression>"
      | ":def" -> hint "<definition>"
      | ":prove" -> hint "<constraint>"
      | ":assume" -> hint "<constraint>"
      | ":compile" -> hint "<target>"
      | ":rewrites" -> hint "<target>"
      | str -> (
          let args = Str.split (Str.regexp " +") str in
          match args with
          | [":rewrite"] -> hint "<rewrite>"
          | ":rewrite" :: rw :: args -> begin
              match List.assoc_opt rw Rewrites.all_rewriters with
              | Some rw -> (
                  let hints = Rewrites.describe_rewriter rw in
                  let hints = Util.drop (List.length args) hints in
                  match hints with [] -> None | _ -> hint (String.concat " " hints)
                )
              | None -> None
            end
          | [":option"] -> hint "<flag>"
          | [":option"; flag] -> begin
              match List.find_opt (fun (opt, _, _) -> flag = opt) options with
              | Some (_, _, help) -> hint (Str.global_replace (Str.regexp " +") " " help)
              | None -> None
            end
          | _ -> None
        )
  );

  let istate = List.fold_left handle_input istate script in

  LNoise.history_load ~filename:"sail_history" |> ignore;
  LNoise.history_set ~max_length:100 |> ignore;

  if banner then List.iter print_endline sail_logo;
  let istate = setup_sail_scripting istate in
  user_input istate handle_input
