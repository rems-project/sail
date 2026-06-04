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
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

open Libsail

open Ast
open Ast_compare
open Ast_defs
open Ast_util
open Interpreter
open Pretty_print_sail
open Reporting.Position

module Callgraph_commands = Callgraph_commands

type mode = Normal | Evaluation of frame | PartialEvaluation of Partial_eval.partial_state

type display_options = { clear : bool; registers : IdSet.t }

type repl_state = {
  ctx : Initial_check.ctx;
  ast : Type_check.typed_ast;
  effect_info : Effects.side_effect_info;
  env : Type_check.Env.t;
  vs_ids : IdSet.t ref;
  options : (Arg.key * Arg.spec * Arg.doc) list;
  mode : mode;
  display_options : display_options;
  state : Interpreter.lstate * Interpreter.gstate;
  default_sail_dir : string;
  config : Yojson.Safe.t option;
}

let shrink_repl_state rstate : Interactive.State.istate =
  {
    ctx = rstate.ctx;
    ast = rstate.ast;
    effect_info = rstate.effect_info;
    env = rstate.env;
    options = rstate.options;
    default_sail_dir = rstate.default_sail_dir;
    config = rstate.config;
  }

let initial_repl_state config options ctx env effect_info ast =
  {
    ctx;
    ast;
    effect_info;
    env;
    vs_ids = ref (val_spec_ids ast.defs);
    options;
    mode = Normal;
    display_options = { clear = true; registers = IdSet.empty };
    state = initial_state ast env !Value.primops;
    default_sail_dir = Locations.sail_dir;
    config;
  }

let prompt rstate =
  if not (IdSet.is_empty rstate.display_options.registers) then (
    let _, gstate = rstate.state in
    print_endline ("---- registers ----" |> Util.cyan |> Util.clear);
    List.iter
      (fun reg ->
        match Bindings.find_opt reg gstate.registers with
        | Some value ->
            print_endline (string_of_id reg ^ " = " ^ (Value.string_of_value value |> Util.green |> Util.clear))
        | None -> print_endline ("No register " ^ string_of_id reg)
      )
      (IdSet.elements rstate.display_options.registers)
  );
  let l = Sail_file.repl_prompt_line () in
  match rstate.mode with
  | Normal -> Printf.sprintf "REPL:%d> " l
  | Evaluation _ -> Printf.sprintf "REPL:%d eval> " l
  | PartialEvaluation _ -> Printf.sprintf "REPL:%d partial> " l

let mode_clear rstate =
  match rstate.mode with
  | Normal -> ()
  | Evaluation _ | PartialEvaluation _ -> if rstate.display_options.clear then LNoise.clear_screen () else ()

let rec user_input rstate callback =
  match LNoise.linenoise (prompt rstate) with
  | None -> ()
  | Some line ->
      mode_clear rstate;
      user_input (callback rstate line) callback

let color_command cmd = Util.(cmd |> green |> clear)
let color_arg arg = Util.(arg |> yellow |> clear)

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
    [
      Printf.sprintf "Type %s for a list of commands, and %s %s for help." (color_command ":commands")
        (color_command ":help") (color_arg "<command>");
      "Type expressions to evaluate them.";
    ]
  in
  List.map banner logo @ [""] @ help @ [""]

let sep = "-----------------------------------------------------" |> Util.blue |> Util.clear

let print_program rstate =
  match rstate.mode with
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
  | PartialEvaluation pstate ->
      let open PPrint in
      let docs = Partial_eval.(Pretty.docs (partial_state_ctx pstate)) in
      let num_docs = List.length docs in
      List.iteri
        (fun n doc ->
          let prefix = string_of_int (num_docs - n) ^ ": " in
          let doc = nest (String.length prefix) (string prefix ^^ doc) in
          print_endline (Pretty_print_sail.Document.to_string doc)
        )
        docs;
      print_endline (Partial_eval.string_of_focus pstate)

let rec run rstate =
  match rstate.mode with
  | Normal | PartialEvaluation _ -> rstate
  | Evaluation frame -> (
      match frame with
      | Done (state, v) ->
          print_endline ("Result = " ^ Value.string_of_value v);
          { rstate with mode = Normal; state }
      | Fail (_, _, _, _, msg) ->
          print_endline ("Error: " ^ msg);
          { rstate with mode = Normal }
      | Step _ ->
          let rstate =
            try { rstate with mode = Evaluation (eval_frame frame) }
            with Failure str ->
              print_endline str;
              { rstate with mode = Normal }
          in
          run rstate
      | Break frame ->
          print_endline "Breakpoint";
          { rstate with mode = Evaluation frame }
      | Effect_request (out, state, stack, eff) ->
          let rstate =
            try { rstate with mode = Evaluation (!Interpreter.effect_interp out state stack eff) }
            with Failure str ->
              print_endline str;
              { rstate with mode = Normal }
          in
          run rstate
    )

let rec run_function rstate depth =
  let run_function' rstate stack =
    match depth with
    | None -> run_function rstate (Some (List.length stack))
    | Some n -> if List.compare_length_with stack n >= 0 then run_function rstate depth else rstate
  in
  match rstate.mode with
  | Normal | PartialEvaluation _ -> rstate
  | Evaluation frame -> (
      match frame with
      | Done (state, v) ->
          print_endline ("Result = " ^ Value.string_of_value v);
          { rstate with mode = Normal; state }
      | Fail (_, _, _, _, msg) ->
          print_endline ("Error: " ^ msg);
          { rstate with mode = Normal }
      | Step (_, _, _, stack) ->
          let rstate =
            try { rstate with mode = Evaluation (eval_frame frame) }
            with Failure str ->
              print_endline str;
              { rstate with mode = Normal }
          in
          run_function' rstate stack
      | Break frame ->
          print_endline "Breakpoint";
          { rstate with mode = Evaluation frame }
      | Effect_request (out, state, stack, eff) ->
          let rstate =
            try { rstate with mode = Evaluation (!Interpreter.effect_interp out state stack eff) }
            with Failure str ->
              print_endline str;
              { rstate with mode = Normal }
          in
          run_function' rstate stack
    )

let rec run_steps rstate n =
  match rstate.mode with
  | _ when n <= 0 -> rstate
  | Normal | PartialEvaluation _ -> rstate
  | Evaluation frame -> (
      match frame with
      | Done (state, v) ->
          print_endline ("Result = " ^ Value.string_of_value v);
          { rstate with mode = Normal; state }
      | Fail (_, _, _, _, msg) ->
          print_endline ("Error: " ^ msg);
          { rstate with mode = Normal }
      | Step (_, _, _, _) ->
          let rstate =
            try { rstate with mode = Evaluation (eval_frame frame) }
            with Failure str ->
              print_endline str;
              { rstate with mode = Normal }
          in
          run_steps rstate (n - 1)
      | Break frame ->
          print_endline "Breakpoint";
          { rstate with mode = Evaluation frame }
      | Effect_request (out, state, stack, eff) ->
          let rstate =
            try { rstate with mode = Evaluation (!Interpreter.effect_interp out state stack eff) }
            with Failure str ->
              print_endline str;
              { rstate with mode = Normal }
          in
          run_steps rstate (n - 1)
    )

type repl_action = string -> Lexing.position -> string -> repl_state -> repl_state

type repl_command = { commands : string list; help : string; arg_help : string option; repl_action : repl_action }

let repl_commands =
  [
    {
      commands = [":n"; ":normal"];
      help = "Exit evaluation mode back to normal mode.";
      arg_help = None;
      repl_action = (fun _ _ _ rstate -> { rstate with mode = Normal });
    };
    {
      commands = [":clear"];
      help = "Set whether to clear the screen or not in evaluation mode.";
      arg_help = Some "(on|off)";
      repl_action =
        (fun _ _ arg rstate ->
          if arg = "on" || arg = "true" then
            { rstate with display_options = { rstate.display_options with clear = true } }
          else if arg = "off" || arg = "false" then
            { rstate with display_options = { rstate.display_options with clear = false } }
          else (
            print_endline "Invalid argument for :clear, expected either :clear on or :clear off";
            rstate
          )
        );
    };
    {
      commands = [":reset"];
      help = "Reset the interpreter state.";
      arg_help = None;
      repl_action = (fun _ _ _ rstate -> { rstate with state = initial_state rstate.ast rstate.env !Value.primops });
    };
    {
      commands = [":show_register"; ":show_registers"];
      help = "Print the value of the given registers above the prompt.";
      arg_help = Some "<register1> <register2> ...";
      repl_action =
        (fun _ _ arg rstate ->
          let args = Str.split (Str.regexp " +") arg in
          List.fold_left
            (fun rstate arg ->
              let display_options = rstate.display_options in
              let display_options =
                { display_options with registers = IdSet.add (mk_id arg) display_options.registers }
              in
              { rstate with display_options }
            )
            rstate args
        );
    };
    {
      commands = [":hide_register"; ":hide_registers"];
      help =
        Printf.sprintf "Do not print the value of the given registers above the prompt, undoing the action of %s"
          (color_command ":show_register");
      arg_help = Some "<register1> <register2> ...";
      repl_action =
        (fun _ _ arg rstate ->
          let args = Str.split (Str.regexp " +") arg in
          List.fold_left
            (fun rstate arg ->
              let display_options = rstate.display_options in
              let reg = mk_id arg in
              if IdSet.mem reg display_options.registers then (
                let display_options =
                  { display_options with registers = IdSet.remove (mk_id arg) display_options.registers }
                in
                { rstate with display_options }
              )
              else (
                print_endline ("Register " ^ arg ^ " is not being displayed");
                rstate
              )
            )
            rstate args
        );
    };
    {
      commands = [":partial"; ":p"];
      help = Printf.sprintf "Begin partially evaluating an expression";
      arg_help = Some "<expression>";
      repl_action =
        (fun _ pos arg rstate ->
          let exp = Type_check.infer_exp rstate.env (Initial_check.exp_of_string ~inline:pos rstate.ctx arg) in
          { rstate with mode = PartialEvaluation (Partial_eval.from_exp exp) }
        );
    };
  ]

let help cmd =
  let open Printf in
  match String.trim cmd with
  | ":r" | ":run" -> sprintf "%s - Completely evaluate the currently evaluating expression." (color_command cmd)
  | ":s" | ":step" -> sprintf "%s %s - Perform a number of evaluation steps." (color_command cmd) (color_arg "<number>")
  | ":f" | ":step_function" ->
      sprintf "%s - Perform evaluation steps until the currently evaulating function returns." (color_command cmd)
  | "" ->
      sprintf "Type %s for a list of commands, and %s %s for information about a specific command"
        (color_command ":commands") (color_command ":help") (color_arg "<command>")
  | _ -> (
      match List.find_opt (fun rcmd -> List.mem cmd rcmd.commands) repl_commands with
      | Some rcmd ->
          sprintf "%s %s- %s" (color_command cmd)
            (match rcmd.arg_help with Some a -> color_arg a ^ " " | None -> "")
            rcmd.help
      | None -> (
          match Interactive.get_command cmd with
          | Some (help_message, action) ->
              let cmd, args, desc = Interactive.generate_help cmd help_message action in
              sprintf "%s %s - %s" cmd args desc
          | None ->
              sprintf "Either invalid command passed to help, or no documentation for %s. Try %s." (color_command cmd)
                (color_command ":help :help")
        )
    )

type input = Command of string * string * Lexing.position | Expression of string * Lexing.position | Empty

let editor = ref "vim"

let editor_command cmd =
  let open Lexing in
  let temp_file = Filename.temp_file "repl" ".sail" in
  Reporting.system_checked (!editor ^ " " ^ temp_file);
  let contents = Util.read_whole_file temp_file in
  let start_line, start_bol = Sail_file.add_to_repl_contents ~command:contents in
  let pos = { pos_fname = "REPL"; pos_lnum = start_line; pos_bol = start_bol; pos_cnum = start_bol } in
  if cmd = "" then Expression (contents, pos) else Command (cmd, contents, pos)

let () =
  let module CliArg = Arg in
  let open Interactive in
  (register_command ~name:"set_editor" ~help:"Set the editor for the :edit command. Default vim."
  @@ let@ cmd = Arg.String "editor command" in
     unit_action (fun () -> editor := cmd)
  );

  register_command ~name:"quit" ~shortname:"q" ~help:"Exit the REPL."
  @@ unit_action (fun () ->
      Value.output_close ();
      exit 0
  );

  (* We can't set up the elf commands in elf_loader.ml because it's used
     by Sail OCaml emulators at runtime, so set them up here. *)
  (register_command ~name:"elf" ~help:"Load an elf file."
  @@ let@ file = Arg.String "file" in
     unit_action (fun () -> Elf_loader.load_elf file)
  );

  (register_command ~name:"bin" ~help:"Load a raw binary file at :0. Use :elf to load an ELF."
  @@ let@ addr_s = Arg.String "addr" in
     let@ filename = Arg.String "file" in
     let@ _ = Arg.Get in
     let addr = Big_int.of_string addr_s in
     Elf_loader.load_binary addr filename
  );

  (register_command ~name:"sail_dir" ~help:"Print Sail directory location."
  @@ let@ istate = Arg.Get in
     print_endline (Reporting.get_sail_dir istate.default_sail_dir)
  );

  (register_command ~name:"infer" ~shortname:"i" ~help:"Infer the type of an expression."
  @@ let@ pos, arg, istate = Arg.Rest "expression" in
     let exp = Initial_check.exp_of_string ~inline:pos istate.ctx arg in
     let exp = Type_check.infer_exp istate.env exp in
     Document.to_channel stdout (doc_typ (Type_check.typ_of exp));
     print_newline ();
     None
  );

  (register_command ~name:"prove" ~help:"Try to prove a constraint."
  @@ let@ pos, arg, istate = Arg.Rest "constraint" in
     let nc = Initial_check.constraint_of_string ~inline:pos istate.ctx arg in
     print_endline (string_of_bool (Type_check.prove __POS__ istate.env nc));
     None
  );

  (register_command ~name:"type" ~shortname:"t" ~help:"Lookup the type of a function."
  @@ let@ pos, arg, istate = Arg.Rest "function name" in
     let typq, typ = Type_check.Env.get_val_spec (mk_id arg) istate.env in
     Document.to_channel stdout (doc_binding (typq, typ));
     print_newline ();
     None
  );

  (register_command ~name:"assume" ~help:"Add a constraint to the REPL environment."
  @@ let@ pos, arg, istate = Arg.Rest "function name" in
     let nc = Initial_check.constraint_of_string ~inline:pos istate.ctx arg in
     Some { istate with env = Type_check.Env.add_constraint nc istate.env }
  );

  (register_command ~name:"verbose" ~shortname:"v" ~help:"Set verbose typechecking output."
  @@ let@ level = Arg.Int "verbosity" in
     unit_action (fun () -> Type_check.set_tc_debug level)
  );

  (register_command ~name:"ast" ~help:"Dump the syntax tree to a file."
  @@ let@ filename = Arg.String "filename" in
     let@ istate = Arg.Get in
     let chan = open_out filename in
     Pretty_print_sail.output_ast chan (Type_check.strip_ast istate.ast);
     close_out chan
  );

  (register_command ~name:"output" ~help:"Redirect evaluating expression output to a file."
  @@ let@ filename = Arg.String "filename" in
     unit_action (fun () ->
         let chan = open_out filename in
         Value.output_redirect chan
     )
  );

  (register_command ~name:"def" ~help:"Evaluate a top-level definition."
  @@ let@ pos, arg, istate = Arg.Rest "definition" in
     (* Add an extra blank line so we can handle directives that require a newline to be parsed. *)
     ignore (Sail_file.add_to_repl_contents ~command:"");
     let ast, ctx =
       Initial_check.ast_of_def_string_with ~inline:pos __POS__ istate.ctx
         (Preprocess.preprocess istate.default_sail_dir None istate.options)
         (arg ^ "\n")
     in
     let ast, env = Type_check.check istate.env ast in
     Some { istate with ast = append_ast istate.ast ast; env; ctx }
  );

  (register_command ~name:"option"
     ~help:"Parse string as if it was an option passed on the command line. e.g. :option -help."
  @@ let@ pos, arg, istate = Arg.Rest "option" in
     let current = ref 0 in
     let args, reset = Preprocess.create_argv_array ~offset:0 ~current (Range (pos, pos)) arg in
     ( try
         match args with
         | opt :: args ->
             CliArg.parse_argv ~current
               (Array.of_list ["sail"; opt; String.concat " " args])
               istate.options
               (fun _ -> ())
               ""
         | [] -> print_endline "Must provide a valid option"
       with CliArg.Bad message | CliArg.Help message -> print_endline message
     );
     reset ();
     None
  );

  (register_command ~name:"instantiate" ~help:"Instantiate abstract types."
  @@ let@ istate = Arg.Update in
     let ast, _ = Frontend.instantiate_abstract_types None (`Assoc []) !Sail_options.opt_instantiations istate.ast in
     let ast, env = Type_check.check istate.env (Type_check.strip_ast ast) in
     { istate with ast = append_ast istate.ast ast; env }
  );

  (register_command ~name:"recheck_types" ~shortname:"recheck"
     ~help:"Re type-check the Sail AST, and synchronize the interpreter's internal state to that AST."
  @@ let@ istate = Arg.Update in
     let ast, env = Type_check.check Type_check.initial_env (Type_check.strip_ast istate.ast) in
     { istate with env; ast }
  );

  (register_command ~name:"let" ~help:"Bind a variable to expression."
  @@ let@ pos, arg, istate = Arg.Rest "variable = expression" in
     match String.split_on_char '=' arg with
     | [v; exp_str] ->
         let exp =
           Initial_check.exp_of_string ~inline:(advance_position ~after:1 ~trim:false v pos) istate.ctx exp_str
         in
         let arg_l = string_location ~start:pos ~trim:true arg in
         let v_l = string_location ~start:pos ~trim:true v in
         let defs, env =
           Type_check.check_defs istate.env
             [mk_def ~loc:arg_l (DEF_let (mk_pat ~loc:v_l (P_id (mk_id ~loc:v_l (String.trim v))), exp)) ()]
         in
         Some { istate with ast = append_ast_defs istate.ast defs; env }
     | _ -> failwith "Invalid arguments for :let"
  );

  (register_command ~name:"bind" ~shortname:"b" ~help:"Declare a variable of a specific type."
  @@ let@ pos, arg, istate = Arg.Rest "id : type" in
     match String.split_on_char ':' arg with
     | [v; arg] ->
         let typ = Initial_check.typ_of_string ~inline:(advance_position ~after:1 ~trim:false v pos) istate.ctx arg in
         let v_l = string_location ~start:pos ~trim:true v in
         let _, env, _ = Type_check.bind_pat istate.env (mk_pat ~loc:v_l (P_id (mk_id ~loc:v_l (String.trim v)))) typ in
         Some { istate with env }
     | _ -> failwith "Invalid arguments for :bind"
  );

  (register_command ~name:"help"
     ~help:
       (Printf.sprintf "Get a description of %s. Commands are prefixed with a colon, e.g. %s." (color_arg "<command>")
          (color_command ":help :type")
       )
  @@ let@ command_name = Arg.String "command" in
     unit_action (fun () -> print_endline (help command_name))
  );

  register_command ~name:"commands" ~help:"List all available commands"
  @@ unit_action (fun () ->
      let format_command (cmd, (help, shortname, action)) =
        let _, args, _ = Interactive.generate_help cmd help action in
        match shortname with
        | Some s -> Printf.sprintf "  %s | %s %s" (color_command (":" ^ s)) (color_command cmd) args
        | _ -> Printf.sprintf "  %s %s" (color_command cmd) args
      in
      let more_commands = List.map format_command (Interactive.all_commands ()) in
      print_endline "Commands:";
      List.iter print_endline more_commands;
      print_endline "";
      print_endline "When evaluating an expression:";
      List.iter
        (fun (s, cmd) -> Printf.ksprintf print_endline "  %s | %s" (color_command s) (color_command cmd))
        [(":r", ":run"); (":s", ":step"); (":f", ":step_function")];
      print_endline "";
      print_endline "REPL control:";
      List.iter
        (fun rcmd ->
          Printf.ksprintf print_endline "  %s%s"
            (Util.string_of_list " | " color_command rcmd.commands)
            (match rcmd.arg_help with Some a -> " " ^ color_arg a | None -> "")
        )
        repl_commands
  );

  register_command ~name:"rewrite"
    ~help:
      (Printf.sprintf "Apply a rewrite to the AST. %s shows all possible rewrites. See also %s"
         (color_command ":list_rewrites") (color_command ":rewrites")
      )
  @@ let@ pos, arg, istate = Arg.Rest "rewrite arg0 ... argN" in
     let open Rewrites in
     let args = Str.split (Str.regexp " +") arg in
     let rec parse_args rw args =
       match (rw, args) with
       | Full_rewriter rw, [] -> rw
       | Bool_rewriter rw, arg :: args -> parse_args (rw (bool_of_string arg)) args
       | String_rewriter rw, arg :: args -> parse_args (rw arg) args
       | Literal_rewriter rw, arg :: args -> (
           match arg with
           | "ocaml" -> parse_args (rw rewrite_lit_ocaml) args
           | "lem" -> parse_args (rw rewrite_lit_lem) args
           | "all" -> parse_args (rw (fun _ -> true)) args
           | _ -> failwith "Target for literal rewrite must be one of ocaml/lem/all"
         )
       | _, _ -> failwith "Invalid arguments to rewrite"
     in
     match args with
     | rw :: args ->
         let rw = List.assoc rw Rewrites.all_rewriters in
         let rw = parse_args rw args in
         let ctx', ast', effect_info', env' = rw istate.ctx istate.effect_info istate.env istate.ast in
         Some { istate with ctx = ctx'; ast = ast'; effect_info = effect_info'; env = env' }
     | [] -> failwith "Must provide the name of a rewrite, use :list_rewrites for a list of possible rewrites"

(* This function is called on every line of input passed to the interpreter *)
let handle_input' rstate input =
  LNoise.history_add input |> ignore;

  (* Process the input and check if it's a command, a raw expression,
     or empty. *)
  let input =
    let open Lexing in
    if input <> "" && input.[0] = ':' then (
      let start_line, start_bol = Sail_file.add_to_repl_contents ~command:input in
      let n = try String.index input ' ' with Not_found -> String.length input in
      let cmd = Str.string_before input n in
      let arg = Str.string_after input n in
      let pos = { pos_fname = "REPL"; pos_lnum = start_line; pos_bol = start_bol; pos_cnum = start_bol + n } in
      Command (cmd, String.trim arg, trim_position arg pos)
    )
    else if String.length input >= 2 && input.[0] = '/' && input.[1] = '/' then
      (* Treat anything starting with // as a comment *)
      Empty
    else if input <> "" then (
      let start_line, start_bol = Sail_file.add_to_repl_contents ~command:input in
      Expression (input, { pos_fname = "REPL"; pos_lnum = start_line; pos_bol = start_bol; pos_cnum = start_bol })
    )
    else Empty
  in

  let unrecognised_command cmd = print_endline ("Command " ^ cmd ^ " is not a valid command in this mode.") in

  let input = match input with Command (":edit", arg, _) -> editor_command arg | input -> input in

  let handle_command rstate cmd arg pos =
    match List.find_opt (fun rcmd -> List.mem cmd rcmd.commands) repl_commands with
    | Some rcmd -> rcmd.repl_action cmd pos arg rstate
    | None -> (
        match Interactive.get_command cmd with
        | Some (_, action) ->
            let res = Interactive.run_action (shrink_repl_state rstate) cmd pos arg action in
            { rstate with ast = res.ast; effect_info = res.effect_info; env = res.env }
        | None ->
            unrecognised_command cmd;
            rstate
      )
  in

  match rstate.mode with
  | Normal -> (
      match input with
      | Command (cmd, arg, pos) -> handle_command rstate cmd arg pos
      | Expression (str, pos) ->
          (* An expression in normal mode is type checked, then puts
               us in evaluation mode. *)
          let exp = Type_check.infer_exp rstate.env (Initial_check.exp_of_string ~inline:pos rstate.ctx str) in
          let rstate =
            { rstate with mode = Evaluation (eval_frame (Step (lazy "", rstate.state, Monad.pure exp, []))) }
          in
          print_program rstate;
          rstate
      | Empty -> rstate
    )
  | Evaluation frame -> (
      match input with
      | Command (cmd, arg, pos) -> (
          (* Evaluation mode commands *)
          match cmd with
          | ":r" | ":run" -> run rstate
          | ":s" | ":step" ->
              let rstate = run_steps rstate (int_of_string arg) in
              print_program rstate;
              rstate
          | ":f" | ":step_function" ->
              let rstate = run_function rstate None in
              print_program rstate;
              rstate
          | _ -> handle_command rstate cmd arg pos
        )
      | Expression _ ->
          print_endline "Already evaluating expression";
          rstate
      | Empty -> (
          (* Empty input will evaluate one step, or switch back to
             normal mode when evaluation is completed. *)
          match frame with
          | Done (state, v) ->
              print_endline ("Result = " ^ Value.string_of_value v);
              { rstate with mode = Normal; state }
          | Fail (_, _, _, _, msg) ->
              print_endline ("Error: " ^ msg);
              { rstate with mode = Normal }
          | Step (_, state, _, _) -> (
              try
                let rstate = { rstate with mode = Evaluation (eval_frame frame); state } in
                print_program rstate;
                rstate
              with Failure str ->
                print_endline str;
                { rstate with mode = Normal }
            )
          | Break frame ->
              print_endline "Breakpoint";
              { rstate with mode = Evaluation frame }
          | Effect_request (out, state, stack, eff) -> (
              try
                let rstate =
                  { rstate with mode = Evaluation (!Interpreter.effect_interp out state stack eff); state }
                in
                print_program rstate;
                rstate
              with Failure str ->
                print_endline str;
                { rstate with mode = Normal }
            )
        )
    )
  | PartialEvaluation pstate -> (
      match input with
      | Command (cmd, arg, pos) -> handle_command rstate cmd arg pos
      | Empty ->
          let rstate = { rstate with mode = PartialEvaluation (Partial_eval.step pstate) } in
          print_program rstate;
          rstate
      | _ ->
          print_program rstate;
          rstate
    )

let handle_input rstate input =
  try handle_input' rstate input with
  | Failure str ->
      print_endline ("Error: " ^ str);
      rstate
  | Type_error.Type_error (l, err) ->
      let msg, hint = Type_error.string_of_type_error err in
      Reporting.print_type_error ?hint l msg;
      rstate
  | Reporting.Fatal_error err ->
      Reporting.print_error ~interactive:true err;
      rstate
  | exn ->
      print_endline (Printexc.to_string exn);
      rstate

let start_repl ?(banner = true) ?commands:(script = []) ?auto_rewrites:(rewrites = true) ~config ~options ctx env
    effect_info ast =
  let rstate =
    if rewrites then (
      let ctx, ast, effect_info, env =
        Rewrites.rewrite ctx effect_info env (Rewrites.instantiate_rewrites Rewrites.rewrites_interpreter) ast
      in
      initial_repl_state config options ctx env effect_info ast
    )
    else initial_repl_state config options ctx env effect_info ast
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
      if last_id <> "" then (
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
            IdSet.elements !(rstate.vs_ids) |> List.map string_of_id
            |> List.filter (fun id -> Str.string_match (Str.regexp_string last_id) id 0)
            |> List.map (fun completion -> line_so_far ^ completion)
            |> List.iter (LNoise.add_completion ln_completions)
      )
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
          | ":rewrite" :: rw :: args -> (
              match List.assoc_opt rw Rewrites.all_rewriters with
              | Some rw -> (
                  let hints = Rewrites.describe_rewriter rw in
                  let hints = Util.drop (List.length args) hints in
                  match hints with [] -> None | _ -> hint (String.concat " " hints)
                )
              | None -> None
            )
          | [":option"] -> hint "<flag>"
          | [":option"; flag] -> (
              match List.find_opt (fun (opt, _, _) -> flag = opt) options with
              | Some (_, _, help) -> hint (Str.global_replace (Str.regexp " +") " " help)
              | None -> None
            )
          | _ -> None
        )
  );

  let rstate = List.fold_left handle_input rstate script in

  LNoise.history_load ~filename:"sail_history" |> ignore;
  LNoise.history_set ~max_length:100 |> ignore;

  if banner then List.iter print_endline sail_logo;
  user_input rstate handle_input
