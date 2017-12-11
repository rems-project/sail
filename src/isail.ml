open Sail

open Ast
open Ast_util
open Pretty_print_sail2

let rec user_input prompt callback =
  match LNoise.linenoise prompt with
  | None -> ()
  | Some v -> 
     callback v;
     user_input prompt callback

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
  else
    let exp = Type_check.infer_exp !interactive_env (Initial_check.exp_of_string Ast_util.dec_ord input) in
    let v = Interpreter.eval_exp !interactive_ast (Interpreter.step exp) in
    print_endline ("Result = " ^ Value.string_of_value v)


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
    user_input "sail> " handle_input
  else ()
