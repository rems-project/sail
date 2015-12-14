(** A Sail library *)

(* This library is not well-thought. It has grown driven by the need to
 * reuse some components of Sail in the Power XML extraction tool. It
 * should by no means by considered stable (hence the lack of mli
 * interface file), and is not intended for general consumption. Use at
 * your own risks. *)

module Pretty = Pretty_print

let parse_exps s =
  let lexbuf = Lexing.from_string s in
  try
  let pre_exps = Parser.nonempty_exp_list Lexer.token lexbuf in
  List.map (Initial_check.to_ast_exp Type_internal.initial_kind_env (Ast.Ord_aux(Ast.Ord_inc,Parse_ast.Unknown))) pre_exps
  with
    | Parsing.Parse_error ->
        let pos = Lexing.lexeme_start_p lexbuf in
        let msg = Printf.sprintf "syntax error on character %d" pos.Lexing.pos_cnum in
        failwith msg
    | Parse_ast.Parse_error_locn(l,m) ->
        let rec format l = match l with
        | Parse_ast.Unknown -> "???"
        | Parse_ast.Range(p1,p2) -> Printf.sprintf "%d:%d" p1.Lexing.pos_cnum p2.Lexing.pos_cnum
        | Parse_ast.Generated l -> Printf.sprintf "code generated near: %s" (format l)
        | Parse_ast.Int(s,_) -> Printf.sprintf "code for by: %s" s in
        let msg = Printf.sprintf "syntax error: %s %s" (format l) m in
        failwith msg
    | Lexer.LexError(s,p) ->
        let msg = Printf.sprintf "lexing error: %s %d" s p.Lexing.pos_cnum in
        failwith msg
        


