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

open Parse_ast
open Chunk_ast

let id_loc (Id_aux (_, l)) = l

let rec map_last f = function
  | [] -> []
  | [x] -> [f true x]
  | x :: xs ->
      let x = f false x in
      x :: map_last f xs

let line_comment_opt = function Comment (Lexer.Comment_line, _, _, contents) -> Some contents | _ -> None

(* Remove additional (> 1) trailing newlines at the end of a string *)
let discard_extra_trailing_newlines s =
  let len = String.length s in
  let i = ref (len - 1) in
  let newlines = ref 0 in
  while s.[!i] = '\n' do
    incr newlines;
    decr i
  done;
  if !newlines > 1 then String.sub s 0 (len - (!newlines - 1)) else s

(* This function inserts a space before each comment if there is not
   already one, so "2/* comment */" will become "2 /* comment */"
   and similarly for line comments. *)
let fixup_comments ~filename source =
  (* Using the full parser is bit inefficient, it would be better to just tokenize *)
  let comments, _ = Initial_check.parse_file_from_string ~filename ~contents:source in
  let comment_stack = Stack.of_seq (List.to_seq comments) in
  let fixed = Buffer.create (String.length source) in
  let needs_space = ref false in
  String.iteri
    (fun cnum c ->
      begin
        match Stack.top_opt comment_stack with
        | Some (Lexer.Comment (_, start, _, _)) ->
            if c = ' ' || c = '\n' then needs_space := false
            else if cnum = start.pos_cnum then (
              if !needs_space then Buffer.add_char fixed ' ';
              ignore (Stack.pop comment_stack)
            )
            else needs_space := true
        | None -> ()
      end;
      Buffer.add_char fixed c
    )
    source;
  Buffer.contents fixed

(** We implement a small wrapper around a subset of the PPrint API to
    track line breaks and dedents (points where the indentation level
    decreases), re-implementing a few core combinators. *)
module PPrintWrapper = struct
  type hardline_type = Required | Desired

  type document =
    | Empty
    | Char of char
    | String of string
    | Utf8string of string
    | Group of document
    | Nest of int * document
    | Align of document
    | Cat of document * document
    | Hardline of hardline_type
    | Ifflat of document * document

  type linebreak_info = { hardlines : (int * int * hardline_type) Queue.t; dedents : (int * int * int) Queue.t }

  let empty_linebreak_info () = { hardlines = Queue.create (); dedents = Queue.create () }

  let rec to_pprint lb_info =
    let open PPrint in
    function
    | Empty -> empty
    | Char c -> char c
    | String s -> string s
    | Utf8string s -> utf8string s
    | Group doc -> group (to_pprint lb_info doc)
    | Nest (n, doc) ->
        let doc = to_pprint lb_info doc in
        ifflat (nest n doc) (range (fun (_, (l, c)) -> Queue.add (l, c, n) lb_info.dedents) (nest n doc))
    | Align doc ->
        let doc = to_pprint lb_info doc in
        ifflat (align doc) (range (fun ((_, amount), (l, c)) -> Queue.add (l, c, amount) lb_info.dedents) (align doc))
    | Cat (doc1, doc2) ->
        let doc1 = to_pprint lb_info doc1 in
        let doc2 = to_pprint lb_info doc2 in
        doc1 ^^ doc2
    | Hardline t -> range (fun ((l, c), _) -> Queue.add (l, c, t) lb_info.hardlines) hardline
    | Ifflat (doc1, doc2) ->
        let doc1 = to_pprint lb_info doc1 in
        let doc2 = to_pprint lb_info doc2 in
        ifflat doc1 doc2

  let ( ^^ ) doc1 doc2 = match (doc1, doc2) with Empty, _ -> doc2 | _, Empty -> doc1 | _, _ -> Cat (doc1, doc2)

  let repeat n doc =
    let rec go n acc = if n = 0 then acc else go (n - 1) (doc ^^ acc) in
    go n Empty

  let blank n = repeat n (Char ' ')

  let break n = Ifflat (blank n, Hardline Desired)

  let empty = Empty

  let hardline = Hardline Desired

  let require_hardline = Hardline Required

  let nest n doc = Nest (n, doc)

  let align doc = Align doc

  let char c = Char c

  let string s = String s

  let utf8string s = Utf8string s

  let group doc = Group doc

  let space = char ' '

  let enclose l r x = l ^^ x ^^ r

  let parens = enclose (char '(') (char ')')

  let ifflat doc1 doc2 = Ifflat (doc1, doc2)

  let separate_map sep f xs = Util.fold_left_index (fun n acc x -> if n = 0 then f x else acc ^^ sep ^^ f x) Empty xs

  let separate sep xs = separate_map sep (fun x -> x) xs

  let concat_map_last f xs =
    Util.fold_left_index_last (fun n last acc x -> if n = 0 then f last x else acc ^^ f last x) Empty xs

  let prefix n b x y = Group (x ^^ Nest (n, break b ^^ y))

  let infix n b op x y = prefix n b (x ^^ blank b ^^ op) y

  let surround n b opening contents closing = opening ^^ Nest (n, break b ^^ contents) ^^ break b ^^ closing

  let repeat n doc =
    let rec go n acc = if n = 0 then acc else go (n - 1) (doc ^^ acc) in
    go n empty

  let lines s = List.map string (Util.split_on_char '\n' s)

  let block_comment_lines col s =
    let lines = Util.split_on_char '\n' s in
    List.mapi
      (fun n line ->
        if n = 0 || col > String.length line then string line
        else (
          (* Check we aren't deleting any content when adjusting the
             indentation of a block comment. *)
          let prefix = String.sub line 0 col in
          if prefix = String.make col ' ' then string (String.sub line col (String.length line - col))
          else (* TODO: Maybe we should provide a warning here? *)
            string line
        )
      )
      lines
end

open PPrintWrapper

let doc_id (Id_aux (id_aux, _)) = string (match id_aux with Id v -> v | Operator op -> "operator " ^ op)

type opts = {
  (* Controls the bracketing of operators by underapproximating the
     precedence level of the grammar as we print *)
  precedence : int;
  (* True if we are in a statement-like context. Controls how
     if-then-else statements are formatted *)
  statement : bool;
}

let default_opts = { precedence = 10; statement = true }

(* atomic lowers the allowed precedence of binary operators to zero,
   forcing them to always be bracketed *)
let atomic opts = { opts with precedence = 0 }

(* nonatomic raises the allowed precedence to the maximum, so nothing
   is bracketed. *)
let nonatomic opts = { opts with precedence = 10 }

(* subatomic forces even some atomic constructs to be bracketed, by
   setting the allowed precedence below zero *)
let subatomic opts = { opts with precedence = -1 }

let precedence n opts = { opts with precedence = n }

let atomic_parens opts doc = if opts.precedence <= 0 then parens doc else doc

let subatomic_parens opts doc = if opts.precedence < 0 then parens doc else doc

(* While everything in Sail is an expression, for formatting we
   recognize that some constructs will appear as either statement-like
   or expression-like depending on where they occur. For example, and
   if then else may be used as either a ternary:

   if x then y else z // like `x ? y : z`

   or as a statement

   if x then {
       y
   } else {
       z
   }

   These functions allow switching between these formatting modes *)
let expression_like opts = { opts with statement = false }

let statement_like opts = { opts with statement = true }

let operator_precedence = function
  | "=" -> (10, precedence 1, nonatomic, 1)
  | ":" -> (0, subatomic, subatomic, 1)
  | ".." -> (10, atomic, atomic, 0)
  | "@" -> (6, precedence 5, precedence 6, 1)
  | _ -> (10, subatomic, subatomic, 1)

let max_precedence infix_chunks =
  List.fold_left
    (fun max_prec infix_chunk ->
      match infix_chunk with
      | Infix_op op ->
          let prec, _, _, _ = operator_precedence op in
          max prec max_prec
      | _ -> max_prec
    )
    0 infix_chunks

let intersperse_operator_precedence = function "@" -> (6, precedence 5) | _ -> (10, subatomic)

let ternary_operator_precedence = function
  | "..", "=" -> (0, atomic, atomic, nonatomic)
  | ":", "=" -> (0, atomic, nonatomic, nonatomic)
  | _ -> (10, subatomic, subatomic, subatomic)

let unary_operator_precedence = function
  | "throw" -> (0, nonatomic, space)
  | "return" -> (0, nonatomic, space)
  | "internal_return" -> (0, nonatomic, space)
  | "*" -> (10, atomic, empty)
  | "-" -> (10, atomic, empty)
  | "2^" -> (10, atomic, empty)
  | _ -> (10, subatomic, empty)

let can_hang chunks = match Queue.peek_opt chunks with Some (Comment _) -> false | _ -> true

let opt_delim s = ifflat empty (string s)

let softline = break 0

let prefix_parens n x y =
  x ^^ ifflat space (space ^^ char '(') ^^ nest n (softline ^^ y) ^^ softline ^^ ifflat empty (char ')')

let surround_hardline h n b opening contents closing =
  let b = if h then hardline else break b in
  group (opening ^^ nest n (b ^^ contents) ^^ b ^^ closing)

type config = { indent : int; preserve_structure : bool; line_width : int; ribbon_width : float }

let default_config = { indent = 4; preserve_structure = false; line_width = 120; ribbon_width = 1. }

let known_key k = k = "indent" || k = "preserve_structure" || k = "line_width" || k = "ribbon_width"

let int_option k = function
  | `Int n -> Some n
  | json ->
      Reporting.simple_warn
        (Printf.sprintf "Argument for key %s must be an integer, got %s instead. Using default value." k
           (Yojson.Basic.to_string json)
        );
      None

let bool_option k = function
  | `Bool n -> Some n
  | json ->
      Reporting.simple_warn
        (Printf.sprintf "Argument for key %s must be a boolean, got %s instead. Using default value." k
           (Yojson.Basic.to_string json)
        );
      None

let float_option k = function
  | `Int n -> Some (float_of_int n)
  | `Float n -> Some n
  | json ->
      Reporting.simple_warn
        (Printf.sprintf "Argument for key %s must be a number, got %s instead. Using default value." k
           (Yojson.Basic.to_string json)
        );
      None

let get_option ~key:k ~keys:ks ~read ~default:d =
  List.assoc_opt k ks |> (fun opt -> Option.bind opt (read k)) |> Option.value ~default:d

let config_from_json (json : Yojson.Basic.t) =
  match json with
  | `Assoc keys ->
      begin
        match List.find_opt (fun (k, _) -> not (known_key k)) keys with
        | Some (k, _) -> Reporting.simple_warn (Printf.sprintf "Unknown key %s in formatting config" k)
        | None -> ()
      end;
      {
        indent = get_option ~key:"indent" ~keys ~read:int_option ~default:default_config.indent;
        preserve_structure =
          get_option ~key:"preserve_structure" ~keys ~read:bool_option ~default:default_config.preserve_structure;
        line_width = get_option ~key:"line_width" ~keys ~read:int_option ~default:default_config.line_width;
        ribbon_width = get_option ~key:"ribbon_width" ~keys ~read:float_option ~default:default_config.ribbon_width;
      }
  | _ -> raise (Reporting.err_general Parse_ast.Unknown "Invalid formatting configuration")

module type CONFIG = sig
  val config : config
end

module Make (Config : CONFIG) = struct
  let indent = Config.config.indent
  let preserve_structure = Config.config.preserve_structure

  let rec doc_chunk ?(ungroup_tuple = false) ?(toplevel = false) opts = function
    | Atom s -> string s
    | Chunks chunks -> doc_chunks opts chunks
    | Delim s -> string s ^^ space
    | Opt_delim s -> opt_delim s
    | String_literal s -> utf8string ("\"" ^ String.escaped s ^ "\"")
    | App (id, args) ->
        doc_id id
        ^^ group
             (surround indent 0 (char '(')
                (separate_map softline (doc_chunks (opts |> nonatomic |> expression_like)) args)
                (char ')')
             )
    | Tuple (l, r, spacing, args) ->
        let group_fn = if ungroup_tuple then fun x -> x else group in
        group_fn
          (surround indent spacing (string l) (separate_map softline (doc_chunks (nonatomic opts)) args) (string r))
    | Intersperse (op, args) ->
        let outer_prec, prec = intersperse_operator_precedence op in
        let doc =
          group (separate_map (space ^^ string op ^^ space) (doc_chunks (opts |> prec |> expression_like)) args)
        in
        if outer_prec > opts.precedence then parens doc else doc
    | Spacer (line, n) -> if line then repeat n hardline else repeat n space
    | Unary (op, exp) ->
        let outer_prec, inner_prec, spacing = unary_operator_precedence op in
        let doc = string op ^^ spacing ^^ doc_chunks (opts |> inner_prec |> expression_like) exp in
        if outer_prec > opts.precedence then parens doc else doc
    | Infix_sequence infix_chunks ->
        let outer_prec = max_precedence infix_chunks in
        let doc =
          separate_map empty
            (function
              | Infix_prefix op -> string op
              | Infix_op op -> space ^^ string op ^^ space
              | Infix_chunks chunks -> doc_chunks (opts |> atomic |> expression_like) chunks
              )
            infix_chunks
        in
        if outer_prec > opts.precedence then parens doc else doc
    | Binary (lhs, op, rhs) ->
        let outer_prec, lhs_prec, rhs_prec, spacing = operator_precedence op in
        let doc =
          infix indent spacing (string op)
            (doc_chunks (opts |> lhs_prec |> expression_like) lhs)
            (doc_chunks (opts |> rhs_prec |> expression_like) rhs)
        in
        if outer_prec > opts.precedence then parens doc else doc
    | Ternary (x, op1, y, op2, z) ->
        let outer_prec, x_prec, y_prec, z_prec = ternary_operator_precedence (op1, op2) in
        let doc =
          prefix indent 1
            (doc_chunks (opts |> x_prec |> expression_like) x
            ^^ space ^^ string op1 ^^ space
            ^^ doc_chunks (opts |> y_prec |> expression_like) y
            ^^ space ^^ string op2
            )
            (doc_chunks (opts |> z_prec |> expression_like) z)
        in
        if outer_prec > opts.precedence then parens doc else doc
    | If_then_else (bracing, i, t, e) ->
        let insert_braces = opts.statement || bracing.then_brace || bracing.else_brace in
        let i = doc_chunks (opts |> nonatomic |> expression_like) i in
        let t =
          if insert_braces && (not preserve_structure) && not bracing.then_brace then doc_chunk opts (Block (true, [t]))
          else doc_chunks (opts |> nonatomic |> expression_like) t
        in
        let e =
          if insert_braces && (not preserve_structure) && not bracing.else_brace then doc_chunk opts (Block (true, [e]))
          else doc_chunks (opts |> nonatomic |> expression_like) e
        in
        separate space [string "if"; i; string "then"; t; string "else"; e] |> atomic_parens opts
    | If_then (bracing, i, t) ->
        let i = doc_chunks (opts |> nonatomic |> expression_like) i in
        let t =
          if opts.statement && (not preserve_structure) && not bracing then doc_chunk opts (Block (true, [t]))
          else doc_chunks (opts |> nonatomic |> expression_like) t
        in
        separate space [string "if"; i; string "then"; t] |> atomic_parens opts
    | Vector_updates (exp, updates) ->
        let opts = opts |> nonatomic |> expression_like in
        let exp_doc = doc_chunks opts exp in
        surround indent 0
          (char '[' ^^ exp_doc ^^ space ^^ string "with" ^^ space)
          (group (separate_map (char ',' ^^ break 1) (doc_chunk opts) updates))
          (char ']')
        |> atomic_parens opts
    | Index (exp, ix) ->
        let exp_doc = doc_chunks (opts |> atomic |> expression_like) exp in
        let ix_doc = doc_chunks (opts |> nonatomic |> expression_like) ix in
        exp_doc ^^ surround indent 0 (char '[') ix_doc (char ']') |> subatomic_parens opts
    | Exists ex ->
        let ex_doc =
          doc_chunks (atomic opts) ex.vars
          ^^ char ',' ^^ break 1
          ^^ doc_chunks (nonatomic opts) ex.constr
          ^^ char '.' ^^ break 1
          ^^ doc_chunks (nonatomic opts) ex.typ
        in
        enclose (char '{') (char '}') (align ex_doc)
    | Function_typ ft ->
        separate space
          [
            group (doc_chunks opts ft.lhs);
            (if ft.mapping then string "<->" else string "->");
            group (doc_chunks opts ft.rhs);
          ]
    | Typ_quant typq ->
        group
          (align
             (string "forall" ^^ space
             ^^ nest 2
                  (doc_chunks opts typq.vars
                  ^^
                  match typq.constr_opt with
                  | None -> char '.'
                  | Some constr -> char ',' ^^ break 1 ^^ doc_chunks opts constr ^^ char '.'
                  )
             )
          )
        ^^ break 1
    | Struct_update (exp, fexps) ->
        surround indent 1 (char '{')
          (doc_chunks opts exp ^^ space ^^ string "with" ^^ break 1 ^^ separate_map (break 1) (doc_chunks opts) fexps)
          (char '}')
    | Comment (comment_type, n, col, contents) -> begin
        match comment_type with
        | Lexer.Comment_line -> blank n ^^ string "//" ^^ string contents ^^ require_hardline
        | Lexer.Comment_block -> (
            (* Allow a linebreak after a block comment with newlines. This prevents formatting like:
               /* comment line 1
                  comment line 2 */exp
               by forcing exp on a newline if the comment contains linebreaks
            *)
            match block_comment_lines col contents with
            | [l] -> blank n ^^ string "/*" ^^ l ^^ string "*/" ^^ space
            | ls -> blank n ^^ group (align (string "/*" ^^ separate hardline ls ^^ string "*/")) ^^ require_hardline
          )
      end
    | Function f ->
        let sep = hardline ^^ string "and" ^^ space in
        let clauses =
          match f.funcls with
          | [] -> Reporting.unreachable (id_loc f.id) __POS__ "Function with no clauses found"
          | [funcl] -> doc_funcl f.return_typ_opt opts funcl
          | funcl :: funcls ->
              doc_funcl f.return_typ_opt opts funcl ^^ sep ^^ separate_map sep (doc_funcl None opts) f.funcls
        in
        string "function"
        ^^ (if f.clause then space ^^ string "clause" else empty)
        ^^ space ^^ doc_id f.id
        ^^ (match f.typq_opt with Some typq -> space ^^ doc_chunks opts typq | None -> empty)
        ^^ clauses ^^ hardline
    | Val vs ->
        let doc_binding (target, name) =
          string target ^^ char ':' ^^ space ^^ char '"' ^^ utf8string name ^^ char '"'
        in
        string "val" ^^ space ^^ doc_id vs.id
        ^^ group
             ( match vs.extern_opt with
             | Some extern ->
                 space ^^ char '=' ^^ space
                 ^^ string (if extern.pure then "pure" else "monadic")
                 ^^ space
                 ^^ surround indent 1 (char '{')
                      (separate_map (char ',' ^^ break 1) doc_binding extern.bindings)
                      (char '}')
             | None -> empty
             )
        ^^ space ^^ char ':'
        ^^ group
             (nest indent
                ((match vs.typq_opt with Some typq -> space ^^ doc_chunks opts typq | None -> space)
                ^^ doc_chunks opts vs.typ
                )
             )
    | Enum e ->
        string "enum" ^^ space ^^ doc_id e.id
        ^^ group
             (( match e.enum_functions with
              | Some enum_functions ->
                  space ^^ string "with" ^^ space ^^ align (separate_map softline (doc_chunks opts) enum_functions)
              | None -> empty
              )
             ^^ space ^^ char '=' ^^ space
             ^^ surround indent 1 (char '{') (separate_map softline (doc_chunks opts) e.members) (char '}')
             )
    | Pragma (pragma, arg) -> char '$' ^^ string pragma ^^ space ^^ string arg ^^ hardline
    | Block (always_hardline, exps) ->
        let exps =
          map_last
            (fun no_semi chunks -> doc_block_exp_chunks (opts |> nonatomic |> statement_like) no_semi chunks)
            exps
        in
        let sep = if always_hardline || List.exists snd exps then hardline else break 1 in
        let exps = List.map fst exps in
        surround_hardline always_hardline indent 1 (char '{') (separate sep exps) (char '}') |> atomic_parens opts
    | Block_binder (binder, x, y) ->
        if can_hang y then
          separate space
            [string (binder_keyword binder); doc_chunks (atomic opts) x; char '='; doc_chunks (nonatomic opts) y]
        else
          separate space [string (binder_keyword binder); doc_chunks (atomic opts) x; char '=']
          ^^ nest 4 (hardline ^^ doc_chunks (nonatomic opts) y)
    | Binder (binder, x, y, z) ->
        prefix indent 1
          (separate space
             [
               string (binder_keyword binder);
               doc_chunks (atomic opts) x;
               char '=';
               doc_chunks (nonatomic opts) y;
               string "in";
             ]
          )
          (doc_chunks (nonatomic opts) z)
    | Match m ->
        let kw1, kw2 = match_keywords m.kind in
        string kw1 ^^ space
        ^^ doc_chunks (nonatomic opts) m.exp
        ^^ Option.fold ~none:empty ~some:(fun k -> space ^^ string k) kw2
        ^^ space
        ^^ surround indent 1 (char '{') (separate_map hardline (doc_pexp_chunks opts) m.cases) (char '}')
        |> atomic_parens opts
    | Foreach loop ->
        let to_keyword = string (if loop.decreasing then "downto" else "to") in
        string "foreach" ^^ space
        ^^ group
             (surround indent 0 (char '(')
                (separate (break 1)
                   ([
                      doc_chunks (opts |> atomic) loop.var;
                      string "from" ^^ space ^^ doc_chunks (opts |> atomic |> expression_like) loop.from_index;
                      to_keyword ^^ space ^^ doc_chunks (opts |> atomic |> expression_like) loop.to_index;
                    ]
                   @
                   match loop.step with
                   | Some step -> [string "by" ^^ space ^^ doc_chunks (opts |> atomic |> expression_like) step]
                   | None -> []
                   )
                )
                (char ')')
             )
        ^^ space
        ^^ group (doc_chunks (opts |> nonatomic |> statement_like) loop.body)
    | While loop ->
        let measure =
          match loop.termination_measure with
          | Some chunks ->
              string "termination_measure" ^^ space
              ^^ group (surround indent 1 (char '{') (doc_chunks opts chunks) (char '}'))
              ^^ space
          | None -> empty
        in
        let cond = doc_chunks (opts |> nonatomic |> expression_like) loop.cond in
        let body = doc_chunks (opts |> nonatomic |> statement_like) loop.body in
        if loop.repeat_until then
          string "repeat" ^^ space ^^ measure ^^ body ^^ space ^^ string "until" ^^ space ^^ cond
        else string "while" ^^ space ^^ measure ^^ cond ^^ space ^^ string "do" ^^ space ^^ body
    | Field (exp, id) -> doc_chunks (subatomic opts) exp ^^ char '.' ^^ doc_id id
    | Raw str -> separate hardline (lines str)

  and doc_pexp_chunks_pair opts pexp =
    let pat = doc_chunks opts pexp.pat in
    let body = doc_chunks opts pexp.body in
    match pexp.guard with
    | None -> (pat, body)
    | Some guard -> (separate space [pat; string "if"; doc_chunks opts guard], body)

  and doc_pexp_chunks opts pexp =
    let guarded_pat, body = doc_pexp_chunks_pair opts pexp in
    separate space [guarded_pat; string "=>"; body]

  and doc_funcl return_typ_opt opts (header, pexp) =
    let return_typ =
      match return_typ_opt with
      | Some chunks -> space ^^ prefix_parens indent (string "->") (doc_chunks opts chunks) ^^ space
      | None -> space
    in
    doc_chunks opts header
    ^^
    match pexp.guard with
    | None ->
        (if pexp.funcl_space then space else empty)
        ^^ group (doc_chunks ~ungroup_tuple:true opts pexp.pat ^^ return_typ)
        ^^ string "=" ^^ space ^^ doc_chunks opts pexp.body
    | Some guard ->
        parens (separate space [doc_chunks opts pexp.pat; string "if"; doc_chunks opts guard])
        ^^ return_typ ^^ string "=" ^^ space ^^ doc_chunks opts pexp.body

  (* Format an expression in a block, optionally terminating it with a
     semicolon. If the expression has a trailing comment then we will
     format as:

     doc; // comment

     In this case a hardline must be inserted by the block formatter, so
     we return and additional boolean to indicate this. *)
  and doc_block_exp_chunks opts no_semi chunks =
    let chunks = Queue.to_seq chunks |> List.of_seq in
    let requires_hardline = ref false in
    let terminator = if no_semi then empty else char ';' in
    let doc =
      concat_map_last
        (fun last chunk ->
          if last then (
            match line_comment_opt chunk with
            | Some contents ->
                requires_hardline := true;
                terminator ^^ space ^^ string "//" ^^ string contents ^^ require_hardline
            | None -> doc_chunk opts chunk ^^ terminator
          )
          else doc_chunk opts chunk
        )
        chunks
    in
    (group doc, !requires_hardline)

  and doc_chunks ?(ungroup_tuple = false) opts chunks =
    Queue.fold (fun doc chunk -> doc ^^ doc_chunk ~ungroup_tuple opts chunk) empty chunks

  let to_string doc =
    let b = Buffer.create 1024 in
    let lb_info = empty_linebreak_info () in
    PPrint.ToBuffer.pretty Config.config.ribbon_width Config.config.line_width b (to_pprint lb_info doc);
    (Buffer.contents b, lb_info)

  let fixup ?(debug = false) lb_info s =
    let buf = Buffer.create (String.length s) in
    let column = ref 0 in
    let line = ref 0 in
    (* The amount of spaces since the last desired hardline *)
    let pending_spaces = ref 0 in
    (* after_hardline is true after a hardline (either desired or
       required) before we see any non-whitespace character. *)
    let after_hardline = ref false in
    (* true if we require a hardline. If we encounter any non-newline
       (or space) character when this is true, print a
       hardline. Encountering a desired hardline means the requirement
       has been satisifed so we set it to false. *)
    let require_hardline = ref false in
    String.iter
      (fun c ->
        let rec pop_dedents () =
          begin
            match Queue.peek_opt lb_info.dedents with
            | Some (l, c, amount) when l < !line || (l = !line && c = !column) ->
                (* This happens when the formatter removes trailing
                   whitespace premptively, so we never reach the dedent
                   column. *)
                if l < !line && debug then Buffer.add_string buf Util.(">" ^ string_of_int c |> yellow |> clear);
                if !after_hardline && l = !line then pending_spaces := !pending_spaces - amount;
                if debug then Buffer.add_string buf Util.("D" ^ string_of_int amount |> green |> clear);
                ignore (Queue.take lb_info.dedents);
                pop_dedents ()
            | _ -> ()
          end
        in
        pop_dedents ();

        if c = '\n' then (
          begin
            match Queue.take_opt lb_info.hardlines with
            | Some (l, c, hardline_type) -> begin
                match hardline_type with
                | Desired ->
                    if debug then Buffer.add_string buf Util.("H" |> red |> clear);
                    Buffer.add_char buf '\n';
                    pending_spaces := 0;
                    if !require_hardline then require_hardline := false;
                    after_hardline := true
                | Required ->
                    if debug then Buffer.add_string buf Util.("R" |> red |> clear);
                    require_hardline := true;
                    after_hardline := true
              end
            | None ->
                Reporting.unreachable Parse_ast.Unknown __POS__ (Printf.sprintf "Missing hardline %d %d" !line !column)
          end;
          incr line;
          column := 0
        )
        else (
          if c = ' ' then incr pending_spaces
          else (
            if !require_hardline then (
              Buffer.add_char buf '\n';
              require_hardline := false
            );
            if !pending_spaces > 0 then Buffer.add_string buf (String.make !pending_spaces ' ');
            Buffer.add_char buf c;
            after_hardline := false;
            pending_spaces := 0
          );
          incr column
        )
      )
      s;
    Buffer.contents buf

  let format_defs_once ?(debug = false) filename source comments defs =
    let chunks = chunk_defs source comments defs in
    if debug then Queue.iter (prerr_chunk "") chunks;
    let doc = Queue.fold (fun doc chunk -> doc ^^ doc_chunk ~toplevel:true default_opts chunk) empty chunks in
    if debug then (
      let formatted, lb_info = to_string (doc ^^ hardline) in
      let debug_src = fixup ~debug lb_info formatted in
      prerr_endline debug_src
    );
    let formatted, lb_info = to_string (doc ^^ hardline) in
    fixup lb_info formatted |> fixup_comments ~filename |> discard_extra_trailing_newlines

  let format_defs ?(debug = false) filename source comments defs =
    let open Initial_check in
    let f1 = format_defs_once ~debug filename source comments defs in
    let comments, defs = parse_file_from_string ~filename ~contents:f1 in
    let f2 = format_defs_once ~debug filename f1 comments defs in
    let comments, defs = parse_file_from_string ~filename ~contents:f2 in
    let f3 = format_defs_once ~debug filename f2 comments defs in
    if f2 <> f3 then (
      print_endline f2;
      print_endline f3;
      raise (Reporting.err_general Parse_ast.Unknown filename)
    );
    f3
end
