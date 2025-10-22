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

open Parse_ast
open Chunk_ast

module IntMap = Util.IntMap

let id_loc (Id_aux (_, l)) = l

let rec map_last f = function
  | [] -> []
  | [x] -> [f true x]
  | x :: xs ->
      let x = f false x in
      x :: map_last f xs

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

(** We implement a small wrapper around a subset of the PPrint API to track line breaks and dedents (points where the
    indentation level decreases), re-implementing a few core combinators. *)
module PPrintWrapper = struct
  type hardline_type = Required | Desired

  type lineup = Lineup_start | Lineup_point | Lineup_end

  type document =
    | Empty
    | Weak_space
    | Char of char
    | Lineup_char of lineup * char
    | String of string
    | Utf8string of string
    | Group of document
    | Nest of int * document
    | Align of document
    | Cat of document * document
    | Hardline of hardline_type
    | Ifflat of document * document

  type linebreak_info = {
    hardlines : (int * int * hardline_type) Queue.t;
    dedents : (int * int * int) Queue.t;
    weak_spaces : (int * int) Queue.t;
    lineups : (int * int * lineup) Queue.t;
  }

  let empty_linebreak_info () =
    { hardlines = Queue.create (); dedents = Queue.create (); weak_spaces = Queue.create (); lineups = Queue.create () }

  let rec to_pprint lb_info =
    let open PPrint in
    function
    | Empty -> empty
    | Weak_space -> range (fun (lc, _) -> Queue.add lc lb_info.weak_spaces) (char ' ')
    | Char c -> char c
    | Lineup_char (p, c) -> range (fun ((l, c), _) -> Queue.add (l, c, p) lb_info.lineups) (char c)
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

  let lineup_start c = Lineup_char (Lineup_start, c)

  let lineup_point c = Lineup_char (Lineup_point, c)

  let lineup_end c = Lineup_char (Lineup_end, c)

  (* A weak_space is like a space, but it is empty when it appears before any non-whitespace character in a line. *)
  let weak_space = Weak_space

  let enclose l r x = l ^^ x ^^ r

  let parens = enclose (char '(') (char ')')

  let ifflat doc1 doc2 = Ifflat (doc1, doc2)

  let separate_map sep f xs = Util.fold_left_index (fun n acc x -> if n = 0 then f x else acc ^^ sep ^^ f x) Empty xs

  let separate sep xs = separate_map sep (fun x -> x) xs

  let prefix n b x y = Group (x ^^ Nest (n, break b ^^ y))

  let infix n b op x y = prefix n b (x ^^ blank b ^^ op) y

  let surround n b opening contents closing = opening ^^ Nest (n, break b ^^ contents) ^^ break b ^^ closing

  let repeat n doc =
    let rec go n acc = if n = 0 then acc else go (n - 1) (doc ^^ acc) in
    go n empty

  let lines s = List.map string (Util.split_on_char '\n' s)

  let count_indent line =
    let rec loop i = if i < String.length line && line.[i] = ' ' then loop (i + 1) else i in
    loop 0

  let rtrim str =
    let len = String.length str in
    let rec find_end i =
      if i < 0 then 0
      else if str.[i] = ' ' || str.[i] = '\t' || str.[i] = '\n' || str.[i] = '\r' then find_end (i - 1)
      else i + 1
    in
    let new_len = find_end (len - 1) in
    String.sub str 0 new_len

  let count_lines_min_indent lines =
    let rec loop min_indent lines =
      match lines with
      | line :: rest_of_lines ->
          (* Ignore empty line *)
          if line = "" then loop min_indent rest_of_lines
          else (
            let indent = count_indent line in
            let new_min_indent = min indent min_indent in
            loop new_min_indent rest_of_lines
          )
      | [] -> min_indent
    in
    match lines with _ :: xs -> loop max_int xs | _ -> 0

  let patch_comment_lines_indent col lines =
    let min_indent = count_lines_min_indent lines in
    let right_indent_count = col - min_indent in
    let lines =
      List.mapi
        (fun i l ->
          (* The first_line or empty_line remains unchanged *)
          if i == 0 || l = "" then l
          else if right_indent_count > 0 then String.make (abs right_indent_count) ' ' ^ l
          else l
        )
        lines
    in
    lines

  let block_comment_lines col s =
    let lines = Util.split_on_char '\n' s in
    (* Last line (before */) shouldn't be rtrimed *)
    let lines = List.mapi (fun i l -> if i + 1 = List.length lines then l else rtrim l) lines in
    let lines = patch_comment_lines_indent col lines in
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

  (* TODO: maybe save line_number in ast *)
  let is_single_line_block_comment s =
    let lines = Util.split_on_char '\n' s in
    List.length lines <= 1
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
  | ".." -> (10, atomic, atomic, 1)
  | _ -> (10, subatomic, subatomic, 1)

let unary_operator_precedence = function
  | "throw" -> (0, nonatomic, space)
  | "return" -> (0, nonatomic, space)
  | "internal_return" -> (0, nonatomic, space)
  | "*" -> (0, atomic, empty)
  | "-" -> (0, atomic, empty)
  | "2^" -> (10, atomic, empty)
  | _ -> (10, subatomic, empty)

let max_precedence infix_chunks =
  List.fold_left
    (fun max_prec infix_chunk ->
      match infix_chunk with
      | Infix_prefix op ->
          let prec, _, _ = unary_operator_precedence op in
          max prec max_prec
      | Infix_op op ->
          let prec, _, _, _ = operator_precedence op in
          max prec max_prec
      | _ -> max_prec
    )
    0 infix_chunks

let longest_operator infix_chunks =
  List.fold_left
    (fun max_len infix_chunk -> match infix_chunk with Infix_op op -> max (String.length op) max_len | _ -> max_len)
    0 infix_chunks

let intersperse_operator_precedence = function "@" -> (6, precedence 5) | _ -> (10, subatomic)

let ternary_operator_precedence = function
  | "..", "=" -> (0, atomic, atomic, nonatomic)
  | ":", "=" -> (0, atomic, nonatomic, nonatomic)
  | _ -> (10, subatomic, subatomic, subatomic)

let can_hang chunks =
  match Queue.peek_opt chunks with
  | Some (Comment (t, _, _, contents, _)) -> (
      match t with Comment_block -> is_single_line_block_comment contents | _ -> false
    )
  | _ -> true

let can_hang_bracketed chunks =
  match Queue.peek_opt chunks with
  | Some (Block _) -> true
  | Some (Struct_update _) -> true
  | Some (Match _) -> true
  | Some (App _) -> true
  | _ -> false

let is_block chunks = match Queue.peek_opt chunks with Some (Block _) -> true | _ -> false

let opt_delim s = ifflat empty (string s)

let softline = break 0

let prefix_parens n x y =
  x ^^ ifflat space (space ^^ char '(') ^^ nest n (softline ^^ y) ^^ softline ^^ ifflat empty (char ')')

let surround_hardline h n b opening contents closing =
  let b = if h then hardline else break b in
  opening ^^ nest n (b ^^ contents) ^^ b ^^ closing

type infix_style = Prefix_lineup | Prefix

let infix_style_of_string = function "prefix_lineup" -> Some Prefix_lineup | "prefix" -> Some Prefix | _ -> None

type config = {
  indent : int;
  preserve_structure : bool;
  line_width : int;
  ribbon_width : float;
  infix_style : infix_style;
}

let default_config =
  { indent = 4; preserve_structure = false; line_width = 120; ribbon_width = 1.; infix_style = Prefix_lineup }

let known_key k =
  k = "indent" || k = "preserve_structure" || k = "line_width" || k = "ribbon_width" || k = "infix_style"

let int_option k = function
  | `Int n -> Some n
  | json ->
      Reporting.simple_warn
        (Printf.sprintf "Argument for key %s must be an integer, got %s instead. Using default value." k
           (Yojson.Safe.to_string json)
        );
      None

let bool_option k = function
  | `Bool n -> Some n
  | json ->
      Reporting.simple_warn
        (Printf.sprintf "Argument for key %s must be a boolean, got %s instead. Using default value." k
           (Yojson.Safe.to_string json)
        );
      None

let float_option k = function
  | `Int n -> Some (float_of_int n)
  | `Float n -> Some n
  | json ->
      Reporting.simple_warn
        (Printf.sprintf "Argument for key %s must be a number, got %s instead. Using default value." k
           (Yojson.Safe.to_string json)
        );
      None

let enum_option f k = function
  | `String s ->
      let res = f s in
      if Option.is_none res then
        Reporting.simple_warn (Printf.sprintf "Argument for key %s was not a recognized setting. Using default value." k);
      res
  | json ->
      Reporting.simple_warn
        (Printf.sprintf "Argument for key %s must be a string, got %s instead. Using default value." k
           (Yojson.Safe.to_string json)
        );
      None

let get_option ~key:k ~keys:ks ~read ~default:d =
  List.assoc_opt k ks |> (fun opt -> Option.bind opt (read k)) |> Option.value ~default:d

let config_from_json (json : Yojson.Safe.t) =
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
        infix_style =
          get_option ~key:"infix_style" ~keys ~read:(enum_option infix_style_of_string)
            ~default:default_config.infix_style;
      }
  | _ -> raise (Reporting.err_general Parse_ast.Unknown "Invalid formatting configuration")

module type CONFIG = sig
  val config : config
end

let rec can_chunks_list_wrap cqs =
  match cqs with
  | [] -> true
  | [cq] -> (
      match List.of_seq (Queue.to_seq cq) with
      | [] -> true
      | [c] -> (
          match c with
          (* Atom is ok *)
          | Atom _ -> true
          (* {{{ Atom }}} is ok *)
          | Block (_, exps) -> can_chunks_list_wrap exps
          | If_then_else (_, i, t, e) -> can_chunks_list_wrap [t; e]
          | _ -> false
        )
      | c :: cq ->
          can_chunks_list_wrap [Queue.of_seq (List.to_seq [c])] && can_chunks_list_wrap [Queue.of_seq (List.to_seq cq)]
    )
  | cq :: cqs -> can_chunks_list_wrap [cq] && can_chunks_list_wrap cqs

module Make (Config : CONFIG) = struct
  let indent = Config.config.indent
  let preserve_structure = Config.config.preserve_structure
  let infix_style = Config.config.infix_style

  let rec doc_chunk ?(ungroup_tuple = false) ?(toplevel = false) opts = function
    | Atom s -> string s
    | Chunks chunks -> doc_chunks opts chunks
    | Delim s -> string s ^^ space
    | Opt_delim s -> opt_delim s
    | String_literal s -> utf8string ("\"" ^ String.escaped s ^ "\"")
    | Multiline_string_literal lines ->
        string "\"\"\"" ^^ hardline ^^ separate_map hardline string lines ^^ hardline ^^ string "\"\"\""
    | Attribute (attr, arg) ->
        (* Reset opts to defaults, so attributes are always formatted
          the same no matter where they appear. *)
        string "$[" ^^ string attr ^^ space ^^ doc_chunks default_opts arg ^^ char ']'
    | App (id, args) -> (
        match args with
        | [] -> doc_id id ^^ string "()"
        | _ ->
            doc_id id
            ^^ group
                 (surround indent 0 (char '(')
                    (separate_map softline (doc_chunks (opts |> nonatomic |> expression_like)) args)
                    (char ')')
                 )
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
        let longest_op = longest_operator infix_chunks in
        let doc =
          separate_map empty
            (function
              | Infix_prefix op -> string op
              | Infix_op op ->
                  let op_w = String.length op in
                  let padding =
                    match infix_style with
                    | Prefix_lineup -> ifflat space (repeat (longest_op - op_w + 1) space)
                    | Prefix -> space
                  in
                  break 1 ^^ string op ^^ padding
              | Infix_chunks chunks ->
                  let nesting = match infix_style with Prefix_lineup -> longest_op + 1 | Prefix -> indent in
                  nest nesting (doc_chunks (opts |> atomic |> expression_like) chunks)
              )
            infix_chunks
        in
        let start_padding =
          match infix_style with Prefix_lineup -> ifflat empty (repeat (longest_op + 1) space) | Prefix -> empty
        in
        let doc = start_padding ^^ doc in
        group (align (if outer_prec > opts.precedence then parens doc else doc))
    | Binary (lhs, op, rhs) ->
        let outer_prec, lhs_prec, rhs_prec, spacing = operator_precedence op in
        let doc =
          infix indent spacing (string op)
            (doc_chunks (opts |> lhs_prec |> expression_like) lhs)
            (doc_chunks (opts |> rhs_prec |> expression_like) rhs)
        in
        if outer_prec > opts.precedence then parens doc else doc
    | Vector_binary (lhs, op, rhs) ->
        infix indent 1 (string op)
          (doc_chunks (opts |> nonatomic |> expression_like) lhs)
          (doc_chunks (opts |> nonatomic |> expression_like) rhs)
    | Assign (x, ternary, op, z) -> (
        match ternary with
        | None ->
            let x_doc = doc_chunks (nonatomic opts) x in
            let z_doc = doc_chunks (nonatomic opts) z in
            let rhs = if can_hang_bracketed z then space ^^ z_doc else nest indent (break 1 ^^ z_doc) in
            group (x_doc ^^ space ^^ char '=' ^^ rhs)
        | Some (t_op, y) ->
            let outer_prec, x_prec, y_prec, z_prec = ternary_operator_precedence (t_op, op) in
            let doc =
              prefix indent 1
                (doc_chunks (opts |> x_prec |> expression_like) x
                ^^ space ^^ string t_op ^^ space
                ^^ doc_chunks (opts |> y_prec |> expression_like) y
                ^^ space ^^ string op
                )
                (doc_chunks (opts |> z_prec |> expression_like) z)
            in
            if outer_prec > opts.precedence then parens doc else doc
      )
    | If_then_else (bracing, i, t, e) ->
        let have_braces = bracing.then_brace || bracing.else_brace in
        let insert_braces = (opts.statement || have_braces) && not preserve_structure in
        let i = doc_chunks (opts |> nonatomic |> expression_like) i in
        let t =
          if insert_braces && not bracing.then_brace then doc_chunk opts (Block (true, [t]))
          else doc_chunks (opts |> nonatomic |> expression_like) t
        in
        let e =
          if insert_braces && not bracing.else_brace then doc_chunk opts (Block (true, [e]))
          else doc_chunks (opts |> nonatomic |> expression_like) e
        in
        if not (have_braces || insert_braces) then
          string "if" ^^ space ^^ i ^^ break 1 ^^ string "then" ^^ space ^^ t ^^ break 1 ^^ string "else" ^^ space ^^ e
          |> atomic_parens opts |> align |> group
        else (
          let ite_part kw doc = string kw ^^ space ^^ doc in
          ite_part "if" i ^^ weak_space ^^ ite_part "then" t ^^ weak_space ^^ ite_part "else" e
          |> atomic_parens opts |> group
        )
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
        align
          (char '[' ^^ ifflat empty space ^^ exp_doc ^^ space ^^ string "with"
          ^^ nest 2 (break 1 ^^ separate_map (char ',' ^^ break 1) (doc_chunks opts) updates)
          ^^ break 0 ^^ char ']'
          )
        |> atomic_parens opts |> group
    | Index (exp, ix) ->
        let exp_doc = doc_chunks (opts |> atomic |> expression_like) exp in
        let ix_doc = doc_chunks (opts |> nonatomic |> expression_like) ix in
        let ix_doc = group (surround_hardline false indent 0 (char '[') ix_doc (char ']')) in
        exp_doc ^^ ix_doc
    | Exists ex ->
        let ex_doc =
          doc_chunks (atomic opts) ex.vars
          ^^ (match ex.constr with Some cs -> char ',' ^^ break 1 ^^ doc_chunks (nonatomic opts) cs | None -> empty)
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
        ^^ space
    | Struct_update (exp, fexps) ->
        surround indent 1 (char '{')
          (doc_chunks opts exp ^^ space ^^ string "with" ^^ break 1 ^^ separate_map (break 1) (doc_chunks opts) fexps)
          (char '}')
    | Comment (comment_type, n, col, contents, _) -> begin
        match comment_type with
        | Comment_line -> blank n ^^ string "//" ^^ string contents ^^ require_hardline
        | Comment_block -> (
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
    | Doc_comment { contents; comment_type } -> (
        match comment_type with
        | Comment_block ->
            let ls = block_comment_lines 0 contents in
            align (string "/*!" ^^ separate hardline ls ^^ string "*/") ^^ require_hardline
        | Comment_line ->
            let ls = String.split_on_char '\n' contents in
            align (string "///" ^^ separate_map (hardline ^^ string "///") string ls) ^^ require_hardline
      )
    | Function f ->
        let sep = hardline ^^ string "and" ^^ space in
        let clauses =
          match f.funcls with
          | [] -> Reporting.unreachable (id_loc f.id) __POS__ "Function with no clauses found"
          | [funcl] -> doc_funcl f.hanging f.typq_opt f.return_typ_opt opts funcl
          | funcl :: funcls ->
              doc_funcl f.hanging f.typq_opt f.return_typ_opt opts funcl
              ^^ sep
              ^^ separate_map sep (doc_funcl false None None opts) f.funcls
        in
        string "function"
        ^^ (if f.clause then space ^^ string "clause" else empty)
        ^^ space ^^ doc_id f.id ^^ clauses ^^ hardline
    | Val vs ->
        let doc_binding (target, name) =
          string target ^^ char ':' ^^ space ^^ char '"' ^^ utf8string name ^^ char '"'
        in
        string "val" ^^ space ^^ doc_id vs.id
        ^^ group
             ( match vs.extern_opt with
             | Some extern ->
                 space ^^ char '=' ^^ space
                 ^^ string (if extern.pure then "pure" else "impure")
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
        let always_hardline =
          match exps with [x] -> if can_chunks_list_wrap exps then false else always_hardline | _ -> always_hardline
        in
        let exps =
          map_last
            (fun no_semi chunks -> doc_block_exp_chunks (opts |> nonatomic |> statement_like) no_semi chunks)
            exps
        in
        let sep = if always_hardline || List.exists snd exps then hardline else break 1 in
        let exps = List.map fst exps in
        surround_hardline always_hardline indent 1 (char '{') (separate sep exps) (char '}') |> atomic_parens opts
    | Block_binder (binder, x, y) ->
        (* If the body is braced or otherwise bracketed, then the bracketing construct will take care of indentation *)
        if can_hang_bracketed y then
          separate space
            [string (binder_keyword binder); doc_chunks (atomic opts) x; char '='; doc_chunks (nonatomic opts) y]
        else if can_hang y then
          nest indent
            (separate space
               [string (binder_keyword binder); doc_chunks (atomic opts) x; char '='; doc_chunks (nonatomic opts) y]
            )
        else
          separate space [string (binder_keyword binder); doc_chunks (atomic opts) x; char '=']
          ^^ nest indent (hardline ^^ doc_chunks (nonatomic opts) y)
    | Binder (binder, x, y, z) ->
        group
          (separate space
             [
               string (binder_keyword binder);
               doc_chunks (atomic opts) x;
               char '=';
               doc_chunks (nonatomic opts) y;
               string "in";
             ]
          )
        ^^ break 1
        ^^ doc_chunks (nonatomic opts) z
    | Match m ->
        let opener, closer = if m.aligned then (lineup_start '{', lineup_end '}') else (char '{', char '}') in
        let kw1, kw2 = match_keywords m.kind in
        string kw1 ^^ space
        ^^ doc_chunks (nonatomic opts) m.exp
        ^^ Option.fold ~none:empty ~some:(fun k -> space ^^ string k) kw2
        ^^ space
        ^^ surround indent 1 opener (separate_map hardline (doc_pexp_chunks m.aligned opts) m.cases) closer
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
        ^^
        if is_block loop.body then space ^^ group (doc_chunks (opts |> nonatomic |> statement_like) loop.body)
        else nest indent (hardline ^^ group (doc_chunks (opts |> nonatomic |> statement_like) loop.body))
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

  and doc_pexp_chunks aligned opts pexp =
    let guarded_pat, body = doc_pexp_chunks_pair opts pexp in
    let arrow = if aligned then lineup_point '=' ^^ char '>' else string "=>" in
    let doc = separate space [guarded_pat; arrow; body] in
    match pexp.attr with
    | Some attr ->
        let attr = doc_chunks opts attr in
        attr ^^ parens doc ^^ char ','
    | None -> doc

  and doc_funcl hanging typq_opt return_typ_opt opts (header, pexp) =
    let return_typ =
      match return_typ_opt with
      | Some chunks -> space ^^ prefix_parens indent (string "->") (doc_chunks opts chunks) ^^ space
      | None -> space
    in
    let typq = match typq_opt with None -> empty | Some typq -> space ^^ doc_chunks opts typq in
    let paren_args doc = if pexp.funcl_space then parens doc else doc in
    doc_chunks opts header
    ^^
    match pexp.guard with
    | None ->
        group (typq ^^ paren_args (doc_chunks ~ungroup_tuple:true opts pexp.pat) ^^ return_typ)
        ^^ string "="
        ^^
        if is_block pexp.body || hanging then space ^^ doc_chunks opts pexp.body
        else nest indent (hardline ^^ doc_chunks opts pexp.body)
    | Some guard ->
        typq
        ^^ parens (separate space [doc_chunks opts pexp.pat; string "if"; doc_chunks opts guard])
        ^^ return_typ ^^ string "=" ^^ space ^^ doc_chunks opts pexp.body

  (* Format an expression in a block, optionally terminating it with a
     semicolon. If the expression has a trailing comment then we will
     format as:

     doc; // comment

     In this case a hardline must be inserted by the block formatter, so
     we return and additional boolean to indicate this. *)
  and doc_block_exp_chunks opts no_semi chunks =
    let requires_hardline = ref false in
    let terminator = if no_semi then empty else char ';' in
    let rec splice_into_doc chunks doc_acc =
      match Queue.peek_opt chunks with
      | Some chunk ->
          let _ = Queue.pop chunks in
          let doc_acc = ref (doc_acc ^^ doc_chunk opts chunk) in
          let doc_acc =
            match (chunk, Queue.peek_opt chunks) with
            | Comment _, _ -> !doc_acc
            | Spacer _, _ -> !doc_acc
            | _, Some (Comment (_, _, _, _, trailing)) ->
                doc_acc := !doc_acc ^^ terminator;
                (* if current is not a Comment or Spacer, and next is not trailing, then insert a hardline *)
                if not trailing then doc_acc := !doc_acc ^^ hardline;
                doc_acc := !doc_acc ^^ doc_chunk opts (Queue.pop chunks);
                if Queue.peek_opt chunks = None then requires_hardline := true;
                !doc_acc
            | _, None -> !doc_acc ^^ terminator
            | _, _ -> !doc_acc
          in
          splice_into_doc chunks doc_acc
      | None -> doc_acc
    in
    let doc = splice_into_doc chunks empty in
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
    let last_newline = ref 0 in
    let all_lineups = ref [] in
    let current_lineup = ref None in
    let lineup_nesting = ref 0 in

    let add_newline () =
      Buffer.add_char buf '\n';
      last_newline := Buffer.length buf
    in

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
                    add_newline ();
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
          if c = ' ' then (
            match Queue.peek_opt lb_info.weak_spaces with
            | Some (l, c) when l = !line && c = !column ->
                ignore (Queue.take lb_info.weak_spaces);
                if !after_hardline then (if debug then Buffer.add_string buf Util.("W" |> magenta |> bold |> clear))
                else (
                  if debug then Buffer.add_string buf Util.("W" |> blue |> clear);
                  incr pending_spaces
                )
            | _ -> incr pending_spaces
          )
          else (
            if !require_hardline then (
              add_newline ();
              require_hardline := false
            );
            if !pending_spaces > 0 then Buffer.add_string buf (String.make !pending_spaces ' ');
            Buffer.add_char buf c;
            after_hardline := false;
            pending_spaces := 0
          );

          ( match Queue.peek_opt lb_info.lineups with
          | Some (l, c, lineup_type) when l = !line && c = !column ->
              ( match lineup_type with
              | Lineup_start -> (
                  match !current_lineup with None -> current_lineup := Some [] | Some _ -> incr lineup_nesting
                )
              | Lineup_point -> (
                  match !current_lineup with
                  | Some lineup when !lineup_nesting = 0 ->
                      let offset = Buffer.length buf in
                      current_lineup := Some (lineup @ [(offset, !last_newline)])
                  | _ -> ()
                )
              | Lineup_end -> (
                  match !current_lineup with
                  | None -> ()
                  | Some lineup ->
                      if !lineup_nesting = 0 then (
                        all_lineups := !all_lineups @ [lineup];
                        current_lineup := None
                      )
                      else decr lineup_nesting
                )
              );
              ignore (Queue.take lb_info.lineups)
          | _ -> ()
          );

          incr column
        )
      )
      s;

    let lineup_map =
      List.map
        (fun lineup ->
          let indent = List.fold_left (fun m (n, ln) -> max m (n - ln)) 0 lineup in
          List.map (fun (n, ln) -> (n, indent - (n - ln))) lineup
        )
        !all_lineups
      |> List.flatten |> List.to_seq |> IntMap.of_seq
    in

    let unaligned = Buffer.contents buf in
    let buf = Buffer.create (String.length unaligned) in
    String.iteri
      (fun offset c ->
        ( match IntMap.find_opt (offset + 1) lineup_map with
        | Some align -> Buffer.add_string buf (String.make align ' ')
        | None -> ()
        );
        Buffer.add_char buf c
      )
      unaligned;
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

  let format_defs ?(debug = false) filename source comments starting_defs =
    let open Initial_check in
    let open Parse_ast_diff in
    let f1 = format_defs_once ~debug filename source comments starting_defs in
    let comments, defs = parse_file_from_string ~filename ~contents:f1 in
    let f2 = format_defs_once ~debug filename f1 comments defs in
    let comments, defs = parse_file_from_string ~filename ~contents:f2 in
    let f3 = format_defs_once ~debug filename f2 comments defs in
    if f2 <> f3 then (
      prerr_endline f2;
      prerr_endline f3;
      raise (Reporting.err_general Parse_ast.Unknown filename)
    );
    ( match diff_list ~at:Parse_ast.Unknown diff_def starting_defs defs with
    | Some difference ->
        prerr_endline f3;
        raise
          (Reporting.err_general difference
             (Printf.sprintf "Found difference in syntax tree here after formatting %s" filename)
          )
    | None -> ()
    );
    f3
end
