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

let id_loc (Id_aux (_, l)) = l

let rec map_last f = function
  | [] -> []
  | [x] -> [f true x]
  | x :: xs ->
      let x = f false x in
      x :: map_last f xs

let is_sep_point op = Util.list_contains op ["&&"; "||"; "&"; "|"; "^"; "@"]

(* single chunk *)
let is_spacer = function Spacer _ -> true | _ -> false
let is_comment = function Comment (_, _, _, _, _) | Doc_comment _ -> true | _ -> false
let is_block = function Block (_, _) -> true | _ -> false
let is_match = function Match _ -> true | _ -> false
let is_struct = function Struct_update _ -> true | _ -> false
let is_tuple = function Tuple _ -> true | _ -> false
let is_let = function Binder (_, _, _, _) -> true | _ -> false
let is_delim = function Delim _ | Opt_delim _ -> true | _ -> false
let is_binary = function Binary _ -> true | _ -> false
let is_op = function Binary _ -> true | Ternary _ | Infix_sequence _ -> true | _ -> false
let is_if_then_else = function If_then_else _ -> true | _ -> false
let is_if_then = function If_then _ -> true | _ -> false

(* single chunk extra *)
let is_spacer_space = function Spacer (false, _) -> true | _ -> false
let is_spacer_hardline = function Spacer (true, _) -> true | _ -> false
let is_blcok_comment = function Comment (Lexer.Comment_block, _, _, _, _) -> true | _ -> false
let is_if_stmt chunk = is_if_then_else chunk || is_if_then chunk
let is_block_like chunk = is_block chunk || is_match chunk || is_tuple chunk

(* multi chunk *)
let rec is_chunks_match ?(tl_rule = fun c -> is_delim c) ?(skip_hd_rule = is_blcok_comment) hd_rule chunks =
  let skip_index = ref 0 in
  let acc, _ =
    Queue.fold
      (fun (acc, i) chunk ->
        let res =
          match i with
          | i when i = !skip_index ->
              if skip_hd_rule chunk then (
                skip_index := !skip_index + 1;
                acc
              )
              else hd_rule chunk
          | _ -> acc && tl_rule chunk
        in
        (res, i + 1)
      )
      (false, 0) chunks
  in
  acc
let rec is_chunks_block_like =
  is_chunks_match ~tl_rule:(fun c -> is_delim c || is_blcok_comment c || is_spacer c) is_block_like

let rec is_chunks_if_then_else = is_chunks_match is_if_then_else

let find_rtrim_index match_rule chunks =
  let acc, _ =
    Queue.fold
      (fun (acc, i) chunk ->
        let acc = if not (match_rule chunk) then i + 1 else i in
        (acc, i + 1)
      )
      (0, 0) chunks
  in
  acc

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

let surround_hardline ?(nogroup = false) h n b opening contents closing =
  let b = if h then hardline else break b in
  let doc = opening ^^ nest n (b ^^ contents) ^^ b ^^ closing in
  if nogroup then doc else group doc

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

module WrapChecker = struct
  type opt = { strict : bool; in_braces : bool }

  let opt_strict opt = { opt with strict = true }

  let opt_in_braces opt = { opt with in_braces = true }

  let default_opt = { strict = false; in_braces = false }

  let rec check_nowrap opt c =
    match c with
    | Delim _ | Opt_delim _ -> true
    | Atom _ | String_literal _ ->
        (* Atom *)
        true
    | Spacer (newline, n) -> not newline
    | Field (cq, id) ->
        (* zero_extend(fcsr.bits) *)
        check_chunks_nowrap ~opt [cq]
    | Unary (_, cq) ->
        (* (return 1) *)
        check_chunks_nowrap ~opt [cq]
    | Block (_, cqs) ->
        (* {{{ Atom }}} *)
        if List.length cqs > 1 then false else check_chunks_nowrap ~opt:(opt |> opt_in_braces) cqs
    | Infix_sequence infix_chunks ->
        (* i + rs1_val < VLMAX *)
        List.fold_left
          (fun res c ->
            match c with Infix_prefix s | Infix_op s -> res | Infix_chunks cs -> res && check_chunks_nowrap ~opt [cs]
          )
          true infix_chunks
    | Binary (x, op, y) ->
        (* (v128 >> shift)[64..0] *)
        check_chunks_nowrap ~opt [x] && check_chunks_nowrap ~opt [y]
    | Index (cq, ix) ->
        (* regval[31..16] *)
        let opt = opt |> opt_in_braces in
        check_chunks_nowrap ~opt [cq] && check_chunks_nowrap ~opt [ix]
    | App (_, cqs) -> (* func(foo) *) check_chunks_nowrap ~opt cqs
    | Struct_update (exps, fexps) ->
        (* struct { variety = AV_exclusive } *)
        check_chunks_nowrap ~opt [exps] && check_chunks_nowrap ~opt fexps
    | Vector_updates (cq, cs) ->
        (* [foo with a = 1, b = 2] *)
        check_chunks_nowrap ~opt [cq] && List.fold_left (fun res c -> res && check_nowrap opt c) true cs
    | Ternary (x, op1, y, op2, z) ->
        (* with 37..36 = 0b00 *)
        check_chunks_nowrap ~opt [x] && check_chunks_nowrap ~opt [y] && check_chunks_nowrap ~opt [z]
    | Tuple (_, _, _, cqs) -> (* (1, 2) *) check_chunks_nowrap ~opt cqs
    | _ -> false

  and check_nowrap_extra last_check opt c =
    match c with
    | If_then (_, i, t) -> check_chunks_nowrap ~opt [i] && check_chunks_nowrap ~opt [t]
    | If_then_else (_, i, t, e) ->
        (* if (a > 1) then {1} else {2} *)
        check_chunks_nowrap ~opt [i] && check_chunks_nowrap ~opt [t] && check_chunks_nowrap ~opt [e]
    | Comment (Comment_block, _, _, _, _) -> not opt.in_braces
    | Comment _ ->
        if not last_check then false
        else (
          match c with
          | Comment (Comment_line, _, _, _, true) ->
              (* case => (), // comment *)
              (* then 2 // comment *)
              not opt.in_braces
          | Comment (Comment_block, _, _, _, _) -> true
          | _ -> false
        )
    | _ -> false

  and check_chunks_nowrap ?(opt = default_opt) cqs =
    match cqs with
    | [] -> true
    | [cq] ->
        let nest_nowrap_count = ref 0 in
        let len = Queue.length cq in
        let res, _ =
          Queue.fold
            (fun (acc, index) c ->
              let res =
                if (* unit => (), *)
                   is_delim c then true
                else (
                  (* strict rule, for nested chunks *)
                  let res = check_nowrap opt c in
                  if opt.strict then res
                  else (
                    if res then nest_nowrap_count := !nest_nowrap_count + 1;
                    let last_chunk = index = len - 1 in
                    res || check_nowrap_extra last_chunk opt c
                  )
                )
              in
              (acc && res, index + 1)
            )
            (true, 0) cq
        in
        res
    | cq :: cqs -> check_chunks_nowrap ~opt [cq] && check_chunks_nowrap ~opt cqs

  and check_chunks_wrap ?(opt = default_opt) cqs = not (check_chunks_nowrap ~opt cqs)
end

module Make (Config : CONFIG) = struct
  let indent = Config.config.indent
  let preserve_structure = Config.config.preserve_structure

  let chunks_of_chunk c =
    let q = Queue.create () in
    Queue.add c q;
    q

  type opt = {
    ungroup_tuple : bool;
    ungroup_block : bool;
    toplevel : bool;
    wrap : bool;
    binary_rhs : bool;
    skip_spacer : bool;
    end_comment_no_spacer : bool;
  }

  let default_opt =
    {
      ungroup_tuple = false;
      ungroup_block = false;
      toplevel = false;
      wrap = false;
      binary_rhs = false;
      skip_spacer = false;
      end_comment_no_spacer = false;
    }

  let opt_ungroup_tuple opt = { opt with ungroup_tuple = true }
  let opt_toplevel opt = { opt with toplevel = true }
  let opt_wrap opt = { opt with wrap = true }
  let opt_binary_rhs opt = { opt with binary_rhs = true }
  let opt_ungroup_block opt = { opt with ungroup_block = true }

  let rec doc_chunk ?(opt = default_opt) opts = function
    | Atom s -> string s
    | Chunks chunks -> doc_chunks opts chunks
    | Delim s -> string s ^^ space
    | Opt_delim s -> opt_delim s
    | String_literal s -> utf8string ("\"" ^ String.escaped s ^ "\"")
    | App (id, args) ->
        doc_id id
        ^^ group
             ( if Util.list_empty args then (* avoid `let foo = bar(\n)` *)
                 string "()"
               else
                 surround indent 0 (char '(')
                   (separate_map softline (doc_chunks (opts |> nonatomic |> expression_like)) args)
                   (char ')')
             )
    | Tuple (l, r, spacing, args) ->
        let group_fn = if opt.ungroup_tuple then fun x -> x else group in
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
        let chunks_count = ref 0 in

        let op = ref None in
        let prefix = ref None in
        let doc =
          List.fold_left
            (fun acc c ->
              match c with
              | Infix_prefix p ->
                  prefix := Some (String.trim p);
                  acc
              | Infix_chunks cs ->
                  chunks_count := !chunks_count + 1;
                  let doc = doc_chunks (opts |> atomic |> expression_like) cs in
                  let doc =
                    match !prefix with
                    | Some p ->
                        let p = if String.length p = 1 then p else p ^ " " in
                        string p ^^ doc
                    | None -> doc
                  in
                  let doc =
                    match !op with
                    | Some op ->
                        let sep_op_chunk =
                          ifflat space (if is_sep_point op then hardline ^^ repeat indent space else space)
                        in
                        sep_op_chunk ^^ string op ^^ space ^^ group doc
                    | None -> doc
                  in
                  op := None;
                  prefix := None;
                  acc ^^ doc
              | Infix_op o ->
                  op := Some o;
                  acc
            )
            empty infix_chunks
        in
        let doc = group doc in
        if outer_prec > opts.precedence then parens doc else doc
    | Binary (lhs, op, rhs) ->
        let outer_prec, lhs_prec, rhs_prec, spacing = operator_precedence op in
        let doc_l = doc_chunks_rhs (opts |> lhs_prec |> expression_like) lhs in
        let doc_r = doc_chunks_rhs ~opt:(default_opt |> opt_binary_rhs) (opts |> rhs_prec |> expression_like) rhs in
        let sep = repeat spacing space in
        let doc =
          group
            (ifflat
               (doc_l ^^ sep ^^ string op ^^ sep ^^ doc_r)
               ( if is_sep_point op then (
                   let doc_r = string op ^^ sep ^^ group doc_r in
                   doc_l ^^ group (ifflat (sep ^^ doc_r) (nest indent (hardline ^^ doc_r)))
                 )
                 else doc_l ^^ sep ^^ string op ^^ group (sep ^^ doc_r)
               )
            )
        in
        if outer_prec > opts.precedence then parens doc else doc
    | Ternary (x, op1, y, op2, z) ->
        let outer_prec, x_prec, y_prec, z_prec = ternary_operator_precedence (op1, op2) in
        let doc =
          let sep_op1 = if op1 = ".." then empty else space in
          group
            (doc_chunks (opts |> x_prec |> expression_like) x
            ^^ sep_op1 ^^ string op1 ^^ sep_op1
            ^^ doc_chunks (opts |> y_prec |> expression_like) y
            ^^ space ^^ string op2 ^^ break 1
            )
          ^^ doc_chunks_rhs (opts |> z_prec |> expression_like) z
        in
        if outer_prec > opts.precedence then parens doc else doc
    | If_then_else (bracing, i, t, e) ->
        let insert_braces = opts.statement || bracing.then_brace || bracing.else_brace in
        let i_doc = doc_chunks_rhs ~opt (opts |> nonatomic |> expression_like) i in
        (* check_nowrap with strict mode here *)
        let check_opt = WrapChecker.default_opt |> WrapChecker.opt_strict in
        (* if any one can't wrap, then then and else block will expand *)
        let force_wrap =
          WrapChecker.check_chunks_wrap ~opt:check_opt [t] || WrapChecker.check_chunks_wrap ~opt:check_opt [e]
        in
        let t, t_brace =
          if insert_braces && (not preserve_structure) && not bracing.then_brace then
            (chunks_of_chunk (Block (true, [t])), true)
          else (t, bracing.then_brace)
        in
        let e, e_brace =
          if insert_braces && (not preserve_structure) && not bracing.else_brace then
            (chunks_of_chunk (Block (true, [e])), true)
          else (e, bracing.else_brace)
        in
        let doc_chunks_exp ~brace =
          doc_chunks_rhs
            ~opt:
              {
                default_opt with
                ungroup_block = true;
                binary_rhs = not brace;
                wrap = force_wrap;
                skip_spacer = true;
                end_comment_no_spacer = true;
              }
            (opts |> nonatomic |> expression_like)
        in
        let t_doc = doc_chunks_exp ~brace:t_brace t in
        let e_doc = doc_chunks_exp ~brace:e_brace e in
        let doc_i = separate space [string "if"; i_doc] in
        let doc_t = separate space [string "then"; t_doc] in
        let doc_e = separate space [string "else"; e_doc] in
        let res =
          ifflat
            (doc_i ^^ space ^^ doc_t ^^ space ^^ doc_e |> atomic_parens opts)
            (let doc =
               if t_brace then
                 (*
                    if foo then {
                      ...
                    } else {
                      ...
                    }
                 *)
                 group (doc_i ^^ break 1) ^^ doc_t ^^ space ^^ doc_e
               else
                 (*
                    if ...
                    then ...
                    else ...
                 *)
                 doc_i ^^ hardline ^^ doc_t ^^ hardline ^^ doc_e
             in
             let doc = doc |> atomic_parens opts in
             (*
                let a =
                  if_stmt...
             *)
             if opt.binary_rhs then nest indent (hardline ^^ doc) else doc
            )
        in
        group res
    | If_then (bracing, i, t) ->
        let i = doc_chunks_rhs ~opt:default_opt (opts |> nonatomic |> expression_like) i in
        let t =
          if opts.statement && (not preserve_structure) && not bracing then doc_chunk opts (Block (true, [t]))
          else doc_chunks_rhs (opts |> nonatomic |> expression_like) t
        in
        if bracing then
          group (group (string "if" ^^ space ^^ i ^^ ifflat space hardline) ^^ string "then" ^^ space ^^ t)
          |> atomic_parens opts
        else group (string "if" ^^ space ^^ i ^^ string "then" ^^ t) |> atomic_parens opts
    | Vector_updates (exp, updates) ->
        let opts = opts |> nonatomic |> expression_like in
        let exp_doc = doc_chunks opts exp in
        surround indent 0
          (char '[' ^^ exp_doc ^^ space ^^ string "with" ^^ space)
          (group (separate_map (char ',' ^^ break 1) (doc_chunk opts) updates))
          (char ']')
        |> atomic_parens opts
    | Index (exp, ix) ->
        let exp_doc = doc_chunks_rhs (opts |> atomic |> expression_like) exp in
        let exp_doc = group (empty ^^ nest indent exp_doc ^^ empty) in
        let ix_doc = doc_chunks_nowrap_or_surround (opts |> nonatomic |> expression_like) ix in
        exp_doc ^^ char '[' ^^ ix_doc ^^ char ']' |> subatomic_parens opts
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
    | Comment (comment_type, n, col, contents, trailing) -> begin
        match comment_type with
        | Lexer.Comment_line -> blank n ^^ string "//" ^^ string contents ^^ require_hardline
        | Lexer.Comment_block -> (
            (* Allow a linebreak after a block comment with newlines. This prevents formatting like:
               /* comment line 1
                  comment line 2 */exp
               by forcing exp on a newline if the comment contains linebreaks
            *)
            match block_comment_lines col contents with
            | [l] ->
                blank n ^^ string "/*" ^^ l ^^ string "*/"
                ^^ if trailing || opt.end_comment_no_spacer then empty else space
            | ls -> blank n ^^ group (align (string "/*" ^^ separate hardline ls ^^ string "*/")) ^^ require_hardline
          )
      end
    | Doc_comment contents ->
        let ls = block_comment_lines 0 contents in
        align (string "/*!" ^^ separate hardline ls ^^ string "*/") ^^ require_hardline
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
          match exps with
          | [x] ->
              if opt.wrap || opt.toplevel then true
              else if not (WrapChecker.check_chunks_wrap exps) then false
              else always_hardline
          | _ -> always_hardline
        in
        let exps =
          map_last
            (fun no_semi chunks -> doc_block_exp_chunks (opts |> nonatomic |> statement_like) no_semi chunks)
            exps
        in
        let sep = if always_hardline || List.exists snd exps then hardline else space in
        let exps = List.map fst exps in
        surround_hardline ~nogroup:opt.ungroup_block always_hardline indent 1 (char '{') (separate sep exps) (char '}')
        |> atomic_parens opts
    | Block_binder (binder, x, y) ->
        let doc_x = group (separate space [string (binder_keyword binder); doc_chunks (atomic opts) x; char '=']) in
        let doc_y = doc_chunks_rhs ~opt:(opt |> opt_binary_rhs) (nonatomic opts) y in
        doc_x ^^ space ^^ doc_y
    | Binder (binder, x, y, z) ->
        let x = doc_chunks_rhs (atomic opts) x in
        let y = doc_chunks_rhs ~opt:(opt |> opt_binary_rhs) (atomic opts) y in
        let doc =
          group (separate space [string (binder_keyword binder); x; char '='; group y] ^^ break 1)
          ^^ separate space [string "in"; hardline]
        in
        Queue.fold
          (fun acc chunk ->
            let doc = doc_chunk opts chunk in
            acc ^^ doc
          )
          doc z
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
        let doc =
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
        in
        let body = doc_chunks_rhs ~opt:(default_opt |> opt_wrap) (opts |> nonatomic |> statement_like) loop.body in
        if is_chunks_block_like loop.body then doc ^^ space ^^ group body
        else doc ^^ nest indent (hardline ^^ group body)
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

  (*
    1. nowrap
      [if cond then x else y]

    2. surround
      [
        let a = 1 in
        a
      ]
  *)
  and doc_chunks_nowrap_or_surround ?(opt = default_opt) opts chunks =
    let doc = Queue.fold (fun doc chunk -> doc ^^ doc_chunk ~opt opts chunk) empty chunks in
    let wrap = WrapChecker.check_chunks_wrap [chunks] in
    if wrap then surround_hardline true indent 1 empty doc empty else doc

  (* format rhs chunks
     - if_stmt:
       let a = if cond then x else y
       let a =
         if cond then {
           x
         } else {
           y
         }

     - block like:
       let a = match|tuple|block {
         ...
       }

     - other
       - nowrap:
         let a = 1 // comment

       - prefix:
         let a =
           let a = 1 in
           a
  *)
  and doc_chunks_rhs ?(opt = default_opt) opts chunks =
    let rtrim_index = find_rtrim_index is_spacer chunks in
    let doc, _ =
      Queue.fold
        (fun (doc, i) chunk ->
          let res = if opt.skip_spacer && i >= rtrim_index then doc else doc ^^ doc_chunk ~opt opts chunk in
          (res, i + 1)
        )
        (empty, 0) chunks
    in
    (* test if can nowrap with optional strict mode *)
    let doc =
      (* add prefix for multi line chunks if wrap *)
      if is_chunks_if_then_else chunks then if opt.toplevel then nest indent (group (softline ^^ doc)) else doc
      else (
        let block_like = is_chunks_block_like chunks in
        let doc = if block_like then doc else group doc in
        let nowrap = not (WrapChecker.check_chunks_wrap [chunks]) in
        if nowrap || block_like then doc else nest indent (group (break 1 ^^ doc))
      )
    in
    doc

  and doc_pexp_chunks_pair opts pexp =
    let pat = doc_chunks opts pexp.pat in
    let body = doc_chunks_rhs ~opt:(default_opt |> opt_ungroup_tuple) opts pexp.body in
    match pexp.guard with
    | None -> (pat, body)
    | Some guard -> (separate space [pat; string "if"; doc_chunks opts guard], group body)

  and doc_pexp_chunks opts pexp =
    let guarded_pat, body = doc_pexp_chunks_pair opts pexp in
    group (separate space [guarded_pat; string "=>"; body])

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
        let body_doc = doc_chunks_rhs ~opt:(default_opt |> opt_toplevel) opts pexp.body in
        (if pexp.funcl_space then space else empty)
        ^^ group (doc_chunks ~opt:(default_opt |> opt_ungroup_tuple) opts pexp.pat ^^ return_typ)
        ^^ string "=" ^^ space ^^ body_doc
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
    let requires_hardline = ref false in
    let terminator = if no_semi then empty else char ';' in
    let rec splice_into_doc chunks doc_acc =
      match Queue.peek_opt chunks with
      | Some chunk ->
          let _ = Queue.pop chunks in
          let doc_acc = ref (doc_acc ^^ doc_chunk opts chunk) in
          let doc_acc =
            match (chunk, Queue.peek_opt chunks) with
            | Comment (Lexer.Comment_block, _, _, _, _), _ -> !doc_acc
            | Comment _, _ -> !doc_acc
            | Spacer _, _ -> !doc_acc
            | _, Some (Comment (t, _, _, _, trailing)) ->
                doc_acc := !doc_acc ^^ terminator;
                (* if current is not a Comment or Spacer, and next is not trailing, then insert a hardline *)
                if not trailing then doc_acc := !doc_acc ^^ hardline;
                doc_acc := !doc_acc ^^ doc_chunk opts (Queue.pop chunks);
                if Queue.peek_opt chunks = None && match t with Lexer.Comment_line -> true | _ -> false then
                  requires_hardline := true;
                !doc_acc
            | _, None -> !doc_acc ^^ terminator
            | _, _ -> !doc_acc
          in
          splice_into_doc chunks doc_acc
      | None -> doc_acc
    in
    let doc = splice_into_doc chunks empty in
    (group doc, !requires_hardline)

  and doc_chunks ?(opt = default_opt) opts chunks =
    Queue.fold (fun doc chunk -> doc ^^ doc_chunk ~opt opts chunk) empty chunks

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
    let doc =
      Queue.fold (fun doc chunk -> doc ^^ doc_chunk ~opt:(default_opt |> opt_toplevel) default_opts chunk) empty chunks
    in
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
