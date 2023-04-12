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

let tabwidth = 4
let preserve_structure = false

let rec map_last f = function
  | [] -> []
  | [x] -> [f true x]
  | x :: xs ->
     let x = f false x in
     x :: map_last f xs

let rec map_sep_last ~default:d ~last:g f = function
  | [] -> [], d
  | [x] -> [], g x
  | x :: xs ->
     let x = f x in
     let xs, l = map_sep_last ~default:d ~last:g f xs in
     (x :: xs, l)

let line_comment_opt = function
  | Comment (Lexer.Comment_line, _, contents) -> Some contents
  | _ -> None

(** We implement a small wrapper around a subset of the PPrint API to
    track line breaks and dedents (points where the indentation level
    decreases), re-implementing a few core combinators. *)
module PPrintWrapper = struct
  type document =
    | Empty
    | Char of char
    | String of string
    | Utf8string of string
    | Group of document
    | Nest of int * document
    | Align of document
    | Cat of document * document
    | Hardline
    | Ifflat of document * document
    | Blank of int

  type linebreak_info = {
      hardlines : (int * int) Queue.t;
      dedents: (int * int * int) Queue.t;
    }

  let empty_linebreak_info () = {
      hardlines = Queue.create ();
      dedents = Queue.create ();
    }

  let rec to_pprint lb_info =
    let open PPrint in
    function
    | Empty ->
       empty
    | Char c ->
       char c
    | String s ->
       string s
    | Utf8string s ->
       utf8string s
    | Group doc ->
       group (to_pprint lb_info doc)
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
    | Hardline ->
       range (fun (e, _) -> Queue.add e lb_info.hardlines) hardline
    | Ifflat (doc1, doc2) ->
       let doc1 = to_pprint lb_info doc1 in
       let doc2 = to_pprint lb_info doc2 in
       ifflat doc1 doc2
    | Blank n ->
       blank n

  let break n = Ifflat (Blank n, Hardline)

  let (^^) doc1 doc2 =
    match doc1, doc2 with
    | Empty, _ -> doc2
    | _, Empty -> doc1
    | _, _ -> Cat (doc1, doc2)

  let empty = Empty

  let hardline = Hardline

  let nest n doc = Nest (n, doc)

  let align doc = Align doc

  let char c = Char c

  let string s = String s

  let utf8string s = Utf8string s

  let group doc = Group doc

  let blank n = Blank n

  let space = char ' '

  let enclose l r x = l ^^ x ^^ r

  let parens = enclose (char '(') (char ')')

  let ifflat doc1 doc2 = Ifflat (doc1, doc2)

  let concat = List.fold_left (^^) Empty

  let separate_map sep f xs =
    Util.fold_left_index (fun n acc x ->
        if n = 0 then f x else acc ^^ sep ^^ f x
      ) Empty xs

  let separate sep xs = separate_map sep (fun x -> x) xs

  let concat_map_last f xs =
    Util.fold_left_index_last (fun n last acc x ->
        if n = 0 then
          f last x
        else
          acc ^^ f last x
      ) Empty xs

  let prefix n b x y =
    Group (x ^^ Nest (n, break b ^^ y))

  let infix n b op x y =
    prefix n b (x ^^ Blank b ^^ op) y

  let surround n b opening contents closing =
    opening ^^ Nest (n, break b ^^ contents) ^^ break b ^^ closing

  let twice doc = doc ^^ doc

  let repeat n doc =
    let rec go n acc =
      if n = 0 then
        acc
      else
        go (n - 1) (doc ^^ acc)
    in
    go n empty

  let lines s = List.map string (Util.split_on_char '\n' s)

end

open PPrintWrapper

let doc_id (Id_aux (id_aux, _)) =
  string (match id_aux with
          | Id v -> v
          | Operator op -> "operator " ^ op)

type opts = {
    (* Controls the bracketing of operators by underapproximating the
       precedence level of the grammar as we print *)
    precedence : int;
    (* True if we are in a statement-like context. Controls how
       if-then-else statements are formatted *)
    statement : bool
  }

let default_opts = {
    precedence = 10;
    statement = true
  }

(* atomic lowers the allowed precedence of binary operators to zero,
   forcing them to always be bracketed *)
let atomic opts = { opts with precedence = 0 }

(* nonatomic raises the allowed precedence to the maximum, so nothing
   is bracketed. *)
let nonatomic opts = { opts with precedence = 10 }

(* subatomic forces even some atomic constructs to be bracketed, by
   setting the allowed precedence below zero *)
let subatomic opts = { opts with precedence = -1 }

let atomic_parens opts doc = if opts.precedence <> 10 then parens doc else doc

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
  | "=" -> 10, atomic, nonatomic 
  | ":" -> 0, subatomic, subatomic
  | _ -> 10, subatomic, subatomic

let ternary_operator_precedence = function
  | ("..", "=") -> 0, atomic, atomic, nonatomic
  | (":", "=") -> 0, atomic, nonatomic, nonatomic
  | _ -> 10, subatomic, subatomic, subatomic

let opt_delim s = ifflat empty (string s)

let softline = break 0

let prefix_parens n x y =
  x ^^ ifflat space (space ^^ char '(') ^^ nest n (softline ^^ y) ^^ softline ^^ ifflat empty (char ')')

let chunk_inserts_trailing_hardline = function
  | Comment (Lexer.Comment_line, _, _) -> true
  | _ -> false

let surround_hardline h n b opening contents closing =
  let b = if h then hardline else break b in
  group (opening ^^ nest n (b ^^ contents) ^^ b ^^ closing)

let rec doc_chunk ?toplevel:(toplevel=false) opts = function
  | Atom s -> string s
  | Chunks chunks -> doc_chunks opts chunks
  | Delim s -> string s ^^ space
  | Opt_delim s -> opt_delim s
  | String_literal s ->
     utf8string ("\"" ^ String.escaped s ^ "\"")
  | App (id, args) ->
     doc_id id
     ^^ surround tabwidth 0 (char '(') (separate_map softline (doc_chunks (opts |> nonatomic |> expression_like)) args) (char ')')
  | Tuple (l, r, spacing, args) ->
     surround tabwidth spacing (string l) (separate_map softline (doc_chunks (nonatomic opts)) args) (string r)
  | Intersperse (op, args) ->
     group (separate_map (string op) (doc_chunks (atomic opts)) args)
  | Spacer (line, n) ->
     if line then
       repeat n hardline
     else
       repeat n space
  | Binary (lhs, op, rhs) ->
     let outer_prec, lhs_prec, rhs_prec = operator_precedence op in
     let doc =
       infix tabwidth 1 (string op)
         (doc_chunks (opts |> lhs_prec |> expression_like) lhs)
         (doc_chunks (opts |> rhs_prec |> expression_like) rhs)
     in
     if outer_prec > opts.precedence then (
       parens doc
     ) else (
       doc
     )
  | Ternary (x, op1, y, op2, z) ->
     let outer_prec, x_prec, y_prec, z_prec = ternary_operator_precedence (op1, op2) in
     let doc =
       prefix tabwidth 1 (doc_chunks (opts |> x_prec |> expression_like) x
                          ^^ space ^^ string op1 ^^ space
                          ^^ doc_chunks (opts |> y_prec |> expression_like) y
                          ^^ space ^^ string op2)
         (doc_chunks (opts |> z_prec |> expression_like) z)
     in
     if outer_prec > opts.precedence then (
       parens doc
     ) else (
       doc
     )
  | If_then_else (bracing, i, t, e) ->
     let insert_braces = opts.statement || bracing.then_brace || bracing.else_brace in
     let i = doc_chunks (opts |> nonatomic |> expression_like) i in
     let t =
       if insert_braces && not preserve_structure && not bracing.then_brace then (
         doc_chunk opts (Block (true, [t]))
       ) else (
         doc_chunks (opts |> nonatomic |> expression_like) t
       ) in
     let e =
       if insert_braces && not preserve_structure && not bracing.else_brace then (
         doc_chunk opts (Block (true, [e]))
       ) else (
         doc_chunks (opts |> nonatomic |> expression_like) e
       ) in
     separate space [string "if"; i; string "then"; t; string "else"; e]
     |> atomic_parens opts
  | If_then (bracing, i, t) ->
     let i = doc_chunks (opts |> nonatomic |> expression_like) i in
     let t =
       if opts.statement && not preserve_structure && not bracing then (
         doc_chunk opts (Block (true, [t]))
       ) else (
         doc_chunks (opts |> nonatomic |> expression_like) t
       ) in
     separate space [string "if"; i; string "then"; t]
     |> atomic_parens opts
  | Vector_updates (exp, updates) ->
     let opts = opts |> nonatomic |> expression_like in
     let exp_doc = doc_chunks opts exp in
     surround tabwidth 0
       (char '[' ^^ exp_doc ^^ space ^^ string "with" ^^ space)
       (group (separate_map (char ',' ^^ break 1) (doc_chunk opts) updates))
       (char ']')
     |> atomic_parens opts
  | Index (exp, ix) ->
     let exp_doc = doc_chunks (opts |> atomic |> expression_like) exp in
     let ix_doc = doc_chunks (opts |> nonatomic |> expression_like) ix in
     exp_doc ^^ surround tabwidth 0 (char '[') ix_doc (char ']')
     |> atomic_parens opts
  | Exists ex ->
     let ex_doc =
       doc_chunks (atomic opts) ex.vars
       ^^ char ',' ^^ break 1
       ^^ doc_chunks (nonatomic opts) ex.constr
       ^^ char '.' ^^ break 1
       ^^ doc_chunks (nonatomic opts) ex.typ
     in
     enclose (char '{') (char '}') (align ex_doc)
  | Typ_quant typq ->
     group (
         align (
             string "forall" ^^ space
             ^^ nest 2 (
                    doc_chunks opts typq.vars
                    ^^ (match typq.constr_opt with
                        | None -> char '.'
                        | Some constr -> char ',' ^^ break 1 ^^ doc_chunks opts constr ^^ char '.')
                  )
           )
         ^^ break 1
       )
  | Comment (comment_type, n, contents) ->
     begin match comment_type with
     | Lexer.Comment_line ->
        blank n ^^ string "//" ^^ string contents ^^ hardline
     | Lexer.Comment_block ->
        (* Allow a linebreak after a block comment with newlines. This prevents formatting like:
           /* comment line 1
              comment line 2 */exp */
           by forcing exp on a newline if the comment contains linebreaks
         *)
        match lines contents with
        | [l] -> blank n ^^ string "/*" ^^ l ^^ string "*/" ^^ space
        | ls ->
           align (blank n ^^ string "/*" ^^ separate hardline ls ^^ string "*/")
           ^^ softline
     end
  | Function f ->
     let sep = hardline ^^ string "and" ^^ space in
     let clauses = match f.funcls with
       | [] -> Reporting.unreachable (id_loc f.id) __POS__ "Function with no clauses found"
       | [funcl] -> doc_funcl f.return_typ_opt opts funcl
       | funcl :: funcls ->
          doc_funcl f.return_typ_opt opts funcl ^^ sep ^^ separate_map sep (doc_funcl None opts) f.funcls in
     string "function" ^^ space ^^ doc_id f.id
     ^^ (match f.typq_opt with Some typq -> space ^^ doc_chunks opts typq | None -> empty)
     ^^ clauses ^^ hardline
  | Val vs ->
     let doc_binding (target, name) = string target ^^ char ':' ^^ space ^^ char '"' ^^ utf8string name ^^ char '"' in
     string "val" ^^ space ^^ (if vs.is_cast then string "cast" ^^ space else empty) ^^ doc_id vs.id ^^ space
     ^^ group (match vs.extern_opt with
               | Some extern ->
                  char '=' ^^ space
                  ^^ string (if extern.pure then "pure" else "monadic") ^^ space
                  ^^ surround tabwidth 1 (char '{') (separate_map (break 1) doc_binding extern.bindings) (char '}')
               | None -> empty)
  | Pragma (pragma, arg) ->
     string "$pragma" ^^ space ^^ string arg ^^ hardline
  | Block (always_hardline, exps) ->
     let exps = map_last (fun no_semi chunks -> doc_block_exp_chunks (opts |> nonatomic |> statement_like) no_semi chunks) exps in
     let require_hardline = always_hardline || List.exists snd exps in
     let exps = List.map fst exps in
     let sep = if require_hardline then hardline else break 1 in
     surround_hardline always_hardline tabwidth 1 (char '{') (separate sep exps) (char '}')
     |> atomic_parens opts
  | Block_binder (binder, x, y) ->
     separate space [string (binder_keyword binder); doc_chunks (atomic opts) x; char '='; doc_chunks (nonatomic opts) y]
  | Binder (binder, x, y, z) ->
     prefix tabwidth 1
       (separate space [string (binder_keyword binder); doc_chunks (atomic opts) x; char '='; doc_chunks (nonatomic opts) y; string "in"])
       (doc_chunks (nonatomic opts) z)
  | Match m ->
     let kw1, kw2 = match_keywords m.kind in
     string kw1 ^^ space ^^ doc_chunks (nonatomic opts) m.exp
     ^^ (Option.fold ~none:empty ~some:(fun k -> space ^^ string k) kw2) ^^ space
     ^^ surround tabwidth 1 (char '{') (separate_map hardline (doc_pexp_chunks opts) m.cases) (char '}')
     |> atomic_parens opts
  | Field (exp, id) ->
     doc_chunks (subatomic opts) exp ^^ char '.' ^^ doc_id id

and doc_pexp_chunks_pair opts pexp =
  let pat = doc_chunks opts pexp.pat in
  let body = doc_chunks opts pexp.body in
  match pexp.guard with
  | None -> pat, body
  | Some guard ->
     separate space [pat; string "if"; doc_chunks opts guard],
     body

and doc_pexp_chunks opts pexp =
  let guarded_pat, body = doc_pexp_chunks_pair opts pexp in
  separate space [guarded_pat; string "=>"; body]

and doc_funcl return_typ_opt opts pexp =
  let return_typ = match return_typ_opt with
    | Some chunks -> space ^^ prefix_parens tabwidth (string "->") (doc_chunks opts chunks) ^^ space
    | None -> space in
  match pexp.guard with
  | None ->
     (if pexp.funcl_space then space else empty)
     ^^ group (
            doc_chunks opts pexp.pat
            ^^ return_typ
          )
     ^^ string "="
     ^^ space ^^ doc_chunks opts pexp.body
  | Some guard ->
     parens (separate space [doc_chunks opts pexp.pat; string "if"; doc_chunks opts guard])
     ^^ return_typ
     ^^ string "="
     ^^ space ^^ doc_chunks opts pexp.body

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
    concat_map_last (fun last chunk ->
        if last then
          match line_comment_opt chunk with
          | Some contents ->
             requires_hardline := true;
             terminator ^^ space ^^ string "//" ^^ string contents
          | None -> doc_chunk opts chunk ^^ terminator
        else
          doc_chunk opts chunk
      ) chunks in
  (group doc, !requires_hardline)

and doc_chunks opts chunks =
  Queue.fold (fun doc chunk ->
      doc ^^ doc_chunk opts chunk
    ) empty chunks

let to_string doc =
  let b = Buffer.create 1024 in
  let lb_info = empty_linebreak_info () in
  PPrint.ToBuffer.pretty 1. 80 b (to_pprint lb_info doc);
  Queue.iter (fun (l, c, n) ->
      Printf.eprintf "Dedent %d:%d:%d\n" l c n
    ) lb_info.dedents;
  Buffer.contents b, lb_info

let fixup lb_info s =
  let buf = Buffer.create (String.length s) in
  let column = ref 0 in
  let line = ref 0 in
  let space_after_hardline = ref None in
  String.iter (fun c ->
      Printf.eprintf "%d:%d\n" !line !column;
      let rec pop_dedents () =
        begin match Queue.peek_opt lb_info.dedents with
        | Some (l, c, amount) when l = !line && c = !column ->
           begin match !space_after_hardline with
           | Some n -> space_after_hardline := Some (n - 4)
           | None -> ()
           end;
           Buffer.add_string buf Util.("D" ^ string_of_int amount |> green |> clear);
           ignore (Queue.pop lb_info.dedents);
           pop_dedents ()
        | _ -> ();
        end
      in
      pop_dedents ();
      begin match Queue.peek_opt lb_info.hardlines with
      | Some (l, c) when l = !line && c = !column ->
         Buffer.add_string buf Util.("H" |> red |> clear);
         space_after_hardline := Some 0;
         ignore (Queue.pop lb_info.hardlines)
      | _ -> ();
      end;
      if c = '\n' then (
        incr line;
        column := 0;
        Buffer.add_char buf c
      ) else if c = ' ' then (
        begin match !space_after_hardline with
        | Some n -> space_after_hardline := Some (n + 1)
        | None -> Buffer.add_char buf c
        end;
        incr column
      ) else (
        begin match !space_after_hardline with
        | Some n when n > 0 -> Buffer.add_string buf (String.make n ' ');
        | _ -> ()
        end;
        space_after_hardline := None;
        incr column;
        Buffer.add_char buf c
      )
    ) s;
  Buffer.contents buf

let format_defs comments defs =
  let chunks = chunk_defs comments defs in
  Queue.iter (prerr_chunk "") chunks;
  let doc = Queue.fold (fun doc chunk -> doc ^^ doc_chunk ~toplevel:true default_opts chunk) empty chunks in
  let s, lb_info = to_string (doc ^^ hardline) in
  let s = fixup lb_info s in
  s
