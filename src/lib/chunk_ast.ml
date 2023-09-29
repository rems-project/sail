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

let string_of_id_aux = function Id v -> v | Operator v -> v

let string_of_id (Id_aux (id, _)) = string_of_id_aux id

let id_loc (Id_aux (_, l)) = l

let starting_line_num l = match Reporting.simp_loc l with Some (s, _) -> Some s.pos_lnum | None -> None

let starting_column_num l =
  match Reporting.simp_loc l with Some (s, _) -> Some (s.pos_cnum - s.pos_bol) | None -> None

let ending_line_num l = match Reporting.simp_loc l with Some (_, e) -> Some e.pos_lnum | None -> None

type binder = Var_binder | Let_binder | Internal_plet_binder

type if_format = { then_brace : bool; else_brace : bool }

type match_kind = Try_match | Match_match

let match_keywords = function Try_match -> ("try", Some "catch") | Match_match -> ("match", None)

let binder_keyword = function Var_binder -> "var" | Let_binder -> "let" | Internal_plet_binder -> "internal_plet"

let comment_type_delimiters = function Lexer.Comment_line -> ("//", "") | Lexer.Comment_block -> ("/*", "*/")

type infix_chunk = Infix_prefix of string | Infix_op of string | Infix_chunks of chunks

and chunk =
  | Comment of Lexer.comment_type * int * int * string
  | Spacer of bool * int
  | Function of {
      id : id;
      clause : bool;
      rec_opt : chunks option;
      typq_opt : chunks option;
      return_typ_opt : chunks option;
      funcls : (chunks * pexp_chunks) list;
    }
  | Val of { id : id; extern_opt : extern option; typq_opt : chunks option; typ : chunks }
  | Enum of { id : id; enum_functions : chunks list option; members : chunks list }
  | Function_typ of { mapping : bool; lhs : chunks; rhs : chunks }
  | Exists of { vars : chunks; constr : chunks; typ : chunks }
  | Typ_quant of { vars : chunks; constr_opt : chunks option }
  | App of id * chunks list
  | Field of chunks * id
  | Tuple of string * string * int * chunks list
  | Intersperse of string * chunks list
  | Atom of string
  | String_literal of string
  | Pragma of string * string
  | Unary of string * chunks
  | Binary of chunks * string * chunks
  | Ternary of chunks * string * chunks * string * chunks
  | Infix_sequence of infix_chunk list
  | Index of chunks * chunks
  | Delim of string
  | Opt_delim of string
  | Block of (bool * chunks list)
  | Binder of binder * chunks * chunks * chunks
  | Block_binder of binder * chunks * chunks
  | If_then of bool * chunks * chunks
  | If_then_else of if_format * chunks * chunks * chunks
  | Struct_update of chunks * chunks list
  | Match of { kind : match_kind; exp : chunks; aligned : bool; cases : pexp_chunks list }
  | Foreach of {
      var : chunks;
      decreasing : bool;
      from_index : chunks;
      to_index : chunks;
      step : chunks option;
      body : chunks;
    }
  | While of { repeat_until : bool; termination_measure : chunks option; cond : chunks; body : chunks }
  | Vector_updates of chunks * chunk list
  | Chunks of chunks
  | Raw of string

and chunks = chunk Queue.t

and pexp_chunks = { funcl_space : bool; pat : chunks; guard : chunks option; body : chunks }

let add_chunk q chunk = Queue.add chunk q

[@@@coverage off]
let rec prerr_chunk indent = function
  | Comment (comment_type, n, col, contents) ->
      let s, e = comment_type_delimiters comment_type in
      Printf.eprintf "%sComment: blank=%d col=%d %s%s%s\n" indent n col s contents e
  | Spacer (line, w) -> Printf.eprintf "%sSpacer:%b %d\n" indent line w
  | Atom str -> Printf.eprintf "%sAtom:%s\n" indent str
  | String_literal str -> Printf.eprintf "%sString_literal:%s\n" indent str
  | App (id, args) ->
      Printf.eprintf "%sApp:%s\n" indent (string_of_id id);
      List.iteri
        (fun i arg ->
          Printf.eprintf "%s  %d:\n" indent i;
          Queue.iter (prerr_chunk (indent ^ "    ")) arg
        )
        args
  | Tuple (s, e, n, args) ->
      Printf.eprintf "%sTuple:%s %s %d\n" indent s e n;
      List.iteri
        (fun i arg ->
          Printf.eprintf "%s  %d:\n" indent i;
          Queue.iter (prerr_chunk (indent ^ "    ")) arg
        )
        args
  | Intersperse (str, args) ->
      Printf.eprintf "%sIntersperse:%s\n" indent str;
      List.iteri
        (fun i arg ->
          Printf.eprintf "%s  %d:\n" indent i;
          Queue.iter (prerr_chunk (indent ^ "    ")) arg
        )
        args
  | Block (always_hardline, args) ->
      Printf.eprintf "%sBlock: always_hardline=%b\n" indent always_hardline;
      List.iteri
        (fun i arg ->
          Printf.eprintf "%s  %d:\n" indent i;
          Queue.iter (prerr_chunk (indent ^ "    ")) arg
        )
        args
  | Function fn ->
      Printf.eprintf "%sFunction:%s clause=%b\n" indent (string_of_id fn.id) fn.clause;
      begin
        match fn.typq_opt with
        | Some typq ->
            Printf.eprintf "%s  typq:\n" indent;
            Queue.iter (prerr_chunk (indent ^ "    ")) typq
        | None -> ()
      end;
      begin
        match fn.return_typ_opt with
        | Some return_typ ->
            Printf.eprintf "%s  return_typ:\n" indent;
            Queue.iter (prerr_chunk (indent ^ "    ")) return_typ
        | None -> ()
      end;
      List.iteri
        (fun i (funcl_header, funcl) ->
          Printf.eprintf "%s  header %d:\n" indent i;
          Queue.iter (prerr_chunk (indent ^ "    ")) funcl_header;
          Printf.eprintf "%s  pat %d:\n" indent i;
          Queue.iter (prerr_chunk (indent ^ "    ")) funcl.pat;
          begin
            match funcl.guard with
            | Some guard ->
                Printf.eprintf "%s  guard %d:\n" indent i;
                Queue.iter (prerr_chunk (indent ^ "    ")) guard
            | None -> ()
          end;
          Printf.eprintf "%s  body %d:\n" indent i;
          Queue.iter (prerr_chunk (indent ^ "    ")) funcl.body
        )
        fn.funcls
  | Val vs -> Printf.eprintf "%sVal:%s has_extern=%b\n" indent (string_of_id vs.id) (Option.is_some vs.extern_opt)
  | Enum e ->
      Printf.eprintf "%sEnum:%s\n" indent (string_of_id e.id);
      begin
        match e.enum_functions with
        | Some enum_functions ->
            List.iter
              (fun chunks ->
                Printf.eprintf "%s  enum_function:\n" indent;
                Queue.iter (prerr_chunk (indent ^ "    ")) chunks
              )
              enum_functions
        | None -> ()
      end;
      List.iter
        (fun chunks ->
          Printf.eprintf "%s  member:\n" indent;
          Queue.iter (prerr_chunk (indent ^ "    ")) chunks
        )
        e.members
  | Match m ->
      Printf.eprintf "%sMatch:%s %b\n" indent (fst (match_keywords m.kind)) m.aligned;
      Printf.eprintf "%s  exp:\n" indent;
      Queue.iter (prerr_chunk (indent ^ "    ")) m.exp;
      List.iteri
        (fun i funcl ->
          Printf.eprintf "%s  pat %d:\n" indent i;
          Queue.iter (prerr_chunk (indent ^ "    ")) funcl.pat;
          begin
            match funcl.guard with
            | Some guard ->
                Printf.eprintf "%s  guard %d:\n" indent i;
                Queue.iter (prerr_chunk (indent ^ "    ")) guard
            | None -> ()
          end;
          Printf.eprintf "%s  body %d:\n" indent i;
          Queue.iter (prerr_chunk (indent ^ "    ")) funcl.body
        )
        m.cases
  | Function_typ fn_typ ->
      Printf.eprintf "%sFunction_typ: is_mapping=%b\n" indent fn_typ.mapping;
      List.iter
        (fun (name, arg) ->
          Printf.eprintf "%s  %s:\n" indent name;
          Queue.iter (prerr_chunk (indent ^ "    ")) arg
        )
        [("lhs", fn_typ.lhs); ("rhs", fn_typ.rhs)]
  | Foreach loop ->
      Printf.eprintf "%sForeach: downto=%b\n" indent loop.decreasing;
      begin
        match loop.step with
        | Some step ->
            Printf.eprintf "%s  step:\n" indent;
            Queue.iter (prerr_chunk (indent ^ "    ")) step
        | None -> ()
      end;
      List.iter
        (fun (name, arg) ->
          Printf.eprintf "%s  %s:\n" indent name;
          Queue.iter (prerr_chunk (indent ^ "    ")) arg
        )
        [("var", loop.var); ("from", loop.from_index); ("to", loop.to_index); ("body", loop.body)]
  | While loop ->
      Printf.eprintf "%sWhile: repeat_until=%b\n" indent loop.repeat_until;
      begin
        match loop.termination_measure with
        | Some measure ->
            Printf.eprintf "%s  step:\n" indent;
            Queue.iter (prerr_chunk (indent ^ "    ")) measure
        | None -> ()
      end;
      List.iter
        (fun (name, arg) ->
          Printf.eprintf "%s  %s:\n" indent name;
          Queue.iter (prerr_chunk (indent ^ "    ")) arg
        )
        [("cond", loop.cond); ("body", loop.body)]
  | Typ_quant typq ->
      Printf.eprintf "%sTyp_quant:\n" indent;
      List.iter
        (fun (name, arg) ->
          Printf.eprintf "%s  %s:\n" indent name;
          Queue.iter (prerr_chunk (indent ^ "    ")) arg
        )
        ( match typq.constr_opt with
        | Some constr -> [("vars", typq.vars); ("constr", constr)]
        | None -> [("vars", typq.vars)]
        )
  | Pragma (pragma, arg) -> Printf.eprintf "%sPragma:$%s %s\n" indent pragma arg
  | Unary (op, arg) ->
      Printf.eprintf "%sUnary:%s\n" indent op;
      Queue.iter (prerr_chunk (indent ^ "  ")) arg
  | Binary (lhs, op, rhs) ->
      Printf.eprintf "%sBinary:%s\n" indent op;
      List.iter
        (fun (name, arg) ->
          Printf.eprintf "%s  %s:\n" indent name;
          Queue.iter (prerr_chunk (indent ^ "    ")) arg
        )
        [("lhs", lhs); ("rhs", rhs)]
  | Ternary (x, op1, y, op2, z) ->
      Printf.eprintf "%sTernary:%s %s\n" indent op1 op2;
      List.iter
        (fun (name, arg) ->
          Printf.eprintf "%s  %s:\n" indent name;
          Queue.iter (prerr_chunk (indent ^ "    ")) arg
        )
        [("x", x); ("y", y); ("z", z)]
  | Infix_sequence infix_chunks ->
      Printf.eprintf "%sInfix:\n" indent;
      List.iter
        (function
          | Infix_prefix op -> Printf.eprintf "%s  Prefix:%s\n" indent op
          | Infix_op op -> Printf.eprintf "%s  Op:%s\n" indent op
          | Infix_chunks chunks ->
              Printf.eprintf "%s  Chunks:\n" indent;
              Queue.iter (prerr_chunk (indent ^ "    ")) chunks
          )
        infix_chunks
  | Delim str -> Printf.eprintf "%sDelim:%s\n" indent str
  | Opt_delim str -> Printf.eprintf "%sOpt_delim:%s\n" indent str
  | Exists ex ->
      Printf.eprintf "%sExists:\n" indent;
      List.iter
        (fun (name, arg) ->
          Printf.eprintf "%s  %s:\n" indent name;
          Queue.iter (prerr_chunk (indent ^ "    ")) arg
        )
        [("vars", ex.vars); ("constr", ex.constr); ("typ", ex.typ)]
  | Binder _ -> ()
  | Block_binder (binder, binding, exp) ->
      Printf.eprintf "%sBlock_binder:%s\n" indent (binder_keyword binder);
      List.iter
        (fun (name, arg) ->
          Printf.eprintf "%s  %s:\n" indent name;
          Queue.iter (prerr_chunk (indent ^ "    ")) arg
        )
        [("binding", binding); ("exp", exp)]
  | If_then (_, i, t) ->
      Printf.eprintf "%sIf_then:\n" indent;
      List.iter
        (fun (name, arg) ->
          Printf.eprintf "%s  %s:\n" indent name;
          Queue.iter (prerr_chunk (indent ^ "    ")) arg
        )
        [("if", i); ("then", t)]
  | If_then_else (_, i, t, e) ->
      Printf.eprintf "%sIf_then_else:\n" indent;
      List.iter
        (fun (name, arg) ->
          Printf.eprintf "%s  %s:\n" indent name;
          Queue.iter (prerr_chunk (indent ^ "    ")) arg
        )
        [("if", i); ("then", t); ("else", e)]
  | Field (exp, id) ->
      Printf.eprintf "%sField:%s\n" indent (string_of_id id);
      Queue.iter (prerr_chunk (indent ^ "  ")) exp
  | Struct_update (exp, exps) ->
      Printf.eprintf "%sStruct_update:\n" indent;
      Queue.iter (prerr_chunk (indent ^ "    ")) exp;
      Printf.eprintf "%s  with:" indent;
      List.iter (fun exp -> Queue.iter (prerr_chunk (indent ^ "    ")) exp) exps
  | Vector_updates (_exp, _updates) -> Printf.eprintf "%sVector_updates:\n" indent
  | Index (exp, ix) ->
      Printf.eprintf "%sIndex:\n" indent;
      List.iter
        (fun (name, arg) ->
          Printf.eprintf "%s  %s:\n" indent name;
          Queue.iter (prerr_chunk (indent ^ "    ")) arg
        )
        [("exp", exp); ("ix", ix)]
  | Chunks chunks ->
      Printf.eprintf "%sChunks:\n" indent;
      Queue.iter (prerr_chunk (indent ^ "  ")) chunks
  | Raw _ -> Printf.eprintf "%sRaw\n" indent
[@@@coverage on]

let string_of_var (Kid_aux (Var v, _)) = v

let rec pop_header_comments comments chunks l lnum =
  match Stack.top_opt comments with
  | None -> ()
  | Some (Lexer.Comment (comment_type, comment_s, e, contents)) -> begin
      match Reporting.simp_loc l with
      | Some (s, _) when e.pos_cnum < s.pos_cnum && comment_s.pos_lnum = lnum ->
          let _ = Stack.pop comments in
          Queue.add (Comment (comment_type, 0, comment_s.pos_cnum - comment_s.pos_bol, contents)) chunks;
          Queue.add (Spacer (true, 1)) chunks;
          pop_header_comments comments chunks l (lnum + 1)
      | _ -> ()
    end

let chunk_header_comments comments chunks = function
  | [] -> ()
  | DEF_aux (_, l) :: _ -> pop_header_comments comments chunks l 1

(* Pop comments preceeding location into the chunkstream *)
let rec pop_comments ?(spacer = true) comments chunks l =
  match Stack.top_opt comments with
  | None -> ()
  | Some (Lexer.Comment (comment_type, comment_s, e, contents)) -> begin
      match Reporting.simp_loc l with
      | Some (s, _) when e.pos_cnum <= s.pos_cnum ->
          let _ = Stack.pop comments in
          Queue.add (Comment (comment_type, 0, comment_s.pos_cnum - comment_s.pos_bol, contents)) chunks;
          if spacer && e.pos_lnum < s.pos_lnum then Queue.add (Spacer (true, 1)) chunks;
          pop_comments comments chunks l
      | _ -> ()
    end

let rec discard_comments comments (pos : Lexing.position) =
  match Stack.top_opt comments with
  | None -> ()
  | Some (Lexer.Comment (_, _, e, _)) ->
      if e.pos_cnum <= pos.pos_cnum then (
        let _ = Stack.pop comments in
        discard_comments comments pos
      )

let pop_trailing_comment ?space:(n = 0) comments chunks line_num =
  match line_num with
  | None -> false
  | Some lnum -> begin
      match Stack.top_opt comments with
      | Some (Lexer.Comment (comment_type, s, _, contents)) when s.pos_lnum = lnum ->
          let _ = Stack.pop comments in
          Queue.add (Comment (comment_type, n, s.pos_cnum - s.pos_bol, contents)) chunks;
          begin
            match comment_type with Lexer.Comment_line -> true | _ -> false
          end
      | _ -> false
    end

let string_of_kind (K_aux (k, _)) =
  match k with K_type -> "Type" | K_int -> "Int" | K_order -> "Order" | K_bool -> "Bool"

(* Right now, let's just assume we never break up kinded-identifiers *)
let chunk_of_kopt (KOpt_aux (KOpt_kind (special, vars, kind), l)) =
  match (special, kind) with
  | Some c, Some k ->
      Atom (Printf.sprintf "(%s %s : %s)" c (Util.string_of_list " " string_of_var vars) (string_of_kind k))
  | None, Some k -> Atom (Printf.sprintf "(%s : %s)" (Util.string_of_list " " string_of_var vars) (string_of_kind k))
  | None, None -> Atom (Util.string_of_list " " string_of_var vars)
  | _, _ ->
      (* No other KOpt should be parseable *)
      Reporting.unreachable l __POS__ "Invalid KOpt in formatter" [@coverage off]

let chunk_of_lit (L_aux (aux, _)) =
  match aux with
  | L_unit -> Atom "()"
  | L_zero -> Atom "bitzero"
  | L_one -> Atom "bitone"
  | L_true -> Atom "true"
  | L_false -> Atom "false"
  | L_num n -> Atom (Big_int.to_string n)
  | L_hex b -> Atom ("0x" ^ b)
  | L_bin b -> Atom ("0b" ^ b)
  | L_undef -> Atom "undefined"
  | L_string s -> String_literal s
  | L_real r -> Atom r

let rec map_peek f = function
  | x1 :: x2 :: xs ->
      let x1 = f (Some x2) x1 in
      x1 :: map_peek f (x2 :: xs)
  | [x] -> [f None x]
  | [] -> []

let rec map_peek_acc f acc = function
  | x1 :: x2 :: xs ->
      let x1, acc = f acc (Some x2) x1 in
      x1 :: map_peek_acc f acc (x2 :: xs)
  | [x] -> [fst (f acc None x)]
  | [] -> []

let have_linebreak line_num1 line_num2 = match (line_num1, line_num2) with Some p1, Some p2 -> p1 < p2 | _, _ -> false

let have_blank_linebreak line_num1 line_num2 =
  match (line_num1, line_num2) with Some p1, Some p2 -> p1 + 1 < p2 | _, _ -> false

let chunk_delimit ?delim ~get_loc ~chunk comments xs =
  map_peek
    (fun next x ->
      let l = get_loc x in
      let chunks = Queue.create () in
      chunk comments chunks x;

      (* Add a delimiter, which is optional for the last element *)
      begin
        match delim with
        | Some delim ->
            if Option.is_some next then Queue.add (Delim delim) chunks else Queue.add (Opt_delim delim) chunks
        | None -> ()
      end;

      (* If the next delimited expression is on a new line,
         pop any single trailing comment on the same line into
         this chunk sequence.

         If we have multiple trailing comments like:

         arg1 /* block comment */, // line comment
         arg2

         the line comment will be attached to arg2, and the
         block comment to arg1 *)
      let next_line_num = Option.bind next (fun x2 -> starting_line_num (get_loc x2)) in
      if have_linebreak (ending_line_num l) next_line_num then
        ignore (pop_trailing_comment comments chunks (ending_line_num l));

      chunks
    )
    xs

let chunk_infix_token comments chunk_primary (infix_token, _, _) =
  match infix_token with
  | IT_op id -> Infix_op (string_of_id id)
  | IT_prefix id -> (
      match id with
      | Id_aux (Id "__deref", _) -> Infix_prefix "*"
      | Id_aux (Id "pow2", _) -> Infix_prefix "2 ^"
      | Id_aux (Id "negate", _) -> Infix_prefix "-"
      | _ -> Infix_prefix (string_of_id id)
    )
  | IT_primary exp ->
      let chunks = Queue.create () in
      chunk_primary comments chunks exp;
      Infix_chunks chunks

let rec chunk_atyp comments chunks (ATyp_aux (aux, l)) =
  pop_comments comments chunks l;
  let rec_chunk_atyp atyp =
    let chunks = Queue.create () in
    chunk_atyp comments chunks atyp;
    chunks
  in
  match aux with
  | ATyp_parens atyp -> chunk_atyp comments chunks atyp
  | ATyp_id id -> Queue.add (Atom (string_of_id id)) chunks
  | ATyp_var v -> Queue.add (Atom (string_of_var v)) chunks
  | ATyp_lit lit -> Queue.add (chunk_of_lit lit) chunks
  | ATyp_nset set -> Queue.add (Atom ("{" ^ Util.string_of_list ", " Big_int.to_string set ^ "}")) chunks
  | ATyp_in (lhs, rhs) ->
      let lhs_chunks = rec_chunk_atyp lhs in
      let rhs_chunks = rec_chunk_atyp rhs in
      Queue.add (Binary (lhs_chunks, "in", rhs_chunks)) chunks
  | ATyp_infix [(IT_primary lhs, _, _); (IT_op (Id_aux (Id op, _)), _, _); (IT_primary rhs, _, _)] ->
      let lhs_chunks = rec_chunk_atyp lhs in
      let rhs_chunks = rec_chunk_atyp rhs in
      Queue.add (Binary (lhs_chunks, op, rhs_chunks)) chunks
  | ATyp_infix infix_tokens ->
      let infix_chunks = List.map (chunk_infix_token comments chunk_atyp) infix_tokens in
      Queue.add (Infix_sequence infix_chunks) chunks
  | (ATyp_times (lhs, rhs) | ATyp_sum (lhs, rhs) | ATyp_minus (lhs, rhs)) as binop ->
      let op_symbol =
        match binop with
        | ATyp_times _ -> "*"
        | ATyp_sum _ -> "+"
        | ATyp_minus _ -> "-"
        | _ -> Reporting.unreachable l __POS__ "Invalid binary atyp" [@coverage off]
      in
      let lhs_chunks = rec_chunk_atyp lhs in
      let rhs_chunks = rec_chunk_atyp rhs in
      Queue.add (Binary (lhs_chunks, op_symbol, rhs_chunks)) chunks
  | ATyp_exp arg ->
      let lhs_chunks = Queue.create () in
      Queue.add (Atom "2") lhs_chunks;
      let rhs_chunks = rec_chunk_atyp arg in
      Queue.add (Binary (lhs_chunks, "^", rhs_chunks)) chunks
  | ATyp_neg arg ->
      let arg_chunks = rec_chunk_atyp arg in
      Queue.add (Unary ("-", arg_chunks)) chunks
  | ATyp_inc -> Queue.add (Atom "inc") chunks
  | ATyp_dec -> Queue.add (Atom "dec") chunks
  | ATyp_fn (lhs, rhs, _) ->
      let lhs_chunks = rec_chunk_atyp lhs in
      let rhs_chunks = rec_chunk_atyp rhs in
      Queue.add (Function_typ { mapping = false; lhs = lhs_chunks; rhs = rhs_chunks }) chunks
  | ATyp_bidir (lhs, rhs, _) ->
      let lhs_chunks = rec_chunk_atyp lhs in
      let rhs_chunks = rec_chunk_atyp rhs in
      Queue.add (Function_typ { mapping = true; lhs = lhs_chunks; rhs = rhs_chunks }) chunks
  | ATyp_app (Id_aux (Operator op, _), [lhs; rhs]) ->
      let lhs_chunks = rec_chunk_atyp lhs in
      let rhs_chunks = rec_chunk_atyp rhs in
      Queue.add (Binary (lhs_chunks, op, rhs_chunks)) chunks
  | ATyp_app (id, ([_] as args)) when string_of_id id = "atom" ->
      let args = chunk_delimit ~delim:"," ~get_loc:(fun (ATyp_aux (_, l)) -> l) ~chunk:chunk_atyp comments args in
      Queue.add (App (Id_aux (Id "int", id_loc id), args)) chunks
  | ATyp_app (id, args) ->
      let args = chunk_delimit ~delim:"," ~get_loc:(fun (ATyp_aux (_, l)) -> l) ~chunk:chunk_atyp comments args in
      Queue.add (App (id, args)) chunks
  | ATyp_tuple args ->
      let args = chunk_delimit ~delim:"," ~get_loc:(fun (ATyp_aux (_, l)) -> l) ~chunk:chunk_atyp comments args in
      Queue.add (Tuple ("(", ")", 0, args)) chunks
  | ATyp_wild -> Queue.add (Atom "_") chunks
  | ATyp_exist (vars, constr, typ) ->
      let var_chunks = Queue.create () in
      List.iter (fun kopt -> Queue.add (chunk_of_kopt kopt) var_chunks) vars;
      let constr_chunks = rec_chunk_atyp constr in
      let typ_chunks = rec_chunk_atyp typ in
      Queue.add (Exists { vars = var_chunks; constr = constr_chunks; typ = typ_chunks }) chunks
  | ATyp_set _ -> ()

let rec chunk_pat comments chunks (P_aux (aux, l)) =
  pop_comments comments chunks l;
  let rec_chunk_pat pat =
    let chunks = Queue.create () in
    chunk_pat comments chunks pat;
    chunks
  in
  match aux with
  | P_id id -> Queue.add (Atom (string_of_id id)) chunks
  | P_wild -> Queue.add (Atom "_") chunks
  | P_lit lit -> Queue.add (chunk_of_lit lit) chunks
  | P_app (id, [P_aux (P_lit (L_aux (L_unit, _)), _)]) -> Queue.add (App (id, [])) chunks
  | P_app (id, pats) ->
      let pats = chunk_delimit ~delim:"," ~get_loc:(fun (P_aux (_, l)) -> l) ~chunk:chunk_pat comments pats in
      Queue.add (App (id, pats)) chunks
  | P_tuple pats ->
      let pats = chunk_delimit ~delim:"," ~get_loc:(fun (P_aux (_, l)) -> l) ~chunk:chunk_pat comments pats in
      Queue.add (Tuple ("(", ")", 0, pats)) chunks
  | P_vector pats ->
      let pats = chunk_delimit ~delim:"," ~get_loc:(fun (P_aux (_, l)) -> l) ~chunk:chunk_pat comments pats in
      Queue.add (Tuple ("[", "]", 0, pats)) chunks
  | P_list pats ->
      let pats = chunk_delimit ~delim:"," ~get_loc:(fun (P_aux (_, l)) -> l) ~chunk:chunk_pat comments pats in
      Queue.add (Tuple ("[|", "|]", 0, pats)) chunks
  | P_string_append pats ->
      let pats = chunk_delimit ~get_loc:(fun (P_aux (_, l)) -> l) ~chunk:chunk_pat comments pats in
      Queue.add (Intersperse ("^", pats)) chunks
  | P_vector_concat pats ->
      let pats = chunk_delimit ~get_loc:(fun (P_aux (_, l)) -> l) ~chunk:chunk_pat comments pats in
      Queue.add (Intersperse ("@", pats)) chunks
  | P_vector_subrange (id, n, m) ->
      let id_chunks = Queue.create () in
      Queue.add (Atom (string_of_id id)) id_chunks;
      let ix_chunks = Queue.create () in
      if Big_int.equal n m then Queue.add (Atom (Big_int.to_string n)) ix_chunks
      else (
        let n_chunks = Queue.create () in
        Queue.add (Atom (Big_int.to_string n)) n_chunks;
        let m_chunks = Queue.create () in
        Queue.add (Atom (Big_int.to_string m)) m_chunks;
        Queue.add (Binary (n_chunks, "..", m_chunks)) ix_chunks
      );
      Queue.add (Index (id_chunks, ix_chunks)) chunks
  | P_typ (typ, pat) ->
      let pat_chunks = rec_chunk_pat pat in
      let typ_chunks = Queue.create () in
      chunk_atyp comments typ_chunks typ;
      Queue.add (Binary (pat_chunks, ":", typ_chunks)) chunks
  | P_var (pat, typ) ->
      let pat_chunks = rec_chunk_pat pat in
      let typ_chunks = Queue.create () in
      chunk_atyp comments typ_chunks typ;
      Queue.add (Binary (pat_chunks, "as", typ_chunks)) chunks
  | P_cons (hd_pat, tl_pat) ->
      let hd_pat_chunks = rec_chunk_pat hd_pat in
      let tl_pat_chunks = rec_chunk_pat tl_pat in
      Queue.add (Binary (hd_pat_chunks, "::", tl_pat_chunks)) chunks
  | P_struct fpats ->
      let is_fpat_wild = function FP_aux (FP_wild, _) -> true | _ -> false in
      let wild_fpats, field_fpats = List.partition is_fpat_wild fpats in
      let fpats = field_fpats @ wild_fpats in
      let chunk_fpat comments chunks (FP_aux (aux, l)) =
        pop_comments comments chunks l;
        match aux with
        | FP_field (field, pat) ->
            let field_chunks = Queue.create () in
            Queue.add (Atom (string_of_id field)) field_chunks;
            let pat_chunks = rec_chunk_pat pat in
            Queue.add (Binary (field_chunks, "=", pat_chunks)) chunks
        | FP_wild -> Queue.add (Atom "_") chunks
      in
      let fpats = chunk_delimit ~delim:"," ~get_loc:(fun (FP_aux (_, l)) -> l) ~chunk:chunk_fpat comments fpats in
      Queue.add (Tuple ("struct {", "}", 1, fpats)) chunks
  | P_attribute (attr, arg, pat) ->
      Queue.add (Atom (Printf.sprintf "$[%s %s]" attr arg)) chunks;
      Queue.add (Spacer (false, 1)) chunks;
      chunk_pat comments chunks pat

type block_exp = Block_exp of exp | Block_let of letbind | Block_var of exp * exp

let block_exp_locs = function
  | Block_exp (E_aux (_, l)) -> (l, l)
  | Block_let (LB_aux (_, l)) -> (l, l)
  | Block_var (E_aux (_, s_l), E_aux (_, e_l)) -> (s_l, e_l)

let flatten_block exps =
  let block_exps = Queue.create () in
  let rec go = function
    | [] -> ()
    | [E_aux (E_let (letbind, E_aux (E_block more_exps, _)), _)] ->
        Queue.add (Block_let letbind) block_exps;
        go more_exps
    | [E_aux (E_var (lexp, exp, E_aux (E_block more_exps, _)), _)] ->
        Queue.add (Block_var (lexp, exp)) block_exps;
        go more_exps
    | [E_aux (E_let (letbind, E_aux (E_lit (L_aux (L_unit, _)), _)), _)] -> Queue.add (Block_let letbind) block_exps
    | [E_aux (E_var (lexp, exp, E_aux (E_lit (L_aux (L_unit, _)), _)), _)] ->
        Queue.add (Block_var (lexp, exp)) block_exps
    | exp :: exps ->
        Queue.add (Block_exp exp) block_exps;
        go exps
  in
  go exps;
  List.of_seq (Queue.to_seq block_exps)

(* Check if a sequence of cases in a match or try statement is aligned *)
let is_aligned pexps =
  let pexp_exp_column = function
    | Pat_aux (Pat_exp (_, E_aux (_, l)), _) -> starting_column_num l
    | Pat_aux (Pat_when (_, _, E_aux (_, l)), _) -> starting_column_num l
  in
  List.fold_left
    (fun (all_same, col) pexp ->
      if not all_same then (false, None)
      else (
        let new_col = pexp_exp_column pexp in
        match (col, new_col) with
        | _, None ->
            (* If a column number is unknown, assume not aligned *)
            (false, None)
        | None, Some _ -> (true, new_col)
        | Some col, Some new_col -> if col = new_col then (true, Some col) else (false, None)
      )
    )
    (true, None) pexps
  |> fst

let rec chunk_exp comments chunks (E_aux (aux, l)) =
  pop_comments comments chunks l;

  let rec_chunk_exp exp =
    let chunks = Queue.create () in
    chunk_exp comments chunks exp;
    chunks
  in
  match aux with
  | E_id id -> Queue.add (Atom (string_of_id id)) chunks
  | E_ref id -> Queue.add (Atom ("ref " ^ string_of_id id)) chunks
  | E_lit lit -> Queue.add (chunk_of_lit lit) chunks
  | E_attribute (attr, arg, exp) ->
      Queue.add (Atom (Printf.sprintf "$[%s %s]" attr arg)) chunks;
      Queue.add (Spacer (false, 1)) chunks;
      chunk_exp comments chunks exp
  | E_app (id, [E_aux (E_lit (L_aux (L_unit, _)), _)]) -> Queue.add (App (id, [])) chunks
  | E_app (id, args) ->
      let args = chunk_delimit ~delim:"," ~get_loc:(fun (E_aux (_, l)) -> l) ~chunk:chunk_exp comments args in
      Queue.add (App (id, args)) chunks
  | (E_sizeof atyp | E_constraint atyp) as typ_app ->
      let name =
        match typ_app with
        | E_sizeof _ -> "sizeof"
        | E_constraint _ -> "constraint"
        | _ -> Reporting.unreachable l __POS__ "Invalid typ_app"
      in
      let typ_chunks = Queue.create () in
      chunk_atyp comments typ_chunks atyp;
      Queue.add (App (Id_aux (Id name, Unknown), [typ_chunks])) chunks
  | E_assert (exp, E_aux (E_lit (L_aux (L_string "", _)), _)) ->
      let exp_chunks = rec_chunk_exp exp in
      Queue.add (App (Id_aux (Id "assert", Unknown), [exp_chunks])) chunks
  | E_assert (exp, msg) ->
      let exp_chunks = rec_chunk_exp exp in
      Queue.add (Delim ",") exp_chunks;
      let msg_chunks = rec_chunk_exp msg in
      Queue.add (App (Id_aux (Id "assert", Unknown), [exp_chunks; msg_chunks])) chunks
  | E_exit exp ->
      let exp_chunks = rec_chunk_exp exp in
      Queue.add (App (Id_aux (Id "exit", Unknown), [exp_chunks])) chunks
  | E_infix [(IT_primary lhs, _, _); (IT_op (Id_aux (Id op, _)), _, _); (IT_primary rhs, _, _)] ->
      let lhs_chunks = rec_chunk_exp lhs in
      let rhs_chunks = rec_chunk_exp rhs in
      Queue.add (Binary (lhs_chunks, op, rhs_chunks)) chunks
  | E_infix infix_tokens ->
      let infix_chunks = List.map (chunk_infix_token comments chunk_exp) infix_tokens in
      Queue.add (Infix_sequence infix_chunks) chunks
  | E_app_infix (lhs, op, rhs) ->
      let lhs_chunks = rec_chunk_exp lhs in
      let rhs_chunks = rec_chunk_exp rhs in
      Queue.add (Binary (lhs_chunks, string_of_id op, rhs_chunks)) chunks
  | E_cons (lhs, rhs) ->
      let lhs_chunks = rec_chunk_exp lhs in
      let rhs_chunks = rec_chunk_exp rhs in
      Queue.add (Binary (lhs_chunks, "::", rhs_chunks)) chunks
  | E_vector_append (lhs, rhs) ->
      let lhs_chunks = rec_chunk_exp lhs in
      let rhs_chunks = rec_chunk_exp rhs in
      Queue.add (Binary (lhs_chunks, "@", rhs_chunks)) chunks
  | E_typ (typ, exp) ->
      let exp_chunks = rec_chunk_exp exp in
      let typ_chunks = Queue.create () in
      chunk_atyp comments typ_chunks typ;
      Queue.add (Binary (exp_chunks, ":", typ_chunks)) chunks
  | E_tuple exps ->
      let exps = chunk_delimit ~delim:"," ~get_loc:(fun (E_aux (_, l)) -> l) ~chunk:chunk_exp comments exps in
      Queue.add (Tuple ("(", ")", 0, exps)) chunks
  | E_vector [] -> Queue.add (Atom "[]") chunks
  | E_vector exps ->
      let exps = chunk_delimit ~delim:"," ~get_loc:(fun (E_aux (_, l)) -> l) ~chunk:chunk_exp comments exps in
      Queue.add (Tuple ("[", "]", 0, exps)) chunks
  | E_list [] -> Queue.add (Atom "[||]") chunks
  | E_list exps ->
      let exps = chunk_delimit ~delim:"," ~get_loc:(fun (E_aux (_, l)) -> l) ~chunk:chunk_exp comments exps in
      Queue.add (Tuple ("[|", "|]", 0, exps)) chunks
  | E_struct fexps ->
      let fexps = chunk_delimit ~delim:"," ~get_loc:(fun (E_aux (_, l)) -> l) ~chunk:chunk_exp comments fexps in
      Queue.add (Tuple ("struct {", "}", 1, fexps)) chunks
  | E_struct_update (exp, fexps) ->
      let exp = rec_chunk_exp exp in
      let fexps = chunk_delimit ~delim:"," ~get_loc:(fun (E_aux (_, l)) -> l) ~chunk:chunk_exp comments fexps in
      Queue.add (Struct_update (exp, fexps)) chunks
  | E_block exps ->
      let block_exps = flatten_block exps in
      let block_chunks =
        map_peek_acc
          (fun need_spacer next block_exp ->
            let s_l, e_l = block_exp_locs block_exp in
            let chunks = Queue.create () in

            if need_spacer then Queue.add (Spacer (true, 1)) chunks;

            begin
              match block_exp with
              | Block_exp exp -> chunk_exp comments chunks exp
              | Block_let (LB_aux (LB_val (pat, exp), _)) ->
                  pop_comments comments chunks s_l;
                  let pat_chunks = Queue.create () in
                  chunk_pat comments pat_chunks pat;
                  let exp_chunks = rec_chunk_exp exp in
                  Queue.add (Block_binder (Let_binder, pat_chunks, exp_chunks)) chunks
              | Block_var (lexp, exp) ->
                  pop_comments comments chunks s_l;
                  let lexp_chunks = rec_chunk_exp lexp in
                  let exp_chunks = rec_chunk_exp exp in
                  Queue.add (Block_binder (Var_binder, lexp_chunks, exp_chunks)) chunks
            end;

            (* TODO: Do we need to do something different for multiple trailing comments at end of a block? *)
            let next_line_num = Option.bind next (fun bexp -> block_exp_locs bexp |> fst |> starting_line_num) in
            if have_linebreak (ending_line_num e_l) next_line_num || Option.is_none next then
              ignore (pop_trailing_comment comments chunks (ending_line_num e_l));

            (chunks, have_blank_linebreak (ending_line_num e_l) next_line_num)
          )
          false block_exps
      in
      Queue.add (Block (true, block_chunks)) chunks
  | (E_let (LB_aux (LB_val (pat, exp), _), body) | E_internal_plet (pat, exp, body)) as binder ->
      let binder =
        match binder with
        | E_let _ -> Let_binder
        | E_internal_plet _ -> Internal_plet_binder
        | _ -> Reporting.unreachable l __POS__ "Unknown binder"
      in
      let pat_chunks = Queue.create () in
      chunk_pat comments pat_chunks pat;
      let exp_chunks = rec_chunk_exp exp in
      let body_chunks = rec_chunk_exp body in
      Queue.add (Binder (binder, pat_chunks, exp_chunks, body_chunks)) chunks
  | E_var (lexp, exp, body) ->
      let lexp_chunks = rec_chunk_exp lexp in
      let exp_chunks = rec_chunk_exp exp in
      let body_chunks = rec_chunk_exp body in
      Queue.add (Binder (Var_binder, lexp_chunks, exp_chunks, body_chunks)) chunks
  | E_assign (lexp, exp) ->
      let lexp_chunks = rec_chunk_exp lexp in
      let exp_chunks = rec_chunk_exp exp in
      Queue.add (Binary (lexp_chunks, "=", exp_chunks)) chunks
  | E_if (i, t, E_aux (E_lit (L_aux (L_unit, _)), _), keywords) ->
      let then_brace = match t with E_aux (E_block _, _) -> true | _ -> false in
      let i_chunks = rec_chunk_exp i in
      let t_chunks = rec_chunk_exp t in
      Queue.add (If_then (then_brace, i_chunks, t_chunks)) chunks
  | E_if (i, t, e, keywords) ->
      let if_format =
        {
          then_brace = (match t with E_aux (E_block _, _) -> true | _ -> false);
          else_brace = (match e with E_aux (E_block _, _) -> true | _ -> false);
        }
      in
      let i_chunks = rec_chunk_exp i in
      pop_comments ~spacer:false comments i_chunks keywords.then_loc;
      let t_chunks = rec_chunk_exp t in
      (match keywords.else_loc with Some l -> pop_comments comments t_chunks l | None -> ());
      let e_chunks = rec_chunk_exp e in
      Queue.add (If_then_else (if_format, i_chunks, t_chunks, e_chunks)) chunks
  | (E_throw exp | E_return exp | E_deref exp | E_internal_return exp) as unop ->
      let unop =
        match unop with
        | E_throw _ -> "throw"
        | E_return _ -> "return"
        | E_internal_return _ -> "internal_return"
        | E_deref _ -> "*"
        | _ -> Reporting.unreachable l __POS__ "invalid unop"
      in
      let e_chunks = rec_chunk_exp exp in
      Queue.add (Unary (unop, e_chunks)) chunks
  | E_field (exp, id) ->
      let exp_chunks = rec_chunk_exp exp in
      Queue.add (Field (exp_chunks, id)) chunks
  | (E_match (exp, cases) | E_try (exp, cases)) as match_exp ->
      let kind = match match_exp with E_match _ -> Match_match | _ -> Try_match in
      let exp_chunks = rec_chunk_exp exp in
      let aligned = is_aligned cases in
      let cases = List.map (chunk_pexp ~delim:"," comments) cases in
      Match { kind; exp = exp_chunks; aligned; cases } |> add_chunk chunks
  | E_vector_update _ | E_vector_update_subrange _ ->
      let vec_chunks, updates = chunk_vector_update comments (E_aux (aux, l)) in
      Queue.add (Vector_updates (vec_chunks, List.rev updates)) chunks
  | E_vector_access (exp, ix) ->
      let exp_chunks = rec_chunk_exp exp in
      let ix_chunks = rec_chunk_exp ix in
      Queue.add (Index (exp_chunks, ix_chunks)) chunks
  | E_vector_subrange (exp, ix1, ix2) ->
      let exp_chunks = rec_chunk_exp exp in
      let ix1_chunks = rec_chunk_exp ix1 in
      let ix2_chunks = rec_chunk_exp ix2 in
      let ix_chunks = Queue.create () in
      Queue.add (Binary (ix1_chunks, "..", ix2_chunks)) ix_chunks;
      Queue.add (Index (exp_chunks, ix_chunks)) chunks
  | E_for (var, from_index, to_index, step, order, body) ->
      let decreasing =
        match order with
        | ATyp_aux (ATyp_inc, _) -> false
        | ATyp_aux (ATyp_dec, _) -> true
        | _ -> Reporting.unreachable l __POS__ "Invalid foreach order"
      in
      let var_chunks = Queue.create () in
      pop_comments comments var_chunks (id_loc var);
      Queue.add (Atom (string_of_id var)) var_chunks;
      let from_chunks = Queue.create () in
      chunk_exp comments from_chunks from_index;
      let to_chunks = Queue.create () in
      chunk_exp comments to_chunks to_index;
      let step_chunks_opt =
        match step with
        | E_aux (E_lit (L_aux (L_num n, _)), _) when Big_int.equal n (Big_int.of_int 1) -> None
        | _ ->
            let step_chunks = Queue.create () in
            chunk_exp comments step_chunks step;
            Some step_chunks
      in
      let body_chunks = Queue.create () in
      chunk_exp comments body_chunks body;
      Foreach
        {
          var = var_chunks;
          decreasing;
          from_index = from_chunks;
          to_index = to_chunks;
          step = step_chunks_opt;
          body = body_chunks;
        }
      |> add_chunk chunks
  | E_loop (loop_type, measure, cond, body) ->
      let measure_chunks_opt =
        match measure with
        | Measure_aux (Measure_none, _) -> None
        | Measure_aux (Measure_some exp, _) ->
            let measure_chunks = Queue.create () in
            chunk_exp comments measure_chunks exp;
            Some measure_chunks
      in
      begin
        match loop_type with
        | While ->
            let cond_chunks = Queue.create () in
            chunk_exp comments cond_chunks cond;
            let body_chunks = Queue.create () in
            chunk_exp comments body_chunks body;
            While
              { repeat_until = false; termination_measure = measure_chunks_opt; cond = cond_chunks; body = body_chunks }
            |> add_chunk chunks
        | Until ->
            let cond_chunks = Queue.create () in
            chunk_exp comments cond_chunks cond;
            let body_chunks = Queue.create () in
            chunk_exp comments body_chunks body;
            While
              { repeat_until = true; termination_measure = measure_chunks_opt; cond = cond_chunks; body = body_chunks }
            |> add_chunk chunks
      end
  | E_internal_assume (nc, exp) ->
      let nc_chunks = Queue.create () in
      chunk_atyp comments nc_chunks nc;
      let exp_chunks = rec_chunk_exp exp in
      Queue.add (App (Id_aux (Id "internal_assume", l), [nc_chunks; exp_chunks])) chunks

and chunk_vector_update comments (E_aux (aux, l) as exp) =
  let rec_chunk_exp exp =
    let chunks = Queue.create () in
    chunk_exp comments chunks exp;
    chunks
  in
  match aux with
  | E_vector_update (vec, ix, exp) ->
      let vec_chunks, update = chunk_vector_update comments vec in
      let ix = rec_chunk_exp ix in
      let exp = rec_chunk_exp exp in
      (vec_chunks, Binary (ix, "=", exp) :: update)
  | E_vector_update_subrange (vec, ix1, ix2, exp) ->
      let vec_chunks, update = chunk_vector_update comments vec in
      let ix1 = rec_chunk_exp ix1 in
      let ix2 = rec_chunk_exp ix2 in
      let exp = rec_chunk_exp exp in
      (vec_chunks, Ternary (ix1, "..", ix2, "=", exp) :: update)
  | _ ->
      let exp_chunks = Queue.create () in
      chunk_exp comments exp_chunks exp;
      (exp_chunks, [])

and chunk_pexp ?delim comments (Pat_aux (aux, l)) =
  match aux with
  | Pat_exp (pat, exp) ->
      let funcl_space = match pat with P_aux (P_tuple _, _) -> false | _ -> true in
      let pat_chunks = Queue.create () in
      chunk_pat comments pat_chunks pat;
      let exp_chunks = Queue.create () in
      chunk_exp comments exp_chunks exp;
      (match delim with Some d -> Queue.add (Delim d) exp_chunks | _ -> ());
      ignore (pop_trailing_comment comments exp_chunks (ending_line_num l));
      { funcl_space; pat = pat_chunks; guard = None; body = exp_chunks }
  | Pat_when (pat, guard, exp) ->
      let pat_chunks = Queue.create () in
      chunk_pat comments pat_chunks pat;
      let guard_chunks = Queue.create () in
      chunk_exp comments guard_chunks guard;
      let exp_chunks = Queue.create () in
      chunk_exp comments exp_chunks exp;
      (match delim with Some d -> Queue.add (Delim d) exp_chunks | _ -> ());
      ignore (pop_trailing_comment comments exp_chunks (ending_line_num l));
      { funcl_space = true; pat = pat_chunks; guard = Some guard_chunks; body = exp_chunks }

let chunk_funcl comments funcl =
  let chunks = Queue.create () in
  let rec chunk_funcl' comments (FCL_aux (aux, _)) =
    match aux with
    | FCL_attribute (attr, arg, funcl) ->
        Queue.add (Atom (Printf.sprintf "$[%s %s]" attr arg)) chunks;
        Queue.add (Spacer (false, 1)) chunks;
        chunk_funcl' comments funcl
    | FCL_doc (_, funcl) -> chunk_funcl' comments funcl
    | FCL_funcl (_, pexp) -> chunk_pexp comments pexp
  in
  (chunks, chunk_funcl' comments funcl)

let chunk_quant_item comments chunks last = function
  | QI_aux (QI_id kopt, l) ->
      pop_comments comments chunks l;
      Queue.add (chunk_of_kopt kopt) chunks;
      if not last then Queue.add (Spacer (false, 1)) chunks
  | QI_aux (QI_constraint atyp, _) -> chunk_atyp comments chunks atyp

let chunk_quant_items l comments chunks quant_items =
  pop_comments comments chunks l;
  let is_qi_id = function QI_aux (QI_id _, _) as qi -> Ok qi | QI_aux (QI_constraint _, _) as qi -> Error qi in
  let kopts, constrs = Util.map_split is_qi_id quant_items in
  let kopt_chunks = Queue.create () in
  Util.iter_last (chunk_quant_item comments kopt_chunks) kopts;
  let constr_chunks_opt =
    match constrs with
    | [] -> None
    | _ ->
        let constr_chunks = Queue.create () in
        Util.iter_last (chunk_quant_item comments constr_chunks) constrs;
        Some constr_chunks
  in
  Typ_quant { vars = kopt_chunks; constr_opt = constr_chunks_opt } |> add_chunk chunks

let chunk_tannot_opt comments (Typ_annot_opt_aux (aux, l)) =
  match aux with
  | Typ_annot_opt_none -> (None, None)
  | Typ_annot_opt_some (TypQ_aux (TypQ_no_forall, _), typ) ->
      let typ_chunks = Queue.create () in
      chunk_atyp comments typ_chunks typ;
      (None, Some typ_chunks)
  | Typ_annot_opt_some (TypQ_aux (TypQ_tq quant_items, _), typ) ->
      let typq_chunks = Queue.create () in
      chunk_quant_items l comments typq_chunks quant_items;
      let typ_chunks = Queue.create () in
      chunk_atyp comments typ_chunks typ;
      (Some typq_chunks, Some typ_chunks)

let chunk_default_typing_spec comments chunks (DT_aux (DT_order (kind, typ), l)) =
  pop_comments comments chunks l;
  Queue.push (Atom "default") chunks;
  Queue.push (Spacer (false, 1)) chunks;
  Queue.push (Atom (string_of_kind kind)) chunks;
  Queue.push (Spacer (false, 1)) chunks;
  chunk_atyp comments chunks typ;
  Queue.push (Spacer (true, 1)) chunks

let chunk_fundef comments chunks (FD_aux (FD_function (rec_opt, tannot_opt, _, funcls), l)) =
  pop_comments comments chunks l;
  let fn_id =
    match funcls with
    | FCL_aux (FCL_funcl (id, _), _) :: _ -> id
    | _ -> Reporting.unreachable l __POS__ "Empty funcl list in formatter"
  in
  let typq_opt, return_typ_opt = chunk_tannot_opt comments tannot_opt in
  let funcls = List.map (chunk_funcl comments) funcls in
  Function { id = fn_id; clause = false; rec_opt = None; typq_opt; return_typ_opt; funcls } |> add_chunk chunks

let chunk_val_spec comments chunks (VS_aux (VS_val_spec (typschm, id, extern_opt), l)) =
  pop_comments comments chunks l;
  let typq_chunks_opt, typ =
    match typschm with
    | TypSchm_aux (TypSchm_ts (TypQ_aux (TypQ_no_forall, _), typ), _) -> (None, typ)
    | TypSchm_aux (TypSchm_ts (TypQ_aux (TypQ_tq quant_items, _), typ), l) ->
        let typq_chunks = Queue.create () in
        chunk_quant_items l comments typq_chunks quant_items;
        (Some typq_chunks, typ)
  in
  let typ_chunks = Queue.create () in
  chunk_atyp comments typ_chunks typ;
  add_chunk chunks (Val { id; extern_opt; typq_opt = typq_chunks_opt; typ = typ_chunks });
  if not (pop_trailing_comment ~space:1 comments chunks (ending_line_num l)) then Queue.push (Spacer (true, 1)) chunks

let chunk_register comments chunks (DEC_aux (DEC_reg ((ATyp_aux (_, typ_l) as typ), id, opt_exp), l)) =
  pop_comments comments chunks l;
  let def_chunks = Queue.create () in
  Queue.push (Atom "register") def_chunks;
  Queue.push (Spacer (false, 1)) def_chunks;

  let id_chunks = Queue.create () in
  pop_comments comments id_chunks (id_loc id);
  Queue.push (Atom (string_of_id id)) id_chunks;

  let typ_chunks = Queue.create () in
  chunk_atyp comments typ_chunks typ;
  let skip_spacer =
    match opt_exp with
    | Some (E_aux (_, exp_l) as exp) ->
        let exp_chunks = Queue.create () in
        chunk_exp comments exp_chunks exp;
        Queue.push (Ternary (id_chunks, ":", typ_chunks, "=", exp_chunks)) def_chunks;
        pop_trailing_comment ~space:1 comments exp_chunks (ending_line_num exp_l)
    | None ->
        Queue.push (Binary (id_chunks, ":", typ_chunks)) def_chunks;
        pop_trailing_comment ~space:1 comments typ_chunks (ending_line_num typ_l)
  in
  Queue.push (Chunks def_chunks) chunks;
  if not skip_spacer then Queue.push (Spacer (true, 1)) chunks

let chunk_toplevel_let l comments chunks (LB_aux (LB_val (pat, exp), _)) =
  pop_comments comments chunks l;
  let def_chunks = Queue.create () in
  Queue.push (Atom "let") def_chunks;
  Queue.push (Spacer (false, 1)) def_chunks;

  let pat_chunks = Queue.create () in
  let exp_chunks = Queue.create () in
  begin
    match pat with
    | P_aux (P_typ (typ, pat), pat_l) ->
        chunk_pat comments pat_chunks pat;
        let typ_chunks = Queue.create () in
        chunk_atyp comments typ_chunks typ;
        chunk_exp comments exp_chunks exp;
        Queue.push (Ternary (pat_chunks, ":", typ_chunks, "=", exp_chunks)) def_chunks
    | _ ->
        chunk_pat comments pat_chunks pat;
        chunk_exp comments exp_chunks exp;
        Queue.push (Binary (pat_chunks, "=", exp_chunks)) def_chunks
  end;
  Queue.push (Chunks def_chunks) chunks;
  if not (pop_trailing_comment ~space:1 comments exp_chunks (ending_line_num l)) then
    Queue.push (Spacer (true, 1)) chunks

let chunk_keyword k chunks =
  Queue.push (Atom k) chunks;
  Queue.push (Spacer (false, 1)) chunks

let chunk_id id comments chunks =
  pop_comments comments chunks (id_loc id);
  Queue.push (Atom (string_of_id id)) chunks;
  Queue.push (Spacer (false, 1)) chunks

let finish_def def_chunks chunks =
  Queue.push (Chunks def_chunks) chunks;
  Queue.push (Spacer (true, 1)) chunks

let build_def chunks fs =
  let def_chunks = Queue.create () in
  List.iter (fun f -> f def_chunks) fs;
  finish_def def_chunks chunks

let chunk_type_def comments chunks (TD_aux (aux, l)) =
  pop_comments comments chunks l;
  let chunk_enum_member comments chunks member =
    match member with
    | id, None ->
        pop_comments comments chunks (id_loc id);
        Queue.push (Atom (string_of_id id)) chunks
    | id, Some exp ->
        chunk_id id comments chunks;
        chunk_keyword "=>" chunks;
        chunk_exp comments chunks exp
  in
  let chunk_enum_function comments chunks (id, typ) =
    chunk_id id comments chunks;
    chunk_keyword "->" chunks;
    chunk_atyp comments chunks typ
  in
  match aux with
  | TD_enum (id, [], members) ->
      let members =
        chunk_delimit ~delim:"," ~get_loc:(fun x -> id_loc (fst x)) ~chunk:chunk_enum_member comments members
      in
      Queue.add (Enum { id; enum_functions = None; members }) chunks;
      Queue.add (Spacer (true, 1)) chunks
  | TD_enum (id, enum_functions, members) ->
      let enum_functions =
        chunk_delimit ~delim:"," ~get_loc:(fun x -> id_loc (fst x)) ~chunk:chunk_enum_function comments enum_functions
      in
      let members =
        chunk_delimit ~delim:"," ~get_loc:(fun x -> id_loc (fst x)) ~chunk:chunk_enum_member comments members
      in
      Queue.add (Enum { id; enum_functions = Some enum_functions; members }) chunks;
      Queue.add (Spacer (true, 1)) chunks
  | _ -> Reporting.unreachable l __POS__ "unhandled type def"

let chunk_scattered comments chunks (SD_aux (aux, l)) =
  pop_comments comments chunks l;
  match aux with
  | SD_funcl (FCL_aux (FCL_funcl (id, _), _) as funcl) ->
      let funcl_chunks = chunk_funcl comments funcl in
      Queue.push
        (Function { id; clause = true; rec_opt = None; typq_opt = None; return_typ_opt = None; funcls = [funcl_chunks] })
        chunks
  | SD_end id -> build_def chunks [chunk_keyword "end"; chunk_id id comments]
  | SD_function (_, _, _, id) -> build_def chunks [chunk_keyword "scattered function"; chunk_id id comments]
  | _ -> Reporting.unreachable l __POS__ "unhandled scattered def"

let def_spacer (_, e) (s, _) = match (e, s) with Some l_e, Some l_s -> if l_s > l_e + 1 then 1 else 0 | _, _ -> 1

let read_source (p1 : Lexing.position) (p2 : Lexing.position) source =
  String.sub source p1.pos_cnum (p2.pos_cnum - p1.pos_cnum)

let can_handle_td (TD_aux (aux, _)) = match aux with TD_enum _ -> true | _ -> false

let can_handle_sd (SD_aux (aux, _)) = match aux with SD_funcl _ | SD_end _ | SD_function _ -> true | _ -> false

let chunk_def source last_line_span comments chunks (DEF_aux (def, l)) =
  let line_span = (starting_line_num l, ending_line_num l) in
  let spacing = def_spacer last_line_span line_span in
  if spacing > 0 then Queue.add (Spacer (true, spacing)) chunks;
  let pragma_span = ref false in
  begin
    match def with
    | DEF_fundef fdef -> chunk_fundef comments chunks fdef
    | DEF_pragma (pragma, arg) ->
        Queue.add (Pragma (pragma, arg)) chunks;
        pragma_span := true
    | DEF_default dts -> chunk_default_typing_spec comments chunks dts
    | DEF_fixity (prec, n, id) ->
        pop_comments comments chunks (id_loc id);
        let string_of_prec = function Infix -> "infix" | InfixL -> "infixl" | InfixR -> "infixr" in
        Queue.add
          (Atom (Printf.sprintf "%s %s %s" (string_of_prec prec) (Big_int.to_string n) (string_of_id id)))
          chunks;
        Queue.add (Spacer (true, 1)) chunks
    | DEF_register reg -> chunk_register comments chunks reg
    | DEF_let lb -> chunk_toplevel_let l comments chunks lb
    | DEF_val vs -> chunk_val_spec comments chunks vs
    | DEF_scattered sd when can_handle_sd sd -> chunk_scattered comments chunks sd
    | DEF_type td when can_handle_td td -> chunk_type_def comments chunks td
    | _ -> begin
        match Reporting.simp_loc l with
        | Some (p1, p2) ->
            pop_comments comments chunks l;
            (* These comments are within the source we are about to include *)
            discard_comments comments p2;
            let source = read_source p1 p2 source in
            Queue.add (Raw source) chunks;
            Queue.add (Spacer (true, 1)) chunks
        | None -> Reporting.unreachable l __POS__ "Could not format"
      end
  end;
  (* Adjust the line span of a pragma to a single line so the spacing works out *)
  if not !pragma_span then line_span else (fst line_span, fst line_span)

let chunk_defs source comments defs =
  let comments = Stack.of_seq (List.to_seq comments) in
  let chunks = Queue.create () in
  chunk_header_comments comments chunks defs;
  let _ = List.fold_left (fun last_span def -> chunk_def source last_span comments chunks def) (None, Some 0) defs in
  chunks
