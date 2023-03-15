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
open PPrint

type line_num = int option

let starting_line_num l = match Reporting.simp_loc l with
  | Some (s, _) -> Some s.pos_lnum
  | None -> None

let starting_column_num l = match Reporting.simp_loc l with
  | Some (s, _) -> Some (s.pos_cnum - s.pos_bol)
  | None -> None
          
let ending_line_num l = match Reporting.simp_loc l with
  | Some (_, e) -> Some e.pos_lnum
  | None -> None

let string_of_line_num = function
  | Some n -> string_of_int n
  | None -> "?"

let string_of_id_aux = function
  | Id v -> v
  | Operator v -> v

let string_of_id (Id_aux (id, l)) = string_of_id_aux id

let id_loc (Id_aux (_, l)) = l
                                  
type binder = Var_binder | Let_binder | Internal_plet_binder

type if_format = {
    then_brace : bool;
    else_brace : bool
  }

type match_kind = Try_match | Match_match

let match_keywords = function
  | Try_match -> "try", Some "catch"
  | Match_match -> "match", None
                            
let string_of_binder = function
  | Var_binder -> "var"
  | Let_binder -> "let"
  | Internal_plet_binder -> "internal_plet"

let comment_type_delimiters = function
  | Lexer.Comment_line -> "//", ""
  | Lexer.Comment_block -> "/*", "*/"

type chunk =
  | Comment of Lexer.comment_type * int * string
  | Spacer of bool * int
  | Function of {
      id : id;
      rec_opt : chunks option;
      typq_opt : chunks option;
      return_typ_opt : chunks option;
      funcls : pexp_chunks list
    }
  | Function_typ of {
      mapping : bool;
      lhs : chunks;
      rhs : chunks;
    }
  | Exists of {
      vars: chunks;
      constr: chunks;
      typ: chunks;
    }
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
  | Index of chunks * chunks
  | Delim of string
  | Opt_delim of string
  | Block of (bool * chunks list)
  | Binder of binder * chunks * chunks * chunks
  | Block_binder of binder * chunks * chunks
  | If_then of bool * chunks * chunks
  | If_then_else of if_format * chunks * chunks * chunks
  | Record_update of chunks * chunks list
  | Match of {
      kind : match_kind;
      exp : chunks;
      aligned : bool;
      cases : pexp_chunks list
    }
  | Vector_updates of chunks * chunk list
  | Chunks of chunks

and chunks = chunk Queue.t

and pexp_chunks = {
    funcl_space : bool;
    pat : chunks;
    guard : chunks option;
    body : chunks
  }

let add_chunk q chunk =
  Queue.add chunk q

let rec prerr_chunk indent = function
  | Comment (comment_type, n, contents) ->
     let s, e = comment_type_delimiters comment_type in
     Printf.eprintf "%sComment:%d %s%s%s\n" indent n s contents e
  | Spacer (line, w) ->
     Printf.eprintf "%sSpacer:%b %d\n" indent line w;
  | Atom str ->
     Printf.eprintf "%sAtom:%s\n" indent str
  | String_literal str ->
     Printf.eprintf "%sString_literal:%s" indent str
  | App (id, args) ->
     Printf.eprintf "%sApp:%s\n" indent (string_of_id id);
     List.iteri (fun i arg ->
         Printf.eprintf "%s  %d:\n" indent i;
         Queue.iter (prerr_chunk (indent ^ "    ")) arg
       ) args
  | Tuple (s, e, n, args) ->
     Printf.eprintf "%sTuple:%s %s %d\n" indent s e n;
     List.iteri (fun i arg ->
         Printf.eprintf "%s  %d:\n" indent i;
         Queue.iter (prerr_chunk (indent ^ "    ")) arg
       ) args
  | Intersperse (str, args) ->
     Printf.eprintf "%sIntersperse:%s\n" indent str;
     List.iteri (fun i arg ->
         Printf.eprintf "%s  %d:\n" indent i;
         Queue.iter (prerr_chunk (indent ^ "    ")) arg
       ) args
  | Block (always_hardline, args) ->
     Printf.eprintf "%sBlock: %b\n" indent always_hardline;
     List.iteri (fun i arg ->
         Printf.eprintf "%s  %d:\n" indent i;
         Queue.iter (prerr_chunk (indent ^ "    ")) arg
       ) args
  | Function fn ->
     Printf.eprintf "%sFunction:%s\n" indent (string_of_id fn.id);
     begin match fn.return_typ_opt with
     | Some return_typ ->
        Printf.eprintf "%s  return_typ:\n" indent;
        Queue.iter (prerr_chunk (indent ^ "    ")) return_typ
     | None -> ()
     end;
     List.iteri (fun i funcl ->
         Printf.eprintf "%s  pat %d:\n" indent i;
         Queue.iter (prerr_chunk (indent ^ "    ")) funcl.pat;
         begin match funcl.guard with
         | Some guard ->
            Printf.eprintf "%s  guard %d:\n" indent i;
            Queue.iter (prerr_chunk (indent ^ "    ")) guard;
         | None -> ()
         end;
         Printf.eprintf "%s  body %d:\n" indent i;
         Queue.iter (prerr_chunk (indent ^ "    ")) funcl.body;
       ) fn.funcls
  | Match m ->
     Printf.eprintf "%sMatch:%s %b\n" indent (fst (match_keywords m.kind)) m.aligned;
     Printf.eprintf "%s  exp:\n" indent;
     Queue.iter (prerr_chunk (indent ^ "    ")) m.exp;
     List.iteri (fun i funcl ->
         Printf.eprintf "%s  pat %d:\n" indent i;
         Queue.iter (prerr_chunk (indent ^ "    ")) funcl.pat;
         begin match funcl.guard with
         | Some guard ->
            Printf.eprintf "%s  guard %d:\n" indent i;
            Queue.iter (prerr_chunk (indent ^ "    ")) guard;
         | None -> ()
         end;
         Printf.eprintf "%s  body %d:\n" indent i;
         Queue.iter (prerr_chunk (indent ^ "    ")) funcl.body;
       ) m.cases
  | Function_typ fn_typ ->
     Printf.eprintf "%sFunction_typ: is_mapping=%b\n" indent fn_typ.mapping;
     List.iter (fun (name, arg) ->
         Printf.eprintf "%s  %s:\n" indent name;
         Queue.iter (prerr_chunk (indent ^ "    ")) arg
       ) [("lhs", fn_typ.lhs); ("rhs", fn_typ.rhs)]
  | Pragma (pragma, arg) ->
     Printf.eprintf "%sPragma:$%s %s\n" indent pragma arg
  | Unary (op, arg) ->
     Printf.eprintf "%sUnary:%s\n" indent op;
     Queue.iter (prerr_chunk (indent ^ "  ")) arg
  | Binary (lhs, op, rhs) ->
     Printf.eprintf "%sBinary:%s\n" indent op;
     List.iter (fun (name, arg) ->
         Printf.eprintf "%s  %s:\n" indent name;
         Queue.iter (prerr_chunk (indent ^ "    ")) arg
       ) [("lhs", lhs); ("rhs", rhs)]
  | Ternary (x, op1, y, op2, z) ->
     Printf.eprintf "%sTernary:%s %s\n" indent op1 op2;
     List.iter (fun (name, arg) ->
         Printf.eprintf "%s  %s:\n" indent name;
         Queue.iter (prerr_chunk (indent ^ "    ")) arg
       ) [("x", x); ("y", y); ("z", z)]
  | Delim str ->
     Printf.eprintf "%sDelim:%s\n" indent str
  | Opt_delim str ->
     Printf.eprintf "%sOpt_delim:%s\n" indent str
  | Exists ex ->
     Printf.eprintf "%sExists:\n" indent;
     List.iter (fun (name, arg) ->
         Printf.eprintf "%s  %s:\n" indent name;
         Queue.iter (prerr_chunk (indent ^ "    ")) arg
       ) [("vars", ex.vars); ("constr", ex.constr); ("typ", ex.typ)]
  | Binder _ -> ()
  | Block_binder (binder, binding, exp) ->
     Printf.eprintf "%sBlock_binder:%s\n" indent (string_of_binder binder);
     List.iter (fun (name, arg) ->
         Printf.eprintf "%s  %s:\n" indent name;
         Queue.iter (prerr_chunk (indent ^ "    ")) arg
       ) [("binding", binding); ("exp", exp)]
  | If_then (_, i, t) ->
     Printf.eprintf "%sIf_then:\n" indent;
     List.iter (fun (name, arg) ->
         Printf.eprintf "%s  %s:\n" indent name;
         Queue.iter (prerr_chunk (indent ^ "    ")) arg
       ) [("if", i); ("then", t)]
  | If_then_else (_, i, t, e) ->
     Printf.eprintf "%sIf_then_else:\n" indent;
     List.iter (fun (name, arg) ->
         Printf.eprintf "%s  %s:\n" indent name;
         Queue.iter (prerr_chunk (indent ^ "    ")) arg
       ) [("if", i); ("then", t); ("else", e)]
  | Field (exp, id) ->
     Printf.eprintf "%sField:%s\n" indent (string_of_id id);
     Queue.iter (prerr_chunk (indent ^ "  ")) exp
  | Record_update (exp, exps) ->
     Printf.eprintf "%sRecord_update:\n" indent;
     Queue.iter (prerr_chunk (indent ^ "    ")) exp;
     Printf.eprintf "%s  with:" indent;
     List.iter (fun exp ->
         Queue.iter (prerr_chunk (indent ^ "    ")) exp
       ) exps
  | Vector_updates (exp, updates) ->
     Printf.eprintf "%sVector_updates:\n" indent
  | Index (exp, ix) ->
     Printf.eprintf "%sIndex:\n" indent;
     List.iter (fun (name, arg) ->
         Printf.eprintf "%s  %s:\n" indent name;
         Queue.iter (prerr_chunk (indent ^ "    ")) arg
       ) [("exp", exp); ("ix", ix)]
  | Chunks chunks ->
     Printf.eprintf "%sChunks:\n" indent;
     Queue.iter (prerr_chunk (indent ^ "  ")) chunks
 
let string_of_var (Kid_aux (Var v, _)) = v

(* Pop comments preceeding location into the chunkstream *)
let rec pop_comments comments chunks l =
  match Stack.top_opt comments with
  | None -> ()
  | Some (Lexer.Comment (comment_type, _, e, contents)) ->
     begin match Reporting.simp_loc l with
     | Some (s, _) when e.pos_cnum <= s.pos_cnum ->
        let _ = Stack.pop comments in
        Queue.add (Comment (comment_type, 0, contents)) chunks;
        pop_comments comments chunks l
     | _ -> ()
     end

let pop_trailing_comment ?space:(n = 0) comments chunks line_num =
  match line_num with
  | None -> false
  | Some lnum ->
     begin match Stack.top_opt comments with
     | Some (Lexer.Comment (comment_type, s, _, contents)) when s.pos_lnum = lnum ->
        let _ = Stack.pop comments in
        Queue.add (Comment (comment_type, n, contents)) chunks;
        begin match comment_type with
        | Lexer.Comment_line -> true
        | _ -> false
        end
     | _ -> false
     end

let string_of_kind (K_aux (k, _)) =
  match k with
  | K_type  -> "Type"
  | K_int   -> "Int"
  | K_order -> "Order"
  | K_bool  -> "Bool"

(* Right now, let's just assume we never break up kinded-identifiers *)
let chunk_of_kopt (KOpt_aux (KOpt_kind (special, vars, kind), l)) =
  match special, kind with
  | Some c, Some k ->
     Atom (Printf.sprintf "(%s %s : %s)" c (Util.string_of_list " " string_of_var vars) (string_of_kind k))
  | None, Some k ->
     Atom (Printf.sprintf "(%s : %s)" (Util.string_of_list " " string_of_var vars) (string_of_kind k))
  | None, None ->
     Atom (Util.string_of_list " " string_of_var vars)
  | _, _ ->
     (* No other KOpt should be parseable *)
     Reporting.unreachable l __POS__ "Invalid KOpt in formatter"
 
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
     x1 :: map_peek f (x2 ::xs)
  | [x] -> [f None x]
  | [] -> []

let rec map_peek_acc f acc = function
  | x1 :: x2 :: xs ->
     let x1, acc = f acc (Some x2) x1 in
     x1 :: map_peek_acc f acc (x2 ::xs)
  | [x] -> [fst (f acc None x)]
  | [] -> []
        
let have_linebreak line_num1 line_num2 =
  match line_num1, line_num2 with
  | Some p1, Some p2 -> p1 < p2
  | _, _ -> false

let have_blank_linebreak line_num1 line_num2 =
  match line_num1, line_num2 with
  | Some p1, Some p2 -> p1 + 1 < p2
  | _, _ -> false
          
let chunk_delimit ?delim ~get_loc ~chunk comments chunks xs =
  map_peek (fun next x ->
      let l = get_loc x in
      let chunks = Queue.create () in
      chunk comments chunks x;
      
      (* Add a delimiter, which is optional for the last element *)
      begin match delim with
      | Some delim ->
         if Util.is_some next then (
           Queue.add (Delim delim) chunks
         ) else (
           Queue.add (Opt_delim delim) chunks
         )
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
      if have_linebreak (ending_line_num l) next_line_num then (
        ignore (pop_trailing_comment comments chunks (ending_line_num l))
      );
      
      chunks
    ) xs
 
let rec chunk_atyp comments chunks (ATyp_aux (aux, l)) =
  pop_comments comments chunks l;
  let rec_chunk_atyp atyp =
    let chunks = Queue.create () in
    chunk_atyp comments chunks atyp;
    chunks
  in
  match aux with
  | ATyp_id id ->
     Queue.add (Atom (string_of_id id)) chunks
  | ATyp_var v ->
     Queue.add (Atom (string_of_var v)) chunks
  | ATyp_lit lit ->
     Queue.add (chunk_of_lit lit) chunks
  | ATyp_nset (n, set) ->
     let n_chunk = Queue.create () in
     (* We would need more granular location information to do anything better here *)
     Queue.add (Atom (Printf.sprintf "%s in {%s}" (string_of_var n) (Util.string_of_list ", " Big_int.to_string set))) chunks
  | (ATyp_times (lhs, rhs) | ATyp_sum (lhs, rhs) | ATyp_minus (lhs, rhs)) as binop ->
     let op_symbol = match binop with
       | ATyp_times _ -> "*" | ATyp_sum _ -> "+" | ATyp_minus _ -> "-" | _ -> Reporting.unreachable l __POS__ "Invalid binary atyp" in
     let lhs_chunks = rec_chunk_atyp lhs in
     let rhs_chunks = rec_chunk_atyp rhs in
     Queue.add (Binary (lhs_chunks, op_symbol, rhs_chunks)) chunks
  | (ATyp_exp arg | ATyp_neg arg) as unop->
     let op_symbol = match unop with
       | ATyp_exp _ -> "2^" | ATyp_neg _ -> "-" | _ -> Reporting.unreachable l __POS__ "Invalid unary atyp" in
     let arg_chunks = rec_chunk_atyp arg in
     Queue.add (Unary (op_symbol, arg_chunks)) chunks
  | ATyp_inc ->
     Queue.add (Atom "inc") chunks
  | ATyp_dec ->
     Queue.add (Atom "dec") chunks
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
  | ATyp_app (id, args) ->
     let args = chunk_delimit ~delim:"," ~get_loc:(fun (ATyp_aux (_, l)) -> l) ~chunk:chunk_atyp comments chunks args in
     Queue.add (App (id, args)) chunks
  | ATyp_tup args ->
     let args = chunk_delimit ~delim:"," ~get_loc:(fun (ATyp_aux (_, l)) -> l) ~chunk:chunk_atyp comments chunks args in
     Queue.add (Tuple ("(", ")", 0, args)) chunks
  | ATyp_wild ->
     Queue.add (Atom "_") chunks
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
  | P_id id ->
     Queue.add (Atom (string_of_id id)) chunks
  | P_wild ->
     Queue.add (Atom "_") chunks
  | P_lit lit ->
     Queue.add (chunk_of_lit lit) chunks
  | P_app (id, pats) ->
     let pats = chunk_delimit ~delim:"," ~get_loc:(fun (P_aux (_, l)) -> l) ~chunk:chunk_pat comments chunks pats in
     Queue.add (App (id, pats)) chunks
  | P_tup pats ->
     let pats = chunk_delimit ~delim:"," ~get_loc:(fun (P_aux (_, l)) -> l) ~chunk:chunk_pat comments chunks pats in
     Queue.add (Tuple ("(", ")", 0, pats)) chunks
  | P_vector pats ->
     let pats = chunk_delimit ~delim:"," ~get_loc:(fun (P_aux (_, l)) -> l) ~chunk:chunk_pat comments chunks pats in
     Queue.add (Tuple ("[", "]", 0, pats)) chunks
  | P_list pats ->
     let pats = chunk_delimit ~delim:"," ~get_loc:(fun (P_aux (_, l)) -> l) ~chunk:chunk_pat comments chunks pats in
     Queue.add (Tuple ("[|", "|]", 0, pats)) chunks
  | P_string_append pats ->
     let pats = chunk_delimit ~get_loc:(fun (P_aux (_, l)) -> l) ~chunk:chunk_pat comments chunks pats in
     Queue.add (Intersperse ("^", pats)) chunks
  | P_vector_concat pats ->
     let pats = chunk_delimit ~get_loc:(fun (P_aux (_, l)) -> l) ~chunk:chunk_pat comments chunks pats in
     Queue.add (Intersperse ("@", pats)) chunks
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

type block_exp =
  | Block_exp of exp
  | Block_let of letbind
  | Block_var of exp * exp

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
  List.fold_left (fun (all_same, col) pexp ->
      if not all_same then (
        (false, None)
      ) else (
        let new_col = pexp_exp_column pexp in
        match col, new_col with
        | _, None ->
           (* If a column number is unknown, assume not aligned *)
           (false, None)
        | None, Some _ ->
           (true, new_col)
        | Some col, Some new_col ->
           if col = new_col then (
             (true, Some col)
           ) else (
             (false, None)
           )
      )
    ) (true, None) pexps
  |> fst

let rec chunk_exp comments chunks (E_aux (aux, l)) =
  pop_comments comments chunks l;
  
  let rec_chunk_exp exp =
    let chunks = Queue.create () in
    chunk_exp comments chunks exp;
    chunks
  in
  match aux with
  | E_id id ->
     Queue.add (Atom (string_of_id id)) chunks
  | E_ref id ->
     Queue.add (Atom ("ref " ^ string_of_id id)) chunks
  | E_lit lit ->
     Queue.add (chunk_of_lit lit) chunks
  | E_app (id, args) ->
     let args = chunk_delimit ~delim:"," ~get_loc:(fun (E_aux (_, l)) -> l) ~chunk:chunk_exp comments chunks args in
     Queue.add (App (id, args)) chunks
  | (E_sizeof atyp | E_constraint atyp) as typ_app ->
     let name = match typ_app with E_sizeof _ -> "sizeof" | E_constraint _ -> "constraint" | _ -> Reporting.unreachable l __POS__ "Invalid typ_app" in
     let typ_chunks = Queue.create () in
     chunk_atyp comments typ_chunks atyp;
     Queue.add (App (Id_aux (Id name, Unknown), [typ_chunks])) chunks
  | E_assert (exp, E_aux (E_lit (L_aux (L_string "", _)), _)) ->
     let exp_chunks = rec_chunk_exp exp in
     Queue.add (App (Id_aux (Id "assert", Unknown), [exp_chunks])) chunks
  | E_assert (exp, msg) ->
     let exp_chunks = rec_chunk_exp exp in
     let msg_chunks = rec_chunk_exp msg in
     Queue.add (App (Id_aux (Id "assert", Unknown), [exp_chunks; msg_chunks])) chunks
  | E_exit exp ->
     let exp_chunks = rec_chunk_exp exp in
     Queue.add (App (Id_aux (Id "exit", Unknown), [exp_chunks])) chunks
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
  | E_cast (typ, exp) ->
     let exp_chunks = rec_chunk_exp exp in
     let typ_chunks = Queue.create () in
     chunk_atyp comments typ_chunks typ;
     Queue.add (Binary (exp_chunks, ":", typ_chunks)) chunks
  | E_tuple exps -> 
     let exps = chunk_delimit ~delim:"," ~get_loc:(fun (E_aux (_, l)) -> l) ~chunk:chunk_exp comments chunks exps in
     Queue.add (Tuple ("(", ")", 0, exps)) chunks
  | E_vector [] ->
     Queue.add (Atom "[]") chunks
  | E_vector exps ->
     let exps = chunk_delimit ~delim:"," ~get_loc:(fun (E_aux (_, l)) -> l) ~chunk:chunk_exp comments chunks exps in
     Queue.add (Tuple ("[", "]", 0, exps)) chunks
  | E_list [] ->
     Queue.add (Atom "[||]") chunks
  | E_list exps ->
     let exps = chunk_delimit ~delim:"," ~get_loc:(fun (E_aux (_, l)) -> l) ~chunk:chunk_exp comments chunks exps in
     Queue.add (Tuple ("[|", "|]", 0, exps)) chunks
  | E_record fexps ->
     let fexps = chunk_delimit ~delim:"," ~get_loc:(fun (E_aux (_, l)) -> l) ~chunk:chunk_exp comments chunks fexps in
     Queue.add (Tuple ("struct {", "}", 1, fexps)) chunks
  | E_record_update (exp, fexps) ->
     let exp = rec_chunk_exp exp in
     let fexps = chunk_delimit ~delim:"," ~get_loc:(fun (E_aux (_, l)) -> l) ~chunk:chunk_exp comments chunks fexps in
     Queue.add (Record_update (exp, fexps)) chunks
  | E_block exps ->
     let block_exps = flatten_block exps in
     let block_chunks =
       map_peek_acc (fun need_spacer next block_exp ->
           let s_l, e_l = block_exp_locs block_exp in
           let chunks = Queue.create () in

           if need_spacer then (
             Queue.add (Spacer (true, 1)) chunks
           );
           
           begin match block_exp with
           | Block_exp exp ->
              chunk_exp comments chunks exp;
           | Block_let (LB_aux (LB_val (pat, exp), _)) ->
              let pat_chunks = Queue.create () in
              chunk_pat comments pat_chunks pat;
              let exp_chunks = rec_chunk_exp exp in
              Queue.add (Block_binder (Let_binder, pat_chunks, exp_chunks)) chunks
           | Block_var (lexp, exp) ->
              let lexp_chunks = rec_chunk_exp lexp in
              let exp_chunks = rec_chunk_exp exp in
              Queue.add (Block_binder (Var_binder, lexp_chunks, exp_chunks)) chunks
           end;
              
           (* TODO: Do we need to do something different for multiple trailing comments at end of a block? *)
           let next_line_num = Option.bind next (fun bexp -> block_exp_locs bexp |> fst |> starting_line_num) in
           if have_linebreak (ending_line_num e_l) next_line_num || Util.is_none next then (
             ignore (pop_trailing_comment comments chunks (ending_line_num e_l))
           );

           (chunks, have_blank_linebreak (ending_line_num e_l) next_line_num)
         ) false block_exps in
     Queue.add (Block (false, block_chunks)) chunks
  | (E_let (LB_aux (LB_val (pat, exp), _), body) | E_internal_plet (pat, exp, body)) as binder ->
     let binder = match binder with E_let _ -> Let_binder | E_internal_plet _ -> Internal_plet_binder | _ -> Reporting.unreachable l __POS__ "Unknown binder" in
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
  | E_if (i, t, E_aux (E_lit (L_aux (L_unit, _)), _)) ->
     let then_brace = (match t with E_aux (E_block _, _) -> true | _ -> false) in
     let i_chunks = rec_chunk_exp i in
     let t_chunks = rec_chunk_exp t in
     Queue.add (If_then (then_brace, i_chunks, t_chunks)) chunks
  | E_if (i, t, e) ->
     let if_format = {
         then_brace = (match t with E_aux (E_block _, _) -> true | _ -> false);
         else_brace = (match e with E_aux (E_block _, _) -> true | _ -> false);
       } in
     let i_chunks = rec_chunk_exp i in
     let t_chunks = rec_chunk_exp t in
     let e_chunks = rec_chunk_exp e in
     Queue.add (If_then_else (if_format, i_chunks, t_chunks, e_chunks)) chunks
  | (E_throw exp | E_return exp | E_deref exp) as unop ->
     let unop = match unop with
       | E_throw _ -> "throw"
       | E_return _ -> "return"
       | E_deref _ -> "*"
       | _ -> Reporting.unreachable l __POS__ "invalid unop" in
     let e_chunks = rec_chunk_exp exp in
     Queue.add (Unary (unop, e_chunks)) chunks
  | E_field (exp, id) ->
     let exp_chunks = rec_chunk_exp exp in
     Queue.add (Field (exp_chunks, id)) chunks
  | E_internal_return exp ->
     let e_chunks = rec_chunk_exp exp in
     Queue.add (Unary ("internal_return", e_chunks)) chunks
  | (E_case (exp, cases) | E_try (exp, cases)) as match_exp ->
     let kind = match match_exp with E_case _ -> Match_match | _ -> Try_match in
     let exp_chunks = rec_chunk_exp exp in
     let aligned = is_aligned cases in
     let cases = List.map (chunk_pexp ~delim:"," comments) cases in
     (Match {
         kind = kind;
         exp = exp_chunks;
         aligned = aligned;
         cases = cases
     }) |> add_chunk chunks
  | (E_vector_update _ | E_vector_update_subrange _) ->
     let (vec_chunks, updates) = chunk_vector_update comments (E_aux (aux, l)) in
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

and chunk_vector_update comments (E_aux (aux, l) as exp) =
  let rec_chunk_exp exp =
    let chunks = Queue.create () in
    chunk_exp comments chunks exp;
    chunks
  in
  match aux with
  | E_vector_update (vec, ix, exp) ->
     let (vec_chunks, update) = chunk_vector_update comments vec in
     let ix = rec_chunk_exp ix in
     let exp = rec_chunk_exp exp in
     (vec_chunks, Binary (ix, "=", exp) :: update)
  | E_vector_update_subrange (vec, ix1, ix2, exp) ->
     let (vec_chunks, update) = chunk_vector_update comments vec in
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
     let funcl_space = match pat with P_aux (P_tup _, _) -> false | _ -> true in
     let pat_chunks = Queue.create () in
     chunk_pat comments pat_chunks pat;
     let exp_chunks = Queue.create () in
     chunk_exp comments exp_chunks exp;
     (match delim with Some d -> Queue.add (Delim d) exp_chunks | _ -> ());
     ignore (pop_trailing_comment comments exp_chunks (ending_line_num l));
     { funcl_space = funcl_space; pat = pat_chunks; guard = None; body = exp_chunks } 
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
 
let chunk_funcl comments (FCL_aux (FCL_Funcl (_, pexp), _)) = chunk_pexp comments pexp

let chunk_tannot_opt comments (Typ_annot_opt_aux (aux, l)) =
  match aux with
  | Typ_annot_opt_none -> None, None
  | Typ_annot_opt_some (TypQ_aux (TypQ_no_forall, _), typ) ->
     let typ_chunks = Queue.create () in
     chunk_atyp comments typ_chunks typ;
     None, Some typ_chunks
  | Typ_annot_opt_some (typq, typ) ->
     let typq_chunks = Queue.create () in
     pop_comments comments typq_chunks l;
     let typ_chunks = Queue.create () in
     chunk_atyp comments typ_chunks typ;
     Some typq_chunks, Some typ_chunks

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
  let fn_id = match funcls with
    | FCL_aux (FCL_Funcl (id, _), _) :: _ -> id
    | _ -> Reporting.unreachable l __POS__ "Empty funcl list in formatter"
  in
  let typq_opt, return_typ_opt = chunk_tannot_opt comments tannot_opt in
  let funcls = List.map (chunk_funcl comments) funcls in
  (Function {
       id = fn_id;
       rec_opt = None;
       typq_opt = typq_opt;
       return_typ_opt = return_typ_opt;
       funcls = funcls;
  }) |> add_chunk chunks

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
  let skip_spacer = match opt_exp with
    | Some (E_aux (_, exp_l) as exp) ->
       let exp_chunks = Queue.create () in
       chunk_exp comments exp_chunks exp;
       Queue.push (Ternary (id_chunks, ":", typ_chunks, "=", exp_chunks)) def_chunks;
       pop_trailing_comment ~space:1 comments exp_chunks (ending_line_num exp_l)
    | None -> 
       Queue.push (Binary (id_chunks, ":", typ_chunks)) def_chunks;
       pop_trailing_comment ~space:1 comments typ_chunks (ending_line_num typ_l) in
  Queue.push (Chunks def_chunks) chunks;
  if not skip_spacer then (
    Queue.push (Spacer (true, 1)) chunks
  )

let def_span = function
  | DEF_type (TD_aux (_, l))
  | DEF_fundef (FD_aux (_, l))
  | DEF_mapdef (MD_aux (_, l))
  | DEF_outcome (OV_aux (_, l), _)
  | DEF_impl (FCL_aux (_, l))
  | DEF_val (LB_aux (_, l))
  | DEF_spec (VS_aux (_, l))
  | DEF_default (DT_aux (_, l))
  | DEF_scattered (SD_aux (_, l))
  | DEF_reg_dec (DEC_aux (_, l)) -> starting_line_num l, ending_line_num l
  (* We don't want to count the newline that would otherwise be part of the span here *)
  | DEF_pragma (_, _, l) -> starting_line_num l, starting_line_num l
  | DEF_fixity (_, _, id) -> starting_line_num (id_loc id), starting_line_num (id_loc id)
  (* The following constructs don't have a complete enough span *)
  | DEF_overload _
  | DEF_instantiation _
  | DEF_internal_mutrec _
  | DEF_measure _
  | DEF_loop_measures _ -> (None, None)

let def_spacer (_, e) (s, _) =
  prerr_endline ((string_of_line_num e) ^ " " ^ (string_of_line_num s));
  match e, s with
  | Some l_e, Some l_s ->
     if l_s > l_e + 1 then 1 else 0
  | _, _ -> 1
 
let chunk_def last_line_span comments chunks def =
  let line_span = def_span def in
  let spacing = def_spacer last_line_span line_span in
  if spacing > 0 then (
    Queue.add (Spacer (true, spacing)) chunks
  );
  begin match def with
  | DEF_fundef fdef ->
     chunk_fundef comments chunks fdef
  | DEF_pragma (pragma, arg, _) ->
     Queue.add (Pragma (pragma, arg)) chunks
  | DEF_default dts ->
     chunk_default_typing_spec comments chunks dts
  | DEF_fixity (prec, n, id) ->
     pop_comments comments chunks (id_loc id);
     let string_of_prec = function
       | Infix -> "infix"
       | InfixL -> "infixl"
       | InfixR -> "infixr" in
     Queue.add (Atom (Printf.sprintf "%s %s %s" (string_of_prec prec) (Big_int.to_string n) (string_of_id id))) chunks;
     Queue.add (Spacer (true, 1)) chunks
  | DEF_reg_dec reg ->
     chunk_register comments chunks reg
  | _ ->
     Queue.add (Atom "DEF") chunks
  end;
  line_span

let doc_id (Id_aux (id_aux, _)) =
  string (match id_aux with
          | Id v -> v
          | Operator op -> "operator " ^ op)
 
let tabwidth = 4
let preserve_structure = false

let to_compact_string doc =
  let b = Buffer.create 120 in
  ToBuffer.compact b doc;
  Buffer.contents b
             
(* Comma separation, but with a trailing comma if non-flat *)
let comma_sep_trailing f xs = separate_map (comma ^^ break 1) f xs ^^ ifflat empty (comma ^^ hardline) 

let fold_left_index_last f init xs =
  let rec go acc n = function
    | [] -> acc
    | [x] -> f true n acc x
    | x :: xs -> go (f false n acc x) (n + 1) xs
  in
  go init 0 xs

let separate_map_last sep f xs =
  fold_left_index_last (fun last i acc x ->
      if i = 0 then
        f last x
      else
        acc ^^ sep ^^ f last x
    ) empty xs

let concat_map_last f xs =
  fold_left_index_last (fun last i acc x ->
      if i = 0 then
        f last x
      else
        acc ^^ f last x
    ) empty xs

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

type opts = {
    (* Controls the bracketing of operators by underapproximating the precedence level of the grammar as we print *)
    precedence : int;
    (* True if we are in a statement-like context. Controls how if-then-else statements are formatted *)
    statement : bool
  }

let default_opts = {
    precedence = 10;
    statement = true
  }

(* atomic lowers the allowed precedence of binary operators to zero, forcing them to always be bracketed *)
let atomic opts = { opts with precedence = 0 }

(* nonatomic raises the allowed precedence to the maximum, so nothing is bracketed. *)               
let nonatomic opts = { opts with precedence = 10 }

(* subatomic forces even some atomic constructs to be bracketed, by setting the allowed precedence below zero *)
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
  group (x ^^ ifflat space (space ^^ lparen) ^^ nest n (softline ^^ y) ^^ softline ^^ ifflat empty rparen)
             
let chunk_inserts_trailing_hardline = function
  | Comment (Lexer.Comment_line, _, _) -> true
  | _ -> false

(* This function inserts linebreaks (b) in a sequence of documents
   produced by a function f, which can either be hardlines or
   softlines.

   However, we want to avoid inserting additional linebreaks after
   line comments, so f returns both a document and boolean indicating
   whether (a hard) linebreak has already been introduced. *)
let rec broken b f = function
  | [] -> empty
  | [x] -> let doc, _ = f x in doc
  | x :: xs ->
     let doc, already_have_hardline = f x in
     doc ^^ (if already_have_hardline then empty else b) ^^ broken b f xs

let rec softbroken_sep sep f = function
  | [] -> empty
  | [x] -> let doc, _ = f x in doc
  | x :: xs ->
     let doc, already_have_hardline = f x in
     doc ^^ (if already_have_hardline then sep else (break 1 ^^ sep)) ^^ space ^^ softbroken_sep sep f xs

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
     ^^ surround tabwidth 0 lparen (broken softline (doc_chunks_linebreak (opts |> nonatomic |> expression_like)) args) rparen
  | Tuple (l, r, spacing, args) ->
     surround tabwidth spacing (string l) (broken softline (doc_chunks_linebreak (nonatomic opts)) args) (string r)
  | Intersperse (op, args) ->
     prerr_endline op;
     group (softbroken_sep (string op) (doc_chunks_linebreak (atomic opts)) args)
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
       (lbracket ^^ exp_doc ^^ space ^^ string "with" ^^ space)
       (group (separate_map (comma ^^ break 1) (doc_chunk opts) updates))
       rbracket
     |> atomic_parens opts
  | Index (exp, ix) ->
     let exp_doc = doc_chunks (opts |> atomic |> expression_like) exp in
     let ix_doc = doc_chunks (opts |> nonatomic |> expression_like) ix in
     exp_doc ^^ surround tabwidth 0 lbracket ix_doc rbracket
     |> atomic_parens opts
  | Exists ex ->
     let ex_doc =
       doc_chunks (atomic opts) ex.vars
       ^^ comma ^^ break 1
       ^^ doc_chunks (nonatomic opts) ex.constr
       ^^ dot ^^ break 1
       ^^ doc_chunks (nonatomic opts) ex.typ
     in
     enclose lbrace rbrace (align ex_doc)
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
     string "function" ^^ space ^^ doc_id f.id ^^ clauses ^^ hardline
  | Pragma (pragma, arg) ->
     string "$pragma" ^^ space ^^ string arg ^^ hardline
  | Block (always_hardline, exps) ->
     let exps = map_last (fun no_semi chunks -> doc_block_exp_chunks (opts |> nonatomic |> statement_like) no_semi chunks) exps in
     let require_hardline = always_hardline || List.exists snd exps in
     let exps = List.map fst exps in
     let sep = if require_hardline then hardline else break 1 in
     surround_hardline always_hardline tabwidth 1 lbrace (separate sep exps) rbrace
     |> atomic_parens opts
  | Block_binder (binder, x, y) ->
     separate space [string (string_of_binder binder); doc_chunks (atomic opts) x; equals; doc_chunks (nonatomic opts) y]
  | Binder (binder, x, y, z) ->
     prefix tabwidth 1
       (separate space [string (string_of_binder binder); doc_chunks (atomic opts) x; equals; doc_chunks (nonatomic opts) y; string "in"])
       (doc_chunks (nonatomic opts) z)
  | Match m ->
     let kw1, kw2 = match_keywords m.kind in
     string kw1 ^^ space ^^ doc_chunks (nonatomic opts) m.exp
     ^^ (Option.fold ~none:empty ~some:(fun k -> space ^^ string k) kw2) ^^ space
     ^^ (if m.aligned then
           let pexps = List.map (fun pexp -> let p, e, _ = doc_pexp_chunks_pair opts pexp in (to_compact_string p, to_compact_string e)) m.cases in
           let pad_to = List.fold_left (fun n (p, _) -> if String.length p > n then String.length p else n) 0 pexps in
           let pad s = String.make (pad_to - String.length s) ' ' in
           surround tabwidth 1 lbrace (separate_map hardline (fun (p, e) -> Printf.ksprintf string "%s%s => %s" p (pad p) e) pexps) rbrace
         else
           surround tabwidth 1 lbrace (broken hardline (doc_pexp_chunks opts) m.cases) rbrace
        )
     |> atomic_parens opts
  | Field (exp, id) ->
     doc_chunks (subatomic opts) exp ^^ dot ^^ doc_id id

and doc_pexp_chunks_pair opts pexp =
  let pat = doc_chunks opts pexp.pat in
  let body, ih = doc_chunks_linebreak opts pexp.body in
  match pexp.guard with
  | None -> pat, body, ih
  | Some guard ->
     separate space [pat; string "if"; doc_chunks opts guard],
     body,
     ih

and doc_pexp_chunks opts pexp =
  let guarded_pat, body, ih = doc_pexp_chunks_pair opts pexp in
  separate space [guarded_pat; string "=>"; body], ih

and doc_funcl return_typ_opt opts pexp =
  let return_typ = match return_typ_opt with
    | Some chunks -> space ^^ prefix_parens tabwidth (string "->") (doc_chunks opts chunks) ^^ space
    | None -> space in
  match pexp.guard with
  | None ->
     (if pexp.funcl_space then space else empty)
     ^^ doc_chunks opts pexp.pat
     ^^ return_typ
     ^^ string "="
     ^^ space ^^ doc_chunks opts pexp.body
  | Some guard ->
     parens (separate space [doc_chunks opts pexp.pat; string "if"; doc_chunks opts guard])
     ^^ return_typ
     ^^ string "="
     ^^ space ^^ doc_chunks opts pexp.body

(* Format an expression in a block, optionally terminating it with a semicolon. If the expression has a trailing comment then we will format as:

   doc; // comment

   In this case a hardline must be inserted by the block formatter, so we return and additional boolean to indicate this. *)
and doc_block_exp_chunks opts no_semi chunks =
  let chunks = Queue.to_seq chunks |> List.of_seq in
  let requires_hardline = ref false in
  let terminator = if no_semi then empty else semi in
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
 
and doc_chunks_linebreak opts chunks =
  let chunks = Queue.to_seq chunks |> List.of_seq in
  (* Push optional trailing delimiters out of the group so they respect the enclosing flatness *)
  let is_opt_delim = function
    | Opt_delim s -> true
    | chunk -> false in
  let docs =
    List.rev_map (fun c ->
        (doc_chunk opts c, is_opt_delim c, chunk_inserts_trailing_hardline c)
      ) chunks in
  let get_doc (doc, _, _) = doc in
  let inserts_hardline (_, _, ih) = ih in
  match docs with
  | [] -> empty, false
  | (last_doc, d, ih) :: docs ->
     let docs = concat (List.rev_map get_doc docs) in
     let doc = if d then group docs ^^ last_doc else group (docs ^^ last_doc) in
     doc, ih

and doc_chunks opts chunks = fst (doc_chunks_linebreak opts chunks)
    
let to_string doc =
  let b = Buffer.create 1024 in
  ToBuffer.pretty 1. 80 b doc;
  Buffer.contents b
 
let chunk_ast comments defs =
  let comments = Stack.of_seq (List.to_seq comments) in
  let chunks = Queue.create () in
  let _ = List.fold_left (fun last_span def -> chunk_def last_span comments chunks def) (None, Some 0) defs in
  Queue.iter (prerr_chunk "") chunks;
  let doc = Queue.fold (fun doc chunk -> doc ^^ char 'X' ^^ doc_chunk ~toplevel:true default_opts chunk) empty chunks in
  prerr_string (to_string (doc ^^ hardline));

  prerr_endline (to_string (nest 2 (char 'a' ^^ hardline) ^^ char 'b'));
