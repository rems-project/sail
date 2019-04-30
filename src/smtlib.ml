(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

open Ast
open Ast_util

type smt_typ =
  | Bitvec of int
  | Bool
  | Datatype of string * (string * (string * smt_typ) list) list
  | Tuple of smt_typ list
  | Array of smt_typ * smt_typ

let rec smt_typ_equal t1 t2 =
  match t1, t2 with
  | Bitvec n, Bitvec m -> n = m
  | Bool, Bool -> true
  | Datatype (name1, ctors1), Datatype (name2, ctors2) ->
     let field_equal (field_name1, typ1) (field_name2, typ2) =
       field_name1 = field_name2 && smt_typ_equal typ1 typ2
     in
     let ctor_equal (ctor_name1, fields1) (ctor_name2, fields2) =
       ctor_name1 = ctor_name2
       && List.length fields1 = List.length fields2
       && List.for_all2 field_equal fields1 fields2
     in
     name1 = name2
     && List.length ctors1 = List.length ctors2
     && List.for_all2 ctor_equal ctors1 ctors2
  | _, _ -> false

let mk_enum name elems =
  Datatype (name, List.map (fun elem -> (elem, [])) elems)

let mk_record name fields =
  Datatype (name, [(name, fields)])

let mk_variant name ctors =
  Datatype (name, List.map (fun (ctor, ty) -> (ctor, [("un" ^ ctor, ty)])) ctors)

type smt_exp =
  | Bool_lit of bool
  | Hex of string
  | Bin of string
  | Var of string
  | Fn of string * smt_exp list
  | Ite of smt_exp * smt_exp * smt_exp
  | SignExtend of int * smt_exp
  | Extract of int * int * smt_exp
  | Tester of string * smt_exp

let extract i j x = Extract (i, j, x)

let bvnot x    = Fn ("bvnot", [x])
let bvand x y  = Fn ("bvand", [x; y])
let bvor x y   = Fn ("bvor", [x; y])
let bvneg x    = Fn ("bvneg", [x])
let bvadd x y  = Fn ("bvadd", [x; y])
let bvmul x y  = Fn ("bvmul", [x; y])
let bvudiv x y = Fn ("bvudiv", [x; y])
let bvurem x y = Fn ("bvurem", [x; y])
let bvshl x y  = Fn ("bvshl", [x; y])
let bvlshr x y = Fn ("bvlshr", [x; y])
let bvult x y  = Fn ("bvult", [x; y])

let bvzero n =
  if n mod 4 = 0 then
    Hex (String.concat "" (Util.list_init (n / 4) (fun _ -> "0")))
  else
    Bin (String.concat "" (Util.list_init n (fun _ -> "0")))

let bvones n =
  if n mod 4 = 0 then
    Hex (String.concat "" (Util.list_init (n / 4) (fun _ -> "F")))
  else
    Bin (String.concat "" (Util.list_init n (fun _ -> "1")))

let simp_fn = function
  | Fn ("not", [Fn ("not", [exp])]) -> exp
  | Fn ("not", [Bool_lit b]) -> Bool_lit (not b)
  | Fn ("contents", [Fn ("Bits", [_; contents])]) -> contents
  | Fn ("len", [Fn ("Bits", [len; _])]) -> len
  | Fn ("or", [x]) -> x
  | Fn ("and", [x]) -> x
  | exp -> exp

let simp_ite = function
  | Ite (cond, Bool_lit true, Bool_lit false) -> cond
  | Ite (cond, Bool_lit x, Bool_lit y) when x = y -> Bool_lit x
  | Ite (_, Var v, Var v') when v = v' -> Var v
  | Ite (Bool_lit true, then_exp, _) -> then_exp
  | Ite (Bool_lit false, _, else_exp) -> else_exp
  | exp -> exp

let rec simp_smt_exp vars = function
  | Var v ->
     begin match Hashtbl.find_opt vars v with
     | Some exp -> simp_smt_exp vars exp
     | None -> Var v
     end
  | (Hex _ | Bin _ | Bool_lit _ as exp) -> exp
  | Fn (f, exps) ->
     let exps = List.map (simp_smt_exp vars) exps in
     simp_fn (Fn (f, exps))
  | Ite (cond, t, e) ->
     let cond = simp_smt_exp vars cond in
     let t = simp_smt_exp vars t in
     let e = simp_smt_exp vars e in
     simp_ite (Ite (cond, t, e))
  | Extract (i, j, exp) ->
     let exp = simp_smt_exp vars exp in
     Extract (i, j, exp)
  | Tester (str, exp) ->
     let exp = simp_smt_exp vars exp in
     Tester (str, exp)
  | SignExtend (i, exp) ->
     let exp = simp_smt_exp vars exp in
     SignExtend (i, exp)

type smt_def =
  | Define_fun of string * (string * smt_typ) list * smt_typ * smt_exp
  | Declare_const of string * smt_typ
  | Define_const of string * smt_typ * smt_exp
  | Declare_datatypes of string * (string * (string * smt_typ) list) list
  | Declare_tuple of int
  | Assert of smt_exp

let declare_datatypes = function
  | Datatype (name, ctors) -> Declare_datatypes (name, ctors)
  | _ -> assert false

let pp_sfun str docs =
  let open PPrint in
  parens (separate space (string str :: docs))

let rec pp_smt_exp =
  let open PPrint in
  function
  | Bool_lit b -> string (string_of_bool b)
  | Hex str -> string ("#x" ^ str)
  | Bin str -> string ("#b" ^ str)
  | Var str -> string str
  | Fn (str, exps) -> parens (string str ^^ space ^^ separate_map space pp_smt_exp exps)
  | Ite (cond, then_exp, else_exp) ->
     parens (separate space [string "ite"; pp_smt_exp cond; pp_smt_exp then_exp; pp_smt_exp else_exp])
  | Extract (i, j, exp) ->
     parens (string (Printf.sprintf "(_ extract %d %d)" i j) ^^ space ^^ pp_smt_exp exp)
  | Tester (kind, exp) ->
     parens (string (Printf.sprintf "(_ is %s)" kind) ^^ space ^^ pp_smt_exp exp)
  | SignExtend (i, exp) ->
     parens (string (Printf.sprintf "(_ sign_extend %d)" i) ^^ space ^^ pp_smt_exp exp)

let rec pp_smt_typ =
  let open PPrint in
  function
  | Bool -> string "Bool"
  | Bitvec n -> string (Printf.sprintf "(_ BitVec %d)" n)
  | Datatype (name, _) -> string name
  | Tuple tys -> pp_sfun ("Tup" ^ string_of_int (List.length tys)) (List.map pp_smt_typ tys)
  | Array (ty1, ty2) -> pp_sfun "Array" [pp_smt_typ ty1; pp_smt_typ ty2]

let pp_str_smt_typ (str, ty) = let open PPrint in string str ^^ space ^^ pp_smt_typ ty

let pp_smt_def =
  let open PPrint in
  let open Printf in
  function
  | Define_fun (str, args, ty, exp) ->
     parens (string "define-fun"
             ^^ space ^^ parens (separate_map space pp_str_smt_typ args)
             ^^ space ^^ pp_smt_typ ty
             ^//^ pp_smt_exp exp)

  | Declare_const (name, ty) ->
     pp_sfun "declare-const" [string name; pp_smt_typ ty]

  | Define_const (name, ty, exp) ->
     pp_sfun "define-const" [string name; pp_smt_typ ty; pp_smt_exp exp]

  | Declare_datatypes (name, ctors) ->
     let pp_ctor (ctor_name, fields) =
       match fields with
       | [] -> parens (string ctor_name)
       | _ -> pp_sfun ctor_name (List.map (fun field -> parens (pp_str_smt_typ field)) fields)
     in
     pp_sfun "declare-datatypes"
       [Printf.ksprintf string "((%s 0))" name;
        parens (parens (separate_map space pp_ctor ctors))]

  | Declare_tuple n ->
     let par = separate_map space string (Util.list_init n (fun i -> "T" ^ string_of_int i)) in
     let fields = separate space (Util.list_init n (fun i -> Printf.ksprintf string "(tup_%d_%d T%d)" n i i)) in
     pp_sfun "declare-datatypes"
       [Printf.ksprintf string "((Tup%d %d))" n n;
        parens (parens (separate space
                          [string "par";
                           parens par;
                           parens (parens (ksprintf string "tup%d" n ^^ space ^^ fields))]))]

  | Assert exp ->
     pp_sfun "assert" [pp_smt_exp exp]

let string_of_smt_def def = Pretty_print_sail.to_string (pp_smt_def def)

let output_smt_defs out_chan smt =
  List.iter (fun def -> output_string out_chan (string_of_smt_def def ^ "\n")) smt

(**************************************************************************)
(* 2. Parser for SMT solver output                                        *)
(**************************************************************************)

(* Output format from each SMT solver does not seem to be completely
   standardised, unlike the SMTLIB input format, but usually is some
   form of s-expression based representation. Therefore we define a
   simple parser for s-expressions using monadic parser combinators. *)

type sexpr = List of (sexpr list) | Atom of string

let rec string_of_sexpr = function
  | List sexprs -> "(" ^ Util.string_of_list " " string_of_sexpr sexprs ^ ")"
  | Atom str -> str

type 'a parse_result =
  | Ok of 'a * Str.split_result list
  | Fail

type 'a parser = Str.split_result list -> 'a parse_result

let (>>=) (m : 'a parser) (f : 'a -> 'b parser) (toks : Str.split_result list) =
  match m toks with
  | Ok (r, toks) -> f r toks
  | Fail -> Fail

let pmap f m toks =
  match m toks with
  | Ok (r, toks) -> Ok (f r, toks)
  | Fail -> Fail

let token f = function
  | tok :: toks ->
     begin match f tok with
     | Some x -> Ok (x, toks)
     | None -> Fail
     end
  | [] -> Fail

let preturn x toks = Ok (x, toks)

let rec plist m toks =
  match m toks with
  | Ok (x, toks) ->
     begin match plist m toks with
     | Ok (xs, toks) -> Ok (x :: xs, toks)
     | Fail -> Fail
     end
  | Fail -> Ok ([], toks)

let pchoose m n toks =
  match m toks with
  | Fail -> n toks
  | Ok (x, toks) -> Ok (x, toks)

let lparen = token (function Str.Delim "(" -> Some () | _ -> None)
let rparen = token (function Str.Delim ")" -> Some () | _ -> None)
let atom   = token (function Str.Text str -> Some str | _ -> None)

let rec sexp toks =
  let parse =
    pchoose
      (atom >>= fun str -> preturn (Atom str))
      (lparen     >>= fun _ ->
       plist sexp >>= fun xs ->
       rparen     >>= fun _ ->
       preturn (List xs))
  in
  parse toks

let parse p delim_regexp input =
  let delim = Str.regexp delim_regexp in
  let tokens = Str.full_split delim input in
  let non_whitespace = function
    | Str.Delim d when String.trim d = "" -> false
    | _ -> true
  in
  let tokens = List.filter non_whitespace tokens in
  match p tokens with
  | Ok (result, []) -> Some result
  | Ok (result, _) -> None
  | Fail -> None

let parse_sexps input =
  let delim = Str.regexp "[ \n\t]+\\|(\\|)" in
  let tokens = Str.full_split delim input in
  let non_whitespace = function
    | Str.Delim d when String.trim d = "" -> false
    | _ -> true
  in
  let tokens = List.filter non_whitespace tokens in
  match plist sexp tokens with
  | Ok (result, _) -> result
  | Fail -> failwith "Parse failure"

let value_of_sexpr sexpr =
  let open Jib in
  let open Value in
  function
  | CT_fbits (n, _) ->
     begin match sexpr with
     | List [Atom "_"; Atom v; Atom m]
          when int_of_string m = n && String.length v > 2 && String.sub v 0 2 = "bv" ->
        let v = String.sub v 2 (String.length v - 2) in
        mk_vector (Sail_lib.get_slice_int' (n, Big_int.of_string v, 0))
     | _ -> failwith "Cannot parse sexpr as ctyp"
     end
  | _ -> assert false

let rec find_arg id ctyp arg_smt_names = function
  | List [Atom "define-fun"; Atom str; List []; _; value] :: _
       when Util.assoc_compare_opt Id.compare id arg_smt_names = Some (Some str) ->
     (id, value_of_sexpr value ctyp)
  | _ :: sexps -> find_arg id ctyp arg_smt_names sexps
  | [] -> (id, V_unit)

let build_counterexample args arg_ctyps arg_smt_names model =
  List.map2 (fun id ctyp -> find_arg id ctyp arg_smt_names model) args arg_ctyps

let rec run frame =
  match frame with
  | Interpreter.Done (state, v) -> v
  | Interpreter.Step (lazy_str, _, _, _) ->
     run (Interpreter.eval_frame frame)
  | Interpreter.Break frame ->
     run (Interpreter.eval_frame frame)

let check_counterexample ast env fname args arg_ctyps arg_smt_names =
  let open Printf in
  prerr_endline ("Checking counterexample: " ^ fname);
  let in_chan = ksprintf Unix.open_process_in "cvc4 --lang=smt2.6 %s" fname in
  let lines = ref [] in
  begin
    try
      while true do
        lines := input_line in_chan :: !lines
      done
    with
    | End_of_file -> ()
  end;
  let solver_output = List.rev !lines |> String.concat "\n" |> parse_sexps in
  begin match solver_output with
  | Atom "sat" :: List (Atom "model" :: model) :: _ ->
     let open Value in
     let open Interpreter in
     prerr_endline (sprintf "Solver found counterexample: %s" Util.("ok" |> green |> clear));
     let counterexample = build_counterexample args arg_ctyps arg_smt_names model in
     List.iter (fun (id, v) -> prerr_endline ("  " ^ string_of_id id ^ " -> " ^ string_of_value v)) counterexample;
     let istate = initial_state ast env primops in
     let annot = (Parse_ast.Unknown, Type_check.mk_tannot env bool_typ no_effect) in
     let call = E_aux (E_app (mk_id "prop", List.map (fun (_, v) -> E_aux (E_internal_value v, (Parse_ast.Unknown, Type_check.empty_tannot))) counterexample), annot) in
     let result = run (Step (lazy "", istate, return call, [])) in
     begin match result with
     | V_bool false ->
        ksprintf prerr_endline "Replaying counterexample: %s" Util.("ok" |> green |> clear)
     | _ -> ()
     end
  | _ ->
     prerr_endline "failure"
  end;
  let status = Unix.close_process_in in_chan in
  ()
