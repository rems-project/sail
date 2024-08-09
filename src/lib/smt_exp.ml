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

open Ast_util

let zencode_id id = Util.zencode_string (string_of_id id)
let zencode_upper_id id = Util.zencode_upper_string (string_of_id id)
let zencode_name id = Jib_util.string_of_name ~deref_current_exception:false ~zencode:true id

type smt_typ =
  | Bitvec of int
  | Bool
  | String
  | Real
  | Datatype of string * (string * (string * smt_typ) list) list
  | Array of smt_typ * smt_typ

let mk_enum name elems = Datatype (name, List.map (fun elem -> (elem, [])) elems)

let mk_record name fields = Datatype (name, [(name, fields)])

let mk_variant name ctors = Datatype (name, List.map (fun (ctor, ty) -> (ctor, [("un" ^ ctor, ty)])) ctors)

type smt_array_info = Fixed of int

type smt_exp =
  | Bool_lit of bool
  | Bitvec_lit of Sail2_values.bitU list
  | Real_lit of string
  | String_lit of string
  | Var of Jib.name
  | Unit
  | Member of Ast.id
  | Fn of string * smt_exp list
  | Ite of smt_exp * smt_exp * smt_exp
  | SignExtend of int * int * smt_exp
  | ZeroExtend of int * int * smt_exp
  | Extract of int * int * smt_exp
  | Tester of string * smt_exp
  | Unwrap of Ast.id * bool * smt_exp
  | Field of Ast.id * Ast.id * smt_exp
  | Store of smt_array_info * string * smt_exp * smt_exp * smt_exp
  | Empty_list
  | Hd of string * smt_exp
  | Tl of string * smt_exp

let var_id id = Var (Name (id, -1))

let rec fold_smt_exp f = function
  | Fn (name, args) -> f (Fn (name, List.map (fold_smt_exp f) args))
  | Ite (cond, t, e) -> f (Ite (fold_smt_exp f cond, fold_smt_exp f t, fold_smt_exp f e))
  | SignExtend (len, n, exp) -> f (SignExtend (len, n, fold_smt_exp f exp))
  | ZeroExtend (len, n, exp) -> f (ZeroExtend (len, n, fold_smt_exp f exp))
  | Extract (n, m, exp) -> f (Extract (n, m, fold_smt_exp f exp))
  | Tester (ctor, exp) -> f (Tester (ctor, fold_smt_exp f exp))
  | Unwrap (ctor, b, exp) -> f (Unwrap (ctor, b, fold_smt_exp f exp))
  | Field (struct_id, field_id, exp) -> f (Field (struct_id, field_id, fold_smt_exp f exp))
  | Store (info, store_fn, arr, index, x) ->
      f (Store (info, store_fn, fold_smt_exp f arr, fold_smt_exp f index, fold_smt_exp f x))
  | Hd (hd_op, xs) -> f (Hd (hd_op, fold_smt_exp f xs))
  | Tl (tl_op, xs) -> f (Tl (tl_op, fold_smt_exp f xs))
  | (Bool_lit _ | Bitvec_lit _ | Real_lit _ | String_lit _ | Var _ | Unit | Member _ | Empty_list) as exp -> f exp

let extract i j x = Extract (i, j, x)

let bvnot x = Fn ("bvnot", [x])
let bvand x y = Fn ("bvand", [x; y])
let bvor x y = Fn ("bvor", [x; y])
let bvneg x = Fn ("bvneg", [x])
let bvadd x y = Fn ("bvadd", [x; y])
let bvsub x y = Fn ("bvsub", [x; y])
let bvmul x y = Fn ("bvmul", [x; y])
let bvudiv x y = Fn ("bvudiv", [x; y])
let bvurem x y = Fn ("bvurem", [x; y])
let bvshl x y = Fn ("bvshl", [x; y])
let bvlshr x y = Fn ("bvlshr", [x; y])
let bvult x y = Fn ("bvult", [x; y])

let bvzero n = Bitvec_lit (Sail2_operators_bitlists.zeros (Big_int.of_int n))

let bvones n = Bitvec_lit (Sail2_operators_bitlists.ones (Big_int.of_int n))

let bvone n =
  if n > 0 then Bitvec_lit (Sail2_operators_bitlists.zeros (Big_int.of_int (n - 1)) @ [Sail2_values.B1])
  else Bitvec_lit []

let smt_conj = function [] -> Bool_lit true | [x] -> x | xs -> Fn ("and", xs)

let smt_disj = function [] -> Bool_lit false | [x] -> x | xs -> Fn ("or", xs)

let rec simp_and xs =
  let xs = List.filter (function Bool_lit true -> false | _ -> true) xs in
  match xs with
  | [] -> Bool_lit true
  | [x] -> x
  | _ -> if List.exists (function Bool_lit false -> true | _ -> false) xs then Bool_lit false else Fn ("and", xs)

and simp_or vars xs =
  let xs = List.filter (function Bool_lit false -> false | _ -> true) xs in
  match xs with
  | [] -> Bool_lit false
  | _ when List.exists (function Bool_lit true -> true | _ -> false) xs -> Bool_lit true
  | [x] -> x
  | Var v :: xs -> begin
      let make_constant v lit v' = if Jib_util.Name.compare v v' = 0 then Some lit else vars v' in
      match simp_or vars (List.map (simp (make_constant v (Bool_lit false))) xs) with
      | Bool_lit true -> Bool_lit true
      | Bool_lit false -> Var v
      | Fn ("or", xs) -> Fn ("or", Var v :: xs)
      | _ -> Fn ("or", Var v :: xs)
    end
  | _ -> Fn ("or", xs)

and simp_eq x y =
  match (x, y) with Bool_lit x, Bool_lit y -> Some (x = y) | Bitvec_lit x, Bitvec_lit y -> Some (x = y) | _ -> None

and simp_fn vars f args =
  let open Sail2_operators_bitlists in
  match (f, args) with
  | "=", [x; y] -> begin match simp_eq x y with Some b -> Bool_lit b | None -> Fn (f, args) end
  | "not", [Fn ("not", [exp])] -> exp
  | "not", [Bool_lit b] -> Bool_lit (not b)
  | "contents", [Fn ("Bits", [_; bv])] -> bv
  | "len", [Fn ("Bits", [len; _])] -> len
  | "or", _ -> simp_or vars args
  | "and", _ -> simp_and args
  | "concat", _ ->
      let chunks, bv =
        List.fold_left
          (fun (chunks, current_literal) arg ->
            match (current_literal, arg) with
            | Some bv1, Bitvec_lit bv2 -> (chunks, Some (bv1 @ bv2))
            | None, Bitvec_lit bv -> (chunks, Some bv)
            | Some bv, exp -> (exp :: Bitvec_lit bv :: chunks, None)
            | None, exp -> (exp :: chunks, None)
          )
          ([], None) args
      in
      begin
        match (chunks, bv) with
        | [], Some bv -> Bitvec_lit bv
        | chunks, Some bv -> Fn ("concat", List.rev (Bitvec_lit bv :: chunks))
        | chunks, None -> Fn ("concat", List.rev chunks)
      end
  | "bvnot", [Bitvec_lit bv] -> Bitvec_lit (not_vec bv)
  | "bvand", [Bitvec_lit lhs; Bitvec_lit rhs] -> Bitvec_lit (and_vec lhs rhs)
  | "bvor", [Bitvec_lit lhs; Bitvec_lit rhs] -> Bitvec_lit (or_vec lhs rhs)
  | "bvxor", [Bitvec_lit lhs; Bitvec_lit rhs] -> Bitvec_lit (xor_vec lhs rhs)
  | "bvshl", [Bitvec_lit lhs; Bitvec_lit rhs] -> begin
      match sint_maybe rhs with Some shift -> Bitvec_lit (shiftl lhs shift) | None -> Fn (f, args)
    end
  | "bvlshr", [Bitvec_lit lhs; Bitvec_lit rhs] -> begin
      match sint_maybe rhs with Some shift -> Bitvec_lit (shiftr lhs shift) | None -> Fn (f, args)
    end
  | "bvashr", [Bitvec_lit lhs; Bitvec_lit rhs] -> begin
      match sint_maybe rhs with Some shift -> Bitvec_lit (shiftr lhs shift) | None -> Fn (f, args)
    end
  | _, _ -> Fn (f, args)

and simp vars exp =
  let open Sail2_operators_bitlists in
  match exp with
  | Var v -> begin match vars v with Some exp -> simp vars exp | None -> Var v end
  | Fn (f, args) ->
      let args = List.map (simp vars) args in
      simp_fn vars f args
  | ZeroExtend (to_len, by_len, arg) ->
      let arg = simp vars arg in
      begin
        match arg with
        | Bitvec_lit bv -> Bitvec_lit (zero_extend bv (Big_int.of_int to_len))
        | _ -> ZeroExtend (to_len, by_len, arg)
      end
  | SignExtend (to_len, by_len, arg) ->
      let arg = simp vars arg in
      begin
        match arg with
        | Bitvec_lit bv -> Bitvec_lit (sign_extend bv (Big_int.of_int to_len))
        | _ -> SignExtend (to_len, by_len, arg)
      end
  | Extract (n, m, arg) -> begin
      match simp vars arg with
      | Bitvec_lit bv -> Bitvec_lit (subrange_vec_dec bv (Big_int.of_int n) (Big_int.of_int m))
      | exp -> Extract (n, m, exp)
    end
  | Store (info, store_fn, arr, i, x) -> Store (info, store_fn, simp vars arr, simp vars i, simp vars x)
  | Ite (cond, then_exp, else_exp) -> begin
      let cond = simp vars cond in
      let make_constant v lit v' = if Jib_util.Name.compare v v' = 0 then Some lit else vars v' in
      let mk_ite i t e = match simp_eq t e with Some true -> t | Some false | None -> Ite (i, t, e) in
      match cond with
      | Bool_lit true -> simp vars then_exp
      | Bool_lit false -> simp vars else_exp
      | Var v ->
          mk_ite (Var v)
            (simp (make_constant v (Bool_lit true)) then_exp)
            (simp (make_constant v (Bool_lit false)) else_exp)
      | Fn ("not", [cond]) -> simp vars (Ite (cond, else_exp, then_exp))
      | _ -> mk_ite cond (simp vars then_exp) (simp vars else_exp)
    end
  | Tester (ctor, exp) -> Tester (ctor, simp vars exp)
  | Unwrap (ctor, b, exp) -> Unwrap (ctor, b, simp vars exp)
  | Field (struct_id, field_id, exp) -> Field (struct_id, field_id, simp vars exp)
  | Empty_list | Bool_lit _ | Bitvec_lit _ | Real_lit _ | String_lit _ | Unit | Member _ | Hd _ | Tl _ -> exp

type smt_def =
  | Define_fun of string * (string * smt_typ) list * smt_typ * smt_exp
  | Declare_fun of string * smt_typ list * smt_typ
  | Declare_const of Jib.name * smt_typ
  | Define_const of Jib.name * smt_typ * smt_exp
  | Declare_datatypes of string * (string * (string * smt_typ) list) list
  | Assert of smt_exp

let declare_datatypes = function Datatype (name, ctors) -> Declare_datatypes (name, ctors) | _ -> assert false

let pp_sfun str docs =
  let open PPrint in
  parens (separate space (string str :: docs))

let rec pp_smt_typ =
  let open PPrint in
  function
  | Bool -> string "Bool"
  | String -> string "String"
  | Real -> string "Real"
  | Bitvec n -> string (Printf.sprintf "(_ BitVec %d)" n)
  | Datatype (name, _) -> string name
  | Array (ty1, ty2) -> pp_sfun "Array" [pp_smt_typ ty1; pp_smt_typ ty2]

let pp_str_smt_typ (str, ty) =
  let open PPrint in
  parens (string str ^^ space ^^ pp_smt_typ ty)

let rec pp_smt_exp =
  let open PPrint in
  function
  | Bool_lit b -> string (string_of_bool b)
  | Real_lit str -> string str
  | String_lit str -> string ("\"" ^ str ^ "\"")
  | Bitvec_lit bv -> string (Sail2_values.show_bitlist_prefix '#' bv)
  | Var id -> string (zencode_name id)
  | Member id -> string (zencode_id id)
  | Unit -> string "unit"
  | Fn (str, exps) -> parens (string str ^^ space ^^ separate_map space pp_smt_exp exps)
  | Field (struct_id, field_id, exp) ->
      parens (string (zencode_upper_id struct_id ^ "_" ^ zencode_id field_id) ^^ space ^^ pp_smt_exp exp)
  | Unwrap (ctor, _, exp) -> parens (string ("un" ^ zencode_id ctor) ^^ space ^^ pp_smt_exp exp)
  | Ite (cond, then_exp, else_exp) ->
      parens (separate space [string "ite"; pp_smt_exp cond; pp_smt_exp then_exp; pp_smt_exp else_exp])
  | Extract (i, j, exp) -> parens (string (Printf.sprintf "(_ extract %d %d)" i j) ^^ space ^^ pp_smt_exp exp)
  | Tester (kind, exp) -> parens (string (Printf.sprintf "(_ is %s)" kind) ^^ space ^^ pp_smt_exp exp)
  | SignExtend (_, i, exp) -> parens (string (Printf.sprintf "(_ sign_extend %d)" i) ^^ space ^^ pp_smt_exp exp)
  | ZeroExtend (_, i, exp) -> parens (string (Printf.sprintf "(_ zero_extend %d)" i) ^^ space ^^ pp_smt_exp exp)
  | Store (_, _, arr, index, x) -> parens (string "store" ^^ space ^^ separate_map space pp_smt_exp [arr; index; x])
  | Hd (op, exp) | Tl (op, exp) -> parens (string op ^^ space ^^ pp_smt_exp exp)
  | Empty_list -> string "empty_list"

let pp_smt_def =
  let open PPrint in
  let open Printf in
  function
  | Define_fun (name, args, ty, exp) ->
      parens
        (string "define-fun" ^^ space ^^ string name ^^ space
        ^^ parens (separate_map space pp_str_smt_typ args)
        ^^ space ^^ pp_smt_typ ty ^//^ pp_smt_exp exp
        )
  | Declare_fun (name, args, ty) ->
      parens
        (string "declare-fun" ^^ space ^^ string name ^^ space
        ^^ parens (separate_map space pp_smt_typ args)
        ^^ space ^^ pp_smt_typ ty
        )
  | Declare_const (name, ty) -> pp_sfun "declare-const" [string (zencode_name name); pp_smt_typ ty]
  | Define_const (name, ty, exp) -> pp_sfun "define-const" [string (zencode_name name); pp_smt_typ ty; pp_smt_exp exp]
  | Declare_datatypes (name, ctors) ->
      let pp_ctor (ctor_name, fields) =
        match fields with [] -> parens (string ctor_name) | _ -> pp_sfun ctor_name (List.map pp_str_smt_typ fields)
      in
      pp_sfun "declare-datatypes"
        [Printf.ksprintf string "((%s 0))" name; parens (parens (separate_map space pp_ctor ctors))]
  | Assert exp -> pp_sfun "assert" [pp_smt_exp exp]

let string_of_smt_def def = Pretty_print_sail.Document.to_string (pp_smt_def def)

(**************************************************************************)
(* 2. Parser for SMT solver output                                        *)
(**************************************************************************)

(* Output format from each SMT solver does not seem to be completely
   standardised, unlike the SMTLIB input format, but usually is some
   form of s-expression based representation. Therefore we define a
   simple parser for s-expressions using monadic parser combinators. *)

type counterexample_solver = Cvc5 | Cvc4 | Z3

let counterexample_command = function Cvc5 -> "cvc5 --lang=smt2.6" | Cvc4 -> "cvc4 --lang=smt2.6" | Z3 -> "z3"

let counterexample_solver_from_name name =
  match String.lowercase_ascii name with "cvc4" -> Some Cvc4 | "cvc5" -> Some Cvc5 | "z3" -> Some Z3 | _ -> None

module type COUNTEREXAMPLE_CONFIG = sig
  val max_unknown_integer_width : int
end

module Counterexample (Config : COUNTEREXAMPLE_CONFIG) = struct
  type sexpr = List of sexpr list | Atom of string

  let rec string_of_sexpr = function
    | List sexprs -> "(" ^ Util.string_of_list " " string_of_sexpr sexprs ^ ")"
    | Atom str -> str

  open Parser_combinators

  let lparen = token (function Str.Delim "(" -> Some () | _ -> None)
  let rparen = token (function Str.Delim ")" -> Some () | _ -> None)
  let atom = token (function Str.Text str -> Some str | _ -> None)

  let rec sexp toks =
    let parse =
      pchoose
        (atom >>= fun str -> preturn (Atom str))
        ( lparen >>= fun _ ->
          plist sexp >>= fun xs ->
          rparen >>= fun _ -> preturn (List xs)
        )
    in
    parse toks

  let parse_sexps input =
    let delim = Str.regexp "[ \n\t]+\\|(\\|)" in
    let tokens = Str.full_split delim input in
    let non_whitespace = function Str.Delim d when String.trim d = "" -> false | _ -> true in
    let tokens = List.filter non_whitespace tokens in
    match plist sexp tokens with Ok (result, _) -> Some result | Fail -> None

  let parse_sexpr_int width = function
    | List [Atom "_"; Atom v; Atom m] when int_of_string m = width && String.length v > 2 && String.sub v 0 2 = "bv" ->
        let v = String.sub v 2 (String.length v - 2) in
        Some (Big_int.of_string v)
    | Atom v when String.length v > 2 && String.sub v 0 2 = "#b" ->
        let v = String.sub v 2 (String.length v - 2) in
        Some (Big_int.of_string ("0b" ^ v))
    | Atom v when String.length v > 2 && String.sub v 0 2 = "#x" ->
        let v = String.sub v 2 (String.length v - 2) in
        Some (Big_int.of_string ("0x" ^ v))
    | _ -> None

  let rec value_of_sexpr sexpr =
    let open Jib in
    let open Value in
    function
    | CT_fbits width -> begin
        match parse_sexpr_int width sexpr with
        | Some value -> mk_vector (Sail_lib.get_slice_int' (width, value, 0))
        | None -> failwith ("Cannot parse sexpr as bitvector: " ^ string_of_sexpr sexpr)
      end
    | CT_struct (_, fields) -> begin
        match sexpr with
        | List (Atom name :: smt_fields) ->
            V_record
              (List.fold_left2
                 (fun m (field_id, ctyp) sexpr -> StringMap.add (string_of_id field_id) (value_of_sexpr sexpr ctyp) m)
                 StringMap.empty fields smt_fields
              )
        | _ -> failwith ("Cannot parse sexpr as struct " ^ string_of_sexpr sexpr)
      end
    | CT_enum (_, members) -> begin
        match sexpr with
        | Atom name -> begin
            match List.find_opt (fun member -> Util.zencode_string (string_of_id member) = name) members with
            | Some member -> V_member (string_of_id member)
            | None ->
                failwith
                  ("Could not find enum member for " ^ name ^ " in " ^ Util.string_of_list ", " string_of_id members)
          end
        | _ -> failwith ("Cannot parse sexpr as enum " ^ string_of_sexpr sexpr)
      end
    | CT_bool -> begin
        match sexpr with
        | Atom "true" -> V_bool true
        | Atom "false" -> V_bool false
        | _ -> failwith ("Cannot parse sexpr as bool " ^ string_of_sexpr sexpr)
      end
    | CT_fint width -> begin
        match parse_sexpr_int width sexpr with
        | Some value -> V_int value
        | None -> failwith ("Cannot parse sexpr as fixed-width integer: " ^ string_of_sexpr sexpr)
      end
    | CT_lint -> begin
        match parse_sexpr_int Config.max_unknown_integer_width sexpr with
        | Some value -> V_int value
        | None -> failwith ("Cannot parse sexpr as integer: " ^ string_of_sexpr sexpr)
      end
    | ctyp -> failwith ("Unsupported type in sexpr: " ^ Jib_util.string_of_ctyp ctyp)

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
    | Interpreter.Done (state, v) -> Some v
    | Interpreter.Step (lazy_str, _, _, _) -> run (Interpreter.eval_frame frame)
    | Interpreter.Break frame -> run (Interpreter.eval_frame frame)
    | Interpreter.Fail (_, _, _, _, msg) -> None
    | Interpreter.Effect_request (out, state, stack, eff) -> run (Interpreter.default_effect_interp state eff)

  let check ~env ~ast ~solver ~file_name ~function_id ~args ~arg_ctyps ~arg_smt_names =
    let open Printf in
    let open Ast in
    print_endline ("Checking counterexample: " ^ file_name);
    let in_chan = ksprintf Unix.open_process_in "%s %s" (counterexample_command solver) file_name in
    let lines = ref [] in
    begin
      try
        while true do
          lines := input_line in_chan :: !lines
        done
      with End_of_file -> ()
    end;
    let solver_output = List.rev !lines |> String.concat "\n" in
    begin
      match parse_sexps solver_output with
      | Some (Atom "sat" :: (List (Atom "model" :: model) | List model) :: _) ->
          let open Value in
          let open Interpreter in
          print_endline (sprintf "Solver found counterexample: %s" Util.("ok" |> green |> clear));
          let counterexample = build_counterexample args arg_ctyps arg_smt_names model in
          List.iter (fun (id, v) -> print_endline ("  " ^ string_of_id id ^ " -> " ^ string_of_value v)) counterexample;
          let istate = initial_state ast env !primops in
          let annot = (Parse_ast.Unknown, Type_check.mk_tannot env bool_typ) in
          let call =
            E_aux
              ( E_app
                  ( function_id,
                    List.map
                      (fun (_, v) -> E_aux (E_internal_value v, (Parse_ast.Unknown, Type_check.empty_tannot)))
                      counterexample
                  ),
                annot
              )
          in
          let result = run (Step (lazy "", istate, return call, [])) in
          begin
            match result with
            | Some (V_bool false) | None ->
                ksprintf print_endline "Replaying counterexample: %s" Util.("ok" |> green |> clear)
            | _ -> ()
          end
      | Some (Atom "unsat" :: _) ->
          print_endline "Solver could not find counterexample";
          print_endline "Solver output:";
          print_endline solver_output
      | _ ->
          print_endline "Unexpected solver output:";
          print_endline solver_output
    end;
    let _ = Unix.close_process_in in_chan in
    ()
end
