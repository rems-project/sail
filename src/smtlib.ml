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
  | String
  | Real
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
  | Real_lit of string
  | String_lit of string
  | Var of string
  | Read_res of string
  | Enum of string
  | Fn of string * smt_exp list
  | Ctor of string * smt_exp list
  | Ite of smt_exp * smt_exp * smt_exp
  | SignExtend of int * smt_exp
  | Extract of int * int * smt_exp
  | Tester of string * smt_exp

let rec fold_smt_exp f = function
  | Fn (name, args) -> f (Fn (name, List.map (fold_smt_exp f) args))
  | Ctor (name, args) -> f (Ctor (name, List.map (fold_smt_exp f) args))
  | Ite (cond, t, e) -> f (Ite (fold_smt_exp f cond, fold_smt_exp f t, fold_smt_exp f e))
  | SignExtend (n, exp) -> f (SignExtend (n, fold_smt_exp f exp))
  | Extract (n, m, exp) -> f (Extract (n, m, fold_smt_exp f exp))
  | Tester (ctor, exp) -> f (Tester (ctor, fold_smt_exp f exp))
  | (Bool_lit _ | Hex _ | Bin _ | Real_lit _ | String_lit _ | Var _ | Read_res _ | Enum _ as exp) -> f exp

let smt_conj = function
  | [] -> Bool_lit true
  | [x] -> x
  | xs -> Fn ("and", xs)

let smt_disj = function
  | [] -> Bool_lit false
  | [x] -> x
  | xs -> Fn ("or", xs)

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

let simp_equal x y =
  match x, y with
  | Bin str1, Bin str2 -> Some (str1 = str2)
  | _, _ -> None

let simp_and xs =
  let xs = List.filter (function Bool_lit true -> false | _ -> true) xs in
  match xs with
  | [] -> Bool_lit true
  | [x] -> x
  | _ ->
     if List.exists (function Bool_lit false -> true | _ -> false) xs then
       Bool_lit false
     else
       Fn ("and", xs)

let simp_or xs =
  let xs = List.filter (function Bool_lit false -> false | _ -> true) xs in
  match xs with
  | [] -> Bool_lit false
  | [x] -> x
  | _ ->
     if List.exists (function Bool_lit true -> true | _ -> false) xs then
       Bool_lit true
     else
       Fn ("or", xs)

let simp_fn = function
  | Fn ("not", [Fn ("not", [exp])]) -> exp
  | Fn ("not", [Bool_lit b]) -> Bool_lit (not b)
  | Fn ("contents", [Fn ("Bits", [_; contents])]) -> contents
  | Fn ("len", [Fn ("Bits", [len; _])]) -> len
  | Fn ("or", xs) -> simp_or xs
  | Fn ("and", xs) -> simp_and xs
  | Fn ("=>", [Bool_lit true; y]) -> y
  | Fn ("=>", [Bool_lit false; y]) -> Bool_lit true
  | Fn ("=", [x; y]) as exp ->
     begin match simp_equal x y with
     | Some b -> Bool_lit b
     | None -> exp
     end
  | exp -> exp

let simp_ite = function
  | Ite (cond, Bool_lit true, Bool_lit false) -> cond
  | Ite (cond, Bool_lit x, Bool_lit y) when x = y -> Bool_lit x
  | Ite (_, Var v, Var v') when v = v' -> Var v
  | Ite (Bool_lit true, then_exp, _) -> then_exp
  | Ite (Bool_lit false, _, else_exp) -> else_exp
  | exp -> exp

let rec simp_smt_exp vars kinds = function
  | Var v ->
     begin match Hashtbl.find_opt vars v with
     | Some exp -> simp_smt_exp vars kinds exp
     | None -> Var v
     end
  | (Read_res _ | Enum _ | Hex _ | Bin _ | Bool_lit _ | String_lit _ | Real_lit _ as exp) -> exp
  | Fn (f, exps) ->
     let exps = List.map (simp_smt_exp vars kinds) exps in
     simp_fn (Fn (f, exps))
  | Ctor (f, exps) ->
     let exps = List.map (simp_smt_exp vars kinds) exps in
     simp_fn (Ctor (f, exps))
  | Ite (cond, t, e) ->
     let cond = simp_smt_exp vars kinds cond in
     let t = simp_smt_exp vars kinds t in
     let e = simp_smt_exp vars kinds e in
     simp_ite (Ite (cond, t, e))
  | Extract (i, j, exp) ->
     let exp = simp_smt_exp vars kinds exp in
     begin match exp with
     | Bin str ->
        Bin (String.sub str ((String.length str - 1) - i) ((i + 1) - j))
     | _ -> Extract (i, j, exp)
     end
  | Tester (str, exp) ->
     let exp = simp_smt_exp vars kinds exp in
     begin match exp with
     | Var v ->
        begin match Hashtbl.find_opt kinds v with
        | Some str' when str = str' -> Bool_lit true
        | Some str' -> Bool_lit false
        | None -> Tester (str, exp)
        end
     | _ -> Tester (str, exp)
     end
  | SignExtend (i, exp) ->
     let exp = simp_smt_exp vars kinds exp in
     SignExtend (i, exp)

type smt_def =
  | Define_fun of string * (string * smt_typ) list * smt_typ * smt_exp
  | Declare_const of string * smt_typ
  | Define_const of string * smt_typ * smt_exp
  | Write_mem of string * int * smt_exp * smt_exp * smt_exp * smt_typ * smt_exp * smt_typ
  | Write_mem_ea of string * int * smt_exp * smt_exp * smt_exp * smt_typ * smt_exp * smt_typ
  | Read_mem of string * int * smt_exp * smt_typ * smt_exp * smt_exp * smt_typ
  | Barrier of string * int * smt_exp * smt_exp
  | Excl_res of string * int * smt_exp
  | Declare_datatypes of string * (string * (string * smt_typ) list) list
  | Declare_tuple of int
  | Assert of smt_exp

let declare_datatypes = function
  | Datatype (name, ctors) -> Declare_datatypes (name, ctors)
  | _ -> assert false

let suffix_variables_exp sfx =
  fold_smt_exp (function Var v -> Var (v ^ sfx) | exp -> exp)

let suffix_variables_def sfx = function
  | Define_fun (name, args, ty, exp) ->
     Define_fun (name ^ sfx, List.map (fun (arg, ty) -> sfx ^ arg, ty) args, ty, suffix_variables_exp sfx exp)
  | Declare_const (name, ty) ->
     Declare_const (name ^ sfx, ty)
  | Define_const (name, ty, exp) ->
     Define_const (name ^ sfx, ty, suffix_variables_exp sfx exp)
  | Write_mem (name, node, active, wk, addr, addr_ty, data, data_ty) ->
     Write_mem (name ^ sfx, node, suffix_variables_exp sfx active, suffix_variables_exp sfx wk,
                suffix_variables_exp sfx addr, addr_ty, suffix_variables_exp sfx data, data_ty)
  | Write_mem_ea (name, node, active , wk, addr, addr_ty, data_size, data_size_ty) ->
     Write_mem (name ^ sfx, node, suffix_variables_exp sfx active, suffix_variables_exp sfx wk,
                suffix_variables_exp sfx addr, addr_ty, suffix_variables_exp sfx data_size, data_size_ty)
  | Read_mem (name, node, active, ty, rk, addr, addr_ty) ->
     Read_mem (name ^ sfx, node, suffix_variables_exp sfx active, ty, suffix_variables_exp sfx rk,
               suffix_variables_exp sfx addr, addr_ty)
  | Barrier (name, node, active, bk) ->
     Barrier (name ^ sfx, node, suffix_variables_exp sfx active, suffix_variables_exp sfx bk)
  | Excl_res (name, node, active) ->
     Excl_res (name ^ sfx, node, suffix_variables_exp sfx active)
  | Declare_datatypes (name, ctors) ->
     Declare_datatypes (name, ctors)
  | Declare_tuple n ->
     Declare_tuple n
  | Assert exp ->
     Assert (suffix_variables_exp sfx exp)

let merge_datatypes defs1 defs2 =
  let module StringSet = Set.Make(String) in
  let datatype_name = function
    | Declare_datatypes (name, _) -> name
    | _ -> assert false
  in
  let names = List.fold_left (fun set def -> StringSet.add (datatype_name def) set) StringSet.empty defs1 in
  defs1 @ List.filter (fun def -> not (StringSet.mem (datatype_name def) names)) defs2

let merge_tuples defs1 defs2 =
  let tuple_size = function
    | Declare_tuple size -> size
    | _ -> assert false
  in
  let names = List.fold_left (fun set def -> Util.IntSet.add (tuple_size def) set) Util.IntSet.empty defs1 in
  defs1 @ List.filter (fun def -> not (Util.IntSet.mem (tuple_size def) names)) defs2

let merge_smt_defs defs1 defs2 =
  let is_tuple = function
    | Declare_datatypes _ | Declare_tuple _ -> true
    | _ -> false
  in
  let is_datatype = function
    | Declare_datatypes _ | Declare_tuple _ -> true
    | _ -> false
  in
  let datatypes1, body1 = List.partition is_datatype defs1 in
  let datatypes2, body2 = List.partition is_datatype defs2 in
  let tuples1, datatypes1 = List.partition is_tuple datatypes1 in
  let tuples2, datatypes2 = List.partition is_tuple datatypes2 in
  merge_tuples tuples1 tuples2 @ merge_datatypes datatypes1 datatypes2 @ body1 @ body2

let pp_sfun str docs =
  let open PPrint in
  parens (separate space (string str :: docs))

let rec pp_smt_exp =
  let open PPrint in
  function
  | Bool_lit b -> string (string_of_bool b)
  | Real_lit str -> string str
  | String_lit str -> string ("\"" ^ str ^ "\"")
  | Hex str -> string ("#x" ^ str)
  | Bin str -> string ("#b" ^ str)
  | Var str -> string str
  | Read_res str -> string (str ^ "_ret")
  | Enum str -> string str
  | Fn (str, exps) -> parens (string str ^^ space ^^ separate_map space pp_smt_exp exps)
  | Ctor (str, exps) -> parens (string str ^^ space ^^ separate_map space pp_smt_exp exps)
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
  | String -> string "String"
  | Real -> string "Real"
  | Bitvec n -> string (Printf.sprintf "(_ BitVec %d)" n)
  | Datatype (name, _) -> string name
  | Tuple tys -> pp_sfun ("Tup" ^ string_of_int (List.length tys)) (List.map pp_smt_typ tys)
  | Array (ty1, ty2) -> pp_sfun "Array" [pp_smt_typ ty1; pp_smt_typ ty2]

let pp_str_smt_typ (str, ty) = let open PPrint in string str ^^ space ^^ pp_smt_typ ty

let pp_smt_def =
  let open PPrint in
  let open Printf in
  function
  | Define_fun (name, args, ty, exp) ->
     parens (string "define-fun" ^^ space ^^ string name
             ^^ space ^^ parens (separate_map space pp_str_smt_typ args)
             ^^ space ^^ pp_smt_typ ty
             ^//^ pp_smt_exp exp)

  | Declare_const (name, ty) ->
     pp_sfun "declare-const" [string name; pp_smt_typ ty]

  | Define_const (name, ty, exp) ->
     pp_sfun "define-const" [string name; pp_smt_typ ty; pp_smt_exp exp]

  | Write_mem (name, _, active, wk, addr, addr_ty, data, data_ty) ->
     pp_sfun "define-const" [string (name ^ "_kind"); string "Zwrite_kind"; pp_smt_exp wk] ^^ hardline
     ^^ pp_sfun "define-const" [string (name ^ "_active"); pp_smt_typ Bool; pp_smt_exp active] ^^ hardline
     ^^ pp_sfun "define-const" [string (name ^ "_data"); pp_smt_typ data_ty; pp_smt_exp data] ^^ hardline
     ^^ pp_sfun "define-const" [string (name ^ "_addr"); pp_smt_typ addr_ty; pp_smt_exp addr] ^^ hardline
     ^^ pp_sfun "declare-const" [string (name ^ "_ret"); pp_smt_typ Bool]

  | Write_mem_ea (name, _, active, wk, addr, addr_ty, data_size, data_size_ty) ->
     pp_sfun "define-const" [string (name ^ "_kind"); string "Zwrite_kind"; pp_smt_exp wk] ^^ hardline
     ^^ pp_sfun "define-const" [string (name ^ "_active"); pp_smt_typ Bool; pp_smt_exp active] ^^ hardline
     ^^ pp_sfun "define-const" [string (name ^ "_size"); pp_smt_typ data_size_ty; pp_smt_exp data_size] ^^ hardline
     ^^ pp_sfun "define-const" [string (name ^ "_addr"); pp_smt_typ addr_ty; pp_smt_exp addr]

  | Read_mem (name, _, active, ty, rk, addr, addr_ty) ->
     pp_sfun "define-const" [string (name ^ "_kind"); string "Zread_kind"; pp_smt_exp rk] ^^ hardline
     ^^ pp_sfun "define-const" [string (name ^ "_active"); pp_smt_typ Bool; pp_smt_exp active] ^^ hardline
     ^^ pp_sfun "define-const" [string (name ^ "_addr"); pp_smt_typ addr_ty; pp_smt_exp addr] ^^ hardline
     ^^ pp_sfun "declare-const" [string (name ^ "_ret"); pp_smt_typ ty]

  | Barrier (name, _, active, bk) ->
     pp_sfun "define-const" [string (name ^ "_kind"); string "Zbarrier_kind"; pp_smt_exp bk] ^^ hardline
     ^^ pp_sfun "define-const" [string (name ^ "_active"); pp_smt_typ Bool; pp_smt_exp active]

  | Excl_res (name, _, active) ->
     pp_sfun "declare-const" [string (name ^ "_res"); pp_smt_typ Bool] ^^ hardline
     ^^ pp_sfun "define-const" [string (name ^ "_active"); pp_smt_typ Bool; pp_smt_exp active]

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

open Parser_combinators

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
  | Interpreter.Done (state, v) -> Some v
  | Interpreter.Step (lazy_str, _, _, _) ->
     run (Interpreter.eval_frame frame)
  | Interpreter.Break frame ->
     run (Interpreter.eval_frame frame)
  | Interpreter.Fail (_, _, _, _, msg) ->
     None
  | Interpreter.Effect_request (out, state, stack, eff) ->
     run (Interpreter.default_effect_interp state eff)

let check_counterexample ast env fname function_id args arg_ctyps arg_smt_names =
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
     let istate = initial_state ast env !primops in
     let annot = (Parse_ast.Unknown, Type_check.mk_tannot env bool_typ no_effect) in
     let call = E_aux (E_app (function_id, List.map (fun (_, v) -> E_aux (E_internal_value v, (Parse_ast.Unknown, Type_check.empty_tannot))) counterexample), annot) in
     let result = run (Step (lazy "", istate, return call, [])) in
     begin match result with
     | Some (V_bool false) | None ->
        ksprintf prerr_endline "Replaying counterexample: %s" Util.("ok" |> green |> clear)
     | _ -> ()
     end
  | _ ->
     prerr_endline "Solver could not find counterexample"
  end;
  let status = Unix.close_process_in in_chan in
  ()
