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
open Type_check
open PPrint
module Big_int = Nat_big_num

let zencode_id = function
  | Id_aux (Id str, l) -> Id_aux (Id (Util.zencode_string str), l)
  | Id_aux (DeIid str, l) -> Id_aux (Id (Util.zencode_string ("op " ^ str)), l)

let lvar_typ = function
  | Local (_, typ) -> typ
  | Register typ -> typ
  | _ -> assert false

(**************************************************************************)
(* 1. Conversion to A-normal form (ANF)                                   *)
(**************************************************************************)

type aexp =
  | AE_val of aval
  | AE_app of id * aval list * typ
  | AE_cast of aexp * typ
  | AE_assign of id * aexp
  | AE_let of id * typ * aexp * aexp * typ
  | AE_block of aexp list * aexp * typ
  | AE_return of aval * typ

and aval =
  | AV_lit of lit * typ
  | AV_id of id * Type_check.lvar
  | AV_tuple of aval list
  | AV_C_fragment of string * typ

let rec map_aval f = function
  | AE_val v -> AE_val (f v)
  | AE_cast (aexp, typ) -> AE_cast (map_aval f aexp, typ)
  | AE_assign (id, aexp) -> AE_assign (id, map_aval f aexp)
  | AE_app (id, vs, typ) -> AE_app (id, List.map f vs, typ)
  | AE_let (id, typ1, aexp1, aexp2, typ2) -> AE_let (id, typ1, map_aval f aexp1, map_aval f aexp2, typ2)
  | AE_block (aexps, aexp, typ) -> AE_block (List.map (map_aval f) aexps, map_aval f aexp, typ)
  | AE_return (aval, typ) -> AE_return (f aval, typ)

let rec map_functions f = function
  | AE_app (id, vs, typ) -> f id vs typ
  | AE_cast (aexp, typ) -> AE_cast (map_functions f aexp, typ)
  | AE_assign (id, aexp) -> AE_assign (id, map_functions f aexp)
  | AE_let (id, typ1, aexp1, aexp2, typ2) -> AE_let (id, typ1, map_functions f aexp1, map_functions f aexp2, typ2)
  | AE_block (aexps, aexp, typ) -> AE_block (List.map (map_functions f) aexps, map_functions f aexp, typ)
  | AE_val _ | AE_return _ as v -> v

let pp_id ?color:(color=Util.green) id =
  string (string_of_id id |> color |> Util.clear)

let pp_lvar lvar doc =
  match lvar with
  | Register typ ->
     string "[R/" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Local (Mutable, typ) ->
     string "[M/" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Local (Immutable, typ) ->
     string "[I/" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Enum typ ->
     string "[E/" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Union (typq, typ) ->
     string "[U/" ^^ string (string_of_typquant typq ^ "/" ^ string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc
  | Unbound -> string "[?]" ^^ doc

let pp_annot typ doc =
  string "[" ^^ string (string_of_typ typ |> Util.yellow |> Util.clear) ^^ string "]" ^^ doc

let rec pp_aexp = function
  | AE_val v -> pp_aval v
  | AE_cast (aexp, typ) ->
     pp_annot typ (string "$" ^^ pp_aexp aexp)
  | AE_assign (id, aexp) ->
     pp_id id ^^ string " := " ^^ pp_aexp aexp
  | AE_app (id, args, typ) ->
     pp_annot typ (pp_id ~color:Util.red id ^^ parens (separate_map (comma ^^ space) pp_aval args))
  | AE_let (id, id_typ, binding, body, typ) -> group
     begin
       match binding with
       | AE_let _ ->
          (pp_annot typ (separate space [string "let"; pp_annot id_typ (pp_id id); string "="])
           ^^ hardline ^^ nest 2 (pp_aexp binding))
          ^^ hardline ^^ string "in" ^^ space ^^ pp_aexp body
       | _ ->
          pp_annot typ (separate space [string "let"; pp_annot id_typ (pp_id id); string "="; pp_aexp binding; string "in"])
          ^^ hardline ^^ pp_aexp body
     end
  | AE_block (aexps, aexp, typ) ->
     pp_annot typ (surround 2 0 lbrace (pp_block (aexps @ [aexp])) rbrace)
  | AE_return (v, typ) -> pp_annot typ (string "return" ^^ parens (pp_aval v))

and pp_block = function
  | [] -> string "()"
  | [aexp] -> pp_aexp aexp
  | aexp :: aexps -> pp_aexp aexp ^^ semi ^^ hardline ^^ pp_block aexps

and pp_aval = function
  | AV_lit (lit, typ) -> pp_annot typ (string (string_of_lit lit))
  | AV_id (id, lvar) -> pp_lvar lvar (pp_id id)
  | AV_tuple avals -> parens (separate_map (comma ^^ space) pp_aval avals)
  | AV_C_fragment (str, typ) -> pp_annot typ (string (str |> Util.cyan |> Util.clear))

let ae_lit lit typ = AE_val (AV_lit (lit, typ))

let gensym_counter = ref 0

let gensym () =
  let id = mk_id ("v" ^ string_of_int !gensym_counter) in
  incr gensym_counter;
  id

let rec split_block = function
  | [exp] -> [], exp
  | exp :: exps ->
     let exps, last = split_block exps in
     exp :: exps, last
  | [] -> failwith "empty block"

let rec anf (E_aux (e_aux, _) as exp) =
  let to_aval = function
    | AE_val v -> (v, fun x -> x)
    | AE_app (_, _, typ) | AE_let (_, _, _, _, typ) | AE_return (_, typ) | AE_cast (_, typ) as aexp ->
       let id = gensym () in
       (AV_id (id, Local (Immutable, typ)), fun x -> AE_let (id, typ, aexp, x, typ_of exp))
  in
  match e_aux with
  | E_lit lit -> ae_lit lit (typ_of exp)

  | E_block exps ->
     let exps, last = split_block exps in
     let aexps = List.map anf exps in
     let alast = anf last in
     AE_block (aexps, alast, typ_of exp)

  | E_assign (LEXP_aux (LEXP_id id, _), exp) ->
     let aexp = anf exp in
     AE_assign (id, aexp)

  | E_app (id, exps) ->
     let aexps = List.map anf exps in
     let avals = List.map to_aval aexps in
     let wrap = List.fold_left (fun f g x -> f (g x)) (fun x -> x) (List.map snd avals) in
     wrap (AE_app (id, List.map fst avals, typ_of exp))

  | E_throw exp ->
     let aexp = anf exp in
     let aval, wrap = to_aval aexp in
     wrap (AE_app (mk_id "throw", [aval], unit_typ))

  | E_exit exp ->
     let aexp = anf exp in
     let aval, wrap = to_aval aexp in
     wrap (AE_app (mk_id "exit", [aval], unit_typ))

  | E_return exp ->
     let aexp = anf exp in
     let aval, wrap = to_aval aexp in
     wrap (AE_return (aval, unit_typ))

  | E_assert (exp1, exp2) ->
     let aexp1 = anf exp1 in
     let aexp2 = anf exp2 in
     let aval1, wrap1 = to_aval aexp1 in
     let aval2, wrap2 = to_aval aexp2 in
     wrap1 (wrap2 (AE_app (mk_id "return", [aval1; aval2], unit_typ)))

  | E_cons (exp1, exp2) ->
     let aexp1 = anf exp1 in
     let aexp2 = anf exp2 in
     let aval1, wrap1 = to_aval aexp1 in
     let aval2, wrap2 = to_aval aexp2 in
     wrap1 (wrap2 (AE_app (mk_id "cons", [aval1; aval2], unit_typ)))

  | E_id id ->
     let lvar = Env.lookup_id id (env_of exp) in
     AE_val (AV_id (zencode_id id, lvar))

  | E_return exp ->
     let aval, wrap = to_aval (anf exp) in
     wrap (AE_return (aval, typ_of exp))

  | E_let (LB_aux (LB_val (P_aux (P_id id, _), binding), _), body) ->
     let env = env_of body in
     let lvar = Env.lookup_id id env in
     AE_let (zencode_id id, lvar_typ lvar, anf binding, anf body, typ_of exp)

  | E_tuple exps ->
     let aexps = List.map anf exps in
     let avals = List.map to_aval aexps in
     let wrap = List.fold_left (fun f g x -> f (g x)) (fun x -> x) (List.map snd avals) in
     wrap (AE_val (AV_tuple (List.map fst avals)))

  | E_cast (typ, exp) -> AE_cast (anf exp, typ)

  (* Need to think about how to do exception handling *)
  | E_try _ -> failwith "E_try TODO"

  | E_vector_access _ | E_vector_subrange _ | E_vector_update _ | E_vector_update_subrange _ | E_vector_append _ ->
     (* Should be re-written by type checker *)
     failwith "encountered raw vector operation when converting to ANF"

  | E_internal_value _ ->
     (* Interpreter specific *)
     failwith "encountered E_internal_value when converting to ANF"

  | E_sizeof _ | E_constraint _ ->
     (* Sizeof nodes removed by sizeof rewriting pass *)
     failwith "encountered E_sizeof or E_constraint node when converting to ANF"

  | _ -> failwith ("Cannot convert to ANF: " ^ string_of_exp exp)

(**************************************************************************)
(* 2. Converting sail types to C types                                    *)
(**************************************************************************)

let max_int64 = Big_int.of_int64 Int64.max_int
let min_int64 = Big_int.of_int64 Int64.min_int

type ctyp =
  | CT_mpz
  | CT_bv of bool
  | CT_uint64 of int * bool
  | CT_int
  | CT_int64
  | CT_unit

let ctyp_equal ctyp1 ctyp2 =
  match ctyp1, ctyp2 with
  | CT_mpz, CT_mpz -> true
  | CT_bv d1, CT_bv d2 -> d1 = d2
  | CT_uint64 (m1, d1), CT_uint64 (m2, d2) -> m1 = m2 && d1 = d2
  | CT_int, CT_int -> true
  | CT_int64, CT_int64 -> true
  | _, _ -> false

let string_of_ctyp = function
  | CT_mpz -> "mpz_t"
  | CT_bv true -> "bv_t<dec>"
  | CT_bv false -> "bv_t<inc>"
  | CT_uint64 (n, true) -> "uint64_t<" ^ string_of_int n ^ ", dec>"
  | CT_uint64 (n, false) -> "uint64_t<" ^ string_of_int n ^ ", int>"
  | CT_int64 -> "int64_t"
  | CT_int -> "int"
  | CT_unit -> "unit"

(* Convert a sail type into a C-type *)
let ctyp_of_typ (Typ_aux (typ_aux, _) as typ) =
  match typ_aux with
  | Typ_id id when string_of_id id = "bit" -> CT_int
  | Typ_id id when string_of_id id = "bool" -> CT_int
  | Typ_id id when string_of_id id = "int" -> CT_mpz
  | Typ_app (id, _) when string_of_id id = "range" || string_of_id id = "atom" ->
     begin
       match destruct_range typ with
       | None -> assert false (* Checked if range in guard *)
       | Some (n, m) ->
          match nexp_simp n, nexp_simp m with
          | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
               when Big_int.less_equal min_int64 n && Big_int.less_equal m max_int64 ->
             CT_int64
          | _ -> CT_mpz
     end
  | Typ_app (id, [Typ_arg_aux (Typ_arg_nexp n, _);
                  Typ_arg_aux (Typ_arg_order ord, _);
                  Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id vtyp_id, _)), _)])
       when string_of_id id = "vector" && string_of_id vtyp_id = "bit" ->
     begin
       let direction = match ord with Ord_aux (Ord_dec, _) -> true | Ord_aux (Ord_inc, _) -> false | _ -> assert false in
       match nexp_simp n with
       | Nexp_aux (Nexp_constant n, _) when Big_int.less_equal n (Big_int.of_int 64) -> CT_uint64 (Big_int.to_int n, direction)
       | _ -> CT_bv direction
     end
  | Typ_id id when string_of_id id = "unit" -> CT_unit
  | _ -> assert false

let is_stack_ctyp ctyp = match ctyp with
  | CT_uint64 _ | CT_int64 | CT_int -> true
  | CT_bv _ | CT_mpz -> false

let is_stack_typ typ = is_stack_ctyp (ctyp_of_typ typ)

(**************************************************************************)
(* 3. Optimization of primitives and literals                             *)
(**************************************************************************)

let literal_to_cstring (L_aux (l_aux, _) as lit) =
  match l_aux with
  | L_num n when Big_int.less_equal min_int64 n && Big_int.less_equal n max_int64 ->
     Some (Big_int.to_string n ^ "L")
  | L_hex str when String.length str <= 16 ->
     let padding = 16 - String.length str in
     Some ("0x" ^ String.make padding '0' ^ str ^ "ul")
  | L_unit -> Some "0"
  | _ -> None

let c_literals =
  let c_literal = function
    | AV_lit (lit, typ) as v ->
       begin
         match literal_to_cstring lit with
         | Some str -> AV_C_fragment (str, typ)
         | None -> v
       end
    | v -> v
  in
  map_aval c_literal

let mask m =
  if Big_int.less_equal m (Big_int.of_int 64) then
    let n = Big_int.to_int m in
    if n mod 4 == 0
    then "0x" ^ String.make (16 - n / 4) '0' ^ String.make (n / 4) 'F' ^ "ul"
    else "0b" ^ String.make (64 - n) '0' ^ String.make n '1' ^ "ul"
  else
    failwith "Tried to create a mask literal for a vector greater than 64 bits."

let c_aval = function
  | AV_lit (lit, typ) as v ->
     begin
       match literal_to_cstring lit with
       | Some str -> AV_C_fragment (str, typ)
       | None -> v
     end
  | AV_C_fragment (str, typ) -> AV_C_fragment (str, typ)
  (* An id can be converted to a C fragment if it's type can be stack-allocated. *)
  | AV_id (id, lvar) as v ->
     begin
       match lvar with
       | Local (_, typ) when is_stack_typ typ ->
          AV_C_fragment (string_of_id id, typ)
       | _ -> v
     end
  | AV_tuple avals -> AV_tuple avals

let is_c_fragment = function
  | AV_C_fragment _ -> true
  | _ -> false

let c_fragment_string = function
  | AV_C_fragment (str, _) -> str
  | _ -> assert false

let analyze_primop' id args typ =
  let no_change = AE_app (id, args, typ) in

  (* primops add_range and add_atom *)
  if string_of_id id = "add_range" || string_of_id id = "add_atom" then
    begin
      let n, m, x, y = match destruct_range typ, args with
        | Some (n, m), [x; y] -> n, m, x, y
        | _ -> failwith ("add_range has incorrect return type or arity ^ " ^ string_of_typ typ)
      in
      match nexp_simp n, nexp_simp m with
      | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _) ->
         if Big_int.less_equal min_int64 n && Big_int.less_equal m max_int64 then
           let x, y = c_aval x, c_aval y in
           if is_c_fragment x && is_c_fragment y then
             AE_val (AV_C_fragment (c_fragment_string x ^ " + " ^ c_fragment_string y, typ))
           else
             no_change
         else
           no_change
      | _ -> no_change
    end

  else if string_of_id id = "xor_vec" then
    begin
      let n, x, y = match typ, args with
        | Typ_aux (Typ_app (id, [Typ_arg_aux (Typ_arg_nexp n, _); _; _]), _), [x; y]
             when string_of_id id = "vector" -> n, x, y
        | _ -> failwith ("xor_vec has incorrect return type or arity " ^ string_of_typ typ)
      in
      match nexp_simp n with
      | Nexp_aux (Nexp_constant n, _) when Big_int.less_equal n (Big_int.of_int 64) ->
         let x, y = c_aval x, c_aval y in
         if is_c_fragment x && is_c_fragment y then
           AE_val (AV_C_fragment (c_fragment_string x ^ " ^ " ^ c_fragment_string y, typ))
         else
           no_change
      | _ -> no_change
    end

  else if string_of_id id = "add_vec" then
    begin
      let n, x, y = match typ, args with
        | Typ_aux (Typ_app (id, [Typ_arg_aux (Typ_arg_nexp n, _); _; _]), _), [x; y]
             when string_of_id id = "vector" -> n, x, y
        | _ -> failwith ("add_vec has incorrect return type or arity " ^ string_of_typ typ)
      in
      match nexp_simp n with
      | Nexp_aux (Nexp_constant n, _) when Big_int.less_equal n (Big_int.of_int 64) ->
         let x, y = c_aval x, c_aval y in
         if is_c_fragment x && is_c_fragment y then
           AE_val (AV_C_fragment ("(" ^ c_fragment_string x ^ " + " ^ c_fragment_string y ^ ") & " ^ mask n, typ))
         else
           no_change
      | _ -> no_change
    end

  else
    no_change

let analyze_primop id args typ =
  let no_change = AE_app (id, args, typ) in
  try analyze_primop' id args typ with
  | Failure _ -> no_change

(**************************************************************************)
(* 4. Conversion to low-level AST                                         *)
(**************************************************************************)

type cval =
  | CV_id of id * ctyp
  | CV_C_fragment of string * ctyp

let cval_ctyp = function
  | CV_id (_, ctyp) -> ctyp
  | CV_C_fragment (_, ctyp) -> ctyp

type instr =
  | I_decl of ctyp * id
  | I_alloc of ctyp * id
  | I_init of ctyp * id * cval
  | I_funcall of id * id * cval list * ctyp
  | I_convert of id * ctyp * id * ctyp
  | I_assign of id * cval
  | I_clear of ctyp * id
  | I_return of id

type cdef =
  | CDEF_reg_dec of ctyp * id
  | CDEF_fundef of id * id list * instr list

let pp_ctyp ctyp =
  string (string_of_ctyp ctyp |> Util.yellow |> Util.clear)

let pp_keyword str =
  string ((str |> Util.red |> Util.clear) ^ "$")

and pp_cval = function
  | CV_id (id, ctyp) -> parens (pp_ctyp ctyp) ^^ (pp_id id)
  | CV_C_fragment (str, ctyp) -> parens (pp_ctyp ctyp) ^^ (string (str |> Util.cyan |> Util.clear))

let pp_instr = function
  | I_decl (ctyp, id) ->
     parens (pp_ctyp ctyp) ^^ space ^^ pp_id id
  | I_alloc (ctyp, id) ->
     pp_keyword "ALLOC" ^^ parens (pp_ctyp ctyp) ^^ space ^^ pp_id id
  | I_init (ctyp, id, cval) ->
     pp_keyword "INIT" ^^ pp_ctyp ctyp ^^ parens (pp_id id ^^ string ", " ^^ pp_cval cval)
  | I_funcall (x, f, args, ctyp2) ->
     separate space [ pp_id x; string ":=";
                      pp_id ~color:Util.red f ^^ parens (separate_map (string ", ") pp_cval args);
                      string "->"; pp_ctyp ctyp2 ]
  | I_convert (x, ctyp1, y, ctyp2) ->
     separate space [ pp_id x; string ":=";
                      pp_keyword "CONVERT" ^^ pp_ctyp ctyp2 ^^ parens (pp_id y);
                      string "->"; pp_ctyp ctyp1 ]
  | I_assign (id, cval) ->
     separate space [pp_id id; string ":="; pp_cval cval]
  | I_clear (ctyp, id) ->
     pp_keyword "CLEAR" ^^ pp_ctyp ctyp ^^ parens (pp_id id)
  | I_return id ->
     pp_keyword "RETURN" ^^ pp_id id

let compile_funcall env id args typ =
  let setup = ref [] in
  let cleanup = ref [] in

  let _, Typ_aux (fn_typ, _) = Env.get_val_spec id env in
  let arg_typs, ret_typ = match fn_typ with
    | Typ_fn (Typ_aux (Typ_tup arg_typs, _), ret_typ, _) -> arg_typs, ret_typ
    | Typ_fn (arg_typ, ret_typ, _) -> [arg_typ], ret_typ
    | _ -> assert false
  in
  let arg_ctyps, ret_ctyp = List.map ctyp_of_typ arg_typs, ctyp_of_typ ret_typ in
  let final_ctyp = ctyp_of_typ typ in

  let setup_arg ctyp aval =
    match aval with
    | AV_C_fragment (c, typ) ->
      if is_stack_ctyp ctyp then
        CV_C_fragment (c, ctyp_of_typ typ)
      else
        let gs = gensym () in
        setup := I_decl (ctyp, gs) :: !setup;
        setup := I_init (ctyp, gs, CV_C_fragment (c, ctyp_of_typ typ)) :: !setup;
        cleanup := I_clear (ctyp, gs) :: !cleanup;
        CV_id (gs, ctyp)
    | AV_id (id, lvar) ->
       let have_ctyp = ctyp_of_typ (lvar_typ lvar) in
       if ctyp_equal ctyp have_ctyp then
         CV_id (id, ctyp)
       else if is_stack_ctyp have_ctyp && not (is_stack_ctyp ctyp) then
         let gs = gensym () in
         setup := I_decl (ctyp, gs) :: !setup;
         setup := I_init (ctyp, gs, CV_id (id, have_ctyp)) :: !setup;
         cleanup := I_clear (ctyp, gs) :: !cleanup;
         CV_id (gs, ctyp)
       else
         CV_id (mk_id ("????" ^ string_of_ctyp (ctyp_of_typ (lvar_typ lvar))), ctyp)
    | _ -> CV_id (mk_id "???", ctyp)
  in

  let sargs = List.map2 setup_arg arg_ctyps args in

  let call =
    if ctyp_equal final_ctyp ret_ctyp then
      fun ret -> I_funcall (ret, id, sargs, ret_ctyp)
    else if not (is_stack_ctyp ret_ctyp) && is_stack_ctyp final_ctyp then
      let gs = gensym () in
      setup := I_alloc (ret_ctyp, gs) :: !setup;
      setup := I_funcall (gs, id, sargs, ret_ctyp) :: !setup;
      cleanup := I_clear (ret_ctyp, gs) :: !cleanup;
      fun ret -> I_convert (ret, final_ctyp, gs, ret_ctyp)
    else
      assert false
  in

  (List.rev !setup, final_ctyp, call, !cleanup)

let rec compile_aexp env = function
  | AE_let (id, _, binding, body, typ) ->
     let setup, ctyp, call, cleanup = compile_aexp env binding in
     let letb1, letb1c =
       if is_stack_ctyp ctyp then
         [I_decl (ctyp, id); call id], []
       else
         [I_alloc (ctyp, id); call id], [I_clear (ctyp, id)]
     in
     let letb2 = setup @ letb1 @ cleanup in
     let setup, ctyp, call, cleanup = compile_aexp env body in
     letb2 @ setup, ctyp, call, cleanup @ letb1c

  | AE_app (id, vs, typ) ->
     compile_funcall env id vs typ

  | AE_val (AV_C_fragment (c, typ)) ->
     let ctyp = ctyp_of_typ typ in
     [], ctyp, (fun id -> I_assign (id, CV_C_fragment (c, ctyp))), []

  | AE_val (AV_id (id, lvar)) ->
     let ctyp = ctyp_of_typ (lvar_typ lvar) in
     [], CT_unit, (fun id -> I_assign (id, CV_id (id, ctyp))), []

  | AE_block (aexps, aexp, _) ->
     let block = compile_block env aexps in
     let setup, ctyp, call, cleanup = compile_aexp env aexp in
     block @ setup, ctyp, call, cleanup

  | AE_cast (aexp, typ) -> compile_aexp env aexp

and compile_block env = function
  | [] -> []
  | exp :: exps ->
     let setup, _, call, cleanup = compile_aexp env exp in
     let rest = compile_block env exps in
     let gs = gensym () in
     setup @ [I_decl (CT_unit, gs); call gs] @ cleanup @ rest

let compile_def env = function
  | DEF_reg_dec (DEC_aux (DEC_reg (typ, id), _)) ->
     [CDEF_reg_dec (ctyp_of_typ typ, id)]
  | DEF_reg_dec _ -> failwith "Unsupported register declaration" (* FIXME *)

  | DEF_spec _ -> []

  | DEF_fundef (FD_aux (FD_function (_, _, _, [FCL_aux (FCL_Funcl (id, pexp), _)]), _)) ->
     begin
       match pexp with
       | Pat_aux (Pat_exp (pat, exp), _) ->
          let aexp = map_functions analyze_primop (c_literals (anf exp)) in
          print_endline (Pretty_print_sail.to_string (pp_aexp aexp));
          let setup, ctyp, call, cleanup = compile_aexp env aexp in
          let gs = gensym () in
          let instrs =
            if is_stack_ctyp ctyp then
              setup @ [I_decl (ctyp, gs); call gs] @ cleanup @ [I_return gs]
            else
              assert false
          in
          [CDEF_fundef (id, [], instrs)]
       | _ -> assert false
     end

  | _ -> assert false

(**************************************************************************)
(* 5. Code generation                                                     *)
(**************************************************************************)

let sgen_id id = Util.zencode_string (string_of_id id)
let codegen_id id = string (sgen_id id)

let sgen_ctyp = function
  | CT_unit -> "int"
  | CT_int -> "int"
  | CT_uint64 _ -> "uint64_t"
  | CT_int64 -> "int64_t"
  | CT_mpz -> "mpz_t"
  | CT_bv _ -> "bv_t"

let sgen_cval = function
  | CV_C_fragment (c, _) -> c
  | CV_id (id, _) -> string_of_id id
  | _ -> "CVAL??"

let codegen_instr = function
  | I_decl (ctyp, id) ->
     string (Printf.sprintf "%s %s;" (sgen_ctyp ctyp) (string_of_id id))
  | I_assign (id, cval) ->
     string (Printf.sprintf "%s = %s;" (string_of_id id) (sgen_cval cval))
  | I_funcall (x, f, args, ctyp) ->
     let args = Util.string_of_list ", " sgen_cval args in
     if is_stack_ctyp ctyp then
       string (Printf.sprintf "%s = %s(%s);" (string_of_id x) (sgen_id f) args)
     else
       string (Printf.sprintf "%s(%s, %s);" (sgen_id f) (string_of_id x) args)
  | I_clear (ctyp, id) ->
     string (Printf.sprintf "clear_%s(%s);" (sgen_ctyp ctyp) (string_of_id id))
  | I_init (ctyp, id, cval) ->
     string (Printf.sprintf "init_%s_of_%s(%s, %s);"
                            (sgen_ctyp ctyp)
                            (sgen_ctyp (cval_ctyp cval))
                            (string_of_id id)
                            (sgen_cval cval))
  | I_alloc (ctyp, id) ->
     string (Printf.sprintf "%s %s;" (sgen_ctyp ctyp) (string_of_id id))
     ^^ hardline
     ^^ string (Printf.sprintf "init_%s(%s);" (sgen_ctyp ctyp) (string_of_id id))
  | I_convert (x, ctyp1, y, ctyp2) ->
     string (Printf.sprintf "%s = convert_%s_of_%s(%s);"
                            (string_of_id x)
                            (sgen_ctyp ctyp1)
                            (sgen_ctyp ctyp2)
                            (string_of_id y))
  | I_return id ->
     string (Printf.sprintf "return %s;" (string_of_id id))

let codegen_def env = function
  | CDEF_reg_dec (ctyp, id) ->
     string (Printf.sprintf "%s %s;" (sgen_ctyp ctyp) (sgen_id id))
  | CDEF_fundef (id, _, instrs) ->
     List.iter (fun instr -> print_endline (Pretty_print_sail.to_string (pp_instr instr))) instrs;
     codegen_id id ^^ hardline
     ^^ string "{"
     ^^ jump 2 2 (separate_map hardline codegen_instr instrs) ^^ hardline
     ^^ string "}"

let compile_ast env (Defs defs) =
  let cdefs = List.concat (List.map (compile_def env) defs) in
  let docs = List.map (codegen_def env) cdefs in

  let preamble = separate hardline
    [ string "#include \"sail.h\"" ]
  in

  let hlhl = hardline ^^ hardline in

  Pretty_print_sail.to_string (preamble ^^ hlhl ^^ separate hlhl docs)
  |> print_endline

let print_compiled (setup, ctyp, call, cleanup) =
  List.iter (fun instr -> print_endline (Pretty_print_sail.to_string (pp_instr instr))) setup;
  print_endline (Pretty_print_sail.to_string (pp_instr (call (mk_id ("?" ^ string_of_ctyp ctyp)))));
  List.iter (fun instr -> print_endline (Pretty_print_sail.to_string (pp_instr instr))) cleanup

let compile_exp env exp =
  let aexp = anf exp in
  let aexp = c_literals aexp in
  let aexp = map_functions analyze_primop aexp in
  print_endline "\n###################### COMPILED ######################\n";
  print_compiled (compile_aexp env aexp);
  print_endline "\n###################### ANF ######################\n";
  aexp


(*

{
  uint64_t zx = 0x000000000000F000L;
  uint64_t v0 = (zx + 0x000000000000000FL) & 0x000000000000FFFFL;
  uint64_t res = (v0 + 0x000000000000FFFFL) & 0x000000000000FFFFL;
  return res;
}

*)
