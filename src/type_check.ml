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
open Util
open Ast_util
open Big_int

let opt_tc_debug = ref 0
let opt_no_effects = ref false
let depth = ref 0

let rec take n xs = match n, xs with
  | 0, _ -> []
  | n, [] -> []
  | n, (x :: xs) -> x :: take (n - 1) xs 

let rec indent n = match n with
  | 0 -> ""
  | n -> "|   " ^ indent (n - 1)

let typ_debug m = if !opt_tc_debug > 1 then prerr_endline (indent !depth ^ m) else ()

let typ_print m = if !opt_tc_debug > 0 then prerr_endline (indent !depth ^ m) else ()

let typ_warning m = prerr_endline ("Warning: " ^ m)

exception Type_error of l * string;;

let typ_error l m = raise (Type_error (l, m))

let deinfix = function
  | Id_aux (Id v, l) -> Id_aux (DeIid v, l)
  | Id_aux (DeIid v, l) -> Id_aux (DeIid v, l)

let field_name rec_id id =
  match rec_id, id with
  | Id_aux (Id r, _), Id_aux (Id v, l) -> Id_aux (Id (r ^ "." ^ v), l)
  | _, _ -> assert false

let string_of_bind (typquant, typ) = string_of_typquant typquant ^ ". " ^ string_of_typ typ

let unaux_nexp (Nexp_aux (nexp, _)) = nexp
let unaux_order (Ord_aux (ord, _)) = ord
let unaux_typ (Typ_aux (typ, _)) = typ

let mk_typ typ = Typ_aux (typ, Parse_ast.Unknown)
let mk_typ_arg arg = Typ_arg_aux (arg, Parse_ast.Unknown)
let mk_id str = Id_aux (Id str, Parse_ast.Unknown)
let mk_kid str = Kid_aux (Var ("'" ^ str), Parse_ast.Unknown)
let mk_infix_id str = Id_aux (DeIid str, Parse_ast.Unknown)

let mk_id_typ id = Typ_aux (Typ_id id, Parse_ast.Unknown)

let inc_ord = Ord_aux (Ord_inc, Parse_ast.Unknown)
let dec_ord = Ord_aux (Ord_dec, Parse_ast.Unknown)

let mk_ord ord_aux = Ord_aux (ord_aux, Parse_ast.Unknown)

let rec nexp_simp (Nexp_aux (nexp, l)) = Nexp_aux (nexp_simp_aux nexp, l)
and nexp_simp_aux = function
  | Nexp_sum (n1, n2) ->
     begin
       let (Nexp_aux (n1_simp, _) as n1) = nexp_simp n1 in
       let (Nexp_aux (n2_simp, _) as n2) = nexp_simp n2 in
       match n1_simp, n2_simp with
       | Nexp_constant c1, Nexp_constant c2 -> Nexp_constant (c1 + c2)
       | _, Nexp_neg n2 -> Nexp_minus (n1, n2)
       | _, _ -> Nexp_sum (n1, n2)
     end
  | Nexp_times (n1, n2) ->
     begin
       let (Nexp_aux (n1_simp, _) as n1) = nexp_simp n1 in
       let (Nexp_aux (n2_simp, _) as n2) = nexp_simp n2 in
       match n1_simp, n2_simp with
       | Nexp_constant c1, Nexp_constant c2 -> Nexp_constant (c1 * c2)
       | _, _ -> Nexp_times (n1, n2)
     end
  | Nexp_minus (n1, n2) ->
     begin
       let (Nexp_aux (n1_simp, _) as n1) = nexp_simp n1 in
       let (Nexp_aux (n2_simp, _) as n2) = nexp_simp n2 in
       typ_debug ("SIMP: " ^ string_of_nexp n1 ^ " - " ^ string_of_nexp n2);
       match n1_simp, n2_simp with
       | Nexp_constant c1, Nexp_constant c2 -> Nexp_constant (c1 - c2)
       | _, _ -> Nexp_minus (n1, n2)
     end
  | nexp -> nexp

let int_typ = mk_id_typ (mk_id "int")
let nat_typ = mk_id_typ (mk_id "nat")
let unit_typ = mk_id_typ (mk_id "unit")
let bit_typ = mk_id_typ (mk_id "bit")
let real_typ = mk_id_typ (mk_id "real")
let app_typ id args = mk_typ (Typ_app (id, args))
let atom_typ nexp =
  mk_typ (Typ_app (mk_id "atom", [mk_typ_arg (Typ_arg_nexp (nexp_simp nexp))]))
let range_typ nexp1 nexp2 =
  mk_typ (Typ_app (mk_id "range", [mk_typ_arg (Typ_arg_nexp (nexp_simp nexp1));
                                   mk_typ_arg (Typ_arg_nexp (nexp_simp nexp2))]))
let bool_typ = mk_id_typ (mk_id "bool")
let string_typ = mk_id_typ (mk_id "string")
let list_typ typ = mk_typ (Typ_app (mk_id "list", [mk_typ_arg (Typ_arg_typ typ)]))

let vector_typ n m ord typ =
  mk_typ (Typ_app (mk_id "vector",
                   [mk_typ_arg (Typ_arg_nexp (nexp_simp n));
                    mk_typ_arg (Typ_arg_nexp (nexp_simp m));
                    mk_typ_arg (Typ_arg_order ord);
                    mk_typ_arg (Typ_arg_typ typ)]))

let exc_typ = mk_id_typ (mk_id "exception")

let is_range (Typ_aux (typ_aux, _)) =
  match typ_aux with
  | Typ_app (f, [Typ_arg_aux (Typ_arg_nexp n, _)])
       when string_of_id f = "atom" -> Some (n, n)
  | Typ_app (f, [Typ_arg_aux (Typ_arg_nexp n1, _); Typ_arg_aux (Typ_arg_nexp n2, _)])
       when string_of_id f = "range" -> Some (n1, n2)
  | _ -> None

let is_list (Typ_aux (typ_aux, _)) =
  match typ_aux with
  | Typ_app (f, [Typ_arg_aux (Typ_arg_typ typ, _)])
       when string_of_id f = "list" -> Some typ
  | _ -> None

let nconstant c = Nexp_aux (Nexp_constant c, Parse_ast.Unknown)
let nminus n1 n2 = Nexp_aux (Nexp_minus (n1, n2), Parse_ast.Unknown)
let nsum n1 n2 = Nexp_aux (Nexp_sum (n1, n2), Parse_ast.Unknown)
let ntimes n1 n2 = Nexp_aux (Nexp_times (n1, n2), Parse_ast.Unknown)
let npow2 n = Nexp_aux (Nexp_exp n, Parse_ast.Unknown)
let nvar kid = Nexp_aux (Nexp_var kid, Parse_ast.Unknown)
let nid id = Nexp_aux (Nexp_id id, Parse_ast.Unknown)

let nc_eq n1 n2 = mk_nc (NC_fixed (n1, n2))
let nc_neq n1 n2 = mk_nc (NC_not_equal (n1, n2))
let nc_lteq n1 n2 = NC_aux (NC_bounded_le (n1, n2), Parse_ast.Unknown)
let nc_gteq n1 n2 = NC_aux (NC_bounded_ge (n1, n2), Parse_ast.Unknown)
let nc_lt n1 n2 = nc_lteq n1 (nsum n2 (nconstant 1))
let nc_gt n1 n2 = nc_gteq n1 (nsum n2 (nconstant 1))
let nc_and nc1 nc2 = mk_nc (NC_and (nc1, nc2))
let nc_or nc1 nc2 = mk_nc (NC_or (nc1, nc2))
let nc_true = mk_nc NC_true
let nc_false = mk_nc NC_false

let mk_lit l = E_aux (E_lit (L_aux (l, Parse_ast.Unknown)), (Parse_ast.Unknown, ()))

let rec nc_negate (NC_aux (nc, _)) =
  match nc with
  | NC_bounded_ge (n1, n2) -> nc_lt n1 n2
  | NC_bounded_le (n1, n2) -> nc_gt n1 n2
  | NC_fixed (n1, n2) -> nc_neq n1 n2
  | NC_not_equal (n1, n2) -> nc_eq n1 n2
  | NC_and (n1, n2) -> mk_nc (NC_or (nc_negate n1, nc_negate n2))
  | NC_or (n1, n2) -> mk_nc (NC_and (nc_negate n1, nc_negate n2))
  | NC_false -> mk_nc NC_true
  | NC_true -> mk_nc NC_false
  | NC_nat_set_bounded (kid, []) -> typ_error Parse_ast.Unknown "Cannot negate empty nexp set"
  | NC_nat_set_bounded (kid, [int]) -> nc_neq (nvar kid) (nconstant int)
  | NC_nat_set_bounded (kid, int :: ints) ->
     mk_nc (NC_and (nc_neq (nvar kid) (nconstant int), nc_negate (mk_nc (NC_nat_set_bounded (kid, ints)))))

(* Utilities for constructing effect sets *)

let mk_effect effs =
  Effect_aux (Effect_set (List.map (fun be_aux -> BE_aux (be_aux, Parse_ast.Unknown)) effs), Parse_ast.Unknown)

let no_effect = mk_effect []

module BESet = Set.Make(BE)

let union_effects e1 e2 =
  match e1, e2 with
  | Effect_aux (Effect_set base_effs1, _), Effect_aux (Effect_set base_effs2, _) ->
     let base_effs3 = BESet.elements (BESet.of_list (base_effs1 @ base_effs2)) in
     Effect_aux (Effect_set base_effs3, Parse_ast.Unknown)
  | _, _ -> assert false (* We don't do Effect variables *)

let equal_effects e1 e2 =
  match e1, e2 with
  | Effect_aux (Effect_set base_effs1, _), Effect_aux (Effect_set base_effs2, _) ->
     BESet.compare (BESet.of_list base_effs1) (BESet.of_list base_effs2) = 0
  | _, _ -> assert false (* We don't do Effect variables *)

(* An index_sort is a more general form of range type: it can either
   be IS_int, which represents every natural number, or some set of
   natural numbers given by an IS_prop expression of the form
   {'n. f('n) <= g('n) /\ ...} *)
type index_sort =
  | IS_int
  | IS_prop of kid * (nexp * nexp) list

let string_of_index_sort = function
  | IS_int -> "INT"
  | IS_prop (kid, constraints) ->
     "{" ^ string_of_kid kid ^ " | "
     ^ string_of_list " & " (fun (x, y) -> string_of_nexp x ^ " <= " ^ string_of_nexp y) constraints
     ^ "}"

let quant_items : typquant -> quant_item list = function
  | TypQ_aux (TypQ_tq qis, _) -> qis
  | TypQ_aux (TypQ_no_forall, _) -> []

let quant_split typq =
  let qi_kopt = function
    | QI_aux (QI_id kopt, _) -> [kopt]
    | _ -> []
  in
  let qi_nc = function
    | QI_aux (QI_const nc, _) -> [nc]
    | _ -> []
  in
  let qis = quant_items typq in
  List.concat (List.map qi_kopt qis), List.concat (List.map qi_nc qis)

let kopt_kid (KOpt_aux (kopt_aux, _)) =
  match kopt_aux with
  | KOpt_none kid | KOpt_kind (_, kid) -> kid

let is_nat_kopt = function
  | KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (BK_nat, _)], _), _), _) -> true
  | KOpt_aux (KOpt_none _, _) -> true
  | _ -> false

let is_order_kopt = function
  | KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (BK_order, _)], _), _), _) -> true
  | _ -> false

let is_typ_kopt = function
  | KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (BK_type, _)], _), _), _) -> true
  | _ -> false

(**************************************************************************)
(* 1. Substitutions                                                       *)
(**************************************************************************)

let rec nexp_subst sv subst (Nexp_aux (nexp, l)) = Nexp_aux (nexp_subst_aux sv subst nexp, l)
and nexp_subst_aux sv subst = function
  | Nexp_id v -> Nexp_id v
  | Nexp_var kid -> if Kid.compare kid sv = 0 then subst else Nexp_var kid
  | Nexp_constant c -> Nexp_constant c
  | Nexp_times (nexp1, nexp2) -> Nexp_times (nexp_subst sv subst nexp1, nexp_subst sv subst nexp2)
  | Nexp_sum (nexp1, nexp2) -> Nexp_sum (nexp_subst sv subst nexp1, nexp_subst sv subst nexp2)
  | Nexp_minus (nexp1, nexp2) -> Nexp_minus (nexp_subst sv subst nexp1, nexp_subst sv subst nexp2)
  | Nexp_exp nexp -> Nexp_exp (nexp_subst sv subst nexp)
  | Nexp_neg nexp -> Nexp_neg (nexp_subst sv subst nexp)

let rec nexp_set_to_or l subst = function
  | [] -> typ_error l "Cannot substitute into empty nexp set"
  | [int] -> NC_fixed (subst, nconstant int)
  | (int :: ints) -> NC_or (mk_nc (NC_fixed (subst, nconstant int)), mk_nc (nexp_set_to_or l subst ints))

let rec nc_subst_nexp sv subst (NC_aux (nc, l)) = NC_aux (nc_subst_nexp_aux l sv subst nc, l)
and nc_subst_nexp_aux l sv subst = function
  | NC_fixed (n1, n2) -> NC_fixed (nexp_subst sv subst n1, nexp_subst sv subst n2)
  | NC_bounded_ge (n1, n2) -> NC_bounded_ge (nexp_subst sv subst n1, nexp_subst sv subst n2)
  | NC_bounded_le (n1, n2) -> NC_bounded_le (nexp_subst sv subst n1, nexp_subst sv subst n2)
  | NC_nat_set_bounded (kid, ints) as set_nc ->
     if Kid.compare kid sv = 0
     then nexp_set_to_or l (mk_nexp subst) ints
     else set_nc
  | NC_or (nc1, nc2) -> NC_or (nc_subst_nexp sv subst nc1, nc_subst_nexp sv subst nc2)
  | NC_and (nc1, nc2) -> NC_and (nc_subst_nexp sv subst nc1, nc_subst_nexp sv subst nc2)
  | NC_false -> NC_false
  | NC_true -> NC_true

let rec typ_subst_nexp sv subst (Typ_aux (typ, l)) = Typ_aux (typ_subst_nexp_aux sv subst typ, l)
and typ_subst_nexp_aux sv subst = function
  | Typ_wild -> Typ_wild
  | Typ_id v -> Typ_id v
  | Typ_var kid -> Typ_var kid
  | Typ_fn (typ1, typ2, effs) -> Typ_fn (typ_subst_nexp sv subst typ1, typ_subst_nexp sv subst typ2, effs)
  | Typ_tup typs -> Typ_tup (List.map (typ_subst_nexp sv subst) typs)
  | Typ_app (f, args) -> Typ_app (f, List.map (typ_subst_arg_nexp sv subst) args)
  | Typ_exist (kids, nc, typ) when KidSet.mem sv (KidSet.of_list kids) -> Typ_exist (kids, nc, typ)
  | Typ_exist (kids, nc, typ) -> Typ_exist (kids, nc_subst_nexp sv subst nc, typ_subst_nexp sv subst typ)
and typ_subst_arg_nexp sv subst (Typ_arg_aux (arg, l)) = Typ_arg_aux (typ_subst_arg_nexp_aux sv subst arg, l)
and typ_subst_arg_nexp_aux sv subst = function
  | Typ_arg_nexp nexp -> Typ_arg_nexp (nexp_subst sv subst nexp)
  | Typ_arg_typ typ -> Typ_arg_typ (typ_subst_nexp sv subst typ)
  | Typ_arg_order ord -> Typ_arg_order ord
  | Typ_arg_effect eff -> Typ_arg_effect eff

let rec typ_subst_typ sv subst (Typ_aux (typ, l)) = Typ_aux (typ_subst_typ_aux sv subst typ, l)
and typ_subst_typ_aux sv subst = function
  | Typ_wild -> Typ_wild
  | Typ_id v -> Typ_id v
  | Typ_var kid -> if Kid.compare kid sv = 0 then subst else Typ_var kid
  | Typ_fn (typ1, typ2, effs) -> Typ_fn (typ_subst_typ sv subst typ1, typ_subst_typ sv subst typ2, effs)
  | Typ_tup typs -> Typ_tup (List.map (typ_subst_typ sv subst) typs)
  | Typ_app (f, args) -> Typ_app (f, List.map (typ_subst_arg_typ sv subst) args)
  | Typ_exist (kids, nc, typ) -> Typ_exist (kids, nc, typ_subst_typ sv subst typ)
and typ_subst_arg_typ sv subst (Typ_arg_aux (arg, l)) = Typ_arg_aux (typ_subst_arg_typ_aux sv subst arg, l)
and typ_subst_arg_typ_aux sv subst = function
  | Typ_arg_nexp nexp -> Typ_arg_nexp nexp
  | Typ_arg_typ typ -> Typ_arg_typ (typ_subst_typ sv subst typ)
  | Typ_arg_order ord -> Typ_arg_order ord
  | Typ_arg_effect eff -> Typ_arg_effect eff

let order_subst_aux sv subst = function
  | Ord_var kid -> if Kid.compare kid sv = 0 then subst else Ord_var kid
  | Ord_inc -> Ord_inc
  | Ord_dec -> Ord_dec

let order_subst sv subst (Ord_aux (ord, l)) = Ord_aux (order_subst_aux sv subst ord, l)

let rec typ_subst_order sv subst (Typ_aux (typ, l)) = Typ_aux (typ_subst_order_aux sv subst typ, l)
and typ_subst_order_aux sv subst = function
  | Typ_wild -> Typ_wild
  | Typ_id v -> Typ_id v
  | Typ_var kid -> Typ_var kid
  | Typ_fn (typ1, typ2, effs) -> Typ_fn (typ_subst_order sv subst typ1, typ_subst_order sv subst typ2, effs)
  | Typ_tup typs -> Typ_tup (List.map (typ_subst_order sv subst) typs)
  | Typ_app (f, args) -> Typ_app (f, List.map (typ_subst_arg_order sv subst) args)
  | Typ_exist (kids, nc, typ) -> Typ_exist (kids, nc, typ_subst_order sv subst typ)
and typ_subst_arg_order sv subst (Typ_arg_aux (arg, l)) = Typ_arg_aux (typ_subst_arg_order_aux sv subst arg, l)
and typ_subst_arg_order_aux sv subst = function
  | Typ_arg_nexp nexp -> Typ_arg_nexp nexp
  | Typ_arg_typ typ -> Typ_arg_typ (typ_subst_order sv subst typ)
  | Typ_arg_order ord -> Typ_arg_order (order_subst sv subst ord)
  | Typ_arg_effect eff -> Typ_arg_effect eff

let rec typ_subst_kid sv subst (Typ_aux (typ, l)) = Typ_aux (typ_subst_kid_aux sv subst typ, l)
and typ_subst_kid_aux sv subst = function
  | Typ_wild -> Typ_wild
  | Typ_id v -> Typ_id v
  | Typ_var kid -> if Kid.compare kid sv = 0 then Typ_var subst else Typ_var kid
  | Typ_fn (typ1, typ2, effs) -> Typ_fn (typ_subst_kid sv subst typ1, typ_subst_kid sv subst typ2, effs)
  | Typ_tup typs -> Typ_tup (List.map (typ_subst_kid sv subst) typs)
  | Typ_app (f, args) -> Typ_app (f, List.map (typ_subst_arg_kid sv subst) args)
  | Typ_exist (kids, nc, typ) when KidSet.mem sv (KidSet.of_list kids) -> Typ_exist (kids, nc, typ)
  | Typ_exist (kids, nc, typ) -> Typ_exist (kids, nc_subst_nexp sv (Nexp_var subst) nc, typ_subst_kid sv subst typ)
and typ_subst_arg_kid sv subst (Typ_arg_aux (arg, l)) = Typ_arg_aux (typ_subst_arg_kid_aux sv subst arg, l)
and typ_subst_arg_kid_aux sv subst = function
  | Typ_arg_nexp nexp -> Typ_arg_nexp (nexp_subst sv (Nexp_var subst) nexp)
  | Typ_arg_typ typ -> Typ_arg_typ (typ_subst_kid sv subst typ)
  | Typ_arg_order ord -> Typ_arg_order (order_subst sv (Ord_var subst) ord)
  | Typ_arg_effect eff -> Typ_arg_effect eff

let quant_item_subst_kid_aux sv subst = function
  | QI_id (KOpt_aux (KOpt_none kid, l)) as qid ->
     if Kid.compare kid sv = 0 then QI_id (KOpt_aux (KOpt_none subst, l)) else qid
  | QI_id (KOpt_aux (KOpt_kind (k, kid), l)) as qid ->
     if Kid.compare kid sv = 0 then QI_id (KOpt_aux (KOpt_kind (k, subst), l)) else qid
  | QI_const nc -> QI_const (nc_subst_nexp sv (Nexp_var subst) nc)

let quant_item_subst_kid sv subst (QI_aux (quant, l)) = QI_aux (quant_item_subst_kid_aux sv subst quant, l)

let typquant_subst_kid_aux sv subst = function
  | TypQ_tq quants -> TypQ_tq (List.map (quant_item_subst_kid sv subst) quants)
  | TypQ_no_forall -> TypQ_no_forall

let typquant_subst_kid sv subst (TypQ_aux (typq, l)) = TypQ_aux (typquant_subst_kid_aux sv subst typq, l)

(**************************************************************************)
(* 2. Environment                                                         *)
(**************************************************************************)

type mut = Immutable | Mutable

type lvar = Register of typ | Enum of typ | Local of mut * typ | Union of typquant * typ | Unbound

module Env : sig
  type t
  val add_val_spec : id -> typquant * typ -> t -> t
  val get_val_spec : id -> t -> typquant * typ
  val is_union_constructor : id -> t -> bool
  val add_record : id -> typquant -> (typ * id) list -> t -> t
  val is_record : id -> t -> bool
  val get_accessor : id -> id -> t -> typquant * typ
  val add_local : id -> mut * typ -> t -> t
  val add_variant : id -> typquant * type_union list -> t -> t
  val add_union_id : id -> typquant * typ -> t -> t
  val add_flow : id -> (typ -> typ) -> t -> t
  val get_flow : id -> t -> typ -> typ
  val is_register : id -> t -> bool
  val get_register : id -> t -> typ
  val add_register : id -> typ -> t -> t
  val add_regtyp : id -> int -> int -> (index_range * id) list -> t -> t
  val is_regtyp : id -> t -> bool
  val get_regtyp : id -> t -> int * int * (index_range * id) list
  val is_mutable : id -> t -> bool
  val get_constraints : t -> n_constraint list
  val add_constraint : n_constraint -> t -> t
  val get_typ_var : kid -> t -> base_kind_aux
  val get_typ_vars : t -> base_kind_aux KBindings.t
  val add_typ_var : kid -> base_kind_aux -> t -> t
  val get_ret_typ : t -> typ option
  val add_ret_typ : typ -> t -> t
  val add_typ_synonym : id -> (t -> typ_arg list -> typ) -> t -> t
  val get_typ_synonym : id -> t -> t -> typ_arg list -> typ
  val add_overloads : id -> id list -> t -> t
  val get_overloads : id -> t -> id list
  val is_extern : id -> t -> bool
  val add_extern : id -> string -> t -> t
  val get_extern : id -> t -> string
  val get_default_order : t -> order
  val set_default_order_inc : t -> t
  val set_default_order_dec : t -> t
  val add_enum : id -> id list -> t -> t
  val get_enum : id -> t -> id list
  val get_casts : t -> id list
  val allow_casts : t -> bool
  val no_casts : t -> t
  val enable_casts : t -> t
  val add_cast : id -> t -> t
  val lookup_id : id -> t -> lvar
  val fresh_kid : t -> kid
  val expand_synonyms : t -> typ -> typ
  val base_typ_of : t -> typ -> typ
  val empty : t
end = struct
  type t =
    { top_val_specs : (typquant * typ) Bindings.t;
      locals : (mut * typ) Bindings.t;
      union_ids : (typquant * typ) Bindings.t;
      registers : typ Bindings.t;
      regtyps : (int * int * (index_range * id) list) Bindings.t;
      variants : (typquant * type_union list) Bindings.t;
      typ_vars : base_kind_aux KBindings.t;
      typ_synonyms : (t -> typ_arg list -> typ) Bindings.t;
      overloads : (id list) Bindings.t;
      flow : (typ -> typ) Bindings.t;
      enums : IdSet.t Bindings.t;
      records : (typquant * (typ * id) list) Bindings.t;
      accessors : (typquant * typ) Bindings.t;
      externs : string Bindings.t;
      casts : id list;
      allow_casts : bool;
      constraints : n_constraint list;
      default_order : order option;
      ret_typ : typ option
    }

  let empty =
    { top_val_specs = Bindings.empty;
      locals = Bindings.empty;
      union_ids = Bindings.empty;
      registers = Bindings.empty;
      regtyps = Bindings.empty;
      variants = Bindings.empty;
      typ_vars = KBindings.empty;
      typ_synonyms = Bindings.empty;
      overloads = Bindings.empty;
      flow = Bindings.empty;
      enums = Bindings.empty;
      records = Bindings.empty;
      accessors = Bindings.empty;
      externs = Bindings.empty;
      casts = [];
      allow_casts = true;
      constraints = [];
      default_order = None;
      ret_typ = None;
    }

  let counter = ref 0

  let fresh_kid env =
    let fresh = Kid_aux (Var ("'fv" ^ string_of_int !counter), Parse_ast.Unknown) in
    incr counter; fresh

  let freshen_kid env kid (typq, typ) =
    let fresh = fresh_kid env in
    (typquant_subst_kid kid fresh typq, typ_subst_kid kid fresh typ)

  let freshen_bind env bind =
    List.fold_left (fun bind (kid, _) -> freshen_kid env kid bind) bind (KBindings.bindings env.typ_vars)

  let get_val_spec id env =
    try
      let bind = Bindings.find id env.top_val_specs in
      typ_debug ("get_val_spec: Env has " ^ string_of_list ", " (fun (kid, bk) -> string_of_kid kid ^ " => " ^ string_of_base_kind_aux bk) (KBindings.bindings env.typ_vars));
      let bind' = List.fold_left (fun bind (kid, _) -> freshen_kid env kid bind) bind (KBindings.bindings env.typ_vars) in
      typ_debug ("get_val_spec: freshened to " ^ string_of_bind bind');
      bind'
    with
    | Not_found -> typ_error (id_loc id) ("No val spec found for " ^ string_of_id id)

  let add_val_spec id bind env =
    if Bindings.mem id env.top_val_specs
    then typ_error (id_loc id) ("Identifier " ^ string_of_id id ^ " is already bound")
    else
      begin
        typ_print ("Adding val spec binding " ^ string_of_id id ^ " :: " ^ string_of_bind bind);
        { env with top_val_specs = Bindings.add id bind env.top_val_specs }
      end

  let is_union_constructor id env =
    let is_ctor id (Tu_aux (tu, _)) = match tu with
      | Tu_id ctor_id when Id.compare id ctor_id = 0 -> true
      | Tu_ty_id (_, ctor_id) when Id.compare id ctor_id = 0 -> true
      | _ -> false
    in
    let type_unions = List.concat (List.map (fun (_, (_, tus)) -> tus) (Bindings.bindings env.variants)) in
    List.exists (is_ctor id) type_unions

  let get_typ_var kid env =
    try KBindings.find kid env.typ_vars with
    | Not_found -> typ_error (kid_loc kid) ("No kind identifier " ^ string_of_kid kid)

  let get_typ_vars env = env.typ_vars

  (* FIXME: Add an IdSet for builtin types *)
  let bound_typ_id env id =
    Bindings.mem id env.typ_synonyms
    || Bindings.mem id env.variants
    || Bindings.mem id env.records
    || Bindings.mem id env.regtyps
    || Bindings.mem id env.enums
    || Id.compare id (mk_id "range") = 0
    || Id.compare id (mk_id "vector") = 0
    || Id.compare id (mk_id "register") = 0
    || Id.compare id (mk_id "bit") = 0
    || Id.compare id (mk_id "unit") = 0
    || Id.compare id (mk_id "int") = 0
    || Id.compare id (mk_id "nat") = 0
    || Id.compare id (mk_id "bool") = 0
    || Id.compare id (mk_id "real") = 0
    || Id.compare id (mk_id "list") = 0
    || Id.compare id (mk_id "string") = 0

  (* Check if a type, order, or n-expression is well-formed. Throws a
     type error if the type is badly formed. FIXME: Add arity to type
     constructors, although arity checking for the builtin types does
     seem to be done by the initial ast check. *)
  let rec wf_typ ?exs:(exs=KidSet.empty) env (Typ_aux (typ_aux, l)) =
    match typ_aux with
    | Typ_wild -> ()
    | Typ_id id when bound_typ_id env id -> ()
    | Typ_id id -> typ_error l ("Undefined type " ^ string_of_id id)
    | Typ_var kid when KBindings.mem kid env.typ_vars -> ()
    | Typ_var kid -> typ_error l ("Unbound kind identifier " ^ string_of_kid kid)
    | Typ_fn (typ_arg, typ_ret, effs) -> wf_typ ~exs:exs env typ_arg; wf_typ ~exs:exs env typ_ret
    | Typ_tup typs -> List.iter (wf_typ ~exs:exs env) typs
    | Typ_app (id, args) when bound_typ_id env id -> List.iter (wf_typ_arg ~exs:exs env) args
    | Typ_app (id, _) -> typ_error l ("Undefined type " ^ string_of_id id)
    | Typ_exist ([], _, _) -> typ_error l ("Existential must have some type variables")
    | Typ_exist (kids, nc, typ) when KidSet.is_empty exs -> wf_typ ~exs:(KidSet.of_list kids) env typ
    | Typ_exist (_, _, _) -> typ_error l ("Nested existentials are not allowed")
  and wf_typ_arg ?exs:(exs=KidSet.empty) env (Typ_arg_aux (typ_arg_aux, _)) =
    match typ_arg_aux with
    | Typ_arg_nexp nexp -> wf_nexp ~exs:exs env nexp
    | Typ_arg_typ typ -> wf_typ ~exs:exs env typ
    | Typ_arg_order ord -> wf_order env ord
    | Typ_arg_effect _ -> () (* Check: is this ever used? *)
  and wf_nexp ?exs:(exs=KidSet.empty) env (Nexp_aux (nexp_aux, l)) =
    match nexp_aux with
    | Nexp_id _ -> ()
    | Nexp_var kid when KidSet.mem kid exs -> ()
    | Nexp_var kid ->
       begin
         match get_typ_var kid env with
         | BK_nat -> ()
         | kind -> typ_error l ("Constraint is badly formed, "
                                ^ string_of_kid kid ^ " has kind "
                                ^ string_of_base_kind_aux kind ^ " but should have kind Nat")
       end
    | Nexp_constant _ -> ()
    | Nexp_times (nexp1, nexp2) -> wf_nexp ~exs:exs env nexp1; wf_nexp ~exs:exs env nexp2
    | Nexp_sum (nexp1, nexp2) -> wf_nexp ~exs:exs env nexp1; wf_nexp ~exs:exs env nexp2
    | Nexp_minus (nexp1, nexp2) -> wf_nexp ~exs:exs env nexp1; wf_nexp ~exs:exs env nexp2
    | Nexp_exp nexp -> wf_nexp ~exs:exs env nexp (* MAYBE: Could put restrictions on what is allowed here *)
    | Nexp_neg nexp -> wf_nexp ~exs:exs env nexp
  and wf_order env (Ord_aux (ord_aux, l)) =
    match ord_aux with
    | Ord_var kid ->
       begin
         match get_typ_var kid env with
         | BK_order -> ()
         | kind -> typ_error l ("Order is badly formed, "
                                ^ string_of_kid kid ^ " has kind "
                                ^ string_of_base_kind_aux kind ^ " but should have kind Order")
       end
    | Ord_inc | Ord_dec -> ()

  let add_enum id ids env =
    if bound_typ_id env id
    then typ_error (id_loc id) ("Cannot create enum " ^ string_of_id id ^ ", type name is already bound")
    else
      begin
        typ_print ("Adding enum " ^ string_of_id id);
        { env with enums = Bindings.add id (IdSet.of_list ids) env.enums }
      end

  let get_enum id env =
    try IdSet.elements (Bindings.find id env.enums)
    with
    | Not_found -> typ_error (id_loc id) ("Enumeration " ^ string_of_id id ^ " does not exist")

  let is_record id env = Bindings.mem id env.records

  let add_record id typq fields env =
    if bound_typ_id env id
    then typ_error (id_loc id) ("Cannot create record " ^ string_of_id id ^ ", type name is already bound")
    else
      begin
        typ_print ("Adding record " ^ string_of_id id);
        let rec record_typ_args = function
          | [] -> []
          | ((QI_aux (QI_id kopt, _)) :: qis) when is_nat_kopt kopt ->
             mk_typ_arg (Typ_arg_nexp (nvar (kopt_kid kopt))) :: record_typ_args qis
          | ((QI_aux (QI_id kopt, _)) :: qis) when is_typ_kopt kopt ->
             mk_typ_arg (Typ_arg_typ (mk_typ (Typ_var (kopt_kid kopt)))) :: record_typ_args qis
          | ((QI_aux (QI_id kopt, _)) :: qis) when is_order_kopt kopt ->
             mk_typ_arg (Typ_arg_order (mk_ord (Ord_var (kopt_kid kopt)))) :: record_typ_args qis
          | (_ :: qis) -> record_typ_args qis
        in
        let rectyp = match record_typ_args (quant_items typq) with
          | [] -> mk_id_typ id
          | args -> mk_typ (Typ_app (id, args))
        in
        let fold_accessors accs (typ, fid) =
          let acc_typ = mk_typ (Typ_fn (rectyp, typ, Effect_aux (Effect_set [], Parse_ast.Unknown))) in
          typ_print (indent 1 ^ "Adding accessor " ^ string_of_id id ^ "." ^ string_of_id fid ^ " :: " ^ string_of_bind (typq, acc_typ));
          Bindings.add (field_name id fid) (typq, acc_typ) accs
        in
        { env with records = Bindings.add id (typq, fields) env.records;
                   accessors = List.fold_left fold_accessors env.accessors fields }
      end

  let get_accessor rec_id id env =
    let freshen_bind bind = List.fold_left (fun bind (kid, _) -> freshen_kid env kid bind) bind (KBindings.bindings env.typ_vars) in
    try freshen_bind (Bindings.find (field_name rec_id id) env.accessors)
    with
    | Not_found -> typ_error (id_loc id) ("No accessor found for " ^ string_of_id (field_name rec_id id))

  let is_mutable id env =
    try
      let (mut, _) = Bindings.find id env.locals in
      match mut with
      | Mutable -> true
      | Immutable -> false
    with
    | Not_found -> typ_error (id_loc id) ("No local binding found for " ^ string_of_id id)

  let string_of_mtyp (mut, typ) = match mut with
    | Immutable -> string_of_typ typ
    | Mutable -> "ref<" ^ string_of_typ typ ^ ">"

  let add_local id mtyp env =
    begin
      wf_typ env (snd mtyp);
      typ_print ("Adding local binding " ^ string_of_id id ^ " :: " ^ string_of_mtyp mtyp);
      { env with locals = Bindings.add id mtyp env.locals }
    end

  let add_variant id variant env =
    begin
      typ_print ("Adding variant " ^ string_of_id id);
      { env with variants = Bindings.add id variant env.variants }
    end

  let add_union_id id bind env =
    begin
      typ_print ("Adding union identifier binding " ^ string_of_id id ^ " :: " ^ string_of_bind bind);
      { env with union_ids = Bindings.add id bind env.union_ids }
    end

  let get_flow id env =
    try Bindings.find id env.flow with
    | Not_found -> fun typ -> typ

  let add_flow id f env =
    begin
      typ_print ("Adding flow constraints for " ^ string_of_id id);
      { env with flow = Bindings.add id (fun typ -> f (get_flow id env typ)) env.flow }
    end

  let is_register id env =
    Bindings.mem id env.registers

  let get_register id env =
    try Bindings.find id env.registers with
    | Not_found -> typ_error (id_loc id) ("No register binding found for " ^ string_of_id id)

  let get_overloads id env =
    try Bindings.find id env.overloads with
    | Not_found -> []

  let add_overloads id ids env =
    typ_print ("Adding overloads for " ^ string_of_id id ^ " [" ^ string_of_list ", " string_of_id ids ^ "]");
    { env with overloads = Bindings.add id ids env.overloads }

  let is_extern id env =
    Bindings.mem id env.externs

  let add_extern id ext env =
    { env with externs = Bindings.add id ext env.externs }

  let get_extern id env =
    try Bindings.find id env.externs with
    | Not_found -> typ_error (id_loc id) ("No extern binding found for " ^ string_of_id id)

  let get_casts env = env.casts

  let check_index_range cmp f t (BF_aux (ir, l)) =
    match ir with
    | BF_single n ->
       if cmp f n && cmp n t
       then n
       else typ_error l ("Badly ordered index range: " ^ string_of_list ", " string_of_int [f; n; t])
    | BF_range (n1, n2) ->
       if cmp f n1 && cmp n1 n2 && cmp n2 t
       then n2
       else typ_error l ("Badly ordered index range: " ^ string_of_list ", " string_of_int [f; n1; n2; t])
    | BF_concat _ -> typ_error l "Index range concatenation currently unsupported"

  let rec check_index_ranges ids cmp base top = function
    | [] -> ()
    | ((range, id) :: ranges) ->
       if IdSet.mem id ids
       then typ_error (id_loc id) ("Duplicate id " ^ string_of_id id ^ " in register typedef")
       else
         begin
           let base' = check_index_range cmp base top range in
           check_index_ranges (IdSet.add id ids) cmp base' top ranges
         end

  let add_register id typ env =
    if Bindings.mem id env.registers
    then typ_error (id_loc id) ("Register " ^ string_of_id id ^ " is already bound")
    else
      begin
        typ_print ("Adding register binding " ^ string_of_id id ^ " :: " ^ string_of_typ typ);
        { env with registers = Bindings.add id typ env.registers }
      end

  let add_regtyp id base top ranges env =
    if Bindings.mem id env.regtyps
    then typ_error (id_loc id) ("Register type " ^ string_of_id id ^ " is already bound")
    else
      begin
        typ_print ("Adding register type " ^ string_of_id id);
        if base > top
        then check_index_ranges IdSet.empty (fun x y -> x > y) (base + 1) (top - 1) ranges
        else check_index_ranges IdSet.empty (fun x y -> x < y) (base - 1) (top + 1) ranges;
        { env with regtyps = Bindings.add id (base, top, ranges) env.regtyps }
      end

  let is_regtyp id env = Bindings.mem id env.regtyps

  let get_regtyp id env =
    try Bindings.find id env.regtyps with
    | Not_found -> typ_error (id_loc id) (string_of_id id ^ " is not a register type")

  let lookup_id id env =
    try
      let (mut, typ) = Bindings.find id env.locals in
      let flow = get_flow id env in
      Local (mut, flow typ)
    with
    | Not_found ->
       begin
         try Register (Bindings.find id env.registers) with
         | Not_found ->
            begin
              try
                let (enum, _) = List.find (fun (enum, ctors) -> IdSet.mem id ctors) (Bindings.bindings env.enums) in
                Enum (mk_typ (Typ_id enum))
              with
              | Not_found ->
                 begin
                   try
                     let (typq, typ) = freshen_bind env (Bindings.find id env.union_ids) in
                     Union (typq, typ)
                   with
                   | Not_found -> Unbound
                 end
            end
       end

  let add_typ_var kid k env =
    if KBindings.mem kid env.typ_vars
    then typ_error (kid_loc kid) ("Kind identifier " ^ string_of_kid kid ^ " is already bound")
    else
      begin
        typ_debug ("Adding kind identifier binding " ^ string_of_kid kid ^ " :: " ^ string_of_base_kind_aux k);
        { env with typ_vars = KBindings.add kid k env.typ_vars }
      end

  let rec wf_constraint env (NC_aux (nc, _)) =
    match nc with
    | NC_fixed (n1, n2) -> wf_nexp env n1; wf_nexp env n2
    | NC_not_equal (n1, n2) -> wf_nexp env n1; wf_nexp env n2
    | NC_bounded_ge (n1, n2) -> wf_nexp env n1; wf_nexp env n2
    | NC_bounded_le (n1, n2) -> wf_nexp env n1; wf_nexp env n2
    | NC_nat_set_bounded (kid, ints) -> () (* MAYBE: We could demand that ints are all unique here *)
    | NC_or (nc1, nc2) -> wf_constraint env nc1; wf_constraint env nc2
    | NC_and (nc1, nc2) -> wf_constraint env nc1; wf_constraint env nc2
    | NC_true | NC_false -> ()

  let get_constraints env = env.constraints

  let add_constraint (NC_aux (_, l) as constr) env =
    wf_constraint env constr;
    begin
      typ_print ("Adding constraint " ^ string_of_n_constraint constr);
      { env with constraints = constr :: env.constraints }
    end

  let get_ret_typ env = env.ret_typ

  let add_ret_typ typ env = { env with ret_typ = Some typ }

  let allow_casts env = env.allow_casts

  let no_casts env = { env with allow_casts = false }
  let enable_casts env = { env with allow_casts = true }

  let add_cast cast env =
    typ_print ("Adding cast " ^ string_of_id cast);
    { env with casts = cast :: env.casts }

  let add_typ_synonym id synonym env =
    if Bindings.mem id env.typ_synonyms
    then typ_error (id_loc id) ("Type synonym " ^ string_of_id id ^ " already exists")
    else
      begin
        typ_print ("Adding type synonym " ^ string_of_id id);
        { env with typ_synonyms = Bindings.add id synonym env.typ_synonyms }
      end

  let get_typ_synonym id env = Bindings.find id env.typ_synonyms

  let rec expand_synonyms env (Typ_aux (typ, l) as t) =
    match typ with
    | Typ_tup typs -> Typ_aux (Typ_tup (List.map (expand_synonyms env) typs), l)
    | Typ_fn (typ1, typ2, effs) -> Typ_aux (Typ_fn (expand_synonyms env typ1, expand_synonyms env typ2, effs), l)
    | Typ_app (id, args) ->
       begin
         try
           let synonym = Bindings.find id env.typ_synonyms in
           expand_synonyms env (synonym env args)
         with
       | Not_found -> Typ_aux (Typ_app (id, List.map (expand_synonyms_arg env) args), l)
       end
    | Typ_id id ->
       begin
         try
           let synonym = Bindings.find id env.typ_synonyms in
           expand_synonyms env (synonym env [])
         with
         | Not_found -> Typ_aux (Typ_id id, l)
       end
    | typ -> Typ_aux (typ, l)
  and expand_synonyms_arg env (Typ_arg_aux (typ_arg, l)) =
    match typ_arg with
    | Typ_arg_typ typ -> Typ_arg_aux (Typ_arg_typ (expand_synonyms env typ), l)
    | arg -> Typ_arg_aux (arg, l)

  let get_default_order env =
    match env.default_order with
    | None -> typ_error Parse_ast.Unknown ("No default order has been set")
    | Some ord -> ord

  let set_default_order o env =
    match env.default_order with
    | None -> { env with default_order = Some (Ord_aux (o, Parse_ast.Unknown)) }
    | Some _ -> typ_error Parse_ast.Unknown ("Cannot change default order once already set")

  let set_default_order_inc = set_default_order Ord_inc
  let set_default_order_dec = set_default_order Ord_dec

  let base_typ_of env typ =
    let rec aux (Typ_aux (t,a)) =
      let rewrap t = Typ_aux (t,a) in
      match t with
      | Typ_fn (t1, t2, eff) ->
        rewrap (Typ_fn (aux t1, aux t2, eff))
      | Typ_tup ts ->
        rewrap (Typ_tup (List.map aux ts))
      | Typ_app (register, [Typ_arg_aux (Typ_arg_typ rtyp,_)])
        when string_of_id register = "register" ->
        aux rtyp
      | Typ_app (id, targs) ->
        rewrap (Typ_app (id, List.map aux_arg targs))
      | Typ_id id when is_regtyp id env ->
        let base, top, ranges = get_regtyp id env in
        let len = abs(top - base) + 1 in
        vector_typ (nconstant base) (nconstant len) (get_default_order env) bit_typ
        (* TODO registers with non-default order? non-bitvector registers? *)
      | t -> rewrap t
    and aux_arg (Typ_arg_aux (targ,a)) =
      let rewrap targ = Typ_arg_aux (targ,a) in
      match targ with
      | Typ_arg_typ typ -> rewrap (Typ_arg_typ (aux typ))
      | targ -> rewrap targ in
    aux (expand_synonyms env typ)

end


let add_typquant (quant : typquant) (env : Env.t) : Env.t =
  let rec add_quant_item env = function
    | QI_aux (qi, _) -> add_quant_item_aux env qi
  and add_quant_item_aux env = function
    | QI_const constr -> Env.add_constraint constr env
    | QI_id (KOpt_aux (KOpt_none kid, _)) -> Env.add_typ_var kid BK_nat env
    | QI_id (KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (k, _)], _), kid), _)) -> Env.add_typ_var kid k env
    | QI_id (KOpt_aux (_, l)) -> typ_error l "Type variable had non base kinds!"
  in
  match quant with
  | TypQ_aux (TypQ_no_forall, _) -> env
  | TypQ_aux (TypQ_tq quants, _) -> List.fold_left add_quant_item env quants

(* Create vectors with the default order from the environment *)

let dvector_typ env n m typ = vector_typ n m (Env.get_default_order env) typ

let lvector_typ env l typ =
  match Env.get_default_order env with
  | Ord_aux (Ord_inc, _) as ord ->
     vector_typ (nconstant 0) l ord typ
  | Ord_aux (Ord_dec, _) as ord ->
     vector_typ (nminus l (nconstant 1)) l ord typ

let initial_env =
  Env.empty
  |> Env.add_typ_synonym (mk_id "atom") (fun _ args -> mk_typ (Typ_app (mk_id "range", args @ args)))

let ex_counter = ref 0

let fresh_existential () =
  let fresh = Kid_aux (Var ("'ex" ^ string_of_int !ex_counter), Parse_ast.Unknown) in
  incr ex_counter; fresh

let destructure_exist env typ =
  match Env.expand_synonyms env typ with
  | Typ_aux (Typ_exist (kids, nc, typ), _) ->
     let fresh_kids = List.map (fun kid -> (kid, fresh_existential ())) kids in
     let nc = List.fold_left (fun nc (kid, fresh) -> nc_subst_nexp kid (Nexp_var fresh) nc) nc fresh_kids in
     let typ = List.fold_left (fun typ (kid, fresh) -> typ_subst_nexp kid (Nexp_var fresh) typ) typ fresh_kids in
     Some (List.map snd fresh_kids, nc, typ)
  | _ -> None

let is_exist = function
  | Typ_aux (Typ_exist (_, _, _), _) -> true
  | _ -> false

let exist_typ constr typ =
  let fresh_kid = fresh_existential () in
  mk_typ (Typ_exist ([fresh_kid], constr fresh_kid, typ fresh_kid))

let destruct_vector_typ env typ =
  let destruct_vector_typ' = function
    | Typ_aux (Typ_app (id, [Typ_arg_aux (Typ_arg_nexp n1, _);
                             Typ_arg_aux (Typ_arg_nexp n2, _);
                             Typ_arg_aux (Typ_arg_order o, _);
                             Typ_arg_aux (Typ_arg_typ vtyp, _)]
                       ), _) when string_of_id id = "vector" -> Some (n1, n2, o, vtyp)
    | typ -> None
  in
  destruct_vector_typ' (Env.expand_synonyms env typ)

(**************************************************************************)
(* 3. Subtyping and constraint solving                                    *)
(**************************************************************************)

let rec simp_typ (Typ_aux (typ_aux, l)) = Typ_aux (simp_typ_aux typ_aux, l)
and simp_typ_aux = function
  | Typ_exist (kids1, nc1, Typ_aux (Typ_exist (kids2, nc2, typ), _)) ->
     Typ_exist (kids1 @ kids2, nc_and nc1 nc2, typ)
  | typ_aux -> typ_aux

let order_eq (Ord_aux (ord_aux1, _)) (Ord_aux (ord_aux2, _)) =
  match ord_aux1, ord_aux2 with
  | Ord_inc, Ord_inc -> true
  | Ord_dec, Ord_dec -> true
  | Ord_var kid1, Ord_var kid2 -> Kid.compare kid1 kid2 = 0
  | _, _ -> false

let rec props_subst sv subst props =
  match props with
  | [] -> []
  | ((nexp1, nexp2) :: props) -> (nexp_subst sv subst nexp1, nexp_subst sv subst nexp2) :: props_subst sv subst props

type tnf =
  | Tnf_wild
  | Tnf_id of id
  | Tnf_var of kid
  | Tnf_tup of tnf list
  | Tnf_index_sort of index_sort
  | Tnf_app of id * tnf_arg list
and tnf_arg =
  | Tnf_arg_nexp of nexp
  | Tnf_arg_typ of tnf
  | Tnf_arg_order of order
  | Tnf_arg_effect of effect

let rec string_of_tnf = function
  | Tnf_wild -> "_"
  | Tnf_id id -> string_of_id id
  | Tnf_var kid -> string_of_kid kid
  | Tnf_tup tnfs -> "(" ^ string_of_list ", " string_of_tnf tnfs ^ ")"
  | Tnf_app (id, args) -> string_of_id id ^ "<" ^ string_of_list ", " string_of_tnf_arg args ^ ">"
  | Tnf_index_sort IS_int -> "INT"
  | Tnf_index_sort (IS_prop (kid, props)) ->
     "{" ^ string_of_kid kid ^ " | " ^ string_of_list " & " (fun (n1, n2) -> string_of_nexp n1 ^ " <= " ^ string_of_nexp n2) props ^ "}"
and string_of_tnf_arg = function
  | Tnf_arg_nexp n -> string_of_nexp n
  | Tnf_arg_typ tnf -> string_of_tnf tnf
  | Tnf_arg_order o -> string_of_order o
  | Tnf_arg_effect eff -> string_of_effect eff

let rec normalize_typ env (Typ_aux (typ, l)) =
  match typ with
  | Typ_wild -> Tnf_wild
  | Typ_id (Id_aux (Id "int", _)) -> Tnf_index_sort IS_int
  | Typ_id (Id_aux (Id "nat", _)) ->
     let kid = Env.fresh_kid env in Tnf_index_sort (IS_prop (kid, [(nconstant 0, nvar kid)]))
  | Typ_id v ->
     begin
       try normalize_typ env (Env.get_typ_synonym v env env []) with
       | Not_found -> Tnf_id v
     end
  | Typ_var kid -> Tnf_var kid
  | Typ_tup typs -> Tnf_tup (List.map (normalize_typ env) typs)
  | Typ_app (f, []) -> normalize_typ env (Typ_aux (Typ_id f, l))
  | Typ_app (Id_aux (Id "range", _), [Typ_arg_aux (Typ_arg_nexp n1, _); Typ_arg_aux (Typ_arg_nexp n2, _)]) ->
     let kid = Env.fresh_kid env in
     Tnf_index_sort (IS_prop (kid, [(n1, nvar kid); (nvar kid, n2)]))
  | Typ_app ((Id_aux (Id "vector", _) as vector), args) ->
     Tnf_app (vector, List.map (normalize_typ_arg env) args)
  | Typ_app (id, args) ->
     begin
       try normalize_typ env (Env.get_typ_synonym id env env args) with
       | Not_found -> Tnf_app (id, List.map (normalize_typ_arg env) args)
     end
  | Typ_exist (kids, nc, typ) -> typ_error l "Cannot normalise existential type"
  | Typ_fn _ -> typ_error l ("Cannot normalize function type " ^ string_of_typ (Typ_aux (typ, l)))
and normalize_typ_arg env (Typ_arg_aux (typ_arg, _)) =
  match typ_arg with
  | Typ_arg_nexp n -> Tnf_arg_nexp n
  | Typ_arg_typ typ -> Tnf_arg_typ (normalize_typ env typ)
  | Typ_arg_order o -> Tnf_arg_order o
  | Typ_arg_effect e -> Tnf_arg_effect e

(* Here's how the constraint generation works for subtyping

X(b,c...) --> {a. Y(a,b,c...)} \subseteq {a. Z(a,b,c...)}

this is equivalent to

\forall b c. X(b,c) --> \forall a. Y(a,b,c) --> Z(a,b,c)

\forall b c. X(b,c) --> \forall a. !Y(a,b,c) \/ !Z^-1(a,b,c)

\forall b c. X(b,c) --> !\exists a. Y(a,b,c) /\ Z^-1(a,b,c)

\forall b c. !X(b,c) \/ !\exists a. Y(a,b,c) /\ Z^-1(a,b,c)

!\exists b c. X(b,c) /\ \exists a. Y(a,b,c) /\ Z^-1(a,b,c)

!\exists a b c. X(b,c) /\ Y(a,b,c) /\ Z^-1(a,b,c)

which is then a problem we can feed to the constraint solver expecting unsat.
 *)

let rec nexp_constraint var_of (Nexp_aux (nexp, l)) =
  match nexp with
  | Nexp_id v -> typ_error l "Unimplemented: Cannot generate constraint from Nexp_id"
  | Nexp_var kid -> Constraint.variable (var_of kid)
  | Nexp_constant c -> Constraint.constant (big_int_of_int c)
  | Nexp_times (nexp1, nexp2) -> Constraint.mult (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
  | Nexp_sum (nexp1, nexp2) -> Constraint.add (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
  | Nexp_minus (nexp1, nexp2) -> Constraint.sub (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
  | Nexp_exp nexp -> Constraint.pow2 (nexp_constraint var_of nexp)
  | Nexp_neg nexp -> Constraint.sub (Constraint.constant (big_int_of_int 0)) (nexp_constraint var_of nexp)

let rec nc_constraint var_of (NC_aux (nc, l)) =
  match nc with
  | NC_fixed (nexp1, nexp2) -> Constraint.eq (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
  | NC_not_equal (nexp1, nexp2) -> Constraint.neq (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
  | NC_bounded_ge (nexp1, nexp2) -> Constraint.gteq (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
  | NC_bounded_le (nexp1, nexp2) -> Constraint.lteq (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
  | NC_nat_set_bounded (_, []) -> Constraint.literal false
  | NC_nat_set_bounded (kid, (int :: ints)) ->
     List.fold_left Constraint.disj
                    (Constraint.eq (nexp_constraint var_of (nvar kid)) (Constraint.constant (big_int_of_int int)))
                    (List.map (fun i -> Constraint.eq (nexp_constraint var_of (nvar kid)) (Constraint.constant (big_int_of_int i))) ints)
  | NC_or (nc1, nc2) -> Constraint.disj (nc_constraint var_of nc1) (nc_constraint var_of nc2)
  | NC_and (nc1, nc2) -> Constraint.conj (nc_constraint var_of nc1) (nc_constraint var_of nc2)
  | NC_false -> Constraint.literal false
  | NC_true -> Constraint.literal true

let rec nc_constraints var_of ncs =
  match ncs with
  | [] -> Constraint.literal true
  | [nc] -> nc_constraint var_of nc
  | (nc :: ncs) ->
     Constraint.conj (nc_constraint var_of nc) (nc_constraints var_of ncs)

let prove_z3 env nc =
  typ_print ("Prove " ^ string_of_list ", " string_of_n_constraint (Env.get_constraints env) ^ " |- " ^ string_of_n_constraint nc);
  let module Bindings = Map.Make(Kid) in
  let bindings = ref Bindings.empty  in
  let fresh_var kid =
    let n = Bindings.cardinal !bindings in
    bindings := Bindings.add kid n !bindings;
    n
  in
  let var_of kid =
    try Bindings.find kid !bindings with
    | Not_found -> fresh_var kid
  in
  let constr = Constraint.conj (nc_constraints var_of (Env.get_constraints env)) (Constraint.negate (nc_constraint var_of nc)) in
  match Constraint.call_z3 constr with
  | Constraint.Unsat _ -> typ_debug "unsat"; true
  | Constraint.Unknown [] -> typ_debug "sat"; false
  | Constraint.Unknown _ -> typ_debug "unknown"; false

let prove env (NC_aux (nc_aux, _) as nc) =
  let compare_const f (Nexp_aux (n1, _)) (Nexp_aux (n2, _)) =
    match n1, n2 with
    | Nexp_constant c1, Nexp_constant c2 when f c1 c2 -> true
    | _, _ -> false
  in
  match nc_aux with
  | NC_fixed (nexp1, nexp2) when compare_const (fun c1 c2 -> c1 = c2) (nexp_simp nexp1) (nexp_simp nexp2) -> true
  | NC_bounded_le (nexp1, nexp2) when compare_const (fun c1 c2 -> c1 <= c2) (nexp_simp nexp1) (nexp_simp nexp2) -> true
  | NC_bounded_ge (nexp1, nexp2) when compare_const (fun c1 c2 -> c1 >= c2) (nexp_simp nexp1) (nexp_simp nexp2) -> true
  | NC_fixed (nexp1, nexp2) when compare_const (fun c1 c2 -> c1 <> c2) (nexp_simp nexp1) (nexp_simp nexp2) -> false
  | NC_bounded_le (nexp1, nexp2) when compare_const (fun c1 c2 -> c1 > c2) (nexp_simp nexp1) (nexp_simp nexp2) -> false
  | NC_bounded_ge (nexp1, nexp2) when compare_const (fun c1 c2 -> c1 < c2) (nexp_simp nexp1) (nexp_simp nexp2) -> false
  | NC_true -> true
  | NC_false -> false
  | _ -> prove_z3 env nc

let rec subtyp_tnf env tnf1 tnf2 =
  typ_print ("Subset " ^ string_of_list ", " string_of_n_constraint (Env.get_constraints env) ^ " |- " ^ string_of_tnf tnf1 ^ " " ^ string_of_tnf tnf2);
  let module Bindings = Map.Make(Kid) in
  let bindings = ref Bindings.empty  in
  let fresh_var kid =
    let n = Bindings.cardinal !bindings in
    bindings := Bindings.add kid n !bindings;
    n
  in
  let var_of kid =
    try Bindings.find kid !bindings with
    | Not_found -> fresh_var kid
  in
  let rec neg_props props =
    match props with
    | [] -> Constraint.literal false
    | [(nexp1, nexp2)] -> Constraint.gt (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
    | ((nexp1, nexp2) :: props) ->
       Constraint.disj (Constraint.gt (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)) (neg_props props)
  in
  let rec pos_props props =
    match props with
    | [] -> Constraint.literal true
    | [(nexp1, nexp2)] -> Constraint.lteq (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)
    | ((nexp1, nexp2) :: props) ->
       Constraint.conj (Constraint.lteq (nexp_constraint var_of nexp1) (nexp_constraint var_of nexp2)) (pos_props props)
  in
  match (tnf1, tnf2) with
  | Tnf_wild, Tnf_wild -> true
  | Tnf_id v1, Tnf_id v2 -> Id.compare v1 v2 = 0
  | Tnf_var kid1, Tnf_var kid2 -> Kid.compare kid1 kid2 = 0
  | Tnf_tup tnfs1, Tnf_tup tnfs2 ->
     begin
       try List.for_all2 (subtyp_tnf env) tnfs1 tnfs2 with
       | Invalid_argument _ -> false
     end
  | Tnf_app (v1, args1), Tnf_app (v2, args2) -> Id.compare v1 v2 = 0 && List.for_all2 (tnf_args_eq env) args1 args2
  | Tnf_index_sort IS_int, Tnf_index_sort IS_int -> true
  | Tnf_index_sort (IS_prop _), Tnf_index_sort IS_int -> true
  | Tnf_index_sort (IS_prop (kid1, prop1)), Tnf_index_sort (IS_prop (kid2, prop2)) ->
     begin
       let kid3 = Env.fresh_kid env in
       let (prop1, prop2) = props_subst kid1 (Nexp_var kid3) prop1, props_subst kid2 (Nexp_var kid3) prop2 in
       let constr = Constraint.conj (nc_constraints var_of (Env.get_constraints env)) (Constraint.conj (pos_props prop1) (neg_props prop2)) in
       match Constraint.call_z3 constr with
       | Constraint.Unsat _ -> typ_debug "unsat"; true
       | Constraint.Unknown [] -> typ_debug "sat"; false
       | Constraint.Unknown _ -> typ_debug "unknown"; false
     end
  | _, _ -> false

and tnf_args_eq env arg1 arg2 =
  match arg1, arg2 with
  | Tnf_arg_nexp n1, Tnf_arg_nexp n2 -> prove env (NC_aux (NC_fixed (n1, n2), Parse_ast.Unknown))
  | Tnf_arg_order ord1, Tnf_arg_order ord2 -> order_eq ord1 ord2
  | Tnf_arg_typ tnf1, Tnf_arg_typ tnf2 -> subtyp_tnf env tnf1 tnf2 && subtyp_tnf env tnf2 tnf1
  | _, _ -> assert false

(**************************************************************************)
(* 4. Unification                                                         *)
(**************************************************************************)

let rec nexp_frees ?exs:(exs=KidSet.empty) (Nexp_aux (nexp, l)) =
  match nexp with
  | Nexp_id _ -> KidSet.empty
  | Nexp_var kid -> KidSet.singleton kid
  | Nexp_constant _ -> KidSet.empty
  | Nexp_times (n1, n2) -> KidSet.union (nexp_frees ~exs:exs n1) (nexp_frees ~exs:exs n2)
  | Nexp_sum (n1, n2) -> KidSet.union (nexp_frees ~exs:exs n1) (nexp_frees ~exs:exs n2)
  | Nexp_minus (n1, n2) -> KidSet.union (nexp_frees ~exs:exs n1) (nexp_frees ~exs:exs n2)
  | Nexp_exp n -> nexp_frees ~exs:exs n
  | Nexp_neg n -> nexp_frees ~exs:exs n

let order_frees (Ord_aux (ord_aux, l)) =
  match ord_aux with
  | Ord_var kid -> KidSet.singleton kid
  | _ -> KidSet.empty

let rec typ_frees ?exs:(exs=KidSet.empty) (Typ_aux (typ_aux, l)) =
  match typ_aux with
  | Typ_wild -> KidSet.empty
  | Typ_id v -> KidSet.empty
  | Typ_var kid when KidSet.mem kid exs -> KidSet.empty
  | Typ_var kid -> KidSet.singleton kid
  | Typ_tup typs -> List.fold_left KidSet.union KidSet.empty (List.map (typ_frees ~exs:exs) typs)
  | Typ_app (f, args) -> List.fold_left KidSet.union KidSet.empty (List.map (typ_arg_frees ~exs:exs) args)
  | Typ_exist (kids, nc, typ) -> typ_frees ~exs:(KidSet.of_list kids) typ
and typ_arg_frees ?exs:(exs=KidSet.empty) (Typ_arg_aux (typ_arg_aux, l)) =
  match typ_arg_aux with
  | Typ_arg_nexp n -> nexp_frees ~exs:exs n
  | Typ_arg_typ typ -> typ_frees ~exs:exs typ
  | Typ_arg_order ord -> order_frees ord
  | Typ_arg_effect _ -> assert false

let rec nexp_identical (Nexp_aux (nexp1, _)) (Nexp_aux (nexp2, _)) =
  match nexp1, nexp2 with
  | Nexp_id v1, Nexp_id v2 -> Id.compare v1 v2 = 0
  | Nexp_var kid1, Nexp_var kid2 -> Kid.compare kid1 kid2 = 0
  | Nexp_constant c1, Nexp_constant c2 -> c1 = c2
  | Nexp_times (n1a, n1b), Nexp_times (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | Nexp_sum (n1a, n1b), Nexp_sum (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | Nexp_minus (n1a, n1b), Nexp_minus (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | Nexp_exp n1, Nexp_exp n2 -> nexp_identical n1 n2
  | Nexp_neg n1, Nexp_neg n2 -> nexp_identical n1 n2
  | _, _ -> false

let ord_identical (Ord_aux (ord1, _)) (Ord_aux (ord2, _)) =
  match ord1, ord2 with
  | Ord_var kid1, Ord_var kid2 -> Kid.compare kid1 kid2 = 0
  | Ord_inc, Ord_inc -> true
  | Ord_dec, Ord_dec -> true
  | _, _ -> false

let rec typ_identical (Typ_aux (typ1, _)) (Typ_aux (typ2, _)) =
  match typ1, typ2 with
  | Typ_wild, Typ_wild -> true
  | Typ_id v1, Typ_id v2 -> Id.compare v1 v2 = 0
  | Typ_var kid1, Typ_var kid2 -> Kid.compare kid1 kid2 = 0
  | Typ_tup typs1, Typ_tup typs2 ->
     begin
       try List.for_all2 typ_identical typs1 typs2 with
       | Invalid_argument _ -> false
     end
  | Typ_app (f1, args1), Typ_app (f2, args2) ->
     begin
       try Id.compare f1 f2 = 0 && List.for_all2 typ_arg_identical args1 args2 with
       | Invalid_argument _ -> false
     end
  | _, _ -> false
and typ_arg_identical (Typ_arg_aux (arg1, _)) (Typ_arg_aux (arg2, _)) =
  match arg1, arg2 with
  | Typ_arg_nexp n1, Typ_arg_nexp n2 -> nexp_identical n1 n2
  | Typ_arg_typ typ1, Typ_arg_typ typ2 -> typ_identical typ1 typ2
  | Typ_arg_order ord1, Typ_arg_order ord2 -> ord_identical ord1 ord2
  | Typ_arg_effect _, Typ_arg_effect _ -> assert false

type uvar =
  | U_nexp of nexp
  | U_order of order
  | U_effect of effect
  | U_typ of typ

exception Unification_error of l * string;;

let unify_error l str = raise (Unification_error (l, str))

let rec unify_nexps l env goals (Nexp_aux (nexp_aux1, _) as nexp1) (Nexp_aux (nexp_aux2, _) as nexp2) =
  typ_debug ("UNIFYING NEXPS " ^ string_of_nexp nexp1 ^ " AND " ^ string_of_nexp nexp2 ^ " FOR GOALS " ^ string_of_list ", " string_of_kid (KidSet.elements goals));
  if KidSet.is_empty (KidSet.inter (nexp_frees nexp1) goals)
  then
    begin
      if prove env (NC_aux (NC_fixed (nexp1, nexp2), Parse_ast.Unknown))
      then None
      else unify_error l ("Nexp " ^ string_of_nexp nexp1 ^ " and " ^ string_of_nexp nexp2 ^ " are not equal")
    end
  else
    match nexp_aux1 with
    | Nexp_id v -> unify_error l "Unimplemented Nexp_id in unify nexp"
    | Nexp_var kid when KidSet.mem kid goals -> Some (kid, nexp2)
    | Nexp_constant c1 ->
       begin
         match nexp_aux2 with
         | Nexp_constant c2 -> if c1 = c2 then None else unify_error l "Constants are not the same"
         | _ -> unify_error l "Unification error"
       end
    | Nexp_sum (n1a, n1b) ->
       if KidSet.is_empty (nexp_frees n1b)
       then unify_nexps l env goals n1a (nminus nexp2 n1b)
       else
         if KidSet.is_empty (nexp_frees n1a)
         then unify_nexps l env goals n1b (nminus nexp2 n1a)
         else unify_error l ("Both sides of Nat expression " ^ string_of_nexp nexp1
                             ^ " contain free type variables so it cannot be unified with " ^ string_of_nexp nexp2)
    | Nexp_minus (n1a, n1b) ->
       if KidSet.is_empty (nexp_frees n1b)
       then unify_nexps l env goals n1a (nsum nexp2 n1b)
       else  unify_error l ("Cannot unify minus Nat expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
    | Nexp_times (n1a, n1b) ->
       if KidSet.is_empty (nexp_frees n1a)
       then
         begin
           match nexp_aux2 with
           | Nexp_times (n2a, n2b) when prove env (NC_aux (NC_fixed (n1a, n2a), Parse_ast.Unknown)) ->
              unify_nexps l env goals n1b n2b
           | Nexp_constant c2 ->
              begin
                match n1a with
                | Nexp_aux (Nexp_constant c1,_) when c2 mod c1 = 0 ->
                   unify_nexps l env goals n1b (mk_nexp (Nexp_constant (c2 / c1)))
                | _ -> unify_error l ("Cannot unify Nat expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
              end
           | _ -> unify_error l ("Cannot unify Nat expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
         end
       else if KidSet.is_empty (nexp_frees n1b)
       then
         begin
           match nexp_aux2 with
           | Nexp_times (n2a, n2b) when prove env (NC_aux (NC_fixed (n1b, n2b), Parse_ast.Unknown)) ->
              unify_nexps l env goals n1a n2a
           | _ -> unify_error l ("Cannot unify Nat expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
         end
       else unify_error l ("Cannot unify Nat expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
    | _ -> unify_error l ("Cannot unify Nat expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)

let string_of_uvar = function
  | U_nexp n -> string_of_nexp n
  | U_order o -> string_of_order o
  | U_effect eff -> string_of_effect eff
  | U_typ typ -> string_of_typ typ

let unify_order l (Ord_aux (ord_aux1, _) as ord1) (Ord_aux (ord_aux2, _) as ord2) =
  typ_debug ("UNIFYING ORDERS " ^ string_of_order ord1 ^ " AND " ^ string_of_order ord2);
  match ord_aux1, ord_aux2 with
  | Ord_var kid, _ -> KBindings.singleton kid (U_order ord2)
  | Ord_inc, Ord_inc -> KBindings.empty
  | Ord_dec, Ord_dec -> KBindings.empty
  | _, _ -> unify_error l (string_of_order ord1 ^ " cannot be unified with " ^ string_of_order ord2)

let subst_unifiers unifiers typ =
  let subst_unifier typ (kid, uvar) =
    match uvar with
    | U_nexp nexp -> typ_subst_nexp kid (unaux_nexp nexp) typ
    | U_order ord -> typ_subst_order kid (unaux_order ord) typ
    | U_typ subst -> typ_subst_typ kid (unaux_typ subst) typ
    | _ -> typ_error Parse_ast.Unknown "Cannot subst unifier"
  in
  List.fold_left subst_unifier typ (KBindings.bindings unifiers)

let subst_args_unifiers unifiers typ_args =
  let subst_unifier typ_args (kid, uvar) =
    match uvar with
    | U_nexp nexp -> List.map (typ_subst_arg_nexp kid (unaux_nexp nexp)) typ_args
    | U_order ord -> List.map (typ_subst_arg_order kid (unaux_order ord)) typ_args
    | U_typ subst -> List.map (typ_subst_arg_typ kid (unaux_typ subst)) typ_args
    | _ -> typ_error Parse_ast.Unknown "Cannot subst unifier"
  in
  List.fold_left subst_unifier typ_args (KBindings.bindings unifiers)

let merge_unifiers l kid uvar1 uvar2 =
  match uvar1, uvar2 with
  | Some (U_nexp n1), Some (U_nexp n2) ->
     if nexp_identical n1 n2 then Some (U_nexp n1)
     else unify_error l ("Multiple non-identical unifiers for " ^ string_of_kid kid
                         ^ ": " ^ string_of_nexp n1 ^ " and " ^ string_of_nexp n2)
  | Some _, Some _ -> unify_error l "Multiple non-identical non-nexp unifiers"
  | None, Some u2 -> Some u2
  | Some u1, None -> Some u1
  | None, None -> None

let rec unify l env typ1 typ2 =
  typ_print ("Unify " ^ string_of_typ typ1 ^ " with " ^ string_of_typ typ2);
  let goals = KidSet.inter (KidSet.diff (typ_frees typ1) (typ_frees typ2)) (typ_frees typ1) in
  let rec unify_typ l (Typ_aux (typ1_aux, _) as typ1) (Typ_aux (typ2_aux, _) as typ2) =
    typ_debug ("UNIFYING TYPES " ^ string_of_typ typ1 ^ " AND " ^ string_of_typ typ2);
    match typ1_aux, typ2_aux with
    | Typ_wild, Typ_wild -> KBindings.empty
    | Typ_id v1, Typ_id v2 ->
       if Id.compare v1 v2 = 0 then KBindings.empty
       else unify_error l (string_of_typ typ1 ^ " cannot be unified with " ^ string_of_typ typ2)
    | Typ_id v1, Typ_app (f2, []) ->
       if Id.compare v1 f2 = 0 then KBindings.empty
       else unify_error l (string_of_typ typ1 ^ " cannot be unified with " ^ string_of_typ typ2)
    | Typ_app (f1, []), Typ_id v2 ->
       if Id.compare f1 v2 = 0 then KBindings.empty
       else unify_error l (string_of_typ typ1 ^ " cannot be unified with " ^ string_of_typ typ2)
    | Typ_var kid, _ when KidSet.mem kid goals -> KBindings.singleton kid (U_typ typ2)
    | Typ_var kid1, Typ_var kid2 when Kid.compare kid1 kid2 = 0 -> KBindings.empty
    | Typ_tup typs1, Typ_tup typs2 ->
       begin
         try List.fold_left (KBindings.merge (merge_unifiers l)) KBindings.empty (List.map2 (unify_typ l) typs1 typs2) with
         | Invalid_argument _ -> unify_error l (string_of_typ typ1 ^ " cannot be unified with " ^ string_of_typ typ2
                                              ^ " tuple type is of different length")
       end
    | Typ_app (f1, args1), Typ_app (f2, args2) when Id.compare f1 f2 = 0 ->
       unify_typ_arg_list 0 KBindings.empty [] [] args1 args2
    | _, _ -> unify_error l (string_of_typ typ1 ^ " cannot be unified with " ^ string_of_typ typ2)

  and unify_typ_arg_list unified acc uargs1 uargs2 args1 args2 =
    match args1, args2 with
    | [], [] when unified = 0 && List.length uargs1 > 0 ->
       unify_error l "Could not unify arg lists" (*FIXME improve error *)
    | [], [] when unified > 0 && List.length uargs1 > 0 -> unify_typ_arg_list 0 acc [] [] uargs1 uargs2
    | [], [] when List.length uargs1 = 0 -> acc
    | (a1 :: a1s), (a2 :: a2s) ->
       begin
         let unifiers, success =
           try unify_typ_args l a1 a2, true with
           | Unification_error _ -> KBindings.empty, false
         in
         let a1s = subst_args_unifiers unifiers a1s in
         let a2s = subst_args_unifiers unifiers a2s in
         let uargs1 = subst_args_unifiers unifiers uargs1 in
         let uargs2 = subst_args_unifiers unifiers uargs2 in
         if success
         then unify_typ_arg_list (unified + 1) (KBindings.merge (merge_unifiers l) unifiers acc) uargs1 uargs2 a1s a2s
         else unify_typ_arg_list unified acc (a1 :: uargs1) (a2 :: uargs2) a1s a2s
       end
    | _, _ -> unify_error l "Cannot unify type lists of different length"

  and unify_typ_args l (Typ_arg_aux (typ_arg_aux1, _) as typ_arg1) (Typ_arg_aux (typ_arg_aux2, _) as typ_arg2) =
    match typ_arg_aux1, typ_arg_aux2 with
    | Typ_arg_nexp n1, Typ_arg_nexp n2 ->
       begin
         match unify_nexps l env goals (nexp_simp n1) (nexp_simp n2) with
         | Some (kid, unifier) -> KBindings.singleton kid (U_nexp unifier)
         | None -> KBindings.empty
       end
    | Typ_arg_typ typ1, Typ_arg_typ typ2 -> unify_typ l typ1 typ2
    | Typ_arg_order ord1, Typ_arg_order ord2 -> unify_order l ord1 ord2
    | Typ_arg_effect _, Typ_arg_effect _ -> assert false
    | _, _ -> unify_error l (string_of_typ_arg typ_arg1 ^ " cannot be unified with type argument " ^ string_of_typ_arg typ_arg2)
  in
  match destructure_exist env typ2 with
  | Some (kids, nc, typ2) ->
     let typ1, typ2 = Env.expand_synonyms env typ1, Env.expand_synonyms env typ2 in
     let (unifiers, _, _) = unify l env typ1 typ2 in
     typ_debug (string_of_list ", " (fun (kid, uvar) -> string_of_kid kid ^ " => " ^ string_of_uvar uvar) (KBindings.bindings unifiers));
     unifiers, kids, Some nc
  | None ->
   let typ1, typ2 = Env.expand_synonyms env typ1, Env.expand_synonyms env typ2 in
   unify_typ l typ1 typ2, [], None

let merge_uvars l unifiers1 unifiers2 =
  try KBindings.merge (merge_unifiers l) unifiers1 unifiers2
  with
  | Unification_error (_, m) -> typ_error l ("Could not merge unification variables: " ^ m)

(**************************************************************************)
(* 4.5. Subtyping with existentials                                       *)
(**************************************************************************)

let nc_subst_uvar kid uvar nc =
  match uvar with
  | U_nexp nexp -> nc_subst_nexp kid (unaux_nexp nexp) nc
  | _ -> nc

let uv_nexp_constraint env (kid, uvar) =
  match uvar with
  | U_nexp nexp -> Env.add_constraint (nc_eq (nvar kid) nexp) env
  | _ -> env

let rec subtyp l env typ1 typ2 =
  match destructure_exist env typ1, destructure_exist env typ2 with
  | Some (kids, nc, typ1), _ ->
     let env = List.fold_left (fun env kid -> Env.add_typ_var kid BK_nat env) env kids in
     let env = Env.add_constraint nc env in
     subtyp l env typ1 typ2
  | _, Some (kids, nc, typ2) ->
     let env = List.fold_left (fun env kid -> Env.add_typ_var kid BK_nat env) env kids in
     let unifiers, existential_kids, existential_nc =
       try unify l env typ2 typ1 with
       | Unification_error (_, m) -> typ_error l m
     in
     let nc = List.fold_left (fun nc (kid, uvar) -> nc_subst_uvar kid uvar nc) nc (KBindings.bindings unifiers) in
     let env = match existential_kids, existential_nc with
       | [], None -> env
       | _, Some enc ->
          let env = List.fold_left (fun env kid -> Env.add_typ_var kid BK_nat env) env existential_kids in
          let env = List.fold_left uv_nexp_constraint env (KBindings.bindings unifiers) in
          Env.add_constraint enc env
     in
     if prove env nc then ()
     else typ_error l ("Could not show " ^ string_of_typ typ1 ^ " is a subset of existential " ^ string_of_typ typ2)
  | _, None ->
     if subtyp_tnf env (normalize_typ env typ1) (normalize_typ env typ2)
     then ()
     else typ_error l (string_of_typ typ1
                       ^ " is not a subtype of " ^ string_of_typ typ2
                       ^ " in context " ^ string_of_list ", " string_of_n_constraint (Env.get_constraints env))

let typ_equality l env typ1 typ2 =
  subtyp l env typ1 typ2; subtyp l env typ2 typ1

let subtype_check env typ1 typ2 =
  try subtyp Parse_ast.Unknown env typ1 typ2; true with
  | Type_error _ -> false

(**************************************************************************)
(* 5. Type checking expressions                                           *)
(**************************************************************************)

(* The type checker produces a fully annoted AST - tannot is the type
   of these type annotations. *)
type tannot = (Env.t * typ * effect) option

let infer_lit env (L_aux (lit_aux, l) as lit) =
  match lit_aux with
  | L_unit -> unit_typ
  | L_zero -> bit_typ
  | L_one -> bit_typ
  | L_num n -> atom_typ (nconstant n)
  | L_true -> bool_typ
  | L_false -> bool_typ
  | L_string _ -> string_typ
  | L_real _ -> real_typ
  | L_bin str ->
     begin
       match Env.get_default_order env with
       | Ord_aux (Ord_inc, _) ->
          dvector_typ env (nconstant 0) (nconstant (String.length str)) (mk_typ (Typ_id (mk_id "bit")))
       | Ord_aux (Ord_dec, _) ->
          dvector_typ env
                     (nconstant (String.length str - 1))
                     (nconstant (String.length str))
                     (mk_typ (Typ_id (mk_id "bit")))
     end
  | L_hex str ->
     begin
       match Env.get_default_order env with
       | Ord_aux (Ord_inc, _) ->
          dvector_typ env (nconstant 0) (nconstant (String.length str * 4)) (mk_typ (Typ_id (mk_id "bit")))
       | Ord_aux (Ord_dec, _) ->
          dvector_typ env
                     (nconstant (String.length str * 4 - 1))
                     (nconstant (String.length str * 4))
                     (mk_typ (Typ_id (mk_id "bit")))
     end
  | L_undef -> typ_error l "Cannot infer the type of undefined"

let is_nat_kid kid = function
  | KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (BK_nat, _)], _), kid'), _) -> Kid.compare kid kid' = 0
  | KOpt_aux (KOpt_none kid', _) -> Kid.compare kid kid' = 0
  | _ -> false

let is_order_kid kid = function
  | KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (BK_order, _)], _), kid'), _) -> Kid.compare kid kid' = 0
  | _ -> false

let is_typ_kid kid = function
  | KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (BK_type, _)], _), kid'), _) -> Kid.compare kid kid' = 0
  | _ -> false

let rec instantiate_quants quants kid uvar = match quants with
  | [] -> []
  | ((QI_aux (QI_id kinded_id, _) as quant) :: quants) ->
     typ_debug ("instantiating quant " ^ string_of_quant_item quant);
     begin
       match uvar with
       | U_nexp nexp ->
          if is_nat_kid kid kinded_id
          then instantiate_quants quants kid uvar
          else quant :: instantiate_quants quants kid uvar
       | U_order ord ->
          if is_order_kid kid kinded_id
          then instantiate_quants quants kid uvar
          else quant :: instantiate_quants quants kid uvar
       | U_typ typ ->
          if is_typ_kid kid kinded_id
          then instantiate_quants quants kid uvar
          else quant :: instantiate_quants quants kid uvar
       | _ -> typ_error Parse_ast.Unknown "Cannot instantiate quantifier"
     end
  | ((QI_aux (QI_const nc, l)) :: quants) ->
     begin
       match uvar with
       | U_nexp nexp ->
          QI_aux (QI_const (nc_subst_nexp kid (unaux_nexp nexp) nc), l) :: instantiate_quants quants kid uvar
       | _ -> (QI_aux (QI_const nc, l)) :: instantiate_quants quants kid uvar
     end

let destructure_vec_typ l env typ =
  let destructure_vec_typ' l = function
    | Typ_aux (Typ_app (id, [Typ_arg_aux (Typ_arg_nexp n1, _);
                             Typ_arg_aux (Typ_arg_nexp n2, _);
                             Typ_arg_aux (Typ_arg_order o, _);
                             Typ_arg_aux (Typ_arg_typ vtyp, _)]
                       ), _) when string_of_id id = "vector" -> (n1, n2, o, vtyp)
    | typ -> typ_error l ("Expected vector type, got " ^ string_of_typ typ)
  in
  destructure_vec_typ' l (Env.expand_synonyms env typ)


let env_of_annot (l, tannot) = match tannot with
  | Some (env, _, _) -> env
  | None -> raise (Reporting_basic.err_unreachable l "no type annotation")

let env_of (E_aux (_, (l, tannot))) = env_of_annot (l, tannot)

let typ_of_annot (l, tannot) = match tannot with
  | Some (_, typ, _) -> typ
  | None -> raise (Reporting_basic.err_unreachable l "no type annotation")

let env_of_annot (l, tannot) = match tannot with
  | Some (env, _, _) -> env
  | None -> raise (Reporting_basic.err_unreachable l "no type annotation")

let typ_of (E_aux (_, (l, tannot))) = typ_of_annot (l, tannot)

let env_of (E_aux (_, (l, tannot))) = env_of_annot (l, tannot)

let pat_typ_of (P_aux (_, (l, tannot))) = typ_of_annot (l, tannot)

(* Flow typing *)

let destructure_atom (Typ_aux (typ_aux, _)) =
  match typ_aux with
  | Typ_app (f, [Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_constant c, _)), _)])
       when string_of_id f = "atom" -> c
  | Typ_app (f, [Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_constant c1, _)), _); Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_constant c2, _)), _)])
       when string_of_id f = "range" && c1 = c2 -> c1
  | _ -> assert false

let destructure_atom_nexp (Typ_aux (typ_aux, _)) =
  match typ_aux with
  | Typ_app (f, [Typ_arg_aux (Typ_arg_nexp n, _)])
       when string_of_id f = "atom" -> n
  | Typ_app (f, [Typ_arg_aux (Typ_arg_nexp n, _); Typ_arg_aux (Typ_arg_nexp _, _)])
       when string_of_id f = "range" -> n
  | _ -> assert false

let restrict_range_upper c1 (Typ_aux (typ_aux, l) as typ) =
  match typ_aux with
  | Typ_app (f, [Typ_arg_aux (Typ_arg_nexp nexp, _); Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_constant c2, _)), _)])
     when string_of_id f = "range" ->
     range_typ nexp (nconstant (min c1 c2))
  | _ -> typ

let restrict_range_lower c1 (Typ_aux (typ_aux, l) as typ) =
  match typ_aux with
  | Typ_app (f, [Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_constant c2, _)), _); Typ_arg_aux (Typ_arg_nexp nexp, _)])
     when string_of_id f = "range" ->
     range_typ (nconstant (max c1 c2)) nexp
  | _ -> typ

exception Not_a_constraint;;

let rec assert_nexp (E_aux (exp_aux, l)) =
  match exp_aux with
  | E_sizeof nexp -> nexp
  | E_lit (L_aux (L_num n, _)) -> nconstant n
  | _ -> raise Not_a_constraint

let rec assert_constraint (E_aux (exp_aux, l)) =
  match exp_aux with
  | E_app_infix (x, op, y) when string_of_id op = "|" ->
     nc_or (assert_constraint x) (assert_constraint y)
  | E_app_infix (x, op, y) when string_of_id op = "&" ->
     nc_and (assert_constraint x) (assert_constraint y)
  | E_app_infix (x, op, y) when string_of_id op = "==" ->
     nc_eq (assert_nexp x) (assert_nexp y)
  | E_app_infix (x, op, y) when string_of_id op = ">=" ->
     nc_gteq (assert_nexp x) (assert_nexp y)
  | _ -> nc_true

type flow_constraint =
  | Flow_lteq of int
  | Flow_gteq of int

let apply_flow_constraint = function
  | Flow_lteq c -> (restrict_range_upper c, restrict_range_lower (c + 1))
  | Flow_gteq c -> (restrict_range_lower c, restrict_range_upper (c - 1))

let rec infer_flow env (E_aux (exp_aux, (l, _))) =
  match exp_aux with
  | E_app (f, [x; y]) when string_of_id f = "lteq_atom_atom" ->
     let n1 = destructure_atom_nexp (typ_of x) in
     let n2 = destructure_atom_nexp (typ_of y) in
     [], [nc_lteq n1 n2]
  | E_app (f, [x; y]) when string_of_id f = "gteq_atom_atom" ->
     let n1 = destructure_atom_nexp (typ_of x) in
     let n2 = destructure_atom_nexp (typ_of y) in
     [], [nc_gteq n1 n2]
  | E_app (f, [x; y]) when string_of_id f = "lt_atom_atom" ->
     let n1 = destructure_atom_nexp (typ_of x) in
     let n2 = destructure_atom_nexp (typ_of y) in
     [], [nc_lt n1 n2]
  | E_app (f, [x; y]) when string_of_id f = "gt_atom_atom" ->
     let n1 = destructure_atom_nexp (typ_of x) in
     let n2 = destructure_atom_nexp (typ_of y) in
     [], [nc_gt n1 n2]
  | E_app (f, [E_aux (E_id v, _); y]) when string_of_id f = "lt_range_atom" ->
     let kid = Env.fresh_kid env in
     let c = destructure_atom (typ_of y) in
     [(v, Flow_lteq (c - 1))], []
  | E_app (f, [E_aux (E_id v, _); y]) when string_of_id f = "lteq_range_atom" ->
     let kid = Env.fresh_kid env in
     let c = destructure_atom (typ_of y) in
     [(v, Flow_lteq c)], []
  | E_app (f, [E_aux (E_id v, _); y]) when string_of_id f = "gt_range_atom" ->
     let kid = Env.fresh_kid env in
     let c = destructure_atom (typ_of y) in
     [(v, Flow_gteq (c + 1))], []
  | E_app (f, [E_aux (E_id v, _); y]) when string_of_id f = "gteq_range_atom" ->
     let kid = Env.fresh_kid env in
     let c = destructure_atom (typ_of y) in
     [(v, Flow_gteq c)], []
  | _ -> [], []

let rec add_flows b flows env =
  match flows with
  | [] -> env
  | (id, flow) :: flows when b -> add_flows true flows (Env.add_flow id (fst (apply_flow_constraint flow)) env)
  | (id, flow) :: flows -> add_flows false flows (Env.add_flow id (snd (apply_flow_constraint flow)) env)

let rec add_constraints constrs env =
  List.fold_left (fun env constr -> Env.add_constraint constr env) env constrs

(* When doing implicit type coercion, for performance reasons we want
   to filter out the possible casts to only those that could
   reasonably apply. We don't mind if we try some coercions that are
   impossible, but we should be careful to never rule out a possible
   cast - match_typ and filter_casts implement this logic. It must be
   the case that if two types unify, then they match. *)
let rec match_typ env typ1 typ2 =
  let Typ_aux (typ1_aux, _) = Env.expand_synonyms env typ1 in
  let Typ_aux (typ2_aux, _) = Env.expand_synonyms env typ2 in
  match typ1_aux, typ2_aux with
  | Typ_exist (_, _, typ1), _ -> match_typ env typ1 typ2
  | _, Typ_exist (_, _, typ2) -> match_typ env typ1 typ2
  | Typ_wild, Typ_wild -> true
  | _, Typ_var kid2 -> true
  | Typ_id v1, Typ_id v2 when Id.compare v1 v2 = 0 -> true
  | Typ_id v1, Typ_id v2 when string_of_id v1 = "int" && string_of_id v2 = "nat" -> true
  | Typ_tup typs1, Typ_tup typs2 -> List.for_all2 (match_typ env) typs1 typs2
  | Typ_id v, Typ_app (f, _) when string_of_id v = "nat" && string_of_id f = "atom" -> true
  | Typ_id v, Typ_app (f, _) when string_of_id v = "int" &&  string_of_id f = "atom" -> true
  | Typ_id v, Typ_app (f, _) when string_of_id v = "nat" &&  string_of_id f = "range" -> true
  | Typ_id v, Typ_app (f, _) when string_of_id v = "int" &&  string_of_id f = "range" -> true
  | Typ_app (f1, _), Typ_app (f2, _) when string_of_id f1 = "range" && string_of_id f2 = "atom" -> true
  | Typ_app (f1, _), Typ_app (f2, _) when string_of_id f1 = "atom" && string_of_id f2 = "range" -> true
  | Typ_app (f1, _), Typ_app (f2, _) when Id.compare f1 f2 = 0 -> true
  | Typ_id v1, Typ_app (f2, _) when Id.compare v1 f2 = 0 -> true
  | Typ_app (f1, _), Typ_id v2 when Id.compare f1 v2 = 0 -> true
  | _, _ -> false

let rec filter_casts env from_typ to_typ casts =
  match casts with
  | (cast :: casts) ->
     begin
       let (quant, cast_typ) = Env.get_val_spec cast env in
       match cast_typ with
       | Typ_aux (Typ_fn (cast_from_typ, cast_to_typ, _), _)
            when match_typ env from_typ cast_from_typ && match_typ env to_typ cast_to_typ ->
          typ_print ("Considering cast " ^ string_of_typ cast_typ ^ " for " ^ string_of_typ from_typ ^ " to " ^ string_of_typ to_typ);
          cast :: filter_casts env from_typ to_typ casts
       | _ -> filter_casts env from_typ to_typ casts
     end
  | [] -> []

let is_union_id id env =
  match Env.lookup_id id env with
  | Union (_, _) -> true
  | _ -> false

let crule r env exp typ =
  incr depth;
  typ_print ("Check " ^ string_of_exp exp ^ " <= " ^ string_of_typ typ);
  try
    let checked_exp = r env exp typ in
    decr depth; checked_exp
  with
  | Type_error (l, m) -> decr depth; typ_error l m

let irule r env exp =
  incr depth;
  try
    let inferred_exp = r env exp in
    typ_print ("Infer " ^ string_of_exp exp ^ " => " ^ string_of_typ (typ_of inferred_exp));
    decr depth;
    inferred_exp
  with
  | Type_error (l, m) -> decr depth; typ_error l m

let strip_exp : 'a exp -> unit exp = function exp -> map_exp_annot (fun (l, _) -> (l, ())) exp
let strip_pat : 'a pat -> unit pat = function pat -> map_pat_annot (fun (l, _) -> (l, ())) pat

let rec check_exp env (E_aux (exp_aux, (l, ())) as exp : unit exp) (Typ_aux (typ_aux, _) as typ) : tannot exp =
  let annot_exp_effect exp typ eff = E_aux (exp, (l, Some (env, typ, eff))) in
  let annot_exp exp typ = annot_exp_effect exp typ no_effect in
  match (exp_aux, typ_aux) with
  | E_block exps, _ ->
     begin
       let rec check_block l env exps typ = match exps with
         | [] -> typ_equality l env typ unit_typ; []
         | [exp] -> [crule check_exp env exp typ]
         | (E_aux (E_assign (lexp, bind), _) :: exps) ->
            let texp, env = bind_assignment env lexp bind in
            texp :: check_block l env exps typ
         | ((E_aux (E_assert (E_aux (E_constraint nc, _), assert_msg), _) as exp) :: exps) ->
            typ_print ("Adding constraint " ^ string_of_n_constraint nc ^ " for assert");
            let inferred_exp = irule infer_exp env exp in
            inferred_exp :: check_block l (Env.add_constraint nc env) exps typ
         | ((E_aux (E_assert (const_expr, assert_msg), _) as exp) :: exps) ->
            begin
              try
                let nc = assert_constraint const_expr in
                check_block l (Env.add_constraint nc env) exps typ
              with
              | Not_a_constraint -> check_block l env exps typ
            end
         | (exp :: exps) ->
            let texp = crule check_exp env exp (mk_typ (Typ_id (mk_id "unit"))) in
            texp :: check_block l env exps typ
       in
       annot_exp (E_block (check_block l env exps typ)) typ
     end
  | E_case (exp, cases), _ ->
     let inferred_exp = irule infer_exp env exp in
     let check_case pat typ = match pat with
       | Pat_aux (Pat_exp (pat, case), (l, _)) ->
          let tpat, env = bind_pat env pat (typ_of inferred_exp) in
          Pat_aux (Pat_exp (tpat, crule check_exp env case typ), (l, None))
       | Pat_aux (Pat_when (pat, guard, case), (l, _)) ->
          let tpat, env = bind_pat env pat (typ_of inferred_exp) in
          let checked_guard = check_exp env guard bool_typ in
          Pat_aux (Pat_when (tpat, checked_guard, crule check_exp env case typ), (l, None))
     in
     annot_exp (E_case (inferred_exp, List.map (fun case -> check_case case typ) cases)) typ
  | E_try (exp, cases), _ ->
     let checked_exp = crule check_exp env exp typ in
     let check_case pat typ = match pat with
       | Pat_aux (Pat_exp (pat, case), (l, _)) ->
          let tpat, env = bind_pat env pat exc_typ in
          Pat_aux (Pat_exp (tpat, crule check_exp env case typ), (l, None))
       | Pat_aux (Pat_when (pat, guard, case), (l, _)) ->
          let tpat, env = bind_pat env pat exc_typ in
          let checked_guard = check_exp env guard bool_typ in
          Pat_aux (Pat_when (tpat, checked_guard, crule check_exp env case typ), (l, None))
     in
     annot_exp (E_try (checked_exp, List.map (fun case -> check_case case typ) cases)) typ
  | E_cons (x, xs), _ ->
     begin
       match is_list (Env.expand_synonyms env typ) with
       | Some elem_typ ->
          let checked_xs = crule check_exp env xs typ in
          let checked_x = crule check_exp env x elem_typ in
          annot_exp (E_cons (checked_x, checked_xs)) typ
       | None -> typ_error l ("Cons " ^ string_of_exp exp ^ " must have list type, got " ^ string_of_typ typ)
     end
  | E_list xs, _ ->
     begin
       match is_list (Env.expand_synonyms env typ) with
       | Some elem_typ ->
          let checked_xs = List.map (fun x -> crule check_exp env x elem_typ) xs in
          annot_exp (E_list checked_xs) typ
       | None -> typ_error l ("List " ^ string_of_exp exp ^ " must have list type, got " ^ string_of_typ typ)
     end
  | E_let (LB_aux (letbind, (let_loc, _)), exp), _ ->
     begin
       match letbind with
       | LB_val_explicit (typschm, pat, bind) -> assert false
       | LB_val_implicit (P_aux (P_typ (ptyp, _), _) as pat, bind) ->
          let checked_bind = crule check_exp env bind ptyp in
          let tpat, env = bind_pat env pat ptyp in
          annot_exp (E_let (LB_aux (LB_val_implicit (tpat, checked_bind), (let_loc, None)), crule check_exp env exp typ)) typ
       | LB_val_implicit (pat, bind) ->
          let inferred_bind = irule infer_exp env bind in
          let tpat, env = bind_pat env pat (typ_of inferred_bind) in
          annot_exp (E_let (LB_aux (LB_val_implicit (tpat, inferred_bind), (let_loc, None)), crule check_exp env exp typ)) typ
     end
  | E_app_infix (x, op, y), _ when List.length (Env.get_overloads (deinfix op) env) > 0 ->
     check_exp env (E_aux (E_app (deinfix op, [x; y]), (l, ()))) typ
  | E_app (f, [E_aux (E_constraint nc, _)]), _ when Id.compare f (mk_id "_prove") = 0 ->
     if prove env nc
     then annot_exp (E_lit (L_aux (L_unit, Parse_ast.Unknown))) unit_typ
     else typ_error l ("Cannot prove " ^ string_of_n_constraint nc)
  | E_app (f, xs), _ when List.length (Env.get_overloads f env) > 0 ->
     let rec try_overload = function
       | [] -> typ_error l ("No valid overloading for " ^ string_of_exp exp)
       | (f :: fs) -> begin
           typ_print ("Overload: " ^ string_of_id f ^ "(" ^ string_of_list ", " string_of_exp xs ^ ")");
           try crule check_exp env (E_aux (E_app (f, xs), (l, ()))) typ with
           | Type_error (_, m) -> typ_print ("Error : " ^ m); try_overload fs
         end
     in
     try_overload (Env.get_overloads f env)
  | E_return exp, _ ->
     let checked_exp = match Env.get_ret_typ env with
       | Some ret_typ -> crule check_exp env exp ret_typ
       | None -> typ_error l "Cannot use return outside a function"
     in
     annot_exp (E_return checked_exp) typ
  | E_app (f, xs), _ ->
     let inferred_exp = infer_funapp l env f xs (Some typ) in
     type_coercion env inferred_exp typ
  | E_if (cond, then_branch, else_branch), _ ->
     let cond' = crule check_exp env cond (mk_typ (Typ_id (mk_id "bool"))) in
     let flows, constrs = infer_flow env cond' in
     let then_branch' = crule check_exp (add_constraints constrs (add_flows true flows env)) then_branch typ in
     let else_branch' = crule check_exp (add_constraints (List.map nc_negate constrs) (add_flows false flows env)) else_branch typ in
     annot_exp (E_if (cond', then_branch', else_branch')) typ
  | E_exit exp, _ ->
     let checked_exp = crule check_exp env exp (mk_typ (Typ_id (mk_id "unit"))) in
     annot_exp_effect (E_exit checked_exp) typ (mk_effect [BE_escape])
  | E_throw exp, _ ->
     let checked_exp = crule check_exp env exp exc_typ in
     annot_exp_effect (E_throw checked_exp) typ (mk_effect [BE_escape])
  | E_vector vec, _ ->
     begin
       let (start, len, ord, vtyp) = destructure_vec_typ l env typ in
       let checked_items = List.map (fun i -> crule check_exp env i vtyp) vec in
       match nexp_simp len with
       | Nexp_aux (Nexp_constant lenc, _) ->
          if List.length vec = lenc then annot_exp (E_vector checked_items) typ
          else typ_error l "List length didn't match" (* FIXME: improve error message *)
       | _ -> typ_error l "Cannot check list constant against non-constant length vector type"
     end
  | E_lit (L_aux (L_undef, _) as lit), _ ->
     annot_exp_effect (E_lit lit) typ (mk_effect [BE_undef])
  (* This rule allows registers of type t to be passed by name with type register<t>*)
  | E_id reg, Typ_app (id, [Typ_arg_aux (Typ_arg_typ typ, _)])
    when string_of_id id = "register" && Env.is_register reg env ->
     let rtyp = Env.get_register reg env in
     subtyp l env rtyp typ; annot_exp (E_id reg) typ (* CHECK: is this subtyp the correct way around? *)
  | E_id id, _ when is_union_id id env ->
     begin
       match Env.lookup_id id env with
       | Union (typq, ctor_typ) ->
          let inferred_exp = fst (infer_funapp' l env id (typq, mk_typ (Typ_fn (unit_typ, ctor_typ, no_effect))) [mk_lit L_unit] (Some typ)) in
          annot_exp (E_id id) (typ_of inferred_exp)
       | _ -> assert false (* Unreachble due to guard *)
     end
  | _, _ ->
     let inferred_exp = irule infer_exp env exp in
     type_coercion env inferred_exp typ

(* type_coercion env exp typ takes a fully annoted (i.e. already type
   checked) expression exp, and attempts to cast (coerce) it to the
   type typ by inserting a coercion function that transforms the
   annotated expression into the correct type. Returns an annoted
   expression consisting of a type coercion function applied to exp,
   or throws a type error if the coercion cannot be performed. *)
and type_coercion env (E_aux (_, (l, _)) as annotated_exp) typ =
  let strip exp_aux = strip_exp (E_aux (exp_aux, (Parse_ast.Unknown, None))) in
  let annot_exp exp typ = E_aux (exp, (l, Some (env, typ, no_effect))) in
  let rec try_casts m = function
    | [] -> typ_error l ("No valid casts:\n" ^ m)
    | (cast :: casts) -> begin
        typ_print ("Casting with " ^ string_of_id cast ^ " expression " ^ string_of_exp annotated_exp ^ " to " ^ string_of_typ typ);
        try
          let checked_cast = crule check_exp (Env.no_casts env) (strip (E_app (cast, [annotated_exp]))) typ in
          annot_exp (E_cast (typ, checked_cast)) typ
        with
        | Type_error (_, m) -> try_casts m casts
      end
  in
  begin
    try
      typ_debug ("PERFORMING TYPE COERCION: from " ^ string_of_typ (typ_of annotated_exp) ^ " to " ^ string_of_typ typ);
      subtyp l env (typ_of annotated_exp) typ; annotated_exp
    with
    | Type_error (_, m) when Env.allow_casts env ->
       let casts = filter_casts env (typ_of annotated_exp) typ (Env.get_casts env) in
       try_casts "" casts
    | Type_error (l, m) -> typ_error l ("Subtype error " ^ m)
  end

(* type_coercion_unify env exp typ attempts to coerce exp to a type
   exp_typ in the same way as type_coercion, except it is only
   required that exp_typ unifies with typ. Returns the annotated
   coercion as with type_coercion and also a set of unifiers, or
   throws a unification error *)
and type_coercion_unify env (E_aux (_, (l, _)) as annotated_exp) typ =
  let strip exp_aux = strip_exp (E_aux (exp_aux, (Parse_ast.Unknown, None))) in
  let annot_exp exp typ = E_aux (exp, (l, Some (env, typ, no_effect))) in
  let rec try_casts m = function
    | [] -> unify_error l ("No valid casts resulted in unification:\n" ^ m)
    | (cast :: casts) -> begin
        typ_print ("Casting with " ^ string_of_id cast ^ " expression " ^ string_of_exp annotated_exp ^ " for unification");
        try
          let inferred_cast = irule infer_exp (Env.no_casts env) (strip (E_app (cast, [annotated_exp]))) in
          let ityp = typ_of inferred_cast in
          annot_exp (E_cast (ityp, inferred_cast)) ityp, unify l env typ ityp
        with
        | Type_error (_, m) -> try_casts m casts
        | Unification_error (_, m) -> try_casts m casts
      end
  in
  begin
    try
      typ_debug "PERFORMING COERCING UNIFICATION";
      annotated_exp, unify l env typ (typ_of annotated_exp)
    with
    | Unification_error (_, m) when Env.allow_casts env ->
       let casts = filter_casts env (typ_of annotated_exp) typ (Env.get_casts env) in
       try_casts "" casts
  end

and bind_pat env (P_aux (pat_aux, (l, ())) as pat) (Typ_aux (typ_aux, _) as typ) =
  typ_print ("Binding " ^ string_of_pat pat ^  " to " ^ string_of_typ typ);
  let annot_pat pat typ = P_aux (pat, (l, Some (env, typ, no_effect))) in
  let switch_typ (P_aux (pat_aux, (l, Some (env, _, eff)))) typ = P_aux (pat_aux, (l, Some (env, typ, eff))) in
  let bind_tuple_pat (tpats, env) pat typ =
    let tpat, env = bind_pat env pat typ in tpat :: tpats, env
  in
  match pat_aux with
  | P_id v ->
     begin
       match Env.lookup_id v env with
       | Local (Immutable, _) | Unbound -> annot_pat (P_id v) typ, Env.add_local v (Immutable, typ) env
       | Local (Mutable, _) | Register _ ->
          typ_error l ("Cannot shadow mutable local or register in switch statement pattern " ^ string_of_pat pat)
       | Enum enum -> subtyp l env enum typ; annot_pat (P_id v) typ, env
       | Union (typq, ctor_typ) ->
          begin
            try
              let _ = unify l env ctor_typ typ in
              annot_pat (P_id v) typ, env
            with
            | Unification_error (l, m) -> typ_error l ("Unification error when pattern matching against union constructor: " ^ m)
          end
     end
  | P_wild -> annot_pat P_wild typ, env
  | P_cons (hd_pat, tl_pat) ->
     begin
       match Env.expand_synonyms env typ with
       | Typ_aux (Typ_app (f, [Typ_arg_aux (Typ_arg_typ ltyp, _)]), _) when Id.compare f (mk_id "list") = 0 ->
          let hd_pat, env = bind_pat env hd_pat ltyp in
          let tl_pat, env = bind_pat env tl_pat typ in
          annot_pat (P_cons (hd_pat, tl_pat)) typ, env
       | _ -> typ_error l "Cannot match cons pattern against non-list type"
     end
  | P_list pats ->
     begin
       match Env.expand_synonyms env typ with
       | Typ_aux (Typ_app (f, [Typ_arg_aux (Typ_arg_typ ltyp, _)]), _) when Id.compare f (mk_id "list") = 0 ->
          let rec process_pats env = function
            | [] -> [], env
            | (pat :: pats) ->
               let pat', env = bind_pat env pat ltyp in
               let pats', env = process_pats env pats in
               pat' :: pats', env
          in
          let pats, env = process_pats env pats in
          annot_pat (P_list pats) typ, env
       | _ -> typ_error l "Cannot match list pattern against non-list type"
     end
  | P_tup [] ->
     begin
       match Env.expand_synonyms env typ with
       | Typ_aux (Typ_id typ_id, _) when string_of_id typ_id = "unit" ->
          annot_pat (P_tup []) typ, env
       | _ -> typ_error l "Cannot match unit pattern against non-unit type"
     end
  | P_tup pats ->
     begin
       match Env.expand_synonyms env typ with
       | Typ_aux (Typ_tup typs, _) ->
          let tpats, env =
            try List.fold_left2 bind_tuple_pat ([], env) pats typs with
            | Invalid_argument _ -> typ_error l "Tuple pattern and tuple type have different length"
          in
          annot_pat (P_tup (List.rev tpats)) typ, env
       | _ -> typ_error l "Cannot bind tuple pattern against non tuple type"
     end
  | P_app (f, pats) when Env.is_union_constructor f env ->
     begin
       let (typq, ctor_typ) = Env.get_val_spec f env in
       let quants = quant_items typq in
       let untuple (Typ_aux (typ_aux, _) as typ) = match typ_aux with
         | Typ_tup typs -> typs
         | _ -> [typ]
       in
       match Env.expand_synonyms env ctor_typ with
       | Typ_aux (Typ_fn (arg_typ, ret_typ, _), _) ->
          begin
            try
              typ_debug ("Unifying " ^ string_of_bind (typq, ctor_typ) ^ " for pattern " ^ string_of_typ typ);
              let unifiers, _, _ (* FIXME! *) = unify l env ret_typ typ in
              typ_debug (string_of_list ", " (fun (kid, uvar) -> string_of_kid kid ^ " => " ^ string_of_uvar uvar) (KBindings.bindings unifiers));
              let arg_typ' = subst_unifiers unifiers arg_typ in
              let quants' = List.fold_left (fun qs (kid, uvar) -> instantiate_quants qs kid uvar) quants (KBindings.bindings unifiers) in
              if (match quants' with [] -> false | _ -> true)
              then typ_error l ("Quantifiers " ^ string_of_list ", " string_of_quant_item quants' ^ " not resolved in pattern " ^ string_of_pat pat)
              else ();
              let ret_typ' = subst_unifiers unifiers ret_typ in
              let tpats, env =
                try List.fold_left2 bind_tuple_pat ([], env) pats (untuple arg_typ') with
                | Invalid_argument _ -> typ_error l "Union constructor pattern arguments have incorrect length"
              in
              annot_pat (P_app (f, List.rev tpats)) typ, env
            with
            | Unification_error (l, m) -> typ_error l ("Unification error when pattern matching against union constructor: " ^ m)
          end
       | _ -> typ_error l ("Mal-formed constructor " ^ string_of_id f)
     end
  | P_app (f, _) when not (Env.is_union_constructor f env) ->
     typ_error l (string_of_id f ^ " is not a union constructor in pattern " ^ string_of_pat pat)
  | _ ->
     let (inferred_pat, env) = infer_pat env pat in
     subtyp l env (pat_typ_of inferred_pat) typ;
     switch_typ inferred_pat typ, env

and infer_pat env (P_aux (pat_aux, (l, ())) as pat) =
  let annot_pat pat typ = P_aux (pat, (l, Some (env, typ, no_effect))) in
  match pat_aux with
  | P_id v ->
     begin
       match Env.lookup_id v env with
       | Local (Immutable, _) | Unbound ->
          typ_error l ("Cannot infer identifier in pattern " ^ string_of_pat pat ^ " - try adding a type annotation")
       | Local (Mutable, _) | Register _ ->
          typ_error l ("Cannot shadow mutable local or register in switch statement pattern " ^ string_of_pat pat)
       | Enum enum -> annot_pat (P_id v) enum, env
     end
  | P_typ (typ_annot, pat) ->
     let (typed_pat, env) = bind_pat env pat typ_annot in
     annot_pat (P_typ (typ_annot, typed_pat)) typ_annot, env
  | P_lit lit ->
     annot_pat (P_lit lit) (infer_lit env lit), env
  | P_vector (pat :: pats) ->
     let fold_pats (pats, env) pat =
       let typed_pat, env = bind_pat env pat bit_typ in
       pats @ [typed_pat], env
     in
     let ((typed_pat :: typed_pats) as pats), env =
       List.fold_left fold_pats ([], env) (pat :: pats) in
     let len = nexp_simp (nconstant (List.length pats)) in
     let etyp = pat_typ_of typed_pat in
     List.map (fun pat -> typ_equality l env etyp (pat_typ_of pat)) pats;
     annot_pat (P_vector pats) (lvector_typ env len etyp), env
  | P_vector_concat (pat :: pats) ->
     let fold_pats (pats, env) pat =
       let inferred_pat, env = infer_pat env pat in
       pats @ [inferred_pat], env
     in
     let (inferred_pat :: inferred_pats), env = List.fold_left fold_pats ([], env) (pat :: pats) in
     let (_, len, _, vtyp) = destructure_vec_typ l env (pat_typ_of inferred_pat) in
     let fold_len len pat =
       let (_, len', _, vtyp') = destructure_vec_typ l env (pat_typ_of pat) in
       typ_equality l env vtyp vtyp';
       nsum len len'
     in
     let len = nexp_simp (List.fold_left fold_len len inferred_pats) in
     annot_pat (P_vector_concat (inferred_pat :: inferred_pats)) (lvector_typ env len vtyp), env
  | P_as (pat, id) ->
     let (typed_pat, env) = infer_pat env pat in
     annot_pat (P_as (typed_pat, id)) (pat_typ_of typed_pat), Env.add_local id (Immutable, pat_typ_of typed_pat) env
  | _ -> typ_error l ("Couldn't infer type of pattern " ^ string_of_pat pat)

and bind_assignment env (LEXP_aux (lexp_aux, _) as lexp) (E_aux (_, (l, ())) as exp) =
  let annot_assign lexp exp = E_aux (E_assign (lexp, exp), (l, Some (env, mk_typ (Typ_id (mk_id "unit")), no_effect))) in
  let annot_lexp_effect lexp typ eff = LEXP_aux (lexp, (l, Some (env, typ, eff))) in
  let annot_lexp lexp typ = annot_lexp_effect lexp typ no_effect in
  let has_typ v env =
    match Env.lookup_id v env with
    | Local (Mutable, _) | Register _ -> true
    | _ -> false
  in
  match lexp_aux with
  | LEXP_field (LEXP_aux (flexp, _), field) ->
     begin
       let infer_flexp = function
         | LEXP_id v ->
            begin match Env.lookup_id v env with
            | Register typ -> typ, LEXP_id v, true
            | Local (Mutable, typ) -> typ, LEXP_id v, false
            | _ -> typ_error l "l-expression field is not a register or a local mutable type"
            end
         | LEXP_vector (LEXP_aux (LEXP_id v, _), exp) ->
            begin
              (* Check: is this ok if the vector is immutable? *)
              let is_immutable, vtyp, is_register = match Env.lookup_id v env with
                | Unbound -> typ_error l "Cannot assign to element of unbound vector"
                | Enum _ -> typ_error l "Cannot vector assign to enumeration element"
                | Local (Immutable, vtyp) -> true, vtyp, false
                | Local (Mutable, vtyp) -> false, vtyp, false
                | Register vtyp -> false, vtyp, true
              in
              let access = infer_exp (Env.enable_casts env) (E_aux (E_app (mk_id "vector_access", [E_aux (E_id v, (l, ())); exp]), (l, ()))) in
              let E_aux (E_app (_, [_; inferred_exp]), _) = access in
              typ_of access, LEXP_vector (annot_lexp (LEXP_id v) vtyp, inferred_exp), is_register
            end
       in
       let regtyp, inferred_flexp, is_register = infer_flexp flexp in
       typ_debug ("REGTYP: " ^ string_of_typ regtyp ^ " / " ^ string_of_typ (Env.expand_synonyms env regtyp));
       match Env.expand_synonyms env regtyp with
       | Typ_aux (Typ_app (Id_aux (Id "register", _), [Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id regtyp_id, _)), _)]), _)
       | Typ_aux (Typ_id regtyp_id, _) when Env.is_regtyp regtyp_id env ->
          let eff = mk_effect [BE_wreg] in
          let base, top, ranges = Env.get_regtyp regtyp_id env in
          let range, _ =
            try List.find (fun (_, id) -> Id.compare id field = 0) ranges with
            | Not_found -> typ_error l ("Field " ^ string_of_id field ^ " doesn't exist for register type " ^ string_of_id regtyp_id)
          in
          let vec_typ = match range, Env.get_default_order env with
            | BF_aux (BF_single n, _), Ord_aux (Ord_dec, _) ->
               dvector_typ env (nconstant n) (nconstant 1) (mk_typ (Typ_id (mk_id "bit")))
            | BF_aux (BF_range (n, m), _), Ord_aux (Ord_dec, _) ->
               dvector_typ env (nconstant n) (nconstant (n - m + 1)) (mk_typ (Typ_id (mk_id "bit")))
            | _, _ -> typ_error l "Not implemented this register field type yet..."
          in
          let checked_exp = crule check_exp env exp vec_typ in
          annot_assign (annot_lexp (LEXP_field (annot_lexp_effect inferred_flexp regtyp eff, field)) vec_typ) checked_exp, env
       | Typ_aux (Typ_id rectyp_id, _) | Typ_aux (Typ_app (rectyp_id, _), _) when Env.is_record rectyp_id env ->
          let eff = if is_register then mk_effect [BE_wreg] else no_effect in
          let (typq, Typ_aux (Typ_fn (rectyp_q, field_typ, _), _)) = Env.get_accessor rectyp_id field env in
          let unifiers, _, _ (* FIXME *) = try unify l env rectyp_q regtyp with Unification_error (l, m) -> typ_error l ("Unification error: " ^ m) in
          let field_typ' = subst_unifiers unifiers field_typ in
          let checked_exp = crule check_exp env exp field_typ' in
          annot_assign (annot_lexp (LEXP_field (annot_lexp_effect inferred_flexp regtyp eff, field)) field_typ') checked_exp, env
       | _ ->  typ_error l "Field l-expression has invalid type"
     end
  | LEXP_memory (f, xs) ->
     check_exp env (E_aux (E_app (f, xs @ [exp]), (l, ()))) unit_typ, env
  | LEXP_cast (typ_annot, v) ->
     let checked_exp = crule check_exp env exp typ_annot in
     let tlexp, env' = bind_lexp env lexp (typ_of checked_exp) in
     annot_assign tlexp checked_exp, env'
  | LEXP_id v when has_typ v env ->
     begin match Env.lookup_id v env with
     | Local (Mutable, vtyp) | Register vtyp ->
        let checked_exp = crule check_exp env exp vtyp in
        let tlexp, env' = bind_lexp env lexp (typ_of checked_exp) in
        annot_assign tlexp checked_exp, env'
     | _ -> assert false
     end
  | _ ->
     let inferred_exp = irule infer_exp env exp in
     let tlexp, env' = bind_lexp env lexp (typ_of inferred_exp) in
     annot_assign tlexp inferred_exp, env'

and bind_lexp env (LEXP_aux (lexp_aux, (l, ())) as lexp) typ =
  let annot_lexp_effect lexp typ eff = LEXP_aux (lexp, (l, Some (env, typ, eff))) in
  let annot_lexp lexp typ = annot_lexp_effect lexp typ no_effect in
  match lexp_aux with
  | LEXP_id v ->
     begin match Env.lookup_id v env with
     | Local (Immutable, _) | Enum _ ->
        typ_error l ("Cannot modify let-bound constant or enumeration constructor " ^ string_of_id v)
     | Local (Mutable, vtyp) -> subtyp l env typ vtyp; annot_lexp (LEXP_id v) typ, env
     | Register vtyp -> subtyp l env typ vtyp; annot_lexp_effect (LEXP_id v) typ (mk_effect [BE_wreg]), env
     | Unbound -> annot_lexp (LEXP_id v) typ, Env.add_local v (Mutable, typ) env
     end
  | LEXP_cast (typ_annot, v) ->
     begin
       match Env.lookup_id v env with
       | Local (Immutable, _) | Enum _ ->
          typ_error l ("Cannot modify let-bound constant or enumeration constructor " ^ string_of_id v)
       | Local (Mutable, vtyp) ->
          begin
            subtyp l env typ typ_annot;
            subtyp l env typ_annot vtyp;
            annot_lexp (LEXP_cast (typ_annot, v)) typ, Env.add_local v (Mutable, typ_annot) env
          end
       | Register vtyp ->
          begin
            subtyp l env typ typ_annot;
            subtyp l env typ_annot vtyp;
            annot_lexp_effect (LEXP_cast (typ_annot, v)) typ (mk_effect [BE_wreg]), env
          end
       | Unbound ->
          begin
            subtyp l env typ typ_annot;
            annot_lexp (LEXP_cast (typ_annot, v)) typ, Env.add_local v (Mutable, typ_annot) env
          end
     end
  | LEXP_tup lexps ->
     begin
       let (Typ_aux (typ_aux, _)) = typ in
       match typ_aux with
       | Typ_tup typs ->
          let bind_tuple_lexp (tlexps, env) lexp typ =
            let tlexp, env = bind_lexp env lexp typ in tlexp :: tlexps, env
          in
          let tlexps, env =
            try List.fold_left2 bind_tuple_lexp ([], env) lexps typs with
            | Invalid_argument _ -> typ_error l "Tuple l-expression and tuple type have different length"
          in
          annot_lexp (LEXP_tup tlexps) typ, env
       | _ -> typ_error l "Cannot bind tuple l-expression against non tuple type"
     end
  | LEXP_vector_range (LEXP_aux (LEXP_id v, _), exp1, exp2) ->
     begin
       let is_immutable, is_register, vtyp = match Env.lookup_id v env with
         | Unbound -> typ_error l "Cannot assign to element of unbound vector"
         | Enum _ -> typ_error l "Cannot vector assign to enumeration element"
         | Local (Immutable, vtyp) -> true, false, vtyp
         | Local (Mutable, vtyp) -> false, false, vtyp
         | Register vtyp -> false, true, vtyp
       in
       let access = infer_exp (Env.enable_casts env) (E_aux (E_app (mk_id "vector_subrange", [E_aux (E_id v, (l, ())); exp1; exp2]), (l, ()))) in
       let E_aux (E_app (_, [_; inferred_exp1; inferred_exp2]), _) = access in
       match typ_of access with
       | Typ_aux (Typ_app (id, [Typ_arg_aux (Typ_arg_typ deref_typ, _)]), _) when string_of_id id = "register" ->
          subtyp l env typ deref_typ;
          annot_lexp (LEXP_vector_range (annot_lexp_effect (LEXP_id v) vtyp (mk_effect [BE_wreg]), inferred_exp1, inferred_exp2)) typ, env
       | _ when not is_immutable && is_register ->
          subtyp l env typ (typ_of access);
          annot_lexp (LEXP_vector_range (annot_lexp_effect (LEXP_id v) vtyp (mk_effect [BE_wreg]), inferred_exp1, inferred_exp2)) typ, env
       | _ when not is_immutable ->
          subtyp l env typ (typ_of access);
          annot_lexp (LEXP_vector_range (annot_lexp (LEXP_id v) vtyp, inferred_exp1, inferred_exp2)) typ, env
       | _ -> typ_error l ("Bad vector assignment: " ^ string_of_lexp lexp)
     end
  (* Not sure about this case... can the left lexp be anything other than an identifier? *)
  | LEXP_vector (LEXP_aux (LEXP_id v, _), exp) ->
     begin
       let is_immutable, is_register, vtyp = match Env.lookup_id v env with
         | Unbound -> typ_error l "Cannot assign to element of unbound vector"
         | Enum _ -> typ_error l "Cannot vector assign to enumeration element"
         | Local (Immutable, vtyp) -> true, false, vtyp
         | Local (Mutable, vtyp) -> false, false, vtyp
         | Register vtyp -> false, true, vtyp
       in
       let access = infer_exp (Env.enable_casts env) (E_aux (E_app (mk_id "vector_access", [E_aux (E_id v, (l, ())); exp]), (l, ()))) in
       let E_aux (E_app (_, [_; inferred_exp]), _) = access in
       match typ_of access with
       | Typ_aux (Typ_app (id, [Typ_arg_aux (Typ_arg_typ deref_typ, _)]), _) when string_of_id id = "register" ->
          subtyp l env typ deref_typ;
          annot_lexp (LEXP_vector (annot_lexp_effect (LEXP_id v) vtyp (mk_effect [BE_wreg]), inferred_exp)) typ, env
       | _ when not is_immutable && is_register ->
          subtyp l env typ (typ_of access);
          annot_lexp (LEXP_vector (annot_lexp_effect (LEXP_id v) vtyp (mk_effect [BE_wreg]), inferred_exp)) typ, env
       | _ when not is_immutable ->
          subtyp l env typ (typ_of access);
          annot_lexp (LEXP_vector (annot_lexp (LEXP_id v) vtyp, inferred_exp)) typ, env
       | _ -> typ_error l ("Bad vector assignment: " ^ string_of_lexp lexp)
     end
  | LEXP_field (LEXP_aux (LEXP_id v, _), fid) ->
     (* FIXME: will only work for ASL *)
     let rec_id =
       match Env.lookup_id v env with
       | Register (Typ_aux (Typ_id rec_id, _)) -> rec_id
       | _ -> typ_error l (string_of_lexp lexp ^ " must be a record register here")
     in
     let typq, (Typ_aux (Typ_fn (_, ret_typ, _), _)) = Env.get_accessor rec_id fid env in
     annot_lexp_effect (LEXP_field (annot_lexp (LEXP_id v) (mk_id_typ rec_id), fid)) ret_typ (mk_effect [BE_wreg]), env
  | _ -> typ_error l ("Unhandled l-expression " ^ string_of_lexp lexp)

and infer_exp env (E_aux (exp_aux, (l, ())) as exp) =
  let annot_exp_effect exp typ eff = E_aux (exp, (l, Some (env, typ, eff))) in
  let annot_exp exp typ = annot_exp_effect exp typ no_effect in
  match exp_aux with
  | E_nondet exps ->
     annot_exp (E_nondet (List.map (fun exp -> crule check_exp env exp unit_typ) exps)) unit_typ
  | E_id v ->
     begin
       match Env.lookup_id v env with
       | Local (_, typ) | Enum typ -> annot_exp (E_id v) typ
       | Register typ -> annot_exp_effect (E_id v) typ (mk_effect [BE_rreg])
       | Unbound -> typ_error l ("Identifier " ^ string_of_id v ^ " is unbound")
       | Union (typq, typ) ->
          if quant_items typq = []
          then annot_exp (E_id v) typ
          else typ_error l ("Cannot infer the type of polymorphic union indentifier " ^ string_of_id v)
     end
  | E_lit lit -> annot_exp (E_lit lit) (infer_lit env lit)
  | E_sizeof nexp -> annot_exp (E_sizeof nexp) (mk_typ (Typ_app (mk_id "atom", [mk_typ_arg (Typ_arg_nexp nexp)])))
  | E_constraint nc ->
     annot_exp (E_constraint nc) bool_typ
  | E_field (exp, field) ->
     begin
       let inferred_exp = irule infer_exp env exp in
       match Env.expand_synonyms env (typ_of inferred_exp) with
       (* Accessing a (bit) field of a register *)
       | Typ_aux (Typ_app (Id_aux (Id "register", _), [Typ_arg_aux (Typ_arg_typ ((Typ_aux (Typ_id regtyp, _) as regtyp_aux)), _)]), _)
       | (Typ_aux (Typ_id regtyp, _) as regtyp_aux) when Env.is_regtyp regtyp env ->
          let base, top, ranges = Env.get_regtyp regtyp env in
          let range, _ =
            try List.find (fun (_, id) -> Id.compare id field = 0) ranges with
            | Not_found -> typ_error l ("Field " ^ string_of_id field ^ " doesn't exist for register type " ^ string_of_id regtyp)
          in
          let checked_exp = crule check_exp env (strip_exp inferred_exp) regtyp_aux in
          begin
            match range, Env.get_default_order env with
            | BF_aux (BF_single n, _), Ord_aux (Ord_dec, _) ->
               let vec_typ = dvector_typ env (nconstant n) (nconstant 1) bit_typ in
               annot_exp (E_field (checked_exp, field)) vec_typ
            | BF_aux (BF_range (n, m), _), Ord_aux (Ord_dec, _) ->
               let vec_typ = dvector_typ env (nconstant n) (nconstant (n - m + 1)) bit_typ in
               annot_exp (E_field (checked_exp, field)) vec_typ
            | BF_aux (BF_single n, _), Ord_aux (Ord_inc, _) ->
               let vec_typ = dvector_typ env (nconstant n) (nconstant 1) bit_typ in
               annot_exp (E_field (checked_exp, field)) vec_typ
            | BF_aux (BF_range (n, m), _), Ord_aux (Ord_inc, _) ->
               let vec_typ = dvector_typ env (nconstant n) (nconstant (m - n + 1)) bit_typ in
               annot_exp (E_field (checked_exp, field)) vec_typ
            | _, _ -> typ_error l "Invalid register field type"
          end
       (* Accessing a field of a record *)
       | Typ_aux (Typ_id rectyp, _) as typ when Env.is_record rectyp env ->
          begin
            let inferred_acc, _ = infer_funapp' l (Env.no_casts env) field (Env.get_accessor rectyp field env) [strip_exp inferred_exp] None in
            match inferred_acc with
            | E_aux (E_app (field, [inferred_exp]) ,_) -> annot_exp (E_field (inferred_exp, field)) (typ_of inferred_acc)
            | _ -> assert false (* Unreachable *)
          end
       | _ ->  typ_error l ("Field expression " ^ string_of_exp exp ^ " :: " ^ string_of_typ (typ_of inferred_exp) ^ " is not valid")
     end
  | E_tuple exps ->
     let inferred_exps = List.map (irule infer_exp env) exps in
     annot_exp (E_tuple inferred_exps) (mk_typ (Typ_tup (List.map typ_of inferred_exps)))
  | E_assign (lexp, bind) ->
     fst (bind_assignment env lexp bind)
  | E_cast (typ, exp) ->
     let checked_exp = crule check_exp env exp typ in
     annot_exp (E_cast (typ, checked_exp)) typ
  | E_app_infix (x, op, y) when List.length (Env.get_overloads (deinfix op) env) > 0 -> infer_exp env (E_aux (E_app (deinfix op, [x; y]), (l, ())))
  | E_app (f, xs) when List.length (Env.get_overloads f env) > 0 ->
     let rec try_overload = function
       | [] -> typ_error l ("No valid overloading for " ^ string_of_exp exp)
       | (f :: fs) -> begin
           typ_print ("Overload: " ^ string_of_id f ^ "(" ^ string_of_list ", " string_of_exp xs ^ ")");
           try irule infer_exp env (E_aux (E_app (f, xs), (l, ()))) with
           | Type_error (_, m) -> typ_print ("Error: " ^ m); try_overload fs
         end
     in
     try_overload (Env.get_overloads f env)
  | E_app (f, xs) -> infer_funapp l env f xs None
  | E_for (v, f, t, step, ord, body) ->
     begin
       let f, t = match ord with
         | Ord_aux (Ord_inc, _) -> f, t
         | Ord_aux (Ord_dec, _) -> t, f (* reverse direction for downto loop *)
       in
       let inferred_f = irule infer_exp env f in
       let inferred_t = irule infer_exp env t in
       let checked_step = crule check_exp env step int_typ in
       match is_range (typ_of inferred_f), is_range (typ_of inferred_t) with
       | None, _ -> typ_error l ("Type of " ^ string_of_exp f ^ " in foreach must be a range")
       | _, None -> typ_error l ("Type of " ^ string_of_exp t ^ " in foreach must be a range")
       (* | Some (l1, l2), Some (u1, u2) when prove env (nc_lteq l2 u1) ->
          let loop_vtyp = exist_typ (fun e -> nc_and (nc_lteq l1 (nvar e)) (nc_lteq (nvar e) u2)) (fun e -> atom_typ (nvar e)) in
          let checked_body = crule check_exp (Env.add_local v (Immutable, loop_vtyp) env) body unit_typ in
          annot_exp (E_for (v, inferred_f, inferred_t, checked_step, ord, checked_body)) unit_typ *)
       | Some (l1, l2), Some (u1, u2) when prove env (nc_lteq l2 u1) ->
          let kid = mk_kid ("loop_" ^ string_of_id v) in
          if KBindings.mem kid (Env.get_typ_vars env)
          then typ_error l "Nested loop variables cannot have the same name"
          else
            begin
              let env = Env.add_typ_var kid BK_nat env in
              let env = Env.add_constraint (nc_and (nc_lteq l1 (nvar kid)) (nc_lteq (nvar kid) u2)) env in
              let loop_vtyp = atom_typ (nvar kid) in
              let checked_body = crule check_exp (Env.add_local v (Immutable, loop_vtyp) env) body unit_typ in
              annot_exp (E_for (v, inferred_f, inferred_t, checked_step, ord, checked_body)) unit_typ
            end
       | _, _ -> typ_error l "Ranges in foreach overlap"
     end
  | E_if (cond, then_branch, else_branch) ->
     let cond' = crule check_exp env cond (mk_typ (Typ_id (mk_id "bool"))) in
     let flows, constrs = infer_flow env cond' in
     let then_branch' = irule infer_exp (add_constraints constrs (add_flows true flows env)) then_branch in
     let else_branch' = crule check_exp (add_constraints (List.map nc_negate constrs) (add_flows false flows env)) else_branch (typ_of then_branch') in
     annot_exp (E_if (cond', then_branch', else_branch')) (typ_of then_branch')
  | E_vector_access (v, n) -> infer_exp env (E_aux (E_app (mk_id "vector_access", [v; n]), (l, ())))
  | E_vector_append (v1, v2) -> infer_exp env (E_aux (E_app (mk_id "vector_append", [v1; v2]), (l, ())))
  | E_vector_subrange (v, n, m) -> infer_exp env (E_aux (E_app (mk_id "vector_subrange", [v; n; m]), (l, ())))
  | E_vector [] -> typ_error l "Cannot infer type of empty vector"
  | E_vector ((item :: items) as vec) ->
     let inferred_item = irule infer_exp env item in
     let checked_items = List.map (fun i -> crule check_exp env i (typ_of inferred_item)) items in
     let vec_typ = match Env.get_default_order env with
       | Ord_aux (Ord_inc, _) ->
          mk_typ (Typ_app (mk_id "vector",
                           [mk_typ_arg (Typ_arg_nexp (nconstant 0));
                            mk_typ_arg (Typ_arg_nexp (nconstant (List.length vec)));
                            mk_typ_arg (Typ_arg_order (Env.get_default_order env));
                            mk_typ_arg (Typ_arg_typ (typ_of inferred_item))]))
       | Ord_aux (Ord_dec, _) ->
          mk_typ (Typ_app (mk_id "vector",
                           [mk_typ_arg (Typ_arg_nexp (nconstant (List.length vec - 1)));
                            mk_typ_arg (Typ_arg_nexp (nconstant (List.length vec)));
                            mk_typ_arg (Typ_arg_order (Env.get_default_order env));
                            mk_typ_arg (Typ_arg_typ (typ_of inferred_item))]))
     in
     annot_exp (E_vector (inferred_item :: checked_items)) vec_typ
  | E_assert (test, msg) ->
     let checked_test = crule check_exp env test bool_typ in
     let checked_msg = crule check_exp env msg string_typ in
     annot_exp (E_assert (checked_test, checked_msg)) unit_typ
  | _ -> typ_error l ("Cannot infer type of: " ^ string_of_exp exp)

and infer_funapp l env f xs ret_ctx_typ = fst (infer_funapp' l env f (Env.get_val_spec f env) xs ret_ctx_typ)

and instantiation_of (E_aux (exp_aux, (l, _)) as exp) =
  let env = env_of exp in
  match exp_aux with
  | E_app (f, xs) -> snd (infer_funapp' l (Env.no_casts env) f (Env.get_val_spec f env) (List.map strip_exp xs) (Some (typ_of exp)))
  | _ -> invalid_arg ("instantiation_of expected application,  got " ^ string_of_exp exp)

and infer_funapp' l env f (typq, f_typ) xs ret_ctx_typ =
  let annot_exp exp typ eff = E_aux (exp, (l, Some (env, typ, eff))) in
  let all_unifiers = ref KBindings.empty in
  let ex_goal = ref None in
  let prove_goal env = match !ex_goal with
    | Some goal when prove env goal -> ()
    | Some goal -> typ_error l ("Could not prove existential goal: " ^ string_of_n_constraint goal)
    | None -> ()
  in
  let universals = Env.get_typ_vars env in
  let universal_constraints = Env.get_constraints env in
  let is_bound kid env = KBindings.mem kid (Env.get_typ_vars env) in
  let rec number n = function
    | [] -> []
    | (x :: xs) -> (n, x) :: number (n + 1) xs
  in
  let solve_quant env = function
    | QI_aux (QI_id _, _) -> false
    | QI_aux (QI_const nc, _) -> prove env nc
  in
  let rec instantiate env quants typs ret_typ args =
    match typs, args with
    | (utyps, []), (uargs, []) ->
       begin
         typ_debug ("Got unresolved args: " ^ string_of_list ", " (fun (_, exp) -> string_of_exp exp) uargs);
         if List.for_all (solve_quant env) quants
         then
           let iuargs = List.map2 (fun utyp (n, uarg) -> (n, crule check_exp env uarg utyp)) utyps uargs in
           (iuargs, ret_typ, env)
         else typ_error l ("Quantifiers " ^ string_of_list ", " string_of_quant_item quants
                           ^ " not resolved during application of " ^ string_of_id f)
       end
    | (utyps, (typ :: typs)), (uargs, ((n, arg) :: args))
         when List.for_all (fun kid -> is_bound kid env) (KidSet.elements (typ_frees typ)) ->
       begin
         let carg = crule check_exp env arg typ in
         let (iargs, ret_typ', env) = instantiate env quants (utyps, typs) ret_typ (uargs, args) in
         ((n, carg) :: iargs, ret_typ', env)
       end
    | (utyps, (typ :: typs)), (uargs, ((n, arg) :: args)) ->
       begin
         typ_debug ("INSTANTIATE: " ^ string_of_exp arg ^ " with " ^ string_of_typ typ);
         let iarg = irule infer_exp env arg in
         typ_debug ("INFER: " ^ string_of_exp arg ^ " type " ^ string_of_typ (typ_of iarg));
         try
           let iarg, (unifiers, ex_kids, ex_nc) (* FIXME *) = type_coercion_unify env iarg typ in
           typ_debug (string_of_list ", " (fun (kid, uvar) -> string_of_kid kid ^ " => " ^ string_of_uvar uvar) (KBindings.bindings unifiers));
           typ_debug ("EX KIDS: " ^ string_of_list ", " string_of_kid ex_kids);
           let env = match ex_kids, ex_nc with
             | [], None -> env
             | _, Some enc ->
                let env = List.fold_left (fun env kid -> Env.add_typ_var kid BK_nat env) env ex_kids in
                Env.add_constraint enc env
           in
           all_unifiers := merge_uvars l !all_unifiers unifiers;
           let utyps' = List.map (subst_unifiers unifiers) utyps in
           let typs' = List.map (subst_unifiers unifiers) typs in
           let quants' = List.fold_left (fun qs (kid, uvar) -> instantiate_quants qs kid uvar) quants (KBindings.bindings unifiers) in
           let ret_typ' = subst_unifiers unifiers ret_typ in
           let (iargs, ret_typ'', env) = instantiate env quants' (utyps', typs') ret_typ' (uargs, args) in
           ((n, iarg) :: iargs, ret_typ'', env)
         with
         | Unification_error (l, str) ->
            typ_debug ("Unification error: " ^ str);
            instantiate env quants (typ :: utyps, typs) ret_typ ((n, arg) :: uargs, args)
       end
    | (_, []), _ -> typ_error l ("Function " ^ string_of_id f ^ " applied to too many arguments")
    | _, (_, []) -> typ_error l ("Function " ^ string_of_id f ^ " not applied to enough arguments")
  in
  let instantiate_ret env quants typs ret_typ =
    match ret_ctx_typ with
    | None -> (quants, typs, ret_typ, env)
    | Some rct when is_exist (Env.expand_synonyms env rct) -> (quants, typs, ret_typ, env) 
    | Some rct ->
       begin
         typ_debug ("RCT is " ^ string_of_typ rct);
         typ_debug ("INSTANTIATE RETURN:" ^ string_of_typ ret_typ);
         let unifiers, ex_kids, ex_nc =
           try unify l env ret_typ rct with
           | Unification_error _ -> typ_debug "UERROR"; KBindings.empty, [], None
         in
         typ_debug (string_of_list ", " (fun (kid, uvar) -> string_of_kid kid ^ " => " ^ string_of_uvar uvar) (KBindings.bindings unifiers));
         if ex_kids = [] then () else (typ_debug ("EX GOAL: " ^ string_of_option string_of_n_constraint ex_nc); ex_goal := ex_nc);
         all_unifiers := merge_uvars l !all_unifiers unifiers;
         let env = List.fold_left (fun env kid -> Env.add_typ_var kid BK_nat env) env ex_kids in
         let typs' = List.map (subst_unifiers unifiers) typs in
         let quants' = List.fold_left (fun qs (kid, uvar) -> instantiate_quants qs kid uvar) quants (KBindings.bindings unifiers) in
         let ret_typ' =
           match ex_nc with
           | None -> subst_unifiers unifiers ret_typ
           | Some nc -> mk_typ (Typ_exist (ex_kids, nc, subst_unifiers unifiers ret_typ))
         in
         (quants', typs', ret_typ', env)
       end
  in
  let (quants, typ_args, typ_ret, env), eff =
    match Env.expand_synonyms env f_typ with
    | Typ_aux (Typ_fn (Typ_aux (Typ_tup typ_args, _), typ_ret, eff), _) ->
       instantiate_ret env (quant_items typq) typ_args typ_ret, eff
    | Typ_aux (Typ_fn (typ_arg, typ_ret, eff), _) ->
       instantiate_ret env (quant_items typq) [typ_arg] typ_ret, eff
    | _ -> typ_error l (string_of_typ f_typ ^ " is not a function type")
  in
  let (xs_instantiated, typ_ret, env) = instantiate env quants ([], typ_args) typ_ret ([], number 0 xs) in
  let xs_reordered = List.map snd (List.sort (fun (n, _) (m, _) -> compare n m) xs_instantiated) in

  prove_goal env;

  let ty_vars = List.map fst (KBindings.bindings (Env.get_typ_vars env)) in
  let existentials = List.filter (fun kid -> not (KBindings.mem kid universals)) ty_vars in
  let num_new_ncs = List.length (Env.get_constraints env) - List.length universal_constraints in
  let ex_constraints = take num_new_ncs (Env.get_constraints env) in 

  typ_debug ("Existentials: " ^ string_of_list ", " string_of_kid existentials);
  typ_debug ("Existential constraints: " ^ string_of_list ", " string_of_n_constraint ex_constraints);

  let typ_ret =
    if KidSet.is_empty (KidSet.of_list existentials)
    then (typ_debug "Returning Existential"; typ_ret)
    else mk_typ (Typ_exist (existentials, List.fold_left nc_and nc_true ex_constraints, typ_ret))
  in
  let typ_ret = simp_typ typ_ret in
  let exp = annot_exp (E_app (f, xs_reordered)) typ_ret eff in
  typ_debug ("RETURNING: " ^ string_of_typ (typ_of exp));
  match ret_ctx_typ with
  | None ->
     exp, !all_unifiers
  | Some rct ->
     let exp = type_coercion env exp rct in
     typ_debug ("RETURNING AFTER COERCION " ^ string_of_typ (typ_of exp));
     exp, !all_unifiers

(**************************************************************************)
(* 6. Effect system                                                       *)
(**************************************************************************)

let effect_of_annot = function
| Some (_, _, eff) -> eff
| None -> no_effect

let effect_of (E_aux (exp, (l, annot))) = effect_of_annot annot

let add_effect (E_aux (exp, (l, annot))) eff1 =
  match annot with
  | Some (env, typ, eff2) -> E_aux (exp, (l, Some (env, typ, union_effects eff1 eff2)))
  | None -> assert false

let effect_of_lexp (LEXP_aux (exp, (l, annot))) = effect_of_annot annot

let add_effect_lexp (LEXP_aux (lexp, (l, annot))) eff1 =
  match annot with
  | Some (env, typ, eff2) -> LEXP_aux (lexp, (l, Some (env, typ, union_effects eff1 eff2)))
  | None -> assert false

let effect_of_pat (P_aux (exp, (l, annot))) = effect_of_annot annot

let add_effect_pat (P_aux (pat, (l, annot))) eff1 =
  match annot with
  | Some (env, typ, eff2) -> P_aux (pat, (l, Some (env, typ, union_effects eff1 eff2)))
  | None -> assert false

let collect_effects xs = List.fold_left union_effects no_effect (List.map effect_of xs)

let collect_effects_lexp xs = List.fold_left union_effects no_effect (List.map effect_of_lexp xs)

let collect_effects_pat xs = List.fold_left union_effects no_effect (List.map effect_of_pat xs)

(* Traversal that propagates effects upwards through expressions *)

let rec propagate_exp_effect (E_aux (exp, annot)) =
  let p_exp, eff = propagate_exp_effect_aux exp in
  add_effect (E_aux (p_exp, annot)) eff
and propagate_exp_effect_aux = function
  | E_block xs ->
     let p_xs = List.map propagate_exp_effect xs in
     E_block p_xs, collect_effects p_xs
  | E_nondet xs ->
     let p_xs = List.map propagate_exp_effect xs in
     E_nondet p_xs, collect_effects p_xs
  | E_id id -> E_id id, no_effect
  | E_lit lit -> E_lit lit, no_effect
  | E_cast (typ, exp) ->
     let p_exp = propagate_exp_effect exp in
     E_cast (typ, p_exp), effect_of p_exp
  | E_app (id, xs) ->
     let p_xs = List.map propagate_exp_effect xs in
     E_app (id, p_xs), collect_effects p_xs
  | E_vector xs ->
     let p_xs = List.map propagate_exp_effect xs in
     E_vector p_xs, collect_effects p_xs
  | E_tuple xs ->
     let p_xs = List.map propagate_exp_effect xs in
     E_tuple p_xs, collect_effects p_xs
  | E_if (cond, t, e) ->
     let p_cond = propagate_exp_effect cond in
     let p_t = propagate_exp_effect t in
     let p_e =  propagate_exp_effect e in
     E_if (p_cond, p_t, p_e), collect_effects [p_cond; p_t; p_e]
  | E_case (exp, cases) ->
     let p_exp = propagate_exp_effect exp in
     let p_cases = List.map propagate_pexp_effect cases in
     let case_eff = List.fold_left union_effects no_effect (List.map snd p_cases) in
     E_case (p_exp, List.map fst p_cases), union_effects (effect_of p_exp) case_eff
  | E_try (exp, cases) ->
     let p_exp = propagate_exp_effect exp in
     let p_cases = List.map propagate_pexp_effect cases in
     let case_eff = List.fold_left union_effects no_effect (List.map snd p_cases) in
     E_try (p_exp, List.map fst p_cases), union_effects (effect_of p_exp) case_eff
  | E_for (v, f, t, step, ord, body) ->
     let p_f = propagate_exp_effect f in
     let p_t = propagate_exp_effect t in
     let p_step = propagate_exp_effect step in
     let p_body = propagate_exp_effect body in
     E_for (v, p_f, p_t, p_step, ord, p_body),
     collect_effects [p_f; p_t; p_step; p_body]
  | E_let (letbind, exp) ->
     let p_lb, eff = propagate_letbind_effect letbind in
     let p_exp = propagate_exp_effect exp in
     E_let (p_lb, p_exp), union_effects (effect_of p_exp) eff
  | E_cons (x, xs) ->
     let p_x = propagate_exp_effect x in
     let p_xs = propagate_exp_effect xs in
     E_cons (p_x, p_xs), union_effects (effect_of p_x) (effect_of p_xs)
  | E_list xs ->
     let p_xs = List.map propagate_exp_effect xs in
     E_list p_xs, collect_effects p_xs
  | E_assign (lexp, exp) ->
     let p_lexp = propagate_lexp_effect lexp in
     let p_exp = propagate_exp_effect exp in
     E_assign (p_lexp, p_exp), union_effects (effect_of p_exp) (effect_of_lexp p_lexp)
  | E_sizeof nexp -> E_sizeof nexp, no_effect
  | E_constraint nc -> E_constraint nc, no_effect
  | E_exit exp ->
     let p_exp = propagate_exp_effect exp in
     E_exit p_exp, effect_of p_exp
  | E_throw exp ->
     let p_exp = propagate_exp_effect exp in
     E_throw p_exp, effect_of p_exp
  | E_return exp ->
     let p_exp = propagate_exp_effect exp in
     E_return p_exp, effect_of p_exp
  | E_assert (test, msg) ->
     let p_test = propagate_exp_effect test in
     let p_msg = propagate_exp_effect msg in
     E_assert (p_test, p_msg), collect_effects [p_test; p_msg]
  | E_field (exp, id) ->
     let p_exp = propagate_exp_effect exp in
     E_field (p_exp, id), effect_of p_exp
  | exp_aux -> typ_error Parse_ast.Unknown ("Unimplemented: Cannot propagate effect in expression "
                                            ^ string_of_exp (E_aux (exp_aux, (Parse_ast.Unknown, None))))

and propagate_pexp_effect = function
  | Pat_aux (Pat_exp (pat, exp), (l, annot)) ->
     begin
       let p_pat = propagate_pat_effect pat in
       let p_exp = propagate_exp_effect exp in
       let p_eff = union_effects (effect_of_pat p_pat) (effect_of p_exp) in
       match annot with
       | Some (typq, typ, eff) ->
          Pat_aux (Pat_exp (p_pat, p_exp), (l, Some (typq, typ, union_effects eff p_eff))),
         union_effects eff p_eff
       | None -> Pat_aux (Pat_exp (p_pat, p_exp), (l, None)), p_eff
     end
  | Pat_aux (Pat_when (pat, guard, exp), (l, annot)) ->
     begin
       let p_pat = propagate_pat_effect pat in
       let p_guard = propagate_exp_effect guard in
       let p_exp = propagate_exp_effect exp in
       let p_eff = union_effects (effect_of_pat p_pat)
                                          (union_effects (effect_of p_guard) (effect_of p_exp))
       in
       match annot with
       | Some (typq, typ, eff) ->
          Pat_aux (Pat_when (p_pat, p_guard, p_exp), (l, Some (typq, typ, union_effects eff p_eff))),
          union_effects eff p_eff
       | None -> Pat_aux (Pat_when (p_pat, p_guard, p_exp), (l, None)), p_eff
     end

and propagate_pat_effect (P_aux (pat, annot)) =
  let p_pat, eff = propagate_pat_effect_aux pat in
  add_effect_pat (P_aux (p_pat, annot)) eff
and propagate_pat_effect_aux = function
  | P_lit lit -> P_lit lit, no_effect
  | P_wild -> P_wild, no_effect
  | P_cons (pat1, pat2) ->
     let p_pat1 = propagate_pat_effect pat1 in
     let p_pat2 = propagate_pat_effect pat2 in
     P_cons (p_pat1, p_pat2), union_effects (effect_of_pat p_pat1) (effect_of_pat p_pat2)
  | P_as (pat, id) ->
     let p_pat = propagate_pat_effect pat in
     P_as (p_pat, id), effect_of_pat p_pat
  | P_typ (typ, pat) ->
     let p_pat = propagate_pat_effect pat in
     P_typ (typ, p_pat), effect_of_pat p_pat
  | P_id id -> P_id id, no_effect
  | P_app (id, pats) ->
     let p_pats = List.map propagate_pat_effect pats in
     P_app (id, p_pats), collect_effects_pat p_pats
  | P_tup pats ->
     let p_pats = List.map propagate_pat_effect pats in
     P_tup p_pats, collect_effects_pat p_pats
  | P_list pats ->
     let p_pats = List.map propagate_pat_effect pats in
     P_list p_pats, collect_effects_pat p_pats
  | P_vector_concat pats ->
     let p_pats = List.map propagate_pat_effect pats in
     P_vector_concat p_pats, collect_effects_pat p_pats
  | P_vector pats ->
     let p_pats = List.map propagate_pat_effect pats in
     P_vector p_pats, collect_effects_pat p_pats
  | _ -> typ_error Parse_ast.Unknown "Unimplemented: Cannot propagate effect in pat"

and propagate_letbind_effect (LB_aux (lb, (l, annot))) =
  let p_lb, eff = propagate_letbind_effect_aux lb in
  match annot with
  | Some (typq, typ, eff) -> LB_aux (p_lb, (l, Some (typq, typ, eff))), eff
  | None -> LB_aux (p_lb, (l, None)), eff
and propagate_letbind_effect_aux = function
  | LB_val_explicit (typschm, pat, exp) ->
     let p_pat = propagate_pat_effect pat in
     let p_exp = propagate_exp_effect exp in
     LB_val_explicit (typschm, p_pat, p_exp),
     union_effects (effect_of_pat p_pat) (effect_of p_exp)
  | LB_val_implicit (pat, exp) ->
     let p_pat = propagate_pat_effect pat in
     let p_exp = propagate_exp_effect exp in
     LB_val_implicit (p_pat, p_exp),
     union_effects (effect_of_pat p_pat) (effect_of p_exp)

and propagate_lexp_effect (LEXP_aux (lexp, annot)) =
  let p_lexp, eff = propagate_lexp_effect_aux lexp in
  add_effect_lexp (LEXP_aux (p_lexp, annot)) eff
and propagate_lexp_effect_aux = function
  | LEXP_id id -> LEXP_id id, no_effect
  | LEXP_memory (id, exps) ->
     let p_exps = List.map propagate_exp_effect exps in
     LEXP_memory (id, p_exps), collect_effects p_exps
  | LEXP_cast (typ, id) -> LEXP_cast (typ, id), no_effect
  | LEXP_tup lexps ->
     let p_lexps = List.map propagate_lexp_effect lexps in
     LEXP_tup p_lexps, collect_effects_lexp p_lexps
  | LEXP_vector (lexp, exp) ->
     let p_lexp = propagate_lexp_effect lexp in
     let p_exp = propagate_exp_effect exp in
     LEXP_vector (p_lexp, p_exp), union_effects (effect_of p_exp) (effect_of_lexp p_lexp)
  | LEXP_vector_range (lexp, exp1, exp2) ->
     let p_lexp = propagate_lexp_effect lexp in
     let p_exp1 = propagate_exp_effect exp1 in
     let p_exp2 = propagate_exp_effect exp2 in
     LEXP_vector_range (p_lexp, p_exp1, p_exp2),
     union_effects (collect_effects [p_exp1; p_exp2]) (effect_of_lexp p_lexp)
  | LEXP_field (lexp, id) ->
     let p_lexp = propagate_lexp_effect lexp in
     LEXP_field (p_lexp, id),effect_of_lexp p_lexp
  | _ -> typ_error Parse_ast.Unknown "Unimplemented: Cannot propagate effect in lexp"

(**************************************************************************)
(* 6. Checking toplevel definitions                                       *)
(**************************************************************************)

let check_letdef env (LB_aux (letbind, (l, _))) =
  begin
    match letbind with
    | LB_val_explicit (typschm, pat, bind) -> assert false
    | LB_val_implicit (P_aux (P_typ (typ_annot, pat), _), bind) ->
       let checked_bind = crule check_exp env (strip_exp bind) typ_annot in
       let tpat, env = bind_pat env (strip_pat pat) typ_annot in
       [DEF_val (LB_aux (LB_val_implicit (P_aux (P_typ (typ_annot, tpat), (l, Some (env, typ_annot, no_effect))), checked_bind), (l, None)))], env
    | LB_val_implicit (pat, bind) ->
       let inferred_bind = irule infer_exp env (strip_exp bind) in
       let tpat, env = bind_pat env (strip_pat pat) (typ_of inferred_bind) in
       [DEF_val (LB_aux (LB_val_implicit (tpat, inferred_bind), (l, None)))], env
  end

let check_funcl env (FCL_aux (FCL_Funcl (id, pat, exp), (l, _))) typ =
  match typ with
  | Typ_aux (Typ_fn (typ_arg, typ_ret, eff), _) ->
     begin
       let typed_pat, env = bind_pat env (strip_pat pat) typ_arg in
       let env = Env.add_ret_typ typ_ret env in
       let exp = propagate_exp_effect (crule check_exp env (strip_exp exp) typ_ret) in
       FCL_aux (FCL_Funcl (id, typed_pat, exp), (l, Some (env, typ, effect_of exp)))
     end
  | _ -> typ_error l ("Function clause must have function type: " ^ string_of_typ typ ^ " is not a function type")

let funcl_effect (FCL_aux (FCL_Funcl (id, typed_pat, exp), (l, annot))) =
  match annot with
  | Some (_, _, eff) -> eff
  | None -> no_effect (* Maybe could be assert false. This should never happen *)

let infer_funtyp l env tannotopt funcls =
  match tannotopt with
  | Typ_annot_opt_aux (Typ_annot_opt_some (quant, ret_typ), _) ->
     begin
       let rec typ_from_pat (P_aux (pat_aux, (l, _)) as pat) =
         match pat_aux with
         | P_lit lit -> infer_lit env lit
         | P_typ (typ, _) -> typ
         | P_tup pats -> mk_typ (Typ_tup (List.map typ_from_pat pats))
         | _ -> typ_error l ("Cannot infer type from pattern " ^ string_of_pat pat)
       in
       match funcls with
       | [FCL_aux (FCL_Funcl (_, pat, _), _)] ->
          let arg_typ = typ_from_pat pat in
          let fn_typ = mk_typ (Typ_fn (arg_typ, ret_typ, Effect_aux (Effect_set [], Parse_ast.Unknown))) in
          (quant, fn_typ)
       | _ -> typ_error l "Cannot infer function type for function with multiple clauses"
     end
  | Typ_annot_opt_aux (Typ_annot_opt_none, _) -> typ_error l "Cannot infer function type for unannotated function"

let mk_val_spec typq typ id = DEF_spec (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (typq, typ), Parse_ast.Unknown), id), (Parse_ast.Unknown, None)))

let check_tannotopt typq ret_typ = function
  | Typ_annot_opt_aux (Typ_annot_opt_none, _) -> ()
  | Typ_annot_opt_aux (Typ_annot_opt_some (annot_typq, annot_ret_typ), l) ->
     if typ_identical ret_typ annot_ret_typ
     then ()
     else typ_error l (string_of_bind (typq, ret_typ) ^ " and " ^ string_of_bind (annot_typq, annot_ret_typ) ^ " do not match between function and val spec")

let check_fundef env (FD_aux (FD_function (recopt, tannotopt, effectopt, funcls), (l, _)) as fd_aux) =
  let id =
    match (List.fold_right
             (fun (FCL_aux (FCL_Funcl (id, _, _), _)) id' ->
               match id' with
               | Some id' -> if string_of_id id' = string_of_id id then Some id'
                             else typ_error l ("Function declaration expects all definitions to have the same name, "
                                               ^ string_of_id id ^ " differs from other definitions of " ^ string_of_id id')
               | None -> Some id) funcls None)
    with
    | Some id -> id
    | None -> typ_error l "funcl list is empty"
  in
  typ_print ("\nChecking function " ^ string_of_id id);
  let have_val_spec, (quant, (Typ_aux (Typ_fn (vtyp_arg, vtyp_ret, declared_eff), vl) as typ)), env =
    try true, Env.get_val_spec id env, env with
    | Type_error (l, _) ->
       let (quant, typ) = infer_funtyp l env tannotopt funcls in
       false, (quant, typ), env
  in
  check_tannotopt quant vtyp_ret tannotopt;
  typ_debug ("Checking fundef " ^ string_of_id id ^ " has type " ^ string_of_bind (quant, typ));
  let funcl_env = add_typquant quant env in
  let funcls = List.map (fun funcl -> check_funcl funcl_env funcl typ) funcls in
  let eff = List.fold_left union_effects no_effect (List.map funcl_effect funcls) in
  let vs_def, env, declared_eff =
    if not have_val_spec
    then
      let typ = Typ_aux (Typ_fn (vtyp_arg, vtyp_ret, eff), vl) in
      [mk_val_spec quant typ id], Env.add_val_spec id (quant, typ) env, eff
    else [], env, declared_eff
  in
  if (equal_effects eff declared_eff || !opt_no_effects)
  then
    vs_def @ [DEF_fundef (FD_aux (FD_function (recopt, tannotopt, effectopt, funcls), (l, None)))], env
  else typ_error l ("Effects do not match: " ^ string_of_effect declared_eff ^ " declared and " ^ string_of_effect eff ^ " found")

(* Checking a val spec simply adds the type as a binding in the
   context. We have to destructure the various kinds of val specs, but
   the difference is irrelevant for the typechecker. *)
let check_val_spec env (VS_aux (vs, (l, _))) =
  let (id, quants, typ, env) = match vs with
    | VS_val_spec (TypSchm_aux (TypSchm_ts (quants, typ), _), id) -> (id, quants, typ, env)
    | VS_cast_spec (TypSchm_aux (TypSchm_ts (quants, typ), _), id) -> (id, quants, typ, Env.add_cast id env)
    | VS_extern_no_rename (TypSchm_aux (TypSchm_ts (quants, typ), _), id) ->
      let env = Env.add_extern id (string_of_id id) env in
      (id, quants, typ, env)
    | VS_extern_spec (TypSchm_aux (TypSchm_ts (quants, typ), _), id, ext) ->
      let env = Env.add_extern id ext env in
      (id, quants, typ, env) in
  [DEF_spec (VS_aux (vs, (l, None)))], Env.add_val_spec id (quants, typ) env

let check_default env (DT_aux (ds, l)) =
  match ds with
  | DT_kind _ -> [DEF_default (DT_aux (ds,l))], env (* Check: Is this supposed to do nothing? *)
  | DT_order (Ord_aux (Ord_inc, _)) -> [DEF_default (DT_aux (ds, l))], Env.set_default_order_inc env
  | DT_order (Ord_aux (Ord_dec, _)) -> [DEF_default (DT_aux (ds, l))], Env.set_default_order_dec env
  | DT_order (Ord_aux (Ord_var _, _)) -> typ_error l "Cannot have variable default order"
  (* This branch allows us to write something like: default forall Nat 'n. [|'n|] name... what does this even mean?! *)
  | DT_typ (typschm, id) -> typ_error l ("Unsupported default construct")

let check_register env id base top ranges =
  match base, top with
  | Nexp_aux (Nexp_constant basec, _), Nexp_aux (Nexp_constant topc, _) ->
     let no_typq = TypQ_aux (TypQ_tq [], Parse_ast.Unknown) (* Maybe could be TypQ_no_forall? *) in
     (* FIXME: wrong for default Order inc? *)
     let vec_typ = dvector_typ env base (nconstant ((basec - topc) + 1)) bit_typ in
     let cast_typ = mk_typ (Typ_fn (mk_id_typ id, vec_typ, no_effect)) in
     let cast_to_typ = mk_typ (Typ_fn (vec_typ, mk_id_typ id, no_effect)) in
     env
     |> Env.add_regtyp id basec topc ranges
  (* |> Env.add_typ_synonym id (fun _ -> vec_typ) *)
     |> Env.add_val_spec (mk_id ("cast_" ^ string_of_id id)) (no_typq, cast_typ)
     |> Env.add_cast (mk_id ("cast_" ^ string_of_id id))
     |> Env.add_val_spec (mk_id ("cast_to_" ^ string_of_id id)) (no_typq, cast_to_typ)
     |> Env.add_cast (mk_id ("cast_to_" ^ string_of_id id))
  | _, _ -> typ_error (id_loc id) "Num expressions in register type declaration do not evaluate to constants"

let kinded_id_arg kind_id =
  let typ_arg arg = Typ_arg_aux (arg, Parse_ast.Unknown) in
  match kind_id with
  | KOpt_aux (KOpt_none kid, _) -> typ_arg (Typ_arg_nexp (nvar kid))
  | KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (BK_nat, _)], _), kid), _) -> typ_arg (Typ_arg_nexp (nvar kid))
  | KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (BK_order, _)], _), kid), _) ->
     typ_arg (Typ_arg_order (Ord_aux (Ord_var kid, Parse_ast.Unknown)))
  | KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (BK_type, _)], _), kid), _) ->
     typ_arg (Typ_arg_typ (mk_typ (Typ_var kid)))

let fold_union_quant quants (QI_aux (qi, l)) =
  match qi with
  | QI_id kind_id -> quants @ [kinded_id_arg kind_id]
  | _ -> quants

let check_type_union env variant typq (Tu_aux (tu, l)) =
  let ret_typ = app_typ variant (List.fold_left fold_union_quant [] (quant_items typq)) in
  match tu with
  | Tu_id v -> Env.add_union_id v (typq, ret_typ) env
  | Tu_ty_id (typ, v) ->
     let typ' = mk_typ (Typ_fn (typ, ret_typ, no_effect)) in
     env
     |> Env.add_union_id v (typq, typ')
     |> Env.add_val_spec v (typq, typ')

let mk_synonym typq typ =
  let kopts, ncs = quant_split typq in
  let rec subst_args kopts args =
    match kopts, args with
    | kopt :: kopts, Typ_arg_aux (Typ_arg_nexp arg, _) :: args when is_nat_kopt kopt ->
       let typ, ncs = subst_args kopts args in
       typ_subst_nexp (kopt_kid kopt) (unaux_nexp arg) typ,
       List.map (nc_subst_nexp (kopt_kid kopt) (unaux_nexp arg)) ncs
    | kopt :: kopts, Typ_arg_aux (Typ_arg_typ arg, _) :: args when is_typ_kopt kopt ->
       let typ, ncs = subst_args kopts args in
       typ_subst_typ (kopt_kid kopt) (unaux_typ arg) typ, ncs
    | kopt :: kopts, Typ_arg_aux (Typ_arg_order arg, _) :: args when is_order_kopt kopt ->
       let typ, ncs = subst_args kopts args in
       typ_subst_order (kopt_kid kopt) (unaux_order arg) typ, ncs     
    | [], [] -> typ, ncs
    | _, Typ_arg_aux (_, l) :: _ -> typ_error l "Synonym applied to bad arguments"
    | _, _ -> typ_error Parse_ast.Unknown "Synonym applied to bad arguments"
  in
  fun env args ->
    let typ, ncs = subst_args kopts args in
    if List.for_all (prove env) ncs
    then typ
    else typ_error Parse_ast.Unknown "Could not prove constraints in type synonym"

let check_typedef env (TD_aux (tdef, (l, _))) =
  let td_err () = raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Unimplemented Typedef") in
  match tdef with
  | TD_abbrev(id, nmscm, (TypSchm_aux (TypSchm_ts (typq, typ), _))) ->
     [DEF_type (TD_aux (tdef, (l, None)))], Env.add_typ_synonym id (mk_synonym typq typ) env
  | TD_record(id, nmscm, typq, fields, _) ->
     [DEF_type (TD_aux (tdef, (l, None)))], Env.add_record id typq fields env
  | TD_variant(id, nmscm, typq, arms, _) ->
     let env =
       env
       |> Env.add_variant id (typq, arms)
       |> (fun env -> List.fold_left (fun env tu -> check_type_union env id typq tu) env arms)
     in
     [DEF_type (TD_aux (tdef, (l, None)))], env
  | TD_enum(id, nmscm, ids, _) ->
     [DEF_type (TD_aux (tdef, (l, None)))], Env.add_enum id ids env
  | TD_register(id, base, top, ranges) -> [DEF_type (TD_aux (tdef, (l, None)))], check_register env id base top ranges

let rec check_def env def =
  let cd_err () = raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Unimplemented Case") in
  match def with
  | DEF_kind kdef -> cd_err ()
  | DEF_type tdef -> check_typedef env tdef
  | DEF_fundef fdef -> check_fundef env fdef
  | DEF_val letdef -> check_letdef env letdef
  | DEF_spec vs -> check_val_spec env vs
  | DEF_default default -> check_default env default
  | DEF_overload (id, ids) -> [DEF_overload (id, ids)], Env.add_overloads id ids env
  | DEF_reg_dec (DEC_aux (DEC_reg (typ, id), (l, _))) ->
     let env = Env.add_register id typ env in
     [DEF_reg_dec (DEC_aux (DEC_reg (typ, id), (l, Some (env, typ, no_effect))))], env
  | DEF_reg_dec (DEC_aux (DEC_alias (id, aspec), (l, annot))) -> cd_err ()
  | DEF_reg_dec (DEC_aux (DEC_typ_alias (typ, id, aspec), (l, tannot))) -> cd_err ()
  | DEF_scattered _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown "Scattered given to type checker")
  | DEF_comm (DC_comm str) -> [DEF_comm (DC_comm str)], env
  | DEF_comm (DC_comm_struct def) ->
     let defs, env = check_def env def
     in List.map (fun def -> DEF_comm (DC_comm_struct def)) defs, env

let rec check' env (Defs defs) =
  match defs with
  | [] -> (Defs []), env
  | def :: defs ->
     let (def, env) = check_def env def in
     let (Defs defs, env) = check' env (Defs defs) in
     (Defs (def @ defs)), env

let check env defs =
  try check' env defs with
  | Type_error (l, m) -> raise (Reporting_basic.err_typ l m)
