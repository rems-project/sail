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

open Ast
open Ast_defs
open Util
module Big_int = Nat_big_num

(* The type of annotations for untyped AST nodes *)
type uannot = { attrs : (l * string * string) list }

let empty_uannot = { attrs = [] }

let add_attribute l attr arg (annot : uannot) = { attrs = (l, attr, arg) :: annot.attrs }

let remove_attribute attr1 (annot : uannot) = { attrs = List.filter (fun (_, attr2, _) -> attr1 <> attr2) annot.attrs }

let get_attribute attr annot =
  List.find_opt (fun (_, attr', _) -> attr = attr') annot.attrs |> Option.map (fun (l, _, arg) -> (l, arg))

let get_attributes annot = annot.attrs

let find_attribute_opt attr1 attrs =
  List.find_opt (fun (_, attr2, _) -> attr1 = attr2) attrs |> Option.map (fun (_, _, arg) -> arg)

let mk_def_annot ?doc ?(attrs = []) l = { doc_comment = doc; attrs; loc = l }

let map_clause_annot f (def_annot, annot) =
  let l, annot' = f (def_annot.loc, annot) in
  ({ def_annot with loc = l }, annot')

let def_annot_map_loc f (annot : def_annot) = { annot with loc = f annot.loc }

let add_def_attribute l attr arg (annot : def_annot) = { annot with attrs = (l, attr, arg) :: annot.attrs }

let get_def_attribute attr (annot : def_annot) =
  List.find_opt (fun (_, attr', _) -> attr = attr') annot.attrs |> Option.map (fun (l, _, arg) -> (l, arg))

type mut = Immutable | Mutable

type 'a lvar = Register of 'a | Enum of 'a | Local of mut * 'a | Unbound of id

let is_unbound = function Unbound _ -> true | _ -> false

let is_order_inc = function Ord_aux (Ord_inc, _) -> true | Ord_aux (Ord_dec, _) -> false

let is_order_dec o = not (is_order_inc o)

let string_of_id = function Id_aux (Id v, _) -> v | Id_aux (Operator v, _) -> "(operator " ^ v ^ ")"

let lvar_typ ?loc:(l = Parse_ast.Unknown) = function
  | Local (_, typ) -> typ
  | Register typ -> typ
  | Enum typ -> typ
  | Unbound id -> Reporting.unreachable l __POS__ ("No type for unbound variable " ^ string_of_id id)

let no_annot = (Parse_ast.Unknown, empty_uannot)

let id_loc = function Id_aux (_, l) -> l

let kid_loc = function Kid_aux (_, l) -> l

let kopt_loc = function KOpt_aux (_, l) -> l

let typ_loc = function Typ_aux (_, l) -> l

let pat_loc = function P_aux (_, (l, _)) -> l

let mpat_loc = function MP_aux (_, (l, _)) -> l

let exp_loc = function E_aux (_, (l, _)) -> l

let nexp_loc = function Nexp_aux (_, l) -> l

let gen_loc = function Parse_ast.Generated l -> Parse_ast.Generated l | l -> Parse_ast.Generated l

let rec is_gen_loc = function
  | Parse_ast.Unknown -> false
  | Parse_ast.Unique (_, l) -> is_gen_loc l
  | Parse_ast.Generated _ -> true
  | Parse_ast.Hint (_, l1, l2) -> is_gen_loc l1 || is_gen_loc l2
  | Parse_ast.Range _ -> false

let mk_id str = Id_aux (Id str, Parse_ast.Unknown)

let mk_nc nc_aux = NC_aux (nc_aux, Parse_ast.Unknown)

let mk_nexp nexp_aux = Nexp_aux (nexp_aux, Parse_ast.Unknown)

let mk_exp ?loc:(l = Parse_ast.Unknown) exp_aux = E_aux (exp_aux, (l, empty_uannot))
let unaux_exp (E_aux (exp_aux, _)) = exp_aux
let uncast_exp = function
  | E_aux (E_internal_return (E_aux (E_typ (typ, exp), _)), a) -> (E_aux (E_internal_return exp, a), Some typ)
  | E_aux (E_typ (typ, exp), _) -> (exp, Some typ)
  | exp -> (exp, None)

let mk_pat ?loc:(l = Parse_ast.Unknown) pat_aux = P_aux (pat_aux, (l, empty_uannot))
let unaux_pat (P_aux (pat_aux, _)) = pat_aux
let untyp_pat = function P_aux (P_typ (typ, pat), _) -> (pat, Some typ) | pat -> (pat, None)

let mk_pexp ?loc:(l = Parse_ast.Unknown) pexp_aux = Pat_aux (pexp_aux, (l, empty_uannot))

let mk_mpat mpat_aux = MP_aux (mpat_aux, no_annot)
let mk_mpexp mpexp_aux = MPat_aux (mpexp_aux, no_annot)

let mk_lexp lexp_aux = LE_aux (lexp_aux, no_annot)

let mk_typ_pat tpat_aux = TP_aux (tpat_aux, Parse_ast.Unknown)

let mk_lit lit_aux = L_aux (lit_aux, Parse_ast.Unknown)

let mk_lit_exp ?loc:(l = Parse_ast.Unknown) lit_aux = mk_exp ~loc:l (E_lit (mk_lit lit_aux))

let mk_funcl ?loc:(l = Parse_ast.Unknown) id pat body =
  FCL_aux (FCL_funcl (id, Pat_aux (Pat_exp (pat, body), (l, empty_uannot))), (mk_def_annot l, empty_uannot))

let mk_qi_nc nc = QI_aux (QI_constraint nc, Parse_ast.Unknown)

let mk_qi_id k kid =
  let kopt = KOpt_aux (KOpt_kind (K_aux (k, Parse_ast.Unknown), kid), Parse_ast.Unknown) in
  QI_aux (QI_id kopt, Parse_ast.Unknown)

let mk_qi_kopt kopt = QI_aux (QI_id kopt, Parse_ast.Unknown)

let mk_fundef funcls =
  let tannot_opt = Typ_annot_opt_aux (Typ_annot_opt_none, Parse_ast.Unknown) in
  let rec_opt = Rec_aux (Rec_nonrec, Parse_ast.Unknown) in
  DEF_aux (DEF_fundef (FD_aux (FD_function (rec_opt, tannot_opt, funcls), no_annot)), mk_def_annot Parse_ast.Unknown)

let mk_letbind pat exp = LB_aux (LB_val (pat, exp), no_annot)

let mk_val_spec vs_aux = DEF_aux (DEF_val (VS_aux (vs_aux, no_annot)), mk_def_annot Parse_ast.Unknown)

let mk_def ?loc:(l = Parse_ast.Unknown) def = DEF_aux (def, mk_def_annot l)

let rec pat_of_mpat (MP_aux (mpat, annot)) =
  match mpat with
  | MP_lit lit -> P_aux (P_lit lit, annot)
  | MP_id id -> P_aux (P_id id, annot)
  | MP_app (id, args) -> P_aux (P_app (id, List.map pat_of_mpat args), annot)
  | MP_vector mpats -> P_aux (P_vector (List.map pat_of_mpat mpats), annot)
  | MP_vector_concat mpats -> P_aux (P_vector_concat (List.map pat_of_mpat mpats), annot)
  | MP_vector_subrange (id, n, m) -> P_aux (P_vector_subrange (id, n, m), annot)
  | MP_tuple mpats -> P_aux (P_tuple (List.map pat_of_mpat mpats), annot)
  | MP_list mpats -> P_aux (P_list (List.map pat_of_mpat mpats), annot)
  | MP_cons (mpat1, mpat2) -> P_aux (P_cons (pat_of_mpat mpat1, pat_of_mpat mpat2), annot)
  | MP_string_append mpats -> P_aux (P_string_append (List.map pat_of_mpat mpats), annot)
  | MP_typ (mpat, typ) -> P_aux (P_typ (typ, pat_of_mpat mpat), annot)
  | MP_as (mpat, id) -> P_aux (P_as (pat_of_mpat mpat, id), annot)
  | MP_struct fmpats ->
      P_aux (P_struct (List.map (fun (field, mpat) -> (field, pat_of_mpat mpat)) fmpats, FP_no_wild), annot)

let kopt_kid (KOpt_aux (KOpt_kind (_, kid), _)) = kid
let kopt_kind (KOpt_aux (KOpt_kind (k, _), _)) = k

let is_int_kopt = function KOpt_aux (KOpt_kind (K_aux (K_int, _), _), _) -> true | _ -> false

let is_typ_kopt = function KOpt_aux (KOpt_kind (K_aux (K_type, _), _), _) -> true | _ -> false

let is_bool_kopt = function KOpt_aux (KOpt_kind (K_aux (K_bool, _), _), _) -> true | _ -> false

let string_of_kid = function Kid_aux (Var v, _) -> v

module Kid = struct
  type t = kid
  let compare kid1 kid2 = String.compare (string_of_kid kid1) (string_of_kid kid2)
end

module Kind = struct
  type t = kind
  let compare (K_aux (aux1, _)) (K_aux (aux2, _)) =
    match (aux1, aux2) with
    | K_int, K_int -> 0
    | K_type, K_type -> 0
    | K_bool, K_bool -> 0
    | K_int, _ -> 1
    | _, K_int -> -1
    | K_type, _ -> 1
    | _, K_type -> -1
end

module KOpt = struct
  type t = kinded_id
  let compare kopt1 kopt2 =
    let lex_ord c1 c2 = if c1 = 0 then c2 else c1 in
    lex_ord (Kid.compare (kopt_kid kopt1) (kopt_kid kopt2)) (Kind.compare (kopt_kind kopt1) (kopt_kind kopt2))
end

module Id = struct
  type t = id
  let compare id1 id2 =
    match (id1, id2) with
    | Id_aux (Id x, _), Id_aux (Id y, _) -> String.compare x y
    | Id_aux (Operator x, _), Id_aux (Operator y, _) -> String.compare x y
    | Id_aux (Id _, _), Id_aux (Operator _, _) -> -1
    | Id_aux (Operator _, _), Id_aux (Id _, _) -> 1
end

module Nexp = struct
  type t = nexp
  let rec compare (Nexp_aux (nexp1, _)) (Nexp_aux (nexp2, _)) =
    let lex_ord (c1, c2) = if c1 = 0 then c2 else c1 in
    match (nexp1, nexp2) with
    | Nexp_id v1, Nexp_id v2 -> Id.compare v1 v2
    | Nexp_var kid1, Nexp_var kid2 -> Kid.compare kid1 kid2
    | Nexp_constant c1, Nexp_constant c2 -> Big_int.compare c1 c2
    | Nexp_app (op1, args1), Nexp_app (op2, args2) ->
        let lex1 = Id.compare op1 op2 in
        let lex2 = List.length args1 - List.length args2 in
        let lex3 = if lex2 = 0 then List.fold_left2 (fun l n1 n2 -> lex_ord (l, compare n1 n2)) 0 args1 args2 else 0 in
        lex_ord (lex1, lex_ord (lex2, lex3))
    | Nexp_times (n1a, n1b), Nexp_times (n2a, n2b)
    | Nexp_sum (n1a, n1b), Nexp_sum (n2a, n2b)
    | Nexp_minus (n1a, n1b), Nexp_minus (n2a, n2b) ->
        lex_ord (compare n1a n2a, compare n1b n2b)
    | Nexp_exp n1, Nexp_exp n2 -> compare n1 n2
    | Nexp_neg n1, Nexp_neg n2 -> compare n1 n2
    | Nexp_constant _, _ -> -1
    | _, Nexp_constant _ -> 1
    | Nexp_id _, _ -> -1
    | _, Nexp_id _ -> 1
    | Nexp_var _, _ -> -1
    | _, Nexp_var _ -> 1
    | Nexp_neg _, _ -> -1
    | _, Nexp_neg _ -> 1
    | Nexp_exp _, _ -> -1
    | _, Nexp_exp _ -> 1
    | Nexp_minus _, _ -> -1
    | _, Nexp_minus _ -> 1
    | Nexp_sum _, _ -> -1
    | _, Nexp_sum _ -> 1
    | Nexp_times _, _ -> -1
    | _, Nexp_times _ -> 1
end

module Bindings = Map.Make (Id)
module IdSet = Set.Make (Id)
module KBindings = Map.Make (Kid)
module KidSet = Set.Make (Kid)
module KOptSet = Set.Make (KOpt)
module KOptMap = Map.Make (KOpt)
module NexpSet = Set.Make (Nexp)
module NexpMap = Map.Make (Nexp)

let nexp_identical nexp1 nexp2 = Nexp.compare nexp1 nexp2 = 0

let rec is_nexp_constant (Nexp_aux (nexp, _)) =
  match nexp with
  | Nexp_id _ | Nexp_var _ -> false
  | Nexp_constant _ -> true
  | Nexp_times (n1, n2) | Nexp_sum (n1, n2) | Nexp_minus (n1, n2) -> is_nexp_constant n1 && is_nexp_constant n2
  | Nexp_exp n | Nexp_neg n -> is_nexp_constant n
  | Nexp_app (_, nexps) -> List.for_all is_nexp_constant nexps

let int_of_nexp_opt nexp = match nexp with Nexp_aux (Nexp_constant i, _) -> Some i | _ -> None

let rec nexp_simp (Nexp_aux (nexp, l)) = Nexp_aux (nexp_simp_aux nexp, l)

and nexp_simp_aux = function
  (* (n - (n - m)) often appears in foreach loops *)
  | Nexp_minus (nexp1, Nexp_aux (Nexp_minus (nexp2, Nexp_aux (n3, _)), _)) when nexp_identical nexp1 nexp2 ->
      nexp_simp_aux n3
  | Nexp_minus (Nexp_aux (Nexp_sum (Nexp_aux (n1, _), nexp2), _), nexp3) when nexp_identical nexp2 nexp3 ->
      nexp_simp_aux n1
  | Nexp_sum (Nexp_aux (Nexp_minus (Nexp_aux (n1, _), nexp2), _), nexp3) when nexp_identical nexp2 nexp3 ->
      nexp_simp_aux n1
  | Nexp_sum (n1, n2) -> begin
      let (Nexp_aux (n1_simp, _) as n1) = nexp_simp n1 in
      let (Nexp_aux (n2_simp, _) as n2) = nexp_simp n2 in
      match (n1_simp, n2_simp) with
      | Nexp_constant c1, Nexp_constant c2 -> Nexp_constant (Big_int.add c1 c2)
      | _, Nexp_neg n2 -> Nexp_minus (n1, n2)
      | _, _ -> Nexp_sum (n1, n2)
    end
  | Nexp_times (n1, n2) -> begin
      let (Nexp_aux (n1_simp, _) as n1) = nexp_simp n1 in
      let (Nexp_aux (n2_simp, _) as n2) = nexp_simp n2 in
      match (n1_simp, n2_simp) with
      | Nexp_constant c, _ when Big_int.equal c (Big_int.of_int 1) -> n2_simp
      | _, Nexp_constant c when Big_int.equal c (Big_int.of_int 1) -> n1_simp
      | Nexp_constant c1, Nexp_constant c2 -> Nexp_constant (Big_int.mul c1 c2)
      | _, _ -> Nexp_times (n1, n2)
    end
  | Nexp_minus (n1, n2) -> begin
      let (Nexp_aux (n1_simp, _) as n1) = nexp_simp n1 in
      let (Nexp_aux (n2_simp, _) as n2) = nexp_simp n2 in
      match (n1_simp, n2_simp) with
      | Nexp_constant c1, Nexp_constant c2 -> Nexp_constant (Big_int.sub c1 c2)
      (* A vector range x['n-1 .. 0] can result in the size "('n-1) - -1" *)
      | Nexp_minus (Nexp_aux (n, _), Nexp_aux (Nexp_constant c1, _)), Nexp_constant c2
        when Big_int.equal c1 (Big_int.negate c2) ->
          n
      | _, _ -> Nexp_minus (n1, n2)
    end
  | Nexp_neg n -> begin
      let (Nexp_aux (n_simp, _) as n) = nexp_simp n in
      match n_simp with Nexp_constant c -> Nexp_constant (Big_int.negate c) | _ -> Nexp_neg n
    end
  | Nexp_app ((Id_aux (Id "div", _) as id), [n1; n2]) -> begin
      let (Nexp_aux (n1_simp, _) as n1) = nexp_simp n1 in
      let (Nexp_aux (n2_simp, _) as n2) = nexp_simp n2 in
      match (n1_simp, n2_simp) with
      | Nexp_constant c1, Nexp_constant c2 -> Nexp_constant (Big_int.div c1 c2)
      | _, _ -> Nexp_app (id, [n1; n2])
    end
  | Nexp_exp nexp ->
      let nexp = nexp_simp nexp in
      begin
        match nexp with
        | Nexp_aux (Nexp_constant c, _)
          when Big_int.greater_equal c Big_int.zero && Big_int.less_equal c (Big_int.of_int 7) ->
            Nexp_constant (Big_int.pow_int_positive 2 (Big_int.to_int c))
        | _ -> Nexp_exp nexp
      end
  | nexp -> nexp

let rec constraint_simp (NC_aux (nc_aux, l)) =
  let nc_aux =
    match nc_aux with
    | NC_equal (nexp1, nexp2) ->
        let nexp1, nexp2 = (nexp_simp nexp1, nexp_simp nexp2) in
        if nexp_identical nexp1 nexp2 then NC_true else NC_equal (nexp1, nexp2)
    | NC_and (nc1, nc2) ->
        let nc1, nc2 = (constraint_simp nc1, constraint_simp nc2) in
        begin
          match (nc1, nc2) with
          | NC_aux (NC_true, _), NC_aux (nc, _) -> nc
          | NC_aux (nc, _), NC_aux (NC_true, _) -> nc
          | NC_aux (NC_false, _), NC_aux (_, _) -> NC_false
          | NC_aux (_, _), NC_aux (NC_false, _) -> NC_false
          | _, _ -> NC_and (nc1, nc2)
        end
    | NC_or (nc1, nc2) ->
        let nc1, nc2 = (constraint_simp nc1, constraint_simp nc2) in
        begin
          match (nc1, nc2) with
          | NC_aux (NC_false, _), NC_aux (nc, _) -> nc
          | NC_aux (nc, _), NC_aux (NC_false, _) -> nc
          | NC_aux (NC_true, _), NC_aux (_, _) -> NC_true
          | NC_aux (_, _), NC_aux (NC_true, _) -> NC_true
          | _, _ -> NC_or (nc1, nc2)
        end
    | NC_bounded_ge (nexp1, nexp2) ->
        let nexp1, nexp2 = (nexp_simp nexp1, nexp_simp nexp2) in
        begin
          match (nexp1, nexp2) with
          | Nexp_aux (Nexp_constant c1, _), Nexp_aux (Nexp_constant c2, _) ->
              if Big_int.greater_equal c1 c2 then NC_true else NC_false
          | _, _ -> NC_bounded_ge (nexp1, nexp2)
        end
    | NC_bounded_gt (nexp1, nexp2) ->
        let nexp1, nexp2 = (nexp_simp nexp1, nexp_simp nexp2) in
        begin
          match (nexp1, nexp2) with
          | Nexp_aux (Nexp_constant c1, _), Nexp_aux (Nexp_constant c2, _) ->
              if Big_int.greater c1 c2 then NC_true else NC_false
          | _, _ -> NC_bounded_gt (nexp1, nexp2)
        end
    | NC_bounded_le (nexp1, nexp2) ->
        let nexp1, nexp2 = (nexp_simp nexp1, nexp_simp nexp2) in
        begin
          match (nexp1, nexp2) with
          | Nexp_aux (Nexp_constant c1, _), Nexp_aux (Nexp_constant c2, _) ->
              if Big_int.less_equal c1 c2 then NC_true else NC_false
          | _, _ -> NC_bounded_le (nexp1, nexp2)
        end
    | NC_bounded_lt (nexp1, nexp2) ->
        let nexp1, nexp2 = (nexp_simp nexp1, nexp_simp nexp2) in
        begin
          match (nexp1, nexp2) with
          | Nexp_aux (Nexp_constant c1, _), Nexp_aux (Nexp_constant c2, _) ->
              if Big_int.less c1 c2 then NC_true else NC_false
          | _, _ -> NC_bounded_lt (nexp1, nexp2)
        end
    | NC_app (id, [A_aux (A_bool nc, arg_l)]) when Id.compare (mk_id "not") id = 0 ->
        let nc = constraint_simp nc in
        begin
          match nc with
          | NC_aux (NC_false, _) -> NC_true
          | NC_aux (NC_true, _) -> NC_false
          | NC_aux (NC_app (id, [A_aux (A_bool (NC_aux (nc_aux, _)), _)]), _) when Id.compare (mk_id "not") id = 0 ->
              nc_aux
          | _ -> NC_app (id, [A_aux (A_bool nc, arg_l)])
        end
    | _ -> nc_aux
  in
  NC_aux (nc_aux, l)

let rec constraint_conj (NC_aux (nc_aux, _) as nc) =
  match nc_aux with NC_and (nc1, nc2) -> constraint_conj nc1 @ constraint_conj nc2 | _ -> [nc]

let rec constraint_disj (NC_aux (nc_aux, _) as nc) =
  match nc_aux with NC_or (nc1, nc2) -> constraint_disj nc1 @ constraint_disj nc2 | _ -> [nc]

let mk_typ typ = Typ_aux (typ, Parse_ast.Unknown)
let mk_typ_arg arg = A_aux (arg, Parse_ast.Unknown)
let mk_kid str = Kid_aux (Var ("'" ^ str), Parse_ast.Unknown)

let mk_id_typ id = Typ_aux (Typ_id id, Parse_ast.Unknown)

let mk_kopt ?loc:(l = Parse_ast.Unknown) kind_aux v =
  let l = match l with Parse_ast.Unknown -> kid_loc v | l -> l in
  KOpt_aux (KOpt_kind (K_aux (kind_aux, l), v), l)

let unknown_typ = mk_typ Typ_internal_unknown
let int_typ = mk_id_typ (mk_id "int")
let nat_typ = mk_id_typ (mk_id "nat")
let unit_typ = mk_id_typ (mk_id "unit")
let bit_typ = mk_id_typ (mk_id "bit")
let real_typ = mk_id_typ (mk_id "real")
let app_typ id args = mk_typ (Typ_app (id, args))
let register_typ typ = mk_typ (Typ_app (mk_id "register", [mk_typ_arg (A_typ typ)]))
let atom_typ nexp = mk_typ (Typ_app (mk_id "atom", [mk_typ_arg (A_nexp (nexp_simp nexp))]))
let implicit_typ nexp = mk_typ (Typ_app (mk_id "implicit", [mk_typ_arg (A_nexp (nexp_simp nexp))]))
let range_typ nexp1 nexp2 =
  mk_typ (Typ_app (mk_id "range", [mk_typ_arg (A_nexp (nexp_simp nexp1)); mk_typ_arg (A_nexp (nexp_simp nexp2))]))
let bool_typ = mk_id_typ (mk_id "bool")
let atom_bool_typ nc = mk_typ (Typ_app (mk_id "atom_bool", [mk_typ_arg (A_bool nc)]))
let string_typ = mk_id_typ (mk_id "string")
let list_typ typ = mk_typ (Typ_app (mk_id "list", [mk_typ_arg (A_typ typ)]))
let tuple_typ typs = mk_typ (Typ_tuple typs)
let function_typ arg_typs ret_typ = mk_typ (Typ_fn (arg_typs, ret_typ))

let vector_typ n typ = mk_typ (Typ_app (mk_id "vector", [mk_typ_arg (A_nexp (nexp_simp n)); mk_typ_arg (A_typ typ)]))

let bitvector_typ n = mk_typ (Typ_app (mk_id "bitvector", [mk_typ_arg (A_nexp (nexp_simp n))]))

let exc_typ = mk_id_typ (mk_id "exception")

let nconstant c = Nexp_aux (Nexp_constant c, Parse_ast.Unknown)
let nint i = nconstant (Big_int.of_int i)
let nminus n1 n2 = Nexp_aux (Nexp_minus (n1, n2), Parse_ast.Unknown)
let nsum n1 n2 = Nexp_aux (Nexp_sum (n1, n2), Parse_ast.Unknown)
let ntimes n1 n2 = Nexp_aux (Nexp_times (n1, n2), Parse_ast.Unknown)
let npow2 n = Nexp_aux (Nexp_exp n, Parse_ast.Unknown)
let nvar kid = Nexp_aux (Nexp_var kid, Parse_ast.Unknown)
let nid id = Nexp_aux (Nexp_id id, Parse_ast.Unknown)
let napp id args = Nexp_aux (Nexp_app (id, args), Parse_ast.Unknown)

let nc_set kid nums = mk_nc (NC_set (kid, nums))
let nc_int_set kid ints = mk_nc (NC_set (kid, List.map Big_int.of_int ints))
let nc_eq n1 n2 = mk_nc (NC_equal (n1, n2))
let nc_neq n1 n2 = mk_nc (NC_not_equal (n1, n2))
let nc_lteq n1 n2 = NC_aux (NC_bounded_le (n1, n2), Parse_ast.Unknown)
let nc_lt n1 n2 = NC_aux (NC_bounded_lt (n1, n2), Parse_ast.Unknown)
let nc_gteq n1 n2 = NC_aux (NC_bounded_ge (n1, n2), Parse_ast.Unknown)
let nc_gt n1 n2 = NC_aux (NC_bounded_gt (n1, n2), Parse_ast.Unknown)
let nc_var kid = mk_nc (NC_var kid)
let nc_true = mk_nc NC_true
let nc_false = mk_nc NC_false

let nc_or nc1 nc2 =
  match (nc1, nc2) with
  | _, NC_aux (NC_false, _) -> nc1
  | NC_aux (NC_false, _), _ -> nc2
  | _, _ -> mk_nc (NC_or (nc1, nc2))

let nc_and nc1 nc2 =
  match (nc1, nc2) with
  | _, NC_aux (NC_true, _) -> nc1
  | NC_aux (NC_true, _), _ -> nc2
  | _, _ -> mk_nc (NC_and (nc1, nc2))

let arg_nexp ?loc:(l = Parse_ast.Unknown) n = A_aux (A_nexp n, l)
let arg_typ ?loc:(l = Parse_ast.Unknown) typ = A_aux (A_typ typ, l)
let arg_bool ?loc:(l = Parse_ast.Unknown) nc = A_aux (A_bool nc, l)

let arg_kopt (KOpt_aux (KOpt_kind (K_aux (k, _), v), _)) =
  match k with K_int -> arg_nexp (nvar v) | K_bool -> arg_bool (nc_var v) | K_type -> arg_typ (mk_typ (Typ_var v))

let nc_not nc = mk_nc (NC_app (mk_id "not", [arg_bool nc]))

let mk_typschm typq typ = TypSchm_aux (TypSchm_ts (typq, typ), Parse_ast.Unknown)

let mk_typquant qis = TypQ_aux (TypQ_tq qis, Parse_ast.Unknown)

let mk_fexp id exp = FE_aux (FE_fexp (id, exp), no_annot)

type effect = bool

let no_effect = false
let monadic_effect = true

let quant_add qi typq =
  match (qi, typq) with
  | QI_aux (QI_constraint (NC_aux (NC_true, _)), _), _ -> typq
  | QI_aux (QI_id _, _), TypQ_aux (TypQ_tq qis, l) -> TypQ_aux (TypQ_tq (qi :: qis), l)
  | QI_aux (QI_constraint _, _), TypQ_aux (TypQ_tq qis, l) -> TypQ_aux (TypQ_tq (qis @ [qi]), l)
  | _, TypQ_aux (TypQ_no_forall, l) -> TypQ_aux (TypQ_tq [qi], l)

let quant_items : typquant -> quant_item list = function
  | TypQ_aux (TypQ_tq qis, _) -> qis
  | TypQ_aux (TypQ_no_forall, _) -> []

let quant_kopts typq =
  let qi_kopt = function QI_aux (QI_id kopt, _) -> [kopt] | QI_aux _ -> [] in
  quant_items typq |> List.map qi_kopt |> List.concat

let quant_split typq =
  let qi_kopt = function QI_aux (QI_id kopt, _) -> [kopt] | _ -> [] in
  let qi_nc = function QI_aux (QI_constraint nc, _) -> [nc] | _ -> [] in
  let qis = quant_items typq in
  (List.concat (List.map qi_kopt qis), List.concat (List.map qi_nc qis))

let quant_map_items f = function
  | TypQ_aux (TypQ_no_forall, l) -> TypQ_aux (TypQ_no_forall, l)
  | TypQ_aux (TypQ_tq qis, l) -> TypQ_aux (TypQ_tq (List.map f qis), l)

let is_quant_kopt = function QI_aux (QI_id _, _) -> true | _ -> false

let is_quant_constraint = function QI_aux (QI_constraint _, _) -> true | _ -> false

let unaux_nexp (Nexp_aux (nexp, _)) = nexp
let unaux_typ (Typ_aux (typ, _)) = typ
let unaux_kind (K_aux (k, _)) = k
let unaux_constraint (NC_aux (nc, _)) = nc

let rec insert_subrange ms (n1, n2) =
  match ms with
  | (m1, m2) :: ms ->
      if Big_int.equal n2 (Big_int.succ m1) then (n1, m2) :: ms
      else if Big_int.greater n2 m1 then (n1, n2) :: (m1, m2) :: ms
      else if Big_int.equal m2 (Big_int.succ n1) then insert_subrange ms (m1, n2)
      else (m1, m2) :: insert_subrange ms (n1, n2)
  | [] -> [(n1, n2)]

let insert_subranges ns ms = List.fold_left insert_subrange ns ms

let rec pattern_vector_subranges (P_aux (aux, _)) =
  match aux with
  | P_vector_subrange (id, n, m) when Big_int.greater n m -> Bindings.singleton id [(n, m)]
  | P_vector_subrange (id, n, m) -> Bindings.singleton id [(m, n)]
  | P_typ (_, pat) | P_var (pat, _) | P_as (pat, _) | P_not pat -> pattern_vector_subranges pat
  | P_cons (pat1, pat2) | P_or (pat1, pat2) ->
      Bindings.union
        (fun _ r1 r2 -> Some (insert_subranges r1 r2))
        (pattern_vector_subranges pat1) (pattern_vector_subranges pat2)
  | P_tuple pats | P_vector_concat pats | P_app (_, pats) | P_list pats | P_string_append pats | P_vector pats ->
      List.fold_left
        (fun ranges pat ->
          Bindings.union (fun _ r1 r2 -> Some (insert_subranges r1 r2)) ranges (pattern_vector_subranges pat)
        )
        Bindings.empty pats
  | P_struct (fpats, _) ->
      let pats = List.map snd fpats in
      List.fold_left
        (fun ranges pat ->
          Bindings.union (fun _ r1 r2 -> Some (insert_subranges r1 r2)) ranges (pattern_vector_subranges pat)
        )
        Bindings.empty pats
  | P_id _ | P_lit _ | P_wild -> Bindings.empty

let rec map_exp_annot f (E_aux (exp, annot)) = E_aux (map_exp_annot_aux f exp, f annot)

and map_exp_annot_aux f = function
  | E_block xs -> E_block (List.map (map_exp_annot f) xs)
  | E_id id -> E_id id
  | E_ref id -> E_ref id
  | E_lit lit -> E_lit lit
  | E_typ (typ, exp) -> E_typ (typ, map_exp_annot f exp)
  | E_app (id, xs) -> E_app (id, List.map (map_exp_annot f) xs)
  | E_app_infix (x, op, y) -> E_app_infix (map_exp_annot f x, op, map_exp_annot f y)
  | E_tuple xs -> E_tuple (List.map (map_exp_annot f) xs)
  | E_if (cond, t, e) -> E_if (map_exp_annot f cond, map_exp_annot f t, map_exp_annot f e)
  | E_for (v, e1, e2, e3, o, e4) ->
      E_for (v, map_exp_annot f e1, map_exp_annot f e2, map_exp_annot f e3, o, map_exp_annot f e4)
  | E_loop (loop_type, measure, e1, e2) ->
      E_loop (loop_type, map_measure_annot f measure, map_exp_annot f e1, map_exp_annot f e2)
  | E_vector exps -> E_vector (List.map (map_exp_annot f) exps)
  | E_vector_access (exp1, exp2) -> E_vector_access (map_exp_annot f exp1, map_exp_annot f exp2)
  | E_vector_subrange (exp1, exp2, exp3) ->
      E_vector_subrange (map_exp_annot f exp1, map_exp_annot f exp2, map_exp_annot f exp3)
  | E_vector_update (exp1, exp2, exp3) ->
      E_vector_update (map_exp_annot f exp1, map_exp_annot f exp2, map_exp_annot f exp3)
  | E_vector_update_subrange (exp1, exp2, exp3, exp4) ->
      E_vector_update_subrange (map_exp_annot f exp1, map_exp_annot f exp2, map_exp_annot f exp3, map_exp_annot f exp4)
  | E_vector_append (exp1, exp2) -> E_vector_append (map_exp_annot f exp1, map_exp_annot f exp2)
  | E_list xs -> E_list (List.map (map_exp_annot f) xs)
  | E_cons (exp1, exp2) -> E_cons (map_exp_annot f exp1, map_exp_annot f exp2)
  | E_struct fexps -> E_struct (List.map (map_fexp_annot f) fexps)
  | E_struct_update (exp, fexps) -> E_struct_update (map_exp_annot f exp, List.map (map_fexp_annot f) fexps)
  | E_field (exp, id) -> E_field (map_exp_annot f exp, id)
  | E_match (exp, cases) -> E_match (map_exp_annot f exp, List.map (map_pexp_annot f) cases)
  | E_try (exp, cases) -> E_try (map_exp_annot f exp, List.map (map_pexp_annot f) cases)
  | E_let (letbind, exp) -> E_let (map_letbind_annot f letbind, map_exp_annot f exp)
  | E_assign (lexp, exp) -> E_assign (map_lexp_annot f lexp, map_exp_annot f exp)
  | E_sizeof nexp -> E_sizeof nexp
  | E_constraint nc -> E_constraint nc
  | E_exit exp -> E_exit (map_exp_annot f exp)
  | E_throw exp -> E_throw (map_exp_annot f exp)
  | E_return exp -> E_return (map_exp_annot f exp)
  | E_assert (test, msg) -> E_assert (map_exp_annot f test, map_exp_annot f msg)
  | E_internal_value v -> E_internal_value v
  | E_var (lexp, exp1, exp2) -> E_var (map_lexp_annot f lexp, map_exp_annot f exp1, map_exp_annot f exp2)
  | E_internal_plet (pat, exp1, exp2) ->
      E_internal_plet (map_pat_annot f pat, map_exp_annot f exp1, map_exp_annot f exp2)
  | E_internal_return exp -> E_internal_return (map_exp_annot f exp)
  | E_internal_assume (nc, exp) -> E_internal_assume (nc, map_exp_annot f exp)

and map_measure_annot f (Measure_aux (m, l)) = Measure_aux (map_measure_annot_aux f m, l)

and map_measure_annot_aux f = function
  | Measure_none -> Measure_none
  | Measure_some exp -> Measure_some (map_exp_annot f exp)

and map_fexp_annot f (FE_aux (FE_fexp (id, exp), annot)) = FE_aux (FE_fexp (id, map_exp_annot f exp), f annot)

and map_pexp_annot f (Pat_aux (pexp, annot)) = Pat_aux (map_pexp_annot_aux f pexp, f annot)

and map_pexp_annot_aux f = function
  | Pat_exp (pat, exp) -> Pat_exp (map_pat_annot f pat, map_exp_annot f exp)
  | Pat_when (pat, guard, exp) -> Pat_when (map_pat_annot f pat, map_exp_annot f guard, map_exp_annot f exp)

and map_pat_annot f (P_aux (pat, annot)) = P_aux (map_pat_annot_aux f pat, f annot)

and map_pat_annot_aux f = function
  | P_lit lit -> P_lit lit
  | P_wild -> P_wild
  | P_or (pat1, pat2) -> P_or (map_pat_annot f pat1, map_pat_annot f pat2)
  | P_not pat -> P_not (map_pat_annot f pat)
  | P_as (pat, id) -> P_as (map_pat_annot f pat, id)
  | P_typ (typ, pat) -> P_typ (typ, map_pat_annot f pat)
  | P_id id -> P_id id
  | P_var (pat, tpat) -> P_var (map_pat_annot f pat, tpat)
  | P_app (id, pats) -> P_app (id, List.map (map_pat_annot f) pats)
  | P_tuple pats -> P_tuple (List.map (map_pat_annot f) pats)
  | P_list pats -> P_list (List.map (map_pat_annot f) pats)
  | P_vector_concat pats -> P_vector_concat (List.map (map_pat_annot f) pats)
  | P_vector_subrange (id, n, m) -> P_vector_subrange (id, n, m)
  | P_vector pats -> P_vector (List.map (map_pat_annot f) pats)
  | P_cons (pat1, pat2) -> P_cons (map_pat_annot f pat1, map_pat_annot f pat2)
  | P_string_append pats -> P_string_append (List.map (map_pat_annot f) pats)
  | P_struct (fpats, fwild) -> P_struct (List.map (fun (field, pat) -> (field, map_pat_annot f pat)) fpats, fwild)

and map_mpexp_annot f (MPat_aux (mpexp, annot)) = MPat_aux (map_mpexp_annot_aux f mpexp, f annot)

and map_mpexp_annot_aux f = function
  | MPat_pat mpat -> MPat_pat (map_mpat_annot f mpat)
  | MPat_when (mpat, guard) -> MPat_when (map_mpat_annot f mpat, map_exp_annot f guard)

and map_mapcl_annot f = function
  | MCL_aux (MCL_bidir (mpexp1, mpexp2), annot) ->
      MCL_aux (MCL_bidir (map_mpexp_annot f mpexp1, map_mpexp_annot f mpexp2), map_clause_annot f annot)
  | MCL_aux (MCL_forwards (mpexp, exp), annot) ->
      MCL_aux (MCL_forwards (map_mpexp_annot f mpexp, map_exp_annot f exp), map_clause_annot f annot)
  | MCL_aux (MCL_backwards (mpexp, exp), annot) ->
      MCL_aux (MCL_backwards (map_mpexp_annot f mpexp, map_exp_annot f exp), map_clause_annot f annot)

and map_mpat_annot f (MP_aux (mpat, annot)) = MP_aux (map_mpat_annot_aux f mpat, f annot)

and map_mpat_annot_aux f = function
  | MP_lit lit -> MP_lit lit
  | MP_id id -> MP_id id
  | MP_app (id, mpats) -> MP_app (id, List.map (map_mpat_annot f) mpats)
  | MP_tuple mpats -> MP_tuple (List.map (map_mpat_annot f) mpats)
  | MP_list mpats -> MP_list (List.map (map_mpat_annot f) mpats)
  | MP_vector_concat mpats -> MP_vector_concat (List.map (map_mpat_annot f) mpats)
  | MP_vector mpats -> MP_vector (List.map (map_mpat_annot f) mpats)
  | MP_vector_subrange (id, n, m) -> MP_vector_subrange (id, n, m)
  | MP_cons (mpat1, mpat2) -> MP_cons (map_mpat_annot f mpat1, map_mpat_annot f mpat2)
  | MP_string_append mpats -> MP_string_append (List.map (map_mpat_annot f) mpats)
  | MP_typ (mpat, typ) -> MP_typ (map_mpat_annot f mpat, typ)
  | MP_as (mpat, id) -> MP_as (map_mpat_annot f mpat, id)
  | MP_struct fmpats -> MP_struct (List.map (fun (field, mpat) -> (field, map_mpat_annot f mpat)) fmpats)

and map_letbind_annot f (LB_aux (lb, annot)) = LB_aux (map_letbind_annot_aux f lb, f annot)

and map_letbind_annot_aux f = function LB_val (pat, exp) -> LB_val (map_pat_annot f pat, map_exp_annot f exp)

and map_lexp_annot f (LE_aux (lexp, annot)) = LE_aux (map_lexp_annot_aux f lexp, f annot)

and map_lexp_annot_aux f = function
  | LE_id id -> LE_id id
  | LE_deref exp -> LE_deref (map_exp_annot f exp)
  | LE_app (id, exps) -> LE_app (id, List.map (map_exp_annot f) exps)
  | LE_typ (typ, id) -> LE_typ (typ, id)
  | LE_tuple lexps -> LE_tuple (List.map (map_lexp_annot f) lexps)
  | LE_vector_concat lexps -> LE_vector_concat (List.map (map_lexp_annot f) lexps)
  | LE_vector (lexp, exp) -> LE_vector (map_lexp_annot f lexp, map_exp_annot f exp)
  | LE_vector_range (lexp, exp1, exp2) ->
      LE_vector_range (map_lexp_annot f lexp, map_exp_annot f exp1, map_exp_annot f exp2)
  | LE_field (lexp, id) -> LE_field (map_lexp_annot f lexp, id)

and map_typedef_annot f = function TD_aux (td_aux, annot) -> TD_aux (td_aux, f annot)

and map_fundef_annot f = function FD_aux (fd_aux, annot) -> FD_aux (map_fundef_annot_aux f fd_aux, f annot)

and map_fundef_annot_aux f = function
  | FD_function (rec_opt, tannot_opt, funcls) ->
      FD_function (map_recopt_annot f rec_opt, tannot_opt, List.map (map_funcl_annot f) funcls)

and map_funcl_annot f = function FCL_aux (fcl, annot) -> FCL_aux (map_funcl_annot_aux f fcl, map_clause_annot f annot)

and map_funcl_annot_aux f = function FCL_funcl (id, pexp) -> FCL_funcl (id, map_pexp_annot f pexp)

and map_recopt_annot f = function Rec_aux (rec_aux, l) -> Rec_aux (map_recopt_annot_aux f rec_aux, l)

and map_recopt_annot_aux f = function
  | Rec_nonrec -> Rec_nonrec
  | Rec_rec -> Rec_rec
  | Rec_measure (pat, exp) -> Rec_measure (map_pat_annot f pat, map_exp_annot f exp)

and map_mapdef_annot f = function MD_aux (md_aux, annot) -> MD_aux (map_mapdef_annot_aux f md_aux, f annot)

and map_mapdef_annot_aux f = function
  | MD_mapping (id, tannot_opt, mapcls) -> MD_mapping (id, tannot_opt, List.map (map_mapcl_annot f) mapcls)

and map_valspec_annot f = function VS_aux (vs_aux, annot) -> VS_aux (vs_aux, f annot)

and map_scattered_annot f = function SD_aux (sd_aux, annot) -> SD_aux (map_scattered_annot_aux f sd_aux, f annot)

and map_scattered_annot_aux f = function
  | SD_function (rec_opt, tannot_opt, name) -> SD_function (map_recopt_annot f rec_opt, tannot_opt, name)
  | SD_funcl fcl -> SD_funcl (map_funcl_annot f fcl)
  | SD_variant (id, typq) -> SD_variant (id, typq)
  | SD_unioncl (id, tu) -> SD_unioncl (id, tu)
  | SD_internal_unioncl_record (id, record_id, typq, fields) -> SD_internal_unioncl_record (id, record_id, typq, fields)
  | SD_mapping (id, tannot_opt) -> SD_mapping (id, tannot_opt)
  | SD_mapcl (id, mcl) -> SD_mapcl (id, map_mapcl_annot f mcl)
  | SD_end id -> SD_end id
  | SD_enum id -> SD_enum id
  | SD_enumcl (id, member) -> SD_enumcl (id, member)

and map_register_annot f = function DEC_aux (dec_aux, annot) -> DEC_aux (map_register_annot_aux f dec_aux, f annot)

and map_register_annot_aux f = function
  | DEC_reg (typ, id, None) -> DEC_reg (typ, id, None)
  | DEC_reg (typ, id, Some exp) -> DEC_reg (typ, id, Some (map_exp_annot f exp))

and map_def_annot f (DEF_aux (aux, annot)) =
  let aux =
    match aux with
    | DEF_type td -> DEF_type (map_typedef_annot f td)
    | DEF_fundef fd -> DEF_fundef (map_fundef_annot f fd)
    | DEF_mapdef md -> DEF_mapdef (map_mapdef_annot f md)
    | DEF_outcome (outcome_spec, defs) -> DEF_outcome (outcome_spec, List.map (map_def_annot f) defs)
    | DEF_instantiation (IN_aux (IN_id id, annot), substs) -> DEF_instantiation (IN_aux (IN_id id, f annot), substs)
    | DEF_impl funcl -> DEF_impl (map_funcl_annot f funcl)
    | DEF_let lb -> DEF_let (map_letbind_annot f lb)
    | DEF_val vs -> DEF_val (map_valspec_annot f vs)
    | DEF_fixity (prec, n, id) -> DEF_fixity (prec, n, id)
    | DEF_overload (name, overloads) -> DEF_overload (name, overloads)
    | DEF_default ds -> DEF_default ds
    | DEF_scattered sd -> DEF_scattered (map_scattered_annot f sd)
    | DEF_measure (id, pat, exp) -> DEF_measure (id, map_pat_annot f pat, map_exp_annot f exp)
    | DEF_loop_measures (id, measures) -> DEF_loop_measures (id, List.map (map_loop_measure_annot f) measures)
    | DEF_register ds -> DEF_register (map_register_annot f ds)
    | DEF_internal_mutrec fds -> DEF_internal_mutrec (List.map (map_fundef_annot f) fds)
    | DEF_pragma (name, arg, l) -> DEF_pragma (name, arg, l)
  in
  DEF_aux (aux, annot)

and map_ast_annot f ast = { ast with defs = List.map (map_def_annot f) ast.defs }

and map_loop_measure_annot f = function Loop (loop, exp) -> Loop (loop, map_exp_annot f exp)

let def_loc (DEF_aux (_, annot)) = annot.loc

let deinfix = function Id_aux (Id v, l) -> Id_aux (Operator v, l) | Id_aux (Operator v, l) -> Id_aux (Operator v, l)

let id_of_kid = function Kid_aux (Var v, l) -> Id_aux (Id (String.sub v 1 (String.length v - 1)), l)

let kid_of_id = function Id_aux (Id v, l) -> Kid_aux (Var ("'" ^ v), l) | Id_aux (Operator _, _) -> assert false

let prepend_id str = function
  | Id_aux (Id v, l) -> Id_aux (Id (str ^ v), l)
  | Id_aux (Operator v, l) -> Id_aux (Operator (str ^ v), l)

let append_id id str =
  match id with Id_aux (Id v, l) -> Id_aux (Id (v ^ str), l) | Id_aux (Operator v, l) -> Id_aux (Operator (v ^ str), l)

let prepend_kid str = function
  | Kid_aux (Var v, l) -> Kid_aux (Var ("'" ^ str ^ String.sub v 1 (String.length v - 1)), l)

let string_of_kind_aux = function K_type -> "Type" | K_int -> "Int" | K_bool -> "Bool"

let string_of_kind (K_aux (k, _)) = string_of_kind_aux k

let string_of_kinded_id (KOpt_aux (KOpt_kind (k, kid), _)) = "(" ^ string_of_kid kid ^ " : " ^ string_of_kind k ^ ")"

let rec string_of_nexp = function Nexp_aux (nexp, _) -> string_of_nexp_aux nexp

and string_of_nexp_aux = function
  | Nexp_id id -> string_of_id id
  | Nexp_var kid -> string_of_kid kid
  | Nexp_constant c -> Big_int.to_string c
  | Nexp_times (n1, n2) -> "(" ^ string_of_nexp n1 ^ " * " ^ string_of_nexp n2 ^ ")"
  | Nexp_sum (n1, n2) -> "(" ^ string_of_nexp n1 ^ " + " ^ string_of_nexp n2 ^ ")"
  | Nexp_minus (n1, n2) -> "(" ^ string_of_nexp n1 ^ " - " ^ string_of_nexp n2 ^ ")"
  | Nexp_app (id, nexps) -> string_of_id id ^ "(" ^ string_of_list ", " string_of_nexp nexps ^ ")"
  | Nexp_exp n -> "2 ^ " ^ string_of_nexp n
  | Nexp_neg n -> "- " ^ string_of_nexp n

let rec string_of_typ = function Typ_aux (typ, _) -> string_of_typ_aux typ

and string_of_typ_aux = function
  | Typ_internal_unknown -> "<UNKNOWN TYPE>"
  | Typ_id id -> string_of_id id
  | Typ_var kid -> string_of_kid kid
  | Typ_tuple typs -> "(" ^ string_of_list ", " string_of_typ typs ^ ")"
  | Typ_app (id, args) when Id.compare id (mk_id "atom") = 0 ->
      "int(" ^ string_of_list ", " string_of_typ_arg args ^ ")"
  | Typ_app (id, args) when Id.compare id (mk_id "atom_bool") = 0 ->
      "bool(" ^ string_of_list ", " string_of_typ_arg args ^ ")"
  | Typ_app (id, args) -> string_of_id id ^ "(" ^ string_of_list ", " string_of_typ_arg args ^ ")"
  | Typ_fn ([typ_arg], typ_ret) -> string_of_typ typ_arg ^ " -> " ^ string_of_typ typ_ret
  | Typ_fn (typ_args, typ_ret) -> "(" ^ string_of_list ", " string_of_typ typ_args ^ ") -> " ^ string_of_typ typ_ret
  | Typ_bidir (typ1, typ2) -> string_of_typ typ1 ^ " <-> " ^ string_of_typ typ2
  | Typ_exist (kids, nc, typ) ->
      "{"
      ^ string_of_list " " string_of_kinded_id kids
      ^ ", " ^ string_of_n_constraint nc ^ ". " ^ string_of_typ typ ^ "}"

and string_of_typ_arg = function A_aux (typ_arg, _) -> string_of_typ_arg_aux typ_arg

and string_of_typ_arg_aux = function
  | A_nexp n -> string_of_nexp n
  | A_typ typ -> string_of_typ typ
  | A_bool nc -> string_of_n_constraint nc

and string_of_n_constraint = function
  | NC_aux (NC_equal (n1, n2), _) -> string_of_nexp n1 ^ " == " ^ string_of_nexp n2
  | NC_aux (NC_not_equal (n1, n2), _) -> string_of_nexp n1 ^ " != " ^ string_of_nexp n2
  | NC_aux (NC_bounded_ge (n1, n2), _) -> string_of_nexp n1 ^ " >= " ^ string_of_nexp n2
  | NC_aux (NC_bounded_gt (n1, n2), _) -> string_of_nexp n1 ^ " > " ^ string_of_nexp n2
  | NC_aux (NC_bounded_le (n1, n2), _) -> string_of_nexp n1 ^ " <= " ^ string_of_nexp n2
  | NC_aux (NC_bounded_lt (n1, n2), _) -> string_of_nexp n1 ^ " < " ^ string_of_nexp n2
  | NC_aux (NC_or (nc1, nc2), _) -> "(" ^ string_of_n_constraint nc1 ^ " | " ^ string_of_n_constraint nc2 ^ ")"
  | NC_aux (NC_and (nc1, nc2), _) -> "(" ^ string_of_n_constraint nc1 ^ " & " ^ string_of_n_constraint nc2 ^ ")"
  | NC_aux (NC_set (kid, ns), _) -> string_of_kid kid ^ " in {" ^ string_of_list ", " Big_int.to_string ns ^ "}"
  | NC_aux (NC_app (Id_aux (Operator op, _), [arg1; arg2]), _) ->
      "(" ^ string_of_typ_arg arg1 ^ " " ^ op ^ " " ^ string_of_typ_arg arg2 ^ ")"
  | NC_aux (NC_app (id, args), _) -> string_of_id id ^ "(" ^ string_of_list ", " string_of_typ_arg args ^ ")"
  | NC_aux (NC_var v, _) -> string_of_kid v
  | NC_aux (NC_true, _) -> "true"
  | NC_aux (NC_false, _) -> "false"

let string_of_kinded_id (KOpt_aux (KOpt_kind (k, kid), _)) = "(" ^ string_of_kid kid ^ " : " ^ string_of_kind k ^ ")"

let string_of_quant_item_aux = function
  | QI_id kopt -> string_of_kinded_id kopt
  | QI_constraint constr -> string_of_n_constraint constr

let string_of_quant_item = function QI_aux (qi, _) -> string_of_quant_item_aux qi

let string_of_typquant_aux = function
  | TypQ_tq quants -> "forall " ^ string_of_list ", " string_of_quant_item quants
  | TypQ_no_forall -> ""

let string_of_typquant = function TypQ_aux (quant, _) -> string_of_typquant_aux quant

let string_of_typschm (TypSchm_aux (TypSchm_ts (quant, typ), _)) = string_of_typquant quant ^ ". " ^ string_of_typ typ
let string_of_lit (L_aux (lit, _)) =
  match lit with
  | L_unit -> "()"
  | L_zero -> "bitzero"
  | L_one -> "bitone"
  | L_true -> "true"
  | L_false -> "false"
  | L_num n -> Big_int.to_string n
  | L_hex n -> "0x" ^ n
  | L_bin n -> "0b" ^ n
  | L_undef -> "undefined"
  | L_real r -> r
  | L_string str -> "\"" ^ str ^ "\""

let string_of_order (Ord_aux (aux, _)) = match aux with Ord_inc -> "inc" | Ord_dec -> "dec"

let rec string_of_exp (E_aux (exp, _)) =
  match exp with
  | E_block exps -> "{ " ^ string_of_list "; " string_of_exp exps ^ " }"
  | E_id v -> string_of_id v
  | E_ref id -> "ref " ^ string_of_id id
  | E_sizeof nexp -> "sizeof " ^ string_of_nexp nexp
  | E_constraint nc -> "constraint(" ^ string_of_n_constraint nc ^ ")"
  | E_lit lit -> string_of_lit lit
  | E_return exp -> "return " ^ string_of_exp exp
  | E_app (f, [E_aux (E_lit (L_aux (L_unit, _)), _)]) -> string_of_id f ^ "()"
  | E_app (f, args) -> string_of_id f ^ "(" ^ string_of_list ", " string_of_exp args ^ ")"
  | E_app_infix (x, op, y) -> "(" ^ string_of_exp x ^ " " ^ string_of_id op ^ " " ^ string_of_exp y ^ ")"
  | E_tuple exps -> "(" ^ string_of_list ", " string_of_exp exps ^ ")"
  | E_match (exp, cases) -> "match " ^ string_of_exp exp ^ " { " ^ string_of_list ", " string_of_pexp cases ^ " }"
  | E_try (exp, cases) ->
      "try " ^ string_of_exp exp ^ " catch { case " ^ string_of_list " case " string_of_pexp cases ^ "}"
  | E_let (letbind, exp) -> "let " ^ string_of_letbind letbind ^ " in " ^ string_of_exp exp
  | E_assign (lexp, bind) -> string_of_lexp lexp ^ " = " ^ string_of_exp bind
  | E_typ (typ, exp) -> string_of_exp exp ^ " : " ^ string_of_typ typ
  | E_vector vec -> "[" ^ string_of_list ", " string_of_exp vec ^ "]"
  | E_vector_access (v, n) -> string_of_exp v ^ "[" ^ string_of_exp n ^ "]"
  | E_vector_update (v, n, exp) -> "[" ^ string_of_exp v ^ " with " ^ string_of_exp n ^ " = " ^ string_of_exp exp ^ "]"
  | E_vector_update_subrange (v, n, m, exp) ->
      "[" ^ string_of_exp v ^ " with " ^ string_of_exp n ^ " .. " ^ string_of_exp m ^ " = " ^ string_of_exp exp ^ "]"
  | E_vector_subrange (v, n1, n2) -> string_of_exp v ^ "[" ^ string_of_exp n1 ^ " .. " ^ string_of_exp n2 ^ "]"
  | E_vector_append (v1, v2) -> string_of_exp v1 ^ " @ " ^ string_of_exp v2
  | E_if (cond, then_branch, else_branch) ->
      "if " ^ string_of_exp cond ^ " then " ^ string_of_exp then_branch ^ " else " ^ string_of_exp else_branch
  | E_field (exp, id) -> string_of_exp exp ^ "." ^ string_of_id id
  | E_for (id, f, t, u, ord, body) ->
      "foreach (" ^ string_of_id id ^ " from " ^ string_of_exp f ^ " to " ^ string_of_exp t ^ " by " ^ string_of_exp u
      ^ " order " ^ string_of_order ord ^ ") { " ^ string_of_exp body
  | E_loop (While, measure, cond, body) ->
      "while " ^ string_of_measure measure ^ string_of_exp cond ^ " do " ^ string_of_exp body
  | E_loop (Until, measure, cond, body) ->
      "repeat " ^ string_of_measure measure ^ string_of_exp body ^ " until " ^ string_of_exp cond
  | E_assert (test, msg) -> "assert(" ^ string_of_exp test ^ ", " ^ string_of_exp msg ^ ")"
  | E_exit exp -> "exit " ^ string_of_exp exp
  | E_throw exp -> "throw " ^ string_of_exp exp
  | E_cons (x, xs) -> string_of_exp x ^ " :: " ^ string_of_exp xs
  | E_list xs -> "[|" ^ string_of_list ", " string_of_exp xs ^ "|]"
  | E_struct_update (exp, fexps) ->
      "struct { " ^ string_of_exp exp ^ " with " ^ string_of_list "; " string_of_fexp fexps ^ " }"
  | E_struct fexps -> "struct { " ^ string_of_list "; " string_of_fexp fexps ^ " }"
  | E_var (lexp, binding, exp) ->
      "var " ^ string_of_lexp lexp ^ " = " ^ string_of_exp binding ^ " in " ^ string_of_exp exp
  | E_internal_return exp -> "internal_return (" ^ string_of_exp exp ^ ")"
  | E_internal_plet (pat, exp, body) ->
      "internal_plet " ^ string_of_pat pat ^ " = " ^ string_of_exp exp ^ " in " ^ string_of_exp body
  | E_internal_value v -> "INTERNAL_VALUE(" ^ Value.string_of_value v ^ ")"
  | E_internal_assume (nc, exp) -> "internal_assume " ^ string_of_n_constraint nc ^ " in " ^ string_of_exp exp

and string_of_measure (Measure_aux (m, _)) =
  match m with Measure_none -> "" | Measure_some exp -> "termination_measure { " ^ string_of_exp exp ^ "}"

and string_of_fexp (FE_aux (FE_fexp (field, exp), _)) = string_of_id field ^ " = " ^ string_of_exp exp

and string_of_pexp (Pat_aux (pexp, _)) =
  match pexp with
  | Pat_exp (pat, exp) -> string_of_pat pat ^ " => " ^ string_of_exp exp
  | Pat_when (pat, guard, exp) -> string_of_pat pat ^ " if " ^ string_of_exp guard ^ " => " ^ string_of_exp exp

and string_of_typ_pat (TP_aux (tpat_aux, _)) =
  match tpat_aux with
  | TP_wild -> "_"
  | TP_var kid -> string_of_kid kid
  | TP_app (f, tpats) -> string_of_id f ^ "(" ^ string_of_list ", " string_of_typ_pat tpats ^ ")"

and string_of_pat (P_aux (pat, _)) =
  match pat with
  | P_lit lit -> string_of_lit lit
  | P_wild -> "_"
  | P_or (pat1, pat2) -> "(" ^ string_of_pat pat1 ^ " | " ^ string_of_pat pat2 ^ ")"
  | P_not pat -> "(!" ^ string_of_pat pat ^ ")"
  | P_id v -> string_of_id v
  | P_var (pat, tpat) -> string_of_pat pat ^ " as " ^ string_of_typ_pat tpat
  | P_typ (typ, pat) -> string_of_pat pat ^ " : " ^ string_of_typ typ
  | P_tuple pats -> "(" ^ string_of_list ", " string_of_pat pats ^ ")"
  | P_app (f, pats) -> string_of_id f ^ "(" ^ string_of_list ", " string_of_pat pats ^ ")"
  | P_cons (pat1, pat2) -> string_of_pat pat1 ^ " :: " ^ string_of_pat pat2
  | P_list pats -> "[||" ^ string_of_list "," string_of_pat pats ^ "||]"
  | P_vector_concat pats -> string_of_list " @ " string_of_pat pats
  | P_vector_subrange (id, n, m) ->
      if Big_int.equal n m then string_of_id id ^ "[" ^ Big_int.to_string n ^ "]"
      else string_of_id id ^ "[" ^ Big_int.to_string n ^ ".." ^ Big_int.to_string m ^ "]"
  | P_vector pats -> "[" ^ string_of_list ", " string_of_pat pats ^ "]"
  | P_as (pat, id) -> "(" ^ string_of_pat pat ^ " as " ^ string_of_id id ^ ")"
  | P_string_append [] -> "\"\""
  | P_string_append pats -> string_of_list " ^ " string_of_pat pats
  | P_struct (fpats, fwild) ->
      let wild_string = function FP_wild _ -> ", _" | FP_no_wild -> "" in
      "struct { "
      ^ Util.string_of_list ", " (fun (field, pat) -> string_of_id field ^ " = " ^ string_of_pat pat) fpats
      ^ wild_string fwild ^ " }"

and string_of_mpat (MP_aux (pat, _)) =
  match pat with
  | MP_lit lit -> string_of_lit lit
  | MP_id v -> string_of_id v
  | MP_tuple pats -> "(" ^ string_of_list ", " string_of_mpat pats ^ ")"
  | MP_app (f, pats) -> string_of_id f ^ "(" ^ string_of_list ", " string_of_mpat pats ^ ")"
  | MP_cons (pat1, pat2) -> string_of_mpat pat1 ^ " :: " ^ string_of_mpat pat2
  | MP_list pats -> "[||" ^ string_of_list "," string_of_mpat pats ^ "||]"
  | MP_vector_concat pats -> string_of_list " @ " string_of_mpat pats
  | MP_vector pats -> "[" ^ string_of_list ", " string_of_mpat pats ^ "]"
  | MP_vector_subrange (id, n, m) -> string_of_id id ^ "[" ^ Big_int.to_string n ^ " .. " ^ Big_int.to_string m ^ "]"
  | MP_string_append pats -> string_of_list " ^ " string_of_mpat pats
  | MP_typ (mpat, typ) -> "(" ^ string_of_mpat mpat ^ " : " ^ string_of_typ typ ^ ")"
  | MP_as (mpat, id) -> "((" ^ string_of_mpat mpat ^ ") as " ^ string_of_id id ^ ")"
  | MP_struct fmpats ->
      "struct { "
      ^ Util.string_of_list ", " (fun (field, mpat) -> string_of_id field ^ " = " ^ string_of_mpat mpat) fmpats
      ^ " }"

and string_of_lexp (LE_aux (lexp, _)) =
  match lexp with
  | LE_id v -> string_of_id v
  | LE_deref exp -> "*(" ^ string_of_exp exp ^ ")"
  | LE_typ (typ, v) -> string_of_id v ^ " : " ^ string_of_typ typ
  | LE_tuple lexps -> "(" ^ string_of_list ", " string_of_lexp lexps ^ ")"
  | LE_vector (lexp, exp) -> string_of_lexp lexp ^ "[" ^ string_of_exp exp ^ "]"
  | LE_vector_range (lexp, exp1, exp2) ->
      string_of_lexp lexp ^ "[" ^ string_of_exp exp1 ^ " .. " ^ string_of_exp exp2 ^ "]"
  | LE_vector_concat lexps -> string_of_list " @ " string_of_lexp lexps
  | LE_field (lexp, id) -> string_of_lexp lexp ^ "." ^ string_of_id id
  | LE_app (f, xs) -> string_of_id f ^ "(" ^ string_of_list ", " string_of_exp xs ^ ")"

and string_of_letbind (LB_aux (lb, _)) =
  match lb with LB_val (pat, exp) -> string_of_pat pat ^ " = " ^ string_of_exp exp

let rec string_of_index_range (BF_aux (ir, _)) =
  match ir with
  | BF_single n -> string_of_nexp n
  | BF_range (n, m) -> string_of_nexp n ^ " .. " ^ string_of_nexp m
  | BF_concat (ir1, ir2) -> "(" ^ string_of_index_range ir1 ^ " @ " ^ string_of_index_range ir2 ^ ")"

let rec pat_ids (P_aux (pat_aux, _)) =
  match pat_aux with
  | P_lit _ | P_wild -> IdSet.empty
  | P_id id | P_vector_subrange (id, _, _) -> IdSet.singleton id
  | P_as (pat, id) -> IdSet.add id (pat_ids pat)
  | P_or (pat1, pat2) -> IdSet.union (pat_ids pat1) (pat_ids pat2)
  | P_not pat -> pat_ids pat
  | P_var (pat, _) | P_typ (_, pat) -> pat_ids pat
  | P_app (_, pats) | P_tuple pats | P_vector pats | P_vector_concat pats | P_list pats ->
      List.fold_left IdSet.union IdSet.empty (List.map pat_ids pats)
  | P_cons (pat1, pat2) -> IdSet.union (pat_ids pat1) (pat_ids pat2)
  | P_string_append pats -> List.fold_left IdSet.union IdSet.empty (List.map pat_ids pats)
  | P_struct (fpats, _) -> List.fold_left IdSet.union IdSet.empty (List.map (fun (_, pat) -> pat_ids pat) fpats)

let id_of_fundef (FD_aux (FD_function (_, _, funcls), (l, _))) =
  match
    List.fold_right
      (fun (FCL_aux (FCL_funcl (id, _), _)) id' ->
        match id' with
        | Some id' ->
            if string_of_id id' = string_of_id id then Some id'
            else
              raise
                (Reporting.err_typ l
                   ("Function declaration expects all definitions to have the same name, " ^ string_of_id id
                  ^ " differs from other definitions of " ^ string_of_id id'
                   )
                )
        | None -> Some id
      )
      funcls None
  with
  | Some id -> id
  | None -> raise (Reporting.err_typ l "Function clause list is empty")

let id_of_mapdef (MD_aux (MD_mapping (id, _, _), _)) = id

let id_of_type_def_aux = function
  | TD_abbrev (id, _, _)
  | TD_record (id, _, _, _)
  | TD_variant (id, _, _, _)
  | TD_enum (id, _, _)
  | TD_bitfield (id, _, _) ->
      id
let id_of_type_def (TD_aux (td_aux, _)) = id_of_type_def_aux td_aux

let id_of_val_spec (VS_aux (VS_val_spec (_, id, _), _)) = id

let id_of_dec_spec (DEC_aux (DEC_reg (_, id, _), _)) = id

let id_of_scattered (SD_aux (sdef, _)) =
  match sdef with
  | SD_function (_, _, id)
  | SD_funcl (FCL_aux (FCL_funcl (id, _), _))
  | SD_end id
  | SD_variant (id, _)
  | SD_unioncl (id, _)
  | SD_internal_unioncl_record (_, id, _, _)
  | SD_mapping (id, _)
  | SD_mapcl (id, _)
  | SD_enum id
  | SD_enumcl (id, _) ->
      id

let ids_of_def (DEF_aux (aux, _)) =
  match aux with
  | DEF_type td -> IdSet.singleton (id_of_type_def td)
  | DEF_fundef fd -> IdSet.singleton (id_of_fundef fd)
  | DEF_mapdef md -> IdSet.singleton (id_of_mapdef md)
  | DEF_let (LB_aux (LB_val (pat, _), _)) -> pat_ids pat
  | DEF_register (DEC_aux (DEC_reg (_, id, _), _)) -> IdSet.singleton id
  | DEF_val vs -> IdSet.singleton (id_of_val_spec vs)
  | DEF_internal_mutrec fds -> IdSet.of_list (List.map id_of_fundef fds)
  | DEF_scattered sdef -> IdSet.singleton (id_of_scattered sdef)
  | _ -> IdSet.empty
let ids_of_defs defs = List.fold_left IdSet.union IdSet.empty (List.map ids_of_def defs)
let ids_of_ast ast = ids_of_defs ast.defs

let val_spec_ids defs =
  let val_spec_id (VS_aux (vs_aux, _)) = match vs_aux with VS_val_spec (_, id, _) -> id in
  let rec vs_ids = function
    | DEF_aux (DEF_val vs, _) :: defs -> val_spec_id vs :: vs_ids defs
    | _ :: defs -> vs_ids defs
    | [] -> []
  in
  IdSet.of_list (vs_ids defs)

let record_ids defs =
  let rec rec_ids = function
    | DEF_aux (DEF_type (TD_aux (TD_record (id, _, _, _), _)), _) :: defs -> id :: rec_ids defs
    | _ :: defs -> rec_ids defs
    | [] -> []
  in
  IdSet.of_list (rec_ids defs)

let rec get_scattered_union_clauses id = function
  | DEF_aux (DEF_scattered (SD_aux (SD_unioncl (uid, Tu_aux (tu, _)), _)), def_annot) :: defs when Id.compare id uid = 0
    ->
      Tu_aux (tu, def_annot) :: get_scattered_union_clauses id defs
  | _ :: defs -> get_scattered_union_clauses id defs
  | [] -> []

let rec get_scattered_enum_clauses id = function
  | DEF_aux (DEF_scattered (SD_aux (SD_enumcl (uid, member), _)), _) :: defs when Id.compare id uid = 0 ->
      member :: get_scattered_enum_clauses id defs
  | _ :: defs -> get_scattered_enum_clauses id defs
  | [] -> []

let lex_ord f g x1 x2 y1 y2 = match f x1 x2 with 0 -> g y1 y2 | n -> n

let rec nc_compare (NC_aux (nc1, _)) (NC_aux (nc2, _)) =
  match (nc1, nc2) with
  | NC_equal (n1, n2), NC_equal (n3, n4)
  | NC_bounded_ge (n1, n2), NC_bounded_ge (n3, n4)
  | NC_bounded_gt (n1, n2), NC_bounded_gt (n3, n4)
  | NC_bounded_le (n1, n2), NC_bounded_le (n3, n4)
  | NC_bounded_lt (n1, n2), NC_bounded_lt (n3, n4)
  | NC_not_equal (n1, n2), NC_not_equal (n3, n4) ->
      lex_ord Nexp.compare Nexp.compare n1 n3 n2 n4
  | NC_set (k1, s1), NC_set (k2, s2) -> lex_ord Kid.compare (Util.compare_list Nat_big_num.compare) k1 k2 s1 s2
  | NC_or (nc1, nc2), NC_or (nc3, nc4) | NC_and (nc1, nc2), NC_and (nc3, nc4) ->
      lex_ord nc_compare nc_compare nc1 nc3 nc2 nc4
  | NC_app (f1, args1), NC_app (f2, args2) -> lex_ord Id.compare (Util.compare_list typ_arg_compare) f1 f2 args1 args2
  | NC_var v1, NC_var v2 -> Kid.compare v1 v2
  | NC_true, NC_true | NC_false, NC_false -> 0
  | NC_equal _, _ -> -1
  | _, NC_equal _ -> 1
  | NC_bounded_ge _, _ -> -1
  | _, NC_bounded_ge _ -> 1
  | NC_bounded_gt _, _ -> -1
  | _, NC_bounded_gt _ -> 1
  | NC_bounded_le _, _ -> -1
  | _, NC_bounded_le _ -> 1
  | NC_bounded_lt _, _ -> -1
  | _, NC_bounded_lt _ -> 1
  | NC_not_equal _, _ -> -1
  | _, NC_not_equal _ -> 1
  | NC_set _, _ -> -1
  | _, NC_set _ -> 1
  | NC_or _, _ -> -1
  | _, NC_or _ -> 1
  | NC_and _, _ -> -1
  | _, NC_and _ -> 1
  | NC_app _, _ -> -1
  | _, NC_app _ -> 1
  | NC_var _, _ -> -1
  | _, NC_var _ -> 1
  | NC_true, _ -> -1
  | _, NC_true -> 1

and typ_compare (Typ_aux (t1, _)) (Typ_aux (t2, _)) =
  match (t1, t2) with
  | Typ_internal_unknown, Typ_internal_unknown -> 0
  | Typ_id id1, Typ_id id2 -> Id.compare id1 id2
  | Typ_var kid1, Typ_var kid2 -> Kid.compare kid1 kid2
  | Typ_fn (ts1, t2), Typ_fn (ts3, t4) -> (
      match Util.compare_list typ_compare ts1 ts3 with 0 -> typ_compare t2 t4 | n -> n
    )
  | Typ_bidir (t1, t2), Typ_bidir (t3, t4) -> (
      match typ_compare t1 t3 with 0 -> typ_compare t2 t4 | n -> n
    )
  | Typ_tuple ts1, Typ_tuple ts2 -> Util.compare_list typ_compare ts1 ts2
  | Typ_exist (ks1, nc1, t1), Typ_exist (ks2, nc2, t2) -> (
      match Util.compare_list KOpt.compare ks1 ks2 with
      | 0 -> (
          match nc_compare nc1 nc2 with 0 -> typ_compare t1 t2 | n -> n
        )
      | n -> n
    )
  | Typ_app (id1, ts1), Typ_app (id2, ts2) -> (
      match Id.compare id1 id2 with 0 -> Util.compare_list typ_arg_compare ts1 ts2 | n -> n
    )
  | Typ_internal_unknown, _ -> -1
  | _, Typ_internal_unknown -> 1
  | Typ_id _, _ -> -1
  | _, Typ_id _ -> 1
  | Typ_var _, _ -> -1
  | _, Typ_var _ -> 1
  | Typ_fn _, _ -> -1
  | _, Typ_fn _ -> 1
  | Typ_bidir _, _ -> -1
  | _, Typ_bidir _ -> 1
  | Typ_tuple _, _ -> -1
  | _, Typ_tuple _ -> 1
  | Typ_exist _, _ -> -1
  | _, Typ_exist _ -> 1

and typ_arg_compare (A_aux (ta1, _)) (A_aux (ta2, _)) =
  match (ta1, ta2) with
  | A_nexp n1, A_nexp n2 -> Nexp.compare n1 n2
  | A_typ t1, A_typ t2 -> typ_compare t1 t2
  | A_bool nc1, A_bool nc2 -> nc_compare nc1 nc2
  | A_nexp _, _ -> -1
  | _, A_nexp _ -> 1
  | A_typ _, _ -> -1
  | _, A_typ _ -> 1

let is_typ_arg_nexp = function A_aux (A_typ _, _) -> true | _ -> false

let is_typ_arg_typ = function A_aux (A_typ _, _) -> true | _ -> false

let is_typ_arg_bool = function A_aux (A_bool _, _) -> true | _ -> false

module NC = struct
  type t = n_constraint
  let compare = nc_compare
end

module NCMap = Map.Make (NC)

module Typ = struct
  type t = typ
  let compare = typ_compare
end

module TypMap = Map.Make (Typ)

let rec nexp_frees (Nexp_aux (nexp, l)) =
  match nexp with
  | Nexp_id _ -> raise (Reporting.err_typ l "Unimplemented Nexp_id in nexp_frees")
  | Nexp_var kid -> KidSet.singleton kid
  | Nexp_constant _ -> KidSet.empty
  | Nexp_times (n1, n2) -> KidSet.union (nexp_frees n1) (nexp_frees n2)
  | Nexp_sum (n1, n2) -> KidSet.union (nexp_frees n1) (nexp_frees n2)
  | Nexp_minus (n1, n2) -> KidSet.union (nexp_frees n1) (nexp_frees n2)
  | Nexp_exp n -> nexp_frees n
  | Nexp_neg n -> nexp_frees n
  | Nexp_app (_, nexps) -> List.fold_left KidSet.union KidSet.empty (List.map nexp_frees nexps)

let rec lexp_to_exp (LE_aux (lexp_aux, annot)) =
  let rewrap e_aux = E_aux (e_aux, annot) in
  match lexp_aux with
  | LE_id id | LE_typ (_, id) -> rewrap (E_id id)
  | LE_tuple les ->
      let get_id (LE_aux (lexp, ((l, _) as annot)) as le) =
        match lexp with
        | LE_id id | LE_typ (_, id) -> E_aux (E_id id, annot)
        | _ -> raise (Reporting.err_unreachable l __POS__ ("Unsupported sub-lexp " ^ string_of_lexp le ^ " in tuple"))
      in
      rewrap (E_tuple (List.map get_id les))
  | LE_vector (lexp, e) -> rewrap (E_vector_access (lexp_to_exp lexp, e))
  | LE_vector_range (lexp, e1, e2) -> rewrap (E_vector_subrange (lexp_to_exp lexp, e1, e2))
  | LE_field (lexp, id) -> rewrap (E_field (lexp_to_exp lexp, id))
  | LE_app (id, exps) -> rewrap (E_app (id, exps))
  | LE_vector_concat [] -> rewrap (E_vector [])
  | LE_vector_concat (lexp :: lexps) ->
      List.fold_left (fun exp lexp -> rewrap (E_vector_append (exp, lexp_to_exp lexp))) (lexp_to_exp lexp) lexps
  | LE_deref exp -> rewrap (E_app (mk_id "__deref", [exp]))

let is_unit_typ = function Typ_aux (Typ_id u, _) -> string_of_id u = "unit" | _ -> false

let is_number (Typ_aux (t, _)) =
  match t with
  | Typ_id (Id_aux (Id "int", _))
  | Typ_id (Id_aux (Id "nat", _))
  | Typ_app (Id_aux (Id "range", _), _)
  | Typ_app (Id_aux (Id "implicit", _), _)
  | Typ_app (Id_aux (Id "atom", _), _) ->
      true
  | _ -> false

let is_ref_typ (Typ_aux (typ_aux, _)) =
  match typ_aux with Typ_app (id, _) -> string_of_id id = "register" || string_of_id id = "reg" | _ -> false

let rec is_vector_typ = function
  | Typ_aux (Typ_app (Id_aux (Id "vector", _), [_; _]), _) -> true
  | Typ_aux (Typ_app (Id_aux (Id "register", _), [A_aux (A_typ rtyp, _)]), _) -> is_vector_typ rtyp
  | _ -> false

let typ_app_args_of = function
  | Typ_aux (Typ_app (Id_aux (Id c, _), targs), l) -> (c, List.map (fun (A_aux (a, _)) -> a) targs, l)
  | Typ_aux (_, l) as typ -> raise (Reporting.err_typ l ("typ_app_args_of called on non-app type " ^ string_of_typ typ))

let rec vector_typ_args_of typ =
  match typ_app_args_of typ with
  | "vector", [A_nexp len; A_typ etyp], _ -> (nexp_simp len, etyp)
  | "bitvector", [A_nexp len], _ -> (nexp_simp len, bit_typ)
  | "register", [A_typ rtyp], _ -> vector_typ_args_of rtyp
  | _, _, l -> raise (Reporting.err_typ l ("vector_typ_args_of called on non-vector type " ^ string_of_typ typ))

let is_order_inc = function Ord_aux (Ord_inc, _) -> true | Ord_aux (Ord_dec, _) -> false

let is_bit_typ = function Typ_aux (Typ_id (Id_aux (Id "bit", _)), _) -> true | _ -> false

let rec is_bitvector_typ = function
  | Typ_aux (Typ_app (Id_aux (Id "bitvector", _), [_]), _) -> true
  | Typ_aux (Typ_app (Id_aux (Id "register", _), [A_aux (A_typ rtyp, _)]), _) -> is_bitvector_typ rtyp
  | _ -> false

(* Utilities for constructing effect sets *)

let effectful e = e

let union_effects e1 e2 = e1 || e2

let equal_effects e1 e2 = e1 = e2

let subseteq_effects e1 e2 = match (e1, e2) with false, _ -> true | true, true -> true | true, false -> false

let rec kopts_of_nexp (Nexp_aux (nexp, _)) =
  match nexp with
  | Nexp_id _ | Nexp_constant _ -> KOptSet.empty
  | Nexp_var kid -> KOptSet.singleton (mk_kopt K_int kid)
  | Nexp_times (n1, n2) | Nexp_sum (n1, n2) | Nexp_minus (n1, n2) -> KOptSet.union (kopts_of_nexp n1) (kopts_of_nexp n2)
  | Nexp_exp n | Nexp_neg n -> kopts_of_nexp n
  | Nexp_app (_, nexps) -> List.fold_left KOptSet.union KOptSet.empty (List.map kopts_of_nexp nexps)

let rec kopts_of_constraint (NC_aux (nc, _)) =
  match nc with
  | NC_equal (nexp1, nexp2)
  | NC_bounded_ge (nexp1, nexp2)
  | NC_bounded_gt (nexp1, nexp2)
  | NC_bounded_le (nexp1, nexp2)
  | NC_bounded_lt (nexp1, nexp2)
  | NC_not_equal (nexp1, nexp2) ->
      KOptSet.union (kopts_of_nexp nexp1) (kopts_of_nexp nexp2)
  | NC_set (kid, _) -> KOptSet.singleton (mk_kopt K_int kid)
  | NC_or (nc1, nc2) | NC_and (nc1, nc2) -> KOptSet.union (kopts_of_constraint nc1) (kopts_of_constraint nc2)
  | NC_app (_, args) -> List.fold_left (fun s t -> KOptSet.union s (kopts_of_typ_arg t)) KOptSet.empty args
  | NC_var kid -> KOptSet.singleton (mk_kopt K_bool kid)
  | NC_true | NC_false -> KOptSet.empty

and kopts_of_typ (Typ_aux (t, _)) =
  match t with
  | Typ_internal_unknown -> KOptSet.empty
  | Typ_id _ -> KOptSet.empty
  | Typ_var kid -> KOptSet.singleton (mk_kopt K_type kid)
  | Typ_fn (ts, t) -> List.fold_left KOptSet.union (kopts_of_typ t) (List.map kopts_of_typ ts)
  | Typ_bidir (t1, t2) -> KOptSet.union (kopts_of_typ t1) (kopts_of_typ t2)
  | Typ_tuple ts -> List.fold_left (fun s t -> KOptSet.union s (kopts_of_typ t)) KOptSet.empty ts
  | Typ_app (_, tas) -> List.fold_left (fun s ta -> KOptSet.union s (kopts_of_typ_arg ta)) KOptSet.empty tas
  | Typ_exist (kopts, nc, t) ->
      let s = KOptSet.union (kopts_of_typ t) (kopts_of_constraint nc) in
      KOptSet.diff s (KOptSet.of_list kopts)

and kopts_of_typ_arg (A_aux (ta, _)) =
  match ta with
  | A_nexp nexp -> kopts_of_nexp nexp
  | A_typ typ -> kopts_of_typ typ
  | A_bool nc -> kopts_of_constraint nc

let kopts_of_quant_item (QI_aux (qi, _)) =
  match qi with QI_id kopt -> KOptSet.singleton kopt | QI_constraint nc -> kopts_of_constraint nc

let rec tyvars_of_nexp (Nexp_aux (nexp, _)) =
  match nexp with
  | Nexp_id _ | Nexp_constant _ -> KidSet.empty
  | Nexp_var kid -> KidSet.singleton kid
  | Nexp_times (n1, n2) | Nexp_sum (n1, n2) | Nexp_minus (n1, n2) -> KidSet.union (tyvars_of_nexp n1) (tyvars_of_nexp n2)
  | Nexp_exp n | Nexp_neg n -> tyvars_of_nexp n
  | Nexp_app (_, nexps) -> List.fold_left KidSet.union KidSet.empty (List.map tyvars_of_nexp nexps)

let rec tyvars_of_constraint (NC_aux (nc, _)) =
  match nc with
  | NC_equal (nexp1, nexp2)
  | NC_bounded_ge (nexp1, nexp2)
  | NC_bounded_gt (nexp1, nexp2)
  | NC_bounded_le (nexp1, nexp2)
  | NC_bounded_lt (nexp1, nexp2)
  | NC_not_equal (nexp1, nexp2) ->
      KidSet.union (tyvars_of_nexp nexp1) (tyvars_of_nexp nexp2)
  | NC_set (kid, _) -> KidSet.singleton kid
  | NC_or (nc1, nc2) | NC_and (nc1, nc2) -> KidSet.union (tyvars_of_constraint nc1) (tyvars_of_constraint nc2)
  | NC_app (_, args) -> List.fold_left (fun s t -> KidSet.union s (tyvars_of_typ_arg t)) KidSet.empty args
  | NC_var kid -> KidSet.singleton kid
  | NC_true | NC_false -> KidSet.empty

and tyvars_of_typ (Typ_aux (t, _)) =
  match t with
  | Typ_internal_unknown -> KidSet.empty
  | Typ_id _ -> KidSet.empty
  | Typ_var kid -> KidSet.singleton kid
  | Typ_fn (ts, t) -> List.fold_left KidSet.union (tyvars_of_typ t) (List.map tyvars_of_typ ts)
  | Typ_bidir (t1, t2) -> KidSet.union (tyvars_of_typ t1) (tyvars_of_typ t2)
  | Typ_tuple ts -> List.fold_left (fun s t -> KidSet.union s (tyvars_of_typ t)) KidSet.empty ts
  | Typ_app (_, tas) -> List.fold_left (fun s ta -> KidSet.union s (tyvars_of_typ_arg ta)) KidSet.empty tas
  | Typ_exist (kids, nc, t) ->
      let s = KidSet.union (tyvars_of_typ t) (tyvars_of_constraint nc) in
      List.fold_left (fun s k -> KidSet.remove k s) s (List.map kopt_kid kids)

and tyvars_of_typ_arg (A_aux (ta, _)) =
  match ta with
  | A_nexp nexp -> tyvars_of_nexp nexp
  | A_typ typ -> tyvars_of_typ typ
  | A_bool nc -> tyvars_of_constraint nc

let tyvars_of_quant_item (QI_aux (qi, _)) =
  match qi with
  | QI_id (KOpt_aux (KOpt_kind (_, kid), _)) -> KidSet.singleton kid
  | QI_constraint nc -> tyvars_of_constraint nc

let is_kid_generated kid = String.contains (string_of_kid kid) '#'

let rec undefined_of_typ mwords l annot (Typ_aux (typ_aux, _) as typ) =
  let wrap e_aux typ = E_aux (e_aux, (l, annot typ)) in
  match typ_aux with
  | Typ_id id -> wrap (E_app (prepend_id "undefined_" id, [wrap (E_lit (mk_lit L_unit)) unit_typ])) typ
  | Typ_app (_, [size; _; _]) when mwords && is_bitvector_typ typ ->
      wrap (E_app (mk_id "undefined_bitvector", undefined_of_typ_args mwords l annot size)) typ
  | Typ_app (atom, [A_aux (A_nexp i, _)]) when string_of_id atom = "atom" -> wrap (E_sizeof i) typ
  | Typ_app (id, args) ->
      wrap (E_app (prepend_id "undefined_" id, List.concat (List.map (undefined_of_typ_args mwords l annot) args))) typ
  | Typ_tuple typs -> wrap (E_tuple (List.map (undefined_of_typ mwords l annot) typs)) typ
  | Typ_var kid ->
      (* Undefined monomorphism restriction in the type checker should
         guarantee that the typ_(kid) parameter was always one created
         in an undefined_(type) function created in
         initial_check.ml. i.e. the rewriter should only encounter this
         case when re-writing those functions. *)
      wrap (E_id (prepend_id "typ_" (id_of_kid kid))) typ
  | Typ_internal_unknown -> assert false
  | Typ_bidir _ -> assert false
  | Typ_fn _ -> assert false
  | Typ_exist _ -> assert false (* Typ_exist should be re-written *)

and undefined_of_typ_args mwords l annot (A_aux (typ_arg_aux, _)) =
  match typ_arg_aux with
  | A_nexp n -> [E_aux (E_sizeof n, (l, annot (atom_typ n)))]
  | A_typ typ -> [undefined_of_typ mwords l annot typ]
  | A_bool nc -> [E_aux (E_constraint nc, (l, annot (atom_bool_typ nc)))]

let destruct_pexp (Pat_aux (pexp, ann)) =
  match pexp with
  | Pat_exp (pat, exp) -> (pat, None, exp, ann)
  | Pat_when (pat, guard, exp) -> (pat, Some guard, exp, ann)

let construct_pexp (pat, guard, exp, ann) =
  match guard with None -> Pat_aux (Pat_exp (pat, exp), ann) | Some guard -> Pat_aux (Pat_when (pat, guard, exp), ann)

let destruct_mpexp (MPat_aux (mpexp, ann)) =
  match mpexp with MPat_pat mpat -> (mpat, None, ann) | MPat_when (mpat, guard) -> (mpat, Some guard, ann)

let construct_mpexp (mpat, guard, ann) =
  match guard with None -> MPat_aux (MPat_pat mpat, ann) | Some guard -> MPat_aux (MPat_when (mpat, guard), ann)

let is_valspec id = function
  | DEF_aux (DEF_val (VS_aux (VS_val_spec (_, id', _), _)), _) when Id.compare id id' = 0 -> true
  | _ -> false

let is_fundef id = function
  | DEF_aux (DEF_fundef (FD_aux (FD_function (_, _, FCL_aux (FCL_funcl (id', _), _) :: _), _)), _)
    when Id.compare id' id = 0 ->
      true
  | _ -> false

let rename_valspec id (VS_aux (VS_val_spec (typschm, _, externs), annot)) =
  VS_aux (VS_val_spec (typschm, id, externs), annot)

let rename_funcl id (FCL_aux (FCL_funcl (_, pexp), annot)) = FCL_aux (FCL_funcl (id, pexp), annot)

let rename_fundef id (FD_aux (FD_function (ropt, topt, funcls), annot)) =
  FD_aux (FD_function (ropt, topt, List.map (rename_funcl id) funcls), annot)

let rec split_defs' f defs acc =
  match defs with
  | [] -> None
  | def :: defs when f def -> Some (acc, def, defs)
  | def :: defs -> split_defs' f defs (def :: acc)

let split_defs f defs =
  match split_defs' f defs [] with
  | None -> None
  | Some (pre_defs, def, post_defs) -> Some (List.rev pre_defs, def, post_defs)

let append_ast ast1 ast2 = { defs = ast1.defs @ ast2.defs; comments = ast1.comments @ ast2.comments }
let append_ast_defs ast defs = { ast with defs = ast.defs @ defs }
let concat_ast asts = List.fold_right append_ast asts empty_ast

let type_union_id (Tu_aux (Tu_ty_id (_, id), _)) = id

let rec subst id value (E_aux (e_aux, annot) as exp) =
  let wrap e_aux = E_aux (e_aux, annot) in
  let e_aux =
    match e_aux with
    | E_block exps -> E_block (List.map (subst id value) exps)
    | E_id id' -> if Id.compare id id' = 0 then unaux_exp value else E_id id'
    | E_lit lit -> E_lit lit
    | E_typ (typ, exp) -> E_typ (typ, subst id value exp)
    | E_app (fn, exps) -> E_app (fn, List.map (subst id value) exps)
    | E_app_infix (exp1, op, exp2) -> E_app_infix (subst id value exp1, op, subst id value exp2)
    | E_tuple exps -> E_tuple (List.map (subst id value) exps)
    | E_if (cond, then_exp, else_exp) -> E_if (subst id value cond, subst id value then_exp, subst id value else_exp)
    | E_loop (loop, measure, cond, body) ->
        E_loop (loop, subst_measure id value measure, subst id value cond, subst id value body)
    | E_for (id', exp1, exp2, exp3, order, body) when Id.compare id id' = 0 -> E_for (id', exp1, exp2, exp3, order, body)
    | E_for (id', exp1, exp2, exp3, order, body) ->
        E_for (id', subst id value exp1, subst id value exp2, subst id value exp3, order, subst id value body)
    | E_vector exps -> E_vector (List.map (subst id value) exps)
    | E_vector_access (exp1, exp2) -> E_vector_access (subst id value exp1, subst id value exp2)
    | E_vector_subrange (exp1, exp2, exp3) ->
        E_vector_subrange (subst id value exp1, subst id value exp2, subst id value exp3)
    | E_vector_update (exp1, exp2, exp3) ->
        E_vector_update (subst id value exp1, subst id value exp2, subst id value exp3)
    | E_vector_update_subrange (exp1, exp2, exp3, exp4) ->
        E_vector_update_subrange (subst id value exp1, subst id value exp2, subst id value exp3, subst id value exp4)
    | E_vector_append (exp1, exp2) -> E_vector_append (subst id value exp1, subst id value exp2)
    | E_list exps -> E_list (List.map (subst id value) exps)
    | E_cons (exp1, exp2) -> E_cons (subst id value exp1, subst id value exp2)
    | E_struct fexps -> E_struct (List.map (subst_fexp id value) fexps)
    | E_struct_update (exp, fexps) -> E_struct_update (subst id value exp, List.map (subst_fexp id value) fexps)
    | E_field (exp, id') -> E_field (subst id value exp, id')
    | E_match (exp, pexps) -> E_match (subst id value exp, List.map (subst_pexp id value) pexps)
    | E_let (LB_aux (LB_val (pat, bind), lb_annot), body) ->
        E_let
          ( LB_aux (LB_val (pat, subst id value bind), lb_annot),
            if IdSet.mem id (pat_ids pat) then body else subst id value body
          )
    | E_assign (lexp, exp) -> E_assign (subst_lexp id value lexp, subst id value exp) (* Shadowing... *)
    (* Should be re-written *)
    | E_sizeof nexp -> E_sizeof nexp
    | E_constraint nc -> E_constraint nc
    | E_return exp -> E_return (subst id value exp)
    | E_exit exp -> E_exit (subst id value exp)
    (* id should always be immutable while id' must be mutable register name so should be ok to never substitute here *)
    | E_ref id' -> E_ref id'
    | E_throw exp -> E_throw (subst id value exp)
    | E_try (exp, pexps) -> E_try (subst id value exp, List.map (subst_pexp id value) pexps)
    | E_assert (exp1, exp2) -> E_assert (subst id value exp1, subst id value exp2)
    | E_internal_value v -> E_internal_value v
    | E_var (lexp, exp1, exp2) -> E_var (subst_lexp id value lexp, subst id value exp1, subst id value exp2)
    | E_internal_assume (nc, exp) -> E_internal_assume (nc, subst id value exp)
    | E_internal_plet _ | E_internal_return _ -> failwith ("subst " ^ string_of_exp exp)
  in
  wrap e_aux

and subst_measure id value (Measure_aux (m_aux, l)) =
  match m_aux with
  | Measure_none -> Measure_aux (Measure_none, l)
  | Measure_some exp -> Measure_aux (Measure_some (subst id value exp), l)

and subst_pexp id value (Pat_aux (pexp_aux, annot)) =
  let pexp_aux =
    match pexp_aux with
    | Pat_exp (pat, exp) when IdSet.mem id (pat_ids pat) -> Pat_exp (pat, exp)
    | Pat_exp (pat, exp) -> Pat_exp (pat, subst id value exp)
    | Pat_when (pat, guard, exp) when IdSet.mem id (pat_ids pat) -> Pat_when (pat, guard, exp)
    | Pat_when (pat, guard, exp) -> Pat_when (pat, subst id value guard, subst id value exp)
  in
  Pat_aux (pexp_aux, annot)

and subst_fexp id value (FE_aux (FE_fexp (id', exp), annot)) = FE_aux (FE_fexp (id', subst id value exp), annot)

and subst_lexp id value (LE_aux (lexp_aux, annot)) =
  let wrap lexp_aux = LE_aux (lexp_aux, annot) in
  let lexp_aux =
    match lexp_aux with
    | LE_deref exp -> LE_deref (subst id value exp)
    | LE_id id' -> LE_id id'
    | LE_app (f, exps) -> LE_app (f, List.map (subst id value) exps)
    | LE_typ (typ, id') -> LE_typ (typ, id')
    | LE_tuple lexps -> LE_tuple (List.map (subst_lexp id value) lexps)
    | LE_vector (lexp, exp) -> LE_vector (subst_lexp id value lexp, subst id value exp)
    | LE_vector_range (lexp, exp1, exp2) ->
        LE_vector_range (subst_lexp id value lexp, subst id value exp1, subst id value exp2)
    | LE_vector_concat lexps -> LE_vector_concat (List.map (subst_lexp id value) lexps)
    | LE_field (lexp, id') -> LE_field (subst_lexp id value lexp, id')
  in
  wrap lexp_aux

let hex_to_bin hex =
  Util.string_to_list hex |> List.map Sail_lib.hex_char |> List.concat |> List.map Sail_lib.char_of_bit |> fun bits ->
  String.init (List.length bits) (List.nth bits)

let explode s =
  let rec exp i l = if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let vector_string_to_bit_list (L_aux (lit, l)) =
  let hexchar_to_binlist = function
    | '0' -> ['0'; '0'; '0'; '0']
    | '1' -> ['0'; '0'; '0'; '1']
    | '2' -> ['0'; '0'; '1'; '0']
    | '3' -> ['0'; '0'; '1'; '1']
    | '4' -> ['0'; '1'; '0'; '0']
    | '5' -> ['0'; '1'; '0'; '1']
    | '6' -> ['0'; '1'; '1'; '0']
    | '7' -> ['0'; '1'; '1'; '1']
    | '8' -> ['1'; '0'; '0'; '0']
    | '9' -> ['1'; '0'; '0'; '1']
    | 'A' -> ['1'; '0'; '1'; '0']
    | 'B' -> ['1'; '0'; '1'; '1']
    | 'C' -> ['1'; '1'; '0'; '0']
    | 'D' -> ['1'; '1'; '0'; '1']
    | 'E' -> ['1'; '1'; '1'; '0']
    | 'F' -> ['1'; '1'; '1'; '1']
    | _ -> raise (Reporting.err_unreachable l __POS__ "hexchar_to_binlist given unrecognized character")
  in

  let s_bin =
    match lit with
    | L_hex s_hex -> List.flatten (List.map hexchar_to_binlist (explode (String.uppercase_ascii s_hex)))
    | L_bin s_bin -> explode s_bin
    | _ -> raise (Reporting.err_unreachable l __POS__ "s_bin given non vector literal")
  in

  List.map
    (function
      | '0' -> L_aux (L_zero, gen_loc l)
      | '1' -> L_aux (L_one, gen_loc l)
      | _ -> raise (Reporting.err_unreachable (gen_loc l) __POS__ "binary had non-zero or one")
      )
    s_bin

(* Functions for working with locations *)

let locate_id f (Id_aux (name, l)) = Id_aux (name, f l)

let locate_kid f (Kid_aux (name, l)) = Kid_aux (name, f l)

let locate_kind f (K_aux (kind, l)) = K_aux (kind, f l)

let locate_kinded_id f (KOpt_aux (KOpt_kind (k, kid), l)) = KOpt_aux (KOpt_kind (locate_kind f k, locate_kid f kid), f l)

let locate_lit f (L_aux (lit, l)) = L_aux (lit, f l)

let rec locate_nexp f (Nexp_aux (nexp_aux, l)) =
  let nexp_aux =
    match nexp_aux with
    | Nexp_id id -> Nexp_id (locate_id f id)
    | Nexp_var kid -> Nexp_var (locate_kid f kid)
    | Nexp_constant n -> Nexp_constant n
    | Nexp_app (id, nexps) -> Nexp_app (locate_id f id, List.map (locate_nexp f) nexps)
    | Nexp_times (nexp1, nexp2) -> Nexp_times (locate_nexp f nexp1, locate_nexp f nexp2)
    | Nexp_sum (nexp1, nexp2) -> Nexp_sum (locate_nexp f nexp1, locate_nexp f nexp2)
    | Nexp_minus (nexp1, nexp2) -> Nexp_minus (locate_nexp f nexp1, locate_nexp f nexp2)
    | Nexp_exp nexp -> Nexp_exp (locate_nexp f nexp)
    | Nexp_neg nexp -> Nexp_neg (locate_nexp f nexp)
  in
  Nexp_aux (nexp_aux, f l)

let rec locate_nc f (NC_aux (nc_aux, l)) =
  let nc_aux =
    match nc_aux with
    | NC_equal (nexp1, nexp2) -> NC_equal (locate_nexp f nexp1, locate_nexp f nexp2)
    | NC_bounded_ge (nexp1, nexp2) -> NC_bounded_ge (locate_nexp f nexp1, locate_nexp f nexp2)
    | NC_bounded_gt (nexp1, nexp2) -> NC_bounded_gt (locate_nexp f nexp1, locate_nexp f nexp2)
    | NC_bounded_le (nexp1, nexp2) -> NC_bounded_le (locate_nexp f nexp1, locate_nexp f nexp2)
    | NC_bounded_lt (nexp1, nexp2) -> NC_bounded_lt (locate_nexp f nexp1, locate_nexp f nexp2)
    | NC_not_equal (nexp1, nexp2) -> NC_not_equal (locate_nexp f nexp1, locate_nexp f nexp2)
    | NC_set (kid, nums) -> NC_set (locate_kid f kid, nums)
    | NC_or (nc1, nc2) -> NC_or (locate_nc f nc1, locate_nc f nc2)
    | NC_and (nc1, nc2) -> NC_and (locate_nc f nc1, locate_nc f nc2)
    | NC_true -> NC_true
    | NC_false -> NC_false
    | NC_var v -> NC_var (locate_kid f v)
    | NC_app (id, args) -> NC_app (locate_id f id, List.map (locate_typ_arg f) args)
  in
  NC_aux (nc_aux, f l)

and locate_typ f (Typ_aux (typ_aux, l)) =
  let typ_aux =
    match typ_aux with
    | Typ_internal_unknown -> Typ_internal_unknown
    | Typ_id id -> Typ_id (locate_id f id)
    | Typ_var kid -> Typ_var (locate_kid f kid)
    | Typ_fn (arg_typs, ret_typ) -> Typ_fn (List.map (locate_typ f) arg_typs, locate_typ f ret_typ)
    | Typ_bidir (typ1, typ2) -> Typ_bidir (locate_typ f typ1, locate_typ f typ2)
    | Typ_tuple typs -> Typ_tuple (List.map (locate_typ f) typs)
    | Typ_exist (kopts, constr, typ) ->
        Typ_exist (List.map (locate_kinded_id f) kopts, locate_nc f constr, locate_typ f typ)
    | Typ_app (id, typ_args) -> Typ_app (locate_id f id, List.map (locate_typ_arg f) typ_args)
  in
  Typ_aux (typ_aux, f l)

and locate_typ_arg f (A_aux (typ_arg_aux, l)) =
  let typ_arg_aux =
    match typ_arg_aux with
    | A_nexp nexp -> A_nexp (locate_nexp f nexp)
    | A_typ typ -> A_typ (locate_typ f typ)
    | A_bool nc -> A_bool (locate_nc f nc)
  in
  A_aux (typ_arg_aux, f l)

let rec locate_typ_pat f (TP_aux (tp_aux, l)) =
  let tp_aux =
    match tp_aux with
    | TP_wild -> TP_wild
    | TP_var kid -> TP_var (locate_kid f kid)
    | TP_app (id, tps) -> TP_app (locate_id f id, List.map (locate_typ_pat f) tps)
  in
  TP_aux (tp_aux, f l)

let rec locate_pat : 'a. (l -> l) -> 'a pat -> 'a pat =
 fun f (P_aux (p_aux, (l, annot))) ->
  let p_aux =
    match p_aux with
    | P_lit lit -> P_lit (locate_lit f lit)
    | P_wild -> P_wild
    | P_or (pat1, pat2) -> P_or (locate_pat f pat1, locate_pat f pat2)
    | P_not pat -> P_not (locate_pat f pat)
    | P_as (pat, id) -> P_as (locate_pat f pat, locate_id f id)
    | P_typ (typ, pat) -> P_typ (locate_typ f typ, locate_pat f pat)
    | P_id id -> P_id (locate_id f id)
    | P_var (pat, typ_pat) -> P_var (locate_pat f pat, locate_typ_pat f typ_pat)
    | P_app (id, pats) -> P_app (locate_id f id, List.map (locate_pat f) pats)
    | P_vector pats -> P_vector (List.map (locate_pat f) pats)
    | P_vector_concat pats -> P_vector_concat (List.map (locate_pat f) pats)
    | P_vector_subrange (id, n, m) -> P_vector_subrange (locate_id f id, n, m)
    | P_tuple pats -> P_tuple (List.map (locate_pat f) pats)
    | P_list pats -> P_list (List.map (locate_pat f) pats)
    | P_cons (hd_pat, tl_pat) -> P_cons (locate_pat f hd_pat, locate_pat f tl_pat)
    | P_string_append pats -> P_string_append (List.map (locate_pat f) pats)
    | P_struct (fpats, fwild) -> P_struct (List.map (fun (field, pat) -> (field, locate_pat f pat)) fpats, fwild)
  in
  P_aux (p_aux, (f l, annot))

let rec locate : 'a. (l -> l) -> 'a exp -> 'a exp =
 fun f (E_aux (e_aux, (l, annot))) ->
  let e_aux =
    match e_aux with
    | E_block exps -> E_block (List.map (locate f) exps)
    | E_id id -> E_id (locate_id f id)
    | E_lit lit -> E_lit (locate_lit f lit)
    | E_typ (typ, exp) -> E_typ (locate_typ f typ, locate f exp)
    | E_app (id, exps) -> E_app (locate_id f id, List.map (locate f) exps)
    | E_app_infix (exp1, op, exp2) -> E_app_infix (locate f exp1, locate_id f op, locate f exp2)
    | E_tuple exps -> E_tuple (List.map (locate f) exps)
    | E_if (cond_exp, then_exp, else_exp) -> E_if (locate f cond_exp, locate f then_exp, locate f else_exp)
    | E_loop (loop, measure, cond, body) -> E_loop (loop, locate_measure f measure, locate f cond, locate f body)
    | E_for (id, exp1, exp2, exp3, ord, exp4) ->
        E_for (locate_id f id, locate f exp1, locate f exp2, locate f exp3, ord, locate f exp4)
    | E_vector exps -> E_vector (List.map (locate f) exps)
    | E_vector_access (exp1, exp2) -> E_vector_access (locate f exp1, locate f exp2)
    | E_vector_subrange (exp1, exp2, exp3) -> E_vector_subrange (locate f exp1, locate f exp2, locate f exp3)
    | E_vector_update (exp1, exp2, exp3) -> E_vector_update (locate f exp1, locate f exp2, locate f exp3)
    | E_vector_update_subrange (exp1, exp2, exp3, exp4) ->
        E_vector_update_subrange (locate f exp1, locate f exp2, locate f exp3, locate f exp4)
    | E_vector_append (exp1, exp2) -> E_vector_append (locate f exp1, locate f exp2)
    | E_list exps -> E_list (List.map (locate f) exps)
    | E_cons (exp1, exp2) -> E_cons (locate f exp1, locate f exp2)
    | E_struct fexps -> E_struct (List.map (locate_fexp f) fexps)
    | E_struct_update (exp, fexps) -> E_struct_update (locate f exp, List.map (locate_fexp f) fexps)
    | E_field (exp, id) -> E_field (locate f exp, locate_id f id)
    | E_match (exp, cases) -> E_match (locate f exp, List.map (locate_pexp f) cases)
    | E_let (letbind, exp) -> E_let (locate_letbind f letbind, locate f exp)
    | E_assign (lexp, exp) -> E_assign (locate_lexp f lexp, locate f exp)
    | E_sizeof nexp -> E_sizeof (locate_nexp f nexp)
    | E_return exp -> E_return (locate f exp)
    | E_exit exp -> E_exit (locate f exp)
    | E_ref id -> E_ref (locate_id f id)
    | E_throw exp -> E_throw (locate f exp)
    | E_try (exp, cases) -> E_try (locate f exp, List.map (locate_pexp f) cases)
    | E_assert (exp, message) -> E_assert (locate f exp, locate f message)
    | E_constraint constr -> E_constraint (locate_nc f constr)
    | E_var (lexp, exp1, exp2) -> E_var (locate_lexp f lexp, locate f exp1, locate f exp2)
    | E_internal_plet (pat, exp1, exp2) -> E_internal_plet (locate_pat f pat, locate f exp1, locate f exp2)
    | E_internal_return exp -> E_internal_return (locate f exp)
    | E_internal_value value -> E_internal_value value
    | E_internal_assume (nc, exp) -> E_internal_assume (locate_nc f nc, locate f exp)
  in
  E_aux (e_aux, (f l, annot))

and locate_measure : 'a. (l -> l) -> 'a internal_loop_measure -> 'a internal_loop_measure =
 fun f (Measure_aux (m, l)) ->
  let m = match m with Measure_none -> Measure_none | Measure_some exp -> Measure_some (locate f exp) in
  Measure_aux (m, f l)

and locate_letbind : 'a. (l -> l) -> 'a letbind -> 'a letbind =
 fun f (LB_aux (LB_val (pat, exp), (l, annot))) -> LB_aux (LB_val (locate_pat f pat, locate f exp), (f l, annot))

and locate_pexp : 'a. (l -> l) -> 'a pexp -> 'a pexp =
 fun f (Pat_aux (pexp_aux, (l, annot))) ->
  let pexp_aux =
    match pexp_aux with
    | Pat_exp (pat, exp) -> Pat_exp (locate_pat f pat, locate f exp)
    | Pat_when (pat, guard, exp) -> Pat_when (locate_pat f pat, locate f guard, locate f exp)
  in
  Pat_aux (pexp_aux, (f l, annot))

and locate_lexp : 'a. (l -> l) -> 'a lexp -> 'a lexp =
 fun f (LE_aux (lexp_aux, (l, annot))) ->
  let lexp_aux =
    match lexp_aux with
    | LE_id id -> LE_id (locate_id f id)
    | LE_deref exp -> LE_deref (locate f exp)
    | LE_app (id, exps) -> LE_app (locate_id f id, List.map (locate f) exps)
    | LE_typ (typ, id) -> LE_typ (locate_typ f typ, locate_id f id)
    | LE_tuple lexps -> LE_tuple (List.map (locate_lexp f) lexps)
    | LE_vector_concat lexps -> LE_vector_concat (List.map (locate_lexp f) lexps)
    | LE_vector (lexp, exp) -> LE_vector (locate_lexp f lexp, locate f exp)
    | LE_vector_range (lexp, exp1, exp2) -> LE_vector_range (locate_lexp f lexp, locate f exp1, locate f exp2)
    | LE_field (lexp, id) -> LE_field (locate_lexp f lexp, locate_id f id)
  in
  LE_aux (lexp_aux, (f l, annot))

and locate_fexp : 'a. (l -> l) -> 'a fexp -> 'a fexp =
 fun f (FE_aux (FE_fexp (id, exp), (l, annot))) -> FE_aux (FE_fexp (locate_id f id, locate f exp), (f l, annot))

let unique_ref = ref 0

let unique l =
  let l = Parse_ast.Unique (!unique_ref, l) in
  incr unique_ref;
  l

let extern_assoc backend ext =
  match ext with
  | None -> None
  | Some ext -> (
      match List.assoc_opt backend ext.bindings with Some f -> Some f | None -> List.assoc_opt "_" ext.bindings
    )

(**************************************************************************)
(* 1. Substitutions                                                       *)
(**************************************************************************)

let rec nexp_subst sv subst = function
  | Nexp_aux (Nexp_var kid, _) as nexp -> begin
      match subst with A_aux (A_nexp n, _) when Kid.compare kid sv = 0 -> n | _ -> nexp
    end
  | Nexp_aux (nexp, l) -> Nexp_aux (nexp_subst_aux sv subst nexp, l)

and nexp_subst_aux sv subst = function
  | Nexp_var kid -> begin
      match subst with A_aux (A_nexp n, _) when Kid.compare kid sv = 0 -> unaux_nexp n | _ -> Nexp_var kid
    end
  | Nexp_id id -> Nexp_id id
  | Nexp_constant c -> Nexp_constant c
  | Nexp_times (nexp1, nexp2) -> Nexp_times (nexp_subst sv subst nexp1, nexp_subst sv subst nexp2)
  | Nexp_sum (nexp1, nexp2) -> Nexp_sum (nexp_subst sv subst nexp1, nexp_subst sv subst nexp2)
  | Nexp_minus (nexp1, nexp2) -> Nexp_minus (nexp_subst sv subst nexp1, nexp_subst sv subst nexp2)
  | Nexp_app (id, nexps) -> Nexp_app (id, List.map (nexp_subst sv subst) nexps)
  | Nexp_exp nexp -> Nexp_exp (nexp_subst sv subst nexp)
  | Nexp_neg nexp -> Nexp_neg (nexp_subst sv subst nexp)

let rec nexp_set_to_or l subst = function
  | [] -> raise (Reporting.err_unreachable l __POS__ "Empty set in constraint")
  | [int] -> NC_equal (subst, nconstant int)
  | int :: ints -> NC_or (mk_nc (NC_equal (subst, nconstant int)), mk_nc (nexp_set_to_or l subst ints))

let rec constraint_subst sv subst (NC_aux (nc, l)) = NC_aux (constraint_subst_aux l sv subst nc, l)

and constraint_subst_aux l sv subst = function
  | NC_equal (n1, n2) -> NC_equal (nexp_subst sv subst n1, nexp_subst sv subst n2)
  | NC_bounded_ge (n1, n2) -> NC_bounded_ge (nexp_subst sv subst n1, nexp_subst sv subst n2)
  | NC_bounded_gt (n1, n2) -> NC_bounded_gt (nexp_subst sv subst n1, nexp_subst sv subst n2)
  | NC_bounded_le (n1, n2) -> NC_bounded_le (nexp_subst sv subst n1, nexp_subst sv subst n2)
  | NC_bounded_lt (n1, n2) -> NC_bounded_lt (nexp_subst sv subst n1, nexp_subst sv subst n2)
  | NC_not_equal (n1, n2) -> NC_not_equal (nexp_subst sv subst n1, nexp_subst sv subst n2)
  | NC_set (kid, ints) as set_nc -> begin
      match subst with
      | A_aux (A_nexp (Nexp_aux (Nexp_var kid', _)), _) when Kid.compare kid sv = 0 -> NC_set (kid', ints)
      | A_aux (A_nexp n, _) when Kid.compare kid sv = 0 -> nexp_set_to_or l n ints
      | _ -> set_nc
    end
  | NC_or (nc1, nc2) -> NC_or (constraint_subst sv subst nc1, constraint_subst sv subst nc2)
  | NC_and (nc1, nc2) -> NC_and (constraint_subst sv subst nc1, constraint_subst sv subst nc2)
  | NC_app (id, args) -> NC_app (id, List.map (typ_arg_subst sv subst) args)
  | NC_var kid -> begin
      match subst with A_aux (A_bool nc, _) when Kid.compare kid sv = 0 -> unaux_constraint nc | _ -> NC_var kid
    end
  | NC_false -> NC_false
  | NC_true -> NC_true

and typ_subst sv subst (Typ_aux (typ, l)) = Typ_aux (typ_subst_aux sv subst typ, l)

and typ_subst_aux sv subst = function
  | Typ_internal_unknown -> Typ_internal_unknown
  | Typ_id v -> Typ_id v
  | Typ_var kid -> begin
      match subst with A_aux (A_typ typ, _) when Kid.compare kid sv = 0 -> unaux_typ typ | _ -> Typ_var kid
    end
  | Typ_fn (arg_typs, ret_typ) -> Typ_fn (List.map (typ_subst sv subst) arg_typs, typ_subst sv subst ret_typ)
  | Typ_bidir (typ1, typ2) -> Typ_bidir (typ_subst sv subst typ1, typ_subst sv subst typ2)
  | Typ_tuple typs -> Typ_tuple (List.map (typ_subst sv subst) typs)
  | Typ_app (f, args) -> Typ_app (f, List.map (typ_arg_subst sv subst) args)
  | Typ_exist (kopts, nc, typ) when KidSet.mem sv (KidSet.of_list (List.map kopt_kid kopts)) ->
      Typ_exist (kopts, nc, typ)
  | Typ_exist (kopts, nc, typ) -> Typ_exist (kopts, constraint_subst sv subst nc, typ_subst sv subst typ)

and typ_arg_subst sv subst (A_aux (arg, l)) = A_aux (typ_arg_subst_aux sv subst arg, l)

and typ_arg_subst_aux sv subst = function
  | A_nexp nexp -> A_nexp (nexp_subst sv subst nexp)
  | A_typ typ -> A_typ (typ_subst sv subst typ)
  | A_bool nc -> A_bool (constraint_subst sv subst nc)

let subst_kid subst sv v x =
  x
  |> subst sv (mk_typ_arg (A_bool (nc_var v)))
  |> subst sv (mk_typ_arg (A_nexp (nvar v)))
  |> subst sv (mk_typ_arg (A_typ (mk_typ (Typ_var v))))

let kopt_subst_kid sv subst (KOpt_aux (KOpt_kind (k, kid), l) as orig) =
  if Kid.compare kid sv = 0 then KOpt_aux (KOpt_kind (k, subst), l) else orig

let quant_item_subst_kid_aux sv subst = function
  | QI_id kopt -> QI_id (kopt_subst_kid sv subst kopt)
  | QI_constraint nc -> QI_constraint (subst_kid constraint_subst sv subst nc)

let quant_item_subst_kid sv subst (QI_aux (quant, l)) = QI_aux (quant_item_subst_kid_aux sv subst quant, l)

let typquant_subst_kid_aux sv subst = function
  | TypQ_tq quants -> TypQ_tq (List.map (quant_item_subst_kid sv subst) quants)
  | TypQ_no_forall -> TypQ_no_forall

let typquant_subst_kid sv subst (TypQ_aux (typq, l)) = TypQ_aux (typquant_subst_kid_aux sv subst typq, l)

let subst_kids_nexp substs nexp =
  let rec s_snexp substs (Nexp_aux (ne, l) as nexp) =
    let re ne = Nexp_aux (ne, l) in
    let s_snexp = s_snexp substs in
    match ne with
    | Nexp_var v -> (
        try KBindings.find v substs with Not_found -> nexp
      )
    | Nexp_id _ | Nexp_constant _ -> nexp
    | Nexp_times (n1, n2) -> re (Nexp_times (s_snexp n1, s_snexp n2))
    | Nexp_sum (n1, n2) -> re (Nexp_sum (s_snexp n1, s_snexp n2))
    | Nexp_minus (n1, n2) -> re (Nexp_minus (s_snexp n1, s_snexp n2))
    | Nexp_exp ne -> re (Nexp_exp (s_snexp ne))
    | Nexp_neg ne -> re (Nexp_neg (s_snexp ne))
    | Nexp_app (id, args) -> re (Nexp_app (id, List.map s_snexp args))
  in
  s_snexp substs nexp

let subst_kids_nc, subst_kids_typ, subst_kids_typ_arg =
  let rec subst_kids_nc substs (NC_aux (nc, l) as n_constraint) =
    let snexp nexp = subst_kids_nexp substs nexp in
    let snc nc = subst_kids_nc substs nc in
    let re nc = NC_aux (nc, l) in
    match nc with
    | NC_equal (n1, n2) -> re (NC_equal (snexp n1, snexp n2))
    | NC_bounded_ge (n1, n2) -> re (NC_bounded_ge (snexp n1, snexp n2))
    | NC_bounded_gt (n1, n2) -> re (NC_bounded_gt (snexp n1, snexp n2))
    | NC_bounded_le (n1, n2) -> re (NC_bounded_le (snexp n1, snexp n2))
    | NC_bounded_lt (n1, n2) -> re (NC_bounded_lt (snexp n1, snexp n2))
    | NC_not_equal (n1, n2) -> re (NC_not_equal (snexp n1, snexp n2))
    | NC_set (kid, is) -> begin
        match KBindings.find kid substs with
        | Nexp_aux (Nexp_constant i, _) ->
            if List.exists (fun j -> Big_int.equal i j) is then re NC_true else re NC_false
        | nexp -> begin
            match List.rev is with
            | i :: is ->
                let equal_num i = re (NC_equal (nexp, nconstant i)) in
                List.fold_left (fun nc i -> re (NC_or (equal_num i, nc))) (equal_num i) is
            | [] -> re NC_false
          end
        | exception Not_found -> n_constraint
      end
    | NC_or (nc1, nc2) -> re (NC_or (snc nc1, snc nc2))
    | NC_and (nc1, nc2) -> re (NC_and (snc nc1, snc nc2))
    | NC_true | NC_false -> n_constraint
    | NC_var kid -> re (NC_var kid)
    | NC_app (f, args) -> re (NC_app (f, List.map (s_starg substs) args))
  and s_styp substs (Typ_aux (t, l) as ty) =
    let re t = Typ_aux (t, l) in
    match t with
    | Typ_id _ | Typ_var _ -> ty
    | Typ_fn (t1, t2) -> re (Typ_fn (List.map (s_styp substs) t1, s_styp substs t2))
    | Typ_bidir (t1, t2) -> re (Typ_bidir (s_styp substs t1, s_styp substs t2))
    | Typ_tuple ts -> re (Typ_tuple (List.map (s_styp substs) ts))
    | Typ_app (id, tas) -> re (Typ_app (id, List.map (s_starg substs) tas))
    | Typ_exist (kopts, nc, t) ->
        let substs = List.fold_left (fun sub kopt -> KBindings.remove (kopt_kid kopt) sub) substs kopts in
        re (Typ_exist (kopts, subst_kids_nc substs nc, s_styp substs t))
    | Typ_internal_unknown -> Reporting.unreachable l __POS__ "escaped Typ_internal_unknown"
  and s_starg substs (A_aux (ta, l)) =
    match ta with
    | A_nexp ne -> A_aux (A_nexp (subst_kids_nexp substs ne), l)
    | A_typ t -> A_aux (A_typ (s_styp substs t), l)
    | A_bool nc -> A_aux (A_bool (subst_kids_nc substs nc), l)
  in
  (subst_kids_nc, s_styp, s_starg)

let before p1 p2 =
  let open Lexing in
  p1.pos_fname = p2.pos_fname && p1.pos_cnum <= p2.pos_cnum

let subloc sl l =
  match (sl, Reporting.simp_loc l) with
  | _, None -> false
  | None, _ -> false
  | Some (p1a, p1b), Some (p2a, p2b) -> before p2a p1a && before p1b p2b

let rec option_mapm f = function
  | [] -> None
  | x :: xs -> begin match f x with Some y -> Some y | None -> option_mapm f xs end

let option_chain opt1 opt2 =
  begin
    match opt1 with None -> opt2 | _ -> opt1
  end

let rec find_annot_exp sl (E_aux (aux, (l, annot))) =
  if not (subloc sl l) then None
  else (
    let result =
      match aux with
      | E_block exps | E_tuple exps -> option_mapm (find_annot_exp sl) exps
      | E_app (_, exps) -> option_mapm (find_annot_exp sl) exps
      | E_let (LB_aux (LB_val (pat, exp), _), body) ->
          option_chain (find_annot_pat sl pat) (option_mapm (find_annot_exp sl) [exp; body])
      | E_assign (lexp, exp) -> option_chain (find_annot_lexp sl lexp) (find_annot_exp sl exp)
      | E_var (lexp, exp1, exp2) -> option_chain (find_annot_lexp sl lexp) (option_mapm (find_annot_exp sl) [exp1; exp2])
      | E_if (cond_exp, then_exp, else_exp) -> option_mapm (find_annot_exp sl) [cond_exp; then_exp; else_exp]
      | E_match (exp, cases) | E_try (exp, cases) ->
          option_chain (find_annot_exp sl exp) (option_mapm (find_annot_pexp sl) cases)
      | E_return exp | E_typ (_, exp) -> find_annot_exp sl exp
      | _ -> None
    in
    match result with None -> Some (l, annot) | _ -> result
  )

and find_annot_lexp sl (LE_aux (aux, (l, annot))) =
  if not (subloc sl l) then None
  else (
    let result =
      match aux with
      | LE_vector_range (lexp, exp1, exp2) ->
          option_chain (find_annot_lexp sl lexp) (option_mapm (find_annot_exp sl) [exp1; exp2])
      | LE_deref exp -> find_annot_exp sl exp
      | LE_tuple lexps -> option_mapm (find_annot_lexp sl) lexps
      | LE_app (_, exps) -> option_mapm (find_annot_exp sl) exps
      | _ -> None
    in
    match result with None -> Some (l, annot) | _ -> result
  )

and find_annot_pat sl (P_aux (aux, (l, annot))) =
  if not (subloc sl l) then None
  else (
    let result = match aux with P_vector_concat pats -> option_mapm (find_annot_pat sl) pats | _ -> None in
    match result with None -> Some (l, annot) | _ -> result
  )

and find_annot_pexp sl (Pat_aux (aux, (l, _))) =
  if not (subloc sl l) then None
  else (
    match aux with
    | Pat_exp (pat, exp) -> option_chain (find_annot_pat sl pat) (find_annot_exp sl exp)
    | Pat_when (pat, guard, exp) -> option_chain (find_annot_pat sl pat) (option_mapm (find_annot_exp sl) [guard; exp])
  )

let find_annot_funcl sl (FCL_aux (FCL_funcl (_, pexp), (def_annot, annot))) =
  let l = def_annot.loc in
  if not (subloc sl l) then None else (match find_annot_pexp sl pexp with None -> Some (l, annot) | result -> result)

let find_annot_fundef sl (FD_aux (FD_function (_, _, funcls), (l, annot))) =
  if not (subloc sl l) then None
  else (match option_mapm (find_annot_funcl sl) funcls with None -> Some (l, annot) | result -> result)

let find_annot_scattered sl (SD_aux (aux, (l, annot))) =
  if not (subloc sl l) then None
  else (
    let result = match aux with SD_funcl fcl -> find_annot_funcl sl fcl | _ -> None in
    match result with None -> Some (l, annot) | _ -> result
  )

let rec find_annot_defs sl = function
  | DEF_aux (DEF_fundef fdef, _) :: defs -> begin
      match find_annot_fundef sl fdef with None -> find_annot_defs sl defs | result -> result
    end
  | DEF_aux (DEF_scattered sdef, _) :: defs -> begin
      match find_annot_scattered sl sdef with None -> find_annot_defs sl defs | result -> result
    end
  | _ :: defs -> find_annot_defs sl defs
  | [] -> None

let find_annot_ast sl { defs; _ } = find_annot_defs sl defs

let string_of_lx lx =
  let open Lexing in
  Printf.sprintf "%s,%d,%d,%d" lx.pos_fname lx.pos_lnum lx.pos_bol lx.pos_cnum

let rec simple_string_of_loc = function
  | Parse_ast.Unknown -> "Unknown"
  | Parse_ast.Unique (n, l) -> "Unique(" ^ string_of_int n ^ ", " ^ simple_string_of_loc l ^ ")"
  | Parse_ast.Generated l -> "Generated(" ^ simple_string_of_loc l ^ ")"
  | Parse_ast.Hint (_, l1, l2) -> "Hint(_," ^ simple_string_of_loc l1 ^ "," ^ simple_string_of_loc l2 ^ ")"
  | Parse_ast.Range (lx1, lx2) -> "Range(" ^ string_of_lx lx1 ^ "->" ^ string_of_lx lx2 ^ ")"
