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

open Libsail

open Ast
open Ast_util
open Jib
open Jib_compile
open Jib_util
open Jib_visitor
open Type_check
open PPrint
open Value2

open Anf

module Big_int = Nat_big_num

let opt_static = ref false
let static () = if !opt_static then "static " else ""
let opt_no_main = ref false
let opt_no_lib = ref false
let opt_no_rts = ref false
let opt_prefix = ref "z"
let opt_extra_params = ref None
let opt_extra_arguments = ref None
let opt_branch_coverage = ref None

let extra_params () = match !opt_extra_params with Some str -> str ^ ", " | _ -> ""

let extra_arguments is_extern = match !opt_extra_arguments with Some str when not is_extern -> str ^ ", " | _ -> ""

(* Optimization flags *)
let optimize_primops = ref false
let optimize_hoist_allocations = ref false
let optimize_struct_updates = ref false
let optimize_alias = ref false
let optimize_fixed_int = ref false
let optimize_fixed_bits = ref false

let gensym, _ = symbol_generator "cb"
let ngensym () = name (gensym ())

let c_error ?loc:(l = Parse_ast.Unknown) message = raise (Reporting.err_general l ("\nC backend: " ^ message))

let zencode_id id = Util.zencode_string (string_of_id id)

let zencode_uid (id, ctyps) =
  match ctyps with
  | [] -> Util.zencode_string (string_of_id id)
  | _ -> Util.zencode_string (string_of_id id ^ "#" ^ Util.string_of_list "_" string_of_ctyp ctyps)

let ctor_bindings = List.fold_left (fun map (id, ctyp) -> Bindings.add id ctyp map) Bindings.empty

(**************************************************************************)
(* 2. Converting sail types to C types                                    *)
(**************************************************************************)

let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))

(** This function is used to split types into those we allocate on the
   stack, versus those which need to live on the heap, or otherwise
   require some additional memory management *)
let rec is_stack_ctyp ctyp =
  match ctyp with
  | CT_fbits _ | CT_sbits _ | CT_bit | CT_unit | CT_bool | CT_enum _ -> true
  | CT_fint n -> n <= 64
  | CT_lint when !optimize_fixed_int -> true
  | CT_lint -> false
  | CT_lbits when !optimize_fixed_bits -> true
  | CT_lbits -> false
  | CT_real | CT_string | CT_list _ | CT_vector _ | CT_fvector _ -> false
  | CT_struct (_, fields) -> List.for_all (fun (_, ctyp) -> is_stack_ctyp ctyp) fields
  | CT_variant (_, _) ->
      false
      (* List.for_all (fun (_, ctyp) -> is_stack_ctyp ctyp) ctors *)
      (* FIXME *)
  | CT_tup ctyps -> List.for_all is_stack_ctyp ctyps
  | CT_ref _ -> true
  | CT_poly _ -> true
  | CT_float _ -> true
  | CT_rounding_mode -> true
  | CT_constant n -> Big_int.less_equal (min_int 64) n && Big_int.greater_equal n (max_int 64)

let v_mask_lower i = V_lit (VL_bits (Util.list_init i (fun _ -> Sail2_values.B1)), CT_fbits i)

let hex_char =
  let open Sail2_values in
  function
  | '0' -> [B0; B0; B0; B0]
  | '1' -> [B0; B0; B0; B1]
  | '2' -> [B0; B0; B1; B0]
  | '3' -> [B0; B0; B1; B1]
  | '4' -> [B0; B1; B0; B0]
  | '5' -> [B0; B1; B0; B1]
  | '6' -> [B0; B1; B1; B0]
  | '7' -> [B0; B1; B1; B1]
  | '8' -> [B1; B0; B0; B0]
  | '9' -> [B1; B0; B0; B1]
  | 'A' | 'a' -> [B1; B0; B1; B0]
  | 'B' | 'b' -> [B1; B0; B1; B1]
  | 'C' | 'c' -> [B1; B1; B0; B0]
  | 'D' | 'd' -> [B1; B1; B0; B1]
  | 'E' | 'e' -> [B1; B1; B1; B0]
  | 'F' | 'f' -> [B1; B1; B1; B1]
  | _ -> failwith "Invalid hex character"

let literal_to_fragment (L_aux (l_aux, _)) =
  match l_aux with
  | L_num n when Big_int.less_equal (min_int 64) n && Big_int.less_equal n (max_int 64) ->
      Some (V_lit (VL_int n, CT_fint 64))
  | L_hex str when String.length str <= 16 ->
      let padding = 16 - String.length str in
      let padding = Util.list_init padding (fun _ -> Sail2_values.B0) in
      let content = Util.string_to_list str |> List.map hex_char |> List.concat in
      Some (V_lit (VL_bits (padding @ content), CT_fbits (String.length str * 4)))
  | L_unit -> Some (V_lit (VL_unit, CT_unit))
  | L_true -> Some (V_lit (VL_bool true, CT_bool))
  | L_false -> Some (V_lit (VL_bool false, CT_bool))
  | _ -> None

module C_config (Opts : sig
  val branch_coverage : out_channel option
end) : CONFIG = struct
  (** Convert a sail type into a C-type. This function can be quite
     slow, because it uses ctx.local_env and SMT to analyse the Sail
     types and attempts to fit them into the smallest possible C
     types, provided ctx.optimize_smt is true (default) **)
  let rec convert_typ ctx typ =
    let (Typ_aux (typ_aux, l) as typ) = Env.expand_synonyms ctx.local_env typ in
    match typ_aux with
    | Typ_id id when string_of_id id = "bit" -> CT_bit
    | Typ_id id when string_of_id id = "bool" -> CT_bool
    | Typ_id id when string_of_id id = "int" -> CT_lint
    | Typ_id id when string_of_id id = "nat" -> CT_lint
    | Typ_id id when string_of_id id = "unit" -> CT_unit
    | Typ_id id when string_of_id id = "string" -> CT_string
    | Typ_id id when string_of_id id = "real" -> CT_real
    | Typ_app (id, _) when string_of_id id = "atom_bool" -> CT_bool
    | Typ_app (id, args) when string_of_id id = "itself" -> convert_typ ctx (Typ_aux (Typ_app (mk_id "atom", args), l))
    | Typ_app (id, _) when string_of_id id = "range" || string_of_id id = "atom" || string_of_id id = "implicit" ->
      begin
        match destruct_range Env.empty typ with
        | None -> assert false (* Checked if range type in guard *)
        | Some (kids, constr, n, m) -> (
            let ctx =
              {
                ctx with
                local_env = add_existential Parse_ast.Unknown (List.map (mk_kopt K_int) kids) constr ctx.local_env;
              }
            in
            match (nexp_simp n, nexp_simp m) with
            | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
              when Big_int.less_equal (min_int 64) n && Big_int.less_equal m (max_int 64) ->
                CT_fint 64
            | n, m ->
                if
                  prove __POS__ ctx.local_env (nc_lteq (nconstant (min_int 64)) n)
                  && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_int 64)))
                then CT_fint 64
                else CT_lint
          )
      end
    | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "list" -> CT_list (ctyp_suprema (convert_typ ctx typ))
    (* When converting a sail bitvector type into C, we have three options in order of efficiency:
       - If the length is obviously static and smaller than 64, use the fixed bits type (aka uint64_t), fbits.
       - If the length is less than 64, then use a small bits type, sbits.
       - If the length may be larger than 64, use a large bits type lbits. *)
    | Typ_app (id, [A_aux (A_nexp n, _)]) when string_of_id id = "bitvector" -> begin
        match nexp_simp n with
        | Nexp_aux (Nexp_constant n, _) when Big_int.less_equal n (Big_int.of_int 64) -> CT_fbits (Big_int.to_int n)
        | n when prove __POS__ ctx.local_env (nc_lteq n (nint 64)) -> CT_sbits 64
        | _ -> CT_lbits
      end
    | Typ_app (id, [A_aux (A_nexp _, _); A_aux (A_typ typ, _)]) when string_of_id id = "vector" ->
        CT_vector (convert_typ ctx typ)
    | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "register" -> CT_ref (convert_typ ctx typ)
    | Typ_id id when Bindings.mem id ctx.records ->
        CT_struct (id, Bindings.find id ctx.records |> snd |> Bindings.bindings)
    | Typ_app (id, typ_args) when Bindings.mem id ctx.records ->
        let typ_params, fields = Bindings.find id ctx.records in
        let quants =
          List.fold_left2
            (fun quants typ_param typ_arg ->
              match typ_arg with
              | A_aux (A_typ typ, _) -> KBindings.add typ_param (convert_typ ctx typ) quants
              | _ -> Reporting.unreachable l __POS__ "Non-type argument for record here should be impossible"
            )
            ctx.quants typ_params (List.filter is_typ_arg_typ typ_args)
        in
        let fix_ctyp ctyp = if is_polymorphic ctyp then ctyp_suprema (subst_poly quants ctyp) else ctyp in
        CT_struct (id, Bindings.map fix_ctyp fields |> Bindings.bindings)
    | Typ_id id when Bindings.mem id ctx.variants ->
        CT_variant (id, Bindings.find id ctx.variants |> snd |> Bindings.bindings)
    | Typ_app (id, typ_args) when Bindings.mem id ctx.variants ->
        let typ_params, ctors = Bindings.find id ctx.variants in
        let quants =
          List.fold_left2
            (fun quants typ_param typ_arg ->
              match typ_arg with
              | A_aux (A_typ typ, _) -> KBindings.add typ_param (convert_typ ctx typ) quants
              | _ -> Reporting.unreachable l __POS__ "Non-type argument for variant here should be impossible"
            )
            ctx.quants typ_params (List.filter is_typ_arg_typ typ_args)
        in
        let fix_ctyp ctyp = if is_polymorphic ctyp then ctyp_suprema (subst_poly quants ctyp) else ctyp in
        CT_variant (id, Bindings.map fix_ctyp ctors |> Bindings.bindings)
    | Typ_id id when Bindings.mem id ctx.enums -> CT_enum (id, Bindings.find id ctx.enums |> IdSet.elements)
    | Typ_tuple typs -> CT_tup (List.map (convert_typ ctx) typs)
    | Typ_exist _ -> begin
        (* Use Type_check.destruct_exist when optimising with SMT, to
           ensure that we don't cause any type variable clashes in
           local_env, and that we can optimize the existential based
           upon its constraints. *)
        match destruct_exist typ with
        | Some (kids, nc, typ) ->
            let env = add_existential l kids nc ctx.local_env in
            convert_typ { ctx with local_env = env } typ
        | None -> raise (Reporting.err_unreachable l __POS__ "Existential cannot be destructured!")
      end
    | Typ_var kid -> CT_poly kid
    | _ -> c_error ~loc:l ("No C type for type " ^ string_of_typ typ)

  (**************************************************************************)
  (* 3. Optimization of primitives and literals                             *)
  (**************************************************************************)

  let c_literals ctx =
    let rec c_literal env l = function
      | AV_lit (lit, typ) as v when is_stack_ctyp (convert_typ { ctx with local_env = env } typ) -> begin
          match literal_to_fragment lit with Some cval -> AV_cval (cval, typ) | None -> v
        end
      | AV_tuple avals -> AV_tuple (List.map (c_literal env l) avals)
      | v -> v
    in
    map_aval c_literal

  let rec is_bitvector = function
    | [] -> true
    | AV_lit (L_aux (L_zero, _), _) :: avals -> is_bitvector avals
    | AV_lit (L_aux (L_one, _), _) :: avals -> is_bitvector avals
    | _ :: _ -> false

  let value_of_aval_bit = function
    | AV_lit (L_aux (L_zero, _), _) -> Sail2_values.B0
    | AV_lit (L_aux (L_one, _), _) -> Sail2_values.B1
    | _ -> assert false

  (** Used to make sure the -Ofixed_int and -Ofixed_bits don't
     interfere with assumptions made about optimizations in the common
     case. *)
  let never_optimize = function CT_lbits | CT_lint -> true | _ -> false

  let rec c_aval ctx = function
    | AV_lit (lit, typ) as v -> begin
        match literal_to_fragment lit with Some cval -> AV_cval (cval, typ) | None -> v
      end
    | AV_cval (cval, typ) -> AV_cval (cval, typ)
    (* An id can be converted to a C fragment if its type can be
       stack-allocated. *)
    | AV_id (id, lvar) as v -> begin
        match lvar with
        | Local (_, typ) ->
            let ctyp = convert_typ ctx typ in
            if is_stack_ctyp ctyp && not (never_optimize ctyp) then begin
              try
                (* We need to check that id's type hasn't changed due to flow typing *)
                let _, ctyp' = Bindings.find id ctx.locals in
                if ctyp_equal ctyp ctyp' then AV_cval (V_id (name_or_global ctx id, ctyp), typ)
                else
                  (* id's type changed due to flow typing, so it's
                     really still heap allocated! *)
                  v
              with (* Hack: Assuming global letbindings don't change from flow typing... *)
              | Not_found ->
                AV_cval (V_id (name_or_global ctx id, ctyp), typ)
            end
            else v
        | Register typ ->
            let ctyp = convert_typ ctx typ in
            if is_stack_ctyp ctyp && not (never_optimize ctyp) then AV_cval (V_id (global id, ctyp), typ) else v
        | _ -> v
      end
    | AV_vector (v, typ) when is_bitvector v && List.length v <= 64 ->
        let bitstring = VL_bits (List.map value_of_aval_bit v) in
        AV_cval (V_lit (bitstring, CT_fbits (List.length v)), typ)
    | AV_tuple avals -> AV_tuple (List.map (c_aval ctx) avals)
    | aval -> aval

  (* Map over all the functions in an aexp. *)
  let rec analyze_functions ctx f (AE_aux (aexp, env, l)) =
    let ctx = { ctx with local_env = env } in
    let aexp =
      match aexp with
      | AE_app (id, vs, typ) -> f ctx id vs typ
      | AE_typ (aexp, typ) -> AE_typ (analyze_functions ctx f aexp, typ)
      | AE_assign (alexp, aexp) -> AE_assign (alexp, analyze_functions ctx f aexp)
      | AE_short_circuit (op, aval, aexp) -> AE_short_circuit (op, aval, analyze_functions ctx f aexp)
      | AE_let (mut, id, typ1, aexp1, (AE_aux (_, env2, _) as aexp2), typ2) ->
          let aexp1 = analyze_functions ctx f aexp1 in
          (* Use aexp2's environment because it will contain constraints for id *)
          let ctyp1 = convert_typ { ctx with local_env = env2 } typ1 in
          let ctx = { ctx with locals = Bindings.add id (mut, ctyp1) ctx.locals } in
          AE_let (mut, id, typ1, aexp1, analyze_functions ctx f aexp2, typ2)
      | AE_block (aexps, aexp, typ) ->
          AE_block (List.map (analyze_functions ctx f) aexps, analyze_functions ctx f aexp, typ)
      | AE_if (aval, aexp1, aexp2, typ) ->
          AE_if (aval, analyze_functions ctx f aexp1, analyze_functions ctx f aexp2, typ)
      | AE_loop (loop_typ, aexp1, aexp2) ->
          AE_loop (loop_typ, analyze_functions ctx f aexp1, analyze_functions ctx f aexp2)
      | AE_for (id, aexp1, aexp2, aexp3, order, aexp4) ->
          let aexp1 = analyze_functions ctx f aexp1 in
          let aexp2 = analyze_functions ctx f aexp2 in
          let aexp3 = analyze_functions ctx f aexp3 in
          (* Currently we assume that loop indexes are always safe to put into an int64 *)
          let ctx = { ctx with locals = Bindings.add id (Immutable, CT_fint 64) ctx.locals } in
          let aexp4 = analyze_functions ctx f aexp4 in
          AE_for (id, aexp1, aexp2, aexp3, order, aexp4)
      | AE_match (aval, cases, typ) ->
          let analyze_case ((AP_aux (_, env, _) as pat), aexp1, aexp2) =
            let pat_bindings = Bindings.bindings (apat_types pat) in
            let ctx = { ctx with local_env = env } in
            let ctx =
              List.fold_left
                (fun ctx (id, typ) -> { ctx with locals = Bindings.add id (Immutable, convert_typ ctx typ) ctx.locals })
                ctx pat_bindings
            in
            (pat, analyze_functions ctx f aexp1, analyze_functions ctx f aexp2)
          in
          AE_match (aval, List.map analyze_case cases, typ)
      | AE_try (aexp, cases, typ) ->
          AE_try
            ( analyze_functions ctx f aexp,
              List.map
                (fun (pat, aexp1, aexp2) -> (pat, analyze_functions ctx f aexp1, analyze_functions ctx f aexp2))
                cases,
              typ
            )
      | (AE_field _ | AE_struct_update _ | AE_val _ | AE_return _ | AE_exit _ | AE_throw _) as v -> v
    in
    AE_aux (aexp, env, l)

  let analyze_primop' ctx id args typ =
    let no_change = AE_app (id, args, typ) in
    let args = List.map (c_aval ctx) args in
    let extern = if ctx_is_extern id ctx then ctx_get_extern id ctx else failwith "Not extern" in

    match (extern, args) with
    | "eq_bits", [AV_cval (v1, _); AV_cval (v2, _)] when ctyp_equal (cval_ctyp v1) (cval_ctyp v2) -> begin
        match cval_ctyp v1 with
        | CT_fbits _ | CT_sbits _ -> AE_val (AV_cval (V_call (Eq, [v1; v2]), typ))
        | _ -> no_change
      end
    | "neq_bits", [AV_cval (v1, _); AV_cval (v2, _)] when ctyp_equal (cval_ctyp v1) (cval_ctyp v2) -> begin
        match cval_ctyp v1 with
        | CT_fbits _ | CT_sbits _ -> AE_val (AV_cval (V_call (Neq, [v1; v2]), typ))
        | _ -> no_change
      end
    | "eq_int", [AV_cval (v1, _); AV_cval (v2, _)] -> AE_val (AV_cval (V_call (Eq, [v1; v2]), typ))
    | "eq_bit", [AV_cval (v1, _); AV_cval (v2, _)] -> AE_val (AV_cval (V_call (Eq, [v1; v2]), typ))
    | "zeros", [_] -> begin
        match destruct_vector ctx.tc_env typ with
        | Some (Nexp_aux (Nexp_constant n, _), Typ_aux (Typ_id id, _))
          when string_of_id id = "bit" && Big_int.less_equal n (Big_int.of_int 64) ->
            let n = Big_int.to_int n in
            AE_val (AV_cval (V_lit (VL_bits (Util.list_init n (fun _ -> Sail2_values.B0)), CT_fbits n), typ))
        | _ -> no_change
      end
    | "zero_extend", [AV_cval (v, _); _] -> begin
        match destruct_vector ctx.tc_env typ with
        | Some (Nexp_aux (Nexp_constant n, _), Typ_aux (Typ_id id, _))
          when string_of_id id = "bit" && Big_int.less_equal n (Big_int.of_int 64) ->
            AE_val (AV_cval (V_call (Zero_extend (Big_int.to_int n), [v]), typ))
        | _ -> no_change
      end
    | "sign_extend", [AV_cval (v, _); _] -> begin
        match destruct_vector ctx.tc_env typ with
        | Some (Nexp_aux (Nexp_constant n, _), Typ_aux (Typ_id id, _))
          when string_of_id id = "bit" && Big_int.less_equal n (Big_int.of_int 64) ->
            AE_val (AV_cval (V_call (Sign_extend (Big_int.to_int n), [v]), typ))
        | _ -> no_change
      end
    | "lteq", [AV_cval (v1, _); AV_cval (v2, _)] -> AE_val (AV_cval (V_call (Ilteq, [v1; v2]), typ))
    | "gteq", [AV_cval (v1, _); AV_cval (v2, _)] -> AE_val (AV_cval (V_call (Igteq, [v1; v2]), typ))
    | "lt", [AV_cval (v1, _); AV_cval (v2, _)] -> AE_val (AV_cval (V_call (Ilt, [v1; v2]), typ))
    | "gt", [AV_cval (v1, _); AV_cval (v2, _)] -> AE_val (AV_cval (V_call (Igt, [v1; v2]), typ))
    | "append", [AV_cval (v1, _); AV_cval (v2, _)] -> begin
        match convert_typ ctx typ with
        | CT_fbits _ | CT_sbits _ -> AE_val (AV_cval (V_call (Concat, [v1; v2]), typ))
        | _ -> no_change
      end
    | "not_bits", [AV_cval (v, _)] -> AE_val (AV_cval (V_call (Bvnot, [v]), typ))
    | "add_bits", [AV_cval (v1, _); AV_cval (v2, _)] when ctyp_equal (cval_ctyp v1) (cval_ctyp v2) ->
        AE_val (AV_cval (V_call (Bvadd, [v1; v2]), typ))
    | "sub_bits", [AV_cval (v1, _); AV_cval (v2, _)] when ctyp_equal (cval_ctyp v1) (cval_ctyp v2) ->
        AE_val (AV_cval (V_call (Bvsub, [v1; v2]), typ))
    | "and_bits", [AV_cval (v1, _); AV_cval (v2, _)] when ctyp_equal (cval_ctyp v1) (cval_ctyp v2) ->
        AE_val (AV_cval (V_call (Bvand, [v1; v2]), typ))
    | "or_bits", [AV_cval (v1, _); AV_cval (v2, _)] when ctyp_equal (cval_ctyp v1) (cval_ctyp v2) ->
        AE_val (AV_cval (V_call (Bvor, [v1; v2]), typ))
    | "xor_bits", [AV_cval (v1, _); AV_cval (v2, _)] when ctyp_equal (cval_ctyp v1) (cval_ctyp v2) ->
        AE_val (AV_cval (V_call (Bvxor, [v1; v2]), typ))
    | "vector_subrange", [AV_cval (vec, _); AV_cval (_, _); AV_cval (t, _)] -> begin
        match convert_typ ctx typ with
        | CT_fbits n -> AE_val (AV_cval (V_call (Slice n, [vec; t]), typ))
        | _ -> no_change
      end
    | "slice", [AV_cval (vec, _); AV_cval (start, _); AV_cval (len, _)] -> begin
        match convert_typ ctx typ with
        | CT_fbits n -> AE_val (AV_cval (V_call (Slice n, [vec; start]), typ))
        | CT_sbits 64 -> AE_val (AV_cval (V_call (Sslice 64, [vec; start; len]), typ))
        | _ -> no_change
      end
    | "vector_access", [AV_cval (vec, _); AV_cval (n, _)] -> AE_val (AV_cval (V_call (Bvaccess, [vec; n]), typ))
    | "add_int", [AV_cval (op1, _); AV_cval (op2, _)] -> begin
        match destruct_range ctx.local_env typ with
        | None -> no_change
        | Some (_, _, n, m) -> (
            match (nexp_simp n, nexp_simp m) with
            | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
              when Big_int.less_equal (min_int 64) n && Big_int.less_equal m (max_int 64) ->
                AE_val (AV_cval (V_call (Iadd, [op1; op2]), typ))
            | n, m
              when prove __POS__ ctx.local_env (nc_lteq (nconstant (min_int 64)) n)
                   && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_int 64))) ->
                AE_val (AV_cval (V_call (Iadd, [op1; op2]), typ))
            | _ -> no_change
          )
      end
    | "replicate_bits", [AV_cval (vec, vtyp); _] -> begin
        match (destruct_vector ctx.tc_env typ, destruct_vector ctx.tc_env vtyp) with
        | Some (Nexp_aux (Nexp_constant n, _), _), Some (Nexp_aux (Nexp_constant m, _), _)
          when Big_int.less_equal n (Big_int.of_int 64) ->
            let times = Big_int.div n m in
            if Big_int.equal (Big_int.mul m times) n then
              AE_val (AV_cval (V_call (Replicate (Big_int.to_int times), [vec]), typ))
            else no_change
        | _, _ -> no_change
      end
    | "undefined_bit", _ -> AE_val (AV_cval (V_lit (VL_bit Sail2_values.B0, CT_bit), typ))
    | "undefined_bool", _ -> AE_val (AV_cval (V_lit (VL_bool false, CT_bool), typ))
    | _, _ -> no_change

  let analyze_primop ctx id args typ =
    let no_change = AE_app (id, args, typ) in
    if !optimize_primops then (try analyze_primop' ctx id args typ with Failure _ -> no_change) else no_change

  let optimize_anf ctx aexp = analyze_functions ctx analyze_primop (c_literals ctx aexp)

  let unroll_loops = None
  let make_call_precise _ _ = true
  let ignore_64 = false
  let struct_value = false
  let tuple_value = false
  let use_real = false
  let branch_coverage = Opts.branch_coverage
  let track_throw = true
end

(** Functions that have heap-allocated return types are implemented by
   passing a pointer a location where the return value should be
   stored. The ANF -> Sail IR pass for expressions simply outputs an
   I_return instruction for any return value, so this function walks
   over the IR ast for expressions and modifies the return statements
   into code that sets that pointer, as well as adds extra control
   flow to cleanup heap-allocated variables correctly when a function
   terminates early. See the generate_cleanup function for how this is
   done. *)
let fix_early_heap_return ret instrs =
  let end_function_label = label "end_function_" in
  let is_return_recur (I_aux (instr, _)) =
    match instr with
    | I_if _ | I_block _ | I_try_block _ | I_end _ | I_funcall _ | I_copy _ | I_undefined _ -> true
    | _ -> false
  in
  let rec rewrite_return instrs =
    match instr_split_at is_return_recur instrs with
    | instrs, [] -> instrs
    | before, I_aux (I_block instrs, _) :: after -> before @ [iblock (rewrite_return instrs)] @ rewrite_return after
    | before, I_aux (I_try_block instrs, (_, l)) :: after ->
        before @ [itry_block l (rewrite_return instrs)] @ rewrite_return after
    | before, I_aux (I_if (cval, then_instrs, else_instrs, ctyp), (_, l)) :: after ->
        before @ [iif l cval (rewrite_return then_instrs) (rewrite_return else_instrs) ctyp] @ rewrite_return after
    | before, I_aux (I_funcall (CL_id (Return _, ctyp), extern, fid, args), aux) :: after ->
        before @ [I_aux (I_funcall (CL_addr (CL_id (ret, CT_ref ctyp)), extern, fid, args), aux)] @ rewrite_return after
    | before, I_aux (I_copy (CL_id (Return _, ctyp), cval), aux) :: after ->
        before @ [I_aux (I_copy (CL_addr (CL_id (ret, CT_ref ctyp)), cval), aux)] @ rewrite_return after
    | before, I_aux ((I_end _ | I_undefined _), _) :: after ->
        before @ [igoto end_function_label] @ rewrite_return after
    | before, (I_aux ((I_copy _ | I_funcall _), _) as instr) :: after -> before @ (instr :: rewrite_return after)
    | _, _ -> assert false
  in
  rewrite_return instrs @ [ilabel end_function_label]

(* This is like fix_early_heap_return, but for stack allocated returns. *)
let fix_early_stack_return ret ret_ctyp instrs =
  let is_return_recur (I_aux (instr, _)) =
    match instr with I_if _ | I_block _ | I_try_block _ | I_end _ | I_funcall _ | I_copy _ -> true | _ -> false
  in
  let rec rewrite_return instrs =
    match instr_split_at is_return_recur instrs with
    | instrs, [] -> instrs
    | before, I_aux (I_block instrs, _) :: after -> before @ [iblock (rewrite_return instrs)] @ rewrite_return after
    | before, I_aux (I_try_block instrs, (_, l)) :: after ->
        before @ [itry_block l (rewrite_return instrs)] @ rewrite_return after
    | before, I_aux (I_if (cval, then_instrs, else_instrs, ctyp), (_, l)) :: after ->
        before @ [iif l cval (rewrite_return then_instrs) (rewrite_return else_instrs) ctyp] @ rewrite_return after
    | before, I_aux (I_funcall (CL_id (Return _, ctyp), extern, fid, args), aux) :: after ->
        before @ [I_aux (I_funcall (CL_id (ret, ctyp), extern, fid, args), aux)] @ rewrite_return after
    | before, I_aux (I_copy (CL_id (Return _, ctyp), cval), aux) :: after ->
        before @ [I_aux (I_copy (CL_id (ret, ctyp), cval), aux)] @ rewrite_return after
    | before, I_aux (I_end _, _) :: after -> before @ [ireturn (V_id (ret, ret_ctyp))] @ rewrite_return after
    | before, (I_aux ((I_copy _ | I_funcall _), _) as instr) :: after -> before @ (instr :: rewrite_return after)
    | _, _ -> assert false
  in
  rewrite_return instrs

let rec insert_heap_returns ret_ctyps = function
  | (CDEF_val (id, _, _, ret_ctyp) as cdef) :: cdefs ->
      cdef :: insert_heap_returns (Bindings.add id ret_ctyp ret_ctyps) cdefs
  | CDEF_fundef (id, None, args, body) :: cdefs ->
      let gs = gensym () in
      begin
        match Bindings.find_opt id ret_ctyps with
        | None -> raise (Reporting.err_general (id_loc id) ("Cannot find return type for function " ^ string_of_id id))
        | Some ret_ctyp when not (is_stack_ctyp ret_ctyp) ->
            CDEF_fundef (id, Some gs, args, fix_early_heap_return (name gs) body) :: insert_heap_returns ret_ctyps cdefs
        | Some ret_ctyp ->
            CDEF_fundef
              (id, None, args, fix_early_stack_return (name gs) ret_ctyp (idecl (id_loc id) ret_ctyp (name gs) :: body))
            :: insert_heap_returns ret_ctyps cdefs
      end
  | CDEF_fundef (id, _, _, _) :: _ ->
      Reporting.unreachable (id_loc id) __POS__ "Found function with return already re-written in insert_heap_returns"
  | cdef :: cdefs -> cdef :: insert_heap_returns ret_ctyps cdefs
  | [] -> []

(** To keep things neat we use GCC's local labels extension to limit
   the scope of labels. We do this by iterating over all the blocks
   and adding a __label__ declaration with all the labels local to
   that block. The add_local_labels function is called by the code
   generator just before it outputs C.

   See https://gcc.gnu.org/onlinedocs/gcc/Local-Labels.html **)
let add_local_labels' instrs =
  let is_label (I_aux (instr, _)) = match instr with I_label str -> [str] | _ -> [] in
  let labels = List.concat (List.map is_label instrs) in
  let local_label_decl = iraw ("__label__ " ^ String.concat ", " labels ^ ";\n") in
  if labels = [] then instrs else local_label_decl :: instrs

let add_local_labels instrs =
  match map_instrs add_local_labels' (iblock instrs) with I_aux (I_block instrs, _) -> instrs | _ -> assert false

(**************************************************************************)
(* 5. Optimizations                                                       *)
(**************************************************************************)

let hoist_ctyp = function CT_lint | CT_lbits | CT_struct _ -> true | _ -> false

let hoist_counter = ref 0
let hoist_id () =
  let id = mk_id ("gh#" ^ string_of_int !hoist_counter) in
  incr hoist_counter;
  name id

let hoist_allocations recursive_functions = function
  | CDEF_fundef (function_id, _, _, _) as cdef when IdSet.mem function_id recursive_functions -> [cdef]
  | CDEF_fundef (function_id, heap_return, args, body) ->
      let decls = ref [] in
      let cleanups = ref [] in
      let rec hoist = function
        | I_aux (I_decl (ctyp, decl_id), annot) :: instrs when hoist_ctyp ctyp ->
            let hid = hoist_id () in
            decls := idecl (snd annot) ctyp hid :: !decls;
            cleanups := iclear ctyp hid :: !cleanups;
            let instrs = instrs_rename decl_id hid instrs in
            I_aux (I_reset (ctyp, hid), annot) :: hoist instrs
        | I_aux (I_init (ctyp, decl_id, cval), annot) :: instrs when hoist_ctyp ctyp ->
            let hid = hoist_id () in
            decls := idecl (snd annot) ctyp hid :: !decls;
            cleanups := iclear ctyp hid :: !cleanups;
            let instrs = instrs_rename decl_id hid instrs in
            I_aux (I_reinit (ctyp, hid, cval), annot) :: hoist instrs
        | I_aux (I_clear (ctyp, _), _) :: instrs when hoist_ctyp ctyp -> hoist instrs
        | I_aux (I_block block, annot) :: instrs -> I_aux (I_block (hoist block), annot) :: hoist instrs
        | I_aux (I_try_block block, annot) :: instrs -> I_aux (I_try_block (hoist block), annot) :: hoist instrs
        | I_aux (I_if (cval, then_instrs, else_instrs, ctyp), annot) :: instrs ->
            I_aux (I_if (cval, hoist then_instrs, hoist else_instrs, ctyp), annot) :: hoist instrs
        | instr :: instrs -> instr :: hoist instrs
        | [] -> []
      in
      let body = hoist body in
      if !decls = [] then [CDEF_fundef (function_id, heap_return, args, body)]
      else
        [
          CDEF_startup (function_id, List.rev !decls);
          CDEF_fundef (function_id, heap_return, args, body);
          CDEF_finish (function_id, !cleanups);
        ]
  | cdef -> [cdef]

let removed = icomment "REMOVED"

let is_not_removed = function I_aux (I_comment "REMOVED", _) -> false | _ -> true

(** This optimization looks for patterns of the form:

    create x : t;
    x = y;
    // modifications to x, and no changes to y
    y = x;
    // no further changes to x
    kill x;

    If found, we can remove the variable x, and directly modify y instead. *)
let remove_alias =
  let pattern ctyp id =
    let alias = ref None in
    let rec scan ctyp id n instrs =
      match (n, !alias, instrs) with
      | 0, None, I_aux (I_copy (CL_id (id', ctyp'), V_id (a, ctyp'')), _) :: instrs
        when Name.compare id id' = 0 && ctyp_equal ctyp ctyp' && ctyp_equal ctyp' ctyp'' ->
          alias := Some a;
          scan ctyp id 1 instrs
      | 1, Some a, I_aux (I_copy (CL_id (a', ctyp'), V_id (id', ctyp'')), _) :: instrs
        when Name.compare a a' = 0 && Name.compare id id' = 0 && ctyp_equal ctyp ctyp' && ctyp_equal ctyp' ctyp'' ->
          scan ctyp id 2 instrs
      | 1, Some a, instr :: instrs -> if NameSet.mem a (instr_ids instr) then None else scan ctyp id 1 instrs
      | 2, Some _, I_aux (I_clear (ctyp', id'), _) :: instrs when Name.compare id id' = 0 && ctyp_equal ctyp ctyp' ->
          scan ctyp id 2 instrs
      | 2, Some _, instr :: instrs -> if NameSet.mem id (instr_ids instr) then None else scan ctyp id 2 instrs
      | 2, Some _, [] -> !alias
      | n, _, _ :: instrs when n = 0 || n > 2 -> scan ctyp id n instrs
      | _, _, I_aux (_, (_, l)) :: _ -> Reporting.unreachable l __POS__ "optimize_alias"
      | _, _, [] -> None
    in
    scan ctyp id 0
  in
  let remove_alias id alias = function
    | I_aux (I_copy (CL_id (id', _), V_id (alias', _)), _) when Name.compare id id' = 0 && Name.compare alias alias' = 0
      ->
        removed
    | I_aux (I_copy (CL_id (alias', _), V_id (id', _)), _) when Name.compare id id' = 0 && Name.compare alias alias' = 0
      ->
        removed
    | I_aux (I_clear (_, _), _) -> removed
    | instr -> instr
  in
  let rec opt = function
    | (I_aux (I_decl (ctyp, id), _) as instr) :: instrs as original_instrs -> begin
        match pattern ctyp id instrs with
        | None ->
            let instrs' = opt instrs in
            if instrs == instrs' then original_instrs else instr :: instrs'
        | Some alias ->
            let instrs = List.map (map_instr (remove_alias id alias)) instrs in
            filter_instrs is_not_removed (List.map (instr_rename id alias) instrs)
      end
    | I_aux (I_block block, aux) :: instrs -> I_aux (I_block (opt block), aux) :: opt instrs
    | I_aux (I_try_block block, aux) :: instrs -> I_aux (I_try_block (opt block), aux) :: opt instrs
    | I_aux (I_if (cval, then_instrs, else_instrs, ctyp), aux) :: instrs ->
        I_aux (I_if (cval, opt then_instrs, opt else_instrs, ctyp), aux) :: opt instrs
    | instr :: instrs -> instr :: opt instrs
    | [] -> []
  in
  function
  | CDEF_fundef (function_id, heap_return, args, body) -> [CDEF_fundef (function_id, heap_return, args, opt body)]
  | cdef -> [cdef]

(** This optimization looks for patterns of the form

    create x : t;
    create y : t;
    // modifications to y, no changes to x
    x = y;
    kill y;

    If found we can replace y by x *)
module Combine_variables = struct
  let pattern ctyp id =
    let combine = ref None in
    let rec scan id n instrs =
      match (n, !combine, instrs) with
      | 0, None, I_aux (I_block block, _) :: instrs -> begin
          match scan id 0 block with Some combine -> Some combine | None -> scan id 0 instrs
        end
      | 0, None, I_aux (I_decl (ctyp', id'), _) :: instrs when ctyp_equal ctyp ctyp' ->
          combine := Some id';
          scan id 1 instrs
      | 1, Some c, I_aux (I_copy (CL_id (id', ctyp'), V_id (c', ctyp'')), _) :: instrs
        when Name.compare c c' = 0 && Name.compare id id' = 0 && ctyp_equal ctyp ctyp' && ctyp_equal ctyp' ctyp'' ->
          scan id 2 instrs
      (* Ignore seemingly early clears of x, as this can happen along exception paths *)
      | 1, Some _, I_aux (I_clear (_, id'), _) :: instrs when Name.compare id id' = 0 -> scan id 1 instrs
      | 1, Some _, instr :: instrs -> if NameSet.mem id (instr_ids instr) then None else scan id 1 instrs
      | 2, Some c, I_aux (I_clear (ctyp', c'), _) :: _ when Name.compare c c' = 0 && ctyp_equal ctyp ctyp' -> !combine
      | 2, Some c, instr :: instrs -> if NameSet.mem c (instr_ids instr) then None else scan id 2 instrs
      | 2, Some _, [] -> !combine
      | n, _, _ :: instrs -> scan id n instrs
      | _, _, [] -> None
    in
    scan id 0

  let remove_variable id = function
    | I_aux (I_decl (_, id'), _) when Name.compare id id' = 0 -> removed
    | I_aux (I_clear (_, id'), _) when Name.compare id id' = 0 -> removed
    | instr -> instr

  let is_not_self_assignment = function
    | I_aux (I_copy (CL_id (id, _), V_id (id', _)), _) when Name.compare id id' = 0 -> false
    | _ -> true

  class visitor : jib_visitor =
    object
      inherit empty_jib_visitor

      method vinstrs =
        function
        | (I_aux (I_decl (ctyp, id), _) as instr) :: instrs -> begin
            match pattern ctyp id instrs with
            | None -> DoChildren
            | Some combine ->
                let instrs = map_no_copy (map_instr (remove_variable combine)) instrs in
                let instrs =
                  filter_instrs
                    (fun i -> is_not_removed i && is_not_self_assignment i)
                    (map_no_copy (instr_rename combine id) instrs)
                in
                change_do_children (instr :: instrs)
          end
        | _ -> DoChildren

      method vcdef = function CDEF_fundef _ -> DoChildren | _ -> SkipChildren
    end
end

let combine_variables = visit_cdefs (new Combine_variables.visitor)

let concatMap f xs = List.concat (List.map f xs)

let optimize recursive_functions cdefs =
  let nothing cdefs = cdefs in
  cdefs
  |> (if !optimize_alias then concatMap remove_alias else nothing)
  |> (if !optimize_alias then combine_variables else nothing)
  (* We need the runtime to initialize hoisted allocations *)
  |>
  if !optimize_hoist_allocations && not !opt_no_rts then concatMap (hoist_allocations recursive_functions) else nothing

(**************************************************************************)
(* 6. Code generation                                                     *)
(**************************************************************************)

let sgen_id id = Util.zencode_string (string_of_id id)
let sgen_uid uid = zencode_uid uid
let sgen_name id = string_of_name ~deref_current_exception:true ~zencode:true id
let codegen_id id = string (sgen_id id)

let sgen_function_id id =
  let str = Util.zencode_string (string_of_id id) in
  !opt_prefix ^ String.sub str 1 (String.length str - 1)

let sgen_function_uid uid =
  let str = zencode_uid uid in
  !opt_prefix ^ String.sub str 1 (String.length str - 1)

let codegen_function_id id = string (sgen_function_id id)

let rec sgen_ctyp = function
  | CT_unit -> "unit"
  | CT_bit -> "fbits"
  | CT_bool -> "bool"
  | CT_fbits _ -> "uint64_t"
  | CT_sbits _ -> "sbits"
  | CT_fint _ -> "int64_t"
  | CT_constant _ -> "int64_t"
  | CT_lint -> "sail_int"
  | CT_lbits -> "lbits"
  | CT_tup _ as tup -> "struct " ^ Util.zencode_string ("tuple_" ^ string_of_ctyp tup)
  | CT_struct (id, _) -> "struct " ^ sgen_id id
  | CT_enum (id, _) -> "enum " ^ sgen_id id
  | CT_variant (id, _) -> "struct " ^ sgen_id id
  | CT_list _ as l -> Util.zencode_string (string_of_ctyp l)
  | CT_vector _ as v -> Util.zencode_string (string_of_ctyp v)
  | CT_fvector (_, typ) -> sgen_ctyp (CT_vector typ)
  | CT_string -> "sail_string"
  | CT_real -> "real"
  | CT_ref ctyp -> sgen_ctyp ctyp ^ "*"
  | CT_float n -> "float" ^ string_of_int n ^ "_t"
  | CT_rounding_mode -> "uint_fast8_t"
  | CT_poly _ -> "POLY" (* c_error "Tried to generate code for non-monomorphic type" *)

let sgen_const_ctyp = function CT_string -> "const_sail_string" | ty -> sgen_ctyp ty

let rec sgen_ctyp_name = function
  | CT_unit -> "unit"
  | CT_bit -> "fbits"
  | CT_bool -> "bool"
  | CT_fbits _ -> "fbits"
  | CT_sbits _ -> "sbits"
  | CT_fint _ -> "mach_int"
  | CT_constant _ -> "mach_int"
  | CT_lint -> "sail_int"
  | CT_lbits -> "lbits"
  | CT_tup _ as tup -> Util.zencode_string ("tuple_" ^ string_of_ctyp tup)
  | CT_struct (id, _) -> sgen_id id
  | CT_enum (id, _) -> sgen_id id
  | CT_variant (id, _) -> sgen_id id
  | CT_list _ as l -> Util.zencode_string (string_of_ctyp l)
  | CT_vector _ as v -> Util.zencode_string (string_of_ctyp v)
  | CT_fvector (_, typ) -> sgen_ctyp_name (CT_vector typ)
  | CT_string -> "sail_string"
  | CT_real -> "real"
  | CT_ref ctyp -> "ref_" ^ sgen_ctyp_name ctyp
  | CT_float n -> "float" ^ string_of_int n
  | CT_rounding_mode -> "rounding_mode"
  | CT_poly _ -> "POLY" (* c_error "Tried to generate code for non-monomorphic type" *)

let sgen_mask n =
  if n = 0 then "UINT64_C(0)"
  else if n <= 64 then (
    let chars_F = String.make (n / 4) 'F' in
    let first = match n mod 4 with 0 -> "" | 1 -> "1" | 2 -> "3" | 3 -> "7" | _ -> assert false in
    "UINT64_C(0x" ^ first ^ chars_F ^ ")"
  )
  else failwith "Tried to create a mask literal for a vector greater than 64 bits."

let sgen_value = function
  | VL_bits [] -> "UINT64_C(0)"
  | VL_bits bs -> "UINT64_C(" ^ Sail2_values.show_bitlist bs ^ ")"
  | VL_int i -> if Big_int.equal i (min_int 64) then "INT64_MIN" else "INT64_C(" ^ Big_int.to_string i ^ ")"
  | VL_bool true -> "true"
  | VL_bool false -> "false"
  | VL_unit -> "UNIT"
  | VL_bit Sail2_values.B0 -> "UINT64_C(0)"
  | VL_bit Sail2_values.B1 -> "UINT64_C(1)"
  | VL_bit Sail2_values.BU -> failwith "Undefined bit found in value"
  | VL_real str -> str
  | VL_string str -> "\"" ^ str ^ "\""
  | VL_enum element -> Util.zencode_string element
  | VL_ref r -> "&" ^ Util.zencode_string r
  | VL_undefined -> Reporting.unreachable Parse_ast.Unknown __POS__ "Cannot generate C value for an undefined literal"

let rec sgen_cval = function
  | V_id (id, _) -> sgen_name id
  | V_lit (vl, _) -> sgen_value vl
  | V_call (op, cvals) -> sgen_call op cvals
  | V_field (f, field) -> Printf.sprintf "%s.%s" (sgen_cval f) (sgen_id field)
  | V_tuple_member (f, _, n) -> Printf.sprintf "%s.ztup%d" (sgen_cval f) n
  | V_ctor_kind (f, ctor, _) -> sgen_cval f ^ ".kind" ^ " != Kind_" ^ zencode_uid ctor
  | V_struct (fields, _) ->
      Printf.sprintf "{%s}"
        (Util.string_of_list ", " (fun (field, cval) -> zencode_id field ^ " = " ^ sgen_cval cval) fields)
  | V_ctor_unwrap (f, ctor, _) -> Printf.sprintf "%s.%s" (sgen_cval f) (sgen_uid ctor)
  | V_tuple _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Cannot generate C value for a tuple literal"

and sgen_call op cvals =
  let open Printf in
  match (op, cvals) with
  | Bnot, [v] -> "!(" ^ sgen_cval v ^ ")"
  | Band, vs -> "(" ^ Util.string_of_list " && " sgen_cval vs ^ ")"
  | Bor, vs -> "(" ^ Util.string_of_list " || " sgen_cval vs ^ ")"
  | List_hd, [v] -> sprintf "(%s).hd" ("*" ^ sgen_cval v)
  | List_tl, [v] -> sprintf "(%s).tl" ("*" ^ sgen_cval v)
  | List_is_empty, [v] -> sprintf "(%s == NULL)" (sgen_cval v)
  | Eq, [v1; v2] -> begin
      match cval_ctyp v1 with
      | CT_sbits _ -> sprintf "eq_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
      | _ -> sprintf "(%s == %s)" (sgen_cval v1) (sgen_cval v2)
    end
  | Neq, [v1; v2] -> begin
      match cval_ctyp v1 with
      | CT_sbits _ -> sprintf "neq_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
      | _ -> sprintf "(%s != %s)" (sgen_cval v1) (sgen_cval v2)
    end
  | Ilt, [v1; v2] -> sprintf "(%s < %s)" (sgen_cval v1) (sgen_cval v2)
  | Igt, [v1; v2] -> sprintf "(%s > %s)" (sgen_cval v1) (sgen_cval v2)
  | Ilteq, [v1; v2] -> sprintf "(%s <= %s)" (sgen_cval v1) (sgen_cval v2)
  | Igteq, [v1; v2] -> sprintf "(%s >= %s)" (sgen_cval v1) (sgen_cval v2)
  | Iadd, [v1; v2] -> sprintf "(%s + %s)" (sgen_cval v1) (sgen_cval v2)
  | Isub, [v1; v2] -> sprintf "(%s - %s)" (sgen_cval v1) (sgen_cval v2)
  | Unsigned 64, [vec] -> sprintf "((mach_int) %s)" (sgen_cval vec)
  | Signed 64, [vec] -> begin
      match cval_ctyp vec with CT_fbits n -> sprintf "fast_signed(%s, %d)" (sgen_cval vec) n | _ -> assert false
    end
  | Bvand, [v1; v2] -> begin
      match cval_ctyp v1 with
      | CT_fbits _ -> sprintf "(%s & %s)" (sgen_cval v1) (sgen_cval v2)
      | CT_sbits _ -> sprintf "and_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
      | _ -> assert false
    end
  | Bvnot, [v] -> begin
      match cval_ctyp v with
      | CT_fbits n -> sprintf "(~(%s) & %s)" (sgen_cval v) (sgen_cval (v_mask_lower n))
      | CT_sbits _ -> sprintf "not_sbits(%s)" (sgen_cval v)
      | _ -> assert false
    end
  | Bvor, [v1; v2] -> begin
      match cval_ctyp v1 with
      | CT_fbits _ -> sprintf "(%s | %s)" (sgen_cval v1) (sgen_cval v2)
      | CT_sbits _ -> sprintf "or_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
      | _ -> assert false
    end
  | Bvxor, [v1; v2] -> begin
      match cval_ctyp v1 with
      | CT_fbits _ -> sprintf "(%s ^ %s)" (sgen_cval v1) (sgen_cval v2)
      | CT_sbits _ -> sprintf "xor_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
      | _ -> assert false
    end
  | Bvadd, [v1; v2] -> begin
      match cval_ctyp v1 with
      | CT_fbits n -> sprintf "((%s + %s) & %s)" (sgen_cval v1) (sgen_cval v2) (sgen_cval (v_mask_lower n))
      | CT_sbits _ -> sprintf "add_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
      | _ -> assert false
    end
  | Bvsub, [v1; v2] -> begin
      match cval_ctyp v1 with
      | CT_fbits n -> sprintf "((%s - %s) & %s)" (sgen_cval v1) (sgen_cval v2) (sgen_cval (v_mask_lower n))
      | CT_sbits _ -> sprintf "sub_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
      | _ -> assert false
    end
  | Bvaccess, [vec; n] -> begin
      match cval_ctyp vec with
      | CT_fbits _ -> sprintf "(UINT64_C(1) & (%s >> %s))" (sgen_cval vec) (sgen_cval n)
      | CT_sbits _ -> sprintf "(UINT64_C(1) & (%s.bits >> %s))" (sgen_cval vec) (sgen_cval n)
      | _ -> assert false
    end
  | Slice len, [vec; start] -> begin
      match cval_ctyp vec with
      | CT_fbits _ -> sprintf "(safe_rshift(UINT64_MAX, 64 - %d) & (%s >> %s))" len (sgen_cval vec) (sgen_cval start)
      | CT_sbits _ ->
          sprintf "(safe_rshift(UINT64_MAX, 64 - %d) & (%s.bits >> %s))" len (sgen_cval vec) (sgen_cval start)
      | _ -> assert false
    end
  | Sslice 64, [vec; start; len] -> begin
      match cval_ctyp vec with
      | CT_fbits _ -> sprintf "sslice(%s, %s, %s)" (sgen_cval vec) (sgen_cval start) (sgen_cval len)
      | CT_sbits _ -> sprintf "sslice(%s.bits, %s, %s)" (sgen_cval vec) (sgen_cval start) (sgen_cval len)
      | _ -> assert false
    end
  | Set_slice, [vec; start; slice] -> begin
      match (cval_ctyp vec, cval_ctyp slice) with
      | CT_fbits _, CT_fbits m ->
          sprintf "((%s & ~(%s << %s)) | (%s << %s))" (sgen_cval vec) (sgen_mask m) (sgen_cval start) (sgen_cval slice)
            (sgen_cval start)
      | _ -> assert false
    end
  | Zero_extend n, [v] -> begin
      match cval_ctyp v with
      | CT_fbits _ -> sgen_cval v
      | CT_sbits _ -> sprintf "fast_zero_extend(%s, %d)" (sgen_cval v) n
      | _ -> assert false
    end
  | Sign_extend n, [v] -> begin
      match cval_ctyp v with
      | CT_fbits m -> sprintf "fast_sign_extend(%s, %d, %d)" (sgen_cval v) m n
      | CT_sbits _ -> sprintf "fast_sign_extend2(%s, %d)" (sgen_cval v) n
      | _ -> assert false
    end
  | Replicate n, [v] -> begin
      match cval_ctyp v with
      | CT_fbits m -> sprintf "fast_replicate_bits(UINT64_C(%d), %s, %d)" m (sgen_cval v) n
      | _ -> assert false
    end
  | Concat, [v1; v2] -> begin
      (* Optimized routines for all combinations of fixed and small bits
         appends, where the result is guaranteed to be smaller than 64. *)
      match (cval_ctyp v1, cval_ctyp v2) with
      | CT_fbits 0, CT_fbits _ -> sgen_cval v2
      | CT_fbits _, CT_fbits n2 -> sprintf "(%s << %d) | %s" (sgen_cval v1) n2 (sgen_cval v2)
      | CT_sbits 64, CT_fbits n2 -> sprintf "append_sf(%s, %s, %d)" (sgen_cval v1) (sgen_cval v2) n2
      | CT_fbits n1, CT_sbits 64 -> sprintf "append_fs(%s, %d, %s)" (sgen_cval v1) n1 (sgen_cval v2)
      | CT_sbits 64, CT_sbits 64 -> sprintf "append_ss(%s, %s)" (sgen_cval v1) (sgen_cval v2)
      | _ -> assert false
    end
  | _, _ -> failwith "Could not generate cval primop"

let sgen_cval_param cval =
  match cval_ctyp cval with
  | CT_lbits -> sgen_cval cval ^ ", " ^ string_of_bool true
  | CT_sbits _ -> sgen_cval cval ^ ", " ^ string_of_bool true
  | CT_fbits len -> sgen_cval cval ^ ", UINT64_C(" ^ string_of_int len ^ ") , " ^ string_of_bool true
  | _ -> sgen_cval cval

let rec sgen_clexp l = function
  | CL_id (Have_exception _, _) -> "have_exception"
  | CL_id (Current_exception _, _) -> "current_exception"
  | CL_id (Throw_location _, _) -> "throw_location"
  | CL_id (Return _, _) -> Reporting.unreachable l __POS__ "CL_return should have been removed"
  | CL_id (Name (id, _), _) -> "&" ^ sgen_id id
  | CL_id (Global (id, _), _) -> "&" ^ sgen_id id
  | CL_field (clexp, field) -> "&((" ^ sgen_clexp l clexp ^ ")->" ^ zencode_id field ^ ")"
  | CL_tuple (clexp, n) -> "&((" ^ sgen_clexp l clexp ^ ")->ztup" ^ string_of_int n ^ ")"
  | CL_addr clexp -> "(*(" ^ sgen_clexp l clexp ^ "))"
  | CL_void -> assert false
  | CL_rmw _ -> assert false

let rec sgen_clexp_pure l = function
  | CL_id (Have_exception _, _) -> "have_exception"
  | CL_id (Current_exception _, _) -> "current_exception"
  | CL_id (Throw_location _, _) -> "throw_location"
  | CL_id (Return _, _) -> Reporting.unreachable l __POS__ "CL_return should have been removed"
  | CL_id (Name (id, _), _) -> sgen_id id
  | CL_id (Global (id, _), _) -> sgen_id id
  | CL_field (clexp, field) -> sgen_clexp_pure l clexp ^ "." ^ zencode_id field
  | CL_tuple (clexp, n) -> sgen_clexp_pure l clexp ^ ".ztup" ^ string_of_int n
  | CL_addr clexp -> "(*(" ^ sgen_clexp_pure l clexp ^ "))"
  | CL_void -> assert false
  | CL_rmw _ -> assert false

(** Generate instructions to copy from a cval to a clexp. This will
   insert any needed type conversions from big integers to small
   integers (or vice versa), or from arbitrary-length bitvectors to
   and from uint64 bitvectors as needed. *)
let rec codegen_conversion l clexp cval =
  let open Printf in
  let ctyp_to = clexp_ctyp clexp in
  let ctyp_from = cval_ctyp cval in
  match (ctyp_to, ctyp_from) with
  (* When both types are equal, we don't need any conversion. *)
  | _, _ when ctyp_equal ctyp_to ctyp_from ->
      if is_stack_ctyp ctyp_to then ksprintf string "  %s = %s;" (sgen_clexp_pure l clexp) (sgen_cval cval)
      else ksprintf string "  COPY(%s)(%s, %s);" (sgen_ctyp_name ctyp_to) (sgen_clexp l clexp) (sgen_cval cval)
  | CT_ref _, _ -> codegen_conversion l (CL_addr clexp) cval
  | (CT_vector ctyp_elem_to | CT_fvector (_, ctyp_elem_to)), (CT_vector ctyp_elem_from | CT_fvector (_, ctyp_elem_from))
    ->
      let i = ngensym () in
      let from = ngensym () in
      let into = ngensym () in
      ksprintf string "  KILL(%s)(%s);" (sgen_ctyp_name ctyp_to) (sgen_clexp l clexp)
      ^^ hardline
      ^^ ksprintf string "  internal_vector_init_%s(%s, %s.len);" (sgen_ctyp_name ctyp_to) (sgen_clexp l clexp)
           (sgen_cval cval)
      ^^ hardline
      ^^ ksprintf string "  for (int %s = 0; %s < %s.len; %s++) {" (sgen_name i) (sgen_name i) (sgen_cval cval)
           (sgen_name i)
      ^^ hardline
      ^^ ( if is_stack_ctyp ctyp_elem_from then
             ksprintf string "    %s %s = %s.data[%s];" (sgen_ctyp ctyp_elem_from) (sgen_name from) (sgen_cval cval)
               (sgen_name i)
           else
             ksprintf string "    %s %s;" (sgen_ctyp ctyp_elem_from) (sgen_name from)
             ^^ hardline
             ^^ ksprintf string "    CREATE(%s)(&%s);" (sgen_ctyp_name ctyp_elem_from) (sgen_name from)
             ^^ hardline
             ^^ ksprintf string "    COPY(%s)(&%s, %s.data[%s]);" (sgen_ctyp_name ctyp_elem_from) (sgen_name from)
                  (sgen_cval cval) (sgen_name i)
         )
      ^^ hardline
      ^^ ksprintf string "    %s %s;" (sgen_ctyp ctyp_elem_to) (sgen_name into)
      ^^ ( if is_stack_ctyp ctyp_elem_to then empty
           else hardline ^^ ksprintf string "    CREATE(%s)(&%s);" (sgen_ctyp_name ctyp_elem_to) (sgen_name into)
         )
      ^^ nest 2 (hardline ^^ codegen_conversion l (CL_id (into, ctyp_elem_to)) (V_id (from, ctyp_elem_from)))
      ^^ hardline
      ^^ ( if is_stack_ctyp ctyp_elem_to then
             ksprintf string "    %s.data[%s] = %s;" (sgen_clexp_pure l clexp) (sgen_name i) (sgen_name into)
           else
             ksprintf string "    COPY(%s)(&((%s)->data[%s]), %s);" (sgen_ctyp_name ctyp_elem_to) (sgen_clexp l clexp)
               (sgen_name i) (sgen_name into)
             ^^ hardline
             ^^ ksprintf string "    KILL(%s)(&%s);" (sgen_ctyp_name ctyp_elem_to) (sgen_name into)
         )
      ^^ ( if is_stack_ctyp ctyp_elem_from then empty
           else hardline ^^ ksprintf string "    KILL(%s)(&%s);" (sgen_ctyp_name ctyp_elem_from) (sgen_name from)
         )
      ^^ hardline ^^ string "  }"
  (* If we have to convert between tuple types, convert the fields individually. *)
  | CT_tup ctyps_to, CT_tup ctyps_from when List.length ctyps_to = List.length ctyps_from ->
      let len = List.length ctyps_to in
      let conversions =
        List.mapi (fun i _ -> codegen_conversion l (CL_tuple (clexp, i)) (V_tuple_member (cval, len, i))) ctyps_from
      in
      string "  /* conversions */" ^^ hardline ^^ separate hardline conversions ^^ hardline
      ^^ string "  /* end conversions */"
  (* For anything not special cased, just try to call a appropriate CONVERT_OF function. *)
  | _, _ when is_stack_ctyp (clexp_ctyp clexp) ->
      ksprintf string "  %s = CONVERT_OF(%s, %s)(%s);" (sgen_clexp_pure l clexp) (sgen_ctyp_name ctyp_to)
        (sgen_ctyp_name ctyp_from) (sgen_cval_param cval)
  | _, _ ->
      ksprintf string "  CONVERT_OF(%s, %s)(%s, %s);" (sgen_ctyp_name ctyp_to) (sgen_ctyp_name ctyp_from)
        (sgen_clexp l clexp) (sgen_cval_param cval)

(* PPrint doesn't provide a nice way to filter out empty documents *)
let squash_empty docs = List.filter (fun doc -> requirement doc > 0) docs
let sq_separate_map sep f xs = separate sep (squash_empty (List.map f xs))

let rec codegen_instr fid ctx (I_aux (instr, (_, l))) =
  let open Printf in
  match instr with
  | I_decl (ctyp, id) when is_stack_ctyp ctyp -> ksprintf string "  %s %s;" (sgen_ctyp ctyp) (sgen_name id)
  | I_decl (ctyp, id) ->
      ksprintf string "  %s %s;" (sgen_ctyp ctyp) (sgen_name id)
      ^^ hardline
      ^^ ksprintf string "  CREATE(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_name id)
  | I_copy (clexp, cval) -> codegen_conversion l clexp cval
  | I_jump (cval, label) -> ksprintf string "  if (%s) goto %s;" (sgen_cval cval) label
  | I_if (cval, [], else_instrs, ctyp) -> codegen_instr fid ctx (iif l (V_call (Bnot, [cval])) else_instrs [] ctyp)
  | I_if (cval, [then_instr], [], _) ->
      ksprintf string "  if (%s)" (sgen_cval cval)
      ^^ space
      ^^ surround 2 0 lbrace (codegen_instr fid ctx then_instr) (twice space ^^ rbrace)
  | I_if (cval, then_instrs, [], _) ->
      string "  if" ^^ space
      ^^ parens (string (sgen_cval cval))
      ^^ space
      ^^ surround 2 0 lbrace (separate_map hardline (codegen_instr fid ctx) then_instrs) (twice space ^^ rbrace)
  | I_if (cval, then_instrs, else_instrs, _) ->
      string "  if" ^^ space
      ^^ parens (string (sgen_cval cval))
      ^^ space
      ^^ surround 2 0 lbrace (sq_separate_map hardline (codegen_instr fid ctx) then_instrs) (twice space ^^ rbrace)
      ^^ space ^^ string "else" ^^ space
      ^^ surround 2 0 lbrace (sq_separate_map hardline (codegen_instr fid ctx) else_instrs) (twice space ^^ rbrace)
  | I_block instrs ->
      string "  {" ^^ jump 2 2 (sq_separate_map hardline (codegen_instr fid ctx) instrs) ^^ hardline ^^ string "  }"
  | I_try_block instrs ->
      string "  { /* try */"
      ^^ jump 2 2 (sq_separate_map hardline (codegen_instr fid ctx) instrs)
      ^^ hardline ^^ string "  }"
  | I_funcall (x, special_extern, f, args) ->
      let c_args = Util.string_of_list ", " sgen_cval args in
      let ctyp = clexp_ctyp x in
      let is_extern = ctx_is_extern (fst f) ctx || special_extern in
      let fname =
        if special_extern then string_of_id (fst f)
        else if ctx_is_extern (fst f) ctx then ctx_get_extern (fst f) ctx
        else sgen_function_uid f
      in
      let fname =
        match (fname, ctyp) with
        | "internal_pick", _ -> Printf.sprintf "pick_%s" (sgen_ctyp_name ctyp)
        | "sail_cons", _ -> begin
            match snd f with
            | [ctyp] -> Util.zencode_string ("cons#" ^ string_of_ctyp ctyp)
            | _ -> c_error "cons without specified type"
          end
        | "eq_anything", _ -> begin
            match args with
            | cval :: _ -> Printf.sprintf "eq_%s" (sgen_ctyp_name (cval_ctyp cval))
            | _ -> c_error "eq_anything function with bad arity."
          end
        | "length", _ -> begin
            match args with
            | cval :: _ -> Printf.sprintf "length_%s" (sgen_ctyp_name (cval_ctyp cval))
            | _ -> c_error "length function with bad arity."
          end
        | "vector_access", CT_bit -> "bitvector_access"
        | "vector_access_inc", CT_bit -> "bitvector_access_inc"
        | "vector_access", _ -> begin
            match args with
            | cval :: _ -> Printf.sprintf "vector_access_%s" (sgen_ctyp_name (cval_ctyp cval))
            | _ -> c_error "vector access function with bad arity."
          end
        | "vector_update_subrange", _ -> Printf.sprintf "vector_update_subrange_%s" (sgen_ctyp_name ctyp)
        | "vector_update_subrange_inc", _ -> Printf.sprintf "vector_update_subrange_inc_%s" (sgen_ctyp_name ctyp)
        | "vector_subrange", _ -> Printf.sprintf "vector_subrange_%s" (sgen_ctyp_name ctyp)
        | "vector_subrange_inc", _ -> Printf.sprintf "vector_subrange_inc_%s" (sgen_ctyp_name ctyp)
        | "vector_update", CT_fbits _ -> "update_fbits"
        | "vector_update", CT_lbits -> "update_lbits"
        | "vector_update", _ -> Printf.sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
        | "vector_update_inc", CT_fbits _ -> "update_fbits_inc"
        | "vector_update_inc", CT_lbits -> "update_lbits_inc"
        | "string_of_bits", _ -> begin
            match cval_ctyp (List.nth args 0) with
            | CT_fbits _ -> "string_of_fbits"
            | CT_lbits -> "string_of_lbits"
            | _ -> assert false
          end
        | "decimal_string_of_bits", _ -> begin
            match cval_ctyp (List.nth args 0) with
            | CT_fbits _ -> "decimal_string_of_fbits"
            | CT_lbits -> "decimal_string_of_lbits"
            | _ -> assert false
          end
        | "internal_vector_update", _ -> Printf.sprintf "internal_vector_update_%s" (sgen_ctyp_name ctyp)
        | "internal_vector_init", _ -> Printf.sprintf "internal_vector_init_%s" (sgen_ctyp_name ctyp)
        | "undefined_bitvector", CT_fbits _ -> "UNDEFINED(fbits)"
        | "undefined_bitvector", CT_lbits -> "UNDEFINED(lbits)"
        | "undefined_bit", _ -> "UNDEFINED(fbits)"
        | "undefined_vector", _ -> Printf.sprintf "UNDEFINED(vector_%s)" (sgen_ctyp_name ctyp)
        | "undefined_list", _ -> Printf.sprintf "UNDEFINED(%s)" (sgen_ctyp_name ctyp)
        | fname, _ -> fname
      in
      if fname = "reg_deref" then
        if is_stack_ctyp ctyp then string (Printf.sprintf "  %s = *(%s);" (sgen_clexp_pure l x) c_args)
        else string (Printf.sprintf "  COPY(%s)(&%s, *(%s));" (sgen_ctyp_name ctyp) (sgen_clexp_pure l x) c_args)
      else if is_stack_ctyp ctyp then
        string (Printf.sprintf "  %s = %s(%s%s);" (sgen_clexp_pure l x) fname (extra_arguments is_extern) c_args)
      else string (Printf.sprintf "  %s(%s%s, %s);" fname (extra_arguments is_extern) (sgen_clexp l x) c_args)
  | I_clear (ctyp, _) when is_stack_ctyp ctyp -> empty
  | I_clear (ctyp, id) -> string (Printf.sprintf "  KILL(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_name id))
  | I_init (ctyp, id, cval) ->
      codegen_instr fid ctx (idecl l ctyp id) ^^ hardline ^^ codegen_conversion l (CL_id (id, ctyp)) cval
  | I_reinit (ctyp, id, cval) ->
      codegen_instr fid ctx (ireset l ctyp id) ^^ hardline ^^ codegen_conversion l (CL_id (id, ctyp)) cval
  | I_reset (ctyp, id) when is_stack_ctyp ctyp -> string (Printf.sprintf "  %s %s;" (sgen_ctyp ctyp) (sgen_name id))
  | I_reset (ctyp, id) -> string (Printf.sprintf "  RECREATE(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_name id))
  | I_return cval -> string (Printf.sprintf "  return %s;" (sgen_cval cval))
  | I_throw _ -> c_error ~loc:l "I_throw reached code generator"
  | I_undefined ctyp ->
      let rec codegen_exn_return ctyp =
        match ctyp with
        | CT_unit -> ("UNIT", [])
        | CT_bit -> ("UINT64_C(0)", [])
        | CT_fint _ -> ("INT64_C(0xdeadc0de)", [])
        | CT_lint when !optimize_fixed_int -> ("((sail_int) 0xdeadc0de)", [])
        | CT_fbits _ -> ("UINT64_C(0xdeadc0de)", [])
        | CT_sbits _ -> ("undefined_sbits()", [])
        | CT_lbits when !optimize_fixed_bits -> ("undefined_lbits(false)", [])
        | CT_bool -> ("false", [])
        | CT_enum (_, ctor :: _) -> (sgen_id ctor, [])
        | CT_tup ctyps when is_stack_ctyp ctyp ->
            let gs = ngensym () in
            let fold (n, ctyp) (inits, prev) =
              let init, prev' = codegen_exn_return ctyp in
              (Printf.sprintf ".ztup%d = %s" n init :: inits, prev @ prev')
            in
            let inits, prev = List.fold_right fold (List.mapi (fun i x -> (i, x)) ctyps) ([], []) in
            ( sgen_name gs,
              [
                Printf.sprintf "struct %s %s = { " (sgen_ctyp_name ctyp) (sgen_name gs)
                ^ Util.string_of_list ", " (fun x -> x) inits
                ^ " };";
              ]
              @ prev
            )
        | CT_struct (_, ctors) when is_stack_ctyp ctyp ->
            let gs = ngensym () in
            let fold (id, ctyp) (inits, prev) =
              let init, prev' = codegen_exn_return ctyp in
              (Printf.sprintf ".%s = %s" (sgen_id id) init :: inits, prev @ prev')
            in
            let inits, prev = List.fold_right fold ctors ([], []) in
            ( sgen_name gs,
              [
                Printf.sprintf "struct %s %s = { " (sgen_ctyp_name ctyp) (sgen_name gs)
                ^ Util.string_of_list ", " (fun x -> x) inits
                ^ " };";
              ]
              @ prev
            )
        | CT_ref _ -> ("NULL", [])
        | ctyp -> c_error ("Cannot create undefined value for type: " ^ string_of_ctyp ctyp)
      in
      let ret, prev = codegen_exn_return ctyp in
      separate_map hardline (fun str -> string ("  " ^ str)) (List.rev prev)
      ^^ hardline
      ^^ string (Printf.sprintf "  return %s;" ret)
  | I_comment str -> string ("  /* " ^ str ^ " */")
  | I_label str -> string (str ^ ": ;")
  | I_goto str -> string (Printf.sprintf "  goto %s;" str)
  | I_raw _ when ctx.no_raw -> empty
  | I_raw str -> string ("  " ^ str)
  | I_end _ -> assert false
  | I_exit _ -> string ("  sail_match_failure(\"" ^ String.escaped (string_of_id fid) ^ "\");")

let codegen_type_def = function
  | CTD_enum (id, (first_id :: _ as ids)) ->
      let codegen_eq =
        let name = sgen_id id in
        string (Printf.sprintf "static bool eq_%s(enum %s op1, enum %s op2) { return op1 == op2; }" name name name)
      in
      let codegen_undefined =
        let name = sgen_id id in
        string (Printf.sprintf "static enum %s UNDEFINED(%s)(unit u) { return %s; }" name name (sgen_id first_id))
      in
      string (Printf.sprintf "// enum %s" (string_of_id id))
      ^^ hardline
      ^^ separate space
           [string "enum"; codegen_id id; lbrace; separate_map (comma ^^ space) codegen_id ids; rbrace ^^ semi]
      ^^ twice hardline ^^ codegen_eq ^^ twice hardline ^^ codegen_undefined
  | CTD_enum (id, []) -> c_error ("Cannot compile empty enum " ^ string_of_id id)
  | CTD_struct (id, ctors) ->
      let struct_ctyp = CT_struct (id, ctors) in
      (* Generate a set_T function for every struct T *)
      let codegen_set (id, ctyp) =
        if is_stack_ctyp ctyp then string (Printf.sprintf "rop->%s = op.%s;" (sgen_id id) (sgen_id id))
        else string (Printf.sprintf "COPY(%s)(&rop->%s, op.%s);" (sgen_ctyp_name ctyp) (sgen_id id) (sgen_id id))
      in
      let codegen_setter id ctors =
        string
          (let n = sgen_id id in
           Printf.sprintf "static void COPY(%s)(struct %s *rop, const struct %s op)" n n n
          )
        ^^ space
        ^^ surround 2 0 lbrace (separate_map hardline codegen_set (Bindings.bindings ctors)) rbrace
      in
      (* Generate an init/clear_T function for every struct T *)
      let codegen_field_init f (id, ctyp) =
        if not (is_stack_ctyp ctyp) then
          [string (Printf.sprintf "%s(%s)(&op->%s);" f (sgen_ctyp_name ctyp) (sgen_id id))]
        else []
      in
      let codegen_init f id ctors =
        string
          (let n = sgen_id id in
           Printf.sprintf "static void %s(%s)(struct %s *op)" f n n
          )
        ^^ space
        ^^ surround 2 0 lbrace
             (separate hardline (Bindings.bindings ctors |> List.map (codegen_field_init f) |> List.concat))
             rbrace
      in
      let codegen_eq =
        let codegen_eq_test (id, ctyp) =
          string (Printf.sprintf "EQUAL(%s)(op1.%s, op2.%s)" (sgen_ctyp_name ctyp) (sgen_id id) (sgen_id id))
        in
        string
          (Printf.sprintf "static bool EQUAL(%s)(struct %s op1, struct %s op2)" (sgen_id id) (sgen_id id) (sgen_id id))
        ^^ space
        ^^ surround 2 0 lbrace
             (string "return" ^^ space ^^ separate_map (string " && ") codegen_eq_test ctors ^^ string ";")
             rbrace
      in
      (* Generate the struct and add the generated functions *)
      let codegen_ctor (id, ctyp) = string (sgen_ctyp ctyp) ^^ space ^^ codegen_id id in
      string (Printf.sprintf "// struct %s" (string_of_id id))
      ^^ hardline ^^ string "struct" ^^ space ^^ codegen_id id ^^ space
      ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) codegen_ctor ctors ^^ semi) rbrace
      ^^ semi ^^ twice hardline
      ^^ codegen_setter id (ctor_bindings ctors)
      ^^ ( if not (is_stack_ctyp struct_ctyp) then
             twice hardline
             ^^ codegen_init "CREATE" id (ctor_bindings ctors)
             ^^ twice hardline
             ^^ codegen_init "RECREATE" id (ctor_bindings ctors)
             ^^ twice hardline
             ^^ codegen_init "KILL" id (ctor_bindings ctors)
           else empty
         )
      ^^ twice hardline ^^ codegen_eq
  | CTD_variant (id, tus) ->
      let codegen_tu (ctor_id, ctyp) =
        separate space [string "struct"; lbrace; string (sgen_ctyp ctyp); codegen_id ctor_id ^^ semi; rbrace]
      in
      (* Create an if, else if, ... block that does something for each constructor *)
      let rec each_ctor v f = function
        | [] -> string "{}"
        | [(ctor_id, ctyp)] -> begin
            match f ctor_id ctyp with
            | None -> string "{}"
            | Some op ->
                string (Printf.sprintf "if (%skind == Kind_%s)" v (sgen_id ctor_id))
                ^^ lbrace ^^ hardline ^^ jump 0 2 op ^^ hardline ^^ rbrace
          end
        | (ctor_id, ctyp) :: ctors -> begin
            match f ctor_id ctyp with
            | None -> each_ctor v f ctors
            | Some op ->
                string (Printf.sprintf "if (%skind == Kind_%s) " v (sgen_id ctor_id))
                ^^ lbrace ^^ hardline ^^ jump 0 2 op ^^ hardline ^^ rbrace ^^ string " else " ^^ each_ctor v f ctors
          end
      in
      let codegen_init =
        let n = sgen_id id in
        let ctor_id, ctyp = List.hd tus in
        string (Printf.sprintf "static void CREATE(%s)(struct %s *op)" n n)
        ^^ hardline
        ^^ surround 2 0 lbrace
             (string (Printf.sprintf "op->kind = Kind_%s;" (sgen_id ctor_id))
             ^^ hardline
             ^^
             if not (is_stack_ctyp ctyp) then
               string (Printf.sprintf "CREATE(%s)(&op->%s);" (sgen_ctyp_name ctyp) (sgen_id ctor_id))
             else empty
             )
             rbrace
      in
      let codegen_reinit =
        let n = sgen_id id in
        string (Printf.sprintf "static void RECREATE(%s)(struct %s *op) {}" n n)
      in
      let clear_field v ctor_id ctyp =
        if is_stack_ctyp ctyp then None
        else Some (string (Printf.sprintf "KILL(%s)(&%s->%s);" (sgen_ctyp_name ctyp) v (sgen_id ctor_id)))
      in
      let codegen_clear =
        let n = sgen_id id in
        string (Printf.sprintf "static void KILL(%s)(struct %s *op)" n n)
        ^^ hardline
        ^^ surround 2 0 lbrace (each_ctor "op->" (clear_field "op") tus ^^ semi) rbrace
      in
      let codegen_ctor (ctor_id, ctyp) =
        let ctor_args, tuple, tuple_cleanup = (Printf.sprintf "%s op" (sgen_const_ctyp ctyp), empty, empty) in
        string
          (Printf.sprintf "static void %s(%sstruct %s *rop, %s)" (sgen_function_id ctor_id) (extra_params ())
             (sgen_id id) ctor_args
          )
        ^^ hardline
        ^^ surround 2 0 lbrace
             (tuple
             ^^ each_ctor "rop->" (clear_field "rop") tus
             ^^ hardline
             ^^ string ("rop->kind = Kind_" ^ sgen_id ctor_id)
             ^^ semi ^^ hardline
             ^^
             if is_stack_ctyp ctyp then string (Printf.sprintf "rop->%s = op;" (sgen_id ctor_id))
             else
               string (Printf.sprintf "CREATE(%s)(&rop->%s);" (sgen_ctyp_name ctyp) (sgen_id ctor_id))
               ^^ hardline
               ^^ string (Printf.sprintf "COPY(%s)(&rop->%s, op);" (sgen_ctyp_name ctyp) (sgen_id ctor_id))
               ^^ hardline ^^ tuple_cleanup
             )
             rbrace
      in
      let codegen_setter =
        let n = sgen_id id in
        let set_field ctor_id ctyp =
          Some
            ( if is_stack_ctyp ctyp then string (Printf.sprintf "rop->%s = op.%s;" (sgen_id ctor_id) (sgen_id ctor_id))
              else
                string (Printf.sprintf "CREATE(%s)(&rop->%s);" (sgen_ctyp_name ctyp) (sgen_id ctor_id))
                ^^ string
                     (Printf.sprintf " COPY(%s)(&rop->%s, op.%s);" (sgen_ctyp_name ctyp) (sgen_id ctor_id)
                        (sgen_id ctor_id)
                     )
            )
        in
        string (Printf.sprintf "static void COPY(%s)(struct %s *rop, struct %s op)" n n n)
        ^^ hardline
        ^^ surround 2 0 lbrace
             (each_ctor "rop->" (clear_field "rop") tus
             ^^ semi ^^ hardline ^^ string "rop->kind = op.kind" ^^ semi ^^ hardline ^^ each_ctor "op." set_field tus
             )
             rbrace
      in
      let codegen_eq =
        let codegen_eq_test ctor_id ctyp =
          string
            (Printf.sprintf "return EQUAL(%s)(op1.%s, op2.%s);" (sgen_ctyp_name ctyp) (sgen_id ctor_id) (sgen_id ctor_id)
            )
        in
        let rec codegen_eq_tests = function
          | [] -> string "return false;"
          | (ctor_id, ctyp) :: ctors ->
              string
                (Printf.sprintf "if (op1.kind == Kind_%s && op2.kind == Kind_%s) " (sgen_id ctor_id) (sgen_id ctor_id))
              ^^ lbrace ^^ hardline
              ^^ jump 0 2 (codegen_eq_test ctor_id ctyp)
              ^^ hardline ^^ rbrace ^^ string " else " ^^ codegen_eq_tests ctors
        in
        let n = sgen_id id in
        string (Printf.sprintf "static bool EQUAL(%s)(struct %s op1, struct %s op2) " n n n)
        ^^ surround 2 0 lbrace (codegen_eq_tests tus) rbrace
      in
      string (Printf.sprintf "// union %s" (string_of_id id))
      ^^ hardline ^^ string "enum" ^^ space
      ^^ string ("kind_" ^ sgen_id id)
      ^^ space
      ^^ separate space
           [
             lbrace;
             separate_map (comma ^^ space) (fun id -> string ("Kind_" ^ sgen_id id)) (List.map fst tus);
             rbrace ^^ semi;
           ]
      ^^ twice hardline ^^ string "struct" ^^ space ^^ codegen_id id ^^ space
      ^^ surround 2 0 lbrace
           (separate space [string "enum"; string ("kind_" ^ sgen_id id); string "kind" ^^ semi]
           ^^ hardline ^^ string "union" ^^ space
           ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) codegen_tu tus ^^ semi) rbrace
           ^^ semi
           )
           rbrace
      ^^ semi ^^ twice hardline ^^ codegen_init ^^ twice hardline ^^ codegen_reinit ^^ twice hardline ^^ codegen_clear
      ^^ twice hardline ^^ codegen_setter ^^ twice hardline ^^ codegen_eq ^^ twice hardline
      ^^ separate_map (twice hardline) codegen_ctor tus
      (* If this is the exception type, then we setup up some global variables to deal with exceptions. *)
      ^^
      if string_of_id id = "exception" then
        twice hardline
        ^^ string "struct zexception *current_exception = NULL;"
        ^^ hardline ^^ string "bool have_exception = false;" ^^ hardline
        ^^ string "sail_string *throw_location = NULL;"
      else empty

(** GLOBAL: because C doesn't have real anonymous tuple types
   (anonymous structs don't quite work the way we need) every tuple
   type in the spec becomes some generated named struct in C. This is
   done in such a way that every possible tuple type has a unique name
   associated with it. This global variable keeps track of these
   generated struct names, so we never generate two copies of the
   struct that is used to represent them in C.
   The way this works is that codegen_def scans each definition's type
   annotations for tuple types and generates the required structs
   using codegen_type_def before the actual definition is generated by
   codegen_def'.
   This variable should be reset to empty only when the entire AST has
   been translated to C. **)
let generated = ref IdSet.empty

let codegen_tup ctyps =
  let id = mk_id ("tuple_" ^ string_of_ctyp (CT_tup ctyps)) in
  if IdSet.mem id !generated then empty
  else begin
    let _, fields =
      List.fold_left
        (fun (n, fields) ctyp -> (n + 1, Bindings.add (mk_id ("tup" ^ string_of_int n)) ctyp fields))
        (0, Bindings.empty) ctyps
    in
    generated := IdSet.add id !generated;
    codegen_type_def (CTD_struct (id, Bindings.bindings fields)) ^^ twice hardline
  end

let codegen_node id ctyp =
  string
    (Printf.sprintf "struct node_%s {\n  unsigned int rc;\n  %s hd;\n  struct node_%s *tl;\n};\n" (sgen_id id)
       (sgen_ctyp ctyp) (sgen_id id)
    )
  ^^ string (Printf.sprintf "typedef struct node_%s *%s;" (sgen_id id) (sgen_id id))

let codegen_list_init id =
  string (Printf.sprintf "static void CREATE(%s)(%s *rop) { *rop = NULL; }" (sgen_id id) (sgen_id id))

let codegen_list_clear id ctyp =
  string (Printf.sprintf "static void KILL(%s)(%s *rop) {\n" (sgen_id id) (sgen_id id))
  ^^ string "  if (*rop == NULL) return;\n" ^^ string "  if ((*rop)->rc >= 1) {\n" ^^ string "    (*rop)->rc -= 1;\n"
  ^^ string "  }\n"
  ^^ string (Printf.sprintf "  %s node = *rop;\n" (sgen_id id))
  ^^ string "  while (node != NULL && node->rc == 0) {\n"
  ^^ (if is_stack_ctyp ctyp then empty else string (Printf.sprintf "    KILL(%s)(&node->hd);\n" (sgen_ctyp_name ctyp)))
  ^^ string (Printf.sprintf "    %s next = node->tl;\n" (sgen_id id))
  ^^ string "    sail_free(node);\n" ^^ string "    node = next;\n"
  ^^ string (Printf.sprintf "    internal_dec_%s(node);\n" (sgen_id id))
  ^^ string "  }\n" ^^ string "}"

let codegen_list_recreate id =
  string
    (Printf.sprintf "static void RECREATE(%s)(%s *rop) { KILL(%s)(rop); *rop = NULL; }" (sgen_id id) (sgen_id id)
       (sgen_id id)
    )

let codegen_inc_reference_count id =
  string (Printf.sprintf "static void internal_inc_%s(%s l) {\n" (sgen_id id) (sgen_id id))
  ^^ string "  if (l == NULL) return;\n" ^^ string "  l->rc += 1;\n" ^^ string "}"

let codegen_dec_reference_count id =
  string (Printf.sprintf "static void internal_dec_%s(%s l) {\n" (sgen_id id) (sgen_id id))
  ^^ string "  if (l == NULL) return;\n" ^^ string "  l->rc -= 1;\n" ^^ string "}"

let codegen_list_copy id =
  string (Printf.sprintf "static void COPY(%s)(%s *rop, %s op) {\n" (sgen_id id) (sgen_id id) (sgen_id id))
  ^^ string (Printf.sprintf "  internal_inc_%s(op);\n" (sgen_id id))
  ^^ string (Printf.sprintf "  KILL(%s)(rop);\n" (sgen_id id))
  ^^ string "  *rop = op;\n" ^^ string "}"

let codegen_cons id ctyp =
  let cons_id = mk_id ("cons#" ^ string_of_ctyp ctyp) in
  string
    (Printf.sprintf "static void %s(%s *rop, %s x, %s xs) {\n" (sgen_function_id cons_id) (sgen_id id)
       (sgen_const_ctyp ctyp) (sgen_id id)
    )
  ^^ string "  bool same = *rop == xs;\n"
  ^^ string (Printf.sprintf "  *rop = sail_new(struct node_%s);\n" (sgen_id id))
  ^^ string "  (*rop)->rc = 1;\n"
  ^^ ( if is_stack_ctyp ctyp then string "  (*rop)->hd = x;\n"
       else
         string (Printf.sprintf "  CREATE(%s)(&(*rop)->hd);\n" (sgen_ctyp_name ctyp))
         ^^ string (Printf.sprintf "  COPY(%s)(&(*rop)->hd, x);\n" (sgen_ctyp_name ctyp))
     )
  ^^ string (Printf.sprintf "  if (!same) internal_inc_%s(xs);\n" (sgen_id id))
  ^^ string "  (*rop)->tl = xs;\n" ^^ string "}"

let codegen_pick id ctyp =
  if is_stack_ctyp ctyp then
    string
      (Printf.sprintf "static %s pick_%s(const %s xs) { return xs->hd; }" (sgen_ctyp ctyp) (sgen_ctyp_name ctyp)
         (sgen_id id)
      )
  else
    string
      (Printf.sprintf "static void pick_%s(%s *x, const %s xs) { COPY(%s)(x, xs->hd); }" (sgen_ctyp_name ctyp)
         (sgen_ctyp ctyp) (sgen_id id) (sgen_ctyp_name ctyp)
      )

let codegen_list_equal id ctyp =
  let open Printf in
  ksprintf string "static bool EQUAL(%s)(const %s op1, const %s op2) {\n" (sgen_id id) (sgen_id id) (sgen_id id)
  ^^ ksprintf string "  if (op1 == NULL && op2 == NULL) { return true; };\n"
  ^^ ksprintf string "  if (op1 == NULL || op2 == NULL) { return false; };\n"
  ^^ ksprintf string "  return EQUAL(%s)(op1->hd, op2->hd) && EQUAL(%s)(op1->tl, op2->tl);\n" (sgen_ctyp_name ctyp)
       (sgen_id id)
  ^^ string "}"

let codegen_list_undefined id ctyp =
  let open Printf in
  ksprintf string "static void UNDEFINED(%s)(%s *rop, %s u) {\n" (sgen_id id) (sgen_id id) (sgen_ctyp ctyp)
  ^^ ksprintf string "  *rop = NULL;\n" ^^ string "}"

let codegen_list ctyp =
  let id = mk_id (string_of_ctyp (CT_list ctyp)) in
  if IdSet.mem id !generated then empty
  else begin
    generated := IdSet.add id !generated;
    codegen_node id ctyp ^^ twice hardline ^^ codegen_list_init id ^^ twice hardline ^^ codegen_inc_reference_count id
    ^^ twice hardline ^^ codegen_dec_reference_count id ^^ twice hardline ^^ codegen_list_clear id ctyp
    ^^ twice hardline ^^ codegen_list_recreate id ^^ twice hardline ^^ codegen_list_copy id ^^ twice hardline
    ^^ codegen_cons id ctyp ^^ twice hardline ^^ codegen_pick id ctyp ^^ twice hardline ^^ codegen_list_equal id ctyp
    ^^ twice hardline ^^ codegen_list_undefined id ctyp ^^ twice hardline
  end

(* Generate functions for working with non-bit vectors of some specific type. *)
let codegen_vector ctyp =
  let id = mk_id (string_of_ctyp (CT_vector ctyp)) in
  if IdSet.mem id !generated then empty
  else (
    let vector_typedef =
      string (Printf.sprintf "struct %s {\n  size_t len;\n  %s *data;\n};\n" (sgen_id id) (sgen_ctyp ctyp))
      ^^ string (Printf.sprintf "typedef struct %s %s;" (sgen_id id) (sgen_id id))
    in
    let vector_init =
      string
        (Printf.sprintf "static void CREATE(%s)(%s *rop) {\n  rop->len = 0;\n  rop->data = NULL;\n}" (sgen_id id)
           (sgen_id id)
        )
    in
    let vector_set =
      string (Printf.sprintf "static void COPY(%s)(%s *rop, %s op) {\n" (sgen_id id) (sgen_id id) (sgen_id id))
      ^^ string (Printf.sprintf "  KILL(%s)(rop);\n" (sgen_id id))
      ^^ string "  rop->len = op.len;\n"
      ^^ string (Printf.sprintf "  rop->data = sail_new_array(%s, rop->len);\n" (sgen_ctyp ctyp))
      ^^ string "  for (int i = 0; i < op.len; i++) {\n"
      ^^ string
           ( if is_stack_ctyp ctyp then "    (rop->data)[i] = op.data[i];\n"
             else
               Printf.sprintf "    CREATE(%s)((rop->data) + i);\n    COPY(%s)((rop->data) + i, op.data[i]);\n"
                 (sgen_ctyp_name ctyp) (sgen_ctyp_name ctyp)
           )
      ^^ string "  }\n" ^^ string "}"
    in
    let vector_clear =
      string (Printf.sprintf "static void KILL(%s)(%s *rop) {\n" (sgen_id id) (sgen_id id))
      ^^ ( if is_stack_ctyp ctyp then empty
           else
             string "  for (int i = 0; i < (rop->len); i++) {\n"
             ^^ string (Printf.sprintf "    KILL(%s)((rop->data) + i);\n" (sgen_ctyp_name ctyp))
             ^^ string "  }\n"
         )
      ^^ string "  if (rop->data != NULL) sail_free(rop->data);\n"
      ^^ string "}"
    in
    let vector_reinit =
      string
        (Printf.sprintf "static void RECREATE(%s)(%s *rop) { KILL(%s)(rop); CREATE(%s)(rop); }" (sgen_id id)
           (sgen_id id) (sgen_id id) (sgen_id id)
        )
    in
    let vector_update =
      string
        (Printf.sprintf "static void vector_update_%s(%s *rop, %s op, sail_int n, %s elem) {\n" (sgen_id id)
           (sgen_id id) (sgen_id id) (sgen_ctyp ctyp)
        )
      ^^ string "  int m = sail_int_get_ui(n);\n"
      ^^ string "  if (rop->data == op.data) {\n"
      ^^ string
           ( if is_stack_ctyp ctyp then "    rop->data[m] = elem;\n"
             else Printf.sprintf "  COPY(%s)((rop->data) + m, elem);\n" (sgen_ctyp_name ctyp)
           )
      ^^ string "  } else {\n"
      ^^ string (Printf.sprintf "    COPY(%s)(rop, op);\n" (sgen_id id))
      ^^ string
           ( if is_stack_ctyp ctyp then "    rop->data[m] = elem;\n"
             else Printf.sprintf "  COPY(%s)((rop->data) + m, elem);\n" (sgen_ctyp_name ctyp)
           )
      ^^ string "  }\n" ^^ string "}"
    in
    let internal_vector_update =
      string
        (Printf.sprintf "static void internal_vector_update_%s(%s *rop, %s op, const int64_t n, %s elem) {\n"
           (sgen_id id) (sgen_id id) (sgen_id id) (sgen_ctyp ctyp)
        )
      ^^ string
           ( if is_stack_ctyp ctyp then "  rop->data[n] = elem;\n"
             else Printf.sprintf "  COPY(%s)((rop->data) + n, elem);\n" (sgen_ctyp_name ctyp)
           )
      ^^ string "}"
    in
    let vector_access =
      if is_stack_ctyp ctyp then
        string
          (Printf.sprintf "static %s vector_access_%s(%s op, sail_int n) {\n" (sgen_ctyp ctyp) (sgen_id id) (sgen_id id))
        ^^ string "  int m = sail_int_get_ui(n);\n"
        ^^ string "  return op.data[m];\n" ^^ string "}"
      else
        string
          (Printf.sprintf "static void vector_access_%s(%s *rop, %s op, sail_int n) {\n" (sgen_id id) (sgen_ctyp ctyp)
             (sgen_id id)
          )
        ^^ string "  int m = sail_int_get_ui(n);\n"
        ^^ string (Printf.sprintf "  COPY(%s)(rop, op.data[m]);\n" (sgen_ctyp_name ctyp))
        ^^ string "}"
    in
    let internal_vector_init =
      string
        (Printf.sprintf "static void internal_vector_init_%s(%s *rop, const int64_t len) {\n" (sgen_id id) (sgen_id id))
      ^^ string "  rop->len = len;\n"
      ^^ string (Printf.sprintf "  rop->data = sail_new_array(%s, len);\n" (sgen_ctyp ctyp))
      ^^ ( if not (is_stack_ctyp ctyp) then
             string "  for (int i = 0; i < len; i++) {\n"
             ^^ string (Printf.sprintf "    CREATE(%s)((rop->data) + i);\n" (sgen_ctyp_name ctyp))
             ^^ string "  }\n"
           else empty
         )
      ^^ string "}"
    in
    let vector_undefined =
      string
        (Printf.sprintf "static void undefined_vector_%s(%s *rop, sail_int len, %s elem) {\n" (sgen_id id) (sgen_id id)
           (sgen_ctyp ctyp)
        )
      ^^ string (Printf.sprintf "  rop->len = sail_int_get_ui(len);\n")
      ^^ string (Printf.sprintf "  rop->data = sail_new_array(%s, rop->len);\n" (sgen_ctyp ctyp))
      ^^ string "  for (int i = 0; i < (rop->len); i++) {\n"
      ^^ string
           ( if is_stack_ctyp ctyp then "    (rop->data)[i] = elem;\n"
             else
               Printf.sprintf "    CREATE(%s)((rop->data) + i);\n    COPY(%s)((rop->data) + i, elem);\n"
                 (sgen_ctyp_name ctyp) (sgen_ctyp_name ctyp)
           )
      ^^ string "  }\n" ^^ string "}"
    in
    let vector_equal =
      let open Printf in
      ksprintf string "static bool EQUAL(%s)(const %s op1, const %s op2) {\n" (sgen_id id) (sgen_id id) (sgen_id id)
      ^^ string "  if (op1.len != op2.len) return false;\n"
      ^^ string "  bool result = true;"
      ^^ string "  for (int i = 0; i < op1.len; i++) {\n"
      ^^ ksprintf string "    result &= EQUAL(%s)(op1.data[i], op2.data[i]);" (sgen_ctyp_name ctyp)
      ^^ string "  }\n" ^^ ksprintf string "  return result;\n" ^^ string "}"
    in
    let vector_length =
      let open Printf in
      ksprintf string "static void length_%s(sail_int *rop, %s op) {\n" (sgen_id id) (sgen_id id)
      ^^ ksprintf string "  mpz_set_ui(*rop, (unsigned long int)(op.len));\n"
      ^^ string "}"
    in
    begin
      generated := IdSet.add id !generated;
      vector_typedef ^^ twice hardline ^^ vector_init ^^ twice hardline ^^ vector_clear ^^ twice hardline
      ^^ vector_reinit ^^ twice hardline ^^ vector_undefined ^^ twice hardline ^^ vector_access ^^ twice hardline
      ^^ vector_set ^^ twice hardline ^^ vector_update ^^ twice hardline ^^ vector_equal ^^ twice hardline
      ^^ vector_length ^^ twice hardline ^^ internal_vector_update ^^ twice hardline ^^ internal_vector_init
      ^^ twice hardline
    end
  )

let is_decl = function I_aux (I_decl _, _) -> true | _ -> false

let codegen_decl = function
  | I_aux (I_decl (ctyp, id), _) -> string (Printf.sprintf "%s %s;" (sgen_ctyp ctyp) (sgen_name id))
  | _ -> assert false

let codegen_alloc = function
  | I_aux (I_decl (ctyp, _), _) when is_stack_ctyp ctyp -> empty
  | I_aux (I_decl (ctyp, id), _) -> string (Printf.sprintf "  CREATE(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_name id))
  | _ -> assert false

let codegen_def' ctx = function
  | CDEF_register (id, ctyp, _) ->
      string (Printf.sprintf "// register %s" (string_of_id id))
      ^^ hardline
      ^^ string (Printf.sprintf "%s%s %s;" (static ()) (sgen_ctyp ctyp) (sgen_id id))
  | CDEF_val (id, _, arg_ctyps, ret_ctyp) ->
      if ctx_is_extern id ctx then empty
      else if is_stack_ctyp ret_ctyp then
        string
          (Printf.sprintf "%s%s %s(%s%s);" (static ()) (sgen_ctyp ret_ctyp) (sgen_function_id id) (extra_params ())
             (Util.string_of_list ", " sgen_const_ctyp arg_ctyps)
          )
      else
        string
          (Printf.sprintf "%svoid %s(%s%s *rop, %s);" (static ()) (sgen_function_id id) (extra_params ())
             (sgen_ctyp ret_ctyp)
             (Util.string_of_list ", " sgen_const_ctyp arg_ctyps)
          )
  | CDEF_fundef (id, ret_arg, args, instrs) ->
      let _, arg_ctyps, ret_ctyp =
        match Bindings.find_opt id ctx.valspecs with
        | Some vs -> vs
        | None -> c_error ~loc:(id_loc id) ("No valspec found for " ^ string_of_id id)
      in

      (* Check that the function has the correct arity at this point. *)
      if List.length arg_ctyps <> List.length args then
        c_error ~loc:(id_loc id)
          ("function arguments "
          ^ Util.string_of_list ", " string_of_id args
          ^ " matched against type "
          ^ Util.string_of_list ", " string_of_ctyp arg_ctyps
          )
      else ();

      let instrs = add_local_labels instrs in
      let args =
        Util.string_of_list ", "
          (fun x -> x)
          (List.map2 (fun ctyp arg -> sgen_const_ctyp ctyp ^ " " ^ sgen_id arg) arg_ctyps args)
      in
      let function_header =
        match ret_arg with
        | None ->
            assert (is_stack_ctyp ret_ctyp);
            (if !opt_static then string "static " else empty)
            ^^ string (sgen_ctyp ret_ctyp)
            ^^ space ^^ codegen_function_id id
            ^^ parens (string (extra_params ()) ^^ string args)
            ^^ hardline
        | Some gs ->
            assert (not (is_stack_ctyp ret_ctyp));
            (if !opt_static then string "static " else empty)
            ^^ string "void" ^^ space ^^ codegen_function_id id
            ^^ parens (string (extra_params ()) ^^ string (sgen_ctyp ret_ctyp ^ " *" ^ sgen_id gs ^ ", ") ^^ string args)
            ^^ hardline
      in
      function_header ^^ string "{"
      ^^ jump 0 2 (separate_map hardline (codegen_instr id ctx) instrs)
      ^^ hardline ^^ string "}"
  | CDEF_type ctype_def -> codegen_type_def ctype_def
  | CDEF_startup (id, instrs) ->
      let startup_header = string (Printf.sprintf "%svoid startup_%s(void)" (static ()) (sgen_function_id id)) in
      separate_map hardline codegen_decl instrs
      ^^ twice hardline ^^ startup_header ^^ hardline ^^ string "{"
      ^^ jump 0 2 (separate_map hardline codegen_alloc instrs)
      ^^ hardline ^^ string "}"
  | CDEF_finish (id, instrs) ->
      let finish_header = string (Printf.sprintf "%svoid finish_%s(void)" (static ()) (sgen_function_id id)) in
      separate_map hardline codegen_decl (List.filter is_decl instrs)
      ^^ twice hardline ^^ finish_header ^^ hardline ^^ string "{"
      ^^ jump 0 2 (separate_map hardline (codegen_instr id ctx) instrs)
      ^^ hardline ^^ string "}"
  | CDEF_let (number, bindings, instrs) ->
      let instrs = add_local_labels instrs in
      let setup = List.concat (List.map (fun (id, ctyp) -> [idecl (id_loc id) ctyp (name id)]) bindings) in
      let cleanup = List.concat (List.map (fun (id, ctyp) -> [iclear ~loc:(id_loc id) ctyp (name id)]) bindings) in
      separate_map hardline
        (fun (id, ctyp) -> string (Printf.sprintf "%s%s %s;" (static ()) (sgen_ctyp ctyp) (sgen_id id)))
        bindings
      ^^ hardline
      ^^ string (Printf.sprintf "static void create_letbind_%d(void) " number)
      ^^ string "{"
      ^^ jump 0 2 (separate_map hardline codegen_alloc setup)
      ^^ hardline
      ^^ jump 0 2 (separate_map hardline (codegen_instr (mk_id "let") { ctx with no_raw = true }) instrs)
      ^^ hardline ^^ string "}" ^^ hardline
      ^^ string (Printf.sprintf "static void kill_letbind_%d(void) " number)
      ^^ string "{"
      ^^ jump 0 2 (separate_map hardline (codegen_instr (mk_id "let") ctx) cleanup)
      ^^ hardline ^^ string "}"
  | CDEF_pragma _ -> empty

(** As we generate C we need to generate specialized version of tuple,
   list, and vector type. These must be generated in the correct
   order. The ctyp_dependencies function generates a list of
   c_gen_typs in the order they must be generated. Types may be
   repeated in ctyp_dependencies so it's up to the code-generator not
   to repeat definitions pointlessly (using the !generated variable)
   *)
type c_gen_typ = CTG_tup of ctyp list | CTG_list of ctyp | CTG_vector of ctyp

let rec ctyp_dependencies = function
  | CT_tup ctyps -> List.concat (List.map ctyp_dependencies ctyps) @ [CTG_tup ctyps]
  | CT_list ctyp -> ctyp_dependencies ctyp @ [CTG_list ctyp]
  | CT_vector ctyp | CT_fvector (_, ctyp) -> ctyp_dependencies ctyp @ [CTG_vector ctyp]
  | CT_ref ctyp -> ctyp_dependencies ctyp
  | CT_struct (_, ctors) -> List.concat (List.map (fun (_, ctyp) -> ctyp_dependencies ctyp) ctors)
  | CT_variant (_, ctors) -> List.concat (List.map (fun (_, ctyp) -> ctyp_dependencies ctyp) ctors)
  | CT_lint | CT_fint _ | CT_lbits | CT_fbits _ | CT_sbits _ | CT_unit | CT_bool | CT_real | CT_bit | CT_string
  | CT_enum _ | CT_poly _ | CT_constant _ | CT_float _ | CT_rounding_mode ->
      []

let codegen_ctg = function
  | CTG_vector ctyp -> codegen_vector ctyp
  | CTG_tup ctyps -> codegen_tup ctyps
  | CTG_list ctyp -> codegen_list ctyp

(** When we generate code for a definition, we need to first generate
   any auxillary type definitions that are required. *)
let codegen_def ctx def =
  let ctyps = cdef_ctyps def |> CTSet.elements in
  (* We should have erased any polymorphism introduced by variants at this point! *)
  if List.exists is_polymorphic ctyps then (
    let polymorphic_ctyps = List.filter is_polymorphic ctyps in
    c_error
      (Printf.sprintf "Found polymorphic types:\n%s\nwhile generating definition."
         (Util.string_of_list "\n" string_of_ctyp polymorphic_ctyps)
      )
  )
  else (
    let deps = List.concat (List.map ctyp_dependencies ctyps) in
    separate_map hardline codegen_ctg deps ^^ codegen_def' ctx def
  )

let is_cdef_startup = function CDEF_startup _ -> true | _ -> false

let sgen_startup = function
  | CDEF_startup (id, _) -> Printf.sprintf "  startup_%s();" (sgen_function_id id)
  | _ -> assert false

let sgen_instr id ctx instr = Pretty_print_sail.to_string (codegen_instr id ctx instr)

let is_cdef_finish = function CDEF_startup _ -> true | _ -> false

let sgen_finish = function
  | CDEF_startup (id, _) -> Printf.sprintf "  finish_%s();" (sgen_function_id id)
  | _ -> assert false

let get_recursive_functions cdefs =
  let graph = Jib_compile.callgraph cdefs in
  let rf = IdGraph.self_loops graph in
  (* Use strongly-connected components for mutually recursive functions *)
  List.fold_left (fun rf component -> match component with [_] -> rf | mutual -> mutual @ rf) rf (IdGraph.scc graph)
  |> IdSet.of_list

let jib_of_ast env effect_info ast =
  let module Jibc = Make (C_config (struct
    let branch_coverage = !opt_branch_coverage
  end)) in
  let env, effect_info = add_special_functions env effect_info in
  let ctx = initial_ctx env effect_info in
  Jibc.compile_ast ctx ast

let compile_ast env effect_info output_chan c_includes ast =
  try
    let cdefs, ctx = jib_of_ast env effect_info ast in
    (* let cdefs', _ = Jib_optimize.remove_tuples cdefs ctx in *)
    let cdefs = insert_heap_returns Bindings.empty cdefs in

    let recursive_functions = get_recursive_functions cdefs in
    let cdefs = optimize recursive_functions cdefs in

    let docs = separate_map (hardline ^^ hardline) (codegen_def ctx) cdefs in

    let preamble =
      separate hardline
        ((if !opt_no_lib then [] else [string "#include \"sail.h\""])
        @ (if !opt_no_rts then [] else [string "#include \"rts.h\""; string "#include \"elf.h\""])
        @ (if Option.is_some !opt_branch_coverage then [string "#include \"sail_coverage.h\""] else [])
        @ List.map (fun h -> string (Printf.sprintf "#include \"%s\"" h)) c_includes
        @ [string "#ifdef __cplusplus"; string "extern \"C\" {"; string "#endif"]
        )
    in

    let exn_boilerplate =
      if not (Bindings.mem (mk_id "exception") ctx.variants) then ([], [])
      else
        ( [
            "  current_exception = sail_new(struct zexception);";
            "  CREATE(zexception)(current_exception);";
            "  throw_location = sail_new(sail_string);";
            "  CREATE(sail_string)(throw_location);";
          ],
          [
            "  if (have_exception) {fprintf(stderr, \"Exiting due to uncaught exception: %s\\n\", *throw_location);}";
            "  KILL(zexception)(current_exception);";
            "  sail_free(current_exception);";
            "  KILL(sail_string)(throw_location);";
            "  sail_free(throw_location);";
            "  if (have_exception) {exit(EXIT_FAILURE);}";
          ]
        )
    in

    let letbind_initializers = List.map (fun n -> Printf.sprintf "  create_letbind_%d();" n) (List.rev ctx.letbinds) in
    let letbind_finalizers = List.map (fun n -> Printf.sprintf "  kill_letbind_%d();" n) ctx.letbinds in
    let startup cdefs = List.map sgen_startup (List.filter is_cdef_startup cdefs) in
    let finish cdefs = List.map sgen_finish (List.filter is_cdef_finish cdefs) in

    let regs = c_ast_registers cdefs in

    let register_init_clear (id, ctyp, instrs) =
      if is_stack_ctyp ctyp then (List.map (sgen_instr (mk_id "reg") ctx) instrs, [])
      else
        ( [Printf.sprintf "  CREATE(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_id id)]
          @ List.map (sgen_instr (mk_id "reg") ctx) instrs,
          [Printf.sprintf "  KILL(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_id id)]
        )
    in

    let init_config_id = mk_id "__InitConfig" in

    let model_init =
      separate hardline
        (List.map string
           ([Printf.sprintf "%svoid model_init(void)" (static ()); "{"; "  setup_rts();"]
           @ fst exn_boilerplate @ startup cdefs @ letbind_initializers
           @ List.concat (List.map (fun r -> fst (register_init_clear r)) regs)
           @ (if regs = [] then [] else [Printf.sprintf "  %s(UNIT);" (sgen_function_id (mk_id "initialize_registers"))])
           @ ( if ctx_has_val_spec init_config_id ctx then
                 [Printf.sprintf "  %s(UNIT);" (sgen_function_id init_config_id)]
               else []
             )
           @ ["}"]
           )
        )
    in

    let model_fini =
      separate hardline
        (List.map string
           ([Printf.sprintf "%svoid model_fini(void)" (static ()); "{"]
           @ letbind_finalizers
           @ List.concat (List.map (fun r -> snd (register_init_clear r)) regs)
           @ finish cdefs @ ["  cleanup_rts();"] @ snd exn_boilerplate @ ["}"]
           )
        )
    in

    let model_pre_exit =
      (["void model_pre_exit()"; "{"]
      @
      if Option.is_some !opt_branch_coverage then
        [
          "  if (sail_coverage_exit() != 0) {";
          "    fprintf(stderr, \"Could not write coverage information\\n\");";
          "    exit(EXIT_FAILURE);";
          "  }";
          "}";
        ]
      else ["}"]
      )
      |> List.map string |> separate hardline
    in

    let model_default_main =
      [
        Printf.sprintf "%sint model_main(int argc, char *argv[])" (static ());
        "{";
        "  model_init();";
        "  if (process_arguments(argc, argv)) exit(EXIT_FAILURE);";
        Printf.sprintf "  %s(UNIT);" (sgen_function_id (mk_id "main"));
        "  model_fini();";
        "  model_pre_exit();";
        "  return EXIT_SUCCESS;";
        "}";
      ]
      |> List.map string |> separate hardline
    in

    let model_main =
      separate hardline
        ( if !opt_no_main then []
          else List.map string ["int main(int argc, char *argv[])"; "{"; "  return model_main(argc, argv);"; "}"]
        )
    in
    let end_extern_cpp = separate hardline (List.map string [""; "#ifdef __cplusplus"; "}"; "#endif"]) in
    let hlhl = hardline ^^ hardline in

    Pretty_print_sail.to_string
      (preamble ^^ hlhl ^^ docs ^^ hlhl
      ^^ ( if not !opt_no_rts then
             model_init ^^ hlhl ^^ model_fini ^^ hlhl ^^ model_pre_exit ^^ hlhl ^^ model_default_main ^^ hlhl
           else empty
         )
      ^^ model_main ^^ hardline ^^ end_extern_cpp ^^ hardline
      )
    |> output_string output_chan
  with Type_error.Type_error (l, err) ->
    c_error ~loc:l ("Unexpected type error when compiling to C:\n" ^ Type_error.string_of_type_error err)

let compile_ast_clib env effect_info ast codegen =
  let cdefs, ctx = jib_of_ast env effect_info ast in
  (* let cdefs', _ = Jib_optimize.remove_tuples cdefs ctx in *)
  let cdefs = insert_heap_returns Bindings.empty cdefs in
  codegen ctx cdefs
