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
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
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
module Document = Pretty_print_sail.Document

open Anf

module Big_int = Nat_big_num

let opt_prefix = ref "z"
let opt_extra_params = ref None
let opt_extra_arguments = ref None

let extra_params () = match !opt_extra_params with Some str -> str ^ ", " | _ -> ""

let extra_arguments is_extern = match !opt_extra_arguments with Some str when not is_extern -> str ^ ", " | _ -> ""

(* Optimization flags *)
let optimize_primops = ref false
let optimize_hoist_allocations = ref false
let optimize_alias = ref false
let optimize_fixed_int = ref false
let optimize_fixed_bits = ref false

let ngensym = symbol_generator ()

let c_error ?loc:(l = Parse_ast.Unknown) message = raise (Reporting.err_general l ("\nC backend: " ^ message))

(**************************************************************************)
(* Converting Sail types to C types                                       *)
(**************************************************************************)

let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))

(** This function is used to split types into those we allocate on the stack, versus those which need to live on the
    heap, or otherwise require some additional memory management.

    This is roughly the same distinction that Rust makes between copy and non-copy types. *)
let rec is_stack_ctyp ctx ctyp =
  match ctyp with
  | CT_fbits _ | CT_sbits _ | CT_unit | CT_bool | CT_enum _ -> true
  | CT_fint n -> n <= 64
  | CT_lint when !optimize_fixed_int -> true
  | CT_lint -> false
  | CT_lbits when !optimize_fixed_bits -> true
  | CT_lbits -> false
  | CT_real | CT_string | CT_list _ | CT_vector _ | CT_fvector _ -> false
  | CT_struct (_, _) ->
      let _, fields = struct_field_bindings Parse_ast.Unknown ctx ctyp in
      Bindings.for_all (fun _ ctyp -> is_stack_ctyp ctx ctyp) fields
  | CT_variant (_, _) -> false
  | CT_tup ctyps -> List.for_all (is_stack_ctyp ctx) ctyps
  | CT_ref _ -> true
  | CT_poly _ -> true
  | CT_float _ -> true
  | CT_rounding_mode -> true
  (* Is a reference to some immutable JSON data *)
  | CT_json -> true
  | CT_json_key -> true
  | CT_constant n -> Big_int.less_equal (min_int 64) n && Big_int.greater_equal n (max_int 64)
  | CT_memory_writes -> false

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
  | L_hex hex ->
      let len = hex_lit_length hex in
      if len <= 64 then (
        let content =
          Semantics.bitlist_of_hex_lit hex
          |> List.map (function Value_type.B0 -> Sail2_values.B0 | Value_type.B1 -> Sail2_values.B1)
        in
        Some (V_lit (VL_bits content, CT_fbits len))
      )
      else None
  | L_unit -> Some (V_lit (VL_unit, CT_unit))
  | L_true -> Some (V_lit (VL_bool true, CT_bool))
  | L_false -> Some (V_lit (VL_bool false, CT_bool))
  | _ -> None

let sail_create ?(prefix = "") ?(suffix = "") ctyp fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sCREATE(%s)(%s)%s" prefix ctyp s suffix) fmt

let sail_recreate ?(prefix = "") ?(suffix = "") ctyp fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sRECREATE(%s)(%s)%s" prefix ctyp s suffix) fmt

let sail_copy ?(prefix = "") ?(suffix = "") ctyp fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sCOPY(%s)(%s)%s" prefix ctyp s suffix) fmt

let sail_kill ?(prefix = "") ?(suffix = "") ctyp fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sKILL(%s)(%s)%s" prefix ctyp s suffix) fmt

let sail_equal ?(prefix = "") ?(suffix = "") ctyp fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sEQUAL(%s)(%s)%s" prefix ctyp s suffix) fmt

let sail_convert_of ?(prefix = "") ?(suffix = "") ctyp1 ctyp2 fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sCONVERT_OF(%s, %s)(%s)%s" prefix ctyp1 ctyp2 s suffix) fmt

let c_function ~return decl body =
  string return ^^ space ^^ decl ^^ space ^^ nest 2 (lbrace ^^ hardline ^^ separate hardline body) ^^ hardline ^^ rbrace

let c_stmt s = string s ^^ semi

let c_assign x op y = separate space [x; string op; y] ^^ semi

let c_for iter body =
  string "for" ^^ space ^^ iter ^^ space ^^ nest 2 (lbrace ^^ hardline ^^ separate hardline body) ^^ hardline ^^ rbrace

let c_cond_block c block = if c then block else []

let c_if_block b = nest 2 (lbrace ^^ hardline ^^ separate hardline b) ^^ hardline ^^ rbrace

let c_if cond then_block = string "if" ^^ space ^^ cond ^^ space ^^ c_if_block then_block

let c_if_else cond then_block else_block =
  string "if" ^^ space ^^ cond ^^ space ^^ c_if_block then_block ^^ space ^^ string "else" ^^ space
  ^^ c_if_block else_block

let c_return exp = string "return" ^^ space ^^ exp ^^ semi

module C_config (Opts : sig
  val branch_coverage : out_channel option
  val assert_to_exception : bool
  val preserve_types : IdSet.t
end) : CONFIG = struct
  (** Convert a sail type into a C-type. This function can be quite slow, because it uses ctx.local_env and SMT to
      analyse the Sail types and attempts to fit them into the smallest possible C types, provided ctx.optimize_smt is
      true (default) **)
  let rec convert_typ ctx typ =
    let (Typ_aux (typ_aux, l) as typ) = Env.expand_synonyms ctx.local_env typ in
    match typ_aux with
    | Typ_id id when string_of_id id = "bool" -> CT_bool
    | Typ_id id when string_of_id id = "int" -> CT_lint
    | Typ_id id when string_of_id id = "nat" -> CT_lint
    | Typ_id id when string_of_id id = "unit" -> CT_unit
    | Typ_id id when string_of_id id = "string" -> CT_string
    | Typ_id id when string_of_id id = "string_literal" -> CT_string
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
    | Typ_id id when Bindings.mem id ctx.records -> CT_struct (id, [])
    | Typ_app (id, typ_args) when Bindings.mem id ctx.records ->
        let ctyp_args =
          List.filter_map
            (function A_aux (A_typ typ, _) -> Some (ctyp_suprema (convert_typ ctx typ)) | _ -> None)
            typ_args
        in
        CT_struct (id, ctyp_args)
    | Typ_id id when Bindings.mem id ctx.variants -> CT_variant (id, []) |> transparent_newtype ctx
    | Typ_app (id, typ_args) when Bindings.mem id ctx.variants ->
        let ctyp_args =
          List.filter_map
            (function A_aux (A_typ typ, _) -> Some (ctyp_suprema (convert_typ ctx typ)) | _ -> None)
            typ_args
        in
        CT_variant (id, ctyp_args) |> transparent_newtype ctx
    | Typ_id id when Bindings.mem id ctx.enums -> CT_enum id
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
    let rec c_literal annot = function
      | AV_lit (lit, typ) as v when is_stack_ctyp ctx (convert_typ { ctx with local_env = annot.env } typ) -> begin
          match literal_to_fragment lit with Some cval -> AV_cval (cval, typ) | None -> v
        end
      | AV_tuple avals -> AV_tuple (List.map (c_literal annot) avals)
      | v -> v
    in
    map_aval c_literal

  let rec is_bitvector = function
    | [] -> true
    | AV_lit (L_aux (L_bin [Non_empty (_, [])], _), _) :: avals -> is_bitvector avals
    | _ :: _ -> false

  let value_of_aval_bit = function
    | AV_lit (L_aux (L_bin [Non_empty (b, [])], _), _) -> (
        match b with Bin_0 -> Sail2_values.B0 | Bin_1 -> Sail2_values.B1
      )
    | _ -> assert false

  (** Used to make sure the -Ofixed_int and -Ofixed_bits don't interfere with assumptions made about optimizations in
      the common case. *)
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
            if is_stack_ctyp ctx ctyp && not (never_optimize ctyp) then (
              (* We need to check that id's type hasn't changed due to flow typing *)
              match NameMap.find_opt id ctx.locals with
              | Some (_, ctyp') ->
                  if ctyp_equal ctyp ctyp' then AV_cval (V_id (id, ctyp), typ)
                  else
                    (* id's type changed due to flow typing, so it's
                      really still heap allocated! *)
                    v
              | None -> (
                  (* We need to take special care around global
                     letbindings, to not refine their types. *)
                  match id with
                  | Name (id', _) -> (
                      match Bindings.find_opt id' ctx.letbind_ctyps with
                      | Some ctyp' -> if ctyp_equal ctyp ctyp' then AV_cval (V_id (id, ctyp), typ) else v
                      | None -> AV_cval (V_id (id, ctyp), typ)
                    )
                  | _ -> AV_cval (V_id (id, ctyp), typ)
                )
            )
            else v
        | Register typ ->
            let ctyp = convert_typ ctx typ in
            if is_stack_ctyp ctx ctyp && not (never_optimize ctyp) then AV_cval (V_id (id, ctyp), typ) else v
        | _ -> v
      end
    | AV_vector (v, typ) when is_bitvector v && List.length v <= 64 ->
        let bitstring = VL_bits (List.map value_of_aval_bit v) in
        AV_cval (V_lit (bitstring, CT_fbits (List.length v)), typ)
    | AV_tuple avals -> AV_tuple (List.map (c_aval ctx) avals)
    | aval -> aval

  (* Map over all the functions in an aexp. *)
  let rec analyze_functions ctx f (AE_aux (aexp, ({ env; _ } as annot))) =
    let ctx = { ctx with local_env = env } in
    let aexp =
      match aexp with
      | AE_app (id, vs, typ) -> f ctx id vs typ
      | AE_typ (aexp, typ) -> AE_typ (analyze_functions ctx f aexp, typ)
      | AE_assign (alexp, aexp) -> AE_assign (alexp, analyze_functions ctx f aexp)
      | AE_short_circuit (op, aval, aexp) -> AE_short_circuit (op, aval, analyze_functions ctx f aexp)
      | AE_let (mut, id, typ1, aexp1, (AE_aux (_, { env = env2; _ }) as aexp2), typ2) ->
          let aexp1 = analyze_functions ctx f aexp1 in
          (* Use aexp2's environment because it will contain constraints for id *)
          let ctyp1 = convert_typ { ctx with local_env = env2 } typ1 in
          let ctx = { ctx with locals = NameMap.add id (mut, ctyp1) ctx.locals } in
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
          let ctx = { ctx with locals = NameMap.add id (Immutable, CT_fint 64) ctx.locals } in
          let aexp4 = analyze_functions ctx f aexp4 in
          AE_for (id, aexp1, aexp2, aexp3, order, aexp4)
      | AE_match (aval, cases, typ) ->
          let analyze_case ((AP_aux (_, { env; _ }) as pat), aexp1, aexp2, uannot) =
            let pat_bindings = NameMap.bindings (apat_types pat) in
            let ctx = { ctx with local_env = env } in
            let ctx =
              List.fold_left
                (fun ctx (id, typ) -> { ctx with locals = NameMap.add id (Immutable, convert_typ ctx typ) ctx.locals })
                ctx pat_bindings
            in
            (pat, analyze_functions ctx f aexp1, analyze_functions ctx f aexp2, uannot)
          in
          AE_match (aval, List.map analyze_case cases, typ)
      | AE_try (aexp, cases, typ) ->
          AE_try
            ( analyze_functions ctx f aexp,
              List.map
                (fun (pat, aexp1, aexp2, uannot) ->
                  (pat, analyze_functions ctx f aexp1, analyze_functions ctx f aexp2, uannot)
                )
                cases,
              typ
            )
      | (AE_field _ | AE_struct_update _ | AE_val _ | AE_return _ | AE_exit _ | AE_throw _) as v -> v
    in
    AE_aux (aexp, annot)

  let analyze_primop' ctx id args typ =
    let no_change = AE_app (Sail_function id, args, typ) in
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
        match destruct_bitvector ctx.tc_env typ with
        | Some (Nexp_aux (Nexp_constant n, _)) when Big_int.less_equal n (Big_int.of_int 64) ->
            let n = Big_int.to_int n in
            AE_val (AV_cval (V_lit (VL_bits (Util.list_init n (fun _ -> Sail2_values.B0)), CT_fbits n), typ))
        | _ -> no_change
      end
    | "zero_extend", [AV_cval (v, _); _] -> begin
        match destruct_bitvector ctx.tc_env typ with
        | Some (Nexp_aux (Nexp_constant n, _)) when Big_int.less_equal n (Big_int.of_int 64) ->
            AE_val (AV_cval (V_call (Zero_extend (Big_int.to_int n), [v]), typ))
        | _ -> no_change
      end
    | "sign_extend", [AV_cval (v, _); _] -> begin
        match destruct_bitvector ctx.tc_env typ with
        | Some (Nexp_aux (Nexp_constant n, _)) when Big_int.less_equal n (Big_int.of_int 64) ->
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
    | "vector_access", [v; AV_cval (n, _)] -> (
        match destruct_vector ctx.tc_env (aval_typ v) with
        | Some (_, elem_typ) -> (
            match cval_ctyp n with
            | CT_fint 64 -> AE_app (Pure_extern (mk_id "fast_vector_access", Some elem_typ), args, typ)
            | _ -> no_change
          )
        | None -> no_change
      )
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
    | "print_int", [_; AV_cval _] -> AE_app (Extern (mk_id "fast_print_int", None), args, typ)
    | "undefined_bit", _ -> AE_val (AV_cval (V_lit (VL_bits [Sail2_values.B0], CT_fbits 1), typ))
    | "undefined_bool", _ -> AE_val (AV_cval (V_lit (VL_bool false, CT_bool), typ))
    | _, _ -> no_change

  let analyze_primop ctx id args typ =
    let no_change = AE_app (id, args, typ) in
    match id with
    | Sail_function id ->
        if !optimize_primops then (try analyze_primop' ctx id args typ with Failure _ -> no_change) else no_change
    | _ -> no_change

  let optimize_anf ctx aexp = analyze_functions ctx analyze_primop (c_literals ctx aexp)

  let unroll_loops = None
  let make_call_precise _ _ _ _ = true
  let ignore_64 = false
  let struct_value = false
  let tuple_value = false
  let use_real = false
  let branch_coverage = Opts.branch_coverage
  let track_throw = true
  let assert_to_exception = Opts.assert_to_exception
  let use_void = false
  let eager_control_flow = false
  let preserve_types = Opts.preserve_types
  let fun_to_wires = Bindings.empty
end

(** Functions that have heap-allocated return types are implemented by passing a pointer a location where the return
    value should be stored. The ANF -> Sail IR pass for expressions simply outputs an I_return instruction for any
    return value, so this function walks over the IR ast for expressions and modifies the return statements into code
    that sets that pointer, as well as adds extra control flow to cleanup heap-allocated variables correctly when a
    function terminates early. See the generate_cleanup function for how this is done. *)
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
    | before, I_aux (I_if (cval, then_instrs, else_instrs), (_, l)) :: after ->
        before @ [iif l cval (rewrite_return then_instrs) (rewrite_return else_instrs)] @ rewrite_return after
    | before, I_aux (I_funcall (CR_one (CL_id (Return _, ctyp)), extern, fid, args), aux) :: after ->
        before
        @ [I_aux (I_funcall (CR_one (CL_addr (CL_id (ret, CT_ref ctyp))), extern, fid, args), aux)]
        @ rewrite_return after
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
    | before, I_aux (I_if (cval, then_instrs, else_instrs), (_, l)) :: after ->
        before @ [iif l cval (rewrite_return then_instrs) (rewrite_return else_instrs)] @ rewrite_return after
    | before, I_aux (I_funcall (CR_one (CL_id (Return _, ctyp)), extern, fid, args), aux) :: after ->
        before @ [I_aux (I_funcall (CR_one (CL_id (ret, ctyp)), extern, fid, args), aux)] @ rewrite_return after
    | before, I_aux (I_copy (CL_id (Return _, ctyp), cval), aux) :: after ->
        before @ [I_aux (I_copy (CL_id (ret, ctyp), cval), aux)] @ rewrite_return after
    | before, I_aux (I_end _, _) :: after -> before @ [ireturn (V_id (ret, ret_ctyp))] @ rewrite_return after
    | before, (I_aux ((I_copy _ | I_funcall _), _) as instr) :: after -> before @ (instr :: rewrite_return after)
    | _, _ -> assert false
  in
  rewrite_return instrs

let rec insert_heap_returns ctx ret_ctyps = function
  | (CDEF_aux (CDEF_val (id, _, _, ret_ctyp, _), _) as cdef) :: cdefs ->
      cdef :: insert_heap_returns ctx (Bindings.add id ret_ctyp ret_ctyps) cdefs
  | CDEF_aux (CDEF_fundef (id, Return_plain, args, body), def_annot) :: cdefs ->
      let gs = ngensym () in
      begin
        match Bindings.find_opt id ret_ctyps with
        | None -> raise (Reporting.err_general (id_loc id) ("Cannot find return type for function " ^ string_of_id id))
        | Some ret_ctyp when not (is_stack_ctyp ctx ret_ctyp) ->
            CDEF_aux (CDEF_fundef (id, Return_via gs, args, fix_early_heap_return gs body), def_annot)
            :: insert_heap_returns ctx ret_ctyps cdefs
        | Some ret_ctyp ->
            CDEF_aux
              ( CDEF_fundef
                  (id, Return_plain, args, fix_early_stack_return gs ret_ctyp (idecl (id_loc id) ret_ctyp gs :: body)),
                def_annot
              )
            :: insert_heap_returns ctx ret_ctyps cdefs
      end
  | CDEF_aux (CDEF_fundef (id, _, _, _), _) :: _ ->
      Reporting.unreachable (id_loc id) __POS__ "Found function with return already re-written in insert_heap_returns"
  | cdef :: cdefs -> cdef :: insert_heap_returns ctx ret_ctyps cdefs
  | [] -> []

(** To keep things neat we use GCC's local labels extension to limit the scope of labels. We do this by iterating over
    all the blocks and adding a __label__ declaration with all the labels local to that block. The add_local_labels
    function is called by the code generator just before it outputs C.

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
  | CDEF_aux (CDEF_fundef (function_id, _, _, _), _) as cdef when IdSet.mem function_id recursive_functions -> [cdef]
  | CDEF_aux (CDEF_fundef (function_id, heap_return, args, body), def_annot) ->
      let decls = ref [] in
      let cleanups = ref [] in
      let rec hoist = function
        | I_aux (I_decl (ctyp, decl_id), annot) :: instrs when hoist_ctyp ctyp ->
            let hid = hoist_id () in
            decls := idecl (snd annot) ctyp hid :: !decls;
            cleanups := iclear ctyp hid :: !cleanups;
            let instrs = instrs_rename decl_id hid instrs in
            I_aux (I_reset (ctyp, hid), annot) :: hoist instrs
        | I_aux (I_init (ctyp, decl_id, Init_cval cval), annot) :: instrs when hoist_ctyp ctyp ->
            let hid = hoist_id () in
            decls := idecl (snd annot) ctyp hid :: !decls;
            cleanups := iclear ctyp hid :: !cleanups;
            let instrs = instrs_rename decl_id hid instrs in
            I_aux (I_reinit (ctyp, hid, cval), annot) :: hoist instrs
        | I_aux (I_clear (ctyp, _), _) :: instrs when hoist_ctyp ctyp -> hoist instrs
        | I_aux (I_block block, annot) :: instrs -> I_aux (I_block (hoist block), annot) :: hoist instrs
        | I_aux (I_try_block block, annot) :: instrs -> I_aux (I_try_block (hoist block), annot) :: hoist instrs
        | I_aux (I_if (cval, then_instrs, else_instrs), annot) :: instrs ->
            I_aux (I_if (cval, hoist then_instrs, hoist else_instrs), annot) :: hoist instrs
        | instr :: instrs -> instr :: hoist instrs
        | [] -> []
      in
      let body = hoist body in
      if !decls = [] then [CDEF_aux (CDEF_fundef (function_id, heap_return, args, body), def_annot)]
      else
        [
          CDEF_aux (CDEF_startup (function_id, List.rev !decls), mk_def_annot (gen_loc def_annot.loc) ());
          CDEF_aux (CDEF_fundef (function_id, heap_return, args, body), def_annot);
          CDEF_aux (CDEF_finish (function_id, !cleanups), mk_def_annot (gen_loc def_annot.loc) ());
        ]
  | cdef -> [cdef]

let removed = icomment "REMOVED"

let is_not_removed = function I_aux (I_comment "REMOVED", _) -> false | _ -> true

(** This optimization looks for patterns of the form:

    {v
       create x : t;
       x = y;
       // modifications to x, and no changes to y
       y = x;
       // no further changes to x
       kill x;
    v}

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
      | 1, Some a, instr :: instrs ->
          if NameSet.mem a (instr_ids ~direct:true instr) then None else scan ctyp id 1 instrs
      | 2, Some _, I_aux (I_clear (ctyp', id'), _) :: instrs when Name.compare id id' = 0 && ctyp_equal ctyp ctyp' ->
          scan ctyp id 2 instrs
      | 2, Some _, instr :: instrs ->
          if NameSet.mem id (instr_ids ~direct:true instr) then None else scan ctyp id 2 instrs
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
    | I_aux (I_if (cval, then_instrs, else_instrs), aux) :: instrs ->
        I_aux (I_if (cval, opt then_instrs, opt else_instrs), aux) :: opt instrs
    | instr :: instrs -> instr :: opt instrs
    | [] -> []
  in
  function
  | CDEF_aux (CDEF_fundef (function_id, heap_return, args, body), def_annot) ->
      [CDEF_aux (CDEF_fundef (function_id, heap_return, args, opt body), def_annot)]
  | cdef -> [cdef]

(** This optimization looks for patterns of the form

    {v
       create x : t;
       ... // some instructions
       { { { ... // and nested in any number of blocks
       create y : t;
       // modifications to y, no references to x
       x = y;
       // no changes to y
       kill y;
    v}

    If found we can replace y by x *)
module Combine_variables = struct
  type block_offset = int * int list

  let no_offset = (0, [])

  let deeper (n, blks) = (0, n :: blks)

  let next (n, blks) = (n + 1, blks)

  let reverse (x, xs) =
    let ys = List.rev (x :: xs) in
    (List.hd ys, List.tl ys)

  type state = Find of block_offset | Modify of block_offset * name | Kill of block_offset * name

  let pattern ctyp x =
    let rec scan state instrs =
      match state with
      | Find offset -> (
          match instrs with
          | I_aux (I_block block, _) :: instrs -> (
              match scan (Find (deeper offset)) block with None -> scan (Find (next offset)) instrs | result -> result
            )
          | I_aux (I_decl (ctyp', y), _) :: instrs when ctyp_equal ctyp ctyp' -> scan (Modify (offset, y)) instrs
          | _ :: instrs -> scan (Find offset) instrs
          | [] -> None
        )
      | Modify (offset, y) -> (
          match instrs with
          | I_aux (I_copy (CL_id (x', ctyp'), V_id (y', ctyp'')), _) :: instrs
            when Name.compare y y' = 0 && Name.compare x x' = 0 && ctyp_equal ctyp ctyp' && ctyp_equal ctyp' ctyp'' ->
              scan (Kill (offset, y)) instrs
          (* Ignore seemingly early clears of x, as this can happen along exception paths *)
          | I_aux (I_clear (_, x'), _) :: instrs when Name.compare x x' = 0 -> scan (Modify (offset, y)) instrs
          | instr :: instrs ->
              if instr_references ~read:x ~write:x ~direct:false instr then None else scan (Modify (offset, y)) instrs
          | [] -> None
        )
      | Kill (offset, y) -> (
          match instrs with
          | [] -> Some (offset, y)
          | I_aux (I_clear (ctyp', y'), _) :: _ when Name.compare y y' = 0 && ctyp_equal ctyp ctyp' -> Some (offset, y)
          | instr :: instrs ->
              if instr_references ~read:y ~write:y ~direct:false instr then None else scan (Kill (offset, y)) instrs
        )
    in
    scan (Find (0, []))

  let modify_error l = Reporting.unreachable l __POS__ "Combine variables optimisation failed"

  let modify l (skipped, nesting) ctyp x pattern_y =
    let rec traverse state instrs =
      match state with
      | Find (skipped, (child :: grandchildren as nesting)) -> (
          match instrs with
          | I_aux (I_block block, aux) :: instrs when skipped > 0 ->
              I_aux (I_block block, aux) :: traverse (Find (skipped - 1, nesting)) instrs
          | I_aux (I_block block, aux) :: instrs ->
              let block = traverse (Find (child, grandchildren)) block in
              I_aux (I_block block, aux) :: instrs
          | instr :: instrs -> instr :: traverse (Find (skipped, nesting)) instrs
          | [] -> modify_error l
        )
      | Find (skipped, []) -> (
          match instrs with
          | I_aux (I_decl (ctyp', y), _) :: instrs when ctyp_equal ctyp ctyp' ->
              assert (Name.compare pattern_y y = 0);
              traverse (Modify (no_offset, y)) instrs
          | I_aux (I_block block, aux) :: instrs when skipped > 0 ->
              I_aux (I_block block, aux) :: traverse (Find (skipped - 1, [])) instrs
          | instr :: instrs -> instr :: traverse (Find (skipped, [])) instrs
          | [] -> modify_error l
        )
      | Modify (_, y) -> (
          match instrs with
          | I_aux (I_copy (CL_id (x', ctyp'), V_id (y', ctyp'')), _) :: instrs
            when Name.compare y y' = 0 && Name.compare x x' = 0 && ctyp_equal ctyp ctyp' && ctyp_equal ctyp' ctyp'' ->
              traverse (Kill (no_offset, y)) instrs
          | instr :: instrs -> instr_rename y x instr :: traverse (Modify (no_offset, y)) instrs
          | [] -> modify_error l
        )
      | Kill (_, y) -> (
          match instrs with
          | I_aux (I_clear (ctyp', y'), _) :: instrs when Name.compare y y' = 0 && ctyp_equal ctyp ctyp' -> instrs
          | instr :: instrs -> instr :: traverse (Kill (no_offset, y)) instrs
          | [] -> []
        )
    in
    traverse (Find (skipped, nesting))

  let rec repeat_pattern l ctyp x instr instrs =
    match pattern ctyp x instrs with
    | None -> instrs
    | Some (offset, y) ->
        let instrs = modify l (reverse offset) ctyp x y instrs in
        repeat_pattern l ctyp x instr instrs

  class visitor ctyp_pred : jib_visitor =
    object
      inherit empty_jib_visitor

      method! vctyp _ = SkipChildren
      method! vclexp _ = SkipChildren
      method! vcval _ = SkipChildren

      method! vinstrs =
        function
        | (I_aux (I_decl (ctyp, x), (_, l)) as instr) :: instrs when ctyp_pred ctyp -> (
            match pattern ctyp x instrs with
            | None -> DoChildren
            | Some (offset, y) ->
                let instrs = modify l (reverse offset) ctyp x y instrs in
                let instrs = repeat_pattern l ctyp x instr instrs in
                change_do_children (instr :: instrs)
          )
        | _ -> DoChildren

      method! vcdef = function CDEF_aux (CDEF_fundef _, _) -> DoChildren | _ -> SkipChildren
    end
end

let combine_variables ctx cdefs =
  visit_cdefs (new Combine_variables.visitor (fun ctyp -> not (is_stack_ctyp ctx ctyp))) cdefs

module Remove_stack_clears = struct
  let is_stack_clear ctx = function I_aux (I_clear (ctyp, _), _) -> is_stack_ctyp ctx ctyp | _ -> false

  class visitor ctx : jib_visitor =
    object
      inherit empty_jib_visitor

      method! vinstrs instrs =
        if List.exists (is_stack_clear ctx) instrs then
          change_do_children (List.filter (fun i -> not (is_stack_clear ctx i)) instrs)
        else DoChildren
    end
end

let remove_stack_clears ctx = visit_cdefs (new Remove_stack_clears.visitor ctx)

let concatMap f xs = List.concat (List.map f xs)

let optimize ~have_rts ctx recursive_functions cdefs =
  let nothing cdefs = cdefs in
  cdefs
  |> (if !optimize_alias then concatMap remove_alias else nothing)
  |> (if !optimize_alias then combine_variables ctx else nothing)
  (* We need the runtime to initialize hoisted allocations *)
  |> (if !optimize_hoist_allocations && have_rts then concatMap (hoist_allocations recursive_functions) else nothing)
  |> remove_stack_clears ctx

(**************************************************************************)
(* 6. Code generation                                                     *)
(**************************************************************************)

let mk_regexp_check regexp_str =
  let regexp = Str.regexp regexp_str in
  fun s -> Str.string_match regexp s 0

let valid_c_identifier = mk_regexp_check "^[A-Za-z_][A-Za-z0-9_]*$"

let c_int_type_name = mk_regexp_check "^[u]?int[0-9]+_t$"

(* The code generator produces a list of C/C++ definitions and declarations
   which go in different places depending on their type and whether we
   are generating C or C++ code.
*)
type file_doc =
  (* Declaration of a custom type (typedef int foo;). This goes in a namespace in C++. *)
  | TypeDeclaration of document
  (* Model function declaration. This goes in a struct in C++ to become a struct method. *)
  | FunctionDeclaration of document
  (* Function definitions. These always go in the .c/.cpp file. *)
  | FunctionDefinition of document
  (* Variable declaration (extern int foo;) and definition (int foo = 4;).
     In C++ we only take the definition and put it in the struct.
     In C the declaration goes in the header and the definition goes in the impl. *)
  | VariableDeclaration of document
  | VariableDefinition of document
  (* Pure static utility functions created for the model's types, e.g. to initialise
     enums, access vector elements, etc. These don't have corresponding declarations. *)
  | StaticFunctionDefinition of document

module type CODEGEN_CONFIG = sig
  val includes : string list
  val header_includes : string list
  val no_main : bool
  val no_lib : bool
  val no_rts : bool
  val no_mangle : bool
  val reserved_words : Util.StringSet.t
  val overrides : string Name_generator.Overrides.t
  val branch_coverage : out_channel option
  val assert_to_exception : bool
  val preserve_types : IdSet.t
  val cpp : bool
  val cpp_class_name : string
  val cpp_namespace : string
  val cpp_derive_from : string option
end

module Codegen (Config : CODEGEN_CONFIG) = struct
  open Printf

  let has_prefix prefix s =
    if String.length s < String.length prefix then false else String.sub s 0 (String.length prefix) = prefix

  let has_sail_prefix s = has_prefix "sail_" s || has_prefix "Sail_" s || has_prefix "SAIL_" s

  (* Prefix to function name in definitions. *)
  let class_impl_prefix () = if Config.cpp then Config.cpp_class_name ^ "::" else ""

  (* = {} is required to zero-initialise the types. In C output mode this is unnecessary because
    they are emitted as globals and are therefore automatically zero-initialised. However in C++ mode they
    become struct members and aren't initialised. The `sail_set_abstract_()` function assumes that they
    have been initialised.

    Note, `int foo = {};` is legal in C23, so we can use it unconditionally eventually. *)
  let variable_zero_init () = if Config.cpp then " = {}" else ""

  module NameGen =
    Name_generator.Make
      (struct
        type style = unit

        let allowed s =
          let valid_name s =
            valid_c_identifier s
            && (not (Util.StringSet.mem s Keywords.c_reserved_words))
            && (not (Util.StringSet.mem s Keywords.c_used_words))
            && (not (Util.StringSet.mem s Config.reserved_words))
            && (not (has_sail_prefix s))
            && not (c_int_type_name s)
          in
          (not Config.no_mangle) || valid_name s

        let pretty () s = if Config.no_mangle then s else Util.zencode_string s

        let mangle () s = Util.zencode_string s

        let variant s = function 0 -> s | n -> s ^ string_of_int n

        let overrides = Config.overrides
      end)
      ()

  let sgen_id id = NameGen.to_string () id

  let sgen_uid (id, ctyps) =
    match ctyps with
    | [] -> NameGen.to_string () id
    | _ -> NameGen.translate () (string_of_id id ^ "#" ^ Util.string_of_list "_" string_of_ctyp ctyps)

  let sgen_name =
    let ssa_num n = if n = -1 then "" else "/" ^ string_of_int n in
    function
    | Gen (v1, v2, n) -> NameGen.to_string () (mk_id (sprintf "%d.%d" v1 v2)) ^ ssa_num n
    | Name (id, n) -> NameGen.to_string () id ^ ssa_num n
    | Abstract id -> NameGen.to_string ~prefix:"abstract_" () id
    | Have_exception n -> "have_exception" ^ ssa_num n
    | Return n -> "return" ^ ssa_num n
    | Current_exception n -> "(*current_exception)" ^ ssa_num n
    | Throw_location n -> "throw_location" ^ ssa_num n
    | Memory_writes n -> "memory_writes" ^ ssa_num n
    | Channel (chan, n) -> (
        match chan with Chan_stdout -> "stdout" ^ ssa_num n | Chan_stderr -> "stderr" ^ ssa_num n
      )

  let codegen_id id = string (sgen_id id)

  let sgen_function_id id =
    let str = NameGen.to_string () id in
    if Config.no_mangle then str else !opt_prefix ^ String.sub str 1 (String.length str - 1)

  let sgen_function_uid uid =
    let str = sgen_uid uid in
    if Config.no_mangle then str else !opt_prefix ^ String.sub str 1 (String.length str - 1)

  let codegen_function_id id = string (sgen_function_id id)

  let rec sgen_ctyp = function
    | CT_unit -> "unit"
    | CT_bool -> "bool"
    | CT_fbits _ -> "uint64_t"
    | CT_sbits _ -> "sbits"
    | CT_fint _ -> "int64_t"
    | CT_constant _ -> "int64_t"
    | CT_lint -> "sail_int"
    | CT_lbits -> "lbits"
    | CT_tup _ as tup -> "struct " ^ Util.zencode_string ("tuple_" ^ string_of_ctyp tup)
    | CT_struct (id, _) -> "struct " ^ sgen_id id
    | CT_enum id -> "enum " ^ sgen_id id
    | CT_variant (id, _) -> "struct " ^ sgen_id id
    | CT_list _ as l -> Util.zencode_string (string_of_ctyp l)
    | CT_vector _ as v -> Util.zencode_string (string_of_ctyp v)
    | CT_fvector (_, typ) -> sgen_ctyp (CT_vector typ)
    | CT_string -> "sail_string"
    | CT_real -> "real"
    | CT_json -> "sail_config_json"
    | CT_json_key -> "sail_config_key"
    | CT_ref ctyp -> sgen_ctyp ctyp ^ "*"
    | CT_float n -> "float" ^ string_of_int n ^ "_t"
    | CT_rounding_mode -> "uint_fast8_t"
    | CT_memory_writes -> "sail_memory_writes"
    | CT_poly _ -> "POLY" (* c_error "Tried to generate code for non-monomorphic type" *)

  let rec sgen_ctyp_name = function
    | CT_unit -> "unit"
    | CT_bool -> "bool"
    | CT_fbits _ -> "fbits"
    | CT_sbits _ -> "sbits"
    | CT_fint _ -> "mach_int"
    | CT_constant _ -> "mach_int"
    | CT_lint -> "sail_int"
    | CT_lbits -> "lbits"
    | CT_tup _ as tup -> Util.zencode_string ("tuple_" ^ string_of_ctyp tup)
    | CT_struct (id, _) -> sgen_id id
    | CT_enum id -> sgen_id id
    | CT_variant (id, _) -> sgen_id id
    | CT_list _ as l -> Util.zencode_string (string_of_ctyp l)
    | CT_vector _ as v -> Util.zencode_string (string_of_ctyp v)
    | CT_fvector (_, typ) -> sgen_ctyp_name (CT_vector typ)
    | CT_string -> "sail_string"
    | CT_real -> "real"
    | CT_json -> "sail_config_json"
    | CT_json_key -> "sail_config_key"
    | CT_ref ctyp -> "ref_" ^ sgen_ctyp_name ctyp
    | CT_float n -> "float" ^ string_of_int n
    | CT_rounding_mode -> "rounding_mode"
    | CT_memory_writes -> "sail_memory_writes"
    | CT_poly _ -> "POLY" (* c_error "Tried to generate code for non-monomorphic type" *)

  let sgen_const_ctyp = function CT_string -> "const_sail_string" | ty -> sgen_ctyp ty

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
    | VL_real str -> str
    | VL_string str -> "\"" ^ str ^ "\""
    | VL_enum element -> Util.zencode_string element
    | VL_ref r -> "&" ^ sgen_id (mk_id r)
    | VL_undefined -> Reporting.unreachable Parse_ast.Unknown __POS__ "Cannot generate C value for an undefined literal"

  let sgen_tuple_id n = sgen_id (mk_id ("tup" ^ string_of_int n))

  let rec sgen_cval = function
    | V_id (id, _) -> sgen_name id
    | V_member (id, _) -> sgen_id id
    | V_lit (vl, _) -> sgen_value vl
    | V_call (op, cvals) -> sgen_call op cvals
    | V_field (f, field, _) -> sprintf "%s.%s" (sgen_cval f) (sgen_id field)
    | V_tuple_member (f, _, n) -> sprintf "%s.%s" (sgen_cval f) (sgen_tuple_id n)
    | V_ctor_kind (f, ctor) -> sgen_cval f ^ ".kind" ^ " != Kind_" ^ sgen_uid ctor
    | V_struct (fields, _) ->
        sprintf "{%s}" (Util.string_of_list ", " (fun (field, cval) -> sgen_id field ^ " = " ^ sgen_cval cval) fields)
    | V_ctor_unwrap (f, ctor, _) -> sprintf "%s.variants.%s" (sgen_cval f) (sgen_uid ctor)
    | V_tuple _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Cannot generate C value for a tuple literal"

  and sgen_call op cvals =
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
            sprintf "((%s & ~(%s << %s)) | (%s << %s))" (sgen_cval vec) (sgen_mask m) (sgen_cval start)
              (sgen_cval slice) (sgen_cval start)
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
    | Ite, [i; t; e] -> sprintf "(%s ? %s : %s)" (sgen_cval i) (sgen_cval t) (sgen_cval e)
    | String_eq, [s1; s2] -> sprintf "(strcmp(%s, %s) == 0)" (sgen_cval s1) (sgen_cval s2)
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
    | CL_id (Memory_writes _, _) -> "memory_writes"
    | CL_id (Channel _, _) -> Reporting.unreachable l __POS__ "CL_id Channel should not appear in C backend"
    | CL_id (Return _, _) -> Reporting.unreachable l __POS__ "CL_id Return should have been removed"
    | CL_id (name, _) -> "&" ^ sgen_name name
    | CL_field (clexp, field, _) -> "&((" ^ sgen_clexp l clexp ^ ")->" ^ sgen_id field ^ ")"
    | CL_tuple (clexp, n) -> sprintf "&((%s)->%s)" (sgen_clexp l clexp) (sgen_tuple_id n)
    | CL_addr clexp -> "(*(" ^ sgen_clexp l clexp ^ "))"
    | CL_void _ -> assert false
    | CL_rmw _ -> assert false

  let rec sgen_clexp_pure l = function
    | CL_id (Have_exception _, _) -> "have_exception"
    | CL_id (Current_exception _, _) -> "current_exception"
    | CL_id (Throw_location _, _) -> "throw_location"
    | CL_id (Memory_writes _, _) -> "memory_writes"
    | CL_id (Channel _, _) -> Reporting.unreachable l __POS__ "CL_id Channel should not appear in C backend"
    | CL_id (Return _, _) -> Reporting.unreachable l __POS__ "CL_id Return should have been removed"
    | CL_id (name, _) -> sgen_name name
    | CL_field (clexp, field, _) -> sgen_clexp_pure l clexp ^ "." ^ sgen_id field
    | CL_tuple (clexp, n) -> sgen_clexp_pure l clexp ^ "." ^ sgen_tuple_id n
    | CL_addr clexp -> "(*(" ^ sgen_clexp_pure l clexp ^ "))"
    | CL_void _ -> assert false
    | CL_rmw _ -> assert false

  let codegen_equal ctyp arg1 arg2 =
    match ctyp with
    | CT_ref _ -> ksprintf string "(%s == %s)" arg1 arg2
    | ctyp -> sail_equal (sgen_ctyp_name ctyp) "%s, %s" arg1 arg2

  (** Generate instructions to copy from a cval to a clexp. This will insert any needed type conversions from big
      integers to small integers (or vice versa), or from arbitrary-length bitvectors to and from uint64 bitvectors as
      needed. *)
  let rec codegen_conversion l ctx clexp cval =
    let ctyp_to = clexp_ctyp clexp in
    let ctyp_from = cval_ctyp cval in
    match (ctyp_to, ctyp_from) with
    (* When both types are equal, we don't need any conversion. *)
    | _, _ when ctyp_equal ctyp_to ctyp_from ->
        if is_stack_ctyp ctx ctyp_to then ksprintf string "  %s = %s;" (sgen_clexp_pure l clexp) (sgen_cval cval)
        else sail_copy ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp_to) "%s, %s" (sgen_clexp l clexp) (sgen_cval cval)
    | CT_ref _, _ -> codegen_conversion l ctx (CL_addr clexp) cval
    | ( (CT_vector ctyp_elem_to | CT_fvector (_, ctyp_elem_to)),
        (CT_vector ctyp_elem_from | CT_fvector (_, ctyp_elem_from)) ) ->
        let i = ngensym () in
        let from = ngensym () in
        let into = ngensym () in
        sail_kill ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp_to) "%s" (sgen_clexp l clexp)
        ^^ hardline
        ^^ ksprintf string "  internal_vector_init_%s(%s, %s.len);" (sgen_ctyp_name ctyp_to) (sgen_clexp l clexp)
             (sgen_cval cval)
        ^^ hardline
        ^^ ksprintf string "  for (int %s = 0; %s < %s.len; %s++) {" (sgen_name i) (sgen_name i) (sgen_cval cval)
             (sgen_name i)
        ^^ hardline
        ^^ ( if is_stack_ctyp ctx ctyp_elem_from then
               ksprintf string "    %s %s = %s.data[%s];" (sgen_ctyp ctyp_elem_from) (sgen_name from) (sgen_cval cval)
                 (sgen_name i)
             else
               ksprintf string "    %s %s;" (sgen_ctyp ctyp_elem_from) (sgen_name from)
               ^^ hardline
               ^^ sail_create ~prefix:"    " ~suffix:";" (sgen_ctyp_name ctyp_elem_from) "&%s" (sgen_name from)
               ^^ hardline
               ^^ sail_copy ~prefix:"    " ~suffix:";" (sgen_ctyp_name ctyp_elem_from) "&%s, %s.data[%s]"
                    (sgen_name from) (sgen_cval cval) (sgen_name i)
           )
        ^^ hardline
        ^^ ksprintf string "    %s %s;" (sgen_ctyp ctyp_elem_to) (sgen_name into)
        ^^ ( if is_stack_ctyp ctx ctyp_elem_to then empty
             else hardline ^^ sail_create ~prefix:"    " ~suffix:";" (sgen_ctyp_name ctyp_elem_to) "&%s" (sgen_name into)
           )
        ^^ nest 2 (hardline ^^ codegen_conversion l ctx (CL_id (into, ctyp_elem_to)) (V_id (from, ctyp_elem_from)))
        ^^ hardline
        ^^ ( if is_stack_ctyp ctx ctyp_elem_to then
               ksprintf string "    %s.data[%s] = %s;" (sgen_clexp_pure l clexp) (sgen_name i) (sgen_name into)
             else
               sail_copy ~prefix:"    " ~suffix:";" (sgen_ctyp_name ctyp_elem_to) "&((%s)->data[%s]), %s"
                 (sgen_clexp l clexp) (sgen_name i) (sgen_name into)
               ^^ hardline
               ^^ sail_kill ~prefix:"    " ~suffix:";" (sgen_ctyp_name ctyp_elem_to) "&%s" (sgen_name into)
           )
        ^^ ( if is_stack_ctyp ctx ctyp_elem_from then empty
             else hardline ^^ sail_kill ~prefix:"    " ~suffix:";" (sgen_ctyp_name ctyp_elem_from) "&%s" (sgen_name from)
           )
        ^^ hardline ^^ string "  }"
    (* If we have to convert between tuple types, convert the fields individually. *)
    | CT_tup ctyps_to, CT_tup ctyps_from when List.length ctyps_to = List.length ctyps_from ->
        let len = List.length ctyps_to in
        let conversions =
          List.mapi
            (fun i _ -> codegen_conversion l ctx (CL_tuple (clexp, i)) (V_tuple_member (cval, len, i)))
            ctyps_from
        in
        string "  /* conversions */" ^^ hardline ^^ separate hardline conversions ^^ hardline
        ^^ string "  /* end conversions */"
    (* For anything not special cased, just try to call a appropriate CONVERT_OF function. *)
    | _, _ when is_stack_ctyp ctx (clexp_ctyp clexp) ->
        sail_convert_of
          ~prefix:(sprintf "  %s = " (sgen_clexp_pure l clexp))
          ~suffix:";" (sgen_ctyp_name ctyp_to) (sgen_ctyp_name ctyp_from) "%s" (sgen_cval_param cval)
    | _, _ ->
        sail_convert_of ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp_to) (sgen_ctyp_name ctyp_from) "%s, %s"
          (sgen_clexp l clexp) (sgen_cval_param cval)

  (* PPrint doesn't provide a nice way to filter out empty documents *)
  let squash_empty docs = List.filter (fun doc -> requirement doc > 0) docs
  let sq_separate_map sep f xs = separate sep (squash_empty (List.map f xs))

  let rec codegen_instr fid ctx (I_aux (instr, (_, l))) =
    match instr with
    | I_decl (ctyp, id) when is_stack_ctyp ctx ctyp -> ksprintf string "  %s %s;" (sgen_ctyp ctyp) (sgen_name id)
    | I_decl (ctyp, id) ->
        ksprintf string "  %s %s;" (sgen_ctyp ctyp) (sgen_name id)
        ^^ hardline
        ^^ sail_create ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
    | I_copy (clexp, cval) -> codegen_conversion l ctx clexp cval
    | I_jump (cval, label) -> ksprintf string "  if (%s) goto %s;" (sgen_cval cval) label
    | I_if (cval, [], else_instrs) -> codegen_instr fid ctx (iif l (V_call (Bnot, [cval])) else_instrs [])
    | I_if (cval, [then_instr], []) ->
        ksprintf string "  if (%s)" (sgen_cval cval)
        ^^ space
        ^^ surround 2 0 lbrace (codegen_instr fid ctx then_instr) (twice space ^^ rbrace)
    | I_if (cval, then_instrs, []) ->
        string "  if" ^^ space
        ^^ parens (string (sgen_cval cval))
        ^^ space
        ^^ surround 2 0 lbrace (separate_map hardline (codegen_instr fid ctx) then_instrs) (twice space ^^ rbrace)
    | I_if (cval, then_instrs, else_instrs) ->
        let rec codegen_if cval then_instrs else_instrs =
          match else_instrs with
          | [I_aux (I_if (else_i, else_t, else_e), _)] ->
              string "if" ^^ space
              ^^ parens (string (sgen_cval cval))
              ^^ space
              ^^ surround 2 0 lbrace
                   (sq_separate_map hardline (codegen_instr fid ctx) then_instrs)
                   (twice space ^^ rbrace)
              ^^ space ^^ string "else" ^^ space ^^ codegen_if else_i else_t else_e
          | _ ->
              string "if" ^^ space
              ^^ parens (string (sgen_cval cval))
              ^^ space
              ^^ surround 2 0 lbrace
                   (sq_separate_map hardline (codegen_instr fid ctx) then_instrs)
                   (twice space ^^ rbrace)
              ^^ space ^^ string "else" ^^ space
              ^^ surround 2 0 lbrace
                   (sq_separate_map hardline (codegen_instr fid ctx) else_instrs)
                   (twice space ^^ rbrace)
        in
        twice space ^^ codegen_if cval then_instrs else_instrs
    | I_block instrs ->
        string "  {" ^^ jump 2 2 (sq_separate_map hardline (codegen_instr fid ctx) instrs) ^^ hardline ^^ string "  }"
    | I_try_block instrs ->
        string "  { /* try */"
        ^^ jump 2 2 (sq_separate_map hardline (codegen_instr fid ctx) instrs)
        ^^ hardline ^^ string "  }"
    | I_funcall (x, extern_info, f, args) ->
        let special_extern = match extern_info with Extern _ -> true | Call -> false in
        let x =
          match x with
          | CR_one x -> x
          | CR_multi _ -> Reporting.unreachable l __POS__ "Multiple returns should not exist in C backend"
        in
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
          | "internal_pick", _ -> sprintf "pick_%s" (sgen_ctyp_name ctyp)
          | "sail_cons", _ -> begin
              match Option.map cval_ctyp (List.nth_opt args 0) with
              | Some ctyp -> Util.zencode_string ("cons#" ^ string_of_ctyp (ctyp_suprema ctyp))
              | None -> c_error "cons without specified type"
            end
          | "eq_anything", _ -> begin
              match args with
              | cval :: _ -> sprintf "eq_%s" (sgen_ctyp_name (cval_ctyp cval))
              | _ -> c_error "eq_anything function with bad arity."
            end
          | "length", _ -> begin
              match args with
              | cval :: _ -> sprintf "length_%s" (sgen_ctyp_name (cval_ctyp cval))
              | _ -> c_error "length function with bad arity."
            end
          | "vector_access", CT_fbits 1 -> "bitvector_access"
          | "vector_access_inc", CT_fbits 1 -> "bitvector_access_inc"
          | "vector_access", _ -> begin
              match args with
              | cval :: _ -> sprintf "vector_access_%s" (sgen_ctyp_name (cval_ctyp cval))
              | _ -> c_error "vector access function with bad arity."
            end
          | "fast_vector_access", _ -> begin
              match args with
              | cval :: _ -> sprintf "fast_vector_access_%s" (sgen_ctyp_name (cval_ctyp cval))
              | _ -> c_error "vector access function with bad arity."
            end
          | "vector_init", _ -> sprintf "vector_init_%s" (sgen_ctyp_name ctyp)
          | "vector_update_subrange", _ -> sprintf "vector_update_subrange_%s" (sgen_ctyp_name ctyp)
          | "vector_update_subrange_inc", _ -> sprintf "vector_update_subrange_inc_%s" (sgen_ctyp_name ctyp)
          | "vector_subrange", _ -> sprintf "vector_subrange_%s" (sgen_ctyp_name ctyp)
          | "vector_subrange_inc", _ -> sprintf "vector_subrange_inc_%s" (sgen_ctyp_name ctyp)
          | "vector_update", CT_fbits _ -> "update_fbits"
          | "vector_update", CT_lbits -> "update_lbits"
          | "vector_update", _ -> sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
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
          | "internal_vector_update", _ -> sprintf "internal_vector_update_%s" (sgen_ctyp_name ctyp)
          | "internal_vector_init", _ -> sprintf "internal_vector_init_%s" (sgen_ctyp_name ctyp)
          | "undefined_bitvector", CT_fbits _ -> "UNDEFINED(fbits)"
          | "undefined_bitvector", CT_lbits -> "UNDEFINED(lbits)"
          | "undefined_bit", _ -> "UNDEFINED(fbits)"
          | "undefined_vector", _ -> sprintf "UNDEFINED(vector_%s)" (sgen_ctyp_name ctyp)
          | "undefined_list", _ -> sprintf "UNDEFINED(%s)" (sgen_ctyp_name ctyp)
          | fname, _ -> fname
        in
        if fname = "reg_deref" then
          if is_stack_ctyp ctx ctyp then ksprintf string "  %s = *(%s);" (sgen_clexp_pure l x) c_args
          else sail_copy ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s, *(%s)" (sgen_clexp_pure l x) c_args
        else if is_stack_ctyp ctx ctyp then
          string (Printf.sprintf "  %s = %s(%s%s);" (sgen_clexp_pure l x) fname (extra_arguments is_extern) c_args)
        else string (Printf.sprintf "  %s(%s%s, %s);" fname (extra_arguments is_extern) (sgen_clexp l x) c_args)
    | I_clear (ctyp, _) when is_stack_ctyp ctx ctyp -> empty
    | I_clear (ctyp, id) -> sail_kill ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
    | I_init (ctyp, id, init) -> (
        match init with
        | Init_cval cval ->
            codegen_instr fid ctx (idecl l ctyp id) ^^ hardline ^^ codegen_conversion l ctx (CL_id (id, ctyp)) cval
        | Init_static VL_undefined -> ksprintf string "  static %s %s;" (sgen_ctyp ctyp) (sgen_name id)
        | Init_static vl -> ksprintf string "  static %s %s = %s;" (sgen_ctyp ctyp) (sgen_name id) (sgen_value vl)
        | Init_json_key parts ->
            let name = sgen_name id in
            (* Separate declaration and assignment avoids errors about goto's crossing the initialisation
               when compiling this code as C++. Unfortunately this also means we can't use an initialiser
               list to assign its value. We could move all of these to the top of the function but
               I don't know how to do that. *)
            ksprintf string "  const_sail_string %s[%d];" name (List.length parts)
            ^^ Util.fold_left_index
                 (fun i acc part -> acc ^^ hardline ^^ ksprintf string "  %s[%d] = \"%s\";" name i part)
                 empty parts
      )
    | I_reinit (ctyp, id, cval) ->
        codegen_instr fid ctx (ireset l ctyp id) ^^ hardline ^^ codegen_conversion l ctx (CL_id (id, ctyp)) cval
    | I_reset (ctyp, id) when is_stack_ctyp ctx ctyp ->
        string (Printf.sprintf "  %s %s;" (sgen_ctyp ctyp) (sgen_name id))
    | I_reset (ctyp, id) -> sail_recreate ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
    | I_return cval -> twice space ^^ c_return (string (sgen_cval cval))
    | I_throw _ -> c_error ~loc:l "I_throw reached code generator"
    | I_undefined ctyp ->
        let rec codegen_exn_return ctyp =
          match ctyp with
          | CT_unit -> ("UNIT", [])
          | CT_fint _ -> ("INT64_C(0xdeadc0de)", [])
          | CT_lint when !optimize_fixed_int -> ("((sail_int) 0xdeadc0de)", [])
          | CT_fbits 1 -> ("UINT64_C(0)", [])
          | CT_fbits _ -> ("UINT64_C(0xdeadc0de)", [])
          | CT_sbits _ -> ("undefined_sbits()", [])
          | CT_lbits when !optimize_fixed_bits -> ("undefined_lbits(false)", [])
          | CT_bool -> ("false", [])
          | CT_enum _ -> (sprintf "((%s)0)" (sgen_ctyp ctyp), [])
          | CT_tup ctyps when is_stack_ctyp ctx ctyp ->
              let gs = ngensym () in
              let fold (n, ctyp) (inits, prev) =
                let init, prev' = codegen_exn_return ctyp in
                (sprintf ".%s = %s" (sgen_tuple_id n) init :: inits, prev @ prev')
              in
              let inits, prev = List.fold_right fold (List.mapi (fun i x -> (i, x)) ctyps) ([], []) in
              ( sgen_name gs,
                [
                  sprintf "struct %s %s = { " (sgen_ctyp_name ctyp) (sgen_name gs)
                  ^ Util.string_of_list ", " (fun x -> x) inits
                  ^ " };";
                ]
                @ prev
              )
          | CT_struct _ when is_stack_ctyp ctx ctyp ->
              let fields = struct_field_bindings l ctx ctyp |> snd |> Bindings.bindings in
              let gs = ngensym () in
              let fold (id, ctyp) (inits, prev) =
                let init, prev' = codegen_exn_return ctyp in
                (sprintf ".%s = %s" (sgen_id id) init :: inits, prev @ prev')
              in
              let inits, prev = List.fold_right fold fields ([], []) in
              ( sgen_name gs,
                [
                  sprintf "struct %s %s = { " (sgen_ctyp_name ctyp) (sgen_name gs)
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

  let codegen_type_def ctx =
    let open Printf in
    function
    | CTD_abstract (id, ctyp, inst) ->
        let setter_prototype, setter =
          match inst with
          | CTDI_none ->
              ( ksprintf string "void sail_set_abstract_%s(%s v);" (string_of_id id) (sgen_ctyp ctyp),
                c_function ~return:"void"
                  (ksprintf string "%ssail_set_abstract_%s(%s v)" (class_impl_prefix ()) (string_of_id id)
                     (sgen_ctyp ctyp)
                  )
                  [
                    ( if is_stack_ctyp ctx ctyp then
                        ksprintf c_stmt "%s = v" (NameGen.to_string ~prefix:"abstract_" () id)
                      else
                        sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "&%s, v"
                          (NameGen.to_string ~prefix:"abstract_" () id)
                    );
                  ]
              )
          | CTDI_instrs init ->
              ( ksprintf string "void sail_set_abstract_%s(void);" (string_of_id id),
                c_function ~return:"void"
                  (ksprintf string "%ssail_set_abstract_%s(void)" (class_impl_prefix ()) (string_of_id id))
                  [separate_map hardline (codegen_instr (mk_id "set_abstract") ctx) init]
              )
        in
        [
          FunctionDeclaration setter_prototype;
          FunctionDefinition setter;
          VariableDefinition
            (ksprintf string "%s %s%s;" (sgen_ctyp ctyp)
               (NameGen.to_string ~prefix:"abstract_" () id)
               (variable_zero_init ())
            );
        ]
    | CTD_enum (id, (first_id :: _ as ids)) ->
        let enum_name = sgen_id id in
        let enum_eq =
          c_function ~return:"static bool"
            (sail_equal enum_name "enum %s op1, enum %s op2" enum_name enum_name)
            [c_stmt "return op1 == op2"]
        in
        let enum_undefined =
          let name = sgen_id id in
          string (Printf.sprintf "static enum %s UNDEFINED(%s)(unit u) { return %s; }" name name (sgen_id first_id))
        in
        [
          TypeDeclaration
            (string (Printf.sprintf "// enum %s" (string_of_id id))
            ^^ hardline
            ^^ separate space
                 [string "enum"; codegen_id id; lbrace; separate_map (comma ^^ space) codegen_id ids; rbrace ^^ semi]
            );
          StaticFunctionDefinition enum_eq;
          StaticFunctionDefinition enum_undefined;
        ]
    | CTD_enum (id, []) -> c_error ("Cannot compile empty enum " ^ string_of_id id)
    | CTD_abbrev (id, ctyp) ->
        [
          TypeDeclaration
            (ksprintf string "// type abbreviation %s" (string_of_id id)
            ^^ hardline
            ^^ separate space [string "typedef"; string (sgen_ctyp ctyp); codegen_id id]
            ^^ semi
            );
        ]
    | CTD_struct (id, _, ctors) ->
        let struct_name = sgen_id id in
        let struct_ctyp = CT_struct (id, []) in
        (* Generate a set_T function for every struct T *)
        let set_field (id, ctyp) =
          if is_stack_ctyp ctx ctyp then ksprintf c_stmt "rop->%s = op.%s" (sgen_id id) (sgen_id id)
          else sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "&rop->%s, op.%s" (sgen_id id) (sgen_id id)
        in
        let struct_copy =
          c_function ~return:"static void"
            (sail_copy struct_name "struct %s *rop, const struct %s op" struct_name struct_name)
            (List.map set_field ctors)
        in
        (* Derive the various lifecycle functions create/recreate/kill for the struct *)
        let derive (f : string -> ('a, unit, string, document) format4 -> 'a) =
          let per_field (field_id, ctyp) =
            if not (is_stack_ctyp ctx ctyp) then [f (sgen_ctyp_name ctyp) "&op->%s" (sgen_id field_id) ^^ semi] else []
          in
          c_function ~return:"static void"
            (f struct_name "struct %s *op" struct_name)
            (List.concat (List.map per_field ctors))
        in
        let struct_eq =
          let field_eq (field_id, ctyp) =
            let field = sgen_id field_id in
            codegen_equal ctyp (sprintf "op1.%s" field) (sprintf "op2.%s" field)
          in
          c_function ~return:"static bool"
            (sail_equal (sgen_id id) "struct %s op1, struct %s op2" (sgen_id id) (sgen_id id))
            [string "return" ^^ space ^^ separate_map (string " && ") field_eq ctors ^^ semi]
        in
        (* Generate the struct and add the generated functions *)
        let struct_field (id, ctyp) = string (sgen_ctyp ctyp) ^^ space ^^ codegen_id id in

        [
          TypeDeclaration
            (string (Printf.sprintf "// struct %s" (string_of_id id))
            ^^ hardline ^^ string "struct" ^^ space ^^ codegen_id id ^^ space
            ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) struct_field ctors ^^ semi) rbrace
            ^^ semi
            );
          StaticFunctionDefinition struct_copy;
        ]
        @ ( if not (is_stack_ctyp ctx struct_ctyp) then
              [
                StaticFunctionDefinition (derive sail_create);
                StaticFunctionDefinition (derive sail_recreate);
                StaticFunctionDefinition (derive sail_kill);
              ]
            else []
          )
        @ [StaticFunctionDefinition struct_eq]
    | CTD_variant (id, _, tus) ->
        let codegen_tu (ctor_id, ctyp) =
          separate space [string "struct"; lbrace; string (sgen_ctyp ctyp); codegen_id ctor_id ^^ semi; rbrace]
        in
        (* Create an if, else if, ... block that does something for each constructor *)
        let rec each_ctor v f = function
          | [] -> string "{}"
          | [(ctor_id, ctyp)] -> begin
              match f ctor_id ctyp with
              | None -> string "{}"
              | Some op -> c_if (ksprintf string "(%skind == Kind_%s)" v (sgen_id ctor_id)) [op]
            end
          | (ctor_id, ctyp) :: ctors -> begin
              match f ctor_id ctyp with
              | None -> each_ctor v f ctors
              | Some op ->
                  c_if (ksprintf string "(%skind == Kind_%s)" v (sgen_id ctor_id)) [op]
                  ^^ space ^^ string "else" ^^ space ^^ each_ctor v f ctors
            end
        in
        let codegen_init =
          let n = sgen_id id in
          let ctor_id, ctyp = List.hd tus in
          c_function ~return:"static void" (sail_create n "struct %s *op" n)
            ([string (Printf.sprintf "op->kind = Kind_%s;" (sgen_id ctor_id))]
            @
            if not (is_stack_ctyp ctx ctyp) then
              [sail_create ~suffix:";" (sgen_ctyp_name ctyp) "&op->variants.%s" (sgen_id ctor_id)]
            else []
            )
        in
        let codegen_reinit =
          let n = sgen_id id in
          c_function ~return:"static void" (sail_recreate n "struct %s *op" n) []
        in
        let clear_field v ctor_id ctyp =
          if is_stack_ctyp ctx ctyp then None
          else Some (sail_kill ~suffix:";" (sgen_ctyp_name ctyp) "&%s->variants.%s" v (sgen_id ctor_id))
        in
        let codegen_clear =
          let n = sgen_id id in
          c_function ~return:"static void" (sail_kill n "struct %s *op" n) [each_ctor "op->" (clear_field "op") tus]
        in
        let codegen_ctor (ctor_id, ctyp) =
          let ctor_args = Printf.sprintf "%s op" (sgen_const_ctyp ctyp) in
          c_function ~return:"static void"
            (ksprintf string "%s(%sstruct %s *rop, %s)" (sgen_function_id ctor_id) (extra_params ()) (sgen_id id)
               ctor_args
            )
            ([each_ctor "rop->" (clear_field "rop") tus; string ("rop->kind = Kind_" ^ sgen_id ctor_id) ^^ semi]
            @
            if is_stack_ctyp ctx ctyp then [ksprintf string "rop->variants.%s = op;" (sgen_id ctor_id)]
            else
              [
                sail_create ~suffix:";" (sgen_ctyp_name ctyp) "&rop->variants.%s" (sgen_id ctor_id);
                sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "&rop->variants.%s, op" (sgen_id ctor_id);
              ]
            )
        in
        let codegen_setter =
          let n = sgen_id id in
          let set_field ctor_id ctyp =
            Some
              ( if is_stack_ctyp ctx ctyp then
                  string (Printf.sprintf "rop->variants.%s = op.variants.%s;" (sgen_id ctor_id) (sgen_id ctor_id))
                else
                  sail_create ~suffix:";" (sgen_ctyp_name ctyp) "&rop->variants.%s" (sgen_id ctor_id)
                  ^^ sail_copy ~prefix:" " ~suffix:";" (sgen_ctyp_name ctyp) "&rop->variants.%s, op.variants.%s"
                       (sgen_id ctor_id) (sgen_id ctor_id)
              )
          in
          c_function ~return:"static void"
            (sail_copy n "struct %s *rop, struct %s op" n n)
            [
              each_ctor "rop->" (clear_field "rop") tus ^^ semi;
              c_stmt "rop->kind = op.kind";
              each_ctor "op." set_field tus;
            ]
        in
        let codegen_eq =
          let codegen_eq_test ctor_id ctyp =
            c_return
              (codegen_equal ctyp
                 (sprintf "op1.variants.%s" (sgen_id ctor_id))
                 (sprintf "op2.variants.%s" (sgen_id ctor_id))
              )
          in
          let rec codegen_eq_tests = function
            | [] -> c_return (string "false")
            | (ctor_id, ctyp) :: ctors ->
                c_if
                  (ksprintf string "(op1.kind == Kind_%s && op2.kind == Kind_%s)" (sgen_id ctor_id) (sgen_id ctor_id))
                  [codegen_eq_test ctor_id ctyp]
                ^^ space ^^ string "else" ^^ space ^^ codegen_eq_tests ctors
          in
          let n = sgen_id id in
          c_function ~return:"static bool" (sail_equal n "struct %s op1, struct %s op2" n n) [codegen_eq_tests tus]
        in
        [
          TypeDeclaration
            (string (Printf.sprintf "// union %s" (string_of_id id))
            ^^ hardline ^^ string "enum" ^^ space
            ^^ string ("kind_" ^ sgen_id id)
            ^^ space
            ^^ separate space
                 [
                   lbrace;
                   separate_map (comma ^^ space) (fun id -> string ("Kind_" ^ sgen_id id)) (List.map fst tus);
                   rbrace ^^ semi;
                 ]
            );
          TypeDeclaration
            (string "struct" ^^ space ^^ codegen_id id ^^ space
            ^^ surround 2 0 lbrace
                 (separate space [string "enum"; string ("kind_" ^ sgen_id id); string "kind" ^^ semi]
                 ^^ hardline ^^ string "union" ^^ space
                 ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) codegen_tu tus ^^ semi) rbrace
                 ^^ space ^^ string "variants" ^^ semi
                 )
                 rbrace
            ^^ semi
            );
          StaticFunctionDefinition codegen_init;
          StaticFunctionDefinition codegen_reinit;
          StaticFunctionDefinition codegen_clear;
          StaticFunctionDefinition codegen_setter;
          StaticFunctionDefinition codegen_eq;
        ]
        @ List.map (fun tu -> StaticFunctionDefinition (codegen_ctor tu)) tus
        (* If this is the exception type, then we setup up some global variables to deal with exceptions. *)
        @
        if string_of_id id = "exception" then
          [
            VariableDeclaration (ksprintf string "extern struct %s *current_exception;" (sgen_id id));
            VariableDefinition (ksprintf string "struct %s *current_exception = NULL;" (sgen_id id));
            VariableDeclaration (string "extern bool have_exception;");
            VariableDefinition (string "bool have_exception = false;");
            VariableDeclaration (string "extern sail_string *throw_location;");
            VariableDefinition (string "sail_string *throw_location = NULL;");
          ]
        else []

  (** GLOBAL: because C doesn't have real anonymous tuple types (anonymous structs don't quite work the way we need)
      every tuple type in the spec becomes some generated named struct in C. This is done in such a way that every
      possible tuple type has a unique name associated with it. This global variable keeps track of these generated
      struct names, so we never generate two copies of the struct that is used to represent them in C. The way this
      works is that codegen_def scans each definition's type annotations for tuple types and generates the required
      structs using codegen_type_def before the actual definition is generated by codegen_def'. This variable should be
      reset to empty only when the entire AST has been translated to C. **)
  let generated = ref IdSet.empty

  let codegen_tup ctx ctyps =
    let id = mk_id ("tuple_" ^ string_of_ctyp (CT_tup ctyps)) in
    if IdSet.mem id !generated then []
    else begin
      let _, fields =
        List.fold_left
          (fun (n, fields) ctyp -> (n + 1, Bindings.add (mk_id ("tup" ^ string_of_int n)) ctyp fields))
          (0, Bindings.empty) ctyps
      in
      generated := IdSet.add id !generated;
      codegen_type_def
        { ctx with records = Bindings.add id ([], fields) ctx.records }
        (CTD_struct (id, [], Bindings.bindings fields))
    end

  let codegen_list ctx ctyp =
    let open Printf in
    let id = mk_id (string_of_ctyp (CT_list ctyp)) in
    if IdSet.mem id !generated then []
    else (
      generated := IdSet.add id !generated;
      let codegen_node =
        ksprintf string "struct node_%s {\n  unsigned int rc;\n  %s hd;\n  struct node_%s *tl;\n};\n" (sgen_id id)
          (sgen_ctyp ctyp) (sgen_id id)
        ^^ string (sprintf "typedef struct node_%s *%s;" (sgen_id id) (sgen_id id))
      in

      let codegen_list_init =
        let create = sail_create (sgen_id id) "%s *rop" (sgen_id id) in
        separate space [string "static void"; create; string "{ *rop = NULL; }"]
      in

      let codegen_list_clear =
        let kill = sail_kill (sgen_id id) "%s *rop" (sgen_id id) in
        separate space [string "static void"; kill; char '{']
        ^^ hardline ^^ string "  if (*rop == NULL) return;\n" ^^ string "  if ((*rop)->rc >= 1) {\n"
        ^^ string "    (*rop)->rc -= 1;\n" ^^ string "  }\n"
        ^^ ksprintf string "  %s node = *rop;\n" (sgen_id id)
        ^^ string "  while (node != NULL && node->rc == 0) {\n"
        ^^ ( if is_stack_ctyp ctx ctyp then empty
             else sail_kill ~prefix:"    " ~suffix:";\n" (sgen_ctyp_name ctyp) "&node->hd"
           )
        ^^ ksprintf string "    %s next = node->tl;\n" (sgen_id id)
        ^^ string "    sail_free(node);\n" ^^ string "    node = next;\n"
        ^^ ksprintf string "    internal_dec_%s(node);\n" (sgen_id id)
        ^^ string "  }\n" ^^ string "}"
      in

      let codegen_list_recreate =
        c_function ~return:"static void"
          (sail_recreate (sgen_id id) "%s *rop" (sgen_id id))
          [sail_kill ~suffix:";" (sgen_id id) "rop"; string "*rop = NULL;"]
      in

      let codegen_inc_reference_count =
        string (sprintf "static void internal_inc_%s(%s l) {\n" (sgen_id id) (sgen_id id))
        ^^ string "  if (l == NULL) return;\n" ^^ string "  l->rc += 1;\n" ^^ string "}"
      in

      let codegen_dec_reference_count =
        string (sprintf "static void internal_dec_%s(%s l) {\n" (sgen_id id) (sgen_id id))
        ^^ string "  if (l == NULL) return;\n" ^^ string "  l->rc -= 1;\n" ^^ string "}"
      in

      let codegen_list_copy =
        let ty = sgen_id id in
        c_function ~return:"static void" (sail_copy ty "%s *rop, %s op" ty ty)
          [ksprintf c_stmt "internal_inc_%s(op)" ty; sail_kill ~suffix:";" ty "rop"; c_stmt "*rop = op"]
      in

      let codegen_cons =
        let cons_id = mk_id ("cons#" ^ string_of_ctyp ctyp) in
        ksprintf string "static void %s(%s *rop, %s x, %s xs) {\n" (sgen_function_id cons_id) (sgen_id id)
          (sgen_const_ctyp ctyp) (sgen_id id)
        ^^ string "  bool same = *rop == xs;\n"
        ^^ ksprintf string "  *rop = sail_new(struct node_%s);\n" (sgen_id id)
        ^^ string "  (*rop)->rc = 1;\n"
        ^^ ( if is_stack_ctyp ctx ctyp then string "  (*rop)->hd = x;\n"
             else
               sail_create ~prefix:"  " ~suffix:";\n" (sgen_ctyp_name ctyp) "&(*rop)->hd"
               ^^ sail_copy ~prefix:"  " ~suffix:";\n" (sgen_ctyp_name ctyp) "&(*rop)->hd, x"
           )
        ^^ ksprintf string "  if (!same) internal_inc_%s(xs);\n" (sgen_id id)
        ^^ string "  (*rop)->tl = xs;\n" ^^ string "}"
      in

      let codegen_pick =
        if is_stack_ctyp ctx ctyp then
          c_function
            ~return:(sprintf "static %s" (sgen_ctyp ctyp))
            (ksprintf string "pick_%s(const %s xs)" (sgen_ctyp_name ctyp) (sgen_id id))
            [c_return (string "xs->hd")]
        else
          c_function ~return:"static void"
            (ksprintf string "pick_%s(%s *x, const %s xs)" (sgen_ctyp_name ctyp) (sgen_ctyp ctyp) (sgen_id id))
            [sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "x, xs->hd"]
      in

      let codegen_list_equal =
        let equal_hd = codegen_equal ctyp "op1->hd" "op2->hd" in
        let equal_tl = sail_equal (sgen_id id) "op1->tl, op2->tl" in
        c_function ~return:"static bool"
          (sail_equal (sgen_id id) "const %s op1, const %s op2" (sgen_id id) (sgen_id id))
          [
            string "if (op1 == NULL && op2 == NULL) { return true; };";
            string "if (op1 == NULL || op2 == NULL) { return false; };";
            c_return (separate space [equal_hd; string "&&"; equal_tl]);
          ]
      in

      let codegen_list_undefined =
        ksprintf string "static void UNDEFINED(%s)(%s *rop, %s u) {\n" (sgen_id id) (sgen_id id) (sgen_ctyp ctyp)
        ^^ ksprintf string "  *rop = NULL;\n" ^^ string "}"
      in
      [
        TypeDeclaration codegen_node;
        StaticFunctionDefinition codegen_list_init;
        StaticFunctionDefinition codegen_inc_reference_count;
        StaticFunctionDefinition codegen_dec_reference_count;
        StaticFunctionDefinition codegen_list_clear;
        StaticFunctionDefinition codegen_list_recreate;
        StaticFunctionDefinition codegen_list_copy;
        StaticFunctionDefinition codegen_cons;
        StaticFunctionDefinition codegen_pick;
        StaticFunctionDefinition codegen_list_equal;
        StaticFunctionDefinition codegen_list_undefined;
      ]
    )

  (* Generate functions for working with non-bit vectors of some specific type. *)
  let codegen_vector ctx ctyp =
    let open Printf in
    let id = mk_id (string_of_ctyp (CT_vector ctyp)) in
    if IdSet.mem id !generated then []
    else (
      let vector_typedef =
        ksprintf string "struct %s {\n  size_t len;\n  %s *data;\n};\n" (sgen_id id) (sgen_ctyp ctyp)
        ^^ ksprintf string "typedef struct %s %s;" (sgen_id id) (sgen_id id)
      in
      let vector_decl =
        c_function ~return:"static void"
          (sail_create (sgen_id id) "%s *rop" (sgen_id id))
          [c_stmt "rop->len = 0"; c_stmt "rop->data = NULL"]
      in
      let vector_init =
        c_function ~return:"static void"
          (ksprintf string "vector_init_%s(%s *vec, sail_int n, %s elem)" (sgen_id id) (sgen_id id) (sgen_ctyp ctyp))
          [
            sail_kill ~suffix:";" (sgen_id id) "vec";
            c_stmt "size_t m = (size_t)sail_int_get_ui(n)";
            c_stmt "vec->len = m";
            ksprintf c_stmt "vec->data = sail_new_array(%s, m)" (sgen_ctyp ctyp);
            c_for (string "(size_t i = 0; i < m; i++)")
              ( if is_stack_ctyp ctx ctyp then [c_stmt "(vec->data)[i] = elem"]
                else
                  [
                    sail_create ~suffix:";" (sgen_ctyp_name ctyp) "(vec->data) + i";
                    sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "(vec->data) + i, elem";
                  ]
              );
          ]
      in
      let vector_set =
        c_function ~return:"static void"
          (sail_copy (sgen_id id) "%s *rop, %s op" (sgen_id id) (sgen_id id))
          [
            sail_kill ~suffix:";" (sgen_id id) "rop";
            c_stmt "rop->len = op.len";
            ksprintf c_stmt "rop->data = sail_new_array(%s, rop->len)" (sgen_ctyp ctyp);
            c_for (string "(int i = 0; i < op.len; i++)")
              ( if is_stack_ctyp ctx ctyp then [c_stmt "(rop->data)[i] = op.data[i]"]
                else
                  [
                    sail_create ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + i";
                    sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + i, op.data[i]";
                  ]
              );
          ]
      in
      let vector_clear =
        c_function ~return:"static void"
          (sail_kill (sgen_id id) "%s *rop" (sgen_id id))
          (( if is_stack_ctyp ctx ctyp then []
             else
               [
                 c_for
                   (string "(int i = 0; i < (rop->len); i++)")
                   [sail_kill ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + i"];
               ]
           )
          @ [c_stmt "if (rop->data != NULL) sail_free(rop->data)"]
          )
      in
      let vector_reinit =
        c_function ~return:"static void"
          (sail_recreate (sgen_id id) "%s *rop" (sgen_id id))
          [sail_kill ~suffix:";" (sgen_id id) "rop"; sail_create ~suffix:";" (sgen_id id) "rop"]
      in
      let vector_update =
        c_function ~return:"static void"
          (ksprintf string "vector_update_%s(%s *rop, %s op, sail_int n, %s elem)" (sgen_id id) (sgen_id id)
             (sgen_id id) (sgen_ctyp ctyp)
          )
          [
            c_stmt "int m = sail_int_get_ui(n)";
            c_if_else (string "(rop->data == op.data)")
              [
                ( if is_stack_ctyp ctx ctyp then c_stmt "rop->data[m] = elem"
                  else sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + m, elem"
                );
              ]
              [
                sail_copy ~suffix:";" (sgen_id id) "rop, op";
                ( if is_stack_ctyp ctx ctyp then c_stmt "rop->data[m] = elem"
                  else sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + m, elem"
                );
              ];
          ]
      in
      let internal_vector_update =
        c_function ~return:"static void"
          (ksprintf string "internal_vector_update_%s(%s *rop, %s op, const int64_t n, %s elem)" (sgen_id id)
             (sgen_id id) (sgen_id id) (sgen_ctyp ctyp)
          )
          ( if is_stack_ctyp ctx ctyp then [c_stmt "rop->data[n] = elem"]
            else [sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + n, elem"]
          )
      in
      let vector_access =
        if is_stack_ctyp ctx ctyp then
          c_function
            ~return:("static " ^ sgen_ctyp ctyp)
            (ksprintf string "vector_access_%s(%s op, sail_int n)" (sgen_id id) (sgen_id id))
            [c_stmt "int m = sail_int_get_ui(n)"; c_stmt "return op.data[m]"]
        else
          c_function ~return:"static void"
            (ksprintf string "vector_access_%s(%s *rop, %s op, sail_int n)" (sgen_id id) (sgen_ctyp ctyp) (sgen_id id))
            [c_stmt "int m = sail_int_get_ui(n)"; sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "rop, op.data[m]"]
      in
      let fast_vector_access =
        if is_stack_ctyp ctx ctyp then
          c_function
            ~return:("static " ^ sgen_ctyp ctyp)
            (ksprintf string "fast_vector_access_%s(%s op, int64_t n)" (sgen_id id) (sgen_id id))
            [c_stmt "return op.data[n]"]
        else
          c_function ~return:"static void"
            (ksprintf string "fast_vector_access_%s(%s *rop, %s op, int64_t n)" (sgen_id id) (sgen_ctyp ctyp)
               (sgen_id id)
            )
            [sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "rop, op.data[n]"]
      in
      let internal_vector_init =
        c_function ~return:"static void"
          (ksprintf string "internal_vector_init_%s(%s *rop, const int64_t len)" (sgen_id id) (sgen_id id))
          ([c_stmt "rop->len = len"; ksprintf c_stmt "rop->data = sail_new_array(%s, len)" (sgen_ctyp ctyp)]
          @ c_cond_block
              (not (is_stack_ctyp ctx ctyp))
              [
                c_for (string "(int i = 0; i < len; i++)")
                  [sail_create ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + i"];
              ]
          )
      in
      let vector_undefined =
        c_function ~return:"static void"
          (ksprintf string "undefined_vector_%s(%s *rop, sail_int len, %s elem)" (sgen_id id) (sgen_id id)
             (sgen_ctyp ctyp)
          )
          [
            c_stmt "rop->len = sail_int_get_ui(len)";
            ksprintf c_stmt "rop->data = sail_new_array(%s, rop->len)" (sgen_ctyp ctyp);
            c_for
              (string "(int i = 0; i < (rop->len); i++)")
              ( if is_stack_ctyp ctx ctyp then [c_stmt "(rop->data)[i] = elem"]
                else
                  [
                    sail_create ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + i";
                    sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + i, elem";
                  ]
              );
          ]
      in
      let vector_equal =
        c_function ~return:"static bool"
          (sail_equal (sgen_id id) "const %s op1, const %s op2" (sgen_id id) (sgen_id id))
          [
            c_stmt "if (op1.len != op2.len) return false";
            c_stmt "bool result = true";
            c_for
              (string "(int i = 0; i < op1.len; i++)")
              [c_assign (string "result") "&=" (codegen_equal ctyp "op1.data[i]" "op2.data[i]")];
            c_stmt "return result";
          ]
      in
      let vector_length =
        c_function ~return:"static void"
          (ksprintf string "length_%s(sail_int *rop, %s op)" (sgen_id id) (sgen_id id))
          [c_stmt "mpz_set_ui(*rop, (unsigned long int)(op.len))"]
      in
      begin
        generated := IdSet.add id !generated;
        [
          TypeDeclaration vector_typedef;
          StaticFunctionDefinition vector_decl;
          StaticFunctionDefinition vector_clear;
          StaticFunctionDefinition vector_init;
          StaticFunctionDefinition vector_reinit;
          StaticFunctionDefinition vector_undefined;
          StaticFunctionDefinition vector_access;
          StaticFunctionDefinition fast_vector_access;
          StaticFunctionDefinition vector_set;
          StaticFunctionDefinition vector_update;
          StaticFunctionDefinition vector_equal;
          StaticFunctionDefinition vector_length;
          StaticFunctionDefinition internal_vector_update;
          StaticFunctionDefinition internal_vector_init;
        ]
      end
    )

  let is_decl = function I_aux (I_decl _, _) -> true | _ -> false

  let codegen_decl = function
    | I_aux (I_decl (ctyp, id), _) -> string (Printf.sprintf "%s %s;" (sgen_ctyp ctyp) (sgen_name id))
    | _ -> assert false

  let codegen_alloc ctx = function
    | I_aux (I_decl (ctyp, _), _) when is_stack_ctyp ctx ctyp -> empty
    | I_aux (I_decl (ctyp, id), _) -> sail_create ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
    | _ -> assert false

  (* Generate C code for a global register, constant (let), function definition, etc. *)
  let codegen_def' ctx (CDEF_aux (aux, _)) =
    match aux with
    | CDEF_register (id, ctyp, _) ->
        let definition =
          VariableDefinition
            (string (Printf.sprintf "// register %s" (string_of_name id))
            ^^ hardline
            ^^ string (Printf.sprintf "%s %s%s;" (sgen_ctyp ctyp) (sgen_name id) (variable_zero_init ()))
            )
        in
        if Config.cpp then [definition]
        else
          [
            VariableDeclaration
              (string (Printf.sprintf "// register %s" (string_of_name id))
              ^^ hardline
              ^^ string (Printf.sprintf "extern %s %s;" (sgen_ctyp ctyp) (sgen_name id))
              );
            definition;
          ]
    | CDEF_val (id, _, arg_ctyps, ret_ctyp, _) ->
        if ctx_is_extern id ctx then []
        else if is_stack_ctyp ctx ret_ctyp then
          [
            FunctionDeclaration
              (string
                 (Printf.sprintf "%s %s(%s%s);" (sgen_ctyp ret_ctyp) (sgen_function_id id) (extra_params ())
                    (Util.string_of_list ", " sgen_const_ctyp arg_ctyps)
                 )
              );
          ]
        else
          [
            FunctionDeclaration
              (string
                 (Printf.sprintf "void %s(%s%s *rop, %s);" (sgen_function_id id) (extra_params ()) (sgen_ctyp ret_ctyp)
                    (Util.string_of_list ", " sgen_const_ctyp arg_ctyps)
                 )
              );
          ]
    | CDEF_fundef (id, ret_arg, args, instrs) ->
        (* We can skip the Sail version of a function if we're going to call the
          externally defined version anyway. *)
        if ctx_is_extern id ctx then []
        else begin
          let _, arg_ctyps, ret_ctyp, _ =
            match Bindings.find_opt id ctx.valspecs with
            | Some vs -> vs
            | None -> c_error ~loc:(id_loc id) ("No valspec found for " ^ string_of_id id)
          in

          (* Check that the function has the correct arity at this point. *)
          if List.length arg_ctyps <> List.length args then
            c_error ~loc:(id_loc id)
              ("function arguments "
              ^ Util.string_of_list ", " string_of_name args
              ^ " matched against type "
              ^ Util.string_of_list ", " string_of_ctyp arg_ctyps
              )
          else ();

          let instrs = add_local_labels instrs in
          let args =
            Util.string_of_list ", "
              (fun x -> x)
              (List.map2 (fun ctyp arg -> sgen_const_ctyp ctyp ^ " " ^ sgen_name arg) arg_ctyps args)
          in
          let function_header =
            match ret_arg with
            | Return_plain ->
                assert (is_stack_ctyp ctx ret_ctyp);
                string (sgen_ctyp ret_ctyp)
                ^^ space
                ^^ string (class_impl_prefix ())
                ^^ codegen_function_id id
                ^^ parens (string (extra_params ()) ^^ string args)
                ^^ hardline
            | Return_via gs ->
                assert (not (is_stack_ctyp ctx ret_ctyp));
                string "void" ^^ space
                ^^ string (class_impl_prefix ())
                ^^ codegen_function_id id
                ^^ parens
                     (string (extra_params ())
                     ^^ string (sgen_ctyp ret_ctyp ^ " *" ^ sgen_name gs ^ ", ")
                     ^^ string args
                     )
                ^^ hardline
          in
          [
            FunctionDefinition
              (function_header ^^ string "{"
              ^^ jump 0 2 (separate_map hardline (codegen_instr id ctx) instrs)
              ^^ hardline ^^ string "}"
              );
          ]
        end
    | CDEF_type ctype_def -> codegen_type_def ctx ctype_def
    | CDEF_startup (id, instrs) ->
        let startup_header =
          string (Printf.sprintf "void %sstartup_%s(void)" (class_impl_prefix ()) (sgen_function_id id))
        in
        let startup_impl =
          separate_map hardline codegen_decl instrs
          ^^ twice hardline ^^ startup_header ^^ hardline ^^ string "{"
          ^^ jump 0 2 (separate_map hardline (codegen_alloc ctx) instrs)
          ^^ hardline ^^ string "}"
        in
        let startup_decl = string (Printf.sprintf "void startup_%s(void);" (sgen_function_id id)) in
        if Config.cpp then [FunctionDefinition startup_impl; FunctionDeclaration startup_decl]
        else [FunctionDefinition startup_impl]
    | CDEF_finish (id, instrs) ->
        let finish_header =
          string (Printf.sprintf "void %sfinish_%s(void)" (class_impl_prefix ()) (sgen_function_id id))
        in
        let finish_impl =
          separate_map hardline codegen_decl (List.filter is_decl instrs)
          ^^ twice hardline ^^ finish_header ^^ hardline ^^ string "{"
          ^^ jump 0 2 (separate_map hardline (codegen_instr id ctx) instrs)
          ^^ hardline ^^ string "}"
        in
        let finish_decl = string (Printf.sprintf "void finish_%s(void);" (sgen_function_id id)) in
        if Config.cpp then [FunctionDefinition finish_impl; FunctionDeclaration finish_decl]
        else [FunctionDefinition finish_impl]
    | CDEF_let (number, bindings, instrs) ->
        let instrs = add_local_labels instrs in
        let setup = List.concat (List.map (fun (id, ctyp) -> [idecl (id_loc id) ctyp (name id)]) bindings) in
        let cleanup = List.concat (List.map (fun (id, ctyp) -> [iclear ~loc:(id_loc id) ctyp (name id)]) bindings) in
        let variable_defs =
          separate_map hardline
            (fun (id, ctyp) -> string (Printf.sprintf "%s %s%s;" (sgen_ctyp ctyp) (sgen_id id) (variable_zero_init ())))
            bindings
          ^^ hardline
        in
        let function_decls =
          string (Printf.sprintf "void create_letbind_%d(void);" number)
          ^^ hardline
          ^^ string (Printf.sprintf "void kill_letbind_%d(void);" number)
          ^^ hardline
        in
        let impl =
          string (Printf.sprintf "void %screate_letbind_%d(void) " (class_impl_prefix ()) number)
          ^^ string "{"
          ^^ jump 0 2 (separate_map hardline (codegen_alloc ctx) setup)
          ^^ hardline
          ^^ jump 0 2 (separate_map hardline (codegen_instr (mk_id "let") { ctx with no_raw = true }) instrs)
          ^^ hardline ^^ string "}" ^^ hardline
          ^^ string (Printf.sprintf "void %skill_letbind_%d(void) " (class_impl_prefix ()) number)
          ^^ string "{"
          ^^ jump 0 2 (separate_map hardline (codegen_instr (mk_id "let") ctx) cleanup)
          ^^ hardline ^^ string "}"
        in

        [VariableDefinition variable_defs; FunctionDeclaration function_decls; FunctionDefinition impl]
    | CDEF_pragma _ -> []

  (** As we generate C we need to generate specialized version of tuple, list, and vector type. These must be generated
      in the correct order. The ctyp_dependencies function generates a list of c_gen_typs in the order they must be
      generated. Types may be repeated in ctyp_dependencies so it's up to the code-generator not to repeat definitions
      pointlessly (using the !generated variable) *)
  type c_gen_typ = CTG_tup of ctyp list | CTG_list of ctyp | CTG_vector of ctyp

  let rec ctyp_dependencies = function
    | CT_tup ctyps -> List.concat (List.map ctyp_dependencies ctyps) @ [CTG_tup ctyps]
    | CT_list ctyp -> ctyp_dependencies ctyp @ [CTG_list ctyp]
    | CT_vector ctyp | CT_fvector (_, ctyp) -> ctyp_dependencies ctyp @ [CTG_vector ctyp]
    | CT_ref ctyp -> ctyp_dependencies ctyp
    | CT_struct (_, ctyps) | CT_variant (_, ctyps) -> List.concat (List.map ctyp_dependencies ctyps)
    | CT_lint | CT_fint _ | CT_lbits | CT_fbits _ | CT_sbits _ | CT_unit | CT_bool | CT_real | CT_string | CT_enum _
    | CT_poly _ | CT_constant _ | CT_float _ | CT_rounding_mode | CT_memory_writes | CT_json | CT_json_key ->
        []

  (* Generate types and utility functions for non-bitvector vectors, tuples and lists.
     The functions are pure, and only emitted in the implementation file as static functions. *)
  let codegen_ctg ctx = function
    | CTG_vector ctyp -> codegen_vector ctx ctyp
    | CTG_tup ctyps -> codegen_tup ctx ctyps
    | CTG_list ctyp -> codegen_list ctx ctyp

  (* Take a single list of `Header doc`, `VariableDeclaration doc`, etc. and split them
     into separate lists each with only one type of `doc`. *)
  type file_docs_by_type = {
    type_decl : document;
    func_decl : document;
    func_def : document;
    var_decl : document;
    var_def : document;
    static_func_def : document;
  }

  let merge_file_docs docs =
    List.fold_left
      (fun acc -> function
        | TypeDeclaration doc -> { acc with type_decl = acc.type_decl ^^ doc ^^ twice hardline }
        | FunctionDeclaration doc -> { acc with func_decl = acc.func_decl ^^ doc ^^ twice hardline }
        | FunctionDefinition doc -> { acc with func_def = acc.func_def ^^ doc ^^ twice hardline }
        | VariableDeclaration doc -> { acc with var_decl = acc.var_decl ^^ doc ^^ twice hardline }
        | VariableDefinition doc -> { acc with var_def = acc.var_def ^^ doc ^^ twice hardline }
        | StaticFunctionDefinition doc -> { acc with static_func_def = acc.static_func_def ^^ doc ^^ twice hardline }
        )
      {
        type_decl = empty;
        func_decl = empty;
        func_def = empty;
        var_decl = empty;
        var_def = empty;
        static_func_def = empty;
      }
      docs

  (** When we generate code for a definition, we need to first generate any auxillary type definitions that are
      required. *)
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
      List.concat (List.map (codegen_ctg ctx) deps) @ codegen_def' ctx def
    )

  let is_cdef_startup = function CDEF_aux (CDEF_startup _, _) -> true | _ -> false

  let sgen_startup = function
    | CDEF_aux (CDEF_startup (id, _), _) -> Printf.sprintf "  startup_%s();" (sgen_function_id id)
    | _ -> assert false

  let sgen_instr id ctx instr = Document.to_string (codegen_instr id ctx instr)

  let is_cdef_finish = function CDEF_aux (CDEF_startup _, _) -> true | _ -> false

  let sgen_finish = function
    | CDEF_aux (CDEF_startup (id, _), _) -> Printf.sprintf "  finish_%s();" (sgen_function_id id)
    | _ -> assert false

  let get_recursive_functions cdefs =
    let graph = Jib_compile.callgraph cdefs in
    let rf = IdGraph.self_loops graph in
    (* Use strongly-connected components for mutually recursive functions *)
    List.fold_left (fun rf component -> match component with [_] -> rf | mutual -> mutual @ rf) rf (IdGraph.scc graph)
    |> IdSet.of_list

  let jib_of_ast env effect_info ast =
    let module Jibc = Make (C_config (struct
      let branch_coverage = Config.branch_coverage
      let assert_to_exception = Config.assert_to_exception
      let preserve_types = Config.preserve_types
    end)) in
    let ctx = initial_ctx env effect_info in
    Jibc.compile_ast ctx ast

  let rec c_ast_registers ~early = function
    | CDEF_aux (CDEF_register (id, ctyp, instrs), def_annot) :: ast
      when early = Option.is_some (get_def_attribute "early_init" def_annot) ->
        (id, ctyp, instrs) :: c_ast_registers ~early ast
    | _ :: ast -> c_ast_registers ~early ast
    | [] -> []

  let get_unit_tests cdefs =
    List.fold_left
      (fun ids -> function
        | CDEF_aux (CDEF_val (id, _, _, _, _), def_annot) when Option.is_some (get_def_attribute "test" def_annot) ->
            IdSet.add id ids
        | _ -> ids
        )
      IdSet.empty cdefs
    |> IdSet.elements

  (* Generate the `model_init()` and `model_fini()` functions
     which initialise and clean up the model (allocating/deallocating
     GMP variables, setting initial register values, etc.). *)
  let gen_model_init_fini ctx cdefs =
    let exception_type = sgen_id (mk_id "exception") in

    let exn_boilerplate =
      if not (Bindings.mem (mk_id "exception") ctx.variants) then ([], [])
      else
        ( [
            sprintf "  current_exception = sail_new(struct %s);" exception_type;
            sprintf "  CREATE(%s)(current_exception);" exception_type;
            "  throw_location = sail_new(sail_string);";
            "  CREATE(sail_string)(throw_location);";
          ],
          [
            "  if (have_exception) {fprintf(stderr, \"Exiting due to uncaught exception: %s\\n\", *throw_location);}";
            sprintf "  KILL(%s)(current_exception);" exception_type;
            "  sail_free(current_exception);";
            "  KILL(sail_string)(throw_location);";
            "  sail_free(throw_location);";
            "  if (have_exception) {exit(EXIT_FAILURE);}";
          ]
        )
    in

    let letbind_initializers = List.map (fun n -> Printf.sprintf "  create_letbind_%d();" n) (List.rev ctx.letbinds) in
    let letbind_finalizers = List.map (fun n -> Printf.sprintf "  kill_letbind_%d();" n) ctx.letbinds in

    let set_abstract_types =
      Bindings.bindings ctx.abstracts
      |> List.filter_map (fun (id, (_, initialised)) ->
             match initialised with
             | Initialised -> Some (Printf.sprintf "  sail_set_abstract_%s();" (Ast_util.string_of_id id))
             (* Skip abstract types that haven't been initialised; we can't initialise them automatically. *)
             | Uninitialised -> None
         )
    in

    let startup cdefs = List.map sgen_startup (List.filter is_cdef_startup cdefs) in
    let finish cdefs = List.map sgen_finish (List.filter is_cdef_finish cdefs) in

    let early_regs = c_ast_registers ~early:true cdefs in
    let regs = c_ast_registers ~early:false cdefs in

    let register_init_clear (id, ctyp, instrs) =
      if is_stack_ctyp ctx ctyp then (List.map (sgen_instr (mk_id "reg") ctx) instrs, [])
      else
        ( [Printf.sprintf "  CREATE(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_name id)]
          @ List.map (sgen_instr (mk_id "reg") ctx) instrs,
          [Printf.sprintf "  KILL(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_name id)]
        )
    in

    let init_config_id = mk_id "__InitConfig" in

    let model_init =
      separate hardline
        (List.map string
           ([Printf.sprintf "void %smodel_init(void)" (class_impl_prefix ()); "{"; "  setup_rts();"]
           @ fst exn_boilerplate
           @ List.concat (List.map (fun r -> fst (register_init_clear r)) early_regs)
           @ set_abstract_types @ startup cdefs @ letbind_initializers
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
           ([Printf.sprintf "void %smodel_fini(void)" (class_impl_prefix ()); "{"]
           @ List.concat (List.map (fun r -> snd (register_init_clear r)) regs)
           @ letbind_finalizers
           @ List.concat (List.map (fun r -> snd (register_init_clear r)) early_regs)
           @ finish cdefs @ ["  cleanup_rts();"] @ snd exn_boilerplate @ ["}"]
           )
        )
    in

    [FunctionDefinition model_init; FunctionDefinition model_fini]

  (* For C++ generate a constructor and destructor to allocate and free abstract
     types that aren't handled in model_init() and model_fini(). These
     cannot be initialised in model_init() because they must be set by
     sail_set_abstract_...() before model_init() runs. They aren't necessary
     in C because in C they are globals so they get automatically zero-initialised
     and Valgrind doesn't care about globals leaking. *)
  let gen_constructor_destructor ctx cdefs =
    let names_and_types =
      Bindings.bindings ctx.abstracts
      |> List.map (fun (id, (ctyp, _)) -> (NameGen.to_string ~prefix:"abstract_" () id, ctyp))
    in

    let create_abstract (name, ctyp) =
      if is_stack_ctyp ctx ctyp then empty else sail_create ~suffix:";" (sgen_ctyp_name ctyp) "&%s" name
    in

    let kill_abstract (name, ctyp) =
      if is_stack_ctyp ctx ctyp then empty else sail_kill ~suffix:";" (sgen_ctyp_name ctyp) "&%s" name
    in

    let constructor_decl = ksprintf string "%s();" Config.cpp_class_name in
    let constructor_def =
      ksprintf string "%s::%s() {" Config.cpp_class_name Config.cpp_class_name
      ^^ jump 2 1 (separate_map hardline create_abstract names_and_types)
      ^^ string "}"
    in
    let destructor_decl = ksprintf string "~%s();" Config.cpp_class_name in
    let destructor_def =
      ksprintf string "%s::~%s() {" Config.cpp_class_name Config.cpp_class_name
      ^^ jump 2 1 (separate_map hardline kill_abstract names_and_types)
      ^^ string "}"
    in

    let copy_constructor_decl = ksprintf string "%s(const %s&) = delete;" Config.cpp_class_name Config.cpp_class_name in
    [
      FunctionDeclaration constructor_decl;
      FunctionDefinition constructor_def;
      FunctionDeclaration destructor_decl;
      FunctionDefinition destructor_def;
      FunctionDeclaration copy_constructor_decl;
    ]

  (* Generate a constant array that points to all the unit test functions. *)
  let gen_unit_test_defs ctx cdefs =
    let unit_tests = get_unit_tests cdefs in

    (* `static constexpr` is another option but it doesn't work for function pointers until C++20. *)
    let inline = if Config.cpp then "inline " else "" in

    [
      VariableDefinition
        ((* Number of unit tests. *)
         [sprintf "%sstatic const size_t SAIL_TEST_COUNT = %d;" inline (List.length unit_tests)]
         (* Pointers to unit test functions, with NULL entry for convenience. *)
         @ [
             sprintf "%sstatic unit (%s*const SAIL_TESTS[%d])(unit) = {" inline (class_impl_prefix ())
               (List.length unit_tests + 1);
           ]
         @ List.map (fun id -> sprintf "  &%s%s," (class_impl_prefix ()) (sgen_function_id id)) unit_tests
         @ ["  NULL"; "};"]
         (* Unit test names, with NULL entry for convenience. *)
         @ [sprintf "%sstatic const char* const SAIL_TEST_NAMES[%d] = {" inline (List.length unit_tests + 1)]
         @ List.map (fun id -> sprintf "  \"%s\"," (String.escaped (string_of_id id))) unit_tests
         @ ["  NULL"; "};"]
        |> List.map string |> separate hardline
        );
    ]

  let compile_ast env effect_info basename ast =
    try
      let cdefs, ctx = jib_of_ast env effect_info ast in
      (* let cdefs', _ = Jib_optimize.remove_tuples cdefs ctx in *)
      let cdefs = insert_heap_returns ctx Bindings.empty cdefs in

      let recursive_functions = get_recursive_functions cdefs in
      let cdefs = optimize ~have_rts:(not Config.no_rts) ctx recursive_functions cdefs in

      (* clang has a default limit of 256 nested braces, so we make
         sure we don't generated definitions with deep nesting by
         flattening all definitions with a nesting depth greater than
         some value < 256 (100 seems reasonable). *)
      let cdefs = List.map (Jib_optimize.flatten_cdef ~max_depth:100) cdefs in

      let docs = List.map (codegen_def ctx) cdefs |> List.concat in

      let docs = docs @ gen_model_init_fini ctx cdefs @ gen_unit_test_defs ctx cdefs in
      let docs = if Config.cpp then docs @ gen_constructor_destructor ctx cdefs else docs in

      let docs_by_type = docs |> merge_file_docs in

      let extern_cpp_begin =
        if Config.cpp then [] else [string "#ifdef __cplusplus"; string "extern \"C\" {"; string "#endif"]
      in
      let extern_cpp_end =
        if Config.cpp then [] else [string ""; string "#ifdef __cplusplus"; string "}"; string "#endif"]
      in

      let coverage_include, coverage_hook_header, coverage_hook =
        let header = string "#include \"sail_coverage.h\"" in
        (* Generate a hook for the RTS to call if we have coverage
           enabled, so it can set the output file with an option. *)
        let coverage_hook_header = string "extern void (*sail_rts_set_coverage_file)(const char *);" in
        let coverage_hook = string "void (*sail_rts_set_coverage_file)(const char *) = &sail_set_coverage_file;" in
        let no_coverage_hook = string "void (*sail_rts_set_coverage_file)(const char *) = NULL;" in
        match Config.branch_coverage with
        | Some _ -> if Config.no_rts then ([header], [], []) else ([header], [coverage_hook_header], [coverage_hook])
        | None -> if Config.no_rts then ([], [], []) else ([], [coverage_hook_header], [no_coverage_hook])
      in

      let preamble in_header =
        separate hardline
          ((if Config.no_lib then [] else [string "#include \"sail.h\""; string "#include \"sail_config.h\""])
          @ (if Config.no_rts then [] else [string "#include \"rts.h\""; string "#include \"elf.h\""])
          @ coverage_include
          @ List.map
              (fun h -> string (Printf.sprintf "#include \"%s\"" h))
              (if in_header then Config.header_includes else Config.includes)
          @ extern_cpp_begin
          @ if in_header then coverage_hook_header else coverage_hook
          )
      in

      (* model_pre_exit() has to be `extern "C"` because it is called from rts.c. *)
      let extern_c = if Config.cpp then "extern \"C\" " else "" in

      let model_pre_exit =
        ([sprintf "%svoid model_pre_exit()" extern_c; "{"]
        @
        if Option.is_some Config.branch_coverage then
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

      let model_main =
        ( if Config.cpp then
            [
              "int model_main(int argc, char *argv[])";
              "{";
              Printf.sprintf "  %s::%s model;" Config.cpp_namespace Config.cpp_class_name;
              "  model.model_init();";
              "  if (process_arguments(argc, argv)) exit(EXIT_FAILURE);";
              Printf.sprintf "  model.%s(UNIT);" (sgen_function_id (mk_id "main"));
              "  model.model_fini();";
              "  model_pre_exit();";
              "  return EXIT_SUCCESS;";
              "}";
            ]
          else
            [
              "int model_main(int argc, char *argv[])";
              "{";
              "  model_init();";
              "  if (process_arguments(argc, argv)) exit(EXIT_FAILURE);";
              Printf.sprintf "  %s(UNIT);" (sgen_function_id (mk_id "main"));
              "  model_fini();";
              "  model_pre_exit();";
              "  return EXIT_SUCCESS;";
              "}";
            ]
        )
        |> List.map string |> separate hardline
      in

      (* A simple function to run the unit tests. It isn't called from anywhere
         by default and you don't need to use it - you can use SAIL_TESTS directly
         in your own custom test runner. *)
      let model_test =
        ( if Config.cpp then
            [
              "void model_test(void)";
              "{";
              sprintf "  %s::%s model;" Config.cpp_namespace Config.cpp_class_name;
              sprintf "  for (size_t i = 0; i < %s::%s::SAIL_TEST_COUNT; ++i) {" Config.cpp_namespace
                Config.cpp_class_name;
              "    model.model_init();";
              sprintf "    printf(\"Testing %%s\\n\", %s::%s::SAIL_TEST_NAMES[i]);" Config.cpp_namespace
                Config.cpp_class_name;
              sprintf "    (model.*%s::%s::SAIL_TESTS[i])(UNIT);" Config.cpp_namespace Config.cpp_class_name;
              "    printf(\"Pass\\n\");";
              "    model.model_fini();";
              "  }";
              "}";
            ]
          else
            [
              "void model_test(void)";
              "{";
              "  for (size_t i = 0; i < SAIL_TEST_COUNT; ++i) {";
              "    model_init();";
              "    printf(\"Testing %s\\n\", SAIL_TEST_NAMES[i]);";
              "    SAIL_TESTS[i](UNIT);";
              "    printf(\"Pass\\n\");";
              "    model_fini();";
              "  }";
              "}";
            ]
        )
        |> List.map string |> separate hardline
      in

      let actual_main =
        let extra_pre =
          List.filter_map
            (function CDEF_aux (CDEF_pragma ("c_in_main", arg), _) -> Some ("  " ^ arg) | _ -> None)
            cdefs
        in
        let extra_post =
          List.filter_map
            (function CDEF_aux (CDEF_pragma ("c_in_main_post", arg), _) -> Some ("  " ^ arg) | _ -> None)
            cdefs
        in
        separate hardline
          ( if Config.no_main then []
            else
              List.map string
                (["int main(int argc, char *argv[])"; "{"; "  int retcode;"]
                @ extra_pre @ ["  retcode = model_main(argc, argv);"] @ extra_post @ ["  return retcode;"; "}"]
                )
          )
      in

      let hlhl = twice hardline in

      (* If compiling in C++ mode wrap the header in a struct { }. *)
      let header_doc =
        if Config.cpp then (
          let derive_from = match Config.cpp_derive_from with Some s -> " : " ^ s | None -> "" in
          ksprintf string "namespace %s {" Config.cpp_namespace
          ^^ hardline ^^ docs_by_type.type_decl
          ^^ ksprintf string "class %s%s {" Config.cpp_class_name derive_from
          ^^ hardline ^^ string "public:" ^^ hardline
          (* All of the types, functions and register declarations. *)
          ^^ jump 2 1
               (docs_by_type.func_decl ^^ docs_by_type.var_def ^^ string "void model_init();" ^^ hardline
              ^^ string "void model_fini();" ^^ hardline
               )
          (* End of struct *)
          ^^ string "};"
          ^^ hardline ^^ string "} // namespace" ^^ hardline
        )
        else docs_by_type.type_decl ^^ docs_by_type.func_decl ^^ docs_by_type.var_decl
      in

      let header =
        string "#pragma once" ^^ hlhl ^^ preamble true ^^ hlhl ^^ header_doc ^^ hardline
        ^^ separate hardline extern_cpp_end ^^ hardline
        |> Document.to_string
      in

      let impl_doc =
        if Config.cpp then
          ksprintf string "namespace %s {" Config.cpp_namespace
          ^^ hlhl ^^ docs_by_type.static_func_def ^^ docs_by_type.func_def
          ^^ ksprintf string "} // namespace %s" Config.cpp_namespace
          ^^ hardline
        else docs_by_type.static_func_def ^^ docs_by_type.var_def ^^ docs_by_type.func_def
      in

      let impl =
        Document.to_string
          (preamble false ^^ hardline
          ^^ Printf.ksprintf string "#include \"%s.h\"" basename
          ^^ hlhl ^^ impl_doc ^^ hlhl
          (* TODO: Does no_rts actually work? Won't actual_main try to call model_main which is missing? *)
          ^^ (if not Config.no_rts then model_pre_exit ^^ hlhl ^^ model_main ^^ hlhl else empty)
          ^^ model_test ^^ hlhl ^^ actual_main ^^ hardline ^^ separate hardline extern_cpp_end ^^ hardline
          )
      in

      (header, impl)
    with Type_error.Type_error (l, err) ->
      c_error ~loc:l ("Unexpected type error when compiling to C:\n" ^ fst (Type_error.string_of_type_error err))
end
