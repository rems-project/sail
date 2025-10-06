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

open Ast
open Ast_defs
open Ast_util
open Parse_ast.Attribute_data
open Jib
open Jib_util
open Jib_visitor
open Type_check
open Value2
module Document = Pretty_print_sail.Document

open Anf

let opt_memo_cache = ref false

let optimize_aarch64_fast_struct = ref false

let ngensym = symbol_generator ()

type funwire = Arg of int | Ret | Invoke

(**************************************************************************)
(* 4. Conversion to low-level AST                                         *)
(**************************************************************************)

(** We now use a low-level AST called Jib (see language/bytecode.ott) that is only slightly abstracted away from C. To
    be succint in comments we usually refer to this as Sail IR or IR rather than low-level AST repeatedly.

    The general idea is ANF expressions are converted into lists of instructions (type instr) where allocations and
    deallocations are now made explicit. ANF values (aval) are mapped to the cval type, which is even simpler still.
    Some things are still more abstract than in C, so the type definitions follow the sail type definition structure,
    just with typ (from ast.ml) replaced with ctyp. Top-level declarations that have no meaning for the backend are not
    included at this level.

    The convention used here is that functions of the form compile_X compile the type X into types in this AST, so
    compile_aval maps avals into cvals. Note that the return types for these functions are often quite complex, and they
    usually return some tuple containing setup instructions (to allocate memory for the expression), cleanup
    instructions (to deallocate that memory) and possibly typing information about what has been translated. **)

(* FIXME: This stage shouldn't care about this *)
let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))

let is_ct_enum = function CT_enum _ -> true | _ -> false

let iblock1 = function [instr] -> instr | instrs -> iblock instrs

type abstract_type_initialised = Initialised | Uninitialised

(** The context type contains two type-checking environments. ctx.local_env contains the closest typechecking
    environment, usually from the expression we are compiling, whereas ctx.tc_env is the global type checking
    environment from type-checking the entire AST. We also keep track of local variables in ctx.locals, so we know when
    their type changes due to flow typing. *)
type ctx = {
  target_name : string;
  records : (kid list * ctyp Bindings.t) Bindings.t;
  enums : IdSet.t Bindings.t;
  variants : (kid list * ctyp Bindings.t) Bindings.t;
  abstracts : (ctyp * abstract_type_initialised) Bindings.t;
  valspecs : (string option * ctyp list * ctyp * uannot) Bindings.t;
  quants : ctyp KBindings.t;
  local_env : Env.t;
  tc_env : Env.t;
  effect_info : Effects.side_effect_info;
  locals : (mut * ctyp) NameMap.t;
  registers : ctyp Bindings.t;
  letbinds : int list;
  letbind_ctyps : ctyp Bindings.t;
  no_raw : bool;
  no_static : bool;
  coverage_override : bool;
  def_annot : unit def_annot option;
}

let letbind_ids ctx =
  List.fold_left (fun ids (id, _) -> NameSet.add (name id) ids) NameSet.empty (Bindings.bindings ctx.letbind_ctyps)

let ctx_map_ctyps f ctx =
  {
    ctx with
    records = Bindings.map (fun (params, fields) -> (params, Bindings.map f fields)) ctx.records;
    variants = Bindings.map (fun (params, fields) -> (params, Bindings.map f fields)) ctx.variants;
    abstracts = Bindings.map (fun (ctyp, initialised) -> (f ctyp, initialised)) ctx.abstracts;
    valspecs =
      Bindings.map
        (fun (extern, param_ctyps, ret_ctyp, uannot) -> (extern, List.map f param_ctyps, f ret_ctyp, uannot))
        ctx.valspecs;
  }

let ctx_is_extern id ctx =
  match Bindings.find_opt id ctx.valspecs with
  | Some (Some _, _, _, _) -> true
  | Some (None, _, _, _) -> false
  | None -> Env.is_extern id ctx.tc_env ctx.target_name

let ctx_get_extern id ctx =
  match Bindings.find_opt id ctx.valspecs with
  | Some (Some extern, _, _, _) -> extern
  | Some (None, _, _, _) ->
      Reporting.unreachable (id_loc id) __POS__
        ("Tried to get extern information for non-extern function " ^ string_of_id id)
  | None -> Env.get_extern id ctx.tc_env ctx.target_name

let ctx_has_val_spec id ctx = Bindings.mem id ctx.valspecs || Bindings.mem id (Env.get_val_specs ctx.tc_env)

let initial_ctx ?for_target env effect_info =
  let initial_valspecs =
    [
      (mk_id "size_itself_int", (Some "size_itself_int", [CT_lint], CT_lint, empty_uannot));
      (mk_id "make_the_value", (Some "make_the_value", [CT_lint], CT_lint, empty_uannot));
    ]
    |> List.to_seq |> Bindings.of_seq
  in
  let target_name =
    match for_target with
    | Some name -> name
    | None -> Option.map Target.name (Target.get_the_target ()) |> Option.value ~default:"c"
  in
  {
    target_name;
    records = Bindings.empty;
    enums = Bindings.empty;
    variants = Bindings.empty;
    abstracts = Bindings.empty;
    valspecs = initial_valspecs;
    quants = KBindings.empty;
    local_env = env;
    tc_env = env;
    effect_info;
    locals = NameMap.empty;
    registers = Bindings.empty;
    letbinds = [];
    letbind_ctyps = Bindings.empty;
    no_raw = false;
    no_static = false;
    coverage_override = true;
    def_annot = None;
  }

let instantiate_polymorphic_type ~at:l typ_id ctyps type_info =
  match Bindings.find_opt typ_id type_info with
  | None -> Reporting.unreachable l __POS__ ("Attempted to instantiate unknown type " ^ string_of_id typ_id)
  | Some (params, constructors) ->
      if List.compare_lengths ctyps params <> 0 then
        Reporting.unreachable l __POS__ ("Incorrect number of arguments for type " ^ string_of_id typ_id);
      let substs =
        List.fold_left2 (fun substs param ctyp -> KBindings.add param ctyp substs) KBindings.empty params ctyps
      in
      Bindings.map (subst_poly substs) constructors

let struct_field_bindings l ctx ctyp =
  match ctyp with
  | CT_struct (struct_id, args) ->
      let field_ctyps = instantiate_polymorphic_type ~at:l struct_id args ctx.records in
      (struct_id, field_ctyps)
  | _ -> Reporting.unreachable l __POS__ ("Expected struct ctyp, got " ^ string_of_ctyp ctyp)

let struct_fields l ctx ctyp =
  let struct_id, field_ctyps = struct_field_bindings l ctx ctyp in
  ( struct_id,
    fun id ->
      match Bindings.find_opt id field_ctyps with
      | Some ctyp -> ctyp
      | None ->
          Reporting.unreachable l __POS__ ("Failed to find field " ^ string_of_id id ^ " in " ^ string_of_ctyp ctyp)
  )

let variant_constructor_bindings l ctx ctyp =
  match ctyp with
  | CT_variant (var_id, args) ->
      let ctor_ctyps = instantiate_polymorphic_type ~at:l var_id args ctx.variants in
      (var_id, ctor_ctyps)
  | _ -> Reporting.unreachable l __POS__ ("Expected variant ctyp, got " ^ string_of_ctyp ctyp)

let enum_members l ctx id =
  match Bindings.find_opt id ctx.enums with
  | Some elems -> elems
  | None -> Reporting.unreachable l __POS__ ("Failed to find enum type " ^ string_of_id id)

let transparent_newtype ctx = function
  | CT_variant (id, args) when Env.is_newtype id ctx.tc_env ->
      instantiate_polymorphic_type ~at:(id_loc id) id args ctx.variants |> Bindings.choose |> snd
  | ctyp -> ctyp

let update_coverage_override' ctx = function
  | Some (_, Some (AD_aux (AD_string "on", _))) -> { ctx with coverage_override = true }
  | Some (_, Some (AD_aux (AD_string "off", _))) -> { ctx with coverage_override = false }
  | _ -> ctx

let update_coverage_override uannot ctx = update_coverage_override' ctx (get_attribute "coverage" uannot)

let update_coverage_override_def def_annot ctx = update_coverage_override' ctx (get_def_attribute "coverage" def_annot)

let rec mangle_string_of_ctyp ctx = function
  | CT_lint -> "i"
  | CT_fint n -> "I" ^ string_of_int n
  | CT_lbits -> "b"
  | CT_sbits n -> "S" ^ string_of_int n
  | CT_fbits n -> "B" ^ string_of_int n
  | CT_constant n -> "C" ^ Big_int.to_string n
  | CT_unit -> "u"
  | CT_bool -> "o"
  | CT_real -> "r"
  | CT_string -> "s"
  | CT_float n -> "f" ^ string_of_int n
  | CT_rounding_mode -> "m"
  | CT_json -> "j"
  | CT_json_key -> "k"
  | CT_enum id -> "E" ^ string_of_id id ^ "%"
  | CT_ref ctyp -> "&" ^ mangle_string_of_ctyp ctx ctyp
  | CT_memory_writes -> "w"
  | CT_tup ctyps -> "(" ^ Util.string_of_list "," (mangle_string_of_ctyp ctx) ctyps ^ ")"
  | CT_struct (id, ctyps) -> (
      match ctyps with
      | [] -> "R" ^ string_of_id id
      | _ -> "R" ^ string_of_id id ^ "<" ^ Util.string_of_list "," (mangle_string_of_ctyp ctx) ctyps ^ ">"
    )
  | CT_variant (id, ctyps) -> (
      let id_str = string_of_id id in
      let prefix = if id_str = "option" then "O" else "U" ^ id_str in
      match ctyps with
      | [] -> prefix
      | _ -> prefix ^ "<" ^ Util.string_of_list "," (mangle_string_of_ctyp ctx) ctyps ^ ">"
    )
  | CT_vector ctyp -> "V" ^ mangle_string_of_ctyp ctx ctyp
  | CT_fvector (n, ctyp) -> "F" ^ string_of_int n ^ mangle_string_of_ctyp ctx ctyp
  | CT_list ctyp -> "L" ^ mangle_string_of_ctyp ctx ctyp
  | CT_poly kid -> "P" ^ string_of_kid kid

module type CONFIG = sig
  val convert_typ : ctx -> typ -> ctyp
  val optimize_anf : ctx -> typ aexp -> typ aexp
  val unroll_loops : int option
  val make_call_precise : ctx -> id -> ctyp list -> ctyp -> bool
  val ignore_64 : bool
  val struct_value : bool
  val tuple_value : bool
  val use_real : bool
  val branch_coverage : out_channel option
  val track_throw : bool
  val assert_to_exception : bool
  val use_void : bool
  val eager_control_flow : bool
  val preserve_types : IdSet.t
  val fun_to_wires : int Bindings.t
end

module IdGraph = Graph.Make (Id)
module IdGraphNS = Set.Make (Id)

let callgraph cdefs =
  List.fold_left
    (fun graph cdef ->
      match cdef with
      | CDEF_aux (CDEF_fundef (id, _, _, body), _) ->
          let graph = ref graph in
          List.iter
            (iter_instr (function
              | I_aux (I_funcall (_, _, (call, _), _), _) -> graph := IdGraph.add_edge id call !graph
              | _ -> ()
              ))
            body;
          !graph
      | _ -> graph
    )
    IdGraph.empty cdefs

module Make (C : CONFIG) = struct
  let ctyp_of_typ ctx typ = C.convert_typ ctx typ

  let rec chunkify n xs = match (Util.take n xs, Util.drop n xs) with xs, [] -> [xs] | xs, ys -> xs :: chunkify n ys

  (* Counters to provide unique IDs for branches, branch targets and functions. *)
  let coverage_branch_count = ref 0
  let coverage_branch_target_count = ref 0
  let coverage_function_count = ref 0

  let coverage_loc_args l =
    match Reporting.simp_loc l with
    (* Scattered definitions may not have a known location but we still want
       to measure coverage of them. *)
    | None -> "\"\", 0, 0, 0, 0"
    | Some (p1, p2) ->
        Printf.sprintf "\"%s\", %d, %d, %d, %d" (String.escaped p1.pos_fname) p1.pos_lnum (p1.pos_cnum - p1.pos_bol)
          p2.pos_lnum (p2.pos_cnum - p2.pos_bol)

  (* A branch is a `match` (including `mapping`), `if` or short-circuiting and/or.
     This returns a new ID for the branch, and the C code to call. It also
     writes the static branch info to C.branch_coverage. *)
  let coverage_branch_reached ctx l =
    match C.branch_coverage with
    | Some out when ctx.coverage_override -> begin
        let branch_id = !coverage_branch_count in
        incr coverage_branch_count;
        let args = coverage_loc_args l in
        Printf.fprintf out "%s\n" ("B " ^ string_of_int branch_id ^ ", " ^ args);
        (branch_id, [iraw (Printf.sprintf "sail_branch_reached(%d, %s);" branch_id args)])
      end
    | _ -> (0, [])

  let append_into_block instrs instr = match instrs with [] -> instr | _ -> iblock (instrs @ [instr])

  let rec find_aexp_loc (AE_aux (e, { loc = l; _ })) =
    match Reporting.simp_loc l with
    | Some _ -> l
    | None -> (
        match e with AE_typ (e', _) -> find_aexp_loc e' | _ -> l
      )

  (* This is called when an *arm* of a branch is taken. For example if you
     have a `match`, it is called for the match arm that is taken.
     For `if` without `else` then it may not be called at all. Same for
     short-circuiting boolean expressions. `branch_id` is the ID for the entire
     conditional expression (the whole `match` etc.). *)
  let coverage_branch_target_taken ctx branch_id aexp =
    match C.branch_coverage with
    | Some out when ctx.coverage_override -> begin
        let branch_target_id = !coverage_branch_target_count in
        incr coverage_branch_target_count;
        let args = coverage_loc_args (find_aexp_loc aexp) in
        Printf.fprintf out "%s\n" ("T " ^ string_of_int branch_id ^ ", " ^ string_of_int branch_target_id ^ ", " ^ args);
        [iraw (Printf.sprintf "sail_branch_target_taken(%d, %d, %s);" branch_id branch_target_id args)]
      end
    | _ -> []

  (* Generate code and static branch info for function entry coverage.
     `id` is the name of the function. *)
  let coverage_function_entry ctx id l =
    match C.branch_coverage with
    | Some out when ctx.coverage_override -> begin
        let function_id = !coverage_function_count in
        incr coverage_function_count;
        let args = coverage_loc_args l in
        Printf.fprintf out "%s\n" ("F " ^ string_of_int function_id ^ ", \"" ^ string_of_id id ^ "\", " ^ args);
        [iraw (Printf.sprintf "sail_function_entry(%d, \"%s\", %s);" function_id (string_of_id id) args)]
      end
    | _ -> []

  let unit_cval = V_lit (VL_unit, CT_unit)

  let assert_exception l msg =
    let exception_ctyp = CT_variant (mk_id "exception", []) in
    let e = ngensym () in
    ( [idecl l exception_ctyp e; ifuncall l (CL_id (e, exception_ctyp)) (mk_id "__assertion_failed#", []) [msg]],
      V_id (e, exception_ctyp)
    )

  let get_variable_ctyp id ctx =
    match NameMap.find_opt id ctx.locals with
    | Some binding -> Some binding
    | None -> (
        match id with
        | Name (id, _) -> (
            match Bindings.find_opt id ctx.registers with
            | Some ctyp -> Some (Mutable, ctyp)
            | None -> (
                match Bindings.find_opt id ctx.letbind_ctyps with Some ctyp -> Some (Immutable, ctyp) | None -> None
              )
          )
        | _ -> None
      )

  let rec compile_aval l ctx = function
    | AV_cval (cval, typ) ->
        let ctyp = cval_ctyp cval in
        let ctyp' = ctyp_of_typ ctx typ in
        if not (ctyp_equal ctyp ctyp') then (
          let gs = ngensym () in
          ([iinit l ctyp' gs cval], V_id (gs, ctyp'), [iclear ctyp' gs])
        )
        else ([], cval, [])
    | AV_id (Name (id, _), Enum typ) -> ([], V_member (id, ctyp_of_typ ctx typ), [])
    | AV_id (id, typ) -> begin
        match get_variable_ctyp id ctx with
        | Some (_, ctyp) -> ([], V_id (id, ctyp), [])
        | None -> ([], V_id (id, ctyp_of_typ ctx (lvar_typ typ)), [])
      end
    | AV_abstract (id, typ) -> (
        match Bindings.find_opt id ctx.abstracts with
        | Some (ctyp, _) -> ([], V_id (Abstract id, ctyp), [])
        | None ->
            Reporting.unreachable l __POS__ ("Failed to find a C-type for abstract type variable " ^ string_of_id id)
      )
    | AV_ref (id, typ) -> ([], V_lit (VL_ref (string_of_id id), CT_ref (ctyp_of_typ ctx (lvar_typ typ))), [])
    | AV_lit (L_aux (L_string str, _), typ) -> ([], V_lit (VL_string (String.escaped str), ctyp_of_typ ctx typ), [])
    | AV_lit (L_aux (L_num n, _), typ) when C.ignore_64 -> ([], V_lit (VL_int n, ctyp_of_typ ctx typ), [])
    | AV_lit (L_aux (L_num n, _), typ) when Big_int.less_equal (min_int 64) n && Big_int.less_equal n (max_int 64) ->
        let gs = ngensym () in
        ([iinit l CT_lint gs (V_lit (VL_int n, CT_fint 64))], V_id (gs, CT_lint), [iclear CT_lint gs])
    | AV_lit (L_aux (L_num n, _), typ) ->
        let gs = ngensym () in
        ( [iinit l CT_lint gs (V_lit (VL_string (Big_int.to_string n), CT_string))],
          V_id (gs, CT_lint),
          [iclear CT_lint gs]
        )
    | AV_lit (L_aux (((L_hex _ | L_bin _) as l_aux), _), _) ->
        let bitlist =
          ( match l_aux with
          | L_hex hex -> Semantics.bitlist_of_hex_lit hex
          | L_bin bin -> Semantics.bitlist_of_bin_lit bin
          | _ -> assert false
          )
          |> List.map (function Value_type.B0 -> Sail2_values.B0 | Value_type.B1 -> Sail2_values.B1)
        in
        let len = List.length bitlist in
        (* For small bitvectors, or when we permit arbitrary-length literals > 64 we can emit a literal directly,
           otherwise we use the special append_64 builtin to construct a literal from 64-bit chunks. *)
        if len <= 64 || C.ignore_64 then ([], V_lit (VL_bits bitlist, CT_fbits len), [])
        else (
          let bv_literal len bits = V_lit (VL_bits bits, CT_fbits len) in
          let first_chunk = Util.take (len mod 64) bitlist |> bv_literal (len mod 64) in
          let chunks = Util.drop (len mod 64) bitlist |> chunkify 64 |> List.map (bv_literal 64) in
          let gs = ngensym () in
          ( [iinit l CT_lbits gs first_chunk]
            @ List.map
                (fun chunk -> ifuncall l (CL_id (gs, CT_lbits)) (mk_id "append_64", []) [V_id (gs, CT_lbits); chunk])
                chunks,
            V_id (gs, CT_lbits),
            [iclear CT_lbits gs]
          )
        )
    | AV_lit (L_aux (L_true, _), _) -> ([], V_lit (VL_bool true, CT_bool), [])
    | AV_lit (L_aux (L_false, _), _) -> ([], V_lit (VL_bool false, CT_bool), [])
    | AV_lit (L_aux (L_real str, _), _) ->
        if C.use_real then ([], V_lit (VL_real str, CT_real), [])
        else (
          let gs = ngensym () in
          ([iinit l CT_real gs (V_lit (VL_string str, CT_string))], V_id (gs, CT_real), [iclear CT_real gs])
        )
    | AV_lit (L_aux (L_unit, _), _) -> ([], V_lit (VL_unit, CT_unit), [])
    | AV_lit (L_aux (L_undef, _), typ) ->
        let ctyp = ctyp_of_typ ctx typ in
        ([], V_lit (VL_undefined, ctyp), [])
    | AV_tuple avals ->
        let elements = List.map (compile_aval l ctx) avals in
        let cvals = List.map (fun (_, cval, _) -> cval) elements in
        let setup = List.concat (List.map (fun (setup, _, _) -> setup) elements) in
        let cleanup = List.concat (List.rev (List.map (fun (_, _, cleanup) -> cleanup) elements)) in
        let tup_ctyp = CT_tup (List.map cval_ctyp cvals) in
        let gs = ngensym () in
        if C.tuple_value then (setup, V_tuple cvals, cleanup)
        else
          ( setup
            @ [idecl l tup_ctyp gs]
            @ List.mapi (fun n cval -> icopy l (CL_tuple (CL_id (gs, tup_ctyp), n)) cval) cvals,
            V_id (gs, CT_tup (List.map cval_ctyp cvals)),
            [iclear tup_ctyp gs] @ cleanup
          )
    | AV_record (fields, typ) when C.struct_value ->
        let ctyp = ctyp_of_typ ctx typ in
        let compile_fields (id, aval) =
          let field_setup, cval, field_cleanup = compile_aval l ctx aval in
          (field_setup, (id, cval), field_cleanup)
        in
        let field_triples = List.map compile_fields (Bindings.bindings fields) in
        let setup = List.concat (List.map (fun (s, _, _) -> s) field_triples) in
        let fields = List.map (fun (_, f, _) -> f) field_triples in
        let cleanup = List.concat (List.map (fun (_, _, c) -> c) field_triples) in
        (setup, V_struct (fields, ctyp), cleanup)
    | AV_record (fields, typ) ->
        let ctyp = ctyp_of_typ ctx typ in
        let _, field_ctyp = struct_fields l ctx ctyp in
        let gs = ngensym () in
        let compile_fields (id, aval) =
          let field_setup, cval, field_cleanup = compile_aval l ctx aval in
          field_setup @ [icopy l (CL_field (CL_id (gs, ctyp), id, field_ctyp id)) cval] @ field_cleanup
        in
        ( [idecl l ctyp gs] @ List.concat (List.map compile_fields (Bindings.bindings fields)),
          V_id (gs, ctyp),
          [iclear ctyp gs]
        )
    | AV_vector ([], typ) ->
        let vector_ctyp = ctyp_of_typ ctx typ in
        begin
          match ctyp_of_typ ctx typ with
          | CT_fbits 0 -> ([], V_lit (VL_bits [], vector_ctyp), [])
          | _ ->
              let gs = ngensym () in
              ( [
                  idecl l vector_ctyp gs;
                  iextern l
                    (CL_id (gs, vector_ctyp))
                    (mk_id "internal_vector_init", [])
                    [V_lit (VL_int Big_int.zero, CT_fint 64)];
                ],
                V_id (gs, vector_ctyp),
                [iclear vector_ctyp gs]
              )
        end
    (* If we have a bitvector value, that isn't a literal then we need to set bits individually. *)
    | AV_vector (avals, Typ_aux (Typ_app (id, _), _)) when string_of_id id = "bitvector" && List.length avals <= 64 ->
        let len = List.length avals in
        let gs = ngensym () in
        let ctyp = CT_fbits len in
        let mask i =
          VL_bits
            (Util.list_init (63 - i) (fun _ -> Sail2_values.B0)
            @ [Sail2_values.B1]
            @ Util.list_init i (fun _ -> Sail2_values.B0)
            )
        in
        let aval_mask i aval =
          let setup, cval, cleanup = compile_aval l ctx aval in
          match cval with
          | V_lit (VL_bits [Sail2_values.B0], _) -> []
          | V_lit (VL_bits [Sail2_values.B1], _) ->
              [icopy l (CL_id (gs, ctyp)) (V_call (Bvor, [V_id (gs, ctyp); V_lit (mask i, ctyp)]))]
          | _ ->
              setup
              @ [
                  iextern l
                    (CL_id (gs, ctyp))
                    (mk_id "update_fbits", [])
                    [V_id (gs, ctyp); V_lit (VL_int (Big_int.of_int i), CT_constant (Big_int.of_int i)); cval];
                ]
              @ cleanup
        in
        ( [
            idecl l ctyp gs;
            icopy l (CL_id (gs, ctyp)) (V_lit (VL_bits (Util.list_init len (fun _ -> Sail2_values.B0)), ctyp));
          ]
          @ List.concat (List.mapi aval_mask (List.rev avals)),
          V_id (gs, ctyp),
          []
        )
    (* Compiling a vector literal that isn't a bitvector *)
    | AV_vector (avals, Typ_aux (Typ_app (id, [_; A_aux (A_typ typ, _)]), _)) when string_of_id id = "vector" ->
        let ord = Env.get_default_order ctx.tc_env in
        let len = List.length avals in
        let direction = match ord with Ord_aux (Ord_inc, _) -> false | Ord_aux (Ord_dec, _) -> true in
        let elem_ctyp = ctyp_of_typ ctx typ in
        let vector_ctyp = CT_fvector (len, elem_ctyp) in
        let gs = ngensym () in
        let aval_set i aval =
          let setup, cval, cleanup = compile_aval l ctx aval in
          let cval, conversion_setup, conversion_cleanup =
            if ctyp_equal (cval_ctyp cval) elem_ctyp then (cval, [], [])
            else (
              let gs = ngensym () in
              (V_id (gs, elem_ctyp), [iinit l elem_ctyp gs cval], [iclear elem_ctyp gs])
            )
          in
          setup @ conversion_setup
          @ [
              iextern l
                (CL_id (gs, vector_ctyp))
                (mk_id "internal_vector_update", [])
                [V_id (gs, vector_ctyp); V_lit (VL_int (Big_int.of_int i), CT_fint 64); cval];
            ]
          @ conversion_cleanup @ cleanup
        in
        ( [
            idecl l vector_ctyp gs;
            iextern l
              (CL_id (gs, vector_ctyp))
              (mk_id "internal_vector_init", [])
              [V_lit (VL_int (Big_int.of_int len), CT_fint 64)];
          ]
          @ List.concat (List.mapi aval_set (if direction then List.rev avals else avals)),
          V_id (gs, vector_ctyp),
          [iclear vector_ctyp gs]
        )
    | AV_vector _ as aval ->
        raise
          (Reporting.err_general l
             ("Have AVL_vector: " ^ Document.to_string (pp_aval aval) ^ " which is not a vector type")
          )
    | AV_list (avals, Typ_aux (typ, _)) ->
        let ctyp =
          match typ with
          | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "list" -> ctyp_suprema (ctyp_of_typ ctx typ)
          | _ -> raise (Reporting.err_general l "Invalid list type")
        in
        let gs = ngensym () in
        let mk_cons aval =
          let setup, cval, cleanup = compile_aval l ctx aval in
          setup
          @ [iextern l (CL_id (gs, CT_list ctyp)) (mk_id "sail_cons", [ctyp]) [cval; V_id (gs, CT_list ctyp)]]
          @ cleanup
        in
        ( [idecl l (CT_list ctyp) gs] @ List.concat (List.map mk_cons (List.rev avals)),
          V_id (gs, CT_list ctyp),
          [iclear (CT_list ctyp) gs]
        )

  (** Compile a function call.

      If called as [compile_funcall ~override_id:foo l ctx bar args], then we will compile as if we are calling [bar],
      but insert a call to [foo] in the IR. This is used for optimizations where we can generate a more efficient
      version of [foo] that doesn't exist in the original Sail. *)
  let compile_funcall_with ?override_id l ctx id compile_arg args =
    let setup = ref [] in
    let cleanup = ref [] in

    let quant, Typ_aux (fn_typ, _) =
      (* If we can't find a function in local_env, fall back to the
         global env - this happens when representing assertions, exit,
         etc as functions in the IR. *)
      try Env.get_val_spec id ctx.local_env with Type_error.Type_error _ -> Env.get_val_spec id ctx.tc_env
    in
    let params = quant_kopts quant |> List.filter is_typ_kopt |> List.map kopt_kid in

    let arg_typs, ret_typ = match fn_typ with Typ_fn (arg_typs, ret_typ) -> (arg_typs, ret_typ) | _ -> assert false in
    let ctx' = { ctx with local_env = Env.add_typquant (id_loc id) quant ctx.local_env } in
    let arg_ctyps, ret_ctyp = (List.map (ctyp_of_typ ctx') arg_typs, ctyp_of_typ ctx' ret_typ) in

    assert (List.length arg_ctyps = List.length args);

    let instantiation = ref KBindings.empty in

    let setup_arg ctyp arg =
      let arg_setup, cval, arg_cleanup = compile_arg arg in
      instantiation := KBindings.union merge_unifiers (ctyp_unify l ctyp (cval_ctyp cval)) !instantiation;
      setup := List.rev arg_setup @ !setup;
      cleanup := arg_cleanup @ !cleanup;
      cval
    in

    let setup_args = List.map2 setup_arg arg_ctyps args in

    let call_id = Option.value ~default:id override_id in

    ( List.rev !setup,
      begin
        fun clexp ->
          let instantiation =
            KBindings.union merge_unifiers (ctyp_unify l ret_ctyp (clexp_ctyp clexp)) !instantiation
          in
          let ctyp_args = List.map (fun v -> KBindings.find v instantiation) params in
          ifuncall l clexp (call_id, ctyp_args) setup_args
        (* iblock1 (optimize_call l ctx clexp (id, KBindings.bindings unifiers |> List.map snd) setup_args arg_ctyps ret_ctyp) *)
      end,
      !cleanup
    )

  let compile_funcall ?override_id l ctx id args = compile_funcall_with ?override_id l ctx id (compile_aval l ctx) args

  let compile_extern l ctx id args return_ctyp =
    let setup = ref [] in
    let cleanup = ref [] in

    let setup_arg aval =
      let arg_setup, cval, arg_cleanup = compile_aval l ctx aval in
      setup := List.rev arg_setup @ !setup;
      cleanup := arg_cleanup @ !cleanup;
      cval
    in

    let setup_args = List.map setup_arg args in

    (List.rev !setup, (fun clexp -> iextern ?return_ctyp l clexp (id, []) setup_args), !cleanup)

  let select_abstract l ctx string_id f =
    let rec if_chain = function [] -> [] | [(_, e)] -> e | (i, t) :: e -> [iif l i t (if_chain e)] in
    Bindings.bindings ctx.abstracts
    |> List.map (fun (id, ctyp) ->
           (V_call (String_eq, [V_id (string_id, CT_string); V_lit (VL_string (string_of_id id), CT_string)]), f id ctyp)
       )
    |> if_chain

  let static_load l ctyp f =
    let loaded, loaded_instr = istatic l CT_bool (VL_bool false) in
    let s, s_instr = istatic l ctyp VL_undefined in
    ( [
        loaded_instr;
        s_instr;
        iif l
          (V_call (Bnot, [V_id (loaded, CT_bool)]))
          (f s @ [icopy l (CL_id (loaded, CT_bool)) (V_lit (VL_bool true, CT_bool))])
          [];
      ],
      (fun clexp -> icopy l clexp (V_id (s, ctyp))),
      []
    )

  let compile_config' l ctx key ctyp =
    let key_name = ngensym () in
    let json = ngensym () in
    let args = [V_lit (VL_int (Big_int.of_int (List.length key)), CT_fint 64); V_id (key_name, CT_json_key)] in
    let init =
      [
        ijson_key l key_name key;
        idecl l CT_json json;
        iextern l (CL_id (json, CT_json)) (mk_id "sail_config_get", []) args;
      ]
    in

    let config_extract ctyp json ~validate ~extract =
      let valid = ngensym () in
      let value = ngensym () in
      ( [
          idecl l CT_bool valid;
          iextern l (CL_id (valid, CT_bool)) (mk_id (fst validate), []) ([V_id (json, CT_json)] @ snd validate);
          iif l (V_call (Bnot, [V_id (valid, CT_bool)])) [ibad_config l] [];
          idecl l ctyp value;
          iextern l (CL_id (value, ctyp)) (mk_id extract, []) [V_id (json, CT_json)];
        ],
        (fun clexp -> icopy l clexp (V_id (value, ctyp))),
        [iclear ctyp value]
      )
    in

    let config_extract_bits ctyp json =
      let value = ngensym () in
      let is_abstract = ngensym () in
      let abstract_name = ngensym () in
      let setup, non_abstract_call, cleanup =
        config_extract ctyp json ~validate:("sail_config_is_bits", []) ~extract:"sail_config_unwrap_bits"
      in
      ( [
          idecl l CT_bool is_abstract;
          iextern l (CL_id (is_abstract, CT_bool)) (mk_id "sail_config_is_bits_abstract", []) [V_id (json, CT_json)];
          idecl l ctyp value;
          iif l
            (V_id (is_abstract, CT_bool))
            ([
               idecl l CT_string abstract_name;
               iextern l
                 (CL_id (abstract_name, CT_string))
                 (mk_id "sail_config_bits_abstract_len", [])
                 [V_id (json, CT_json)];
             ]
            @ select_abstract l ctx abstract_name (fun id (abstract_ctyp, _) ->
                  match abstract_ctyp with
                  | CT_fint 64 ->
                      [
                        iextern l
                          (CL_id (value, ctyp))
                          (mk_id "sail_config_unwrap_abstract_bits", [])
                          [V_id (Abstract id, abstract_ctyp); V_id (json, CT_json)];
                      ]
                  | CT_lint | CT_fint _ ->
                      let len = ngensym () in
                      [
                        iinit l (CT_fint 64) len (V_id (Abstract id, abstract_ctyp));
                        iextern l
                          (CL_id (value, ctyp))
                          (mk_id "sail_config_unwrap_abstract_bits", [])
                          [V_id (len, CT_fint 64); V_id (json, CT_json)];
                      ]
                  | _ -> []
              )
            @ [iclear CT_string abstract_name]
            )
            (setup @ [non_abstract_call (CL_id (value, ctyp))] @ cleanup);
        ],
        (fun clexp -> icopy l clexp (V_id (value, ctyp))),
        [iclear ctyp value]
      )
    in

    let rec extract json = function
      | CT_string ->
          config_extract CT_string json ~validate:("sail_config_is_string", []) ~extract:"sail_config_unwrap_string"
      | CT_unit -> ([], (fun clexp -> icopy l clexp unit_cval), [])
      | CT_lint -> config_extract CT_lint json ~validate:("sail_config_is_int", []) ~extract:"sail_config_unwrap_int"
      | CT_fint _ -> config_extract CT_lint json ~validate:("sail_config_is_int", []) ~extract:"sail_config_unwrap_int"
      | CT_lbits -> config_extract_bits CT_lbits json
      | CT_sbits _ -> config_extract_bits CT_lbits json
      | CT_fbits _ -> config_extract_bits CT_lbits json
      | CT_bool -> config_extract CT_bool json ~validate:("sail_config_is_bool", []) ~extract:"sail_config_unwrap_bool"
      | CT_enum enum_id as enum_ctyp ->
          assert (Bindings.mem enum_id ctx.enums);
          let members = Bindings.find enum_id ctx.enums |> IdSet.elements in
          let enum_name = ngensym () in
          let enum_str = ngensym () in
          let setup, get_string, cleanup =
            config_extract CT_string json ~validate:("sail_config_is_string", []) ~extract:"sail_config_unwrap_string"
          in
          let enum_compare =
            List.fold_left
              (fun rest m ->
                [
                  iif l
                    (V_call (String_eq, [V_id (enum_str, CT_string); V_lit (VL_string (string_of_id m), CT_string)]))
                    [icopy l (CL_id (enum_name, enum_ctyp)) (V_member (m, enum_ctyp))]
                    rest;
                ]
              )
              [ibad_config l]
              members
          in
          ( [idecl l enum_ctyp enum_name; idecl l CT_string enum_str]
            @ setup
            @ [get_string (CL_id (enum_str, CT_string))]
            @ enum_compare,
            (fun clexp -> icopy l clexp (V_id (enum_name, enum_ctyp))),
            cleanup @ [iclear CT_string enum_str; iclear enum_ctyp enum_name]
          )
      | CT_variant (variant_id, args) as variant_ctyp ->
          let constructors = instantiate_polymorphic_type ~at:l variant_id args ctx.variants |> Bindings.bindings in
          let variant_name = ngensym () in
          let ctor_checks, ctor_extracts =
            Util.fold_left_map
              (fun checks (ctor_id, ctyp) ->
                let is_ctor = ngensym () in
                let ctor_json = ngensym () in
                let value = ngensym () in
                let check =
                  [
                    idecl l CT_bool is_ctor;
                    iextern l
                      (CL_id (is_ctor, CT_bool))
                      (mk_id "sail_config_object_has_key", [])
                      [V_id (json, CT_json); V_lit (VL_string (string_of_id ctor_id), CT_string)];
                  ]
                in
                let setup, call, cleanup = extract ctor_json ctyp in
                let ctor_setup, ctor_call, ctor_cleanup =
                  compile_funcall_with l ctx ctor_id (fun cval -> ([], cval, [])) [V_id (value, ctyp)]
                in
                let extract =
                  [
                    idecl l CT_json ctor_json;
                    idecl l ctyp value;
                    iextern l
                      (CL_id (ctor_json, CT_json))
                      (mk_id "sail_config_object_key", [])
                      [V_id (json, CT_json); V_lit (VL_string (string_of_id ctor_id), CT_string)];
                  ]
                  @ setup @ ctor_setup
                  @ [call (CL_id (value, ctyp))]
                  @ [ctor_call (CL_id (variant_name, variant_ctyp))]
                  @ ctor_cleanup @ cleanup
                in
                (checks @ check, (is_ctor, extract))
              )
              [] constructors
          in
          let ctor_extracts =
            List.fold_left (fun rest (b, instrs) -> [iif l (V_id (b, CT_bool)) instrs rest]) [] ctor_extracts
          in
          ( [idecl l variant_ctyp variant_name] @ ctor_checks @ ctor_extracts,
            (fun clexp -> icopy l clexp (V_id (variant_name, variant_ctyp))),
            [iclear variant_ctyp variant_name]
          )
      | CT_struct (struct_id, args) as struct_ctyp ->
          let fields = instantiate_polymorphic_type ~at:l struct_id args ctx.records |> Bindings.bindings in
          let struct_name = ngensym () in
          let fields_from_json =
            List.map
              (fun (field_id, field_ctyp) ->
                let field_json = ngensym () in
                let setup, call, cleanup = extract field_json field_ctyp in
                [
                  idecl l CT_json field_json;
                  iextern l
                    (CL_id (field_json, CT_json))
                    (mk_id "sail_config_object_key", [])
                    [V_id (json, CT_json); V_lit (VL_string (string_of_id field_id), CT_string)];
                ]
                @ setup
                @ [call (CL_field (CL_id (struct_name, struct_ctyp), field_id, field_ctyp))]
                @ cleanup
                @ [iclear CT_json field_json]
              )
              fields
            |> List.concat
          in
          ( [idecl l struct_ctyp struct_name] @ fields_from_json,
            (fun clexp -> icopy l clexp (V_id (struct_name, struct_ctyp))),
            [iclear struct_ctyp struct_name]
          )
      | CT_vector item_ctyp ->
          let vec = ngensym () in
          let len = ngensym () in
          let n = ngensym () in
          let item_json = ngensym () in
          let item = ngensym () in
          let loop = label "config_vector_" in
          let index =
            V_call
              ( Isub,
                [
                  V_id (len, CT_fint 64);
                  V_call (Iadd, [V_id (n, CT_fint 64); V_lit (VL_int (Big_int.of_int 1), CT_fint 64)]);
                ]
              )
          in
          let setup, call, cleanup = extract item_json item_ctyp in
          ( [
              idecl l (CT_fint 64) len;
              iextern l (CL_id (len, CT_bool)) (mk_id "sail_config_list_length", []) [V_id (json, CT_json)];
              iif l
                (V_call (Eq, [V_id (len, CT_fint 64); V_lit (VL_int (Big_int.of_int (-1)), CT_fint 64)]))
                [ibad_config l]
                [];
              idecl l (CT_vector item_ctyp) vec;
              iextern l (CL_id (vec, CT_vector item_ctyp)) (mk_id "internal_vector_init", []) [V_id (len, CT_fint 64)];
              iinit l (CT_fint 64) n (V_lit (VL_int Big_int.zero, CT_fint 64));
              ilabel loop;
              idecl l CT_json item_json;
              iextern l
                (CL_id (item_json, CT_json))
                (mk_id "sail_config_list_nth", [])
                [V_id (json, CT_json); V_id (n, CT_fint 64)];
              idecl l item_ctyp item;
            ]
            @ setup
            @ [
                call (CL_id (item, item_ctyp));
                iextern l
                  (CL_id (vec, CT_vector item_ctyp))
                  (mk_id "internal_vector_update", [])
                  [V_id (vec, CT_vector item_ctyp); index; V_id (item, item_ctyp)];
              ]
            @ cleanup
            @ [
                iclear item_ctyp item;
                iclear CT_json item_json;
                icopy l
                  (CL_id (n, CT_fint 64))
                  (V_call (Iadd, [V_id (n, CT_fint 64); V_lit (VL_int (Big_int.of_int 1), CT_fint 64)]));
                ijump l (V_call (Ilt, [V_id (n, CT_fint 64); V_id (len, CT_fint 64)])) loop;
              ],
            (fun clexp -> icopy l clexp (V_id (vec, CT_vector item_ctyp))),
            [iclear (CT_vector item_ctyp) vec]
          )
      | CT_list item_ctyp ->
          let list = ngensym () in
          let len = ngensym () in
          let n = ngensym () in
          let item_json = ngensym () in
          let item = ngensym () in
          let loop_start = label "config_list_start_" in
          let loop_end = label "config_list_end_" in
          let index =
            V_call
              ( Isub,
                [
                  V_id (len, CT_fint 64);
                  V_call (Iadd, [V_id (n, CT_fint 64); V_lit (VL_int (Big_int.of_int 1), CT_fint 64)]);
                ]
              )
          in
          let setup, call, cleanup = extract item_json item_ctyp in
          ( [
              idecl l (CT_fint 64) len;
              iextern l (CL_id (len, CT_bool)) (mk_id "sail_config_list_length", []) [V_id (json, CT_json)];
              iif l
                (V_call (Eq, [V_id (len, CT_fint 64); V_lit (VL_int (Big_int.of_int (-1)), CT_fint 64)]))
                [ibad_config l]
                [];
              idecl l (CT_list item_ctyp) list;
              iinit l (CT_fint 64) n (V_lit (VL_int Big_int.zero, CT_fint 64));
              ilabel loop_start;
              ijump l (V_call (Igteq, [V_id (n, CT_fint 64); V_id (len, CT_fint 64)])) loop_end;
              idecl l CT_json item_json;
              iextern l (CL_id (item_json, CT_json)) (mk_id "sail_config_list_nth", []) [V_id (json, CT_json); index];
              idecl l item_ctyp item;
            ]
            @ setup
            @ [
                call (CL_id (item, item_ctyp));
                iextern l
                  (CL_id (list, CT_list item_ctyp))
                  (mk_id "sail_cons", [])
                  [V_id (item, item_ctyp); V_id (list, CT_list item_ctyp)];
              ]
            @ cleanup
            @ [
                iclear item_ctyp item;
                iclear CT_json item_json;
                icopy l
                  (CL_id (n, CT_fint 64))
                  (V_call (Iadd, [V_id (n, CT_fint 64); V_lit (VL_int (Big_int.of_int 1), CT_fint 64)]));
                igoto loop_start;
                ilabel loop_end;
              ],
            (fun clexp -> icopy l clexp (V_id (list, CT_list item_ctyp))),
            [iclear (CT_list item_ctyp) list]
          )
      | ctyp -> Reporting.unreachable l __POS__ ("Invalid configuration type " ^ string_of_ctyp ctyp)
    in

    let setup, call, cleanup = extract json ctyp in
    if ctx.no_static then (init @ setup, call, cleanup @ [iclear CT_json json; iclear CT_json_key key_name])
    else
      static_load l ctyp (fun s ->
          init @ setup @ [call (CL_id (s, ctyp))] @ cleanup @ [iclear CT_json json; iclear CT_json_key key_name]
      )

  let compile_config l ctx args typ =
    let ctyp = ctyp_of_typ ctx typ in
    let key =
      List.map
        (function
          | AV_lit (L_aux (L_string part, _), _) -> part
          | _ -> Reporting.unreachable l __POS__ "Invalid argument when compiling config key"
          )
        args
    in
    compile_config' l ctx key ctyp

  let rec compile_match ctx (AP_aux (apat_aux, { env; loc = l; _ })) cval on_failure =
    let ctx = { ctx with local_env = env } in
    let ctyp = cval_ctyp cval in
    match apat_aux with
    | AP_global (pid, typ) ->
        let global_ctyp = ctyp_of_typ ctx typ in
        ([], [icopy l (CL_id (name pid, global_ctyp)) cval], [], ctx)
    | AP_id (Name (pid, _), _) when is_ct_enum ctyp -> begin
        match Env.lookup_id pid ctx.tc_env with
        | Unbound _ -> ([], [idecl l ctyp (name pid); icopy l (CL_id (name pid, ctyp)) cval], [], ctx)
        | _ -> ([on_failure l (V_call (Neq, [V_member (pid, ctyp); cval]))], [], [], ctx)
      end
    | AP_id (pid, typ) ->
        let id_ctyp = ctyp_of_typ ctx typ in
        let ctx = { ctx with locals = NameMap.add pid (Immutable, id_ctyp) ctx.locals } in
        ([], [idecl l id_ctyp pid; icopy l (CL_id (pid, id_ctyp)) cval], [iclear id_ctyp pid], ctx)
    | AP_as (apat, id, typ) ->
        let id_ctyp = ctyp_of_typ ctx typ in
        let pre, instrs, cleanup, ctx = compile_match ctx apat cval on_failure in
        let ctx = { ctx with locals = NameMap.add id (Immutable, id_ctyp) ctx.locals } in
        (pre, instrs @ [idecl l id_ctyp id; icopy l (CL_id (id, id_ctyp)) cval], iclear id_ctyp id :: cleanup, ctx)
    | AP_struct (afpats, _) ->
        let _, field_ctyp = struct_fields l ctx ctyp in
        let fold (pre, instrs, cleanup, ctx) (field, apat) =
          let pre', instrs', cleanup', ctx =
            compile_match ctx apat (V_field (cval, field, field_ctyp field)) on_failure
          in
          (pre @ pre', instrs @ instrs', cleanup' @ cleanup, ctx)
        in
        let pre, instrs, cleanup, ctx = List.fold_left fold ([], [], [], ctx) afpats in
        (pre, instrs, cleanup, ctx)
    | AP_tuple apats -> (
        let get_tup n = V_tuple_member (cval, List.length apats, n) in
        let fold (pre, instrs, cleanup, n, ctx) apat ctyp =
          let pre', instrs', cleanup', ctx = compile_match ctx apat (get_tup n) on_failure in
          (pre @ pre', instrs @ instrs', cleanup' @ cleanup, n + 1, ctx)
        in
        match ctyp with
        | CT_tup ctyps ->
            let pre, instrs, cleanup, _, ctx = List.fold_left2 fold ([], [], [], 0, ctx) apats ctyps in
            (pre, instrs, cleanup, ctx)
        | _ -> Reporting.unreachable l __POS__ ("AP_tuple with ctyp " ^ string_of_ctyp ctyp)
      )
    | AP_app (Newtype_wrapper _, apat, _) -> compile_match ctx apat cval on_failure
    | AP_app (Constructor ctor, apat, variant_typ) -> begin
        match ctyp with
        | CT_variant (var_id, args) ->
            (* These should really be the same, something has gone wrong if they are not. *)
            if not (ctyp_equal (cval_ctyp cval) (ctyp_of_typ ctx variant_typ)) then
              raise
                (Reporting.err_general l
                   (Printf.sprintf "When compiling constructor pattern, %s should have the same type as %s"
                      (string_of_ctyp (cval_ctyp cval))
                      (string_of_ctyp (ctyp_of_typ ctx variant_typ))
                   )
                );
            let ctor_ctyp =
              let ctors = instantiate_polymorphic_type ~at:l var_id args ctx.variants in
              match Bindings.find_opt ctor ctors with
              | Some ctyp -> ctyp
              | None ->
                  Reporting.unreachable l __POS__
                    ("Failed to find constructor " ^ string_of_id ctor ^ " in " ^ string_of_ctyp ctyp)
            in
            let pre, instrs, cleanup, ctx =
              compile_match ctx apat (V_ctor_unwrap (cval, (ctor, args), ctor_ctyp)) on_failure
            in
            ([on_failure l (V_ctor_kind (cval, (ctor, args)))] @ pre, instrs, cleanup, ctx)
        | ctyp ->
            raise
              (Reporting.err_general l
                 (Printf.sprintf "Variant constructor %s : %s matching against non-variant type %s : %s"
                    (string_of_id ctor) (string_of_typ variant_typ) (string_of_cval cval) (string_of_ctyp ctyp)
                 )
              )
      end
    | AP_wild _ -> ([], [], [], ctx)
    | AP_cons (hd_apat, tl_apat) -> begin
        match ctyp with
        | CT_list ctyp ->
            let hd_pre, hd_setup, hd_cleanup, ctx = compile_match ctx hd_apat (V_call (List_hd, [cval])) on_failure in
            let tl_pre, tl_setup, tl_cleanup, ctx = compile_match ctx tl_apat (V_call (List_tl, [cval])) on_failure in
            ( [on_failure l (V_call (List_is_empty, [cval]))] @ hd_pre @ tl_pre,
              hd_setup @ tl_setup,
              tl_cleanup @ hd_cleanup,
              ctx
            )
        | _ -> raise (Reporting.err_general l "Tried to pattern match cons on non list type")
      end
    | AP_nil _ -> ([on_failure l (V_call (Bnot, [V_call (List_is_empty, [cval])]))], [], [], ctx)
    | AP_vector_concat (vc_apats, typ) ->
        let vc_apats, total_width =
          List.fold_right
            (fun (width, apat) (result, offset) -> ((width, offset, apat) :: result, width + offset))
            vc_apats ([], 0)
        in
        List.fold_left
          (fun (pre, instrs, cleanup, ctx) (width, offset, apat) ->
            if (width <= 64 && total_width <= 64) || C.ignore_64 then (
              let pre', instrs', cleanup', ctx =
                compile_match ctx apat
                  (V_call (Slice width, [cval; V_lit (VL_int (Big_int.of_int offset), CT_fint 64)]))
                  on_failure
              in
              (pre @ pre', instrs @ instrs', cleanup' @ cleanup, ctx)
            )
            else (
              let sliced = ngensym () in
              let offset_id = ngensym () in
              let width_id = ngensym () in
              let mk_slice =
                [
                  idecl l CT_lbits sliced;
                  iinit l CT_lint offset_id (V_lit (VL_int (Big_int.of_int offset), CT_fint 64));
                  iinit l CT_lint width_id (V_lit (VL_int (Big_int.of_int width), CT_fint 64));
                  iextern l
                    (CL_id (sliced, CT_lbits))
                    (mk_id "slice", [])
                    [cval; V_id (offset_id, CT_lint); V_id (width_id, CT_lint)];
                  iclear CT_lint width_id;
                  iclear CT_lint offset_id;
                ]
              in
              let pre', instrs', cleanup', ctx = compile_match ctx apat (V_id (sliced, CT_lbits)) on_failure in
              (pre @ pre', instrs @ mk_slice @ instrs', cleanup' @ [iclear CT_lbits sliced] @ cleanup, ctx)
            )
          )
          ([], [], [], ctx) vc_apats

  let rec compile_alexp ctx alexp =
    match alexp with
    | AL_id (id, typ) ->
        let ctyp = match get_variable_ctyp id ctx with Some (_, ctyp) -> ctyp | None -> ctyp_of_typ ctx typ in
        CL_id (id, ctyp)
    | AL_addr (id, typ) ->
        let ctyp = match get_variable_ctyp id ctx with Some (_, ctyp) -> ctyp | None -> ctyp_of_typ ctx typ in
        CL_addr (CL_id (id, ctyp))
    | AL_field (alexp, field_id) ->
        let clexp = compile_alexp ctx alexp in
        let _, field_ctyp = struct_fields (id_loc field_id) ctx (clexp_ctyp clexp) in
        CL_field (compile_alexp ctx alexp, field_id, field_ctyp field_id)

  let can_optimize_control_flow_order ctx =
    match ctx.def_annot with
    | Some def_annot -> Option.is_some (get_def_attribute "optimize_control_flow_order" def_annot)
    | None -> false

  (** Returns true if we have an infalliable mapping case. This occurs only if the final case is marked with
      $[mapping_last] by the mappings.ml rewrite, and we have a $[mapping_infallible] attribute attached to the
      containing function in the context. *)
  let has_infallible_mapping_case ctx = function
    | [] -> true
    | cases ->
        let in_infallible_mapping =
          match ctx.def_annot with
          | None -> false
          | Some def_annot -> Option.is_some (get_def_attribute "mapping_infallible" def_annot)
        in
        in_infallible_mapping
        &&
        let _, _, _, uannot = Util.last cases in
        Option.is_some (get_attribute "mapping_last" uannot)

  let rec compile_aexp ctx (AE_aux (aexp_aux, { env; loc = l; uannot })) =
    let ctx = { ctx with local_env = env } in
    match aexp_aux with
    | AE_let (mut, id, binding_typ, binding, (AE_aux (_, { env = body_env; _ }) as body), body_typ) ->
        let binding_ctyp = ctyp_of_typ { ctx with local_env = body_env } binding_typ in
        let setup, call, cleanup = compile_aexp ctx binding in
        let letb_setup, letb_cleanup =
          ( [idecl l binding_ctyp id; iblock1 (setup @ [call (CL_id (id, binding_ctyp))] @ cleanup)],
            [iclear binding_ctyp id]
          )
        in
        let ctx = { ctx with locals = NameMap.add id (mut, binding_ctyp) ctx.locals } in
        let setup, call, cleanup = compile_aexp ctx body in
        (letb_setup @ setup, call, cleanup @ letb_cleanup)
    | AE_app (Sail_function id, vs, _) ->
        if Option.is_some (get_attribute "mapping_guarded" uannot) then (
          let override_id = append_id id "_infallible" in
          if Bindings.mem override_id ctx.valspecs then compile_funcall ~override_id l ctx id vs
          else compile_funcall l ctx id vs
        )
        else compile_funcall l ctx id vs
    | AE_app (Newtype_wrapper id, args, _) -> (
        match args with
        | [arg] ->
            let setup, cval, cleanup = compile_aval l ctx arg in
            (setup, (fun clexp -> icopy l clexp cval), cleanup)
        | _ -> Reporting.unreachable l __POS__ "Found newtype wrapper with > 1 argument during Jib generation"
      )
    | AE_app (Pure_extern (id, return_typ), args, typ) ->
        let return_ctyp = Option.map (ctyp_of_typ ctx) return_typ in
        compile_extern l ctx id args return_ctyp
    | AE_app (Extern (id, return_typ), args, typ) ->
        let str = string_of_id id in
        if str = "sail_assert" && C.assert_to_exception then (
          match args with
          | [cond; msg] ->
              let cond_setup, cond_cval, cond_cleanup = compile_aval l ctx cond in
              let msg_setup, msg_cval, _ = compile_aval l ctx msg in
              let exn_setup, exn_cval = assert_exception l msg_cval in
              ( cond_setup @ [iif l cond_cval [] (msg_setup @ exn_setup @ [ithrow l exn_cval])] @ cond_cleanup,
                (fun clexp -> icopy l clexp unit_cval),
                []
              )
          | _ -> Reporting.unreachable l __POS__ "Bad arity for sail_assert"
        )
        else if str = "sail_config_get" then compile_config l ctx args typ
        else (
          let return_ctyp = Option.map (ctyp_of_typ ctx) return_typ in
          compile_extern l ctx id args return_ctyp
        )
    | AE_val aval ->
        let setup, cval, cleanup = compile_aval l ctx aval in
        (setup, (fun clexp -> icopy l clexp cval), cleanup)
    (* Compile case statements *)
    | AE_match (aval, cases, typ)
      when C.eager_control_flow
           && (can_optimize_control_flow_order ctx || Option.is_some (get_attribute "anf_pure" uannot)) ->
        let ctyp = ctyp_of_typ ctx typ in
        let aval_setup, cval, aval_cleanup = compile_aval l ctx aval in
        let compile_case case_match_id case_return_id (apat, guard, body, case_uannot) =
          if is_dead_aexp body then None
          else (
            let trivial_guard =
              match guard with
              | AE_aux (AE_val (AV_lit (L_aux (L_true, _), _)), _)
              | AE_aux (AE_val (AV_cval (V_lit (VL_bool true, CT_bool), _)), _) ->
                  true
              | _ -> false
            in
            let pre_destructure, destructure, destructure_cleanup, ctx =
              compile_match ctx apat cval (fun l b -> icopy l (CL_id (case_match_id, CT_bool)) (V_call (Bnot, [b])))
            in
            let guard_setup, guard_call, guard_cleanup = compile_aexp ctx guard in
            let body_setup, body_call, body_cleanup = compile_aexp ctx body in
            Some
              ([idecl l ctyp case_return_id; iinit l CT_bool case_match_id (V_lit (VL_bool true, CT_bool))]
              @ pre_destructure @ destructure
              @ ( if not trivial_guard then (
                    let gs = ngensym () in
                    guard_setup
                    @ [
                        idecl l CT_bool gs;
                        guard_call (CL_id (gs, CT_bool));
                        icopy l
                          (CL_id (case_match_id, CT_bool))
                          (V_call (Band, [V_id (case_match_id, CT_bool); V_id (gs, CT_bool)]));
                      ]
                    @ guard_cleanup
                  )
                  else []
                )
              @ body_setup
              @ [body_call (CL_id (case_return_id, ctyp))]
              @ body_cleanup @ destructure_cleanup
              )
          )
        in
        let case_ids, cases =
          List.filter_map
            (fun case ->
              let open Util.Option_monad in
              let case_match_id = ngensym () in
              let case_return_id = ngensym () in
              let* case = compile_case case_match_id case_return_id case in
              Some ((V_id (case_match_id, CT_bool), V_id (case_return_id, ctyp)), case)
            )
            cases
          |> List.split
        in
        let rec build_ite = function
          | [(_, ret)] -> ret
          | (b, ret) :: rest -> V_call (Ite, [b; ret; build_ite rest])
          | [] -> Reporting.unreachable l __POS__ "Empty match found"
        in
        (aval_setup @ List.concat cases, (fun clexp -> icopy l clexp (build_ite case_ids)), aval_cleanup)
    | AE_match (aval, cases, typ) ->
        let is_complete = Option.is_some (get_attribute "complete" uannot) || has_infallible_mapping_case ctx cases in
        let ctx = update_coverage_override uannot ctx in
        let ctyp = ctyp_of_typ ctx typ in
        let aval_setup, cval, aval_cleanup = compile_aval l ctx aval in
        (* Get the number of cases, because we don't want to check branch
           coverage for matches with only a single case. *)
        let num_cases = List.length cases in
        let branch_id, on_reached = if num_cases > 1 then coverage_branch_reached ctx l else (0, []) in
        let case_return_id = ngensym () in
        let finish_match_label = label "finish_match_" in
        let compile_case is_last (apat, guard, body, case_uannot) =
          let case_label = label "case_" in
          if is_dead_aexp body then [ilabel case_label]
          else (
            let trivial_guard =
              match guard with
              | AE_aux (AE_val (AV_lit (L_aux (L_true, _), _)), _)
              | AE_aux (AE_val (AV_cval (V_lit (VL_bool true, CT_bool), _)), _) ->
                  true
              | _ -> false
            in
            (* If we are at the last case of a complete match, the final destructuring can never fail
               so just make it a no-op. Note that it is important we do this, rather than just keep the
               jump that is never taken, otherwise we confuse targets like Sail->SV which linearize the
               control flow graph. *)
            let pre_destructure, destructure, destructure_cleanup, ctx =
              compile_match ctx apat cval (fun l b ->
                  if is_last && is_complete then icomment "complete" else ijump l b case_label
              )
            in
            let guard_setup, guard_call, guard_cleanup = compile_aexp ctx guard in
            let body_setup, body_call, body_cleanup = compile_aexp ctx body in
            let gs = ngensym () in
            let case_instrs =
              pre_destructure @ destructure
              @ ( if not trivial_guard then
                    guard_setup
                    @ [idecl l CT_bool gs; guard_call (CL_id (gs, CT_bool))]
                    @ guard_cleanup
                    @ [iif l (V_call (Bnot, [V_id (gs, CT_bool)])) (destructure_cleanup @ [igoto case_label]) []]
                  else []
                )
              @ (if num_cases > 1 then coverage_branch_target_taken ctx branch_id body else [])
              @ body_setup
              @ [body_call (CL_id (case_return_id, ctyp))]
              @ body_cleanup @ destructure_cleanup
              @ [igoto finish_match_label]
            in
            [iblock case_instrs; ilabel case_label]
          )
        in
        ( aval_setup @ on_reached
          @ [idecl l ctyp case_return_id]
          @ List.concat (Util.map_last compile_case cases)
          @ (if is_complete then [] else [imatch_failure l])
          @ [ilabel finish_match_label],
          (fun clexp -> icopy l clexp (V_id (case_return_id, ctyp))),
          [iclear ctyp case_return_id] @ aval_cleanup
        )
    (* Compile try statement *)
    | AE_try (aexp, cases, typ) ->
        let ctyp = ctyp_of_typ ctx typ in
        let aexp_setup, aexp_call, aexp_cleanup = compile_aexp ctx aexp in
        let try_return_id = ngensym () in
        let post_exception_handlers_label = label "post_exception_handlers_" in
        let exn_cval = V_id (current_exception, ctyp_of_typ ctx (mk_typ (Typ_id (mk_id "exception")))) in
        let compile_case (apat, guard, body, case_uannot) =
          let trivial_guard =
            match guard with
            | AE_aux (AE_val (AV_lit (L_aux (L_true, _), _)), _)
            | AE_aux (AE_val (AV_cval (V_lit (VL_bool true, CT_bool), _)), _) ->
                true
            | _ -> false
          in
          let try_label = label "try_" in
          let pre_destructure, destructure, destructure_cleanup, ctx =
            compile_match ctx apat exn_cval (fun l b -> ijump l b try_label)
          in
          let guard_setup, guard_call, guard_cleanup = compile_aexp ctx guard in
          let body_setup, body_call, body_cleanup = compile_aexp ctx body in
          let gs = ngensym () in
          let case_instrs =
            pre_destructure @ destructure
            @ ( if not trivial_guard then
                  guard_setup
                  @ [idecl l CT_bool gs; guard_call (CL_id (gs, CT_bool))]
                  @ guard_cleanup
                  @ [ijump l (V_call (Bnot, [V_id (gs, CT_bool)])) try_label]
                else []
              )
            @ body_setup
            @ [body_call (CL_id (try_return_id, ctyp))]
            @ body_cleanup @ destructure_cleanup
            @ [igoto post_exception_handlers_label]
          in
          [iblock case_instrs; ilabel try_label]
        in
        assert (ctyp_equal ctyp (ctyp_of_typ ctx typ));
        ( [
            idecl l ctyp try_return_id;
            itry_block l (aexp_setup @ [aexp_call (CL_id (try_return_id, ctyp))] @ aexp_cleanup);
            ijump l (V_call (Bnot, [V_id (have_exception, CT_bool)])) post_exception_handlers_label;
            icopy l (CL_id (have_exception, CT_bool)) (V_lit (VL_bool false, CT_bool));
          ]
          @ ( if C.assert_to_exception then
                [
                  iif l
                    (V_ctor_kind (exn_cval, (mk_id "__assertion_failed#", [])))
                    []
                    [
                      icopy l (CL_id (have_exception, CT_bool)) (V_lit (VL_bool true, CT_bool));
                      igoto post_exception_handlers_label;
                    ];
                ]
              else []
            )
          @ List.concat (List.map compile_case cases)
          @ [
              (* fallthrough *)
              icopy l (CL_id (have_exception, CT_bool)) (V_lit (VL_bool true, CT_bool));
              ilabel post_exception_handlers_label;
            ],
          (fun clexp -> icopy l clexp (V_id (try_return_id, ctyp))),
          []
        )
    | AE_if (aval, then_aexp, else_aexp, if_typ) ->
        let ctx = update_coverage_override uannot ctx in
        if is_dead_aexp then_aexp then compile_aexp ctx else_aexp
        else if is_dead_aexp else_aexp then compile_aexp ctx then_aexp
        else (
          let if_ctyp = ctyp_of_typ ctx if_typ in
          let setup, cval, cleanup = compile_aval l ctx aval in
          let pure_attr = get_attribute "anf_pure" uannot in
          let eager = C.eager_control_flow && (can_optimize_control_flow_order ctx || Option.is_some pure_attr) in
          if eager then (
            let then_gs = ngensym () in
            let then_setup, then_call, then_cleanup = compile_aexp ctx then_aexp in
            let else_gs = ngensym () in
            let else_setup, else_call, else_cleanup = compile_aexp ctx else_aexp in
            ( setup @ then_setup @ else_setup
              @ [
                  idecl l if_ctyp then_gs;
                  idecl l if_ctyp else_gs;
                  then_call (CL_id (then_gs, if_ctyp));
                  else_call (CL_id (else_gs, if_ctyp));
                ],
              (fun clexp -> icopy l clexp (V_call (Ite, [cval; V_id (then_gs, if_ctyp); V_id (else_gs, if_ctyp)]))),
              [iclear if_ctyp else_gs; iclear if_ctyp then_gs] @ else_cleanup @ then_cleanup @ cleanup
            )
          )
          else (
            let branch_id, on_reached = coverage_branch_reached ctx l in
            let compile_branch aexp =
              let setup, call, cleanup = compile_aexp ctx aexp in
              fun clexp -> coverage_branch_target_taken ctx branch_id aexp @ setup @ [call clexp] @ cleanup
            in
            ( setup,
              (fun clexp ->
                append_into_block on_reached
                  (iif l cval (compile_branch then_aexp clexp) (compile_branch else_aexp clexp))
              ),
              cleanup
            )
          )
        )
    (* FIXME: AE_struct_update could be AV_record_update - would reduce some copying. *)
    | AE_struct_update (aval, fields, typ) ->
        let ctyp = ctyp_of_typ ctx typ in
        let _, field_ctyp = struct_fields l ctx ctyp in
        let gs = ngensym () in
        let compile_fields (id, aval) =
          let field_setup, cval, field_cleanup = compile_aval l ctx aval in
          field_setup @ [icopy l (CL_field (CL_id (gs, ctyp), id, field_ctyp id)) cval] @ field_cleanup
        in
        let setup, cval, cleanup = compile_aval l ctx aval in
        ( [idecl l ctyp gs]
          @ setup
          @ [icopy l (CL_id (gs, ctyp)) cval]
          @ cleanup
          @ List.concat (List.map compile_fields (Bindings.bindings fields)),
          (fun clexp -> icopy l clexp (V_id (gs, ctyp))),
          [iclear ctyp gs]
        )
    | AE_short_circuit (SC_and, aval, aexp) ->
        let left_setup, cval, left_cleanup = compile_aval l ctx aval in
        let right_setup, call, right_cleanup = compile_aexp ctx aexp in
        if
          C.eager_control_flow
          && (can_optimize_control_flow_order ctx || Option.is_some (get_attribute "anf_pure" uannot))
        then (
          let gs = ngensym () in
          ( left_setup @ right_setup @ [idecl l CT_bool gs; call (CL_id (gs, CT_bool))],
            (fun clexp -> icopy l clexp (V_call (Band, [cval; V_id (gs, CT_bool)]))),
            right_cleanup @ left_cleanup
          )
        )
        else (
          let ctx = update_coverage_override uannot ctx in
          let branch_id, on_reached = coverage_branch_reached ctx l in
          let right_coverage = coverage_branch_target_taken ctx branch_id aexp in
          let gs = ngensym () in
          ( left_setup @ on_reached
            @ [
                idecl l CT_bool gs;
                iif l cval
                  (right_coverage @ right_setup @ [call (CL_id (gs, CT_bool))] @ right_cleanup)
                  [icopy l (CL_id (gs, CT_bool)) (V_lit (VL_bool false, CT_bool))];
              ]
            @ left_cleanup,
            (fun clexp -> icopy l clexp (V_id (gs, CT_bool))),
            []
          )
        )
    | AE_short_circuit (SC_or, aval, aexp) ->
        let left_setup, cval, left_cleanup = compile_aval l ctx aval in
        let right_setup, call, right_cleanup = compile_aexp ctx aexp in
        if
          C.eager_control_flow
          && (can_optimize_control_flow_order ctx || Option.is_some (get_attribute "anf_pure" uannot))
        then (
          let gs = ngensym () in
          ( left_setup @ right_setup @ [idecl l CT_bool gs; call (CL_id (gs, CT_bool))],
            (fun clexp -> icopy l clexp (V_call (Bor, [cval; V_id (gs, CT_bool)]))),
            right_cleanup @ left_cleanup
          )
        )
        else (
          let ctx = update_coverage_override uannot ctx in
          let branch_id, on_reached = coverage_branch_reached ctx l in
          let right_coverage = coverage_branch_target_taken ctx branch_id aexp in
          let gs = ngensym () in
          ( left_setup @ on_reached
            @ [
                idecl l CT_bool gs;
                iif l cval
                  [icopy l (CL_id (gs, CT_bool)) (V_lit (VL_bool true, CT_bool))]
                  (right_coverage @ right_setup @ [call (CL_id (gs, CT_bool))] @ right_cleanup);
              ]
            @ left_cleanup,
            (fun clexp -> icopy l clexp (V_id (gs, CT_bool))),
            []
          )
        )
    (* This is a faster assignment rule for updating fields of a
       struct. *)
    | AE_assign (AL_id (id, assign_typ), AE_aux (AE_struct_update (AV_id (rid, _), fields, typ), _))
      when Name.compare id rid = 0 ->
        let ctyp = ctyp_of_typ ctx typ in
        let _, field_ctyp = struct_fields l ctx ctyp in
        let compile_fields (field_id, aval) =
          let field_setup, cval, field_cleanup = compile_aval l ctx aval in
          field_setup @ [icopy l (CL_field (CL_id (id, ctyp), field_id, field_ctyp field_id)) cval] @ field_cleanup
        in
        (List.concat (List.map compile_fields (Bindings.bindings fields)), (fun clexp -> icopy l clexp unit_cval), [])
    | AE_assign (alexp, aexp) ->
        let setup, call, cleanup = compile_aexp ctx aexp in
        (setup @ [call (compile_alexp ctx alexp)], (fun clexp -> icopy l clexp unit_cval), cleanup)
    | AE_block (aexps, aexp, _) ->
        let block = compile_block ctx aexps in
        let setup, call, cleanup = compile_aexp ctx aexp in
        (block @ setup, call, cleanup)
    | AE_loop (While, cond, body) ->
        let loop_start_label = label "while_" in
        let loop_end_label = label "wend_" in
        let cond_setup, cond_call, cond_cleanup = compile_aexp ctx cond in
        let body_setup, body_call, body_cleanup = compile_aexp ctx body in
        let gs = ngensym () in
        let unit_gs = ngensym () in
        let loop_test = V_call (Bnot, [V_id (gs, CT_bool)]) in
        ( [idecl l CT_bool gs; idecl l CT_unit unit_gs]
          @ [ilabel loop_start_label]
          @ [
              iblock
                (cond_setup
                @ [cond_call (CL_id (gs, CT_bool))]
                @ cond_cleanup
                @ [ijump l loop_test loop_end_label]
                @ body_setup
                @ [body_call (CL_id (unit_gs, CT_unit))]
                @ body_cleanup
                @ [igoto loop_start_label]
                );
            ]
          @ [ilabel loop_end_label],
          (fun clexp -> icopy l clexp unit_cval),
          []
        )
    | AE_loop (Until, cond, body) ->
        let loop_start_label = label "repeat_" in
        let loop_end_label = label "until_" in
        let cond_setup, cond_call, cond_cleanup = compile_aexp ctx cond in
        let body_setup, body_call, body_cleanup = compile_aexp ctx body in
        let gs = ngensym () in
        let unit_gs = ngensym () in
        let loop_test = V_id (gs, CT_bool) in
        ( [idecl l CT_bool gs; idecl l CT_unit unit_gs]
          @ [ilabel loop_start_label]
          @ [
              iblock
                (body_setup
                @ [body_call (CL_id (unit_gs, CT_unit))]
                @ body_cleanup @ cond_setup
                @ [cond_call (CL_id (gs, CT_bool))]
                @ cond_cleanup
                @ [ijump l loop_test loop_end_label]
                @ [igoto loop_start_label]
                );
            ]
          @ [ilabel loop_end_label],
          (fun clexp -> icopy l clexp unit_cval),
          []
        )
    | AE_typ (aexp, typ) -> compile_aexp ctx aexp
    | AE_return (aval, typ) ->
        let fn_return_ctyp =
          match Env.get_ret_typ env with
          | Some typ -> ctyp_of_typ ctx typ
          | None -> raise (Reporting.err_general l "No function return type found when compiling return statement")
        in
        (* Cleanup info will be re-added by fix_early_(heap/stack)_return *)
        let return_setup, cval, _ = compile_aval l ctx aval in
        let creturn =
          if ctyp_equal fn_return_ctyp (cval_ctyp cval) then [ireturn cval]
          else (
            let gs = ngensym () in
            [idecl l fn_return_ctyp gs; icopy l (CL_id (gs, fn_return_ctyp)) cval; ireturn (V_id (gs, fn_return_ctyp))]
          )
        in
        (return_setup @ creturn, (fun clexp -> icomment "unreachable after return"), [])
    | AE_throw (aval, typ) ->
        (* Cleanup info will be handled by fix_exceptions *)
        let throw_setup, cval, _ = compile_aval l ctx aval in
        (throw_setup @ [ithrow l cval], (fun clexp -> icomment "unreachable after throw"), [])
    | AE_exit (aval, typ) ->
        let exit_setup, cval, _ = compile_aval l ctx aval in
        (exit_setup @ [iexit l], (fun clexp -> icomment "unreachable after exit"), [])
    | AE_field (aval, id, typ) ->
        let setup, cval, cleanup = compile_aval l ctx aval in
        let _, field_ctyp = struct_fields l ctx (cval_ctyp cval) in
        (setup, (fun clexp -> icopy l clexp (V_field (cval, id, field_ctyp id))), cleanup)
    (* If unrolling is enabled, and all the loop bounds are fixed then just unroll the exact required amount *)
    | AE_for
        ( loop_var,
          AE_aux (AE_val (AV_lit (L_aux (L_num loop_from, _), _)), _),
          AE_aux (AE_val (AV_lit (L_aux (L_num loop_to, _), _)), _),
          AE_aux (AE_val (AV_lit (L_aux (L_num loop_step, _), _)), _),
          Ord_aux (ord, _),
          body
        )
      when Option.is_some C.unroll_loops ->
        let ctx = { ctx with locals = NameMap.add loop_var (Immutable, CT_fint 64) ctx.locals } in

        let is_inc = match ord with Ord_inc -> true | Ord_dec -> false in

        let body_setup, body_call, body_cleanup = compile_aexp ctx body in
        let body_gs = ngensym () in

        let loop_iteration i =
          let loop_body () =
            [icopy l (CL_id (loop_var, CT_fint 64)) (V_lit (VL_int i, CT_fint 64))]
            @ body_setup
            @ [body_call (CL_id (body_gs, CT_unit))]
            @ body_cleanup
          in
          if is_inc then
            if Big_int.greater i loop_to then None else Some (Big_int.add i loop_step, iblock (loop_body ()))
          else if Big_int.less i loop_to then None
          else Some (Big_int.sub i loop_step, iblock (loop_body ()))
        in
        let rec unroll acc i =
          match loop_iteration i with None -> List.rev acc | Some (next, instr) -> unroll (instr :: acc) next
        in

        ( [idecl l (CT_fint 64) loop_var; idecl l CT_unit body_gs] @ unroll [] loop_from,
          (fun clexp -> icopy l clexp unit_cval),
          []
        )
    | AE_for (loop_var, loop_from, loop_to, loop_step, Ord_aux (ord, _), body) ->
        (* We assume that all loop indices are safe to put in a CT_fint. *)
        let ctx = { ctx with locals = NameMap.add loop_var (Immutable, CT_fint 64) ctx.locals } in

        let is_inc = match ord with Ord_inc -> true | Ord_dec -> false in

        (* Loop variables *)
        let from_setup, from_call, from_cleanup = compile_aexp ctx loop_from in
        let from_gs = ngensym () in
        let to_setup, to_call, to_cleanup = compile_aexp ctx loop_to in
        let to_gs = ngensym () in
        let step_setup, step_call, step_cleanup = compile_aexp ctx loop_step in
        let step_gs = ngensym () in
        let variable_init gs setup call cleanup =
          [idecl l (CT_fint 64) gs; iblock (setup @ [call (CL_id (gs, CT_fint 64))] @ cleanup)]
        in

        let loop_start_label = label "for_start_" in
        let loop_end_label = label "for_end_" in
        let body_setup, body_call, body_cleanup = compile_aexp ctx body in
        let body_gs = ngensym () in

        let loop_body prefix continue =
          prefix
          @ [
              iblock
                ([
                   ijump l
                     (V_call ((if is_inc then Igt else Ilt), [V_id (loop_var, CT_fint 64); V_id (to_gs, CT_fint 64)]))
                     loop_end_label;
                 ]
                @ body_setup
                @ [body_call (CL_id (body_gs, CT_unit))]
                @ body_cleanup
                @ [
                    icopy l
                      (CL_id (loop_var, CT_fint 64))
                      (V_call
                         ((if is_inc then Iadd else Isub), [V_id (loop_var, CT_fint 64); V_id (step_gs, CT_fint 64)])
                      );
                  ]
                @ continue ()
                );
            ]
        in
        (* We can either generate an actual loop body for C, or unroll the body for SMT *)
        let actual = loop_body [ilabel loop_start_label] (fun () -> [igoto loop_start_label]) in
        let rec unroll max n = loop_body [] (fun () -> if n < max then unroll max (n + 1) else [imatch_failure l]) in
        let body =
          match (get_attribute "unroll" uannot, C.unroll_loops) with
          | Some attr_data_opt, Some _ -> (
              match attr_data_opt with
              | _, Some (AD_aux (AD_num times, _)) -> unroll (Big_int.to_int times) 0
              | _, Some (AD_aux (_, l)) -> raise (Reporting.err_general l "Invalid argument on unroll attribute")
              | l, None -> raise (Reporting.err_general l "Expected numeric argument for unroll attribute")
            )
          | None, Some times -> unroll times 0
          | _ -> actual
        in

        ( variable_init from_gs from_setup from_call from_cleanup
          @ variable_init to_gs to_setup to_call to_cleanup
          @ variable_init step_gs step_setup step_call step_cleanup
          @ [
              iblock
                ([
                   idecl l (CT_fint 64) loop_var;
                   icopy l (CL_id (loop_var, CT_fint 64)) (V_id (from_gs, CT_fint 64));
                   idecl l CT_unit body_gs;
                 ]
                @ body
                @ [ilabel loop_end_label]
                );
            ],
          (fun clexp -> icopy l clexp unit_cval),
          []
        )

  and compile_block ctx = function
    | [] -> []
    | (AE_aux (_, { loc = l; _ }) as exp) :: exps ->
        let setup, call, cleanup = compile_aexp ctx exp in
        let rest = compile_block ctx exps in
        if C.use_void then setup @ [call (CL_void CT_unit)] @ cleanup @ rest
        else (
          let gs = ngensym () in
          setup @ [idecl l CT_unit gs; call (CL_id (gs, CT_unit))] @ cleanup @ rest
        )

  let fast_int = function CT_lint when !optimize_aarch64_fast_struct -> CT_fint 64 | ctyp -> ctyp

  (** Compile a sail type definition into a IR one. Most of the actual work of translating the typedefs into C is done
      by the code generator, as it's easy to keep track of structs, tuples and unions in their sail form at this level,
      and leave the fiddly details of how they get mapped to C in the next stage. This function also adds details of the
      types it compiles to the context, ctx, which is why it returns a ctypdef * ctx pair. **)
  let compile_type_def ctx (TD_aux (type_def, (l, _))) =
    match type_def with
    | TD_enum (id, members, _) ->
        let ids = List.map fst members in
        (Some (CTD_enum (id, ids)), { ctx with enums = Bindings.add id (IdSet.of_list ids) ctx.enums })
    | TD_record (id, typq, ctors, _) ->
        let record_ctx = { ctx with local_env = Env.add_typquant l typq ctx.local_env } in
        let ctors =
          List.fold_left
            (fun ctors ((id, typ), _) -> Bindings.add id (fast_int (ctyp_of_typ record_ctx typ)) ctors)
            Bindings.empty ctors
        in
        let params = quant_kopts typq |> List.filter is_typ_kopt |> List.map kopt_kid in
        ( Some (CTD_struct (id, params, Bindings.bindings ctors)),
          { ctx with records = Bindings.add id (params, ctors) ctx.records }
        )
    | TD_variant (id, typq, tus, _) ->
        let compile_tu = function
          | Tu_aux (Tu_ty_id (typ, id), _) ->
              let ctx = { ctx with local_env = Env.add_typquant (id_loc id) typq ctx.local_env } in
              (ctyp_of_typ ctx typ, id)
        in
        let tus =
          if string_of_id id = "exception" && C.assert_to_exception then
            tus @ [Tu_aux (Tu_ty_id (string_typ, mk_id "__assertion_failed#"), mk_def_annot (gen_loc l) ())]
          else tus
        in
        let ctus =
          List.fold_left (fun ctus (ctyp, id) -> Bindings.add id ctyp ctus) Bindings.empty (List.map compile_tu tus)
        in
        let params = quant_kopts typq |> List.filter is_typ_kopt |> List.map kopt_kid in
        ( Some (CTD_variant (id, params, Bindings.bindings ctus)),
          { ctx with variants = Bindings.add id (params, ctus) ctx.variants }
        )
    (* All type abbreviations are filtered out in compile_def  *)
    | TD_abbrev (id, typq, arg) -> (
        match arg with
        | A_aux (A_typ typ, _) when string_of_id id <> "bits" && not (List.exists is_typ_kopt (quant_kopts typq)) ->
            let abbrev_ctx = { ctx with local_env = Env.add_typquant l typq ctx.local_env } in
            let ctyp = ctyp_of_typ abbrev_ctx typ in
            (Some (CTD_abbrev (id, ctyp)), ctx)
        | _ -> (None, ctx)
      )
    | TD_abstract (id, K_aux (kind, _), inst) -> (
        let compile_inst ctyp = function
          | TDC_key key ->
              (* The abstract initialisers are ran very early, before the rest of the model,
                 so we can't rely on Jib static initialisers being set up. *)
              let setup, call, cleanup = compile_config' l { ctx with no_static = true } key ctyp in
              CTDI_instrs (setup @ [call (CL_id (Abstract id, ctyp))] @ cleanup)
          | TDC_none -> CTDI_none
        in
        let is_initialised = function CTDI_instrs _ -> Initialised | CTDI_none -> Uninitialised in
        match kind with
        | K_int ->
            let ctyp = ctyp_of_typ ctx (atom_typ (nid id)) in
            let inst = compile_inst ctyp inst in
            ( Some (CTD_abstract (id, ctyp, inst)),
              { ctx with abstracts = Bindings.add id (ctyp, is_initialised inst) ctx.abstracts }
            )
        | K_bool ->
            let inst = compile_inst CT_bool inst in
            ( Some (CTD_abstract (id, CT_bool, inst)),
              { ctx with abstracts = Bindings.add id (CT_bool, is_initialised inst) ctx.abstracts }
            )
        | _ -> Reporting.unreachable l __POS__ "Found abstract type that was neither an integer nor a boolean"
      )
    (* Will be re-written before here, see bitfield.ml *)
    | TD_bitfield _ -> Reporting.unreachable l __POS__ "Cannot compile TD_bitfield"

  let generate_cleanup instrs =
    let generate_cleanup' (I_aux (instr, _)) =
      match instr with
      | I_init (ctyp, id, cval) -> [(id, iclear ctyp id)]
      | I_decl (ctyp, id) -> [(id, iclear ctyp id)]
      | instr -> []
    in
    let is_clear ids = function I_aux (I_clear (_, id), _) -> NameSet.add id ids | _ -> ids in
    let cleaned = List.fold_left is_clear NameSet.empty instrs in
    instrs |> List.map generate_cleanup' |> List.concat
    |> List.filter (fun (id, _) -> not (NameSet.mem id cleaned))
    |> List.map snd

  let fix_exception_block ?(return = None) ctx instrs =
    let end_block_label = label "end_block_exception_" in
    let is_exception_stop (I_aux (instr, _)) =
      match instr with I_throw _ | I_if _ | I_block _ | I_funcall _ -> true | _ -> false
    in
    (* In this function 'after' is instructions after the one we've
       matched on, 'before is instructions before the instruction we've
       matched with, but after the previous match, and 'historic' are
       all the befores from previous matches. *)
    let rec rewrite_exception historic instrs =
      match instr_split_at is_exception_stop instrs with
      | instrs, [] -> instrs
      | before, I_aux (I_block instrs, _) :: after ->
          before @ [iblock (rewrite_exception (historic @ before) instrs)] @ rewrite_exception (historic @ before) after
      | before, I_aux (I_if (cval, then_instrs, else_instrs), (_, l)) :: after ->
          let historic = historic @ before in
          before
          @ [iif l cval (rewrite_exception historic then_instrs) (rewrite_exception historic else_instrs)]
          @ rewrite_exception historic after
      | before, I_aux (I_throw cval, (_, l)) :: after ->
          before
          @ [
              icopy l (CL_id (current_exception, cval_ctyp cval)) cval;
              icopy l (CL_id (have_exception, CT_bool)) (V_lit (VL_bool true, CT_bool));
            ]
          @ ( if C.track_throw then (
                let loc_string = Reporting.short_loc_to_string l in
                [icopy l (CL_id (throw_location, CT_string)) (V_lit (VL_string loc_string, CT_string))]
              )
              else []
            )
          @ generate_cleanup (historic @ before)
          @ [igoto end_block_label]
          @ rewrite_exception (historic @ before) after
      | before, (I_aux (I_funcall (x, _, f, args), (_, l)) as funcall) :: after ->
          let effects =
            match Bindings.find_opt (fst f) ctx.effect_info.functions with
            | Some effects -> effects
            (* Constructors and back-end built-in value operations might not be present *)
            | None -> Effects.EffectSet.empty
          in
          if Effects.throws effects then
            before
            @ [
                funcall;
                iif l
                  (V_id (have_exception, CT_bool))
                  (generate_cleanup (historic @ before) @ [igoto end_block_label])
                  [];
              ]
            @ rewrite_exception (historic @ before) after
          else before @ (funcall :: rewrite_exception (historic @ before) after)
      | _, _ -> assert false (* unreachable *)
    in
    match return with
    | None -> rewrite_exception [] instrs @ [ilabel end_block_label]
    | Some ctyp -> rewrite_exception [] instrs @ [ilabel end_block_label; iundefined ctyp]

  let rec map_try_block f (I_aux (instr, aux)) =
    let instr =
      match instr with
      | I_decl _ | I_reset _ | I_init _ | I_reinit _ -> instr
      | I_if (cval, instrs1, instrs2) ->
          I_if (cval, List.map (map_try_block f) instrs1, List.map (map_try_block f) instrs2)
      | I_funcall _ | I_copy _ | I_clear _ | I_throw _ | I_return _ -> instr
      | I_block instrs -> I_block (List.map (map_try_block f) instrs)
      | I_try_block instrs -> I_try_block (f (List.map (map_try_block f) instrs))
      | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_jump _ | I_exit _ | I_undefined _ | I_end _ -> instr
    in
    I_aux (instr, aux)

  let fix_exception ?(return = None) ctx instrs =
    let instrs = List.map (map_try_block (fix_exception_block ctx)) instrs in
    fix_exception_block ~return ctx instrs

  let rec compile_arg_pat ctx label (P_aux (p_aux, (l, _)) as pat) ctyp =
    match p_aux with
    | P_id id -> (name id, ([], []))
    | P_wild ->
        let gs = ngensym () in
        (gs, ([], []))
    | P_tuple [] | P_lit (L_aux (L_unit, _)) ->
        let gs = ngensym () in
        (gs, ([], []))
    | P_var (pat, _) -> compile_arg_pat ctx label pat ctyp
    | P_typ (_, pat) -> compile_arg_pat ctx label pat ctyp
    | _ ->
        let apat = anf_pat pat in
        let gs = ngensym () in
        let pre_destructure, destructure, cleanup, _ = compile_match ctx apat (V_id (gs, ctyp)) label in
        (gs, (pre_destructure @ destructure, cleanup))

  let rec compile_arg_pats ctx label (P_aux (p_aux, (l, _)) as pat) ctyps =
    match p_aux with
    | P_typ (_, pat) -> compile_arg_pats ctx label pat ctyps
    | P_tuple pats when List.length pats = List.length ctyps ->
        ([], List.map2 (fun pat ctyp -> compile_arg_pat ctx label pat ctyp) pats ctyps, [])
    | _ when List.length ctyps = 1 -> ([], [compile_arg_pat ctx label pat (List.nth ctyps 0)], [])
    | _ ->
        let arg_id, (destructure, cleanup) = compile_arg_pat ctx label pat (CT_tup ctyps) in
        let new_ids = List.map (fun ctyp -> (ngensym (), ctyp)) ctyps in
        ( destructure
          @ [idecl l (CT_tup ctyps) arg_id]
          @ List.mapi
              (fun i (id, ctyp) -> icopy l (CL_tuple (CL_id (arg_id, CT_tup ctyps), i)) (V_id (id, ctyp)))
              new_ids,
          List.map (fun (id, _) -> (id, ([], []))) new_ids,
          [iclear (CT_tup ctyps) arg_id] @ cleanup
        )

  let combine_destructure_cleanup xs = (List.concat (List.map fst xs), List.concat (List.rev (List.map snd xs)))

  let fix_destructure l fail_label = function
    | [], cleanup -> ([], cleanup)
    | destructure, cleanup ->
        let body_label = label "fundef_body_" in
        (destructure @ [igoto body_label; ilabel fail_label; imatch_failure l; ilabel body_label], cleanup)

  (** Functions that have heap-allocated return types are implemented by passing a pointer a location where the return
      value should be stored. The ANF -> Sail IR pass for expressions simply outputs an I_return instruction for any
      return value, so this function walks over the IR ast for expressions and modifies the return statements into code
      that sets that pointer, as well as adds extra control flow to cleanup heap-allocated variables correctly when a
      function terminates early. See the generate_cleanup function for how this is done. *)
  let fix_early_return l ret instrs =
    let end_function_label = label "end_function_" in
    let is_return_recur (I_aux (instr, _)) =
      match instr with I_return _ | I_undefined _ | I_if _ | I_block _ | I_try_block _ -> true | _ -> false
    in
    let rec rewrite_return historic instrs =
      match instr_split_at is_return_recur instrs with
      | instrs, [] -> instrs
      | before, I_aux (I_try_block instrs, (_, l)) :: after ->
          before @ [itry_block l (rewrite_return (historic @ before) instrs)] @ rewrite_return (historic @ before) after
      | before, I_aux (I_block instrs, _) :: after ->
          before @ [iblock (rewrite_return (historic @ before) instrs)] @ rewrite_return (historic @ before) after
      | before, I_aux (I_if (cval, then_instrs, else_instrs), (_, l)) :: after ->
          let historic = historic @ before in
          before
          @ [iif l cval (rewrite_return historic then_instrs) (rewrite_return historic else_instrs)]
          @ rewrite_return historic after
      | before, I_aux (I_return cval, (_, l)) :: after ->
          let cleanup_label = label "cleanup_" in
          let end_cleanup_label = label "end_cleanup_" in
          before
          @ [icopy l ret cval; igoto cleanup_label]
          (* This is probably dead code until cleanup_label, but we cannot be sure there are no jumps into it. *)
          @ rewrite_return (historic @ before) after
          @ [igoto end_cleanup_label; ilabel cleanup_label]
          @ generate_cleanup (historic @ before)
          @ [igoto end_function_label; ilabel end_cleanup_label]
      | before, I_aux (I_undefined _, (_, l)) :: after ->
          let cleanup_label = label "cleanup_" in
          let end_cleanup_label = label "end_cleanup_" in
          before
          @ [igoto cleanup_label]
          @ rewrite_return (historic @ before) after
          @ [igoto end_cleanup_label; ilabel cleanup_label]
          @ generate_cleanup (historic @ before)
          @ [igoto end_function_label; ilabel end_cleanup_label]
      | _, _ -> assert false
    in
    rewrite_return [] instrs @ [ilabel end_function_label; iend l]

  (** This pass ensures that all variables created by I_decl have unique names *)
  let unique_names =
    let unique_counter = ref 0 in
    let unique_id () =
      let id = mk_id ("u#" ^ string_of_int !unique_counter) in
      incr unique_counter;
      name id
    in

    let rec opt seen = function
      | I_aux (I_decl (ctyp, id), aux) :: instrs when NameSet.mem id seen ->
          let id' = unique_id () in
          let instrs', seen = opt seen instrs in
          (I_aux (I_decl (ctyp, id'), aux) :: instrs_rename id id' instrs', seen)
      | I_aux (I_decl (ctyp, id), aux) :: instrs ->
          let instrs', seen = opt (NameSet.add id seen) instrs in
          (I_aux (I_decl (ctyp, id), aux) :: instrs', seen)
      | I_aux (I_block block, aux) :: instrs ->
          let block', seen = opt seen block in
          let instrs', seen = opt seen instrs in
          (I_aux (I_block block', aux) :: instrs', seen)
      | I_aux (I_try_block block, aux) :: instrs ->
          let block', seen = opt seen block in
          let instrs', seen = opt seen instrs in
          (I_aux (I_try_block block', aux) :: instrs', seen)
      | I_aux (I_if (cval, then_instrs, else_instrs), aux) :: instrs ->
          let then_instrs', seen = opt seen then_instrs in
          let else_instrs', seen = opt seen else_instrs in
          let instrs', seen = opt seen instrs in
          (I_aux (I_if (cval, then_instrs', else_instrs'), aux) :: instrs', seen)
      | instr :: instrs ->
          let instrs', seen = opt seen instrs in
          (instr :: instrs', seen)
      | [] -> ([], seen)
    in
    fun instrs -> fst (opt NameSet.empty instrs)

  let letdef_count = ref 0

  let compile_fun_to_wires ctx (def_annot : unit Ast.def_annot) id slots =
    let l = gen_loc def_annot.loc in

    (* Find the function's type. *)
    let quant, Typ_aux (fn_typ, _) =
      try Env.get_val_spec id ctx.local_env with Type_error.Type_error _ -> Env.get_val_spec id ctx.tc_env
    in
    let params = quant_kopts quant |> List.filter is_typ_kopt |> List.map kopt_kid in

    let arg_typs, ret_typ = match fn_typ with Typ_fn (arg_typs, ret_typ) -> (arg_typs, ret_typ) | _ -> assert false in

    let ctx = { ctx with local_env = Env.add_typquant (id_loc id) quant ctx.tc_env } in

    let arg_ctyps = List.mapi (fun n typ -> (name (mk_id ("a" ^ string_of_int n)), ctyp_of_typ ctx typ)) arg_typs in
    let ret_ctyp = ctyp_of_typ ctx ret_typ in

    let num_args = List.length arg_ctyps in

    let funwire_name = function
      | Arg n -> name (append_id id (Printf.sprintf "_fw_arg%d#" n))
      | Ret -> name (append_id id "_fw_ret#")
      | Invoke -> name (append_id id "_fw_invoke#")
    in

    let funwire_attr_info = function
      | Arg n -> AD_aux (AD_num (Big_int.of_int n), l)
      | Ret -> AD_aux (AD_string "return", l)
      | Invoke -> AD_aux (AD_string "invoke", l)
    in

    let funwire_attr fw =
      mk_def_annot
        ~attrs:
          [(l, "funwire", Some (AD_aux (AD_list [AD_aux (AD_string (string_of_id id), l); funwire_attr_info fw], l)))]
        l ()
    in

    let funwire_ctyp = function Arg n -> snd (List.nth arg_ctyps n) | Ret -> ret_ctyp | Invoke -> CT_bool in

    let slotvector ctyp = if slots > 1 then CT_fvector (slots, ctyp) else ctyp in

    let mk_register fw =
      CDEF_aux (CDEF_register (funwire_name fw, slotvector (funwire_ctyp fw), []), funwire_attr fw)
    in

    let read_slot fw slot =
      if slots > 1 then V_call (Index slot, [V_id (funwire_name fw, CT_fvector (slots, funwire_ctyp fw))])
      else V_id (funwire_name fw, funwire_ctyp fw)
    in

    let write_slot fw slot cval =
      if slots > 1 then (
        let vector_ctyp = CT_fvector (slots, funwire_ctyp fw) in
        iextern l
          (CL_id (funwire_name fw, vector_ctyp))
          (mk_id "internal_vector_update", [])
          [V_id (funwire_name fw, vector_ctyp); V_lit (VL_int (Big_int.of_int slot), CT_fint 64); cval]
      )
      else icopy l (CL_id (funwire_name fw, funwire_ctyp fw)) (V_id (funwire_name fw, funwire_ctyp fw))
    in

    let updates =
      List.init slots (fun slot ->
          [
            iif l
              (V_call (Bnot, [read_slot Invoke slot]))
              ([write_slot Invoke slot (V_lit (VL_bool true, CT_bool))]
              @ List.mapi (fun n (arg, ctyp) -> write_slot (Arg n) slot (V_id (arg, ctyp))) arg_ctyps
              @ [icopy l (CL_id (return, ret_ctyp)) (read_slot Ret slot); iend l]
              )
              [];
          ]
      )
      |> List.concat
    in

    let exn_setup, exn_cval =
      assert_exception l (V_lit (VL_string ("reached unreachable in " ^ string_of_id id), CT_string))
    in

    [mk_register Invoke]
    @ List.init num_args (fun n -> mk_register (Arg n))
    @ [mk_register Ret]
    @ [
        CDEF_aux (CDEF_val (id, params, List.map snd arg_ctyps, ret_ctyp, None), def_annot);
        CDEF_aux
          ( CDEF_fundef
              ( id,
                Return_plain,
                List.map fst arg_ctyps,
                fix_exception ~return:(Some ret_ctyp) ctx (updates @ exn_setup @ [ithrow l exn_cval])
              ),
            mk_def_annot l ()
          );
      ]

  let compile_funcl ctx def_annot id pat guard exp =
    let debug_attr = get_def_attribute "jib_debug" def_annot in
    let mapping_function_attr = get_def_attribute "mapping_function" def_annot in
    let test_no_gmp = get_def_attribute "test_no_gmp" def_annot in

    if Option.is_some debug_attr then (
      let extra = if Option.is_some mapping_function_attr then " (mapping)" else "" in
      prerr_endline Util.("Rewritten source for " ^ string_of_id id ^ extra ^ ":" |> yellow |> bold |> clear);
      prerr_endline (Document.to_string (Pretty_print_sail.doc_exp (Type_check.strip_exp exp)))
    );

    (* Find the function's type. *)
    let quant, Typ_aux (fn_typ, _) =
      try Env.get_val_spec id ctx.local_env with Type_error.Type_error _ -> Env.get_val_spec id ctx.tc_env
    in
    let params = quant_kopts quant |> List.filter is_typ_kopt |> List.map kopt_kid in

    let arg_typs, ret_typ = match fn_typ with Typ_fn (arg_typs, ret_typ) -> (arg_typs, ret_typ) | _ -> assert false in

    (* Handle the argument pattern. *)
    let fundef_label = label "fundef_fail_" in
    let orig_ctx = ctx in
    (* The context must be updated before we call ctyp_of_typ on the argument types. *)
    let ctx = { ctx with local_env = Env.add_typquant (id_loc id) quant ctx.local_env } in
    let ctx = update_coverage_override_def def_annot ctx in

    let arg_ctyps = List.map (ctyp_of_typ ctx) arg_typs in
    let ret_ctyp = ctyp_of_typ ctx ret_typ in

    (* Compile the function arguments as patterns. *)
    let arg_setup, compiled_args, arg_cleanup =
      compile_arg_pats ctx (fun l b -> ijump l b fundef_label) pat arg_ctyps
    in
    let ctx =
      (* We need the primop analyzer to be aware of the function argument types, so put them in ctx *)
      List.fold_left2
        (fun ctx (id, _) ctyp -> { ctx with locals = NameMap.add id (Immutable, ctyp) ctx.locals })
        ctx compiled_args arg_ctyps
    in

    let known_ids = IdSet.fold (fun id -> NameSet.add (name id)) (pat_ids pat) (letbind_ids ctx) in
    let guard_bindings = ref NameSet.empty in
    let guard_instrs =
      match guard with
      | Some guard ->
          let (AE_aux (_, { loc = l; _ }) as guard) = anf guard in
          guard_bindings := aexp_bindings guard;
          let guard_aexp = C.optimize_anf ctx (no_shadow known_ids guard) in
          let guard_setup, guard_call, guard_cleanup = compile_aexp ctx guard_aexp in
          let guard_label = label "guard_" in
          let gs = ngensym () in
          [
            iblock
              ([idecl l CT_bool gs]
              @ guard_setup
              @ [guard_call (CL_id (gs, CT_bool))]
              @ guard_cleanup
              @ [ijump (id_loc id) (V_id (gs, CT_bool)) guard_label; imatch_failure l; ilabel guard_label]
              );
          ]
      | None -> []
    in

    (* Optimize and compile the expression to ANF. *)
    let aexp = C.optimize_anf ctx (no_shadow (NameSet.union known_ids !guard_bindings) (anf exp)) in

    if Option.is_some debug_attr then (
      prerr_endline Util.("ANF for " ^ string_of_id id ^ ":" |> yellow |> bold |> clear);
      prerr_endline (Document.to_string (pp_aexp aexp))
    );

    let compile_body ctx =
      let setup, call, cleanup = compile_aexp ctx aexp in
      let destructure, destructure_cleanup =
        compiled_args |> List.map snd |> combine_destructure_cleanup |> fix_destructure (id_loc id) fundef_label
      in

      let instrs =
        arg_setup @ destructure @ guard_instrs @ setup
        @ [call (CL_id (return, ret_ctyp))]
        @ cleanup @ destructure_cleanup @ arg_cleanup
      in
      let instrs = fix_early_return (exp_loc exp) (CL_id (return, ret_ctyp)) instrs in
      let instrs = unique_names instrs in
      let instrs = fix_exception ~return:(Some ret_ctyp) ctx instrs in
      coverage_function_entry ctx id (exp_loc exp) @ instrs
    in

    let compiled_args = List.map fst compiled_args in
    let instrs = compile_body ctx in

    if Option.is_some debug_attr then (
      let type_string = Util.string_of_list ", " string_of_ctyp arg_ctyps ^ " -> " ^ string_of_ctyp ret_ctyp in
      prerr_endline Util.("IR for " ^ string_of_id id ^ ": " ^ type_string |> yellow |> bold |> clear);
      List.iter (fun instr -> prerr_endline (string_of_instr instr)) instrs
    );

    if Option.is_some test_no_gmp then
      List.iter
        (fun instr ->
          iter_instr
            (function
              | I_aux (I_decl (ctyp, _), (_, l)) | I_aux (I_init (ctyp, _, _), (_, l)) ->
                  if ctyp_equal ctyp CT_lint || ctyp_equal ctyp CT_lbits then
                    raise (Reporting.err_general l "Found GMP large integer or bitvector with test_no_gmp attribute")
              | _ -> ()
              )
            instr
        )
        instrs;

    (* If the function is a mapping, we generate an infallible version (that never causes a match_failure) *)
    let mapping_infallible, return_ctx =
      match mapping_function_attr with
      | Some (attr_l, _) ->
          let instrs =
            compile_body
              { ctx with def_annot = Some (add_def_attribute (gen_loc attr_l) "mapping_infallible" None def_annot) }
          in
          let id = append_id id "_infallible" in
          ( [
              CDEF_aux (CDEF_val (id, params, arg_ctyps, ret_ctyp, None), def_annot);
              CDEF_aux (CDEF_fundef (id, Return_plain, compiled_args, instrs), def_annot);
            ],
            { orig_ctx with valspecs = Bindings.add id (None, arg_ctyps, ret_ctyp, empty_uannot) orig_ctx.valspecs }
          )
      | None -> ([], orig_ctx)
    in

    ([CDEF_aux (CDEF_fundef (id, Return_plain, compiled_args, instrs), def_annot)] @ mapping_infallible, return_ctx)

  (** Compile a Sail toplevel definition into an IR definition **)
  let rec compile_def n total ctx (DEF_aux (aux, _) as def) =
    match aux with
    | DEF_fundef (FD_aux (FD_function (_, _, [FCL_aux (FCL_funcl (id, _), _)]), _)) when !opt_memo_cache ->
        let digest = strip_def def |> Pretty_print_sail.doc_def |> Document.to_string |> Digest.string in
        let cachefile = Filename.concat "_sbuild" ("ccache" ^ Digest.to_hex digest) in
        let cached =
          if Sys.file_exists cachefile then (
            let in_chan = open_in cachefile in
            try
              let compiled = Marshal.from_channel in_chan in
              close_in in_chan;
              Some (compiled, ctx)
            with _ ->
              close_in in_chan;
              None
          )
          else None
        in
        begin
          match cached with
          | Some (compiled, ctx) ->
              Util.progress "Compiling " (string_of_id id) n total;
              (compiled, ctx)
          | None ->
              let compiled, ctx = compile_def' n total ctx def in
              let out_chan = open_out cachefile in
              Marshal.to_channel out_chan compiled [Marshal.Closures];
              close_out out_chan;
              (compiled, { ctx with def_annot = None })
        end
    | _ ->
        let compiled, ctx = compile_def' n total ctx def in
        (compiled, { ctx with def_annot = None })

  and compile_def' n total ctx (DEF_aux (aux, def_annot) as def) =
    let def_env = def_annot.env in
    let def_annot = strip_def_annot def_annot in
    let ctx = { ctx with local_env = def_env; def_annot = Some def_annot } in
    match aux with
    | DEF_register (DEC_aux (DEC_reg (typ, id, None), _)) ->
        let ctyp = ctyp_of_typ ctx typ in
        ( [CDEF_aux (CDEF_register (name id, ctyp, []), def_annot)],
          { ctx with registers = Bindings.add id ctyp ctx.registers }
        )
    | DEF_register (DEC_aux (DEC_reg (typ, id, Some exp), _)) ->
        let ctyp = ctyp_of_typ ctx typ in
        let aexp = C.optimize_anf ctx (no_shadow (letbind_ids ctx) (anf exp)) in
        let setup, call, cleanup = compile_aexp ctx aexp in
        let instrs = setup @ [call (CL_id (name id, ctyp))] @ cleanup in
        let instrs = unique_names instrs in
        ( [CDEF_aux (CDEF_register (name id, ctyp, instrs), def_annot)],
          { ctx with registers = Bindings.add id ctyp ctx.registers }
        )
    | DEF_val (VS_aux (VS_val_spec (_, id, ext), _)) ->
        let quant, Typ_aux (fn_typ, _) = Env.get_val_spec id ctx.tc_env in
        let params = quant_kopts quant |> List.filter is_typ_kopt |> List.map kopt_kid in
        let extern =
          if Env.is_extern id ctx.tc_env ctx.target_name then Some (Env.get_extern id ctx.tc_env ctx.target_name)
          else None
        in
        let arg_typs, ret_typ =
          match fn_typ with Typ_fn (arg_typs, ret_typ) -> (arg_typs, ret_typ) | _ -> assert false
        in
        let ctx' = { ctx with local_env = Env.add_typquant (id_loc id) quant ctx.local_env } in
        let arg_ctyps, ret_ctyp = (List.map (ctyp_of_typ ctx') arg_typs, ctyp_of_typ ctx' ret_typ) in
        ( [CDEF_aux (CDEF_val (id, params, arg_ctyps, ret_ctyp, extern), def_annot)],
          {
            ctx with
            valspecs = Bindings.add id (extern, arg_ctyps, ret_ctyp, uannot_of_def_annot def_annot) ctx.valspecs;
          }
        )
    | DEF_fundef (FD_aux (FD_function (_, _, [FCL_aux (FCL_funcl (id, pexp), _)]), _)) -> (
        Util.progress "Compiling " (string_of_id id) n total;
        match Bindings.find_opt id C.fun_to_wires with
        | Some slots -> (compile_fun_to_wires ctx def_annot id slots, ctx)
        | None -> (
            match pexp with
            | Pat_aux (Pat_exp (pat, exp), _) -> compile_funcl ctx def_annot id pat None exp
            | Pat_aux (Pat_when (pat, guard, exp), _) -> compile_funcl ctx def_annot id pat (Some guard) exp
          )
      )
    | DEF_fundef (FD_aux (FD_function (_, _, []), (l, _))) ->
        raise (Reporting.err_general l "Encountered function with no clauses")
    | DEF_fundef (FD_aux (FD_function (_, _, _ :: _ :: _), (l, _))) ->
        raise (Reporting.err_general l "Encountered function with multiple clauses")
    | DEF_type type_def ->
        let tdef_opt, ctx = compile_type_def ctx type_def in
        (List.map (fun tdef -> CDEF_aux (CDEF_type tdef, def_annot)) (Option.to_list tdef_opt), ctx)
    | DEF_let (LB_aux (LB_val (pat, exp), _)) ->
        let debug_attr = get_def_attribute "jib_debug" def_annot in
        let ctyp = ctyp_of_typ ctx (typ_of_pat pat) in
        let aexp = C.optimize_anf ctx (no_shadow (letbind_ids ctx) (anf exp)) in
        let setup, call, cleanup = compile_aexp ctx aexp in
        let apat = anf_pat ~global:true pat in
        let gs = ngensym () in
        let end_label = label "let_end_" in
        let pre_destructure, destructure, destructure_cleanup, _ =
          compile_match ctx apat (V_id (gs, ctyp)) (fun l b -> ijump l b end_label)
        in
        let gs_setup, gs_cleanup = ([idecl (exp_loc exp) ctyp gs], [iclear ctyp gs]) in
        let bindings =
          List.map (fun (id, env, typ) -> (id, ctyp_of_typ { ctx with local_env = env } typ)) (apat_globals apat)
        in
        let n = !letdef_count in
        incr letdef_count;
        let instrs =
          gs_setup @ setup
          @ [call (CL_id (gs, ctyp))]
          @ cleanup @ pre_destructure @ destructure @ destructure_cleanup @ gs_cleanup
          @ [ilabel end_label]
        in
        let instrs = unique_names instrs in
        if Option.is_some debug_attr then (
          prerr_endline Util.("IR for letbind " ^ string_of_int n |> yellow |> bold |> clear);
          prerr_endline
            (Util.string_of_list ", " (fun (id, ctyp) -> string_of_id id ^ " : " ^ string_of_ctyp ctyp) bindings);
          List.iter (fun instr -> prerr_endline (string_of_instr instr)) instrs
        );
        ( [CDEF_aux (CDEF_let (n, bindings, instrs), def_annot)],
          {
            ctx with
            letbinds = n :: ctx.letbinds;
            letbind_ctyps = List.fold_left (fun ids (id, ctyp) -> Bindings.add id ctyp ids) ctx.letbind_ctyps bindings;
          }
        )
    (* Only DEF_default that matters is default Order, but all order
       polymorphism is specialised by this point. *)
    | DEF_default _ -> ([], ctx)
    (* Overloading resolved by type checker *)
    | DEF_overload _ -> ([], ctx)
    (* Only the parser and sail pretty printer care about this. *)
    | DEF_fixity _ -> ([], ctx)
    | DEF_pragma ("abstract", Pragma_line (id_str, _)) -> ([CDEF_aux (CDEF_pragma ("abstract", id_str), def_annot)], ctx)
    | DEF_pragma ("c_in_main", Pragma_line (source, _)) ->
        ([CDEF_aux (CDEF_pragma ("c_in_main", source), def_annot)], ctx)
    | DEF_pragma ("c_in_main_post", Pragma_line (source, _)) ->
        ([CDEF_aux (CDEF_pragma ("c_in_main_post", source), def_annot)], ctx)
    (* We just ignore any pragmas we don't want to deal with. *)
    | DEF_pragma _ -> ([], ctx)
    (* Termination measures only needed for Coq, and other theorem prover output *)
    | DEF_measure _ -> ([], ctx)
    | DEF_loop_measures _ -> ([], ctx)
    | DEF_internal_mutrec fundefs ->
        let defs = List.map (fun fdef -> mk_def (DEF_fundef fdef) def_env) fundefs in
        List.fold_left
          (fun (cdefs, ctx) def ->
            let cdefs', ctx = compile_def n total ctx def in
            (cdefs @ cdefs', ctx)
          )
          ([], ctx) defs
    | DEF_constraint _ -> ([], ctx)
    (* Scattereds, mapdefs, and event related definitions should be removed by this point *)
    | DEF_scattered _ | DEF_mapdef _ | DEF_outcome _ | DEF_impl _ | DEF_instantiation _ ->
        Reporting.unreachable (def_loc def) __POS__
          ("Could not compile:\n" ^ Document.to_string (Pretty_print_sail.doc_def (strip_def def)))

  let mangle_mono_id id ctx ctyps = append_id id ("<" ^ Util.string_of_list "," (mangle_string_of_ctyp ctx) ctyps ^ ">")

  (* The specialized calls argument keeps track of functions we have
     already specialized, so we don't accidentally specialize them twice
     in a future round of specialization *)
  let rec specialize_functions ?(specialized_calls = ref IdSet.empty) ctx cdefs =
    let polymorphic_functions =
      List.filter_map
        (function
          | CDEF_aux (CDEF_val (id, _, param_ctyps, ret_ctyp, _), _) ->
              if List.exists is_polymorphic param_ctyps || is_polymorphic ret_ctyp then Some id else None
          | _ -> None
          )
        cdefs
      |> IdSet.of_list
    in

    (* First we find all the 'monomorphic calls', places where a
       polymorphic function is applied to only concrete type arguments

       At each such location we remove the type arguments and mangle the
       call name using them *)
    let monomorphic_calls = ref Bindings.empty in
    let collect_monomorphic_calls = function
      | I_aux (I_funcall (clexp, extern, (id, ctyp_args), args), aux)
        when IdSet.mem id polymorphic_functions && not (List.exists is_polymorphic ctyp_args) ->
          monomorphic_calls :=
            Bindings.update id
              (function
                | None -> Some (CTListSet.singleton ctyp_args) | Some calls -> Some (CTListSet.add ctyp_args calls)
                )
              !monomorphic_calls;
          I_aux (I_funcall (clexp, extern, (mangle_mono_id id ctx ctyp_args, []), args), aux)
      | instr -> instr
    in
    let cdefs = List.rev_map (cdef_map_instr collect_monomorphic_calls) cdefs |> List.rev in

    (* Now we duplicate function defintions and type declarations for
       each of the monomorphic calls we just found. *)
    let spec_tyargs = ref Bindings.empty in
    let rec specialize_fundefs ctx prior = function
      | (CDEF_aux (CDEF_val (id, tyargs, param_ctyps, ret_ctyp, extern), def_annot) as orig_cdef) :: cdefs
        when Bindings.mem id !monomorphic_calls ->
          spec_tyargs := Bindings.add id tyargs !spec_tyargs;
          let specialized_specs =
            List.filter_map
              (fun instantiation ->
                let specialized_id = mangle_mono_id id ctx instantiation in
                if not (IdSet.mem specialized_id !specialized_calls) then (
                  let substs =
                    List.fold_left2
                      (fun substs tyarg ty -> KBindings.add tyarg ty substs)
                      KBindings.empty tyargs instantiation
                  in
                  let param_ctyps = List.map (subst_poly substs) param_ctyps in
                  let ret_ctyp = subst_poly substs ret_ctyp in
                  Some (CDEF_aux (CDEF_val (specialized_id, [], param_ctyps, ret_ctyp, extern), def_annot))
                )
                else None
              )
              (CTListSet.elements (Bindings.find id !monomorphic_calls))
          in
          let ctx =
            List.fold_left
              (fun ctx cdef ->
                match cdef with
                | CDEF_aux (CDEF_val (id, _, param_ctyps, ret_ctyp, _), def_annot) ->
                    {
                      ctx with
                      valspecs =
                        Bindings.add id (extern, param_ctyps, ret_ctyp, uannot_of_def_annot def_annot) ctx.valspecs;
                    }
                | cdef -> ctx
              )
              ctx specialized_specs
          in
          specialize_fundefs ctx ((orig_cdef :: specialized_specs) @ prior) cdefs
      | (CDEF_aux (CDEF_fundef (id, heap_return, params, body), def_annot) as orig_cdef) :: cdefs
        when Bindings.mem id !monomorphic_calls ->
          let tyargs = Bindings.find id !spec_tyargs in
          let specialized_fundefs =
            List.filter_map
              (fun instantiation ->
                let specialized_id = mangle_mono_id id ctx instantiation in
                if not (IdSet.mem specialized_id !specialized_calls) then (
                  specialized_calls := IdSet.add specialized_id !specialized_calls;
                  let substs =
                    List.fold_left2
                      (fun substs tyarg ty -> KBindings.add tyarg ty substs)
                      KBindings.empty tyargs instantiation
                  in
                  let body = List.map (map_instr_ctyp (subst_poly substs)) body in
                  Some (CDEF_aux (CDEF_fundef (specialized_id, heap_return, params, body), def_annot))
                )
                else None
              )
              (CTListSet.elements (Bindings.find id !monomorphic_calls))
          in
          specialize_fundefs ctx ((orig_cdef :: specialized_fundefs) @ prior) cdefs
      | cdef :: cdefs -> specialize_fundefs ctx (cdef :: prior) cdefs
      | [] -> (List.rev prior, ctx)
    in

    let cdefs, ctx = specialize_fundefs ctx [] cdefs in

    (* Now we want to remove any polymorphic functions that are
       unreachable from any monomorphic function *)
    let graph = callgraph cdefs in
    let monomorphic_roots =
      List.filter_map
        (function
          | CDEF_aux (CDEF_val (id, _, param_ctyps, ret_ctyp, _), _) ->
              if List.exists is_polymorphic param_ctyps || is_polymorphic ret_ctyp then None else Some id
          | _ -> None
          )
        cdefs
      |> IdGraphNS.of_list
    in
    let monomorphic_reachable = IdGraph.reachable monomorphic_roots IdGraphNS.empty graph in
    let unreachable_polymorphic_functions =
      IdSet.filter (fun id -> not (IdGraphNS.mem id monomorphic_reachable)) polymorphic_functions
    in
    let cdefs =
      List.filter_map
        (function
          | CDEF_aux (CDEF_fundef (id, _, _, _), _) when IdSet.mem id unreachable_polymorphic_functions -> None
          | CDEF_aux (CDEF_val (id, _, _, _, _), _) when IdSet.mem id unreachable_polymorphic_functions -> None
          | cdef -> Some cdef
          )
        cdefs
    in

    (* If we have removed all the polymorphic functions we are done, otherwise go again *)
    if IdSet.is_empty (IdSet.diff polymorphic_functions unreachable_polymorphic_functions) then (cdefs, ctx)
    else specialize_functions ~specialized_calls ctx cdefs

  let contains_struct id cdef =
    cdef_has_ctyp (ctyp_has (function CT_struct (id', _) -> Id.compare id id' = 0 | _ -> false)) cdef

  let contains_variant id cdef =
    cdef_has_ctyp (ctyp_has (function CT_variant (id', _) -> Id.compare id id' = 0 | _ -> false)) cdef

  class fix_variants_visitor ctx typ_id =
    object
      inherit empty_jib_visitor

      method! vctyp =
        function
        | CT_variant (id, args) when Id.compare typ_id id = 0 -> ChangeTo (CT_variant (mangle_mono_id id ctx args, []))
        | CT_struct (id, args) when Id.compare typ_id id = 0 -> ChangeTo (CT_struct (mangle_mono_id id ctx args, []))
        | _ -> DoChildren
    end

  class specialize_constructor_visitor instantiations ctx ctor_id =
    object
      inherit empty_jib_visitor

      method! vctyp _ = SkipChildren
      method! vclexp _ = SkipChildren

      method! vcval =
        function
        | V_ctor_kind (cval, (id, unifiers)) when Id.compare id ctor_id = 0 ->
            change_do_children (V_ctor_kind (cval, (mangle_mono_id id ctx unifiers, [])))
        | V_ctor_unwrap (cval, (id, unifiers), ctor_ctyp) when Id.compare id ctor_id = 0 ->
            change_do_children (V_ctor_unwrap (cval, (mangle_mono_id id ctx unifiers, []), ctor_ctyp))
        | _ -> DoChildren

      method! vinstr =
        function
        | I_aux (I_funcall (clexp, extern, (id, ctyp_args), args), aux) when Id.compare id ctor_id = 0 ->
            instantiations := CTListSet.add ctyp_args !instantiations;
            I_aux (I_funcall (clexp, extern, (mangle_mono_id id ctx ctyp_args, []), args), aux) |> change_do_children
        | _ -> DoChildren
    end

  class specialize_field_visitor instantiations ctx struct_id =
    object
      inherit empty_jib_visitor

      method! vctyp _ = SkipChildren
      method! vclexp _ = SkipChildren
      method! vcval _ = SkipChildren

      method! vinstr =
        function
        | I_aux (I_decl (CT_struct (struct_id', args), _), (_, l)) when Id.compare struct_id struct_id' = 0 ->
            instantiations := CTListSet.add args !instantiations;
            DoChildren
        | _ -> DoChildren
    end

  class scan_variant_visitor instantiations ctx var_id =
    object
      inherit empty_jib_visitor

      method! vctyp =
        function
        | CT_variant (var_id', args) when Id.compare var_id var_id' = 0 ->
            instantiations := CTListSet.add args !instantiations;
            DoChildren
        | _ -> DoChildren
    end

  let rec specialize_variants ctx prior =
    let instantiations = ref CTListSet.empty in
    let fix_variants ctx var_id = visit_ctyp (new fix_variants_visitor ctx var_id :> common_visitor) in

    let specialize_constructor ctx ctor_id =
      visit_cdefs (new specialize_constructor_visitor instantiations ctx ctor_id)
    in

    let specialize_field ctx struct_id = visit_cdefs (new specialize_field_visitor instantiations ctx struct_id) in

    let mangled_pragma orig_id mangled_id =
      CDEF_aux
        ( CDEF_pragma
            ("mangled", Util.zencode_string (string_of_id orig_id) ^ " " ^ Util.zencode_string (string_of_id mangled_id)),
          mk_def_annot (gen_loc (id_loc orig_id)) ()
        )
    in

    function
    | CDEF_aux (CDEF_type (CTD_variant (var_id, params, ctors)), def_annot) :: cdefs when not (Util.list_empty params)
      ->
        let _ = visit_cdefs (new scan_variant_visitor instantiations ctx var_id) prior in
        let _ = visit_cdefs (new scan_variant_visitor instantiations ctx var_id) cdefs in

        let cdefs =
          List.fold_left (fun cdefs (ctor_id, ctyp) -> specialize_constructor ctx ctor_id cdefs) cdefs ctors
        in

        let monomorphized_variants =
          List.map
            (fun inst ->
              let substs = KBindings.of_seq (List.map2 (fun x y -> (x, y)) params inst |> List.to_seq) in
              ( mangle_mono_id var_id ctx inst,
                List.map
                  (fun (ctor_id, ctyp) ->
                    (mangle_mono_id ctor_id ctx inst, fix_variants ctx var_id (subst_poly substs ctyp))
                  )
                  ctors
              )
            )
            (CTListSet.elements !instantiations)
        in
        let ctx =
          List.fold_left
            (fun ctx (id, ctors) ->
              { ctx with variants = Bindings.add id ([], Bindings.of_seq (List.to_seq ctors)) ctx.variants }
            )
            ctx monomorphized_variants
        in
        let mangled_ctors =
          List.map
            (fun (_, monomorphized_ctors) ->
              List.map2
                (fun (ctor_id, _) (monomorphized_id, _) -> mangled_pragma ctor_id monomorphized_id)
                ctors monomorphized_ctors
            )
            monomorphized_variants
          |> List.concat
        in

        let prior = Util.map_if (contains_variant var_id) (cdef_map_ctyp (fix_variants ctx var_id)) prior in
        let cdefs = Util.map_if (contains_variant var_id) (cdef_map_ctyp (fix_variants ctx var_id)) cdefs in

        let ctx = ctx_map_ctyps (fix_variants ctx var_id) ctx in
        let ctx = { ctx with variants = Bindings.remove var_id ctx.variants } in

        specialize_variants ctx
          (List.concat
             (List.map
                (fun (id, ctors) ->
                  [CDEF_aux (CDEF_type (CTD_variant (id, [], ctors)), def_annot); mangled_pragma var_id id]
                )
                monomorphized_variants
             )
          @ mangled_ctors @ prior
          )
          cdefs
    | CDEF_aux (CDEF_type (CTD_struct (struct_id, params, fields)), def_annot) :: cdefs when not (Util.list_empty params)
      ->
        let _ = specialize_field ctx struct_id cdefs in
        let monomorphized_structs =
          List.map
            (fun inst ->
              let substs = List.map2 (fun x y -> (x, y)) params inst |> List.to_seq |> KBindings.of_seq in
              ( mangle_mono_id struct_id ctx inst,
                List.map
                  (fun (field_id, ctyp) -> (field_id, fix_variants ctx struct_id (subst_poly substs ctyp)))
                  fields
              )
            )
            (CTListSet.elements !instantiations)
        in
        let mangled_fields =
          List.map
            (fun (_, monomorphized_fields) ->
              List.map2
                (fun (field_id, _) (monomorphized_id, _) -> mangled_pragma field_id monomorphized_id)
                fields monomorphized_fields
            )
            monomorphized_structs
          |> List.concat
        in

        let prior = Util.map_if (contains_struct struct_id) (cdef_map_ctyp (fix_variants ctx struct_id)) prior in
        let cdefs = Util.map_if (contains_struct struct_id) (cdef_map_ctyp (fix_variants ctx struct_id)) cdefs in
        let ctx = ctx_map_ctyps (fix_variants ctx struct_id) ctx in

        let ctx =
          List.fold_left
            (fun ctx (id, fields) ->
              { ctx with records = Bindings.add id ([], Bindings.of_seq (List.to_seq fields)) ctx.records }
            )
            ctx monomorphized_structs
        in
        let ctx = { ctx with records = Bindings.remove struct_id ctx.records } in

        specialize_variants ctx
          (List.concat
             (List.map
                (fun (id, fields) ->
                  [CDEF_aux (CDEF_type (CTD_struct (id, [], fields)), def_annot); mangled_pragma struct_id id]
                )
                monomorphized_structs
             )
          @ mangled_fields @ prior
          )
          cdefs
    | cdef :: cdefs -> specialize_variants ctx (cdef :: prior) cdefs
    | [] -> (List.rev prior, ctx)

  let make_calls_precise ctx cdefs =
    let constructor_types = ref Bindings.empty in

    let get_function_typ id =
      match Bindings.find_opt id ctx.valspecs with
      | None -> Bindings.find_opt id !constructor_types
      | Some (_, param_ctyps, ret_ctyp, _) -> Some (param_ctyps, ret_ctyp)
    in

    let precise_call call tail =
      match call with
      | I_aux (I_funcall (CR_one clexp, extern_info, (id, ctyp_args), args), ((_, l) as aux)) as instr -> (
          match extern_info with
          | Extern ret_ctyp ->
              if string_of_id id = "sail_cons" then (
                match args with
                | [hd_arg; tl_arg] ->
                    let ctyp_arg = ctyp_suprema (cval_ctyp hd_arg) in
                    if not (ctyp_equal (cval_ctyp hd_arg) ctyp_arg) then (
                      let gs = ngensym () in
                      let cast = [idecl l ctyp_arg gs; icopy l (CL_id (gs, ctyp_arg)) hd_arg] in
                      let cleanup = [iclear ~loc:l ctyp_arg gs] in
                      [
                        iblock
                          (cast
                          @ [
                              I_aux
                                (I_funcall (CR_one clexp, Extern ret_ctyp, (id, []), [V_id (gs, ctyp_arg); tl_arg]), aux);
                            ]
                          @ tail @ cleanup
                          );
                      ]
                    )
                    else instr :: tail
                | _ ->
                    (* cons must have two arguments *)
                    Reporting.unreachable (id_loc id) __POS__ "Invalid cons call"
              )
              else if not (ctyp_equal (clexp_ctyp clexp) ret_ctyp) then (
                let gs = ngensym () in
                let setup = [idecl l ret_ctyp gs] in
                let new_clexp = CL_id (gs, ret_ctyp) in
                let cleanup = [icopy l clexp (V_id (gs, ret_ctyp)); iclear ~loc:l ret_ctyp gs] in
                setup
                @ [I_aux (I_funcall (CR_one new_clexp, Extern ret_ctyp, (id, ctyp_args), args), aux)]
                @ cleanup @ tail
              )
              else instr :: tail
          | Call -> (
              match get_function_typ id with
              | Some (param_ctyps, ret_ctyp) when C.make_call_precise ctx id param_ctyps ret_ctyp ->
                  if List.compare_lengths args param_ctyps <> 0 then
                    Reporting.unreachable (id_loc id) __POS__
                      ("Function call found with incorrect arity: " ^ string_of_id id);
                  let casted_args =
                    List.map2
                      (fun arg param_ctyp ->
                        if not (ctyp_equal (cval_ctyp arg) param_ctyp) then (
                          let gs = ngensym () in
                          let cast = [idecl l param_ctyp gs; icopy l (CL_id (gs, param_ctyp)) arg] in
                          let cleanup = [iclear ~loc:l param_ctyp gs] in
                          (cast, V_id (gs, param_ctyp), cleanup)
                        )
                        else ([], arg, [])
                      )
                      args param_ctyps
                  in
                  let ret_setup, clexp, ret_cleanup =
                    if not (ctyp_equal (clexp_ctyp clexp) ret_ctyp) then (
                      let gs = ngensym () in
                      ( [idecl l ret_ctyp gs],
                        CL_id (gs, ret_ctyp),
                        [icopy l clexp (V_id (gs, ret_ctyp)); iclear ~loc:l ret_ctyp gs]
                      )
                    )
                    else ([], clexp, [])
                  in
                  let casts = List.map (fun (x, _, _) -> x) casted_args |> List.concat in
                  let args = List.map (fun (_, y, _) -> y) casted_args in
                  let cleanup = List.rev_map (fun (_, _, z) -> z) casted_args |> List.concat in
                  [
                    iblock1
                      (casts @ ret_setup
                      @ [I_aux (I_funcall (CR_one clexp, Call, (id, ctyp_args), args), aux)]
                      @ tail @ ret_cleanup @ cleanup
                      );
                  ]
              | Some _ -> instr :: tail
              | None -> instr :: tail
            )
        )
      | instr -> instr :: tail
    in

    let rec precise_calls prior = function
      | (CDEF_aux (CDEF_type (CTD_variant (var_id, _, ctors)), _) as cdef) :: cdefs ->
          List.iter
            (fun (id, ctyp) -> constructor_types := Bindings.add id ([ctyp], CT_variant (var_id, [])) !constructor_types)
            ctors;
          precise_calls (cdef :: prior) cdefs
      | cdef :: cdefs -> precise_calls (cdef_map_funcall precise_call cdef :: prior) cdefs
      | [] -> List.rev prior
    in
    precise_calls [] cdefs

  (* Once we specialize variants, there may be additional type
     dependencies which could be in the wrong order. As such we need
     to sort the type definitions in the list of cdefs. *)
  let sort_ctype_defs ctx reverse cdefs =
    (* Split the cdefs into type definitions and non type definitions *)
    let is_ctype_def = function CDEF_aux (CDEF_type _, _) -> true | _ -> false in
    let unwrap = function CDEF_aux (CDEF_type ctdef, def_annot) -> (ctdef, def_annot) | _ -> assert false in
    let ctype_defs = List.map unwrap (List.filter is_ctype_def cdefs) in
    let cdefs = List.filter (fun cdef -> not (is_ctype_def cdef)) cdefs in

    let ctdef_id = function
      | CTD_abstract (id, _, _) | CTD_enum (id, _) | CTD_struct (id, _, _) | CTD_variant (id, _, _) | CTD_abbrev (id, _)
        ->
          id
    in

    let ctdef_ids = function
      | CTD_enum _ | CTD_abstract _ -> IdSet.empty
      | CTD_abbrev (_, ctyp) -> ctyp_ids ctyp
      | CTD_struct (_, _, ctors) | CTD_variant (_, _, ctors) ->
          List.fold_left (fun ids (_, ctyp) -> IdSet.union (ctyp_ids ctyp) ids) IdSet.empty ctors
    in

    (* Create a reverse (i.e. from types to the types that are dependent
       upon them) id graph of dependencies between types *)
    let module IdGraph = Graph.Make (Id) in
    let graph =
      List.fold_left
        (fun g (ctdef, _) ->
          List.fold_left
            (fun g id -> IdGraph.add_edge id (ctdef_id ctdef) g)
            (IdGraph.add_edges (ctdef_id ctdef) [] g) (* Make sure even types with no dependencies are in graph *)
            (IdSet.elements (ctdef_ids ctdef))
        )
        IdGraph.empty ctype_defs
    in

    (* Then select the ctypes in the correct order as given by the topsort *)
    let ids = IdGraph.topsort graph in
    let ctype_defs =
      List.map
        (fun id ->
          let ctdef, def_annot = List.find (fun (ctdef, _) -> Id.compare (ctdef_id ctdef) id = 0) ctype_defs in
          CDEF_aux (CDEF_type ctdef, def_annot)
        )
        ids
    in

    (if reverse then List.rev ctype_defs else ctype_defs) @ cdefs

  let unit_tests_of_ast ast =
    List.fold_left
      (fun ids -> function
        | DEF_aux (DEF_val (VS_aux (VS_val_spec (_, id, _), _)), def_annot)
          when Option.is_some (get_def_attribute "test" def_annot) ->
            IdSet.add id ids
        | _ -> ids
        )
      IdSet.empty ast.defs
    |> IdSet.elements

  let toplevel_lets_of_ast ast =
    let toplevel_lets_of_def = function
      | DEF_aux (DEF_let (LB_aux (LB_val (pat, _), _)), _) -> pat_ids pat
      | _ -> IdSet.empty
    in
    let toplevel_lets_of_defs defs = List.fold_left IdSet.union IdSet.empty (List.map toplevel_lets_of_def defs) in
    toplevel_lets_of_defs ast.defs |> IdSet.elements

  class static_visitor statics =
    object
      inherit empty_jib_visitor

      method! vctyp _ = SkipChildren
      method! vclexp _ = SkipChildren
      method! vcval _ = SkipChildren

      method! vinstr =
        function
        | I_aux (I_init (ctyp, id, Init_static VL_undefined), (_, l)) ->
            statics := (l, ctyp, id, None) :: !statics;
            ChangeTo (Printf.ksprintf icomment "lifted %s" (string_of_name id))
        | I_aux (I_init (ctyp, id, Init_static vl), (_, l)) ->
            statics := (l, ctyp, id, Some vl) :: !statics;
            ChangeTo (Printf.ksprintf icomment "lifted %s" (string_of_name id))
        | _ -> DoChildren
    end

  let lift_statics cdefs =
    List.map
      (fun cdef ->
        let statics = ref [] in
        let cdef = visit_cdef (new static_visitor statics) cdef in
        List.rev_map
          (fun (l, ctyp, id, vl_opt) ->
            let annot = mk_def_annot l () |> add_def_attribute l "early_init" None in
            match vl_opt with
            | None -> CDEF_aux (CDEF_register (id, ctyp, []), annot)
            | Some vl -> CDEF_aux (CDEF_register (id, ctyp, [icopy l (CL_id (id, ctyp)) (V_lit (vl, ctyp))]), annot)
          )
          !statics
        @ [cdef]
      )
      cdefs
    |> List.concat

  let is_def_constraint = function DEF_aux (DEF_constraint _, _) -> true | _ -> false

  let first_env final_env = function [] -> final_env | DEF_aux (_, def_annot) :: _ -> def_annot.env

  (* This function helps optimise abstract types in the following way,
     if we see:

     {@sail[
       type x = ...
       constraint ...
       constraint ...
     ]}

     Then we move the typing environment from after the final
     constraint up to the [type], ensuring we pick the most optimised
     representation for that type declaration we safely can. *)
  let rec move_constraint_contexts final_env acc = function
    | DEF_aux (DEF_type tdef, def_annot) :: defs ->
        let constraints, rest = Util.take_drop is_def_constraint defs in
        let env = first_env final_env rest in
        move_constraint_contexts final_env
          (List.rev constraints @ [DEF_aux (DEF_type tdef, { def_annot with env })] @ acc)
          rest
    | def :: defs -> move_constraint_contexts final_env (def :: acc) defs
    | [] -> List.rev acc

  let compile_ast ctx ast =
    let module G = Graph.Make (Callgraph.Node) in
    let g = Callgraph.graph_of_ast ast in
    let module NodeSet = Set.Make (Callgraph.Node) in
    (* Get the list of unit tests (valspecs with $[test]), so we can
       add them to the list of roots to avoid pruning them as
       dead-code. *)
    let unit_tests = unit_tests_of_ast ast in

    let roots =
      Specialize.get_initial_calls () @ unit_tests |> List.map (fun id -> Callgraph.Function id) |> NodeSet.of_list
    in
    let roots = IdSet.fold (fun id roots -> NodeSet.add (Callgraph.Type id) roots) C.preserve_types roots in
    let roots = NodeSet.add (Callgraph.Type (mk_id "exception")) roots in
    let roots =
      Bindings.fold (fun typ_id _ roots -> NodeSet.add (Callgraph.Type typ_id) roots) (Env.get_enums ctx.tc_env) roots
    in
    let roots =
      NodeSet.union (toplevel_lets_of_ast ast |> List.map (fun id -> Callgraph.Letbind id) |> NodeSet.of_list) roots
    in

    let g = G.prune roots NodeSet.empty g in
    let ast = Callgraph.filter_ast NodeSet.empty g ast in

    if !opt_memo_cache then (
      try
        if Sys.is_directory "_sbuild" then ()
        else raise (Reporting.err_general Parse_ast.Unknown "_sbuild exists, but is a file not a directory!")
      with Sys_error _ -> Unix.mkdir "_sbuild" 0o775
    )
    else ();

    let total = List.length ast.defs in
    let _, chunks, ctx =
      List.fold_left
        (fun (n, chunks, ctx) def ->
          let defs, ctx = compile_def n total ctx def in
          (n + 1, defs :: chunks, ctx)
        )
        (1, [], ctx)
        (move_constraint_contexts ctx.tc_env [] ast.defs)
    in
    let cdefs = List.concat (List.rev chunks) in

    (* If we don't have an exception type, add a dummy one *)
    let cdefs, ctx =
      if not (Bindings.mem (mk_id "exception") ctx.variants) then
        if C.assert_to_exception then (
          let assertion_failed = mk_id "__assertion_failed#" in
          ( CDEF_aux
              ( CDEF_type (CTD_variant (mk_id "exception", [], [(assertion_failed, CT_string)])),
                mk_def_annot Parse_ast.Unknown ()
              )
            :: cdefs,
            {
              ctx with
              variants =
                Bindings.add (mk_id "exception") ([], Bindings.singleton assertion_failed CT_string) ctx.variants;
            }
          )
        )
        else (
          let dummy_exn = mk_id "__dummy_exn#" in
          ( CDEF_aux
              ( CDEF_type (CTD_variant (mk_id "exception", [], [(dummy_exn, CT_unit)])),
                mk_def_annot Parse_ast.Unknown ()
              )
            :: cdefs,
            {
              ctx with
              variants = Bindings.add (mk_id "exception") ([], Bindings.singleton dummy_exn CT_unit) ctx.variants;
            }
          )
        )
      else (cdefs, ctx)
    in
    let cdefs, ctx = specialize_functions ctx cdefs in
    let cdefs = sort_ctype_defs ctx true cdefs in
    let cdefs, ctx = specialize_variants ctx [] cdefs in
    let cdefs = make_calls_precise ctx cdefs in
    let cdefs = sort_ctype_defs ctx false cdefs in
    let cdefs = lift_statics cdefs in
    (cdefs, ctx)
end
