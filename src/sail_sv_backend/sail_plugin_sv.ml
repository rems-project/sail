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
(*    Louis-Emile Ploix                                                     *)
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
open Value2
open PPrint
open Printf
open Smt_exp
open Interactive.State

open Sv_optimize

module StringSet = Util.StringSet
module R = Jib_sv

let opt_output_dir = ref None

let opt_includes = ref []

let opt_toplevel = ref "main"

type verilate_mode = Verilator_none | Verilator_compile | Verilator_run

let opt_verilate = ref Verilator_none
let opt_verilate_args = ref None
let opt_verilate_cflags = ref None
let opt_verilate_ldflags = ref None
let opt_verilate_link_sail_runtime = ref false
let opt_verilate_jobs = ref 0

let append_flag opt flag = match !opt with None -> opt := Some flag | Some flags -> opt := Some (flags ^ " " ^ flag)

let opt_line_directives = ref false

let opt_comb = ref false

let opt_inregs = ref false
let opt_outregs = ref false

let opt_max_unknown_integer_width = ref 128
let opt_max_unknown_bitvector_width = ref 128

let opt_no_strings = ref false
let opt_no_packed = ref false
let opt_no_assertions = ref false
let opt_never_pack_unions = ref false
let opt_padding = ref false
let opt_nomem = ref false

let opt_unreachable = ref []
let opt_fun2wires = ref []

let opt_dpi_sets = ref StringSet.empty

let opt_int_specialize = ref None

let opt_disable_optimizations = ref false

let verilog_options =
  [
    ( Flag.create ~prefix:["sv"] ~arg:"path" "output_dir",
      Arg.String (fun s -> opt_output_dir := Some s),
      "set the output directory for generated SystemVerilog files"
    );
    ( Flag.create ~prefix:["sv"] ~arg:"file" "include",
      Arg.String (fun s -> opt_includes := s :: !opt_includes),
      "add include directive to generated SystemVerilog file"
    );
    ( Flag.create ~prefix:["sv"] ~arg:"id" "toplevel",
      Arg.String
        (fun s ->
          Specialize.add_initial_calls (IdSet.singleton (mk_id s));
          opt_toplevel := s
        ),
      "Sail function to use as toplevel module"
    );
    ( Flag.create ~prefix:["sv"; "verilate"] ~arg:"compile|run" ~override:"sv_verilate" "mode",
      Arg.String
        (fun opt ->
          if opt = "run" then opt_verilate := Verilator_run
          else if opt = "compile" then opt_verilate := Verilator_compile
          else
            raise
              (Reporting.err_general Parse_ast.Unknown
                 "Invalid argument for -sv_verilate option. Valid options are either 'run' or 'compile'."
              )
        ),
      "Invoke verilator on generated output"
    );
    ( Flag.create ~prefix:["sv"; "verilate"] ~arg:"string" "args",
      Arg.String (fun s -> append_flag opt_verilate_args s),
      "Extra arguments to pass to verilator"
    );
    ( Flag.create ~prefix:["sv"; "verilate"] ~arg:"string" "cflags",
      Arg.String (fun s -> append_flag opt_verilate_cflags s),
      "Verilator CFLAGS argument"
    );
    ( Flag.create ~prefix:["sv"; "verilate"] ~arg:"string" "ldflags",
      Arg.String (fun s -> append_flag opt_verilate_ldflags s),
      "Verilator LDFLAGS argument"
    );
    ( Flag.create ~prefix:["sv"; "verilate"] "link_sail_runtime",
      Arg.Set opt_verilate_link_sail_runtime,
      "Link the Sail C runtime with the generated verilator C++"
    );
    ( Flag.create ~prefix:["sv"; "verilate"] ~arg:"n" "jobs",
      Arg.Int (fun i -> opt_verilate_jobs := i),
      "Provide the -j option to verilator"
    );
    (Flag.create ~prefix:["sv"] "lines", Arg.Set opt_line_directives, "output `line directives");
    (Flag.create ~prefix:["sv"] "comb", Arg.Set opt_comb, "output an always_comb block instead of initial block");
    (Flag.create ~prefix:["sv"] "inregs", Arg.Set opt_inregs, "take register values from inputs");
    (Flag.create ~prefix:["sv"] "outregs", Arg.Set opt_outregs, "output register values");
    ( Flag.create ~prefix:["sv"] ~arg:"n" "int_size",
      Arg.Int (fun i -> opt_max_unknown_integer_width := i),
      "set the maximum width for unknown integers"
    );
    ( Flag.create ~prefix:["sv"] ~arg:"n" "bits_size",
      Arg.Int (fun i -> opt_max_unknown_bitvector_width := i),
      "set the maximum width for bitvectors with unknown width"
    );
    (Flag.create ~prefix:["sv"] "no_strings", Arg.Set opt_no_strings, "don't emit any strings, instead emit units");
    (Flag.create ~prefix:["sv"] "no_packed", Arg.Set opt_no_packed, "don't emit packed datastructures");
    (Flag.create ~prefix:["sv"] "no_assertions", Arg.Set opt_no_assertions, "ignore all Sail asserts");
    (Flag.create ~prefix:["sv"] "never_pack_unions", Arg.Set opt_never_pack_unions, "never emit a packed union");
    (Flag.create ~prefix:["sv"] "padding", Arg.Set opt_padding, "add padding on packed unions");
    ( Flag.create ~prefix:["sv"] ~arg:"functionname" "unreachable",
      Arg.String (fun fn -> opt_unreachable := fn :: !opt_unreachable),
      "Mark function as unreachable."
    );
    (Flag.create ~prefix:["sv"] "nomem", Arg.Set opt_nomem, "don't emit a dynamic memory implementation");
    ( Flag.create ~prefix:["sv"] ~arg:"functionname" "fun2wires",
      Arg.String (fun fn -> opt_fun2wires := fn :: !opt_fun2wires),
      "Use input/output ports instead of emitting a function call"
    );
    ( Flag.create ~prefix:["sv"] ~arg:"n" "specialize",
      Arg.Int (fun i -> opt_int_specialize := Some i),
      "Run n specialization passes on Sail Int-kinded type variables"
    );
    ( Flag.create ~prefix:["sv"] "disable_optimizations",
      Arg.Set opt_disable_optimizations,
      "disable SystemVerilog specific optimizations"
    );
    ( Flag.create ~prefix:["sv"] ~arg:"set" "dpi",
      Arg.String (fun s -> opt_dpi_sets := StringSet.add s !opt_dpi_sets),
      "Use SystemVerilog DPI-C for a set of primitives (e.g. memory)"
    );
  ]

let verilog_rewrites =
  let open Rewrites in
  [
    ("instantiate_outcomes", [String_arg "systemverilog"]);
    ("realize_mappings", []);
    ("remove_vector_subrange_pats", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("truncate_hex_literals", []);
    ("mono_rewrites", [If_flag opt_mono_rewrites]);
    ("recheck_defs", [If_flag opt_mono_rewrites]);
    ("toplevel_nexps", [If_mono_arg]);
    ("monomorphise", [String_arg "systemverilog"; If_mono_arg]);
    ("atoms_to_singletons", [String_arg "systemverilog"; If_mono_arg]);
    ("recheck_defs", [If_mono_arg]);
    ("undefined", [Bool_arg false]);
    ("vector_string_pats_to_bit_list", []);
    ("remove_not_pats", []);
    ("remove_vector_concat", []);
    ("remove_bitvector_pats", []);
    ("pattern_literals", [Literal_arg "all"]);
    ("tuple_assignments", []);
    ("vector_concat_assignments", []);
    ("simple_struct_assignments", []);
    ("split", [String_arg "execute"]);
    ("exp_lift_assign", []);
    ("merge_function_clauses", []);
    ("recheck_defs", []);
    ("constant_fold", [String_arg "systemverilog"]);
    ("unroll_constant_loops", [If_flag opt_unroll_loops]);
  ]

module type JIB_CONFIG = sig
  val make_call_precise : Jib_compile.ctx -> id -> bool
end

module Verilog_config (C : JIB_CONFIG) : Jib_compile.CONFIG = struct
  open Type_check
  open Jib_compile

  let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
  let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))

  let rec convert_typ ctx typ =
    let (Typ_aux (typ_aux, l) as typ) = Env.expand_synonyms ctx.local_env typ in
    match typ_aux with
    | Typ_id id when string_of_id id = "bit" -> CT_bit
    | Typ_id id when string_of_id id = "bool" -> CT_bool
    | Typ_id id when string_of_id id = "int" -> CT_lint
    | Typ_id id when string_of_id id = "nat" -> CT_lint
    | Typ_id id when string_of_id id = "unit" -> CT_unit
    | Typ_id id when string_of_id id = "string" -> CT_string
    | Typ_id id when string_of_id id = "string_literal" -> CT_string
    | Typ_id id when string_of_id id = "real" -> CT_real
    | Typ_id id when string_of_id id = "float16" -> CT_float 16
    | Typ_id id when string_of_id id = "float32" -> CT_float 32
    | Typ_id id when string_of_id id = "float64" -> CT_float 64
    | Typ_id id when string_of_id id = "float128" -> CT_float 128
    | Typ_id id when string_of_id id = "float_rounding_mode" -> CT_rounding_mode
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
            | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _) when Big_int.equal n m -> CT_constant n
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
        match solve_unique ctx.local_env n with Some n -> CT_fbits (Big_int.to_int n) | _ -> CT_lbits
      end
    | Typ_app (id, [A_aux (A_nexp n, _); A_aux (A_typ typ, _)]) when string_of_id id = "vector" -> begin
        match nexp_simp n with
        | Nexp_aux (Nexp_constant c, _) -> CT_fvector (Big_int.to_int c, convert_typ ctx typ)
        | _ -> CT_vector (convert_typ ctx typ)
      end
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
        CT_variant (id, Bindings.find id ctx.variants |> snd |> Bindings.bindings) |> transparent_newtype ctx
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
        CT_variant (id, Bindings.map fix_ctyp ctors |> Bindings.bindings) |> transparent_newtype ctx
    | Typ_id id when Bindings.mem id ctx.enums -> CT_enum (id, Bindings.find id ctx.enums |> IdSet.elements)
    | Typ_tuple typs -> CT_tup (List.map (convert_typ ctx) typs)
    | Typ_exist _ -> begin
        (* Use Type_check.destruct_exist when optimising with SMT, to
           ensure that we don't cause any type variable clashes in
           local_env, and that we can optimize the existential based
           upon it's constraints. *)
        match destruct_exist (Env.expand_synonyms ctx.local_env typ) with
        | Some (kids, nc, typ) ->
            let env = add_existential l kids nc ctx.local_env in
            convert_typ { ctx with local_env = env } typ
        | None -> raise (Reporting.err_unreachable l __POS__ "Existential cannot be destructured!")
      end
    | Typ_var kid -> CT_poly kid
    | _ -> Reporting.unreachable l __POS__ ("No C type for type " ^ string_of_typ typ)

  let optimize_anf _ aexp = aexp

  let unroll_loops = Some 64
  let specialize_calls = false
  let make_call_precise ctx id _ _ = C.make_call_precise ctx id
  let ignore_64 = true
  let struct_value = false
  let tuple_value = false
  let track_throw = false
  let branch_coverage = None
  let use_real = false
  let use_void = false
  let eager_control_flow = true
  let preserve_types = IdSet.empty
end

let register_types cdefs =
  List.fold_left
    (fun acc cdef -> match cdef with CDEF_aux (CDEF_register (id, ctyp, _), _) -> Bindings.add id ctyp acc | _ -> acc)
    Bindings.empty cdefs

let jib_of_ast make_call_precise env ast effect_info =
  let open Jib_compile in
  let module Jibc = Make (Verilog_config (struct
    let make_call_precise = make_call_precise
  end)) in
  let ctx = initial_ctx env effect_info in
  Jibc.compile_ast ctx ast

let wrap_module pre mod_name ins_outs doc =
  pre ^^ hardline ^^ string "module" ^^ space ^^ string mod_name
  ^^ parens (nest 4 (hardline ^^ separate (comma ^^ hardline) ins_outs) ^^ hardline)
  ^^ semi
  ^^ nest 4 (hardline ^^ doc)
  ^^ hardline ^^ string "endmodule" ^^ hardline

let verilator_cpp_wrapper name =
  if not !opt_verilate_link_sail_runtime then
    [
      sprintf "#include \"V%s.h\"" name;
      "#include \"verilated.h\"";
      "int main(int argc, char** argv) {";
      "    VerilatedContext* contextp = new VerilatedContext;";
      "    contextp->commandArgs(argc, argv);";
      sprintf "    V%s* top = new V%s{contextp};" name name;
      "    while (!contextp->gotFinish()) { top -> eval(); }";
      "    delete top;";
      "    delete contextp;";
      "    return 0;";
      "}";
    ]
  else
    [
      sprintf "#include \"V%s.h\"" name;
      "#include \"verilated.h\"";
      "#include \"rts.h\"";
      "int main(int argc, char** argv) {";
      "    VerilatedContext* contextp = new VerilatedContext;";
      (* "    contextp->commandArgs(argc, argv);"; *)
      "    setup_rts();";
      "    process_arguments(argc, argv);";
      sprintf "    V%s* top = new V%s{contextp};" name name;
      "    while (!contextp->gotFinish()) { top -> eval(); }";
      "    cleanup_rts();";
      "    delete top;";
      "    delete contextp;";
      "    return 0;";
      "}";
    ]

(*
let make_genlib_file filename =
  let common_primops =
    if !opt_no_strings then
      Generate_primop.common_primops_stubs !opt_max_unknown_bitvector_width !opt_max_unknown_integer_width
    else Generate_primop.common_primops !opt_max_unknown_bitvector_width !opt_max_unknown_integer_width
  in
  let defs = Generate_primop.get_generated_primops () in
  let ((out_chan, _, _, _) as file_info) = Util.open_output_with_check_unformatted !opt_output_dir filename in
  output_string out_chan "`ifndef SAIL_LIBRARY_GENERATED\n";
  output_string out_chan "`define SAIL_LIBRARY_GENERATED\n\n";
  output_string out_chan common_primops;
  List.iter
    (fun def ->
      List.iter
        (fun line ->
          output_string out_chan line;
          output_char out_chan '\n'
        )
        def;
      output_char out_chan '\n'
    )
    defs;
  output_string out_chan "`endif\n";
  Util.close_output_with_check file_info
   *)

let verilog_target out_opt { ast; effect_info; env; default_sail_dir; _ } =
  let module SV = Jib_sv.Make (struct
    let max_unknown_integer_width = !opt_max_unknown_integer_width
    let max_unknown_bitvector_width = !opt_max_unknown_bitvector_width
    let line_directives = !opt_line_directives
    let no_strings = !opt_no_strings
    let no_packed = !opt_no_packed
    let no_assertions = !opt_no_assertions
    let never_pack_unions = !opt_never_pack_unions
    let union_padding = !opt_padding
    let unreachable = !opt_unreachable
    let comb = !opt_comb
    let ignore = !opt_fun2wires
    let dpi_sets = !opt_dpi_sets
  end) in
  let open SV in
  let sail_dir = Reporting.get_sail_dir default_sail_dir in
  let sail_sv_libdir = Filename.concat (Filename.concat sail_dir "lib") "sv" in
  let out = match out_opt with None -> "out" | Some name -> name in

  let ast, env, effect_info =
    let open Specialize in
    match !opt_int_specialize with
    | Some num_passes -> specialize_passes num_passes int_specialization env ast effect_info
    | None -> (ast, env, effect_info)
  in

  let cdefs, ctx = jib_of_ast SV.make_call_precise env ast effect_info in

  let cdefs, ctx = Jib_optimize.remove_tuples cdefs ctx in
  let cdefs = Jib_optimize.remove_mutrec cdefs in
  let registers = register_types cdefs in

  let include_doc =
    (if !opt_no_strings then string "`define SAIL_NOSTRINGS" ^^ hardline else empty)
    ^^ List.fold_left
         (fun doc set -> ksprintf string "SAIL_DPI_%s" (String.uppercase_ascii set) ^^ hardline)
         empty (StringSet.elements !opt_dpi_sets)
    ^^ string "`include \"sail.sv\"" ^^ hardline
    ^^ ksprintf string "`include \"sail_genlib_%s.sv\"" out
    ^^ (if !opt_nomem then empty else hardline ^^ string "`include \"sail_memory.sv\"")
    ^^ hardline
    ^^ separate_map hardline (fun file -> ksprintf string "`include \"%s\"" file) !opt_includes
    ^^ twice hardline
  in

  let exception_vars =
    string "bit sail_reached_unreachable;" ^^ hardline ^^ string "bit sail_have_exception;" ^^ hardline
    ^^ (if !opt_no_strings then string "sail_unit" else string "string")
    ^^ space ^^ string "sail_throw_location;" ^^ twice hardline
  in

  let spec_info = Jib_sv.collect_spec_info ctx cdefs in

  let svir, fn_ctyps =
    List.fold_left
      (fun (defs, fn_ctyps) cdef ->
        let defs', fn_ctyps = svir_cdef spec_info ctx fn_ctyps cdef in
        (List.rev defs' @ defs, fn_ctyps)
      )
      ([], Bindings.empty) cdefs
  in
  let svir = List.rev svir in
  let svir_types, svir = List.partition Sv_ir.is_typedef svir in
  let library_svir = SV.Primops.get_generated_library_defs () in
  let toplevel_svir = [Sv_ir.mk_def (Sv_ir.SVD_module (SV.toplevel_module (mk_id !opt_toplevel) spec_info fn_ctyps))] in

  let svir = library_svir @ svir @ toplevel_svir in

  let svir =
    if not !opt_disable_optimizations then
      svir |> remove_unit_ports |> remove_unused_variables |> simplify_smt |> remove_unused_variables |> simplify_smt
      |> remove_unused_variables |> remove_nulls |> simplify_smt |> insert_case_expressions
    else svir
  in

  let doc =
    let base = Generate_primop2.basic_defs !opt_max_unknown_bitvector_width !opt_max_unknown_integer_width in
    let reg_ref_enums, reg_ref_functions = sv_register_references spec_info in
    Util.fold_left_last
      (fun last doc set ->
        ksprintf string "`define SAIL_DPI_%s" (String.uppercase_ascii set) ^^ if last then twice hardline else hardline
      )
      empty (StringSet.elements !opt_dpi_sets)
    ^^ string base ^^ string "`include \"sail_modules.sv\"" ^^ twice hardline
    ^^ separate_map (twice hardline) (pp_def None) svir_types
    ^^ twice hardline ^^ reg_ref_enums ^^ reg_ref_functions
    ^^ separate_map (twice hardline) (pp_def None) svir
  in

  (*
  let reg_ref_enums, reg_ref_functions = sv_register_references cdefs in
  let out_doc = out_doc ^^ reg_ref_enums in
  let in_doc = reg_doc ^^ reg_ref_functions ^^ in_doc in

  let mk_wire_fun nm =
    let id = mk_id nm in
    match Bindings.find_opt id fn_ctyps with
    | None -> (empty, [], [])
    | Some (arg_typs, ret_ty) ->
        let arg_nms = List.mapi (fun i _ -> mk_id ("a" ^ string_of_int i)) arg_typs in
        let real_name = if ctx_is_extern id ctx then "sail_" ^ ctx_get_extern id ctx else string_of_id id in
        let invoke_flag = string (nm ^ "_sail_invoke") in
        let result = string (nm ^ "_sail_invoke_ret") in
        let arg_out i = string (nm ^ "_sail_invoke_arg_" ^ string_of_int i) in
        let fun_body =
          string "if (" ^^ invoke_flag
          ^^ string ") sail_reached_unreachable = 1;"
          ^^ hardline ^^ invoke_flag ^^ string " = 1;" ^^ hardline
          ^^ (arg_nms
             |> List.mapi (fun i arg -> arg_out i ^^ string " = " ^^ string (string_of_id arg) ^^ semi ^^ hardline)
             |> separate empty
             )
          ^^ string "return " ^^ result ^^ string ";"
        in
        ( sv_fundef_with ctx real_name arg_nms arg_typs ret_ty fun_body ^^ twice hardline,
          separate space [string "output"; string "bit"; invoke_flag]
          :: separate space [string "input"; string (fst (sv_ctyp ret_ty)); result]
          :: List.mapi (fun i typ -> separate space [string "output"; string (fst (sv_ctyp typ)); arg_out i]) arg_typs,
          [invoke_flag ^^ string " = 0;"]
        )
  in

  let wire_funs, wire_fun_ports, wire_invoke_inits =
    List.fold_right
      (fun nm (code, ports, inits) ->
        let new_code, new_ports, new_inits = mk_wire_fun nm in
        (new_code ^^ code, new_ports @ ports, new_inits @ inits)
      )
      !opt_fun2wires (empty, [], [])
  in

  let setup_function =
    string "function automatic void sail_setup();"
    ^^ nest 4
         (hardline ^^ string "sail_reached_unreachable = 0;" ^^ hardline ^^ string "sail_have_exception = 0;"
        ^^ hardline ^^ separate hardline wire_invoke_inits ^^ hardline
         ^^ separate_map (semi ^^ hardline) (fun call -> string call ^^ string "()") (List.rev setup_calls)
         )
    ^^ semi ^^ hardline ^^ string "endfunction" ^^ twice hardline
  in

  let main_recv_inputs =
    if !opt_inregs then
      separate empty
        (List.filter_map
           (function
             | CDEF_aux (CDEF_register (id, ctyp, _), _) ->
                 Some (pp_id id ^^ space ^^ equals ^^ space ^^ pp_id id ^^ string "_in" ^^ semi ^^ hardline)
             | _ -> None
             )
           cdefs
        )
    else empty
  in

  let main_set_outputs =
    if !opt_inregs then
      separate empty
        (List.filter_map
           (function
             | CDEF_aux (CDEF_register (id, ctyp, _), _) ->
                 Some (pp_id id ^^ string "_out" ^^ space ^^ equals ^^ space ^^ pp_id id ^^ semi ^^ hardline)
             | _ -> None
             )
           cdefs
        )
    else empty
  in

  let main =
    List.find_opt (function CDEF_aux (CDEF_fundef (id, _, _, _), _) -> pp_id_string id = "main" | _ -> false) cdefs
  in
  let main_args, main_result, module_main_in_out = main_args main fn_ctyps in

  let invoke_main_body =
    hardline
    ^^ (if Option.is_none main_result then string "sail_unit u;" ^^ hardline else empty)
    ^^ string "sail_setup();" ^^ hardline ^^ string "$display(\"TEST START\");" ^^ hardline ^^ main_recv_inputs
    ^^ Option.value main_result ~default:(string "u")
    ^^ string " = main("
    ^^ separate (comma ^^ space) main_args
    ^^ string ");" ^^ hardline ^^ main_set_outputs ^^ string "$display(\"TEST END\");"
  in

  let invoke_main =
    if not !opt_comb then
      string "initial" ^^ space ^^ string "begin" ^^ nest 4 invoke_main_body ^^ hardline ^^ string "$finish;"
      ^^ hardline ^^ string "end"
    else string "always_comb" ^^ space ^^ string "begin" ^^ nest 4 invoke_main_body ^^ hardline ^^ string "end"
  in

  let inputs =
    if !opt_inregs then
      List.filter_map
        (function
          | CDEF_aux (CDEF_register (id, ctyp, _), _) ->
              Some (string "input" ^^ space ^^ wrap_type ctyp (pp_id id ^^ string "_in"))
          | _ -> None
          )
        cdefs
    else []
  in

  let outputs =
    if !opt_inregs then
      List.filter_map
        (function
          | CDEF_aux (CDEF_register (id, ctyp, _), _) ->
              Some (string "output" ^^ space ^^ wrap_type ctyp (pp_id id ^^ string "_out"))
          | _ -> None
          )
        cdefs
    else []
  in
  let sv_output =
    Pretty_print_sail.Document.to_string
      (wrap_module out_doc ("sail_" ^ out)
         (inputs @ outputs @ wire_fun_ports @ module_main_in_out)
         (in_doc ^^ wire_funs ^^ setup_function ^^ invoke_main)
      )
  in
     *)
  let sv_output = Pretty_print_sail.Document.to_string doc in

  (* make_genlib_file (Filename.concat (Filename.dirname out) (sprintf "sail_genlib_%s.sv" (Filename.basename out))); *)
  let file_info = Util.open_output_with_check ?directory:!opt_output_dir (out ^ ".sv") in
  output_string file_info.channel sv_output;
  Util.close_output_with_check file_info;

  begin
    match !opt_verilate with
    | Verilator_compile | Verilator_run ->
        let file_info = Util.open_output_with_check ?directory:!opt_output_dir ("sim_" ^ out ^ ".cpp") in
        List.iter
          (fun line ->
            output_string file_info.channel line;
            output_char file_info.channel '\n'
          )
          (verilator_cpp_wrapper "sail_toplevel");
        Util.close_output_with_check file_info;

        let extra = match !opt_verilate_args with None -> "" | Some args -> " " ^ args in
        let cflags = match !opt_verilate_cflags with None -> "" | Some args -> sprintf " -CFLAGS \"%s\"" args in
        let ldflags = match !opt_verilate_ldflags with None -> "" | Some args -> sprintf " -LDFLAGS \"%s\"" args in

        (* Verilator sometimes just spuriously returns non-zero exit
           codes even when it suceeds, so we don't use system_checked
           here, and just hope for the best. *)
        let verilator_command =
          sprintf
            "verilator --cc --exe --build -j %d --top-module sail_toplevel -I%s --Mdir %s_obj_dir sim_%s.cpp \
             %s.sv%s%s%s"
            !opt_verilate_jobs (Filename.quote sail_sv_libdir) out out out extra cflags ldflags
        in
        print_endline ("Verilator command: " ^ verilator_command);
        let _ = Unix.system verilator_command in
        begin
          match !opt_verilate with
          | Verilator_run -> Reporting.system_checked (sprintf "%s_obj_dir/V%s" out "sail_toplevel")
          | _ -> ()
        end
    | _ -> ()
  end

let _ =
  Target.register ~name:"systemverilog" ~flag:"sv" ~options:verilog_options ~rewrites:verilog_rewrites verilog_target
