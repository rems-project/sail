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
open Value2
open PPrint
open Printf
open Smt_exp

open Generate_primop

module R = Jib_sv

type verilate_mode = Verilator_none | Verilator_compile | Verilator_run

let opt_verilate = ref Verilator_none

let opt_line_directives = ref false

let opt_comb = ref false

let opt_inregs = ref false
let opt_outregs = ref false

let opt_max_unknown_integer_width = ref 128
let opt_max_unknown_bitvector_width = ref 128

let verilog_options =
  [
    ( "-sv_verilate",
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
      "<compile|run> Invoke verilator on generated output"
    );
    ("-sv_lines", Arg.Set opt_line_directives, " output `line directives");
    ("-sv_comb", Arg.Set opt_comb, " output an always_comb block instead of initial block");
    ("-sv_inregs", Arg.Set opt_inregs, " take register values from inputs");
    ("-sv_outregs", Arg.Set opt_outregs, " output register values");
    ( "-sv_int_size",
      Arg.Int (fun i -> opt_max_unknown_integer_width := i),
      "<n> set the maximum width for unknown integers"
    );
    ( "-sv_bits_size",
      Arg.Int (fun i -> opt_max_unknown_bitvector_width := i),
      "<n> set the maximum width for bitvectors with unknown width"
    );
  ]

let verilog_rewrites =
  let open Rewrites in
  [
    ("instantiate_outcomes", [String_arg "c"]);
    ("realize_mappings", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("truncate_hex_literals", []);
    ("mono_rewrites", [If_flag opt_mono_rewrites]);
    ("recheck_defs", [If_flag opt_mono_rewrites]);
    ("toplevel_nexps", [If_mono_arg]);
    ("monomorphise", [String_arg "c"; If_mono_arg]);
    ("atoms_to_singletons", [String_arg "c"; If_mono_arg]);
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
    ("exp_lift_assign", []);
    ("merge_function_clauses", []);
    ("recheck_defs", []);
    ("constant_fold", [String_arg "c"]);
  ]

module Verilog_config : Jib_compile.Config = struct
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
    | Typ_app (id, [A_aux (A_nexp n, _); A_aux (A_order _, _)]) when string_of_id id = "bitvector" ->
        let direction = true in
        (* match ord with Ord_aux (Ord_dec, _) -> true | Ord_aux (Ord_inc, _) -> false | _ -> assert false in *)
        begin
          match solve_unique ctx.local_env n with
          | Some n -> CT_fbits (Big_int.to_int n, direction)
          | _ -> CT_lbits direction
        end
    | Typ_app (id, [A_aux (A_nexp n, _); A_aux (A_order _, _); A_aux (A_typ typ, _)]) when string_of_id id = "vector" ->
        let direction = true in
        (* let direction = match ord with Ord_aux (Ord_dec, _) -> true | Ord_aux (Ord_inc, _) -> false | _ -> assert false in *)
        begin
          match nexp_simp n with
          | Nexp_aux (Nexp_constant c, _) -> CT_fvector (Big_int.to_int c, direction, convert_typ ctx typ)
          | _ -> CT_vector (direction, convert_typ ctx typ)
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

  let unroll_loops = None
  let specialize_calls = false
  let ignore_64 = true
  let struct_value = false
  let tuple_value = false
  let track_throw = true
  let branch_coverage = None
  let use_real = false
end

type function_footprint = { register_reads : IdSet.t; register_writes : IdSet.t }

let rec instr_footprint (I_aux (aux, _)) = ()

and instrs_footprint instrs = ()

let register_types cdefs =
  List.fold_left
    (fun acc cdef -> match cdef with CDEF_register (id, ctyp, _) -> Bindings.add id ctyp acc | _ -> acc)
    Bindings.empty cdefs

let jib_of_ast env ast effect_info =
  let open Jib_compile in
  let module Jibc = Make (Verilog_config) in
  let env, effect_info = add_special_functions env effect_info in
  let ctx = initial_ctx env effect_info in
  Jibc.compile_ast ctx ast

let wrap_module pre mod_name ins_outs doc =
  pre ^^ hardline ^^ string "module" ^^ space ^^ string mod_name
  ^^ parens (nest 4 (hardline ^^ separate (comma ^^ hardline) ins_outs) ^^ hardline)
  ^^ semi
  ^^ nest 4 (hardline ^^ doc)
  ^^ hardline ^^ string "endmodule" ^^ hardline

let verilator_cpp_wrapper name =
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

let make_genlib_file filename =
  Printf.eprintf "%d" !opt_max_unknown_bitvector_width;
  let common_primops = Generate_primop.common_primops !opt_max_unknown_bitvector_width !opt_max_unknown_integer_width in
  let defs = Generate_primop.get_generated_primops () in
  let ((out_chan, _, _, _) as file_info) = Util.open_output_with_check_unformatted None filename in
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

let verilog_target _ default_sail_dir out_opt ast effect_info env =
  let module SV = Jib_sv.Make (struct
    let max_unknown_integer_width = !opt_max_unknown_integer_width
    let max_unknown_bitvector_width = !opt_max_unknown_bitvector_width
    let line_directives = !opt_line_directives
  end) in
  let open SV in
  let sail_dir = Reporting.get_sail_dir default_sail_dir in
  let sail_sv_libdir = Filename.concat (Filename.concat sail_dir "lib") "sv" in
  let out = match out_opt with None -> "out" | Some name -> name in

  let cdefs, ctx = jib_of_ast env ast effect_info in
  let cdefs, ctx = Jib_optimize.remove_tuples cdefs ctx in
  let registers = register_types cdefs in

  let include_doc =
    string "`include \"sail.sv\"" ^^ hardline ^^ ksprintf string "`include \"sail_genlib_%s.sv\"" out ^^ twice hardline
  in

  let exception_vars =
    string "bit sail_have_exception;" ^^ hardline ^^ string "string sail_throw_location;" ^^ twice hardline
  in

  let in_doc, out_doc, fn_ctyps, setup_calls =
    List.fold_left
      (fun (doc_in, doc_out, fn_ctyps, setup_calls) cdef ->
        let cdef_doc, fn_ctyps, setup_calls, loc = sv_cdef ctx fn_ctyps setup_calls cdef in
        match loc with
        | CDLOC_In -> (doc_in ^^ cdef_doc, doc_out, fn_ctyps, setup_calls)
        | CDLOC_Out -> (doc_in, doc_out ^^ cdef_doc, fn_ctyps, setup_calls)
      )
      (exception_vars, include_doc, Bindings.empty, [])
      cdefs
  in

  let setup_function =
    string "function automatic void sail_setup();"
    ^^ nest 4
         (hardline ^^ separate_map (semi ^^ hardline) (fun call -> string call ^^ string "()") (List.rev setup_calls))
    ^^ semi ^^ hardline ^^ string "endfunction" ^^ twice hardline
  in

  let main_recv_inputs =
    if !opt_inregs then
      separate empty
        (List.filter_map
           (function
             | CDEF_register (id, ctyp, _) ->
                 Some (SV.sv_id id ^^ space ^^ equals ^^ space ^^ sv_id id ^^ string "_in" ^^ semi ^^ hardline)
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
             | CDEF_register (id, ctyp, _) ->
                 Some (sv_id id ^^ string "_out" ^^ space ^^ equals ^^ space ^^ sv_id id ^^ semi ^^ hardline)
             | _ -> None
             )
           cdefs
        )
    else empty
  in

  let main = List.find_opt (function CDEF_fundef (id, _, _, _) -> sv_id_string id = "main" | _ -> false) cdefs in
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
          | CDEF_register (id, ctyp, _) ->
              Some (string "input" ^^ space ^^ sv_ctyp ctyp ^^ space ^^ sv_id id ^^ string "_in")
          | _ -> None
          )
        cdefs
    else []
  in

  let outputs =
    if !opt_inregs then
      List.filter_map
        (function
          | CDEF_register (id, ctyp, _) ->
              Some (string "output" ^^ space ^^ sv_ctyp ctyp ^^ space ^^ sv_id id ^^ string "_out")
          | _ -> None
          )
        cdefs
    else []
  in

  let sv_output =
    Pretty_print_sail.to_string
      (wrap_module out_doc ("sail_" ^ out)
         (inputs @ outputs @ module_main_in_out)
         (in_doc ^^ setup_function ^^ invoke_main)
      )
  in
  make_genlib_file (sprintf "sail_genlib_%s.sv" out);

  let ((out_chan, _, _, _) as file_info) = Util.open_output_with_check_unformatted None (out ^ ".sv") in
  output_string out_chan sv_output;
  Util.close_output_with_check file_info;

  begin
    match !opt_verilate with
    | Verilator_compile | Verilator_run ->
        let ((out_chan, _, _, _) as file_info) = Util.open_output_with_check_unformatted None ("sim_" ^ out ^ ".cpp") in
        List.iter
          (fun line ->
            output_string out_chan line;
            output_char out_chan '\n'
          )
          (verilator_cpp_wrapper out);
        Util.close_output_with_check file_info;

        Reporting.system_checked
          (sprintf "verilator --cc --exe --build -j 0 -I%s sim_%s.cpp %s.sv" sail_sv_libdir out out);
        begin
          match !opt_verilate with Verilator_run -> Reporting.system_checked (sprintf "obj_dir/V%s" out) | _ -> ()
        end
    | _ -> ()
  end

let _ = Target.register ~name:"verilog" ~flag:"sv" ~options:verilog_options ~rewrites:verilog_rewrites verilog_target
