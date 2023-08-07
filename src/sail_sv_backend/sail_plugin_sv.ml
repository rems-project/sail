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
open Value2
open PPrint
open Printf
open Smt_exp

open Generate_primop

type verilate_mode = Verilator_none | Verilator_compile | Verilator_run

let opt_verilate = ref Verilator_none

let opt_line_directives = ref false

let opt_comb = ref false

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
    ( "-sv_lines",
      Arg.Set opt_line_directives,
      " output `line directives"
    );
    ( "-sv_comb",
      Arg.Set opt_comb,
      " output an always_comb block instead of initial block"
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

let variable_decls_to_top instrs =
  let decls, others =
    List.fold_left
      (fun (decls, others) instr ->
        match instr with
        | I_aux (I_decl (ctyp, id), (_, l)) -> (idecl l ctyp id :: decls, others)
        | I_aux (I_init (ctyp, id, cval), (_, l)) ->
            (idecl l ctyp id :: decls, icopy l (CL_id (id, ctyp)) cval :: others)
        | other -> (decls, other :: others)
      )
      ([], []) instrs
  in
  List.rev decls @ List.rev others

type function_footprint = { register_reads : IdSet.t; register_writes : IdSet.t }

let rec instr_footprint (I_aux (aux, _)) = ()

and instrs_footprint instrs = ()

let max_integer_width = 128

let sv_reserved_words =
  [
    "accept_on";
    "alias";
    "always_comb";
    "always_if";
    "always_latch";
    "assert";
    "assume";
    "automatic";
    "before";
    "bind";
    "bins";
    "binsof";
    "bit";
    "break";
    "byte";
    "chandle";
    "checker";
    "class";
    "clocking";
    "config";
    "const";
    "constraint";
    "context";
    "continue";
    "cover";
    "covergroup";
    "cross";
    "dist";
    "do";
    "endchecker";
    "endclass";
    "endclocking";
    "endfunction";
    "endinterface";
    "endpackage";
    "endprogram";
    "endproperty";
    "endsequence";
    "enum";
    "eventually";
    "expect";
    "export";
    "extends";
    "extern";
    "final";
    "first_match";
    "foreach";
    "forkjoin";
    "global";
    "iff";
    "ignore_bins";
    "illegal_bins";
    "implies";
    "import";
    "inside";
    "int";
    "interface";
    "intersect";
    "join_any";
    "join_none";
    "let";
    "local";
    "logic";
    "longint";
    "matches";
    "modport";
    "new";
    "nexttime";
    "null";
    "package";
    "packed";
    "priority";
    "program";
    "property";
    "protected";
    "pure";
    "rand";
    "randc";
    "randcase";
    "randsequence";
    "reg";
    "reject_on";
    "ref";
    "restrict";
    "return";
    "s_always";
    "s_eventually";
    "s_nexttime";
    "s_until";
    "s_until_with";
    "sequence";
    "shortint";
    "solve";
    "static";
    "string";
    "strong";
    "struct";
    "super";
    "sync_accept_on";
    "sync_reject_on";
    "tagged";
    "this";
    "throughout";
    "timeprecision";
    "timeunit";
    "type";
    "typedef";
    "union";
    "unique";
    "unique0";
    "until";
    "until_with";
    "untyped";
    "var";
    "virtual";
    "void";
    "wait_order";
    "weak";
    "wildcard";
    "with";
    "within";
  ]
  |> StringSet.of_list

let valid_sv_identifier_regexp : Str.regexp option ref = ref None

let valid_sv_identifier s =
  let regexp =
    match !valid_sv_identifier_regexp with
    | Some regexp -> regexp
    | None ->
        let regexp = Str.regexp "^[A-Za-z_][A-Za-z0-9_]*$" in
        valid_sv_identifier_regexp := Some regexp;
        regexp
  in
  Str.string_match regexp s 0

let sv_id_string id =
  let s = string_of_id id in
  if valid_sv_identifier s && not (StringSet.mem s sv_reserved_words) then s else Util.zencode_string s

let sv_id id = string (sv_id_string id)

let sv_name = function
  | Name (id, _) -> sv_id id
  | Global (id, _) -> sv_id id
  | Have_exception _ -> string "sail_have_exception"
  | Current_exception _ -> string "sail_current_exception"
  | Throw_location _ -> string "sail_throw_location"
  | Return _ -> string "sail_return"

let rec is_packed = function
  | CT_fbits _ | CT_unit | CT_bit | CT_bool | CT_fint _ | CT_lbits _ | CT_lint | CT_enum _ | CT_constant _ -> true
  | CT_variant (_, ctors) -> List.for_all (fun (_, ctyp) -> is_packed ctyp) ctors
  | CT_struct (_, fields) -> List.for_all (fun (_, ctyp) -> is_packed ctyp) fields
  | _ -> false

let rec sv_ctyp = function
  | CT_bool -> string "bit"
  | CT_bit -> string "logic"
  | CT_fbits (width, is_dec) ->
      if is_dec then ksprintf string "logic [%d:0]" (width - 1) else ksprintf string "logic [0:%d]" (width - 1)
  | CT_sbits (max_width, is_dec) ->
      let logic = if is_dec then sprintf "logic [%d:0]" (max_width - 1) else sprintf "logic [0:%d]" (max_width - 1) in
      ksprintf string "struct packed { logic [7:0] size; %s bits; }" logic
  | CT_lbits _ -> string "sail_bits"
  | CT_fint width -> ksprintf string "logic [%d:0]" (width - 1)
  | CT_lint -> ksprintf string "logic [%d:0]" (max_integer_width - 1)
  | CT_string -> string "string"
  | CT_unit -> string "sail_unit"
  | CT_variant (id, _) | CT_struct (id, _) | CT_enum (id, _) -> sv_id id
  | CT_constant c ->
      let width = required_width c in
      ksprintf string "logic [%d:0]" (width - 1)
  | _ -> empty

let sv_ctyp_default = function CT_bool -> string "0" | CT_bit -> string "1'bX" | _ -> string "DEFAULT"

let sv_type_def = function
  | CTD_enum (id, ids) ->
      string "typedef" ^^ space ^^ string "enum" ^^ space
      ^^ group (lbrace ^^ nest 4 (hardline ^^ separate_map (comma ^^ hardline) sv_id ids) ^^ hardline ^^ rbrace)
      ^^ space ^^ sv_id id ^^ semi
  | CTD_struct (id, fields) ->
      let sv_field (id, ctyp) = sv_ctyp ctyp ^^ space ^^ sv_id id in
      let can_be_packed = List.for_all (fun (_, ctyp) -> is_packed ctyp) fields in
      string "typedef" ^^ space ^^ string "struct"
      ^^ (if can_be_packed then space ^^ string "packed" else empty)
      ^^ space
      ^^ group
           (lbrace ^^ nest 4 (hardline ^^ separate_map (semi ^^ hardline) sv_field fields) ^^ semi ^^ hardline ^^ rbrace)
      ^^ space ^^ sv_id id ^^ semi
  | CTD_variant (id, ctors) ->
      let exception_boilerplate =
        if Id.compare id (mk_id "exception") = 0 then
          twice hardline ^^ ksprintf string "%s sail_current_exception;" (sv_id_string id)
        else empty
      in
      let kind_id (id, _) = string_of_id id |> Util.zencode_string |> String.uppercase_ascii |> string in
      let sv_ctor (id, ctyp) = sv_ctyp ctyp ^^ space ^^ sv_id id in
      let tag_type = string ("sailtag_" ^ sv_id_string id) in
      let value_type = string ("sailunion_" ^ sv_id_string id) in
      let kind_enum =
        separate space
          [
            string "typedef";
            string "enum";
            group (lbrace ^^ nest 4 (hardline ^^ separate_map (comma ^^ hardline) kind_id ctors) ^^ hardline ^^ rbrace);
            tag_type ^^ semi;
          ]
      in
      (* At least verilator only allows unions for packed types (which
         is roughly equivalent to types that can be represented as
         finite bitvectors). *)
      let can_be_packed = List.for_all (fun (_, ctyp) -> is_packed ctyp) ctors in
      kind_enum ^^ twice hardline
      ^^
      if can_be_packed then (
        let constructors =
          List.map
            (fun (ctor_id, ctyp) ->
              separate space [string "function"; string "automatic"; sv_id id; sv_id ctor_id]
              ^^ parens (sv_ctyp ctyp ^^ space ^^ char 'v')
              ^^ semi
              ^^ nest 4
                   (hardline ^^ sv_id id ^^ space ^^ char 'r' ^^ semi ^^ hardline
                   ^^ string ("sailunion_" ^ sv_id_string id)
                   ^^ space ^^ string "u" ^^ semi ^^ hardline
                   ^^ separate space
                        [
                          string "r.tag";
                          equals;
                          string_of_id ctor_id |> Util.zencode_string |> String.uppercase_ascii |> string;
                        ]
                   ^^ semi ^^ hardline
                   ^^ separate space [char 'u' ^^ dot ^^ sv_id ctor_id; equals; char 'v']
                   ^^ semi ^^ hardline
                   ^^ separate space [string "r.value"; equals; char 'u']
                   ^^ semi ^^ hardline ^^ string "return" ^^ space ^^ char 'r' ^^ semi
                   )
              ^^ hardline ^^ string "endfunction"
            )
            ctors
        in
        separate space
          [
            string "typedef";
            string "union";
            string "packed";
            group
              (lbrace
              ^^ nest 4 (hardline ^^ separate_map (semi ^^ hardline) sv_ctor ctors)
              ^^ semi ^^ hardline ^^ rbrace
              );
            value_type ^^ semi;
          ]
        ^^ twice hardline
        ^^ separate space
             [
               string "typedef";
               string "struct";
               string "packed";
               group
                 (lbrace
                 ^^ nest 4
                      (hardline ^^ tag_type ^^ space ^^ string "tag" ^^ semi ^^ hardline ^^ value_type ^^ space
                     ^^ string "value"
                      )
                 ^^ semi ^^ hardline ^^ rbrace
                 );
               sv_id id ^^ semi;
             ]
        ^^ twice hardline
        ^^ separate (twice hardline) constructors
        ^^ exception_boilerplate
      )
      else (
        let constructors =
          List.map
            (fun (ctor_id, ctyp) ->
              separate space [string "function"; string "automatic"; sv_id id; sv_id ctor_id]
              ^^ parens (sv_ctyp ctyp ^^ space ^^ char 'v')
              ^^ semi
              ^^ nest 4
                   (hardline ^^ sv_id id ^^ space ^^ char 'r' ^^ semi ^^ hardline
                   ^^ separate space
                        [
                          string "r.tag";
                          equals;
                          string_of_id ctor_id |> Util.zencode_string |> String.uppercase_ascii |> string;
                        ]
                   ^^ semi ^^ hardline
                   ^^ separate space [char 'r' ^^ dot ^^ sv_id ctor_id; equals; char 'v']
                   ^^ semi ^^ hardline ^^ string "return" ^^ space ^^ char 'r' ^^ semi
                   )
              ^^ hardline ^^ string "endfunction"
            )
            ctors
        in
        separate space
          [
            string "typedef";
            string "struct";
            group
              (lbrace
              ^^ nest 4
                   (hardline ^^ tag_type ^^ space ^^ string "tag" ^^ semi ^^ hardline
                   ^^ separate_map (semi ^^ hardline) sv_ctor ctors
                   )
              ^^ semi ^^ hardline ^^ rbrace
              );
            sv_id id ^^ semi;
          ]
        ^^ twice hardline
        ^^ separate (twice hardline) constructors
        ^^ exception_boilerplate
      )

module Smt =
  Smt_builtins.Make
    (struct
      let max_unknown_integer_width = 128
      let max_unknown_bitvector_width = 128
      let union_ctyp_classify = is_packed
    end)
    (struct
      let print_bits = function
        | CT_lbits _ -> "sail_print_bits"
        | CT_fbits (sz, _) -> Generate_primop.print_fbits sz
        | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "print_bits"
    end)

let ( let* ) = Smt_builtins.bind
let return = Smt_builtins.return

let rec mapM f = function
  | [] -> return []
  | x :: xs ->
      let* x = f x in
      let* xs = mapM f xs in
      return (x :: xs)

let sv_signed x = string "signed'" ^^ parens x

let string_of_bitU = function Sail2_values.B0 -> "0" | Sail2_values.B1 -> "1" | Sail2_values.BU -> "X"

let has_undefined_bit = List.exists (function Sail2_values.BU -> true | _ -> false)

let rec hex_bitvector bits =
  let open Sail2_values in
  match bits with
  | B0 :: B0 :: B0 :: B0 :: rest -> "0" ^ hex_bitvector rest
  | B0 :: B0 :: B0 :: B1 :: rest -> "1" ^ hex_bitvector rest
  | B0 :: B0 :: B1 :: B0 :: rest -> "2" ^ hex_bitvector rest
  | B0 :: B0 :: B1 :: B1 :: rest -> "3" ^ hex_bitvector rest
  | B0 :: B1 :: B0 :: B0 :: rest -> "4" ^ hex_bitvector rest
  | B0 :: B1 :: B0 :: B1 :: rest -> "5" ^ hex_bitvector rest
  | B0 :: B1 :: B1 :: B0 :: rest -> "6" ^ hex_bitvector rest
  | B0 :: B1 :: B1 :: B1 :: rest -> "7" ^ hex_bitvector rest
  | B1 :: B0 :: B0 :: B0 :: rest -> "8" ^ hex_bitvector rest
  | B1 :: B0 :: B0 :: B1 :: rest -> "9" ^ hex_bitvector rest
  | B1 :: B0 :: B1 :: B0 :: rest -> "A" ^ hex_bitvector rest
  | B1 :: B0 :: B1 :: B1 :: rest -> "B" ^ hex_bitvector rest
  | B1 :: B1 :: B0 :: B0 :: rest -> "C" ^ hex_bitvector rest
  | B1 :: B1 :: B0 :: B1 :: rest -> "D" ^ hex_bitvector rest
  | B1 :: B1 :: B1 :: B0 :: rest -> "E" ^ hex_bitvector rest
  | B1 :: B1 :: B1 :: B1 :: rest -> "F" ^ hex_bitvector rest
  | _ -> ""

(* Convert a SMTLIB expression into SystemVerilog *)
let rec sv_smt ?(need_parens = false) =
  let sv_smt_parens exp = sv_smt ~need_parens:true exp in
  let opt_parens doc = if need_parens then parens doc else doc in
  function
  | Bitvec_lit bits ->
      let len = List.length bits in
      if len mod 4 = 0 && not (has_undefined_bit bits) then ksprintf string "%d'h%s" len (hex_bitvector bits)
      else ksprintf string "%d'b%s" len (Util.string_of_list "" string_of_bitU bits)
  | Bool_lit true -> string "1"
  | Bool_lit false -> string "0"
  | String_lit s -> ksprintf string "\"%s\"" s
  | Enum "unit" -> string "SAIL_UNIT"
  | Fn ("Bits", [size; bv]) -> squote ^^ lbrace ^^ sv_smt size ^^ comma ^^ space ^^ sv_smt bv ^^ rbrace
  | Fn ("concat", xs) -> lbrace ^^ separate_map (comma ^^ space) sv_smt xs ^^ rbrace
  | Fn ("not", [Fn ("not", [x])]) -> sv_smt ~need_parens x
  | Fn ("not", [Fn ("=", [x; y])]) -> opt_parens (separate space [sv_smt_parens x; string "!="; sv_smt_parens y])
  | Fn ("not", [x]) -> opt_parens (char '!' ^^ sv_smt_parens x)
  | Fn ("=", [x; y]) -> opt_parens (separate space [sv_smt_parens x; string "=="; sv_smt_parens y])
  | Fn ("and", xs) -> opt_parens (separate_map (space ^^ string "&&" ^^ space) sv_smt_parens xs)
  | Fn ("or", xs) -> opt_parens (separate_map (space ^^ string "||" ^^ space) sv_smt_parens xs)
  | Fn ("bvnot", [x]) -> opt_parens (char '~' ^^ sv_smt_parens x)
  | Fn ("bvneg", [x]) -> opt_parens (char '-' ^^ sv_smt_parens x)
  | Fn ("bvand", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '&'; sv_smt_parens y])
  | Fn ("bvnand", [x; y]) ->
      opt_parens (char '~' ^^ parens (separate space [sv_smt_parens x; char '&'; sv_smt_parens y]))
  | Fn ("bvor", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '|'; sv_smt_parens y])
  | Fn ("bvnor", [x; y]) -> opt_parens (char '~' ^^ parens (separate space [sv_smt_parens x; char '|'; sv_smt_parens y]))
  | Fn ("bvxor", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '^'; sv_smt_parens y])
  | Fn ("bvxnor", [x; y]) ->
      opt_parens (char '~' ^^ parens (separate space [sv_smt_parens x; char '^'; sv_smt_parens y]))
  | Fn ("bvadd", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '+'; sv_smt_parens y])
  | Fn ("bvsub", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '-'; sv_smt_parens y])
  | Fn ("bvult", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '<'; sv_smt_parens y])
  | Fn ("bvule", [x; y]) -> opt_parens (separate space [sv_smt_parens x; string "<="; sv_smt_parens y])
  | Fn ("bvugt", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '>'; sv_smt_parens y])
  | Fn ("bvuge", [x; y]) -> opt_parens (separate space [sv_smt_parens x; string ">="; sv_smt_parens y])
  | Fn ("bvslt", [x; y]) -> opt_parens (separate space [sv_signed (sv_smt x); char '<'; sv_signed (sv_smt y)])
  | Fn ("bvsle", [x; y]) -> opt_parens (separate space [sv_signed (sv_smt x); string "<="; sv_signed (sv_smt y)])
  | Fn ("bvsgt", [x; y]) -> opt_parens (separate space [sv_signed (sv_smt x); char '>'; sv_signed (sv_smt y)])
  | Fn ("bvsge", [x; y]) -> opt_parens (separate space [sv_signed (sv_smt x); string ">="; sv_signed (sv_smt y)])
  | Fn ("bvshl", [x; y]) -> opt_parens (separate space [sv_smt x; string "<<"; sv_signed (sv_smt y)])
  | Fn ("bvlshr", [x; y]) -> opt_parens (separate space [sv_smt x; string ">>"; sv_signed (sv_smt y)])
  | Fn ("bvashr", [x; y]) -> opt_parens (separate space [sv_smt x; string ">>>"; sv_signed (sv_smt y)])
  | Fn ("contents", [x]) -> sv_smt_parens x ^^ dot ^^ string "bits"
  | Fn ("len", [x]) -> sv_smt_parens x ^^ dot ^^ string "size"
  | SignExtend (len, _, x) -> ksprintf string "unsigned'(%d'(signed'({" len ^^ sv_smt x ^^ string "})))"
  | ZeroExtend (len, _, x) -> ksprintf string "%d'({" len ^^ sv_smt x ^^ string "})"
  | Extract (n, m, Bitvec_lit bits) ->
      sv_smt (Bitvec_lit (Sail2_operators_bitlists.subrange_vec_dec bits (Big_int.of_int n) (Big_int.of_int m)))
  | Extract (n, m, Var v) ->
      if n = m then sv_name v ^^ lbracket ^^ string (string_of_int n) ^^ rbracket
      else sv_name v ^^ lbracket ^^ string (string_of_int n) ^^ colon ^^ string (string_of_int m) ^^ rbracket
  | Extract (n, m, x) ->
      if n = m then braces (sv_smt x) ^^ lbracket ^^ string (string_of_int n) ^^ rbracket
      else braces (sv_smt x) ^^ lbracket ^^ string (string_of_int n) ^^ colon ^^ string (string_of_int m) ^^ rbracket
  | Fn (f, args) -> string f ^^ parens (separate_map (comma ^^ space) sv_smt args)
  | Var v -> sv_name v
  | Tester (ctor, v) ->
      opt_parens (separate space [sv_smt v ^^ dot ^^ string "tag"; string "=="; string (ctor |> String.uppercase_ascii)])
  | Unwrap (ctor, packed, v) ->
      if packed then sv_smt v ^^ dot ^^ string "value" ^^ dot ^^ sv_id ctor else sv_smt v ^^ dot ^^ sv_id ctor
  | Field (_, field, v) -> sv_smt v ^^ dot ^^ sv_id field
  | Ite (cond, then_exp, else_exp) ->
      separate space [sv_smt_parens cond; char '?'; sv_smt_parens then_exp; char ':'; sv_smt_parens else_exp]
  | Enum e -> failwith "Unknown enum"

let sv_cval cval =
  let* smt = Smt.smt_cval cval in
  return (sv_smt smt)

let rec sv_clexp = function
  | CL_id (id, _) -> sv_name id
  | CL_field (clexp, field) -> sv_clexp clexp ^^ dot ^^ sv_id field
  | _ -> string "CLEXP"

let clexp_conversion clexp cval =
  let ctyp_to = clexp_ctyp clexp in
  let ctyp_from = cval_ctyp cval in
  let* smt = Smt.smt_cval cval in
  if ctyp_equal ctyp_to ctyp_from then return (separate space [sv_clexp clexp; equals; sv_smt smt])
  else (
    match (ctyp_to, ctyp_from) with
    | CT_fint sz, CT_constant c ->
        let n = required_width c in
        let extended = SignExtend (sz, sz - n, smt) in
        return (separate space [sv_clexp clexp; equals; sv_smt extended])
    | CT_lint, CT_constant c ->
        let n = required_width c in
        let extended = SignExtend (128, 128 - n, smt) in
        return (separate space [sv_clexp clexp; equals; sv_smt extended])
    | CT_lint, CT_fint sz ->
        let extended = SignExtend (128, 128 - sz, smt) in
        return (separate space [sv_clexp clexp; equals; sv_smt extended])
    | CT_fint sz, CT_lint ->
        let* adjusted = Smt_builtins.force_size sz 128 smt in
        return (separate space [sv_clexp clexp; equals; sv_smt adjusted])
    | CT_constant c, _ ->
        return (separate space [sv_clexp clexp; equals; sv_smt (Smt_builtins.bvint (required_width c) c)])
    | CT_fbits (sz, _), CT_lbits _ ->
        let extracted = Extract (sz - 1, 0, Fn ("contents", [smt])) in
        return (separate space [sv_clexp clexp; equals; sv_smt extracted])
    | CT_lbits _, CT_fbits (sz, _) when sz <= 128 ->
        let variable_width =
          Fn ("Bits", [Smt_builtins.bvpint 8 (Big_int.of_int sz); ZeroExtend (128, 128 - sz, smt)])
        in
        return (separate space [sv_clexp clexp; equals; sv_smt variable_width])
    | _, _ -> failwith ("Unknown conversion from " ^ string_of_ctyp ctyp_from ^ " to " ^ string_of_ctyp ctyp_to)
  )

let sv_update_fbits = function
  | [bv; index; bit] -> begin
      match (cval_ctyp bv, cval_ctyp index) with
      | CT_fbits (sz, _), CT_constant c ->
          let c = Big_int.to_int c in
          let* bv_smt = Smt.smt_cval bv in
          let bv_smt_1 = Extract (sz - 1, c + 1, bv_smt) in
          let bv_smt_2 = Extract (c - 1, 0, bv_smt) in
          let* bit_smt = Smt.smt_cval bit in
          let smt =
            if c = 0 then Fn ("concat", [bv_smt_1; bit_smt])
            else if c = sz - 1 then Fn ("concat", [bit_smt; bv_smt_2])
            else Fn ("concat", [bv_smt_1; bit_smt; bv_smt_2])
          in
          return (sv_smt smt)
      | _, _ -> failwith "update_fbits 1"
    end
  | _ -> failwith "update_fbits 2"

let cval_for_ctyp = function CT_unit -> V_lit (VL_unit, CT_unit)

let sv_line_directive l =
  match Reporting.simp_loc l with
  | Some (p1, _) when !opt_line_directives -> ksprintf string "`line %d \"%s\" 0" p1.pos_lnum p1.pos_fname ^^ hardline
  | _ -> empty

let rec sv_instr ctx (I_aux (aux, (_, l))) =
  let ld = sv_line_directive l in
  match aux with
  | I_comment str -> return (concat_map string ["/* "; str; " */"])
  | I_decl (ctyp, id) -> return (ld ^^ sv_ctyp ctyp ^^ space ^^ sv_name id ^^ semi)
  | I_init (ctyp, id, cval) ->
      let* value = sv_cval cval in
      return (ld ^^ separate space [sv_ctyp ctyp; sv_name id; equals; value] ^^ semi)
  | I_return cval ->
      let* value = sv_cval cval in
      return (string "return" ^^ space ^^ value ^^ semi)
  | I_end id -> return (string "return" ^^ space ^^ sv_name id ^^ semi)
  | I_exit _ -> return (string "$finish" ^^ semi)
  | I_copy (clexp, cval) ->
      let* doc = clexp_conversion clexp cval in
      return (ld ^^ doc ^^ semi)
  | I_funcall (clexp, _, (id, _), args) ->
      if Type_check.Env.is_extern id ctx.tc_env "c" then (
        let name = Type_check.Env.get_extern id ctx.tc_env "c" in
        let* value = Smt.builtin name args (clexp_ctyp clexp) in
        return (ld ^^ separate space [sv_clexp clexp; equals; sv_smt value] ^^ semi)
      )
      else if Id.compare id (mk_id "update_fbits") = 0 then
        let* rhs = sv_update_fbits args in
        return (ld ^^ sv_clexp clexp ^^ space ^^ equals ^^ space ^^ rhs ^^ semi)
      else
        let* args = mapM sv_cval args in
        return
          (ld ^^ sv_clexp clexp ^^ space ^^ equals ^^ space ^^ sv_id id
          ^^ parens (separate (comma ^^ space) args)
          ^^ semi
          )
  | I_if (cond, [], else_instrs, _) ->
      let* cond = sv_cval (V_call (Bnot, [cond])) in
      return
        (string "if" ^^ space ^^ parens cond ^^ space ^^ string "begin"
        ^^ nest 4 (hardline ^^ separate_map hardline (sv_checked_instr ctx) else_instrs)
        ^^ hardline ^^ string "end" ^^ semi
        )
  | I_if (cond, then_instrs, [], _) ->
      let* cond = sv_cval cond in
      return
        (string "if" ^^ space ^^ parens cond ^^ space ^^ string "begin"
        ^^ nest 4 (hardline ^^ separate_map hardline (sv_checked_instr ctx) then_instrs)
        ^^ hardline ^^ string "end" ^^ semi
        )
  | I_if (cond, then_instrs, else_instrs, _) ->
      let* cond = sv_cval cond in
      return
        (string "if" ^^ space ^^ parens cond ^^ space ^^ string "begin"
        ^^ nest 4 (hardline ^^ separate_map hardline (sv_checked_instr ctx) then_instrs)
        ^^ hardline ^^ string "end" ^^ space ^^ string "else" ^^ space ^^ string "begin"
        ^^ nest 4 (hardline ^^ separate_map hardline (sv_checked_instr ctx) else_instrs)
        ^^ hardline ^^ string "end" ^^ semi
        )
  | I_block instrs ->
      return
        (string "begin"
        ^^ nest 4 (hardline ^^ separate_map hardline (sv_checked_instr ctx) instrs)
        ^^ hardline ^^ string "end" ^^ semi
        )
  | I_undefined ctyp ->
      let cval = cval_for_ctyp ctyp in
      let* value = sv_cval cval in
      return (ld ^^ string "return" ^^ space ^^ value ^^ semi)
  | I_raw s -> return (string s ^^ semi)
  | I_jump _ | I_goto _ | I_label _ ->
      Reporting.unreachable l __POS__ "Non-structured control flow should not reach SystemVerilog backend"
  | I_throw _ | I_try_block _ ->
      Reporting.unreachable l __POS__ "Exception handling should not reach SystemVerilog backend"
  | I_clear _ | I_reset _ | I_reinit _ ->
      Reporting.unreachable l __POS__ "Cleanup commands should not appear in SystemVerilog backend"

and sv_checked_instr ctx instr =
  let m = sv_instr ctx instr in
  m.value

let sv_fundef ctx f params param_ctyps ret_ctyp body =
  let param_docs =
    try List.map2 (fun param ctyp -> sv_ctyp ctyp ^^ space ^^ sv_id param) params param_ctyps
    with Invalid_argument _ -> Reporting.unreachable (id_loc f) __POS__ "Function arity mismatch"
  in
  separate space [string "function"; string "automatic"; sv_ctyp ret_ctyp; sv_id f]
  ^^ parens (separate (comma ^^ space) param_docs)
  ^^ semi
  ^^ nest 4
       (hardline ^^ sv_ctyp ret_ctyp ^^ space ^^ sv_name Jib_util.return ^^ semi ^^ hardline
       ^^ separate_map hardline (sv_checked_instr ctx) body
       )
  ^^ hardline ^^ string "endfunction"

let filter_clear = filter_instrs (function I_aux (I_clear _, _) -> false | _ -> true)

let sv_setup_function ctx name setup =
  let setup =
    Jib_optimize.(
      setup |> flatten_instrs |> remove_dead_code |> variable_decls_to_top |> structure_control_flow_block
      |> filter_clear
    )
  in
  separate space [string "function"; string "automatic"; string "void"; string name]
  ^^ string "()" ^^ semi
  ^^ nest 4 (hardline ^^ separate_map hardline (sv_checked_instr ctx) setup)
  ^^ hardline ^^ string "endfunction" ^^ twice hardline

let sv_cdef ctx fn_ctyps setup_calls = function
  | CDEF_register (id, ctyp, setup) ->
      let binding_doc = sv_ctyp ctyp ^^ space ^^ sv_id id ^^ semi ^^ twice hardline in
      let name = sprintf "sail_setup_reg_%s" (sv_id_string id) in
      (binding_doc ^^ sv_setup_function ctx name setup, fn_ctyps, name :: setup_calls)
  | CDEF_type td -> (sv_type_def td ^^ twice hardline, fn_ctyps, setup_calls)
  | CDEF_val (f, _, param_ctyps, ret_ctyp) -> (empty, Bindings.add f (param_ctyps, ret_ctyp) fn_ctyps, setup_calls)
  | CDEF_fundef (f, _, params, body) ->
      let body =
        Jib_optimize.(
          body |> flatten_instrs |> remove_dead_code |> variable_decls_to_top |> structure_control_flow_block
          |> filter_clear
        )
      in
      begin
        match Bindings.find_opt f fn_ctyps with
        | Some (param_ctyps, ret_ctyp) ->
            (sv_fundef ctx f params param_ctyps ret_ctyp body ^^ twice hardline, fn_ctyps, setup_calls)
        | None -> Reporting.unreachable (id_loc f) __POS__ ("No function type found for " ^ string_of_id f)
      end
  | CDEF_let (n, bindings, setup) ->
      let bindings_doc =
        separate_map (semi ^^ hardline) (fun (id, ctyp) -> sv_ctyp ctyp ^^ space ^^ sv_id id) bindings
        ^^ semi ^^ twice hardline
      in
      let name = sprintf "sail_setup_let_%d" n in
      (bindings_doc ^^ sv_setup_function ctx name setup, fn_ctyps, name :: setup_calls)
  | _ -> (empty, fn_ctyps, setup_calls)

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

let wrap_module mod_name doc =
  string "module" ^^ space ^^ string mod_name ^^ semi
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
  let common_primops = Generate_primop.common_primops 128 128 in
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

  let doc, _, setup_calls =
    List.fold_left
      (fun (doc, fn_ctyps, setup_calls) cdef ->
        let cdef_doc, fn_ctyps, setup_calls = sv_cdef ctx fn_ctyps setup_calls cdef in
        (doc ^^ cdef_doc, fn_ctyps, setup_calls)
      )
      (include_doc ^^ exception_vars, Bindings.empty, [])
      cdefs
  in

  let setup_function =
    string "function automatic void sail_setup();"
    ^^ nest 4
         (hardline ^^ separate_map (semi ^^ hardline) (fun call -> string call ^^ string "()") (List.rev setup_calls))
    ^^ semi ^^ hardline ^^ string "endfunction" ^^ twice hardline
  in

  let invoke_main =
    if not !opt_comb then
      string "initial" ^^ space ^^ string "begin"
      ^^ nest 4
          (hardline ^^ string "sail_unit u;" ^^ hardline ^^ string "$display(\"TEST START\");" ^^ hardline
          ^^ string "sail_setup();" ^^ hardline ^^ string "u = main(SAIL_UNIT);" ^^ hardline
          ^^ string "$display(\"TEST END\");" ^^ hardline ^^ string "$finish;"
          )
      ^^ hardline ^^ string "end"
    else
      string "always_comb" ^^ space ^^ string "begin"
      ^^ nest 4
          (hardline ^^ string "sail_unit u;" ^^ hardline
          ^^ string "sail_setup();" ^^ hardline ^^ string "u = main(SAIL_UNIT);"
          )
      ^^ hardline ^^ string "end"
  in

  let sv_output = Pretty_print_sail.to_string (wrap_module ("sail_" ^ out) (doc ^^ setup_function ^^ invoke_main)) in
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
