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

open Ast_util
open Jib
open Jib_compile
open Jib_util
open PPrint
open Printf
open Smt_exp

open Generate_primop

module type CONFIG = sig
  val max_unknown_integer_width : int
  val max_unknown_bitvector_width : int
  val line_directives : bool
  val nostrings : bool
  val nopacked : bool
  val union_padding : bool
  val unreachable : string list
  val comb : bool
  val ignore : string list
end

module Make (Config : CONFIG) = struct
  let lbits_index_width = required_width (Big_int.of_int (Config.max_unknown_bitvector_width - 1))

  let valid_sv_identifier_regexp : Str.regexp option ref = ref None

  let has_prefix prefix s =
    if String.length s < String.length prefix then false else String.sub s 0 (String.length prefix) = prefix

  let has_bad_prefix s = has_prefix "sail_" s || has_prefix "t_" s || has_prefix "ret_" s

  let valid_sv_identifier s =
    let regexp =
      (* Cache the regexp to avoid compiling it every time *)
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
    if
      valid_sv_identifier s
      && (not (has_bad_prefix s))
      && (not (StringSet.mem s Keywords.sv_reserved_words))
      && not (StringSet.mem s Keywords.sv_used_words)
    then s
    else Util.zencode_string s

  let sv_id id = string (sv_id_string id)

  let sv_type_id_string id = "t_" ^ sv_id_string id

  let sv_type_id id = string (sv_type_id_string id)

  let rec bit_width = function
    | CT_unit | CT_bit | CT_bool -> Some 1
    | CT_fbits len -> Some len
    | CT_lbits -> Some Config.max_unknown_bitvector_width
    | CT_enum (_, ids) -> Some (required_width (Big_int.of_int (List.length ids - 1)))
    | CT_constant c -> Some (required_width c)
    | CT_variant (_, ctors) ->
        List.map (fun (_, ctyp) -> bit_width ctyp) ctors |> Util.option_all |> Option.map (List.fold_left max 1)
    | CT_struct (_, fields) ->
        List.map (fun (_, ctyp) -> bit_width ctyp) fields |> Util.option_all |> Option.map (List.fold_left ( + ) 0)
    | _ -> None

  let is_packed ctyp = if Config.nopacked then false else Option.is_some (bit_width ctyp)

  let simple_type str = (str, None)

  let rec sv_ctyp = function
    | CT_bool -> simple_type "bit"
    | CT_bit -> simple_type "logic"
    | CT_fbits width -> ksprintf simple_type "logic [%d:0]" (width - 1)
    | CT_sbits max_width ->
        let logic = sprintf "logic [%d:0]" (max_width - 1) in
        ksprintf simple_type "struct packed { logic [7:0] size; %s bits; }" logic
    | CT_lbits -> simple_type "sail_bits"
    | CT_fint width -> ksprintf simple_type "logic [%d:0]" (width - 1)
    | CT_lint -> ksprintf simple_type "logic [%d:0]" (Config.max_unknown_integer_width - 1)
    | CT_string -> simple_type (if Config.nostrings then "sail_unit" else "string")
    | CT_unit -> simple_type "sail_unit"
    | CT_variant (id, _) | CT_struct (id, _) | CT_enum (id, _) -> simple_type (sv_type_id_string id)
    | CT_constant c ->
        let width = required_width c in
        ksprintf simple_type "logic [%d:0]" (width - 1)
    | CT_ref ctyp -> ksprintf simple_type "sail_reg_%s" (Util.zencode_string (string_of_ctyp ctyp))
    | CT_fvector (len, ctyp) ->
        let outer_index = sprintf "[%d:0]" (len - 1) in
        begin
          match sv_ctyp ctyp with
          | ty, Some inner_index -> (ty, Some (inner_index ^ outer_index))
          | ty, None -> (ty, Some outer_index)
        end
    | CT_list ctyp -> begin
        match sv_ctyp ctyp with ty, Some inner_index -> (ty, Some (inner_index ^ "[$]")) | ty, None -> (ty, Some "[$]")
      end
    | CT_vector ctyp -> begin
        match sv_ctyp ctyp with ty, Some inner_index -> (ty, Some (inner_index ^ "[]")) | ty, None -> (ty, Some "[]")
      end
    | CT_real -> simple_type "sail_real"
    | CT_rounding_mode -> simple_type "sail_rounding_mode"
    | CT_float width -> ksprintf simple_type "sail_float%d" width
    | CT_tup _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Tuple type should not reach SV backend"
    | CT_poly _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Polymorphic type should not reach SV backend"

  module Smt =
    Smt_gen.Make
      (struct
        let max_unknown_integer_width = Config.max_unknown_integer_width
        let max_unknown_bitvector_width = Config.max_unknown_bitvector_width
        let union_ctyp_classify = is_packed
      end)
      (struct
        let print_bits l = function
          | CT_lbits -> "sail_print_bits"
          | CT_fbits sz when Config.nostrings -> Generate_primop.print_fbits_stub sz
          | CT_fbits sz -> Generate_primop.print_fbits sz
          | _ -> Reporting.unreachable l __POS__ "print_bits"

        let string_of_bits l = function
          | CT_lbits -> "sail_string_of_bits"
          | CT_fbits sz when Config.nostrings -> Generate_primop.string_of_fbits_stub sz
          | CT_fbits sz -> Generate_primop.string_of_fbits sz
          | _ -> Reporting.unreachable l __POS__ "string_of_bits"

        let dec_str l = function
          | CT_lint -> "sail_dec_str"
          | CT_fint sz when Config.nostrings -> Generate_primop.dec_str_fint_stub sz
          | CT_fint sz -> Generate_primop.dec_str_fint sz
          | _ -> Reporting.unreachable l __POS__ "dec_str"

        let hex_str l = function
          | CT_lint -> "sail_hex_str"
          | CT_fint sz when Config.nostrings -> Generate_primop.hex_str_fint_stub sz
          | CT_fint sz -> Generate_primop.hex_str_fint sz
          | _ -> Reporting.unreachable l __POS__ "hex_str"

        let hex_str_upper l = function
          | CT_lint -> "sail_hex_str_upper"
          | CT_fint sz when Config.nostrings -> Generate_primop.hex_str_upper_fint_stub sz
          | CT_fint sz -> Generate_primop.hex_str_upper_fint sz
          | _ -> Reporting.unreachable l __POS__ "hex_str_upper"

        let count_leading_zeros _l sz = Generate_primop.count_leading_zeros sz

        let fvector_store _l len ctyp =
          Generate_primop.fvector_store len (sv_ctyp ctyp) (Util.zencode_string (string_of_ctyp ctyp))

        let is_empty l = function
          | CT_list ctyp -> Generate_primop.is_empty (sv_ctyp ctyp) (Util.zencode_string (string_of_ctyp ctyp))
          | _ -> Reporting.unreachable l __POS__ "is_empty"

        let hd l = function
          | CT_list ctyp -> Generate_primop.hd (sv_ctyp ctyp) (Util.zencode_string (string_of_ctyp ctyp))
          | _ -> Reporting.unreachable l __POS__ "hd"

        let tl l = function
          | CT_list ctyp -> Generate_primop.tl (sv_ctyp ctyp) (Util.zencode_string (string_of_ctyp ctyp))
          | _ -> Reporting.unreachable l __POS__ "tl"
      end)

  let ( let* ) = Smt_gen.bind
  let return = Smt_gen.return
  let mapM = Smt_gen.mapM

  let sv_name = function
    | Name (id, _) -> sv_id id
    | Global (id, _) -> sv_id id
    | Have_exception _ -> string "sail_have_exception"
    | Current_exception _ -> string "sail_current_exception"
    | Throw_location _ -> string "sail_throw_location"
    | Return _ -> string "sail_return"

  let wrap_type ctyp doc =
    match sv_ctyp ctyp with
    | ty, None -> string ty ^^ space ^^ doc
    | ty, Some index -> string ty ^^ space ^^ doc ^^ space ^^ string index

  (*
  let sv_ctyp_dummy = function
    | CT_bool -> string "0"
    | CT_fbits width ->
      ksprintf string "%d'b%s" width (String.make width 'X')
    | CT_lbits ->
      let index = ksprintf string "%d'b%s" lbits_index_width (String.make lbits_index_width 'X') in
      let sz = Config.max_unknown_bitvector_width in
      let contents = ksprintf string "%d'b%s" sz (String.make sz 'X') in
      squote ^^ lbrace ^^ index ^^ comma ^^ space ^^ ksprintf string ^^ rbrace
    | CT_bit -> string "1'bX"
    | _ -> string "DEFAULT"
     *)

  let sv_type_def = function
    | CTD_enum (id, ids) ->
        string "typedef" ^^ space ^^ string "enum" ^^ space
        ^^ group (lbrace ^^ nest 4 (hardline ^^ separate_map (comma ^^ hardline) sv_id ids) ^^ hardline ^^ rbrace)
        ^^ space ^^ sv_type_id id ^^ semi
    | CTD_struct (id, fields) ->
        let sv_field (id, ctyp) = wrap_type ctyp (sv_id id) in
        let can_be_packed = List.for_all (fun (_, ctyp) -> is_packed ctyp) fields in
        string "typedef" ^^ space ^^ string "struct"
        ^^ (if can_be_packed then space ^^ string "packed" else empty)
        ^^ space
        ^^ group
             (lbrace
             ^^ nest 4 (hardline ^^ separate_map (semi ^^ hardline) sv_field fields)
             ^^ semi ^^ hardline ^^ rbrace
             )
        ^^ space ^^ sv_type_id id ^^ semi
    | CTD_variant (id, ctors) ->
        let exception_boilerplate =
          if Id.compare id (mk_id "exception") = 0 then
            twice hardline ^^ ksprintf string "%s sail_current_exception;" (sv_type_id_string id)
          else empty
        in
        let kind_id (id, _) = string_of_id id |> Util.zencode_string |> String.uppercase_ascii |> string in
        let sv_ctor (id, ctyp) = wrap_type ctyp (sv_id id) in
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
          let max_width = bit_width (CT_variant (id, ctors)) |> Option.get in
          let padding_structs =
            List.map
              (fun (ctor_id, ctyp) ->
                let padding_type = string ("sailpadding_" ^ sv_id_string ctor_id) in
                let required_padding = max_width - Option.get (bit_width ctyp) in
                let padded =
                  separate space
                    [
                      string "typedef";
                      string "struct";
                      string "packed";
                      group
                        (lbrace
                        ^^ nest 4
                             (hardline
                             ^^ sv_ctor (ctor_id, ctyp)
                             ^^ semi
                             ^^
                             if required_padding > 0 then
                               hardline ^^ ksprintf string "logic [%d:0] padding" (required_padding - 1) ^^ semi
                             else empty
                             )
                        ^^ hardline ^^ rbrace
                        );
                      padding_type ^^ semi;
                    ]
                in
                (padded, (ctor_id, ctyp, padding_type, required_padding))
              )
              ctors
          in
          let constructors =
            if Config.union_padding then
              List.map
                (fun (_, (ctor_id, ctyp, padding_type, required_padding)) ->
                  separate space [string "function"; string "automatic"; sv_type_id id; sv_id ctor_id]
                  ^^ parens (wrap_type ctyp (char 'v'))
                  ^^ semi
                  ^^ nest 4
                       (hardline ^^ sv_type_id id ^^ space ^^ char 'r' ^^ semi ^^ hardline
                       ^^ string ("sailunion_" ^ sv_id_string id)
                       ^^ space ^^ char 'u' ^^ semi ^^ hardline ^^ padding_type ^^ space ^^ char 'p' ^^ semi ^^ hardline
                       ^^ separate space
                            [
                              string "r.tag";
                              equals;
                              string_of_id ctor_id |> Util.zencode_string |> String.uppercase_ascii |> string;
                            ]
                       ^^ semi ^^ hardline
                       ^^ separate space [char 'p' ^^ dot ^^ sv_id ctor_id; equals; char 'v']
                       ^^ semi ^^ hardline
                       ^^ ( if required_padding > 0 then
                              separate space
                                [
                                  char 'p' ^^ dot ^^ string "padding";
                                  equals;
                                  ksprintf string "%d'b%s" required_padding (String.make required_padding '0');
                                ]
                              ^^ semi ^^ hardline
                            else empty
                          )
                       ^^ separate space [char 'u' ^^ dot ^^ sv_id ctor_id; equals; char 'p']
                       ^^ semi ^^ hardline
                       ^^ separate space [string "r.value"; equals; char 'u']
                       ^^ semi ^^ hardline ^^ string "return" ^^ space ^^ char 'r' ^^ semi
                       )
                  ^^ hardline ^^ string "endfunction"
                )
                padding_structs
            else
              List.map
                (fun (ctor_id, ctyp) ->
                  separate space [string "function"; string "automatic"; sv_type_id id; sv_id ctor_id]
                  ^^ parens (wrap_type ctyp (char 'v'))
                  ^^ semi
                  ^^ nest 4
                       (hardline ^^ sv_type_id id ^^ space ^^ char 'r' ^^ semi ^^ hardline
                       ^^ string ("sailunion_" ^ sv_id_string id)
                       ^^ space ^^ char 'u' ^^ semi ^^ hardline
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
          let sv_padded_ctor (_, (ctor_id, _, padding_type, _)) = padding_type ^^ space ^^ sv_id ctor_id in
          (if Config.union_padding then separate_map (twice hardline) fst padding_structs ^^ twice hardline else empty)
          ^^ separate space
               [
                 string "typedef";
                 string "union";
                 string "packed";
                 group
                   (lbrace
                   ^^ nest 4
                        (hardline
                        ^^
                        if Config.union_padding then separate_map (semi ^^ hardline) sv_padded_ctor padding_structs
                        else separate_map (semi ^^ hardline) sv_ctor ctors
                        )
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
                 sv_type_id id ^^ semi;
               ]
          ^^ twice hardline
          ^^ separate (twice hardline) constructors
          ^^ exception_boilerplate
        )
        else (
          let constructors =
            List.map
              (fun (ctor_id, ctyp) ->
                separate space [string "function"; string "automatic"; sv_type_id id; sv_id ctor_id]
                ^^ parens (wrap_type ctyp (char 'v'))
                ^^ semi
                ^^ nest 4
                     (hardline ^^ sv_type_id id ^^ space ^^ char 'r' ^^ semi ^^ hardline
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
              sv_type_id id ^^ semi;
            ]
          ^^ twice hardline
          ^^ separate (twice hardline) constructors
          ^^ exception_boilerplate
        )

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

  let rec tails = function
    | Var v -> Some (0, v)
    | Tl (_, arg) -> Option.map (fun (n, v) -> (n + 1, v)) (tails arg)
    | _ -> None

  (* Convert a SMTLIB expression into SystemVerilog *)
  let rec sv_smt ?(need_parens = false) =
    let sv_smt_parens exp = sv_smt ~need_parens:true exp in
    let opt_parens doc = if need_parens then parens doc else doc in
    function
    | Bitvec_lit bits ->
        let len = List.length bits in
        if len mod 4 = 0 && not (has_undefined_bit bits) then ksprintf string "%d'h%s" len (hex_bitvector bits)
        else ksprintf string "%d'b%s" len (Util.string_of_list "" string_of_bitU bits)
    | Bool_lit true -> string "1'h1"
    | Bool_lit false -> string "1'h0"
    | String_lit s -> if Config.nostrings then string "SAIL_UNIT" else ksprintf string "\"%s\"" s
    | Enum "unit" -> string "SAIL_UNIT"
    | Fn ("reg_ref", [String_lit r]) -> ksprintf string "SAIL_REG_%s" (Util.zencode_upper_string r)
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
    | Fn ("bvnor", [x; y]) ->
        opt_parens (char '~' ^^ parens (separate space [sv_smt_parens x; char '|'; sv_smt_parens y]))
    | Fn ("bvxor", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '^'; sv_smt_parens y])
    | Fn ("bvxnor", [x; y]) ->
        opt_parens (char '~' ^^ parens (separate space [sv_smt_parens x; char '^'; sv_smt_parens y]))
    | Fn ("bvadd", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '+'; sv_smt_parens y])
    | Fn ("bvsub", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '-'; sv_smt_parens y])
    | Fn ("bvmul", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '*'; sv_smt_parens y])
    | Fn ("bvult", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '<'; sv_smt_parens y])
    | Fn ("bvule", [x; y]) -> opt_parens (separate space [sv_smt_parens x; string "<="; sv_smt_parens y])
    | Fn ("bvugt", [x; y]) -> opt_parens (separate space [sv_smt_parens x; char '>'; sv_smt_parens y])
    | Fn ("bvuge", [x; y]) -> opt_parens (separate space [sv_smt_parens x; string ">="; sv_smt_parens y])
    | Fn ("bvslt", [x; y]) -> opt_parens (separate space [sv_signed (sv_smt x); char '<'; sv_signed (sv_smt y)])
    | Fn ("bvsle", [x; y]) -> opt_parens (separate space [sv_signed (sv_smt x); string "<="; sv_signed (sv_smt y)])
    | Fn ("bvsgt", [x; y]) -> opt_parens (separate space [sv_signed (sv_smt x); char '>'; sv_signed (sv_smt y)])
    | Fn ("bvsge", [x; y]) -> opt_parens (separate space [sv_signed (sv_smt x); string ">="; sv_signed (sv_smt y)])
    | Fn ("bvshl", [x; y]) -> opt_parens (separate space [sv_smt_parens x; string "<<"; sv_signed (sv_smt y)])
    | Fn ("bvlshr", [x; y]) -> opt_parens (separate space [sv_smt_parens x; string ">>"; sv_signed (sv_smt y)])
    | Fn ("bvashr", [x; y]) -> opt_parens (separate space [sv_smt_parens x; string ">>>"; sv_signed (sv_smt y)])
    | Fn ("select", [x; i]) -> sv_smt_parens x ^^ lbracket ^^ sv_smt i ^^ rbracket
    | Fn ("contents", [Var v]) -> sv_name v ^^ dot ^^ string "bits"
    | Fn ("contents", [x]) -> string "sail_bits_value" ^^ parens (sv_smt x)
    | Fn ("len", [Var v]) -> sv_name v ^^ dot ^^ string "size"
    | Fn ("len", [x]) -> string "sail_bits_size" ^^ parens (sv_smt x)
    | Fn ("cons", [x; xs]) -> lbrace ^^ sv_smt x ^^ comma ^^ space ^^ sv_smt xs ^^ rbrace
    | Fn (f, args) -> string f ^^ parens (separate_map (comma ^^ space) sv_smt args)
    | Store (_, store_fn, arr, i, x) -> string store_fn ^^ parens (separate_map (comma ^^ space) sv_smt [arr; i; x])
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
    | Var v -> sv_name v
    | Tester (ctor, v) ->
        opt_parens
          (separate space [sv_smt v ^^ dot ^^ string "tag"; string "=="; string (ctor |> String.uppercase_ascii)])
    | Unwrap (ctor, packed, v) ->
        let packed_ctor = if Config.union_padding then sv_id ctor ^^ dot ^^ sv_id ctor else sv_id ctor in
        if packed then sv_smt v ^^ dot ^^ string "value" ^^ dot ^^ packed_ctor else sv_smt v ^^ dot ^^ sv_id ctor
    | Field (_, field, v) -> sv_smt v ^^ dot ^^ sv_id field
    | Ite (cond, then_exp, else_exp) ->
        separate space [sv_smt_parens cond; char '?'; sv_smt_parens then_exp; char ':'; sv_smt_parens else_exp]
    | Enum e -> failwith "Unknown enum"
    | Empty_list -> string "{}"
    | Hd (op, arg) -> begin
        match tails arg with
        | Some (index, v) -> sv_name v ^^ brackets (string (string_of_int index))
        | None -> string op ^^ parens (sv_smt arg)
      end
    | Tl (op, arg) -> string op ^^ parens (sv_smt arg)
    | _ -> empty

  let sv_cval cval =
    let* smt = Smt.smt_cval cval in
    return (sv_smt smt)

  let rec sv_clexp = function
    | CL_id (id, _) -> sv_name id
    | CL_field (clexp, field) -> sv_clexp clexp ^^ dot ^^ sv_id field
    | clexp -> string ("// CLEXP " ^ Jib_util.string_of_clexp clexp)

  let sv_update_fbits = function
    | [bv; index; bit] -> begin
        match (cval_ctyp bv, cval_ctyp index) with
        | CT_fbits 1, _ -> Smt_gen.fmap sv_smt (Smt.smt_cval bit)
        | CT_fbits sz, CT_constant c ->
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

  let cval_for_ctyp = function
    | CT_unit -> return (V_lit (VL_unit, CT_unit))
    | ctyp ->
        let* l = Smt_gen.current_location in
        Reporting.unreachable l __POS__ ("Cannot create undefined value of type " ^ string_of_ctyp ctyp)

  let sv_line_directive l =
    match Reporting.simp_loc l with
    | Some (p1, _) when Config.line_directives ->
        ksprintf string "`line %d \"%s\" 0" p1.pos_lnum p1.pos_fname ^^ hardline
    | _ -> empty

  let sv_assign clexp value =
    match clexp with
    | CL_addr (CL_id (id, CT_ref reg_ctyp)) ->
        let encoded = Util.zencode_string (string_of_ctyp reg_ctyp) in
        ksprintf string "sail_reg_assign_%s" encoded ^^ parens (sv_name id ^^ comma ^^ space ^^ value) ^^ semi
    | _ -> sv_clexp clexp ^^ space ^^ equals ^^ space ^^ value ^^ semi

  let rec sv_instr ctx (I_aux (aux, (_, l))) =
    let ld = sv_line_directive l in
    match aux with
    | I_comment str -> return (concat_map string ["/* "; str; " */"])
    | I_decl (ctyp, id) -> return (ld ^^ wrap_type ctyp (sv_name id) ^^ semi)
    | I_init (ctyp, id, cval) ->
        let* value = sv_cval cval in
        return (ld ^^ separate space [wrap_type ctyp (sv_name id); equals; value] ^^ semi)
    | I_return cval ->
        let* value = sv_cval cval in
        return (string "return" ^^ space ^^ value ^^ semi)
    | I_end id -> return (string "return" ^^ space ^^ sv_name id ^^ semi)
    | I_exit _ -> return (if Config.comb then string "sail_reached_unreachable = 1;" else string "$finish" ^^ semi)
    | I_copy (clexp, cval) ->
        let* value =
          Smt_gen.bind (Smt.smt_cval cval) (Smt.smt_conversion ~into:(clexp_ctyp clexp) ~from:(cval_ctyp cval))
        in
        return (sv_assign clexp (sv_smt value))
    | I_funcall (clexp, _, (id, _), args) ->
        if ctx_is_extern id ctx then (
          let name = ctx_get_extern id ctx in
          match Smt.builtin name with
          | Some generator ->
              let* value = Smt_gen.fmap Smt_exp.simp (generator args (clexp_ctyp clexp)) in
              begin
                (* We can optimize R = store(R, i x) into R[i] = x *)
                match (clexp, value) with
                | CL_id (v, _), Store (_, _, Var v', i, x) when Name.compare v v' = 0 ->
                    return
                      (ld
                      ^^ separate space [sv_clexp clexp ^^ lbracket ^^ sv_smt i ^^ rbracket; equals; sv_smt x]
                      ^^ semi
                      )
                | _, _ -> return (ld ^^ sv_assign clexp (sv_smt value))
              end
          | None ->
              let* args = mapM Smt.smt_cval args in
              let value = Fn ("sail_" ^ name, args) in
              return (ld ^^ sv_assign clexp (sv_smt value))
        )
        else if Id.compare id (mk_id "update_fbits") = 0 then
          let* rhs = sv_update_fbits args in
          return (ld ^^ sv_clexp clexp ^^ space ^^ equals ^^ space ^^ rhs ^^ semi)
        else if Id.compare id (mk_id "internal_vector_init") = 0 then return empty
        else if Id.compare id (mk_id "internal_vector_update") = 0 then (
          match args with
          | [arr; i; x] -> begin
              match cval_ctyp arr with
              | CT_fvector (len, _) ->
                  let* i =
                    Smt_gen.bind (Smt.smt_cval i)
                      (Smt_gen.unsigned_size ~checked:false
                         ~into:(required_width (Big_int.of_int (len - 1)) - 1)
                         ~from:(Smt.int_size (cval_ctyp i))
                      )
                  in
                  let* x = Smt.smt_cval x in
                  return
                    (sv_clexp clexp ^^ lbracket ^^ sv_smt i ^^ rbracket ^^ space ^^ equals ^^ space ^^ sv_smt x ^^ semi)
              | _ -> Reporting.unreachable l __POS__ "Invalid vector type for internal vector update"
            end
          | _ -> Reporting.unreachable l __POS__ "Invalid number of arguments to internal vector update"
        )
        else
          let* args = mapM sv_cval args in
          let call = sv_id id ^^ parens (separate (comma ^^ space) args) in
          return (ld ^^ sv_assign clexp call)
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
    | I_raw s -> return (string s ^^ semi)
    | I_undefined ctyp ->
        Reporting.unreachable l __POS__ "Unreachable instruction should not reach SystemVerilog backend"
    | I_jump _ | I_goto _ | I_label _ ->
        Reporting.unreachable l __POS__ "Non-structured control flow should not reach SystemVerilog backend"
    | I_throw _ | I_try_block _ ->
        Reporting.unreachable l __POS__ "Exception handling should not reach SystemVerilog backend"
    | I_clear _ | I_reset _ | I_reinit _ ->
        Reporting.unreachable l __POS__ "Cleanup commands should not appear in SystemVerilog backend"

  and sv_checked_instr ctx (I_aux (_, (_, l)) as instr) =
    let v, _ = Smt_gen.run (sv_instr ctx instr) l in
    v

  let sv_fundef_with ctx f params param_ctyps ret_ctyp fun_body =
    let sv_ret_ty, index_ty = sv_ctyp ret_ctyp in
    let sv_ret_ty, typedef =
      match index_ty with
      | Some index ->
          let encoded = Util.zencode_string (string_of_ctyp ret_ctyp) in
          let new_ty = string ("t_" ^ f ^ "_" ^ encoded) in
          (new_ty, separate space [string "typedef"; string sv_ret_ty; new_ty; string index] ^^ semi ^^ twice hardline)
      | None -> (string sv_ret_ty, empty)
    in
    let param_docs =
      try List.map2 (fun param ctyp -> wrap_type ctyp (sv_id param)) params param_ctyps
      with Invalid_argument _ -> Reporting.unreachable Unknown __POS__ "Function arity mismatch"
    in
    typedef
    ^^ separate space [string "function"; string "automatic"; sv_ret_ty; string f]
    ^^ parens (separate (comma ^^ space) param_docs)
    ^^ semi
    ^^ nest 4 (hardline ^^ fun_body)
    ^^ hardline ^^ string "endfunction"

  let sv_fundef ctx f params param_ctyps ret_ctyp body =
    let fun_body =
      if List.exists (fun unrf -> unrf = string_of_id f) Config.unreachable then string "sail_reached_unreachable = 1;"
      else
        wrap_type ret_ctyp (sv_name Jib_util.return)
        ^^ semi ^^ hardline
        ^^ separate_map hardline (sv_checked_instr ctx) body
    in
    sv_fundef_with ctx (sv_id_string f) params param_ctyps ret_ctyp fun_body

  let filter_clear = filter_instrs (function I_aux (I_clear _, _) -> false | _ -> true)

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

  let sv_setup_function ctx name setup =
    let setup =
      Jib_optimize.(
        setup |> flatten_instrs |> remove_dead_code |> variable_decls_to_top |> structure_control_flow_block
        |> remove_undefined |> filter_clear
      )
    in
    separate space [string "function"; string "automatic"; string "void"; string name]
    ^^ string "()" ^^ semi
    ^^ nest 4 (hardline ^^ separate_map hardline (sv_checked_instr ctx) setup)
    ^^ hardline ^^ string "endfunction" ^^ twice hardline

  let collect_registers cdefs =
    List.fold_left
      (fun rmap cdef ->
        match cdef with
        | CDEF_register (id, ctyp, _) ->
            CTMap.update ctyp (function Some ids -> Some (id :: ids) | None -> Some [id]) rmap
        | _ -> rmap
      )
      CTMap.empty cdefs

  let sv_register_references cdefs =
    let rmap = collect_registers cdefs in
    let reg_ref id = "SAIL_REG_" ^ Util.zencode_upper_string (string_of_id id) in
    let reg_ref_enums =
      List.map
        (fun (ctyp, regs) ->
          separate space [string "typedef"; string "enum"; lbrace]
          ^^ nest 4 (hardline ^^ separate_map (comma ^^ hardline) (fun r -> string (reg_ref r)) regs)
          ^^ hardline ^^ rbrace ^^ space
          ^^ ksprintf string "sail_reg_%s" (Util.zencode_string (string_of_ctyp ctyp))
          ^^ semi
        )
        (CTMap.bindings rmap)
      |> separate (twice hardline)
    in
    let reg_ref_functions =
      List.map
        (fun (ctyp, regs) ->
          let encoded = Util.zencode_string (string_of_ctyp ctyp) in
          let sv_ty, index_ty = sv_ctyp ctyp in
          let sv_ty, typedef =
            match index_ty with
            | Some index ->
                let new_ty = string ("t_reg_deref_" ^ encoded) in
                (new_ty, separate space [string "typedef"; string sv_ty; new_ty; string index] ^^ semi ^^ twice hardline)
            | None -> (string sv_ty, empty)
          in
          typedef
          ^^ separate space [string "function"; string "automatic"; sv_ty]
          ^^ space
          ^^ string ("sail_reg_deref_" ^ encoded)
          ^^ parens (string ("sail_reg_" ^ encoded) ^^ space ^^ char 'r')
          ^^ semi
          ^^ nest 4
               (hardline
               ^^ separate_map hardline
                    (fun reg ->
                      separate space
                        [
                          string "if";
                          parens (separate space [char 'r'; string "=="; string (reg_ref reg)]);
                          string "begin";
                        ]
                      ^^ nest 4 (hardline ^^ string "return" ^^ space ^^ sv_id reg ^^ semi)
                      ^^ hardline ^^ string "end" ^^ semi
                    )
                    regs
               )
          ^^ hardline ^^ string "endfunction" ^^ twice hardline
          ^^ separate space [string "function"; string "automatic"; string "void"]
          ^^ space
          ^^ string ("sail_reg_assign_" ^ encoded)
          ^^ parens (separate space [string ("sail_reg_" ^ encoded); char 'r' ^^ comma; wrap_type ctyp (char 'v')])
          ^^ semi
          ^^ nest 4
               (hardline
               ^^ separate_map hardline
                    (fun reg ->
                      separate space
                        [
                          string "if";
                          parens (separate space [char 'r'; string "=="; string (reg_ref reg)]);
                          string "begin";
                        ]
                      ^^ nest 4 (hardline ^^ sv_id reg ^^ space ^^ equals ^^ space ^^ char 'v' ^^ semi)
                      ^^ hardline ^^ string "end" ^^ semi
                    )
                    regs
               )
          ^^ hardline ^^ string "endfunction"
        )
        (CTMap.bindings rmap)
      |> separate (twice hardline)
    in
    (reg_ref_enums ^^ twice hardline, reg_ref_functions ^^ twice hardline)

  type cdef_doc = { outside_module : document; inside_module_prefix : document; inside_module : document }

  let empty_cdef_doc = { outside_module = empty; inside_module_prefix = empty; inside_module = empty }

  let sv_cdef ctx fn_ctyps setup_calls = function
    | CDEF_register (id, ctyp, setup) ->
        let binding_doc = wrap_type ctyp (sv_id id) ^^ semi ^^ twice hardline in
        let name = sprintf "sail_setup_reg_%s" (sv_id_string id) in
        ( { empty_cdef_doc with inside_module_prefix = binding_doc; inside_module = sv_setup_function ctx name setup },
          fn_ctyps,
          name :: setup_calls
        )
    | CDEF_type td -> ({ empty_cdef_doc with outside_module = sv_type_def td ^^ twice hardline }, fn_ctyps, setup_calls)
    | CDEF_val (f, _, param_ctyps, ret_ctyp) ->
        (empty_cdef_doc, Bindings.add f (param_ctyps, ret_ctyp) fn_ctyps, setup_calls)
    | CDEF_fundef (f, _, params, body) ->
        if List.mem (string_of_id f) Config.ignore then (empty_cdef_doc, fn_ctyps, setup_calls)
        else (
          let body =
            Jib_optimize.(
              body |> flatten_instrs |> remove_dead_code |> variable_decls_to_top |> structure_control_flow_block
              |> remove_undefined |> filter_clear
            )
          in
          begin
            match Bindings.find_opt f fn_ctyps with
            | Some (param_ctyps, ret_ctyp) ->
                ( {
                    empty_cdef_doc with
                    inside_module = sv_fundef ctx f params param_ctyps ret_ctyp body ^^ twice hardline;
                  },
                  fn_ctyps,
                  setup_calls
                )
            | None -> Reporting.unreachable (id_loc f) __POS__ ("No function type found for " ^ string_of_id f)
          end
        )
    | CDEF_let (n, bindings, setup) ->
        let bindings_doc =
          separate_map (semi ^^ hardline) (fun (id, ctyp) -> wrap_type ctyp (sv_id id)) bindings
          ^^ semi ^^ twice hardline
        in
        let name = sprintf "sail_setup_let_%d" n in
        ( { empty_cdef_doc with inside_module = bindings_doc ^^ sv_setup_function ctx name setup },
          fn_ctyps,
          name :: setup_calls
        )
    | _ -> (empty_cdef_doc, fn_ctyps, setup_calls)

  let main_args main fn_ctyps =
    match main with
    | Some (CDEF_fundef (f, _, params, body)) -> begin
        match Bindings.find_opt f fn_ctyps with
        | Some (param_ctyps, ret_ctyp) -> begin
            let main_args =
              List.map2
                (fun param param_ctyp -> match param_ctyp with CT_unit -> string "SAIL_UNIT" | _ -> sv_id param)
                params param_ctyps
            in
            let non_unit =
              List.filter_map
                (fun x -> x)
                (List.map2
                   (fun param param_ctyp -> match param_ctyp with CT_unit -> None | _ -> Some (param, param_ctyp))
                   params param_ctyps
                )
            in
            let module_main_in =
              List.map
                (fun (param, param_ctyp) -> string "input" ^^ space ^^ wrap_type param_ctyp (sv_id param))
                non_unit
            in
            match ret_ctyp with
            | CT_unit -> (main_args, None, module_main_in)
            | _ ->
                ( main_args,
                  Some (string "main_result"),
                  (string "output" ^^ space ^^ wrap_type ret_ctyp (string "main_result")) :: module_main_in
                )
          end
        | None -> Reporting.unreachable (id_loc f) __POS__ ("No function type found for " ^ string_of_id f)
      end
    | _ -> ([], None, [])

  let make_call_precise ctx id =
    if ctx_is_extern id ctx then (
      let name = ctx_get_extern id ctx in
      Option.is_none (Smt.builtin name)
    )
    else true
end
