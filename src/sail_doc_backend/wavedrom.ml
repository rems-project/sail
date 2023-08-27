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

module Big_int = Nat_big_num

exception Invalid_wavedrom

(* Process the $[wavedrom] attribute for a vector concatentation pattern of length n *)
let process_attr_arg = function
  | None -> []
  | Some arg ->
      let labels = String.split_on_char ' ' arg |> List.filter (fun label -> label <> "") in
      List.map (function "_" -> None | label -> Some label) labels

let rec zip_labels xs ys =
  match (xs, ys) with
  | [], ys -> List.map (fun y -> (None, y)) ys
  | _, [] -> []
  | x :: xs, y :: ys -> (x, y) :: zip_labels xs ys

let wavedrom_label size = function
  | None -> Printf.sprintf ", attr: '%d'" size
  | Some label -> Printf.sprintf ", attr: ['%d', '%s']" size label

let binary_to_hex str =
  let open Sail2_values in
  let padded = match String.length str mod 4 with 0 -> str | 1 -> "000" ^ str | 2 -> "00" ^ str | _ -> "0" ^ str in
  Util.string_to_list padded
  |> List.map (function '0' -> B0 | _ -> B1)
  |> hexstring_of_bits |> Option.get
  |> Util.string_of_list "" (fun c -> String.make 1 c)

let rec wavedrom_elem_string size label (P_aux (aux, _)) =
  match aux with
  | P_id id ->
      Printf.sprintf "    { bits: %d, name: '%s'%s, type: 2 }" size (string_of_id id) (wavedrom_label size label)
  | P_lit (L_aux (L_bin bin, _)) ->
      Printf.sprintf "    { bits: %d, name: 0x%s%s, type: 8 }" size (binary_to_hex bin) (wavedrom_label size label)
  | P_lit (L_aux (L_hex hex, _)) ->
      Printf.sprintf "    { bits: %d, name: 0x%s%s, type: 8 }" size hex (wavedrom_label size label)
  | P_vector_subrange (_, n, m) when Big_int.equal n m ->
      Printf.sprintf "    { bits: %d, name: '[%s]'%s, type: 3 }" size (Big_int.to_string n) (wavedrom_label size label)
  | P_vector_subrange (id, n, m) ->
      Printf.sprintf "    { bits: %d, name: '%s[%s..%s]'%s, type: 3 }" size (string_of_id id) (Big_int.to_string n)
        (Big_int.to_string m) (wavedrom_label size label)
  | P_as (pat, _) | P_typ (_, pat) -> wavedrom_elem_string size label pat
  | _ -> raise Invalid_wavedrom

let wavedrom_elem (label, (P_aux (_, (_, tannot)) as pat)) =
  match Type_check.destruct_tannot tannot with
  | None -> raise Invalid_wavedrom
  | Some (env, typ) -> (
      match Type_check.destruct_bitvector env typ with
      | Some (Nexp_aux (Nexp_constant size, _)) ->
          let size = Big_int.to_int size in
          wavedrom_elem_string size label pat
      | _ -> raise Invalid_wavedrom
    )

let of_pattern' attr_arg = function
  | P_aux (P_vector_concat xs, _) ->
      let labels = process_attr_arg attr_arg in
      let elems = List.rev_map wavedrom_elem (zip_labels labels xs) in
      let strs = Util.string_of_list ",\n" (fun x -> x) elems in
      Printf.sprintf "{reg:[\n%s\n]}" strs
  | _ -> raise Invalid_wavedrom

let of_pattern ~labels:attr_arg pat = try Some (of_pattern' attr_arg pat) with Invalid_wavedrom -> None
