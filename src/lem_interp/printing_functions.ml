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

open Printf
open Interp_ast
open Sail_impl_base
open Interp_utilities
open Interp_interface

open Nat_big_num

let lit_to_string = Pretty_interp.lit_to_string
let id_to_string = Pretty_interp.id_to_string
let loc_to_string = Pretty_interp.loc_to_string
let bitvec_to_string = Pretty_interp.bitvec_to_string
let collapse_leading = Pretty_interp.collapse_leading

type bits_lifted_homogenous = Bitslh_concrete of bit list | Bitslh_undef | Bitslh_unknown

let rec bits_lifted_homogenous_of_bit_lifteds' (bls : bit_lifted list) (acc : bits_lifted_homogenous) =
  match (bls, acc) with
  | [], _ -> Some acc
  | Bitl_zero :: bls', Bitslh_concrete bs ->
      bits_lifted_homogenous_of_bit_lifteds' bls' (Bitslh_concrete (bs @ [Bitc_zero]))
  | Bitl_one :: bls', Bitslh_concrete bs ->
      bits_lifted_homogenous_of_bit_lifteds' bls' (Bitslh_concrete (bs @ [Bitc_one]))
  | Bitl_undef :: bls', Bitslh_undef -> bits_lifted_homogenous_of_bit_lifteds' bls' Bitslh_undef
  | Bitl_unknown :: bls', Bitslh_unknown -> bits_lifted_homogenous_of_bit_lifteds' bls' Bitslh_unknown
  | _, _ -> None

let bits_lifted_homogenous_of_bit_lifteds (bls : bit_lifted list) : bits_lifted_homogenous option =
  let bls', acc0 =
    match bls with
    | [] -> ([], Bitslh_concrete [])
    | Bitl_zero :: bls' -> (bls', Bitslh_concrete [Bitc_zero])
    | Bitl_one :: bls' -> (bls', Bitslh_concrete [Bitc_one])
    | Bitl_undef :: bls' -> (bls', Bitslh_undef)
    | Bitl_unknown :: bls' -> (bls', Bitslh_unknown)
  in
  bits_lifted_homogenous_of_bit_lifteds' bls' acc0

(*let byte_it_lifted_to_string = function
  | BL0 -> "0"
  | BL1 ->  "1"
  | BLUndef -> "u"
  | BLUnknown -> "?"
*)

let bit_lifted_to_string = function Bitl_zero -> "0" | Bitl_one -> "1" | Bitl_undef -> "u" | Bitl_unknown -> "?"

let hex_int_to_string i =
  let s = Printf.sprintf "%x" i in
  if String.length s = 1 then "0" ^ s else s

let bytes_lifted_homogenous_to_string = function
  | Bitslh_concrete bs ->
      let i = to_int (Sail_impl_base.integer_of_bit_list bs) in
      hex_int_to_string i
  | Bitslh_undef -> "uu"
  | Bitslh_unknown -> "??"

let simple_bit_lifteds_to_string ?(collapse = true) bls (show_length_and_start : bool) (starto : int option) =
  let s = String.concat "" (List.map bit_lifted_to_string bls) in
  let s = if collapse then collapse_leading s else s in
  let len = string_of_int (List.length bls) in
  if show_length_and_start then (
    match starto with None -> len ^ "b" ^ s | Some start -> len ^ "b" ^ "_" ^ string_of_int start ^ "'" ^ s
  )
  else "0b" ^ s

(* if a multiple of 8 lifted bits and each chunk of 8 is homogenous,
   print as lifted hex, otherwise print as lifted bits *)
let bit_lifteds_to_string ?(collapse = true) (bls : bit_lifted list) (show_length_and_start : bool)
    (starto : int option) (abbreviate_zero_to_nine : bool) =
  let l = List.length bls in
  if l mod 8 = 0 then (
    (*  if List.mem l [8;16;32;64;128] then *)
    let bytesl = List.map (fun (Byte_lifted bs) -> bs) (Sail_impl_base.byte_lifteds_of_bit_lifteds bls) in
    let byteslhos = List.map bits_lifted_homogenous_of_bit_lifteds bytesl in
    match maybe_all byteslhos with
    | None ->
        (* print as bitvector after all *)
        simple_bit_lifteds_to_string ~collapse bls show_length_and_start starto
    | Some (byteslhs : bits_lifted_homogenous list) -> (
        (* if abbreviate_zero_to_nine, all bytes are concrete, and the number is <=9, just print that *)
        (*   (note that that doesn't print the length or start - it's appropriate only for memory values, where we typically have an explicit footprint also printed *)
        let nos =
          List.rev_map
            (function
              | Bitslh_concrete bs -> Some (Sail_impl_base.nat_of_bit_list bs)
              | Bitslh_undef -> None
              | Bitslh_unknown -> None
              )
            byteslhs
        in
        let lsb, msbs = (List.hd nos, List.tl nos) in
        match (abbreviate_zero_to_nine, List.for_all (fun no -> no = Some 0) msbs, lsb) with
        | true, true, Some n when n <= 9 -> string_of_int n
        | _ ->
            (* otherwise, print the bytes as hex *)
            let s = String.concat "" (List.map bytes_lifted_homogenous_to_string byteslhs) in
            if show_length_and_start then (
              match starto with None -> "0x" ^ s | Some start -> "0x" ^ "_" ^ string_of_int start ^ "'" ^ s
            )
            else "0x" ^ s
      )
  )
  else simple_bit_lifteds_to_string ~collapse bls show_length_and_start starto

let register_value_to_string rv = bit_lifteds_to_string rv.rv_bits true (Some rv.rv_start_internal) false

let memory_value_to_string endian mv =
  let bls = Sail_impl_base.match_endianness endian mv |> List.map (fun (Byte_lifted bs) -> bs) |> List.concat in
  bit_lifteds_to_string bls true None true

let logfile_register_value_to_string rv =
  bit_lifteds_to_string ~collapse:false rv.rv_bits false (Some rv.rv_start) false

let logfile_memory_value_to_string endian mv =
  let bls = Sail_impl_base.match_endianness endian mv |> List.map (fun (Byte_lifted bs) -> bs) |> List.concat in
  bit_lifteds_to_string bls false None false

let byte_list_to_string bs =
  let bs' = List.map byte_lifted_of_byte bs in
  memory_value_to_string E_big_endian bs'

let logfile_address_to_string a =
  let bs' = List.map byte_lifted_of_byte (byte_list_of_address a) in
  logfile_memory_value_to_string E_big_endian bs'

(*let bytes_to_string bytes =
   (String.concat ""
      (List.map (fun i -> hex_int_to_string i)
  (List.map (fun (Byte_lifted bs) -> bits_to_word8 bs) bytes)))*)

let bit_to_string = function Bitc_zero -> "0" | Bitc_one -> "1"

let reg_value_to_string v = "deprecated"
(* let l = List.length v.rv_bits in
   let start = string_of_int v.rv_start in
   if List.mem l [8;16;32;64;128] then
     let bytes = Interp_inter_imp.to_bytes v.rv_bits in
     "0x" ^ "_" ^ start ^ "'" ^ bytes_to_string bytes
   else (string_of_int l) ^ "_" ^ start ^ "'b" ^
     collapse_leading (List.fold_right (^) (List.map bit_lifted_to_string v.rv_bits) "")*)

let ifield_to_string v = "0b" ^ collapse_leading (List.fold_right ( ^ ) (List.map bit_to_string v) "")

(*let val_to_string v = match v with
    | Bitvector(bools, inc, fst)->
        let l = List.length bools in
        if List.mem l [8;16;32;64;128] then
          let Bytevector bytes = Interp_inter_imp.coerce_Bytevector_of_Bitvector v in
          "0x" ^
          "_" ^ (string_of_int (Big_int.int_of_big_int fst)) ^ "'" ^
          bytes_to_string bytes
        else
  (*    (string_of_int l) ^ " bits -- 0b" ^ collapse_leading (String.concat "" (List.map (function | true -> "1" | _ -> "0") bools))*)
          (string_of_int l) ^ "_" ^ (string_of_int (Big_int.int_of_big_int fst)) ^ "'b" ^ collapse_leading (String.concat "" (List.map (function | true -> "1" | _ -> "0") bools))
    | Bytevector bytes ->
      (* let l = List.length words in *)
      (*(string_of_int l) ^ " bytes -- " ^*)
        "0x" ^
        bytes_to_string bytes
    | Unknown0 -> "Unknown"*)

let half_byte_to_hex v =
  match v with
  | [false; false; false; false] -> "0"
  | [false; false; false; true] -> "1"
  | [false; false; true; false] -> "2"
  | [false; false; true; true] -> "3"
  | [false; true; false; false] -> "4"
  | [false; true; false; true] -> "5"
  | [false; true; true; false] -> "6"
  | [false; true; true; true] -> "7"
  | [true; false; false; false] -> "8"
  | [true; false; false; true] -> "9"
  | [true; false; true; false] -> "a"
  | [true; false; true; true] -> "b"
  | [true; true; false; false] -> "c"
  | [true; true; false; true] -> "d"
  | [true; true; true; false] -> "e"
  | [true; true; true; true] -> "f"
  | _ -> failwith "half_byte_to_hex given list of length longer than or shorter than 4"

let rec bit_to_hex v =
  match v with
  | [] -> ""
  | a :: b :: c :: d :: vs -> half_byte_to_hex [a; b; c; d] ^ bit_to_hex vs
  | _ -> failwith "bitstring given not divisible by 4"

(*let val_to_hex_string v = match v with
    | Bitvector(bools, _, _) -> "0x" ^ bit_to_hex bools
    | Bytevector words -> val_to_string v
    | Unknown0 -> "Error: cannot turn Unknown into hex"
  ;;*)

let dir_to_string = function D_increasing -> "inc" | D_decreasing -> "dec"

let reg_name_to_string = function
  | Reg (s, start, size, d) ->
      s (*^ "(" ^ (string_of_int start) ^ ", " ^ (string_of_int size) ^ ", " ^ (dir_to_string d) ^ ")"*)
  | Reg_slice (s, start, dir, (first, second)) ->
      let first, second =
        match dir with D_increasing -> (first, second) | D_decreasing -> (start - first, start - second)
      in
      s ^ "[" ^ string_of_int first ^ (if first = second then "" else ".." ^ string_of_int second) ^ "]"
  | Reg_field (s, _, _, f, _) -> s ^ "." ^ f
  | Reg_f_slice (s, start, dir, f, _, (first, second)) ->
      let first, second =
        match dir with D_increasing -> (first, second) | D_decreasing -> (start - first, start - second)
      in
      s ^ "." ^ f ^ "]" ^ string_of_int first ^ (if first = second then "" else ".." ^ string_of_int second) ^ "]"

let dependencies_to_string dependencies = String.concat ", " (List.map reg_name_to_string dependencies)

let rec top_frame_exp_state = function
  | Interp.Top -> raise (Invalid_argument "top_frame_exp")
  | Interp.Hole_frame (_, e, _, env, mem, Interp.Top) | Interp.Thunk_frame (e, _, env, mem, Interp.Top) ->
      (e, (env, mem))
  | Interp.Thunk_frame (_, _, _, _, s) | Interp.Hole_frame (_, _, _, _, _, s) -> top_frame_exp_state s

let tunk = (Unknown, None)
let ldots = E_aux (E_id (Id_aux (Id "...", Unknown)), tunk)
let rec compact_exp (E_aux (e, l)) =
  let wrap e = E_aux (e, l) in
  match e with
  | E_block (e :: _) -> compact_exp e
  | E_nondet (e :: _) -> compact_exp e
  | E_if (e, _, _) -> wrap (E_if (compact_exp e, ldots, E_aux (E_block [], tunk)))
  | E_for (i, e1, e2, e3, o, e4) -> wrap (E_for (i, compact_exp e1, compact_exp e2, compact_exp e3, o, ldots))
  | E_match (e, _) -> wrap (E_match (compact_exp e, []))
  | E_let (bind, _) -> wrap (E_let (bind, ldots))
  | E_app (f, args) -> wrap (E_app (f, List.map compact_exp args))
  | E_app_infix (l, op, r) -> wrap (E_app_infix (compact_exp l, op, compact_exp r))
  | E_tuple exps -> wrap (E_tuple (List.map compact_exp exps))
  | E_vector exps -> wrap (E_vector (List.map compact_exp exps))
  | E_vector_access (e1, e2) -> wrap (E_vector_access (compact_exp e1, compact_exp e2))
  | E_vector_subrange (e1, e2, e3) -> wrap (E_vector_subrange (compact_exp e1, compact_exp e2, compact_exp e3))
  | E_vector_update (e1, e2, e3) -> wrap (E_vector_update (compact_exp e1, compact_exp e2, compact_exp e3))
  | E_vector_update_subrange (e1, e2, e3, e4) ->
      wrap (E_vector_update_subrange (compact_exp e1, compact_exp e2, compact_exp e3, compact_exp e4))
  | E_vector_append (e1, e2) -> wrap (E_vector_append (compact_exp e1, compact_exp e2))
  | E_list exps -> wrap (E_list (List.map compact_exp exps))
  | E_cons (e1, e2) -> wrap (E_cons (compact_exp e1, compact_exp e2))
  | E_struct_update (e, fexps) -> wrap (E_struct_update (compact_exp e, fexps))
  | E_field (e, id) -> wrap (E_field (compact_exp e, id))
  | E_assign (lexp, e) -> wrap (E_assign (lexp, compact_exp e))
  | E_block [] | E_nondet [] | E_typ (_, _) | E_internal_cast (_, _) | _ -> wrap e

(* extract, compact and reverse expressions on the stack;
 * the top of the stack is the head of the returned list. *)
let rec compact_stack ?(acc = []) = function
  | Interp.Top -> acc
  | Interp.Hole_frame (_, e, _, env, mem, s) | Interp.Thunk_frame (e, _, env, mem, s) ->
      compact_stack ~acc:((compact_exp e, (env, mem)) :: acc) s

let sub_to_string = function None -> "" | Some (x, y) -> sprintf " (%s, %s)" (to_string x) (to_string y)

let format_tracking t = match t with Some rs -> "{ " ^ dependencies_to_string rs ^ "}" | None -> "None"

let rec format_events = function
  | [] -> "     Done\n"
  | [E_error s] -> "     Failed with message : " ^ s ^ "\n"
  | E_error s :: events -> "     Failed with message : " ^ s ^ " but continued on erroneously\n"
  | E_read_mem (read_kind, Address_lifted (location, _), length, tracking) :: events ->
      "     Read_mem at "
      ^ memory_value_to_string E_big_endian location
      ^ " based on registers " ^ format_tracking tracking ^ " for " ^ string_of_int length ^ " bytes \n"
      ^ format_events events
  | E_read_memt (read_kind, Address_lifted (location, _), length, tracking) :: events ->
      "     Read_memt at "
      ^ memory_value_to_string E_big_endian location
      ^ " based on registers " ^ format_tracking tracking ^ " for " ^ string_of_int length ^ " bytes \n"
      ^ format_events events
  | E_write_mem (write_kind, Address_lifted (location, _), length, tracking, value, v_tracking) :: events ->
      "     Write_mem at "
      ^ memory_value_to_string E_big_endian location
      ^ ", based on registers " ^ format_tracking tracking ^ ", writing "
      ^ memory_value_to_string E_big_endian value
      ^ ", based on " ^ format_tracking v_tracking ^ " across " ^ string_of_int length ^ " bytes\n"
      ^ format_events events
  | E_write_ea (write_kind, Address_lifted (location, _), length, tracking) :: events ->
      "     Write_ea at "
      ^ memory_value_to_string E_big_endian location
      ^ ", based on registers " ^ format_tracking tracking ^ " across " ^ string_of_int length ^ " bytes\n"
      ^ format_events events
  | E_excl_res :: events -> "     Excl_res\n" ^ format_events events
  | E_write_memv (_, value, v_tracking) :: events ->
      "     Write_memv of "
      ^ memory_value_to_string E_big_endian value
      ^ ", based on registers " ^ format_tracking v_tracking ^ "\n" ^ format_events events
  | E_write_memvt (_, (tag, value), v_tracking) :: events ->
      "     Write_memvt of "
      ^ memory_value_to_string E_big_endian value
      ^ ", based on registers " ^ format_tracking v_tracking ^ "\n" ^ format_events events
  | E_barrier b_kind :: events -> "     Memory_barrier occurred\n" ^ format_events events
  | E_read_reg reg_name :: events -> "     Read_reg of " ^ reg_name_to_string reg_name ^ "\n" ^ format_events events
  | E_write_reg (reg_name, value) :: events ->
      "     Write_reg of " ^ reg_name_to_string reg_name ^ " writing " ^ register_value_to_string value ^ "\n"
      ^ format_events events
  | E_escape :: events -> "     Escape event\n" ^ format_events events
  | E_footprint :: events -> "     Dynamic footprint calculation event\n" ^ format_events events

(* ANSI/VT100 colors *)
type ppmode = Interp_latex | Interp_ascii | Interp_html
let ppmode = ref Interp_ascii
let set_interp_ppmode ppm = ppmode := ppm

let disable_color = ref false

let set_color_enabled on = disable_color := not on

let color bright code s =
  if !disable_color then s else sprintf "\x1b[%s3%dm%s\x1b[m" (if bright then "1;" else "") code s
let red s =
  match !ppmode with
  | Interp_html -> "<fontcolor='red'>" ^ s ^ "</font>"
  | Interp_latex -> "\\myred{" ^ s ^ "}"
  | Interp_ascii -> color true 1 s
let green = color false 2
let yellow = color true 3
let blue = color true 4
let grey = color false 7

let exp_to_string env mem show_hole_value e = Pretty_interp.pp_exp env mem red show_hole_value e

let get_loc (E_aux (_, (l, (_ : tannot)))) = loc_to_string l
let print_exp printer env mem show_hole_value e =
  printer (get_loc e ^ ": " ^ Pretty_interp.pp_exp env mem red show_hole_value e ^ "\n")

let instruction_state_to_string (IState (stack, _)) =
  List.fold_right (fun (e, (env, mem)) es -> exp_to_string env mem true e ^ "\n" ^ es) (compact_stack stack) ""

let top_instruction_state_to_string (IState (stack, _)) =
  let exp, (env, mem) = top_frame_exp_state stack in
  exp_to_string env mem true exp

let instruction_stack_to_string (IState (stack, _)) =
  let rec stack_to_string = function
    | Interp.Top -> ""
    | Interp.Hole_frame (_, e, _, env, mem, Interp.Top) | Interp.Thunk_frame (e, _, env, mem, Interp.Top) ->
        exp_to_string env mem true e
    | Interp.Hole_frame (_, e, _, env, mem, s) | Interp.Thunk_frame (e, _, env, mem, s) ->
        exp_to_string env mem false e ^ "\n----------------------------------------------------------\n"
        ^ stack_to_string s
  in
  match stack with
  | Interp.Hole_frame (_, E_aux (E_id (Id_aux (Id "0", _)), _), _, _, _, s) -> stack_to_string s
  | _ -> stack_to_string stack

let rec option_map f xs =
  match xs with
  | [] -> []
  | x :: xs -> (
      match f x with None -> option_map f xs | Some x -> x :: option_map f xs
    )

let local_variables_to_string (IState (stack, _)) =
  let _, (env, mem) = top_frame_exp_state stack in
  match env with
  | Interp.LEnv (_, env) ->
      String.concat ", "
        (option_map
           (fun (id, value) ->
             match id with
             | "0" -> None (*Let's not print out the context hole again*)
             | _ -> Some (id ^ "=" ^ Interp.string_of_value value)
           )
           (Pmap.bindings_list env)
        )

let instr_parm_to_string (name, typ, value) =
  name ^ "="
  ^
  match typ with
  | Other -> "Unrepresentable external value"
  | _ -> (
      let intern_v = Interp_inter_imp.intern_ifield_value D_increasing value in
      match Interp_lib.to_num Interp_lib.Unsigned intern_v with
      | Interp_ast.V_lit (L_aux (L_num n, _)) -> to_string n
      | _ -> ifield_to_string value
    )

let rec instr_parms_to_string ps =
  match ps with
  | [] -> ""
  | [p] -> instr_parm_to_string p
  | p :: ps -> instr_parm_to_string p ^ " " ^ instr_parms_to_string ps

let pad n s = if String.length s < n then s ^ String.make (n - String.length s) ' ' else s

let instruction_to_string (name, parms) = (*pad 5*) String.lowercase name ^ " " ^ instr_parms_to_string parms

let print_backtrace_compact printer (IState (stack, _)) =
  List.iter (fun (e, (env, mem)) -> print_exp printer env mem true e) (compact_stack stack)

let print_stack printer is = printer (instruction_stack_to_string is)

let print_continuation printer (IState (stack, _)) =
  let e, (env, mem) = top_frame_exp_state stack in
  print_exp printer env mem true e
let print_instruction printer instr = printer (instruction_to_string instr)

let pp_instruction_state state () = (instruction_stack_to_string state, local_variables_to_string state)
