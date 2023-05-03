(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

(*module Big_int = Nat_big_num*)

let opt_elf_threads = ref 1
let opt_elf_entry = ref Nat_big_num.zero
let opt_elf_tohost = ref Nat_big_num.zero

type word8 = int

let escape_char c = if int_of_char c <= 31 then '.' else if int_of_char c >= 127 then '.' else c

let hex_line bs =
  let hex_char i c = (if i mod 2 == 0 && i <> 0 then " " else "") ^ Printf.sprintf "%02x" (int_of_char c) in
  String.concat "" (List.mapi hex_char bs)
  ^ " "
  ^ String.concat "" (List.map (fun c -> Printf.sprintf "%c" (escape_char c)) bs)

let rec break n = function [] -> [] | _ :: _ as xs -> [Lem_list.take n xs] @ break n (Lem_list.drop n xs)

let print_segment seg =
  let bs = seg.Elf_interpreted_segment.elf64_segment_body in
  prerr_endline "0011 2233 4455 6677 8899 aabb ccdd eeff 0123456789abcdef";
  List.iter (fun bs -> prerr_endline (hex_line bs)) (break 16 (Byte_sequence.char_list_of_byte_sequence bs))

let read name =
  let info = Sail_interface.populate_and_obtain_global_symbol_init_info name in

  prerr_endline "Elf read:";
  let elf_file, elf_epi, symbol_map =
    begin
      match info with
      | Error.Fail s -> failwith (Printf.sprintf "populate_and_obtain_global_symbol_init_info: %s" s)
      | Error.Success
          ( (elf_file : Elf_file.elf_file),
            (elf_epi : Sail_interface.executable_process_image),
            (symbol_map : Elf_file.global_symbol_init_info)
          ) ->
          (* XXX disabled because it crashes if entry_point overflows an ocaml int :-(
             prerr_endline (Sail_interface.string_of_executable_process_image elf_epi);*)
          (elf_file, elf_epi, symbol_map)
    end
  in

  prerr_endline "\nElf segments:";
  let segments, e_entry, e_machine =
    begin
      match (elf_epi, elf_file) with
      | Sail_interface.ELF_Class_32 _, _ -> failwith "cannot handle ELF_Class_32"
      | _, Elf_file.ELF_File_32 _ -> failwith "cannot handle ELF_File_32"
      | Sail_interface.ELF_Class_64 (segments, e_entry, e_machine), Elf_file.ELF_File_64 f1 ->
          (* remove all the auto generated segments (they contain only 0s) *)
          let segments =
            Lem_list.mapMaybe (fun (seg, prov) -> if prov = Elf_file.FromELF then Some seg else None) segments
          in
          (segments, e_entry, e_machine)
    end
  in
  (segments, e_entry, symbol_map)

(*let write_sail_lib paddr i byte =
  Sail_lib.wram (Nat_big_num.add paddr (Nat_big_num.of_int i)) byte*)

let write_file chan paddr i byte =
  output_string chan (Nat_big_num.to_string (Nat_big_num.add paddr (Nat_big_num.of_int i)) ^ "\n");
  output_string chan (string_of_int byte ^ "\n")

let load_elf name =
  let segments, e_entry, symbol_map = read name in
  opt_elf_entry := e_entry;
  if List.mem_assoc "tohost" symbol_map then (
    let _, _, tohost_addr, _, _ = List.assoc "tohost" symbol_map in
    opt_elf_tohost := tohost_addr
  );
  (*List.iter (load_segment ~writer:writer) segments*)
  segments

(* The sail model can access this by externing a unit -> Big_int.t function
   as Elf_loader.elf_entry. *)
let elf_entry () = Big_int.big_int_of_string (Nat_big_num.to_string !opt_elf_entry)

(* Used by RISCV sail model test harness for exiting test *)
let elf_tohost () = Big_int.big_int_of_string (Nat_big_num.to_string !opt_elf_tohost)
