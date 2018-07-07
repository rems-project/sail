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
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
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

open Sail_lib;;
module P = Platform_impl;;
module Elf = Elf_loader;;

(* Platform configuration *)

let config_enable_dirty_update = ref false
let config_enable_misaligned_access = ref false

(* Mapping to Sail externs *)

let bits_of_int i =
  get_slice_int (Big_int.of_int 64, Big_int.of_int i, Big_int.zero)

let bits_of_int64 i =
  get_slice_int (Big_int.of_int 64, Big_int.of_int64 i, Big_int.zero)

let rom_size_ref = ref 0
let make_rom start_pc =
  let reset_vec = List.concat (List.map P.uint32_to_bytes (P.reset_vec_int start_pc)) in
  let dtb = P.make_dtb P.dts in
  let rom = reset_vec @ dtb in
  ( rom_size_ref := List.length rom;
    (*
    List.iteri (fun i c ->
                Printf.eprintf "rom[0x%Lx] <- %x\n"
                               (Int64.add P.rom_base (Int64.of_int i))
                               c
               ) rom;
     *)
    rom )

let enable_dirty_update () = !config_enable_dirty_update
let enable_misaligned_access () = !config_enable_misaligned_access

let rom_base () = bits_of_int64 P.rom_base
let rom_size () = bits_of_int   !rom_size_ref

let dram_base () = bits_of_int64 P.dram_base
let dram_size () = bits_of_int64 P.dram_size

let htif_tohost () =
  bits_of_int64 (Big_int.to_int64 (Elf.elf_tohost ()))

let clint_base () = bits_of_int64 P.clint_base
let clint_size () = bits_of_int64 P.clint_size

let insns_per_tick () = Big_int.of_int P.insns_per_tick

(* load reservation *)

let reservation = ref "none"  (* shouldn't match any valid address *)

let load_reservation addr =
  Printf.eprintf "reservation <- %s\n" (string_of_bits addr);
  reservation := string_of_bits addr

let match_reservation addr =
  Printf.eprintf "reservation: %s, key=%s\n" (!reservation) (string_of_bits addr);
  string_of_bits addr = !reservation

let cancel_reservation () =
  Printf.eprintf "reservation <- none\n";
  reservation := "none"

(* terminal I/O *)

let term_write char_bits =
  let big_char = Big_int.bitwise_and (uint char_bits) (Big_int.of_int 255) in
  P.term_write (char_of_int (Big_int.to_int big_char))

let term_read () =
  let c = P.term_read () in
  bits_of_int (int_of_char c)

(* returns starting value for PC, i.e. start of reset vector *)
let init elf_file =
  Elf.load_elf elf_file;

  Printf.eprintf "\nRegistered htif_tohost at 0x%Lx.\n" (Big_int.to_int64 (Elf.elf_tohost ()));
  Printf.eprintf "Registered clint at 0x%Lx (size 0x%Lx).\n%!" P.clint_base P.clint_size;

  let start_pc = Elf.Big_int.to_int64 (Elf.elf_entry ()) in
  let rom = make_rom start_pc in
  let rom_base = Big_int.of_int64 P.rom_base in
  let rec write_rom ofs = function
    | [] -> ()
    | h :: tl -> let addr = Big_int.add rom_base (Big_int.of_int ofs) in
                 (wram addr h);
                 write_rom (ofs + 1) tl
  in ( write_rom 0 rom;
       get_slice_int (Big_int.of_int 64, rom_base, Big_int.zero)
     )
