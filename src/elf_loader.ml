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

module Big_int = Nat_big_num

let opt_elf_threads = ref 1
let opt_elf_entry = ref Big_int.zero
let opt_elf_tohost = ref Big_int.zero

type word8 = int

let escape_char c =
  if int_of_char c <= 31 then '.'
  else if int_of_char c >= 127 then '.'
  else c

let hex_line bs =
  let hex_char i c =
    (if i mod 2 == 0 && i <> 0 then " " else "") ^ Printf.sprintf "%02x" (int_of_char c)
  in
  String.concat "" (List.mapi hex_char bs) ^ " " ^ String.concat "" (List.map (fun c -> Printf.sprintf "%c" (escape_char c)) bs)

let break n xs =
  let rec helper acc =function
    | [] -> List.rev acc
    | (_ :: _ as xs) -> helper ([Lem_list.take n xs] @ acc) (Lem_list.drop n xs)
  in helper [] xs

let print_segment seg =
  let bs = seg.Elf_interpreted_segment.elf64_segment_body in
  prerr_endline "0011 2233 4455 6677 8899 aabb ccdd eeff 0123456789abcdef";
  List.iter (fun bs -> prerr_endline (hex_line bs)) (break 16 (Byte_sequence.char_list_of_byte_sequence bs))

let read name =
  let info = Sail_interface.populate_and_obtain_global_symbol_init_info name in

  prerr_endline "Elf read:";
  let (elf_file, elf_epi, symbol_map) =
    begin match info with
    | Error.Fail s -> failwith (Printf.sprintf "populate_and_obtain_global_symbol_init_info: %s" s)
    | Error.Success ((elf_file: Elf_file.elf_file),
                     (elf_epi: Sail_interface.executable_process_image),
                     (symbol_map: Elf_file.global_symbol_init_info))
      ->
       (* XXX disabled because it crashes if entry_point overflows an ocaml int :-(
       prerr_endline (Sail_interface.string_of_executable_process_image elf_epi);*)
       (elf_file, elf_epi, symbol_map)
    end
  in

  prerr_endline "\nElf segments:";
  let (segments, e_entry, e_machine) =
    begin match elf_epi, elf_file with
    | (Sail_interface.ELF_Class_32 _, _) -> failwith "cannot handle ELF_Class_32"
    | (_, Elf_file.ELF_File_32 _)  -> failwith "cannot handle ELF_File_32"
    | (Sail_interface.ELF_Class_64 (segments, e_entry, e_machine), Elf_file.ELF_File_64 f1) ->
       (* remove all the auto generated segments (they contain only 0s) *)
       let segments =
         Lem_list.mapMaybe
           (fun (seg, prov) -> if prov = Elf_file.FromELF then Some seg else None)
           segments
       in
       (segments, e_entry, e_machine)
    end
  in
  (segments, e_entry, symbol_map)

let write_sail_lib paddr i byte =
  Sail_lib.wram (Big_int.add paddr (Big_int.of_int i)) byte

let write_mem_zeros start len =
  (* write in order for mem tracing logs *)
  let i = ref Big_int.zero in
  while (Big_int.less !i len) do
    Sail_lib.wram (Big_int.add start !i) 0;
    i := Big_int.succ !i
  done

let write_file chan paddr i byte =
  output_string chan (Big_int.to_string (Big_int.add paddr (Big_int.of_int i)) ^ "\n");
  output_string chan (string_of_int byte ^ "\n")

let load_segment ?writer:(writer=write_sail_lib) seg =
  let open Elf_interpreted_segment in
  let bs = seg.elf64_segment_body in
  let paddr = seg.elf64_segment_paddr in
  let base = seg.elf64_segment_base in
  let offset = seg.elf64_segment_offset in
  let size = seg.elf64_segment_size in
  let memsz = seg.elf64_segment_memsz in
  prerr_endline "\nLoading Segment";
  prerr_endline ("Segment offset: " ^ (Printf.sprintf "0x%Lx" (Big_int.to_int64 offset)));
  prerr_endline ("Segment base address: " ^ (Big_int.to_string base));
  (* NB don't attempt to convert paddr to int64 because on MIPS it is quite likely to exceed signed
     64-bit range e.g. addresses beginning 0x9.... Really need to_uint64 or to_string_hex but lem 
     doesn't have them. *)
  prerr_endline ("Segment physical address: " ^ (Printf.sprintf "0x%Lx" (Big_int.to_int64 paddr)));
  prerr_endline ("Segment size: " ^  (Printf.sprintf "0x%Lx" (Big_int.to_int64 size)));
  prerr_endline ("Segment memsz: " ^ (Printf.sprintf "0x%Lx" (Big_int.to_int64 memsz)));
  print_segment seg;
  List.iteri (writer paddr) (List.rev_map int_of_char (List.rev (Byte_sequence.char_list_of_byte_sequence bs)));
  write_mem_zeros (Big_int.add paddr size) (Big_int.sub memsz size)

let load_elf ?writer:(writer=write_sail_lib) name =
  let segments, e_entry, symbol_map = read name in
  opt_elf_entry := e_entry;
  (if List.mem_assoc "tohost" symbol_map then
     let (_, _, tohost_addr, _, _) = List.assoc "tohost" symbol_map in
     opt_elf_tohost := tohost_addr);
  List.iter (load_segment ~writer:writer) segments

(* The sail model can access this by externing a unit -> int function
   as Elf_loader.elf_entry. *)
let elf_entry () = !opt_elf_entry
(* Used by RISCV sail model test harness for exiting test *)
let elf_tohost () = !opt_elf_tohost
