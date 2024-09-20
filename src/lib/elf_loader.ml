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

module Big_int = Nat_big_num

let opt_elf_threads = ref 1
let opt_elf_entry = ref Big_int.zero
let opt_elf_tohost = ref Big_int.zero

(* the type of elf last loaded, and its symbol map *)
type elf_class = ELF_Class_64 | ELF_Class_32
let opt_elf_class = ref ELF_Class_64 (* default *)
let opt_symbol_map = ref ([] : Elf_file.global_symbol_init_info)

type word8 = int

let escape_char c = if int_of_char c <= 31 then '.' else if int_of_char c >= 127 then '.' else c

let hex_line bs =
  let hex_char i c = (if i mod 2 == 0 && i <> 0 then " " else "") ^ Printf.sprintf "%02x" (int_of_char c) in
  String.concat "" (List.mapi hex_char bs)
  ^ " "
  ^ String.concat "" (List.map (fun c -> Printf.sprintf "%c" (escape_char c)) bs)

let break n xs =
  let rec helper acc = function
    | [] -> List.rev acc
    | _ :: _ as xs -> helper ([Lem_list.take n xs] @ acc) (Lem_list.drop n xs)
  in
  helper [] xs

let print_segment bs =
  prerr_endline "0011 2233 4455 6677 8899 aabb ccdd eeff 0123456789abcdef";
  List.iter (fun bs -> prerr_endline (hex_line bs)) (break 16 (Byte_sequence.char_list_of_byte_sequence bs))

type elf_segs =
  | ELF64 of Elf_interpreted_segment.elf64_interpreted_segment list
  | ELF32 of Elf_interpreted_segment.elf32_interpreted_segment list

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

  (* remove all the auto generated segments (they contain only 0s) *)
  let prune_segments segs =
    Lem_list.mapMaybe (fun (seg, prov) -> if prov = Elf_file.FromELF then Some seg else None) segs
  in
  let segments, e_entry, _e_machine =
    begin
      match (elf_epi, elf_file) with
      | Sail_interface.ELF_Class_32 (segments, e_entry, e_machine), Elf_file.ELF_File_32 _ ->
          (ELF32 (prune_segments segments), e_entry, e_machine)
      | Sail_interface.ELF_Class_64 (segments, e_entry, e_machine), Elf_file.ELF_File_64 _ ->
          (ELF64 (prune_segments segments), e_entry, e_machine)
      | _, _ -> failwith "cannot handle ELF file"
    end
  in
  (segments, e_entry, symbol_map)

let write_sail_lib paddr i byte = Sail_lib.wram (Big_int.add paddr (Big_int.of_int i)) byte

let write_mem_zeros start len =
  (* write in order for mem tracing logs *)
  let i = ref Big_int.zero in
  while Big_int.less !i len do
    Sail_lib.wram (Big_int.add start !i) 0;
    i := Big_int.succ !i
  done

let write_file chan paddr i byte =
  output_string chan (Big_int.to_string (Big_int.add paddr (Big_int.of_int i)) ^ "\n");
  output_string chan (string_of_int byte ^ "\n")

let print_seg_info offset base paddr size memsz =
  prerr_endline "\nLoading Segment";
  prerr_endline ("Segment offset: " ^ Printf.sprintf "0x%Lx" (Big_int.to_int64 offset));
  prerr_endline ("Segment base address: " ^ Big_int.to_string base);
  (* NB don't attempt to convert paddr to int64 because on MIPS it is quite likely to exceed signed
     64-bit range e.g. addresses beginning 0x9.... Really need to_uint64 or to_string_hex but lem
     doesn't have them. *)
  prerr_endline ("Segment physical address: " ^ Printf.sprintf "0x%Lx" (Big_int.to_int64 paddr));
  prerr_endline ("Segment size: " ^ Printf.sprintf "0x%Lx" (Big_int.to_int64 size));
  prerr_endline ("Segment memsz: " ^ Printf.sprintf "0x%Lx" (Big_int.to_int64 memsz))

let load_segment ?(writer = write_sail_lib) bs paddr base offset size memsz =
  print_seg_info offset base paddr size memsz;
  print_segment bs;
  List.iteri (writer paddr) (List.rev_map int_of_char (List.rev (Byte_sequence.char_list_of_byte_sequence bs)));
  write_mem_zeros (Big_int.add paddr size) (Big_int.sub memsz size)

let load_elf ?(writer = write_sail_lib) name =
  let segments, e_entry, symbol_map = read name in
  opt_elf_entry := e_entry;
  opt_symbol_map := symbol_map;
  if List.mem_assoc "tohost" symbol_map then (
    let _, _, tohost_addr, _, _ = List.assoc "tohost" symbol_map in
    opt_elf_tohost := tohost_addr
  );
  match segments with
  | ELF64 segs ->
      List.iter
        (fun seg ->
          let open Elf_interpreted_segment in
          let bs = seg.elf64_segment_body in
          let paddr = seg.elf64_segment_paddr in
          let base = seg.elf64_segment_base in
          let offset = seg.elf64_segment_offset in
          let size = seg.elf64_segment_size in
          let memsz = seg.elf64_segment_memsz in
          load_segment ~writer bs paddr base offset size memsz
        )
        segs;
      opt_elf_class := ELF_Class_64
  | ELF32 segs ->
      List.iter
        (fun seg ->
          let open Elf_interpreted_segment in
          let bs = seg.elf32_segment_body in
          let paddr = seg.elf32_segment_paddr in
          let base = seg.elf32_segment_base in
          let offset = seg.elf32_segment_offset in
          let size = seg.elf32_segment_size in
          let memsz = seg.elf32_segment_memsz in
          load_segment ~writer bs paddr base offset size memsz
        )
        segs;
      opt_elf_class := ELF_Class_32

let load_binary ?(writer = write_sail_lib) addr name =
  let f = open_in_bin name in
  let buf = Buffer.create 1024 in
  try
    while true do
      let char = input_char f in
      Buffer.add_char buf char
    done;
    assert false
  with
  | End_of_file -> begin
      Bytes.iteri (fun i ch -> writer addr i (int_of_char ch)) (Buffer.to_bytes buf);
      close_in f
    end
  | exc ->
      close_in f;
      raise exc

(* The sail model can access this by externing a unit -> int function
   as Elf_loader.elf_entry. *)
let elf_entry () = !opt_elf_entry

(* Used by RISCV sail model test harness for exiting test *)
let elf_tohost () = !opt_elf_tohost

(* Used to check last loaded elf class. *)
let elf_class () = !opt_elf_class

(* Lookup the address for a symbol *)
let elf_symbol symbol =
  if List.mem_assoc symbol !opt_symbol_map then (
    let _, _, addr, _, _ = List.assoc symbol !opt_symbol_map in
    Some addr
  )
  else None

(* Get all symbols *)
let elf_symbols () = !opt_symbol_map
