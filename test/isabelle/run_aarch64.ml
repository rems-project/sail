open Aarch64_export

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
(*  SPDX-License-Identifier: BSD-2-Clause                                 *)
(**************************************************************************)

open Elf_loader

let opt_file_arguments = ref ([] : string list)

let options = Arg.align []

let usage_msg = "Sail OCaml RTS options:"

let () = Arg.parse options (fun s -> opt_file_arguments := !opt_file_arguments @ [s]) usage_msg

let ( >> ) = Aarch64.bindS
let liftS = Aarch64.liftState (Aarch64.get_regval, Aarch64.set_regval)

let load_elf_segment seg =
  let open Elf_interpreted_segment in
  let open Aarch64_export in
  let bs = seg.elf64_segment_body in
  let paddr = Big_int.big_int_of_string (Nat_big_num.to_string seg.elf64_segment_paddr) in
  let base = Big_int.big_int_of_string (Nat_big_num.to_string seg.elf64_segment_base) in
  let offset = Big_int.big_int_of_string (Nat_big_num.to_string seg.elf64_segment_offset) in
  let writer i byte = Aarch64.write_char_mem (Aarch64.plus_int (Aarch64.Int_of_integer paddr) i) byte in
  prerr_endline "\nLoading Segment";
  prerr_endline ("Segment offset: " ^ Big_int.string_of_big_int offset);
  prerr_endline ("Segment base address: " ^ Big_int.string_of_big_int base);
  prerr_endline ("Segment physical address: " ^ Big_int.string_of_big_int paddr);
  print_segment seg;
  Aarch64.iteriS writer (Byte_sequence.char_list_of_byte_sequence bs)

let _ =
  Random.self_init ();
  let elf_segments = match !opt_file_arguments with f :: _ -> load_elf f | _ -> [] in
  Aarch64.prerr_results
    (Aarch64.initial_state |> (Aarch64.iterS load_elf_segment elf_segments >> fun _ -> liftS (Aarch64.main ())))
