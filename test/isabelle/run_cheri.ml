open Cheri_export

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

let ( >> ) = Sail2_state_monad.bindS
(*let liftS = Sail2_state_lifting.liftState (Cheri_types.get_regval, Cheri_types.set_regval)*)

let load_elf_segment seg =
  let open Elf_interpreted_segment in
  let bs = seg.elf64_segment_body in
  let paddr = Big_int.big_int_of_string (Nat_big_num.to_string seg.elf64_segment_paddr) in
  let base = Big_int.big_int_of_string (Nat_big_num.to_string seg.elf64_segment_base) in
  let offset = Big_int.big_int_of_string (Nat_big_num.to_string seg.elf64_segment_offset) in
  let writer i byte = Cheri_code.write_char_mem (Arith.plus_int (Arith.Int_of_integer paddr) i) byte in
  prerr_endline "\nLoading Segment";
  prerr_endline ("Segment offset: " ^ Big_int.string_of_big_int offset);
  prerr_endline ("Segment base address: " ^ Big_int.string_of_big_int base);
  prerr_endline ("Segment physical address: " ^ Big_int.string_of_big_int paddr);
  print_segment seg;
  Sail2_state.iteriS writer (Byte_sequence.char_list_of_byte_sequence bs)

let _ =
  Random.self_init ();
  let elf_segments = match !opt_file_arguments with f :: _ -> load_elf f | _ -> [] in
  (* State_monad.prerr_results *)
  Cheri_code.initial_state |> (Sail2_state.iterS load_elf_segment elf_segments >> fun _ -> Cheri_code.mainS ())
