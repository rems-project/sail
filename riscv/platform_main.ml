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

open Elf_loader
open Sail_lib
open Riscv
module PI = Platform_impl
module P = Platform

(* OCaml driver for generated RISC-V model. *)

let opt_file_arguments = ref ([] : string list)

let opt_dump_dts = ref false
let opt_dump_dtb = ref false

let options = Arg.align ([("-dump-dts",
                           Arg.Set opt_dump_dts,
                           " dump the platform device-tree source to stdout");
                          ("-dump-dtb",
                           Arg.Set opt_dump_dtb,
                           " dump the *binary* platform device-tree blob to stdout");
                          ("-enable-dirty-update",
                           Arg.Set P.config_enable_dirty_update,
                           " enable dirty-bit update during page-table walks");
                          ("-enable-misaligned-access",
                           Arg.Set P.config_enable_misaligned_access,
                           " enable misaligned accesses without M-mode traps")
                         ])

let usage_msg = "RISC-V platform options:"

let elf_arg =
  Arg.parse options (fun s -> opt_file_arguments := !opt_file_arguments @ [s])
            usage_msg;
  if !opt_dump_dts then (PI.dump_dts (); exit 0);
  if !opt_dump_dtb then (PI.dump_dtb (); exit 0);
  ( match !opt_file_arguments with
      | f :: _ -> prerr_endline ("Sail/RISC-V: running ELF file " ^ f); f
      | _ -> (prerr_endline "Please provide an ELF file."; exit 0)
  )

let run pc =
  sail_call
    (fun r ->
      try ( zinit_platform (); (* devices *)
            zinit_sys ();      (* processor *)
            zPC := pc;
            zloop ()
          )
      with
        | ZError_not_implemented (zs) ->
              print_string ("Error: Not implemented: ", zs)
        | ZError_internal_error (_) ->
              prerr_endline "Error: internal error"
    )

let show_times init_s init_e run_e insts =
  let init_time = init_e.Unix.tms_utime -. init_s.Unix.tms_utime in
  let exec_time = run_e.Unix.tms_utime -. init_e.Unix.tms_utime in
  Printf.eprintf "\nInitialization: %g secs\n" init_time;
  Printf.eprintf "Execution: %g secs\n" exec_time;
  Printf.eprintf "Instructions retired: %Ld\n" insts;
  Printf.eprintf "Perf: %g ips\n" ((Int64.to_float insts) /. exec_time)

let () =
  Random.self_init ();

  let init_start = Unix.times () in
  let pc = Platform.init elf_arg in
  let init_end = Unix.times () in
  let _ = run pc in
  let run_end = Unix.times () in
  let insts = Big_int.to_int64 (uint (!Riscv.zminstret)) in
  show_times init_start init_end run_end insts
