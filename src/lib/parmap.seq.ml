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
(*  Copyright (c) 2013-2026                                                 *)
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

let opt_sequential = ref false

let read_all ch =
  let buf = Buffer.create 4096 in
  let chunk = Bytes.create 4096 in
  ( try
      while true do
        let n = input ch chunk 0 4096 in
        if n = 0 then raise End_of_file;
        Buffer.add_subbytes buf chunk 0 n
      done
    with End_of_file -> ()
  );
  Buffer.contents buf

let run_process cmd env to_stdin =
  let out_chan, in_chan, err_chan = Unix.open_process_full cmd env in
  (match to_stdin with None -> () | Some str -> output_string in_chan str);
  close_out in_chan;
  let stdout_str = read_all out_chan in
  let stderr_str = read_all err_chan in
  let status = Unix.close_process_full (out_chan, in_chan, err_chan) in
  (status, stdout_str, stderr_str)

module ParUnix = struct
  let open_process_full cmd env to_stdin = run_process cmd env to_stdin
end

let recommended_parallelism () = 1

let map ~parallelism:_ f xs = List.map f xs

let toplevel_handler f = f ()
