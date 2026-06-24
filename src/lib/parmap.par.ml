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

open Effect
open Effect.Deep

let opt_sequential = ref false

type channels = in_channel * out_channel * in_channel

type open_result = Unix.process_status * string * string

type _ Effect.t += Open_process_full : (string * string Array.t * string option) -> open_result t

module ParUnix = struct
  let open_process_full cmd env to_stdin = perform (Open_process_full (cmd, env, to_stdin))
end

let recommended_parallelism () = Domain.recommended_domain_count ()

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

let parmap (type a b) ~parallelism f (xs : a list) : b list =
  let xs = Array.of_list xs in
  let len = Array.length xs in
  let tmp : b option Array.t = Array.make len None in
  let waiting : (int * int * channels * (open_result, unit) continuation) Queue.t = Queue.create () in
  let next = ref 0 in
  let run i action =
    match action () with
    | effect Open_process_full (cmd, env, to_stdin), cont ->
        let ((_, stdin, _) as channels) = Unix.open_process_full cmd env in
        (match to_stdin with None -> () | Some str -> output_string stdin str);
        let pid = Unix.process_full_pid channels in
        close_out stdin;
        Queue.add (i, pid, channels, cont) waiting
    | y -> tmp.(i) <- Some y
  in
  let rec go () =
    if not (!next = len && Queue.is_empty waiting) then (
      (* Find any waiting task which has finished, removing it from the queue. *)
      let ready =
        let pending = Queue.length waiting in
        let rec scan k =
          if k = 0 then None
          else (
            let i, pid, channels, cont = Queue.pop waiting in
            let res, status = Unix.waitpid [Unix.WNOHANG] pid in
            if res = 0 then (
              Queue.add (i, pid, channels, cont) waiting;
              scan (k - 1)
            )
            else (
              let out_chan, _, err_chan = channels in
              let out_str = read_all out_chan in
              let err_str = read_all err_chan in
              close_in out_chan;
              close_in err_chan;
              Some ((status, out_str, err_str), cont)
            )
          )
        in
        scan pending
      in
      ( match ready with
      | Some (result, cont) -> continue cont result
      | None ->
          if Queue.length waiting >= parallelism then ()
          else (
            let i = !next in
            if i = len then ()
            else (
              incr next;
              run i (fun () -> f xs.(i))
            )
          )
      );
      go ()
    )
  in
  go ();
  Option.get (Util.option_all (Array.to_list tmp))

let map ~parallelism f xs = if !opt_sequential then List.map f xs else parmap ~parallelism f xs

let run_process cmd env to_stdin =
  let out_chan, in_chan, err_chan = Unix.open_process_full cmd env in
  (match to_stdin with None -> () | Some str -> output_string in_chan str);
  close_out in_chan;
  let stdout_str = read_all out_chan in
  let stderr_str = read_all err_chan in
  let status = Unix.close_process_full (out_chan, in_chan, err_chan) in
  (status, stdout_str, stderr_str)

let toplevel_handler f =
  let rec run action =
    match action () with
    | effect Open_process_full (cmd, env, to_stdin), cont -> run (fun () -> continue cont (run_process cmd env to_stdin))
    | () -> ()
  in
  run f
