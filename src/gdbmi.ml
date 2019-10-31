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

open Printf

type gdb_session = (in_channel * out_channel * in_channel) option

let gdb_command = ref "gdb-multiarch"

let gdb_token_counter = ref 0

let gdb_token () =
  incr gdb_token_counter;
  !gdb_token_counter

let not_connected = Reporting.err_general Parse_ast.Unknown "Not connected to gdb"

let rec wait_for' regexp stdout =
  let line = input_line stdout in
  if Str.string_match regexp line 0 then (
    print_endline line
  ) else (
    print_endline Util.(line |> dim |> clear);
    wait_for' regexp stdout
  )

let wait_for token stdout =
  let regexp = Str.regexp (sprintf "^%i\\^" token) in
  wait_for' regexp stdout

let wait_for_gdb stdout =
  let regexp = Str.regexp_string "(gdb)" in
  wait_for' regexp stdout

let send_sync session cmd =
  match session with
  | None -> raise not_connected
  | Some (stdout, stdin, _) ->
     let token = gdb_token () in
     let cmd =sprintf "%i-%s\n" token cmd in
     print_string Util.(cmd |> yellow |> clear);
     flush stdin;
     output_string stdin cmd;
     flush stdin;
     wait_for token stdout

let () =
  let open Interactive in
  let session = ref None in

  let gdb_start arg =
    let stdout, stdin, stderr = Unix.open_process_full (sprintf "%s --interpreter=mi" !gdb_command) [||] in
    session := Some (stdout, stdin, stderr);
    wait_for_gdb stdout;
    if arg = "" then () else send_sync !session arg
  in

  let gdb_send arg =
    if arg = "" then () else send_sync !session arg
  in

  register_command
    ~name:"gdb_command"
    ~help:"Use specified gdb. Default is gdb-multiarch. This is the \
           correct version on Ubuntu, but other Linux distros and \
           operating systems may differ in how they package gdb with \
           support for multiple architectures."
    (ArgString ("gdb", fun arg -> Action (fun () -> gdb_command := arg)));

  register_command
    ~name:"gdb_start"
    ~help:"Start a child GDB process sending :0 as the first command, waiting for it to complete"
    (ArgString ("command", fun cmd -> Action (fun () -> gdb_start cmd)));

  (ArgString ("port", fun port -> Action (fun () ->
    if port = "" then
      gdb_start "target-select remote localhost:1234"
    else
      gdb_start ("target-select remote localhost:" ^ port)
  ))) |> register_command
           ~name:"gdb_qemu"
           ~help:"Connect GDB to a remote QEMU target on localhost port :0 (default is 1234, as per -s option for QEMU)";

  register_command
    ~name:"gdb_send"
    ~help:"Send a GDB/MI command to a child GDB process and wait for it to complete"
    (ArgString ("command", fun cmd -> Action (fun () -> gdb_send cmd)));
