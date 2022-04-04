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
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

open Ast
open Ast_util
open Printf
open Gdbmi_types

let parse_gdb_response str =
  let lexbuf = Lexing.from_string str in
  Gdbmi_parser.response_eof Gdbmi_lexer.token lexbuf

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
    line
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
     let cmd = sprintf "%i-%s\n" token cmd in
     print_string Util.(cmd |> yellow |> clear);
     flush stdin;
     output_string stdin cmd;
     flush stdin;
     wait_for token stdout

let send_regular session cmd =
  match session with
  | None -> raise not_connected
  | Some (stdout, stdin, _) ->
     let token = gdb_token () in
     print_endline Util.(cmd |> yellow |> clear);
     flush stdin;
     output_string stdin (cmd ^ "\n");
     flush stdin;
     ignore (wait_for_gdb stdout)

let synced_registers = ref []

let gdb_sync session =
  let gdb_register_names = parse_gdb_response (send_sync session "data-list-register-names") in
  let gdb_register_values = parse_gdb_response (send_sync session "data-list-register-values x") in
  let names = match gdb_register_names with
    | Result (_, "done", output) ->
       List.assoc "register-names" output |> gdb_seq |> List.map gdb_string
    | _ -> failwith "GDB could not get register names"
  in
  let values = match gdb_register_values with
    | Result (_, "done", output) ->
       List.assoc "register-values" output
       |> gdb_seq
       |> List.map gdb_assoc
       |> List.map (List.assoc "value")
       |> List.map gdb_string
    | _ -> failwith "GDB could not get register names"
  in
  synced_registers := List.combine names values

let gdb_list_registers session =
  gdb_sync session;
  List.iter (fun (name, value) ->
      print_endline (sprintf "%s: %s" name value)
    ) !synced_registers

let gdb_read_mem session addr data_size =
  let open Value in
  let cmd = sprintf "data-read-memory %s x 1 1 %i" (Sail_lib.string_of_bits addr) (Big_int.to_int data_size) in
  (* An example response looks something like:

     7^done,addr="0x0000000040009e64",nr-bytes="4",total-bytes="4",next-row="0x0000000040009e68",
     prev-row="0x0000000040009e60",next-page="0x0000000040009e68",prev-page="0x0000000040009e60",
     memory=[{addr="0x0000000040009e64",data=["0x03","0xfc","0x5a","0xd3"]}]
     *)
  match parse_gdb_response (send_sync session cmd) with
  | Result (_, "done", output) ->
     List.assoc "memory" output |> gdb_seq
     |> List.hd |> gdb_assoc
     |> List.assoc "data" |> gdb_seq
     |> List.rev_map (fun byte -> Sail_lib.byte_of_int (int_of_string (gdb_string byte)))
     |> List.concat

  | _ -> failwith "Unexpected response from GDB"

let value_gdb_read_ram session =
  let open Value in
  function
  | [addr_size; data_size; _; addr] ->
     mk_vector (gdb_read_mem session (coerce_bv addr) (coerce_int data_size))

  | _ -> failwith "gdb_read_ram"

let gdb_effect_interp session state eff =
  let open Value in
  let open Interpreter in
  let lstate, gstate = state in
  match eff with
  | Read_mem (rk, addr, len, cont) ->
     let result = mk_vector (gdb_read_mem session (coerce_bv addr) (coerce_int len)) in
     cont result state
  | Read_reg (name, cont) ->
     begin match List.assoc_opt name !synced_registers with
     | Some value ->
        let value = mk_vector (Sail_lib.to_bits' (64, Big_int.of_string value)) in
        cont value state
     | None ->
        cont (Bindings.find (mk_id name) gstate.registers) state
     end
  | Write_reg (name, v, cont) ->
     let id = mk_id name in
     if Bindings.mem id gstate.registers then
       let state' = (lstate, { gstate with registers = Bindings.add id v gstate.registers }) in
       cont () state'
     else
       failwith ("Write of nonexistent register: " ^ name)
  | _ ->
     failwith "Unsupported in GDB state"

let gdb_hooks session =
  Value.add_primop "read_ram" (value_gdb_read_ram session);
  Interpreter.set_effect_interp (gdb_effect_interp session)

let () =
  let open Interactive in
  let session = ref None in

  let gdb_start arg =
    let stdout, stdin, stderr = Unix.open_process_full (sprintf "%s --interpreter=mi" !gdb_command) [||] in
    session := Some (stdout, stdin, stderr);
    wait_for_gdb stdout |> ignore;
    if arg = "" then () else print_endline (send_sync !session arg)
  in

  let gdb_send arg =
    if arg = "" then () else print_endline (send_sync !session arg)
  in

  register_command
    ~name:"gdb_command"
    ~help:"Use specified gdb. Default is gdb-multiarch. This is the \
           correct version on Ubuntu, but other Linux distros and \
           operating systems may differ in how they package gdb with \
           support for multiple architectures."
    (ArgString ("gdb", fun arg -> ActionUnit (fun _ -> gdb_command := arg)));

  register_command
    ~name:"gdb_start"
    ~help:"Start a child GDB process sending :0 as the first command, waiting for it to complete"
    (ArgString ("command", fun cmd -> ActionUnit (fun _ -> gdb_start cmd)));

  (ArgString ("port", fun port -> ActionUnit (fun _ ->
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
    (ArgString ("command", fun cmd -> ActionUnit (fun _ -> gdb_send cmd)));

  register_command
    ~name:"gdb_sync"
    ~help:"Sync sail registers with GDB"
    (ActionUnit (fun _ -> gdb_sync !session));

  register_command
    ~name:"gdb_list_registers"
    ~help:"Sync sail registers with GDB and list them"
    (ActionUnit (fun _ -> gdb_list_registers !session));

  register_command
    ~name:"gdb_hooks"
    ~help:"Make reading and writing memory go via GDB"
    (ActionUnit (fun _ -> gdb_hooks !session));

  (ArgString ("symbol_file", fun file -> ActionUnit (fun _ ->
    send_regular !session ("symbol-file " ^ file)
  ))) |> register_command
           ~name:"gdb_symbol_file"
           ~help:"Load debugging symbols into GDB";
