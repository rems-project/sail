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

open Log

module Io = struct
  type 'a t = 'a

  let return x = x
  let raise = raise

  module O = struct
    let ( let+ ) x f = f x
    let ( let* ) x f = f x
  end
end

module Chan = struct
  type input = in_channel
  type output = out_channel

  let read_line ic = try Some (input_line ic) with End_of_file -> None

  let read_exactly ic n =
    let buf = Bytes.create n in
    try
      really_input ic buf 0 n;
      Some (Bytes.to_string buf)
    with End_of_file -> None

  let write oc parts =
    List.iter (output_string oc) parts;
    flush oc
end

module LspIo = Lsp.Io.Make (Io) (Chan)

let send oc packet = LspIo.write oc packet

let handle_request oc (req : Jsonrpc.Request.t) =
  let open Jsonrpc in
  let resp =
    match Lsp.Client_request.of_jsonrpc req with
    | Error msg -> Response.error req.id (Response.Error.make ~code:Response.Error.Code.InvalidRequest ~message:msg ())
    | Ok (Lsp.Client_request.E r) -> (
        let result =
          match r with
          | Lsp.Client_request.Initialize params ->
              Ok (Lsp.Client_request.yojson_of_result r (Handler.on_initialize params))
          | Lsp.Client_request.Shutdown ->
              Handler.on_shutdown ();
              Ok (Lsp.Client_request.yojson_of_result r ())
          | Lsp.Client_request.SemanticTokensFull params ->
              Ok (Lsp.Client_request.yojson_of_result r (Handler.on_semantic_tokens_full params))
          | Lsp.Client_request.TextDocumentFoldingRange params ->
              Ok (Lsp.Client_request.yojson_of_result r (Handler.on_folding_range params))
          | Lsp.Client_request.TextDocumentHover params ->
              Ok (Lsp.Client_request.yojson_of_result r (Handler.on_hover params))
          | Lsp.Client_request.TextDocumentDefinition params ->
              Ok (Lsp.Client_request.yojson_of_result r (Handler.on_definition params))
          | _ ->
              Error (Response.Error.make ~code:Response.Error.Code.MethodNotFound ~message:"method not implemented" ())
        in
        match result with Ok json -> Response.ok req.id json | Error err -> Response.error req.id err
      )
  in
  send oc (Packet.Response resp)

let rec run ~default_sail_dir () =
  match LspIo.read stdin with
  | None -> ()
  | Some packet ->
      ( match packet with
      | Jsonrpc.Packet.Request req -> (
          try handle_request stdout req with exn -> log_error "request handler raised: %s" (Printexc.to_string exn)
        )
      | Jsonrpc.Packet.Notification n -> (
          match Lsp.Client_notification.of_jsonrpc n with
          | Ok notif -> (
              try
                List.iter
                  (fun server_notif ->
                    let jsonrpc_notif = Lsp.Server_notification.to_jsonrpc server_notif in
                    send stdout (Jsonrpc.Packet.Notification jsonrpc_notif)
                  )
                  (Handler.on_notification ~default_sail_dir notif)
              with exn -> log_error "notification handler raised: %s" (Printexc.to_string exn)
            )
          | Error msg -> log_error "failed to decode notification: %s" msg
        )
      | _ -> ()
      );
      run ~default_sail_dir ()
