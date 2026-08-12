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

open Libsail

open Log

let file_to_handle : (string, Sail_file.handle) Hashtbl.t = Hashtbl.create 16
let handle_to_file : (Sail_file.handle, string) Hashtbl.t = Hashtbl.create 16

let register_handle file handle =
  Hashtbl.replace file_to_handle file handle;
  Hashtbl.replace handle_to_file handle file

let unregister_handle handle =
  (match Hashtbl.find_opt handle_to_file handle with Some file -> Hashtbl.remove file_to_handle file | None -> ());
  Hashtbl.remove handle_to_file handle

(* Search the directory containing [file] and its ancestors for the closest
   file with a [.sail_project] extension, returning its path if one is found. *)
let find_sail_project file =
  let rec search dir =
    let entries = try Sys.readdir dir with Sys_error _ -> [||] in
    Array.sort compare entries;
    match Array.find_opt (fun entry -> Filename.extension entry = ".sail_project") entries with
    | Some entry -> Some (Filename.concat dir entry)
    | None ->
        let parent = Filename.dirname dir in
        (* [Filename.dirname] is idempotent at the filesystem root, so stop there. *)
        if parent = dir then None else search parent
  in
  search (Filename.dirname file)

let state : Server_state.state option ref = ref None

type scan_id = Scan_id of Ast.id | Scan_app of Ast.id

module CursorScanner = Ast_util.Scanner (struct
  open Ast

  type t = Sail_file.position

  type category = scan_id

  let subloc p l =
    let open Sail_file.Position in
    match Reporting.simp_loc l with
    | None -> false
    | Some (p1, p2) ->
        let same_file = Sail_file.handle_compare p1.pos_fname p2.pos_fname = 0 in
        same_file
        &&
        let in_line_range = p1.pos_lnum <= p.pos_lnum && p.pos_lnum <= p2.pos_lnum in
        let in_char_range = p1.pos_cnum <= p.pos_cnum && p.pos_cnum <= p2.pos_cnum in
        in_line_range && in_char_range

  let categorize_exp = function
    | E_id id | E_ref id -> Some (Scan_id id)
    | E_app (id, _) -> Some (Scan_app id)
    | _ -> None

  let categorize_lexp = function LE_id id -> Some (Scan_id id) | _ -> None

  let categorize_pat = function P_id id -> Some (Scan_id id) | _ -> None
end)

(* Turn a [Reporting.error] into an LSP diagnostic. Every error carries a message
   and a location; when the location can't be resolved to an editor range (e.g. an
   unknown or generated location) we fall back to the start of the file so the
   diagnostic is still valid and shown. *)
let error_diagnostic (err : Reporting.error) =
  let loc, message =
    match err with
    | Reporting.Err_general (l, msg) | Reporting.Err_todo (l, msg) | Reporting.Err_syntax_loc (l, msg) -> (l, msg)
    | Reporting.Err_unreachable (l, _, _, msg) -> (l, msg)
    | Reporting.Err_type (l, hint, msg) -> (l, match hint with Some h -> msg ^ "\n" ^ h | None -> msg)
    | Reporting.Err_syntax (p, msg) | Reporting.Err_lex (p, msg) -> (Parse_ast.Range (p, p), msg)
    | Reporting.Err_warning (l, short, msg) -> (l, short ^ ":\n" ^ msg)
  in
  let range =
    match
      Option.bind (Reporting.simp_loc loc) (fun (p1, p2) ->
          match (Sail_file.editor_position p1, Sail_file.editor_position p2) with
          | Some s, Some e -> Some (s, e)
          | _ -> None
      )
    with
    | Some (s, e) ->
        let { Sail_file.line = sl; character = sc } = s in
        let { Sail_file.line = el; character = ec } = e in
        Lsp.Types.Range.create
          ~start:(Lsp.Types.Position.create ~line:sl ~character:sc)
          ~end_:(Lsp.Types.Position.create ~line:el ~character:ec)
    | None ->
        let zero = Lsp.Types.Position.create ~line:0 ~character:0 in
        Lsp.Types.Range.create ~start:zero ~end_:zero
  in
  Lsp.Types.Diagnostic.create ~range ~severity:Lsp.Types.DiagnosticSeverity.Error ~source:"sail"
    ~message:(`String message) ()

let diagnostics_for_handle file handle =
  let diags =
    match !state with
    | Some s -> (
        match Server_state.check_up_to s handle with
        | Ok s' ->
            state := Some s';
            []
        | Error err -> [error_diagnostic err]
      )
    | None -> []
  in
  let params =
    Lsp.Types.PublishDiagnosticsParams.create ~uri:(Lsp.Types.DocumentUri.of_path file) ~diagnostics:diags ()
  in
  Lsp.Server_notification.PublishDiagnostics params

let on_initialize ~(config : Server_config.t) _params =
  let server_info = Lsp.Types.InitializeResult.create_serverInfo ~name:"sail_lsp" () in
  let sync =
    Lsp.Types.TextDocumentSyncOptions.create ~openClose:true ~change:Lsp.Types.TextDocumentSyncKind.Incremental
      ~save:(`Bool true) ()
  in
  let semantic_tokens =
    if config.highlight then
      Some
        (`SemanticTokensOptions (Lsp.Types.SemanticTokensOptions.create ~legend:Highlight.legend ~full:(`Bool true) ()))
    else None
  in
  let capabilities =
    Lsp.Types.ServerCapabilities.create ~hoverProvider:(`Bool true) ~textDocumentSync:(`TextDocumentSyncOptions sync)
      ?semanticTokensProvider:semantic_tokens ~foldingRangeProvider:(`Bool config.folding)
      ~definitionProvider:(`Bool true) ()
  in
  Lsp.Types.InitializeResult.create ~capabilities ~serverInfo:server_info ()

let on_shutdown () = ()

let on_semantic_tokens_full (params : Lsp.Types.SemanticTokensParams.t) =
  let file = Lsp.Types.DocumentUri.to_path params.textDocument.uri in
  log "semanticTokens/full: %s" file;
  match Hashtbl.find_opt file_to_handle file with
  | None ->
      log "semanticTokens/full: no handle for %s" file;
      None
  | Some handle -> Some (Highlight.compute handle)

let on_folding_range (params : Lsp.Types.FoldingRangeParams.t) =
  let file = Lsp.Types.DocumentUri.to_path params.textDocument.uri in
  log "foldingRange: %s" file;
  match Hashtbl.find_opt file_to_handle file with
  | None ->
      log "foldingRange: no handle for %s" file;
      None
  | Some handle -> Some (Folding.compute handle)

let on_hover ({ position = { line; character }; textDocument = { uri } } : Lsp.Types.HoverParams.t) =
  let open Lsp.Types in
  let open Util.Option_monad in
  let file = DocumentUri.to_path uri in
  let* handle = Hashtbl.find_opt file_to_handle file in
  let* p = Sail_file.lexing_position handle { line; character } in
  let* ast = Option.map Server_state.force_last_ast !state in
  let* l, tannot, _ = CursorScanner.find_annot_ast p ast in
  let* _, typ = Type_check.destruct_tannot tannot in
  log "%s" (Reporting.loc_to_string l);
  Some (Hover.create ~contents:(`MarkedString { value = Ast_util.string_of_typ typ; language = None }) ())

(* Turn a Sail source location into an LSP location (file plus range), or [None]
   when it can't be resolved to an editor range (e.g. a generated location). *)
let lsp_location_of_loc loc =
  let open Util.Option_monad in
  let* p1, p2 = Reporting.simp_loc loc in
  let* s = Sail_file.editor_position p1 in
  let* e = Sail_file.editor_position p2 in
  let file = Sail_file.Path.to_string (Sail_file.to_path p1.Sail_file.Position.pos_fname) in
  let range =
    Lsp.Types.Range.create
      ~start:(Lsp.Types.Position.create ~line:s.Sail_file.line ~character:s.Sail_file.character)
      ~end_:(Lsp.Types.Position.create ~line:e.Sail_file.line ~character:e.Sail_file.character)
  in
  Some (Lsp.Types.Location.create ~uri:(Lsp.Types.DocumentUri.of_path file) ~range)

(* Go-to-definition: from a value or function name under the cursor, jump to the point where it is defined. *)
let on_definition ({ position = { line; character }; textDocument = { uri } } : Lsp.Types.DefinitionParams.t) =
  let open Util.Option_monad in
  let file = Lsp.Types.DocumentUri.to_path uri in
  log "declaration: %s" file;
  let* handle = Hashtbl.find_opt file_to_handle file in
  let* p = Sail_file.lexing_position handle { line; character } in
  let* ast = Option.map Server_state.force_last_ast !state in
  let* _, tannot, id_cat = CursorScanner.find_annot_ast p ast in
  match id_cat with
  | Some (Scan_app id) | Some (Scan_id id) ->
      let* _, l = Type_check.Env.get_global_binding_loc (Type_check.env_of_tannot tannot) id in
      let* loc = lsp_location_of_loc l in
      Some (`Location [loc])
  | _ -> None

let refresh_project ~(config : Server_config.t) file =
  match find_sail_project file with
  | Some project_file ->
      state := Some (Server_state.load_project ~default_sail_dir:config.default_sail_dir [project_file])
  | None -> state := None

let on_notification ~config notif =
  let open Lsp.Types in
  match notif with
  | Lsp.Client_notification.Exit -> exit 0
  | Lsp.Client_notification.TextDocumentDidOpen params ->
      let file = DocumentUri.to_path params.textDocument.uri in
      log "didOpen: %s" file;
      let text = params.textDocument.text in
      let handle = Sail_file.editor_take_file ~contents:text file in
      register_handle file handle;
      ( match !state with
      | None -> refresh_project ~config file
      | Some s -> (
          match Server_state.invalidate s handle with
          | Some s' -> state := Some s'
          | None -> refresh_project ~config file
        )
      );
      [diagnostics_for_handle file handle]
  | Lsp.Client_notification.TextDocumentDidChange params -> (
      let file = DocumentUri.to_path params.textDocument.uri in
      log "didChange: %s" file;
      match Hashtbl.find_opt file_to_handle file with
      | None ->
          log "didChange: no handle for %s" file;
          []
      | Some handle ->
          List.iter
            (fun (change : TextDocumentContentChangeEvent.t) ->
              match change with
              | { range = Some range; text; _ } ->
                  (* LSP positions are UTF-16 code-unit offsets; store them as-is. The
                     conversion to byte offsets happens when the edits are applied. *)
                  let startp = { Sail_file.line = range.start.line; character = range.start.character } in
                  let endp = { Sail_file.line = range.end_.line; character = range.end_.character } in
                  Sail_file.edit_file handle { Sail_file.range = (startp, endp); text }
              | { range = None; text; _ } -> ignore (Sail_file.editor_take_file ~contents:text file)
            )
            params.contentChanges;
          Sail_file.apply_edits handle;
          ( match !state with
          | Some s -> (
              match Server_state.invalidate s handle with Some s' -> state := Some s' | None -> ()
            )
          | None -> ()
          );
          [diagnostics_for_handle file handle]
    )
  | Lsp.Client_notification.DidSaveTextDocument params -> (
      let file = DocumentUri.to_path params.textDocument.uri in
      log "didSave: %s" file;
      match Hashtbl.find_opt file_to_handle file with
      | None -> []
      | Some handle ->
          Sail_file.apply_edits handle;
          ( match !state with
          | Some s -> (
              match Server_state.invalidate s handle with Some s' -> state := Some s' | None -> ()
            )
          | None -> ()
          );
          [diagnostics_for_handle file handle]
    )
  | Lsp.Client_notification.TextDocumentDidClose params ->
      let file = DocumentUri.to_path params.textDocument.uri in
      log "didClose: %s" file;
      ( match Hashtbl.find_opt file_to_handle file with
      | None -> ()
      | Some handle ->
          Sail_file.editor_drop_file handle;
          unregister_handle handle
      );
      []
  | _ -> []
