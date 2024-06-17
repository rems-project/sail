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

type handle = int

let handles = ref 0

let new_handle () =
  let handle = !handles in
  incr handles;
  handle

let canonicalizer = ref (fun path -> path)

let canonicalize path = !canonicalizer path

let set_canonicalize_function f = canonicalizer := f

type owner = Compiler | Editor

type editor_position = { line : int; character : int }

type editor_range = editor_position * editor_position

type text_edit = { range : editor_range; text : string }

type text_edit_size = Single_line of int | Multiple_lines of { pre : int; newlines : int; post : int }

let count_newlines s =
  let n = ref 0 in
  String.iter (fun c -> if c = '\n' then incr n) s;
  !n

let measure_edit edit =
  let newlines = count_newlines edit.text in
  if newlines = 0 then Single_line (String.length edit.text)
  else (
    let pre = String.index_from edit.text 0 '\n' in
    let post = String.rindex_from edit.text (String.length edit.text - 1) '\n' in
    Multiple_lines { pre; newlines; post }
  )

type info = {
  (* This is for LSP integration, either we (the compiler) own
     the file, otherwise the editor owns the file. *)
  owner : owner;
  (* The path as provided by the user *)
  given_path : string;
  canonical_path : string;
  mutable contents : string Array.t;
  mutable next_edit : int;
  mutable edits : (text_edit * text_edit_size) option Array.t;
}

let new_info ~owner ~given_path ~canonical_path ~contents =
  { owner; given_path; canonical_path; contents; next_edit = 0; edits = Array.make 64 None }

let files : (int, info) Hashtbl.t = Hashtbl.create 64

let opened : (string, int) Hashtbl.t = Hashtbl.create 64

let edit_file handle edit =
  let info = Hashtbl.find files handle in
  let max_edits = Array.length info.edits in
  let n = info.next_edit in
  if n >= max_edits then (
    let new_edits = Array.make (n * 2) None in
    Array.blit info.edits 0 new_edits 0 max_edits;
    info.edits <- new_edits
  );
  let size = measure_edit edit in
  info.edits.(n) <- Some (edit, size);
  info.next_edit <- n + 1

let apply_edits handle =
  let info = Hashtbl.find files handle in
  Array.fill info.edits 0 (Array.length info.edits) None;
  info.next_edit <- 0

let fold_edits_first_to_last f handle init =
  let info = Hashtbl.find files handle in
  let acc = ref init in
  for i = 0 to info.next_edit - 1 do
    let edit, size = Option.get info.edits.(i) in
    acc := f edit size !acc
  done;
  !acc

let fold_edits_last_to_first f handle init =
  let info = Hashtbl.find files handle in
  let acc = ref init in
  for i = info.next_edit - 1 downto 0 do
    let edit, size = Option.get info.edits.(i) in
    acc := f edit size !acc
  done;
  !acc

let position_before p1 p2 = p1.line < p2.line || (p1.line = p2.line && p1.character < p2.character)

let update_position edit size p =
  let s, e = edit.range in
  if position_before p s then Some p
  else if position_before e p || e = p then
    Some
      ( match size with
      | Multiple_lines { pre = _; newlines; post } ->
          let line_change = newlines - (e.line - s.line) in
          if p.line = e.line then { line = p.line + line_change; character = p.character - e.character + post }
          else { line = p.line + line_change; character = p.character }
      | Single_line n ->
          if p.line = e.line then { line = p.line; character = p.character - (e.character - s.character) + n } else p
      )
  else None

let revert_position edit size p =
  let s, e = edit.range in
  if position_before p s then Some p
  else if position_before e p || e = p then
    Some
      ( match size with
      | Multiple_lines { pre = _; newlines; post } ->
          let line_change = e.line - s.line - newlines in
          if p.line = e.line then { line = p.line + line_change; character = p.character + e.character - post }
          else { line = p.line + line_change; character = p.character }
      | Single_line n ->
          if p.line = e.line then { line = p.line; character = p.character - n + (e.character - s.character) } else p
      )
  else None

let editor_position p =
  let open Lexing in
  let path = canonicalize p.pos_fname in
  match Hashtbl.find_opt opened path with
  | Some handle ->
      fold_edits_first_to_last
        (fun edit size pos_opt -> match pos_opt with None -> None | Some p -> update_position edit size p)
        handle
        (Some { line = p.pos_lnum; character = p.pos_cnum - p.pos_bol })
  | None -> None

let lexing_position handle p =
  let open Lexing in
  let open Util.Option_monad in
  let* p =
    fold_edits_last_to_first
      (fun edit size pos_opt ->
        let* p = pos_opt in
        revert_position edit size p
      )
      handle (Some p)
  in
  let info = Hashtbl.find files handle in
  let bol = ref 0 in
  for i = 0 to p.line - 1 do
    bol := !bol + String.length info.contents.(i) + 1
  done;
  Some { pos_fname = info.given_path; pos_lnum = p.line; pos_bol = !bol; pos_cnum = !bol + p.character }

let file_to_line_array filename =
  let chan = open_in filename in
  let linebuf = Buffer.create 256 in
  let lines = Queue.create () in
  (* Note that this has to be a little intricate, because it handles
     trailing newlines before End_of_file. *)
  try
    let rec loop () =
      let c = input_char chan in
      if c = '\n' then (
        Queue.add (Buffer.contents linebuf) lines;
        Buffer.clear linebuf
      )
      else Buffer.add_char linebuf c;
      loop ()
    in
    loop ()
  with End_of_file ->
    if Buffer.length linebuf = 0 then (
      if
        (* If both the linebuf and lines are empty we were given the
           empty file. If linebuf is empty, but lines is not then we
           just processed a newline immediately prior to End_of_file. *)
        Queue.length lines <> 0
      then Queue.add "" lines
    )
    else Queue.add (Buffer.contents linebuf) lines;
    close_in chan;
    Array.init (Queue.length lines) (fun _ -> Queue.take lines)

let open_file given_path =
  let path = canonicalize given_path in
  match Hashtbl.find_opt opened path with
  | Some handle -> handle
  | None ->
      if not (Sys.file_exists path) then raise (Sys_error (path ^ ": No such file or directory"));
      let contents = file_to_line_array path in
      let handle = new_handle () in
      let info = new_info ~owner:Compiler ~given_path ~canonical_path:path ~contents in
      Hashtbl.add files handle info;
      Hashtbl.add opened path handle;
      handle

let write_file ~contents handle =
  let info = Hashtbl.find files handle in
  let contents = Array.of_list (String.split_on_char '\n' contents) in
  Array.fill info.edits 0 (Array.length info.edits) None;
  info.contents <- contents;
  info.next_edit <- 0

let editor_take_file ~contents path =
  let contents = Array.of_list (String.split_on_char '\n' contents) in
  match Hashtbl.find_opt opened path with
  | Some handle ->
      let info = Hashtbl.find files handle in
      Hashtbl.replace files handle { info with owner = Editor; contents };
      handle
  | None -> (
      let canonical_path = canonicalize path in
      let existing = ref None in
      Hashtbl.iter
        (fun handle info -> if info.canonical_path = canonical_path then existing := Some (handle, info))
        files;
      match !existing with
      | Some (handle, info) ->
          Hashtbl.replace files handle { info with owner = Editor; contents };
          Hashtbl.add opened path handle;
          handle
      | None ->
          let handle = new_handle () in
          let info = new_info ~owner:Editor ~given_path:path ~canonical_path ~contents in
          Hashtbl.add files handle info;
          Hashtbl.add opened path handle;
          handle
    )

let editor_drop_file handle =
  let info = Hashtbl.find files handle in
  Hashtbl.replace files handle { info with owner = Compiler }

let contents handle =
  let lines = (Hashtbl.find files handle).contents in
  let len = Array.fold_left (fun len line -> len + String.length line + 1) 0 lines in
  let buf = Buffer.create len in
  Array.iteri
    (fun n line ->
      Buffer.add_string buf line;
      if n <> Array.length lines - 1 then Buffer.add_char buf '\n'
    )
    lines;
  Buffer.contents buf

module In_channel = struct
  type t = { mutable pos : int; buf : string }

  let from_file handle = { pos = -1; buf = contents handle }

  let from_string s = { pos = -1; buf = s }

  let input_line_opt in_chan =
    if in_chan.pos >= String.length in_chan.buf then None
    else (
      match String.index_from_opt in_chan.buf (in_chan.pos + 1) '\n' with
      | None ->
          let line = String.sub in_chan.buf (in_chan.pos + 1) (String.length in_chan.buf - (in_chan.pos + 1)) in
          in_chan.pos <- String.length in_chan.buf;
          Some line
      | Some next_newline ->
          let line = String.sub in_chan.buf (in_chan.pos + 1) (next_newline - (in_chan.pos + 1)) in
          in_chan.pos <- next_newline;
          Some line
    )

  let input_line in_chan = match input_line_opt in_chan with Some line -> line | None -> raise End_of_file
end
