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

module Path = struct
  type t = Actual of string | Virtual of string

  let canonicalize = function Virtual p -> Virtual p | Actual p -> Actual (Unix.realpath p)

  let actual p = Actual p

  let is_virtual = function Virtual _ -> true | Actual _ -> false

  let map_actual f = function Virtual p -> Virtual p | Actual p -> Actual (f p)

  let to_string = function Virtual p -> p | Actual p -> p
end

type path = Path.t

type handle = int

let handle_compare h1 h2 = Int.compare h1 h2

let handle_equal h1 h2 = Int.equal h1 h2

module HandleSet = Set.Make (struct
  type t = handle
  let compare = handle_compare
end)

module HandleMap = Map.Make (struct
  type t = handle
  let compare = handle_compare
end)

let handles = ref 3

let dummy = 0

let interactive_repl = 1

let argv = 2

let new_handle () =
  let handle = !handles in
  incr handles;
  handle

module Position = struct
  type position = { pos_fname : handle; pos_lnum : int; pos_bol : int; pos_cnum : int }

  let from_lexing handle p =
    { pos_fname = handle; pos_lnum = p.Lexing.pos_lnum; pos_bol = p.Lexing.pos_bol; pos_cnum = p.Lexing.pos_cnum }

  let to_lexing p = { Lexing.pos_fname = ""; pos_lnum = p.pos_lnum; pos_bol = p.pos_bol; pos_cnum = p.pos_cnum }

  let dummy_pos = { pos_fname = dummy; pos_lnum = -1; pos_bol = -1; pos_cnum = -1 }
end

type position = Position.position

type owner = Compiler | Editor

type editor_position = { line : int; character : int }

type editor_range = editor_position * editor_position

type text_edit = { range : editor_range; text : string }

type text_edit_size = Single_line of int | Multiple_lines of { pre : int; newlines : int; post : int }

let count_newlines s =
  let n = ref 0 in
  String.iter (fun c -> if c = '\n' then incr n) s;
  !n

(* LSP positions count characters in UTF-16 code units, whereas Sail's lexer
   works in bytes. A UTF-8 code point in the basic multilingual plane is a
   single UTF-16 code unit; one outside it (a four-byte UTF-8 sequence) is
   encoded as a surrogate pair and so counts as two. These helpers convert
   between byte and UTF-16 offsets within a single (UTF-8 encoded) line. *)

(* The number of UTF-8 bytes and UTF-16 code units of the character whose
   leading byte is [c]. *)
let utf8_char_size c = if c < 0x80 then (1, 1) else if c < 0xe0 then (2, 1) else if c < 0xf0 then (3, 1) else (4, 2)

(* Byte offset into [line] of its [utf16]th UTF-16 code unit. An offset past the
   end of the line clamps to its byte length. *)
let utf16_offset_to_byte line utf16 =
  let len = String.length line in
  let byte = ref 0 in
  let units = ref 0 in
  while !units < utf16 && !byte < len do
    let nbytes, nunits = utf8_char_size (Char.code line.[!byte]) in
    byte := !byte + nbytes;
    units := !units + nunits
  done;
  min !byte len

(* UTF-16 code-unit offset into [line] corresponding to the byte offset [byte].
   An offset past the end of the line clamps to its UTF-16 length. *)
let byte_offset_to_utf16 line byte =
  let target = min byte (String.length line) in
  let b = ref 0 in
  let units = ref 0 in
  while !b < target do
    let nbytes, nunits = utf8_char_size (Char.code line.[!b]) in
    b := !b + nbytes;
    units := !units + nunits
  done;
  !units

(* The length of [s] in UTF-16 code units. *)
let utf16_length s = byte_offset_to_utf16 s (String.length s)

(* Text edits are stored in editor (UTF-16 code-unit) coordinates, so measure
   the inserted text in the same units to keep the position arithmetic in
   [update_position]/[revert_position] consistent. *)
let measure_edit edit =
  let newlines = count_newlines edit.text in
  if newlines = 0 then Single_line (utf16_length edit.text)
  else (
    let pre = byte_offset_to_utf16 edit.text (String.index_from edit.text 0 '\n') in
    let post = byte_offset_to_utf16 edit.text (String.rindex_from edit.text (String.length edit.text - 1) '\n') in
    Multiple_lines { pre; newlines; post }
  )

type info = {
  (* This is for LSP integration, either we (the compiler) own
     the file, otherwise the editor owns the file. *)
  owner : owner;
  (* The path as provided by the user *)
  given_path : path;
  canonical_path : path;
  mutable contents : string Array.t;
  mutable next_edit : int;
  mutable edits : (text_edit * text_edit_size) option Array.t;
}

let new_info ~owner ~given_path ?canonical_path ~contents () =
  {
    owner;
    given_path;
    canonical_path = Option.value ~default:(Path.canonicalize given_path) canonical_path;
    contents;
    next_edit = 0;
    edits = Array.make 64 None;
  }

let sail_argv () =
  let actual_argv = Sys.argv in
  let from_env =
    match Sys.getenv_opt "SAIL_ENCODED_FLAGS" with
    | Some flags ->
        (* Split on ASCII unit separator, like CARGO_ENCODED_RUSTFLAGS in Rust *)
        String.split_on_char '\x1f' flags
    | None -> (
        match Sys.getenv_opt "SAIL_FLAGS" with
        | Some flags -> String.split_on_char ' ' flags |> List.filter (fun flag -> flag <> "")
        | None -> []
      )
  in
  Array.append actual_argv (Array.of_list from_env)

let files : (int, info) Hashtbl.t =
  let tbl = Hashtbl.create 64 in
  let repl_contents = Array.make 1 "0000001,0000016" in
  let argv_contents = sail_argv () in
  Hashtbl.add tbl dummy (new_info ~owner:Compiler ~given_path:(Path.Virtual "EMPTY") ~contents:(Array.make 0 "") ());
  Hashtbl.add tbl interactive_repl
    (new_info ~owner:Compiler ~given_path:(Path.Virtual "REPL") ~contents:repl_contents ());
  Hashtbl.add tbl argv (new_info ~owner:Compiler ~given_path:(Path.Virtual "ARGV") ~contents:argv_contents ());
  tbl

let opened : (path, int) Hashtbl.t =
  let tbl = Hashtbl.create 64 in
  Hashtbl.add tbl (Path.Virtual "EMPTY") dummy;
  Hashtbl.add tbl (Path.Virtual "REPL") interactive_repl;
  Hashtbl.add tbl (Path.Virtual "ARGV") argv;
  tbl

let to_path handle =
  let path = (Hashtbl.find files handle).given_path in
  path

let add_virtual_file ~contents name =
  let handle = new_handle () in
  let path = Path.Virtual name in
  let contents = Array.of_list (String.split_on_char '\n' contents) in
  Hashtbl.add files handle (new_info ~owner:Compiler ~given_path:path ~contents ());
  Hashtbl.add opened path handle;
  (path, handle)

let get_virtual_file name = Hashtbl.find_opt opened (Path.Virtual name)

let bol_of_lnum line file =
  let info = Hashtbl.find files file in
  let bol = ref 0 in
  if line - 2 >= Array.length info.contents then None
  else (
    for i = 0 to line - 2 do
      bol := !bol + String.length info.contents.(i) + 1
    done;
    Some !bol
  )

let add_line_to_repl_contents n line info =
  let len = Array.length info.contents in
  if n >= len then (
    let new_contents = Array.make (len * 2) "" in
    Array.blit info.contents 0 new_contents 0 len;
    info.contents <- new_contents
  );
  info.contents.(n) <- line

let repl_prompt_line () =
  let info = Hashtbl.find files interactive_repl in
  Scanf.sscanf info.contents.(0) "%d,%d" (fun n _ -> n + 1)

let add_to_repl_contents ~command =
  let info = Hashtbl.find files interactive_repl in
  let n, bol = Scanf.sscanf info.contents.(0) "%d,%d" (fun n bol -> (n, bol)) in
  let n', bol' =
    List.fold_left
      (fun (n, bol) line ->
        add_line_to_repl_contents n line info;
        (n + 1, bol + String.length line)
      )
      (n, bol) (String.split_on_char '\n' command)
  in
  info.contents.(0) <- Printf.sprintf "%07d,%07d" n' bol';
  (n + 1, bol)

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
  let open Position in
  let handle = p.pos_fname in
  match Hashtbl.find_opt files handle with
  | None -> None
  | Some info ->
      (* Lexing/AST lines are 1-based; editor lines are 0-based. *)
      let line = p.pos_lnum - 1 in
      let byte_character = p.pos_cnum - p.pos_bol in
      (* The Lexing position is a byte offset into the base contents; editor
     positions are UTF-16 code units, so convert against the base line
     before replaying the pending edits (which are in editor coordinates). *)
      let character =
        if line >= 0 && line < Array.length info.contents then byte_offset_to_utf16 info.contents.(line) byte_character
        else byte_character
      in
      fold_edits_first_to_last
        (fun edit size pos_opt -> match pos_opt with None -> None | Some p -> update_position edit size p)
        handle
        (Some { line; character })

let lexing_position handle p =
  let open Position in
  match
    fold_edits_last_to_first
      (fun edit size pos_opt -> Option.bind pos_opt (fun p -> revert_position edit size p))
      handle (Some p)
  with
  | None -> None
  | Some p ->
      let info = Hashtbl.find files handle in
      let bol = ref 0 in
      for i = 0 to p.line - 1 do
        bol := !bol + String.length info.contents.(i) + 1
      done;
      (* [p.character] is a UTF-16 code-unit offset into the base contents;
         convert it to a byte offset for the Sail lexing position. *)
      let character =
        if p.line >= 0 && p.line < Array.length info.contents then
          utf16_offset_to_byte info.contents.(p.line) p.character
        else p.character
      in
      (* Editor lines are 0-based; Lexing/AST lines are 1-based. *)
      Some { pos_fname = handle; pos_lnum = p.line + 1; pos_bol = !bol; pos_cnum = !bol + character }

(* Apply a single text edit to a line array, returning the updated array. The
   edit's character offsets are UTF-16 code units, so convert them to byte
   offsets into the (UTF-8) lines they index before slicing. The half-open
   range [s, e) is replaced by [edit.text], which may itself span several
   lines. Line numbers are clamped to be in-bounds so that malformed client
   input cannot raise; [utf16_offset_to_byte] already clamps the columns. *)
let apply_edit contents edit =
  let contents = if Array.length contents = 0 then [| "" |] else contents in
  let n = Array.length contents in
  let s, e = edit.range in
  let clamp lo hi x = if x < lo then lo else if x > hi then hi else x in
  let sl = clamp 0 (n - 1) s.line in
  let el = clamp 0 (n - 1) e.line in
  let sc = utf16_offset_to_byte contents.(sl) s.character in
  let ec = utf16_offset_to_byte contents.(el) e.character in
  let before = String.sub contents.(sl) 0 sc in
  let after = String.sub contents.(el) ec (String.length contents.(el) - ec) in
  let replacement = Array.of_list (String.split_on_char '\n' (before ^ edit.text ^ after)) in
  Array.concat [Array.sub contents 0 sl; replacement; Array.sub contents (el + 1) (n - (el + 1))]

(* The current editor view of a file: its base contents with every queued edit
   applied, in order. Does not mutate the stored contents or the edit queue. *)
let current_contents info =
  let contents = ref info.contents in
  for i = 0 to info.next_edit - 1 do
    let edit, _ = Option.get info.edits.(i) in
    contents := apply_edit !contents edit
  done;
  !contents

(* Bake the queued edits into the file's contents, bringing them in sync with
   the editor, and clear the queue. After this the base contents equals the
   editor view, so no pending position translation remains. *)
let apply_edits handle =
  let info = Hashtbl.find files handle in
  info.contents <- current_contents info;
  Array.fill info.edits 0 info.next_edit None;
  info.next_edit <- 0

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
  let path = Path.canonicalize given_path in
  match Hashtbl.find_opt opened path with
  | Some handle -> handle
  | None -> (
      match path with
      | Actual path ->
          if not (Sys.file_exists path) then raise (Sys_error (path ^ ": No such file or directory"));
          let contents = file_to_line_array path in
          let handle = new_handle () in
          let info = new_info ~owner:Compiler ~given_path ~canonical_path:(Path.Actual path) ~contents () in
          Hashtbl.add files handle info;
          Hashtbl.add opened (Path.Actual path) handle;
          handle
      | Virtual path -> assert false
    )

let write_file ~contents handle =
  let info = Hashtbl.find files handle in
  let contents = Array.of_list (String.split_on_char '\n' contents) in
  Array.fill info.edits 0 (Array.length info.edits) None;
  info.contents <- contents;
  info.next_edit <- 0

let editor_take_file ~contents path =
  let path = Path.Actual path in
  let contents = Array.of_list (String.split_on_char '\n' contents) in
  match Hashtbl.find_opt opened path with
  | Some handle ->
      let info = Hashtbl.find files handle in
      Hashtbl.replace files handle { info with owner = Editor; contents };
      handle
  | None -> (
      let canonical_path = Path.canonicalize path in
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
          let info = new_info ~owner:Editor ~given_path:path ~canonical_path ~contents () in
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
