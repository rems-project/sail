open Libsail

let counter = ref 0

(* A fresh file handle initialised with [contents]. Each handle gets a unique
   virtual name so tests do not interfere with one another. *)
let handle_of contents =
  incr counter;
  let _, handle = Sail_file.add_virtual_file ~contents (Printf.sprintf "sail_file_test_%d.sail" !counter) in
  handle

let pos line character = { Sail_file.line; character }

let edit start_ end_ text = { Sail_file.range = (start_, end_); text }
