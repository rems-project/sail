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

type info = {
  (* This is for LSP integration, either we (the compiler) own
     the file, otherwise the editor owns the file. *)
  owner : owner;
  canonical_path : string;
  mutable contents : string Array.t;
}

let files : (int, info) Hashtbl.t = Hashtbl.create 100

let opened : (string, int) Hashtbl.t = Hashtbl.create 100

let file_to_line_array filename =
  let chan = open_in filename in
  let lines = Queue.create () in
  try
    let rec loop () =
      let line = input_line chan in
      Queue.add line lines;
      loop ()
    in
    loop ()
  with End_of_file ->
    close_in chan;
    Array.init (Queue.length lines) (fun _ -> Queue.take lines)

let open_file path =
  match Hashtbl.find_opt opened path with
  | Some handle -> handle
  | None -> (
      if not (Sys.file_exists path) then raise (Sys_error (path ^ ": No such file or directory"));
      let canonical_path = canonicalize path in
      let existing_handle = ref None in
      Hashtbl.iter
        (fun handle info -> if info.canonical_path = canonical_path then existing_handle := Some handle)
        files;
      match !existing_handle with
      | Some handle -> handle
      | None ->
          let contents = file_to_line_array path in
          let handle = new_handle () in
          let info = { owner = Compiler; canonical_path; contents } in
          Hashtbl.add files handle info;
          Hashtbl.add opened path handle;
          handle
    )

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
          let info = { owner = Editor; canonical_path; contents } in
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
      Buffer.add_char buf '\n'
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
