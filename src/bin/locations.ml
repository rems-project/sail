(*
Directory containing the lib and src directories. The most important is the
lib directory which contains the standard library .sail files, e.g. `option.sail`
and the C runtime files (`sail.c`, `rts.c`, etc).

When installed by OPAM, Manifest.dir will be Some absolute_path so we just
return that. When installed by dune we look relative to the location of
the Sail binary. This allows it to be a portable installation which we make
use of to provide a binary tarball.
*)

let sail_dir =
  match Manifest.dir with
  | Some opam_dir -> opam_dir
  | None ->
      let open Filename in
      concat (concat (concat (dirname Sys.executable_name) parent_dir_name) "share") "sail"
