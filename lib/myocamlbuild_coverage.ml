(* ocamlbuild file for use with bisect_ppx *)
open Ocamlbuild_plugin
let () = dispatch Bisect_ppx_plugin.dispatch

