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

open Printf

let git_command args =
  try
    let git_out, git_in, git_err = Unix.open_process_full ("git " ^ args) (Unix.environment ()) in
    let res = input_line git_out in
    match Unix.close_process_full (git_out, git_in, git_err) with Unix.WEXITED 0 -> Some res | _ -> None
  with _ -> None

let gen_manifest () =
  (* See manifest.ml.in for more information about `dir`. *)
  ksprintf print_endline "let dir = None";
  ksprintf print_endline "let commit = \"%s\"" (Option.value (git_command "rev-parse HEAD") ~default:"unknown commit");
  ksprintf print_endline "let branch = \"%s\""
    (Option.value (git_command "rev-parse --abbrev-ref HEAD") ~default:"unknown branch")

(* Copy a single file. Surprisingly there's no built-in function for this. *)
let copy_file (input_path : string) (output_path : string) =
  let buffer_size = 8192 in
  let buffer = Bytes.create buffer_size in
  let ic = open_in_bin input_path in
  let oc = open_out_bin output_path in
  try
    let rec copy_loop () =
      let bytes_read = input ic buffer 0 buffer_size in
      if bytes_read > 0 then begin
        output oc buffer 0 bytes_read;
        copy_loop ()
      end
    in
    copy_loop ();
    close_in ic;
    close_out oc
  with e ->
    close_in_noerr ic;
    close_out_noerr oc;
    raise e

(* Recursively remove a file or directory tree. *)
let rec remove_file_or_dir path =
  if Sys.file_exists path then
    if Sys.is_directory path then begin
      (* Remove all contents of the directory *)
      let entries = Sys.readdir path in
      Array.iter
        (fun entry ->
          let full_path = Filename.concat path entry in
          remove_file_or_dir full_path
        )
        entries;
      (* Remove the now-empty directory *)
      Unix.rmdir path
    end
    else
      (* Remove regular file *)
      Sys.remove path

let parse_tarball_args (args : string list) =
  let usage_msg = "sail_maker tarball --prefix=PREFIX [--z3=Z3_EXE_PATH] [--gmp=GMP_DLL_PATH]" in
  let prefix = ref "" in
  let z3_path = ref "" in
  let gmp_path = ref "" in

  let speclist =
    [
      ("--prefix", Arg.Set_string prefix, "Path to install prefix");
      ("--z3", Arg.Set_string z3_path, "Set path to z3 executable");
      ("--gmp", Arg.Set_string gmp_path, "Set path to GMP shared library");
    ]
  in

  (* Positional arguments are unused and will cause an error. *)
  let anon_fun _ = () in

  let args = Array.of_list ("sail_maker" :: args) in

  let () = Arg.parse_argv args speclist anon_fun usage_msg in

  (!prefix, !z3_path, !gmp_path)

let tarball (prefix : string) (z3 : string) (gmp : string) =
  let bindir = Filename.concat prefix "bin" in
  (* This contains a load of OCaml source files we don't need in the binary distribution. *)
  remove_file_or_dir (Filename.concat prefix "lib");
  (* The sail_maker binary gets installed and I'm not sure how to avoid that with Dune
  so just delete it now. *)
  remove_file_or_dir (Filename.concat bindir (if Sys.win32 then "sail_maker.exe" else "sail_maker"));
  (* Copy in some extra license files. Maybe Dune could do this. *)
  copy_file "LICENSE" (Filename.concat prefix "LICENSE");
  copy_file "THIRD_PARTY_FILES.md" (Filename.concat prefix "THIRD_PARTY_FILES.md");
  copy_file "etc/tarball_extra/INSTALL" (Filename.concat prefix "INSTALL");
  copy_file "etc/tarball_extra/Z3_LICENSE" (Filename.concat prefix "Z3_LICENSE");
  (* Copy in precompiled coverage library. *)
  let coverage_libname = if Sys.win32 then "sail_coverage.lib" else "libsail_coverage.a" in
  copy_file
    (Filename.concat "lib/coverage/target/release" coverage_libname)
    (Filename.concat (Filename.concat prefix "share/sail/lib/coverage") coverage_libname);
  (* For convenience, copy in a z3 executable and GMP shared library (Windows only). *)
  if z3 <> "" then copy_file z3 (Filename.concat bindir (Filename.basename z3));
  if gmp <> "" then copy_file gmp (Filename.concat bindir (Filename.basename gmp));
  ()

let usage =
  "sail_maker gen_manifest\n\n\
  \  Write manifest.ml to stdout containing Git commit and branch information.\n\n\n\n\
   sail_maker tarball --prefix=PREFIX [--z3=Z3_EXE_PATH] [--gmp=GMP_DLL_PATH]\n\n\
  \  Used for fixing up the `dune install` output in preparation for making release tarballs.\n\n"

let main () =
  (* OCaml's pattern matching support is not very good for arrays so convert
  to a list. OCaml loves lists more than ones and zeros. *)
  match Array.to_list Sys.argv with
  | [_; "gen_manifest"] -> gen_manifest ()
  | _ :: "tarball" :: args ->
      let prefix, z3_path, gmp_path = parse_tarball_args args in
      tarball prefix z3_path gmp_path
  | _ ->
      prerr_endline usage;
      exit 1

let () = main ()
