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
      if bytes_read > 0 then (
        output oc buffer 0 bytes_read;
        copy_loop ()
      )
    in
    copy_loop ();
    close_in ic;
    close_out oc;

    (* Copy permission bits; needed for copying in Z3 on Unix platforms. *)
    let in_stat = Unix.stat input_path in
    Unix.chmod output_path in_stat.Unix.st_perm
  with e ->
    close_in_noerr ic;
    close_out_noerr oc;
    raise e

(* Recursively remove a file or directory tree. *)
let rec remove_file_or_dir path =
  if Sys.file_exists path then
    if Sys.is_directory path then (
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
    )
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

let parse_embed_args (args : string list) =
  let usage_msg = "sail_maker embed --file=PATH" in
  let file = ref None in
  let tag = ref "" in
  let virt = ref None in

  let speclist =
    [
      ("--file", Arg.String (fun f -> file := Some f), "<path> Path to file to embed");
      ("--tag", Arg.Set_string tag, "<tag> Tag for generated file");
      ("--virtual-file", Arg.String (fun v -> virt := Some v), "<name> Name of virtual Sail file");
    ]
  in

  let anon_fun _ = () in
  let args = Array.of_list ("sail_maker" :: args) in

  Arg.parse_argv args speclist anon_fun usage_msg;

  if Option.is_none !file then raise (Arg.Bad ("--file argument is required\n\n" ^ usage_msg));

  (!tag, Option.get !file, !virt)

let embed tag file virt_opt =
  let in_chan = open_in_bin file in
  let n = in_channel_length in_chan in
  let contents = really_input_string in_chan n in
  close_in in_chan;
  printf "let contents = {%s|%s|%s}\n" tag contents tag;
  match virt_opt with
  | None -> ()
  | Some virt -> printf "\nlet path, handle = Sail_file.add_virtual_file ~contents \"%s\"\n" virt

let parse_gen_sail_lib_mli_args (args : string list) =
  let usage_msg = "sail_maker gen_sail_lib_mli --externs=PATH --header=PATH --overrides=PATH" in
  let externs = ref "" in
  let header = ref "" in
  let overrides = ref "" in

  let speclist =
    [
      ("--externs", Arg.Set_string externs, "<path> JSON file produced by sail --tool extern_json");
      ("--header", Arg.Set_string header, "<path> Hand-written header for the generated interface");
      ("--overrides", Arg.Set_string overrides, "<path> JSON file with types for, and exclusions of, externs");
    ]
  in

  let anon_fun _ = () in
  let args = Array.of_list ("sail_maker" :: args) in

  Arg.parse_argv args speclist anon_fun usage_msg;

  List.iter
    (fun (name, value) -> if value = "" then raise (Arg.Bad (sprintf "--%s argument is required\n\n%s" name usage_msg)))
    [("externs", !externs); ("header", !header); ("overrides", !overrides)];

  (!externs, !header, !overrides)

(* Only bindings that are plain OCaml identifiers are implemented by
   Sail_lib. Qualified names (e.g. Platform.read_mem) and inline
   expressions are implemented elsewhere. *)
let is_sail_lib_binding name =
  String.length name > 0
  && (match name.[0] with 'a' .. 'z' | '_' -> true | _ -> false)
  && String.for_all (function 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true | _ -> false) name

let read_file file =
  let in_chan = open_in_bin file in
  let n = in_channel_length in_chan in
  let contents = really_input_string in_chan n in
  close_in in_chan;
  contents

(* Generate sail_lib.mli from the externs in the Sail library. Every
   extern with an OCaml binding must either appear in the generated
   interface with its type, or be explicitly listed as unimplemented
   in the overrides file, so the OCaml interface and the Sail library
   are always kept in sync. *)
let gen_sail_lib_mli externs_file header_file overrides_file =
  let open Yojson.Safe.Util in
  let errors = ref [] in
  let error fmt = ksprintf (fun msg -> errors := msg :: !errors) fmt in

  let overrides = Yojson.Safe.from_file overrides_file in
  let override_types = overrides |> member "types" |> to_assoc |> List.map (fun (name, typ) -> (name, to_string typ)) in
  let unimplemented = overrides |> member "unimplemented" |> to_list |> List.map to_string in

  (* The OCaml binding for each extern, and its type (if known), in
     the order they first appear, along with the file of their first
     appearance. *)
  let bindings = Hashtbl.create 256 in
  let order = ref [] in
  Yojson.Safe.from_file externs_file |> member "externs" |> to_list
  |> List.iter (fun extern ->
      let sail_bindings = extern |> member "bindings" in
      let binding =
        match sail_bindings |> member "ocaml" with `Null -> sail_bindings |> member "_" | binding -> binding
      in
      match binding with
      | `String name when is_sail_lib_binding name ->
          let typ = extern |> member "ocaml_type" |> to_string_option in
          let sail_name = extern |> member "name" |> to_string in
          let file = extern |> member "file" |> to_string in
          if not (Hashtbl.mem bindings name) then order := (file, name) :: !order;
          Hashtbl.add bindings name (sail_name, typ)
      | _ -> ()
  );
  (* Group the bindings by file, keeping them in order within each file. *)
  let order = List.stable_sort (fun (f1, _) (f2, _) -> String.compare f1 f2) (List.rev !order) in

  List.iter
    (fun name ->
      if not (Hashtbl.mem bindings name) then error "%s is listed in %s, but is not an extern" name overrides_file;
      if List.mem_assoc name override_types && List.mem name unimplemented then
        error "%s is both given a type and listed as unimplemented in %s" name overrides_file
    )
    (List.map fst override_types @ unimplemented);

  let header = read_file header_file in
  let header_vals =
    String.split_on_char '\n' header
    |> List.filter_map (fun line ->
        match String.split_on_char ' ' line with "val" :: name :: _ -> Some name | _ -> None
    )
  in

  let vals =
    List.filter_map
      (fun (file, name) ->
        let externs = Hashtbl.find_all bindings name |> List.rev in
        let sail_names = String.concat ", " (List.sort_uniq String.compare (List.map fst externs)) in
        if List.mem name header_vals then (
          error "%s (for %s) is declared in %s, but should be generated" name sail_names header_file;
          None
        )
        else if List.mem name unimplemented then None
        else (
          match List.assoc_opt name override_types with
          | Some typ -> Some (file, name, typ)
          | None -> (
              match List.sort_uniq String.compare (List.filter_map snd externs) with
              | _ when List.exists (fun (_, typ) -> Option.is_none typ) externs ->
                  error "No OCaml type for %s (for %s), add it to %s" name sail_names overrides_file;
                  None
              | [typ] -> Some (file, name, typ)
              | typs ->
                  error "Conflicting OCaml types for %s (for %s): %s. Add the correct type to %s" name sail_names
                    (String.concat ", " typs) overrides_file;
                  None
            )
        )
      )
      order
  in

  match List.rev !errors with
  | [] ->
      print_string header;
      printf "\n(* The following are generated from %s by sail_maker. *)\n" (Filename.basename externs_file);
      ignore
        (List.fold_left
           (fun prev_file (file, name, typ) ->
             if prev_file <> Some file then printf "\n(** {1 [%s]} *)\n\n" file;
             printf "val %s : %s\n" name typ;
             Some file
           )
           None vals
        )
  | errors ->
      List.iter (fun msg -> eprintf "Error: %s\n" msg) errors;
      exit 1

let usage =
  "sail_maker gen_manifest\n\n\
  \  Write manifest.ml to stdout containing Git commit and branch information.\n\n\n\n\
   sail_maker tarball --prefix=PREFIX [--z3=Z3_EXE_PATH] [--gmp=GMP_DLL_PATH]\n\n\
  \  Used for fixing up the `dune install` output in preparation for making release tarballs.\n\n\n\n\
   sail_maker gen_sail_lib_mli --externs=PATH --header=PATH --overrides=PATH\n\n\
  \  Write sail_lib.mli to stdout, generated from the externs in the Sail library.\n\n"

let main () =
  match Array.to_list Sys.argv with
  | [_; "gen_manifest"] -> gen_manifest ()
  | _ :: "tarball" :: args ->
      let prefix, z3_path, gmp_path = parse_tarball_args args in
      tarball prefix z3_path gmp_path
  | _ :: "embed" :: args ->
      let tag, file, virt = parse_embed_args args in
      embed tag file virt
  | _ :: "gen_sail_lib_mli" :: args ->
      let externs, header, overrides = parse_gen_sail_lib_mli_args args in
      gen_sail_lib_mli externs header overrides
  | _ ->
      prerr_endline usage;
      exit 1

let () =
  try main () with
  | Arg.Bad msg ->
      prerr_endline msg;
      exit 1
  | Arg.Help msg ->
      prerr_endline msg;
      exit 0
