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

open Interactive.State

let latex_options =
  [
    ( "-latex_prefix",
      Arg.String (fun prefix -> Latex.opt_prefix := prefix),
      "<prefix> set a custom prefix for generated LaTeX labels and macro commands (default sail)"
    );
    ("-latex_full_valspecs", Arg.Clear Latex.opt_simple_val, " print full valspecs in LaTeX output");
    ( "-latex_abbrevs",
      Arg.String
        (fun s ->
          let abbrevs = String.split_on_char ';' s in
          let filtered = List.filter (fun abbrev -> not (String.equal "" abbrev)) abbrevs in
          match
            List.find_opt
              (fun abbrev -> not (String.equal "." (String.sub abbrev (String.length abbrev - 1) 1)))
              filtered
          with
          | None -> Latex.opt_abbrevs := filtered
          | Some abbrev -> raise (Arg.Bad (abbrev ^ " does not end in a '.'"))
        ),
      " semicolon-separated list of abbreviations to fix spacing for in LaTeX output (default 'e.g.;i.e.')"
    );
  ]

let latex_target out_file { ast; effect_info; env; _ } =
  Reporting.opt_warnings := true;
  let latex_dir = match out_file with None -> "sail_latex" | Some s -> s in
  begin
    try
      if not (Sys.is_directory latex_dir) then begin
        prerr_endline ("Failure: latex output location exists and is not a directory: " ^ latex_dir);
        exit 1
      end
    with Sys_error _ -> Unix.mkdir latex_dir 0o755
  end;
  Latex.opt_directory := latex_dir;
  let chan = open_out (Filename.concat latex_dir "commands.tex") in
  output_string chan (Pretty_print_sail.Document.to_string (Latex.defs (Type_check.strip_ast ast)));
  close_out chan

let _ =
  Target.register ~name:"latex" ~options:latex_options
    ~pre_parse_hook:(fun () ->
      Type_check.opt_expand_valspec := false;
      Type_check.opt_no_bitfield_expansion := true
    )
    latex_target
