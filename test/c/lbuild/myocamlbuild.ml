(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  SPDX-License-Identifier: BSD-2-Clause                                 *)
(**************************************************************************)

open Ocamlbuild_plugin
open Command
open Pathname
open Outcome

(* paths relative to _build *)
let lem = "lem"

(* All -wl ignores should be removed if you want to see the pattern compilation, exhaustive, and unused var warnings *)
let lem_opts =
  [
    A "-lib";
    P "..";
    A "-wl_pat_comp";
    P "ign";
    A "-wl_pat_exh";
    P "ign";
    A "-wl_pat_fail";
    P "ign";
    A "-wl_unused_vars";
    P "ign";
  ]
;;

dispatch
  begin
    function
    | After_rules ->
        rule "lem -> ml" ~prod:"%.ml" ~dep:"%.lem" (fun env builder ->
            Seq [Cmd (S ([P lem] @ lem_opts @ [A "-ocaml"; P (env "%.lem")]))]
        )
    | _ -> ()
  end
