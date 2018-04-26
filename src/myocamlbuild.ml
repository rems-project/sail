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
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

open Ocamlbuild_plugin ;;
open Command ;;
open Pathname ;;
open Outcome ;;

let split ch s =
  let x = ref [] in
  let rec go s =
    if not (String.contains s ch) then List.rev (s :: !x)
    else begin
      let pos = String.index s ch in
      x := (String.before s pos)::!x;
      go (String.after s (pos + 1))
    end
  in
  go s

(* paths relative to _build *)
let lem = "lem" ;;

(* All -wl ignores should be removed if you want to see the pattern compilation, exhaustive, and unused var warnings *)
let lem_opts = [A "-lib"; P "../gen_lib";
                A "-wl_pat_comp"; P "ign"; 
                A "-wl_pat_exh";  P "ign"; 
                A "-wl_pat_fail"; P "ign";
                A "-wl_unused_vars";   P "ign";
(*                A "-suppress_renaming";*)
               ] ;;

dispatch begin function
| After_rules ->
    (* ocaml_lib "lem_interp/interp"; *)
    ocaml_lib ~extern:false ~dir:"pprint/src" ~tag_name:"use_pprint" "pprint/src/PPrintLib";

    rule "lem -> ml"
    ~prod: "%.ml"
    ~dep: "%.lem"
    (fun env builder -> Seq [
      Cmd (S ([ P lem] @ lem_opts @ [ A "-ocaml"; P (env "%.lem") ]));
      ]);

    rule "sail -> lem"
    ~prod: "%.lem"
    ~deps: ["%.sail"; "sail.native"]
    (fun env builder ->
      let sail_opts = List.map (fun s -> A s) (
        "-lem_ast" ::
        try
          split ',' (Sys.getenv "SAIL_OPTS")
        with Not_found -> []) in
      Seq [
        Cmd (S ([ P "./sail.native"] @ sail_opts @ [P (env "%.sail")]));
        mv (basename (env "%.lem")) (dirname (env "%.lem"))
      ]);

| _ -> ()
end ;;
