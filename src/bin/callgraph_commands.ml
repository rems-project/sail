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
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

open Libsail

open Ast_util
open Callgraph
open Printf
open Interactive

let node_string n = node_id n |> string_of_id |> String.escaped

let edge_color _from_node _to_node = "black"

let node_color cuts =
  let module NodeSet = Set.Make (Node) in
  function
  | node when NodeSet.mem node cuts -> "red"
  | Register _ -> "lightpink"
  | Function _ -> "white"
  | Mapping _ -> "azure2"
  | Letbind _ -> "yellow"
  | Type _ -> "springgreen"
  | Overload _ -> "peachpuff"
  | Constructor _ -> "lightslateblue"
  | FunctionMeasure _ -> "olivegreen"
  | LoopMeasures _ -> "green"
  | Outcome _ -> "purple"

let dot_of_ast out_chan ast =
  let module G = Graph.Make (Node) in
  let module NodeSet = Set.Make (Node) in
  let g = graph_of_ast ast in
  G.make_dot ~node_color:(node_color NodeSet.empty) ~edge_color ~string_of_node:node_string out_chan g

let node_of_id env =
  let lets = Type_check.Env.get_toplevel_lets env in
  let specs = Type_check.Env.get_defined_val_specs env in
  fun id ->
    if IdSet.mem id lets then Letbind id
    else if IdSet.mem id specs then Function id
    else if Type_check.Env.bound_typ_id env id then Type id
    else (
      prerr_endline ("Warning: unknown identifier " ^ string_of_id id);
      Function id
    )

let () =
  let slice_roots = ref IdSet.empty in
  let slice_keep_std = ref false in
  let slice_cuts = ref IdSet.empty in

  ArgString
    ( "identifiers",
      fun arg ->
        ActionUnit
          (fun _ ->
            let args = Str.split (Str.regexp " +") arg in
            let ids = List.map mk_id args |> IdSet.of_list in
            Specialize.add_initial_calls ids;
            slice_roots := IdSet.union ids !slice_roots
          )
    )
  |> register_command ~name:"slice_roots" ~help:"Set the roots for :slice";

  ActionUnit (fun _ -> slice_keep_std := true)
  |> register_command ~name:"slice_keep_std" ~help:"Keep standard library contents during :slice";

  ArgString
    ( "identifiers",
      fun arg ->
        ActionUnit
          (fun _ ->
            let args = Str.split (Str.regexp " +") arg in
            let ids = List.map mk_id args |> IdSet.of_list in
            slice_cuts := IdSet.union ids !slice_cuts
          )
    )
  |> register_command ~name:"slice_cuts" ~help:"Set the cuts for :slice";

  Action
    (fun istate ->
      let module NodeSet = Set.Make (Node) in
      let module G = Graph.Make (Node) in
      let g = graph_of_ast istate.ast in
      let roots = !slice_roots |> IdSet.elements |> List.map (node_of_id istate.env) |> NodeSet.of_list in
      let cuts = !slice_cuts |> IdSet.elements |> List.map (node_of_id istate.env) |> NodeSet.of_list in
      let g = G.prune roots cuts g in
      { istate with ast = filter_ast_extra cuts g istate.ast !slice_keep_std }
    )
  |> register_command ~name:"slice"
       ~help:
         "Slice AST to the definitions which the functions given by :slice_roots depend on, up to the functions given \
          by :slice_cuts";

  Action
    (fun istate ->
      let module NodeSet = Set.Make (Node) in
      let module NodeMap = Map.Make (Node) in
      let module G = Graph.Make (Node) in
      let g = graph_of_ast istate.ast in
      let roots = !slice_roots |> IdSet.elements |> List.map (node_of_id istate.env) |> NodeSet.of_list in
      let keep = function
        | Function id, _ when IdSet.mem id !slice_roots -> None
        | Function id, _ -> Some (Function id)
        | _ -> None
      in
      let cuts = NodeMap.bindings g |> List.filter_map keep |> NodeSet.of_list in
      let g = G.prune roots cuts g in
      { istate with ast = filter_ast_extra cuts g istate.ast !slice_keep_std }
    )
  |> register_command ~name:"thin_slice"
       ~help:(sprintf ":thin_slice - Slice AST to the function definitions given with %s" (command "slice_roots"));

  ArgString
    ( "format",
      fun arg ->
        ActionUnit
          (fun istate ->
            let format = if arg = "" then "svg" else arg in
            let dotfile, out_chan = Filename.open_temp_file "sail_graph_" ".gz" in
            let image = Filename.temp_file "sail_graph_" ("." ^ format) in
            dot_of_ast out_chan istate.ast;
            close_out out_chan;
            let _ = Unix.system (Printf.sprintf "dot -T%s %s -o %s" format dotfile image) in
            let _ = Unix.system (Printf.sprintf "xdg-open %s" image) in
            ()
          )
    )
  |> register_command ~name:"graph" ~help:"Draw a callgraph using dot in :0 (e.g. svg), and open with xdg-open"
