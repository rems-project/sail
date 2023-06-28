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

open Ast_defs
open Type_check

module StringMap = Map.Make (String)

type target = {
  name : string;
  options : (Arg.key * Arg.spec * Arg.doc) list;
  pre_parse_hook : unit -> unit;
  pre_rewrites_hook : tannot ast -> Effects.side_effect_info -> Env.t -> unit;
  rewrites : (string * Rewrites.rewriter_arg list) list;
  action : Yojson.Basic.t option -> string -> string option -> tannot ast -> Effects.side_effect_info -> Env.t -> unit;
  asserts_termination : bool;
}

let name tgt = tgt.name

let run_pre_parse_hook tgt = tgt.pre_parse_hook

let run_pre_rewrites_hook tgt = tgt.pre_rewrites_hook

let action tgt = tgt.action

let rewrites tgt = Rewrites.instantiate_rewrites tgt.rewrites

let asserts_termination tgt = tgt.asserts_termination

let targets = ref StringMap.empty

let the_target = ref None

let register ~name ?flag ?description:desc ?(options = []) ?(pre_parse_hook = fun () -> ())
    ?(pre_rewrites_hook = fun _ _ _ -> ()) ?(rewrites = []) ?(asserts_termination = false) action =
  let set_target () =
    match !the_target with
    | None -> the_target := Some name
    | Some tgt ->
        prerr_endline ("Cannot use multiple Sail targets simultaneously: " ^ tgt ^ " and " ^ name);
        exit 1
  in
  let desc = match desc with Some desc -> desc | None -> " invoke the Sail " ^ name ^ " target" in
  let flag = match flag with Some flag -> flag | None -> name in
  let tgt =
    {
      name;
      options = ("-" ^ flag, Arg.Unit set_target, desc) :: options;
      pre_parse_hook;
      pre_rewrites_hook;
      rewrites;
      action;
      asserts_termination;
    }
  in
  targets := StringMap.add name tgt !targets;
  tgt

let get_the_target () = match !the_target with Some name -> StringMap.find_opt name !targets | None -> None

let get ~name = StringMap.find_opt name !targets

let extract_options () =
  let opts = StringMap.bindings !targets |> List.map (fun (_, tgt) -> tgt.options) |> List.concat in
  targets := StringMap.map (fun tgt -> { tgt with options = [] }) !targets;
  opts

let () =
  let open Interactive in
  ActionUnit (fun _ -> List.iter (fun (name, _) -> print_endline name) (StringMap.bindings !targets))
  |> register_command ~name:"list_targets" ~help:"list available Sail targets for use with :target";

  ArgString
    ( "target",
      fun name ->
        Action
          (fun istate ->
            match get ~name with
            | Some tgt ->
                let ast, effect_info, env = Rewrites.rewrite istate.effect_info istate.env (rewrites tgt) istate.ast in
                { istate with ast; env; effect_info }
            | None ->
                print_endline ("No target " ^ name);
                istate
          )
    )
  |> register_command ~name:"rewrites" ~help:"perform rewrites for a target. See :list_targets for a list of targets";

  ArgString
    ( "target",
      fun name ->
        ArgString
          ( "out",
            fun out ->
              ActionUnit
                (fun istate ->
                  match get ~name with
                  | Some tgt ->
                      action tgt istate.config istate.default_sail_dir (Some out) istate.ast istate.effect_info
                        istate.env
                  | None -> print_endline ("No target " ^ name)
                )
          )
    )
  |> register_command ~name:"target"
       ~help:
         "invoke Sail target. See :list_targets for a list of targets. out parameter is equivalent to command line -o \
          option"
