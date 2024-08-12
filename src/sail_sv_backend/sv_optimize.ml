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
(*    Louis-Emile Ploix                                                     *)
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

open Jib_util
open Sv_ir

module RemoveUnitPorts = struct
  type port_action = Keep_port | Remove_port

  let is_unit_port (port : sv_module_port) = match port.typ with CT_unit -> true | _ -> false

  let port_var (port : sv_module_port) = SVD_var (port.name, port.typ)

  let scan_ports ports = List.map (fun port -> if is_unit_port port then Remove_port else Keep_port) ports

  let apply_port_action action x = match action with Keep_port -> Some x | Remove_port -> None

  class unit_port_visitor port_actions : svir_visitor =
    object
      inherit empty_svir_visitor

      method! vdef =
        function
        | SVD_module { name; input_ports; output_ports; defs } ->
            port_actions := SVNameMap.add name (scan_ports input_ports, scan_ports output_ports) !port_actions;
            let unit_inputs, input_ports = List.partition is_unit_port input_ports in
            let unit_outputs, output_ports = List.partition is_unit_port output_ports in
            ChangeDoChildrenPost
              ( SVD_module
                  {
                    name;
                    input_ports;
                    output_ports;
                    defs = List.map port_var unit_inputs @ List.map port_var unit_outputs @ defs;
                  },
                fun def -> def
              )
        | _ -> SkipChildren
    end

  class unit_connection_visitor port_actions : svir_visitor =
    object
      inherit empty_svir_visitor

      method! vdef =
        function
        | SVD_instantiate { module_name; instance_name; input_connections; output_connections } -> begin
            match SVNameMap.find_opt module_name port_actions with
            | Some (input_port_action, output_port_action) ->
                let input_connections =
                  List.map2 apply_port_action input_port_action input_connections |> Util.option_these
                in
                let output_connections =
                  List.map2 apply_port_action output_port_action output_connections |> Util.option_these
                in
                ChangeTo (SVD_instantiate { module_name; instance_name; input_connections; output_connections })
            | None -> SkipChildren
          end
        | SVD_module _ -> DoChildren
        | _ -> DoChildren
    end

  let rewrite defs =
    let port_actions = ref SVNameMap.empty in
    let defs = visit_sv_defs (new unit_port_visitor port_actions) defs in
    visit_sv_defs (new unit_connection_visitor !port_actions) defs
end

let remove_unit_ports defs = RemoveUnitPorts.rewrite defs
