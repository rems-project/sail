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

open Ast
open Ast_util
open Rewriter

type node =
  (* In the graph we have a node Register that represents the actual
     register, but functions get only get transitive dependencies on
     that through Register_read, Register_write, and Register_ref
     nodes. *)
  | Register of id
  | Function of id
  | Letbind of id
  | Type of id
  | Overload of id

let node_id = function
  | Register id -> id
  | Function id -> id
  | Letbind id -> id
  | Type id -> id
  | Overload id -> id

let node_kind = function
  | Register _ -> 0
  | Function _ -> 1
  | Letbind _ -> 3
  | Type _ -> 4
  | Overload _ -> 5

module Node = struct
  type t = node
  let compare n1 n2 =
    let lex_ord c1 c2 = if c1 = 0 then c2 else c1 in
    lex_ord (compare (node_kind n1) (node_kind n2)) (Id.compare (node_id n1) (node_id n2))
end

let node_color cuts =
  let module NodeSet = Set.Make(Node) in
  function
  | node when NodeSet.mem node cuts -> "red"
  | Register _ -> "lightpink"
  | Function _ -> "white"
  | Letbind _ -> "yellow"
  | Type _ -> "springgreen"
  | Overload _ -> "peachpuff"

let node_string n = node_id n |> string_of_id |> String.escaped

let edge_color from_node to_node = "black"

let builtins =
  let open Type_check in
  IdSet.of_list (List.map fst (Bindings.bindings Env.builtin_typs))

let typ_ids typ =
  let rec typ_ids (Typ_aux (aux, _)) =
    match aux with
    | Typ_var _ | Typ_internal_unknown -> IdSet.empty
    | Typ_id id -> IdSet.singleton id
    | Typ_app (id, typs) ->
     IdSet.add id (List.fold_left IdSet.union IdSet.empty (List.map typ_arg_ids typs))
    | Typ_fn (typs, typ, _) ->
       IdSet.union (typ_ids typ) (List.fold_left IdSet.union IdSet.empty (List.map typ_ids typs))
    | Typ_bidir (typ1, typ2) ->
       IdSet.union (typ_ids typ1) (typ_ids typ2)
    | Typ_tup typs ->
       List.fold_left IdSet.union IdSet.empty (List.map typ_ids typs)
    | Typ_exist (_, _, typ) -> typ_ids typ
  and typ_arg_ids (A_aux (aux, _)) =
    match aux with
    | A_typ typ -> typ_ids typ
    | _ -> IdSet.empty
  in
  IdSet.diff (typ_ids typ) builtins

let add_def_to_graph graph def =
  let open Type_check in
  let module G = Graph.Make(Node) in
  let graph = ref graph in

  let scan_exp self e_aux annot =
    let env = env_of_annot annot in
    begin match e_aux with
    | E_id id ->
       begin match Env.lookup_id id env with
       | Register _ -> graph := G.add_edge self (Register id) !graph
       | _ ->
          if IdSet.mem id (Env.get_toplevel_lets env) then
            graph := G.add_edge self (Letbind id) !graph
          else ()
       end
    | E_app (id, _) ->
       graph := G.add_edge self (Function id) !graph
    | E_ref id ->
       graph := G.add_edge self (Register id) !graph
    | E_cast (typ, _) ->
       IdSet.iter (fun id -> graph := G.add_edge self (Type id) !graph) (typ_ids typ)
    | _ -> ()
    end;
    E_aux (e_aux, annot)
  in
  let rw_exp self = { id_exp_alg with e_aux = (fun (e_aux, annot) -> scan_exp self e_aux annot) } in

  let rewriters self =
    { rewriters_base with
      rewrite_exp = (fun _ -> fold_exp (rw_exp self));
      rewrite_let = (fun _ -> fold_letbind (rw_exp self));
    }
  in

  begin match def with
  | DEF_spec (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (typq, typ), _), id, _, _), _)) ->
     graph := G.add_edges (Function id) [] !graph;
     IdSet.iter (fun typ_id -> graph := G.add_edge (Function id) (Type typ_id) !graph) (typ_ids typ)
  | DEF_fundef fdef ->
     let id = id_of_fundef fdef in
     graph := G.add_edges (Function id) [] !graph;
     ignore (rewrite_fun (rewriters (Function id)) fdef)
  | DEF_val (LB_aux (LB_val (pat, exp), _) as lb) ->
     let ids = pat_ids pat in
     IdSet.iter (fun id -> graph := G.add_edges (Letbind id) [] !graph) ids;
     IdSet.iter (fun id -> ignore (rewrite_let (rewriters (Letbind id)) lb)) ids
  | _ -> ()
  end;
  !graph

let rec graph_of_ast (Defs defs) =
  let module G = Graph.Make(Node) in

  match defs with
  | def :: defs ->
     let g = graph_of_ast (Defs defs) in
     add_def_to_graph g def

  | [] -> G.empty

let dot_of_ast ast =
  let module G = Graph.Make(Node) in
  let module NodeSet = Set.Make(Node) in
  let g = graph_of_ast ast in
  let roots = NodeSet.of_list (List.map (fun str -> Function (mk_id str)) ["execute_CGetPerm"; "execute_CSeal"]) in
  let cuts = NodeSet.of_list (List.map (fun str -> Function (mk_id str)) ["readCapReg"; "writeCapReg"; "rGPR"; "wGPR"; "SignalException"]) in
  let g = G.prune roots cuts g in
  G.make_dot (node_color cuts) edge_color node_string stdout g
