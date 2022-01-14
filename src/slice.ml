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

open Ast
open Ast_defs
open Ast_util
open Rewriter

type node =
  | Register of id
  | Function of id
  | Letbind of id
  | Type of id
  | Overload of id
  | Constructor of id

let node_id = function
  | Register id -> id
  | Function id -> id
  | Letbind id -> id
  | Type id -> id
  | Overload id -> id
  | Constructor id -> id

let node_kind = function
  | Register _ -> 0
  | Function _ -> 1
  | Letbind _ -> 3
  | Type _ -> 4
  | Overload _ -> 5
  | Constructor _ -> 6

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
  | Constructor _ -> "lightslateblue"

let node_string n = node_id n |> string_of_id |> String.escaped

let edge_color from_node to_node = "black"

let builtins =
  let open Type_check in
  IdSet.of_list (List.map fst (Bindings.bindings Env.builtin_typs))

let rec constraint_ids' (NC_aux (aux, _)) =
  match aux with
  | NC_equal (n1, n2) | NC_bounded_le (n1, n2) | NC_bounded_ge (n1, n2) | NC_bounded_lt (n1, n2) | NC_bounded_gt (n1, n2) | NC_not_equal (n1, n2) ->
     IdSet.union (nexp_ids' n1) (nexp_ids' n2)
  | NC_or (nc1, nc2) | NC_and (nc1, nc2) ->
     IdSet.union (constraint_ids' nc1) (constraint_ids' nc2)
  | NC_var _ | NC_true | NC_false | NC_set _ -> IdSet.empty
  | NC_app (id, args) ->
     IdSet.add id (List.fold_left IdSet.union IdSet.empty (List.map typ_arg_ids' args))

and nexp_ids' (Nexp_aux (aux, _)) =
  match aux with
  | Nexp_id id -> IdSet.singleton id
  | Nexp_app (id, nexps) ->
     IdSet.add id (List.fold_left IdSet.union IdSet.empty (List.map nexp_ids' nexps))
  | Nexp_var _ | Nexp_constant _ -> IdSet.empty
  | Nexp_exp n | Nexp_neg n -> nexp_ids' n
  | Nexp_times (n1, n2) | Nexp_sum (n1, n2) | Nexp_minus (n1, n2) ->
     IdSet.union (nexp_ids' n1) (nexp_ids' n2)

and typ_ids' (Typ_aux (aux, _)) =
  match aux with
  | Typ_var _ | Typ_internal_unknown -> IdSet.empty
  | Typ_id id -> IdSet.singleton id
  | Typ_app (id, args) ->
     IdSet.add id (List.fold_left IdSet.union IdSet.empty (List.map typ_arg_ids' args))
  | Typ_fn (typs, typ, _) ->
     IdSet.union (typ_ids' typ) (List.fold_left IdSet.union IdSet.empty (List.map typ_ids' typs))
  | Typ_bidir (typ1, typ2, _) ->
     IdSet.union (typ_ids' typ1) (typ_ids' typ2)
  | Typ_tup typs ->
     List.fold_left IdSet.union IdSet.empty (List.map typ_ids' typs)
  | Typ_exist (_, _, typ) -> typ_ids' typ

and typ_arg_ids' (A_aux (aux, _)) =
  match aux with
  | A_typ typ -> typ_ids' typ
  | A_nexp nexp -> nexp_ids' nexp
  | A_bool nc -> constraint_ids' nc
  | A_order _ -> IdSet.empty

let constraint_ids nc = IdSet.diff (constraint_ids' nc) builtins
let nexp_ids nc = IdSet.diff (constraint_ids' nc) builtins
and typ_ids typ = IdSet.diff (typ_ids' typ) builtins
let typ_arg_ids nc = IdSet.diff (typ_arg_ids' nc) builtins

let add_def_to_graph graph def =
  let open Type_check in
  let module G = Graph.Make(Node) in
  let graph = ref graph in

  let scan_pat self p_aux annot =
    let env = env_of_annot annot in
    begin match p_aux with
    | P_app (id, _) ->
       graph := G.add_edge self (Constructor id) !graph
    | P_typ (typ, _) ->
       IdSet.iter (fun id -> graph := G.add_edge self (Type id) !graph) (typ_ids typ)
    | _ -> ()
    end;
    P_aux (p_aux, annot)
  in
  let rw_pat self = { id_pat_alg with p_aux = (fun (p_aux, annot) -> scan_pat self p_aux annot) } in

  let scan_lexp self lexp_aux annot =
    let env = env_of_annot annot in
    begin match lexp_aux with
    | LEXP_cast (typ, id) ->
       IdSet.iter (fun id -> graph := G.add_edge self (Type id) !graph) (typ_ids typ);
       begin match Env.lookup_id id env with
       | Register _ ->
          graph := G.add_edge self (Register id) !graph
       | Enum _ -> graph := G.add_edge self (Constructor id) !graph
       | _ ->
          if IdSet.mem id (Env.get_toplevel_lets env) then
            graph := G.add_edge self (Letbind id) !graph
          else ()
       end
    | LEXP_memory (id, _) ->
       graph := G.add_edge self (Function id) !graph
    | LEXP_id id ->
       begin match Env.lookup_id id env with
       | Register _ ->
          graph := G.add_edge self (Register id) !graph
       | Enum _ -> graph := G.add_edge self (Constructor id) !graph
       | _ ->
          if IdSet.mem id (Env.get_toplevel_lets env) then
            graph := G.add_edge self (Letbind id) !graph
          else ()
       end
    | _ -> ()
    end;
    LEXP_aux (lexp_aux, annot)
  in

  let scan_exp self e_aux annot =
    let env = env_of_annot annot in
    begin match e_aux with
    | E_id id ->
       begin match Env.lookup_id id env with
       | Register _ -> graph := G.add_edge self (Register id) !graph
       | Enum _ -> graph := G.add_edge self (Constructor id) !graph
       | _ ->
          if IdSet.mem id (Env.get_toplevel_lets env) then
            graph := G.add_edge self (Letbind id) !graph
          else ()
       end
    | E_app (id, _) ->
       if Env.is_union_constructor id env then
         graph := G.add_edge self (Constructor id) !graph
       else
         graph := G.add_edge self (Function id) !graph
    | E_ref id ->
       graph := G.add_edge self (Register id) !graph
    | E_cast (typ, _) ->
       IdSet.iter (fun id -> graph := G.add_edge self (Type id) !graph) (typ_ids typ)
    | _ -> ()
    end;
    E_aux (e_aux, annot)
  in
  let rw_exp self = { id_exp_alg with e_aux = (fun (e_aux, annot) -> scan_exp self e_aux annot);
                                      lEXP_aux = (fun (l_aux, annot) -> scan_lexp self l_aux annot);
                                      pat_alg = rw_pat self } in

  let rewriters self =
    { rewriters_base with
      rewrite_exp = (fun _ -> fold_exp (rw_exp self));
      rewrite_pat = (fun _ -> fold_pat (rw_pat self));
      rewrite_let = (fun _ -> fold_letbind (rw_exp self));
    }
  in

  let scan_quant_item self (QI_aux (aux, _)) =
    match aux with
    | QI_id _ -> ()
    | QI_constraint nc ->
       IdSet.iter (fun id -> graph := G.add_edge self (Type id) !graph) (constraint_ids nc)
    | QI_constant _ -> ()
  in

  let scan_typquant self (TypQ_aux (aux, _)) =
    match aux with
    | TypQ_no_forall -> ()
    | TypQ_tq quants -> List.iter (scan_quant_item self) quants
  in

  let add_type_def_to_graph (TD_aux (aux, (l, _))) =
    match aux with
    | TD_abbrev (id, typq, arg) ->
       graph := G.add_edges (Type id) (List.map (fun id -> Type id) (IdSet.elements (typ_arg_ids arg))) !graph;
       scan_typquant (Type id) typq
    | TD_record (id, typq, fields, _) ->
       let field_nodes =
         List.map (fun (typ, _) -> typ_ids typ) fields
         |> List.fold_left IdSet.union IdSet.empty
         |> IdSet.elements
         |> List.map (fun id -> Type id)
       in
       graph := G.add_edges (Type id) field_nodes !graph;
       scan_typquant (Type id) typq
    | TD_variant (id, typq, ctors, _) ->
       let ctor_nodes =
         List.map (fun (Tu_aux (Tu_ty_id (typ, id), _)) -> (typ_ids typ, id)) ctors
         |> List.fold_left (fun (ids, ctors) (ids', ctor) -> (IdSet.union ids ids', IdSet.add ctor ctors)) (IdSet.empty, IdSet.empty)
       in
       IdSet.iter (fun ctor_id -> graph := G.add_edge (Constructor ctor_id) (Type id) !graph) (snd ctor_nodes);
       IdSet.iter (fun typ_id -> graph := G.add_edge (Type id) (Type typ_id) !graph) (fst ctor_nodes);
       scan_typquant (Type id) typq
    | TD_enum (id, ctors, _) ->
       List.iter (fun ctor_id -> graph := G.add_edge (Constructor ctor_id) (Type id) !graph) ctors
    | TD_bitfield _ ->
       Reporting.unreachable l __POS__ "Bitfield should be re-written"
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
  | DEF_type tdef ->
     add_type_def_to_graph tdef
  | DEF_reg_dec (DEC_aux (DEC_reg (_, _, typ, id), _)) ->
     IdSet.iter (fun typ_id -> graph := G.add_edge (Register id) (Type typ_id) !graph) (typ_ids typ)
  | DEF_reg_dec (DEC_aux (DEC_config (id, typ, exp), _)) ->
     ignore (fold_exp (rw_exp (Register id)) exp);
     IdSet.iter (fun typ_id -> graph := G.add_edge (Register id) (Type typ_id) !graph) (typ_ids typ)
  | _ -> ()
  end;
  !graph

let rec graph_of_defs defs =
  let module G = Graph.Make(Node) in

  match defs with
  | def :: defs ->
     let g = graph_of_defs defs in
     add_def_to_graph g def

  | [] -> G.empty

let graph_of_ast ast = graph_of_defs ast.defs
        
let id_of_typedef (TD_aux (aux, _)) =
  match aux with
  | TD_abbrev (id, _, _) -> id
  | TD_record (id, _, _, _) -> id
  | TD_variant (id, _, _, _) -> id
  | TD_enum (id, _, _) -> id
  | TD_bitfield (id, _, _) -> id

let id_of_reg_dec (DEC_aux (aux, _)) =
  match aux with
  | DEC_reg (_, _, _, id) -> id
  | DEC_config (id, _, _) -> id
  | _ -> assert false

let filter_ast cuts g ast =
  let rec filter_ast' g =
    let module NS = Set.Make(Node) in
    let module NM = Map.Make(Node) in
    function
    | DEF_fundef fdef :: defs when NS.mem (Function (id_of_fundef fdef)) cuts -> filter_ast' g defs
    | DEF_fundef fdef :: defs when NM.mem (Function (id_of_fundef fdef)) g -> DEF_fundef fdef :: filter_ast' g defs
    | DEF_fundef _ :: defs -> filter_ast' g defs

    | DEF_reg_dec rdec :: defs when NM.mem (Register (id_of_reg_dec rdec)) g -> DEF_reg_dec rdec :: filter_ast' g defs
    | DEF_reg_dec _ :: defs -> filter_ast' g defs

    | DEF_spec vs :: defs when NM.mem (Function (id_of_val_spec vs)) g -> DEF_spec vs :: filter_ast' g defs
    | DEF_spec _ :: defs -> filter_ast' g defs

    | DEF_val (LB_aux (LB_val (pat, exp), _) as lb) :: defs ->
       let ids = pat_ids pat |> IdSet.elements in
       if List.exists (fun id -> NM.mem (Letbind id) g) ids then
         DEF_val lb :: filter_ast' g defs
       else
         filter_ast' g defs

    | DEF_type tdef :: defs when NM.mem (Type (id_of_typedef tdef)) g -> DEF_type tdef :: filter_ast' g defs
    | DEF_type _ :: defs -> filter_ast' g defs

    | DEF_measure (id,_,_) :: defs when NS.mem (Function id) cuts -> filter_ast' g defs
    | (DEF_measure (id,_,_) as def) :: defs when NM.mem (Function id) g -> def :: filter_ast' g defs
    | DEF_measure _ :: defs -> filter_ast' g defs

    | def :: defs -> def :: filter_ast' g defs

    | [] -> []
  in
  { ast with defs = filter_ast' g ast.defs }

let dot_of_ast out_chan ast =
  let module G = Graph.Make(Node) in
  let module NodeSet = Set.Make(Node) in
  let g = graph_of_ast ast in
  G.make_dot (node_color NodeSet.empty) edge_color node_string out_chan g

let filter_ast_ids roots cuts ast =
  let module NodeSet = Set.Make(Node) in
  let module G = Graph.Make(Node) in
  let g = graph_of_ast ast in
  let roots = roots |> IdSet.elements |> List.map (fun id -> Function id) |> NodeSet.of_list in
  let cuts = cuts |> IdSet.elements |> List.map (fun id -> Function id) |> NodeSet.of_list in
  let g = G.prune roots cuts g in
  filter_ast cuts g ast

let () =
  let open Printf in
  let open Interactive in
  let slice_roots = ref IdSet.empty in
  let slice_cuts = ref IdSet.empty in

  ArgString ("identifiers", fun arg -> Action (fun () ->
    let args = Str.split (Str.regexp " +") arg in
    let ids = List.map mk_id args |> IdSet.of_list in
    Specialize.add_initial_calls ids;
    slice_roots := IdSet.union ids !slice_roots
  )) |> register_command ~name:"slice_roots" ~help:"Set the roots for :slice";

  ArgString ("identifiers", fun arg -> Action (fun () ->
    let args = Str.split (Str.regexp " +") arg in
    let ids = List.map mk_id args |> IdSet.of_list in
    slice_cuts := IdSet.union ids !slice_cuts
  )) |> register_command ~name:"slice_cuts" ~help:"Set the cuts for :slice";

  Action (fun () ->
    let module NodeSet = Set.Make(Node) in
    let module G = Graph.Make(Node) in
    let g = graph_of_ast !ast in
    let roots = !slice_roots |> IdSet.elements |> List.map (fun id -> Function id) |> NodeSet.of_list in
    let cuts = !slice_cuts |> IdSet.elements |> List.map (fun id -> Function id) |> NodeSet.of_list in
    let g = G.prune roots cuts g in
    ast := filter_ast cuts g !ast
  ) |> register_command
         ~name:"slice"
         ~help:"Slice AST to the definitions which the functions given \
                by :slice_roots depend on, up to the functions given \
                by :slice_cuts";

  Action (fun () ->
    let module NodeSet = Set.Make(Node) in
    let module NodeMap = Map.Make(Node) in
    let module G = Graph.Make(Node) in
    let g = graph_of_ast !ast in
    let roots = !slice_roots |> IdSet.elements |> List.map (fun id -> Function id) |> NodeSet.of_list in
    let keep = function
      | (Function id,_) when IdSet.mem id (!slice_roots) -> None
      | (Function id,_) -> Some (Function id)
      | _ -> None
    in
    let cuts = NodeMap.bindings g |> Util.map_filter keep |> NodeSet.of_list in
    let g = G.prune roots cuts g in
    ast := filter_ast cuts g !ast
  ) |> register_command
         ~name:"thin_slice"
         ~help:(sprintf ":thin_slice - Slice AST to the function definitions given with %s" (command "slice_roots"));

  ArgString ("format", fun arg -> Action (fun () ->
    let format = if arg = "" then "svg" else arg in
    let dotfile, out_chan = Filename.open_temp_file "sail_graph_" ".gz" in
    let image = Filename.temp_file "sail_graph_" ("." ^ format) in
    dot_of_ast out_chan !ast;
    close_out out_chan;
    let _ = Unix.system (Printf.sprintf "dot -T%s %s -o %s" format dotfile image) in
    let _ = Unix.system (Printf.sprintf "xdg-open %s" image) in
    ()
  )) |> register_command
          ~name:"graph"
          ~help:"Draw a callgraph using dot in :0 (e.g. svg), and open with xdg-open"


