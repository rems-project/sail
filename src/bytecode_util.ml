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
open Bytecode
open Value2
open PPrint

(* Define wrappers for creating bytecode instructions. Each function
   uses a counter to assign each instruction a unique identifier. *)

let instr_counter = ref 0

let instr_number () =
  let n = !instr_counter in
  incr instr_counter;
  n

let idecl ?loc:(l=Parse_ast.Unknown) ctyp id =
  I_aux (I_decl (ctyp, id), (instr_number (), l))

let iinit ?loc:(l=Parse_ast.Unknown) ctyp id cval =
  I_aux (I_init (ctyp, id, cval), (instr_number (), l))

let iif ?loc:(l=Parse_ast.Unknown) cval then_instrs else_instrs ctyp =
  I_aux (I_if (cval, then_instrs, else_instrs, ctyp), (instr_number (), l))

let ifuncall ?loc:(l=Parse_ast.Unknown) clexp id cvals ctyp =
  I_aux (I_funcall (clexp, false, id, cvals, ctyp), (instr_number (), l))

let iextern ?loc:(l=Parse_ast.Unknown) clexp id cvals ctyp =
  I_aux (I_funcall (clexp, true, id, cvals, ctyp), (instr_number (), l))

let icopy ?loc:(l=Parse_ast.Unknown) clexp cval =
  I_aux (I_copy (clexp, cval), (instr_number (), l))

let iconvert ?loc:(l=Parse_ast.Unknown) clexp ctyp1 id ctyp2 =
  I_aux (I_convert (clexp, ctyp1, id, ctyp2), (instr_number (), l))

let iclear ?loc:(l=Parse_ast.Unknown) ctyp id =
  I_aux (I_clear (ctyp, id), (instr_number (), l))

let ireturn ?loc:(l=Parse_ast.Unknown) cval =
  I_aux (I_return cval, (instr_number (), l))

let iblock ?loc:(l=Parse_ast.Unknown) instrs =
  I_aux (I_block instrs, (instr_number (), l))

let itry_block ?loc:(l=Parse_ast.Unknown) instrs =
  I_aux (I_try_block instrs, (instr_number (), l))

let ithrow ?loc:(l=Parse_ast.Unknown) cval =
  I_aux (I_throw cval, (instr_number (), l))
let icomment ?loc:(l=Parse_ast.Unknown) str =
  I_aux (I_comment str, (instr_number (), l))

let ilabel ?loc:(l=Parse_ast.Unknown) label =
  I_aux (I_label label, (instr_number (), l))
let igoto ?loc:(l=Parse_ast.Unknown) label =
  I_aux (I_goto label, (instr_number (), l))

let imatch_failure ?loc:(l=Parse_ast.Unknown) () =
  I_aux (I_match_failure, (instr_number (), l))

let iraw ?loc:(l=Parse_ast.Unknown) str =
  I_aux (I_raw str, (instr_number (), l))

let ijump ?loc:(l=Parse_ast.Unknown) cval label =
  I_aux (I_jump (cval, label), (instr_number (), l))

(**************************************************************************)
(* 1. Instruction pretty printer                                          *)
(**************************************************************************)

let string_of_value = function
  | V_bits bs -> Sail_values.show_bitlist bs ^ "ul"
  | V_int i -> Big_int.to_string i ^ "l"
  | V_bool true -> "true"
  | V_bool false -> "false"
  | V_null -> "NULL"
  | V_unit -> "UNIT"
  | V_bit Sail_values.B0 -> "0ul"
  | V_bit Sail_values.B1 -> "1ul"
  | V_string str -> "\"" ^ str ^ "\""
  | V_ctor_kind str -> "Kind_" ^ Util.zencode_string str
  | _ -> failwith "Cannot convert value to string"

let rec string_of_fragment ?zencode:(zencode=true) = function
  | F_id id when zencode -> Util.zencode_string (string_of_id id)
  | F_id id -> string_of_id id
  | F_ref id when zencode -> "&" ^ Util.zencode_string (string_of_id id)
  | F_ref id -> "&" ^ string_of_id id
  | F_lit v -> string_of_value v
  | F_call (str, frags) ->
     Printf.sprintf "%s(%s)" str (Util.string_of_list ", " (string_of_fragment ~zencode:zencode) frags)
  | F_field (f, field) ->
     Printf.sprintf "%s.%s" (string_of_fragment' ~zencode:zencode f) field
  | F_op (f1, op, f2) ->
     Printf.sprintf "%s %s %s" (string_of_fragment' ~zencode:zencode f1) op (string_of_fragment' ~zencode:zencode f2)
  | F_unary (op, f) ->
     op ^ string_of_fragment' ~zencode:zencode f
  | F_have_exception -> "have_exception"
  | F_current_exception -> "(*current_exception)"
  | F_raw raw -> raw
and string_of_fragment' ?zencode:(zencode=true) f =
  match f with
  | F_op _ | F_unary _ -> "(" ^ string_of_fragment ~zencode:zencode f ^ ")"
  | _ -> string_of_fragment ~zencode:zencode f

(* String representation of ctyps here is only for debugging and
   intermediate language pretty-printer. *)
let rec string_of_ctyp = function
  | CT_int -> "mpz_t"
  | CT_bits true -> "bv_t(dec)"
  | CT_bits false -> "bv_t(inc)"
  | CT_bits64 (n, true) -> "uint64_t(" ^ string_of_int n ^ ", dec)"
  | CT_bits64 (n, false) -> "uint64_t(" ^ string_of_int n ^ ", int)"
  | CT_int64 -> "int64_t"
  | CT_bit -> "bit"
  | CT_unit -> "unit"
  | CT_bool -> "bool"
  | CT_real -> "real"
  | CT_tup ctyps -> "(" ^ Util.string_of_list ", " string_of_ctyp ctyps ^ ")"
  | CT_struct (id, _) | CT_enum (id, _) | CT_variant (id, _) -> string_of_id id
  | CT_string -> "string"
  | CT_vector (true, ctyp) -> "vector(dec, " ^ string_of_ctyp ctyp ^ ")"
  | CT_vector (false, ctyp) -> "vector(inc, " ^ string_of_ctyp ctyp ^ ")"
  | CT_list ctyp -> "list(" ^ string_of_ctyp ctyp ^ ")"
  | CT_ref ctyp -> "ref(" ^ string_of_ctyp ctyp ^ ")"

let pp_id id =
  string (string_of_id id)

let pp_ctyp ctyp =
  string (string_of_ctyp ctyp |> Util.yellow |> Util.clear)

let pp_keyword str =
  string ((str |> Util.red |> Util.clear) ^ " ")

let pp_cval (frag, ctyp) =
  string (string_of_fragment ~zencode:false frag) ^^ string " : " ^^ pp_ctyp ctyp

let rec pp_clexp = function
  | CL_id id -> pp_id id
  | CL_field (id, field) -> pp_id id ^^ string "." ^^ string field
  | CL_addr id -> string "*" ^^ pp_id id
  | CL_addr_field (id, field) -> pp_id id ^^ string "->" ^^ string field
  | CL_current_exception -> string "current_exception"
  | CL_have_exception -> string "have_exception"

let rec pp_instr ?short:(short=false) (I_aux (instr, aux)) =
  match instr with
  | I_decl (ctyp, id) ->
     pp_keyword "var" ^^ pp_id id ^^ string " : " ^^ pp_ctyp ctyp
  | I_if (cval, then_instrs, else_instrs, ctyp) ->
     let pp_if_block = function
       | [] -> string "{}"
       | instrs -> surround 2 0 lbrace (separate_map (semi ^^ hardline) pp_instr instrs) rbrace
     in
     parens (pp_ctyp ctyp) ^^ space
     ^^ pp_keyword "if" ^^ pp_cval cval
     ^^ if short then
          empty
        else
          pp_keyword " then" ^^ pp_if_block then_instrs
          ^^ pp_keyword " else" ^^ pp_if_block else_instrs
  | I_jump (cval, label) ->
     pp_keyword "jump" ^^ pp_cval cval ^^ space ^^ string (label |> Util.blue |> Util.clear)
  | I_block instrs ->
     surround 2 0 lbrace (separate_map (semi ^^ hardline) pp_instr instrs) rbrace
  | I_try_block instrs ->
     pp_keyword "try" ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) pp_instr instrs) rbrace
  | I_reset (ctyp, id) ->
     pp_keyword "recreate" ^^ pp_id id ^^ string " : " ^^ pp_ctyp ctyp
  | I_init (ctyp, id, cval) ->
     pp_keyword "create" ^^ pp_id id ^^ string " : " ^^ pp_ctyp ctyp ^^ string " = " ^^ pp_cval cval
  | I_reinit (ctyp, id, cval) ->
     pp_keyword "recreate" ^^ pp_id id ^^ string " : " ^^ pp_ctyp ctyp ^^ string " = " ^^ pp_cval cval
  | I_funcall (x, _, f, args, ctyp2) ->
     separate space [ pp_clexp x; string "=";
                      string (string_of_id f |> Util.green |> Util.clear) ^^ parens (separate_map (string ", ") pp_cval args);
                      string ":"; pp_ctyp ctyp2 ]
  | I_convert (x, ctyp1, y, ctyp2) ->
     separate space [ pp_clexp x; colon; pp_ctyp ctyp1; string "=";
                      pp_keyword "convert" ^^ pp_id y; colon; pp_ctyp ctyp2 ]
  | I_copy (clexp, cval) ->
     separate space [pp_clexp clexp; string "="; pp_cval cval]
  | I_clear (ctyp, id) ->
     pp_keyword "kill" ^^ pp_id id ^^ string " : " ^^ pp_ctyp ctyp
  | I_return cval ->
     pp_keyword "return" ^^ pp_cval cval
  | I_throw cval ->
     pp_keyword "throw" ^^ pp_cval cval
  | I_comment str ->
     string ("// " ^ str |> Util.magenta |> Util.clear)
  | I_label str ->
     string (str |> Util.blue |> Util.clear) ^^ string ":"
  | I_goto str ->
     pp_keyword "goto" ^^ string (str |> Util.blue |> Util.clear)
  | I_match_failure ->
     pp_keyword "match_failure"
  | I_raw str ->
     pp_keyword "C" ^^ string (str |> Util.cyan |> Util.clear)

let pp_ctype_def = function
  | CTD_enum (id, ids) ->
     pp_keyword "enum" ^^ pp_id id ^^ string " = "
     ^^ separate_map (string " | ") pp_id ids
  | CTD_struct (id, fields) ->
     pp_keyword "struct" ^^ pp_id id ^^ string " = "
     ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) (fun (id, ctyp) -> pp_id id ^^ string " : " ^^ pp_ctyp ctyp) fields) rbrace
  | CTD_variant (id, ctors) ->
     pp_keyword "union" ^^ pp_id id ^^ string " = "
     ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) (fun (id, ctyp) -> pp_id id ^^ string " : " ^^ pp_ctyp ctyp) ctors) rbrace

let pp_cdef = function
  | CDEF_spec (id, ctyps, ctyp) ->
     pp_keyword "val" ^^ pp_id id ^^ string " : " ^^ parens (separate_map (comma ^^ space) pp_ctyp ctyps) ^^ string " -> " ^^ pp_ctyp ctyp
     ^^ hardline
  | CDEF_fundef (id, ret, args, instrs) ->
     let ret = match ret with
       | None -> empty
       | Some id -> space ^^ pp_id id
     in
     pp_keyword "function" ^^ pp_id id ^^ ret ^^ parens (separate_map (comma ^^ space) pp_id args) ^^ space
     ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) pp_instr instrs) rbrace
     ^^ hardline
  | CDEF_reg_dec (id, ctyp) ->
     pp_keyword "register" ^^ pp_id id ^^ string " : " ^^ pp_ctyp ctyp
     ^^ hardline
  | CDEF_type tdef -> pp_ctype_def tdef ^^ hardline
  | CDEF_let (n, bindings, instrs) ->
     let pp_binding (id, ctyp) = pp_id id ^^ string " : " ^^ pp_ctyp ctyp in
     pp_keyword "let" ^^ string (string_of_int n) ^^ parens (separate_map (comma ^^ space) pp_binding bindings) ^^ space
     ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) pp_instr instrs) rbrace ^^ space
     ^^ hardline
  | CDEF_startup (id, instrs)->
     pp_keyword "startup" ^^ pp_id id ^^ space
     ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) pp_instr instrs) rbrace
     ^^ hardline
  | CDEF_finish (id, instrs)->
     pp_keyword "finish" ^^ pp_id id ^^ space
     ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) pp_instr instrs) rbrace
     ^^ hardline

(**************************************************************************)
(* 2. Dependency Graphs                                                   *)
(**************************************************************************)

type graph_node =
  | G_id of id
  | G_label of string
  | G_instr of int * instr
  | G_start

let string_of_node = function
  | G_id id -> string_of_id id
  | G_label label -> label
  | G_instr (n, instr) -> string_of_int n ^ ": " ^ Pretty_print_sail.to_string (pp_instr ~short:true instr)
  | G_start -> "START"

module Node = struct
  type t = graph_node
  let compare gn1 gn2 =
    match gn1, gn2 with
    | G_id id1, G_id id2 -> Id.compare id1 id2
    | G_label str1, G_label str2 -> String.compare str1 str2
    | G_instr (n1, _), G_instr (n2, _) -> compare n1 n2
    | G_start  , _         -> 1
    | _        , G_start   -> -1
    | G_instr _, _         -> 1
    | _        , G_instr _ -> -1
    | G_id _   , _         -> 1
    | _        , G_id _    -> -1
end

module NM = Map.Make(Node)
module NS = Set.Make(Node)

type dep_graph = NS.t NM.t

let rec fragment_deps = function
  | F_id id | F_ref id -> NS.singleton (G_id id)
  | F_lit _ -> NS.empty
  | F_field (frag, _) | F_unary (_, frag) -> fragment_deps frag
  | F_call (_, frags) -> List.fold_left NS.union NS.empty (List.map fragment_deps frags)
  | F_op (frag1, _, frag2) -> NS.union (fragment_deps frag1) (fragment_deps frag2)
  | F_current_exception -> NS.empty
  | F_have_exception -> NS.empty
  | F_raw _ -> NS.empty

let cval_deps = function (frag, _) -> fragment_deps frag

let rec clexp_deps = function
  | CL_id id -> NS.singleton (G_id id)
  | CL_field (id, _) -> NS.singleton (G_id id)
  | CL_addr id -> NS.singleton (G_id id)
  | CL_addr_field (id, _) -> NS.singleton (G_id id)
  | CL_have_exception -> NS.empty
  | CL_current_exception -> NS.empty

(** Return the direct, non program-order dependencies of a single
   instruction **)
let instr_deps = function
  | I_decl (ctyp, id) -> NS.empty, NS.singleton (G_id id)
  | I_reset (ctyp, id) -> NS.empty, NS.singleton (G_id id)
  | I_init (ctyp, id, cval) | I_reinit (ctyp, id, cval) -> cval_deps cval, NS.singleton (G_id id)
  | I_if (cval, _, _, _) -> cval_deps cval, NS.empty
  | I_jump (cval, label) -> cval_deps cval, NS.singleton (G_label label)
  | I_funcall (clexp, _, _, cvals, _) -> List.fold_left NS.union NS.empty (List.map cval_deps cvals), clexp_deps clexp
  | I_convert (clexp, _, id, _) -> NS.singleton (G_id id), clexp_deps clexp
  | I_copy (clexp, cval) -> cval_deps cval, clexp_deps clexp
  | I_clear (_, id) -> NS.singleton (G_id id), NS.singleton (G_id id)
  | I_throw cval | I_return cval -> cval_deps cval, NS.empty
  | I_block _ | I_try_block _ -> NS.empty, NS.empty
  | I_comment _ | I_raw _ -> NS.empty, NS.empty
  | I_label label -> NS.singleton (G_label label), NS.empty
  | I_goto label -> NS.empty, NS.singleton (G_label label)
  | I_match_failure -> NS.empty, NS.empty

let add_link from_node to_node graph =
  try
    NM.add from_node (NS.add to_node (NM.find from_node graph)) graph
  with
  | Not_found -> NM.add from_node (NS.singleton to_node) graph

let leaves graph =
  List.fold_left (fun acc (from_node, to_nodes) -> NS.filter (fun to_node -> Node.compare to_node from_node != 0) (NS.union acc to_nodes))
                 NS.empty
                 (NM.bindings graph)

(* Ensure that all leaves exist in the graph *)
let fix_leaves graph =
  NS.fold (fun leaf graph -> if NM.mem leaf graph then graph else NM.add leaf NS.empty graph) (leaves graph) graph

let instrs_graph instrs =
  let icounter = ref 0 in
  let graph = ref NM.empty in

  let rec add_instr last_instr (I_aux (instr, _) as iaux) =
    incr icounter;
    let node = G_instr (!icounter, iaux) in
    match instr with
    | I_block instrs | I_try_block instrs ->
       List.fold_left add_instr last_instr instrs
    | I_if (_, then_instrs, else_instrs, _) ->
       begin
         let inputs, _ = instr_deps instr in (* if has no outputs *)
         graph := add_link last_instr node !graph;
         NS.iter (fun input -> graph := add_link input node !graph) inputs;
         let n1 = List.fold_left add_instr node then_instrs in
         let n2 = List.fold_left add_instr node else_instrs in
         incr icounter;
         let join = G_instr (!icounter, icomment "join") in
         graph := add_link n1 join !graph;
         graph := add_link n2 join !graph;
         join
       end
    | I_goto label ->
       begin
         let _, outputs = instr_deps instr in
         graph := add_link last_instr node !graph;
         NS.iter (fun output -> graph := add_link node output !graph) outputs;
         incr icounter;
         G_instr (!icounter, icomment "after goto")
       end
    | _ ->
       begin
         let inputs, outputs = instr_deps instr in
         graph := add_link last_instr node !graph;
         NS.iter (fun input -> graph := add_link input node !graph) inputs;
         NS.iter (fun output -> graph := add_link node output !graph) outputs;
         node
       end
  in
  ignore (List.fold_left add_instr G_start instrs);
  fix_leaves !graph

let make_dot id graph =
  Util.opt_colors := false;
  let to_string node = String.escaped (string_of_node node) in
  let node_color = function
    | G_start                           -> "lightpink"
    | G_id _                            -> "yellow"
    | G_instr (_, I_aux (I_decl _, _))  -> "olivedrab1"
    | G_instr (_, I_aux (I_init _, _))  -> "springgreen"
    | G_instr (_, I_aux (I_clear _, _)) -> "peachpuff"
    | G_instr (_, I_aux (I_goto _, _))  -> "orange1"
    | G_instr (_, I_aux (I_label _, _)) -> "white"
    | G_instr (_, I_aux (I_raw _, _))   -> "khaki"
    | G_instr _                         -> "azure"
    | G_label _                         -> "lightpink"
  in
  let edge_color from_node to_node =
    match from_node, to_node with
    | G_start  , _         -> "goldenrod4"
    | G_label _, _         -> "darkgreen"
    | _        , G_label _ -> "goldenrod4"
    | G_instr _, G_instr _ -> "black"
    | G_id _   , G_instr _ -> "blue3"
    | G_instr _, G_id _    -> "red3"
    | _        , _         -> "coral3"
  in
  let out_chan = open_out (Util.zencode_string (string_of_id id) ^ ".gv") in
  output_string out_chan "digraph DEPS {\n";
  let make_node from_node =
    output_string out_chan (Printf.sprintf "  \"%s\" [fillcolor=%s;style=filled];\n" (to_string from_node) (node_color from_node))
  in
  let make_line from_node to_node =
    output_string out_chan (Printf.sprintf "  \"%s\" -> \"%s\" [color=%s];\n" (to_string from_node) (to_string to_node) (edge_color from_node to_node))
  in
  NM.bindings graph |> List.iter (fun (from_node, _) -> make_node from_node);
  NM.bindings graph |> List.iter (fun (from_node, to_nodes) -> NS.iter (make_line from_node) to_nodes);
  output_string out_chan "}\n";
  Util.opt_colors := true;
  close_out out_chan
