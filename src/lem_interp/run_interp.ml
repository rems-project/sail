open Printf ;;
open Interp_ast ;;
open Interp ;;

let lit_to_string = function
 | L_unit -> "unit"
 | L_zero -> "bitzero"
 | L_one -> "bitone"
 | L_true -> "true"
 | L_false -> "false"
 | L_num n -> string_of_int n
 | L_hex s -> s
 | L_bin s -> s
 | L_undef -> "undefined"
 | L_string s -> "\"" ^ s ^ "\""
;;

let id_to_string = function
  | Id s | DeIid s -> s
;;

let rec val_to_string = function
 | V_boxref n -> sprintf "boxref %d" n
 | V_lit l -> sprintf "literal %s" (lit_to_string l)
 | V_tuple l ->
     let repr = String.concat ", " (List.map val_to_string l) in
     sprintf "tuple (%s)" repr
 | V_list l ->
     let repr = String.concat "; " (List.map val_to_string l) in
     sprintf "list [%s]" repr
 | V_vector (first_index, msb, l) ->
     let order = if msb then "big-endian" else "little-endian" in
     let repr = String.concat "; " (List.map val_to_string l) in
     sprintf "vector [%s] (%s, from %d)" repr order first_index
 | V_record l ->
     let pp (id, value) = sprintf "%s = %s" (id_to_string id) (val_to_string value) in
     let repr = String.concat "; " (List.map  pp l) in
     sprintf "record {%s}" repr
 | V_ctor (id, value) ->
     sprintf "constructor %s %s" (id_to_string id) (val_to_string value)
;;

let act_to_string = function
 | Read_reg ((Reg (id, _) | SubReg (id, _, _)), None) ->
     sprintf "read_reg %s" (id_to_string id)
 | Read_reg ((Reg (id, _) | SubReg (id, _, _)), Some (n1, n2)) ->
     sprintf "read_reg %s (%d, %d)" (id_to_string id) n1 n2
 | Write_reg ((Reg (id, _) | SubReg (id, _, _)), None, value) ->
     sprintf "write_reg %s = %s" (id_to_string id) (val_to_string value)
 | Write_reg ((Reg (id, _) | SubReg (id, _, _)), Some (n1, n2), value) ->
     sprintf "write_reg %s (%d, %d) = %s" (id_to_string id) n1 n2
     (val_to_string value)
 | Read_mem (id, args, None) ->
     sprintf "read_mem %s(%s)" (id_to_string id) (val_to_string args)
 | Read_mem (id, args, Some (n1, n2)) ->
     sprintf "read_mem %s(%s) (%d, %d)" (id_to_string id) (val_to_string args) n1 n2
 | Write_mem (id, args, None, value) ->
     sprintf "write_mem %s(%s) = %s" (id_to_string id) (val_to_string args) (val_to_string value)
 | Write_mem (id, args, Some(n1, n2), value) ->
     sprintf "write_mem %s(%s) (%d, %d) = %s" (id_to_string id) (val_to_string args) n1 n2 (val_to_string value)
;;

let run (name, test) =
  let rec loop = function
  | Value v -> eprintf "%s: returned %s\n" name (val_to_string v)
  | Action (a, s) ->
      eprintf "%s: suspended on action %s\n" name (act_to_string a);
      (* XXX return unit for every action *)
      loop (resume test s (V_lit L_unit))
  | Error e -> eprintf "%s: error: %s\n" name e in
  let entry = E_app(E_id(Id "main"), [E_lit L_unit]) in
  loop (interp test entry)
;;
