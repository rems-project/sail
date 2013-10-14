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
 | Read_reg _ -> "read_reg"
 | Write_reg _ -> "write_reg"
 | Read_mem _ -> "read_mem"
 | Write_mem _ -> "write_mem"
;;

let run (name, test) = match interp test (E_app(E_id(Id "main"), [E_lit L_unit])) with
 | Value v -> eprintf "%s: returned %s\n" name (val_to_string v)
 | Action (a, s) -> eprintf "%s: suspended on action %s\n" name (act_to_string a)
 | Error e -> eprintf "%s: error: %s\n" name e
;;
