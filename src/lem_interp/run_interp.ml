open Printf ;;
open Interp_ast ;;
open Interp ;;

let val_to_string = function
 (*
 | V_boxref of nat 
 | V_lit of lit
 | V_tuple of list value
 | V_list of list value
 | V_vector of nat * bool * list value (* The nat stores the first index, the bool whether that's most or least significant *)
 | V_record of list (id * value)
 | V_ctor of id * value
 *)
 | _ -> "*** value pretty-printing not implemented ***"
;;

let act_to_string = function
 | Read_reg _ -> "read_reg"
 | Write_reg _ -> "write_reg"
 | Read_mem _ -> "read_mem"
 | Write_mem _ -> "write_mem"
;;

let run (name, test) = match interp test (E_block []) with
 | Value v -> eprintf "%s: returned %s\n" name (val_to_string v)
 | Action (a, s) -> eprintf "%s: suspended on action %s\n" name (act_to_string a)
 | Error e -> eprintf "%s: error: %s\n" name e
;;
