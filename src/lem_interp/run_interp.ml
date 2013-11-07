open Printf ;;
open Interp_ast ;;
open Interp ;;
open Interp_lib ;;

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

let reg_to_string = function Reg (id,_) | SubReg (id,_,_) -> id_to_string id ;;
let sub_to_string = function None -> "" | Some (x, y) -> sprintf " (%d, %d)" x y
let act_to_string = function
 | Read_reg (reg, sub) ->
     sprintf "read_reg %s%s" (reg_to_string reg) (sub_to_string sub)
 | Write_reg (reg, sub, value) ->
     sprintf "write_reg %s%s = %s" (reg_to_string reg) (sub_to_string sub)
     (val_to_string value)
 | Read_mem (id, args, sub) ->
     sprintf "read_mem %s(%s)%s" (id_to_string id) (val_to_string args)
     (sub_to_string sub)
 | Write_mem (id, args, sub, value) ->
     sprintf "write_mem %s(%s)%s = %s" (id_to_string id) (val_to_string args)
     (sub_to_string sub) (val_to_string value)
 | Call_extern (name, arg) ->
     sprintf "extern call %s applied to %s" name (val_to_string arg)
;;

module Reg = struct
  include Map.Make(struct type t = id let compare = compare end)
  let update k v m = add k v (if mem k m then remove k m else m)
end ;;

module Mem = struct
  include Map.Make(struct type t = id  * value let compare = compare end)
  let update k v m = add k v (if mem k m then remove k m else m)
end ;;

let perform_action ((reg, mem) as env) = function
 | Read_reg ((Reg (id, _) | SubReg (id, _, _)), None) ->
     Reg.find id reg, env
 | Read_mem (id, args, None) ->
     Mem.find (id, args) mem, env
 | Write_reg ((Reg (id, _) | SubReg (id, _, _)), None, value) ->
     V_lit L_unit, (Reg.update id value reg, mem)
 | Write_mem (id, args, None, value) ->
     V_lit L_unit, (reg, Mem.update (id, args) value mem)
 | Call_extern (name, arg) -> eval_external name arg, env
 | _ -> failwith "partial read/write not implemented" (* XXX *)
;;


let run (name, test) =
  let rec loop env = function
  | Value v -> eprintf "%s: returned %s\n" name (val_to_string v)
  | Action (a, s) ->
      eprintf "%s: suspended on action %s\n" name (act_to_string a);
      let return, env' = perform_action env a in
      eprintf "%s: action returned %s\n" name (val_to_string return);
      loop env' (resume test s return)
  | Error e -> eprintf "%s: error: %s\n" name e in
  let entry = E_app(E_id(Id "main"), [E_lit L_unit]) in
  loop (Reg.empty, Mem.empty) (interp test entry)
;;
