open Printf ;;
open Interp_ast ;;
open Interp ;;
open Interp_lib ;;

open Big_int ;;

let lit_to_string = function
 | L_unit -> "unit"
 | L_zero -> "bitzero"
 | L_one -> "bitone"
 | L_true -> "true"
 | L_false -> "false"
 | L_num n -> string_of_big_int n
 | L_hex s -> s
 | L_bin s -> s
 | L_undef -> "undefined"
 | L_string s -> "\"" ^ s ^ "\""
;;

let id_to_string = function
  | Id_aux(Id s,_) | Id_aux(DeIid s,_) -> s
;;

let loc_to_string = function
  | Unknown -> "Unknown"
  | Trans(s,_) -> s
  | Range(s,fline,fchar,tline,tchar) -> 
    "in " ^ s ^ " from line " ^  (string_of_int fline) ^ " character " ^ (string_of_int fchar) ^ 
      " to line " ^ (string_of_int tline) ^ " character " ^ (string_of_int tchar)
;;

let bitvec_to_string l = "0b" ^ (String.concat "" (List.rev_map (function
  | V_lit(L_aux(L_zero, _)) -> "0"
  | V_lit(L_aux(L_one, _)) -> "1"
  | _ -> assert false) l))
;;

let rec reg_to_string = function
  | Reg (id,_) -> id_to_string id
  | SubReg (id,r,_) -> sprintf "%s.%s" (reg_to_string r) (id_to_string id)
;;

let rec val_to_string = function
 | V_boxref(n, t) -> sprintf "boxref %d" n
 | V_lit (L_aux(l,_)) -> sprintf (*"literal %s" *) "%s" (lit_to_string l)
 | V_tuple l ->
     let repr = String.concat ", " (List.map val_to_string l) in
     sprintf "tuple <%s>" repr
 | V_list l ->
     let repr = String.concat "; " (List.map val_to_string l) in
     sprintf "list [%s]" repr
 | V_vector (first_index, inc, l) ->
     let order = if inc then "big-endian" else "little-endian" in
     let repr =
       try bitvec_to_string l
       with Failure _ -> String.concat "; " (List.map val_to_string l) in
     sprintf "vector [%s] (%s, from %s)" repr order (string_of_big_int first_index)
 | V_record(_, l) ->
     let pp (id, value) = sprintf "%s = %s" (id_to_string id) (val_to_string value) in
     let repr = String.concat "; " (List.map  pp l) in
     sprintf "record {%s}" repr
 | V_ctor (id,_, value) ->
     sprintf "constructor %s %s" (id_to_string id) (val_to_string value)
 | V_register r ->
     sprintf "register %s as value" (reg_to_string r)
;;

let rec env_to_string = function
  | [] -> ""
  | [id,v] -> sprintf "%s |-> %s" (id_to_string id) (val_to_string v)
  | (id,v)::env -> sprintf "%s |-> %s, %s" (id_to_string id) (val_to_string v) (env_to_string env)

let rec stack_to_string = function
  | Top -> "Top"
  | Frame(id,exp,env,mem,s) ->
    sprintf "(Frame of %s, e, (%s), m, %s)" (id_to_string id) (env_to_string env) (stack_to_string s)
;;  

let sub_to_string = function None -> "" | Some (x, y) -> sprintf " (%s, %s)"
  (string_of_big_int x) (string_of_big_int y)
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

let id_compare i1 i2 = 
  match (i1, i2) with 
    | (Id_aux(Id(i1),_),Id_aux(Id(i2),_)) 
    | (Id_aux(Id(i1),_),Id_aux(DeIid(i2),_)) 
    | (Id_aux(DeIid(i1),_),Id_aux(Id(i2),_))
    | (Id_aux(DeIid(i1),_),Id_aux(DeIid(i2),_)) -> compare i1 i2

module Reg = struct
  include Map.Make(struct type t = id let compare = id_compare end)
end ;;

module Mem = struct
  include Map.Make(struct
    type t = (id * big_int)
    let compare (i1, v1) (i2, v2) =
      (* optimize for common case: different addresses, same id *)
      match compare_big_int v1 v2 with
      | 0 -> id_compare i1 i2
      | n -> n
    end)
  (* debugging memory accesses
  let add (n, idx) v m =
    eprintf "%s[%s] <- %s\n" (id_to_string n) (string_of_big_int idx) (val_to_string v);
    add (n, idx) v m
  let find (n, idx) m =
    let v = find (n, idx) m in
    eprintf "%s[%s] -> %s\n" (id_to_string n) (string_of_big_int idx) (val_to_string v);
    v
  *)
end ;;

let vconcat v v' = vec_concat (V_tuple [v; v']) ;;

let slice v = function
  | None -> v
  | Some (n, m) -> slice_vector v n m
;;

let rec slice_ir v = function
  | BF_single n -> slice_vector v n n
  | BF_range (n, m) -> slice_vector v n m
  | BF_concat (BF_aux (ir, _), BF_aux (ir', _)) -> vconcat (slice_ir v ir) (slice_ir v ir')
;;

let rec perform_action ((reg, mem) as env) = function
 (* registers *)
 | Read_reg (Reg (id, _), sub) ->
     slice (Reg.find id reg) sub, env
 | Write_reg (Reg (id, _), None, value) ->
     V_lit (L_aux(L_unit,Interp_ast.Unknown)), (Reg.add id value reg, mem)
 | Write_reg (Reg (id, _), Some (start, stop), (V_vector _ as value)) ->
     let old_val = Reg.find id reg in
     let new_val = fupdate_vector_slice old_val value start stop in
     V_lit (L_aux(L_unit,Interp_ast.Unknown)), (Reg.add id new_val reg, mem)
 (* subregisters *)
 | Read_reg (SubReg (_, Reg (id, _), BF_aux (ir, _)), sub) ->
     slice (slice_ir (Reg.find id reg) ir) sub, env
 | Write_reg (SubReg (_, (Reg _ as r), BF_aux (ir, _)), None, value) ->
     (match ir with
     | BF_single n ->
         perform_action env (Write_reg (r, Some(n, n), value))
     | BF_range (n, m) ->
         perform_action env (Write_reg (r, Some(n, m), value))
     | BF_concat _ -> failwith "unimplemented: non-contiguous register write")
 (* memory *)
 | Read_mem (id, V_lit(L_aux((L_num n),_)), sub) ->
     slice (Mem.find (id, n) mem) sub, env
 | Write_mem (id, V_lit(L_aux(L_num n,_)), None, value) ->
     V_lit (L_aux(L_unit, Interp_ast.Unknown)), (reg, Mem.add (id, n) value mem)
 (* multi-byte accesses to memory *)
 | Read_mem (id, V_tuple [V_lit(L_aux(L_num n,_)); V_lit(L_aux(L_num size,_))], sub) ->
     let rec fetch k acc =
       if eq_big_int k size then slice acc sub else
         let slice = Mem.find (id, add_big_int n k) mem in
         fetch (succ_big_int k) (vconcat acc slice)
     in
     fetch zero_big_int (V_vector (zero_big_int, true, [])), env
 (* XXX no support for multi-byte slice write at the moment *)
 | Write_mem (id, V_tuple [V_lit(L_aux(L_num n,_)); V_lit(L_aux(L_num size,_))], None, V_vector (m, inc, vs)) ->
     (* normalize input vector so that it is indexed from 0 - for slices *)
     let value = V_vector (zero_big_int, inc, vs) in
     (* assumes smallest unit of memory is 8 bit *)
     let byte_size = 8 in
     let rec update k mem =
       if eq_big_int k size then mem else
         let n1 = mult_int_big_int byte_size k in
         let n2 = sub_big_int (mult_int_big_int byte_size (succ_big_int k)) (big_int_of_int 1) in
         let slice = slice_vector value n1 n2 in
         let mem' = Mem.add (id, add_big_int n k) slice mem in
         update (succ_big_int k) mem'
     in V_lit (L_aux(L_unit, Interp_ast.Unknown)), (reg, update zero_big_int mem)
 (* This case probably never happens in the POWER spec anyway *)
 | Write_mem (id, V_lit(L_aux(L_num n,_)), Some (start, stop), (V_vector _ as value)) ->
     let old_val = Mem.find (id, n) mem in
     let new_val = fupdate_vector_slice old_val value start stop in
     V_lit (L_aux(L_unit, Interp_ast.Unknown)), (reg, Mem.add (id, n) new_val mem)
 (* extern functions *)
 | Call_extern (name, arg) -> eval_external name arg, env
 | _ -> assert false
;;


let run
  ?(entry=E_aux(E_app(Id_aux((Id "main"),Unknown), [E_aux(E_lit (L_aux(L_unit,Unknown)),(Unknown,None))]),(Unknown,None)))
  ?(reg=Reg.empty)
  ?(mem=Mem.empty)
  (name, test) =
  let rec loop env = function
  | Value (v, _) -> eprintf "%s: returned %s\n" name (val_to_string v); true
  | Action (a, s) ->
      eprintf "%s: suspended on action %s\n" name (act_to_string a);
      (*eprintf "%s: suspended on action %s, with stack %s\n" name (act_to_string a) (stack_to_string s);*)
      let return, env' = perform_action env a in
      eprintf "%s: action returned %s\n" name (val_to_string return);
      loop env' (resume test s return)
  | Error(l, e) -> eprintf "%s: %s: error: %s\n" name (loc_to_string l) e; false in
  eprintf "%s: starting\n" name;
  try
    Printexc.record_backtrace true;
    loop (reg, mem) (interp test entry)
  with e ->
    let trace = Printexc.get_backtrace () in
    eprintf "%s: interpretor error %s\n%s\n" name (Printexc.to_string e) trace;
    false
;;
