open Printf ;;
open Interp_ast ;;
open Interp ;;
open Interp_lib ;;

open Big_int ;;

let lit_to_string = function
 | L_unit -> "unit"
 | L_zero -> "0b0"
 | L_one -> "0b1"
 | L_true -> "true"
 | L_false -> "false"
 | L_num n -> string_of_big_int n
 | L_hex s -> "0x"^s
 | L_bin s -> "0b"^s
 | L_undef -> "undefined"
 | L_string s -> "\"" ^ s ^ "\""
;;

let id_to_string = function
  | Id_aux(Id s,_) | Id_aux(DeIid s,_) -> s
;;

let loc_to_string = function
  | Unknown -> "location unknown"
  | Int(s,_) -> s
  | Range(s,fline,fchar,tline,tchar) -> 
      if fline = tline
      then sprintf "%s:%d:%d" s fline fchar
      else sprintf "%s:%d:%d-%d:%d" s fline fchar tline tchar
;;

let collapse_leading s =
  if String.length s <= 8 then s else
  let first_bit = s.[0] in
  let templ = sprintf "%c...%c" first_bit first_bit in
  let regexp = Str.regexp "^\\(000000*\\|111111*\\)" in
  Str.replace_first regexp templ s
;;

let bitvec_to_string l = "0b" ^ collapse_leading (String.concat "" (List.map (function
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
 | V_lit (L_aux(l,_)) -> sprintf "%s" (lit_to_string l)
 | V_tuple l ->
     let repr = String.concat ", " (List.map val_to_string l) in
     sprintf "(%s)" repr
 | V_list l ->
     let repr = String.concat "; " (List.map val_to_string l) in
     sprintf "[||%s||]" repr
 | V_vector (first_index, inc, l) ->
     let last_index = add_int_big_int (if inc then List.length l - 1 else 1 - List.length l) first_index  in
     let repr =
       try bitvec_to_string (if inc then l else List.rev l)
       with Failure _ ->
         sprintf "[%s]" (String.concat "; " (List.map val_to_string l)) in
     sprintf "%s [%s..%s]" repr (string_of_big_int first_index) (string_of_big_int last_index)
 | V_record(_, l) ->
     let pp (id, value) = sprintf "%s = %s" (id_to_string id) (val_to_string value) in
     let repr = String.concat "; " (List.map  pp l) in
     sprintf "{%s}" repr
 | V_ctor (id,_, value) ->
     sprintf "%s %s" (id_to_string id) (val_to_string value)
 | V_register r ->
     sprintf "reg-as-value %s" (reg_to_string r)
 | V_unknown -> "unknown"
;;

let rec top_frame_exp = function
  | Top -> raise (Invalid_argument "top_frame_exp")
  | Hole_frame(_, e, _, _, _, Top)
  | Thunk_frame(e, _, _, _, Top) -> e
  | Thunk_frame(_, _, _, _, s)
  | Hole_frame(_, _, _, _, _, s) -> top_frame_exp s

let tunk = Unknown, None
let ldots = E_aux(E_id (Id_aux (Id "...", Unknown)), tunk)
let rec compact_exp (E_aux (e, l)) =
  let wrap e = E_aux (e, l) in
  match e with
 | E_block (e :: _) -> compact_exp e
 | E_if (e, _, _) ->
     wrap(E_if(compact_exp e, ldots, E_aux(E_block [], tunk)))
 | E_for (i, e1, e2, e3, o, e4) ->
    wrap(E_for(i, compact_exp e1, compact_exp e2, compact_exp e3, o, ldots))
 | E_case (e, _) ->
     wrap(E_case(compact_exp e, []))
 | E_let (bind, _) -> wrap(E_let(bind, ldots))
 | E_app (f, args) -> wrap(E_app(f, List.map compact_exp args))
 | E_app_infix (l, op, r) -> wrap(E_app_infix(compact_exp l, op, compact_exp r))
 | E_tuple exps -> wrap(E_tuple(List.map compact_exp exps))
 | E_vector exps -> wrap(E_vector(List.map compact_exp exps))
 | E_vector_access (e1, e2) ->
     wrap(E_vector_access(compact_exp e1, compact_exp e2))
 | E_vector_subrange (e1, e2, e3) ->
     wrap(E_vector_subrange(compact_exp e1, compact_exp e2, compact_exp e3))
 | E_vector_update (e1, e2, e3) ->
     wrap(E_vector_update(compact_exp e1, compact_exp e2, compact_exp e3))
 | E_vector_update_subrange (e1, e2, e3, e4) ->
     wrap(E_vector_update_subrange(compact_exp e1, compact_exp e2, compact_exp e3, compact_exp e4))
 | E_vector_append (e1, e2) ->
     wrap(E_vector_append(compact_exp e1, compact_exp e2))
 | E_list exps -> wrap(E_list(List.map compact_exp exps))
 | E_cons (e1, e2) ->
     wrap(E_cons(compact_exp e1, compact_exp e2))
 | E_record_update (e, fexps) ->
     wrap(E_record_update (compact_exp e, fexps))
 | E_field (e, id) ->
     wrap(E_field(compact_exp e, id))
 | E_assign (lexp, e) -> wrap(E_assign(lexp, compact_exp e))
 | E_block [] | E_cast (_, _) | E_internal_cast (_, _)
 | E_id _|E_lit _|E_vector_indexed (_, _)|E_record _|E_internal_exp _ ->
     wrap e

(* extract, compact and reverse expressions on the stack;
 * the top of the stack is the head of the returned list. *)
let rec compact_stack ?(acc=[]) = function
  | Top -> acc
  | Hole_frame(_,e,_,_,_,s)
  | Thunk_frame(e,_,_,_,s) -> compact_stack ~acc:((compact_exp e) :: acc) s
;;  

let sub_to_string = function None -> "" | Some (x, y) -> sprintf " (%s, %s)"
  (string_of_big_int x) (string_of_big_int y)
;;

let id_compare i1 i2 = 
  match (i1, i2) with 
    | (Id_aux(Id(i1),_),Id_aux(Id(i2),_)) 
    | (Id_aux(Id(i1),_),Id_aux(DeIid(i2),_)) 
    | (Id_aux(DeIid(i1),_),Id_aux(Id(i2),_))
    | (Id_aux(DeIid(i1),_),Id_aux(DeIid(i2),_)) -> compare i1 i2

module Reg = struct
  include Map.Make(struct type t = id let compare = id_compare end)
  let to_string id v =
    sprintf "%s -> %s" (id_to_string id) (val_to_string v)
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
  let to_string (n, idx) v =
    sprintf "%s[%s] -> %s" (id_to_string n) (string_of_big_int idx) (val_to_string v)
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

let unit_lit = V_lit (L_aux(L_unit,Interp_ast.Unknown))

let rec perform_action ((reg, mem) as env) = function
 (* registers *)
 | Read_reg (Reg (id, _), sub) ->
     slice (Reg.find id reg) sub, env
 | Write_reg (Reg (id, _), None, value) ->
     unit_lit, (Reg.add id value reg, mem)
 | Write_reg (Reg (id, _), Some (start, stop), (V_vector _ as value)) ->
     let old_val = Reg.find id reg in
     let new_val = fupdate_vector_slice old_val value start stop in
     unit_lit, (Reg.add id new_val reg, mem)
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
     unit_lit, (reg, Mem.add (id, n) value mem)
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
     in unit_lit, (reg, update zero_big_int mem)
 (* This case probably never happens in the POWER spec anyway *)
 | Write_mem (id, V_lit(L_aux(L_num n,_)), Some (start, stop), (V_vector _ as value)) ->
     let old_val = Mem.find (id, n) mem in
     let new_val = fupdate_vector_slice old_val value start stop in
     unit_lit, (reg, Mem.add (id, n) new_val mem)
 (* special case for slices of size 1: wrap value in a vector *)
 | Write_reg ((Reg (_, _) as r), (Some (start, stop) as slice), value) when eq_big_int start stop ->
     perform_action env (Write_reg (r, slice, V_vector(zero_big_int, true, [value])))
 | Write_mem (id, (V_lit(L_aux(L_num _,_)) as n), (Some (start, stop) as slice), value) when eq_big_int start stop ->
     perform_action env (Write_mem (id, n, slice, V_vector(zero_big_int, true, [value])))
 (* extern functions *)
 | Call_extern (name, arg) -> eval_external name arg, env
 | Debug l -> unit_lit, env
 | _ -> assert false
;;

let debug = ref true
let debugf : ('a, out_channel, unit) format -> 'a = function f -> if !debug then eprintf f else ifprintf stderr f

type interactive_mode = Step | Run | Next

let mode_to_string = function
  | Step -> "step"
  | Run -> "run"
  | Next -> "next"

let run
  ?(entry=E_aux(E_app(Id_aux((Id "main"),Unknown), [E_aux(E_lit (L_aux(L_unit,Unknown)),(Unknown,None))]),(Unknown,None)))
  ?(reg=Reg.empty)
  ?(mem=Mem.empty)
  ?(eager_eval=true)
  ?mode
  (name, test) =
  let get_loc (E_aux(_, (l, _))) = loc_to_string l in
  let print_exp  e =
    debugf "%s: %s\n" (get_loc e) (Pretty_interp.pp_exp e) in
  (* interactive loop for step-by-step execution *)
  let usage = "Usage:
    step    go to next action [default]
    next    go to next break point
    run     complete current execution,
    bt      print call stack
    cont    print continuation of the top stack frame
    env     print content of environment
    mem     print content of memory
    quit    exit interpreter" in
  let rec interact mode ((reg, mem) as env) stack =
    flush_all();
    let command = Pervasives.read_line () in
    let command' = if command = "" then mode_to_string mode else command in
    begin match command' with
    | "s" | "step" -> Step
    | "n" | "next" -> Next
    | "r" | "run" -> Run
    | "e" | "env" | "environment" ->
        Reg.iter (fun k v -> debugf "%s\n" (Reg.to_string k v)) reg;
        interact mode env stack
    | "m" | "mem" | "memory" ->
        Mem.iter (fun k v -> debugf "%s\n" (Mem.to_string k v)) mem;
        interact mode env stack
    | "bt" | "backtrace" | "stack" ->
        List.iter print_exp (compact_stack stack);
        interact mode env stack
    | "c" | "cont" | "continuation" ->
        (* print not-compacted continuation *)
        print_exp (top_frame_exp stack);
        interact mode env stack
    | "show_casts" ->
        Pretty_interp.ignore_casts := false;
        interact mode env stack
    | "hide_casts" ->
        Pretty_interp.ignore_casts := true;
        interact mode env stack
    | "q" | "quit" | "exit" -> exit 0
    | _ -> debugf "%s\n" usage; interact mode env stack
    end
  in
  let rec loop mode env = function
  | Value (v, _) ->
      debugf "%s: return %s\n" name (val_to_string v);
      true, mode, env
  | Action (a, s) ->
      let top_exp = top_frame_exp s in
      let loc = get_loc (compact_exp top_exp) in
      let return, env' = perform_action env a in
      let step ?(force=false) () =
        if mode = Step || force then begin
          debugf "%s\n" (Pretty_interp.pp_exp top_exp);
          interact mode env s
       end else
         mode in
      let mode' = begin match a with
      | Read_reg (reg, sub) ->
          debugf "%s: read_reg: %s%s -> %s\n"
            loc (reg_to_string reg) (sub_to_string sub) (val_to_string return);
          step ()
      | Write_reg (reg, sub, value) ->
          assert (return = unit_lit);
          debugf "%s: write_reg: %s%s <- %s\n"
            loc (reg_to_string reg) (sub_to_string sub) (val_to_string value);
          step ()
      | Read_mem (id, args, sub) ->
          debugf "%s: read_mem: %s%s%s -> %s\n"
            loc (id_to_string id) (val_to_string args) (sub_to_string sub) (val_to_string return);
          step ()
      | Write_mem (id, args, sub, value) ->
          assert (return = unit_lit);
          debugf "%s: write_mem: %s%s%s <- %s\n"
            loc (id_to_string id) (val_to_string args) (sub_to_string sub) (val_to_string value);
          step ()
      (* distinguish single argument for pretty-printing *)
      | Call_extern (f, (V_tuple _ as args)) ->
          debugf "%s: call_lib: %s%s -> %s\n"
            loc f (val_to_string args) (val_to_string return);
          step ()
      | Call_extern (f, arg) ->
          debugf "%s: call_lib: %s(%s) -> %s\n"
            loc f (val_to_string arg) (val_to_string return);
          step ()
      | Debug _ ->
          assert (return = unit_lit);
          debugf "%s: breakpoint:\n" loc;
          step ~force:true ()
      | Barrier (_, _) | Write_next_IA _ | Nondet _ ->
          failwith "unexpected action"
      end in
      loop mode' env' (resume {eager_eval = (mode' = Run)} s (Some return))
  | Error(l, e) ->
      debugf "%s: error: %s\n" (loc_to_string l) e;
      false, mode, env in
  debugf "%s: evaluate %s\n" name (Pretty_interp.pp_exp entry);
  let mode = match mode with
  | None -> if eager_eval then Run else Step
  | Some m -> m in
  try
    Printexc.record_backtrace true;
    loop mode (reg, mem) (interp {eager_eval} test entry)
  with e ->
    let trace = Printexc.get_backtrace () in
    debugf "%s: interpretor error %s\n%s\n" name (Printexc.to_string e) trace;
    false, mode, (reg, mem)
;;
