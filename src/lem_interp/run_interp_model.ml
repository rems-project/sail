open Printf ;;
open Interp_ast ;;
(*open Interp ;;
open Interp_lib ;;*)
open Interp_interface ;;
open Interp_inter_imp ;;

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
  | Interp.V_lit(L_aux(L_zero, _)) -> "0"
  | Interp.V_lit(L_aux(L_one, _)) -> "1"
  | _ -> assert false) l))
;;

let val_to_string v = match v with
  | Bitvector(bools, inc, fst)-> let l = List.length bools in
    (string_of_int l) ^ " bits -- 0b" ^ collapse_leading (String.concat "" (List.map (function | true -> "1" | _ -> "0") bools))
  | Bytevector words ->
    let l = List.length words in
    (string_of_int l) ^ " bytes --" ^
      (String.concat ""
	 (List.map (fun i -> (Printf.sprintf "0x%x " i)) words))
  | Unknown0 -> "Unknown"

let reg_name_to_string = function
  | Reg0 s -> s
  | Reg_slice(s,(first,second)) -> 
    s ^ "[" ^ string_of_big_int first ^ (if (eq_big_int first second) then "" else ".." ^ (string_of_big_int second)) ^ "]"
  | Reg_field(s,f,_) -> s ^ "." ^ f
  | Reg_f_slice(s,f,_,(first,second)) -> s ^ "." ^ f ^ "]" ^ string_of_big_int first ^ (if (eq_big_int first second) then "" else ".." ^ (string_of_big_int second)) ^ "]"

let dependencies_to_string dependencies = String.concat ", " (List.map reg_name_to_string dependencies)

let rec val_to_string_internal = function
 | Interp.V_boxref(n, t) -> sprintf "boxref %d" n
 | Interp.V_lit (L_aux(l,_)) -> sprintf "%s" (lit_to_string l)
 | Interp.V_tuple l ->
     let repr = String.concat ", " (List.map val_to_string_internal l) in
     sprintf "(%s)" repr
 | Interp.V_list l ->
     let repr = String.concat "; " (List.map val_to_string_internal l) in
     sprintf "[||%s||]" repr
 | Interp.V_vector (first_index, inc, l) ->
     let last_index = add_int_big_int (if inc then List.length l - 1 else 1 - List.length l) first_index  in
     let repr =
       try bitvec_to_string (* (if inc then l else List.rev l)*) l
       with Failure _ ->
         sprintf "[%s]" (String.concat "; " (List.map val_to_string_internal l)) in
     sprintf "%s [%s..%s]" repr (string_of_big_int first_index) (string_of_big_int last_index)
 | Interp.V_record(_, l) ->
     let pp (id, value) = sprintf "%s = %s" (id_to_string id) (val_to_string_internal value) in
     let repr = String.concat "; " (List.map  pp l) in
     sprintf "{%s}" repr
 | Interp.V_ctor (id,_, value) ->
     sprintf "%s %s" (id_to_string id) (val_to_string_internal value)
 | Interp.V_register r ->
     sprintf "reg-as-value" 
 | Interp.V_unknown -> "unknown"
;;

let rec top_frame_exp = function
  | Interp.Top -> raise (Invalid_argument "top_frame_exp")
  | Interp.Hole_frame(_, e, _, _, _, Top)
  | Interp.Thunk_frame(e, _, _, _, Top) -> e
  | Interp.Thunk_frame(_, _, _, _, s)
  | Interp.Hole_frame(_, _, _, _, _, s) -> top_frame_exp s

let tunk = Unknown, None
let ldots = E_aux(E_id (Id_aux (Id "...", Unknown)), tunk)
let rec compact_exp (E_aux (e, l)) =
  let wrap e = E_aux (e, l) in
  match e with
 | E_block (e :: _) -> compact_exp e
 | E_nondet (e :: _) -> compact_exp e
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
 | E_block [] | E_nondet [] | E_cast (_, _) | E_internal_cast (_, _)
 | E_id _|E_lit _|E_vector_indexed (_, _)|E_record _|E_internal_exp _ ->
     wrap e

(* extract, compact and reverse expressions on the stack;
 * the top of the stack is the head of the returned list. *)
let rec compact_stack ?(acc=[]) = function
  | Interp.Top -> acc
  | Interp.Hole_frame(_,e,_,_,_,s)
  | Interp.Thunk_frame(e,_,_,_,s) -> compact_stack ~acc:((compact_exp e) :: acc) s
;;  

let sub_to_string = function None -> "" | Some (x, y) -> sprintf " (%s, %s)"
  (string_of_big_int x) (string_of_big_int y)
;;

module Reg = struct
  include Map.Make(struct type t = string let compare = compare end)
  let to_string id v = 
    sprintf "%s -> %s" id (val_to_string v)
  let find id m = 
(*    eprintf "reg_find called with %s\n" id;*)
    let v = find id m in
(*    eprintf "%s -> %s\n" id (val_to_string v);*)
    v
end ;;

let compare_bytes v1 v2 = 
  let rec comp v1s v2s = match (v1s,v2s) with
    | ([],[]) -> 0
    | (v1::v1s,v2::v2s) -> 
      match compare v1 v2 with
	| 0 -> comp v1s v2s
	| ans -> ans in 
  let l1 = List.length v1 in
  let l2 = List.length v2 in
  if l1 > l2 then 1
  else if l1 < l2 then -1
  else comp v1 v2

module Mem = struct
  include Map.Make(struct
    type t = word8 list
    let compare v1 v2 = compare_bytes v1 v2
  end)
  let find idx m = 
(*    eprintf "mem_find called with %s\n" (val_to_string (Bytevector idx));*)
    let v = find idx m in
(*    eprintf "mem_find found with %s |-> %i\n" (val_to_string (Bytevector idx)) v;*)
    v
  let add key valu m =
(*    eprintf "mem_add called with %s |-> %s\n" (val_to_string (Bytevector key)) (string_of_int valu);*)
    add key valu m

  let to_string loc v =
    sprintf "[%s] -> %x" (val_to_string (Bytevector loc)) v
end ;;

let rec slice bitvector (start,stop) = 
  match bitvector with
    | Bitvector(bools, inc, fst) -> 
      Bitvector ((Interp.from_n_to_n (if inc then (sub_big_int start fst) else (sub_big_int fst start))
                                    (if inc then (sub_big_int stop fst) else (sub_big_int fst stop)) bools),
                 inc,
                 (if inc then zero_big_int else (add_big_int (sub_big_int stop start) unit_big_int)))
                
    | Bytevector bytes -> 
      Bytevector((Interp.from_n_to_n start stop bytes)) (*This is wrong, need to explode and re-encode, but maybe never happens?*)
    | Unknown0 -> Unknown0
;;

let rec list_update index start stop e vals =  
 match vals with
    | []      -> []
    | x :: xs -> 
      if eq_big_int index stop 
      then e :: xs 
      else if ge_big_int index start
      then e :: (list_update (add_big_int index unit_big_int) start stop e xs)
      else x :: (list_update (add_big_int index unit_big_int) start stop e xs)
;;

let rec list_update_list index start stop es vals =
  match vals with
  | [] -> []
  | x :: xs ->
    match es with
    | [] -> xs
    | e::es ->
      if eq_big_int index stop
      then e::xs
      else if ge_big_int index start
      then e :: (list_update_list (add_big_int index unit_big_int) start stop es xs)
      else x :: (list_update_list (add_big_int index unit_big_int) start stop (e::es) xs)
;;

let fupdate_slice original e (start,stop) =
  match original with
    | Bitvector(bools,inc,fst) -> 
      (match e with 
      | Bitvector ([b],_,_) -> 
        Bitvector((list_update zero_big_int 
                               (if inc then (sub_big_int start fst) else (sub_big_int fst start))
                               (if inc then (sub_big_int stop fst) else (sub_big_int fst stop)) b bools), inc, fst)
      | Bitvector(bs,_,_) -> 
        Bitvector((list_update_list zero_big_int 
                                    (if inc then (sub_big_int start fst) else (sub_big_int fst start))
                                    (if inc then (sub_big_int stop fst) else (sub_big_int fst stop)) bs bools), inc, fst)
      | _ -> Unknown0)
    | Bytevector bytes -> (*Can this happen?*)
      (match e with
      | Bytevector [byte] -> 
        Bytevector (list_update zero_big_int start stop byte bytes)
      | Bytevector bs ->
        Bytevector (list_update_list zero_big_int start stop bs bytes)
      | _ -> Unknown0)
    | Unknown0 -> Unknown0
;;

let combine_slices (start, stop) (inner_start,inner_stop) = (add_big_int start inner_start, add_big_int start inner_stop)

let increment bytes = 
  let adder byte (carry_out, bytes) = 
    let new_byte = carry_out + byte in 
    if new_byte > 255 then (1,0::bytes) else (0,new_byte::bytes)
  in (snd (List.fold_right adder bytes (1,[])))
;;
let unit_lit = (L_aux(L_unit,Interp_ast.Unknown))

let rec format_events = function
  | [] -> 
    "     Done\n"
  | [E_error s] -> 
    "     Failed with message : " ^ s ^ "\n"
  | (E_error s)::events ->
    "     Failed with message : " ^ s ^ " but continued on erroneously\n"
  | (E_read_mem(read_kind, location, length, tracking))::events ->
    "     Read_mem at " ^ (val_to_string location) ^ " for " ^ (string_of_big_int length) ^ " bytes \n" ^
    (format_events events)
  | (E_write_mem(write_kind,location, length, tracking, value, v_tracking))::events ->
    "     Write_mem at " ^ (val_to_string location) ^ " writing " ^ (val_to_string value) ^ " across " ^ (string_of_big_int length) ^ " bytes\n" ^
    (format_events events)
  | ((E_barrier b_kind)::events) ->
    "     Memory_barrier occurred\n" ^ 
    (format_events events)
  | (E_read_reg reg_name)::events ->
    "     Read_reg of " ^ (reg_name_to_string reg_name) ^ "\n" ^
    (format_events events)
  | (E_write_reg(reg_name, value))::events ->
    "     Write_reg of " ^ (reg_name_to_string reg_name) ^ " writing " ^ (val_to_string value) ^ "\n" ^
    (format_events events)
;;

let rec perform_action ((reg, mem) as env) = function
 (* registers *)
 | Read_reg0((Reg0 id), _) -> (Some(Reg.find id reg), env)
 | Read_reg0(Reg_slice(id, range), _)
 | Read_reg0(Reg_field(id, _, range), _) -> (Some(slice (Reg.find id reg) range), env)
 | Read_reg0(Reg_f_slice(id, _, range, mini_range), _) ->
   (Some(slice (slice (Reg.find id reg) range) mini_range),env)
 | Write_reg0(Reg0 id, value, _) -> (None, (Reg.add id value reg,mem))
 | Write_reg0(Reg_slice(id,range),value, _) 
 | Write_reg0(Reg_field(id,_,range),value,_)->
     let old_val = Reg.find id reg in
     let new_val = fupdate_slice old_val value range in
     (None, (Reg.add id new_val reg, mem))
 | Write_reg0(Reg_f_slice(id,_,range,mini_range),value,_) ->
   let old_val = Reg.find id reg in
   let new_val = fupdate_slice old_val value (combine_slices range mini_range) in
   (None,(Reg.add id new_val reg,mem))
 | Read_mem0(_,(Bytevector location), length, _,_) ->
   let rec reading location length = 
     if eq_big_int length zero_big_int 
     then []
     else (Mem.find location mem)::(reading (increment location) (sub_big_int length unit_big_int)) in
   (Some (Bytevector((List.rev (reading location length)))), env)
 | Write_mem0(_,(Bytevector location), length, _, (Bytevector bytes),_,_) ->
   let rec writing location length bytes mem = 
     if eq_big_int length zero_big_int
     then mem
     else match bytes with
       | [] -> mem
       | b::bytes -> 
	 writing (increment location) (sub_big_int length unit_big_int) bytes (Mem.add location b mem) in
   (None,(reg,writing location length bytes mem))
 | _ -> (None, env)
;;

let debug = ref true
let debugf : ('a, out_channel, unit) format -> 'a = function f -> if !debug then eprintf f else ifprintf stderr f

type interactive_mode = Step | Run | Next

let mode_to_string = function
  | Step -> "step"
  | Run -> "run"
  | Next -> "next"

(* ANSI/VT100 colors *)
let disable_color = ref false
let color bright code s =
  if !disable_color then s
  else sprintf "\x1b[%s3%dm%s\x1b[m" (if bright then "1;" else "") code s
let red = color true 1
let green = color false 2
let yellow = color true 3
let blue = color true 4
let grey = color false 7

let run
  ?(main_func = "main")
  ?(parameters = [])
  ?(reg=Reg.empty)
  ?(mem=Mem.empty)
  ?(eager_eval=true)
  ?(track_dependencies= ref false)
  ?mode
  (name, spec) =
  let get_loc (E_aux(_, (l, _))) = loc_to_string l in
  let print_exp  e =
    debugf "%s: %s\n" (get_loc e) (Pretty_interp.pp_exp e) in
  (* interactive loop for step-by-step execution *)
  let usage = "Usage:
    step    go to next action [default]
    next    go to next break point
    run     complete current execution
    track   begin/end tracking register dependencies
    bt      print call stack
    cont    print continuation of the top stack frame
    reg     print content of environment
    mem     print content of memory
    exh     run interpreter exhaustively with unknown and print events 
    quit    exit interpreter" in
  let rec interact mode ((reg, mem) as env) stack =
    flush_all();
    let command = Pervasives.read_line () in
    let command' = if command = "" then mode_to_string mode else command in
    begin match command' with
    | "s" | "step" -> Step
    | "n" | "next" -> Next
    | "r" | "run" -> Run
    | "rg" | "reg" | "registers" ->
        Reg.iter (fun k v -> debugf "%s\n" (Reg.to_string k v)) reg;
        interact mode env stack
    | "m" | "mem" | "memory" ->
        Mem.iter (fun k v -> debugf "%s\n" (Mem.to_string k v)) mem;
        interact mode env stack
    | "bt" | "backtrace" | "stack" ->
        List.iter print_exp (compact_stack stack);
        interact mode env stack
    | "e" | "exh" | "exhaust" ->
      debugf "interpreting exhaustively from current state\n";
      let events = interp_exhaustive stack in
      debugf "%s" (format_events events);
      interact mode env stack
    | "c" | "cont" | "continuation" ->
        (* print not-compacted continuation *)
        print_exp (top_frame_exp stack);
        interact mode env stack
    | "track" | "t" ->
      track_dependencies := not(!track_dependencies);
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
  let show act lhs arrow rhs = debugf "%s: %s %s %s\n"
    (green act) lhs (blue arrow) rhs in
  let left = "<-" and right = "->" in
  let rec loop mode env = function
  | Done ->
    debugf "%s: %s\n" (grey name) (blue "done");
    (true, mode, !track_dependencies, env)
  | Error0 s -> 
    debugf "%s: %s: %s\n" (grey name) (red "error") s;
    (false, mode, !track_dependencies, env) 
  | action ->
    let step ?(force=false) stack =
      let top_exp = top_frame_exp stack in
      let loc = get_loc (compact_exp top_exp) in
      if mode = Step || force then begin
        debugf "%s\n" (Pretty_interp.pp_exp top_exp);
        interact mode env stack
      end else
        mode in
    let (return,env') = perform_action env action in
    let (mode', env', next) =
      match action with    
	| Read_reg0(reg,next_thunk) ->
	  (match return with
	    | Some(value) -> 
	      show "read_reg" (reg_name_to_string reg) right (val_to_string value);
	      let next = next_thunk value in
	      (step next, env', next)
	    | None -> assert false)
	| Write_reg0(reg,value,next) ->
	  show "write_reg" (reg_name_to_string reg) left (val_to_string value);
	  (step next, env', next)
	| Read_mem0(kind, location, length, tracking, next_thunk) ->
	  (match return with
	    | Some(value) -> 
	      show "read_mem" (val_to_string location) right (val_to_string value);
              (match tracking with
              | None -> ()
              | Some(deps) ->
                show "read_mem address depended on" (dependencies_to_string deps) "" "");
	      let next = next_thunk value in
	      (step next, env', next)
	    | None -> assert false)
	| Write_mem0(kind,location, length, tracking, value, v_tracking, next_thunk) ->
	  show "write_mem" (val_to_string location) left (val_to_string value);
          (match (tracking,v_tracking) with
          | (None,None) -> ();
          | (Some(deps),None) ->
            show "write_mem address depended on" (dependencies_to_string deps) "" "";
          | (None,Some(deps)) ->
            show "write_mem value depended on" (dependencies_to_string deps) "" "";
          | (Some(deps),Some(vdeps)) ->
            show "write_mem address depended on" (dependencies_to_string deps) "" "";
            show "write_mem value depended on" (dependencies_to_string vdeps) "" "";);
	  let next = next_thunk true in
	  (step next,env',next)
	| Barrier0(bkind,next) ->
	  show "mem_barrier" "" "" "";
	  (step next, env, next)
	| Internal(None,None, next) ->
          show "breakpoint" "" "" "";
          (step ~force:true next,env',next)
        | Internal((Some fn),None,next) ->
          show "breakpoint" fn "" "";
          (step ~force:true next, env',next)
        | Internal((Some fn),(Some vdisp),next) ->
          show "breakpoint" (fn ^ " " ^ (vdisp ())) "" "";
          (step ~force:true next, env', next)
	| Nondet_choice(nondets, next) ->
	  let choose_order = List.sort (fun (_,i1) (_,i2) -> compare i1 i2) 
	    (List.combine nondets (List.map (fun _ -> Random.bits ()) nondets)) in
	  show "nondeterministic evaluation begun" "" "" "";
	  let (_,_,_,env') = List.fold_right (fun (next,_) (_,_,_,env') -> 
	    loop mode env' (interp0 (make_mode (mode=Run) !track_dependencies) next)) choose_order (false,mode,!track_dependencies,env'); in
	  show "nondeterministic evaluation ended" "" "" "";
	  (step next,env',next)
(*      | Exit e ->
	show "exiting current evaluation" "" "" "";
	step (),env', (set_in_context s e)*)
      in
      loop mode' env' (interp0 (make_mode (mode' = Run) !track_dependencies) next) in
  let mode = match mode with
  | None -> if eager_eval then Run else Step
  | Some m -> m in
  let context = build_context spec in
  let initial_state = initial_instruction_state context main_func parameters in
  let imode = make_mode eager_eval !track_dependencies in
  let top_exp = top_frame_exp initial_state in
  debugf "%s: %s %s\n" (grey name) (blue "evaluate") (Pretty_interp.pp_exp top_exp);
  try
    Printexc.record_backtrace true;
    loop mode (reg, mem) (interp0 imode initial_state)
  with e ->
    let trace = Printexc.get_backtrace () in
    debugf "%s: %s %s\n%s\n" (grey name) (red "interpretor error") (Printexc.to_string e) trace;
    (false, mode, !track_dependencies, (reg, mem))
;;
