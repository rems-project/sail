open Printf ;;
open Interp_ast ;;
open Interp_interface ;;
open Interp_inter_imp ;;

open Big_int ;;
open Printing_functions ;;

module Reg = struct
  include Map.Make(struct type t = string let compare = compare end)
  let to_string id v = 
    sprintf "%s -> %s" id (val_to_string v)
  let find id m = 
(*    eprintf "reg_find called with %s\n" id; *)
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
   (Some (Bytevector(reading location length)), env)
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

let run
  ?(main_func = "main")
  ?(parameters = [])
  ?(reg=Reg.empty)
  ?(mem=Mem.empty)
  ?(eager_eval=true)
  ?(track_dependencies= ref false)
  ?mode
  (name, spec) =
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
      print_backtrace_compact (fun s -> debugf "%s" s) stack;
      interact mode env stack
    | "e" | "exh" | "exhaust" ->
      debugf "interpreting exhaustively from current state\n";
      let events = interp_exhaustive None stack in
      debugf "%s" (format_events events);
      interact mode env stack
    | "c" | "cont" | "continuation" ->
        (* print not-compacted continuation *)
        print_continuation (fun s -> debugf "%s" s) stack;
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
