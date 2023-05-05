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

open Printf
open Interp_ast
open Sail_impl_base
open Interp_interface
open Interp_inter_imp

open Printing_functions
open Nat_big_num

module Reg = struct
  include Map.Make (struct
    type t = string
    let compare = String.compare
  end)
  let to_string id v = sprintf "%s -> %s" id (register_value_to_string v)
  let find id m =
    (*    eprintf "reg_find called with %s\n" id; *)
    let v = find id m in
    (*    eprintf "%s -> %s\n" id (val_to_string v);*)
    v
end

let compare_addresses (Address_lifted (v1, n1)) (Address_lifted (v2, n2)) =
  let rec comp v1s v2s =
    match (v1s, v2s) with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | v1 :: v1s, v2 :: v2s -> (
        match Pervasives.compare v1 v2 with 0 -> comp v1s v2s | ans -> ans
      )
  in
  match (n1, n2) with
  | Some n1, Some n2 -> compare n1 n2
  | _ ->
      let l1 = List.length v1 in
      let l2 = List.length v2 in
      if l1 > l2 then 1 else if l1 < l2 then -1 else comp v1 v2

let default_endian = ref E_big_endian
let default_order = ref D_increasing

module Mem = struct
  include Map.Make (struct
    type t = num
    let compare v1 v2 = compare v1 v2
  end)
  let find idx m = if mem idx m then find idx m else List.hd (memory_value_undef 1)

  let to_string loc v = sprintf "[%s] -> %s" (to_string loc) (memory_value_to_string !default_endian [v])
end

let slice register_vector (start, stop) =
  if register_vector.rv_dir = D_increasing then slice_reg_value register_vector start stop
  else (
    (*Interface turns start and stop into forms for
      increasing because ppcmem only speaks increasing, so here we turn it back *)
    let startd = register_vector.rv_start_internal - start in
    let stopd = startd - (stop - start) in
    (*    let _ = Printf.eprintf "slice decreasing with %i, %i, %i\n" startd stopd register_vector.rv_start in*)
    slice_reg_value register_vector start stop
  )

let big_num_unit = of_int 1

let rec list_update index start stop e vals =
  match vals with
  | [] -> []
  | x :: xs ->
      if Nat_big_num.equal index stop then e :: xs
      else if Nat_big_num.greater_equal index start then
        e :: list_update (Nat_big_num.add index big_num_unit) start stop e xs
      else x :: list_update (Nat_big_num.add index big_num_unit) start stop e xs

let rec list_update_list index start stop es vals =
  match vals with
  | [] -> []
  | x :: xs -> (
      match es with
      | [] -> xs
      | e :: es ->
          if Nat_big_num.equal index stop then e :: xs
          else if Nat_big_num.greater_equal index start then
            e :: list_update_list (Nat_big_num.add index big_num_unit) start stop es xs
          else x :: list_update_list (Nat_big_num.add index big_num_unit) start stop (e :: es) xs
    )

let fupdate_slice reg_name original e (start, stop) =
  if original.rv_dir = D_increasing then update_reg_value_slice reg_name original start stop e
  else (
    (*Interface turns start and stop into forms for
      increasing because ppcmem only speaks increasing, so here we turn it back *)
    let startd = original.rv_start_internal - start in
    let stopd = startd - (stop - start) in
    (*    let _ = Printf.eprintf "fupdate_slice: starts at %i, %i ->  %i,%i ->  %i\n" original.rv_start_internal start startd  stop stopd in *)
    update_reg_value_slice reg_name original startd stopd e
  )

let combine_slices (start, stop) (inner_start, inner_stop) = (start + inner_start, start + inner_stop)

let unit_lit = L_aux (L_unit, Interp_ast.Unknown)

let align_addr addr size = sub addr (modulus addr size)

let rec perform_action (((reg, mem, tagmem) as env), cap_size) = function
  (* registers *)
  | Read_reg1 (Reg (id, _, _, _), _) -> (Some (Reg.find id reg), env)
  | Read_reg1 (Reg_slice (id, _, _, range), _) | Read_reg1 (Reg_field (id, _, _, _, range), _) ->
      (Some (slice (Reg.find id reg) range), env)
  | Read_reg1 (Reg_f_slice (id, _, _, _, range, mini_range), _) ->
      (Some (slice (slice (Reg.find id reg) range) mini_range), env)
  | Write_reg1 (Reg (id, _, _, _), value, _) -> (None, (Reg.add id value reg, mem, tagmem))
  | Write_reg1 ((Reg_slice (id, _, _, range) as reg_n), value, _)
  | Write_reg1 ((Reg_field (id, _, _, _, range) as reg_n), value, _) ->
      let old_val = Reg.find id reg in
      let new_val = fupdate_slice reg_n old_val value range in
      (None, (Reg.add id new_val reg, mem, tagmem))
  | Write_reg1 ((Reg_f_slice (id, _, _, _, range, mini_range) as reg_n), value, _) ->
      let old_val = Reg.find id reg in
      let new_val = fupdate_slice reg_n old_val value (combine_slices range mini_range) in
      (None, (Reg.add id new_val reg, mem, tagmem))
  | Read_mem1 (kind, location, length, _, _) ->
      let address =
        match address_of_address_lifted location with
        | Some a -> a
        | None -> assert false (*TODO remember how to report an error *)
      in
      let naddress = integer_of_address address in
      let rec reading (n : num) length =
        if length = 0 then [] else Mem.find n mem :: reading (add n big_num_unit) (length - 1)
      in
      (Some (register_value_of_memory_value (reading naddress length) !default_order), env)
  | Read_mem_tagged0 (kind, location, length, _, _) ->
      let address =
        match address_of_address_lifted location with
        | Some a -> a
        | None -> assert false (*TODO remember how to report an error *)
      in
      let naddress = integer_of_address address in
      let tag = Mem.find (align_addr naddress cap_size) tagmem in
      let rec reading (n : num) length =
        if length = 0 then [] else Mem.find n mem :: reading (add n big_num_unit) (length - 1)
      in
      (Some (register_value_of_memory_value (tag :: reading naddress length) !default_order), env)
  | Write_mem0 (kind, location, length, _, bytes, _, _) ->
      let address =
        match address_of_address_lifted location with
        | Some a -> a
        | None -> assert false (*TODO remember how to report an error *)
      in
      let naddress = integer_of_address address in
      let rec writing location length bytes mem =
        if length = 0 then mem
        else (
          match bytes with
          | [] -> mem
          | b :: bytes -> writing (add location big_num_unit) (length - 1) bytes (Mem.add location b mem)
        )
      in
      (None, (reg, writing naddress length bytes mem, tagmem))
  | Write_memv1 (Some location, bytes, _, _) ->
      let address =
        match address_of_address_lifted location with Some a -> a | _ -> failwith "Write address not known"
      in
      let naddress = integer_of_address address in
      let length = List.length bytes in
      let rec writing location length bytes mem =
        if length = 0 then mem
        else (
          match bytes with
          | [] -> mem
          | b :: bytes -> writing (add location big_num_unit) (length - 1) bytes (Mem.add location b mem)
        )
      in
      (None, (reg, writing naddress length bytes mem, tagmem))
  | Write_memv_tagged0 (Some location, (tag, bytes), _, _) ->
      let address =
        match address_of_address_lifted location with Some a -> a | _ -> failwith "Write address not known"
      in
      let naddress = integer_of_address address in
      let length = List.length bytes in
      let rec writing location length bytes mem =
        if length = 0 then mem
        else (
          match bytes with
          | [] -> mem
          | b :: bytes -> writing (add location big_num_unit) (length - 1) bytes (Mem.add location b mem)
        )
      in
      let tagmem =
        Mem.add (align_addr naddress cap_size)
          (Byte_lifted [Bitl_zero; Bitl_zero; Bitl_zero; Bitl_zero; Bitl_zero; Bitl_zero; Bitl_zero; tag])
          tagmem
      in
      (None, (reg, writing naddress length bytes mem, tagmem))
  | _ -> (None, env)

let interact_print = ref true
let result_print = ref true
let error_print = ref true
let interactf : ('a, out_channel, unit) format -> 'a = function
  | f -> if !interact_print then eprintf f else ifprintf stderr f
let errorf : ('a, out_channel, unit) format -> 'a = function
  | f -> if !error_print then eprintf f else ifprintf stderr f
let resultf : ('a, out_channel, unit) format -> 'a = function
  | f -> if !result_print then eprintf f else ifprintf stderr f

type interactive_mode = Step | Run | Next

let mode_to_string = function Step -> "step" | Run -> "run" | Next -> "next"

let run (istate : instruction_state) reg mem tagmem cap_size eager_eval track_dependencies mode name =
  (* interactive loop for step-by-step execution *)
  let usage =
    "Usage:\n\
    \    step    go to next action [default]\n\
    \    next    go to next break point\n\
    \    run     complete current execution\n\
    \    track   begin/end tracking register dependencies\n\
    \    bt      print call stack\n\
    \    cont    print continuation of the top stack frame\n\
    \    reg     print content of environment\n\
    \    mem     print content of memory\n\
    \    exh     run interpreter exhaustively with unknown and print events \n\
    \    quit    exit interpreter"
  in
  let rec interact mode ((reg, mem, tagmem) as env) stack =
    flush_all ();
    let command = Pervasives.read_line () in
    let command' = if command = "" then mode_to_string mode else command in
    begin
      match command' with
      | "s" | "step" -> Step
      | "n" | "next" -> Next
      | "r" | "run" -> Run
      | "rg" | "reg" | "registers" ->
          Reg.iter (fun k v -> interactf "%s\n" (Reg.to_string k v)) reg;
          interact mode env stack
      | "m" | "mem" | "memory" ->
          Mem.iter (fun k v -> interactf "%s\n" (Mem.to_string k v)) mem;
          interact mode env stack
      | "bt" | "backtrace" | "stack" ->
          print_backtrace_compact (fun s -> interactf "%s" s) stack;
          interact mode env stack
      | "e" | "exh" | "exhaust" ->
          interactf "interpreting exhaustively from current state\n";
          let events = interp_exhaustive false None stack in
          interactf "%s" (format_events events);
          interact mode env stack
      | "c" | "cont" | "continuation" ->
          (* print not-compacted continuation *)
          print_continuation (fun s -> interactf "%s" s) stack;
          interact mode env stack
      | "track" | "t" ->
          track_dependencies := not !track_dependencies;
          interact mode env stack
      | "show_casts" ->
          Pretty_interp.ignore_casts := false;
          interact mode env stack
      | "hide_casts" ->
          Pretty_interp.ignore_casts := true;
          interact mode env stack
      | "q" | "quit" | "exit" -> exit 0
      | _ ->
          interactf "%s\n" usage;
          interact mode env stack
    end
  in
  let show act lhs arrow rhs = interactf "%s: %s %s %s\n" (green act) lhs (blue arrow) rhs in
  let left = "<-" and right = "->" in
  let rec loop mode env = function
    | Done0 ->
        interactf "%s: %s\n" (grey name) (blue "done");
        (true, mode, !track_dependencies, env)
    | Error1 s ->
        errorf "%s: %s: %s\n" (grey name) (red "error") s;
        (false, mode, !track_dependencies, env)
    | Escape0 (None, _) ->
        show "exiting current instruction" "" "" "";
        interactf "%s: %s\n" (grey name) (blue "done");
        (true, mode, !track_dependencies, env)
    | Fail1 (Some s) ->
        errorf "%s: %s: %s\n" (grey name) (red "assertion failed") s;
        (false, mode, !track_dependencies, env)
    | Fail1 None ->
        errorf "%s: %s: %s\n" (grey name) (red "assertion failed") "No message provided";
        (false, mode, !track_dependencies, env)
    | action ->
        let return, env' = perform_action (env, cap_size) action in
        let step ?(force = false) (state : instruction_state) =
          let stack = match state with IState (stack, _) -> stack in
          let top_exp, (top_env, top_mem) = top_frame_exp_state stack in
          let loc = get_loc (compact_exp top_exp) in
          if mode = Step || force then begin
            interactf "%s\n" (Pretty_interp.pp_exp top_env top_mem Printing_functions.red true top_exp);
            interact mode env' state
          end
          else mode
        in
        let mode', env', next =
          match action with
          | Read_reg1 (reg, next_thunk) -> (
              match return with
              | Some value ->
                  show "read_reg" (reg_name_to_string reg) right (register_value_to_string value);
                  let next = next_thunk value in
                  (step next, env', next)
              | None -> assert false
            )
          | Write_reg1 (reg, value, next) ->
              show "write_reg" (reg_name_to_string reg) left (register_value_to_string value);
              (step next, env', next)
          | Read_mem1 (kind, Address_lifted (location, _), length, tracking, next_thunk) -> (
              match return with
              | Some value ->
                  show "read_mem"
                    (memory_value_to_string !default_endian location)
                    right (register_value_to_string value);
                  ( match tracking with
                  | None -> ()
                  | Some deps -> show "read_mem address depended on" (dependencies_to_string deps) "" ""
                  );
                  let next = next_thunk (memory_value_of_register_value value) in
                  (step next, env', next)
              | None -> assert false
            )
          | Read_mem_tagged0 (kind, Address_lifted (location, _), length, tracking, next_thunk) -> (
              match return with
              | Some value ->
                  show "read_mem_tagged"
                    (memory_value_to_string !default_endian location)
                    right (register_value_to_string value);
                  ( match tracking with
                  | None -> ()
                  | Some deps -> show "read_mem address depended on" (dependencies_to_string deps) "" ""
                  );
                  let next =
                    match memory_value_of_register_value value with
                    | Byte_lifted tag :: bytes -> next_thunk (List.nth tag 7, bytes)
                    | _ -> assert false
                  in
                  (step next, env', next)
              | None -> assert false
            )
          | Write_mem0 (kind, Address_lifted (location, _), length, tracking, value, v_tracking, next_thunk) ->
              show "write_mem"
                (memory_value_to_string !default_endian location)
                left
                (memory_value_to_string !default_endian value);
              ( match (tracking, v_tracking) with
              | None, None -> ()
              | Some deps, None -> show "write_mem address depended on" (dependencies_to_string deps) "" ""
              | None, Some deps -> show "write_mem value depended on" (dependencies_to_string deps) "" ""
              | Some deps, Some vdeps ->
                  show "write_mem address depended on" (dependencies_to_string deps) "" "";
                  show "write_mem value depended on" (dependencies_to_string vdeps) "" ""
              );
              let next = next_thunk true in
              (step next, env', next)
          | Write_memv1 (Some (Address_lifted (location, _)), value, _, next_thunk) ->
              show "write_mem value"
                (memory_value_to_string !default_endian location)
                left
                (memory_value_to_string !default_endian value);
              let next = next_thunk true in
              (step next, env', next)
          | Write_memv_tagged0 (Some (Address_lifted (location, _)), (tag, value), _, next_thunk) ->
              show "write_mem_tagged value"
                (memory_value_to_string !default_endian location)
                left
                (memory_value_to_string !default_endian value);
              let next = next_thunk true in
              (step next, env', next)
          | Write_ea1 (_, Address_lifted (location, _), size, _, next) ->
              show "write_announce"
                (memory_value_to_string !default_endian location)
                left
                (string_of_int size ^ " bytes");
              (step next, env, next)
          | Excl_res1 next_thunk ->
              show "exclusive_result" "" "" "";
              let next = next_thunk true in
              (step next, env', next)
          | Barrier1 (bkind, next) ->
              show "mem_barrier" "" "" "";
              (step next, env, next)
          | Internal0 (None, None, next) ->
              show "stepped" "" "" "";
              (step ~force:true next, env', next)
          | Internal0 (Some fn, None, next) ->
              show "evaluated" fn "" "";
              (step ~force:true next, env', next)
          | Internal0 (None, Some vdisp, next) ->
              show "evaluated" (vdisp ()) "" "";
              (step ~force:true next, env', next)
          | Internal0 (Some fn, Some vdisp, next) ->
              show "evaluated" (fn ^ " " ^ vdisp ()) "" "";
              (step ~force:true next, env', next)
          | Nondet_choice (nondets, next) ->
              let choose_order =
                List.sort
                  (fun (_, i1) (_, i2) -> Pervasives.compare i1 i2)
                  (List.combine nondets (List.map (fun _ -> Random.bits ()) nondets))
              in
              show "nondeterministic evaluation begun" "" "" "";
              let _, _, _, env' =
                List.fold_right
                  (fun (next, _) (_, _, _, env') ->
                    loop mode env' (interp0 (make_mode (mode = Run) !track_dependencies true) next)
                  )
                  choose_order
                  (false, mode, !track_dependencies, env')
              in
              show "nondeterministic evaluation ended" "" "" "";
              (step next, env', next)
          | Analysis_non_det (possible_istates, i_state) ->
              let choose_order =
                List.sort
                  (fun (_, i1) (_, i2) -> Pervasives.compare i1 i2)
                  (List.combine possible_istates (List.map (fun _ -> Random.bits ()) possible_istates))
              in
              if possible_istates = [] then (step i_state, env', i_state)
              else begin
                show "undefined triggered a non_det" "" "" "";
                let _, _, _, env' =
                  List.fold_right
                    (fun (next, _) (_, _, _, env') ->
                      loop mode env' (interp0 (make_mode (mode = Run) !track_dependencies true) next)
                    )
                    choose_order
                    (false, mode, !track_dependencies, env')
                in
                (step i_state, env', i_state)
              end
          | Escape0 (Some e, _) ->
              show "exiting current evaluation" "" "" "";
              (step e, env', e)
          | Escape0 _ -> assert false
          | Error1 _ -> failwith "Internal error"
          | Fail1 _ -> failwith "Assertion in program failed"
          | Done0 ->
              show "done evalution" "" "" "";
              assert false
          | Footprint1 _ -> assert false
          | Write_ea1 _ -> assert false
          | Write_memv1 _ -> assert false
          (*| _ -> assert false*)
        in
        loop mode' env' (Interp_inter_imp.interp0 (make_mode (mode' = Run) !track_dependencies true) next)
  in
  let mode = match mode with None -> if eager_eval then Run else Step | Some m -> m in
  let imode = make_mode eager_eval !track_dependencies true in
  let (IState (instr_state, context)) = istate in
  let top_exp, (top_env, top_mem) = top_frame_exp_state instr_state in
  interactf "%s: %s %s\n" (grey name) (blue "evaluate")
    (Pretty_interp.pp_exp top_env top_mem Printing_functions.red true top_exp);
  try
    Printexc.record_backtrace true;
    loop mode (reg, mem, tagmem) (Interp_inter_imp.interp0 imode istate)
  with e ->
    let trace = Printexc.get_backtrace () in
    interactf "%s: %s %s\n%s\n" (grey name) (red "interpretor error") (Printexc.to_string e) trace;
    (false, mode, !track_dependencies, (reg, mem, tagmem))
