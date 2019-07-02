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
open Jib
open Jib_util
open Value2

module StringMap = Map.Make(String)

type global_state = {
    functions : (calling_convention * id list * instr array * int StringMap.t) Bindings.t;
  }

let empty_global_state = {
    functions = Bindings.empty
  }

let rec make_jump_table n jt = function
  | I_aux (I_label label, _) :: instrs ->
     make_jump_table (n + 1) (StringMap.add label n jt) instrs
  | _ :: instrs ->
     make_jump_table (n + 1) jt instrs
  | [] -> jt

let initialize_global_state cdefs =
  let rec init gstate = function
    | CDEF_fundef (id, cc, args, instrs) :: defs ->
       let instrs = Jib_optimize.flatten_instrs instrs in
       let jump_table = make_jump_table 0 StringMap.empty instrs in
       init { functions = Bindings.add id (cc, args, Array.of_list instrs, jump_table) gstate.functions } defs
    | _ :: defs ->
       init gstate defs
    | [] -> gstate
  in
  init empty_global_state cdefs

module IntMap = Map.Make(struct type t = int let compare = compare end)

type stack = {
    pc: int;
    locals: vl NameMap.t;
    match_state: (int * string) list IntMap.t;
    current_cc: calling_convention;
    instrs: instr array;
    jump_table: int StringMap.t;
    calls: string list;
    pop: (vl option -> stack) option
  }

let initialize_stack instrs = {
    pc = 0;
    locals = NameMap.empty;
    match_state = IntMap.empty;
    current_cc = CC_stack;
    instrs = Array.of_list instrs;
    jump_table = make_jump_table 0 StringMap.empty instrs;
    calls = [];
    pop = None
  }

let string_of_local (name, v) = Util.(string_of_name ~zencode:false name |> green |> clear) ^ " => " ^ string_of_value v

let print_stack stack =
  let banner = "====================================================" in
  print_endline ("Calls: " ^ Util.string_of_list ", " (fun x -> x) stack.calls);
  print_endline banner;
  let pc = string_of_int stack.pc ^ " -> " in
  let margin = String.make (String.length pc) ' ' in
  for i = stack.pc - 10 to stack.pc - 1 do
    if i >= 0 then
      let instr = stack.instrs.(i) in
      print_endline (margin ^ Pretty_print_sail.to_string (pp_instr instr))
    else ()
  done;
  print_endline (pc ^ Pretty_print_sail.to_string (pp_instr stack.instrs.(stack.pc)));
  for i = stack.pc + 1 to stack.pc + 10 do
    if i < Array.length stack.instrs then
      let instr = stack.instrs.(i) in
      print_endline (margin ^ Pretty_print_sail.to_string (pp_instr instr))
    else ()
  done;
  print_endline banner;
  print_endline (Util.string_of_list ", " string_of_local (NameMap.bindings stack.locals));
  if IntMap.cardinal stack.match_state > 0 then (
    print_endline Util.("matches:" |> cyan |> clear);
    List.iter (fun (uid, groups) ->
        print_endline (string_of_int uid ^ ": " ^ Util.string_of_list " " (fun (group, str) -> Printf.sprintf "(%d, \"%s\")" group str) groups)
      ) (IntMap.bindings stack.match_state)
  ) else ()

let evaluate_cval_call f vls =
  let open Sail2_operators_bitlists in
  match f, vls with
  | Bnot, [VL_bool b] -> VL_bool (not b)
  | Bor, [VL_bool a; VL_bool b] -> VL_bool (a || b)
  | Band, [VL_bool a; VL_bool b] -> VL_bool (a && b)
  | List_hd, [VL_list (v :: _)] -> v
  | List_tl, [VL_list (_ :: vs)] -> VL_list vs
  | Eq, [v1; v2] -> VL_bool (v1 = v2)
  | Neq, [v1; v2] -> VL_bool (not (v1 = v2))
  | Ilt, [VL_int x; VL_int y] -> VL_bool (x < y)
  | Ilteq, [VL_int x; VL_int y] -> VL_bool (x <= y)
  | Igt, [VL_int x; VL_int y] -> VL_bool (x > y)
  | Igteq, [VL_int x; VL_int y] -> VL_bool (x >= y)
  | Iadd, [VL_int x; VL_int y] -> VL_int (Big_int.add x y)
  | Isub, [VL_int x; VL_int y] -> VL_int (Big_int.sub x y)
  | Unsigned _, [VL_bits (bv, ord)] -> VL_int (uint bv)
  | Signed _, [VL_bits (bv, ord)] -> VL_int (sint bv)
  | Bvnot, [VL_bits (bv, ord)] -> VL_bits (not_vec bv, ord)
  | Bvand, [VL_bits (bv1, ord1); VL_bits (bv2, ord2)] when ord1 = ord2 -> VL_bits (and_vec bv1 bv2, ord1)
  | Bvor, [VL_bits (bv1, ord1); VL_bits (bv2, ord2)] when ord1 = ord2 -> VL_bits (or_vec bv1 bv2, ord1)
  | Bvxor, [VL_bits (bv1, ord1); VL_bits (bv2, ord2)] when ord1 = ord2 -> VL_bits (xor_vec bv1 bv2, ord1)
  | Bvadd, [VL_bits (bv1, ord1); VL_bits (bv2, ord2)] when ord1 = ord2 -> VL_bits (add_vec bv1 bv2, ord1)
  | Bvsub, [VL_bits (bv1, ord1); VL_bits (bv2, ord2)] when ord1 = ord2 -> VL_bits (sub_vec bv1 bv2, ord1)
  | Concat, [VL_bits (bv1, ord1); VL_bits (bv2, ord2)] when ord1 = ord2 -> VL_bits (concat_vec bv1 bv2, ord1)
  | Zero_extend n, [VL_bits (bv, ord)] -> VL_bits (extz_vec (Big_int.of_int n) bv, ord)
  | Sign_extend n, [VL_bits (bv, ord)] -> VL_bits (exts_vec (Big_int.of_int n) bv, ord)
  | Bit_to_bool, [VL_bit Sail2_values.B0] -> VL_bool false
  | Bit_to_bool, [VL_bit Sail2_values.B1] -> VL_bool false
  | _ -> failwith ("Unsupported cval operator " ^ string_of_op f)

(** [evaluate_cval locals cval] takes a NameMap.t of local variable
   bindings and reduces a cval to a single value. It returns None if
   there is a variable (V_id node) in the cval that does not appear in
   the local variable bindings. It raises [Failure msg] if the cval is
   badly formed. *)
let rec evaluate_cval locals = function
  | V_id (Have_exception _, _) -> Some (VL_bool false)
  | V_id (name, _) ->
     begin match NameMap.find_opt name locals with
     | Some vl -> Some vl
     | None -> None
     end
  | V_call (f, vls) ->
     Util.option_all (List.map (evaluate_cval locals) vls)
     |> Util.option_map (evaluate_cval_call f)
  | V_lit (vl, _) -> Some vl
  | V_ctor_kind (cval, kind, [], _) ->
     begin match evaluate_cval locals cval with
     | Some (VL_constructor (ctor, _)) -> Some (VL_bool (ctor <> string_of_id kind)) 
     | Some _ -> failwith ("Bad ctor_kind call on " ^ string_of_cval cval)
     | None -> None
     end
  | V_ctor_kind (cval, kind, unifiers, _) ->
     begin match evaluate_cval locals cval with
     | Some (VL_constructor (ctor, _)) -> Some (VL_bool (ctor <> (string_of_id kind ^ "_" ^ Util.string_of_list "_" string_of_ctyp unifiers)))
     | Some _ -> failwith "Bad ctor_kind call"
     | None -> None
     end
  | V_ctor_unwrap (_, cval, _, _) ->
     begin match evaluate_cval locals cval with
     | Some (VL_constructor (_, value)) -> Some value
     | Some _  -> failwith ("Bad ctor_unwrap call on " ^ string_of_cval cval)
     | None -> None
     end
  | V_tuple_member (cval, _, n) ->
     begin match evaluate_cval locals cval with
     | Some (VL_tuple vs) -> Some (List.nth vs n)
     | Some _ -> failwith "Bad tuple_member call"
     | None -> None
     end
  | V_field (cval, field) ->
     begin match evaluate_cval locals cval with
     | Some (VL_struct fields as struct_vl)->
        begin match List.assoc_opt field fields with
        | Some vl -> Some vl
        | None -> None
                    (* failwith (Printf.sprintf "Field %s does not exist in struct %s with fields %s"
                              field (string_of_cval cval) (string_of_value struct_vl)) *)
        end
     | Some _ -> failwith "Bad field access on non-struct cval"
     | None -> None
     end
  | V_struct (fields, _) ->
     let evaluate_field (field, cval) =
       match evaluate_cval locals cval with
       | Some vl -> Some (string_of_id field, vl)
       | None -> None
     in
     Some (VL_struct (Util.option_these (List.map evaluate_field fields)))
  | cval -> failwith ("Unsupported cval " ^ string_of_cval cval)

let eval_special name args stack =
  match name, args with
  | "sail_regmatch", [VL_string regex; VL_string input; VL_matcher (n, uid)] ->
     let regex = Str.regexp_case_fold regex in
     if Str.string_match regex input 0 then (
       let groups = List.init n (fun i -> (i + 1, Str.matched_group (i + 1) input)) in
       VL_bool true, { stack with match_state = IntMap.add uid groups stack.match_state }
     ) else (
       VL_bool false, stack
     )
  | "sail_regmatch0", [VL_string regex; VL_string input] ->
     let regex = Str.regexp_case_fold regex in
     if Str.string_match regex input 0 then (
       VL_bool true, stack
     ) else (
       VL_bool false, stack
     )
  | "sail_getmatch", [VL_string _ (* input *); VL_matcher (n, uid); VL_int m] ->
     let groups = IntMap.find uid stack.match_state in
     VL_string (List.assoc (Big_int.to_int m) groups), stack
  | "internal_cons", [v; VL_list vs] ->
     VL_list (v :: vs), stack
  | _ ->
     failwith ("Unknown extern call " ^ name)

type step =
  | Step of stack
  | Done of vl

let global_unique_number = ref (-1)

let unique_number () =
  incr global_unique_number;
  !global_unique_number

let rec declaration = function
  | CT_lint -> VL_int Big_int.zero
  | CT_fint _ -> VL_int Big_int.zero
  | CT_constant n -> VL_int n
  | CT_lbits ord -> VL_bits ([], ord)
  | CT_sbits (_, ord) -> VL_bits ([], ord)
  | CT_fbits (n, ord) -> VL_bits (List.init n (fun _ -> Sail2_values.B0), ord)
  | CT_unit -> VL_unit
  | CT_bool -> VL_bool false
  | CT_bit -> VL_bit Sail2_values.B0
  | CT_string -> VL_string ""
  | CT_real -> VL_real "0.0"
  | CT_tup ctyps -> VL_tuple (List.map declaration ctyps)
  | CT_match n -> VL_matcher (n, unique_number ())
  | CT_list _ -> VL_list []
  | CT_variant (_, fields) ->
     begin match fields with
     | (ctor, ctyp) :: _ -> VL_constructor (string_of_id ctor, declaration ctyp)
     | _ -> failwith "Empty union type"
     end
  | CT_enum (_, elements) ->
     begin match elements with
     | elem :: _ -> VL_enum (string_of_id elem)
     | _ -> failwith "Empty enum type"
     end
  | CT_struct (_, fields) ->
     VL_struct (List.map (fun (id, ctyp) -> string_of_id id, declaration ctyp) fields)
  | ctyp -> failwith (" declaration " ^ string_of_ctyp ctyp)

let set_tuple tup n v =
  match tup with
  | VL_tuple vs -> VL_tuple (Util.take n vs @ [v] @ Util.drop (n + 1) vs)
  | _ -> failwith "Non tuple passed to set_tuple"

let set_struct s field v =
  match s with
  | VL_struct fields -> VL_struct ((field, v) :: List.remove_assoc field fields)
  | _ -> failwith "Non struct passed to set_struct"

let assignment clexp v stack =
  match clexp with
  | CL_id (id, _) -> { stack with locals = NameMap.add id v stack.locals }
  | CL_tuple (CL_id (id, ctyp), n) ->
     let tup = match NameMap.find_opt id stack.locals with
       | Some v -> v
       | None -> declaration ctyp
     in
     { stack with locals = NameMap.add id (set_tuple tup n v) stack.locals }
  | _ -> failwith "Unhandled c-lexp"

let do_return stack v =
  match stack.pop with
  | Some f -> Step (f v)
  | None ->
     match v with
     | Some v -> Done v
     | None -> failwith "Bad return"

let step env global_state stack =
  let pc = stack.pc in
  match stack.instrs.(pc) with
  | I_aux (I_decl (ctyp, id), _) ->
     Step { stack with locals = NameMap.add id (declaration ctyp) stack.locals; pc = pc + 1 }

  | I_aux (I_clear (ctyp, id), _) ->
     Step { stack with locals = NameMap.remove id stack.locals; pc = pc + 1 }

  | I_aux (I_init (ctyp, id, cval), _) ->
     begin match evaluate_cval stack.locals cval with
     | Some v ->
        Step { stack with locals = NameMap.add id v stack.locals; pc = pc + 1 }
     | None ->
        failwith ("cval " ^ string_of_cval cval ^ " contains an unbound identifier")
     end

  | I_aux (I_jump (cval, label), _) ->
     let v = evaluate_cval stack.locals cval in
     begin match v with
     | Some (VL_bool true) ->
        Step { stack with pc = StringMap.find label stack.jump_table }
     | Some (VL_bool false) ->
        Step { stack with pc = pc + 1 }
     | _ -> failwith "Jump argument did not evaluate to boolean"
     end

  | I_aux (I_funcall (clexp, is_special, id, args), _) ->
     let args = Util.option_all (List.map (evaluate_cval stack.locals) args) in
     begin match args, Bindings.find_opt id global_state.functions, is_special with
     (* id is a special IR function *)
     | Some args, _, true ->
        let v, stack' = eval_special (string_of_id id) args stack in
        Step { (assignment clexp v stack') with pc = pc + 1 }
     (* id is a function defined in Jib IR *)
     | Some args, Some (cc, params, body, jump_table), false ->
        let function_return = function
          | Some v ->
             { (assignment clexp v stack) with pc = pc + 1 }
          | None -> failwith "Bad function return"
        in
        Step {
          pc = 0;
          locals = List.fold_left2 (fun locals param arg -> NameMap.add (name param) arg locals) NameMap.empty params args;
          match_state = IntMap.empty;
          current_cc = cc;
          instrs = body;
          jump_table = jump_table;
          calls = string_of_id id :: stack.calls;
          pop = Some function_return
          }
     (* id is an external function call, or a constructor *)
     | Some args, None, false ->
        let open Type_check in
        if Env.is_extern id env "c" then
          let extern = Env.get_extern id env "c" in
          match primops extern args with
          | Some result -> Step { (assignment clexp result stack) with pc = pc + 1 }
          | None -> failwith ("primitive operation " ^ extern ^ "(" ^ Util.string_of_list ", " string_of_value args ^ ") failed")
        else if List.length args = 1 then
          let ctor = VL_constructor (string_of_id id, List.nth args 0) in
          Step { (assignment clexp ctor stack) with pc = pc + 1 }
        else
          failwith ("Malformed function call " ^ string_of_id id)
     | None, _, _ ->
        failwith "Function arguments could not be evaluated"
     end

  | I_aux (I_mapcall (clexp, id, args, label), _) ->
     let args = Util.option_all (List.map (evaluate_cval stack.locals) args) in
     begin match args with
     | Some args ->
        let cc, params, body, jump_table = Bindings.find id global_state.functions in
        let mapping_return = function
          | Some v ->
             { (assignment clexp v stack) with pc = pc + 1 }
          | None ->
             { stack with pc = StringMap.find label stack.jump_table }
        in
        Step {
          pc = 0;
          locals = List.fold_left2 (fun locals param arg -> NameMap.add (name param) arg locals) NameMap.empty params args;
          match_state = IntMap.empty;
          current_cc = cc;
          instrs = body;
          jump_table = jump_table;
          calls = string_of_id id :: stack.calls;
          pop = Some mapping_return
        }
     | None ->
        failwith "Mapping arguments could not be evaluated"
     end

  (* If we hit an I_return, we must be in a mapping*)
  | I_aux (I_return _, _) ->
     begin match NameMap.find_opt return stack.locals with
     | Some return_value -> do_return stack (Some return_value)
     | None -> do_return stack None
     end

  | I_aux (I_end name, _) ->
     begin match NameMap.find_opt name stack.locals with
     | Some return_value -> do_return stack (Some return_value)
     | None -> failwith "Local variable not defined in I_end"
     end

  | I_aux (I_goto label, _) ->
     Step { stack with pc = StringMap.find label stack.jump_table }

  | I_aux (I_match_failure, _) -> failwith "Pattern match failure"

  | I_aux (I_copy (clexp, cval), _) ->
     begin match evaluate_cval stack.locals cval with
     | Some v -> Step { (assignment clexp v stack) with pc = pc + 1 }
     | None -> failwith ("Cound not evaluate cval " ^ string_of_cval cval)
     end
       
  | I_aux (I_label _, _) ->
     Step { stack with pc = pc + 1 }

  | instr -> failwith ("Unimplemented instruction: " ^ Pretty_print_sail.to_string (pp_instr instr))
