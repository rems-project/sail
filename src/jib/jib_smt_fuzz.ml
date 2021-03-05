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
open Jib_smt
open Jib_util
open Smtlib

let (gensym, _) = symbol_generator "fuzz"
let ngensym () = name (gensym ())

let gen_value (Typ_aux (aux, _) as typ) =
  match aux with
  | Typ_id id when string_of_id id = "bit" ->
     Some (
         if Random.bool () then
           mk_lit_exp L_zero, V_lit (VL_bit Sail2_values.B0, CT_bit)
         else
           mk_lit_exp L_one, V_lit (VL_bit Sail2_values.B1, CT_bit)
       )

  | Typ_app (id, _) when string_of_id id = "atom_bool" ->
     Some (
         if Random.bool () then
           mk_lit_exp L_true, V_lit (VL_bool true, CT_bool)
         else
           mk_lit_exp L_false, V_lit (VL_bool false, CT_bool)
       )

  | Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_constant n, _)), _)]) when string_of_id id = "atom" ->
     Some (
         if Random.bool () then
           mk_lit_exp (L_num n), V_lit (VL_int n, CT_constant n)
         else
           let n = Big_int.of_int (Random.int 32) in
           let n = if Random.bool () then n else Big_int.negate n in
           match Random.int 3 with
           | 0 ->
              mk_lit_exp (L_num n), V_lit (VL_int n, CT_fint 64)
           | 1 ->
              mk_lit_exp (L_num n), V_lit (VL_int n, CT_lint)
           | _ ->
              mk_lit_exp (L_num n), V_lit (VL_int n, CT_constant n)
       )

  | Typ_app (id, _) when string_of_id id = "atom" ->
     Some (
         let n = Big_int.of_int (Random.int 32) in
         let n = if Random.bool () then n else Big_int.negate n in
         match Random.int 3 with
         | 0 ->
            mk_lit_exp (L_num n), V_lit (VL_int n, CT_fint 64)
         | 1 ->
            mk_lit_exp (L_num n), V_lit (VL_int n, CT_lint)
         | _ ->
            mk_lit_exp (L_num n), V_lit (VL_int n, CT_constant n)
       )

  | _ ->
     None

let rec gen_ret_ctyp (Typ_aux (aux, _)) =
  match aux with
  | Typ_id id when string_of_id id = "bool" ->
     Some CT_bool
  | Typ_app (id, _) when string_of_id id = "atom" ->
     if Random.bool () then Some (CT_fint 64) else Some CT_lint
  | Typ_app (id, _) when string_of_id id = "atom_bool" ->
     Some CT_bool
  | Typ_id id when string_of_id id = "nat" ->
     Some CT_lint
  | Typ_id id when string_of_id id = "int" ->
     Some CT_lint
  | Typ_exist (_, _, typ) ->
     gen_ret_ctyp typ
  | _ -> None

let gen_assertion ctyp value id =
  let open Smtlib in
  let open Value in
  match ctyp, value with
  | CT_bool, V_bool b ->
     [icopy Parse_ast.Unknown (CL_id (Return (-1), CT_bool)) (V_call (Eq, [V_id (id, ctyp); V_lit (VL_bool b, ctyp)]))]
  | CT_lint, V_int n ->
     [icopy Parse_ast.Unknown (CL_id (Return (-1), CT_bool)) (V_call (Eq, [V_id (id, ctyp); V_lit (VL_int n, ctyp)]))]
  | CT_fint 64, V_int n ->
     [icopy Parse_ast.Unknown (CL_id (Return (-1), CT_bool)) (V_call (Eq, [V_id (id, ctyp); V_lit (VL_int n, ctyp)]))]
  | _ ->
     assert false

let rec run frame =
  match frame with
  | Interpreter.Done (state, v) -> Some v
  | Interpreter.Step (lazy_str, _, _, _) ->
     run (Interpreter.eval_frame frame)
  | Interpreter.Break frame ->
     run (Interpreter.eval_frame frame)
  | Interpreter.Fail (_, _, _, _, msg) ->
     None
  | Interpreter.Effect_request (out, state, stack, eff) ->
     run (Interpreter.default_effect_interp state eff)

exception Skip_iteration of string;;

let fuzz_cdef ctx all_cdefs = function
  | CDEF_spec (id, _, arg_ctyps, ret_ctyp) when not (string_of_id id = "and_bool" || string_of_id id = "or_bool") ->
     let open Type_check in
     let open Interpreter in
     if Env.is_extern id ctx.tc_env "smt" then (
       let extern = Env.get_extern id ctx.tc_env "smt" in
       let typq, (Typ_aux (aux, _) as typ) = Env.get_val_spec id ctx.tc_env in
       let istate = initial_state ctx.ast ctx.tc_env !Value.primops in
       let header = smt_header ctx all_cdefs in
       prerr_endline (Util.("Fuzz: " |> cyan |> clear) ^ string_of_id id ^ " = \"" ^ extern ^ "\" : " ^ string_of_typ typ);

       match aux with
       | Typ_fn (arg_typs, ret_typ, _) ->
          let iterations = ref 0 in
          let max_iterations = 100 in
          let continue = ref true in
          let skipped = ref 0 in

          while !iterations < max_iterations && !continue do
            begin try
              begin match List.map gen_value arg_typs |> Util.option_all, gen_ret_ctyp ret_typ with
              | Some values, Some ret_ctyp ->
                 let ctx = { ctx with events = ref EventMap.empty; pragma_l = id_loc id; arg_stack = Stack.create () } in
                 let call =
                   try mk_exp (E_app (id, List.map fst values)) |> infer_exp ctx.tc_env with
                   | Type_error _ -> raise (Skip_iteration ("Type error for: " ^ Util.string_of_list ", " string_of_exp (List.map fst values)))
                 in
                 let result =
                   match run (Step (lazy "", istate, return call, [])) with
                   | Some v -> v
                   | None ->
                      raise (Skip_iteration ("Interpreter error for: " ^ Util.string_of_list ", " string_of_exp (List.map fst values)))
                 in

                 let jib =
                   let gs = ngensym () in
                   [ifuncall (id_loc id) (CL_id (gs, ret_ctyp)) (id, []) (List.map snd values)]
                   @ gen_assertion ret_ctyp result gs
                   @ [iend ()]
                 in
                 let smt_defs =
                   try (fun (x, _, _) -> x) (smt_instr_list extern ctx all_cdefs jib) with
                   | _ ->
                      raise (Skip_iteration ("SMT error for: " ^ Util.string_of_list ", " string_of_exp (List.map fst values)))
                 in
                 let smt_defs = Stack.fold (fun xs x -> x :: xs) [] smt_defs in
                 let query = Assert (Fn ("not", [smt_query ctx Property.default_query])) in

                 let fname, out_chan = Filename.open_temp_file (Util.zencode_string (string_of_id id)) ".smt2" in
                 if !(ctx.use_string) || !(ctx.use_real) then
                   output_string out_chan "(set-logic ALL)\n"
                 else
                   output_string out_chan "(set-logic QF_AUFBVDT)\n";
                 List.iter (fun smt -> output_string out_chan (string_of_smt_def smt ^ "\n")) (header @ smt_defs @ [query]);
                 output_string out_chan "(check-sat)\n";
                 close_out out_chan;

                 let in_chan = Printf.ksprintf Unix.open_process_in "cvc4 --lang=smt2.6 %s" fname in
                 let lines = ref [] in
                 begin
                   try
                     while true do
                       lines := input_line in_chan :: !lines
                     done
                   with
                   | End_of_file -> ()
                 end;
                 let _ = Unix.close_process_in in_chan in
                 let solver_output = List.rev !lines |> String.concat "\n" |> parse_sexps in
                 begin match solver_output with
                 | [Atom "unsat"] -> ()
                 | _ ->
                    prerr_endline (Util.("SMT check failed:" |> red |> clear)
                                   ^ "\n" ^ Util.string_of_list ", " string_of_exp (List.map fst values)
                                   ^ " : " ^ Util.string_of_list ", " string_of_ctyp (List.map (fun v -> cval_ctyp (snd v)) values)
                                   ^ " -> " ^ string_of_ctyp ret_ctyp
                                   ^ " = " ^ Value.string_of_value result
                                   ^ "\nFilename: " ^ fname);
                    continue := false
                 end
              | _, _ ->
                 prerr_endline Util.("Could not generate values for function types" |> yellow |> clear);
                 continue := false
              end
            with
            | Skip_iteration str ->
               incr skipped
            end;
            incr iterations
          done;
          if !continue then
            prerr_endline (Util.("ok" |> green |> clear) ^ Printf.sprintf " (%d/%d skipped)" !skipped max_iterations)

       | _ ->
          raise (Reporting.err_general (id_loc id) "Function prototype must have a function type")
     ) else ()

  | _ -> ()

let fuzz seed env ast =
  Random.init seed;

  let cdefs, _, ctx = compile env ast in

  List.iter (fuzz_cdef ctx cdefs) cdefs
