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
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

module StringMap = Map.Make (String)

open Ast
open Ast_compare

let print_chan = ref stdout

let output_files : (string * out_channel) list ref = ref []

let output_redirect file =
  let chan =
    match List.assoc_opt file !output_files with
    | Some chan -> chan
    | None ->
        let chan = open_out file in
        output_files := !output_files @ [(file, chan)];
        chan
  in
  print_chan := chan

type output_selector = Output_index of int | Output_name of string | Output_stdout

let output_select sel =
  match sel with
  | Output_stdout ->
      print_chan := stdout;
      true
  | Output_name file -> (
      match List.assoc_opt file !output_files with
      | Some chan ->
          print_chan := chan;
          true
      | None -> false
    )
  | Output_index n -> (
      match List.nth_opt !output_files (n - 1) with
      | Some (_, chan) ->
          print_chan := chan;
          true
      | None -> false
    )

let output_names () = List.map fst !output_files

let output_close () =
  List.iter (fun (_, chan) -> close_out chan) !output_files;
  output_files := [];
  print_chan := stdout

let output str =
  output_string !print_chan str;
  flush !print_chan

let output_endline str =
  output_string !print_chan (str ^ "\n");
  flush !print_chan

let string_of_id = function
  | Id_aux (And_bool, _) -> "and_bool"
  | Id_aux (Or_bool, _) -> "or_bool"
  | Id_aux (Id v, _) -> v
  | Id_aux (Operator v, _) -> "(operator " ^ v ^ ")"

let rec string_of_value = function
  | V_bitvector vs -> Sail_lib.string_of_bits vs
  | V_vector vs -> "[" ^ Util.string_of_list ", " string_of_value vs ^ "]"
  | V_bool true -> "true"
  | V_bool false -> "false"
  | V_int n -> Z.to_string n
  | V_tuple vals -> "(" ^ Util.string_of_list ", " string_of_value vals ^ ")"
  | V_list vals -> "[|" ^ Util.string_of_list ", " string_of_value vals ^ "|]"
  | V_unit -> "()"
  | V_string str -> "\"" ^ str ^ "\""
  | V_ref id -> "ref " ^ string_of_id id
  | V_real r -> Sail_lib.string_of_real (Util.Rational.from_rocq r)
  | V_member id -> string_of_id id
  | V_ctor (id, vals) -> string_of_id id ^ "(" ^ Util.string_of_list ", " string_of_value vals ^ ")"
  | V_record record ->
      "struct {"
      ^ Util.string_of_list ", " (fun (field, v) -> string_of_id field ^ " = " ^ string_of_value v) record
      ^ "}"

let mk_real r = V_real (Util.Rational.to_rocq r)

let rec eq_value v1 v2 =
  match (v1, v2) with
  | V_bitvector b1s, V_bitvector b2s -> Sail_lib.eq_list b1s b2s
  | V_vector v1s, V_vector v2s when List.length v1s = List.length v2s -> List.for_all2 eq_value v1s v2s
  | V_list v1s, V_list v2s when List.length v1s = List.length v2s -> List.for_all2 eq_value v1s v2s
  | V_int n, V_int m -> Z.equal n m
  | V_real n, V_real m -> Q.equal (Util.Rational.from_rocq n) (Util.Rational.from_rocq m)
  | V_bool b1, V_bool b2 -> b1 = b2
  | V_tuple v1s, V_tuple v2s when List.length v1s = List.length v2s -> List.for_all2 eq_value v1s v2s
  | V_unit, V_unit -> true
  | V_string str1, V_string str2 -> str1 = str2
  | V_ref str1, V_ref str2 -> Id.compare str1 str2 = 0
  | V_member name1, V_member name2 -> Id.compare name1 name2 = 0
  | V_ctor (name1, fields1), V_ctor (name2, fields2) when List.length fields1 = List.length fields2 ->
      Id.compare name1 name2 = 0 && List.for_all2 eq_value fields1 fields2
  | V_record fields1, V_record fields2 ->
      let fields1 = Bindings.of_seq @@ List.to_seq fields1 in
      let fields2 = Bindings.of_seq @@ List.to_seq fields2 in
      Bindings.equal eq_value fields1 fields2
  | _, _ -> false

let coerce_member = function V_member str -> str | _ -> assert false

let coerce_ctor = function V_ctor (str, vals) -> (str, vals) | _ -> assert false

let coerce_bool = function V_bool b -> b | _ -> assert false

let and_bool = function [v1; v2] -> V_bool (coerce_bool v1 && coerce_bool v2) | _ -> assert false

let or_bool = function [v1; v2] -> V_bool (coerce_bool v1 || coerce_bool v2) | _ -> assert false

let tuple_value (vs : value list) : value = V_tuple vs

let coerce_tuple = function V_tuple vs -> vs | _ -> assert false

let coerce_list = function V_list vs -> vs | _ -> assert false

let coerce_listlike = function V_tuple vs -> vs | V_list vs -> vs | V_unit -> [] | _ -> assert false

let coerce_int = function V_int i -> i | _ -> assert false

let coerce_real = function V_real r -> Util.Rational.from_rocq r | _ -> assert false

let coerce_cons = function V_list (v :: vs) -> Some (v, vs) | V_list [] -> None | _ -> assert false

let coerce_bv = function V_bitvector vs -> vs | _ -> assert false

let coerce_string = function V_string str -> str | _ -> assert false

let coerce_ref = function V_ref str -> str | _ -> assert false

let unit_value = V_unit

exception Arity_error

module Lifting = struct
  type _ ty =
    | Unit : unit ty
    | Int : Z.t ty
    | BV : Sail_lib.bits ty
    | Bool : bool ty
    | Real : Q.t ty
    | String : string ty

  type _ lifting = Ret : 'a ty -> 'a lifting | Arg : 'a ty * 'b lifting -> ('a -> 'b) lifting

  let ( @-> ) arg rest = Arg (arg, rest)

  let encode : type a. a ty -> a -> value =
   fun ty x ->
    match ty with
    | Unit -> V_unit
    | Int -> V_int x
    | BV -> V_bitvector x
    | Bool -> V_bool x
    | Real -> V_real (Util.Rational.to_rocq x)
    | String -> V_string x

  let decode : type a. a ty -> value -> a option =
   fun ty v ->
    match (ty, v) with
    | Unit, V_unit -> Some ()
    | Int, V_int n -> Some n
    | BV, V_bitvector bv -> Some bv
    | Bool, V_bool b -> Some b
    | String, V_string s -> Some s
    | Real, V_real q -> Some (Util.Rational.from_rocq q)
    | _ -> None

  let rec apply : type f. f -> f lifting -> value list -> value =
   fun f lifting args ->
    match (lifting, args) with
    | Ret ty, [] -> encode ty f
    | Arg (arg, rest), v :: vs -> (
        match decode arg v with Some x -> apply (f x) rest vs | None -> raise Arity_error
      )
    | _ -> raise Arity_error

  let lift : type a b. (a -> b) -> (a -> b) lifting -> value list -> value = fun f lifting args -> apply f lifting args
end

let value_eq_bit = function [v1; v2] -> V_bool (eq_value v1 v2) | _ -> failwith "value eq_bit"

let value_length = function
  | [V_bitvector bits] -> V_int (Sail_lib.length_bits bits)
  | [V_vector vs] -> V_int (Z.of_int (List.length vs))
  | _ -> failwith "value length"

let value_access = function
  | [V_bitvector bits; n] -> V_bitvector (Sail_lib.access bits (coerce_int n))
  | [V_vector vs; n] -> Sail_lib.access_list vs (coerce_int n)
  | _ -> failwith "value access"

let value_access_inc = function
  | [V_bitvector bits; n] -> V_bitvector (Sail_lib.access_inc bits (coerce_int n))
  | [V_vector vs; n] -> Sail_lib.access_list_inc vs (coerce_int n)
  | _ -> failwith "value access"

let value_update = function
  | [V_bitvector bits; n; V_bitvector b] -> V_bitvector (Sail_lib.update bits (coerce_int n) b)
  | [V_vector vs; n; v] -> V_vector (Sail_lib.update_list vs (coerce_int n) v)
  | _ -> failwith "value update"

let value_update_inc = function
  | [V_bitvector bits; n; V_bitvector b] -> V_bitvector (Sail_lib.update_inc bits (coerce_int n) b)
  | [V_vector vs; n; v] -> V_vector (Sail_lib.update_list_inc vs (coerce_int n) v)
  | _ -> failwith "value update_inc"

let value_append = function
  | [V_bitvector bv1; V_bitvector bv2] -> V_bitvector (Sail_lib.append bv1 bv2)
  | [V_vector v1; V_vector v2] -> V_vector (v1 @ v2)
  | _ -> failwith "value append"

let value_append_list = function
  | [v1; v2] -> V_list (coerce_list v1 @ coerce_list v2)
  | _ -> failwith "value_append_list"

let value_slice = function
  | [V_bitvector bits; n; m] -> V_bitvector (Sail_lib.slice bits (coerce_int n) (coerce_int m))
  | [V_vector vs; n; m] -> V_vector (Sail_lib.slice_list vs (coerce_int n) (coerce_int m))
  | _ -> failwith "value slice"

let value_slice_inc = function
  | [V_bitvector bits; n; m] -> V_bitvector (Sail_lib.slice_inc bits (coerce_int n) (coerce_int m))
  | [V_vector vs; n; m] -> V_vector (Sail_lib.slice_list_inc vs (coerce_int n) (coerce_int m))
  | _ -> failwith "value slice_inc"

let is_member = function V_member _ -> true | _ -> false

let is_ctor = function V_ctor _ -> true | _ -> false

(* Generated by monomorphisation, a cast between bitvectors of the same length *)
let value_bitvector_cast = function [v] -> v | _ -> failwith "value zeroExtend"

(* Generated by monomorphisation from string_of_bits(subrange(v, n, m)) *)
let value_string_of_bits_subrange = function
  | [v1; v2; v3] ->
      V_string (string_of_value (V_bitvector (Sail_lib.subrange (coerce_bv v1) (coerce_int v2) (coerce_int v3))))
  | _ -> failwith "value string_of_bits_subrange"

let value_vector_init = function
  | [v1; v2] -> V_vector (Sail_lib.vector_init (coerce_int v1) v2)
  | _ -> failwith "value vector_init"

let value_eq_anything = function [v1; v2] -> V_bool (eq_value v1 v2) | _ -> failwith "value eq_anything"

let value_print = function
  | [V_string str] ->
      output str;
      V_unit
  | [v] ->
      output (string_of_value v |> Util.red |> Util.clear);
      V_unit
  | _ -> assert false

let value_print_endline = function
  | [V_string str] ->
      output_endline str;
      V_unit
  | [v] ->
      output_endline (string_of_value v |> Util.red |> Util.clear);
      V_unit
  | _ -> assert false

let value_internal_pick = function [v1] -> List.hd (coerce_listlike v1) | _ -> failwith "value internal_pick"

let value_undefined_vector = function
  | [v1; v2] -> V_vector (Sail_lib.undefined_vector (coerce_int v1) v2)
  | _ -> failwith "value undefined_vector"

let value_undefined_range = function [v; _] -> v | _ -> failwith "value undefined_range"

let value_undefined_list = function [_] -> V_list [] | _ -> failwith "value undefined_list"

let value_putchar = function
  | [v] ->
      output_char !print_chan (char_of_int (Z.to_int (coerce_int v)));
      flush !print_chan;
      V_unit
  | _ -> failwith "value putchar"

let value_dec_str = function [n] -> V_string (string_of_value n) | _ -> failwith "value print_int"

let value_print_bits = function
  | [msg; bits] ->
      output_endline (coerce_string msg ^ string_of_value bits);
      V_unit
  | _ -> failwith "value print_bits"

let value_print_int = function
  | [msg; n] ->
      output_endline (coerce_string msg ^ string_of_value n);
      V_unit
  | _ -> failwith "value print_int"

let value_print_string = function
  | [msg; str] ->
      output_endline (coerce_string msg ^ coerce_string str);
      V_unit
  | _ -> failwith "value print_string"

let value_prerr_bits = function
  | [msg; bits] ->
      prerr_endline (coerce_string msg ^ string_of_value bits);
      V_unit
  | _ -> failwith "value prerr_bits"

let value_prerr_int = function
  | [msg; n] ->
      prerr_endline (coerce_string msg ^ string_of_value n);
      V_unit
  | _ -> failwith "value prerr_int"

let value_prerr = function
  | [str] ->
      prerr_string (coerce_string str);
      V_unit
  | _ -> failwith "value prerr"

let value_prerr_endline = function
  | [str] ->
      prerr_endline (coerce_string str);
      V_unit
  | _ -> failwith "value prerr_endline"

let value_prerr_string = function
  | [msg; str] ->
      output_endline (coerce_string msg ^ coerce_string str);
      V_unit
  | _ -> failwith "value print_string"

let value_print_real = function
  | [v1; v2] ->
      output_endline (coerce_string v1 ^ string_of_value v2);
      V_unit
  | _ -> failwith "value print_real"

let value_prerr_real = function
  | [v1; v2] ->
      prerr_endline (coerce_string v1 ^ string_of_value v2);
      V_unit
  | _ -> failwith "value prerr_real"

let value_random_real = function [_] -> mk_real (Sail_lib.random_real ()) | _ -> failwith "value random_real"

let value_undefined_real = function [_] -> mk_real (Sail_lib.undefined_real ()) | _ -> failwith "value undefined_real"

let value_cycle_count _ =
  Sail_lib.cycle_count ();
  V_unit

let value_get_cycle_count _ = V_int (Sail_lib.get_cycle_count ())

let primops =
  let open Lifting in
  ref
    (List.fold_left
       (fun r (x, y) -> StringMap.add x y r)
       StringMap.empty
       [
         ("and_bool", and_bool);
         ("or_bool", or_bool);
         ("print", value_print);
         ("prerr", value_prerr);
         ("dec_str", value_dec_str);
         ("print_endline", value_print_endline);
         ("prerr_endline", value_prerr_endline);
         ("putchar", value_putchar);
         ("string_of_int", fun vs -> V_string (string_of_value (List.hd vs)));
         ("string_of_bits", fun vs -> V_string (string_of_value (List.hd vs)));
         ("decimal_string_of_bits", lift Sail_lib.decimal_string_of_bits (BV @-> Ret String));
         ("print_bits", value_print_bits);
         ("print_int", value_print_int);
         ("print_string", value_print_string);
         ("prerr_bits", value_prerr_bits);
         ("prerr_int", value_prerr_int);
         ("prerr_string", value_prerr_string);
         ("concat_str", lift Sail_lib.concat_str (String @-> String @-> Ret String));
         ("eq_int", lift Sail_lib.eq_int (Int @-> Int @-> Ret Bool));
         ("lteq", lift Sail_lib.lteq (Int @-> Int @-> Ret Bool));
         ("gteq", lift Sail_lib.gteq (Int @-> Int @-> Ret Bool));
         ("lt", lift Sail_lib.lt (Int @-> Int @-> Ret Bool));
         ("gt", lift Sail_lib.gt (Int @-> Int @-> Ret Bool));
         ("eq_list", lift Sail_lib.eq_list (BV @-> BV @-> Ret Bool));
         ("eq_bool", lift Sail_lib.eq_bool (Bool @-> Bool @-> Ret Bool));
         ("eq_unit", fun _ -> V_bool true);
         ("eq_string", lift Sail_lib.eq_string (String @-> String @-> Ret Bool));
         ("string_startswith", lift Sail_lib.string_startswith (String @-> String @-> Ret Bool));
         ("string_drop", lift Sail_lib.string_drop (String @-> Int @-> Ret String));
         ("string_take", lift Sail_lib.string_take (String @-> Int @-> Ret String));
         ("string_length", lift Sail_lib.string_length (String @-> Ret Int));
         ("eq_bit", value_eq_bit);
         ("eq_anything", value_eq_anything);
         ("length", value_length);
         ("length_bits", value_length);
         ("subrange", lift Sail_lib.subrange (BV @-> Int @-> Int @-> Ret BV));
         ("subrange_inc", lift Sail_lib.subrange_inc (BV @-> Int @-> Int @-> Ret BV));
         ("access", value_access);
         ("access_inc", value_access_inc);
         ("update", value_update);
         ("update_inc", value_update_inc);
         ("update_subrange", lift Sail_lib.update_subrange (BV @-> Int @-> Int @-> BV @-> Ret BV));
         ("update_subrange_inc", lift Sail_lib.update_subrange_inc (BV @-> Int @-> Int @-> BV @-> Ret BV));
         ("slice", value_slice);
         ("slice_inc", value_slice_inc);
         ("append", value_append);
         ("append_list", value_append_list);
         ("not", lift not (Bool @-> Ret Bool));
         ("not_bits", lift Sail_lib.not_bits (BV @-> Ret BV));
         ("and_bits", lift Sail_lib.and_bits (BV @-> BV @-> Ret BV));
         ("or_bits", lift Sail_lib.or_bits (BV @-> BV @-> Ret BV));
         ("xor_bits", lift Sail_lib.xor_bits (BV @-> BV @-> Ret BV));
         ("uint", lift Sail_lib.uint (BV @-> Ret Int));
         ("sint", lift Sail_lib.sint (BV @-> Ret Int));
         ("get_slice_int", lift Sail_lib.get_slice_int (Int @-> Int @-> Int @-> Ret BV));
         ("set_slice_int", lift Sail_lib.set_slice_int (Int @-> Int @-> Int @-> BV @-> Ret Int));
         ("set_slice", lift Sail_lib.set_slice (Int @-> Int @-> BV @-> Int @-> BV @-> Ret BV));
         ("hex_slice", lift Sail_lib.hex_slice (String @-> Int @-> Int @-> Ret BV));
         ("zero_extend", lift Sail_lib.zero_extend (BV @-> Int @-> Ret BV));
         ("zeroExtend", value_bitvector_cast);
         ("string_of_bits_subrange", value_string_of_bits_subrange);
         ("sign_extend", lift Sail_lib.sign_extend (BV @-> Int @-> Ret BV));
         ("zeros", lift Sail_lib.zeros (Int @-> Ret BV));
         ("ones", lift Sail_lib.ones (Int @-> Ret BV));
         ("shiftr", lift Sail_lib.shiftr (BV @-> Int @-> Ret BV));
         ("shiftl", lift Sail_lib.shiftl (BV @-> Int @-> Ret BV));
         ("arith_shiftr", lift Sail_lib.arith_shiftr (BV @-> Int @-> Ret BV));
         ("shift_bits_left", lift Sail_lib.shift_bits_left (BV @-> BV @-> Ret BV));
         ("shift_bits_right", lift Sail_lib.shift_bits_right (BV @-> BV @-> Ret BV));
         ("add_int", lift Sail_lib.add_int (Int @-> Int @-> Ret Int));
         ("sub_int", lift Sail_lib.sub_int (Int @-> Int @-> Ret Int));
         ("sub_nat", lift Sail_lib.sub_nat (Int @-> Int @-> Ret Int));
         ("div_int", lift Sail_lib.ediv_int (Int @-> Int @-> Ret Int));
         ("tdiv_int", lift Sail_lib.tdiv_int (Int @-> Int @-> Ret Int));
         ("tmod_int", lift Sail_lib.tmod_int (Int @-> Int @-> Ret Int));
         ("mult_int", lift Sail_lib.mult (Int @-> Int @-> Ret Int));
         ("mult", lift Sail_lib.mult (Int @-> Int @-> Ret Int));
         ("ediv_int", lift Sail_lib.ediv_int (Int @-> Int @-> Ret Int));
         ("emod_int", lift Sail_lib.emod_int (Int @-> Int @-> Ret Int));
         ("negate", lift Sail_lib.negate (Int @-> Ret Int));
         ("pow2", lift Sail_lib.pow2 (Int @-> Ret Int));
         ("int_power", lift Sail_lib.int_power (Int @-> Int @-> Ret Int));
         ("shr_int", lift Sail_lib.shr_int (Int @-> Int @-> Ret Int));
         ("shl_int", lift Sail_lib.shl_int (Int @-> Int @-> Ret Int));
         ("max_int", lift Sail_lib.max_int (Int @-> Int @-> Ret Int));
         ("min_int", lift Sail_lib.min_int (Int @-> Int @-> Ret Int));
         ("abs_int", lift Sail_lib.abs_int (Int @-> Ret Int));
         ("add_bits_int", lift Sail_lib.add_bits_int (BV @-> Int @-> Ret BV));
         ("sub_bits_int", lift Sail_lib.sub_bits_int (BV @-> Int @-> Ret BV));
         ("add_bits", lift Sail_lib.add_bits (BV @-> BV @-> Ret BV));
         ("sub_bits", lift Sail_lib.sub_bits (BV @-> BV @-> Ret BV));
         ("vector_init", value_vector_init);
         ("vector_truncate", lift Sail_lib.vector_truncate (BV @-> Int @-> Ret BV));
         ("vector_truncateLSB", lift Sail_lib.vector_truncateLSB (BV @-> Int @-> Ret BV));
         ("read_ram", lift Sail_lib.read_ram (Int @-> Int @-> BV @-> BV @-> Ret BV));
         ("write_ram", lift Sail_lib.write_ram (Int @-> Int @-> BV @-> BV @-> BV @-> Ret Bool));
         ("emulator_read_mem", lift Sail_lib.emulator_read_mem (Int @-> BV @-> Int @-> Ret BV));
         ("emulator_read_mem_ifetch", lift Sail_lib.emulator_read_mem_ifetch (Int @-> BV @-> Int @-> Ret BV));
         ("emulator_read_mem_exclusive", lift Sail_lib.emulator_read_mem_exclusive (Int @-> BV @-> Int @-> Ret BV));
         ("emulator_write_mem", lift Sail_lib.emulator_write_mem (Int @-> BV @-> Int @-> BV @-> Ret Bool));
         ( "emulator_write_mem_exclusive",
           lift Sail_lib.emulator_write_mem_exclusive (Int @-> BV @-> Int @-> BV @-> Ret Bool)
         );
         ("emulator_read_tag", lift Sail_lib.emulator_read_tag (Int @-> BV @-> Ret Bool));
         ("emulator_write_tag", lift Sail_lib.emulator_write_tag (Int @-> BV @-> Bool @-> Ret Unit));
         ("cycle_count", value_cycle_count);
         ("get_cycle_count", value_get_cycle_count);
         ("trace_memory_read", fun _ -> V_unit);
         ("trace_memory_write", fun _ -> V_unit);
         ("get_time_ns", fun _ -> V_int (Sail_lib.get_time_ns ()));
         ("sail_assume", fun _ -> V_unit);
         ("load_raw", lift Sail_lib.load_raw (BV @-> String @-> Ret Unit));
         ("to_real", lift Sail_lib.to_real (Int @-> Ret Real));
         ("eq_real", lift Sail_lib.eq_real (Real @-> Real @-> Ret Bool));
         ("lt_real", lift Sail_lib.lt_real (Real @-> Real @-> Ret Bool));
         ("gt_real", lift Sail_lib.gt_real (Real @-> Real @-> Ret Bool));
         ("lteq_real", lift Sail_lib.lteq_real (Real @-> Real @-> Ret Bool));
         ("gteq_real", lift Sail_lib.gteq_real (Real @-> Real @-> Ret Bool));
         ("add_real", lift Sail_lib.add_real (Real @-> Real @-> Ret Real));
         ("sub_real", lift Sail_lib.sub_real (Real @-> Real @-> Ret Real));
         ("mult_real", lift Sail_lib.mult_real (Real @-> Real @-> Ret Real));
         ("round_up", lift Sail_lib.round_up (Real @-> Ret Int));
         ("round_down", lift Sail_lib.round_down (Real @-> Ret Int));
         ("quot_round_zero", lift Sail_lib.quot_round_zero (Int @-> Int @-> Ret Int));
         ("rem_round_zero", lift Sail_lib.rem_round_zero (Int @-> Int @-> Ret Int));
         ("abs_real", lift Sail_lib.abs_real (Real @-> Ret Real));
         ("div_real", lift Sail_lib.div_real (Real @-> Real @-> Ret Real));
         ("sqrt_real", lift Sail_lib.sqrt_real (Real @-> Ret Real));
         ("print_real", value_print_real);
         ("prerr_real", value_prerr_real);
         ("random_real", value_random_real);
         ("neg_real", lift Sail_lib.neg_real (Real @-> Ret Real));
         ("real_power", lift Sail_lib.real_power (Real @-> Int @-> Ret Real));
         ("undefined_real", value_undefined_real);
         ("undefined_unit", fun _ -> V_unit);
         ("undefined_bit", fun _ -> V_bitvector (Sail_lib.zeros (Z.of_int 1)));
         ("undefined_int", fun _ -> V_int Z.zero);
         ("undefined_range", value_undefined_range);
         ("undefined_nat", fun _ -> V_int Z.zero);
         ("undefined_bool", fun _ -> V_bool false);
         ("undefined_bitvector", lift Sail_lib.undefined_bitvector (Int @-> Ret BV));
         ("undefined_vector", value_undefined_vector);
         ("undefined_list", value_undefined_list);
         ("undefined_string", fun _ -> V_string "");
         ("internal_pick", value_internal_pick);
         ("replicate_bits", lift Sail_lib.replicate_bits (BV @-> Int @-> Ret BV));
         ("count_leading_zeros", lift Sail_lib.count_leading_zeros (BV @-> Ret Int));
         ("count_trailing_zeros", lift Sail_lib.count_trailing_zeros (BV @-> Ret Int));
         ("Elf_loader.elf_entry", fun _ -> V_int !Elf_loader.opt_elf_entry);
         ("Elf_loader.elf_tohost", fun _ -> V_int !Elf_loader.opt_elf_tohost);
         ("string_append", lift Sail_lib.string_append (String @-> String @-> Ret String));
         ("string_length", lift Sail_lib.string_length (String @-> Ret Int));
         ("string_startswith", lift Sail_lib.string_startswith (String @-> String @-> Ret Bool));
         ("string_drop", lift Sail_lib.string_drop (String @-> Int @-> Ret String));
         ("hex_str", lift Sail_lib.hex_str (Int @-> Ret String));
         ("hex_str_upper", lift Sail_lib.hex_str_upper (Int @-> Ret String));
         ("parse_hex_bits", lift Sail_lib.parse_hex_bits (Int @-> String @-> Ret BV));
         ("valid_hex_bits", lift Sail_lib.valid_hex_bits (Int @-> String @-> Ret Bool));
         ("parse_dec_bits", lift Sail_lib.parse_dec_bits (Int @-> String @-> Ret BV));
         ("valid_dec_bits", lift Sail_lib.valid_dec_bits (Int @-> String @-> Ret Bool));
         ("sleep_request", lift Sail_lib.sleep_request (Unit @-> Ret Unit));
         ("wakeup_request", lift Sail_lib.wakeup_request (Unit @-> Ret Unit));
         ("skip", fun _ -> V_unit);
       ]
    )

let add_primop name impl = primops := StringMap.add name impl !primops
