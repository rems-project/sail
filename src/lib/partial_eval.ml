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

open Ast
open Ast_compare
open Ast_defs
open Ast_util

open Extraction.ZAst

module Big_int = Nat_big_num
module StringMap = Util.StringMap

module type SAIL_VALUE = sig
  include Extraction.Lattice.SAIL_VALUE

  val string_of_value : t -> string

  val bitvector_of_bits : Bit.bit list -> t

  val concrete_ref : t -> id_aux option

  val initial_primops : (t list -> t) StringMap.t
end

let concrete_bit = function
  | Extraction.Bit.Three.B0 -> Some Bit.B0
  | Extraction.Bit.Three.B1 -> Some Bit.B1
  | Extraction.Bit.Three.BU -> None

let rec is_concrete_bitvector = function
  | [] -> true
  | Extraction.Bit.Three.BU :: _ -> false
  | _ :: bv -> is_concrete_bitvector bv

let char_of_bit = function
  | Extraction.Bit.Three.B0 -> '0'
  | Extraction.Bit.Three.B1 -> '1'
  | Extraction.Bit.Three.BU -> '?'

module AbsValue : SAIL_VALUE = struct
  include
    Extraction.AbsValue.Dom (Extraction.Interval.Dom) (Extraction.AbsBitvector.Dom)
      (Extraction.TransferBitvectorInterval.Ops)

  let string_of_bitvector bv =
    let len = List.length bv in
    let buf = Buffer.create (List.length bv) in
    if len mod 4 = 0 && is_concrete_bitvector bv then (
      let bv = Option.get (Util.option_all (List.map concrete_bit bv)) in
      Buffer.add_string buf (Sail_lib.string_of_bits (List.rev bv))
    )
    else (
      Buffer.add_string buf "0b";
      let rec go = function
        | [] -> ()
        | b :: bs ->
            Buffer.add_char buf (char_of_bit b);
            go bs
      in
      go (List.rev bv)
    );
    Buffer.contents buf

  let rec string_of_value (v : t) =
    match v with
    | V_bot -> "bot"
    | V_top -> "top"
    | V_int intv -> (
        match intv with
        | Empty -> "empty"
        | Ends (Coq_exist (lo, hi)) -> (
            match (lo, hi) with
            | None, None -> "(-inf,inf)"
            | Some lo, None -> Printf.sprintf "[%s,inf)" (Z.to_string lo)
            | None, Some hi -> Printf.sprintf "(-inf,%s]" (Z.to_string hi)
            | Some lo, Some hi ->
                if Z.equal lo hi then Z.to_string lo else Printf.sprintf "[%s,%s]" (Z.to_string lo) (Z.to_string hi)
          )
      )
    | V_bitvector bitv -> (
        match Extraction.AbsBitvector.Dom.to_bv_list bitv with
        | None -> "bvtop"
        | Some bvs -> (
            match bvs with
            | [] -> "bvbot"
            | [bv] -> string_of_bitvector bv
            | _ -> "{" ^ Util.string_of_list "," string_of_bitvector bvs ^ "}"
          )
      )
    | V_unit -> "()"
    | V_string str -> "\"" ^ String.escaped str ^ "\""
    | V_bool b -> if b then "true" else "false"
    | V_tuple values -> Util.string_of_list ", " string_of_value values
    | V_real qc -> Sail_lib.string_of_real (Util.Rational.from_rocq qc.Extraction.Qcanon.this)
    | _ -> "?"

  let v_real (q : Q.t) = V_real { Extraction.Qcanon.this = Util.Rational.to_rocq q }

  (* Wrap a concrete MSB-first [Bit.bit list] result as a
     [V_bitvector] abstract value. [Bit.Bits.to_bvn] expects MSB-first
     input (its [bits_to_N] threads each bit through [acc := 2*acc +
     b], so the first element is most-significant) so we pass [bits]
     through unchanged. *)
  let bitvector_of_bits bits = V_bitvector (Extraction.AbsBitvector.Dom.abst (Extraction.Bit.Bits.to_bvn bits))

  (** Define a module for lifting primitives.

      If [f] has type [int -> int -> string], then the following will lift it to a function over a list of values.
      [None] is used to signal an arity error.

      {[
        lift f (Int @-> Int @-> Ret String) : value list -> value option
      ]} *)
  module Lifting = struct
    type _ ty =
      | Unit : unit ty
      | Int : Z.t ty
      | AbsInt : Extraction.Interval.Dom.t ty
      | BV : Bit.bit list ty
      | AbsBV : Extraction.AbsBitvector.Dom.t ty
      | Bool : bool ty
      | Real : Q.t ty
      | String : string ty

    type _ lifting = Ret : 'a ty -> 'a lifting | Arg : 'a ty * 'b lifting -> ('a -> 'b) lifting

    let ( @-> ) arg rest = Arg (arg, rest)

    let encode : type a. a ty -> a -> t =
     fun ty x ->
      match ty with
      | Unit -> V_unit
      | Int -> V_int (Extraction.Interval.Dom.abst x)
      | AbsInt -> V_int x
      | BV -> bitvector_of_bits x
      | AbsBV -> V_bitvector x
      | Bool -> V_bool x
      | Real -> v_real x
      | String -> V_string x

    let decode : type a. a ty -> t -> a option =
     fun ty v ->
      match (ty, v) with
      | Unit, V_unit -> Some ()
      | AbsInt, V_int n -> Some n
      | Int, V_int n -> Extraction.Interval.Dom.concrete n
      | AbsBV, V_bitvector bv -> Some bv
      | BV, V_bitvector bv -> (
          match Extraction.AbsBitvector.Dom.to_bv_list bv with
          | Some [bits] -> Option.map List.rev (Util.option_all (List.map concrete_bit bits))
          | _ -> None
        )
      | Bool, V_bool b -> Some b
      | String, V_string s -> Some s
      | Real, V_real qc -> Some (Util.Rational.from_rocq qc.Extraction.Qcanon.this)
      | _ -> None

    let rec apply : type f. f -> f lifting -> t list -> t =
     fun f lifting args ->
      match (lifting, args) with
      | Ret ty, [] -> encode ty f
      | Arg (arg, rest), v :: vs -> (
          match decode arg v with Some x -> apply (f x) rest vs | None -> V_top
        )
      | _ -> V_top

    let lift : type a b. (a -> b) -> (a -> b) lifting -> t list -> t = fun f lifting args -> apply f lifting args
  end

  let concrete_int = function V_int i -> Extraction.Interval.Dom.concrete i | _ -> None

  let rec concrete_bits = function
    | V_bitvector dbv -> (
        match Extraction.AbsBitvector.Dom.to_bv_list dbv with
        | Some [bits] -> Option.map List.rev (Util.option_all (List.map concrete_bit bits))
        | _ -> None
      )
    | _ -> None

  let primop_print_endline args =
    (match args with [V_string str] -> Value.output_endline str | _ -> ());
    V_unit

  let primop_print args =
    (match args with [V_string str] -> Value.output str | _ -> ());
    V_unit

  (* [prerr] / [prerr_endline] write to stderr — matching the regular
   interpreter's [value.ml] bindings. The REPL's [-iout] captures stdout
   only, so stderr output stays out of the test's diff. *)
  let primop_prerr args =
    (match args with [V_string str] -> Stdlib.prerr_string str | _ -> ());
    V_unit

  let primop_prerr_endline args =
    (match args with [V_string str] -> Stdlib.prerr_endline str | _ -> ());
    V_unit

  (* [print_string] / [prerr_string] take (msg, str) — see [value.ml].
   Curiously, [value.ml]'s [value_prerr_string] sends its output to stdout,
   not stderr; we mirror that. *)
  let primop_print_string args =
    (match args with [V_string a; V_string b] -> Value.output_endline (a ^ b) | _ -> ());
    V_unit

  let v_int_concrete n = V_int (Extraction.Interval.Dom.abst n)

  (* Lift a Rocq-verified interval comparison ([interval -> interval -> bool option])
   to the lattice. [None] means the relation cannot be decided from the intervals
   alone, which lifts to [V_top]. *)
  let lift_int_cmp f = function
    | [V_int i; V_int j] -> (
        match f i j with Some b -> V_bool b | None -> V_top
      )
    | _ -> V_top

  let primop_lt = lift_int_cmp Extraction.Interval.Dom.lt
  let primop_gt = lift_int_cmp Extraction.Interval.Dom.gt
  let primop_lteq = lift_int_cmp Extraction.Interval.Dom.lteq
  let primop_gteq = lift_int_cmp Extraction.Interval.Dom.gteq

  let primop_print_int = function
    | [V_string msg; n] ->
        Value.output_endline (msg ^ string_of_value n);
        V_unit
    | _ -> V_unit

  let primop_print_bits = function
    | [V_string msg; bits] ->
        Value.output_endline (msg ^ string_of_value bits);
        V_unit
    | _ -> V_unit

  (* Coerce a [value] argument to an abstract bitvector [Dom.t]. Accepts
   [V_bitvector] directly; falls back to flattening a [V_vector] of singleton
   [V_bitvector]s by concretizing via [concrete_bits]. The fallback handles
   bitvector literals like [[bitone, bitzero]] that the evaluator builds as
   [V_vector] of single-bit [V_bitvector]s without consulting the type. *)
  let as_abs_bv = function
    | V_bitvector dbv -> Some dbv
    | V_vector _ as v -> (
        match concrete_bits v with
        | Some bs -> Some (Extraction.AbsBitvector.Dom.abst (Extraction.Bit.Bits.to_bvn bs))
        | None -> None
      )
    | _ -> None

  let v_bitvector dbv = V_bitvector dbv

  (* [h] caps the number of distinct bitvector widths the result may carry; the
   underlying Rocq op returns [B.⊤] if the input interval admits more widths
   than this. Most Sail code uses concrete widths well under any reasonable
   bound; we pick 256 as a generous default. *)
  let widths_cap = Z.of_int 256

  let primop_length = function [v] -> value_length v | _ -> V_top

  let primop_eq_bits = function
    | [a; b] -> (
        match (concrete_bits a, concrete_bits b) with
        | Some xs, Some ys -> V_bool (List.length xs = List.length ys && List.for_all2 ( = ) xs ys)
        | _ -> V_top
      )
    | _ -> V_top

  let lattice_eq a b = leb a b && leb b a

  let primop_eq_anything = function [a; b] -> V_bool (lattice_eq a b) | _ -> V_top

  let initial_primops =
    let open Lifting in
    let open Extraction in
    let curry f a b = f (a, b) in
    let curry3 f a b c = f (a, b, c) in
    let curry4 f a b c d = f (a, b, c, d) in
    let curry5 f a b c d e = f (a, b, c, d, e) in
    List.fold_left
      (fun m (name, op) -> StringMap.add name op m)
      StringMap.empty
      [
        ("print_endline", primop_print_endline);
        ("prerr_endline", primop_prerr_endline);
        ("print", primop_print);
        ("prerr", primop_prerr);
        ("print_string", primop_print_string);
        ("prerr_string", primop_print_string);
        ("print_int", primop_print_int);
        ("prerr_int", primop_print_int);
        ("print_bits", primop_print_bits);
        ("prerr_bits", primop_print_bits);
        ("dec_str", lift Sail_lib.dec_str (Int @-> Ret String));
        ("hex_str", lift Sail_lib.hex_str (Int @-> Ret String));
        ("hex_str_upper", lift Sail_lib.hex_str_upper (Int @-> Ret String));
        ("negate", lift Interval.Dom.negate (AbsInt @-> Ret AbsInt));
        ("string_take", lift (fun s n -> Sail_lib.string_take (s, n)) (String @-> Int @-> Ret String));
        ("string_drop", lift (fun s n -> Sail_lib.string_drop (s, n)) (String @-> Int @-> Ret String));
        ("string_length", lift Sail_lib.string_length (String @-> Ret Int));
        ("string_append", lift ( ^ ) (String @-> String @-> Ret String));
        ("add_int", lift Interval.Dom.add (AbsInt @-> AbsInt @-> Ret AbsInt));
        ("sub_int", lift Interval.Dom.sub (AbsInt @-> AbsInt @-> Ret AbsInt));
        ("mult_int", lift Interval.Dom.mult (AbsInt @-> AbsInt @-> Ret AbsInt));
        ("mult", lift Interval.Dom.mult (AbsInt @-> AbsInt @-> Ret AbsInt));
        ("abs_int", lift Z.abs (Int @-> Ret Int));
        ("div_int", lift Z.div (Int @-> Int @-> Ret Int));
        ("tdiv_int", lift Z.div (Int @-> Int @-> Ret Int));
        ("quotient", lift Z.ediv (Int @-> Int @-> Ret Int));
        ("modulus", lift Z.erem (Int @-> Int @-> Ret Int));
        ("tmod_int", lift Z.rem (Int @-> Int @-> Ret Int));
        ("eq_int", lift Z.equal (Int @-> Int @-> Ret Bool));
        ("quot_round_zero", lift Z.div (Int @-> Int @-> Ret Int));
        ("rem_round_zero", lift Z.rem (Int @-> Int @-> Ret Int));
        ("lt", primop_lt);
        ("gt", primop_gt);
        ("lteq", primop_lteq);
        ("gteq", primop_gteq);
        ( "sail_zero_extend",
          lift (TransferBitvectorInterval.Ops.zero_extend widths_cap) (AbsBV @-> AbsInt @-> Ret AbsBV)
        );
        ("zero_extend", lift (TransferBitvectorInterval.Ops.zero_extend widths_cap) (AbsBV @-> AbsInt @-> Ret AbsBV));
        ( "sail_sign_extend",
          lift (TransferBitvectorInterval.Ops.sign_extend widths_cap) (AbsBV @-> AbsInt @-> Ret AbsBV)
        );
        ("sign_extend", lift (TransferBitvectorInterval.Ops.sign_extend widths_cap) (AbsBV @-> AbsInt @-> Ret AbsBV));
        ("sail_zeros", lift (TransferBitvectorInterval.Ops.zeros widths_cap) (AbsInt @-> Ret AbsBV));
        ("zeros", lift (TransferBitvectorInterval.Ops.zeros widths_cap) (AbsInt @-> Ret AbsBV));
        ("sail_ones", lift (TransferBitvectorInterval.Ops.ones widths_cap) (AbsInt @-> Ret AbsBV));
        ("ones", lift (TransferBitvectorInterval.Ops.ones widths_cap) (AbsInt @-> Ret AbsBV));
        ("replicate_bits", lift (fun bs n -> Sail_lib.replicate_bits (bs, n)) (BV @-> Int @-> Ret BV));
        ("length", primop_length);
        ("eq_bits", primop_eq_bits);
        ("eq_anything", primop_eq_anything);
        ("not_vec", lift AbsBitvector.Dom.not (AbsBV @-> Ret AbsBV));
        ("add_vec", lift AbsBitvector.Dom.add (AbsBV @-> AbsBV @-> Ret AbsBV));
        ("sub_vec", lift AbsBitvector.Dom.sub (AbsBV @-> AbsBV @-> Ret AbsBV));
        ("and_vec", lift AbsBitvector.Dom.coq_and (AbsBV @-> AbsBV @-> Ret AbsBV));
        ("or_vec", lift AbsBitvector.Dom.coq_or (AbsBV @-> AbsBV @-> Ret AbsBV));
        ("xor_vec", lift AbsBitvector.Dom.xor (AbsBV @-> AbsBV @-> Ret AbsBV));
        ("shiftl", lift (fun bs n -> Sail_lib.shiftl (bs, n)) (BV @-> Int @-> Ret BV));
        ("shiftr", lift (fun bs n -> Sail_lib.shiftr (bs, n)) (BV @-> Int @-> Ret BV));
        ("append", lift AbsBitvector.Dom.append (AbsBV @-> AbsBV @-> Ret AbsBV));
        ("vector_truncate", lift (fun bs n -> Sail_lib.vector_truncate (bs, n)) (BV @-> Int @-> Ret BV));
        ("slice", lift AbsBitvector.Dom.slice (AbsBV @-> Int @-> Int @-> Ret AbsBV));
        ("uint", lift TransferBitvectorInterval.Ops.unsigned (AbsBV @-> Ret AbsInt));
        ("sint", lift TransferBitvectorInterval.Ops.signed (AbsBV @-> Ret AbsInt));
        ("pow2", lift Sail_lib.pow2 (Int @-> Ret Int));
        ("shl_int", lift (fun i n -> Sail_lib.shl_int (i, n)) (Int @-> Int @-> Ret Int));
        ("shr_int", lift (fun i n -> Sail_lib.shr_int (i, n)) (Int @-> Int @-> Ret Int));
        ("concat_str", lift ( ^ ) (String @-> String @-> Ret String));
        ("string_of_bits", lift Sail_lib.string_of_bits (BV @-> Ret String));
        ("eq_string", lift ( = ) (String @-> String @-> Ret Bool));
        ("not", lift not (Bool @-> Ret Bool));
        ("signed", lift TransferBitvectorInterval.Ops.signed (AbsBV @-> Ret AbsInt));
        ("unsigned", lift TransferBitvectorInterval.Ops.unsigned (AbsBV @-> Ret AbsInt));
        ("count_leading_zeros", lift TransferBitvectorInterval.Ops.count_leading_zeros (AbsBV @-> Ret AbsInt));
        ("count_trailing_zeros", lift TransferBitvectorInterval.Ops.count_trailing_zeros (AbsBV @-> Ret AbsInt));
        ( "access",
          fun args ->
            match args with
            | [V_vector xs; n] -> (
                match concrete_int n with
                | Some n ->
                    let i = List.length xs - Z.to_int n - 1 in
                    if i >= 0 && i < List.length xs then List.nth xs i else V_top
                | None -> V_top
              )
            | [bv; n] -> (
                match (as_abs_bv bv, concrete_int n) with
                | Some a, Some n -> v_bitvector (AbsBitvector.Dom.slice a n Z.one)
                | _ -> V_top
              )
            | _ -> V_top
        );
        ( "access_inc",
          fun args ->
            match args with
            | [V_vector xs; n] -> (
                match concrete_int n with
                | Some n ->
                    let i = Z.to_int n in
                    if i >= 0 && i < List.length xs then List.nth xs i else V_top
                | None -> V_top
              )
            | [bv; n] -> (
                match (concrete_bits bv, concrete_int n) with
                | Some bs, Some n -> bitvector_of_bits (Sail_lib.access_inc (bs, n))
                | _ -> V_top
              )
            | _ -> V_top
        );
        ( "access_list",
          fun args ->
            match args with
            | [V_vector xs; n] -> (
                match concrete_int n with
                | Some n ->
                    let i = List.length xs - Z.to_int n - 1 in
                    if i >= 0 && i < List.length xs then List.nth xs i else V_top
                | None -> V_top
              )
            | _ -> V_top
        );
        ( "access_list_inc",
          fun args ->
            match args with
            | [V_vector xs; n] -> (
                match concrete_int n with
                | Some n ->
                    let i = Z.to_int n in
                    if i >= 0 && i < List.length xs then List.nth xs i else V_top
                | None -> V_top
              )
            | _ -> V_top
        );
        ( "update",
          fun args ->
            match args with
            | [V_vector xs; n; x] -> (
                match concrete_int n with
                | Some n ->
                    let i = List.length xs - Z.to_int n - 1 in
                    if i >= 0 && i < List.length xs then V_vector (List.mapi (fun j v -> if j = i then x else v) xs)
                    else V_top
                | None -> V_top
              )
            | [bv; n; bit] -> (
                match (concrete_bits bv, concrete_int n, concrete_bits bit) with
                | Some bs, Some n, Some [b] -> bitvector_of_bits (Sail_lib.update (bs, n, [b]))
                | _ -> V_top
              )
            | _ -> V_top
        );
        ( "update_inc",
          fun args ->
            match args with
            | [V_vector xs; n; x] -> (
                match concrete_int n with
                | Some n ->
                    let i = Z.to_int n in
                    if i >= 0 && i < List.length xs then V_vector (List.mapi (fun j v -> if j = i then x else v) xs)
                    else V_top
                | None -> V_top
              )
            | [bv; n; bit] -> (
                match (concrete_bits bv, concrete_int n, concrete_bits bit) with
                | Some bs, Some n, Some [b] -> bitvector_of_bits (Sail_lib.update_inc (bs, n, [b]))
                | _ -> V_top
              )
            | _ -> V_top
        );
        ( "subrange",
          fun args ->
            match args with
            | [bv; n; m] -> (
                match (as_abs_bv bv, concrete_int n, concrete_int m) with
                | Some a, Some n, Some m -> v_bitvector (AbsBitvector.Dom.slice a m (Z.add (Z.sub n m) Z.one))
                | _ -> V_top
              )
            | _ -> V_top
        );
        ("subrange_inc", lift (curry3 Sail_lib.subrange_inc) (BV @-> Int @-> Int @-> Ret BV));
        ("update_subrange", lift (curry4 Sail_lib.update_subrange) (BV @-> Int @-> Int @-> BV @-> Ret BV));
        ("update_subrange_inc", lift (curry4 Sail_lib.update_subrange_inc) (BV @-> Int @-> Int @-> BV @-> Ret BV));
        ( "eq_list",
          fun args ->
            match args with
            | [V_bitvector _; V_bitvector _] -> primop_eq_bits args
            | [(V_vector _ as a); (V_vector _ as b)] -> V_bool (lattice_eq a b)
            | _ -> V_top
        );
        ( "vector_init",
          fun args ->
            match args with
            | [n; elem] -> (
                match concrete_int n with Some n -> V_vector (List.init (Z.to_int n) (fun _ -> elem)) | None -> V_top
              )
            | _ -> V_top
        );
        ("max_int", lift Interval.Dom.max (AbsInt @-> AbsInt @-> Ret AbsInt));
        ("min_int", lift Interval.Dom.min (AbsInt @-> AbsInt @-> Ret AbsInt));
        ("undefined_int", fun _ -> V_int Interval.Dom.top);
        ("undefined_nat", fun _ -> V_int Interval.Dom.top);
        ("undefined_range", fun _ -> V_int Interval.Dom.top);
        ("undefined_unit", fun _ -> V_unit);
        ("undefined_bool", fun _ -> V_top);
        ("undefined_string", fun _ -> V_string "");
        ( "undefined_bitvector",
          fun args ->
            match args with
            | [n] -> (
                match concrete_int n with
                | Some n ->
                    let zeros = List.init (Z.to_int n) (fun _ -> Bit.B0) in
                    bitvector_of_bits zeros
                | None -> V_top
              )
            | _ -> V_top
        );
        ( "undefined_vector",
          fun args ->
            match args with
            | [n; elem] -> (
                match concrete_int n with Some n -> V_vector (List.init (Z.to_int n) (fun _ -> elem)) | None -> V_top
              )
            | _ -> V_top
        );
        ("undefined_list", fun _ -> V_list []);
        ("get_slice_int", lift (curry3 Sail_lib.get_slice_int) (Int @-> Int @-> Int @-> Ret BV));
        ("add_vec_int", lift (curry Sail_lib.add_vec_int) (BV @-> Int @-> Ret BV));
        ("sub_vec_int", lift (curry Sail_lib.sub_vec_int) (BV @-> Int @-> Ret BV));
        ("valid_hex_bits", lift (curry Sail_lib.valid_hex_bits) (Int @-> String @-> Ret Bool));
        ("parse_dec_bits", lift (curry Sail_lib.parse_dec_bits) (Int @-> String @-> Ret BV));
        ("parse_hex_bits", lift (curry Sail_lib.parse_hex_bits) (Int @-> String @-> Ret BV));
        ("slice_inc", lift (curry3 Sail_lib.slice_inc) (BV @-> Int @-> Int @-> Ret BV));
        ("eq_bool", lift ( = ) (Bool @-> Bool @-> Ret Bool));
        ("to_real", lift Sail_lib.to_real (Int @-> Ret Real));
        ("random_real", fun _ -> V_top);
        ("round_down", lift Sail_lib.round_down (Real @-> Ret Int));
        ("round_up", lift Sail_lib.round_up (Real @-> Ret Int));
        ("sqrt_real", lift Sail_lib.sqrt_real (Real @-> Ret Real));
        ("abs_real", lift Sail_lib.abs_real (Real @-> Ret Real));
        ("negate_real", lift Sail_lib.negate_real (Real @-> Ret Real));
        ("neg_real", lift Sail_lib.neg_real (Real @-> Ret Real));
        ("add_real", lift (curry Sail_lib.add_real) (Real @-> Real @-> Ret Real));
        ("sub_real", lift (curry Sail_lib.sub_real) (Real @-> Real @-> Ret Real));
        ("mult_real", lift (curry Sail_lib.mult_real) (Real @-> Real @-> Ret Real));
        ("div_real", lift (curry Sail_lib.div_real) (Real @-> Real @-> Ret Real));
        ("quotient_real", lift (curry Sail_lib.quotient_real) (Real @-> Real @-> Ret Real));
        ("eq_real", lift (curry Sail_lib.eq_real) (Real @-> Real @-> Ret Bool));
        ("lt_real", lift (curry Sail_lib.lt_real) (Real @-> Real @-> Ret Bool));
        ("gt_real", lift (curry Sail_lib.gt_real) (Real @-> Real @-> Ret Bool));
        ("lteq_real", lift (curry Sail_lib.lteq_real) (Real @-> Real @-> Ret Bool));
        ("gteq_real", lift (curry Sail_lib.gteq_real) (Real @-> Real @-> Ret Bool));
        ("arith_shiftr", lift (fun bs n -> Sail_lib.arith_shiftr (bs, n)) (BV @-> Int @-> Ret BV));
        ( "set_slice",
          fun args ->
            match args with
            | [_out_len; _slice_len; out; n; slice] -> (
                match (concrete_bits out, concrete_int n, concrete_bits slice) with
                | Some out_bs, Some n, Some slice_bs ->
                    bitvector_of_bits
                      (Sail_lib.set_slice
                         (Z.of_int (List.length out_bs), Z.of_int (List.length slice_bs), out_bs, n, slice_bs)
                      )
                | _ -> V_top
              )
            | _ -> V_top
        );
        ( "print_real",
          fun args ->
            match args with
            | [V_string msg; r] ->
                Value.output_endline (msg ^ string_of_value r);
                V_unit
            | _ -> V_unit
        );
        ("cycle_count", lift Sail_lib.cycle_count (Unit @-> Ret Unit));
        ("get_cycle_count", fun _ -> v_int_concrete (Sail_lib.get_cycle_count ()));
        ("read_ram", lift (curry4 Sail_lib.read_ram) (Int @-> Int @-> BV @-> BV @-> Ret BV));
        ("write_ram", lift (curry5 Sail_lib.write_ram) (Int @-> Int @-> BV @-> BV @-> BV @-> Ret Bool));
        ("emulator_read_mem", lift (curry3 Sail_lib.emulator_read_mem) (Int @-> BV @-> Int @-> Ret BV));
        ("emulator_read_mem_ifetch", lift (curry3 Sail_lib.emulator_read_mem_ifetch) (Int @-> BV @-> Int @-> Ret BV));
        ( "emulator_read_mem_exclusive",
          lift (curry3 Sail_lib.emulator_read_mem_exclusive) (Int @-> BV @-> Int @-> Ret BV)
        );
        ("emulator_write_mem", lift (curry4 Sail_lib.emulator_write_mem) (Int @-> BV @-> Int @-> BV @-> Ret Bool));
        ( "emulator_write_mem_exclusive",
          lift (curry4 Sail_lib.emulator_write_mem_exclusive) (Int @-> BV @-> Int @-> BV @-> Ret Bool)
        );
        ("emulator_read_tag", lift (curry Sail_lib.emulator_read_tag) (Int @-> BV @-> Ret Bool));
        ("emulator_write_tag", lift (curry3 Sail_lib.emulator_write_tag) (Int @-> BV @-> Bool @-> Ret Unit));
        ("monomorphize", function [v] -> v | _ -> V_top);
      ]
end

let fallthrough () =
  let open Type_check in
  let open Type_error in
  try
    let env = initial_env |> Env.add_scattered_variant (mk_id "exception") [] in
    check_case env exc_typ
      (mk_pexp (Pat_exp (mk_pat (P_id (mk_id "exn")), mk_exp (E_throw (mk_exp (E_id (mk_id "exn")))))))
      unit_typ
    |> Option.get
  with Type_error (l, err) -> Reporting.unreachable l __POS__ (fst (string_of_type_error err))

module Tannot = struct
  open Extraction.TypeAnnot.Types

  type t = Type_check.tannot

  let get_type tannot =
    let typ = Type_check.typ_of_tannot tannot in
    typ

  let get_id_type (tannot : t) id =
    (* Synthesized expressions (from [desugar_for]/[desugar_loop]) carry an
       empty type annotation; treat those as local variables, matching the
       common case for a freshly-bound loop / let id. *)
    if Type_check.is_empty_tannot tannot then Local_variable
    else (
      let env = Type_check.env_of_tannot tannot in
      match Type_check.Env.lookup_id id env with
      | Register _ -> Global_register
      | Local _ | Unbound _ -> Local_variable
      | Enum _ -> Enum_member
    )

  let get_split tannot =
    let env = Type_check.env_of_tannot tannot in
    let typ = Type_check.typ_of_tannot tannot in
    match Type_check.destruct_vector env typ with
    | Some (Nexp_aux (Nexp_constant n, _), _) -> Split n
    | _ -> (
        match Type_check.destruct_bitvector env typ with
        | Some (Nexp_aux (Nexp_constant n, _)) -> Split n
        | _ -> No_split
      )

  let is_bitvector tannot = is_bitvector_typ (Type_check.typ_of_tannot tannot)

  let annotate l attr tannot = Type_check.map_uannot (add_attribute l attr None) tannot

  let fallthrough () = fallthrough ()
end

module Make (Lattice : SAIL_VALUE) = struct
  module B = Extraction.ZAst.ExpBuilder (Tannot)

  module Zinterp = Extraction.ZAst.Make (Tannot) (B) (Lattice)

  let zexp_aux_parent = function
    | Z_single (p, _)
    | Z_return p
    | Z_inline (p, _)
    | Z_exit p
    | Z_pair_1 (p, _, _)
    | Z_pair_2 (p, _, _)
    | Z_list (p, _, _, _)
    | Z_app (p, _, _, _)
    | Z_block (p, _, _)
    | Z_if_cond (p, _, _)
    | Z_if_then (p, _, _)
    | Z_if_else (p, _, _)
    | Z_match_head (p, _, _, _)
    | Z_match_arms_guard (p, _, _, _, _, _, _, _, _)
    | Z_match_arms_body (p, _, _, _, _, _, _, _)
    | Z_assign_left (p, _, _, _, _)
    | Z_assign_right (p, _, _)
    | Z_var_left (p, _, _, _, _, _)
    | Z_var_right (p, _, _, _)
    | Z_var_body (p, _, _, _)
    | Z_struct (p, _, _, _, _)
    | Z_struct_update_base (p, _, _)
    | Z_struct_update (p, _, _, _, _, _) ->
        p

  module Pretty = struct
    open PPrint
    open Pretty_print_sail

    let prepend c cs = c ^^ hardline ^^ twice space ^^ cs

    let truncate_str n s = if String.length s > n + 3 then String.sub s 0 n ^ "..." else s

    let hole n = string Util.(clear @@ magenta @@ string_of_int n)

    let doc_exp exp = string Util.(clear @@ blue @@ truncate_str 10 (string_of_exp exp))

    let doc_residual ?(show_partial = false) (r : Zinterp.R.t) =
      let p_doc =
        if show_partial then hardline ^^ Pretty_print_sail.doc_exp (Type_check.strip_exp (snd r)) else empty
      in
      let v = fst r in
      let this_doc =
        match v.this with
        | None -> string Util.(clear @@ green ".")
        | Some v -> string Util.(clear @@ green @@ Lattice.string_of_value v)
      in
      let exn_doc =
        match v.exn with
        | None -> string Util.(clear @@ red ".")
        | Some v -> string Util.(clear @@ red @@ Lattice.string_of_value v)
      in
      this_doc ^^ space ^^ exn_doc ^^ space ^^ string Util.(clear @@ yellow @@ string_of_bool v.eff) ^^ p_doc

    let doc_pair c l r =
      match c with
      | Assert -> string "assert" ^^ parens (l ^^ comma ^^ space ^^ r)
      | Vector_append -> separate space [l; char '@'; r]
      | Cons -> separate space [l; string "::"; r]

    let doc_list c docs =
      let l, r =
        match c with
        | List -> (string "[|", string "|]")
        | Tuple -> (char '(', char ')')
        | Vector | Bitvector -> (char '[', char ']')
      in
      l ^^ separate (comma ^^ space) docs ^^ r

    let doc_match c head_doc body =
      match c with
      | Try ->
          separate space [string "try"; head_doc; string "catch"]
          ^^ space
          ^^ group (lbrace ^^ break 1 ^^ nest 4 body ^^ break 1 ^^ rbrace)
      | Match | Letbind | Internal_plet ->
          string "match" ^^ space ^^ head_doc ^^ space ^^ group (lbrace ^^ break 1 ^^ nest 4 body ^^ break 1 ^^ rbrace)

    let doc_ite idoc tdoc edoc = separate space [string "if"; idoc; string "then"; tdoc; string "else"; edoc]

    let docs (zexp : Zinterp.t) =
      let s = Stack.create () in
      let rec go n = function
        | Z_top -> ()
        | Z_aux (aux, _) ->
            let child =
              match aux with
              | Z_single (parent, c) -> (
                  match c with
                  | Field fld -> hole n ^^ dot ^^ doc_id fld
                  | Internal_assume nc -> separate space [string "internal_assume"; doc_nc nc; string "in"; hole n]
                  | Internal_return -> string "internal_return" ^^ space ^^ hole n
                  | Throw -> string "throw" ^^ space ^^ hole n
                  | Typ typ -> separate space [hole n; colon; doc_typ typ]
                )
              | Z_return parent -> string "return" ^^ space ^^ hole n
              | Z_exit parent -> string "exit" ^^ space ^^ hole n
              | Z_pair_1 (parent, c, exp) -> doc_pair c (hole n) (doc_exp exp)
              | Z_pair_2 (parent, c, r) -> doc_pair c (doc_residual r) (hole n)
              | Z_list (parent, c, rs, exps) ->
                  doc_list c (List.rev_map doc_residual rs @ [hole n] @ List.map doc_exp exps)
              | Z_app (parent, id, rs, exps) ->
                  doc_id id
                  ^^ parens (separate (comma ^^ space) (List.rev_map doc_residual rs @ [hole n] @ List.map doc_exp exps))
              | Z_block (parent, rs, exps) ->
                  group
                    (lbrace
                    ^^ nest 4
                         (break 1
                         ^^ separate (semi ^^ break 1) (List.rev_map doc_residual rs @ [hole n] @ List.map doc_exp exps)
                         )
                    ^^ break 1 ^^ rbrace
                    )
              | Z_inline (parent, _) -> string "internal_inlined" ^^ space ^^ hole n
              | Z_if_cond (_, t, e) -> doc_ite (hole n) (doc_exp t) (doc_exp e)
              | Z_if_then (_, (_, i), e) -> doc_ite (doc_residual i) (hole n) (doc_exp e)
              | Z_if_else (_, i, (_, t)) -> doc_ite (doc_residual i) (doc_residual t) (hole n)
              | Z_match_head (_, c, r_arms, arms) -> doc_match c (hole n) (string "...")
              | Z_match_arms_guard (_, c, _, (_, head), r_arms, pat, _, body, arms) ->
                  doc_match c (doc_residual head)
                    (concat
                       (List.rev_map
                          (fun (((_, pat), guard_opt), body) ->
                            separate space [doc_pat (Type_check.strip_pat pat); string "=>"; string "..."]
                            ^^ semi ^^ break 1
                          )
                          r_arms
                       )
                    ^^ separate space
                         [doc_pat (Type_check.strip_pat pat); string "if"; hole n; string "=>"; doc_exp body]
                    ^^ semi
                    ^^ match arms with None -> empty | Some _ -> break 1 ^^ string "..."
                    )
              | Z_match_arms_body (_, c, _, (_, head), r_arms, pat, guard_opt, arms) ->
                  doc_match c (doc_residual head)
                    (concat
                       (List.rev_map
                          (fun (((_, pat), guard_opt), body) ->
                            separate space [doc_pat (Type_check.strip_pat pat); string "=>"; string "..."]
                            ^^ semi ^^ break 1
                          )
                          r_arms
                       )
                    ^^ separate space [doc_pat (Type_check.strip_pat pat); string "=>"; hole n]
                    ^^ semi
                    ^^ match arms with None -> empty | Some _ -> break 1 ^^ string "..."
                    )
              | Z_assign_left _ | Z_assign_right _ | Z_var_left _ | Z_var_right _ | Z_var_body _ -> string "?"
              | Z_struct _ | Z_struct_update_base _ | Z_struct_update _ -> string "?"
            in
            Stack.push child s;
            go (n + 1) (zexp_aux_parent aux)
      in
      go 0 zexp;
      List.of_seq @@ Stack.to_seq s
  end

  type gstate = {
    primops : (Lattice.t list -> Lattice.t) StringMap.t;
    fundefs : Type_check.tannot fundef Bindings.t;
    letbinds : (Type_check.tannot pat * Type_check.tannot exp * Type_check.Env.t def_annot) list;
    registers : (id * typ * Type_check.tannot exp option) list;
    typecheck_env : Type_check.Env.t;
  }

  let initial_gstate ~typecheck_env ~ast =
    let gstate =
      { primops = Lattice.initial_primops; fundefs = Bindings.empty; letbinds = []; registers = []; typecheck_env }
    in
    let add_def gstate = function
      | DEF_aux (DEF_fundef fdef, _) -> { gstate with fundefs = Bindings.add (id_of_fundef fdef) fdef gstate.fundefs }
      | DEF_aux (DEF_let (pat, exp), annot) -> { gstate with letbinds = (pat, exp, annot) :: gstate.letbinds }
      | DEF_aux (DEF_register (DEC_aux (DEC_reg (typ, id, init), _)), _) ->
          { gstate with registers = (id, typ, init) :: gstate.registers }
      | _ -> gstate
    in
    let gstate = List.fold_left add_def gstate ast.defs in
    let gstate = { gstate with letbinds = List.rev gstate.letbinds; registers = List.rev gstate.registers } in
    gstate

  type partial_state = {
    ctx : Zinterp.t;
    state : Zinterp.R.state;
    focus : (Tannot.t exp, Zinterp.R.t) Extraction.Datatypes.sum;
  }

  let partial_state_ctx p = p.ctx

  let dest_focus f g = function
    | { focus = Extraction.Datatypes.Coq_inl l; _ } -> f l
    | { focus = Extraction.Datatypes.Coq_inr r; _ } -> g r

  let string_of_focus p =
    let open Pretty_print_sail in
    dest_focus (fun exp -> doc_exp (Type_check.strip_exp exp)) (fun r -> Pretty.doc_residual ~show_partial:true r) p
    |> Document.to_string

  let from_exp exp = { ctx = Z_top; state = Zinterp.R.empty; focus = Extraction.Datatypes.Coq_inl exp }

  let unaux_id = function Id_aux (id, _) -> id

  let exp_of_value v = E_aux (E_internal_value v, (Parse_ast.Unknown, Type_check.empty_tannot))

  let arms_of_fundef (FD_aux (FD_function (_, _, funcls), annot)) =
    let destruct_pexp = function
      | Pat_aux (Pat_exp (pat, exp), _) -> ((pat, None), exp)
      | Pat_aux (Pat_when (pat, guard, exp), _) -> ((pat, Some guard), exp)
    in
    let pexp_of_funcl (FCL_aux (FCL_funcl (_, pexp), _)) = destruct_pexp pexp in
    (List.map pexp_of_funcl funcls, annot)

  let is_finished { ctx; state = _; focus } =
    match (ctx, focus) with Z_top, Extraction.Datatypes.Coq_inr (v, _) -> Some v | _ -> None

  (* Desugar [foreach (v from F to T by A in ord) body] into a single iteration
   peel:

     if cmp(F, T) then ()
     else let v = F in { body; for v from op(v, A) to T by A ord body }

   where [cmp] is [gt_int] (resp. [lt_int]) and [op] is [add_int] (resp.
   [sub_int]) for [Ord_inc] (resp. [Ord_dec]). Each step of the partial
   evaluator processes one iteration; the recursive E_for is itself desugared
   on the next step. When the bounds are concrete, this terminates after
   [|T - F| / A + 1] iterations; with non-concrete bounds the abstract [if]
   cannot decide and evaluation gets stuck (returning the residual), matching
   what we already do for any unfoldable conditional.

   The recursion sits *inside* the [let v = F] so the next iteration's from
   expression can be [op(v, A)], a reference to the just-bound loop variable.
   Building it from the previous from expression instead ([op(F, A)]) makes
   the counter a syntactic chain that grows by one [op] per iteration and is
   re-evaluated from scratch on every unfold — quadratic in the trip count,
   and it embeds an O(iteration)-sized expression in each iteration's
   residual. *)
  let unknown_annot = (Parse_ast.Unknown, Type_check.empty_tannot)
  let mk_e e = E_aux (e, unknown_annot)
  let mk_p p = P_aux (p, unknown_annot)

  let desugar_for var from_e to_e amount_e ord body =
    let cmp_id, op_id =
      match ord with
      | Ord_aux (Ord_inc, _) -> (mk_id "gt_int", mk_id "add_int")
      | Ord_aux (Ord_dec, _) -> (mk_id "lt_int", mk_id "sub_int")
    in
    let cmp = mk_e (E_app (cmp_id, [from_e; to_e])) in
    let next_from = mk_e (E_app (op_id, [mk_e (E_id var); amount_e])) in
    let recurse = mk_e (E_for (var, next_from, to_e, amount_e, ord, body)) in
    let else_branch = mk_e (E_let (mk_p (P_id var), from_e, mk_e (E_block [body; recurse]))) in
    let then_branch = mk_e (E_lit (mk_lit L_unit)) in
    mk_e (E_if (cmp, then_branch, else_branch))

  (* Desugar [while cond do body] / [repeat body until cond] into

     while cond do body => if cond then { body; while cond do body } else ()
     repeat body until cond => { body; if cond then () else repeat body until cond }

   Same iteration-by-iteration unfold story as [E_for]. *)
  let desugar_loop kind measure cond body =
    match kind with
    | While ->
        let recurse = mk_e (E_loop (While, measure, cond, body)) in
        let then_branch = mk_e (E_block [body; recurse]) in
        let else_branch = mk_e (E_lit (mk_lit L_unit)) in
        mk_e (E_if (cond, then_branch, else_branch))
    | Until ->
        let recurse = mk_e (E_loop (Until, measure, cond, body)) in
        let then_branch = mk_e (E_lit (mk_lit L_unit)) in
        let else_branch = recurse in
        mk_e (E_block [body; mk_e (E_if (cond, then_branch, else_branch))])

  let preprocess_focus p =
    match p.focus with
    | Extraction.Datatypes.Coq_inl (E_aux (E_for (var, from_e, to_e, amount_e, ord, body), _)) ->
        { p with focus = Extraction.Datatypes.Coq_inl (desugar_for var from_e to_e amount_e ord body) }
    | Extraction.Datatypes.Coq_inl (E_aux (E_loop (kind, measure, cond, body), _)) ->
        { p with focus = Extraction.Datatypes.Coq_inl (desugar_loop kind measure cond body) }
    | _ -> p

  let mk_interpreter ~inlining gstate =
    let open Zinterp.Monad in
    let stack = Stack.create () in

    let step p =
      let rec go state = function
        | Pure ((ctx, state), focus) -> (
            match is_finished { ctx; state; focus } with
            | Some v -> (
                match Stack.pop_opt stack with
                | Some cont -> (
                    let state = Zinterp.R.pop_scope state in
                    match cont (Return_value v) with
                    | Pure ((ctx', _), focus') -> go state (Pure ((ctx', state), focus'))
                    | other -> go state other
                  )
                | None -> { ctx; state; focus }
              )
            | None -> { ctx; state; focus }
          )
        | Early_return (v, _) -> (
            match Stack.pop_opt stack with
            | Some cont -> (
                let state = Zinterp.R.pop_scope state in
                match cont (Return_value v) with
                | Pure ((ctx', _), focus') -> go state (Pure ((ctx', state), focus'))
                | other -> go state other
              )
            | None ->
                (* If we see [E_return e] at the very top of a REPL
                 expression, treat it as [e]
                 [e]. *)
                {
                  ctx = Z_top;
                  state;
                  focus =
                    Extraction.Datatypes.Coq_inr
                      (v, E_aux (E_lit (mk_lit L_unit), (Parse_ast.Unknown, Type_check.empty_tannot)));
                }
          )
        | Exit (v, _) ->
            Stack.clear stack;
            {
              ctx = Z_top;
              state;
              focus =
                Extraction.Datatypes.Coq_inr
                  ( v,
                    E_aux
                      ( E_exit (E_aux (E_lit (mk_lit L_unit), (Parse_ast.Unknown, Type_check.empty_tannot))),
                        (Parse_ast.Unknown, Type_check.empty_tannot)
                      )
                  );
            }
        | Call (id, args, cont) -> (
            match Util.option_all (List.map (fun r -> r.Zinterp.R.this) args) with
            | Some args' ->
                let has_fundef = Bindings.mem id gstate.fundefs in
                let is_extern = Type_check.Env.is_extern id gstate.typecheck_env "interpreter" in
                if has_fundef && (not is_extern) && Type_check.Env.is_outcome id gstate.typecheck_env then (
                  let fdef = Bindings.find id gstate.fundefs in
                  let arg = if List.length args != 1 then Lattice.mk_tuple args' else List.hd args' in
                  let arms, annot = arms_of_fundef fdef in
                  Stack.push cont stack;
                  {
                    ctx = Z_aux (Z_match_head (Z_top, Match, [], Some arms), annot);
                    state = Zinterp.R.push_scope state;
                    focus =
                      Extraction.Datatypes.Coq_inr
                        ({ this = Some arg; exn = None; eff = false }, B.mk_id annot (mk_id "funarg#"));
                  }
                )
                else if Type_check.Env.is_outcome id gstate.typecheck_env then
                  go state
                    (cont (Return_value { this = Some (Lattice.mk_ctor (unaux_id id) args'); exn = None; eff = false }))
                else if Type_check.Env.is_union_constructor id gstate.typecheck_env then
                  go state
                    (cont (Return_value { this = Some (Lattice.mk_ctor (unaux_id id) args'); exn = None; eff = false }))
                else if Type_check.Env.is_extern id gstate.typecheck_env "interpreter" then (
                  let extern = Type_check.Env.get_extern id gstate.typecheck_env "interpreter" in
                  if extern = "reg_deref" then (
                    let v =
                      match args' with
                      | [arg] -> (
                          match Lattice.concrete_ref arg with
                          | Some reg_id_aux -> (
                              let key = Id_aux (reg_id_aux, Parse_ast.Unknown) in
                              match Extraction.IdUtil.IdMap.find key state.Zinterp.R.registers with
                              | Some v -> v
                              | None -> Lattice.top
                            )
                          | None -> Lattice.top
                        )
                      | _ -> Lattice.top
                    in
                    go state (cont (Return_value { this = Some v; exn = None; eff = false }))
                  )
                  else (
                    let is_pure = Type_check.Env.is_pure_extern id gstate.typecheck_env in
                    match StringMap.find_opt extern gstate.primops with
                    | Some op -> go state (cont (Return_value { this = Some (op args'); exn = None; eff = not is_pure }))
                    | None -> failwith ("no primop: " ^ extern)
                  )
                )
                else (
                  let arg = if List.length args != 1 then Lattice.mk_tuple args' else List.hd args' in
                  let fdef = match Bindings.find_opt id gstate.fundefs with Some fdef -> Some fdef | None -> None in
                  match fdef with
                  | None -> (
                      match StringMap.find_opt (string_of_id id) gstate.primops with
                      | Some op -> go state (cont (Return_value { this = Some (op args'); exn = None; eff = false }))
                      | None -> failwith ("unknown function: " ^ string_of_id id)
                    )
                  | Some fdef ->
                      let arms, annot = arms_of_fundef fdef in
                      if inlining then go state (cont (Return_inlined arms))
                      else (
                        Stack.push cont stack;
                        {
                          ctx = Z_aux (Z_match_head (Z_top, Match, [], Some arms), annot);
                          state = Zinterp.R.push_scope state;
                          focus =
                            Extraction.Datatypes.Coq_inr
                              ({ this = Some arg; exn = None; eff = false }, B.mk_id annot (mk_id "funarg#"));
                        }
                      )
                )
            | None -> failwith "bad call"
          )
        | Get_config (_, cont) -> failwith "get_config"
        | Runtime_type_error l -> raise (Reporting.err_general l "Type error")
        | Get_undefined (_, cont) -> go state (cont { this = Some Lattice.top; exn = None; eff = false })
      in
      let p = preprocess_focus p in
      go p.state (Zinterp.step p.ctx p.state p.focus)
    in
    step

  (* Walk the partial evaluator forward on a single expression to a final value.
   Used by [from_exp_with_globals] to pre-evaluate each top-level [let] RHS
   into an abstract value we can store in the initial state's locals.

   A non-terminating assignment RHS will hang here. This is just considered a
   user-error in the written Sail. *)
  let evaluate_to_value ?(state = Zinterp.R.empty) step exp =
    let rec loop ps = match is_finished ps with Some v -> (v, ps.state) | None -> loop (step ps) in
    loop { ctx = Z_top; state; focus = Extraction.Datatypes.Coq_inl exp }

  module Matching = Lattice.Matching (Tannot)

  let bindings_of_match pat (v : Lattice.t) =
    let mr = Matching.pattern_match pat v in
    match mr with
    | Extraction.PatternMatch.Matched b | Extraction.PatternMatch.MaybeMatched b ->
        let collapsed = Extraction.IdUtil.IdMap.map Lattice.complete b in
        Some collapsed
    | Extraction.PatternMatch.Unmatched -> None

  (* Pre-evaluate every top-level [let] in the program into the
     initial state's [toplevel_lets]. RHSs that can't be reduced to a
     fully-known abstract value (e.g. because they need a primop we
     haven't bound yet) are silently skipped — the user will get a
     "Type error" when they later try to read the unbound name, which
     mirrors the prior behaviour. *)
  let from_exp_with_globals gstate exp =
    let step = mk_interpreter ~inlining:false gstate in
    let merge_toplevel_lets s b =
      Extraction.IdUtil.IdMap.fold
        (fun id v s -> { s with Zinterp.R.toplevel_lets = Extraction.IdUtil.IdMap.add id v s.Zinterp.R.toplevel_lets })
        b s
    in
    let state =
      List.fold_left
        (fun s (pat, lb_exp, _) ->
          let rval, _ = evaluate_to_value ~state:s step lb_exp in
          match rval.Zinterp.R.this with
          | Some v -> (
              match bindings_of_match pat v with Some b -> merge_toplevel_lets s b | None -> s
            )
          | None -> s
        )
        Zinterp.R.empty gstate.letbinds
    in
    (* Top-level register declarations live separately in state.registers, so
       subsequent E_assign writes route back to the right side of the state.
       If a register has no initial value (or we can't evaluate it concretely),
       we seed it with [V_top], or a more specific symbolic unknown if possible. *)
    let rec default_for_typ typ =
      match Type_check.destruct_vector gstate.typecheck_env typ with
      | Some (Nexp_aux (Nexp_constant n, _), _) -> Lattice.mk_vector (List.init (Z.to_int n) (fun _ -> Lattice.top))
      | _ -> (
          match Type_check.destruct_bitvector gstate.typecheck_env typ with
          | Some (Nexp_aux (Nexp_constant n, _)) -> Lattice.bitvector_of_bits (List.init (Z.to_int n) (fun _ -> Bit.B0))
          | _ -> (
              (* A register typed with a bitfield struct is really a record
               with a single [bits] field carrying the underlying bitvector.
               Seed [bits] to all-zeros (matching the [bits(N)] case) so
               subsequent [r.bits[hi..lo] = e] writes can update concrete
               state; partial-eval would otherwise see [r.bits] as [V_top]. *)
              match typ with
              | Typ_aux (Typ_id id, _) when Type_check.Env.is_bitfield id gstate.typecheck_env ->
                  let underlying, _ = Type_check.Env.get_bitfield id gstate.typecheck_env in
                  let bits_v = default_for_typ underlying in
                  Lattice.mk_record [(Id "bits", bits_v)]
              | _ -> Lattice.top
            )
        )
    in
    let state =
      List.fold_left
        (fun s (id, typ, init_opt) ->
          let v =
            match init_opt with
            | None -> default_for_typ typ
            | Some init -> (
                let rval, _ = evaluate_to_value ~state:s step init in
                match rval.Zinterp.R.this with Some v -> v | None -> default_for_typ typ
              )
          in
          { s with Zinterp.R.registers = Extraction.IdUtil.IdMap.add id v s.Zinterp.R.registers }
        )
        state gstate.registers
    in
    { ctx = Z_top; state; focus = Extraction.Datatypes.Coq_inl exp }
end
