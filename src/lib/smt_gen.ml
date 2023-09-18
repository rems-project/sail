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
(*  Copyright (c) 2013-2023                                                 *)
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

open Ast_util
open Jib
open Jib_util
open Smt_exp

let zencode_upper_id id = Util.zencode_upper_string (string_of_id id)
let zencode_id id = Util.zencode_string (string_of_id id)

let zencode_uid (id, ctyps) =
  match ctyps with
  | [] -> Util.zencode_string (string_of_id id)
  | _ -> Util.zencode_string (string_of_id id ^ "#" ^ Util.string_of_list "_" string_of_ctyp ctyps)

(* [required_width n] is the required number of bits to losslessly
   represent an integer n *)
let required_width n =
  let rec required_width' n =
    if Big_int.equal n Big_int.zero then 1 else 1 + required_width' (Big_int.shift_right n 1)
  in
  required_width' (Big_int.abs n)

(* Generate SMT definitions in a writer monad that keeps tracks of any
   overflow checks needed. *)

type checks = { overflows : smt_exp list; strings_used : bool; reals_used : bool }

let empty_checks = { overflows = []; strings_used = false; reals_used = false }

let append_checks c1 c2 =
  {
    overflows = c1.overflows @ c2.overflows;
    strings_used = c1.strings_used || c2.strings_used;
    reals_used = c1.reals_used || c2.reals_used;
  }

type 'a check_writer_state = { value : 'a; checks : checks }

type 'a check_writer = Parse_ast.l -> 'a check_writer_state

let return x _ = { value = x; checks = empty_checks }

let current_location l = { value = l; checks = empty_checks }

let bind m f l =
  let state = m l in
  let state' = f state.value l in
  { value = state'.value; checks = append_checks state.checks state'.checks }

let fmap f m l =
  let state = m l in
  let value = f state.value in
  { value; checks = state.checks }

let ( let* ) = bind

let ( let+ ) m f = fmap f m

let rec mapM f = function
  | [] -> return []
  | x :: xs ->
      let* x = f x in
      let* xs = mapM f xs in
      return (x :: xs)

let run m l =
  let state = m l in
  (state.value, state.checks)

let overflow_check check (_ : Parse_ast.l) = { value = (); checks = { empty_checks with overflows = [check] } }

let string_used (_ : Parse_ast.l) = { value = (); checks = { empty_checks with strings_used = true } }

let real_used (_ : Parse_ast.l) = { value = (); checks = { empty_checks with reals_used = true } }

(* [signed_size n m exp] takes a smt expression assumed to be a
   integer (signed bitvector) of length m and forces it to be length n
   by either sign extending it or truncating it as required *)
let signed_size ?(checked = true) ~into:n ~from:m smt =
  if n = m then return smt
  else if n > m then return (SignExtend (n, n - m, smt))
  else (
    let check =
      (* If the top bit of the truncated number is one *)
      Ite
        ( Fn ("=", [Extract (n - 1, n - 1, smt); Bitvec_lit [Sail2_values.B1]]),
          (* Then we have an overflow, unless all bits we truncated were also one *)
          Fn ("not", [Fn ("=", [Extract (m - 1, n, smt); bvones (m - n)])]),
          (* Otherwise, all the top bits must be zero *)
          Fn ("not", [Fn ("=", [Extract (m - 1, n, smt); bvzero (m - n)])])
        )
    in
    let* _ = if checked then overflow_check check else return () in
    return (Extract (n - 1, 0, smt))
  )

(* [unsigned_size n m exp] is much like signed_size, but it assumes
   that the bitvector is unsigned, so it either zero extends or
   truncates as required. *)
let unsigned_size ?max_value ?(checked = true) ~into:n ~from:m smt =
  if n = m then return smt
  else if n > m then return (Fn ("concat", [bvzero (n - m); smt]))
  else
    (* Ensure we don't overwrite any high bits when truncating *)
    let* _ =
      if checked then overflow_check (Fn ("not", [Fn ("=", [Extract (m - 1, n, smt); bvzero (m - n)])])) else return ()
    in
    return (Extract (n - 1, 0, smt))

(* We often need to create a SMT bitvector of a length sz with integer
   value x. [bvpint sz x] does this for positive integers, and [bvint sz x]
   does this for all integers. It's quite awkward because we
   don't have a very good way to get the binary representation of
   either an OCaml integer or a big integer. *)
let bvpint ?(loc = Parse_ast.Unknown) sz x =
  let open Sail2_values in
  if Big_int.less_equal Big_int.zero x && Big_int.less_equal x (Big_int.of_int max_int) then (
    let x = Big_int.to_int x in
    match Printf.sprintf "%X" x |> Util.string_to_list |> List.map nibble_of_char |> Util.option_all with
    | Some nibbles ->
        let bin = List.map (fun (a, b, c, d) -> [a; b; c; d]) nibbles |> List.concat in
        let _, bin = Util.take_drop (function B0 -> true | _ -> false) bin in
        let padding = List.init (sz - List.length bin) (fun _ -> B0) in
        Bitvec_lit (padding @ bin)
    | None -> assert false
  )
  else if Big_int.greater x (Big_int.of_int max_int) then (
    let y = ref x in
    let bin = ref [] in
    while not (Big_int.equal !y Big_int.zero) do
      let q, m = Big_int.quomod !y (Big_int.of_int 2) in
      bin := (if Big_int.equal m Big_int.zero then B0 else B1) :: !bin;
      y := q
    done;
    let padding_size = sz - List.length !bin in
    if padding_size < 0 then
      raise
        (Reporting.err_general loc
           (Printf.sprintf "Could not create a %d-bit integer with value %s.\nTry increasing the maximum integer size."
              sz (Big_int.to_string x)
           )
        );
    let padding = List.init padding_size (fun _ -> B0) in
    Bitvec_lit (padding @ !bin)
  )
  else Reporting.unreachable loc __POS__ "bvpint called on non-positive integer"

let bvint sz x =
  if Big_int.less x Big_int.zero then
    Fn ("bvadd", [Fn ("bvnot", [bvpint sz (Big_int.abs x)]); bvpint sz (Big_int.of_int 1)])
  else bvpint sz x

(* [required_width n] is the required number of bits to losslessly
   represent an integer n *)
let required_width n =
  let rec required_width' n =
    if Big_int.equal n Big_int.zero then 1 else 1 + required_width' (Big_int.shift_right n 1)
  in
  required_width' (Big_int.abs n)

module type CONFIG = sig
  val max_unknown_integer_width : int
  val max_unknown_bitvector_width : int
  val union_ctyp_classify : ctyp -> bool
end

module type PRIMOP_GEN = sig
  val print_bits : Parse_ast.l -> ctyp -> string
  val string_of_bits : Parse_ast.l -> ctyp -> string
  val dec_str : Parse_ast.l -> ctyp -> string
  val hex_str : Parse_ast.l -> ctyp -> string
  val hex_str_upper : Parse_ast.l -> ctyp -> string
  val count_leading_zeros : Parse_ast.l -> int -> string
  val fvector_store : Parse_ast.l -> int -> ctyp -> string
  val is_empty : Parse_ast.l -> ctyp -> string
  val hd : Parse_ast.l -> ctyp -> string
  val tl : Parse_ast.l -> ctyp -> string
end

let builtin_type_error fn cvals ret_ctyp_opt =
  let* l = current_location in
  let args = Util.string_of_list ", " (fun cval -> string_of_ctyp (cval_ctyp cval)) cvals in
  match ret_ctyp_opt with
  | Some ret_ctyp ->
      let message = Printf.sprintf "%s : (%s) -> %s" fn args (string_of_ctyp ret_ctyp) in
      raise (Reporting.err_todo l message)
  | None -> raise (Reporting.err_todo l (Printf.sprintf "%s : (%s)" fn args))

module Make (Config : CONFIG) (Primop_gen : PRIMOP_GEN) = struct
  let lint_size = Config.max_unknown_integer_width
  let lbits_size = Config.max_unknown_bitvector_width
  let lbits_index = required_width (Big_int.of_int (lbits_size - 1))

  let int_size = function
    | CT_constant n -> required_width n
    | CT_fint sz -> sz
    | CT_lint -> lint_size
    | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Argument to int_size must be an integer type"

  let bv_size = function
    | CT_fbits sz | CT_sbits sz -> sz
    | CT_lbits -> lbits_size
    | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Argument to bv_size must be a bitvector type"

  let to_fbits ctyp bv =
    match ctyp with
    | CT_fbits n -> (n, bv)
    | CT_lbits -> (lbits_size, Fn ("contents", [bv]))
    | _ ->
        Reporting.unreachable Parse_ast.Unknown __POS__
          (Printf.sprintf "Type %s must be a bitvector in to_fbits" (string_of_ctyp ctyp))

  let literal vl ctyp =
    let open Value2 in
    match (vl, ctyp) with
    | VL_bits bv, CT_fbits n -> unsigned_size ~into:n ~from:(List.length bv) (Bitvec_lit bv)
    | VL_bool b, _ -> return (Bool_lit b)
    | VL_int n, CT_constant m -> return (bvint (required_width n) n)
    | VL_int n, CT_fint sz -> return (bvint sz n)
    | VL_int n, CT_lint -> return (bvint Config.max_unknown_integer_width n)
    | VL_bit b, CT_bit -> return (Bitvec_lit [b])
    | VL_unit, _ -> return (Enum "unit")
    | VL_string str, _ ->
        let* _ = string_used in
        return (String_lit str)
    | VL_real str, _ ->
        let* _ = real_used in
        return (if str.[0] = '-' then Fn ("-", [Real_lit (String.sub str 1 (String.length str - 1))]) else Real_lit str)
    | VL_ref str, _ -> return (Fn ("reg_ref", [String_lit str]))
    | _ ->
        let* l = current_location in
        Reporting.unreachable l __POS__
          ("Cannot translate literal to SMT: " ^ string_of_value vl ^ " : " ^ string_of_ctyp ctyp)

  let smt_cval_call op args =
    match (op, args) with
    | Bnot, [arg] -> Fn ("not", [arg])
    | Bor, [arg] -> arg
    | Bor, args -> Fn ("or", args)
    | Band, [arg] -> arg
    | Band, args -> Fn ("and", args)
    | Eq, args -> Fn ("=", args)
    | Neq, args -> Fn ("not", [Fn ("=", args)])
    | Ilt, [lhs; rhs] -> Fn ("bvslt", [lhs; rhs])
    | Ilteq, [lhs; rhs] -> Fn ("bvsle", [lhs; rhs])
    | Igt, [lhs; rhs] -> Fn ("bvsgt", [lhs; rhs])
    | Igteq, [lhs; rhs] -> Fn ("bvsge", [lhs; rhs])
    | Iadd, args -> Fn ("bvadd", args)
    | Isub, args -> Fn ("bvsub", args)
    | Bvnot, args -> Fn ("bvnot", args)
    | Bvor, args -> Fn ("bvor", args)
    | Bvand, args -> Fn ("bvand", args)
    | Bvxor, args -> Fn ("bvxor", args)
    | Bvadd, args -> Fn ("bvadd", args)
    | Bvsub, args -> Fn ("bvsub", args)
    | Concat, args -> Fn ("concat", args)
    | Zero_extend _, _ -> failwith "ZE"
    | Sign_extend _, _ -> failwith "SE"
    | Slice _, _ -> failwith "slice"
    | Sslice _, _ -> failwith "sslice"
    | Set_slice, _ -> failwith "set_slice"
    | Replicate _, _ -> failwith "replicate"
    | List_hd, [arg] -> Fn ("hd", [arg])
    | op, _ -> failwith (string_of_op op)

  let rec smt_cval cval =
    match cval_ctyp cval with
    | CT_constant n -> return (bvint (required_width n) n)
    | _ -> (
        match cval with
        | V_lit (vl, ctyp) -> literal vl ctyp
        | V_id (id, _) -> return (Var id)
        | V_call (List_hd, [arg]) ->
            let* l = current_location in
            let op = Primop_gen.hd l (cval_ctyp arg) in
            let* arg = smt_cval arg in
            return (Hd (op, arg))
        | V_call (List_tl, [arg]) ->
            let* l = current_location in
            let op = Primop_gen.tl l (cval_ctyp arg) in
            let* arg = smt_cval arg in
            return (Tl (op, arg))
        | V_call (List_is_empty, [arg]) ->
            let* l = current_location in
            let op = Primop_gen.is_empty l (cval_ctyp arg) in
            let* arg = smt_cval arg in
            return (Fn (op, [arg]))
        | V_call (op, args) ->
            let* args = mapM smt_cval args in
            return (smt_cval_call op args)
        | V_ctor_kind (union, ctor, _) ->
            let* union = smt_cval union in
            return (Fn ("not", [Tester (zencode_uid ctor, union)]))
        | V_ctor_unwrap (union, (ctor, _), _) ->
            let union_ctyp = cval_ctyp union in
            let* union = smt_cval union in
            return (Unwrap (ctor, Config.union_ctyp_classify union_ctyp, union))
        | V_field (record, field) -> begin
            match cval_ctyp record with
            | CT_struct (struct_id, _) ->
                let* record = smt_cval record in
                return (Field (struct_id, field, record))
            | _ -> failwith "Field for non-struct type"
          end
        | cval -> return (Var (Name (mk_id "UNKNOWN", -1))) (* failwith ("Unrecognised cval " ^ string_of_cval cval) *)
      )

  (* [bvzeint esz cval] (BitVector Zero Extend INTeger), takes a cval
     which must be an integer type (either CT_fint, or CT_lint), and
     produces a bitvector which is either zero extended or truncated to
     exactly esz bits. *)
  let bvzeint esz cval =
    let sz = int_size (cval_ctyp cval) in
    match cval with
    | V_lit (VL_int n, _) -> return (bvint esz n)
    | _ ->
        let* smt = smt_cval cval in
        return
          ( if esz = sz then smt
            else if esz > sz then Fn ("concat", [bvzero (esz - sz); smt])
            else Extract (esz - 1, 0, smt)
          )

  let builtin_arith fn big_int_fn padding v1 v2 ret_ctyp =
    match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
    | _, _, CT_constant c -> return (bvint (required_width c) c)
    | CT_constant c1, CT_constant c2, _ -> return (bvint (int_size ret_ctyp) (big_int_fn c1 c2))
    | ctyp1, ctyp2, _ ->
        (* To detect arithmetic overflow we can expand the input
           bitvectors to some size determined by a padding function,
           then check we don't lose precision when going back after
           performing the operation. *)
        let ret_sz = int_size ret_ctyp in
        let* smt1 = smt_cval v1 in
        let* smt2 = smt_cval v2 in
        let* padded_smt1 = signed_size ~into:(padding ret_sz) ~from:(int_size ctyp1) smt1 in
        let* padded_smt2 = signed_size ~into:(padding ret_sz) ~from:(int_size ctyp2) smt2 in
        signed_size ~into:ret_sz ~from:(padding ret_sz) (Fn (fn, [padded_smt1; padded_smt2]))

  let builtin_add_int = builtin_arith "bvadd" Big_int.add (fun x -> x + 1)
  let builtin_sub_int = builtin_arith "bvsub" Big_int.sub (fun x -> x + 1)
  let builtin_mult_int = builtin_arith "bvmul" Big_int.mul (fun x -> x * 2)

  let builtin_neg_int v ret_ctyp =
    match (cval_ctyp v, ret_ctyp) with
    | _, CT_constant c -> return (bvint (required_width c) c)
    | CT_constant c, _ -> return (bvint (int_size ret_ctyp) (Big_int.negate c))
    | ctyp, _ ->
        let open Sail2_values in
        let* smt = bind (smt_cval v) (signed_size ~into:(int_size ret_ctyp) ~from:(int_size ctyp)) in
        let* _ = overflow_check (Fn ("=", [smt; Bitvec_lit (B1 :: List.init (int_size ret_ctyp - 1) (fun _ -> B0))])) in
        return (Fn ("bvneg", [smt]))

  let builtin_abs_int v ret_ctyp =
    match (cval_ctyp v, ret_ctyp) with
    | _, CT_constant c -> return (bvint (required_width c) c)
    | CT_constant c, _ -> return (bvint (int_size ret_ctyp) (Big_int.abs c))
    | ctyp, _ ->
        let sz = int_size ctyp in
        let* smt = smt_cval v in
        let* resized_pos = signed_size ~into:(int_size ret_ctyp) ~from:sz smt in
        let* resized_neg = signed_size ~into:(int_size ret_ctyp) ~from:sz (bvneg smt) in
        return (Ite (Fn ("=", [Extract (sz - 1, sz - 1, smt); bvone 1]), resized_neg, resized_pos))

  let builtin_choose_int compare op v1 v2 ret_ctyp =
    match (cval_ctyp v1, cval_ctyp v2) with
    | CT_constant n, CT_constant m -> return (bvint (int_size ret_ctyp) (op n m))
    | ctyp1, ctyp2 ->
        let ret_sz = int_size ret_ctyp in
        let* smt1 = bind (smt_cval v1) (signed_size ~into:ret_sz ~from:(int_size ctyp1)) in
        let* smt2 = bind (smt_cval v2) (signed_size ~into:ret_sz ~from:(int_size ctyp2)) in
        return (Ite (Fn (compare, [smt1; smt2]), smt1, smt2))

  let builtin_max_int = builtin_choose_int "bvsgt" max
  let builtin_min_int = builtin_choose_int "bvslt" min

  let smt_conversion ~into:to_ctyp ~from:from_ctyp x =
    match (from_ctyp, to_ctyp) with
    | _, _ when ctyp_equal from_ctyp to_ctyp -> return x
    | _, CT_constant c -> return (bvint (required_width c) c)
    | CT_constant c, CT_fint sz -> return (bvint sz c)
    | CT_constant c, CT_lint -> return (bvint lint_size c)
    | CT_fint sz, CT_lint -> signed_size ~into:lint_size ~from:sz x
    | CT_lint, CT_fint sz -> signed_size ~into:sz ~from:lint_size x
    | CT_lint, CT_fbits n -> signed_size ~into:n ~from:lint_size x
    | CT_lint, CT_lbits ->
        let* x = signed_size ~into:lbits_size ~from:lint_size x in
        return (Fn ("Bits", [bvint lbits_index (Big_int.of_int lint_size); x]))
    | CT_fint n, CT_lbits ->
        let* x = signed_size ~into:lbits_size ~from:n x in
        return (Fn ("Bits", [bvint lbits_index (Big_int.of_int n); x]))
    | CT_lbits, CT_fbits n -> unsigned_size ~into:n ~from:lbits_size (Fn ("contents", [x]))
    | CT_fbits n, CT_fbits m -> unsigned_size ~into:m ~from:n x
    | CT_fbits n, CT_lbits ->
        let* x = unsigned_size ~into:lbits_size ~from:n x in
        return (Fn ("Bits", [bvint lbits_index (Big_int.of_int n); x]))
    | _, _ ->
        let* l = current_location in
        Reporting.unreachable l __POS__
          (Printf.sprintf "Cannot perform conversion from %s to %s" (string_of_ctyp from_ctyp) (string_of_ctyp to_ctyp))

  let int_comparison fn big_int_fn v1 v2 =
    let* sv1 = smt_cval v1 in
    let* sv2 = smt_cval v2 in
    match (cval_ctyp v1, cval_ctyp v2) with
    | CT_constant c1, CT_constant c2 -> return (Bool_lit (big_int_fn c1 c2))
    | CT_lint, CT_lint -> return (Fn (fn, [sv1; sv2]))
    | CT_fint sz1, CT_fint sz2 ->
        return
          ( if sz1 == sz2 then Fn (fn, [sv1; sv2])
            else if sz1 > sz2 then Fn (fn, [sv1; SignExtend (sz1, sz1 - sz2, sv2)])
            else Fn (fn, [SignExtend (sz2, sz2 - sz1, sv1); sv2])
          )
    | CT_constant c, CT_fint sz -> return (Fn (fn, [bvint sz c; sv2]))
    | CT_fint sz, CT_constant c -> return (Fn (fn, [sv1; bvint sz c]))
    | CT_constant c, CT_lint -> return (Fn (fn, [bvint lint_size c; sv2]))
    | CT_lint, CT_constant c -> return (Fn (fn, [sv1; bvint lint_size c]))
    | CT_fint sz, CT_lint when sz < lint_size -> return (Fn (fn, [SignExtend (lint_size, lint_size - sz, sv1); sv2]))
    | CT_lint, CT_fint sz when sz < lint_size -> return (Fn (fn, [sv1; SignExtend (lint_size, lint_size - sz, sv2)]))
    | _, _ -> builtin_type_error fn [v1; v2] None

  let builtin_eq_int = int_comparison "=" Big_int.equal

  let builtin_lt = int_comparison "bvslt" Big_int.less
  let builtin_lteq = int_comparison "bvsle" Big_int.less_equal
  let builtin_gt = int_comparison "bvsgt" Big_int.greater
  let builtin_gteq = int_comparison "bvsge" Big_int.greater_equal

  let builtin_signed v ret_ctyp =
    let* sv = smt_cval v in
    match (cval_ctyp v, ret_ctyp) with
    | CT_fbits n, CT_fint m when m >= n -> return (SignExtend (m, m - n, sv))
    | CT_fbits n, CT_lint -> return (SignExtend (lint_size, lint_size - n, sv))
    | CT_lbits, CT_lint ->
        let contents = Fn ("contents", [sv]) in
        let top_bit_shift = ZeroExtend (lbits_size, lbits_index, bvsub (Fn ("len", [sv])) (bvone lbits_index)) in
        let top_bit = Extract (0, 0, bvlshr contents top_bit_shift) in
        let is_signed = Fn ("=", [top_bit; bvone 1]) in
        let* zero_extended = unsigned_size ~into:lint_size ~from:lbits_size contents in
        let ones_mask = bvshl (bvones lint_size) (ZeroExtend (lint_size, lbits_index, Fn ("len", [sv]))) in
        let ones_extended = bvor ones_mask zero_extended in
        return (Ite (is_signed, ones_extended, zero_extended))
    | _, _ -> builtin_type_error "signed" [v] (Some ret_ctyp)

  let builtin_unsigned v ret_ctyp =
    let* sv = smt_cval v in
    match (cval_ctyp v, ret_ctyp) with
    | CT_fbits n, CT_fint m when m > n -> return (Fn ("concat", [bvzero (m - n); sv]))
    | CT_fbits n, CT_lint -> return (Fn ("concat", [bvzero (lint_size - n); sv]))
    | CT_lbits, CT_lint -> signed_size ~into:lint_size ~from:lbits_size (Fn ("contents", [sv]))
    | CT_lbits, CT_fint m -> signed_size ~into:m ~from:lbits_size (Fn ("contents", [sv]))
    | _, _ -> builtin_type_error "unsigned" [v] (Some ret_ctyp)

  let bvmask len =
    let all_ones = bvones lbits_size in
    let shift = Fn ("concat", [bvzero (lbits_size - lbits_index); len]) in
    bvnot (bvshl all_ones shift)

  let builtin_shift shiftop vbits vshift ret_ctyp =
    match cval_ctyp vbits with
    | CT_fbits n ->
        let* bv = smt_cval vbits in
        let* shift = bvzeint n vshift in
        return (Fn (shiftop, [bv; shift]))
    | CT_lbits ->
        let* bv = smt_cval vbits in
        let* shift = bvzeint lbits_size vshift in
        let shifted =
          if shiftop = "bvashr" then (
            let mask = bvmask (Fn ("len", [bv])) in
            bvand mask (Fn (shiftop, [bvor (bvnot mask) (Fn ("contents", [bv])); shift]))
          )
          else Fn (shiftop, [Fn ("contents", [bv]); shift])
        in
        return (Fn ("Bits", [Fn ("len", [bv]); shifted]))
    | _ -> builtin_type_error shiftop [vbits; vshift] (Some ret_ctyp)

  let builtin_slice v1 v2 v3 ret_ctyp =
    match (cval_ctyp v1, cval_ctyp v2, cval_ctyp v3, ret_ctyp) with
    | CT_lbits, CT_constant start, CT_constant len, CT_fbits _ ->
        let top = Big_int.pred (Big_int.add start len) in
        let* v1 = smt_cval v1 in
        return (Extract (Big_int.to_int top, Big_int.to_int start, Fn ("contents", [v1])))
    | CT_fbits _, CT_constant start, CT_constant len, CT_fbits _ ->
        let top = Big_int.pred (Big_int.add start len) in
        let* v1 = smt_cval v1 in
        return (Extract (Big_int.to_int top, Big_int.to_int start, v1))
    | CT_fbits _, CT_fint _, CT_constant len, CT_fbits _ ->
        let* shifted = builtin_shift "bvlshr" v1 v2 (cval_ctyp v1) in
        return (Extract (Big_int.to_int (Big_int.pred len), 0, shifted))
    | ctyp1, ctyp2, _, CT_lbits ->
        let* smt1 = smt_cval v1 in
        let sz, smt1 = to_fbits ctyp1 smt1 in
        let* smt1 = unsigned_size ~into:lbits_size ~from:sz smt1 in
        let* smt2 = bind (smt_cval v2) (signed_size ~into:lbits_size ~from:(int_size ctyp2)) in
        let* smt3 = bvzeint lbits_index v3 in
        return (Fn ("Bits", [smt3; Fn ("bvand", [Fn ("bvlshr", [smt1; smt2]); bvmask smt3])]))
    | _ -> builtin_type_error "slice" [v1; v2; v3] (Some ret_ctyp)

  let builtin_zeros v ret_ctyp =
    match (cval_ctyp v, ret_ctyp) with
    | _, CT_fbits n -> return (bvzero n)
    | CT_constant c, CT_lbits -> return (Fn ("Bits", [bvint lbits_index c; bvzero lbits_size]))
    | ctyp, CT_lbits when int_size ctyp >= lbits_index ->
        let* v = smt_cval v in
        return (Fn ("Bits", [extract (lbits_index - 1) 0 v; bvzero lbits_size]))
    | _ -> builtin_type_error "zeros" [v] (Some ret_ctyp)

  let builtin_ones cval = function
    | CT_fbits n -> return (bvones n)
    | CT_lbits ->
        let* v = smt_cval cval in
        let len = extract (lbits_index - 1) 0 v in
        return (Fn ("Bits", [len; Fn ("bvand", [bvmask len; bvones lbits_size])]))
    | ret_ctyp -> builtin_type_error "ones" [cval] (Some ret_ctyp)

  let builtin_zero_extend vbits vlen ret_ctyp =
    match (cval_ctyp vbits, cval_ctyp vlen, ret_ctyp) with
    | CT_fbits n, _, CT_fbits m when n = m -> smt_cval vbits
    | CT_fbits n, _, CT_fbits m ->
        let* bv = smt_cval vbits in
        return (Fn ("concat", [bvzero (m - n); bv]))
    | CT_fbits n, CT_fint m, CT_lbits ->
        let* bv = smt_cval vbits in
        return (Fn ("concat", [bvzero (m - n); bv]))
    | CT_lbits, _, CT_fbits m ->
        let* bv = smt_cval vbits in
        return (Extract (m - 1, 0, Fn ("contents", [bv])))
        (*
    | CT_fbits n, CT_lbits ->
      assert (lbits_size ctx >= n);
      let vbits =
        if lbits_size ctx = n then smt_cval ctx vbits
        else if lbits_size ctx > n then Fn ("concat", [bvzero (lbits_size ctx - n); smt_cval ctx vbits])
        else assert false
      in
      Fn ("Bits", [bvzeint ctx ctx.lbits_index vlen; vbits])
           *)
    | CT_lbits, CT_lint, CT_lbits ->
        let* len = smt_cval vlen in
        let* bv = smt_cval vbits in
        return (Fn ("Bits", [extract (lbits_index - 1) 0 len; Fn ("contents", [bv])]))
    | _ -> builtin_type_error "zero_extend" [vbits; vlen] (Some ret_ctyp)

  let builtin_sign_extend vbits vlen ret_ctyp =
    let* bv = smt_cval vbits in
    match (cval_ctyp vbits, cval_ctyp vlen, ret_ctyp) with
    | CT_fbits n, _, CT_fbits m when n = m -> smt_cval vbits
    | CT_fbits n, _, CT_fbits m ->
        let top_bit_one = Fn ("=", [Extract (n - 1, n - 1, bv); bvone 1]) in
        return (Ite (top_bit_one, Fn ("concat", [bvones (m - n); bv]), Fn ("concat", [bvzero (m - n); bv])))
    | CT_lbits, i_ctyp, CT_lbits ->
        let* len = smt_cval vlen in
        let contents = Fn ("contents", [bv]) in
        let top_bit_shift = ZeroExtend (lbits_size, lbits_index, bvsub (Fn ("len", [bv])) (bvone lbits_index)) in
        let top_bit = Extract (0, 0, bvlshr contents top_bit_shift) in
        let is_signed = Fn ("=", [top_bit; bvone 1]) in
        let* new_len = signed_size ~into:lbits_index ~from:(int_size i_ctyp) len in
        let zero_extended = Fn ("Bits", [new_len; contents]) in
        let ones_mask = bvshl (bvones lbits_size) (ZeroExtend (lbits_size, lbits_index, Fn ("len", [bv]))) in
        let unused_mask = bvnot (bvshl (bvones lbits_size) (ZeroExtend (lbits_size, lbits_index, new_len))) in
        let ones_extended = Fn ("Bits", [new_len; bvand unused_mask (bvor ones_mask contents)]) in
        return (Ite (is_signed, ones_extended, zero_extended))
    | _ -> builtin_type_error "sign_extend" [vbits; vlen] (Some ret_ctyp)

  let builtin_replicate_bits vbits vtimes ret_ctyp =
    match (cval_ctyp vbits, cval_ctyp vtimes, ret_ctyp) with
    | CT_fbits n, _, CT_fbits m ->
        let* bits = smt_cval vbits in
        let times = m / n in
        return (Fn ("concat", List.init times (fun _ -> bits)))
    | CT_fbits n, vtimes_ctyp, CT_lbits ->
        let max_times = (lbits_size / n) + 1 in
        let* times = bind (smt_cval vtimes) (signed_size ~into:lbits_index ~from:(int_size vtimes_ctyp)) in
        let len = bvmul (bvpint lbits_index (Big_int.of_int n)) times in
        let* bits = smt_cval vbits in
        let contents = Extract (lbits_size - 1, 0, Fn ("concat", List.init max_times (fun _ -> bits))) in
        return (Fn ("Bits", [len; Fn ("bvand", [bvmask len; contents])]))
    | CT_lbits, vtimes_ctyp, CT_lbits ->
        let* bits = smt_cval vbits in
        let* times = bind (smt_cval vtimes) (signed_size ~into:lbits_index ~from:(int_size vtimes_ctyp)) in
        let new_len = bvmul (Fn ("len", [bits])) times in
        (* This is extremely inefficient, but we don't have a good alternative if we find ourselves in this case. *)
        let shifted =
          List.init (lbits_size - 1) (fun n ->
              let amount =
                bvmul
                  (bvpint lbits_size (Big_int.of_int (n + 1)))
                  (ZeroExtend (lbits_size, lbits_index, Fn ("len", [bits])))
              in
              bvshl (Fn ("contents", [bits])) amount
          )
        in
        let contents = List.fold_left bvor (Fn ("contents", [bits])) shifted in
        return (Fn ("Bits", [new_len; Fn ("bvand", [bvmask new_len; contents])]))
    | _ -> builtin_type_error "replicate_bits" [vbits; vtimes] (Some ret_ctyp)

  let builtin_not_bits v ret_ctyp =
    match (cval_ctyp v, ret_ctyp) with
    | CT_lbits, CT_fbits n ->
        let* bv = smt_cval v in
        return (bvnot (Extract (n - 1, 0, Fn ("contents", [bv]))))
    | CT_lbits, CT_lbits ->
        let* bv = smt_cval v in
        let len = Fn ("len", [bv]) in
        return (Fn ("Bits", [len; Fn ("bvand", [bvmask len; bvnot (Fn ("contents", [bv]))])]))
    | CT_fbits n, CT_fbits m when n = m ->
        let* bv = smt_cval v in
        return (bvnot bv)
    | _, _ -> builtin_type_error "not_bits" [v] (Some ret_ctyp)

  let builtin_length v ret_ctyp =
    match (cval_ctyp v, ret_ctyp) with
    | _, CT_constant len -> return (bvpint (int_size ret_ctyp) len)
    | CT_fbits n, _ -> return (bvpint (int_size ret_ctyp) (Big_int.of_int n))
    | CT_lbits, _ ->
        let* bv = smt_cval v in
        unsigned_size ~into:(int_size ret_ctyp) ~from:lbits_index (Fn ("len", [bv]))
    | _ -> builtin_type_error "length" [v] (Some ret_ctyp)

  let builtin_arith_bits op v1 v2 ret_ctyp =
    let* smt1 = smt_cval v1 in
    let* smt2 = smt_cval v2 in
    match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
    | CT_fbits n, CT_fbits m, CT_fbits o ->
        (* The Sail type system should guarantee this *)
        assert (n = m && m = o);
        return (Fn (op, [smt1; smt2]))
    | CT_lbits, CT_lbits, CT_lbits ->
        return (Fn ("Bits", [Fn ("len", [smt1]); Fn (op, [Fn ("contents", [smt1]); Fn ("contents", [smt2])])]))
    | _ -> builtin_type_error ("arith_bits " ^ op) [v1; v2] (Some ret_ctyp)

  let builtin_arith_bits_int op v1 v2 ret_ctyp =
    let* smt1 = smt_cval v1 in
    let* smt2 = smt_cval v2 in
    match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
    | CT_fbits n, CT_constant c, CT_fbits o ->
        assert (n = o);
        return (Fn (op, [smt1; bvint o c]))
    | CT_fbits n, CT_fint m, CT_fbits o ->
        assert (n = o);
        let* smt2 = signed_size ~into:o ~from:m smt2 in
        return (Fn (op, [smt1; smt2]))
    | CT_fbits n, CT_lint, CT_fbits o ->
        assert (n = o);
        let* smt2 = signed_size ~into:o ~from:lint_size smt2 in
        return (Fn (op, [smt1; smt2]))
    | CT_lbits, v2_ctyp, CT_lbits ->
        let* smt2 = signed_size ~into:lbits_size ~from:(int_size v2_ctyp) smt2 in
        return (Fn ("Bits", [Fn ("len", [smt1]); Fn (op, [Fn ("contents", [smt1]); smt2])]))
    | _ -> builtin_type_error ("arith_bits_int " ^ op) [v1; v2] (Some ret_ctyp)

  let builtin_eq_bits v1 v2 =
    match (cval_ctyp v1, cval_ctyp v2) with
    | CT_fbits n, CT_fbits m ->
        let o = max n m in
        let* smt1 = bind (smt_cval v1) (unsigned_size ~into:o ~from:n) in
        let* smt2 = bind (smt_cval v2) (unsigned_size ~into:o ~from:n) in
        return (Fn ("=", [smt1; smt2]))
    | CT_lbits, CT_lbits ->
        let* smt1 = smt_cval v1 in
        let* smt2 = smt_cval v2 in
        let len1 = Fn ("len", [smt1]) in
        let contents1 = Fn ("contents", [smt1]) in
        let len2 = Fn ("len", [smt2]) in
        let contents2 = Fn ("contents", [smt2]) in
        return
          (Fn
             ( "and",
               [
                 Fn ("=", [len1; len2]);
                 Fn ("=", [Fn ("bvand", [bvmask len1; contents1]); Fn ("bvand", [bvmask len2; contents2])]);
               ]
             )
          )
    | CT_lbits, CT_fbits n ->
        let* smt1 = bind (smt_cval v1) (fun bv -> unsigned_size ~into:n ~from:lbits_size (Fn ("contents", [bv]))) in
        let* smt2 = smt_cval v2 in
        return (Fn ("=", [smt1; smt2]))
    | CT_fbits n, CT_lbits ->
        let* smt1 = smt_cval v1 in
        let* smt2 = bind (smt_cval v2) (fun bv -> unsigned_size ~into:n ~from:lbits_size (Fn ("contents", [bv]))) in
        return (Fn ("=", [smt1; smt2]))
    | _ -> builtin_type_error "eq_bits" [v1; v2] None

  let builtin_neq_bits v1 v2 =
    let* t = builtin_eq_bits v1 v2 in
    return (Fn ("not", [t]))

  let builtin_append v1 v2 ret_ctyp =
    match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
    | CT_fbits n, CT_fbits m, CT_fbits o ->
        assert (n + m = o);
        let* smt1 = smt_cval v1 in
        let* smt2 = smt_cval v2 in
        return (Fn ("concat", [smt1; smt2]))
    | CT_fbits n, CT_lbits, CT_lbits ->
        let* smt1 = smt_cval v1 in
        let* smt2 = smt_cval v2 in
        let x = Fn ("concat", [bvzero (lbits_size - n); smt1]) in
        let shift = Fn ("concat", [bvzero (lbits_size - lbits_index); Fn ("len", [smt2])]) in
        return
          (Fn
             ( "Bits",
               [
                 bvadd (bvint lbits_index (Big_int.of_int n)) (Fn ("len", [smt2]));
                 bvor (bvshl x shift) (Fn ("contents", [smt2]));
               ]
             )
          )
    | CT_lbits, CT_fbits n, CT_fbits m ->
        let* smt1 = smt_cval v1 in
        let* smt2 = smt_cval v2 in
        return (Extract (m - 1, 0, Fn ("concat", [Fn ("contents", [smt1]); smt2])))
        (*
    | CT_lbits, CT_fbits n, CT_lbits ->
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      Fn
        ( "Bits",
          [
            bvadd (bvint ctx.lbits_index (Big_int.of_int n)) (Fn ("len", [smt1]));
            Extract (lbits_size ctx - 1, 0, Fn ("concat", [Fn ("contents", [smt1]); smt2]));
          ]
        )
    | CT_fbits n, CT_fbits m, CT_lbits ->
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      Fn
        ( "Bits",
          [
            bvint ctx.lbits_index (Big_int.of_int (n + m));
            unsigned_size ctx (lbits_size ctx) (n + m) (Fn ("concat", [smt1; smt2]));
          ]
        )
           *)
    | CT_lbits, CT_lbits, CT_lbits ->
        let* smt1 = smt_cval v1 in
        let* smt2 = smt_cval v2 in
        let x = Fn ("contents", [smt1]) in
        let shift = Fn ("concat", [bvzero (lbits_size - lbits_index); Fn ("len", [smt2])]) in
        return
          (Fn ("Bits", [bvadd (Fn ("len", [smt1])) (Fn ("len", [smt2])); bvor (bvshl x shift) (Fn ("contents", [smt2]))])
          )
        (*
    | CT_lbits, CT_lbits, CT_fbits n ->
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      let x = Fn ("contents", [smt1]) in
      let shift = Fn ("concat", [bvzero (lbits_size ctx - ctx.lbits_index); Fn ("len", [smt2])]) in
      unsigned_size ctx n (lbits_size ctx) (bvor (bvshl x shift) (Fn ("contents", [smt2])))
           *)
    | _ -> builtin_type_error "append" [v1; v2] (Some ret_ctyp)

  let builtin_sail_truncate v1 v2 ret_ctyp =
    match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
    | v1_ctyp, CT_constant c, CT_fbits m ->
        let* smt1 = smt_cval v1 in
        let sz, bv = to_fbits v1_ctyp smt1 in
        assert (Big_int.to_int c = m && m <= sz);
        return (Extract (Big_int.to_int c - 1, 0, bv))
    | v1_ctyp, _, CT_lbits ->
        let* smt1 = smt_cval v1 in
        let sz, bv = to_fbits v1_ctyp smt1 in
        let* smt1 = unsigned_size ~into:lbits_size ~from:sz bv in
        let* smt2 = bvzeint lbits_index v2 in
        return (Fn ("Bits", [smt2; Fn ("bvand", [bvmask smt2; smt1])]))
    | _ -> builtin_type_error "sail_truncate" [v1; v2] (Some ret_ctyp)

  let builtin_sail_truncateLSB v1 v2 ret_ctyp =
    match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
    | v1_ctyp, CT_constant c, CT_fbits m ->
        let* smt1 = smt_cval v1 in
        let sz, bv = to_fbits v1_ctyp smt1 in
        assert (Big_int.to_int c = m && m <= sz);
        return (Extract (sz - 1, sz - Big_int.to_int c, bv))
    | CT_fbits sz, _, CT_lbits ->
        let* smt1 = smt_cval v1 in
        let* len = bvzeint lbits_index v2 in
        let shift = bvsub (bvpint lbits_index (Big_int.of_int sz)) len in
        let shifted = bvlshr smt1 (ZeroExtend (sz, lbits_index, shift)) in
        let* shifted = unsigned_size ~checked:false ~into:lbits_size ~from:sz shifted in
        return (Fn ("Bits", [len; shifted]))
    | CT_lbits, _, CT_lbits ->
        let* smt1 = smt_cval v1 in
        let* len = bvzeint lbits_index v2 in
        let shift = bvsub (Fn ("len", [smt1])) len in
        let shifted = bvlshr (Fn ("contents", [smt1])) (ZeroExtend (lbits_size, lbits_index, shift)) in
        return (Fn ("Bits", [len; shifted]))
    | _ -> builtin_type_error "sail_truncateLSB" [v1; v2] (Some ret_ctyp)

  let builtin_bitwise fn v1 v2 ret_ctyp =
    match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
    | CT_fbits n, CT_fbits m, CT_fbits o ->
        assert (n = m && m = o);
        let* smt1 = smt_cval v1 in
        let* smt2 = smt_cval v2 in
        return (Fn (fn, [smt1; smt2]))
    | CT_lbits, CT_lbits, CT_lbits ->
        let* smt1 = smt_cval v1 in
        let* smt2 = smt_cval v2 in
        return (Fn ("Bits", [Fn ("len", [smt1]); Fn (fn, [Fn ("contents", [smt1]); Fn ("contents", [smt2])])]))
    | _ -> builtin_type_error fn [v1; v2] (Some ret_ctyp)

  let fbits_mask mask_sz len = bvnot (bvshl (bvones mask_sz) len)

  let builtin_vector_access vec i ret_ctyp =
    match (cval_ctyp vec, cval_ctyp i, ret_ctyp) with
    | CT_fbits n, CT_constant i, CT_bit ->
        let* bv = smt_cval vec in
        return (Extract (Big_int.to_int i, Big_int.to_int i, bv))
    | CT_lbits, CT_constant i, CT_bit ->
        let* bv = smt_cval vec in
        return (Extract (Big_int.to_int i, Big_int.to_int i, Fn ("contents", [bv])))
    | ((CT_lbits | CT_fbits _) as bv_ctyp), i_ctyp, CT_bit ->
        let* bv = smt_cval vec in
        let sz, bv = to_fbits bv_ctyp bv in
        let* i = smt_cval i in
        (* checked:false should be fine here, as the Sail type system has already checked the bounds *)
        let* shift = signed_size ~checked:false ~into:sz ~from:(int_size i_ctyp) i in
        return (Extract (0, 0, Fn ("bvlshr", [bv; shift])))
    | CT_fvector (len, _), i_ctyp, _ ->
        let* vec = smt_cval vec in
        let* i =
          bind (smt_cval i)
            (unsigned_size ~checked:false ~into:(required_width (Big_int.of_int (len - 1)) - 1) ~from:(int_size i_ctyp))
        in
        return (Fn ("select", [vec; i]))
        (*
    | CT_vector _, CT_constant i, _ -> Fn ("select", [smt_cval ctx vec; bvint !vector_index i])
    | CT_vector _, index_ctyp, _ ->
      Fn ("select", [smt_cval ctx vec; force_size ctx !vector_index (int_size ctx index_ctyp) (smt_cval ctx i)])
      *)
    | _ -> builtin_type_error "vector_access" [vec; i] (Some ret_ctyp)

  let builtin_vector_subrange vec i j ret_ctyp =
    match (cval_ctyp vec, cval_ctyp i, cval_ctyp j, ret_ctyp) with
    | CT_fbits n, CT_constant i, CT_constant j, CT_fbits _ ->
        let* vec = smt_cval vec in
        return (Extract (Big_int.to_int i, Big_int.to_int j, vec))
    | CT_lbits, CT_constant i, CT_constant j, CT_fbits _ ->
        let* vec = smt_cval vec in
        return (Extract (Big_int.to_int i, Big_int.to_int j, Fn ("contents", [vec])))
        (*
    | CT_fbits n, i_ctyp, CT_constant j, CT_lbits when Big_int.equal j Big_int.zero ->
      let i' = signed_size ~checked:false ctx ctx.lbits_index (int_size ctx i_ctyp) (smt_cval ctx i) in
      let len = bvadd i' (bvint ctx.lbits_index (Big_int.of_int 1)) in
      Fn ("Bits", [len; Fn ("bvand", [bvmask ctx len; unsigned_size ctx (lbits_size ctx) n (smt_cval ctx vec)])])
           *)
    | bv_ctyp, i_ctyp, j_ctyp, ret_ctyp ->
        let* vec = smt_cval vec in
        let sz, vec = to_fbits bv_ctyp vec in
        let* i' = bind (smt_cval i) (signed_size ~into:sz ~from:(int_size i_ctyp)) in
        let* j' = bind (smt_cval j) (signed_size ~into:sz ~from:(int_size j_ctyp)) in
        let len = bvadd (bvadd i' (bvneg j')) (bvint sz (Big_int.of_int 1)) in
        let extracted = bvand (bvlshr vec j') (fbits_mask sz len) in
        smt_conversion ~into:ret_ctyp ~from:(CT_fbits sz) extracted

  let builtin_vector_update vec i x ret_ctyp =
    match (cval_ctyp vec, cval_ctyp i, cval_ctyp x, ret_ctyp) with
    | CT_fbits n, CT_constant i, CT_bit, CT_fbits m when n - 1 > Big_int.to_int i && Big_int.to_int i > 0 ->
        assert (n = m);
        let* bv = smt_cval vec in
        let* x = smt_cval x in
        let top = Extract (n - 1, Big_int.to_int i + 1, bv) in
        let bot = Extract (Big_int.to_int i - 1, 0, bv) in
        return (Fn ("concat", [top; Fn ("concat", [x; bot])]))
    | CT_fbits n, CT_constant i, CT_bit, CT_fbits m when n - 1 = Big_int.to_int i && Big_int.to_int i > 0 ->
        let* bv = smt_cval vec in
        let* x = smt_cval x in
        let bot = Extract (Big_int.to_int i - 1, 0, bv) in
        return (Fn ("concat", [x; bot]))
    | CT_fbits n, CT_constant i, CT_bit, CT_fbits m when n - 1 > Big_int.to_int i && Big_int.to_int i = 0 ->
        let* bv = smt_cval vec in
        let* x = smt_cval x in
        let top = Extract (n - 1, 1, bv) in
        return (Fn ("concat", [top; x]))
    | CT_fbits n, CT_constant i, CT_bit, CT_fbits m when n - 1 = 0 && Big_int.to_int i = 0 -> smt_cval x
    | CT_fbits n, i_ctyp, CT_bit, CT_fbits m ->
        assert (n = m);
        let* bv = smt_cval vec in
        let* bit = smt_cval x in
        (* Sail type system won't allow us to index out of range *)
        let* shift = bind (smt_cval i) (unsigned_size ~checked:false ~into:n ~from:(int_size i_ctyp)) in
        let mask = bvnot (bvshl (ZeroExtend (n, n - 1, bvone 1)) shift) in
        let shifted_bit = bvshl (ZeroExtend (n, n - 1, bit)) shift in
        return (bvor (bvand mask bv) shifted_bit)
    | CT_lbits, i_ctyp, CT_bit, CT_lbits ->
        let* bv = smt_cval vec in
        let* bit = smt_cval x in
        (* Sail type system won't allow us to index out of range *)
        let* shift = bind (smt_cval i) (unsigned_size ~checked:false ~into:lbits_size ~from:(int_size i_ctyp)) in
        let mask = bvnot (bvshl (ZeroExtend (lbits_size, lbits_size - 1, bvone 1)) shift) in
        let shifted_bit = bvshl (ZeroExtend (lbits_size, lbits_size - 1, bit)) shift in
        let contents = bvor (bvand mask (Fn ("contents", [bv]))) shifted_bit in
        return (Fn ("Bits", [Fn ("len", [bv]); contents]))
    | CT_fvector (len, ctyp), i_ctyp, _, CT_fvector (len_out, _) ->
        assert (len = len_out);
        let* l = current_location in
        let store_fn = Primop_gen.fvector_store l len ctyp in
        let* vec = smt_cval vec in
        let* x = smt_cval x in
        let* i =
          bind (smt_cval i)
            (unsigned_size ~checked:false ~into:(required_width (Big_int.of_int (len - 1)) - 1) ~from:(int_size i_ctyp))
        in
        return (Store (Fixed len, store_fn, vec, i, x))
    (*
       | CT_vector _, CT_constant i, ctyp, CT_vector _ ->
         Fn ("store", [smt_cval ctx vec; bvint !vector_index i; smt_cval ctx x])
       | CT_vector _, index_ctyp, _, CT_vector _ ->
         Fn
           ( "store",
             [smt_cval ctx vec; force_size ctx !vector_index (int_size ctx index_ctyp) (smt_cval ctx i); smt_cval ctx x]
           )
    *)
    | _ -> builtin_type_error "vector_update" [vec; i; x] (Some ret_ctyp)

  let builtin_vector_update_subrange vec i j x ret_ctyp =
    match (cval_ctyp vec, cval_ctyp i, cval_ctyp j, cval_ctyp x, ret_ctyp) with
    | CT_fbits n, CT_constant i, CT_constant j, CT_fbits sz, CT_fbits m
      when n - 1 > Big_int.to_int i && Big_int.to_int j > 0 ->
        assert (n = m);
        let* vec = smt_cval vec in
        let* x = smt_cval x in
        let top = Extract (n - 1, Big_int.to_int i + 1, vec) in
        let bot = Extract (Big_int.to_int j - 1, 0, vec) in
        return (Fn ("concat", [top; Fn ("concat", [x; bot])]))
    | CT_fbits n, CT_constant i, CT_constant j, CT_fbits sz, CT_fbits m
      when n - 1 = Big_int.to_int i && Big_int.to_int j > 0 ->
        assert (n = m);
        let* vec = smt_cval vec in
        let* x = smt_cval x in
        let bot = Extract (Big_int.to_int j - 1, 0, vec) in
        return (Fn ("concat", [x; bot]))
    | CT_fbits n, CT_constant i, CT_constant j, CT_fbits sz, CT_fbits m
      when n - 1 > Big_int.to_int i && Big_int.to_int j = 0 ->
        assert (n = m);
        let* vec = smt_cval vec in
        let* x = smt_cval x in
        let top = Extract (n - 1, Big_int.to_int i + 1, vec) in
        return (Fn ("concat", [top; x]))
    | CT_fbits n, CT_constant i, CT_constant j, CT_fbits sz, CT_fbits m
      when n - 1 = Big_int.to_int i && Big_int.to_int j = 0 ->
        smt_cval x
    | CT_fbits n, ctyp_i, ctyp_j, ctyp_x, CT_fbits m ->
        assert (n = m);
        let* vec = smt_cval vec in
        let* i' = bind (smt_cval i) (signed_size ~into:n ~from:(int_size ctyp_i)) in
        let* j' = bind (smt_cval j) (signed_size ~into:n ~from:(int_size ctyp_j)) in
        let* x' = bind (smt_cval x) (smt_conversion ~into:(CT_fbits n) ~from:ctyp_x) in
        let len = bvadd (bvadd i' (bvneg j')) (bvint n (Big_int.of_int 1)) in
        let mask = bvshl (fbits_mask n len) j' in
        return (bvor (bvand vec (bvnot mask)) (bvand (bvshl x' j') mask))
    | bv_ctyp, ctyp_i, ctyp_j, ctyp_x, CT_lbits ->
        let* sz, bv = fmap (to_fbits bv_ctyp) (smt_cval vec) in
        let* i = bind (smt_cval i) (signed_size ~into:sz ~from:(int_size ctyp_i)) in
        let* j = bind (smt_cval j) (signed_size ~into:sz ~from:(int_size ctyp_j)) in
        let* x = bind (smt_cval x) (smt_conversion ~into:(CT_fbits sz) ~from:ctyp_x) in
        let len = bvadd (bvadd i (bvneg j)) (bvpint sz (Big_int.of_int 1)) in
        let mask = bvshl (fbits_mask sz len) j in
        let contents = bvor (bvand bv (bvnot mask)) (bvand (bvshl x j) mask) in
        let* index = signed_size ~into:lbits_index ~from:sz len in
        return (Fn ("Bits", [index; contents]))
    | _ -> builtin_type_error "vector_update_subrange" [vec; i; j; x] (Some ret_ctyp)

  let builtin_get_slice_int v1 v2 v3 ret_ctyp =
    match (cval_ctyp v1, cval_ctyp v2, cval_ctyp v3, ret_ctyp) with
    | CT_constant len, ctyp, CT_constant start, CT_fbits ret_sz ->
        let len = Big_int.to_int len in
        let start = Big_int.to_int start in
        let in_sz = int_size ctyp in
        let* smt =
          if in_sz < len + start then bind (smt_cval v2) (signed_size ~into:(len + start) ~from:in_sz) else smt_cval v2
        in
        return (Extract (start + len - 1, start, smt))
    | CT_lint, CT_lint, CT_constant start, CT_lbits when Big_int.equal start Big_int.zero ->
        let* v1 = smt_cval v1 in
        let len = Extract (lbits_index - 1, 0, v1) in
        let* contents = bind (smt_cval v2) (unsigned_size ~into:lbits_size ~from:lint_size) in
        return (Fn ("Bits", [len; bvand (bvmask len) contents]))
    | ctyp1, ctyp2, ctyp3, ret_ctyp ->
        let* smt1 = smt_cval v1 in
        let* len = signed_size ~into:lbits_index ~from:(int_size ctyp1) smt1 in
        let* smt2 = bind (smt_cval v2) (signed_size ~into:lbits_size ~from:(int_size ctyp2)) in
        let* smt3 = bind (smt_cval v3) (signed_size ~into:lbits_size ~from:(int_size ctyp3)) in
        let result = Fn ("Bits", [len; bvand (bvmask len) (bvlshr smt2 smt3)]) in
        smt_conversion ~into:ret_ctyp ~from:CT_lbits result

  let builtin_pow2 v ret_ctyp =
    match (cval_ctyp v, ret_ctyp) with
    | CT_constant n, _ when Big_int.greater_equal n Big_int.zero ->
        return (bvint (int_size ret_ctyp) (Big_int.pow_int_positive 2 (Big_int.to_int n)))
    | CT_lint, CT_lint ->
        let* v = smt_cval v in
        (* TODO: Check we haven't shifted too far *)
        return (bvshl (bvone lint_size) v)
    | _ -> builtin_type_error "pow2" [v] (Some ret_ctyp)

  (* Technically, there's no bvclz in SMTLIB, but we can't generate
     anything nice, so leave it in case a backend like SystemVerilog
     can do better *)
  let builtin_count_leading_zeros v ret_ctyp =
    let* l = current_location in
    match cval_ctyp v with
    | CT_fbits sz ->
        let bvclz = Primop_gen.count_leading_zeros l sz in
        let* bv = smt_cval v in
        unsigned_size ~max_value:sz ~into:(int_size ret_ctyp) ~from:sz (Fn (bvclz, [bv]))
    | CT_lbits ->
        let bvclz = Primop_gen.count_leading_zeros l lbits_size in
        let* bv = smt_cval v in
        let contents_clz = Fn (bvclz, [Fn ("contents", [bv])]) in
        let* len = unsigned_size ~into:lbits_size ~from:lbits_index (Fn ("len", [bv])) in
        let lz = bvsub contents_clz (bvsub (bvpint lbits_size (Big_int.of_int lbits_size)) len) in
        unsigned_size ~max_value:lbits_size ~into:(int_size ret_ctyp) ~from:lbits_size lz
    | _ -> builtin_type_error "count_leading_zeros" [v] (Some ret_ctyp)

  let arity_error =
    let* l = current_location in
    raise (Reporting.unreachable l __POS__ "Trying to generate primitive with incorrect number of arguments")

  let unary_primop f = Some (fun args ret_ctyp -> match args with [v] -> f v ret_ctyp | _ -> arity_error)

  let unary_primop_simple f = Some (fun args _ -> match args with [v] -> f v | _ -> arity_error)

  let binary_primop f = Some (fun args ret_ctyp -> match args with [v1; v2] -> f v1 v2 ret_ctyp | _ -> arity_error)

  let binary_primop_simple f = Some (fun args _ -> match args with [v1; v2] -> f v1 v2 | _ -> arity_error)

  let ternary_primop f =
    Some (fun args ret_ctyp -> match args with [v1; v2; v3] -> f v1 v2 v3 ret_ctyp | _ -> arity_error)

  let builtin = function
    | "eq_bit" ->
        binary_primop_simple (fun v1 v2 ->
            let* smt1 = smt_cval v1 in
            let* smt2 = smt_cval v2 in
            return (Fn ("=", [smt1; smt2]))
        )
    | "eq_bool" ->
        binary_primop_simple (fun v1 v2 ->
            let* smt1 = smt_cval v1 in
            let* smt2 = smt_cval v2 in
            return (Fn ("=", [smt1; smt2]))
        )
    | "eq_int" -> binary_primop_simple builtin_eq_int
    | "not" ->
        unary_primop_simple (fun v ->
            let* v = smt_cval v in
            return (Fn ("not", [v]))
        )
    | "lt" -> binary_primop_simple builtin_lt
    | "lteq" -> binary_primop_simple builtin_lteq
    | "gt" -> binary_primop_simple builtin_gt
    | "gteq" -> binary_primop_simple builtin_gteq
    | "add_int" -> binary_primop builtin_add_int
    | "sub_int" -> binary_primop builtin_sub_int
    | "mult_int" -> binary_primop builtin_mult_int
    | "neg_int" -> unary_primop builtin_neg_int
    | "abs_int" -> unary_primop builtin_abs_int
    | "max_int" -> binary_primop builtin_max_int
    | "min_int" -> binary_primop builtin_min_int
    | "pow2" -> unary_primop builtin_pow2
    | "zeros" -> unary_primop builtin_zeros
    | "ones" -> unary_primop builtin_ones
    | "zero_extend" -> binary_primop builtin_zero_extend
    | "sign_extend" -> binary_primop builtin_sign_extend
    | "sail_signed" -> unary_primop builtin_signed
    | "sail_unsigned" -> unary_primop builtin_unsigned
    | "slice" -> ternary_primop builtin_slice
    | "add_bits" -> binary_primop (builtin_arith_bits "bvadd")
    | "add_bits_int" -> binary_primop (builtin_arith_bits_int "bvadd")
    | "sub_bits" -> binary_primop (builtin_arith_bits "bvsub")
    | "sub_bits_int" -> binary_primop (builtin_arith_bits_int "bvsub")
    | "append" -> binary_primop builtin_append
    | "get_slice_int" -> ternary_primop builtin_get_slice_int
    | "eq_bits" -> binary_primop_simple builtin_eq_bits
    | "neq_bits" -> binary_primop_simple builtin_neq_bits
    | "not_bits" -> unary_primop builtin_not_bits
    | "sail_truncate" -> binary_primop builtin_sail_truncate
    | "sail_truncateLSB" -> binary_primop builtin_sail_truncateLSB
    | "shiftl" -> binary_primop (builtin_shift "bvshl")
    | "shiftr" -> binary_primop (builtin_shift "bvlshr")
    | "arith_shiftr" -> binary_primop (builtin_shift "bvashr")
    | "and_bits" -> binary_primop (builtin_bitwise "bvand")
    | "or_bits" -> binary_primop (builtin_bitwise "bvor")
    | "xor_bits" -> binary_primop (builtin_bitwise "bvxor")
    | "vector_access" -> binary_primop builtin_vector_access
    | "vector_subrange" -> ternary_primop builtin_vector_subrange
    | "vector_update" -> ternary_primop builtin_vector_update
    | "vector_update_subrange" ->
        Some
          (fun args ret_ctyp ->
            match args with [v1; v2; v3; v4] -> builtin_vector_update_subrange v1 v2 v3 v4 ret_ctyp | _ -> arity_error
          )
    | "length" -> unary_primop builtin_length
    | "replicate_bits" -> binary_primop builtin_replicate_bits
    | "count_leading_zeros" -> unary_primop builtin_count_leading_zeros
    | "print_bits" ->
        binary_primop_simple (fun str bv ->
            let* l = current_location in
            let op = Primop_gen.print_bits l (cval_ctyp bv) in
            let* str = smt_cval str in
            let* bv = smt_cval bv in
            return (Fn (op, [str; bv]))
        )
    | "string_of_bits" ->
        unary_primop_simple (fun bv ->
            let* l = current_location in
            let op = Primop_gen.string_of_bits l (cval_ctyp bv) in
            let* bv = smt_cval bv in
            return (Fn (op, [bv]))
        )
    | "dec_str" ->
        unary_primop_simple (fun bv ->
            let* l = current_location in
            let op = Primop_gen.dec_str l (cval_ctyp bv) in
            let* bv = smt_cval bv in
            return (Fn (op, [bv]))
        )
    | "hex_str" ->
        unary_primop_simple (fun bv ->
            let* l = current_location in
            let op = Primop_gen.hex_str l (cval_ctyp bv) in
            let* bv = smt_cval bv in
            return (Fn (op, [bv]))
        )
    | "hex_str_upper" ->
        unary_primop_simple (fun bv ->
            let* l = current_location in
            let op = Primop_gen.hex_str_upper l (cval_ctyp bv) in
            let* bv = smt_cval bv in
            return (Fn (op, [bv]))
        )
    | "sail_assert" ->
        binary_primop_simple (fun b msg ->
            let* b = smt_cval b in
            let* msg = smt_cval msg in
            return (Fn ("sail_assert", [b; msg]))
        )
    | "reg_deref" ->
        unary_primop_simple (fun reg_ref ->
            match cval_ctyp reg_ref with
            | CT_ref ctyp ->
                let* reg_ref = smt_cval reg_ref in
                let op = "sail_reg_deref_" ^ Util.zencode_string (string_of_ctyp ctyp) in
                return (Fn (op, [reg_ref]))
            | _ ->
                let* l = current_location in
                Reporting.unreachable l __POS__ "reg_deref given non register reference"
        )
    | "sail_cons" ->
        binary_primop_simple (fun x xs ->
            let* x = smt_cval x in
            let* xs = smt_cval xs in
            return (Fn ("cons", [x; xs]))
        )
    | "eq_anything" ->
        binary_primop_simple (fun a b ->
            let* a = smt_cval a in
            let* b = smt_cval b in
            return (Fn ("=", [a; b]))
        )
    | _ -> None
end
