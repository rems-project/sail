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

type 'a check_writer = { value : 'a; checks : checks }

let return x = { value = x; checks = empty_checks }

let bind m f =
  let m' = f m.value in
  { value = m'.value; checks = append_checks m.checks m'.checks }

let fmap f m =
  let value = f m.value in
  { value; checks = m.checks }

let ( let* ) = bind

let rec mapM f = function
  | [] -> return []
  | x :: xs ->
      let* x = f x in
      let* xs = mapM f xs in
      return (x :: xs)

let overflow_check check = { value = (); checks = { empty_checks with overflows = [check] } }

let string_used = { value = (); checks = { empty_checks with strings_used = true } }

let real_used = { value = (); checks = { empty_checks with reals_used = true } }

(* [force_size ctx n m exp] takes a smt expression assumed to be a
   integer (signed bitvector) of length m and forces it to be length n
   by either sign extending it or truncating it as required *)
let force_size ?(checked = true) n m smt =
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
    let* _ = overflow_check check in
    return (Extract (n - 1, 0, smt))
  )

(* [unsigned_size ctx n m exp] is much like force_size, but it
   assumes that the bitvector is unsigned *)
let unsigned_size n m smt =
  if n = m then return smt
  else if n > m then return (Fn ("concat", [bvzero (n - m); smt]))
  else
    (* Ensure we don't overwrite any high bits when truncating *)
    let* _ = overflow_check (Fn ("not", [Fn ("=", [Extract (m - 1, n, smt); bvzero (m - n)])])) in
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
end

module type PRIMOP_GEN = sig
  val print_bits : ctyp -> string
end

let builtin_type_error fn cvals =
  let args = Util.string_of_list ", " (fun cval -> string_of_ctyp (cval_ctyp cval)) cvals in
  function
  | Some ret_ctyp ->
      let message = Printf.sprintf "%s : (%s) -> %s" fn args (string_of_ctyp ret_ctyp) in
      raise (Reporting.err_todo Parse_ast.Unknown message)
  | None -> raise (Reporting.err_todo Parse_ast.Unknown (Printf.sprintf "%s : (%s)" fn args))

module Make (Config : CONFIG) (Primop_gen : PRIMOP_GEN) = struct
  let lint_size = Config.max_unknown_integer_width
  let lbits_size = Config.max_unknown_bitvector_width
  let lbits_index = required_width (Big_int.of_int (lint_size - 1))

  let int_size = function
    | CT_constant n -> required_width n
    | CT_fint sz -> sz
    | CT_lint -> lint_size
    | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Argument to int_size must be an integer type"

  let bv_size = function CT_fbits (sz, _) -> sz | CT_lbits _ -> lbits_size

  let literal vl ctyp =
    let open Value2 in
    match (vl, ctyp) with
    | VL_bits (bv, true), CT_fbits (n, _) -> unsigned_size n (List.length bv) (Bitvec_lit bv)
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
    | _ -> failwith ("Cannot translate literal to SMT: " ^ string_of_value vl ^ " : " ^ string_of_ctyp ctyp)

  let smt_cval_call op args =
    match (op, args) with
    | Bnot, [arg] -> Fn ("not", [arg])
    | Bor, [arg] -> arg
    | Bor, args -> Fn ("or", args)
    | Band, [arg] -> arg
    | Band, args -> Fn ("and", args)
    | Eq, args -> Fn ("=", args)
    | Neq, args -> Fn ("not", [Fn ("=", args)])
    | Bvnot, args -> Fn ("bvnot", args)
    | Bvor, args -> Fn ("bvor", args)
    | Bvand, args -> Fn ("bvand", args)
    | Bvxor, args -> Fn ("bvxor", args)
    | Bvadd, args -> Fn ("bvadd", args)
    | Bvsub, args -> Fn ("bvsub", args)
    | _ -> failwith "unknown op"

  let rec smt_cval cval =
    match cval_ctyp cval with
    | CT_constant n -> return (bvint (required_width n) n)
    | _ -> (
        match cval with
        | V_lit (vl, ctyp) -> literal vl ctyp
        | V_id (id, _) -> return (Var id)
        | V_call (op, args) ->
            let* args = mapM smt_cval args in
            return (smt_cval_call op args)
        | V_ctor_kind (union, ctor, _) ->
            let* union = smt_cval union in
            return (Fn ("not", [Tester (zencode_uid ctor, union)]))
        | V_ctor_unwrap (union, (ctor, _), _) ->
            let* union = smt_cval union in
            return (Unwrap (ctor, union))
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
    (* To detect arithmetic overflow we can expand the input bitvectors
       to some size determined by a padding function, then check we
       don't lose precision when going back after performing the
       operation. *)
    match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
    | _, _, CT_constant c -> return (bvint (required_width c) c)
    | CT_constant c1, CT_constant c2, _ -> return (bvint (int_size ret_ctyp) (big_int_fn c1 c2))
    | ctyp1, ctyp2, _ ->
        let ret_sz = int_size ret_ctyp in
        let* smt1 = smt_cval v1 in
        let* smt2 = smt_cval v2 in
        let* padded_smt1 = force_size (padding ret_sz) (int_size ctyp1) smt1 in
        let* padded_smt2 = force_size (padding ret_sz) (int_size ctyp2) smt2 in
        force_size ret_sz (padding ret_sz) (Fn (fn, [padded_smt1; padded_smt2]))

  let builtin_add_int = builtin_arith "bvadd" Big_int.add (fun x -> x + 1)
  let builtin_sub_int = builtin_arith "bvsub" Big_int.sub (fun x -> x + 1)
  let builtin_mult_int = builtin_arith "bvmul" Big_int.mul (fun x -> x * 2)

  let smt_conversion from_ctyp to_ctyp x =
    match (from_ctyp, to_ctyp) with
    | _, _ when ctyp_equal from_ctyp to_ctyp -> return x
    | CT_constant c, CT_fint sz -> return (bvint sz c)
    | CT_constant c, CT_lint -> return (bvint lint_size c)
    | CT_fint sz, CT_lint -> force_size lint_size sz x
    | CT_lint, CT_fint sz -> force_size sz lint_size x
    | CT_lint, CT_fbits (n, _) -> force_size n lint_size x
    | CT_lint, CT_lbits _ ->
        let* x = force_size lbits_size lint_size x in
        return (Fn ("Bits", [bvint lbits_index (Big_int.of_int lint_size); x]))
    | CT_fint n, CT_lbits _ ->
        let* x = force_size lbits_size n x in
        return (Fn ("Bits", [bvint lbits_index (Big_int.of_int n); x]))
    | CT_lbits _, CT_fbits (n, _) -> unsigned_size n lbits_size (Fn ("contents", [x]))
    | CT_fbits (n, _), CT_fbits (m, _) -> unsigned_size m n x
    | CT_fbits (n, _), CT_lbits _ ->
        let* x = unsigned_size lbits_size n x in
        return (Fn ("Bits", [bvint lbits_index (Big_int.of_int n); x]))
    | _, _ ->
        failwith
          (Printf.sprintf "Cannot perform conversion from %s to %s" (string_of_ctyp from_ctyp) (string_of_ctyp to_ctyp))

  let int_comparison fn big_int_fn v1 v2 =
    let* sv1 = smt_cval v1 in
    let* sv2 = smt_cval v2 in
    return
      ( match (cval_ctyp v1, cval_ctyp v2) with
      | CT_constant c1, CT_constant c2 -> Bool_lit (big_int_fn c1 c2)
      | CT_lint, CT_lint -> Fn (fn, [sv1; sv2])
      | CT_fint sz1, CT_fint sz2 ->
          if sz1 == sz2 then Fn (fn, [sv1; sv2])
          else if sz1 > sz2 then Fn (fn, [sv1; SignExtend (sz1, sz1 - sz2, sv2)])
          else Fn (fn, [SignExtend (sz2, sz2 - sz1, sv1); sv2])
      | CT_constant c, CT_fint sz -> Fn (fn, [bvint sz c; sv2])
      | CT_fint sz, CT_constant c -> Fn (fn, [sv1; bvint sz c])
      | CT_constant c, CT_lint -> Fn (fn, [bvint lint_size c; sv2])
      | CT_lint, CT_constant c -> Fn (fn, [sv1; bvint lint_size c])
      | CT_fint sz, CT_lint when sz < lint_size -> Fn (fn, [SignExtend (lint_size, lint_size - sz, sv1); sv2])
      | CT_lint, CT_fint sz when sz < lint_size -> Fn (fn, [sv1; SignExtend (lint_size, lint_size - sz, sv2)])
      | _, _ -> builtin_type_error fn [v1; v2] None
      )

  let builtin_eq_int = int_comparison "=" Big_int.equal

  let builtin_lt = int_comparison "bvslt" Big_int.less
  let builtin_lteq = int_comparison "bvsle" Big_int.less_equal
  let builtin_gt = int_comparison "bvsgt" Big_int.greater
  let builtin_gteq = int_comparison "bvsge" Big_int.greater_equal

  let builtin_signed v ret_ctyp =
    let* sv = smt_cval v in
    match (cval_ctyp v, ret_ctyp) with
    | CT_fbits (n, _), CT_fint m when m >= n -> return (SignExtend (m, m - n, sv))
    | CT_fbits (n, _), CT_lint -> return (SignExtend (lint_size, lint_size - n, sv))
    | CT_lbits _, CT_lint -> return (Extract (lint_size - 1, 0, Fn ("contents", [sv])))
    | _, _ -> builtin_type_error "signed" [v] (Some ret_ctyp)

  let builtin_unsigned v ret_ctyp =
    let* sv = smt_cval v in
    match (cval_ctyp v, ret_ctyp) with
    | CT_fbits (n, _), CT_fint m when m > n -> return (Fn ("concat", [bvzero (m - n); sv]))
    | CT_fbits (n, _), CT_lint -> return (Fn ("concat", [bvzero (lint_size - n); sv]))
    | CT_lbits _, CT_lint -> force_size lint_size lbits_size (Fn ("contents", [sv]))
    | CT_lbits _, CT_fint m -> force_size m lbits_size (Fn ("contents", [sv]))
    | _, _ -> builtin_type_error "unsigned" [v] (Some ret_ctyp)

  let bvmask len =
    let all_ones = bvones lbits_size in
    let shift = Fn ("concat", [bvzero (lbits_size - lbits_index); len]) in
    bvnot (bvshl all_ones shift)

  let builtin_shift shiftop vbits vshift ret_ctyp =
    match cval_ctyp vbits with
    | CT_fbits (n, _) ->
        let* bv = smt_cval vbits in
        let* len = bvzeint n vshift in
        return (Fn (shiftop, [bv; len]))
    | CT_lbits _ ->
        let* bv = smt_cval vbits in
        let* shift = bvzeint lbits_size vshift in
        return (Fn ("Bits", [Fn ("len", [bv]); Fn (shiftop, [Fn ("contents", [bv]); shift])]))
    | _ -> builtin_type_error shiftop [vbits; vshift] (Some ret_ctyp)

  let builtin_slice v1 v2 v3 ret_ctyp =
    match (cval_ctyp v1, cval_ctyp v2, cval_ctyp v3, ret_ctyp) with
    | CT_lbits _, CT_constant start, CT_constant len, CT_fbits (_, _) ->
        let top = Big_int.pred (Big_int.add start len) in
        let* v1 = smt_cval v1 in
        return (Extract (Big_int.to_int top, Big_int.to_int start, Fn ("contents", [v1])))
    | CT_fbits (_, _), CT_constant start, CT_constant len, CT_fbits (_, _) ->
        let top = Big_int.pred (Big_int.add start len) in
        let* v1 = smt_cval v1 in
        return (Extract (Big_int.to_int top, Big_int.to_int start, v1))
    | CT_fbits (_, ord), CT_fint _, CT_constant len, CT_fbits (_, _) ->
        let* shifted = builtin_shift "bvlshr" v1 v2 (cval_ctyp v1) in
        return (Extract (Big_int.to_int (Big_int.pred len), 0, shifted))
    | ctyp1, ctyp2, _, CT_lbits _ ->
        let* smt1 = bind (smt_cval v1) (force_size lbits_size (bv_size ctyp1)) in
        let* smt2 = bind (smt_cval v2) (force_size lbits_size (int_size ctyp2)) in
        let* smt3 = bvzeint lbits_index v3 in
        return (Fn ("Bits", [smt3; Fn ("bvand", [Fn ("bvlshr", [Fn ("contents", [smt1]); smt2]); bvmask smt3])]))
    | _ -> builtin_type_error "slice" [v1; v2; v3] (Some ret_ctyp)

  let builtin_zeros v ret_ctyp =
    match (cval_ctyp v, ret_ctyp) with
    | _, CT_fbits (n, _) -> return (bvzero n)
    | CT_constant c, CT_lbits _ -> return (Fn ("Bits", [bvint lbits_index c; bvzero lbits_size]))
    | ctyp, CT_lbits _ when int_size ctyp >= lbits_index ->
        let* v = smt_cval v in
        return (Fn ("Bits", [extract (lbits_index - 1) 0 v; bvzero lbits_size]))
    | _ -> builtin_type_error "zeros" [v] (Some ret_ctyp)

  let builtin_ones cval = function
    | CT_fbits (n, _) -> return (bvones n)
    | CT_lbits _ ->
        let* v = smt_cval cval in
        let len = extract (lbits_index - 1) 0 v in
        return (Fn ("Bits", [len; Fn ("bvand", [bvmask len; bvones lbits_size])]))
    | ret_ctyp -> builtin_type_error "ones" [cval] (Some ret_ctyp)

  let builtin_zero_extend vbits vlen ret_ctyp =
    match (cval_ctyp vbits, ret_ctyp) with
    | CT_fbits (n, _), CT_fbits (m, _) when n = m -> smt_cval vbits
    | CT_fbits (n, _), CT_fbits (m, _) ->
        let* bv = smt_cval vbits in
        return (Fn ("concat", [bvzero (m - n); bv]))
        (*
    | CT_lbits _, CT_fbits (m, _) ->
      assert (lbits_size ctx >= m);
      Extract (m - 1, 0, Fn ("contents", [smt_cval ctx vbits]))
    | CT_fbits (n, _), CT_lbits _ ->
      assert (lbits_size ctx >= n);
      let vbits =
        if lbits_size ctx = n then smt_cval ctx vbits
        else if lbits_size ctx > n then Fn ("concat", [bvzero (lbits_size ctx - n); smt_cval ctx vbits])
        else assert false
      in
      Fn ("Bits", [bvzeint ctx ctx.lbits_index vlen; vbits])
           *)
    | _ -> builtin_type_error "zero_extend" [vbits; vlen] (Some ret_ctyp)

  let builtin_sign_extend vbits vlen ret_ctyp =
    match (cval_ctyp vbits, ret_ctyp) with
    | CT_fbits (n, _), CT_fbits (m, _) when n = m ->
        smt_cval vbits
        (*
    | CT_fbits (n, _), CT_fbits (m, _) ->
      let* bv = smt_cval ctx vbits in
      let top_bit_one = Fn ("=", [Extract (n - 1, n - 1, bv); Bitvec_lit [Sail2_values.B1]]) in
      Ite (top_bit_one, Fn ("concat", [bvones (m - n); bv]), Fn ("concat", [bvzero (m - n); bv]))
                                                          *)
    | _ -> builtin_type_error "sign_extend" [vbits; vlen] (Some ret_ctyp)

  let builtin_not_bits v ret_ctyp =
    match (cval_ctyp v, ret_ctyp) with
    | CT_lbits _, CT_fbits (n, _) ->
        let* bv = smt_cval v in
        return (bvnot (Extract (n - 1, 0, Fn ("contents", [bv]))))
    | CT_lbits _, CT_lbits _ ->
        let* bv = smt_cval v in
        let len = Fn ("len", [bv]) in
        return (Fn ("Bits", [len; Fn ("bvand", [bvmask len; bvnot (Fn ("contents", [bv]))])]))
    | CT_fbits (n, _), CT_fbits (m, _) when n = m ->
        let* bv = smt_cval v in
        return (bvnot bv)
    | _, _ -> builtin_type_error "not_bits" [v] (Some ret_ctyp)

  let builtin_add_bits v1 v2 ret_ctyp =
    let* smt1 = smt_cval v1 in
    let* smt2 = smt_cval v2 in
    match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
    | CT_fbits (n, _), CT_fbits (m, _), CT_fbits (o, _) ->
        (* The Sail type system should guarantee this *)
        assert (n = m && m = o);
        return (Fn ("bvadd", [smt1; smt2]))
    | CT_lbits _, CT_lbits _, CT_lbits _ ->
        return (Fn ("Bits", [Fn ("len", [smt1]); Fn ("bvadd", [Fn ("contents", [smt1]); Fn ("contents", [smt2])])]))
    | _ -> builtin_type_error "add_bits" [v1; v2] (Some ret_ctyp)

  let builtin_add_bits_int v1 v2 ret_ctyp =
    let* smt1 = smt_cval v1 in
    let* smt2 = smt_cval v2 in
    match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
    | CT_fbits (n, _), CT_constant c, CT_fbits (o, _) ->
        assert (n = o);
        return (bvadd smt1 (bvint o c))
    | CT_fbits (n, _), CT_fint m, CT_fbits (o, _) ->
        assert (n = o);
        let* smt2 = force_size o lint_size smt2 in
        return (bvadd smt1 smt2)
    | CT_fbits (n, _), CT_lint, CT_fbits (o, _) ->
        assert (n = o);
        let* smt2 = force_size o lint_size smt2 in
        return (bvadd smt1 smt2)
    | CT_lbits _, CT_fint n, CT_lbits _ when n < lbits_size ->
        let* smt2 = force_size lbits_size n smt2 in
        return (Fn ("Bits", [Fn ("len", [smt1]); bvadd (Fn ("contents", [smt1])) smt2]))
    | _ -> builtin_type_error "add_bits_int" [v1; v2] (Some ret_ctyp)

  let builtin_eq_bits v1 v2 =
    match (cval_ctyp v1, cval_ctyp v2) with
    | CT_fbits (n, _), CT_fbits (m, _) ->
        let o = max n m in
        let* smt1 = bind (smt_cval v1) (unsigned_size o n) in
        let* smt2 = bind (smt_cval v2) (unsigned_size o n) in
        return (Fn ("=", [smt1; smt2]))
    | CT_lbits _, CT_lbits _ ->
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
        (*
    | CT_lbits _, CT_fbits (n, _) ->
      let smt1 = unsigned_size ctx n (lbits_size ctx) (Fn ("contents", [smt_cval ctx v1])) in
      Fn ("=", [smt1; smt_cval ctx v2])
    | CT_fbits (n, _), CT_lbits _ ->
      let smt2 = unsigned_size ctx n (lbits_size ctx) (Fn ("contents", [smt_cval ctx v2])) in
      Fn ("=", [smt_cval ctx v1; smt2])
           *)
    | _ -> builtin_type_error "eq_bits" [v1; v2] None

  let builtin_append v1 v2 ret_ctyp =
    match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
    | CT_fbits (n, _), CT_fbits (m, _), CT_fbits (o, _) ->
        assert (n + m = o);
        let* smt1 = smt_cval v1 in
        let* smt2 = smt_cval v2 in
        return (Fn ("concat", [smt1; smt2]))
    | CT_fbits (n, _), CT_lbits _, CT_lbits _ ->
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
    | CT_lbits _, CT_fbits (n, _), CT_fbits (m, _) ->
        let* smt1 = smt_cval v1 in
        let* smt2 = smt_cval v2 in
        return (Extract (m - 1, 0, Fn ("concat", [Fn ("contents", [smt1]); smt2])))
        (*
    | CT_lbits _, CT_fbits (n, _), CT_lbits _ ->
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      Fn
        ( "Bits",
          [
            bvadd (bvint ctx.lbits_index (Big_int.of_int n)) (Fn ("len", [smt1]));
            Extract (lbits_size ctx - 1, 0, Fn ("concat", [Fn ("contents", [smt1]); smt2]));
          ]
        )
    | CT_fbits (n, _), CT_fbits (m, _), CT_lbits _ ->
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      Fn
        ( "Bits",
          [
            bvint ctx.lbits_index (Big_int.of_int (n + m));
            unsigned_size ctx (lbits_size ctx) (n + m) (Fn ("concat", [smt1; smt2]));
          ]
        )
    | CT_lbits _, CT_lbits _, CT_lbits _ ->
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      let x = Fn ("contents", [smt1]) in
      let shift = Fn ("concat", [bvzero (lbits_size ctx - ctx.lbits_index); Fn ("len", [smt2])]) in
      Fn ("Bits", [bvadd (Fn ("len", [smt1])) (Fn ("len", [smt2])); bvor (bvshl x shift) (Fn ("contents", [smt2]))])
    | CT_lbits _, CT_lbits _, CT_fbits (n, _) ->
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      let x = Fn ("contents", [smt1]) in
      let shift = Fn ("concat", [bvzero (lbits_size ctx - ctx.lbits_index); Fn ("len", [smt2])]) in
      unsigned_size ctx n (lbits_size ctx) (bvor (bvshl x shift) (Fn ("contents", [smt2])))
           *)
    | _ -> builtin_type_error "append" [v1; v2] (Some ret_ctyp)

  let to_fbits ctyp bv = match ctyp with CT_fbits (n, _) -> (n, bv) | CT_lbits _ -> (lbits_size, Fn ("contents", [bv]))

  let fbits_mask mask_sz len = bvnot (bvshl (bvones mask_sz) len)

  let builtin_vector_subrange vec i j ret_ctyp =
    match (cval_ctyp vec, cval_ctyp i, cval_ctyp j, ret_ctyp) with
    | CT_fbits (n, _), CT_constant i, CT_constant j, CT_fbits _ ->
        let* vec = smt_cval vec in
        return (Extract (Big_int.to_int i, Big_int.to_int j, vec))
    | CT_lbits _, CT_constant i, CT_constant j, CT_fbits _ ->
        let* vec = smt_cval vec in
        return (Extract (Big_int.to_int i, Big_int.to_int j, Fn ("contents", [vec])))
        (*
    | CT_fbits (n, _), i_ctyp, CT_constant j, CT_lbits _ when Big_int.equal j Big_int.zero ->
      let i' = force_size ~checked:false ctx ctx.lbits_index (int_size ctx i_ctyp) (smt_cval ctx i) in
      let len = bvadd i' (bvint ctx.lbits_index (Big_int.of_int 1)) in
      Fn ("Bits", [len; Fn ("bvand", [bvmask ctx len; unsigned_size ctx (lbits_size ctx) n (smt_cval ctx vec)])])
           *)
    | bv_ctyp, i_ctyp, j_ctyp, ret_ctyp ->
        let* vec = smt_cval vec in
        let sz, vec = to_fbits bv_ctyp vec in
        let* i' = bind (smt_cval i) (force_size sz (int_size i_ctyp)) in
        let* j' = bind (smt_cval j) (force_size sz (int_size j_ctyp)) in
        let len = bvadd (bvadd i' (bvneg j')) (bvint sz (Big_int.of_int 1)) in
        let extracted = bvand (bvlshr vec j') (fbits_mask sz len) in
        smt_conversion (CT_fbits (sz, false)) ret_ctyp extracted
    | _ -> builtin_type_error "vector_subrange" [vec; i; j] (Some ret_ctyp)

  let builtin_get_slice_int v1 v2 v3 ret_ctyp =
    match (cval_ctyp v1, cval_ctyp v2, cval_ctyp v3, ret_ctyp) with
    | CT_constant len, ctyp, CT_constant start, CT_fbits (ret_sz, _) ->
        let len = Big_int.to_int len in
        let start = Big_int.to_int start in
        let in_sz = int_size ctyp in
        let* smt = if in_sz < len + start then bind (smt_cval v2) (force_size (len + start) in_sz) else smt_cval v2 in
        return (Extract (start + len - 1, start, smt))
    | CT_lint, CT_lint, CT_constant start, CT_lbits _ when Big_int.equal start Big_int.zero ->
        let* v1 = smt_cval v1 in
        let len = Extract (lbits_index - 1, 0, v1) in
        let* contents = bind (smt_cval v2) (unsigned_size lbits_size lint_size) in
        return (Fn ("Bits", [len; bvand (bvmask len) contents]))
    | CT_lint, ctyp2, ctyp3, ret_ctyp ->
        let* smt1 = smt_cval v1 in
        let len = Extract (lbits_index - 1, 0, smt1) in
        let* smt2 = bind (smt_cval v2) (force_size lbits_size (int_size ctyp2)) in
        let* smt3 = bind (smt_cval v3) (force_size lbits_size (int_size ctyp3)) in
        let result = Fn ("Bits", [len; bvand (bvmask len) (bvlshr smt2 smt3)]) in
        smt_conversion (CT_lbits true) ret_ctyp result
    | _ -> builtin_type_error "get_slice_int" [v1; v2; v3] (Some ret_ctyp)

  let builtin name args ret_ctyp =
    match (name, args, ret_ctyp) with
    | "eq_bit", [v1; v2], _ ->
        let* smt1 = smt_cval v1 in
        let* smt2 = smt_cval v2 in
        return (Fn ("=", [smt1; smt2]))
    | "eq_bool", [v1; v2], _ ->
        let* smt1 = smt_cval v1 in
        let* smt2 = smt_cval v2 in
        return (Fn ("=", [smt1; smt2]))
    | "eq_int", [v1; v2], _ -> builtin_eq_int v1 v2
    | "not", [v], _ ->
        let* v = smt_cval v in
        return (Fn ("not", [v]))
    | "lt", [v1; v2], _ -> builtin_lt v1 v2
    | "lteq", [v1; v2], _ -> builtin_lteq v1 v2
    | "gt", [v1; v2], _ -> builtin_gt v1 v2
    | "gteq", [v1; v2], _ -> builtin_gteq v1 v2 (* arithmetic operations *)
    | "add_int", [v1; v2], _ -> builtin_add_int v1 v2 ret_ctyp
    | "sub_int", [v1; v2], _ ->
        builtin_sub_int v1 v2 ret_ctyp
        (*
  | "sub_nat", [v1; v2], _ -> builtin_sub_nat v1 v2 ret_ctyp
                                    *)
    | "mult_int", [v1; v2], _ -> builtin_mult_int v1 v2 ret_ctyp
    (*
  | "neg_int", [v], _ -> builtin_negate_int v ret_ctyp
  | "shl_int", [v1; v2], _ -> builtin_shl_int v1 v2 ret_ctyp
  | "shr_int", [v1; v2], _ -> builtin_shr_int v1 v2 ret_ctyp
  | "shl_mach_int", [v1; v2], _ -> builtin_shl_int v1 v2 ret_ctyp
  | "shr_mach_int", [v1; v2], _ -> builtin_shr_int v1 v2 ret_ctyp
  | "abs_int", [v], _ -> builtin_abs_int v ret_ctyp
  | "pow2", [v], _ -> builtin_pow2 v ret_ctyp
  | "max_int", [v1; v2], _ -> builtin_max_int v1 v2 ret_ctyp
  | "min_int", [v1; v2], _ -> builtin_min_int v1 v2 ret_ctyp
  | "ediv_int", [v1; v2], _ -> builtin_tdiv_int v1 v2 ret_ctyp
                                    *)
    (* bitvector operations *)
    | "zeros", [v], _ -> builtin_zeros v ret_ctyp
    | "ones", [v], _ -> builtin_ones v ret_ctyp
    | "zero_extend", [v1; v2], _ -> builtin_zero_extend v1 v2 ret_ctyp
    | "sign_extend", [v1; v2], _ -> builtin_sign_extend v1 v2 ret_ctyp
    | "sail_signed", [v], _ -> builtin_signed v ret_ctyp
    | "sail_unsigned", [v], _ -> builtin_unsigned v ret_ctyp
    | "slice", [v1; v2; v3], _ -> builtin_slice v1 v2 v3 ret_ctyp
    | "add_bits", [v1; v2], _ -> builtin_add_bits v1 v2 ret_ctyp
    | "add_bits_int", [v1; v2], _ -> builtin_add_bits_int v1 v2 ret_ctyp
    | "get_slice_int", [v1; v2; v3], _ -> builtin_get_slice_int v1 v2 v3 ret_ctyp
    | "eq_bits", [v1; v2], _ -> builtin_eq_bits v1 v2
    | "not_bits", [v], _ -> builtin_not_bits v ret_ctyp
    | "append", [v1; v2], _ -> builtin_append v1 v2 ret_ctyp
    | "vector_subrange", [v1; v2; v3], ret_ctyp -> builtin_vector_subrange v1 v2 v3 ret_ctyp
    | "print_endline", [v], _ ->
        let* v = smt_cval v in
        return (Fn ("sail_print_endline", [v]))
    | "prerr_endline", [v], _ ->
        let* v = smt_cval v in
        return (Fn ("sail_prerr_endline", [v]))
    | "print", [v], _ ->
        let* v = smt_cval v in
        return (Fn ("sail_print", [v]))
    | "prerr", [v], _ ->
        let* v = smt_cval v in
        return (Fn ("sail_prerr", [v]))
    | "print_bits", [str; bv], _ ->
        let op = Primop_gen.print_bits (cval_ctyp bv) in
        let* str = smt_cval str in
        let* bv = smt_cval bv in
        return (Fn (op, [str; bv]))
    | "print_int", [str; i], _ ->
        let* str = smt_cval str in
        let* i = smt_cval i in
        return (Fn ("sail_print_int", [str; i]))
    | "sail_assert", [b; msg], _ ->
        let* b = smt_cval b in
        let* msg = smt_cval msg in
        return (Fn ("sail_assert", [b; msg]))
    | "eq_string", [s1; s2], _ ->
        let* s1 = smt_cval s1 in
        let* s2 = smt_cval s2 in
        return (Fn ("sail_eq_string", [s1; s2]))
    | name, _, _ -> Reporting.unreachable Parse_ast.Unknown __POS__ ("No implementation for " ^ name)
end
