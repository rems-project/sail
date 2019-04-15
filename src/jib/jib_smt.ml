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

open Anf
open Ast
open Ast_util
open Jib
open Jib_util
open Smtlib

let ignore_overflow = ref false

let zencode_upper_id id = Util.zencode_upper_string (string_of_id id)
let zencode_id id = Util.zencode_string (string_of_id id)
let zencode_name id = string_of_name ~deref_current_exception:false ~zencode:true id

let lbits_index = ref 8

let lbits_size () = Util.power 2 !lbits_index

let lint_size = ref 128

let smt_unit = mk_enum "Unit" ["Unit"]
let smt_lbits = mk_record "Bits" [("size", Bitvec !lbits_index); ("bits", Bitvec (lbits_size ()))]

let required_width n =
  let rec required_width' n =
    if Big_int.equal n Big_int.zero then
      1
    else
      1 + required_width' (Big_int.shift_right n 1)
  in
  required_width' (Big_int.abs n)

let rec smt_ctyp = function
  | CT_constant n -> Bitvec (required_width n)
  | CT_fint n -> Bitvec n
  | CT_lint -> Bitvec !lint_size
  | CT_unit -> smt_unit
  | CT_bit -> Bitvec 1
  | CT_fbits (n, _) -> Bitvec n
  | CT_sbits (n, _) -> smt_lbits
  | CT_lbits _ -> smt_lbits
  | CT_bool -> Bool
  | CT_enum (id, elems) ->
     mk_enum (zencode_upper_id id) (List.map zencode_id elems)
  | CT_struct (id, fields) ->
     mk_record (zencode_upper_id id) (List.map (fun (id, ctyp) -> (zencode_id id, smt_ctyp ctyp)) fields)
  | CT_variant (id, ctors) ->
     mk_variant (zencode_upper_id id) (List.map (fun (id, ctyp) -> (zencode_id id, smt_ctyp ctyp)) ctors)
  | CT_tup ctyps -> Tuple (List.map smt_ctyp ctyps)
  | CT_vector (_, ctyp) -> Array (Bitvec 8, smt_ctyp ctyp)
  | CT_string -> Bitvec 64
  | ctyp -> failwith ("Unhandled ctyp: " ^ string_of_ctyp ctyp)

let bvpint sz x =
  if Big_int.less_equal Big_int.zero x && Big_int.less_equal x (Big_int.of_int max_int) then (
    let open Sail_lib in
    let x = Big_int.to_int x in
    if sz mod 4 = 0 then
      let hex = Printf.sprintf "%X" x in
      let padding = String.make (sz / 4 - String.length hex) '0' in
      Hex (padding ^ hex)
    else
      let bin = Printf.sprintf "%X" x |> list_of_string |> List.map hex_char |> List.concat in
      let _, bin = Util.take_drop (function B0 -> true | B1 -> false) bin in
      let bin = String.concat "" (List.map string_of_bit bin) in
      let padding = String.make (sz - String.length bin) '0' in
      Bin (padding ^ bin)
  ) else if Big_int.greater x (Big_int.of_int max_int) then (
    let open Sail_lib in
    let y = ref x in
    let bin = ref [] in
    while (not (Big_int.equal !y Big_int.zero)) do
      let (q, m) = Big_int.quomod !y (Big_int.of_int 2) in
      bin := (if Big_int.equal m Big_int.zero then B0 else B1) :: !bin;
      y := q
    done;
    let bin = String.concat "" (List.map string_of_bit !bin) in
    let padding_size = sz - String.length bin in
    if padding_size < 0 then
      raise (Reporting.err_general Parse_ast.Unknown
               (Printf.sprintf "Count not create a %d-bit integer with value %s.\nTry increasing the maximum integer size"
                  sz (Big_int.to_string x)));
    let padding = String.make (sz - String.length bin) '0' in
    Bin (padding ^ bin)
  ) else failwith "Invalid bvpint"

let bvint sz x =
  if Big_int.less x Big_int.zero then
    Fn ("bvadd", [Fn ("bvnot", [bvpint sz (Big_int.abs x)]); bvpint sz (Big_int.of_int 1)])
  else
    bvpint sz x

let smt_value vl ctyp =
  let open Value2 in
  match vl, ctyp with
  | VL_bits (bs, true), _ ->
     begin match Sail2_values.hexstring_of_bits bs with
     | Some s -> Hex (Xstring.implode s)
     | None -> Bin (Xstring.implode (List.map Sail2_values.bitU_char bs))
     end
  | VL_bool b, _ -> Bool_lit b
  | VL_int n, CT_constant m -> bvint (required_width n) n
  | VL_int n, CT_fint sz -> bvint sz n
  | VL_int n, CT_lint -> bvint !lint_size n
  | VL_bit Sail2_values.B0, CT_bit -> Bin "0"
  | VL_bit Sail2_values.B1, CT_bit -> Bin "1"
  | VL_unit, _ -> Var "unit"
  | vl, _ -> failwith ("Cannot translate literal to SMT " ^ string_of_value vl)

let zencode_ctor ctor_id unifiers =
  match unifiers with
  | [] ->
     zencode_id ctor_id
  | _ ->
     Util.zencode_string (string_of_id ctor_id ^ "_" ^ Util.string_of_list "_" string_of_ctyp unifiers)

let rec smt_cval env cval =
  match cval with
  | V_lit (vl, ctyp) -> smt_value vl ctyp
  | V_id (Name (id, _) as ssa_id, _) ->
     begin match Type_check.Env.lookup_id id env with
     | Enum _ -> Var (zencode_id id)
     | _ -> Var (zencode_name ssa_id)
     end
  | V_id (ssa_id, _) -> Var (zencode_name ssa_id)
  | V_op (frag1, "!=", frag2) ->
     Fn ("not", [Fn ("=", [smt_cval env frag1; smt_cval env frag2])])
  | V_unary ("!", cval) ->
     Fn ("not", [smt_cval env cval])
  | V_ctor_kind (union, ctor_id, unifiers, _) ->
     Fn ("not", [Tester (zencode_ctor ctor_id unifiers, smt_cval env union)])
  | V_ctor_unwrap (ctor_id, union, unifiers, _) ->
     Fn ("un" ^ zencode_ctor ctor_id unifiers, [smt_cval env union])
  | V_field (union, field) ->
     begin match cval_ctyp union with
     | CT_struct (struct_id, _) ->
        Fn (zencode_upper_id struct_id ^ "_" ^ field, [smt_cval env union])
     | _ -> failwith "Field for non-struct type"
     end
  | V_tuple_member (frag, len, n) ->
     Fn (Printf.sprintf "tup_%d_%d" len n, [smt_cval env frag])
  | cval -> failwith ("Unrecognised cval " ^ string_of_cval ~zencode:false cval)


let overflow_checks = Stack.create ()

let overflow_check smt =
  if not !ignore_overflow then (
    Util.warn "Adding overflow check in generated SMT";
    Stack.push (Define_const ("overflow" ^ string_of_int (Stack.length overflow_checks), Bool, Fn ("not", [smt]))) overflow_checks
  )

let builtin_type_error fn cvals =
  let args = Util.string_of_list ", " (fun cval -> string_of_ctyp (cval_ctyp cval)) cvals in
  function
  | Some ret_ctyp ->
     Reporting.unreachable Parse_ast.Unknown __POS__
       (Printf.sprintf "%s : (%s) -> %s" fn args (string_of_ctyp ret_ctyp))
  | None ->
     Reporting.unreachable Parse_ast.Unknown __POS__ (Printf.sprintf "%s : (%s)" fn args)

(* ***** Basic comparisons: lib/flow.sail ***** *)

let builtin_int_comparison fn big_int_fn env v1 v2 =
  match cval_ctyp v1, cval_ctyp v2 with
  | CT_lint, CT_lint ->
     Fn (fn, [smt_cval env v1; smt_cval env v2])
  | CT_fint sz1, CT_fint sz2 ->
     if sz1 == sz2 then
       Fn (fn, [smt_cval env v1; smt_cval env v2])
     else if sz1 > sz2 then
       Fn (fn, [smt_cval env v1; SignExtend (sz1 - sz2, smt_cval env v2)])
     else
       Fn (fn, [SignExtend (sz2 - sz1, smt_cval env v1); smt_cval env v2])
  | CT_constant c, CT_fint sz ->
     Fn (fn, [bvint sz c; smt_cval env v2])
  | CT_constant c, CT_lint ->
     Fn (fn, [bvint !lint_size c; smt_cval env v2])
  | CT_fint sz, CT_constant c ->
     Fn (fn, [smt_cval env v1; bvint sz c])
  | CT_lint, CT_constant c ->
     Fn (fn, [smt_cval env v1; bvint !lint_size c])
  | CT_constant c1, CT_constant c2 ->
     Bool_lit (big_int_fn c1 c2)
  | _, _ -> builtin_type_error fn [v1; v2] None

let builtin_eq_int = builtin_int_comparison "=" Big_int.equal

let builtin_lt = builtin_int_comparison "bvslt" Big_int.less
let builtin_lteq = builtin_int_comparison "bvsle" Big_int.less_equal
let builtin_gt = builtin_int_comparison "bvsgt" Big_int.greater
let builtin_gteq = builtin_int_comparison "bvsge" Big_int.greater_equal

(* ***** Arithmetic operations: lib/arith.sail ***** *)

(** [force_size n m exp] takes a smt expression assumed to be a
   integer (signed bitvector) of length m and forces it to be length n
   by either sign extending it or truncating it as required *)
let force_size n m smt =
  if n = m then
    smt
  else if n > m then
    SignExtend (n - m, smt)
  else
    let check =
      (* If the top bit of the truncated number is one *)
      Ite (Fn ("=", [Extract (n - 1, n - 1, smt); Bin "1"]),
           (* Then we have an overflow, unless all bits we truncated were also one *)
           Fn ("not", [Fn ("=", [Extract (m - 1, n, smt); bvones (m - n)])]),
           (* Otherwise, all the top bits must be zero *)
           Fn ("not", [Fn ("=", [Extract (m - 1, n, smt); bvzero (m - n)])]))
    in
    overflow_check check;
    Extract (n - 1, 0, smt)

let int_size = function
  | CT_constant n -> required_width n
  | CT_fint sz -> sz
  | CT_lint -> !lint_size
  | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Argument to int_size must be an integer type"

let builtin_arith fn big_int_fn padding env v1 v2 ret_ctyp =
  (* To detect arithmetic overflow we can expand the input bitvectors
     to some size determined by a padding function, then check we
     don't lose precision when going back after performing the
     operation. *)
  let padding = if !ignore_overflow then (fun x -> x) else padding in
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | _, _, CT_constant c ->
     bvint (required_width c) c
  | CT_constant c1, CT_constant c2, _ ->
     bvint (int_size ret_ctyp) (big_int_fn c1 c2)

  | ctyp, CT_constant c, _ ->
     let n = int_size ctyp in
     force_size (int_size ret_ctyp) n (Fn (fn, [smt_cval env v1; bvint n c]))
  | CT_constant c, ctyp, _ ->
     let n = int_size ctyp in
     force_size (int_size ret_ctyp) n (Fn (fn, [bvint n c; smt_cval env v2]))

  | ctyp1, ctyp2, _ ->
     let ret_sz = int_size ret_ctyp in
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     force_size ret_sz (padding ret_sz) (Fn (fn, [force_size (padding ret_sz) (int_size ctyp1) smt1;
                                                  force_size (padding ret_sz) (int_size ctyp2) smt2]))

let builtin_add_int = builtin_arith "bvadd" Big_int.add (fun x -> x + 1)
let builtin_sub_int = builtin_arith "bvsub" Big_int.sub (fun x -> x + 1)
let builtin_mult_int = builtin_arith "bvmul" Big_int.mul (fun x -> x * 2)

let builtin_negate_int env v ret_ctyp =
  match cval_ctyp v, ret_ctyp with
  | _, CT_constant c ->
     bvint (required_width c) c
  | CT_constant c, _ ->
     bvint (int_size ret_ctyp) (Big_int.negate c)
  | ctyp, _ ->
     let smt = force_size (int_size ret_ctyp) (int_size ctyp) (smt_cval env v) in
     overflow_check (Fn ("=", [smt; Bin ("1" ^ String.make (int_size ret_ctyp - 1) '0')]));
     Fn ("bvneg", [smt])

let builtin_shift_int fn big_int_fn env v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | _, _, CT_constant c ->
     bvint (required_width c) c
  | CT_constant c1, CT_constant c2, _ ->
     bvint (int_size ret_ctyp) (big_int_fn c1 (Big_int.to_int c2))

  | ctyp, CT_constant c, _ ->
     let n = int_size ctyp in
     force_size (int_size ret_ctyp) n (Fn (fn, [smt_cval env v1; bvint n c]))
  | CT_constant c, ctyp, _ ->
     let n = int_size ctyp in
     force_size (int_size ret_ctyp) n (Fn (fn, [bvint n c; smt_cval env v2]))

  | ctyp1, ctyp2, _ ->
     let ret_sz = int_size ret_ctyp in
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     (Fn (fn, [force_size ret_sz (int_size ctyp1) smt1;
               force_size ret_sz (int_size ctyp2) smt2]))

let builtin_shl_int = builtin_shift_int "bvshl" Big_int.shift_left
let builtin_shr_int = builtin_shift_int "bvashr" Big_int.shift_right

let builtin_abs_int env v ret_ctyp =
  match cval_ctyp v, ret_ctyp with
  | _, CT_constant c ->
     bvint (required_width c) c
  | CT_constant c, _ ->
     bvint (int_size ret_ctyp) (Big_int.abs c)
  | ctyp, _ ->
     let sz = int_size ctyp in
     let smt = smt_cval env v in
     Ite (Fn ("=", [Extract (sz - 1, sz -1, smt); Bin "1"]),
          force_size (int_size ret_ctyp) sz (Fn ("bvneg", [smt])),
          force_size (int_size ret_ctyp) sz smt)

let builtin_zeros env v ret_ctyp =
  match cval_ctyp v, ret_ctyp with
  | _, CT_fbits (n, _) -> bvzero n
  | CT_constant c, CT_lbits _ ->
     Fn ("Bits", [bvint !lbits_index c; bvzero (lbits_size ())])
  | ctyp, CT_lbits _ when int_size ctyp >= !lbits_index ->
     Fn ("Bits", [extract (!lbits_index - 1) 0 (smt_cval env v); bvzero (lbits_size ())])
  | _ -> builtin_type_error "zeros" [v] (Some ret_ctyp)

let bvmask len =
  let all_ones = bvones (lbits_size ()) in
  let shift = Fn ("concat", [bvzero (lbits_size () - !lbits_index); len]) in
  bvnot (bvshl all_ones shift)
       
let builtin_ones env cval = function
  | CT_fbits (n, _) -> bvones n
  | CT_lbits _ ->
     let len = extract (!lbits_index - 1) 0 (smt_cval env cval) in
     Fn ("Bits", [len; Fn ("bvand", [bvmask len; bvones (lbits_size ())])]); 
  | ret_ctyp -> builtin_type_error "ones" [cval] (Some ret_ctyp)
     
let builtin_zero_extend env vbits vlen ret_ctyp =
  match cval_ctyp vbits, ret_ctyp with
  | CT_fbits (n, _), CT_fbits (m, _) when n = m ->
     smt_cval env vbits
  | CT_fbits (n, _), CT_fbits (m, _) ->
     let bv = smt_cval env vbits in
     Fn ("concat", [bvzero (m - n); bv])
  | CT_lbits _, CT_fbits (m, _) ->
     assert (lbits_size () >= m);
     Extract (m - 1, 0, Fn ("contents", [smt_cval env vbits]))
     
  | _ -> builtin_type_error "zero_extend" [vbits; vlen] (Some ret_ctyp)

let builtin_sign_extend env vbits vlen ret_ctyp =
  match cval_ctyp vbits, ret_ctyp with
  | CT_fbits (n, _), CT_fbits (m, _) when n = m ->
     smt_cval env vbits
  | CT_fbits (n, _), CT_fbits (m, _) ->
     let bv = smt_cval env vbits in
     let top_bit_one = Fn ("=", [Extract (n - 1, n - 1, bv); Bin "1"]) in
     Ite (top_bit_one, Fn ("concat", [bvones (m - n); bv]), Fn ("concat", [bvzero (m - n); bv]))
     
  | _ -> failwith "Cannot compile zero_extend"

(* [bvzeint esz cval] (BitVector Zero Extend INTeger), takes a cval
   which must be an integer type (either CT_fint, or CT_lint), and
   produces a bitvector which is either zero extended or truncated to
   exactly esz bits. *)
let bvzeint env esz cval =
  let sz = int_size (cval_ctyp cval) in
  match cval with
  | V_lit (VL_int n, _) ->
     bvint esz n
  | _ ->
     let smt = smt_cval env cval in
     if esz = sz then
       smt
     else if esz > sz then
       Fn ("concat", [bvzero (esz - sz); smt])
     else
       Extract (esz - 1, 0, smt)

let builtin_shift shiftop env vbits vshift ret_ctyp =
  match cval_ctyp vbits with
  | CT_fbits (n, _) ->
     let bv = smt_cval env vbits in
     let len = bvzeint env n vshift in
     Fn (shiftop, [bv; len])

  | CT_lbits _ ->
     let bv = smt_cval env vbits in
     let shift = bvzeint env (lbits_size ()) vshift in
     Fn ("Bits", [Fn ("len", [bv]); Fn (shiftop, [Fn ("contents", [bv]); shift])])

  | _ -> failwith ("Cannot compile shift: " ^ shiftop)

let builtin_not_bits env v ret_ctyp =
  match cval_ctyp v, ret_ctyp with
  | CT_lbits _, CT_fbits (n, _) ->
     bvnot (Extract (n - 1, 0, Fn ("contents", [smt_cval env v])))

  | CT_lbits _, CT_lbits _ ->
     let bv = smt_cval env v in
     let len = Fn ("len", [bv]) in
     Fn ("Bits", [len; Fn ("bvand", [bvmask len; bvnot (Fn ("contents", [bv]))])])

  | CT_fbits (n, _), CT_fbits (m, _) when n = m ->
     bvnot (smt_cval env v)

  | _, _ -> builtin_type_error "not_bits" [v] (Some ret_ctyp)

let builtin_or_bits env v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2 with
  | CT_fbits (n, _), CT_fbits (m, _) ->
     assert (n = m);
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     bvor smt1 smt2

  | CT_lbits _, CT_lbits _ ->
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     Fn ("Bits", [Fn ("len", [smt1]); bvor (Fn ("contents", [smt1])) (Fn ("contents", [smt2]))])

  | _ -> failwith "Cannot compile or_bits"

let builtin_and_bits env v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2 with
  | CT_fbits (n, _), CT_fbits (m, _) ->
     assert (n = m);
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     bvand smt1 smt2

  | CT_lbits _, CT_lbits _ ->
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     Fn ("Bits", [Fn ("len", [smt1]); bvand (Fn ("contents", [smt1])) (Fn ("contents", [smt2]))])

  | _ -> failwith "Cannot compile or_bits"

let builtin_append env v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_fbits (m, _), CT_fbits (o, _) ->
     assert (n + m = o);
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     Fn ("concat", [smt1; smt2])

  | CT_fbits (n, _), CT_lbits _, CT_lbits _ ->
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     let x = Fn ("concat", [bvzero (lbits_size () - n); smt1]) in
     let shift = Fn ("concat", [bvzero (lbits_size () - !lbits_index); Fn ("len", [smt2])]) in
     Fn ("Bits", [bvadd (bvint !lbits_index (Big_int.of_int n)) (Fn ("len", [smt2]));
                  bvor (bvshl x shift) (Fn ("contents", [smt2]))])

  | CT_lbits _, CT_fbits (n, _), CT_lbits _ ->
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     Fn ("Bits", [bvadd (bvint !lbits_index (Big_int.of_int n)) (Fn ("len", [smt1]));
                  Extract (lbits_size () - 1, 0, Fn ("concat", [Fn ("contents", [smt1]); smt2]))])

  | CT_lbits _, CT_lbits _, CT_lbits _ ->
     let smt1 = smt_cval env v1 in
     let smt2 = smt_cval env v2 in
     let x = Fn ("contents", [smt1]) in
     let shift = Fn ("concat", [bvzero (lbits_size () - !lbits_index); Fn ("len", [smt2])]) in
     Fn ("Bits", [bvadd (Fn ("len", [smt1])) (Fn ("len", [smt2])); bvor (bvshl x shift) (Fn ("contents", [smt2]))])

  | _ -> builtin_type_error "append" [v1; v2] (Some ret_ctyp)

let builtin_length env v ret_ctyp =
  match cval_ctyp v, ret_ctyp with
  | CT_lbits _, CT_fint m ->
     let sz = !lbits_index in
     let len = Fn ("len", [smt_cval env v]) in
     if m = sz then
       len
     else if m > sz then
       Fn ("concat", [bvzero (m - sz); len])
     else
       Extract (m - 1, 0, len)

  | _, _ -> failwith "Cannot compile length"

let builtin_vector_subrange env vec i j ret_ctyp =
  match cval_ctyp vec, cval_ctyp i, cval_ctyp j with
  | CT_fbits (n, _), CT_constant i, CT_constant j ->
     Extract (Big_int.to_int i, Big_int.to_int j, smt_cval env vec)

  | _ -> failwith "Cannot compile vector subrange"

let builtin_vector_access env vec i ret_ctyp =
  match cval_ctyp vec, cval_ctyp i, ret_ctyp with
  | CT_fbits (n, _), CT_constant i, CT_bit ->
     Extract (Big_int.to_int i, Big_int.to_int i, smt_cval env vec)

  | _ -> failwith "Cannot compile vector subrange"

let builtin_vector_update env vec i x ret_ctyp =
  match cval_ctyp vec, cval_ctyp i, cval_ctyp x, ret_ctyp with
  | CT_fbits (n, _), CT_constant i, CT_bit, CT_fbits (m, _) when n - 1 > Big_int.to_int i && Big_int.to_int i > 0 ->
     assert (n = m);
     let top = Extract (n - 1, Big_int.to_int i + 1, smt_cval env vec) in
     let bot = Extract (Big_int.to_int i - 1, 0, smt_cval env vec) in
     Fn ("concat", [top; Fn ("concat", [smt_cval env x; bot])])

  | CT_fbits (n, _), CT_constant i, CT_bit, CT_fbits (m, _) when n - 1 = Big_int.to_int i ->
     let bot = Extract (Big_int.to_int i - 1, 0, smt_cval env vec) in
     Fn ("concat", [smt_cval env x; bot])

  | CT_fbits (n, _), CT_constant i, CT_bit, CT_fbits (m, _) when Big_int.to_int i = 0 ->
     let top = Extract (n - 1, 1, smt_cval env vec) in
     Fn ("concat", [top; smt_cval env x])

  | _ -> failwith "Cannot compile vector update"

let builtin_unsigned env v ret_ctyp =
  match cval_ctyp v, ret_ctyp with
  | CT_fbits (n, _), CT_fint m when m > n ->
     let smt = smt_cval env v in
     Fn ("concat", [bvzero (m - n); smt])

  | CT_fbits (n, _), CT_lint ->
     if n >= !lint_size then
       failwith "Overflow detected"
     else
       let smt = smt_cval env v in
       Fn ("concat", [bvzero (!lint_size - n); smt])

  | ctyp, _ -> failwith (Printf.sprintf "Cannot compile unsigned : %s -> %s" (string_of_ctyp ctyp) (string_of_ctyp ret_ctyp))

let builtin_add_bits env v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_fbits (m, _), CT_fbits (o, _) ->
     assert (n = m && m = o);
     Fn ("bvadd", [smt_cval env v1; smt_cval env v2])

  | _ -> builtin_type_error "add_bits" [v1; v2] (Some ret_ctyp)

let builtin_sub_bits env v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_fbits (m, _), CT_fbits (o, _) ->
     assert (n = m && m = o);
     Fn ("bvadd", [smt_cval env v1; Fn ("bvneg", [smt_cval env v2])])

  | _ -> failwith "Cannot compile sub_bits"

let builtin_add_bits_int env v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_constant c, CT_fbits (o, _) when n = o ->
     Fn ("bvadd", [smt_cval env v1; bvint o c])

  | CT_fbits (n, _), CT_fint m, CT_fbits (o, _) when n = o ->
     Fn ("bvadd", [smt_cval env v1; force_size o m (smt_cval env v2)])

  | _ -> builtin_type_error "add_bits_int" [v1; v2] (Some ret_ctyp)

let builtin_replicate_bits env v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_constant c, CT_fbits (m, _) ->
     assert (n * Big_int.to_int c = m);
     let smt = smt_cval env v1 in
     Fn ("concat", List.init (Big_int.to_int c) (fun _ -> smt))

  | CT_fbits (n, _), ctyp2, CT_lbits _ ->
     let len = Fn ("bvmul", [bvint !lbits_index (Big_int.of_int n);
                             Extract (!lbits_index - 1, 0, smt_cval env v2)])
     in
     assert false
     
  | _ -> builtin_type_error "replicate_bits" [v1; v2] (Some ret_ctyp)

let builtin_sail_truncate env v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_constant c, CT_fbits (m, _) ->
     assert (Big_int.to_int c = m);
     Extract (Big_int.to_int c - 1, 0, smt_cval env v1)

  | CT_lbits _, CT_constant c, CT_fbits (m, _) ->
     assert (Big_int.to_int c = m && m < lbits_size ());
     Extract (Big_int.to_int c - 1, 0, Fn ("contents", [smt_cval env v1]))

  | t1, t2, _ -> failwith (Printf.sprintf "Cannot compile sail_truncate (%s, %s) -> %s" (string_of_ctyp t1) (string_of_ctyp t2) (string_of_ctyp ret_ctyp))

let builtin_sail_truncateLSB env v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_constant c, CT_fbits (m, _) ->
     assert (Big_int.to_int c = m);
     Extract (n - 1, n - Big_int.to_int c, smt_cval env v1)

  | _ -> failwith "Cannot compile sail_truncate"

let builtin_get_slice_int env v1 v2 v3 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, cval_ctyp v3, ret_ctyp with
  | CT_constant len, ctyp, CT_constant start, CT_fbits (ret_sz, _) ->
     let len = Big_int.to_int len in
     let start = Big_int.to_int start in
     let in_sz = int_size ctyp in
     let smt =
       if in_sz < len + start then
         force_size (len + start) in_sz (smt_cval env v2)
       else
         smt_cval env v2
     in
     assert (start + len <= in_sz);
     Extract ((start + len) - 1, start, smt)

  | _, _, _, _ -> builtin_type_error "get_slice_int" [v1; v2; v3] (Some ret_ctyp)

let builtin_count_leading_zeros env v ret_ctyp =
  let ret_sz = int_size ret_ctyp in
  let rec lzcnt sz smt =
    if sz == 1 then
      Ite (Fn ("=", [Extract (0, 0, smt); Bin "0"]),
           bvint ret_sz (Big_int.of_int 1),
           bvint ret_sz (Big_int.zero))
    else (
      assert (sz land (sz - 1) = 0);
      let hsz = sz /2 in
      Ite (Fn ("=", [Extract (sz - 1, hsz, smt); bvzero hsz]),
           Fn ("bvadd", [bvint ret_sz (Big_int.of_int hsz); lzcnt hsz (Extract (hsz - 1, 0, smt))]),
           lzcnt hsz (Extract (sz - 1, hsz, smt)))
    )
  in
  let smallest_greater_power_of_two n =
    let m = ref 1 in
    while !m < n do
      m := !m lsl 1
    done;
    assert (!m land (!m - 1) = 0);
    !m
  in
  match cval_ctyp v with
  | CT_fbits (sz, _) when sz land (sz - 1) = 0 ->
     lzcnt sz (smt_cval env v)

  | CT_fbits (sz, _) ->
     let padded_sz = smallest_greater_power_of_two sz in
     let padding = bvzero (padded_sz - sz) in
     Fn ("bvsub", [lzcnt padded_sz (Fn ("concat", [padding; smt_cval env v]));
                   bvint ret_sz (Big_int.of_int (padded_sz - sz))])

  | CT_lbits _ ->
     let smt = smt_cval env v in
     Fn ("bvsub", [lzcnt (lbits_size ()) (Fn ("contents", [smt]));
                   Fn ("bvsub", [bvint ret_sz (Big_int.of_int (lbits_size ()));
                                 Fn ("concat", [bvzero (ret_sz - !lbits_index); Fn ("len", [smt])])])])

  | _ -> builtin_type_error "count_leading_zeros" [v] (Some ret_ctyp)

let smt_builtin env name args ret_ctyp =
  match name, args, ret_ctyp with
  | "eq_bits", [v1; v2], _ -> Fn ("=", [smt_cval env v1; smt_cval env v2])
  | "eq_anything", [v1; v2], CT_bool -> Fn ("=", [smt_cval env v1; smt_cval env v2])

  (* lib/flow.sail *)
  | "eq_bit",  [v1; v2], CT_bool -> Fn ("=", [smt_cval env v1; smt_cval env v2])
  | "eq_bool", [v1; v2], CT_bool -> Fn ("=", [smt_cval env v1; smt_cval env v2])
  | "eq_unit", [v1; v2], CT_bool -> Fn ("=", [smt_cval env v1; smt_cval env v2])

  | "eq_int",  [v1; v2], CT_bool -> builtin_eq_int env v1 v2

  | "not", [v], _ -> Fn ("not", [smt_cval env v])
  | "lt",   [v1; v2], _ -> builtin_lt env v1 v2
  | "lteq", [v1; v2], _ -> builtin_lteq env v1 v2
  | "gt",   [v1; v2], _ -> builtin_gt env v1 v2
  | "gteq", [v1; v2], _ -> builtin_gteq env v1 v2

  (* lib/arith.sail *)
  | "add_int", [v1; v2], _ -> builtin_add_int env v1 v2 ret_ctyp
  | "sub_int", [v1; v2], _ -> builtin_sub_int env v1 v2 ret_ctyp
  | "mult_int", [v1; v2], _ -> builtin_mult_int env v1 v2 ret_ctyp
  | "neg_int", [v], _ -> builtin_negate_int env v ret_ctyp
  | "shl_int", [v1; v2], _ -> builtin_shl_int env v1 v2 ret_ctyp
  | "shr_int", [v1; v2], _ -> builtin_shr_int env v1 v2 ret_ctyp
  | "shl_mach_int", [v1; v2], _ -> builtin_shl_int env v1 v2 ret_ctyp
  | "shr_mach_int", [v1; v2], _ -> builtin_shr_int env v1 v2 ret_ctyp
  | "abs_int", [v], _ -> builtin_abs_int env v ret_ctyp

  (* lib/vector_dec.sail *)
  | "zeros", [v], _ -> builtin_zeros env v ret_ctyp
  | "ones", [v], _ -> builtin_ones env v ret_ctyp
  | "zero_extend", [v1; v2], _ -> builtin_zero_extend env v1 v2 ret_ctyp
  | "sign_extend", [v1; v2], _ -> builtin_sign_extend env v1 v2 ret_ctyp
  | "sail_truncate", [v1; v2], _ -> builtin_sail_truncate env v1 v2 ret_ctyp
  | "sail_truncateLSB", [v1; v2], _ -> builtin_sail_truncateLSB env v1 v2 ret_ctyp
  | "shiftl", [v1; v2], _ -> builtin_shift "bvshl" env v1 v2 ret_ctyp
  | "shiftr", [v1; v2], _ -> builtin_shift "bvlshr" env v1 v2 ret_ctyp
  | "or_bits", [v1; v2], _ -> builtin_or_bits env v1 v2 ret_ctyp
  | "and_bits", [v1; v2], _ -> builtin_and_bits env v1 v2 ret_ctyp
  | "not_bits", [v], _ -> builtin_not_bits env v ret_ctyp
  | "add_bits", [v1; v2], _ -> builtin_add_bits env v1 v2 ret_ctyp
  | "add_bits_int", [v1; v2], _ -> builtin_add_bits_int env v1 v2 ret_ctyp
  | "sub_bits", [v1; v2], _ -> builtin_sub_bits env v1 v2 ret_ctyp
  | "append", [v1; v2], _ -> builtin_append env v1 v2 ret_ctyp
  | "length", [v], ret_ctyp -> builtin_length env v ret_ctyp
  | "vector_access", [v1; v2], ret_ctyp -> builtin_vector_access env v1 v2 ret_ctyp
  | "vector_subrange", [v1; v2; v3], ret_ctyp -> builtin_vector_subrange env v1 v2 v3 ret_ctyp
  | "vector_update", [v1; v2; v3], ret_ctyp -> builtin_vector_update env v1 v2 v3 ret_ctyp
  | "sail_unsigned", [v], ret_ctyp -> builtin_unsigned env v ret_ctyp
  | "replicate_bits", [v1; v2], ret_ctyp -> builtin_replicate_bits env v1 v2 ret_ctyp
  | "count_leading_zeros", [v], ret_ctyp -> builtin_count_leading_zeros env v ret_ctyp
  | "get_slice_int", [v1; v2; v3], ret_ctyp -> builtin_get_slice_int env v1 v2 v3 ret_ctyp
                                          
  | _ -> failwith ("Bad builtin " ^ name ^ " " ^ Util.string_of_list ", " string_of_ctyp (List.map cval_ctyp args) ^ " -> " ^ string_of_ctyp ret_ctyp)

let rec smt_conversion from_ctyp to_ctyp x =
  match from_ctyp, to_ctyp with
  | _, _ when ctyp_equal from_ctyp to_ctyp -> x
  | CT_constant c, CT_fint sz ->
     bvint sz c
  | _, _ -> failwith (Printf.sprintf "Cannot perform conversion from %s to %s" (string_of_ctyp from_ctyp) (string_of_ctyp to_ctyp))

let define_const id ctyp exp = Define_const (zencode_name id, smt_ctyp ctyp, exp)
let declare_const id ctyp = Declare_const (zencode_name id, smt_ctyp ctyp)

let smt_ctype_def = function
  | CTD_enum (id, elems) ->
     [declare_datatypes (mk_enum (zencode_upper_id id) (List.map zencode_id elems))]

  | CTD_struct (id, fields) ->
     [declare_datatypes
       (mk_record (zencode_upper_id id)
          (List.map (fun (field, ctyp) -> zencode_upper_id id ^ "_" ^ zencode_id field, smt_ctyp ctyp) fields))]

  | CTD_variant (id, ctors) ->
     [declare_datatypes
       (mk_variant (zencode_upper_id id)
         (List.map (fun (ctor, ctyp) -> zencode_id ctor, smt_ctyp ctyp) ctors))]

let rec generate_ctype_defs = function
  | CDEF_type ctd :: cdefs -> smt_ctype_def ctd :: generate_ctype_defs cdefs
  | _ :: cdefs -> generate_ctype_defs cdefs
  | [] -> []

let rec generate_reg_decs inits = function
  | CDEF_reg_dec (id, ctyp, _) :: cdefs when not (NameMap.mem (Name (id, 0)) inits)->
     Declare_const (zencode_name (Name (id, 0)), smt_ctyp ctyp)
     :: generate_reg_decs inits cdefs
  | _ :: cdefs -> generate_reg_decs inits cdefs
  | [] -> []

(**************************************************************************)
(* 2. Converting sail types to Jib types for SMT                          *)
(**************************************************************************)

let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))

(** Convert a sail type into a C-type. This function can be quite
   slow, because it uses ctx.local_env and SMT to analyse the Sail
   types and attempts to fit them into the smallest possible C
   types, provided ctx.optimize_smt is true (default) **)
let rec ctyp_of_typ ctx typ =
  let open Ast in
  let open Type_check in
  let open Jib_compile in
  let Typ_aux (typ_aux, l) as typ = Env.expand_synonyms ctx.tc_env typ in
  match typ_aux with
  | Typ_id id when string_of_id id = "bit"    -> CT_bit
  | Typ_id id when string_of_id id = "bool"   -> CT_bool
  | Typ_id id when string_of_id id = "int"    -> CT_lint
  | Typ_id id when string_of_id id = "nat"    -> CT_lint
  | Typ_id id when string_of_id id = "unit"   -> CT_unit
  | Typ_id id when string_of_id id = "string" -> CT_string
  | Typ_id id when string_of_id id = "real"   -> CT_real

  | Typ_app (id, _) when string_of_id id = "atom_bool" -> CT_bool

  | Typ_app (id, args) when string_of_id id = "itself" ->
     ctyp_of_typ ctx (Typ_aux (Typ_app (mk_id "atom", args), l))
  | Typ_app (id, _) when string_of_id id = "range" || string_of_id id = "atom" || string_of_id id = "implicit" ->
     begin match destruct_range Env.empty typ with
     | None -> assert false (* Checked if range type in guard *)
     | Some (kids, constr, n, m) ->
        let ctx = { ctx with local_env = add_existential Parse_ast.Unknown (List.map (mk_kopt K_int) kids) constr ctx.local_env } in
        match nexp_simp n, nexp_simp m with
        | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
             when n = m ->
           CT_constant n
        | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
             when Big_int.less_equal (min_int 64) n && Big_int.less_equal m (max_int 64) ->
           CT_fint 64
        | n, m ->
           if prove __POS__ ctx.local_env (nc_lteq (nconstant (min_int 64)) n) && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_int 64))) then
             CT_fint 64
           else
             CT_lint
     end

  | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "list" ->
     CT_list (ctyp_of_typ ctx typ)

  (* When converting a sail bitvector type into C, we have three options in order of efficiency:
     - If the length is obviously static and smaller than 64, use the fixed bits type (aka uint64_t), fbits.
     - If the length is less than 64, then use a small bits type, sbits.
     - If the length may be larger than 64, use a large bits type lbits. *)
  | Typ_app (id, [A_aux (A_nexp n, _);
                  A_aux (A_order ord, _);
                  A_aux (A_typ (Typ_aux (Typ_id vtyp_id, _)), _)])
       when string_of_id id = "vector" && string_of_id vtyp_id = "bit" ->
     let direction = match ord with Ord_aux (Ord_dec, _) -> true | Ord_aux (Ord_inc, _) -> false | _ -> assert false in
     begin match nexp_simp n with
     | Nexp_aux (Nexp_constant n, _) -> CT_fbits (Big_int.to_int n, direction)
     | _ -> CT_lbits direction
     end

  | Typ_app (id, [A_aux (A_nexp n, _);
                  A_aux (A_order ord, _);
                  A_aux (A_typ typ, _)])
       when string_of_id id = "vector" ->
     let direction = match ord with Ord_aux (Ord_dec, _) -> true | Ord_aux (Ord_inc, _) -> false | _ -> assert false in
     CT_vector (direction, ctyp_of_typ ctx typ)

  | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "register" ->
     CT_ref (ctyp_of_typ ctx typ)

  | Typ_id id | Typ_app (id, _) when Bindings.mem id ctx.records  -> CT_struct (id, Bindings.find id ctx.records |> Bindings.bindings)
  | Typ_id id | Typ_app (id, _) when Bindings.mem id ctx.variants -> CT_variant (id, Bindings.find id ctx.variants |> Bindings.bindings)
  | Typ_id id when Bindings.mem id ctx.enums -> CT_enum (id, Bindings.find id ctx.enums |> IdSet.elements)

  | Typ_tup typs -> CT_tup (List.map (ctyp_of_typ ctx) typs)

  | Typ_exist _ ->
     (* Use Type_check.destruct_exist when optimising with SMT, to
        ensure that we don't cause any type variable clashes in
        local_env, and that we can optimize the existential based upon
        it's constraints. *)
     begin match destruct_exist (Env.expand_synonyms ctx.local_env typ) with
     | Some (kids, nc, typ) ->
        let env = add_existential l kids nc ctx.local_env in
        ctyp_of_typ { ctx with local_env = env } typ
     | None -> raise (Reporting.err_unreachable l __POS__ "Existential cannot be destructured!")
     end

  | Typ_var kid -> CT_poly

  | _ -> raise (Reporting.err_unreachable l __POS__ ("No C type for type " ^ string_of_typ typ))

(**************************************************************************)
(* 3. Optimization of primitives and literals                             *)
(**************************************************************************)

let hex_char =
  let open Sail2_values in
  function
  | '0' -> [B0; B0; B0; B0]
  | '1' -> [B0; B0; B0; B1]
  | '2' -> [B0; B0; B1; B0]
  | '3' -> [B0; B0; B1; B1]
  | '4' -> [B0; B1; B0; B0]
  | '5' -> [B0; B1; B0; B1]
  | '6' -> [B0; B1; B1; B0]
  | '7' -> [B0; B1; B1; B1]
  | '8' -> [B1; B0; B0; B0]
  | '9' -> [B1; B0; B0; B1]
  | 'A' | 'a' -> [B1; B0; B1; B0]
  | 'B' | 'b' -> [B1; B0; B1; B1]
  | 'C' | 'c' -> [B1; B1; B0; B0]
  | 'D' | 'd' -> [B1; B1; B0; B1]
  | 'E' | 'e' -> [B1; B1; B1; B0]
  | 'F' | 'f' -> [B1; B1; B1; B1]
  | _ -> failwith "Invalid hex character"

let literal_to_cval (L_aux (l_aux, _) as lit) =
  match l_aux with
  | L_num n -> Some (V_lit (VL_int n, CT_constant n))
  | L_hex str when String.length str <= 16 ->
     let content = Util.string_to_list str |> List.map hex_char |> List.concat in
     Some (V_lit (VL_bits (content, true), CT_fbits (String.length str * 4, true)))
  | L_unit -> Some (V_lit (VL_unit, CT_unit))
  | L_true -> Some (V_lit (VL_bool true, CT_bool))
  | L_false -> Some (V_lit (VL_bool false, CT_bool))
  | _ -> None

let c_literals ctx =
  let rec c_literal env l = function
    | AV_lit (lit, typ) as v ->
       begin match literal_to_cval lit with
       | Some cval -> AV_cval (cval, typ)
       | None -> v
       end
    | AV_tuple avals -> AV_tuple (List.map (c_literal env l) avals)
    | v -> v
  in
  map_aval c_literal

(**************************************************************************)
(* 3. Generating SMT                                                      *)
(**************************************************************************)

let push_smt_defs stack smt_defs =
  List.iter (fun def -> Stack.push def stack) smt_defs

(* When generating SMT when we encounter joins between two or more
   blocks such as in the example below, we have to generate a muxer
   that chooses the correct value of v_n or v_m to assign to v_o. We
   use the pi nodes that contain the global path condition for each
   block to generate an if-then-else for each phi function. The order
   of the arguments to each phi function is based on the graph node
   index for the predecessor nodes.

   +---------------+      +---------------+
   | pi(cond_1)    |      | pi(cond_2)    |
   | ...           |      | ...           |
   | Basic block 1 |      | Basic block 2 |
   +---------------+      +---------------+
              \               /
               \             /
            +---------------------+
            | v/o = phi(v/n, v/m) |
            | ...                 |
            +---------------------+

   would generate:

   (define-const v/o (ite cond_1 v/n v/m_))
*)
let smt_ssanode env cfg preds =
  let open Jib_ssa in
  function
  | Pi _ -> []
  | Phi (id, ctyp, ids) ->
     let get_pi n =
       match get_vertex cfg n with
       | Some ((ssanodes, _), _, _) ->
          List.concat (List.map (function Pi guards -> guards | _ -> []) ssanodes)
       | None -> failwith "Predecessor node does not exist"
     in
     let pis = List.map get_pi (IntSet.elements preds) in
     let mux =
       List.fold_right2 (fun pi id chain ->
           let pathcond =
             match pi with
             | [cval] -> smt_cval env cval
             | _ -> Fn ("and", List.map (smt_cval env) pi)
           in
           match chain with
           | Some smt ->
              Some (Ite (pathcond, Var (zencode_name id), smt))
           | None ->
              Some (Var (zencode_name id)))
         pis ids None
     in
     match mux with
     | None -> []
     | Some mux ->
        [Define_const (zencode_name id, smt_ctyp ctyp, mux)]

(* For any complex l-expression we need to turn it into a
   read-modify-write in the SMT solver. The SSA transform turns CL_id
   nodes into CL_rmw (read, write, ctyp) nodes when CL_id is wrapped
   in any other l-expression. The read and write must have the same
   name but different SSA numbers.
*)
let rec rmw_write = function
  | CL_rmw (_, write, ctyp) -> write, ctyp
  | CL_id _ -> assert false
  | CL_tuple (clexp, _) -> rmw_write clexp
  | CL_field (clexp, _) -> rmw_write clexp
  | clexp ->
     failwith (Pretty_print_sail.to_string (pp_clexp clexp))

let rmw_read = function
  | CL_rmw (read, _, _) -> zencode_name read
  | _ -> assert false

let rmw_modify smt = function
  | CL_tuple (clexp, n) ->
     let ctyp = clexp_ctyp clexp in
     begin match ctyp with
     | CT_tup ctyps ->
        let len = List.length ctyps in
        let set_tup i =
          if i == n then
            smt
          else
            Fn (Printf.sprintf "tup_%d_%d" len i, [Var (rmw_read clexp)])
        in
        Fn ("tup" ^ string_of_int len, List.init len set_tup)
     | _ ->
        failwith "Tuple modify does not have tuple type"
     end
  | CL_field (clexp, field) ->
     let ctyp = clexp_ctyp clexp in
     begin match ctyp with
     | CT_struct (struct_id, fields) ->
        let set_field (field', _) =
          if Util.zencode_string field = zencode_id field' then
            smt
          else
            Fn (zencode_upper_id struct_id ^ "_" ^ zencode_id field', [Var (rmw_read clexp)])
        in
        Fn (zencode_upper_id struct_id, List.map set_field fields)
     | _ ->
        failwith "Struct modify does not have struct type"
     end
  | _ -> assert false

(* For a basic block (contained in a control-flow node / cfnode), we
   turn the instructions into a sequence of define-const and
   declare-const expressions. Because we are working with a SSA graph,
   each variable is guaranteed to only be declared once.
*)
let smt_instr env =
  let open Type_check in
  function
  | I_aux (I_funcall (CL_id (id, ret_ctyp), _, function_id, args), _) ->
     if Env.is_extern function_id env "c" then
       let name = Env.get_extern function_id env "c" in
       let value = smt_builtin env name args ret_ctyp in
       [define_const id ret_ctyp value]
     else
       let smt_args = List.map (smt_cval env) args in
       [define_const id ret_ctyp (Fn (zencode_id function_id, smt_args))]

  | I_aux (I_init (ctyp, id, cval), _) | I_aux (I_copy (CL_id (id, ctyp), cval), _) ->
     [define_const id ctyp
        (smt_conversion (cval_ctyp cval) ctyp (smt_cval env cval))]

  | I_aux (I_copy (clexp, cval), _) ->
     let smt = smt_cval env cval in
     let write, ctyp = rmw_write clexp in
     [define_const write ctyp (rmw_modify smt clexp)]

  | I_aux (I_decl (ctyp, id), _) ->
     [declare_const id ctyp]

  | I_aux (I_end id, _) ->
     if !ignore_overflow then
       [Assert (Fn ("not", [Var (zencode_name id)]))]
     else
       let checks =
         Stack.fold (fun checks -> function (Define_const (name, _, _) as def) -> (name, def) :: checks | _ -> assert false) [] overflow_checks
       in
       List.map snd checks @ [Assert (Fn ("and", Fn ("not", [Var (zencode_name id)]) :: List.map (fun check -> Var (fst check)) checks))]

  | I_aux (I_clear _, _) -> []

  | I_aux (I_match_failure, _) -> []

  | instr ->
     failwith ("Cannot translate: " ^ Pretty_print_sail.to_string (pp_instr instr))

let smt_cfnode all_cdefs env =
  let open Jib_ssa in
  function
  | CF_start inits ->
     let smt_reg_decs = generate_reg_decs inits all_cdefs in
     let smt_start (id, ctyp) =
       match id with
       | Have_exception _ -> define_const id ctyp (Bool_lit false)
       | _ -> declare_const id ctyp
     in
     smt_reg_decs @ List.map smt_start (NameMap.bindings inits)
  | CF_block instrs ->
     List.concat (List.map (smt_instr env) instrs)
  (* We can ignore any non basic-block/start control-flow nodes *)
  | _ -> []

let rec find_function id = function
  | CDEF_fundef (id', heap_return, args, body) :: _ when Id.compare id id' = 0 ->
     Some (heap_return, args, body)
  | _ :: cdefs ->
     find_function id cdefs
  | [] -> None

let optimize_smt stack =
  let stack' = Stack.create () in
  let uses = Hashtbl.create (Stack.length stack) in

  let rec uses_in_exp = function
    | Var var ->
       begin match Hashtbl.find_opt uses var with
       | Some n -> Hashtbl.replace uses var (n + 1)
       | None -> Hashtbl.add uses var 1
       end
    | Hex _ | Bin _ | Bool_lit _ -> ()
    | Fn (f, exps) ->
       List.iter uses_in_exp exps
    | Ite (cond, t, e) ->
       uses_in_exp cond; uses_in_exp t; uses_in_exp e
    | Extract (_, _, exp) | Tester (_, exp) | SignExtend (_, exp) ->
       uses_in_exp exp
  in

  let remove_unused () = function
    | Declare_const (var, _) as def ->
       begin match Hashtbl.find_opt uses var with
       | None -> ()
       | Some _ ->
          Stack.push def stack'
       end
    | Define_const (var, _, exp) as def ->
       begin match Hashtbl.find_opt uses var with
       | None -> ()
       | Some _ ->
          uses_in_exp exp;
          Stack.push def stack'
       end
    | (Declare_datatypes _ | Declare_tuple _) as def ->
       Stack.push def stack'
    | Assert exp as def ->
       uses_in_exp exp;
       Stack.push def stack'
    | Define_fun _ -> assert false
  in
  Stack.fold remove_unused () stack;

  let vars = Hashtbl.create (Stack.length stack') in
  let queue = Queue.create () in

  let constant_propagate = function
    | Declare_const _ as def ->
       Queue.add def queue
    | Define_const (var, typ, exp) ->
       begin match Hashtbl.find_opt uses var with
       | Some 1 ->
          Hashtbl.add vars var exp
       | Some _ ->
          Queue.add (Define_const (var, typ, simp_smt_exp vars exp)) queue
       | None -> assert false
       end
    | Assert exp ->
       Queue.add (Assert (simp_smt_exp vars exp)) queue
    | (Declare_datatypes _ | Declare_tuple _) as def ->
       Queue.add def queue
    | Define_fun _ -> assert false
  in
  Stack.iter constant_propagate stack';
  queue

(** [smt_header stack cdefs] pushes all the type declarations required
   for cdefs onto the SMT stack *)
let smt_header stack cdefs =
  push_smt_defs stack
    [declare_datatypes (mk_enum "Unit" ["unit"]);
     Declare_tuple 2;
     Declare_tuple 3;
     Declare_tuple 4;
     Declare_tuple 5;
     declare_datatypes (mk_record "Bits" [("len", Bitvec !lbits_index);
                                          ("contents", Bitvec (lbits_size ()))])

    ];
  let smt_type_defs = List.concat (generate_ctype_defs cdefs) in
  push_smt_defs stack smt_type_defs

let smt_cdef props name_file env all_cdefs = function
  | CDEF_spec (function_id, arg_ctyps, ret_ctyp) when Bindings.mem function_id props ->
     begin match find_function function_id all_cdefs with
     | Some (None, args, instrs) ->
        let prop_type, prop_args, pragma_l, vs = Bindings.find function_id props in

        let stack = Stack.create () in

        smt_header stack all_cdefs;
        let smt_args =
          List.map2 (fun id ctyp -> declare_const (Name (id, 0)) ctyp) args arg_ctyps
        in
        push_smt_defs stack smt_args;

        let instrs =
          let open Jib_optimize in
          instrs
          (* |> optimize_unit *)
          |> inline all_cdefs (fun _ -> true)
          |> flatten_instrs
          |> remove_pointless_goto
        in

        let str = Pretty_print_sail.to_string PPrint.(separate_map hardline Jib_util.pp_instr instrs) in
        prerr_endline str;

        let open Jib_ssa in
        let start, cfg = ssa instrs in
        (* let chan = open_out "smt_ssa.gv" in
        make_dot chan cfg;
        close_out chan; *)

        let visit_order = topsort cfg in

        List.iter (fun n ->
            begin match get_vertex cfg n with
            | None -> ()
            | Some ((ssanodes, cfnode), preds, succs) ->
               let muxers =
                 ssanodes |> List.map (smt_ssanode env cfg preds) |> List.concat
               in
               let basic_block = smt_cfnode all_cdefs env cfnode in
               push_smt_defs stack muxers;
               push_smt_defs stack basic_block;
            end
          ) visit_order;

        let out_chan = open_out (name_file (string_of_id function_id)) in
        output_string out_chan "(set-logic QF_AUFBVDT)\n";

        (* let stack' = Stack.create () in
        Stack.iter (fun def -> Stack.push def stack') stack;
        Stack.iter (fun def -> output_string out_chan (string_of_smt_def def); output_string out_chan "\n") stack'; *)
        let queue = optimize_smt stack in
        Queue.iter (fun def -> output_string out_chan (string_of_smt_def def); output_string out_chan "\n") queue;

        output_string out_chan "(check-sat)\n"

     | _ -> failwith "Bad function body"
     end
  | _ -> ()

let rec smt_cdefs props name_file env ast =
  function
  | cdef :: cdefs ->
     smt_cdef props name_file env ast cdef;
     smt_cdefs props name_file env ast cdefs
  | [] -> ()

let generate_smt props name_file env ast =
  try
    let open Jib_compile in
    let ctx =
      initial_ctx
        ~convert_typ:ctyp_of_typ
        ~optimize_anf:(fun ctx aexp -> c_literals ctx aexp)
        env
    in
    let t = Profile.start () in
    let cdefs, ctx = compile_ast { ctx with specialize_calls = true; ignore_64 = true } ast in
    Profile.finish "Compiling to Jib IR" t;

    smt_cdefs props name_file env cdefs cdefs
  with
  | Type_check.Type_error (_, l, err) ->
     raise (Reporting.err_typ l (Type_error.string_of_type_error err));
