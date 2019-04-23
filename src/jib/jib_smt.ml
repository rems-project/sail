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

let zencode_upper_id id = Util.zencode_upper_string (string_of_id id)
let zencode_id id = Util.zencode_string (string_of_id id)
let zencode_name id = string_of_name ~deref_current_exception:false ~zencode:true id

let opt_ignore_overflow = ref false

let opt_auto = ref false

type ctx = {
    (* Arbitrary-precision bitvectors are represented as a (BitVec lbits_index, BitVec (2 ^ lbits_index)) pair. *)
    lbits_index : int;
    (* The size we use for integers where we don't know how large they are statically. *)
    lint_size : int;
    (* A generic vector, vector('a) becomes Array (BitVec vector_index) 'a.
       We need to take care that vector_index is large enough for all generic vectors. *)
    vector_index : int;
    register_map : id list CTMap.t;
    tc_env : Type_check.Env.t
  }

(* These give the default bounds for various SMT types, stored in the
   initial_ctx. They shouldn't be read or written by anything else! If
   they are changed the output of sail -help needs to be updated to
   reflect this. *)
let opt_default_lint_size = ref 128
let opt_default_lbits_index = ref 8
let opt_default_vector_index = ref 5

let initial_ctx () = {
    lbits_index = !opt_default_lbits_index;
    lint_size = !opt_default_lint_size;
    vector_index = !opt_default_vector_index;
    register_map = CTMap.empty;
    tc_env = Type_check.initial_env
  }

let lbits_size ctx = Util.power 2 ctx.lbits_index

let vector_index = ref 5

let smt_unit = mk_enum "Unit" ["Unit"]
let smt_lbits ctx = mk_record "Bits" [("size", Bitvec ctx.lbits_index); ("bits", Bitvec (lbits_size ctx))]

(* [required_width n] is the required number of bits to losslessly
   represent an integer n *)
let required_width n =
  let rec required_width' n =
    if Big_int.equal n Big_int.zero then
      1
    else
      1 + required_width' (Big_int.shift_right n 1)
  in
  required_width' (Big_int.abs n)

let rec smt_ctyp ctx = function
  | CT_constant n -> Bitvec (required_width n)
  | CT_fint n -> Bitvec n
  | CT_lint -> Bitvec ctx.lint_size
  | CT_unit -> smt_unit
  | CT_bit -> Bitvec 1
  | CT_fbits (n, _) -> Bitvec n
  | CT_sbits (n, _) -> smt_lbits ctx
  | CT_lbits _ -> smt_lbits ctx
  | CT_bool -> Bool
  | CT_enum (id, elems) ->
     mk_enum (zencode_upper_id id) (List.map zencode_id elems)
  | CT_struct (id, fields) ->
     mk_record (zencode_upper_id id) (List.map (fun (id, ctyp) -> (zencode_id id, smt_ctyp ctx ctyp)) fields)
  | CT_variant (id, ctors) ->
     mk_variant (zencode_upper_id id) (List.map (fun (id, ctyp) -> (zencode_id id, smt_ctyp ctx ctyp)) ctors)
  | CT_tup ctyps -> Tuple (List.map (smt_ctyp ctx) ctyps)
  | CT_vector (_, ctyp) -> Array (Bitvec !vector_index, smt_ctyp ctx ctyp)
  | CT_string -> Bitvec 64
  | CT_ref ctyp ->
     begin match CTMap.find_opt ctyp ctx.register_map with
     | Some regs -> Bitvec (required_width (Big_int.of_int (List.length regs)))
     | _ -> failwith ("No registers with ctyp: " ^ string_of_ctyp ctyp)
     end
  | ctyp -> failwith ("Unhandled ctyp: " ^ string_of_ctyp ctyp)

(* We often need to create a SMT bitvector of a length sz with integer
   value x. [bvpint sz x] does this for positive integers, and [bvint sz x]
   does this for all integers. It's quite awkward because we
   don't have a very good way to get the binary representation of
   either an ocaml integer or a big integer. *)
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

(* Translate Jib literals into SMT *)
let smt_value ctx vl ctyp =
  let open Value2 in
  match vl, ctyp with
  | VL_bits (bs, true), CT_fbits (n, _) ->
     (* FIXME: Output the correct number of bits in Jib_compile *)
     begin match Sail2_values.hexstring_of_bits (List.rev (Util.take n (List.rev bs))) with
     | Some s -> Hex (Xstring.implode s)
     | None -> Bin (Xstring.implode (List.map Sail2_values.bitU_char (List.rev (Util.take n (List.rev bs)))))
     end
  | VL_bool b, _ -> Bool_lit b
  | VL_int n, CT_constant m -> bvint (required_width n) n
  | VL_int n, CT_fint sz -> bvint sz n
  | VL_int n, CT_lint -> bvint ctx.lint_size n
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

let rec smt_cval ctx cval =
  match cval with
  | V_lit (vl, ctyp) -> smt_value ctx vl ctyp
  | V_id (Name (id, _) as ssa_id, _) ->
     begin match Type_check.Env.lookup_id id ctx.tc_env with
     | Enum _ -> Var (zencode_id id)
     | _ -> Var (zencode_name ssa_id)
     end
  | V_id (ssa_id, _) -> Var (zencode_name ssa_id)
  | V_op (frag1, "!=", frag2) ->
     Fn ("not", [Fn ("=", [smt_cval ctx frag1; smt_cval ctx frag2])])
  | V_op (frag1, "|", frag2) ->
     Fn ("bvor", [smt_cval ctx frag1; smt_cval ctx frag2])
  | V_call ("bit_to_bool", [cval]) ->
     Fn ("=", [smt_cval ctx cval; Bin "1"])
  | V_unary ("!", cval) ->
     Fn ("not", [smt_cval ctx cval])
  | V_ctor_kind (union, ctor_id, unifiers, _) ->
     Fn ("not", [Tester (zencode_ctor ctor_id unifiers, smt_cval ctx union)])
  | V_ctor_unwrap (ctor_id, union, unifiers, _) ->
     Fn ("un" ^ zencode_ctor ctor_id unifiers, [smt_cval ctx union])
  | V_field (union, field) ->
     begin match cval_ctyp union with
     | CT_struct (struct_id, _) ->
        Fn (zencode_upper_id struct_id ^ "_" ^ field, [smt_cval ctx union])
     | _ -> failwith "Field for non-struct type"
     end
  | V_struct (fields, ctyp) ->
     begin match ctyp with
     | CT_struct (struct_id, field_ctyps) ->
        let set_field (field, cval) =
          match Util.assoc_compare_opt Id.compare field field_ctyps with
          | None -> failwith "Field type not found"
          | Some ctyp when ctyp_equal (cval_ctyp cval) ctyp ->
             smt_cval ctx cval
          | _ -> failwith "Type mismatch when generating struct for SMT"
        in
        Fn (zencode_upper_id struct_id, List.map set_field fields)
     | _ -> failwith "Struct does not have struct type"
     end
  | V_tuple_member (frag, len, n) ->
     Fn (Printf.sprintf "tup_%d_%d" len n, [smt_cval ctx frag])
  | V_ref (Name (id, _), _) ->
     let rmap = CTMap.filter (fun ctyp regs -> List.exists (fun reg -> Id.compare reg id = 0) regs) ctx.register_map in
     assert (CTMap.cardinal rmap = 1);
     begin match CTMap.min_binding_opt rmap with
     | Some (ctyp, regs) ->
        begin match Util.list_index (fun reg -> Id.compare reg id = 0) regs with
        | Some i ->
           bvint (required_width (Big_int.of_int (List.length regs))) (Big_int.of_int i)
        | None -> assert false
        end
     | _ -> assert false
     end
  | cval -> failwith ("Unrecognised cval " ^ string_of_cval ~zencode:false cval)

let overflow_checks = Stack.create ()

let overflow_check smt =
  if not !opt_ignore_overflow then (
    Util.warn "Adding overflow check in generated SMT";
    Stack.push (Define_const ("overflow" ^ string_of_int (Stack.length overflow_checks), Bool, Fn ("not", [smt]))) overflow_checks
  )

(**************************************************************************)
(* 1. Generating SMT for Sail builtins                                    *)
(**************************************************************************)

let builtin_type_error fn cvals =
  let args = Util.string_of_list ", " (fun cval -> string_of_ctyp (cval_ctyp cval)) cvals in
  function
  | Some ret_ctyp ->
     Reporting.unreachable Parse_ast.Unknown __POS__
       (Printf.sprintf "%s : (%s) -> %s" fn args (string_of_ctyp ret_ctyp))
  | None ->
     Reporting.unreachable Parse_ast.Unknown __POS__ (Printf.sprintf "%s : (%s)" fn args)

(* ***** Basic comparisons: lib/flow.sail ***** *)

let builtin_int_comparison fn big_int_fn ctx v1 v2 =
  match cval_ctyp v1, cval_ctyp v2 with
  | CT_lint, CT_lint ->
     Fn (fn, [smt_cval ctx v1; smt_cval ctx v2])
  | CT_fint sz1, CT_fint sz2 ->
     if sz1 == sz2 then
       Fn (fn, [smt_cval ctx v1; smt_cval ctx v2])
     else if sz1 > sz2 then
       Fn (fn, [smt_cval ctx v1; SignExtend (sz1 - sz2, smt_cval ctx v2)])
     else
       Fn (fn, [SignExtend (sz2 - sz1, smt_cval ctx v1); smt_cval ctx v2])
  | CT_constant c, CT_fint sz ->
     Fn (fn, [bvint sz c; smt_cval ctx v2])
  | CT_constant c, CT_lint ->
     Fn (fn, [bvint ctx.lint_size c; smt_cval ctx v2])
  | CT_fint sz, CT_constant c ->
     Fn (fn, [smt_cval ctx v1; bvint sz c])
  | CT_fint sz, CT_lint when sz < ctx.lint_size ->
     Fn (fn, [SignExtend (ctx.lint_size - sz, smt_cval ctx v1); smt_cval ctx v2])
  | CT_lint, CT_fint sz when sz < ctx.lint_size ->
     Fn (fn, [smt_cval ctx v1; SignExtend (ctx.lint_size - sz, smt_cval ctx v2)])
  | CT_lint, CT_constant c ->
     Fn (fn, [smt_cval ctx v1; bvint ctx.lint_size c])
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
let force_size ?checked:(checked=true) n m smt =
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
    if checked then overflow_check check else ();
    Extract (n - 1, 0, smt)

let int_size ctx = function
  | CT_constant n -> required_width n
  | CT_fint sz -> sz
  | CT_lint -> ctx.lint_size
  | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Argument to int_size must be an integer type"

let builtin_arith fn big_int_fn padding ctx v1 v2 ret_ctyp =
  (* To detect arithmetic overflow we can expand the input bitvectors
     to some size determined by a padding function, then check we
     don't lose precision when going back after performing the
     operation. *)
  let padding = if !opt_ignore_overflow then (fun x -> x) else padding in
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | _, _, CT_constant c ->
     bvint (required_width c) c
  | CT_constant c1, CT_constant c2, _ ->
     bvint (int_size ctx ret_ctyp) (big_int_fn c1 c2)

  | ctyp, CT_constant c, _ ->
     let n = int_size ctx ctyp in
     force_size (int_size ctx ret_ctyp) n (Fn (fn, [smt_cval ctx v1; bvint n c]))
  | CT_constant c, ctyp, _ ->
     let n = int_size ctx ctyp in
     force_size (int_size ctx ret_ctyp) n (Fn (fn, [bvint n c; smt_cval ctx v2]))

  | ctyp1, ctyp2, _ ->
     let ret_sz = int_size ctx ret_ctyp in
     let smt1 = smt_cval ctx v1 in
     let smt2 = smt_cval ctx v2 in
     force_size ret_sz (padding ret_sz) (Fn (fn, [force_size (padding ret_sz) (int_size ctx ctyp1) smt1;
                                                  force_size (padding ret_sz) (int_size ctx ctyp2) smt2]))

let builtin_add_int = builtin_arith "bvadd" Big_int.add (fun x -> x + 1)
let builtin_sub_int = builtin_arith "bvsub" Big_int.sub (fun x -> x + 1)
let builtin_mult_int = builtin_arith "bvmul" Big_int.mul (fun x -> x * 2)

let builtin_negate_int ctx v ret_ctyp =
  match cval_ctyp v, ret_ctyp with
  | _, CT_constant c ->
     bvint (required_width c) c
  | CT_constant c, _ ->
     bvint (int_size ctx ret_ctyp) (Big_int.negate c)
  | ctyp, _ ->
     let smt = force_size (int_size ctx ret_ctyp) (int_size ctx ctyp) (smt_cval ctx v) in
     overflow_check (Fn ("=", [smt; Bin ("1" ^ String.make (int_size ctx ret_ctyp - 1) '0')]));
     Fn ("bvneg", [smt])

let builtin_shift_int fn big_int_fn ctx v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | _, _, CT_constant c ->
     bvint (required_width c) c
  | CT_constant c1, CT_constant c2, _ ->
     bvint (int_size ctx ret_ctyp) (big_int_fn c1 (Big_int.to_int c2))

  | ctyp, CT_constant c, _ ->
     let n = int_size ctx ctyp in
     force_size (int_size ctx ret_ctyp) n (Fn (fn, [smt_cval ctx v1; bvint n c]))
  | CT_constant c, ctyp, _ ->
     let n = int_size ctx ctyp in
     force_size (int_size ctx ret_ctyp) n (Fn (fn, [bvint n c; smt_cval ctx v2]))

  | ctyp1, ctyp2, _ ->
     let ret_sz = int_size ctx ret_ctyp in
     let smt1 = smt_cval ctx v1 in
     let smt2 = smt_cval ctx v2 in
     (Fn (fn, [force_size ret_sz (int_size ctx ctyp1) smt1;
               force_size ret_sz (int_size ctx ctyp2) smt2]))

let builtin_shl_int = builtin_shift_int "bvshl" Big_int.shift_left
let builtin_shr_int = builtin_shift_int "bvashr" Big_int.shift_right

let builtin_abs_int ctx v ret_ctyp =
  match cval_ctyp v, ret_ctyp with
  | _, CT_constant c ->
     bvint (required_width c) c
  | CT_constant c, _ ->
     bvint (int_size ctx ret_ctyp) (Big_int.abs c)
  | ctyp, _ ->
     let sz = int_size ctx ctyp in
     let smt = smt_cval ctx v in
     Ite (Fn ("=", [Extract (sz - 1, sz -1, smt); Bin "1"]),
          force_size (int_size ctx ret_ctyp) sz (Fn ("bvneg", [smt])),
          force_size (int_size ctx ret_ctyp) sz smt)

let builtin_pow2 ctx v ret_ctyp =
  match cval_ctyp v, ret_ctyp with
  | CT_constant n, _ when Big_int.greater_equal n Big_int.zero ->
     bvint (int_size ctx ret_ctyp) (Big_int.pow_int_positive 2 (Big_int.to_int n))

  | _ -> builtin_type_error "pow2" [v] (Some ret_ctyp)

let builtin_zeros ctx v ret_ctyp =
  match cval_ctyp v, ret_ctyp with
  | _, CT_fbits (n, _) -> bvzero n
  | CT_constant c, CT_lbits _ ->
     Fn ("Bits", [bvint ctx.lbits_index c; bvzero (lbits_size ctx)])
  | ctyp, CT_lbits _ when int_size ctx ctyp >= ctx.lbits_index ->
     Fn ("Bits", [extract (ctx.lbits_index - 1) 0 (smt_cval ctx v); bvzero (lbits_size ctx)])
  | _ -> builtin_type_error "zeros" [v] (Some ret_ctyp)

let bvmask ctx len =
  let all_ones = bvones (lbits_size ctx) in
  let shift = Fn ("concat", [bvzero (lbits_size ctx - ctx.lbits_index); len]) in
  bvnot (bvshl all_ones shift)

let builtin_ones ctx cval = function
  | CT_fbits (n, _) -> bvones n
  | CT_lbits _ ->
     let len = extract (ctx.lbits_index - 1) 0 (smt_cval ctx cval) in
     Fn ("Bits", [len; Fn ("bvand", [bvmask ctx len; bvones (lbits_size ctx)])]);
  | ret_ctyp -> builtin_type_error "ones" [cval] (Some ret_ctyp)

(* [bvzeint esz cval] (BitVector Zero Extend INTeger), takes a cval
   which must be an integer type (either CT_fint, or CT_lint), and
   produces a bitvector which is either zero extended or truncated to
   exactly esz bits. *)
let bvzeint ctx esz cval =
  let sz = int_size ctx (cval_ctyp cval) in
  match cval with
  | V_lit (VL_int n, _) ->
     bvint esz n
  | _ ->
     let smt = smt_cval ctx cval in
     if esz = sz then
       smt
     else if esz > sz then
       Fn ("concat", [bvzero (esz - sz); smt])
     else
       Extract (esz - 1, 0, smt)

let builtin_zero_extend ctx vbits vlen ret_ctyp =
  match cval_ctyp vbits, ret_ctyp with
  | CT_fbits (n, _), CT_fbits (m, _) when n = m ->
     smt_cval ctx vbits
  | CT_fbits (n, _), CT_fbits (m, _) ->
     let bv = smt_cval ctx vbits in
     Fn ("concat", [bvzero (m - n); bv])
  | CT_lbits _, CT_fbits (m, _) ->
     assert (lbits_size ctx >= m);
     Extract (m - 1, 0, Fn ("contents", [smt_cval ctx vbits]))
  | CT_fbits (n, _), CT_lbits _ ->
     assert (lbits_size ctx >= n);
     let vbits =
       if lbits_size ctx = n then smt_cval ctx vbits else
       if lbits_size ctx > n then Fn ("concat", [bvzero (lbits_size ctx - n); smt_cval ctx vbits]) else
       assert false
     in
     Fn ("Bits", [bvzeint ctx ctx.lbits_index vlen; vbits])

  | _ -> builtin_type_error "zero_extend" [vbits; vlen] (Some ret_ctyp)

let builtin_sign_extend ctx vbits vlen ret_ctyp =
  match cval_ctyp vbits, ret_ctyp with
  | CT_fbits (n, _), CT_fbits (m, _) when n = m ->
     smt_cval ctx vbits
  | CT_fbits (n, _), CT_fbits (m, _) ->
     let bv = smt_cval ctx vbits in
     let top_bit_one = Fn ("=", [Extract (n - 1, n - 1, bv); Bin "1"]) in
     Ite (top_bit_one, Fn ("concat", [bvones (m - n); bv]), Fn ("concat", [bvzero (m - n); bv]))

  | _ -> builtin_type_error "sign_extend" [vbits; vlen] (Some ret_ctyp)

let builtin_shift shiftop ctx vbits vshift ret_ctyp =
  match cval_ctyp vbits with
  | CT_fbits (n, _) ->
     let bv = smt_cval ctx vbits in
     let len = bvzeint ctx n vshift in
     Fn (shiftop, [bv; len])

  | CT_lbits _ ->
     let bv = smt_cval ctx vbits in
     let shift = bvzeint ctx (lbits_size ctx) vshift in
     Fn ("Bits", [Fn ("len", [bv]); Fn (shiftop, [Fn ("contents", [bv]); shift])])

  | _ -> builtin_type_error shiftop [vbits; vshift] (Some ret_ctyp)

let builtin_not_bits ctx v ret_ctyp =
  match cval_ctyp v, ret_ctyp with
  | CT_lbits _, CT_fbits (n, _) ->
     bvnot (Extract (n - 1, 0, Fn ("contents", [smt_cval ctx v])))

  | CT_lbits _, CT_lbits _ ->
     let bv = smt_cval ctx v in
     let len = Fn ("len", [bv]) in
     Fn ("Bits", [len; Fn ("bvand", [bvmask ctx len; bvnot (Fn ("contents", [bv]))])])

  | CT_fbits (n, _), CT_fbits (m, _) when n = m ->
     bvnot (smt_cval ctx v)

  | _, _ -> builtin_type_error "not_bits" [v] (Some ret_ctyp)

let builtin_bitwise fn ctx v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2 with
  | CT_fbits (n, _), CT_fbits (m, _) ->
     assert (n = m);
     let smt1 = smt_cval ctx v1 in
     let smt2 = smt_cval ctx v2 in
     Fn (fn, [smt1; smt2])

  | CT_lbits _, CT_lbits _ ->
     let smt1 = smt_cval ctx v1 in
     let smt2 = smt_cval ctx v2 in
     Fn ("Bits", [Fn ("len", [smt1]); Fn (fn, [Fn ("contents", [smt1]); Fn ("contents", [smt2])])])

  | _ -> builtin_type_error fn [v1; v2] (Some ret_ctyp)

let builtin_and_bits = builtin_bitwise "bvand"
let builtin_or_bits = builtin_bitwise "bvor"

let builtin_append ctx v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_fbits (m, _), CT_fbits (o, _) ->
     assert (n + m = o);
     let smt1 = smt_cval ctx v1 in
     let smt2 = smt_cval ctx v2 in
     Fn ("concat", [smt1; smt2])

  | CT_fbits (n, _), CT_lbits _, CT_lbits _ ->
     let smt1 = smt_cval ctx v1 in
     let smt2 = smt_cval ctx v2 in
     let x = Fn ("concat", [bvzero (lbits_size ctx - n); smt1]) in
     let shift = Fn ("concat", [bvzero (lbits_size ctx - ctx.lbits_index); Fn ("len", [smt2])]) in
     Fn ("Bits", [bvadd (bvint ctx.lbits_index (Big_int.of_int n)) (Fn ("len", [smt2]));
                  bvor (bvshl x shift) (Fn ("contents", [smt2]))])

  | CT_lbits _, CT_fbits (n, _), CT_lbits _ ->
     let smt1 = smt_cval ctx v1 in
     let smt2 = smt_cval ctx v2 in
     Fn ("Bits", [bvadd (bvint ctx.lbits_index (Big_int.of_int n)) (Fn ("len", [smt1]));
                  Extract (lbits_size ctx - 1, 0, Fn ("concat", [Fn ("contents", [smt1]); smt2]))])

  | CT_lbits _, CT_lbits _, CT_lbits _ ->
     let smt1 = smt_cval ctx v1 in
     let smt2 = smt_cval ctx v2 in
     let x = Fn ("contents", [smt1]) in
     let shift = Fn ("concat", [bvzero (lbits_size ctx - ctx.lbits_index); Fn ("len", [smt2])]) in
     Fn ("Bits", [bvadd (Fn ("len", [smt1])) (Fn ("len", [smt2])); bvor (bvshl x shift) (Fn ("contents", [smt2]))])

  | _ -> builtin_type_error "append" [v1; v2] (Some ret_ctyp)

let builtin_length ctx v ret_ctyp =
  match cval_ctyp v, ret_ctyp with
  | CT_fbits (n, _), (CT_constant _ | CT_fint _ | CT_lint) ->
     bvint (int_size ctx ret_ctyp) (Big_int.of_int n)

  | CT_lbits _, (CT_constant _ | CT_fint _ | CT_lint) ->
     let sz = ctx.lbits_index in
     let m = int_size ctx ret_ctyp in
     let len = Fn ("len", [smt_cval ctx v]) in
     if m = sz then
       len
     else if m > sz then
       Fn ("concat", [bvzero (m - sz); len])
     else
       Extract (m - 1, 0, len)

  | _, _ -> builtin_type_error "length" [v] (Some ret_ctyp)

let builtin_vector_subrange ctx vec i j ret_ctyp =
  match cval_ctyp vec, cval_ctyp i, cval_ctyp j with
  | CT_fbits (n, _), CT_constant i, CT_constant j ->
     Extract (Big_int.to_int i, Big_int.to_int j, smt_cval ctx vec)

  | _ -> failwith "Cannot compile vector subrange"

let builtin_vector_access ctx vec i ret_ctyp =
  match cval_ctyp vec, cval_ctyp i, ret_ctyp with
  | CT_fbits (n, _), CT_constant i, CT_bit ->
     Extract (Big_int.to_int i, Big_int.to_int i, smt_cval ctx vec)

  | CT_vector _, CT_constant i, _ ->
     Fn ("select", [smt_cval ctx vec; bvint !vector_index i])
  | CT_vector _, index_ctyp, _ ->
     Fn ("select", [smt_cval ctx vec; force_size !vector_index (int_size ctx index_ctyp) (smt_cval ctx i)])

  | _ -> builtin_type_error "vector_access" [vec; i] (Some ret_ctyp)

let builtin_vector_update ctx vec i x ret_ctyp =
  match cval_ctyp vec, cval_ctyp i, cval_ctyp x, ret_ctyp with
  | CT_fbits (n, _), CT_constant i, CT_bit, CT_fbits (m, _) when n - 1 > Big_int.to_int i && Big_int.to_int i > 0 ->
     assert (n = m);
     let top = Extract (n - 1, Big_int.to_int i + 1, smt_cval ctx vec) in
     let bot = Extract (Big_int.to_int i - 1, 0, smt_cval ctx vec) in
     Fn ("concat", [top; Fn ("concat", [smt_cval ctx x; bot])])

  | CT_fbits (n, _), CT_constant i, CT_bit, CT_fbits (m, _) when n - 1 = Big_int.to_int i ->
     let bot = Extract (Big_int.to_int i - 1, 0, smt_cval ctx vec) in
     Fn ("concat", [smt_cval ctx x; bot])

  | CT_fbits (n, _), CT_constant i, CT_bit, CT_fbits (m, _) when Big_int.to_int i = 0 ->
     let top = Extract (n - 1, 1, smt_cval ctx vec) in
     Fn ("concat", [top; smt_cval ctx x])

  | CT_vector _, CT_constant i, ctyp, CT_vector _ ->
     Fn ("store", [smt_cval ctx vec; bvint !vector_index i; smt_cval ctx x])
  | CT_vector _, index_ctyp, _, CT_vector _ ->
     Fn ("store", [smt_cval ctx vec; force_size !vector_index (int_size ctx index_ctyp) (smt_cval ctx i); smt_cval ctx x])

  | _ -> builtin_type_error "vector_update" [vec; i; x] (Some ret_ctyp)

let builtin_unsigned ctx v ret_ctyp =
  match cval_ctyp v, ret_ctyp with
  | CT_fbits (n, _), CT_fint m when m > n ->
     let smt = smt_cval ctx v in
     Fn ("concat", [bvzero (m - n); smt])

  | CT_fbits (n, _), CT_lint ->
     if n >= ctx.lint_size then
       failwith "Overflow detected"
     else
       let smt = smt_cval ctx v in
       Fn ("concat", [bvzero (ctx.lint_size - n); smt])

  | ctyp, _ -> builtin_type_error "unsigned" [v] (Some ret_ctyp)

let builtin_signed ctx v ret_ctyp =
  match cval_ctyp v, ret_ctyp with
  | CT_fbits (n, _), CT_fint m when m > n ->
     SignExtend(m - n, smt_cval ctx v)

  | ctyp, _ -> failwith (Printf.sprintf "Cannot compile signed : %s -> %s" (string_of_ctyp ctyp) (string_of_ctyp ret_ctyp))

let builtin_add_bits ctx v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_fbits (m, _), CT_fbits (o, _) ->
     assert (n = m && m = o);
     Fn ("bvadd", [smt_cval ctx v1; smt_cval ctx v2])

  | _ -> builtin_type_error "add_bits" [v1; v2] (Some ret_ctyp)

let builtin_sub_bits ctx v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_fbits (m, _), CT_fbits (o, _) ->
     assert (n = m && m = o);
     Fn ("bvadd", [smt_cval ctx v1; Fn ("bvneg", [smt_cval ctx v2])])

  | _ -> failwith "Cannot compile sub_bits"

let builtin_add_bits_int ctx v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_constant c, CT_fbits (o, _) when n = o ->
     Fn ("bvadd", [smt_cval ctx v1; bvint o c])

  | CT_fbits (n, _), CT_fint m, CT_fbits (o, _) when n = o ->
     Fn ("bvadd", [smt_cval ctx v1; force_size o m (smt_cval ctx v2)])

  | CT_fbits (n, _), CT_lint, CT_fbits (o, _) when n = o ->
     Fn ("bvadd", [smt_cval ctx v1; force_size o ctx.lint_size (smt_cval ctx v2)])

  | _ -> builtin_type_error "add_bits_int" [v1; v2] (Some ret_ctyp)

let builtin_sub_bits_int ctx v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_constant c, CT_fbits (o, _) when n = o ->
     Fn ("bvadd", [smt_cval ctx v1; bvint o (Big_int.negate c)])

  | CT_fbits (n, _), CT_fint m, CT_fbits (o, _) when n = o ->
     Fn ("bvsub", [smt_cval ctx v1; force_size o m (smt_cval ctx v2)])

  | CT_fbits (n, _), CT_lint, CT_fbits (o, _) when n = o ->
     Fn ("bvsub", [smt_cval ctx v1; force_size o ctx.lint_size (smt_cval ctx v2)])

  | _ -> builtin_type_error "sub_bits_int" [v1; v2] (Some ret_ctyp)

let builtin_replicate_bits ctx v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_constant c, CT_fbits (m, _) ->
     assert (n * Big_int.to_int c = m);
     let smt = smt_cval ctx v1 in
     Fn ("concat", List.init (Big_int.to_int c) (fun _ -> smt))

  (*| CT_fbits (n, _), ctyp2, CT_lbits _ ->
     let len = Fn ("bvmul", [bvint ctx.lbits_index (Big_int.of_int n);
                             Extract (ctx.lbits_index - 1, 0, smt_cval ctx v2)])
     in
     assert false*)

  | _ -> builtin_type_error "replicate_bits" [v1; v2] (Some ret_ctyp)

let builtin_sail_truncate ctx v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_constant c, CT_fbits (m, _) ->
     assert (Big_int.to_int c = m);
     Extract (Big_int.to_int c - 1, 0, smt_cval ctx v1)

  | CT_lbits _, CT_constant c, CT_fbits (m, _) ->
     assert (Big_int.to_int c = m && m < lbits_size ctx);
     Extract (Big_int.to_int c - 1, 0, Fn ("contents", [smt_cval ctx v1]))

  | t1, t2, _ -> failwith (Printf.sprintf "Cannot compile sail_truncate (%s, %s) -> %s" (string_of_ctyp t1) (string_of_ctyp t2) (string_of_ctyp ret_ctyp))

let builtin_sail_truncateLSB ctx v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, ret_ctyp with
  | CT_fbits (n, _), CT_constant c, CT_fbits (m, _) ->
     assert (Big_int.to_int c = m);
     Extract (n - 1, n - Big_int.to_int c, smt_cval ctx v1)

  | _ -> failwith "Cannot compile sail_truncate"

let builtin_slice ctx v1 v2 v3 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, cval_ctyp v3, ret_ctyp with
  | CT_lbits _, CT_constant start, CT_constant len, CT_fbits (_, _) ->
     let top = Big_int.pred (Big_int.add start len) in
     Extract(Big_int.to_int top, Big_int.to_int start, Fn ("contents", [smt_cval ctx v1]))

  | CT_fbits (_, _), CT_constant start, CT_constant len, CT_fbits (_, _) ->
     let top = Big_int.pred (Big_int.add start len) in
     Extract(Big_int.to_int top, Big_int.to_int start, smt_cval ctx v1)

  | CT_fbits (_, ord), CT_fint _, CT_constant len, CT_fbits (_, _) ->
     Extract(Big_int.to_int (Big_int.pred len), 0, builtin_shift "bvlshr" ctx v1 v2 (cval_ctyp v1))

  | CT_fbits(n, ord), ctyp2, _, CT_lbits _ ->
     let smt1 = force_size (lbits_size ctx) n (smt_cval ctx v1) in
     let smt2 = force_size (lbits_size ctx) (int_size ctx ctyp2) (smt_cval ctx v2) in
     let smt3 = bvzeint ctx ctx.lbits_index v3 in
     Fn ("Bits", [smt3; Fn ("bvand", [Fn ("bvlshr", [smt1; smt2]); bvmask ctx smt3])])

  | _ -> builtin_type_error "slice" [v1; v2; v3] (Some ret_ctyp)

let builtin_get_slice_int ctx v1 v2 v3 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, cval_ctyp v3, ret_ctyp with
  | CT_constant len, ctyp, CT_constant start, CT_fbits (ret_sz, _) ->
     let len = Big_int.to_int len in
     let start = Big_int.to_int start in
     let in_sz = int_size ctx ctyp in
     let smt =
       if in_sz < len + start then
         force_size (len + start) in_sz (smt_cval ctx v2)
       else
         smt_cval ctx v2
     in
     Extract ((start + len) - 1, start, smt)

  | _, _, _, _ -> builtin_type_error "get_slice_int" [v1; v2; v3] (Some ret_ctyp)

let builtin_count_leading_zeros ctx v ret_ctyp =
  let ret_sz = int_size ctx ret_ctyp in
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
     lzcnt sz (smt_cval ctx v)

  | CT_fbits (sz, _) ->
     let padded_sz = smallest_greater_power_of_two sz in
     let padding = bvzero (padded_sz - sz) in
     Fn ("bvsub", [lzcnt padded_sz (Fn ("concat", [padding; smt_cval ctx v]));
                   bvint ret_sz (Big_int.of_int (padded_sz - sz))])

  | CT_lbits _ ->
     let smt = smt_cval ctx v in
     Fn ("bvsub", [lzcnt (lbits_size ctx) (Fn ("contents", [smt]));
                   Fn ("bvsub", [bvint ret_sz (Big_int.of_int (lbits_size ctx));
                                 Fn ("concat", [bvzero (ret_sz - ctx.lbits_index); Fn ("len", [smt])])])])

  | _ -> builtin_type_error "count_leading_zeros" [v] (Some ret_ctyp)

let builtin_set_slice_bits ctx v1 v2 v3 v4 v5 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2, cval_ctyp v3, cval_ctyp v4, cval_ctyp v5, ret_ctyp with
  | CT_constant n', CT_constant m', CT_fbits (n, _), CT_constant pos, CT_fbits (m, _), CT_fbits(n'', _)
    when Big_int.to_int m' = m && Big_int.to_int n' = n && n'' = n && Big_int.less_equal (Big_int.add pos m') n' ->
     let pos = Big_int.to_int pos in
     if pos = 0 then
       let mask = Fn ("concat", [bvones (n - m); bvzero m]) in
       let smt5 = Fn ("concat", [bvzero (n - m); smt_cval ctx v5]) in
       Fn ("bvor", [Fn ("bvand", [smt_cval ctx v3; mask]); smt5])
     else if n - m - pos = 0 then
       let mask = Fn ("concat", [bvzero m; bvones pos]) in
       let smt5 = Fn ("concat", [smt_cval ctx v5; bvzero pos]) in
       Fn ("bvor", [Fn ("bvand", [smt_cval ctx v3; mask]); smt5])
     else
       let mask = Fn ("concat", [bvones (n - m - pos); Fn ("concat", [bvzero m; bvones pos])]) in
       let smt5 = Fn ("concat", [bvzero (n - m - pos); Fn ("concat", [smt_cval ctx v5; bvzero pos])]) in
       Fn ("bvor", [Fn ("bvand", [smt_cval ctx v3; mask]); smt5])

  | _ -> builtin_type_error "set_slice" [v1; v2; v3; v4; v5] (Some ret_ctyp)

let builtin_compare_bits fn ctx v1 v2 ret_ctyp =
  match cval_ctyp v1, cval_ctyp v2 with
  | CT_fbits (n, _), CT_fbits (m, _) when n = m ->
     Fn (fn, [smt_cval ctx v1; smt_cval ctx v2])

  | _ -> builtin_type_error fn [v1; v2] (Some ret_ctyp)

let smt_builtin ctx name args ret_ctyp =
  match name, args, ret_ctyp with
  | "eq_bits", [v1; v2], _ -> Fn ("=", [smt_cval ctx v1; smt_cval ctx v2])
  | "eq_anything", [v1; v2], CT_bool -> Fn ("=", [smt_cval ctx v1; smt_cval ctx v2])

  (* lib/flow.sail *)
  | "eq_bit",  [v1; v2], CT_bool -> Fn ("=", [smt_cval ctx v1; smt_cval ctx v2])
  | "eq_bool", [v1; v2], CT_bool -> Fn ("=", [smt_cval ctx v1; smt_cval ctx v2])
  | "eq_unit", [v1; v2], CT_bool -> Fn ("=", [smt_cval ctx v1; smt_cval ctx v2])

  | "eq_int",  [v1; v2], CT_bool -> builtin_eq_int ctx v1 v2

  | "not", [v], _ -> Fn ("not", [smt_cval ctx v])
  | "lt",   [v1; v2], _ -> builtin_lt ctx v1 v2
  | "lteq", [v1; v2], _ -> builtin_lteq ctx v1 v2
  | "gt",   [v1; v2], _ -> builtin_gt ctx v1 v2
  | "gteq", [v1; v2], _ -> builtin_gteq ctx v1 v2

  (* lib/arith.sail *)
  | "add_int", [v1; v2], _ -> builtin_add_int ctx v1 v2 ret_ctyp
  | "sub_int", [v1; v2], _ -> builtin_sub_int ctx v1 v2 ret_ctyp
  | "mult_int", [v1; v2], _ -> builtin_mult_int ctx v1 v2 ret_ctyp
  | "neg_int", [v], _ -> builtin_negate_int ctx v ret_ctyp
  | "shl_int", [v1; v2], _ -> builtin_shl_int ctx v1 v2 ret_ctyp
  | "shr_int", [v1; v2], _ -> builtin_shr_int ctx v1 v2 ret_ctyp
  | "shl_mach_int", [v1; v2], _ -> builtin_shl_int ctx v1 v2 ret_ctyp
  | "shr_mach_int", [v1; v2], _ -> builtin_shr_int ctx v1 v2 ret_ctyp
  | "abs_int", [v], _ -> builtin_abs_int ctx v ret_ctyp
  | "pow2", [v], _ -> builtin_pow2 ctx v ret_ctyp

  (* All signed and unsigned bitvector comparisons *)
  | "slt_bits", [v1; v2], CT_bool -> builtin_compare_bits "bvslt" ctx v1 v2 ret_ctyp
  | "ult_bits", [v1; v2], CT_bool -> builtin_compare_bits "bvult" ctx v1 v2 ret_ctyp
  | "sgt_bits", [v1; v2], CT_bool -> builtin_compare_bits "bvsgt" ctx v1 v2 ret_ctyp
  | "ugt_bits", [v1; v2], CT_bool -> builtin_compare_bits "bvugt" ctx v1 v2 ret_ctyp
  | "slteq_bits", [v1; v2], CT_bool -> builtin_compare_bits "bvsle" ctx v1 v2 ret_ctyp
  | "ulteq_bits", [v1; v2], CT_bool -> builtin_compare_bits "bvule" ctx v1 v2 ret_ctyp
  | "sgteq_bits", [v1; v2], CT_bool -> builtin_compare_bits "bvsge" ctx v1 v2 ret_ctyp
  | "ugteq_bits", [v1; v2], CT_bool -> builtin_compare_bits "bvuge" ctx v1 v2 ret_ctyp

  (* lib/vector_dec.sail *)
  | "zeros", [v], _ -> builtin_zeros ctx v ret_ctyp
  | "sail_zeros", [v], _ -> builtin_zeros ctx v ret_ctyp
  | "ones", [v], _ -> builtin_ones ctx v ret_ctyp
  | "sail_ones", [v], _ -> builtin_ones ctx v ret_ctyp
  | "zero_extend", [v1; v2], _ -> builtin_zero_extend ctx v1 v2 ret_ctyp
  | "sign_extend", [v1; v2], _ -> builtin_sign_extend ctx v1 v2 ret_ctyp
  | "sail_truncate", [v1; v2], _ -> builtin_sail_truncate ctx v1 v2 ret_ctyp
  | "sail_truncateLSB", [v1; v2], _ -> builtin_sail_truncateLSB ctx v1 v2 ret_ctyp
  | "shiftl", [v1; v2], _ -> builtin_shift "bvshl" ctx v1 v2 ret_ctyp
  | "shiftr", [v1; v2], _ -> builtin_shift "bvlshr" ctx v1 v2 ret_ctyp
  | "or_bits", [v1; v2], _ -> builtin_or_bits ctx v1 v2 ret_ctyp
  | "and_bits", [v1; v2], _ -> builtin_and_bits ctx v1 v2 ret_ctyp
  | "not_bits", [v], _ -> builtin_not_bits ctx v ret_ctyp
  | "add_bits", [v1; v2], _ -> builtin_add_bits ctx v1 v2 ret_ctyp
  | "add_bits_int", [v1; v2], _ -> builtin_add_bits_int ctx v1 v2 ret_ctyp
  | "sub_bits", [v1; v2], _ -> builtin_sub_bits ctx v1 v2 ret_ctyp
  | "sub_bits_int", [v1; v2], _ -> builtin_sub_bits_int ctx v1 v2 ret_ctyp
  | "append", [v1; v2], _ -> builtin_append ctx v1 v2 ret_ctyp
  | "length", [v], ret_ctyp -> builtin_length ctx v ret_ctyp
  | "vector_access", [v1; v2], ret_ctyp -> builtin_vector_access ctx v1 v2 ret_ctyp
  | "vector_subrange", [v1; v2; v3], ret_ctyp -> builtin_vector_subrange ctx v1 v2 v3 ret_ctyp
  | "vector_update", [v1; v2; v3], ret_ctyp -> builtin_vector_update ctx v1 v2 v3 ret_ctyp
  | "sail_unsigned", [v], ret_ctyp -> builtin_unsigned ctx v ret_ctyp
  | "sail_signed", [v], ret_ctyp -> builtin_signed ctx v ret_ctyp
  | "replicate_bits", [v1; v2], ret_ctyp -> builtin_replicate_bits ctx v1 v2 ret_ctyp
  | "count_leading_zeros", [v], ret_ctyp -> builtin_count_leading_zeros ctx v ret_ctyp
  | "slice", [v1; v2; v3], ret_ctyp -> builtin_slice ctx v1 v2 v3 ret_ctyp
  | "get_slice_int", [v1; v2; v3], ret_ctyp -> builtin_get_slice_int ctx v1 v2 v3 ret_ctyp
  | "set_slice", [v1; v2; v3; v4; v5], ret_ctyp -> builtin_set_slice_bits ctx v1 v2 v3 v4 v5 ret_ctyp

  | _ -> failwith ("Unknown builtin " ^ name ^ " " ^ Util.string_of_list ", " string_of_ctyp (List.map cval_ctyp args) ^ " -> " ^ string_of_ctyp ret_ctyp)

let rec smt_conversion ctx from_ctyp to_ctyp x =
  match from_ctyp, to_ctyp with
  | _, _ when ctyp_equal from_ctyp to_ctyp -> x
  | CT_constant c, CT_fint sz ->
     bvint sz c
  | CT_constant c, CT_lint ->
     bvint ctx.lint_size c
  | _, _ -> failwith (Printf.sprintf "Cannot perform conversion from %s to %s" (string_of_ctyp from_ctyp) (string_of_ctyp to_ctyp))

let define_const ctx id ctyp exp = Define_const (zencode_name id, smt_ctyp ctx ctyp, exp)
let declare_const ctx id ctyp = Declare_const (zencode_name id, smt_ctyp ctx ctyp)

let smt_ctype_def ctx = function
  | CTD_enum (id, elems) ->
     [declare_datatypes (mk_enum (zencode_upper_id id) (List.map zencode_id elems))]

  | CTD_struct (id, fields) ->
     [declare_datatypes
       (mk_record (zencode_upper_id id)
          (List.map (fun (field, ctyp) -> zencode_upper_id id ^ "_" ^ zencode_id field, smt_ctyp ctx ctyp) fields))]

  | CTD_variant (id, ctors) ->
     [declare_datatypes
       (mk_variant (zencode_upper_id id)
         (List.map (fun (ctor, ctyp) -> zencode_id ctor, smt_ctyp ctx ctyp) ctors))]

let rec generate_ctype_defs ctx = function
  | CDEF_type ctd :: cdefs -> smt_ctype_def ctx ctd :: generate_ctype_defs ctx cdefs
  | _ :: cdefs -> generate_ctype_defs ctx cdefs
  | [] -> []

let rec generate_reg_decs ctx inits = function
  | CDEF_reg_dec (id, ctyp, _) :: cdefs when not (NameMap.mem (Name (id, 0)) inits)->
     Declare_const (zencode_name (Name (id, 0)), smt_ctyp ctx ctyp)
     :: generate_reg_decs ctx inits cdefs
  | _ :: cdefs -> generate_reg_decs ctx inits cdefs
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

  (* Note that we have to use lbits for zero-length bitvectors because they are not allowed by SMTLIB *)
  | Typ_app (id, [A_aux (A_nexp n, _);
                  A_aux (A_order ord, _);
                  A_aux (A_typ (Typ_aux (Typ_id vtyp_id, _)), _)])
       when string_of_id id = "vector" && string_of_id vtyp_id = "bit" ->
     let direction = match ord with Ord_aux (Ord_dec, _) -> true | Ord_aux (Ord_inc, _) -> false | _ -> assert false in
     begin match nexp_simp n with
     | Nexp_aux (Nexp_constant n, _) when Big_int.equal n Big_int.zero -> CT_lbits direction
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

let unroll_foreach ctx = function
  | AE_aux (AE_for (id, from_aexp, to_aexp, by_aexp, order, body), env, l) as aexp ->
     begin match ctyp_of_typ ctx (aexp_typ from_aexp), ctyp_of_typ ctx (aexp_typ to_aexp), ctyp_of_typ ctx (aexp_typ by_aexp), order with
     | CT_constant f, CT_constant t, CT_constant b, Ord_aux (Ord_inc, _) ->
        let i = ref f in
        let unrolled = ref [] in
        while Big_int.less_equal !i t do
          let current_index = AE_aux (AE_val (AV_lit (L_aux (L_num !i, gen_loc l), atom_typ (nconstant !i))), env, gen_loc l) in
          let iteration = AE_aux (AE_let (Immutable, id, atom_typ (nconstant !i), current_index, body, unit_typ), env, gen_loc l) in
          unrolled := iteration :: !unrolled;
          i := Big_int.add !i b
        done;
        begin match !unrolled with
        | last :: iterations ->
           AE_aux (AE_block (List.rev iterations, last, unit_typ), env, gen_loc l)
        | [] -> AE_aux (AE_val (AV_lit (L_aux (L_unit, gen_loc l), unit_typ)), env, gen_loc l)
        end
     | _ -> aexp
     end
  | aexp -> aexp

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
let smt_ssanode ctx cfg preds =
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
             | [cval] -> smt_cval ctx cval
             | _ -> Fn ("and", List.map (smt_cval ctx) pi)
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
        [Define_const (zencode_name id, smt_ctyp ctx ctyp, mux)]

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
let smt_instr ctx =
  let open Type_check in
  function
  | I_aux (I_funcall (CL_id (id, ret_ctyp), extern, function_id, args), (_, l)) ->
     if Env.is_extern function_id ctx.tc_env "c" && not extern then
       let name = Env.get_extern function_id ctx.tc_env "c" in
       let value = smt_builtin ctx name args ret_ctyp in
       [define_const ctx id ret_ctyp value]
     else if extern && string_of_id function_id = "internal_vector_init" then
       [declare_const ctx id ret_ctyp]
     else if extern && string_of_id function_id = "internal_vector_update" then
       begin match args with
       | [vec; i; x] ->
          let sz = int_size ctx (cval_ctyp i) in
          [define_const ctx id ret_ctyp
             (Fn ("store", [smt_cval ctx vec; force_size ~checked:false ctx.vector_index sz (smt_cval ctx i); smt_cval ctx x]))]
       | _ ->
          Reporting.unreachable l __POS__ "Bad arguments for internal_vector_update"
       end
     else
       let smt_args = List.map (smt_cval ctx) args in
       [define_const ctx id ret_ctyp (Fn (zencode_id function_id, smt_args))]

  | I_aux (I_copy (CL_addr (CL_id (_, _)), _), (_, l)) ->
     Reporting.unreachable l __POS__ "Register reference write should be re-written by now"

  | I_aux (I_init (ctyp, id, cval), _) | I_aux (I_copy (CL_id (id, ctyp), cval), _) ->
     [define_const ctx id ctyp
        (smt_conversion ctx (cval_ctyp cval) ctyp (smt_cval ctx cval))]

  | I_aux (I_copy (clexp, cval), _) ->
     let smt = smt_cval ctx cval in
     let write, ctyp = rmw_write clexp in
     [define_const ctx write ctyp (rmw_modify smt clexp)]

  | I_aux (I_decl (ctyp, id), _) ->
     [declare_const ctx id ctyp]

  | I_aux (I_end id, _) ->
     if !opt_ignore_overflow then
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

let smt_cfnode all_cdefs ctx =
  let open Jib_ssa in
  function
  | CF_start inits ->
     let smt_reg_decs = generate_reg_decs ctx inits all_cdefs in
     let smt_start (id, ctyp) =
       match id with
       | Have_exception _ -> define_const ctx id ctyp (Bool_lit false)
       | _ -> declare_const ctx id ctyp
     in
     smt_reg_decs @ List.map smt_start (NameMap.bindings inits)
  | CF_block instrs ->
     List.concat (List.map (smt_instr ctx) instrs)
  (* We can ignore any non basic-block/start control-flow nodes *)
  | _ -> []

(** When we generate a property for a CDEF_spec, we find it's
   associated function body in a CDEF_fundef node. However, we must
   keep track of any global letbindings between the spec and the
   fundef, so they can appear in the generated SMT. *)
let rec find_function lets id = function
  | CDEF_fundef (id', heap_return, args, body) :: _ when Id.compare id id' = 0 ->
     lets, Some (heap_return, args, body)
  | CDEF_let (_, vars, setup) :: cdefs ->
     let vars = List.map (fun (id, ctyp) -> idecl ctyp (name id)) vars in
     find_function (lets @ vars @ setup) id cdefs;
  | _ :: cdefs ->
     find_function lets id cdefs
  | [] -> lets, None

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
let smt_header ctx stack cdefs =
  push_smt_defs stack
    [declare_datatypes (mk_enum "Unit" ["unit"]);
     Declare_tuple 2;
     Declare_tuple 3;
     Declare_tuple 4;
     Declare_tuple 5;
     declare_datatypes (mk_record "Bits" [("len", Bitvec ctx.lbits_index);
                                          ("contents", Bitvec (lbits_size ctx))])

    ];
  let smt_type_defs = List.concat (generate_ctype_defs ctx cdefs) in
  push_smt_defs stack smt_type_defs

(* For generating SMT when we have a reg_deref(r : register(t))
   function, we have to expand it into a if-then-else cascade that
   checks if r is any one of the registers with type t, and reads that
   register if it is. We also do a similar thing for *r = x
*)
let expand_reg_deref ctx = function
  | I_aux (I_funcall (clexp, false, function_id, [reg_ref]), (_, l)) as instr ->
     let open Type_check in
     begin match (if Env.is_extern function_id ctx.tc_env "smt" then Some (Env.get_extern function_id ctx.tc_env "smt") else None) with
     | Some "reg_deref" ->
        begin match cval_ctyp reg_ref with
        | CT_ref reg_ctyp ->
           (* Not find all the registers with this ctyp *)
           begin match CTMap.find_opt reg_ctyp ctx.register_map with
           | Some regs ->
              let end_label = label "end_reg_deref_" in
              let try_reg r =
                let next_label = label "next_reg_deref_" in
                [ijump (V_op (V_ref (name r, reg_ctyp), "!=", reg_ref)) next_label;
                 icopy l clexp (V_id (name r, reg_ctyp));
                 igoto end_label;
                 ilabel next_label]
              in
              iblock (List.concat (List.map try_reg regs) @ [ilabel end_label])
           | None ->
              raise (Reporting.err_general l ("Could not find any registers with type " ^ string_of_ctyp reg_ctyp))
           end
        | _ ->
           raise (Reporting.err_general l "Register dereference must have a register reference as an argument")
        end
     | _ -> instr
     end
  | I_aux (I_copy (CL_addr (CL_id (id, ctyp)), cval), (_, l)) ->
     begin match ctyp with
     | CT_ref reg_ctyp ->
        begin match CTMap.find_opt reg_ctyp ctx.register_map with
        | Some regs ->
           let end_label = label "end_reg_write_" in
           let try_reg r =
             let next_label = label "next_reg_write_" in
             [ijump (V_op (V_ref (name r, reg_ctyp), "!=", V_id (id, ctyp))) next_label;
              icopy l (CL_id (name r, reg_ctyp)) cval;
              igoto end_label;
              ilabel next_label]
           in
           iblock (List.concat (List.map try_reg regs) @ [ilabel end_label])
        | None ->
           raise (Reporting.err_general l ("Could not find any registers with type " ^ string_of_ctyp reg_ctyp))
        end
     | _ ->
        raise (Reporting.err_general l "Register reference assignment must take a register reference as an argument")
     end
  | instr -> instr

let smt_cdef props lets name_file ctx all_cdefs = function
  | CDEF_spec (function_id, arg_ctyps, ret_ctyp) when Bindings.mem function_id props ->
     begin match find_function [] function_id all_cdefs with
     | intervening_lets, Some (None, args, instrs) ->
        let prop_type, prop_args, pragma_l, vs = Bindings.find function_id props in

        let stack = Stack.create () in

        smt_header ctx stack all_cdefs;
        let arg_decls =
          List.map2 (fun id ctyp -> idecl ctyp (name id)) args arg_ctyps
        in
        let instrs =
          let open Jib_optimize in
          (lets @ intervening_lets @ arg_decls @ instrs)
          |> inline all_cdefs (fun _ -> true)
          |> List.map (map_instr (expand_reg_deref ctx))
          |> flatten_instrs
          |> remove_unused_labels
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
                 ssanodes |> List.map (smt_ssanode ctx cfg preds) |> List.concat
               in
               let basic_block = smt_cfnode all_cdefs ctx cfnode in
               push_smt_defs stack muxers;
               push_smt_defs stack basic_block;
            end
          ) visit_order;

        let fname = name_file (string_of_id function_id) in
        let out_chan = open_out fname in
        if prop_type = "counterexample" then
          output_string out_chan "(set-option :produce-models true)\n";
        output_string out_chan "(set-logic QF_AUFBVDT)\n";

        (* let stack' = Stack.create () in
        Stack.iter (fun def -> Stack.push def stack') stack;
        Stack.iter (fun def -> output_string out_chan (string_of_smt_def def); output_string out_chan "\n") stack'; *)
        let queue = optimize_smt stack in
        Queue.iter (fun def -> output_string out_chan (string_of_smt_def def); output_string out_chan "\n") queue;

        output_string out_chan "(check-sat)\n";
        if prop_type = "counterexample" then
          output_string out_chan "(get-model)\n";

        close_out out_chan;
        if prop_type = "counterexample" then
          check_counterexample fname args

     | _ -> failwith "Bad function body"
     end
  | _ -> ()

let rec smt_cdefs props lets name_file ctx ast =
  function
  | CDEF_let (_, vars, setup) :: cdefs ->
     let vars = List.map (fun (id, ctyp) -> idecl ctyp (name id)) vars in
     smt_cdefs props (lets @ vars @ setup) name_file ctx ast cdefs;
  | cdef :: cdefs ->
     smt_cdef props lets name_file ctx ast cdef;
     smt_cdefs props lets name_file ctx ast cdefs
  | [] -> ()

(* In order to support register references, we need to build a map
   from each ctyp to a list of registers with that ctyp, then when we
   see a type like register(bits(32)) we can use the map to figure out
   all the registers that such a reference could be pointing to.
*)
let rec build_register_map rmap = function
  | CDEF_reg_dec (reg, ctyp, _) :: cdefs ->
     let rmap = match CTMap.find_opt ctyp rmap with
       | Some regs ->
          CTMap.add ctyp (reg :: regs) rmap
       | None ->
          CTMap.add ctyp [reg] rmap
     in
     build_register_map rmap cdefs
  | _ :: cdefs -> build_register_map rmap cdefs
  | [] -> rmap

let generate_smt props name_file env ast =
  try
    let cdefs =
      let open Jib_compile in
      let ctx =
        initial_ctx
          ~convert_typ:ctyp_of_typ
          ~optimize_anf:(fun ctx aexp -> fold_aexp (unroll_foreach ctx) (c_literals ctx aexp))
          env
      in
      let t = Profile.start () in
      let cdefs, ctx = compile_ast { ctx with specialize_calls = true; ignore_64 = true; struct_value = true } ast in
      Profile.finish "Compiling to Jib IR" t;
      cdefs
    in
    let cdefs = Jib_optimize.unique_per_function_ids cdefs in
    let rmap = build_register_map CTMap.empty cdefs in

    smt_cdefs props [] name_file { (initial_ctx ()) with tc_env = env; register_map = rmap } cdefs cdefs
  with
  | Type_check.Type_error (_, l, err) ->
     raise (Reporting.err_typ l (Type_error.string_of_type_error err));
