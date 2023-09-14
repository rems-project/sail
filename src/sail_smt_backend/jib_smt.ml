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

open Libsail

open Anf
open Ast
open Ast_defs
open Ast_util
open Jib
open Jib_util
open Smtlib
open Property

module IntSet = Set.Make (struct
  type t = int
  let compare = compare
end)
module IntMap = Map.Make (struct
  type t = int
  let compare = compare
end)

let zencode_upper_id id = Util.zencode_upper_string (string_of_id id)
let zencode_id id = Util.zencode_string (string_of_id id)
let zencode_name id = string_of_name ~deref_current_exception:false ~zencode:true id
let zencode_uid (id, ctyps) =
  match ctyps with
  | [] -> Util.zencode_string (string_of_id id)
  | _ -> Util.zencode_string (string_of_id id ^ "#" ^ Util.string_of_list "_" string_of_ctyp ctyps)

let opt_ignore_overflow = ref false

let opt_auto = ref false

let opt_debug_graphs = ref false

let opt_propagate_vars = ref false

let opt_unroll_limit = ref 10

module EventMap = Map.Make (Event)

(* Note that we have to use x : ty ref rather than mutable x : ty, to
   make sure { ctx with x = ... } doesn't break the mutable state. *)

(* See mli file for a description of each field *)
type ctx = {
  lbits_index : int;
  lint_size : int;
  vector_index : int;
  register_map : id list CTMap.t;
  tuple_sizes : IntSet.t ref;
  tc_env : Type_check.Env.t;
  pragma_l : Ast.l;
  arg_stack : (int * string) Stack.t;
  ast : Type_check.tannot ast;
  shared : ctyp Bindings.t;
  preserved : IdSet.t;
  events : smt_exp Stack.t EventMap.t ref;
  node : int;
  pathcond : smt_exp Lazy.t;
  use_string : bool ref;
  use_real : bool ref;
}

(* These give the default bounds for various SMT types, stored in the
   initial_ctx. They shouldn't be read or written by anything else! If
   they are changed the output of sail -help needs to be updated to
   reflect this. *)
let opt_default_lint_size = ref 128
let opt_default_lbits_index = ref 8
let opt_default_vector_index = ref 5

let initial_ctx () =
  {
    lbits_index = !opt_default_lbits_index;
    lint_size = !opt_default_lint_size;
    vector_index = !opt_default_vector_index;
    register_map = CTMap.empty;
    tuple_sizes = ref IntSet.empty;
    tc_env = Type_check.initial_env;
    pragma_l = Parse_ast.Unknown;
    arg_stack = Stack.create ();
    ast = empty_ast;
    shared = Bindings.empty;
    preserved = IdSet.empty;
    events = ref EventMap.empty;
    node = -1;
    pathcond = lazy (Bool_lit true);
    use_string = ref false;
    use_real = ref false;
  }

let event_stack ctx ev =
  match EventMap.find_opt ev !(ctx.events) with
  | Some stack -> stack
  | None ->
      let stack = Stack.create () in
      ctx.events := EventMap.add ev stack !(ctx.events);
      stack

let add_event ctx ev smt =
  let stack = event_stack ctx ev in
  Stack.push (Fn ("and", [Lazy.force ctx.pathcond; smt])) stack

let add_pathcond_event ctx ev = Stack.push (Lazy.force ctx.pathcond) (event_stack ctx ev)

let overflow_check ctx smt =
  if not !opt_ignore_overflow then (
    Reporting.warn "Overflow check in generated SMT for" ctx.pragma_l "";
    add_event ctx Overflow smt
  )

let lbits_size ctx = Util.power 2 ctx.lbits_index

let vector_index = ref 5

let smt_unit = mk_enum "Unit" ["Unit"]
let smt_lbits ctx = mk_record "Bits" [("size", Bitvec ctx.lbits_index); ("bits", Bitvec (lbits_size ctx))]

(* [required_width n] is the required number of bits to losslessly
   represent an integer n *)
let required_width n =
  let rec required_width' n =
    if Big_int.equal n Big_int.zero then 1 else 1 + required_width' (Big_int.shift_right n 1)
  in
  required_width' (Big_int.abs n)

let rec smt_ctyp ctx = function
  | CT_constant n -> Bitvec (required_width n)
  | CT_fint n -> Bitvec n
  | CT_lint -> Bitvec ctx.lint_size
  | CT_unit -> smt_unit
  | CT_bit -> Bitvec 1
  | CT_fbits n -> Bitvec n
  | CT_sbits n -> smt_lbits ctx
  | CT_lbits -> smt_lbits ctx
  | CT_bool -> Bool
  | CT_enum (id, elems) -> mk_enum (zencode_upper_id id) (List.map zencode_id elems)
  | CT_struct (id, fields) ->
      mk_record (zencode_upper_id id) (List.map (fun (id, ctyp) -> (zencode_id id, smt_ctyp ctx ctyp)) fields)
  | CT_variant (id, ctors) ->
      mk_variant (zencode_upper_id id) (List.map (fun (id, ctyp) -> (zencode_id id, smt_ctyp ctx ctyp)) ctors)
  | CT_tup ctyps ->
      ctx.tuple_sizes := IntSet.add (List.length ctyps) !(ctx.tuple_sizes);
      Tuple (List.map (smt_ctyp ctx) ctyps)
  | CT_vector ctyp | CT_fvector (_, ctyp) -> Array (Bitvec !vector_index, smt_ctyp ctx ctyp)
  | CT_string ->
      ctx.use_string := true;
      String
  | CT_real ->
      ctx.use_real := true;
      Real
  | CT_ref ctyp -> begin
      match CTMap.find_opt ctyp ctx.register_map with
      | Some regs -> Bitvec (required_width (Big_int.of_int (List.length regs)))
      | _ -> failwith ("No registers with ctyp: " ^ string_of_ctyp ctyp)
    end
  | CT_list _ -> raise (Reporting.err_todo ctx.pragma_l "Lists not yet supported in SMT generation")
  | CT_float _ | CT_rounding_mode -> Reporting.unreachable ctx.pragma_l __POS__ "Floating point in SMT property"
  | CT_poly _ -> Reporting.unreachable ctx.pragma_l __POS__ "Found polymorphic type in SMT property"

(* We often need to create a SMT bitvector of a length sz with integer
   value x. [bvpint sz x] does this for positive integers, and [bvint sz x]
   does this for all integers. It's quite awkward because we
   don't have a very good way to get the binary representation of
   either an ocaml integer or a big integer. *)
let bvpint sz x =
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
        (Reporting.err_general Parse_ast.Unknown
           (Printf.sprintf "Could not create a %d-bit integer with value %s.\nTry increasing the maximum integer size"
              sz (Big_int.to_string x)
           )
        );
    let padding = List.init padding_size (fun _ -> B0) in
    Bitvec_lit (padding @ !bin)
  )
  else failwith "Invalid bvpint"

let bvint sz x =
  if Big_int.less x Big_int.zero then
    Fn ("bvadd", [Fn ("bvnot", [bvpint sz (Big_int.abs x)]); bvpint sz (Big_int.of_int 1)])
  else bvpint sz x

(** [force_size ctx n m exp] takes a smt expression assumed to be a
   integer (signed bitvector) of length m and forces it to be length n
   by either sign extending it or truncating it as required *)
let force_size ?(checked = true) ctx n m smt =
  if n = m then smt
  else if n > m then SignExtend (n - m, smt)
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
    if checked then overflow_check ctx check else ();
    Extract (n - 1, 0, smt)
  )

(** [unsigned_size ctx n m exp] is much like force_size, but it
   assumes that the bitvector is unsigned *)
let unsigned_size ?(checked = true) ctx n m smt =
  if n = m then smt else if n > m then Fn ("concat", [bvzero (n - m); smt]) else Extract (n - 1, 0, smt)

let smt_conversion ctx from_ctyp to_ctyp x =
  match (from_ctyp, to_ctyp) with
  | _, _ when ctyp_equal from_ctyp to_ctyp -> x
  | CT_constant c, CT_fint sz -> bvint sz c
  | CT_constant c, CT_lint -> bvint ctx.lint_size c
  | CT_fint sz, CT_lint -> force_size ctx ctx.lint_size sz x
  | CT_lint, CT_fint sz -> force_size ctx sz ctx.lint_size x
  | CT_lint, CT_fbits n -> force_size ctx n ctx.lint_size x
  | CT_lint, CT_lbits ->
      Fn
        ("Bits", [bvint ctx.lbits_index (Big_int.of_int ctx.lint_size); force_size ctx (lbits_size ctx) ctx.lint_size x])
  | CT_fint n, CT_lbits -> Fn ("Bits", [bvint ctx.lbits_index (Big_int.of_int n); force_size ctx (lbits_size ctx) n x])
  | CT_lbits, CT_fbits n -> unsigned_size ctx n (lbits_size ctx) (Fn ("contents", [x]))
  | CT_fbits n, CT_fbits m -> unsigned_size ctx m n x
  | CT_fbits n, CT_lbits ->
      Fn ("Bits", [bvint ctx.lbits_index (Big_int.of_int n); unsigned_size ctx (lbits_size ctx) n x])
  | CT_fvector _, CT_vector _ -> x
  | CT_vector _, CT_fvector _ -> x
  | _, _ ->
      failwith
        (Printf.sprintf "Cannot perform conversion from %s to %s" (string_of_ctyp from_ctyp) (string_of_ctyp to_ctyp))

(* Translate Jib literals into SMT *)
let smt_value ctx vl ctyp =
  let open Value2 in
  match (vl, ctyp) with
  | VL_bits bv, CT_fbits n -> unsigned_size ctx n (List.length bv) (Bitvec_lit bv)
  | VL_bits bv, CT_lbits ->
      let sz = List.length bv in
      Fn ("Bits", [bvint ctx.lbits_index (Big_int.of_int sz); unsigned_size ctx (lbits_size ctx) sz (Bitvec_lit bv)])
  | VL_bool b, _ -> Bool_lit b
  | VL_int n, CT_constant m -> bvint (required_width n) n
  | VL_int n, CT_fint sz -> bvint sz n
  | VL_int n, CT_lint -> bvint ctx.lint_size n
  | VL_bit b, CT_bit -> Bitvec_lit [b]
  | VL_unit, _ -> Enum "unit"
  | VL_string str, _ ->
      ctx.use_string := true;
      String_lit (String.escaped str)
  | VL_real str, _ ->
      ctx.use_real := true;
      if str.[0] = '-' then Fn ("-", [Real_lit (String.sub str 1 (String.length str - 1))]) else Real_lit str
  | VL_enum str, _ -> Enum (Util.zencode_string str)
  | VL_ref reg_name, _ ->
      let id = mk_id reg_name in
      let rmap = CTMap.filter (fun ctyp regs -> List.exists (fun reg -> Id.compare reg id = 0) regs) ctx.register_map in
      assert (CTMap.cardinal rmap = 1);
      begin
        match CTMap.min_binding_opt rmap with
        | Some (ctyp, regs) -> begin
            match Util.list_index (fun reg -> Id.compare reg id = 0) regs with
            | Some i -> bvint (required_width (Big_int.of_int (List.length regs))) (Big_int.of_int i)
            | None -> assert false
          end
        | _ -> assert false
      end
  | _ -> failwith ("Cannot translate literal to SMT: " ^ string_of_value vl ^ " : " ^ string_of_ctyp ctyp)

let rec smt_cval ctx cval =
  match cval_ctyp cval with
  | CT_constant n -> bvint (required_width n) n
  | _ -> (
      match cval with
      | V_lit (vl, ctyp) -> smt_value ctx vl ctyp
      | V_id (((Name (id, _) | Global (id, _)) as ssa_id), _) -> begin
          match Type_check.Env.lookup_id id ctx.tc_env with
          | Enum _ -> Enum (zencode_id id)
          | _ when Bindings.mem id ctx.shared -> Shared (zencode_id id)
          | _ -> Var (zencode_name ssa_id)
        end
      | V_id (ssa_id, _) -> Var (zencode_name ssa_id)
      | V_call (Neq, [cval1; cval2]) -> Fn ("not", [Fn ("=", [smt_cval ctx cval1; smt_cval ctx cval2])])
      | V_call (Bvor, [cval1; cval2]) -> Fn ("bvor", [smt_cval ctx cval1; smt_cval ctx cval2])
      | V_call (Eq, [cval1; cval2]) -> Fn ("=", [smt_cval ctx cval1; smt_cval ctx cval2])
      | V_call (Bnot, [cval]) -> Fn ("not", [smt_cval ctx cval])
      | V_call (Band, cvals) -> smt_conj (List.map (smt_cval ctx) cvals)
      | V_call (Bor, cvals) -> smt_disj (List.map (smt_cval ctx) cvals)
      | V_call (Igt, [cval1; cval2]) -> Fn ("bvsgt", [smt_cval ctx cval1; smt_cval ctx cval2])
      | V_call (Iadd, [cval1; cval2]) -> Fn ("bvadd", [smt_cval ctx cval1; smt_cval ctx cval2])
      | V_ctor_kind (union, ctor, _) -> Fn ("not", [Tester (zencode_uid ctor, smt_cval ctx union)])
      | V_ctor_unwrap (union, ctor, _) -> Fn ("un" ^ zencode_uid ctor, [smt_cval ctx union])
      | V_field (record, field) -> begin
          match cval_ctyp record with
          | CT_struct (struct_id, _) -> Field (zencode_upper_id struct_id ^ "_" ^ zencode_id field, smt_cval ctx record)
          | _ -> failwith "Field for non-struct type"
        end
      | V_struct (fields, ctyp) -> begin
          match ctyp with
          | CT_struct (struct_id, field_ctyps) ->
              let set_field (field, cval) =
                match Util.assoc_compare_opt Id.compare field field_ctyps with
                | None -> failwith "Field type not found"
                | Some ctyp ->
                    ( zencode_upper_id struct_id ^ "_" ^ zencode_id field,
                      smt_conversion ctx (cval_ctyp cval) ctyp (smt_cval ctx cval)
                    )
              in
              Struct (zencode_upper_id struct_id, List.map set_field fields)
          | _ -> failwith "Struct does not have struct type"
        end
      | V_tuple_member (frag, len, n) ->
          ctx.tuple_sizes := IntSet.add len !(ctx.tuple_sizes);
          Fn (Printf.sprintf "tup_%d_%d" len n, [smt_cval ctx frag])
      | cval -> failwith ("Unrecognised cval " ^ string_of_cval cval)
    )

(**************************************************************************)
(* 1. Generating SMT for Sail builtins                                    *)
(**************************************************************************)

let builtin_type_error ctx fn cvals =
  let args = Util.string_of_list ", " (fun cval -> string_of_ctyp (cval_ctyp cval)) cvals in
  function
  | Some ret_ctyp ->
      let message = Printf.sprintf "%s : (%s) -> %s" fn args (string_of_ctyp ret_ctyp) in
      raise (Reporting.err_todo ctx.pragma_l message)
  | None -> raise (Reporting.err_todo ctx.pragma_l (Printf.sprintf "%s : (%s)" fn args))

(* ***** Basic comparisons: lib/flow.sail ***** *)

let builtin_int_comparison fn big_int_fn ctx v1 v2 =
  match (cval_ctyp v1, cval_ctyp v2) with
  | CT_lint, CT_lint -> Fn (fn, [smt_cval ctx v1; smt_cval ctx v2])
  | CT_fint sz1, CT_fint sz2 ->
      if sz1 == sz2 then Fn (fn, [smt_cval ctx v1; smt_cval ctx v2])
      else if sz1 > sz2 then Fn (fn, [smt_cval ctx v1; SignExtend (sz1 - sz2, smt_cval ctx v2)])
      else Fn (fn, [SignExtend (sz2 - sz1, smt_cval ctx v1); smt_cval ctx v2])
  | CT_constant c, CT_fint sz -> Fn (fn, [bvint sz c; smt_cval ctx v2])
  | CT_constant c, CT_lint -> Fn (fn, [bvint ctx.lint_size c; smt_cval ctx v2])
  | CT_fint sz, CT_constant c -> Fn (fn, [smt_cval ctx v1; bvint sz c])
  | CT_fint sz, CT_lint when sz < ctx.lint_size ->
      Fn (fn, [SignExtend (ctx.lint_size - sz, smt_cval ctx v1); smt_cval ctx v2])
  | CT_lint, CT_fint sz when sz < ctx.lint_size ->
      Fn (fn, [smt_cval ctx v1; SignExtend (ctx.lint_size - sz, smt_cval ctx v2)])
  | CT_lint, CT_constant c -> Fn (fn, [smt_cval ctx v1; bvint ctx.lint_size c])
  | CT_constant c1, CT_constant c2 -> Bool_lit (big_int_fn c1 c2)
  | _, _ -> builtin_type_error ctx fn [v1; v2] None

let builtin_eq_int = builtin_int_comparison "=" Big_int.equal

let builtin_lt = builtin_int_comparison "bvslt" Big_int.less
let builtin_lteq = builtin_int_comparison "bvsle" Big_int.less_equal
let builtin_gt = builtin_int_comparison "bvsgt" Big_int.greater
let builtin_gteq = builtin_int_comparison "bvsge" Big_int.greater_equal

(* ***** Arithmetic operations: lib/arith.sail ***** *)

let int_size ctx = function
  | CT_constant n -> required_width n
  | CT_fint sz -> sz
  | CT_lint -> ctx.lint_size
  | _ -> Reporting.unreachable ctx.pragma_l __POS__ "Argument to int_size must be an integer type"

let builtin_arith fn big_int_fn padding ctx v1 v2 ret_ctyp =
  (* To detect arithmetic overflow we can expand the input bitvectors
     to some size determined by a padding function, then check we
     don't lose precision when going back after performing the
     operation. *)
  let padding = if !opt_ignore_overflow then fun x -> x else padding in
  match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
  | _, _, CT_constant c -> bvint (required_width c) c
  | CT_constant c1, CT_constant c2, _ -> bvint (int_size ctx ret_ctyp) (big_int_fn c1 c2)
  | ctyp1, ctyp2, _ ->
      let ret_sz = int_size ctx ret_ctyp in
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      force_size ctx ret_sz (padding ret_sz)
        (Fn
           ( fn,
             [
               force_size ctx (padding ret_sz) (int_size ctx ctyp1) smt1;
               force_size ctx (padding ret_sz) (int_size ctx ctyp2) smt2;
             ]
           )
        )

let builtin_add_int = builtin_arith "bvadd" Big_int.add (fun x -> x + 1)
let builtin_sub_int = builtin_arith "bvsub" Big_int.sub (fun x -> x + 1)
let builtin_mult_int = builtin_arith "bvmul" Big_int.mul (fun x -> x * 2)

let builtin_sub_nat ctx v1 v2 ret_ctyp =
  let result = builtin_arith "bvsub" Big_int.sub (fun x -> x + 1) ctx v1 v2 ret_ctyp in
  Ite
    ( Fn ("bvslt", [result; bvint (int_size ctx ret_ctyp) Big_int.zero]),
      bvint (int_size ctx ret_ctyp) Big_int.zero,
      result
    )

let builtin_negate_int ctx v ret_ctyp =
  match (cval_ctyp v, ret_ctyp) with
  | _, CT_constant c -> bvint (required_width c) c
  | CT_constant c, _ -> bvint (int_size ctx ret_ctyp) (Big_int.negate c)
  | ctyp, _ ->
      let open Sail2_values in
      let smt = force_size ctx (int_size ctx ret_ctyp) (int_size ctx ctyp) (smt_cval ctx v) in
      overflow_check ctx (Fn ("=", [smt; Bitvec_lit (B1 :: List.init (int_size ctx ret_ctyp - 1) (fun _ -> B0))]));
      Fn ("bvneg", [smt])

let builtin_shift_int fn big_int_fn ctx v1 v2 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
  | _, _, CT_constant c -> bvint (required_width c) c
  | CT_constant c1, CT_constant c2, _ -> bvint (int_size ctx ret_ctyp) (big_int_fn c1 (Big_int.to_int c2))
  | ctyp, CT_constant c, _ ->
      let n = int_size ctx ctyp in
      force_size ctx (int_size ctx ret_ctyp) n (Fn (fn, [smt_cval ctx v1; bvint n c]))
  | CT_constant c, ctyp, _ ->
      let n = int_size ctx ctyp in
      force_size ctx (int_size ctx ret_ctyp) n (Fn (fn, [bvint n c; smt_cval ctx v2]))
  | ctyp1, ctyp2, _ ->
      let ret_sz = int_size ctx ret_ctyp in
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      Fn (fn, [force_size ctx ret_sz (int_size ctx ctyp1) smt1; force_size ctx ret_sz (int_size ctx ctyp2) smt2])

let builtin_shl_int = builtin_shift_int "bvshl" Big_int.shift_left
let builtin_shr_int = builtin_shift_int "bvashr" Big_int.shift_right

let builtin_abs_int ctx v ret_ctyp =
  match (cval_ctyp v, ret_ctyp) with
  | _, CT_constant c -> bvint (required_width c) c
  | CT_constant c, _ -> bvint (int_size ctx ret_ctyp) (Big_int.abs c)
  | ctyp, _ ->
      let sz = int_size ctx ctyp in
      let smt = smt_cval ctx v in
      Ite
        ( Fn ("=", [Extract (sz - 1, sz - 1, smt); Bitvec_lit [Sail2_values.B1]]),
          force_size ctx (int_size ctx ret_ctyp) sz (Fn ("bvneg", [smt])),
          force_size ctx (int_size ctx ret_ctyp) sz smt
        )

let builtin_pow2 ctx v ret_ctyp =
  match (cval_ctyp v, ret_ctyp) with
  | CT_constant n, _ when Big_int.greater_equal n Big_int.zero ->
      bvint (int_size ctx ret_ctyp) (Big_int.pow_int_positive 2 (Big_int.to_int n))
  | _ -> builtin_type_error ctx "pow2" [v] (Some ret_ctyp)

let builtin_max_int ctx v1 v2 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2) with
  | CT_constant n, CT_constant m -> bvint (int_size ctx ret_ctyp) (max n m)
  | ctyp1, ctyp2 ->
      let ret_sz = int_size ctx ret_ctyp in
      let smt1 = force_size ctx ret_sz (int_size ctx ctyp1) (smt_cval ctx v1) in
      let smt2 = force_size ctx ret_sz (int_size ctx ctyp2) (smt_cval ctx v2) in
      Ite (Fn ("bvslt", [smt1; smt2]), smt2, smt1)

let builtin_min_int ctx v1 v2 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2) with
  | CT_constant n, CT_constant m -> bvint (int_size ctx ret_ctyp) (min n m)
  | ctyp1, ctyp2 ->
      let ret_sz = int_size ctx ret_ctyp in
      let smt1 = force_size ctx ret_sz (int_size ctx ctyp1) (smt_cval ctx v1) in
      let smt2 = force_size ctx ret_sz (int_size ctx ctyp2) (smt_cval ctx v2) in
      Ite (Fn ("bvslt", [smt1; smt2]), smt1, smt2)

let builtin_min_int ctx v1 v2 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2) with
  | CT_constant n, CT_constant m -> bvint (int_size ctx ret_ctyp) (min n m)
  | ctyp1, ctyp2 ->
      let ret_sz = int_size ctx ret_ctyp in
      let smt1 = force_size ctx ret_sz (int_size ctx ctyp1) (smt_cval ctx v1) in
      let smt2 = force_size ctx ret_sz (int_size ctx ctyp2) (smt_cval ctx v2) in
      Ite (Fn ("bvslt", [smt1; smt2]), smt1, smt2)

let builtin_tdiv_int = builtin_arith "bvudiv" Sail2_values.tdiv_int (fun x -> x)

let builtin_tmod_int = builtin_arith "bvurem" Sail2_values.tmod_int (fun x -> x)

let bvmask ctx len =
  let all_ones = bvones (lbits_size ctx) in
  let shift = Fn ("concat", [bvzero (lbits_size ctx - ctx.lbits_index); len]) in
  bvnot (bvshl all_ones shift)

let fbits_mask ctx n len = bvnot (bvshl (bvones n) len)

let builtin_eq_bits ctx v1 v2 =
  match (cval_ctyp v1, cval_ctyp v2) with
  | CT_fbits n, CT_fbits m ->
      let o = max n m in
      let smt1 = unsigned_size ctx o n (smt_cval ctx v1) in
      let smt2 = unsigned_size ctx o n (smt_cval ctx v2) in
      Fn ("=", [smt1; smt2])
  | CT_lbits, CT_lbits ->
      let len1 = Fn ("len", [smt_cval ctx v1]) in
      let contents1 = Fn ("contents", [smt_cval ctx v1]) in
      let len2 = Fn ("len", [smt_cval ctx v2]) in
      let contents2 = Fn ("contents", [smt_cval ctx v2]) in
      Fn
        ( "and",
          [
            Fn ("=", [len1; len2]);
            Fn ("=", [Fn ("bvand", [bvmask ctx len1; contents1]); Fn ("bvand", [bvmask ctx len2; contents2])]);
          ]
        )
  | CT_lbits, CT_fbits n ->
      let smt1 = unsigned_size ctx n (lbits_size ctx) (Fn ("contents", [smt_cval ctx v1])) in
      Fn ("=", [smt1; smt_cval ctx v2])
  | CT_fbits n, CT_lbits ->
      let smt2 = unsigned_size ctx n (lbits_size ctx) (Fn ("contents", [smt_cval ctx v2])) in
      Fn ("=", [smt_cval ctx v1; smt2])
  | _ -> builtin_type_error ctx "eq_bits" [v1; v2] None

let builtin_zeros ctx v ret_ctyp =
  match (cval_ctyp v, ret_ctyp) with
  | _, CT_fbits n -> bvzero n
  | CT_constant c, CT_lbits -> Fn ("Bits", [bvint ctx.lbits_index c; bvzero (lbits_size ctx)])
  | ctyp, CT_lbits when int_size ctx ctyp >= ctx.lbits_index ->
      Fn ("Bits", [extract (ctx.lbits_index - 1) 0 (smt_cval ctx v); bvzero (lbits_size ctx)])
  | _ -> builtin_type_error ctx "zeros" [v] (Some ret_ctyp)

let builtin_ones ctx cval = function
  | CT_fbits n -> bvones n
  | CT_lbits ->
      let len = extract (ctx.lbits_index - 1) 0 (smt_cval ctx cval) in
      Fn ("Bits", [len; Fn ("bvand", [bvmask ctx len; bvones (lbits_size ctx)])])
  | ret_ctyp -> builtin_type_error ctx "ones" [cval] (Some ret_ctyp)

(* [bvzeint ctx esz cval] (BitVector Zero Extend INTeger), takes a cval
   which must be an integer type (either CT_fint, or CT_lint), and
   produces a bitvector which is either zero extended or truncated to
   exactly esz bits. *)
let bvzeint ctx esz cval =
  let sz = int_size ctx (cval_ctyp cval) in
  match cval with
  | V_lit (VL_int n, _) -> bvint esz n
  | _ ->
      let smt = smt_cval ctx cval in
      if esz = sz then smt else if esz > sz then Fn ("concat", [bvzero (esz - sz); smt]) else Extract (esz - 1, 0, smt)

let builtin_zero_extend ctx vbits vlen ret_ctyp =
  match (cval_ctyp vbits, ret_ctyp) with
  | CT_fbits n, CT_fbits m when n = m -> smt_cval ctx vbits
  | CT_fbits n, CT_fbits m ->
      let bv = smt_cval ctx vbits in
      Fn ("concat", [bvzero (m - n); bv])
  | CT_lbits, CT_fbits m ->
      assert (lbits_size ctx >= m);
      Extract (m - 1, 0, Fn ("contents", [smt_cval ctx vbits]))
  | CT_fbits n, CT_lbits ->
      assert (lbits_size ctx >= n);
      let vbits =
        if lbits_size ctx = n then smt_cval ctx vbits
        else if lbits_size ctx > n then Fn ("concat", [bvzero (lbits_size ctx - n); smt_cval ctx vbits])
        else assert false
      in
      Fn ("Bits", [bvzeint ctx ctx.lbits_index vlen; vbits])
  | _ -> builtin_type_error ctx "zero_extend" [vbits; vlen] (Some ret_ctyp)

let builtin_sign_extend ctx vbits vlen ret_ctyp =
  match (cval_ctyp vbits, ret_ctyp) with
  | CT_fbits n, CT_fbits m when n = m -> smt_cval ctx vbits
  | CT_fbits n, CT_fbits m ->
      let bv = smt_cval ctx vbits in
      let top_bit_one = Fn ("=", [Extract (n - 1, n - 1, bv); Bitvec_lit [Sail2_values.B1]]) in
      Ite (top_bit_one, Fn ("concat", [bvones (m - n); bv]), Fn ("concat", [bvzero (m - n); bv]))
  | _ -> builtin_type_error ctx "sign_extend" [vbits; vlen] (Some ret_ctyp)

let builtin_shift shiftop ctx vbits vshift ret_ctyp =
  match cval_ctyp vbits with
  | CT_fbits n ->
      let bv = smt_cval ctx vbits in
      let len = bvzeint ctx n vshift in
      Fn (shiftop, [bv; len])
  | CT_lbits ->
      let bv = smt_cval ctx vbits in
      let shift = bvzeint ctx (lbits_size ctx) vshift in
      Fn ("Bits", [Fn ("len", [bv]); Fn (shiftop, [Fn ("contents", [bv]); shift])])
  | _ -> builtin_type_error ctx shiftop [vbits; vshift] (Some ret_ctyp)

let builtin_not_bits ctx v ret_ctyp =
  match (cval_ctyp v, ret_ctyp) with
  | CT_lbits, CT_fbits n -> bvnot (Extract (n - 1, 0, Fn ("contents", [smt_cval ctx v])))
  | CT_lbits, CT_lbits ->
      let bv = smt_cval ctx v in
      let len = Fn ("len", [bv]) in
      Fn ("Bits", [len; Fn ("bvand", [bvmask ctx len; bvnot (Fn ("contents", [bv]))])])
  | CT_fbits n, CT_fbits m when n = m -> bvnot (smt_cval ctx v)
  | _, _ -> builtin_type_error ctx "not_bits" [v] (Some ret_ctyp)

let builtin_bitwise fn ctx v1 v2 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
  | CT_fbits n, CT_fbits m, CT_fbits o ->
      assert (n = m && m = o);
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      Fn (fn, [smt1; smt2])
  | CT_lbits, CT_lbits, CT_lbits ->
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      Fn ("Bits", [Fn ("len", [smt1]); Fn (fn, [Fn ("contents", [smt1]); Fn ("contents", [smt2])])])
  | _ -> builtin_type_error ctx fn [v1; v2] (Some ret_ctyp)

let builtin_and_bits = builtin_bitwise "bvand"
let builtin_or_bits = builtin_bitwise "bvor"
let builtin_xor_bits = builtin_bitwise "bvxor"

let builtin_append ctx v1 v2 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
  | CT_fbits n, CT_fbits m, CT_fbits o ->
      assert (n + m = o);
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      Fn ("concat", [smt1; smt2])
  | CT_fbits n, CT_lbits, CT_lbits ->
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      let x = Fn ("concat", [bvzero (lbits_size ctx - n); smt1]) in
      let shift = Fn ("concat", [bvzero (lbits_size ctx - ctx.lbits_index); Fn ("len", [smt2])]) in
      Fn
        ( "Bits",
          [
            bvadd (bvint ctx.lbits_index (Big_int.of_int n)) (Fn ("len", [smt2]));
            bvor (bvshl x shift) (Fn ("contents", [smt2]));
          ]
        )
  | CT_lbits, CT_fbits n, CT_fbits m ->
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      Extract (m - 1, 0, Fn ("concat", [Fn ("contents", [smt1]); smt2]))
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
  | CT_lbits, CT_lbits, CT_lbits ->
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      let x = Fn ("contents", [smt1]) in
      let shift = Fn ("concat", [bvzero (lbits_size ctx - ctx.lbits_index); Fn ("len", [smt2])]) in
      Fn ("Bits", [bvadd (Fn ("len", [smt1])) (Fn ("len", [smt2])); bvor (bvshl x shift) (Fn ("contents", [smt2]))])
  | CT_lbits, CT_lbits, CT_fbits n ->
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      let x = Fn ("contents", [smt1]) in
      let shift = Fn ("concat", [bvzero (lbits_size ctx - ctx.lbits_index); Fn ("len", [smt2])]) in
      unsigned_size ctx n (lbits_size ctx) (bvor (bvshl x shift) (Fn ("contents", [smt2])))
  | _ -> builtin_type_error ctx "append" [v1; v2] (Some ret_ctyp)

let builtin_length ctx v ret_ctyp =
  match (cval_ctyp v, ret_ctyp) with
  | CT_fbits n, (CT_constant _ | CT_fint _ | CT_lint) -> bvint (int_size ctx ret_ctyp) (Big_int.of_int n)
  | CT_lbits, (CT_constant _ | CT_fint _ | CT_lint) ->
      let sz = ctx.lbits_index in
      let m = int_size ctx ret_ctyp in
      let len = Fn ("len", [smt_cval ctx v]) in
      if m = sz then len else if m > sz then Fn ("concat", [bvzero (m - sz); len]) else Extract (m - 1, 0, len)
  | _, _ -> builtin_type_error ctx "length" [v] (Some ret_ctyp)

let builtin_vector_subrange ctx vec i j ret_ctyp =
  match (cval_ctyp vec, cval_ctyp i, cval_ctyp j, ret_ctyp) with
  | CT_fbits n, CT_constant i, CT_constant j, CT_fbits _ ->
      Extract (Big_int.to_int i, Big_int.to_int j, smt_cval ctx vec)
  | CT_lbits, CT_constant i, CT_constant j, CT_fbits _ ->
      Extract (Big_int.to_int i, Big_int.to_int j, Fn ("contents", [smt_cval ctx vec]))
  | CT_fbits n, i_ctyp, CT_constant j, CT_lbits when Big_int.equal j Big_int.zero ->
      let i' = force_size ~checked:false ctx ctx.lbits_index (int_size ctx i_ctyp) (smt_cval ctx i) in
      let len = bvadd i' (bvint ctx.lbits_index (Big_int.of_int 1)) in
      Fn ("Bits", [len; Fn ("bvand", [bvmask ctx len; unsigned_size ctx (lbits_size ctx) n (smt_cval ctx vec)])])
  | CT_fbits n, i_ctyp, j_ctyp, ret_ctyp ->
      let i' = force_size ctx n (int_size ctx i_ctyp) (smt_cval ctx i) in
      let j' = force_size ctx n (int_size ctx j_ctyp) (smt_cval ctx j) in
      let len = bvadd (bvadd i' (bvneg j')) (bvint n (Big_int.of_int 1)) in
      let vec' = bvand (bvlshr (smt_cval ctx vec) j') (fbits_mask ctx n len) in
      smt_conversion ctx (CT_fbits n) ret_ctyp vec'
  | _ -> builtin_type_error ctx "vector_subrange" [vec; i; j] (Some ret_ctyp)

let builtin_vector_access ctx vec i ret_ctyp =
  match (cval_ctyp vec, cval_ctyp i, ret_ctyp) with
  | CT_fbits n, CT_constant i, CT_bit -> Extract (Big_int.to_int i, Big_int.to_int i, smt_cval ctx vec)
  | CT_lbits, CT_constant i, CT_bit -> Extract (Big_int.to_int i, Big_int.to_int i, Fn ("contents", [smt_cval ctx vec]))
  | CT_lbits, i_ctyp, CT_bit ->
      let shift = force_size ~checked:false ctx (lbits_size ctx) (int_size ctx i_ctyp) (smt_cval ctx i) in
      Extract (0, 0, Fn ("bvlshr", [Fn ("contents", [smt_cval ctx vec]); shift]))
  | CT_vector _, CT_constant i, _ -> Fn ("select", [smt_cval ctx vec; bvint !vector_index i])
  | CT_vector _, index_ctyp, _ ->
      Fn ("select", [smt_cval ctx vec; force_size ctx !vector_index (int_size ctx index_ctyp) (smt_cval ctx i)])
  | _ -> builtin_type_error ctx "vector_access" [vec; i] (Some ret_ctyp)

let builtin_vector_update ctx vec i x ret_ctyp =
  match (cval_ctyp vec, cval_ctyp i, cval_ctyp x, ret_ctyp) with
  | CT_fbits n, CT_constant i, CT_bit, CT_fbits m when n - 1 > Big_int.to_int i && Big_int.to_int i > 0 ->
      assert (n = m);
      let top = Extract (n - 1, Big_int.to_int i + 1, smt_cval ctx vec) in
      let bot = Extract (Big_int.to_int i - 1, 0, smt_cval ctx vec) in
      Fn ("concat", [top; Fn ("concat", [smt_cval ctx x; bot])])
  | CT_fbits n, CT_constant i, CT_bit, CT_fbits m when n - 1 = Big_int.to_int i && Big_int.to_int i > 0 ->
      let bot = Extract (Big_int.to_int i - 1, 0, smt_cval ctx vec) in
      Fn ("concat", [smt_cval ctx x; bot])
  | CT_fbits n, CT_constant i, CT_bit, CT_fbits m when n - 1 > Big_int.to_int i && Big_int.to_int i = 0 ->
      let top = Extract (n - 1, 1, smt_cval ctx vec) in
      Fn ("concat", [top; smt_cval ctx x])
  | CT_fbits n, CT_constant i, CT_bit, CT_fbits m when n - 1 = 0 && Big_int.to_int i = 0 -> smt_cval ctx x
  | CT_vector _, CT_constant i, ctyp, CT_vector _ ->
      Fn ("store", [smt_cval ctx vec; bvint !vector_index i; smt_cval ctx x])
  | CT_vector _, index_ctyp, _, CT_vector _ ->
      Fn
        ( "store",
          [smt_cval ctx vec; force_size ctx !vector_index (int_size ctx index_ctyp) (smt_cval ctx i); smt_cval ctx x]
        )
  | _ -> builtin_type_error ctx "vector_update" [vec; i; x] (Some ret_ctyp)

let builtin_vector_update_subrange ctx vec i j x ret_ctyp =
  match (cval_ctyp vec, cval_ctyp i, cval_ctyp j, cval_ctyp x, ret_ctyp) with
  | CT_fbits n, CT_constant i, CT_constant j, CT_fbits sz, CT_fbits m
    when n - 1 > Big_int.to_int i && Big_int.to_int j > 0 ->
      assert (n = m);
      let top = Extract (n - 1, Big_int.to_int i + 1, smt_cval ctx vec) in
      let bot = Extract (Big_int.to_int j - 1, 0, smt_cval ctx vec) in
      Fn ("concat", [top; Fn ("concat", [smt_cval ctx x; bot])])
  | CT_fbits n, CT_constant i, CT_constant j, CT_fbits sz, CT_fbits m
    when n - 1 = Big_int.to_int i && Big_int.to_int j > 0 ->
      assert (n = m);
      let bot = Extract (Big_int.to_int j - 1, 0, smt_cval ctx vec) in
      Fn ("concat", [smt_cval ctx x; bot])
  | CT_fbits n, CT_constant i, CT_constant j, CT_fbits sz, CT_fbits m
    when n - 1 > Big_int.to_int i && Big_int.to_int j = 0 ->
      assert (n = m);
      let top = Extract (n - 1, Big_int.to_int i + 1, smt_cval ctx vec) in
      Fn ("concat", [top; smt_cval ctx x])
  | CT_fbits n, CT_constant i, CT_constant j, CT_fbits sz, CT_fbits m
    when n - 1 = Big_int.to_int i && Big_int.to_int j = 0 ->
      smt_cval ctx x
  | CT_fbits n, ctyp_i, ctyp_j, ctyp_x, CT_fbits m ->
      assert (n = m);
      let i' = force_size ctx n (int_size ctx ctyp_i) (smt_cval ctx i) in
      let j' = force_size ctx n (int_size ctx ctyp_j) (smt_cval ctx j) in
      let x' = smt_conversion ctx ctyp_x (CT_fbits n) (smt_cval ctx x) in
      let len = bvadd (bvadd i' (bvneg j')) (bvint n (Big_int.of_int 1)) in
      let mask = bvshl (fbits_mask ctx n len) j' in
      bvor (bvand (smt_cval ctx vec) (bvnot mask)) (bvand (bvshl x' j') mask)
  | _ -> builtin_type_error ctx "vector_update_subrange" [vec; i; j; x] (Some ret_ctyp)

let builtin_unsigned ctx v ret_ctyp =
  match (cval_ctyp v, ret_ctyp) with
  | CT_fbits n, CT_fint m when m > n ->
      let smt = smt_cval ctx v in
      Fn ("concat", [bvzero (m - n); smt])
  | CT_fbits n, CT_lint ->
      if n >= ctx.lint_size then failwith "Overflow detected"
      else (
        let smt = smt_cval ctx v in
        Fn ("concat", [bvzero (ctx.lint_size - n); smt])
      )
  | CT_lbits, CT_lint -> Extract (ctx.lint_size - 1, 0, Fn ("contents", [smt_cval ctx v]))
  | CT_lbits, CT_fint m ->
      let smt = Fn ("contents", [smt_cval ctx v]) in
      force_size ctx m (lbits_size ctx) smt
  | ctyp, _ -> builtin_type_error ctx "unsigned" [v] (Some ret_ctyp)

let builtin_signed ctx v ret_ctyp =
  match (cval_ctyp v, ret_ctyp) with
  | CT_fbits n, CT_fint m when m >= n -> SignExtend (m - n, smt_cval ctx v)
  | CT_fbits n, CT_lint -> SignExtend (ctx.lint_size - n, smt_cval ctx v)
  | CT_lbits, CT_lint -> Extract (ctx.lint_size - 1, 0, Fn ("contents", [smt_cval ctx v]))
  | ctyp, _ -> builtin_type_error ctx "signed" [v] (Some ret_ctyp)

let builtin_add_bits ctx v1 v2 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
  | CT_fbits n, CT_fbits m, CT_fbits o ->
      assert (n = m && m = o);
      Fn ("bvadd", [smt_cval ctx v1; smt_cval ctx v2])
  | CT_lbits, CT_lbits, CT_lbits ->
      let smt1 = smt_cval ctx v1 in
      let smt2 = smt_cval ctx v2 in
      Fn ("Bits", [Fn ("len", [smt1]); Fn ("bvadd", [Fn ("contents", [smt1]); Fn ("contents", [smt2])])])
  | _ -> builtin_type_error ctx "add_bits" [v1; v2] (Some ret_ctyp)

let builtin_sub_bits ctx v1 v2 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
  | CT_fbits n, CT_fbits m, CT_fbits o ->
      assert (n = m && m = o);
      Fn ("bvadd", [smt_cval ctx v1; Fn ("bvneg", [smt_cval ctx v2])])
  | _ -> failwith "Cannot compile sub_bits"

let builtin_add_bits_int ctx v1 v2 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
  | CT_fbits n, CT_constant c, CT_fbits o when n = o -> Fn ("bvadd", [smt_cval ctx v1; bvint o c])
  | CT_fbits n, CT_fint m, CT_fbits o when n = o -> Fn ("bvadd", [smt_cval ctx v1; force_size ctx o m (smt_cval ctx v2)])
  | CT_fbits n, CT_lint, CT_fbits o when n = o ->
      Fn ("bvadd", [smt_cval ctx v1; force_size ctx o ctx.lint_size (smt_cval ctx v2)])
  | CT_lbits, CT_fint n, CT_lbits when n < lbits_size ctx ->
      let smt1 = smt_cval ctx v1 in
      let smt2 = force_size ctx (lbits_size ctx) n (smt_cval ctx v2) in
      Fn ("Bits", [Fn ("len", [smt1]); Fn ("bvadd", [Fn ("contents", [smt1]); smt2])])
  | _ -> builtin_type_error ctx "add_bits_int" [v1; v2] (Some ret_ctyp)

let builtin_sub_bits_int ctx v1 v2 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
  | CT_fbits n, CT_constant c, CT_fbits o when n = o -> Fn ("bvadd", [smt_cval ctx v1; bvint o (Big_int.negate c)])
  | CT_fbits n, CT_fint m, CT_fbits o when n = o -> Fn ("bvsub", [smt_cval ctx v1; force_size ctx o m (smt_cval ctx v2)])
  | CT_fbits n, CT_lint, CT_fbits o when n = o ->
      Fn ("bvsub", [smt_cval ctx v1; force_size ctx o ctx.lint_size (smt_cval ctx v2)])
  | _ -> builtin_type_error ctx "sub_bits_int" [v1; v2] (Some ret_ctyp)

let builtin_replicate_bits ctx v1 v2 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
  | CT_fbits n, CT_constant c, CT_fbits m ->
      assert (n * Big_int.to_int c = m);
      let smt = smt_cval ctx v1 in
      Fn ("concat", List.init (Big_int.to_int c) (fun _ -> smt))
  | CT_fbits n, _, CT_fbits m ->
      let smt = smt_cval ctx v1 in
      let c = m / n in
      Fn ("concat", List.init c (fun _ -> smt))
  | CT_fbits n, v2_ctyp, CT_lbits ->
      let times = (lbits_size ctx / n) + 1 in
      let len = force_size ~checked:false ctx ctx.lbits_index (int_size ctx v2_ctyp) (smt_cval ctx v2) in
      let smt1 = smt_cval ctx v1 in
      let contents = Extract (lbits_size ctx - 1, 0, Fn ("concat", List.init times (fun _ -> smt1))) in
      Fn ("Bits", [len; Fn ("bvand", [bvmask ctx len; contents])])
  | _ -> builtin_type_error ctx "replicate_bits" [v1; v2] (Some ret_ctyp)

let builtin_sail_truncate ctx v1 v2 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
  | CT_fbits n, CT_constant c, CT_fbits m ->
      assert (Big_int.to_int c = m);
      Extract (Big_int.to_int c - 1, 0, smt_cval ctx v1)
  | CT_lbits, CT_constant c, CT_fbits m ->
      assert (Big_int.to_int c = m && m < lbits_size ctx);
      Extract (Big_int.to_int c - 1, 0, Fn ("contents", [smt_cval ctx v1]))
  | CT_fbits n, _, CT_lbits ->
      let smt1 = unsigned_size ctx (lbits_size ctx) n (smt_cval ctx v1) in
      let smt2 = bvzeint ctx ctx.lbits_index v2 in
      Fn ("Bits", [smt2; Fn ("bvand", [bvmask ctx smt2; smt1])])
  | _ -> builtin_type_error ctx "sail_truncate" [v1; v2] (Some ret_ctyp)

let builtin_sail_truncateLSB ctx v1 v2 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2, ret_ctyp) with
  | CT_fbits n, CT_constant c, CT_fbits m ->
      assert (Big_int.to_int c = m);
      Extract (n - 1, n - Big_int.to_int c, smt_cval ctx v1)
  | _ -> builtin_type_error ctx "sail_truncateLSB" [v1; v2] (Some ret_ctyp)

let builtin_slice ctx v1 v2 v3 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2, cval_ctyp v3, ret_ctyp) with
  | CT_lbits, CT_constant start, CT_constant len, CT_fbits _ ->
      let top = Big_int.pred (Big_int.add start len) in
      Extract (Big_int.to_int top, Big_int.to_int start, Fn ("contents", [smt_cval ctx v1]))
  | CT_fbits _, CT_constant start, CT_constant len, CT_fbits _ ->
      let top = Big_int.pred (Big_int.add start len) in
      Extract (Big_int.to_int top, Big_int.to_int start, smt_cval ctx v1)
  | CT_fbits _, CT_fint _, CT_constant len, CT_fbits _ ->
      Extract (Big_int.to_int (Big_int.pred len), 0, builtin_shift "bvlshr" ctx v1 v2 (cval_ctyp v1))
  | CT_fbits n, ctyp2, _, CT_lbits ->
      let smt1 = force_size ctx (lbits_size ctx) n (smt_cval ctx v1) in
      let smt2 = force_size ctx (lbits_size ctx) (int_size ctx ctyp2) (smt_cval ctx v2) in
      let smt3 = bvzeint ctx ctx.lbits_index v3 in
      Fn ("Bits", [smt3; Fn ("bvand", [Fn ("bvlshr", [smt1; smt2]); bvmask ctx smt3])])
  | _ -> builtin_type_error ctx "slice" [v1; v2; v3] (Some ret_ctyp)

let builtin_get_slice_int ctx v1 v2 v3 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2, cval_ctyp v3, ret_ctyp) with
  | CT_constant len, ctyp, CT_constant start, CT_fbits ret_sz ->
      let len = Big_int.to_int len in
      let start = Big_int.to_int start in
      let in_sz = int_size ctx ctyp in
      let smt = if in_sz < len + start then force_size ctx (len + start) in_sz (smt_cval ctx v2) else smt_cval ctx v2 in
      Extract (start + len - 1, start, smt)
  | CT_lint, CT_lint, CT_constant start, CT_lbits when Big_int.equal start Big_int.zero ->
      let len = Extract (ctx.lbits_index - 1, 0, smt_cval ctx v1) in
      let contents = unsigned_size ~checked:false ctx (lbits_size ctx) ctx.lint_size (smt_cval ctx v2) in
      Fn ("Bits", [len; Fn ("bvand", [bvmask ctx len; contents])])
  | CT_lint, ctyp2, ctyp3, ret_ctyp ->
      let len = Extract (ctx.lbits_index - 1, 0, smt_cval ctx v1) in
      let smt2 = force_size ctx (lbits_size ctx) (int_size ctx ctyp2) (smt_cval ctx v2) in
      let smt3 = force_size ctx (lbits_size ctx) (int_size ctx ctyp3) (smt_cval ctx v3) in
      let result = bvand (bvmask ctx len) (bvlshr smt2 smt3) in
      smt_conversion ctx CT_lint ret_ctyp result
  | _ -> builtin_type_error ctx "get_slice_int" [v1; v2; v3] (Some ret_ctyp)

let builtin_count_leading_zeros ctx v ret_ctyp =
  let ret_sz = int_size ctx ret_ctyp in
  let rec lzcnt sz smt =
    if sz == 1 then
      Ite
        ( Fn ("=", [Extract (0, 0, smt); Bitvec_lit [Sail2_values.B0]]),
          bvint ret_sz (Big_int.of_int 1),
          bvint ret_sz Big_int.zero
        )
    else (
      assert (sz land (sz - 1) = 0);
      let hsz = sz / 2 in
      Ite
        ( Fn ("=", [Extract (sz - 1, hsz, smt); bvzero hsz]),
          Fn ("bvadd", [bvint ret_sz (Big_int.of_int hsz); lzcnt hsz (Extract (hsz - 1, 0, smt))]),
          lzcnt hsz (Extract (sz - 1, hsz, smt))
        )
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
  | CT_fbits sz when sz land (sz - 1) = 0 -> lzcnt sz (smt_cval ctx v)
  | CT_fbits sz ->
      let padded_sz = smallest_greater_power_of_two sz in
      let padding = bvzero (padded_sz - sz) in
      Fn
        ( "bvsub",
          [lzcnt padded_sz (Fn ("concat", [padding; smt_cval ctx v])); bvint ret_sz (Big_int.of_int (padded_sz - sz))]
        )
  | CT_lbits ->
      let smt = smt_cval ctx v in
      Fn
        ( "bvsub",
          [
            lzcnt (lbits_size ctx) (Fn ("contents", [smt]));
            Fn
              ( "bvsub",
                [
                  bvint ret_sz (Big_int.of_int (lbits_size ctx));
                  Fn ("concat", [bvzero (ret_sz - ctx.lbits_index); Fn ("len", [smt])]);
                ]
              );
          ]
        )
  | _ -> builtin_type_error ctx "count_leading_zeros" [v] (Some ret_ctyp)

let builtin_set_slice_bits ctx v1 v2 v3 v4 v5 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2, cval_ctyp v3, cval_ctyp v4, cval_ctyp v5, ret_ctyp) with
  | CT_constant n', CT_constant m', CT_fbits n, CT_constant pos, CT_fbits m, CT_fbits n''
    when Big_int.to_int m' = m && Big_int.to_int n' = n && n'' = n && Big_int.less_equal (Big_int.add pos m') n' ->
      let pos = Big_int.to_int pos in
      if pos = 0 then (
        let mask = Fn ("concat", [bvones (n - m); bvzero m]) in
        let smt5 = Fn ("concat", [bvzero (n - m); smt_cval ctx v5]) in
        Fn ("bvor", [Fn ("bvand", [smt_cval ctx v3; mask]); smt5])
      )
      else if n - m - pos = 0 then (
        let mask = Fn ("concat", [bvzero m; bvones pos]) in
        let smt5 = Fn ("concat", [smt_cval ctx v5; bvzero pos]) in
        Fn ("bvor", [Fn ("bvand", [smt_cval ctx v3; mask]); smt5])
      )
      else (
        let mask = Fn ("concat", [bvones (n - m - pos); Fn ("concat", [bvzero m; bvones pos])]) in
        let smt5 = Fn ("concat", [bvzero (n - m - pos); Fn ("concat", [smt_cval ctx v5; bvzero pos])]) in
        Fn ("bvor", [Fn ("bvand", [smt_cval ctx v3; mask]); smt5])
      )
  (* set_slice_bits(len, slen, x, pos, y) =
       let mask = slice_mask(len, pos, slen) in
       (x AND NOT(mask)) OR ((unsigned_size(len, y) << pos) AND mask) *)
  | CT_constant n', _, CT_fbits n, _, CT_lbits, CT_fbits n'' when Big_int.to_int n' = n && n'' = n ->
      let pos = bvzeint ctx (lbits_size ctx) v4 in
      let slen = bvzeint ctx ctx.lbits_index v2 in
      let mask = Fn ("bvshl", [bvmask ctx slen; pos]) in
      let smt3 = unsigned_size ctx (lbits_size ctx) n (smt_cval ctx v3) in
      let smt3' = Fn ("bvand", [smt3; Fn ("bvnot", [mask])]) in
      let smt5 = Fn ("contents", [smt_cval ctx v5]) in
      let smt5' = Fn ("bvand", [Fn ("bvshl", [smt5; pos]); mask]) in
      Extract (n - 1, 0, Fn ("bvor", [smt3'; smt5']))
  | _ -> builtin_type_error ctx "set_slice" [v1; v2; v3; v4; v5] (Some ret_ctyp)

let builtin_compare_bits fn ctx v1 v2 ret_ctyp =
  match (cval_ctyp v1, cval_ctyp v2) with
  | CT_fbits n, CT_fbits m when n = m -> Fn (fn, [smt_cval ctx v1; smt_cval ctx v2])
  | _ -> builtin_type_error ctx fn [v1; v2] (Some ret_ctyp)

(* ***** String operations: lib/real.sail ***** *)

let builtin_decimal_string_of_bits ctx v =
  begin
    match cval_ctyp v with
    | CT_fbits n -> Fn ("int.to.str", [Fn ("bv2nat", [smt_cval ctx v])])
    | _ -> builtin_type_error ctx "decimal_string_of_bits" [v] None
  end

(* ***** Real number operations: lib/real.sail ***** *)

let builtin_sqrt_real ctx root v =
  ctx.use_real := true;
  let smt = smt_cval ctx v in
  [
    Declare_const (root, Real);
    Assert (Fn ("and", [Fn ("=", [smt; Fn ("*", [Var root; Var root])]); Fn (">=", [Var root; Real_lit "0.0"])]));
  ]

let smt_builtin ctx name args ret_ctyp =
  match (name, args, ret_ctyp) with
  | "eq_anything", [v1; v2], CT_bool -> Fn ("=", [smt_cval ctx v1; smt_cval ctx v2])
  (* lib/flow.sail *)
  | "eq_bit", [v1; v2], CT_bool -> Fn ("=", [smt_cval ctx v1; smt_cval ctx v2])
  | "eq_bool", [v1; v2], CT_bool -> Fn ("=", [smt_cval ctx v1; smt_cval ctx v2])
  | "eq_unit", [v1; v2], CT_bool -> Fn ("=", [smt_cval ctx v1; smt_cval ctx v2])
  | "eq_int", [v1; v2], CT_bool -> builtin_eq_int ctx v1 v2
  | "not", [v], _ -> Fn ("not", [smt_cval ctx v])
  | "lt", [v1; v2], _ -> builtin_lt ctx v1 v2
  | "lteq", [v1; v2], _ -> builtin_lteq ctx v1 v2
  | "gt", [v1; v2], _ -> builtin_gt ctx v1 v2
  | "gteq", [v1; v2], _ -> builtin_gteq ctx v1 v2
  (* lib/arith.sail *)
  | "add_int", [v1; v2], _ -> builtin_add_int ctx v1 v2 ret_ctyp
  | "sub_int", [v1; v2], _ -> builtin_sub_int ctx v1 v2 ret_ctyp
  | "sub_nat", [v1; v2], _ -> builtin_sub_nat ctx v1 v2 ret_ctyp
  | "mult_int", [v1; v2], _ -> builtin_mult_int ctx v1 v2 ret_ctyp
  | "neg_int", [v], _ -> builtin_negate_int ctx v ret_ctyp
  | "shl_int", [v1; v2], _ -> builtin_shl_int ctx v1 v2 ret_ctyp
  | "shr_int", [v1; v2], _ -> builtin_shr_int ctx v1 v2 ret_ctyp
  | "shl_mach_int", [v1; v2], _ -> builtin_shl_int ctx v1 v2 ret_ctyp
  | "shr_mach_int", [v1; v2], _ -> builtin_shr_int ctx v1 v2 ret_ctyp
  | "abs_int", [v], _ -> builtin_abs_int ctx v ret_ctyp
  | "pow2", [v], _ -> builtin_pow2 ctx v ret_ctyp
  | "max_int", [v1; v2], _ -> builtin_max_int ctx v1 v2 ret_ctyp
  | "min_int", [v1; v2], _ -> builtin_min_int ctx v1 v2 ret_ctyp
  | "ediv_int", [v1; v2], _ -> builtin_tdiv_int ctx v1 v2 ret_ctyp
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
  | "eq_bits", [v1; v2], CT_bool -> builtin_eq_bits ctx v1 v2
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
  | "arith_shiftr", [v1; v2], _ -> builtin_shift "bvashr" ctx v1 v2 ret_ctyp
  | "and_bits", [v1; v2], _ -> builtin_and_bits ctx v1 v2 ret_ctyp
  | "or_bits", [v1; v2], _ -> builtin_or_bits ctx v1 v2 ret_ctyp
  | "xor_bits", [v1; v2], _ -> builtin_xor_bits ctx v1 v2 ret_ctyp
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
  | "vector_update_subrange", [v1; v2; v3; v4], ret_ctyp -> builtin_vector_update_subrange ctx v1 v2 v3 v4 ret_ctyp
  | "sail_unsigned", [v], ret_ctyp -> builtin_unsigned ctx v ret_ctyp
  | "sail_signed", [v], ret_ctyp -> builtin_signed ctx v ret_ctyp
  | "replicate_bits", [v1; v2], ret_ctyp -> builtin_replicate_bits ctx v1 v2 ret_ctyp
  | "count_leading_zeros", [v], ret_ctyp -> builtin_count_leading_zeros ctx v ret_ctyp
  | "slice", [v1; v2; v3], ret_ctyp -> builtin_slice ctx v1 v2 v3 ret_ctyp
  | "get_slice_int", [v1; v2; v3], ret_ctyp -> builtin_get_slice_int ctx v1 v2 v3 ret_ctyp
  | "set_slice", [v1; v2; v3; v4; v5], ret_ctyp -> builtin_set_slice_bits ctx v1 v2 v3 v4 v5 ret_ctyp
  (* string builtins *)
  | "concat_str", [v1; v2], CT_string ->
      ctx.use_string := true;
      Fn ("str.++", [smt_cval ctx v1; smt_cval ctx v2])
  | "eq_string", [v1; v2], CT_bool ->
      ctx.use_string := true;
      Fn ("=", [smt_cval ctx v1; smt_cval ctx v2])
  | "decimal_string_of_bits", [v], CT_string ->
      ctx.use_string := true;
      builtin_decimal_string_of_bits ctx v
  (* lib/real.sail *)
  (* Note that sqrt_real is special and is handled by smt_instr. *)
  | "eq_real", [v1; v2], CT_bool ->
      ctx.use_real := true;
      Fn ("=", [smt_cval ctx v1; smt_cval ctx v2])
  | "neg_real", [v], CT_real ->
      ctx.use_real := true;
      Fn ("-", [smt_cval ctx v])
  | "add_real", [v1; v2], CT_real ->
      ctx.use_real := true;
      Fn ("+", [smt_cval ctx v1; smt_cval ctx v2])
  | "sub_real", [v1; v2], CT_real ->
      ctx.use_real := true;
      Fn ("-", [smt_cval ctx v1; smt_cval ctx v2])
  | "mult_real", [v1; v2], CT_real ->
      ctx.use_real := true;
      Fn ("*", [smt_cval ctx v1; smt_cval ctx v2])
  | "div_real", [v1; v2], CT_real ->
      ctx.use_real := true;
      Fn ("/", [smt_cval ctx v1; smt_cval ctx v2])
  | "lt_real", [v1; v2], CT_bool ->
      ctx.use_real := true;
      Fn ("<", [smt_cval ctx v1; smt_cval ctx v2])
  | "gt_real", [v1; v2], CT_bool ->
      ctx.use_real := true;
      Fn (">", [smt_cval ctx v1; smt_cval ctx v2])
  | "lteq_real", [v1; v2], CT_bool ->
      ctx.use_real := true;
      Fn ("<=", [smt_cval ctx v1; smt_cval ctx v2])
  | "gteq_real", [v1; v2], CT_bool ->
      ctx.use_real := true;
      Fn (">=", [smt_cval ctx v1; smt_cval ctx v2])
  | _ ->
      Reporting.unreachable ctx.pragma_l __POS__
        ("Unknown builtin " ^ name ^ " "
        ^ Util.string_of_list ", " string_of_ctyp (List.map cval_ctyp args)
        ^ " -> " ^ string_of_ctyp ret_ctyp
        )

let loc_doc _ = "UNKNOWN"

(* Memory reads and writes as defined in lib/regfp.sail *)
let writes = ref (-1)

let builtin_write_mem l ctx wk addr_size addr data_size data =
  incr writes;
  let name = "W" ^ string_of_int !writes in
  ( [
      Write_mem
        {
          name;
          node = ctx.node;
          active = Lazy.force ctx.pathcond;
          kind = smt_cval ctx wk;
          addr = smt_cval ctx addr;
          addr_type = smt_ctyp ctx (cval_ctyp addr);
          data = smt_cval ctx data;
          data_type = smt_ctyp ctx (cval_ctyp data);
          doc = loc_doc l;
        };
    ],
    Var (name ^ "_ret")
  )

let ea_writes = ref (-1)

let builtin_write_mem_ea ctx wk addr_size addr data_size =
  incr ea_writes;
  let name = "A" ^ string_of_int !ea_writes in
  ( [
      Write_mem_ea
        ( name,
          ctx.node,
          Lazy.force ctx.pathcond,
          smt_cval ctx wk,
          smt_cval ctx addr,
          smt_ctyp ctx (cval_ctyp addr),
          smt_cval ctx data_size,
          smt_ctyp ctx (cval_ctyp data_size)
        );
    ],
    Enum "unit"
  )

let reads = ref (-1)

let builtin_read_mem l ctx rk addr_size addr data_size ret_ctyp =
  incr reads;
  let name = "R" ^ string_of_int !reads in
  ( [
      Read_mem
        {
          name;
          node = ctx.node;
          active = Lazy.force ctx.pathcond;
          ret_type = smt_ctyp ctx ret_ctyp;
          kind = smt_cval ctx rk;
          addr = smt_cval ctx addr;
          addr_type = smt_ctyp ctx (cval_ctyp addr);
          doc = loc_doc l;
        };
    ],
    Read_res name
  )

let excl_results = ref (-1)

let builtin_excl_res ctx =
  incr excl_results;
  let name = "E" ^ string_of_int !excl_results in
  ([Excl_res (name, ctx.node, Lazy.force ctx.pathcond)], Var (name ^ "_ret"))

let barriers = ref (-1)

let builtin_barrier l ctx bk =
  incr barriers;
  let name = "B" ^ string_of_int !barriers in
  ( [Barrier { name; node = ctx.node; active = Lazy.force ctx.pathcond; kind = smt_cval ctx bk; doc = loc_doc l }],
    Enum "unit"
  )

let cache_maintenances = ref (-1)

let builtin_cache_maintenance l ctx cmk addr_size addr =
  incr cache_maintenances;
  let name = "M" ^ string_of_int !cache_maintenances in
  ( [
      Cache_maintenance
        {
          name;
          node = ctx.node;
          active = Lazy.force ctx.pathcond;
          kind = smt_cval ctx cmk;
          addr = smt_cval ctx addr;
          addr_type = smt_ctyp ctx (cval_ctyp addr);
          doc = loc_doc l;
        };
    ],
    Enum "unit"
  )

let branch_announces = ref (-1)

let builtin_branch_announce l ctx addr_size addr =
  incr branch_announces;
  let name = "C" ^ string_of_int !branch_announces in
  ( [
      Branch_announce
        {
          name;
          node = ctx.node;
          active = Lazy.force ctx.pathcond;
          addr = smt_cval ctx addr;
          addr_type = smt_ctyp ctx (cval_ctyp addr);
          doc = loc_doc l;
        };
    ],
    Enum "unit"
  )

let define_const ctx id ctyp exp = Define_const (zencode_name id, smt_ctyp ctx ctyp, exp)
let preserve_const ctx id ctyp exp = Preserve_const (string_of_id id, smt_ctyp ctx ctyp, exp)
let declare_const ctx id ctyp = Declare_const (zencode_name id, smt_ctyp ctx ctyp)

let smt_ctype_def ctx = function
  | CTD_enum (id, elems) -> [declare_datatypes (mk_enum (zencode_upper_id id) (List.map zencode_id elems))]
  | CTD_struct (id, fields) ->
      [
        declare_datatypes
          (mk_record (zencode_upper_id id)
             (List.map (fun (field, ctyp) -> (zencode_upper_id id ^ "_" ^ zencode_id field, smt_ctyp ctx ctyp)) fields)
          );
      ]
  | CTD_variant (id, ctors) ->
      [
        declare_datatypes
          (mk_variant (zencode_upper_id id) (List.map (fun (ctor, ctyp) -> (zencode_id ctor, smt_ctyp ctx ctyp)) ctors));
      ]

let rec generate_ctype_defs ctx = function
  | CDEF_type ctd :: cdefs -> smt_ctype_def ctx ctd :: generate_ctype_defs ctx cdefs
  | _ :: cdefs -> generate_ctype_defs ctx cdefs
  | [] -> []

let rec generate_reg_decs ctx inits = function
  | CDEF_register (id, ctyp, _) :: cdefs when not (NameMap.mem (Global (id, 0)) inits) ->
      Declare_const (zencode_name (Global (id, 0)), smt_ctyp ctx ctyp) :: generate_reg_decs ctx inits cdefs
  | _ :: cdefs -> generate_reg_decs ctx inits cdefs
  | [] -> []

(**************************************************************************)
(* 2. Converting sail types to Jib types for SMT                          *)
(**************************************************************************)

let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))

module SMT_config (Opts : sig
  val unroll_limit : int
end) : Jib_compile.CONFIG = struct
  open Jib_compile

  (** Convert a sail type into a C-type. This function can be quite
     slow, because it uses ctx.local_env and SMT to analyse the Sail
     types and attempts to fit them into the smallest possible C
     types, provided ctx.optimize_smt is true (default) **)
  let rec convert_typ ctx typ =
    let open Ast in
    let open Type_check in
    let (Typ_aux (typ_aux, l) as typ) = Env.expand_synonyms ctx.local_env typ in
    match typ_aux with
    | Typ_id id when string_of_id id = "bit" -> CT_bit
    | Typ_id id when string_of_id id = "bool" -> CT_bool
    | Typ_id id when string_of_id id = "int" -> CT_lint
    | Typ_id id when string_of_id id = "nat" -> CT_lint
    | Typ_id id when string_of_id id = "unit" -> CT_unit
    | Typ_id id when string_of_id id = "string" -> CT_string
    | Typ_id id when string_of_id id = "real" -> CT_real
    | Typ_app (id, _) when string_of_id id = "atom_bool" -> CT_bool
    | Typ_app (id, args) when string_of_id id = "itself" -> convert_typ ctx (Typ_aux (Typ_app (mk_id "atom", args), l))
    | Typ_app (id, _) when string_of_id id = "range" || string_of_id id = "atom" || string_of_id id = "implicit" ->
      begin
        match destruct_range ctx.local_env typ with
        | None -> assert false (* Checked if range type in guard *)
        | Some (kids, constr, n, m) -> (
            let ctx =
              {
                ctx with
                local_env = add_existential Parse_ast.Unknown (List.map (mk_kopt K_int) kids) constr ctx.local_env;
              }
            in
            match (nexp_simp n, nexp_simp m) with
            | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _) when n = m -> CT_constant n
            | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
              when Big_int.less_equal (min_int 64) n && Big_int.less_equal m (max_int 64) ->
                CT_fint 64
            | n, m ->
                if
                  prove __POS__ ctx.local_env (nc_lteq (nconstant (min_int 64)) n)
                  && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_int 64)))
                then CT_fint 64
                else CT_lint
          )
      end
    | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "list" -> CT_list (convert_typ ctx typ)
    (* Note that we have to use lbits for zero-length bitvectors because they are not allowed by SMTLIB *)
    | Typ_app (id, [A_aux (A_nexp n, _)]) when string_of_id id = "bitvector" -> begin
        match nexp_simp n with
        | Nexp_aux (Nexp_constant n, _) when Big_int.equal n Big_int.zero -> CT_lbits
        | Nexp_aux (Nexp_constant n, _) -> CT_fbits (Big_int.to_int n)
        | _ -> CT_lbits
      end
    | Typ_app (id, [A_aux (A_nexp n, _); A_aux (A_typ typ, _)]) when string_of_id id = "vector" ->
        CT_vector (convert_typ ctx typ)
    | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "register" -> CT_ref (convert_typ ctx typ)
    | Typ_id id when Bindings.mem id ctx.records ->
        CT_struct (id, Bindings.find id ctx.records |> snd |> Bindings.bindings)
    | Typ_app (id, typ_args) when Bindings.mem id ctx.records ->
        let typ_params, fields = Bindings.find id ctx.records in
        let quants =
          List.fold_left2
            (fun quants typ_param typ_arg ->
              match typ_arg with
              | A_aux (A_typ typ, _) -> KBindings.add typ_param (convert_typ ctx typ) quants
              | _ -> Reporting.unreachable l __POS__ "Non-type argument for record here should be impossible"
            )
            ctx.quants typ_params (List.filter is_typ_arg_typ typ_args)
        in
        let fix_ctyp ctyp = if is_polymorphic ctyp then ctyp_suprema (subst_poly quants ctyp) else ctyp in
        CT_struct (id, Bindings.map fix_ctyp fields |> Bindings.bindings)
    | Typ_id id when Bindings.mem id ctx.variants ->
        CT_variant (id, Bindings.find id ctx.variants |> snd |> Bindings.bindings)
    | Typ_app (id, typ_args) when Bindings.mem id ctx.variants ->
        let typ_params, ctors = Bindings.find id ctx.variants in
        let quants =
          List.fold_left2
            (fun quants typ_param typ_arg ->
              match typ_arg with
              | A_aux (A_typ typ, _) -> KBindings.add typ_param (convert_typ ctx typ) quants
              | _ -> Reporting.unreachable l __POS__ "Non-type argument for variant here should be impossible"
            )
            ctx.quants typ_params (List.filter is_typ_arg_typ typ_args)
        in
        let fix_ctyp ctyp = if is_polymorphic ctyp then ctyp_suprema (subst_poly quants ctyp) else ctyp in
        CT_variant (id, Bindings.map fix_ctyp ctors |> Bindings.bindings)
    | Typ_id id when Bindings.mem id ctx.enums -> CT_enum (id, Bindings.find id ctx.enums |> IdSet.elements)
    | Typ_tuple typs -> CT_tup (List.map (convert_typ ctx) typs)
    | Typ_exist _ -> begin
        (* Use Type_check.destruct_exist when optimising with SMT, to
           ensure that we don't cause any type variable clashes in
           local_env, and that we can optimize the existential based
           upon its constraints. *)
        match destruct_exist typ with
        | Some (kids, nc, typ) ->
            let env = add_existential l kids nc ctx.local_env in
            convert_typ { ctx with local_env = env } typ
        | None -> raise (Reporting.err_unreachable l __POS__ "Existential cannot be destructured!")
      end
    | Typ_var kid -> CT_poly kid
    | _ -> raise (Reporting.err_unreachable l __POS__ ("No SMT type for type " ^ string_of_typ typ))

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
        Some (V_lit (VL_bits content, CT_fbits (String.length str * 4)))
    | L_unit -> Some (V_lit (VL_unit, CT_unit))
    | L_true -> Some (V_lit (VL_bool true, CT_bool))
    | L_false -> Some (V_lit (VL_bool false, CT_bool))
    | _ -> None

  let c_literals ctx =
    let rec c_literal env l = function
      | AV_lit (lit, typ) as v -> begin match literal_to_cval lit with Some cval -> AV_cval (cval, typ) | None -> v end
      | AV_tuple avals -> AV_tuple (List.map (c_literal env l) avals)
      | v -> v
    in
    map_aval c_literal

  (* If we know the loop variables exactly (especially after
     specialization), we can unroll the exact number of times required,
     and omit any comparisons. *)
  let unroll_static_foreach ctx = function
    | AE_aux (AE_for (id, from_aexp, to_aexp, by_aexp, order, body), env, l) as aexp -> begin
        match
          ( convert_typ ctx (aexp_typ from_aexp),
            convert_typ ctx (aexp_typ to_aexp),
            convert_typ ctx (aexp_typ by_aexp),
            order
          )
        with
        | CT_constant f, CT_constant t, CT_constant b, Ord_aux (Ord_inc, _) ->
            let i = ref f in
            let unrolled = ref [] in
            while Big_int.less_equal !i t do
              let current_index =
                AE_aux (AE_val (AV_lit (L_aux (L_num !i, gen_loc l), atom_typ (nconstant !i))), env, gen_loc l)
              in
              let iteration =
                AE_aux (AE_let (Immutable, id, atom_typ (nconstant !i), current_index, body, unit_typ), env, gen_loc l)
              in
              unrolled := iteration :: !unrolled;
              i := Big_int.add !i b
            done;
            begin
              match !unrolled with
              | last :: iterations -> AE_aux (AE_block (List.rev iterations, last, unit_typ), env, gen_loc l)
              | [] -> AE_aux (AE_val (AV_lit (L_aux (L_unit, gen_loc l), unit_typ)), env, gen_loc l)
            end
        | _ -> aexp
      end
    | aexp -> aexp

  let optimize_anf ctx aexp = aexp |> c_literals ctx |> fold_aexp (unroll_static_foreach ctx)

  let make_call_precise _ _ = false
  let ignore_64 = true
  let unroll_loops = Some Opts.unroll_limit
  let struct_value = true
  let tuple_value = false
  let use_real = true
  let branch_coverage = None
  let track_throw = false
end

(**************************************************************************)
(* 3. Generating SMT                                                      *)
(**************************************************************************)

let push_smt_defs stack smt_defs = List.iter (fun def -> Stack.push def stack) smt_defs

(* When generating SMT when we encounter joins between two or more
   blocks such as in the example below, we have to generate a muxer
   that chooses the correct value of v_n or v_m to assign to v_o. We
   use the pi nodes that contain the path condition for each
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
  | Phi (id, ctyp, ids) -> (
      let get_pi n =
        match get_vertex cfg n with
        | Some ((ssa_elems, _), _, _) -> List.concat (List.map (function Pi guards -> guards | _ -> []) ssa_elems)
        | None -> failwith "Predecessor node does not exist"
      in
      let pis = List.map get_pi (IntSet.elements preds) in
      let mux =
        List.fold_right2
          (fun pi id chain ->
            let pathcond = smt_conj (List.map (smt_cval ctx) pi) in
            match chain with
            | Some smt -> Some (Ite (pathcond, Var (zencode_name id), smt))
            | None -> Some (Var (zencode_name id))
          )
          pis ids None
      in
      match mux with None -> assert false | Some mux -> [Define_const (zencode_name id, smt_ctyp ctx ctyp, mux)]
    )

(* The pi condition are computed by traversing the dominator tree,
   with each node having a pi condition defined as the conjunction of
   all guards between it and the start node in the dominator
   tree. This is imprecise because we have situations like:

      1
     / \
    2   3
    |   |
    |   4
    |   |\
    5   6 9
     \ /  |
      7   10
      |
      8

   where 8 = match_failure, 1 = start and 10 = return.
   2, 3, 6 and 9 are guards as they come directly after a control flow
   split, which always follows a conditional jump.

   Here the path through the dominator tree for the match_failure is
   1->7->8 which contains no guards so the pi condition would be empty.
   What we do now is walk backwards (CFG must be acyclic at this point)
   until we hit the join point prior to where we require a path
   condition. We then take the disjunction of the pi conditions for the
   join point's predecessors, so 5 and 6 in this case. Which gives us a
   path condition of 2 | (3 & 6) as the dominator chains are 1->2->5 and
   1->3->4->6.

   This should work as any split in the control flow must have been
   caused by a conditional jump followed by distinct guards, so each of
   the nodes immediately prior to a join point must be dominated by at
   least one unique guard. It also explains why the pi conditions are
   sufficient to choose outcomes of phi functions above.

   If we hit a guard before a join (such as 9 for return's path
   conditional) we just return the pi condition for that guard, i.e.
   (3 & 9) for 10. If we reach start then the path condition is simply
   true.
*)
let rec get_pathcond n cfg ctx =
  let open Jib_ssa in
  let get_pi m =
    match get_vertex cfg m with
    | Some ((ssa_elems, _), _, _) ->
        V_call (Band, List.concat (List.map (function Pi guards -> guards | _ -> []) ssa_elems))
    | None -> failwith "Node does not exist"
  in
  match get_vertex cfg n with
  | Some ((_, CF_guard cond), _, _) -> smt_cval ctx (get_pi n)
  | Some (_, preds, succs) ->
      if IntSet.cardinal preds = 0 then Bool_lit true
      else if IntSet.cardinal preds = 1 then get_pathcond (IntSet.min_elt preds) cfg ctx
      else (
        let pis = List.map get_pi (IntSet.elements preds) in
        smt_cval ctx (V_call (Bor, pis))
      )
  | None -> assert false (* Should never be called for a non-existent node *)

(* For any complex l-expression we need to turn it into a
   read-modify-write in the SMT solver. The SSA transform turns CL_id
   nodes into CL_rmw (read, write, ctyp) nodes when CL_id is wrapped
   in any other l-expression. The read and write must have the same
   name but different SSA numbers.
*)
let rec rmw_write = function
  | CL_rmw (_, write, ctyp) -> (write, ctyp)
  | CL_id _ -> assert false
  | CL_tuple (clexp, _) -> rmw_write clexp
  | CL_field (clexp, _) -> rmw_write clexp
  | clexp -> failwith "Could not understand l-expression"

let rmw_read = function CL_rmw (read, _, _) -> zencode_name read | _ -> assert false

let rmw_modify smt = function
  | CL_tuple (clexp, n) ->
      let ctyp = clexp_ctyp clexp in
      begin
        match ctyp with
        | CT_tup ctyps ->
            let len = List.length ctyps in
            let set_tup i = if i == n then smt else Fn (Printf.sprintf "tup_%d_%d" len i, [Var (rmw_read clexp)]) in
            Fn ("tup" ^ string_of_int len, List.init len set_tup)
        | _ -> failwith "Tuple modify does not have tuple type"
      end
  | CL_field (clexp, field) ->
      let ctyp = clexp_ctyp clexp in
      begin
        match ctyp with
        | CT_struct (struct_id, fields) ->
            let set_field (field', _) =
              if Id.compare field field' = 0 then smt
              else Field (zencode_upper_id struct_id ^ "_" ^ zencode_id field', Var (rmw_read clexp))
            in
            Fn (zencode_upper_id struct_id, List.map set_field fields)
        | _ -> failwith "Struct modify does not have struct type"
      end
  | _ -> assert false

let smt_terminator ctx =
  let open Jib_ssa in
  function
  | T_end id ->
      add_event ctx Return (Var (zencode_name id));
      []
  | T_exit _ ->
      add_pathcond_event ctx Match;
      []
  | T_undefined _ | T_goto _ | T_jump _ | T_label _ | T_none -> []

(* For a basic block (contained in a control-flow node / cfnode), we
   turn the instructions into a sequence of define-const and
   declare-const expressions. Because we are working with a SSA graph,
   each variable is guaranteed to only be declared once.
*)
let smt_instr ctx =
  let open Type_check in
  function
  | I_aux (I_funcall (CL_id (id, ret_ctyp), extern, function_id, args), (_, l)) ->
      if Env.is_extern (fst function_id) ctx.tc_env "c" && not extern then (
        let name = Env.get_extern (fst function_id) ctx.tc_env "c" in
        if name = "sqrt_real" then begin
          match args with
          | [v] -> builtin_sqrt_real ctx (zencode_name id) v
          | _ -> Reporting.unreachable l __POS__ "Bad arguments for sqrt_real"
          (* See lib/regfp.sail *)
        end
        else if name = "platform_write_mem" then begin
          match args with
          | [wk; addr_size; addr; data_size; data] ->
              let mem_event, var = builtin_write_mem l ctx wk addr_size addr data_size data in
              mem_event @ [define_const ctx id ret_ctyp var]
          | _ -> Reporting.unreachable l __POS__ "Bad arguments for __write_mem"
        end
        else if name = "platform_write_mem_ea" then begin
          match args with
          | [wk; addr_size; addr; data_size] ->
              let mem_event, var = builtin_write_mem_ea ctx wk addr_size addr data_size in
              mem_event @ [define_const ctx id ret_ctyp var]
          | _ -> Reporting.unreachable l __POS__ "Bad arguments for __write_mem_ea"
        end
        else if name = "platform_read_mem" then begin
          match args with
          | [rk; addr_size; addr; data_size] ->
              let mem_event, var = builtin_read_mem l ctx rk addr_size addr data_size ret_ctyp in
              mem_event @ [define_const ctx id ret_ctyp var]
          | _ -> Reporting.unreachable l __POS__ "Bad arguments for __read_mem"
        end
        else if name = "platform_barrier" then begin
          match args with
          | [bk] ->
              let mem_event, var = builtin_barrier l ctx bk in
              mem_event @ [define_const ctx id ret_ctyp var]
          | _ -> Reporting.unreachable l __POS__ "Bad arguments for __barrier"
        end
        else if name = "platform_cache_maintenance" then begin
          match args with
          | [cmk; addr_size; addr] ->
              let mem_event, var = builtin_cache_maintenance l ctx cmk addr_size addr in
              mem_event @ [define_const ctx id ret_ctyp var]
          | _ -> Reporting.unreachable l __POS__ "Bad arguments for __barrier"
        end
        else if name = "platform_branch_announce" then begin
          match args with
          | [addr_size; addr] ->
              let mem_event, var = builtin_branch_announce l ctx addr_size addr in
              mem_event @ [define_const ctx id ret_ctyp var]
          | _ -> Reporting.unreachable l __POS__ "Bad arguments for __barrier"
        end
        else if name = "platform_excl_res" then begin
          match args with
          | [_] ->
              let mem_event, var = builtin_excl_res ctx in
              mem_event @ [define_const ctx id ret_ctyp var]
          | _ -> Reporting.unreachable l __POS__ "Bad arguments for __excl_res"
        end
        else if name = "sail_exit" then (
          add_event ctx Assertion (Bool_lit false);
          []
        )
        else if name = "sail_assert" then begin
          match args with
          | [assertion; _] ->
              let smt = smt_cval ctx assertion in
              add_event ctx Assertion (Fn ("not", [smt]));
              []
          | _ -> Reporting.unreachable l __POS__ "Bad arguments for assertion"
        end
        else (
          let value = smt_builtin ctx name args ret_ctyp in
          [define_const ctx id ret_ctyp (Syntactic (value, List.map (smt_cval ctx) args))]
        )
      )
      else if extern && string_of_id (fst function_id) = "internal_vector_init" then [declare_const ctx id ret_ctyp]
      else if extern && string_of_id (fst function_id) = "internal_vector_update" then begin
        match args with
        | [vec; i; x] ->
            let sz = int_size ctx (cval_ctyp i) in
            [
              define_const ctx id ret_ctyp
                (Fn
                   ( "store",
                     [
                       smt_cval ctx vec;
                       force_size ~checked:false ctx ctx.vector_index sz (smt_cval ctx i);
                       smt_cval ctx x;
                     ]
                   )
                );
            ]
        | _ -> Reporting.unreachable l __POS__ "Bad arguments for internal_vector_update"
      end
      else if
        (string_of_id (fst function_id) = "update_fbits" || string_of_id (fst function_id) = "update_lbits") && extern
      then begin
        match args with
        | [vec; i; x] -> [define_const ctx id ret_ctyp (builtin_vector_update ctx vec i x ret_ctyp)]
        | _ -> Reporting.unreachable l __POS__ "Bad arguments for update_{f,l}bits"
      end
      else if string_of_id (fst function_id) = "sail_assume" then begin
        match args with
        | [assumption] ->
            let smt = smt_cval ctx assumption in
            add_event ctx Assumption smt;
            []
        | _ -> Reporting.unreachable l __POS__ "Bad arguments for assumption"
      end
      else if not extern then (
        let smt_args = List.map (smt_cval ctx) args in
        [define_const ctx id ret_ctyp (Ctor (zencode_uid function_id, smt_args))]
      )
      else failwith ("Unrecognised function " ^ string_of_uid function_id)
  | I_aux (I_copy (CL_addr (CL_id (_, _)), _), (_, l)) ->
      Reporting.unreachable l __POS__ "Register reference write should be re-written by now"
  | I_aux (I_init (ctyp, id, cval), _) | I_aux (I_copy (CL_id (id, ctyp), cval), _) -> begin
      match (id, cval) with
      | (Name (id, _) | Global (id, _)), _ when IdSet.mem id ctx.preserved ->
          [preserve_const ctx id ctyp (smt_conversion ctx (cval_ctyp cval) ctyp (smt_cval ctx cval))]
      | _, V_lit (VL_undefined, _) ->
          (* Declare undefined variables as arbitrary but fixed *)
          [declare_const ctx id ctyp]
      | _, _ -> [define_const ctx id ctyp (smt_conversion ctx (cval_ctyp cval) ctyp (smt_cval ctx cval))]
    end
  | I_aux (I_copy (clexp, cval), _) ->
      let smt = smt_cval ctx cval in
      let write, ctyp = rmw_write clexp in
      [define_const ctx write ctyp (rmw_modify smt clexp)]
  | I_aux (I_decl (ctyp, id), (_, l)) ->
      (* Function arguments have unique locations defined from the
         $property pragma. We record how they will appear in the
         generated SMT so we can check models. *)
      begin
        match l with Unique (n, l') when l' = ctx.pragma_l -> Stack.push (n, zencode_name id) ctx.arg_stack | _ -> ()
      end;
      [declare_const ctx id ctyp]
  | I_aux (I_clear _, _) -> []
  (* Should only appear as terminators for basic blocks. *)
  | I_aux ((I_jump _ | I_goto _ | I_end _ | I_exit _ | I_undefined _), (_, l)) ->
      Reporting.unreachable l __POS__ "SMT: Instruction should only appear as block terminator"
  | I_aux (_, (_, l)) -> Reporting.unreachable l __POS__ "Cannot translate instruction"

let smt_cfnode all_cdefs ctx ssa_elems =
  let open Jib_ssa in
  function
  | CF_start inits ->
      let smt_reg_decs = generate_reg_decs ctx inits all_cdefs in
      let smt_start (id, ctyp) =
        match id with Have_exception _ -> define_const ctx id ctyp (Bool_lit false) | _ -> declare_const ctx id ctyp
      in
      smt_reg_decs @ List.map smt_start (NameMap.bindings inits)
  | CF_block (instrs, terminator) ->
      let smt_instrs = List.map (smt_instr ctx) instrs in
      let smt_term = smt_terminator ctx terminator in
      List.concat (smt_instrs @ [smt_term])
  (* We can ignore any non basic-block/start control-flow nodes *)
  | _ -> []

(** When we generate a property for a CDEF_val, we find it's
   associated function body in a CDEF_fundef node. However, we must
   keep track of any global letbindings between the spec and the
   fundef, so they can appear in the generated SMT. *)
let rec find_function lets id = function
  | CDEF_fundef (id', heap_return, args, body) :: _ when Id.compare id id' = 0 -> (lets, Some (heap_return, args, body))
  | CDEF_let (_, vars, setup) :: cdefs ->
      let vars = List.map (fun (id, ctyp) -> idecl (id_loc id) ctyp (global id)) vars in
      find_function (lets @ vars @ setup) id cdefs
  | _ :: cdefs -> find_function lets id cdefs
  | [] -> (lets, None)

module type Sequence = sig
  type 'a t
  val create : unit -> 'a t
  val add : 'a -> 'a t -> unit
end

module Make_optimizer (S : Sequence) = struct
  let optimize stack =
    let stack' = Stack.create () in
    let uses = Hashtbl.create (Stack.length stack) in

    let rec uses_in_exp = function
      | Var var -> begin
          match Hashtbl.find_opt uses var with
          | Some n -> Hashtbl.replace uses var (n + 1)
          | None -> Hashtbl.add uses var 1
        end
      | Syntactic (exp, _) -> uses_in_exp exp
      | Shared _ | Enum _ | Read_res _ | Bitvec_lit _ | Bool_lit _ | String_lit _ | Real_lit _ -> ()
      | Fn (_, exps) | Ctor (_, exps) -> List.iter uses_in_exp exps
      | Field (_, exp) -> uses_in_exp exp
      | Struct (_, fields) -> List.iter (fun (_, exp) -> uses_in_exp exp) fields
      | Ite (cond, t, e) ->
          uses_in_exp cond;
          uses_in_exp t;
          uses_in_exp e
      | Extract (_, _, exp) | Tester (_, exp) | SignExtend (_, exp) -> uses_in_exp exp
      | Forall _ -> assert false
    in

    let remove_unused () = function
      | Declare_const (var, _) as def -> begin
          match Hashtbl.find_opt uses var with None -> () | Some _ -> Stack.push def stack'
        end
      | Declare_fun _ as def -> Stack.push def stack'
      | Preserve_const (_, _, exp) as def ->
          uses_in_exp exp;
          Stack.push def stack'
      | Define_const (var, _, exp) as def -> begin
          match Hashtbl.find_opt uses var with
          | None -> ()
          | Some _ ->
              uses_in_exp exp;
              Stack.push def stack'
        end
      | (Declare_datatypes _ | Declare_tuple _) as def -> Stack.push def stack'
      | Write_mem w as def ->
          uses_in_exp w.active;
          uses_in_exp w.kind;
          uses_in_exp w.addr;
          uses_in_exp w.data;
          Stack.push def stack'
      | Write_mem_ea (_, _, active, wk, addr, _, data_size, _) as def ->
          uses_in_exp active;
          uses_in_exp wk;
          uses_in_exp addr;
          uses_in_exp data_size;
          Stack.push def stack'
      | Read_mem r as def ->
          uses_in_exp r.active;
          uses_in_exp r.kind;
          uses_in_exp r.addr;
          Stack.push def stack'
      | Barrier b as def ->
          uses_in_exp b.active;
          uses_in_exp b.kind;
          Stack.push def stack'
      | Cache_maintenance m as def ->
          uses_in_exp m.active;
          uses_in_exp m.kind;
          uses_in_exp m.addr;
          Stack.push def stack'
      | Branch_announce c as def ->
          uses_in_exp c.active;
          uses_in_exp c.addr;
          Stack.push def stack'
      | Excl_res (_, _, active) as def ->
          uses_in_exp active;
          Stack.push def stack'
      | Assert exp as def ->
          uses_in_exp exp;
          Stack.push def stack'
      | Define_fun _ -> assert false
    in
    Stack.fold remove_unused () stack;

    let vars = Hashtbl.create (Stack.length stack') in
    let kinds = Hashtbl.create (Stack.length stack') in
    let seq = S.create () in

    let constant_propagate = function
      | Declare_const _ as def -> S.add def seq
      | Declare_fun _ as def -> S.add def seq
      | Preserve_const (var, typ, exp) -> S.add (Preserve_const (var, typ, simp_smt_exp vars kinds exp)) seq
      | Define_const (var, typ, exp) ->
          let exp = simp_smt_exp vars kinds exp in
          begin
            match (Hashtbl.find_opt uses var, simp_smt_exp vars kinds exp) with
            | _, (Bitvec_lit _ | Bool_lit _) -> Hashtbl.add vars var exp
            | _, Var _ when !opt_propagate_vars -> Hashtbl.add vars var exp
            | _, Ctor (str, _) ->
                Hashtbl.add kinds var str;
                S.add (Define_const (var, typ, exp)) seq
            | Some 1, _ -> Hashtbl.add vars var exp
            | Some _, exp -> S.add (Define_const (var, typ, exp)) seq
            | None, _ -> assert false
          end
      | Write_mem w ->
          S.add
            (Write_mem
               {
                 w with
                 active = simp_smt_exp vars kinds w.active;
                 kind = simp_smt_exp vars kinds w.kind;
                 addr = simp_smt_exp vars kinds w.addr;
                 data = simp_smt_exp vars kinds w.data;
               }
            )
            seq
      | Write_mem_ea (name, node, active, wk, addr, addr_ty, data_size, data_size_ty) ->
          S.add
            (Write_mem_ea
               ( name,
                 node,
                 simp_smt_exp vars kinds active,
                 simp_smt_exp vars kinds wk,
                 simp_smt_exp vars kinds addr,
                 addr_ty,
                 simp_smt_exp vars kinds data_size,
                 data_size_ty
               )
            )
            seq
      | Read_mem r ->
          S.add
            (Read_mem
               {
                 r with
                 active = simp_smt_exp vars kinds r.active;
                 kind = simp_smt_exp vars kinds r.kind;
                 addr = simp_smt_exp vars kinds r.addr;
               }
            )
            seq
      | Barrier b ->
          S.add
            (Barrier { b with active = simp_smt_exp vars kinds b.active; kind = simp_smt_exp vars kinds b.kind })
            seq
      | Cache_maintenance m ->
          S.add
            (Cache_maintenance
               {
                 m with
                 active = simp_smt_exp vars kinds m.active;
                 kind = simp_smt_exp vars kinds m.kind;
                 addr = simp_smt_exp vars kinds m.addr;
               }
            )
            seq
      | Branch_announce c ->
          S.add
            (Branch_announce { c with active = simp_smt_exp vars kinds c.active; addr = simp_smt_exp vars kinds c.addr })
            seq
      | Excl_res (name, node, active) -> S.add (Excl_res (name, node, simp_smt_exp vars kinds active)) seq
      | Assert exp -> S.add (Assert (simp_smt_exp vars kinds exp)) seq
      | (Declare_datatypes _ | Declare_tuple _) as def -> S.add def seq
      | Define_fun _ -> assert false
    in
    Stack.iter constant_propagate stack';
    seq
end

module Queue_optimizer = Make_optimizer (struct
  type 'a t = 'a Queue.t
  let create = Queue.create
  let add = Queue.add
  let iter = Queue.iter
end)

(** [smt_header ctx cdefs] produces a list of smt definitions for all the datatypes in a specification *)
let smt_header ctx cdefs =
  let smt_ctype_defs = List.concat (generate_ctype_defs ctx cdefs) in
  [declare_datatypes (mk_enum "Unit" ["unit"])]
  @ (IntSet.elements !(ctx.tuple_sizes) |> List.map (fun n -> Declare_tuple n))
  @ [declare_datatypes (mk_record "Bits" [("len", Bitvec ctx.lbits_index); ("contents", Bitvec (lbits_size ctx))])]
  @ smt_ctype_defs

(* For generating SMT when we have a reg_deref(r : register(t))
   function, we have to expand it into a if-then-else cascade that
   checks if r is any one of the registers with type t, and reads that
   register if it is. We also do a similar thing for *r = x
*)
let expand_reg_deref env register_map = function
  | I_aux (I_funcall (CL_addr (CL_id (id, ctyp)), false, function_id, args), (_, l)) -> begin
      match ctyp with
      | CT_ref reg_ctyp -> begin
          match CTMap.find_opt reg_ctyp register_map with
          | Some regs ->
              let end_label = label "end_reg_write_" in
              let try_reg r =
                let next_label = label "next_reg_write_" in
                [
                  ijump l (V_call (Neq, [V_lit (VL_ref (string_of_id r), reg_ctyp); V_id (id, ctyp)])) next_label;
                  ifuncall l (CL_id (global r, reg_ctyp)) function_id args;
                  igoto end_label;
                  ilabel next_label;
                ]
              in
              iblock (List.concat (List.map try_reg regs) @ [ilabel end_label])
          | None -> raise (Reporting.err_general l ("Could not find any registers with type " ^ string_of_ctyp reg_ctyp))
        end
      | _ ->
          raise (Reporting.err_general l "Register reference assignment must take a register reference as an argument")
    end
  | I_aux (I_funcall (clexp, false, function_id, [reg_ref]), (_, l)) as instr ->
      let open Type_check in
      begin
        match
          if Env.is_extern (fst function_id) env "smt" then Some (Env.get_extern (fst function_id) env "smt") else None
        with
        | Some "reg_deref" -> begin
            match cval_ctyp reg_ref with
            | CT_ref reg_ctyp -> begin
                (* Not find all the registers with this ctyp *)
                match CTMap.find_opt reg_ctyp register_map with
                | Some regs ->
                    let end_label = label "end_reg_deref_" in
                    let try_reg r =
                      let next_label = label "next_reg_deref_" in
                      [
                        ijump l (V_call (Neq, [V_lit (VL_ref (string_of_id r), reg_ctyp); reg_ref])) next_label;
                        icopy l clexp (V_id (global r, reg_ctyp));
                        igoto end_label;
                        ilabel next_label;
                      ]
                    in
                    iblock (List.concat (List.map try_reg regs) @ [ilabel end_label])
                | None ->
                    raise (Reporting.err_general l ("Could not find any registers with type " ^ string_of_ctyp reg_ctyp))
              end
            | _ -> raise (Reporting.err_general l "Register dereference must have a register reference as an argument")
          end
        | _ -> instr
      end
  | I_aux (I_copy (CL_addr (CL_id (id, ctyp)), cval), (_, l)) -> begin
      match ctyp with
      | CT_ref reg_ctyp -> begin
          match CTMap.find_opt reg_ctyp register_map with
          | Some regs ->
              let end_label = label "end_reg_write_" in
              let try_reg r =
                let next_label = label "next_reg_write_" in
                [
                  ijump l (V_call (Neq, [V_lit (VL_ref (string_of_id r), reg_ctyp); V_id (id, ctyp)])) next_label;
                  icopy l (CL_id (global r, reg_ctyp)) cval;
                  igoto end_label;
                  ilabel next_label;
                ]
              in
              iblock (List.concat (List.map try_reg regs) @ [ilabel end_label])
          | None -> raise (Reporting.err_general l ("Could not find any registers with type " ^ string_of_ctyp reg_ctyp))
        end
      | _ ->
          raise (Reporting.err_general l "Register reference assignment must take a register reference as an argument")
    end
  | instr -> instr

let rec smt_query ctx = function
  | Q_all ev ->
      let stack = event_stack ctx ev in
      smt_conj (Stack.fold (fun xs x -> x :: xs) [] stack)
  | Q_exist ev ->
      let stack = event_stack ctx ev in
      smt_disj (Stack.fold (fun xs x -> x :: xs) [] stack)
  | Q_not q -> Fn ("not", [smt_query ctx q])
  | Q_and qs -> Fn ("and", List.map (smt_query ctx) qs)
  | Q_or qs -> Fn ("or", List.map (smt_query ctx) qs)

let dump_graph name cfg =
  let gv_file = name ^ ".gv" in
  let out_chan = open_out gv_file in
  Jib_ssa.make_dot out_chan cfg;
  close_out out_chan

let smt_instr_list name ctx all_cdefs instrs =
  let stack = Stack.create () in

  let open Jib_ssa in
  let start, cfg = ssa instrs in
  let visit_order =
    try topsort cfg
    with Not_a_DAG n ->
      dump_graph name cfg;
      raise
        (Reporting.err_general ctx.pragma_l
           (Printf.sprintf "%s: control flow graph is not acyclic (node %d is in cycle)\nWrote graph to %s.gv" name n
              name
           )
        )
  in
  if !opt_debug_graphs then dump_graph name cfg;

  List.iter
    (fun n ->
      match get_vertex cfg n with
      | None -> ()
      | Some ((ssa_elems, cfnode), preds, succs) ->
          let muxers = ssa_elems |> List.map (smt_ssanode ctx cfg preds) |> List.concat in
          let ctx = { ctx with node = n; pathcond = lazy (get_pathcond n cfg ctx) } in
          let basic_block = smt_cfnode all_cdefs ctx ssa_elems cfnode in
          push_smt_defs stack muxers;
          push_smt_defs stack basic_block
    )
    visit_order;

  (stack, start, cfg)

let smt_cdef props lets name_file ctx all_cdefs = function
  | CDEF_val (function_id, _, arg_ctyps, ret_ctyp) when Bindings.mem function_id props -> begin
      match find_function [] function_id all_cdefs with
      | intervening_lets, Some (None, args, instrs) ->
          let prop_type, prop_args, pragma_l, vs = Bindings.find function_id props in

          let pragma = parse_pragma pragma_l prop_args in

          let ctx = { ctx with events = ref EventMap.empty; pragma_l; arg_stack = Stack.create () } in

          (* When we create each argument declaration, give it a unique
             location from the $property pragma, so we can identify it later. *)
          let arg_decls =
            List.map2
              (fun id ctyp ->
                let l = unique pragma_l in
                idecl l ctyp (name id)
              )
              args arg_ctyps
          in
          let instrs =
            let open Jib_optimize in
            lets @ intervening_lets @ arg_decls @ instrs
            |> inline all_cdefs (fun _ -> true)
            |> List.map (map_instr (expand_reg_deref ctx.tc_env ctx.register_map))
            |> flatten_instrs |> remove_unused_labels |> remove_pointless_goto
          in

          let stack, _, _ = smt_instr_list (string_of_id function_id) ctx all_cdefs instrs in

          let query = smt_query ctx pragma.query in
          push_smt_defs stack [Assert (Fn ("not", [query]))];

          let fname = name_file (string_of_id function_id) in
          let out_chan = open_out fname in
          if prop_type = "counterexample" then output_string out_chan "(set-option :produce-models true)\n";

          let header = smt_header ctx all_cdefs in

          if !(ctx.use_string) || !(ctx.use_real) then output_string out_chan "(set-logic ALL)\n"
          else output_string out_chan "(set-logic QF_AUFBVDT)\n";

          List.iter
            (fun def ->
              output_string out_chan (string_of_smt_def def);
              output_string out_chan "\n"
            )
            header;

          let queue = Queue_optimizer.optimize stack in
          Queue.iter
            (fun def ->
              output_string out_chan (string_of_smt_def def);
              output_string out_chan "\n"
            )
            queue;

          output_string out_chan "(check-sat)\n";
          if prop_type = "counterexample" then output_string out_chan "(get-model)\n";

          close_out out_chan;
          if prop_type = "counterexample" && !opt_auto then (
            let arg_names = Stack.fold (fun m (k, v) -> (k, v) :: m) [] ctx.arg_stack in
            let arg_smt_names =
              List.map
                (function
                  | I_aux (I_decl (_, Name (id, _)), (_, Unique (n, _))) -> (id, List.assoc_opt n arg_names)
                  | _ -> assert false
                  )
                arg_decls
            in
            check_counterexample ctx.ast ctx.tc_env fname function_id args arg_ctyps arg_smt_names
          )
      | _ -> failwith "Bad function body"
    end
  | _ -> ()

let rec smt_cdefs props lets name_file ctx ast = function
  | CDEF_let (_, vars, setup) :: cdefs ->
      let vars = List.map (fun (id, ctyp) -> idecl (id_loc id) ctyp (global id)) vars in
      smt_cdefs props (lets @ vars @ setup) name_file ctx ast cdefs
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
  | CDEF_register (reg, ctyp, _) :: cdefs ->
      let rmap =
        match CTMap.find_opt ctyp rmap with
        | Some regs -> CTMap.add ctyp (reg :: regs) rmap
        | None -> CTMap.add ctyp [reg] rmap
      in
      build_register_map rmap cdefs
  | _ :: cdefs -> build_register_map rmap cdefs
  | [] -> rmap

let compile env effect_info ast =
  let cdefs, jib_ctx =
    let module Jibc = Jib_compile.Make (SMT_config (struct
      let unroll_limit = !opt_unroll_limit
    end)) in
    let env, effect_info = Jib_compile.add_special_functions env effect_info in
    let ctx = Jib_compile.initial_ctx env effect_info in
    let t = Profile.start () in
    let cdefs, ctx = Jibc.compile_ast ctx ast in
    Profile.finish "Compiling to Jib IR" t;
    (cdefs, ctx)
  in
  let cdefs = Jib_optimize.unique_per_function_ids cdefs in
  let rmap = build_register_map CTMap.empty cdefs in
  (cdefs, jib_ctx, { (initial_ctx ()) with tc_env = jib_ctx.tc_env; register_map = rmap; ast })

let serialize_smt_model file env effect_info ast =
  let cdefs, _, ctx = compile env effect_info ast in
  let out_chan = open_out file in
  Marshal.to_channel out_chan cdefs [];
  Marshal.to_channel out_chan (Type_check.Env.set_prover None ctx.tc_env) [];
  Marshal.to_channel out_chan ctx.register_map [];
  close_out out_chan

let deserialize_smt_model file =
  let in_chan = open_in file in
  let cdefs = (Marshal.from_channel in_chan : cdef list) in
  let env = (Marshal.from_channel in_chan : Type_check.env) in
  let rmap = (Marshal.from_channel in_chan : id list CTMap.t) in
  close_in in_chan;
  (cdefs, { (initial_ctx ()) with tc_env = env; register_map = rmap })

let generate_smt props name_file env effect_info ast =
  try
    let cdefs, _, ctx = compile env effect_info ast in
    smt_cdefs props [] name_file ctx cdefs cdefs
  with Type_error.Type_error (l, err) -> raise (Reporting.err_typ l (Type_error.string_of_type_error err))
