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
(*    Louis-Emile Ploix                                                     *)
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
open Ast_util
open Jib
open Jib_compile
open Jib_util
open PPrint
open Printf
open Smt_exp
open Property

let opt_debug_graphs = ref false

let zencode_upper_id id = Util.zencode_upper_string (string_of_id id)
let zencode_id id = Util.zencode_string (string_of_id id)
let zencode_name id = string_of_name ~deref_current_exception:false ~zencode:true id

let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))

let required_width n =
  let rec required_width' n =
    if Big_int.equal n Big_int.zero then 1 else 1 + required_width' (Big_int.shift_right n 1)
  in
  required_width' (Big_int.abs n)

module type Sequence = sig
  type 'a t
  val create : unit -> 'a t
  val add : 'a -> 'a t -> unit
end

module Make_optimizer (S : Sequence) = struct
  module NameHash = struct
    type t = Jib.name
    let equal x y = Name.compare x y = 0
    let hash = function
      | Name (Id_aux (aux, _), n) -> Hashtbl.hash (0, (aux, n))
      | Have_exception n -> Hashtbl.hash (1, n)
      | Current_exception n -> Hashtbl.hash (2, n)
      | Throw_location n -> Hashtbl.hash (3, n)
      | Return n -> Hashtbl.hash (4, n)
      | Channel (chan, n) -> Hashtbl.hash (5, (chan, n))
  end

  module NameHashtbl = Hashtbl.Make (NameHash)

  let optimize stack =
    let stack' = Stack.create () in
    let uses = NameHashtbl.create (Stack.length stack) in

    let rec uses_in_exp = function
      | Var var -> begin
          match NameHashtbl.find_opt uses var with
          | Some n -> NameHashtbl.replace uses var (n + 1)
          | None -> NameHashtbl.add uses var 1
        end
      | Unit | Member _ | Bitvec_lit _ | Bool_lit _ | String_lit _ | Real_lit _ | Empty_list -> ()
      | Fn (_, exps) -> List.iter uses_in_exp exps
      | Field (_, _, exp) -> uses_in_exp exp
      | Ite (cond, t, e) ->
          uses_in_exp cond;
          uses_in_exp t;
          uses_in_exp e
      | Extract (_, _, exp)
      | Unwrap (_, _, exp)
      | Tester (_, exp)
      | SignExtend (_, _, exp)
      | ZeroExtend (_, _, exp)
      | Hd (_, exp)
      | Tl (_, exp) ->
          uses_in_exp exp
      | Store (_, _, arr, index, x) ->
          uses_in_exp arr;
          uses_in_exp index;
          uses_in_exp x
    in

    let remove_unused () = function
      | Declare_const (var, _) as def -> begin
          match NameHashtbl.find_opt uses var with None -> () | Some _ -> Stack.push def stack'
        end
      | Declare_fun _ as def -> Stack.push def stack'
      | Define_const (var, _, exp) as def -> begin
          match NameHashtbl.find_opt uses var with
          | None -> ()
          | Some _ ->
              uses_in_exp exp;
              Stack.push def stack'
        end
      | Declare_datatypes _ as def -> Stack.push def stack'
      | Assert exp as def ->
          uses_in_exp exp;
          Stack.push def stack'
      | Define_fun _ -> assert false
    in
    Stack.fold remove_unused () stack;

    let vars = NameHashtbl.create (Stack.length stack') in
    let seq = S.create () in

    let constant_propagate = function
      | Declare_const _ as def -> S.add def seq
      | Declare_fun _ as def -> S.add def seq
      | Define_const (var, typ, exp) ->
          let exp = Smt_exp.simp (NameHashtbl.find_opt vars) exp in
          begin
            match (NameHashtbl.find_opt uses var, Smt_exp.simp (NameHashtbl.find_opt vars) exp) with
            | _, (Bitvec_lit _ | Bool_lit _) -> NameHashtbl.add vars var exp
            | Some 1, _ -> NameHashtbl.add vars var exp
            | Some _, exp -> S.add (Define_const (var, typ, exp)) seq
            | None, _ -> assert false
          end
      | Assert exp -> S.add (Assert (Smt_exp.simp (NameHashtbl.find_opt vars) exp)) seq
      | Declare_datatypes _ as def -> S.add def seq
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

module EventMap = Map.Make (Event)

type state = {
  events : smt_exp Stack.t EventMap.t ref;
  node : int;
  cfg : (Jib_ssa.ssa_elem list * Jib_ssa.cf_node) Jib_ssa.array_graph;
  arg_stack : (int * string) Stack.t;
}

let event_stack state ev =
  match EventMap.find_opt ev !(state.events) with
  | Some stack -> stack
  | None ->
      let stack = Stack.create () in
      state.events := EventMap.add ev stack !(state.events);
      stack

module type CONFIG = sig
  val max_unknown_integer_width : int
  val max_unknown_bitvector_width : int
  val max_unknown_generic_vector_length : int
  val register_map : id list CTMap.t
  val ignore_overflow : bool
end

module Make (Config : CONFIG) = struct
  open Jib_visitor

  let lbits_index_width = required_width (Big_int.of_int Config.max_unknown_bitvector_width)
  let vector_index_width = required_width (Big_int.of_int (Config.max_unknown_generic_vector_length - 1))

  module Smt =
    Smt_gen.Make
      (struct
        let max_unknown_integer_width = Config.max_unknown_integer_width
        let max_unknown_bitvector_width = Config.max_unknown_bitvector_width
        let max_unknown_generic_vector_length = Config.max_unknown_generic_vector_length
        let union_ctyp_classify _ = true
        let register_ref reg_name =
          let id = mk_id reg_name in
          let rmap =
            CTMap.filter (fun ctyp regs -> List.exists (fun reg -> Id.compare reg id = 0) regs) Config.register_map
          in
          assert (CTMap.cardinal rmap = 1);
          match CTMap.min_binding_opt rmap with
          | Some (ctyp, regs) -> begin
              match Util.list_index (fun reg -> Id.compare reg id = 0) regs with
              | Some i -> Smt_gen.bvint (required_width (Big_int.of_int (List.length regs))) (Big_int.of_int i)
              | None -> assert false
            end
          | _ -> assert false
      end)
      (struct
        let print_bits l = function _ -> Reporting.unreachable l __POS__ "print_bits"

        let string_of_bits l = function _ -> Reporting.unreachable l __POS__ "string_of_bits"

        let dec_str l = function _ -> Reporting.unreachable l __POS__ "dec_str"

        let hex_str l = function _ -> Reporting.unreachable l __POS__ "hex_str"

        let hex_str_upper l = function _ -> Reporting.unreachable l __POS__ "hex_str_upper"

        let count_leading_zeros l = function _ -> Reporting.unreachable l __POS__ "count_leading_zeros"

        let fvector_store l _ _ = "store"

        let is_empty l = function _ -> Reporting.unreachable l __POS__ "is_empty"

        let hd l = function _ -> Reporting.unreachable l __POS__ "hd"

        let tl l = function _ -> Reporting.unreachable l __POS__ "tl"
      end)

  let ( let* ) = Smt_gen.bind
  let return = Smt_gen.return
  let mapM = Smt_gen.mapM

  let rec sequence = function
    | x :: xs ->
        let* y = x in
        let* ys = sequence xs in
        return (y :: ys)
    | [] -> return []

  let smt_unit = mk_enum "Unit" ["Unit"]
  let smt_lbits =
    mk_record "Bits" [("len", Bitvec lbits_index_width); ("bits", Bitvec Config.max_unknown_bitvector_width)]

  let rec wf_smt_ctyp = function CT_lbits -> Some (fun exp -> Smt.wf_lbits exp) | _ -> None

  let rec smt_ctyp = function
    | CT_constant n -> return (Bitvec (required_width n))
    | CT_fint n -> return (Bitvec n)
    | CT_lint -> return (Bitvec Config.max_unknown_integer_width)
    | CT_unit -> return smt_unit
    | CT_bit -> return (Bitvec 1)
    | CT_fbits n -> return (Bitvec n)
    | CT_sbits n -> return smt_lbits
    | CT_lbits -> return smt_lbits
    | CT_bool -> return Bool
    | CT_enum (id, elems) -> return (mk_enum (zencode_upper_id id) (List.map zencode_id elems))
    | CT_struct (id, fields) ->
        let* fields =
          mapM
            (fun (id, ctyp) ->
              let* ctyp = smt_ctyp ctyp in
              return (zencode_id id, ctyp)
            )
            fields
        in
        return (mk_record (zencode_upper_id id) fields)
    | CT_variant (id, ctors) ->
        let* ctors =
          mapM
            (fun (id, ctyp) ->
              let* ctyp = smt_ctyp ctyp in
              return (zencode_id id, ctyp)
            )
            ctors
        in
        return (mk_variant (zencode_upper_id id) ctors)
    | CT_fvector (n, ctyp) ->
        let* ctyp = smt_ctyp ctyp in
        return (Array (Bitvec (required_width (Big_int.of_int (n - 1)) - 1), ctyp))
    | CT_vector ctyp ->
        let* ctyp = smt_ctyp ctyp in
        return (Array (Bitvec vector_index_width, ctyp))
    | CT_string ->
        let* _ = Smt_gen.string_used in
        return String
    | CT_real ->
        let* _ = Smt_gen.real_used in
        return Real
    | CT_ref ctyp -> begin
        match CTMap.find_opt ctyp Config.register_map with
        | Some regs -> return (Bitvec (required_width (Big_int.of_int (List.length regs))))
        | _ ->
            let* l = Smt_gen.current_location in
            Reporting.unreachable l __POS__ ("No registers with ctyp: " ^ string_of_ctyp ctyp)
      end
    | CT_list _ ->
        let* l = Smt_gen.current_location in
        raise (Reporting.err_todo l "Lists not yet supported in SMT generation")
    | CT_float _ | CT_rounding_mode ->
        let* l = Smt_gen.current_location in
        Reporting.unreachable l __POS__ "Floating point in SMT property"
    | CT_tup _ ->
        let* l = Smt_gen.current_location in
        Reporting.unreachable l __POS__ "Tuples should be re-written before SMT generation"
    | CT_poly _ ->
        let* l = Smt_gen.current_location in
        Reporting.unreachable l __POS__ "Found polymorphic type in SMT property"

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

     (define-const v/o (ite cond_1 v/n v/m))
  *)
  let smt_ssanode cfg preds =
    let open Jib_ssa in
    function
    | Pi _ -> return []
    | Phi (id, ctyp, ids) -> (
        let get_pi n =
          match get_vertex cfg n with
          | Some ((ssa_elems, _), _, _) -> List.concat (List.map (function Pi guards -> guards | _ -> []) ssa_elems)
          | None -> failwith "Predecessor node does not exist"
        in
        let pis = List.map get_pi (IntSet.elements preds) in
        let* mux =
          List.fold_right2
            (fun pi id chain ->
              let* chain = chain in
              let* pi = mapM Smt.smt_cval pi in
              let pathcond = smt_conj pi in
              match chain with Some smt -> return (Some (Ite (pathcond, Var id, smt))) | None -> return (Some (Var id))
            )
            pis ids (return None)
        in
        let* ctyp = smt_ctyp ctyp in
        match mux with None -> assert false | Some mux -> return [Define_const (id, ctyp, mux)]
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
  let rec get_pathcond n cfg =
    let open Jib_ssa in
    let get_pi m =
      match get_vertex cfg m with
      | Some ((ssa_elems, _), _, _) ->
          V_call (Band, List.concat (List.map (function Pi guards -> guards | _ -> []) ssa_elems))
      | None -> failwith "Node does not exist"
    in
    match get_vertex cfg n with
    | Some ((_, CF_guard cond), _, _) -> Smt.smt_cval (get_pi n)
    | Some (_, preds, succs) ->
        if IntSet.cardinal preds = 0 then return (Bool_lit true)
        else if IntSet.cardinal preds = 1 then get_pathcond (IntSet.min_elt preds) cfg
        else (
          let pis = List.map get_pi (IntSet.elements preds) in
          Smt.smt_cval (V_call (Bor, pis))
        )
    | None -> assert false (* Should never be called for a non-existent node *)

  let add_event state ev smt =
    let stack = event_stack state ev in
    let* pathcond = get_pathcond state.node state.cfg in
    Stack.push (Fn ("and", [pathcond; smt])) stack;
    return ()

  let add_pathcond_event state ev =
    let* pathcond = get_pathcond state.node state.cfg in
    Stack.push pathcond (event_stack state ev);
    return ()

  let define_const id ctyp exp =
    let* ty = smt_ctyp ctyp in
    return (Define_const (id, ty, exp))

  let declare_const id ctyp =
    let* ty = smt_ctyp ctyp in
    return (Declare_const (id, ty))

  let singleton = Smt_gen.fmap (fun x -> [x])

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

  let rmw_read = function CL_rmw (read, _, _) -> read | _ -> assert false

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
                if Id.compare field field' = 0 then smt else Field (struct_id, field', Var (rmw_read clexp))
              in
              Fn (zencode_upper_id struct_id, List.map set_field fields)
          | _ -> failwith "Struct modify does not have struct type"
        end
    | _ -> assert false

  let builtin_sqrt_real root v =
    let* smt = Smt.smt_cval v in
    return
      [
        Declare_const (root, Real);
        Assert (Fn ("and", [Fn ("=", [smt; Fn ("*", [Var root; Var root])]); Fn (">=", [Var root; Real_lit "0.0"])]));
      ]

  (* For a basic block (contained in a control-flow node / cfnode), we
     turn the instructions into a sequence of define-const and
     declare-const expressions. Because we are working with a SSA graph,
     each variable is guaranteed to only be declared once.
  *)
  let smt_instr state ctx (I_aux (aux, (_, l)) as instr) =
    let open Type_check in
    match aux with
    | I_funcall (CR_one (CL_id (id, ret_ctyp)), extern, (function_id, _), args) ->
        if ctx_is_extern function_id ctx then (
          let name = ctx_get_extern function_id ctx in
          if name = "sail_assert" then (
            match args with
            | [assertion; _] ->
                let* smt = Smt.smt_cval assertion in
                let* _ = add_event state Assertion (Fn ("not", [smt])) in
                return []
            | _ -> Reporting.unreachable l __POS__ "Bad arguments for assertion"
          )
          else if name = "sail_assume" then (
            match args with
            | [assumption] ->
                let* smt = Smt.smt_cval assumption in
                let* _ = add_event state Assumption smt in
                return []
            | _ -> Reporting.unreachable l __POS__ "Bad arguments for assertion"
          )
          else if name = "sqrt_real" then (
            match args with
            | [v] -> builtin_sqrt_real id v
            | _ -> Reporting.unreachable l __POS__ "Bad arguments for sqrt_real"
          )
          else (
            match Smt.builtin ~allow_io:false name with
            | Some generator ->
                let* value = generator args ret_ctyp in
                singleton (define_const id ret_ctyp value)
            | None -> failwith ("No generator " ^ string_of_id function_id)
          )
        )
        else if extern && string_of_id function_id = "internal_vector_init" then singleton (declare_const id ret_ctyp)
        else if extern && string_of_id function_id = "internal_vector_update" then begin
          match args with
          | [vec; i; x] ->
              let sz = required_width (Big_int.of_int (Smt.generic_vector_length (cval_ctyp vec) - 1)) - 1 in
              let* vec = Smt.smt_cval vec in
              let* i =
                Smt_gen.bind (Smt.smt_cval i) (Smt_gen.unsigned_size ~into:sz ~from:(Smt.int_size (cval_ctyp i)))
              in
              let* x = Smt.smt_cval x in
              singleton (define_const id ret_ctyp (Fn ("store", [vec; i; x])))
          | _ -> Reporting.unreachable l __POS__ "Bad arguments for internal_vector_update"
        end
        else if not extern then
          let* smt_args = mapM Smt.smt_cval args in
          singleton (define_const id ret_ctyp (Fn (zencode_id function_id, smt_args)))
        else failwith ("Unrecognised function " ^ string_of_id function_id)
    | I_init (ctyp, id, cval) | I_copy (CL_id (id, ctyp), cval) ->
        let* cval_smt = Smt.smt_cval cval in
        let* converted_smt = Smt.smt_conversion ~into:ctyp ~from:(cval_ctyp cval) cval_smt in
        singleton (define_const id ctyp converted_smt)
    | I_copy (clexp, cval) ->
        let* smt = Smt.smt_cval cval in
        let write, ctyp = rmw_write clexp in
        singleton (define_const write ctyp (rmw_modify smt clexp))
    | I_decl (ctyp, id) -> begin
        begin
          match l with Unique (n, _) -> Stack.push (n, zencode_name id) state.arg_stack | _ -> ()
        end;
        let* ty = smt_ctyp ctyp in
        let wf_pred = wf_smt_ctyp ctyp in
        match wf_pred with
        | Some p -> return [Declare_const (id, ty); Assert (p (Var id))]
        | None -> return [Declare_const (id, ty)]
      end
    | I_clear _ -> return []
    (* Should only appear as terminators for basic blocks. *)
    | I_jump _ | I_goto _ | I_end _ | I_exit _ | I_undefined _ ->
        Reporting.unreachable l __POS__ "SMT: Instruction should only appear as block terminator"
    | _ -> Reporting.unreachable l __POS__ (string_of_instr instr)

  let generate_reg_decs inits cdefs =
    let rec go acc = function
      | CDEF_aux (CDEF_register (id, ctyp, _), _) :: cdefs when not (NameMap.mem (Name (id, 0)) inits) ->
          let* smt_typ = smt_ctyp ctyp in
          go (Declare_const (Name (id, 0), smt_typ) :: acc) cdefs
      | _ :: cdefs -> go acc cdefs
      | [] -> return (List.rev acc)
    in
    go [] cdefs

  let smt_terminator ctx state =
    let open Jib_ssa in
    function
    | T_end id -> add_event state Return (Var id)
    | T_exit _ -> add_pathcond_event state Match
    | T_undefined _ | T_goto _ | T_jump _ | T_label _ | T_none -> return ()

  let smt_cfnode all_cdefs ctx state =
    let open Jib_ssa in
    function
    | CF_start inits ->
        let* smt_reg_decs = generate_reg_decs inits all_cdefs in
        let smt_start (id, ctyp) =
          match id with Have_exception _ -> define_const id ctyp (Bool_lit false) | _ -> declare_const id ctyp
        in
        let* smt_inits = mapM smt_start (NameMap.bindings inits) in
        return (smt_reg_decs @ smt_inits)
    | CF_block (instrs, terminator) ->
        let* smt_instrs = mapM (smt_instr state ctx) instrs in
        let* _ = smt_terminator ctx state terminator in
        return (List.concat smt_instrs)
    (* We can ignore any non basic-block/start control-flow nodes *)
    | _ -> return []

  let smt_ctype_def = function
    | CTD_enum (id, elems) -> return (declare_datatypes (mk_enum (zencode_upper_id id) (List.map zencode_id elems)))
    | CTD_struct (id, fields) ->
        let* fields =
          mapM
            (fun (field, ctyp) ->
              let* smt_typ = smt_ctyp ctyp in
              return (zencode_upper_id id ^ "_" ^ zencode_id field, smt_typ)
            )
            fields
        in
        return (declare_datatypes (mk_record (zencode_upper_id id) fields))
    | CTD_variant (id, ctors) ->
        let* ctors =
          mapM
            (fun (ctor, ctyp) ->
              let* smt_typ = smt_ctyp ctyp in
              return (zencode_id ctor, smt_typ)
            )
            ctors
        in
        return (declare_datatypes (mk_variant (zencode_upper_id id) ctors))

  let rec generate_ctype_defs acc = function
    | CDEF_aux (CDEF_type ctd, _) :: cdefs ->
        let* smt_type_def = smt_ctype_def ctd in
        generate_ctype_defs (smt_type_def :: acc) cdefs
    | _ :: cdefs -> generate_ctype_defs acc cdefs
    | [] -> return (List.rev acc)

  (* [smt_header ctx cdefs] produces a list of smt definitions for all
     the datatypes in a specification *)
  let smt_header cdefs =
    let* smt_type_defs = generate_ctype_defs [] cdefs in
    return
      ([declare_datatypes (mk_enum "Unit" ["unit"])]
      @ [
          declare_datatypes
            (mk_record "Bits"
               [("len", Bitvec lbits_index_width); ("contents", Bitvec Config.max_unknown_bitvector_width)]
            );
        ]
      @ smt_type_defs
      )

  let dump_graph name cfg =
    let gv_file = name ^ ".gv" in
    prerr_endline Util.("Dumping graph: " ^ gv_file |> bold |> yellow |> clear);
    let out_chan = open_out gv_file in
    Jib_ssa.make_dot out_chan cfg;
    close_out out_chan

  let debug_attr_skip_graph attr =
    Option.value ~default:false
      (let open Util.Option_monad in
       let* _, attr_data = attr in
       let* obj = Option.bind attr_data attribute_data_object in
       let* skip_graph = List.assoc_opt "skip_graph" obj in
       attribute_data_bool skip_graph
      )

  let push_smt_defs stack smt_defs = List.iter (fun def -> Stack.push def stack) smt_defs

  let smt_instr_list debug_attr name ctx all_cdefs instrs =
    let stack = Stack.create () in

    let open Jib_ssa in
    let start, _, cfg = ssa ?debug_prefix:(Option.map (fun _ -> name) debug_attr) instrs in
    let visit_order =
      try topsort cfg
      with Not_a_DAG n ->
        dump_graph name cfg;
        raise
          (Reporting.err_general Parse_ast.Unknown
             (Printf.sprintf "%s: control flow graph is not acyclic (node %d is in cycle)\nWrote graph to %s.gv" name n
                name
             )
          )
    in
    if Option.is_some debug_attr && not (debug_attr_skip_graph debug_attr) then dump_graph name cfg;

    let state = { events = ref EventMap.empty; cfg; node = -1; arg_stack = Stack.create () } in

    List.iter
      (fun n ->
        match get_vertex cfg n with
        | None -> ()
        | Some ((ssa_elems, cfnode), preds, succs) ->
            let pathcond, checks =
              Smt_gen.run
                (let* muxers = Smt_gen.fmap List.concat (mapM (smt_ssanode cfg preds) ssa_elems) in
                 let state = { state with node = n } in
                 let* basic_block = smt_cfnode all_cdefs ctx state cfnode in
                 push_smt_defs stack muxers;
                 push_smt_defs stack basic_block;
                 get_pathcond state.node state.cfg
                )
                Parse_ast.Unknown
            in
            if not Config.ignore_overflow then (
              let overflow_stack = event_stack state Overflow in
              List.iter
                (fun overflow_smt -> Stack.push (Fn ("and", [pathcond; overflow_smt])) overflow_stack)
                (Smt_gen.get_overflows checks)
            )
      )
      visit_order;

    return (stack, state)

  (** When we generate a property for a CDEF_val, we find it's
   associated function body in a CDEF_fundef node. However, we must
   keep track of any global letbindings between the spec and the
   fundef, so they can appear in the generated SMT. *)
  let rec find_function lets id = function
    | CDEF_aux (CDEF_fundef (id', heap_return, args, body), def_annot) :: _ when Id.compare id id' = 0 ->
        (lets, Some (heap_return, args, body, def_annot))
    | CDEF_aux (CDEF_let (_, vars, setup), _) :: cdefs ->
        let vars = List.map (fun (id, ctyp) -> idecl (id_loc id) ctyp (name id)) vars in
        find_function (lets @ vars @ setup) id cdefs
    | _ :: cdefs -> find_function lets id cdefs
    | [] -> (lets, None)

  let rec smt_query state = function
    | Q_all ev ->
        let stack = event_stack state ev in
        smt_conj (Stack.fold (fun xs x -> x :: xs) [] stack)
    | Q_exist ev ->
        let stack = event_stack state ev in
        smt_disj (Stack.fold (fun xs x -> x :: xs) [] stack)
    | Q_not q -> Fn ("not", [smt_query state q])
    | Q_and qs -> smt_conj (List.map (smt_query state) qs)
    | Q_or qs -> smt_disj (List.map (smt_query state) qs)

  type generated_smt_info = {
    file_name : string;
    function_id : id;
    args : id list;
    arg_ctyps : ctyp list;
    arg_smt_names : (id * string option) list;
  }

  let smt_cdef props lets name_file ctx all_cdefs smt_includes (CDEF_aux (aux, def_annot)) =
    match aux with
    | CDEF_val (function_id, _, arg_ctyps, ret_ctyp) when Bindings.mem function_id props -> begin
        match find_function [] function_id all_cdefs with
        | intervening_lets, Some (None, args, instrs, function_def_annot) ->
            let debug_attr = get_def_attribute "jib_debug" function_def_annot in
            let prop_type, prop_args, pragma_l, vs = Bindings.find function_id props in

            let pragma = Property.parse_pragma pragma_l prop_args in

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
              (* |> List.map (map_instr (expand_reg_deref ctx.tc_env Config.register_map)) *)
              |> flatten_instrs
              |> remove_unused_labels |> remove_pointless_goto
            in

            if Option.is_some debug_attr then (
              prerr_endline Util.("Pre-SMT IR for " ^ string_of_id function_id ^ ":" |> yellow |> bold |> clear);
              List.iter (fun instr -> prerr_endline (string_of_instr instr)) instrs
            );

            let (stack, state), _ =
              Smt_gen.run (smt_instr_list debug_attr (string_of_id function_id) ctx all_cdefs instrs) pragma_l
            in

            let query = smt_query state pragma.query in
            push_smt_defs stack [Assert (Fn ("not", [query]))];

            let fname = name_file (string_of_id function_id) in
            let out_chan = open_out fname in
            if prop_type = "counterexample" then output_string out_chan "(set-option :produce-models true)\n";

            let header, _ = Smt_gen.run (smt_header all_cdefs) pragma_l in
            List.iter
              (fun def ->
                output_string out_chan (string_of_smt_def def);
                output_string out_chan "\n"
              )
              header;

            (* Include custom SMT definitions. *)
            List.iter (fun include_file -> output_string out_chan (Util.read_whole_file include_file)) smt_includes;

            let queue = Queue_optimizer.optimize stack in

            (* let queue = Queue.of_seq (List.to_seq (List.rev (List.of_seq (Stack.to_seq stack)))) in *)
            Queue.iter
              (fun def ->
                output_string out_chan (string_of_smt_def def);
                output_string out_chan "\n"
              )
              queue;

            output_string out_chan "(check-sat)\n";
            if prop_type = "counterexample" then output_string out_chan "(get-model)\n";

            close_out out_chan;
            let arg_names = Stack.fold (fun m (k, v) -> (k, v) :: m) [] state.arg_stack in
            let arg_smt_names =
              List.map
                (function
                  | I_aux (I_decl (_, Name (id, _)), (_, Unique (n, _))) -> (id, List.assoc_opt n arg_names)
                  | _ -> assert false
                  )
                arg_decls
            in
            Some { file_name = fname; function_id; args; arg_ctyps; arg_smt_names }
        | _ ->
            let _, _, pragma_l, _ = Bindings.find function_id props in
            raise (Reporting.err_general pragma_l "No function body found")
      end
    | _ -> None

  let rec smt_cdefs acc props lets name_file ctx all_cdefs smt_includes = function
    | CDEF_aux (CDEF_let (_, vars, setup), _) :: cdefs ->
        let vars = List.map (fun (id, ctyp) -> idecl (id_loc id) ctyp (name id)) vars in
        smt_cdefs acc props (lets @ vars @ setup) name_file ctx all_cdefs smt_includes cdefs
    | cdef :: cdefs -> begin
        match smt_cdef props lets name_file ctx all_cdefs smt_includes cdef with
        | Some generation_info ->
            smt_cdefs (generation_info :: acc) props lets name_file ctx all_cdefs smt_includes cdefs
        | None -> smt_cdefs acc props lets name_file ctx all_cdefs smt_includes cdefs
      end
    | [] -> acc

  (* For generating SMT when we have a reg_deref(r : register(t))
     function, we have to expand it into a if-then-else cascade that
     checks if r is any one of the registers with type t, and reads that
     register if it is. We also do a similar thing for *r = x
  *)
  class expand_reg_deref_visitor env : jib_visitor =
    object
      inherit empty_jib_visitor

      method! vcval _ = SkipChildren
      method! vctyp _ = SkipChildren
      method! vclexp _ = SkipChildren

      method! vinstr =
        function
        | I_aux (I_funcall (CR_one (CL_addr (CL_id (id, ctyp))), false, function_id, args), (_, l)) -> begin
            match ctyp with
            | CT_ref reg_ctyp -> begin
                match CTMap.find_opt reg_ctyp Config.register_map with
                | Some regs ->
                    let end_label = label "end_reg_write_" in
                    let try_reg r =
                      let next_label = label "next_reg_write_" in
                      [
                        ijump l (V_call (Neq, [V_lit (VL_ref (string_of_id r), reg_ctyp); V_id (id, ctyp)])) next_label;
                        ifuncall l (CL_id (name r, reg_ctyp)) function_id args;
                        igoto end_label;
                        ilabel next_label;
                      ]
                    in
                    ChangeTo (iblock (List.concat (List.map try_reg regs) @ [ilabel end_label]))
                | None ->
                    raise (Reporting.err_general l ("Could not find any registers with type " ^ string_of_ctyp reg_ctyp))
              end
            | _ ->
                raise
                  (Reporting.err_general l "Register reference assignment must take a register reference as an argument")
          end
        | I_aux (I_funcall (CR_one clexp, false, function_id, [reg_ref]), (_, l)) as instr ->
            let open Type_check in
            begin
              match
                if Env.is_extern (fst function_id) env "smt" then Some (Env.get_extern (fst function_id) env "smt")
                else None
              with
              | Some "reg_deref" -> begin
                  match cval_ctyp reg_ref with
                  | CT_ref reg_ctyp -> begin
                      (* Not find all the registers with this ctyp *)
                      match CTMap.find_opt reg_ctyp Config.register_map with
                      | Some regs ->
                          let end_label = label "end_reg_deref_" in
                          let try_reg r =
                            let next_label = label "next_reg_deref_" in
                            [
                              ijump l (V_call (Neq, [V_lit (VL_ref (string_of_id r), reg_ctyp); reg_ref])) next_label;
                              icopy l clexp (V_id (name r, reg_ctyp));
                              igoto end_label;
                              ilabel next_label;
                            ]
                          in
                          ChangeTo (iblock (List.concat (List.map try_reg regs) @ [ilabel end_label]))
                      | None ->
                          raise
                            (Reporting.err_general l
                               ("Could not find any registers with type " ^ string_of_ctyp reg_ctyp)
                            )
                    end
                  | _ ->
                      raise
                        (Reporting.err_general l "Register dereference must have a register reference as an argument")
                end
              | _ -> SkipChildren
            end
        | I_aux (I_copy (CL_addr (CL_id (id, ctyp)), cval), (_, l)) -> begin
            match ctyp with
            | CT_ref reg_ctyp -> begin
                match CTMap.find_opt reg_ctyp Config.register_map with
                | Some regs ->
                    let end_label = label "end_reg_write_" in
                    let try_reg r =
                      let next_label = label "next_reg_write_" in
                      [
                        ijump l (V_call (Neq, [V_lit (VL_ref (string_of_id r), reg_ctyp); V_id (id, ctyp)])) next_label;
                        icopy l (CL_id (name r, reg_ctyp)) cval;
                        igoto end_label;
                        ilabel next_label;
                      ]
                    in
                    ChangeTo (iblock (List.concat (List.map try_reg regs) @ [ilabel end_label]))
                | None ->
                    raise (Reporting.err_general l ("Could not find any registers with type " ^ string_of_ctyp reg_ctyp))
              end
            | _ ->
                raise
                  (Reporting.err_general l "Register reference assignment must take a register reference as an argument")
          end
        | _ -> DoChildren
    end

  let generate_smt ~properties ~name_file ~smt_includes ctx cdefs =
    let cdefs = visit_cdefs (new expand_reg_deref_visitor ctx.tc_env) cdefs in
    smt_cdefs [] properties [] name_file ctx cdefs smt_includes cdefs
end

module CompileConfig (Opts : sig
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
    | Typ_app (id, [A_aux (A_nexp n, _); A_aux (A_typ typ, _)]) when string_of_id id = "vector" -> begin
        match nexp_simp n with
        | Nexp_aux (Nexp_constant c, _) -> CT_fvector (Big_int.to_int c, convert_typ ctx typ)
        | _ -> CT_vector (convert_typ ctx typ)
      end
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

  let smt_literals ctx =
    let rec smt_literal annot = function
      | AV_lit (lit, typ) as v -> begin match literal_to_cval lit with Some cval -> AV_cval (cval, typ) | None -> v end
      | AV_tuple avals -> AV_tuple (List.map (smt_literal annot) avals)
      | v -> v
    in
    map_aval smt_literal

  (* If we know the loop variables exactly (especially after
     specialization), we can unroll the exact number of times required,
     and omit any comparisons. *)
  let unroll_static_foreach ctx = function
    | AE_aux (AE_for (id, from_aexp, to_aexp, by_aexp, order, body), annot) as aexp -> begin
        match
          ( convert_typ ctx (aexp_typ from_aexp),
            convert_typ ctx (aexp_typ to_aexp),
            convert_typ ctx (aexp_typ by_aexp),
            order
          )
        with
        | CT_constant f, CT_constant t, CT_constant b, Ord_aux (Ord_inc, _) ->
            let new_annot = { annot with loc = gen_loc annot.loc; uannot = empty_uannot } in
            let i = ref f in
            let unrolled = ref [] in
            while Big_int.less_equal !i t do
              let current_index =
                AE_aux (AE_val (AV_lit (L_aux (L_num !i, gen_loc annot.loc), atom_typ (nconstant !i))), new_annot)
              in
              let iteration =
                AE_aux (AE_let (Immutable, id, atom_typ (nconstant !i), current_index, body, unit_typ), new_annot)
              in
              unrolled := iteration :: !unrolled;
              i := Big_int.add !i b
            done;
            begin
              match !unrolled with
              | last :: iterations ->
                  AE_aux (AE_block (List.rev iterations, last, unit_typ), { annot with loc = gen_loc annot.loc })
              | [] -> AE_aux (AE_val (AV_lit (L_aux (L_unit, gen_loc annot.loc), unit_typ)), new_annot)
            end
        | _ -> aexp
      end
    | aexp -> aexp

  let rec is_pure_aexp ctx (AE_aux (aexp, { uannot; _ })) =
    match get_attribute "anf_pure" uannot with
    | Some _ -> true
    | None -> (
        match aexp with
        | AE_app (f, _, _) -> Effects.function_is_pure f ctx.effect_info
        | AE_let (Immutable, _, _, aexp1, aexp2, _) -> is_pure_aexp ctx aexp1 && is_pure_aexp ctx aexp2
        | AE_val _ -> true
        | _ -> false
      )

  (* Map over all the functions in an aexp. *)
  let rec analyze ctx (AE_aux (aexp, ({ env; uannot; loc } as annot))) =
    let ctx = { ctx with local_env = env } in
    let aexp, annot =
      match aexp with
      | AE_typ (aexp, typ) -> (AE_typ (analyze ctx aexp, typ), annot)
      | AE_assign (alexp, aexp) -> (AE_assign (alexp, analyze ctx aexp), annot)
      | AE_short_circuit (op, aval, aexp) -> (AE_short_circuit (op, aval, analyze ctx aexp), annot)
      | AE_let (mut, id, typ1, aexp1, (AE_aux (_, { env = env2; _ }) as aexp2), typ2) ->
          let aexp1 = analyze ctx aexp1 in
          (* Use aexp2's environment because it will contain constraints for id *)
          let ctyp1 = convert_typ { ctx with local_env = env2 } typ1 in
          let ctx = { ctx with locals = Bindings.add id (mut, ctyp1) ctx.locals } in
          (AE_let (mut, id, typ1, aexp1, analyze ctx aexp2, typ2), annot)
      | AE_block (aexps, aexp, typ) -> (AE_block (List.map (analyze ctx) aexps, analyze ctx aexp, typ), annot)
      | AE_if (aval, aexp1, aexp2, typ) ->
          let aexp1 = analyze ctx aexp1 in
          let aexp2 = analyze ctx aexp2 in
          let annot =
            if is_pure_aexp ctx aexp1 && is_pure_aexp ctx aexp2 then
              { annot with uannot = add_attribute (gen_loc loc) "anf_pure" None uannot }
            else annot
          in
          (AE_if (aval, aexp1, aexp2, typ), annot)
      | AE_loop (loop_typ, aexp1, aexp2) -> (AE_loop (loop_typ, analyze ctx aexp1, analyze ctx aexp2), annot)
      | AE_for (id, aexp1, aexp2, aexp3, order, aexp4) ->
          let aexp1 = analyze ctx aexp1 in
          let aexp2 = analyze ctx aexp2 in
          let aexp3 = analyze ctx aexp3 in
          (* Currently we assume that loop indexes are always safe to put into an int64 *)
          let ctx = { ctx with locals = Bindings.add id (Immutable, CT_fint 64) ctx.locals } in
          let aexp4 = analyze ctx aexp4 in
          (AE_for (id, aexp1, aexp2, aexp3, order, aexp4), annot)
      | AE_match (aval, cases, typ) ->
          let analyze_case ((AP_aux (_, env, _) as pat), aexp1, aexp2) =
            let pat_bindings = Bindings.bindings (apat_types pat) in
            let ctx = { ctx with local_env = env } in
            let ctx =
              List.fold_left
                (fun ctx (id, typ) -> { ctx with locals = Bindings.add id (Immutable, convert_typ ctx typ) ctx.locals })
                ctx pat_bindings
            in
            (pat, analyze ctx aexp1, analyze ctx aexp2)
          in
          (AE_match (aval, List.map analyze_case cases, typ), annot)
      | AE_try (aexp, cases, typ) ->
          ( AE_try
              ( analyze ctx aexp,
                List.map (fun (pat, aexp1, aexp2) -> (pat, analyze ctx aexp1, analyze ctx aexp2)) cases,
                typ
              ),
            annot
          )
      | (AE_field _ | AE_struct_update _ | AE_val _ | AE_return _ | AE_exit _ | AE_throw _ | AE_app _) as v -> (v, annot)
    in
    AE_aux (aexp, annot)

  let optimize_anf ctx aexp = aexp |> analyze ctx |> smt_literals ctx |> fold_aexp (unroll_static_foreach ctx)

  let make_call_precise _ _ = false
  let ignore_64 = true
  let unroll_loops = Some Opts.unroll_limit
  let struct_value = true
  let tuple_value = false
  let use_real = true
  let branch_coverage = None
  let track_throw = false
  let use_void = false
end

(* In order to support register references, we need to build a map
   from each ctyp to a list of registers with that ctyp, then when we
   see a type like register(bits(32)) we can use the map to figure out
   all the registers that such a reference could be pointing to.
*)
let rec build_register_map rmap = function
  | CDEF_aux (CDEF_register (reg, ctyp, _), _) :: cdefs ->
      let rmap =
        match CTMap.find_opt ctyp rmap with
        | Some regs -> CTMap.add ctyp (reg :: regs) rmap
        | None -> CTMap.add ctyp [reg] rmap
      in
      build_register_map rmap cdefs
  | _ :: cdefs -> build_register_map rmap cdefs
  | [] -> rmap

let compile ~unroll_limit env effect_info ast =
  let cdefs, jib_ctx =
    let module Jibc = Jib_compile.Make (CompileConfig (struct
      let unroll_limit = unroll_limit
    end)) in
    let env, effect_info = Jib_compile.add_special_functions env effect_info in
    let ctx = Jib_compile.initial_ctx env effect_info in
    let t = Profile.start () in
    let cdefs, ctx = Jibc.compile_ast ctx ast in
    let cdefs, ctx = Jib_optimize.remove_tuples cdefs ctx in
    let cdefs = Jib_optimize.unique_per_function_ids cdefs in
    Profile.finish "Compiling to Jib IR" t;
    (cdefs, ctx)
  in
  let register_map = build_register_map CTMap.empty cdefs in
  (cdefs, jib_ctx, register_map)
