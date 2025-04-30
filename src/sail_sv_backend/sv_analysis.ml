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
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

open Libsail

open Ast
open Ast_util
open Jib
open Jib_compile
open Jib_util
open Jib_visitor

open Sv_attribute

module IntSet = Util.IntSet
module IntMap = Util.IntMap

(* The direct footprint contains information about the effects
   directly performed by the function itself, i.e. not those from any
   transitive function calls. It is constructed by the footprint
   visitor below as it scans the body of the function. *)
type direct_footprint = {
  mutable reads : NameSet.t;
  mutable writes : NameSet.t;
  mutable throws : bool;
  mutable stdout : bool;
  mutable stderr : bool;
  mutable reads_mem : bool;
  mutable writes_mem : bool;
  mutable contains_assert : bool;
  mutable references : CTSet.t;
  mutable exits : bool;
}

let empty_direct_footprint () : direct_footprint =
  {
    reads = NameSet.empty;
    writes = NameSet.empty;
    throws = false;
    stdout = false;
    stderr = false;
    reads_mem = false;
    writes_mem = false;
    contains_assert = false;
    references = CTSet.empty;
    exits = false;
  }

class footprint_visitor ctx registers (footprint : direct_footprint) : jib_visitor =
  object
    inherit empty_jib_visitor

    method! vctyp _ = SkipChildren

    method! vcval =
      function
      | V_id (id, local_ctyp) ->
          begin
            match NameMap.find_opt id registers with
            | Some (ctyp, _) ->
                assert (ctyp_equal local_ctyp ctyp);
                footprint.reads <- NameSet.add id footprint.reads
            | None -> ()
          end;
          SkipChildren
      | _ -> DoChildren

    method! vinstr =
      function
      | I_aux (I_exit _, _) ->
          footprint.exits <- true;
          SkipChildren
      | I_aux (I_funcall (_, true, (id, _), args), (l, _)) ->
          let name = string_of_id id in
          if name = "sail_assert" then footprint.contains_assert <- true;
          DoChildren
      | I_aux (I_funcall (_, false, (id, _), args), (l, _)) ->
          let open Util.Option_monad in
          if ctx_is_extern id ctx then (
            let name = ctx_get_extern id ctx in
            Option.value ~default:()
              (let* _, _, _, uannot = Bindings.find_opt id ctx.valspecs in
               let* attr_object =
                 Option.bind (Option.bind (get_attribute "sv_module" uannot) snd) attribute_data_object
               in
               check_attribute "stdout" attr_object (fun () -> footprint.stdout <- true);
               check_attribute "stderr" attr_object (fun () -> footprint.stdout <- true);
               check_attribute "reads_memory" attr_object (fun () -> footprint.reads_mem <- true);
               check_attribute "writes_memory" attr_object (fun () -> footprint.writes_mem <- true);
               Some ()
              );
            if name = "reg_deref" then (
              match args with
              | [cval] -> begin
                  match cval_ctyp cval with
                  | CT_ref reg_ctyp -> footprint.references <- CTSet.add reg_ctyp footprint.references
                  | _ -> ()
                end
              | _ -> ()
            )
          );
          DoChildren
      | _ -> DoChildren

    method! vclexp =
      function
      | CL_addr (CL_id (_, CT_ref ctyp)) ->
          footprint.references <- CTSet.add ctyp footprint.references;
          DoChildren
      | CL_id (Have_exception _, _) ->
          footprint.throws <- true;
          SkipChildren
      | CL_id (id, local_ctyp) ->
          begin
            match NameMap.find_opt id registers with
            | Some (ctyp, _) ->
                assert (ctyp_equal local_ctyp ctyp);
                footprint.writes <- NameSet.add id footprint.writes
            | None -> ()
          end;
          SkipChildren
      | _ -> DoChildren
  end

type footprint = {
  direct_reads : NameSet.t;
  direct_writes : NameSet.t;
  direct_throws : bool;
  all_reads : NameSet.t;
  all_writes : NameSet.t;
  throws : bool;
  need_stdout : bool;
  need_stderr : bool;
  reads_mem : bool;
  writes_mem : bool;
  contains_assert : bool;
  exits : bool;
}

let pure_footprint =
  {
    direct_reads = NameSet.empty;
    direct_writes = NameSet.empty;
    direct_throws = false;
    all_reads = NameSet.empty;
    all_writes = NameSet.empty;
    throws = false;
    need_stdout = false;
    need_stderr = false;
    reads_mem = false;
    writes_mem = false;
    contains_assert = false;
    exits = false;
  }

type spec_info = {
  (* A map from register types to all the registers with that type *)
  register_ctyp_map : NameSet.t CTMap.t;
  (* A map from register names to types *)
  registers : (ctyp * unit def_annot) NameMap.t;
  (* A list of registers with initial values *)
  initialized_registers : name list;
  (* A list of constructor functions *)
  constructors : IdSet.t;
  (* Global letbindings *)
  global_lets : NameSet.t;
  (* Global let numbers *)
  global_let_numbers : Ast.id list IntMap.t;
  (* Function footprint information *)
  footprints : footprint Bindings.t;
  (* Specification callgraph *)
  callgraph : IdGraph.graph;
  (* The type of exceptions *)
  exception_ctyp : ctyp;
}

let collect_spec_info ctx cdefs =
  let register_ctyp_map, registers, initialized_registers =
    List.fold_left
      (fun (ctyp_map, regs, inits) cdef ->
        match cdef with
        | CDEF_aux (CDEF_register (id, ctyp, setup), def_annot) ->
            let setup_id = match setup with [] -> [] | _ -> [id] in
            ( CTMap.update ctyp
                (function Some ids -> Some (NameSet.add id ids) | None -> Some (NameSet.singleton id))
                ctyp_map,
              NameMap.add id (ctyp, def_annot) regs,
              setup_id @ inits
            )
        | _ -> (ctyp_map, regs, inits)
      )
      (CTMap.empty, NameMap.empty, []) cdefs
  in
  let initialized_registers = List.rev initialized_registers in
  let constructors =
    List.fold_left
      (fun acc cdef ->
        match cdef with
        | CDEF_aux (CDEF_type (CTD_variant (_, _, ctors)), _) ->
            List.fold_left (fun acc (id, _) -> IdSet.add id acc) acc ctors
        | _ -> acc
      )
      IdSet.empty cdefs
  in
  let global_lets, global_let_numbers =
    List.fold_left
      (fun (names, nums) cdef ->
        match cdef with
        | CDEF_aux (CDEF_let (n, bindings, _), _) ->
            ( List.fold_left
                (fun acc (id, ctyp) ->
                  Globals.add id ctyp;
                  NameSet.add (name id) acc
                )
                names bindings,
              IntMap.add n (List.map fst bindings) nums
            )
        | _ -> (names, nums)
      )
      (NameSet.empty, IntMap.empty) cdefs
  in
  let footprints =
    List.fold_left
      (fun footprints cdef ->
        match cdef with
        | CDEF_aux (CDEF_fundef (f, _, _, body), _) ->
            let direct_footprint = empty_direct_footprint () in
            let _ = visit_cdef (new footprint_visitor ctx registers direct_footprint) cdef in
            CTSet.iter
              (fun ctyp ->
                NameSet.iter
                  (fun reg -> direct_footprint.writes <- NameSet.add reg direct_footprint.writes)
                  (Option.value ~default:NameSet.empty (CTMap.find_opt ctyp register_ctyp_map))
              )
              direct_footprint.references;
            Bindings.add f
              {
                direct_reads = direct_footprint.reads;
                direct_writes = direct_footprint.writes;
                direct_throws = direct_footprint.throws;
                all_reads = NameSet.empty;
                all_writes = NameSet.empty;
                throws = false;
                need_stdout = direct_footprint.stdout;
                need_stderr = direct_footprint.stderr;
                reads_mem = direct_footprint.reads_mem;
                writes_mem = direct_footprint.writes_mem;
                contains_assert = direct_footprint.contains_assert;
                exits = direct_footprint.exits;
              }
              footprints
        | _ -> footprints
      )
      Bindings.empty cdefs
  in
  let cfg = callgraph cdefs in
  let footprints =
    List.fold_left
      (fun footprints cdef ->
        match cdef with
        | CDEF_aux (CDEF_fundef (f, _, _, body), _) ->
            let footprint = Bindings.find f footprints in
            let callees = cfg |> IdGraph.reachable (IdSet.singleton f) IdSet.empty |> IdSet.remove f in
            let all_reads, all_writes, throws, need_stdout, need_stderr, reads_mem, writes_mem, contains_assert, exits =
              List.fold_left
                (fun ( all_reads,
                       all_writes,
                       throws,
                       need_stdout,
                       need_stderr,
                       reads_mem,
                       writes_mem,
                       contains_assert,
                       exits
                     ) callee ->
                  match Bindings.find_opt callee footprints with
                  | Some footprint ->
                      ( NameSet.union all_reads footprint.direct_reads,
                        NameSet.union all_writes footprint.direct_writes,
                        throws || footprint.direct_throws,
                        need_stdout || footprint.need_stdout,
                        need_stderr || footprint.need_stderr,
                        reads_mem || footprint.reads_mem,
                        writes_mem || footprint.writes_mem,
                        contains_assert || footprint.contains_assert,
                        exits || footprint.exits
                      )
                  | _ ->
                      ( all_reads,
                        all_writes,
                        throws,
                        need_stdout,
                        need_stderr,
                        reads_mem,
                        writes_mem,
                        contains_assert,
                        exits
                      )
                )
                ( footprint.direct_reads,
                  footprint.direct_writes,
                  footprint.direct_throws,
                  footprint.need_stdout,
                  footprint.need_stderr,
                  footprint.reads_mem,
                  footprint.writes_mem,
                  footprint.contains_assert,
                  footprint.exits
                )
                (IdSet.elements callees)
            in
            Bindings.update f
              (fun _ ->
                Some
                  {
                    footprint with
                    all_reads;
                    all_writes;
                    throws;
                    need_stdout;
                    need_stderr;
                    reads_mem;
                    writes_mem;
                    contains_assert;
                    exits;
                  }
              )
              footprints
        | _ -> footprints
      )
      footprints cdefs
  in
  let exception_ctyp =
    List.fold_left
      (fun ctyp cdef ->
        match cdef with
        | CDEF_aux (CDEF_type ctd, _) when Id.compare (ctype_def_id ctd) (mk_id "exception") = 0 ->
            ctype_def_to_ctyp ctd
        | _ -> ctyp
      )
      CT_unit cdefs
  in
  {
    register_ctyp_map;
    registers;
    initialized_registers;
    constructors;
    global_lets;
    global_let_numbers;
    footprints;
    callgraph = cfg;
    exception_ctyp;
  }
