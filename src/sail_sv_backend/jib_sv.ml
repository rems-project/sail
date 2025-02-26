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

open Ast_util
open Jib
open Jib_compile
open Jib_util
open Jib_visitor
open Parse_ast.Attribute_data
open PPrint
open Printf
open Smt_exp

open Generate_primop2
open Sv_ir

module IntSet = Util.IntSet
module IntMap = Util.IntMap

let gensym, _ = symbol_generator "sv"
let ngensym () = name (gensym ())

let sv_type_of_string = Initial_check.parse_from_string (Sv_type_parser.sv_type Sv_type_lexer.token)

let parse_sv_type = function
  | AD_aux (AD_string s, l) ->
      let open Lexing in
      let p =
        match Reporting.simp_loc l with Some (p, _) -> Some { p with pos_cnum = p.pos_cnum + 1 } | None -> None
      in
      let num_opt, ctyp = sv_type_of_string ?inline:p s in
      (l, num_opt, ctyp)
  | AD_aux (_, l) -> raise (Reporting.err_general l "Cannot parse systemverilog type from attribute")

module type ATTRIBUTE_INFO = sig
  val loc : Ast.l
  val attribute_name : string
end

module NullAttributeInfo : ATTRIBUTE_INFO = struct
  let loc = Parse_ast.Unknown
  let attribute_name = "unknown"
end

let get_sv_attribute_from ~getter name annot =
  match getter name annot with
  | Some (l, attr_data_opt) -> (
      let module Info = struct
        let loc = l
        let attribute_name = name
      end in
      match attr_data_opt with
      | None -> (Some [], (module Info : ATTRIBUTE_INFO))
      | Some attr_data -> (
          match attribute_data_object attr_data with
          | Some obj -> (Some obj, (module Info : ATTRIBUTE_INFO))
          | None -> raise (Reporting.err_general l ("Expected key-value pairs on " ^ name ^ " attribute"))
        )
    )
  | None -> (None, (module NullAttributeInfo))

let get_sv_attribute name uannot = get_sv_attribute_from ~getter:get_attribute name uannot
let get_sv_def_attribute name def_annot = get_sv_attribute_from ~getter:get_def_attribute name def_annot

module AttributeParser (Info : ATTRIBUTE_INFO) = struct
  open Util.Option_monad

  let key_type_error ~expected key l =
    Reporting.err_general
      (Hint ("key here", l, Info.loc))
      (Printf.sprintf "Expected %s type for %s in %s attribute" expected key Info.attribute_name)

  let get_bool ~default key obj_opt =
    match obj_opt with
    | None -> default
    | Some obj -> (
        match List.assoc_opt key obj with
        | None -> default
        | Some (AD_aux (AD_bool b, _)) -> b
        | Some (AD_aux (_, l)) -> raise (key_type_error ~expected:"boolean" key l)
      )

  let get_string ~default key obj_opt =
    match obj_opt with
    | None -> default
    | Some obj -> (
        match List.assoc_opt key obj with
        | None -> default
        | Some (AD_aux (AD_string s, _)) -> s
        | Some (AD_aux (_, l)) -> raise (key_type_error ~expected:"string" key l)
      )

  let get_types ~arity obj_opt =
    let* types = Option.bind obj_opt (List.assoc_opt "types") in
    let ctyps =
      match types with
      | AD_aux (AD_string _, _) as s -> [parse_sv_type s]
      | AD_aux (AD_list types, _) -> List.map parse_sv_type types
      | _ -> raise (Reporting.err_general Info.loc "types field must be either a string, or an array of strings")
    in
    if List.for_all (fun (_, num_opt, _) -> Option.is_some num_opt) ctyps then
      Some
        (List.init arity (fun n ->
             let* _, _, ctyp = List.find_opt (fun (_, num_opt, _) -> Option.get num_opt = n) ctyps in
             Some ctyp
         )
        )
    else if List.for_all (fun (_, num_opt, _) -> Option.is_none num_opt) ctyps then
      if List.length ctyps <> arity then
        raise
          (Reporting.err_general Info.loc
             "Number of items of types key must match number of function arguments, unless argument positions are \
              explicit"
          )
      else Some (List.map (fun (_, _, ctyp) -> Some ctyp) ctyps)
    else (
      let l1, _, _ = List.find (fun (_, num_opt, _) -> Option.is_some num_opt) ctyps in
      let l2, _, _ = List.find (fun (_, num_opt, _) -> Option.is_none num_opt) ctyps in
      raise
        (Reporting.err_general
           (Hint ("Non-positional type specified here", l2, l1))
           "Mixed use of types with specified positions and non-specified positions"
        )
    )

  let get_return_type obj_opt =
    let* return_type = Option.bind obj_opt (List.assoc_opt "return_type") in
    let l, num_opt, ctyp =
      match return_type with
      | AD_aux (AD_string _, _) as s -> parse_sv_type s
      | AD_aux (_, l) -> raise (Reporting.err_general l "return_type field must be a string")
    in
    match num_opt with
    | None -> Some ctyp
    | Some _ -> raise (Reporting.err_general l "return_type field should not have positional argument")

  let get_string_set ~default key obj_opt =
    let add_to_set set = function
      | AD_aux (AD_string s, _) -> StringSet.add s set
      | AD_aux (_, l) -> raise (key_type_error ~expected:"string" key l)
    in
    match obj_opt with
    | None -> default
    | Some obj -> (
        match List.assoc_opt key obj with
        | None -> default
        | Some (AD_aux (AD_list xs, _)) -> List.fold_left add_to_set StringSet.empty xs
        | Some (AD_aux (_, l)) -> raise (key_type_error ~expected:"boolean" key l)
      )

  let get_dpi sets obj_opt =
    let* dpi = Option.bind obj_opt (List.assoc_opt "dpi") in
    match dpi with
    | AD_aux (AD_bool b, _) -> Some b
    | AD_aux (AD_string s, _) -> Some (StringSet.mem s sets)
    | AD_aux (_, l) -> raise (Reporting.err_general l "dpi field must be a boolean or string")
end

let get_bool_attribute name attr_object =
  let open Parse_ast.Attribute_data in
  match List.assoc_opt name attr_object with
  | Some (AD_aux (AD_bool true, _)) -> true
  | Some (AD_aux (AD_bool false, _)) | None -> false
  | Some (AD_aux (_, l)) ->
      raise (Reporting.err_general l (Printf.sprintf "Expected boolean for %s key on sv_module attribute" name))

let check_attribute name attr_object f =
  let open Parse_ast.Attribute_data in
  match List.assoc_opt name attr_object with
  | Some (AD_aux (AD_bool true, _)) -> f ()
  | Some (AD_aux (AD_bool false, _)) | None -> ()
  | Some (AD_aux (_, l)) ->
      raise (Reporting.err_general l (Printf.sprintf "Expected boolean for %s key on sv_module attribute" name))

(* The direct footprint contains information about the effects
   directly performed by the function itself, i.e. not those from any
   transitive function calls. It is constructed by the footprint
   visitor below as it scans the body of the function. *)
type direct_footprint = {
  mutable reads : IdSet.t;
  mutable writes : IdSet.t;
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
    reads = IdSet.empty;
    writes = IdSet.empty;
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
      | V_id (Name (id, _), local_ctyp) ->
          begin
            match Bindings.find_opt id registers with
            | Some ctyp ->
                assert (ctyp_equal local_ctyp ctyp);
                footprint.reads <- IdSet.add id footprint.reads
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
      | CL_id (Name (id, _), local_ctyp) ->
          begin
            match Bindings.find_opt id registers with
            | Some ctyp ->
                assert (ctyp_equal local_ctyp ctyp);
                footprint.writes <- IdSet.add id footprint.writes
            | None -> ()
          end;
          SkipChildren
      | _ -> DoChildren
  end

type footprint = {
  direct_reads : IdSet.t;
  direct_writes : IdSet.t;
  direct_throws : bool;
  all_reads : IdSet.t;
  all_writes : IdSet.t;
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
    direct_reads = IdSet.empty;
    direct_writes = IdSet.empty;
    direct_throws = false;
    all_reads = IdSet.empty;
    all_writes = IdSet.empty;
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
  register_ctyp_map : IdSet.t CTMap.t;
  (* A map from register names to types *)
  registers : ctyp Bindings.t;
  (* A list of registers with initial values *)
  initialized_registers : Ast.id list;
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
        | CDEF_aux (CDEF_register (id, ctyp, setup), _) ->
            let setup_id = match setup with [] -> [] | _ -> [id] in
            ( CTMap.update ctyp
                (function Some ids -> Some (IdSet.add id ids) | None -> Some (IdSet.singleton id))
                ctyp_map,
              Bindings.add id ctyp regs,
              setup_id @ inits
            )
        | _ -> (ctyp_map, regs, inits)
      )
      (CTMap.empty, Bindings.empty, []) cdefs
  in
  let initialized_registers = List.rev initialized_registers in
  let constructors =
    List.fold_left
      (fun acc cdef ->
        match cdef with
        | CDEF_aux (CDEF_type (CTD_variant (_, ctors)), _) ->
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
            ( List.fold_left (fun acc (id, _) -> NameSet.add (name id) acc) names bindings,
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
                IdSet.iter
                  (fun reg -> direct_footprint.writes <- IdSet.add reg direct_footprint.writes)
                  (Option.value ~default:IdSet.empty (CTMap.find_opt ctyp register_ctyp_map))
              )
              direct_footprint.references;
            Bindings.add f
              {
                direct_reads = direct_footprint.reads;
                direct_writes = direct_footprint.writes;
                direct_throws = direct_footprint.throws;
                all_reads = IdSet.empty;
                all_writes = IdSet.empty;
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
                      ( IdSet.union all_reads footprint.direct_reads,
                        IdSet.union all_writes footprint.direct_writes,
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

module type CONFIG = sig
  val max_unknown_integer_width : int
  val max_unknown_bitvector_width : int
  val line_directives : bool
  val no_strings : bool
  val no_packed : bool
  val no_assertions : bool
  val never_pack_unions : bool
  val union_padding : bool
  val unreachable : string list
  val comb : bool
  val ignore : string list
  val dpi_sets : StringSet.t
end

module Make (Config : CONFIG) = struct
  let lbits_index_width = required_width (Big_int.of_int (Config.max_unknown_bitvector_width - 1))

  module Primops =
    Generate_primop2.Make
      (struct
        let max_unknown_bitvector_width = Config.max_unknown_bitvector_width
        let max_unknown_integer_width = Config.max_unknown_integer_width
      end)
      ()

  let valid_sv_identifier_regexp : Str.regexp option ref = ref None

  let has_prefix prefix s =
    if String.length s < String.length prefix then false else String.sub s 0 (String.length prefix) = prefix

  let has_bad_prefix s = has_prefix "sail_" s || has_prefix "t_" s || has_prefix "ret_" s

  let valid_sv_identifier s =
    let regexp =
      (* Cache the regexp to avoid compiling it every time *)
      match !valid_sv_identifier_regexp with
      | Some regexp -> regexp
      | None ->
          let regexp = Str.regexp "^[A-Za-z_][A-Za-z0-9_]*$" in
          valid_sv_identifier_regexp := Some regexp;
          regexp
    in
    Str.string_match regexp s 0

  module NameGen =
    Name_generator.Make
      (struct
        type style = unit

        let allowed s =
          valid_sv_identifier s
          && (not (has_bad_prefix s))
          && (not (StringSet.mem s Keywords.sv_reserved_words))
          && not (StringSet.mem s Keywords.sv_used_words)

        let pretty () s = s

        let mangle () s = Util.zencode_string s

        let variant s = function 0 -> s | n -> s ^ string_of_int n

        let overrides = Name_generator.Overrides.empty
      end)
      ()

  let pp_id_string id = NameGen.to_string () id

  let pp_id id = string (pp_id_string id)

  let pp_sv_name_string = function SVN_id id -> pp_id_string id | SVN_string s -> s

  let pp_sv_name = function SVN_id id -> pp_id id | SVN_string s -> string s

  let sv_type_id_string id = NameGen.to_string ~prefix:"t_" () id

  let sv_type_id id = string (sv_type_id_string id)

  let rec bit_width = function
    | CT_unit | CT_bit | CT_bool -> Some 1
    | CT_fbits len -> Some len
    | CT_lbits -> Some Config.max_unknown_bitvector_width
    | CT_enum (_, ids) -> Some (required_width (Big_int.of_int (List.length ids - 1)))
    | CT_constant c -> Some (required_width c)
    | CT_variant (_, ctors) ->
        List.map (fun (_, ctyp) -> bit_width ctyp) ctors |> Util.option_all |> Option.map (List.fold_left max 1)
    | CT_struct (_, fields) ->
        List.map (fun (_, ctyp) -> bit_width ctyp) fields |> Util.option_all |> Option.map (List.fold_left ( + ) 0)
    | _ -> None

  let is_packed ctyp = if Config.no_packed then false else Option.is_some (bit_width ctyp)

  let simple_type str = (str, None)

  let rec sv_ctyp ?(two_state = false) = function
    | CT_bool -> simple_type "bit"
    | CT_bit when two_state -> simple_type "bit"
    | CT_bit -> simple_type "logic"
    | CT_fbits 0 -> simple_type "sail_zwbv"
    | CT_fbits width when two_state -> ksprintf simple_type "bit [%d:0]" (width - 1)
    | CT_fbits width -> ksprintf simple_type "logic [%d:0]" (width - 1)
    | CT_sbits max_width ->
        let logic = sprintf "logic [%d:0]" (max_width - 1) in
        ksprintf simple_type "struct packed { logic [7:0] size; %s bits; }" logic
    | CT_lbits -> simple_type "sail_bits"
    | CT_fint width when two_state -> ksprintf simple_type "bit [%d:0]" (width - 1)
    | CT_fint width -> ksprintf simple_type "logic [%d:0]" (width - 1)
    | CT_lint -> ksprintf simple_type "logic [%d:0]" (Config.max_unknown_integer_width - 1)
    | CT_string -> simple_type (if Config.no_strings then "sail_unit" else "string")
    | CT_unit -> simple_type "sail_unit"
    | CT_variant (id, _) | CT_struct (id, _) | CT_enum (id, _) -> simple_type (sv_type_id_string id)
    | CT_constant c ->
        let width = required_width c in
        if two_state then ksprintf simple_type "bit [%d:0]" (width - 1)
        else ksprintf simple_type "logic [%d:0]" (width - 1)
    | CT_ref ctyp -> ksprintf simple_type "sail_reg_%s" (Util.zencode_string (string_of_ctyp ctyp))
    | CT_fvector (len, ctyp) ->
        let outer_index = sprintf "[%d:0]" (len - 1) in
        begin
          match sv_ctyp ~two_state ctyp with
          | ty, Some inner_index -> (ty, Some (inner_index ^ outer_index))
          | ty, None -> (ty, Some outer_index)
        end
    | CT_list ctyp -> begin
        match sv_ctyp ~two_state ctyp with
        | ty, Some inner_index -> (ty, Some (inner_index ^ "[$]"))
        | ty, None -> (ty, Some "[$]")
      end
    | CT_vector ctyp -> begin
        match sv_ctyp ~two_state ctyp with
        | ty, Some inner_index -> (ty, Some (inner_index ^ "[]"))
        | ty, None -> (ty, Some "[]")
      end
    | CT_real -> simple_type "sail_real"
    | CT_rounding_mode -> simple_type "sail_rounding_mode"
    | CT_float width -> ksprintf simple_type "sail_float%d" width
    | CT_memory_writes -> simple_type "sail_memory_writes"
    | CT_tup _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Tuple type should not reach SV backend"
    | CT_poly _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Polymorphic type should not reach SV backend"
    | CT_json | CT_json_key -> Reporting.unreachable Parse_ast.Unknown __POS__ "JSON type should not reach SV backend"

  module Smt =
    Smt_gen.Make
      (struct
        let max_unknown_integer_width = Config.max_unknown_integer_width
        let max_unknown_bitvector_width = Config.max_unknown_bitvector_width
        let max_unknown_generic_vector_length = 32
        let union_ctyp_classify ctyp = is_packed ctyp && not Config.never_pack_unions
        let register_ref reg_name = Fn ("reg_ref", [String_lit reg_name])
      end)
      (struct
        let print_bits l = function CT_lbits -> "sail_print_bits" | _ -> Reporting.unreachable l __POS__ "print_bits"

        let string_of_bits l = function
          | CT_lbits -> "sail_string_of_bits"
          | CT_fbits sz -> Primops.string_of_fbits sz
          | _ -> Reporting.unreachable l __POS__ "string_of_bits"

        let dec_str _ = Primops.dec_str

        let hex_str _ = Primops.hex_str

        let hex_str_upper _ = Primops.hex_str_upper

        let count_leading_zeros l _ = Reporting.unreachable l __POS__ "count_leading_zeros"

        let count_trailing_zeros l _ = Reporting.unreachable l __POS__ "count_trailing_zeros"

        let fvector_store _l len ctyp = Primops.fvector_store len ctyp

        let is_empty l = function
          | CT_list ctyp -> Primops.is_empty ctyp
          | _ -> Reporting.unreachable l __POS__ "is_empty"

        let hd l = function CT_list ctyp -> Primops.hd ctyp | _ -> Reporting.unreachable l __POS__ "hd"

        let tl l = function CT_list ctyp -> Primops.tl ctyp | _ -> Reporting.unreachable l __POS__ "tl"

        let eq_list _ eq_elem ctyp1 ctyp2 = Primops.eq_list eq_elem ctyp1 ctyp2
      end)

  let ( let* ) = Smt_gen.bind
  let return = Smt_gen.return
  let mapM = Smt_gen.mapM
  let fmap = Smt_gen.fmap

  let pp_name =
    let ssa_num n = if n = -1 then empty else string ("_" ^ string_of_int n) in
    function
    | Name (id, n) -> pp_id id ^^ ssa_num n
    | Have_exception n -> string "sail_have_exception" ^^ ssa_num n
    | Current_exception n -> string "sail_current_exception" ^^ ssa_num n
    | Throw_location n -> string "sail_throw_location" ^^ ssa_num n
    | Channel (Chan_stdout, n) -> string "sail_stdout" ^^ ssa_num n
    | Channel (Chan_stderr, n) -> string "sail_stderr" ^^ ssa_num n
    | Memory_writes n -> string "sail_writes" ^^ ssa_num n
    | Return n -> string "sail_return" ^^ ssa_num n

  let wrap_type ctyp doc =
    match sv_ctyp ctyp with
    | ty, None -> string ty ^^ space ^^ doc
    | ty, Some index -> string ty ^^ space ^^ doc ^^ space ^^ string index

  let pp_type_def = function
    | CTD_abstract (id, _, _) ->
        Reporting.unreachable (id_loc id) __POS__ "Abstract types not supported for SystemVerilog target"
    | CTD_abbrev _ -> empty
    | CTD_enum (id, ids) ->
        string "typedef" ^^ space ^^ string "enum" ^^ space
        ^^ group (lbrace ^^ nest 4 (hardline ^^ separate_map (comma ^^ hardline) pp_id ids) ^^ hardline ^^ rbrace)
        ^^ space ^^ sv_type_id id ^^ semi
    | CTD_struct (id, fields) ->
        let sv_field (id, ctyp) = wrap_type ctyp (pp_id id) in
        let can_be_packed = List.for_all (fun (_, ctyp) -> is_packed ctyp) fields in
        string "typedef" ^^ space ^^ string "struct"
        ^^ (if can_be_packed then space ^^ string "packed" else empty)
        ^^ space
        ^^ group
             (lbrace
             ^^ nest 4 (hardline ^^ separate_map (semi ^^ hardline) sv_field fields)
             ^^ semi ^^ hardline ^^ rbrace
             )
        ^^ space ^^ sv_type_id id ^^ semi
    | CTD_variant (id, ctors) ->
        let kind_id (id, _) = string_of_id id |> Util.zencode_string |> String.uppercase_ascii |> string in
        let sv_ctor (id, ctyp) = wrap_type ctyp (pp_id id) in
        let tag_type = string ("sailtag_" ^ pp_id_string id) in
        let value_type = string ("sailunion_" ^ pp_id_string id) in
        let kind_enum =
          separate space
            [
              string "typedef";
              string "enum";
              group (lbrace ^^ nest 4 (hardline ^^ separate_map (comma ^^ hardline) kind_id ctors) ^^ hardline ^^ rbrace);
              tag_type ^^ semi;
            ]
        in
        (* At least verilator only allows unions for packed types (which
           is roughly equivalent to types that can be represented as
           finite bitvectors). *)
        let can_be_packed = List.for_all (fun (_, ctyp) -> is_packed ctyp) ctors && not Config.never_pack_unions in
        kind_enum ^^ twice hardline
        ^^
        if can_be_packed then (
          let max_width = bit_width (CT_variant (id, ctors)) |> Option.get in
          let padding_structs =
            List.map
              (fun (ctor_id, ctyp) ->
                let padding_type = string ("sailpadding_" ^ pp_id_string ctor_id) in
                let required_padding = max_width - Option.get (bit_width ctyp) in
                let padded =
                  separate space
                    [
                      string "typedef";
                      string "struct";
                      string "packed";
                      group
                        (lbrace
                        ^^ nest 4
                             (hardline
                             ^^ sv_ctor (ctor_id, ctyp)
                             ^^ semi
                             ^^
                             if required_padding > 0 then
                               hardline ^^ ksprintf string "logic [%d:0] padding" (required_padding - 1) ^^ semi
                             else empty
                             )
                        ^^ hardline ^^ rbrace
                        );
                      padding_type ^^ semi;
                    ]
                in
                (padded, (ctor_id, ctyp, padding_type, required_padding))
              )
              ctors
          in
          let constructors =
            if Config.union_padding then
              List.map
                (fun (_, (ctor_id, ctyp, padding_type, required_padding)) ->
                  separate space [string "function"; string "automatic"; sv_type_id id; pp_id ctor_id]
                  ^^ parens (wrap_type ctyp (char 'v'))
                  ^^ semi
                  ^^ nest 4
                       (hardline ^^ sv_type_id id ^^ space ^^ char 'r' ^^ semi ^^ hardline
                       ^^ string ("sailunion_" ^ pp_id_string id)
                       ^^ space ^^ char 'u' ^^ semi ^^ hardline ^^ padding_type ^^ space ^^ char 'p' ^^ semi ^^ hardline
                       ^^ separate space
                            [
                              string "r.tag";
                              equals;
                              string_of_id ctor_id |> Util.zencode_string |> String.uppercase_ascii |> string;
                            ]
                       ^^ semi ^^ hardline
                       ^^ separate space [char 'p' ^^ dot ^^ pp_id ctor_id; equals; char 'v']
                       ^^ semi ^^ hardline
                       ^^ ( if required_padding > 0 then
                              separate space
                                [
                                  char 'p' ^^ dot ^^ string "padding";
                                  equals;
                                  ksprintf string "%d'b%s" required_padding (String.make required_padding '0');
                                ]
                              ^^ semi ^^ hardline
                            else empty
                          )
                       ^^ separate space [char 'u' ^^ dot ^^ pp_id ctor_id; equals; char 'p']
                       ^^ semi ^^ hardline
                       ^^ separate space [string "r.value"; equals; char 'u']
                       ^^ semi ^^ hardline ^^ string "return" ^^ space ^^ char 'r' ^^ semi
                       )
                  ^^ hardline ^^ string "endfunction"
                )
                padding_structs
            else
              List.map
                (fun (ctor_id, ctyp) ->
                  separate space [string "function"; string "automatic"; sv_type_id id; pp_id ctor_id]
                  ^^ parens (wrap_type ctyp (char 'v'))
                  ^^ semi
                  ^^ nest 4
                       (hardline ^^ sv_type_id id ^^ space ^^ char 'r' ^^ semi ^^ hardline
                       ^^ string ("sailunion_" ^ pp_id_string id)
                       ^^ space ^^ char 'u' ^^ semi ^^ hardline
                       ^^ separate space
                            [
                              string "r.tag";
                              equals;
                              string_of_id ctor_id |> Util.zencode_string |> String.uppercase_ascii |> string;
                            ]
                       ^^ semi ^^ hardline
                       ^^ separate space [char 'u' ^^ dot ^^ pp_id ctor_id; equals; char 'v']
                       ^^ semi ^^ hardline
                       ^^ separate space [string "r.value"; equals; char 'u']
                       ^^ semi ^^ hardline ^^ string "return" ^^ space ^^ char 'r' ^^ semi
                       )
                  ^^ hardline ^^ string "endfunction"
                )
                ctors
          in
          let sv_padded_ctor (_, (ctor_id, _, padding_type, _)) = padding_type ^^ space ^^ pp_id ctor_id in
          (if Config.union_padding then separate_map (twice hardline) fst padding_structs ^^ twice hardline else empty)
          ^^ separate space
               [
                 string "typedef";
                 string "union";
                 string "packed";
                 group
                   (lbrace
                   ^^ nest 4
                        (hardline
                        ^^
                        if Config.union_padding then separate_map (semi ^^ hardline) sv_padded_ctor padding_structs
                        else separate_map (semi ^^ hardline) sv_ctor ctors
                        )
                   ^^ semi ^^ hardline ^^ rbrace
                   );
                 value_type ^^ semi;
               ]
          ^^ twice hardline
          ^^ separate space
               [
                 string "typedef";
                 string "struct";
                 string "packed";
                 group
                   (lbrace
                   ^^ nest 4
                        (hardline ^^ tag_type ^^ space ^^ string "tag" ^^ semi ^^ hardline ^^ value_type ^^ space
                       ^^ string "value"
                        )
                   ^^ semi ^^ hardline ^^ rbrace
                   );
                 sv_type_id id ^^ semi;
               ]
          ^^ twice hardline
          ^^ separate (twice hardline) constructors
        )
        else (
          let constructors =
            List.map
              (fun (ctor_id, ctyp) ->
                separate space [string "function"; string "automatic"; sv_type_id id; pp_id ctor_id]
                ^^ parens (wrap_type ctyp (char 'v'))
                ^^ semi
                ^^ nest 4
                     (hardline ^^ sv_type_id id ^^ space ^^ char 'r' ^^ semi ^^ hardline
                     ^^ separate space
                          [
                            string "r.tag";
                            equals;
                            string_of_id ctor_id |> Util.zencode_string |> String.uppercase_ascii |> string;
                          ]
                     ^^ semi ^^ hardline
                     ^^ separate space [char 'r' ^^ dot ^^ pp_id ctor_id; equals; char 'v']
                     ^^ semi ^^ hardline ^^ string "return" ^^ space ^^ char 'r' ^^ semi
                     )
                ^^ hardline ^^ string "endfunction"
              )
              ctors
          in
          separate space
            [
              string "typedef";
              string "struct";
              group
                (lbrace
                ^^ nest 4
                     (hardline ^^ tag_type ^^ space ^^ string "tag" ^^ semi ^^ hardline
                     ^^ separate_map (semi ^^ hardline) sv_ctor ctors
                     )
                ^^ semi ^^ hardline ^^ rbrace
                );
              sv_type_id id ^^ semi;
            ]
          ^^ twice hardline
          ^^ separate (twice hardline) constructors
        )

  let sv_signed x = string "signed'" ^^ parens x

  let string_of_bitU = function Sail2_values.B0 -> "0" | Sail2_values.B1 -> "1" | Sail2_values.BU -> "X"

  let all_ones = List.for_all (function Sail2_values.B1 -> true | _ -> false)

  let all_zeros = List.for_all (function Sail2_values.B0 -> true | _ -> false)

  let has_undefined_bit = List.exists (function Sail2_values.BU -> true | _ -> false)

  let rec hex_bitvector ?(drop_leading_zeros = false) bits =
    let open Sail2_values in
    match bits with
    | B0 :: B0 :: B0 :: B0 :: rest ->
        if drop_leading_zeros then hex_bitvector ~drop_leading_zeros rest
        else "0" ^ hex_bitvector ~drop_leading_zeros rest
    | B0 :: B0 :: B0 :: B1 :: rest -> "1" ^ hex_bitvector rest
    | B0 :: B0 :: B1 :: B0 :: rest -> "2" ^ hex_bitvector rest
    | B0 :: B0 :: B1 :: B1 :: rest -> "3" ^ hex_bitvector rest
    | B0 :: B1 :: B0 :: B0 :: rest -> "4" ^ hex_bitvector rest
    | B0 :: B1 :: B0 :: B1 :: rest -> "5" ^ hex_bitvector rest
    | B0 :: B1 :: B1 :: B0 :: rest -> "6" ^ hex_bitvector rest
    | B0 :: B1 :: B1 :: B1 :: rest -> "7" ^ hex_bitvector rest
    | B1 :: B0 :: B0 :: B0 :: rest -> "8" ^ hex_bitvector rest
    | B1 :: B0 :: B0 :: B1 :: rest -> "9" ^ hex_bitvector rest
    | B1 :: B0 :: B1 :: B0 :: rest -> "A" ^ hex_bitvector rest
    | B1 :: B0 :: B1 :: B1 :: rest -> "B" ^ hex_bitvector rest
    | B1 :: B1 :: B0 :: B0 :: rest -> "C" ^ hex_bitvector rest
    | B1 :: B1 :: B0 :: B1 :: rest -> "D" ^ hex_bitvector rest
    | B1 :: B1 :: B1 :: B0 :: rest -> "E" ^ hex_bitvector rest
    | B1 :: B1 :: B1 :: B1 :: rest -> "F" ^ hex_bitvector rest
    | _ -> ""

  let rec tails = function
    | Var v -> Some (0, v)
    | Tl (_, arg) -> Option.map (fun (n, v) -> (n + 1, v)) (tails arg)
    | _ -> None

  (* Convert a SMTLIB expression into SystemVerilog *)
  let rec pp_smt ?(need_parens = false) =
    let pp_smt_parens exp = pp_smt ~need_parens:true exp in
    let opt_parens doc = if need_parens then parens doc else doc in
    let rec pp_smt_ite = function
      | Ite (cond, then_exp, else_exp) ->
          prefix 2 1 (pp_smt_parens cond ^^ space ^^ char '?') (pp_smt_parens then_exp)
          ^^ break 1 ^^ char ':' ^^ space ^^ pp_smt_ite else_exp
      | exp -> pp_smt_parens exp
    in
    function
    | Bitvec_lit [] -> string "SAIL_ZWBV"
    | Bitvec_lit bits ->
        let len = List.length bits in
        if all_zeros bits then ksprintf string "%d'h0" len
        else if len mod 4 = 0 && not (has_undefined_bit bits) then
          ksprintf string "%d'h%s" len (hex_bitvector ~drop_leading_zeros:true bits)
        else ksprintf string "%d'b%s" len (Util.string_of_list "" string_of_bitU bits)
    | Bool_lit true -> string "1'h1"
    | Bool_lit false -> string "1'h0"
    | String_lit s -> if Config.no_strings then string "SAIL_UNIT" else ksprintf string "\"%s\"" s
    | Unit -> string "SAIL_UNIT"
    | Member id -> string (string_of_id id)
    | Fn ("reg_ref", [String_lit r]) -> ksprintf string "SAIL_REG_%s" (Util.zencode_upper_string r)
    | Fn ("Bits", [size; bv]) -> squote ^^ lbrace ^^ pp_smt size ^^ comma ^^ space ^^ pp_smt bv ^^ rbrace
    | Fn ("concat", xs) -> lbrace ^^ separate_map (comma ^^ space) pp_smt xs ^^ rbrace
    | Fn ("not", [Fn ("not", [x])]) -> pp_smt ~need_parens x
    | Fn ("not", [Fn ("=", [x; y])]) -> opt_parens (separate space [pp_smt_parens x; string "!="; pp_smt_parens y])
    | Fn ("not", [x]) -> opt_parens (char '!' ^^ pp_smt_parens x)
    | Fn ("=", [x; y]) -> opt_parens (separate space [pp_smt_parens x; string "=="; pp_smt_parens y])
    | Fn ("and", xs) -> opt_parens (separate_map (space ^^ string "&&" ^^ space) pp_smt_parens xs)
    | Fn ("or", xs) -> opt_parens (separate_map (space ^^ string "||" ^^ space) pp_smt_parens xs)
    | Fn ("bvnot", [x]) -> opt_parens (char '~' ^^ pp_smt_parens x)
    | Fn ("bvneg", [x]) -> opt_parens (char '-' ^^ pp_smt_parens x)
    | Fn ("bvand", [x; y]) -> opt_parens (separate space [pp_smt_parens x; char '&'; pp_smt_parens y])
    | Fn ("bvnand", [x; y]) ->
        opt_parens (char '~' ^^ parens (separate space [pp_smt_parens x; char '&'; pp_smt_parens y]))
    | Fn ("bvor", [x; y]) -> opt_parens (separate space [pp_smt_parens x; char '|'; pp_smt_parens y])
    | Fn ("bvnor", [x; y]) ->
        opt_parens (char '~' ^^ parens (separate space [pp_smt_parens x; char '|'; pp_smt_parens y]))
    | Fn ("bvxor", [x; y]) -> opt_parens (separate space [pp_smt_parens x; char '^'; pp_smt_parens y])
    | Fn ("bvxnor", [x; y]) ->
        opt_parens (char '~' ^^ parens (separate space [pp_smt_parens x; char '^'; pp_smt_parens y]))
    | Fn ("bvadd", [x; y]) -> opt_parens (separate space [pp_smt_parens x; char '+'; pp_smt_parens y])
    | Fn ("bvsub", [x; y]) -> opt_parens (separate space [pp_smt_parens x; char '-'; pp_smt_parens y])
    | Fn ("bvmul", [x; y]) -> opt_parens (separate space [pp_smt_parens x; char '*'; pp_smt_parens y])
    | Fn ("bvult", [x; y]) -> opt_parens (separate space [pp_smt_parens x; char '<'; pp_smt_parens y])
    | Fn ("bvule", [x; y]) -> opt_parens (separate space [pp_smt_parens x; string "<="; pp_smt_parens y])
    | Fn ("bvugt", [x; y]) -> opt_parens (separate space [pp_smt_parens x; char '>'; pp_smt_parens y])
    | Fn ("bvuge", [x; y]) -> opt_parens (separate space [pp_smt_parens x; string ">="; pp_smt_parens y])
    | Fn ("bvslt", [x; y]) -> opt_parens (separate space [sv_signed (pp_smt x); char '<'; sv_signed (pp_smt y)])
    | Fn ("bvsle", [x; y]) -> opt_parens (separate space [sv_signed (pp_smt x); string "<="; sv_signed (pp_smt y)])
    | Fn ("bvsgt", [x; y]) -> opt_parens (separate space [sv_signed (pp_smt x); char '>'; sv_signed (pp_smt y)])
    | Fn ("bvsge", [x; y]) -> opt_parens (separate space [sv_signed (pp_smt x); string ">="; sv_signed (pp_smt y)])
    | Fn ("bvshl", [x; y]) -> opt_parens (separate space [pp_smt_parens x; string "<<"; sv_signed (pp_smt y)])
    | Fn ("bvlshr", [x; y]) -> opt_parens (separate space [pp_smt_parens x; string ">>"; sv_signed (pp_smt y)])
    | Fn ("bvashr", [x; y]) -> opt_parens (separate space [pp_smt_parens x; string ">>>"; sv_signed (pp_smt y)])
    (* SV LRM: The integer division shall truncate any fractional part toward zero
       SMTLIB bvsdiv: Truncation is towards zero (could not find official reference, but z3 and cvc5 are consistent). *)
    | Fn ("bvsdiv", [x; y]) -> opt_parens (separate space [sv_signed (pp_smt x); string "/"; sv_signed (pp_smt y)])
    (* SV LRM: The result of a modulus operation shall take the sign of the first operand (dividend).
       SMTLIB bvsrem: Sign follows dividend *)
    | Fn ("bvsrem", [x; y]) -> opt_parens (separate space [sv_signed (pp_smt x); string "%"; sv_signed (pp_smt y)])
    | Fn ("select", [x; i]) -> pp_smt_parens x ^^ lbracket ^^ pp_smt i ^^ rbracket
    | Fn ("contents", [Var v]) -> pp_name v ^^ dot ^^ string "bits"
    | Fn ("contents", [x]) -> string "sail_bits_value" ^^ parens (pp_smt x)
    | Fn ("len", [Var v]) -> pp_name v ^^ dot ^^ string "size"
    | Fn ("len", [x]) -> string "sail_bits_size" ^^ parens (pp_smt x)
    | Fn ("cons", [x; xs]) -> lbrace ^^ pp_smt x ^^ comma ^^ space ^^ pp_smt xs ^^ rbrace
    | Fn ("str.++", xs) -> lbrace ^^ separate_map (comma ^^ space) pp_smt xs ^^ rbrace
    | Fn ("Array", xs) -> squote ^^ lbrace ^^ separate_map (comma ^^ space) pp_smt xs ^^ rbrace
    | Fn (f, args) -> string f ^^ parens (separate_map (comma ^^ space) pp_smt args)
    | Store (_, store_fn, arr, i, x) -> string store_fn ^^ parens (separate_map (comma ^^ space) pp_smt [arr; i; x])
    | SignExtend (len, _, x) -> ksprintf string "unsigned'(%d'(signed'({" len ^^ pp_smt x ^^ string "})))"
    | ZeroExtend (len, _, x) -> ksprintf string "%d'({" len ^^ pp_smt x ^^ string "})"
    | Extract (n, m, _, Bitvec_lit bits) ->
        pp_smt (Bitvec_lit (Sail2_operators_bitlists.subrange_vec_dec bits (Big_int.of_int n) (Big_int.of_int m)))
    | Extract (n, m, len, Var v) ->
        if len = 1 then pp_name v
        else if n = m then pp_name v ^^ lbracket ^^ string (string_of_int n) ^^ rbracket
        else pp_name v ^^ lbracket ^^ string (string_of_int n) ^^ colon ^^ string (string_of_int m) ^^ rbracket
    | Extract (n, m, len, x) ->
        if len = 1 then pp_smt x
        else if n = m then braces (pp_smt x) ^^ lbracket ^^ string (string_of_int n) ^^ rbracket
        else braces (pp_smt x) ^^ lbracket ^^ string (string_of_int n) ^^ colon ^^ string (string_of_int m) ^^ rbracket
    | Var v -> pp_name v
    | Tester (ctor, v) ->
        opt_parens
          (separate space
             [pp_smt v ^^ dot ^^ string "tag"; string "=="; string (ctor |> zencode_id |> String.uppercase_ascii)]
          )
    | Unwrap (ctor, packed, v) ->
        let packed_ctor = if Config.union_padding then pp_id ctor ^^ dot ^^ pp_id ctor else pp_id ctor in
        if packed then pp_smt v ^^ dot ^^ string "value" ^^ dot ^^ packed_ctor else pp_smt v ^^ dot ^^ pp_id ctor
    | Field (_, field, v) -> pp_smt v ^^ dot ^^ pp_id field
    | Ite (cond, then_exp, else_exp) ->
        opt_parens
          (align
             (prefix 2 1 (pp_smt_parens cond ^^ space ^^ char '?') (pp_smt_parens then_exp)
             ^^ break 1 ^^ char ':' ^^ space ^^ pp_smt_ite else_exp
             )
          )
    | Empty_list -> string "{}"
    | Hd (op, arg) -> begin
        match tails arg with
        | Some (index, v) -> pp_name v ^^ brackets (string (string_of_int index))
        | None -> string op ^^ parens (pp_smt arg)
      end
    | Tl (op, arg) -> string op ^^ parens (pp_smt arg)
    | _ -> empty

  let sv_cval cval =
    let* smt = Smt.smt_cval cval in
    return (pp_smt smt)

  let rec sv_clexp = function
    | CL_id (id, _) -> pp_name id
    | CL_field (clexp, field) -> sv_clexp clexp ^^ dot ^^ pp_id field
    | clexp -> string ("// CLEXP " ^ Jib_util.string_of_clexp clexp)

  let svir_update_fbits = function
    | [bv; index; bit] -> begin
        match (cval_ctyp bv, cval_ctyp index) with
        | CT_fbits 1, _ -> Smt.smt_cval bit
        | CT_fbits sz, CT_constant c ->
            let c = Big_int.to_int c in
            let* bv_smt = Smt.smt_cval bv in
            let bv_smt_1 = Extract (sz - 1, c + 1, sz, bv_smt) in
            let bv_smt_2 = Extract (c - 1, 0, sz, bv_smt) in
            let* bit_smt = Smt.smt_cval bit in
            let smt =
              if c = 0 then Fn ("concat", [bv_smt_1; bit_smt])
              else if c = sz - 1 then Fn ("concat", [bit_smt; bv_smt_2])
              else Fn ("concat", [bv_smt_1; bit_smt; bv_smt_2])
            in
            return smt
        | _, _ -> failwith "update_fbits 1"
      end
    | _ -> failwith "update_fbits 2"

  let cval_for_ctyp = function
    | CT_unit -> return (V_lit (VL_unit, CT_unit))
    | ctyp ->
        let* l = Smt_gen.current_location in
        Reporting.unreachable l __POS__ ("Cannot create undefined value of type " ^ string_of_ctyp ctyp)

  let sv_line_directive l =
    match Reporting.simp_loc l with
    | Some (p1, _) when Config.line_directives ->
        ksprintf string "`line %d \"%s\" 0" p1.pos_lnum p1.pos_fname ^^ hardline
    | _ -> empty

  let sv_assign clexp value =
    match clexp with
    | CL_addr (CL_id (id, CT_ref reg_ctyp)) ->
        let encoded = Util.zencode_string (string_of_ctyp reg_ctyp) in
        ksprintf string "sail_reg_assign_%s" encoded ^^ parens (pp_name id ^^ comma ^^ space ^^ value) ^^ semi
    | _ -> sv_clexp clexp ^^ space ^^ equals ^^ space ^^ value ^^ semi

  let rec svir_clexp ?(parents = []) = function
    | CL_id (id, _) -> ([], SVP_id id)
    | CL_field (clexp, field) ->
        let updates, lexp = svir_clexp ~parents:(field :: parents) clexp in
        (updates, SVP_field (lexp, field))
    | CL_void ctyp -> ([], SVP_void ctyp)
    | CL_rmw (id_from, id, ctyp) ->
        let rec assignments lexp subpart ctyp = function
          | parent :: parents -> begin
              match ctyp with
              | CT_struct (struct_id, fields) ->
                  let _, field_ctyp = List.find (fun (f, _) -> Id.compare f parent = 0) fields in
                  let other_fields = List.filter (fun (f, _) -> Id.compare f parent <> 0) fields in
                  assignments (SVP_field (lexp, parent)) (Field (struct_id, parent, subpart)) field_ctyp parents
                  @ List.map
                      (fun (f, _) -> SVS_assign (SVP_field (lexp, f), Field (struct_id, f, subpart)))
                      other_fields
              | _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "expected struct type"
            end
          | [] -> []
        in
        let updates = assignments (SVP_id id) (Var id_from) ctyp parents in
        (updates, SVP_id id)
    | CL_addr _ | CL_tuple _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "addr/tuple"

  let svir_creturn = function
    | CR_one clexp -> svir_clexp clexp
    | CR_multi clexps -> ([], SVP_multi (List.map snd (List.map svir_clexp clexps)))

  let with_updates l updates aux =
    let wrap aux = SVS_aux (aux, l) in
    match updates with [] -> aux | _ -> SVS_block (List.map wrap updates @ [wrap aux])

  let convert_return l creturn to_aux return_type_opt =
    let wrap aux = SVS_aux (aux, l) in
    let ctyp = creturn_ctyp creturn in
    let updates, ret = svir_creturn creturn in
    match return_type_opt with
    | Some ctyp' ->
        let temp = ngensym () in
        let* converted = Smt.smt_conversion ~into:ctyp ~from:ctyp' (Var temp) in
        return
          (SVS_block
             ((wrap (SVS_var (temp, ctyp', None)) :: List.map wrap updates)
             @ [wrap (to_aux (SVP_id temp)); wrap (SVS_assign (ret, converted))]
             )
          )
    | None -> (
        match updates with
        | [] -> return (to_aux ret)
        | _ -> return (SVS_block (List.map wrap updates @ [wrap (to_aux ret)]))
      )

  let convert_arguments ?(reverse = false) args = function
    | None ->
        mapM
          (fun arg ->
            let* smt = Smt.smt_cval arg in
            return (smt, cval_ctyp arg)
          )
          args
    | Some conversions ->
        let arg_ctyps = List.map cval_ctyp args in
        mapM
          (fun (arg, (ctyp, convert)) ->
            let* smt = Smt.smt_cval arg in
            match convert with
            | None -> return (smt, ctyp)
            | Some ctyp' ->
                let* smt = Smt.smt_cval arg in
                let* converted =
                  if reverse then Smt.smt_conversion ~into:ctyp ~from:ctyp' smt
                  else Smt.smt_conversion ~into:ctyp' ~from:ctyp smt
                in
                return (converted, ctyp')
          )
          (List.combine args (List.combine arg_ctyps conversions))

  let extern_generate l ctx creturn id name args =
    let wrap aux = return (Some (SVS_aux (aux, l))) in
    match Smt.builtin ~allow_io:false name with
    | Some generator ->
        let clexp =
          match creturn with
          | CR_one clexp -> clexp
          | CR_multi clexps ->
              Reporting.unreachable l __POS__
                (sprintf "Multiple return generator primitive found: %s (%s)" name
                   (Util.string_of_list ", " string_of_clexp clexps)
                )
        in
        let* value = Smt_gen.fmap (Smt_exp.simp SimpSet.empty) (generator args (clexp_ctyp clexp)) in
        begin
          (* We can optimize R = store(R, i x) into R[i] = x *)
          match (clexp, value) with
          | CL_id (v, _), Store (_, _, Var v', i, x) when Name.compare v v' = 0 ->
              wrap (SVS_assign (SVP_index (SVP_id v, i), x))
          | _, _ ->
              let updates, lexp = svir_clexp clexp in
              wrap (with_updates l updates (SVS_assign (lexp, value)))
        end
    | None -> (
        match Primops.generate_module ~at:l name with
        | Some generator ->
            let generated_name = generator args (creturn_ctyp creturn) in
            let* args = mapM Smt.smt_cval args in
            let updates, ret = svir_creturn creturn in
            wrap (with_updates l updates (SVS_call (ret, SVN_string generated_name, args)))
        | None ->
            let _, _, _, uannot = Bindings.find id ctx.valspecs in
            let arity = List.length args in
            let* arg_convs, ret_conv, is_function =
              match get_sv_attribute "sv_module" uannot with
              | Some obj, (module ModuleAttr) ->
                  let module Attr = AttributeParser (ModuleAttr) in
                  let types = Attr.get_types ~arity (Some obj) in
                  let return_type = Attr.get_return_type (Some obj) in
                  return (types, return_type, false)
              | None, _ ->
                  let attr, (module FunctionAttr) = get_sv_attribute "sv_function" uannot in
                  let module Attr = AttributeParser (FunctionAttr) in
                  let types = Attr.get_types ~arity attr in
                  let return_type = Attr.get_return_type attr in
                  return (types, return_type, true)
            in
            let* args = fmap (List.map fst) (convert_arguments args arg_convs) in
            let* aux =
              if is_function then convert_return l creturn (fun ret -> SVS_assign (ret, Fn (name, args))) ret_conv
              else convert_return l creturn (fun ret -> SVS_call (ret, SVN_string name, args)) ret_conv
            in
            wrap aux
      )

  let rec svir_instr ?pathcond spec_info ctx (I_aux (aux, (_, l))) =
    let wrap aux = return (Some (SVS_aux (aux, l))) in
    match aux with
    | I_comment str -> wrap (SVS_comment str)
    | I_decl (ctyp, id) -> wrap (SVS_var (id, ctyp, None))
    | I_init (ctyp, id, init) -> (
        match init with
        | Init_cval cval ->
            let* value = Smt.smt_cval cval in
            wrap (SVS_var (id, ctyp, Some value))
        | Init_json_key _ | Init_static _ ->
            Reporting.unreachable l __POS__ "Unexpected cval initializer found in SV backend"
      )
    | I_return cval ->
        let* value = Smt.smt_cval cval in
        wrap (SVS_return value)
    | I_end id -> wrap (SVS_return (Var id))
    | I_exit _ -> wrap (svs_raw "$finish")
    | I_copy (CL_void _, cval) -> return None
    | I_copy (clexp, cval) ->
        let* value =
          Smt_gen.bind (Smt.smt_cval cval) (Smt.smt_conversion ~into:(clexp_ctyp clexp) ~from:(cval_ctyp cval))
        in
        let updates, lexp = svir_clexp clexp in
        wrap (with_updates l updates (SVS_assign (lexp, value)))
    | I_funcall (creturn, preserve_name, (id, _), args) ->
        if ctx_is_extern id ctx then (
          let name = ctx_get_extern id ctx in
          extern_generate l ctx creturn id name args
        )
        else if Id.compare id (mk_id "sail_assert") = 0 then
          if Config.no_assertions then wrap SVS_skip
          else (
            let _, ret = svir_creturn creturn in
            match args with
            | [cond; msg] ->
                let* cond = Smt.smt_cval cond in
                let* msg = Smt.smt_cval msg in
                (* If the assert is only reachable under some path-condition, then the assert should pass
                   whenever the path-condition is not true. *)
                let cond =
                  match pathcond with
                  | Some pathcond ->
                      Fn ("or", [Fn ("not", [pathcond]); Fn ("not", [Var (Name (mk_id "assert_reachable#", -1))]); cond])
                  | None -> cond
                in
                wrap (SVS_block [SVS_aux (SVS_assert (cond, msg), l); SVS_aux (SVS_assign (ret, Unit), l)])
            | _ -> Reporting.unreachable l __POS__ "Invalid arguments for sail_assert"
          )
        else if Id.compare id (mk_id "sail_cons") = 0 then extern_generate l ctx creturn id "sail_cons" args
        else if Id.compare id (mk_id "update_fbits") = 0 then
          let* rhs = svir_update_fbits args in
          let updates, ret = svir_creturn creturn in
          wrap (with_updates l updates (SVS_assign (ret, rhs)))
        else if Id.compare id (mk_id "internal_vector_init") = 0 then return None
        else if Id.compare id (mk_id "internal_vector_update") = 0 then (
          match args with
          | [arr; i; x] -> begin
              match cval_ctyp arr with
              | CT_fvector (len, _) ->
                  let* arr = Smt.smt_cval arr in
                  let sz = required_width (Big_int.of_int (len - 1)) - 1 in
                  let* i =
                    Smt_gen.bind (Smt.smt_cval i)
                      (Smt_gen.unsigned_size ~checked:false ~into:sz ~from:(Smt.int_size (cval_ctyp i)))
                  in
                  let* x = Smt.smt_cval x in
                  let j = mk_id "j" in
                  let updates, ret = svir_creturn creturn in
                  begin
                    match (ret, arr) with
                    | SVP_id id1, Var id2 when Name.compare id1 id2 = 0 ->
                        wrap (with_updates l updates (SVS_assign (SVP_index (ret, i), x)))
                    | _ ->
                        wrap
                          (with_updates l updates
                             (SVS_foreach
                                ( SVN_id j,
                                  arr,
                                  SVS_aux
                                    ( SVS_assign
                                        ( SVP_index (ret, var_id j),
                                          Ite
                                            ( Fn ("=", [Extract (sz - 1, 0, 32, var_id j); i]),
                                              x,
                                              Fn ("select", [arr; var_id j])
                                            )
                                        ),
                                      l
                                    )
                                )
                             )
                          )
                  end
              | _ -> Reporting.unreachable l __POS__ "Invalid vector type for internal vector update"
            end
          | _ -> Reporting.unreachable l __POS__ "Invalid number of arguments to internal vector update"
        )
        else (
          let footprint = Bindings.find_opt id spec_info.footprints |> Option.value ~default:pure_footprint in
          let* args = mapM Smt.smt_cval args in
          let args =
            args @ if footprint.contains_assert then [Option.value ~default:(Bool_lit true) pathcond] else []
          in
          let updates, ret = svir_creturn creturn in
          if preserve_name then wrap (with_updates l updates (SVS_call (ret, SVN_string (string_of_id id), args)))
          else wrap (with_updates l updates (SVS_call (ret, SVN_id id, args)))
        )
    | I_block instrs ->
        let* statements = fmap Util.option_these (mapM (svir_instr ?pathcond spec_info ctx) instrs) in
        wrap (svs_block statements)
    | I_if (cond, then_instrs, else_instrs) ->
        let* cond = Smt.smt_cval cond in
        let to_block statements =
          match filter_skips (Util.option_these statements) with
          | [] -> None
          | [statement] -> Some statement
          | statements -> Some (SVS_aux (SVS_block statements, Parse_ast.Unknown))
        in
        let* then_block = fmap to_block (mapM (svir_instr ?pathcond spec_info ctx) then_instrs) in
        let* else_block = fmap to_block (mapM (svir_instr ?pathcond spec_info ctx) else_instrs) in
        wrap (SVS_if (cond, then_block, else_block))
    | I_raw str -> wrap (svs_raw str)
    | I_undefined ctyp ->
        Reporting.unreachable l __POS__ "Unreachable instruction should not reach SystemVerilog backend"
    | I_jump _ | I_goto _ | I_label _ ->
        Reporting.unreachable l __POS__ "Non-structured control flow should not reach SystemVerilog backend"
    | I_throw _ | I_try_block _ ->
        Reporting.unreachable l __POS__ "Exception handling should not reach SystemVerilog backend"
    | I_clear _ | I_reset _ | I_reinit _ ->
        Reporting.unreachable l __POS__ "Cleanup commands should not appear in SystemVerilog backend"

  let rec pp_place = function
    | SVP_id id -> pp_name id
    | SVP_index (place, i) -> pp_place place ^^ lbracket ^^ pp_smt i ^^ rbracket
    | SVP_field (place, field) -> pp_place place ^^ dot ^^ pp_id field
    | SVP_multi places -> parens (separate_map (comma ^^ space) pp_place places)
    | SVP_void _ -> string "void"

  let pp_sv_name = function SVN_id id -> pp_id id | SVN_string s -> string s

  let rec pp_statement ?(terminator = semi ^^ hardline) (SVS_aux (aux, l)) =
    let ld = sv_line_directive l in
    match aux with
    | SVS_comment str -> concat_map string ["/* "; str; " */"]
    | SVS_split_comb -> string "/* split comb */"
    | SVS_assert (cond, msg) ->
        separate space
          [string "if"; parens (pp_smt cond) ^^ semi; string "else"; string "$fatal" ^^ parens (pp_smt msg)]
        ^^ terminator
    | SVS_foreach (i, exp, stmt) ->
        separate space [string "foreach"; parens (pp_smt exp ^^ brackets (pp_sv_name i))]
        ^^ nest 4 (hardline ^^ pp_statement ~terminator:empty stmt)
        ^^ terminator
    | SVS_for (loop, stmt) ->
        let vars =
          let i, ctyp, init = loop.for_var in
          separate space [wrap_type ctyp (pp_name i); equals; pp_smt init]
        in
        let modifier =
          match loop.for_modifier with
          | SVF_increment i -> pp_name i ^^ string "++"
          | SVF_decrement i -> pp_name i ^^ string "--"
        in
        separate space [string "for"; parens (separate (semi ^^ space) [vars; pp_smt loop.for_cond; modifier])]
        ^^ nest 4 (hardline ^^ pp_statement ~terminator:empty stmt)
        ^^ terminator
    | SVS_var (id, ctyp, init_opt) -> begin
        match init_opt with
        | Some init -> ld ^^ separate space [wrap_type ctyp (pp_name id); equals; pp_smt init] ^^ terminator
        | None -> ld ^^ wrap_type ctyp (pp_name id) ^^ terminator
      end
    | SVS_return smt -> string "return" ^^ space ^^ pp_smt smt ^^ terminator
    | SVS_assign (place, value) -> ld ^^ separate space [pp_place place; equals; pp_smt value] ^^ terminator
    | SVS_continuous_assign (place, value) ->
        ld ^^ separate space [pp_place place; string "<="; pp_smt value] ^^ terminator
    | SVS_call (place, ctor, args) ->
        ld
        ^^ separate space [pp_place place; equals; pp_sv_name ctor]
        ^^ parens (separate_map (comma ^^ space) pp_smt args)
        ^^ terminator
    | SVS_if (_, None, None) -> empty
    | SVS_if (cond, None, Some else_block) ->
        let cond = pp_smt (Fn ("not", [cond])) in
        string "if" ^^ space ^^ parens cond ^^ space ^^ pp_statement else_block
    | SVS_if (cond, Some then_block, None) ->
        string "if" ^^ space ^^ parens (pp_smt cond) ^^ space ^^ pp_statement then_block
    | SVS_if (cond, Some then_block, Some else_block) ->
        string "if" ^^ space
        ^^ parens (pp_smt cond)
        ^^ space
        ^^ pp_statement ~terminator:hardline then_block
        ^^ string "else" ^^ space ^^ pp_statement else_block
    | SVS_case { head_exp; cases; fallthrough } ->
        let pp_case (exp, statement) = separate space [pp_smt exp; colon; pp_statement ~terminator:semi statement] in
        let pp_fallthrough = function
          | None -> empty
          | Some statement ->
              hardline ^^ separate space [string "default"; colon; pp_statement ~terminator:semi statement]
        in
        string "case" ^^ space
        ^^ parens (pp_smt head_exp)
        ^^ nest 4 (hardline ^^ separate_map hardline pp_case cases ^^ pp_fallthrough fallthrough)
        ^^ hardline ^^ string "endcase" ^^ terminator
    | SVS_block statements ->
        let statements = List.filter (fun stmt -> not (is_skip stmt)) statements in
        let block_terminator last = if last then semi else semi ^^ hardline in
        string "begin"
        ^^ nest 4
             (hardline
             ^^ concat (Util.map_last (fun last -> pp_statement ~terminator:(block_terminator last)) statements)
             )
        ^^ hardline ^^ string "end" ^^ terminator
    | SVS_raw (s, _, _) -> string s ^^ terminator
    | SVS_skip -> string "begin" ^^ hardline ^^ string "end" ^^ terminator

  let sv_instr spec_info ctx instr =
    let* statement_opt = svir_instr spec_info ctx instr in
    match statement_opt with Some statement -> return (pp_statement statement) | None -> return empty

  let sv_checked_instr spec_info ctx (I_aux (_, (_, l)) as instr) =
    let v, _ = Smt_gen.run (sv_instr spec_info ctx instr) l in
    v

  let smt_ssanode cfg pathconds =
    let open Jib_ssa in
    function
    | Pi _ -> return None
    | Phi (id, ctyp, ids) -> (
        let ids, pathconds =
          List.combine ids pathconds |> List.filter (fun (_, pc) -> Option.is_some pc) |> List.split
        in
        let mux =
          List.fold_right2
            (fun pathcond id chain ->
              let pathcond = Option.get pathcond in
              match chain with Some smt -> Some (Ite (pathcond, Var id, smt)) | None -> Some (Var id)
            )
            pathconds ids None
        in
        let mux = Option.map (Smt_exp.simp SimpSet.empty) mux in
        match mux with None -> assert false | Some mux -> return (Some (id, ctyp, mux))
      )

  let svir_cfnode spec_info ctx pathcond =
    let open Jib_ssa in
    function
    | CF_start inits ->
        let svir_start (id, ctyp) = SVS_aux (SVS_var (id, ctyp, None), Parse_ast.Unknown) in
        let svir_inits = List.map svir_start (NameMap.bindings inits) in
        return svir_inits
    | CF_block (instrs, _) ->
        let* statements = fmap Util.option_these (mapM (svir_instr ~pathcond spec_info ctx) instrs) in
        return statements
    | _ -> return []

  class register_fix_visitor spec_info ssa_nums : svir_visitor =
    object
      inherit empty_svir_visitor

      method! vctyp _ = SkipChildren

      method! vname name =
        let name, n = Jib_ssa.unssa_name name in
        ssa_nums :=
          NameMap.update name
            (function None -> Some (IntSet.singleton n) | Some ns -> Some (IntSet.add n ns))
            !ssa_nums;
        None
    end

  class thread_registers ctx spec_info : jib_visitor =
    object
      inherit empty_jib_visitor

      method! vctyp _ = SkipChildren

      method! vinstr (I_aux (aux, iannot) as no_change) =
        match aux with
        | I_copy (CL_addr (CL_id (id, CT_ref reg_ctyp)), cval) -> begin
            let regs = Option.value ~default:IdSet.empty (CTMap.find_opt reg_ctyp spec_info.register_ctyp_map) in

            let encoded = "sail_reg_assign_" ^ Util.zencode_string (string_of_ctyp reg_ctyp) in
            let reads = List.map (fun id -> V_id (Name (id, -1), reg_ctyp)) (natural_sort_ids (IdSet.elements regs)) in
            let writes =
              List.map (fun id -> CL_id (Name (id, -1), reg_ctyp)) (natural_sort_ids (IdSet.elements regs))
            in
            ChangeTo
              (I_aux
                 ( I_funcall (CR_multi writes, true, (mk_id encoded, []), V_id (id, CT_ref reg_ctyp) :: cval :: reads),
                   iannot
                 )
              )
          end
        | I_funcall (CR_one clexp, ext, (f, []), args) -> begin
            match Bindings.find_opt f spec_info.footprints with
            | Some footprint ->
                let reads =
                  List.map
                    (fun id -> V_id (Name (id, -1), Bindings.find id spec_info.registers))
                    (natural_sort_ids (IdSet.elements (IdSet.union footprint.all_writes footprint.all_reads)))
                in
                let writes =
                  List.map
                    (fun id -> CL_id (Name (id, -1), Bindings.find id spec_info.registers))
                    (natural_sort_ids (IdSet.elements footprint.all_writes))
                in
                let throws =
                  if footprint.throws || footprint.exits then
                    [CL_id (Have_exception (-1), CT_bool); CL_id (Current_exception (-1), spec_info.exception_ctyp)]
                  else []
                in
                let channels =
                  (if footprint.need_stdout then [Channel (Chan_stdout, -1)] else [])
                  @ if footprint.need_stderr then [Channel (Chan_stderr, -1)] else []
                in
                let input_channels = List.map (fun c -> V_id (c, CT_string)) channels in
                let output_channels = List.map (fun c -> CL_id (c, CT_string)) channels in
                let input_memory_writes, output_memory_writes =
                  if footprint.writes_mem then
                    ([V_id (Memory_writes (-1), CT_memory_writes)], [CL_id (Memory_writes (-1), CT_memory_writes)])
                  else ([], [])
                in
                let cr_multi x = function [] -> CR_one x | xs -> CR_multi (x :: xs) in
                ChangeTo
                  (I_aux
                     ( I_funcall
                         ( cr_multi clexp (writes @ throws @ output_channels @ output_memory_writes),
                           ext,
                           (f, []),
                           args @ reads @ input_channels @ input_memory_writes
                         ),
                       iannot
                     )
                  )
            | None ->
                let attr =
                  match Bindings.find_opt f ctx.valspecs with
                  | Some (_, _, _, uannot) ->
                      Option.bind (Option.bind (get_attribute "sv_module" uannot) snd) attribute_data_object
                  | None -> None
                in
                if ctx_is_extern f ctx then (
                  let name = ctx_get_extern f ctx in
                  if name = "print" || name = "print_endline" || name = "print_bits" || name = "print_int" then
                    ChangeTo
                      (I_aux
                         ( I_funcall
                             ( CR_multi (clexp :: [CL_id (Channel (Chan_stdout, -1), CT_string)]),
                               ext,
                               (f, []),
                               args @ [V_id (Channel (Chan_stdout, -1), CT_string)]
                             ),
                           iannot
                         )
                      )
                  else if Option.fold ~none:false ~some:(get_bool_attribute "writes_memory") attr then
                    ChangeTo
                      (I_aux
                         ( I_funcall
                             ( CR_multi (clexp :: [CL_id (Memory_writes (-1), CT_memory_writes)]),
                               ext,
                               (f, []),
                               args @ [V_id (Memory_writes (-1), CT_memory_writes)]
                             ),
                           iannot
                         )
                      )
                  else if name = "reg_deref" then (
                    match args with
                    | [cval] -> begin
                        match cval_ctyp cval with
                        | CT_ref reg_ctyp ->
                            let regs =
                              Option.value ~default:IdSet.empty (CTMap.find_opt reg_ctyp spec_info.register_ctyp_map)
                            in
                            let encoded = "sail_reg_deref_" ^ Util.zencode_string (string_of_ctyp reg_ctyp) in
                            let reads =
                              List.map
                                (fun id -> V_id (Name (id, -1), reg_ctyp))
                                (natural_sort_ids (IdSet.elements regs))
                            in
                            ChangeTo (I_aux (I_funcall (CR_one clexp, true, (mk_id encoded, []), cval :: reads), iannot))
                        | _ -> Reporting.unreachable (snd iannot) __POS__ "Invalid type for reg_deref argument"
                      end
                    | _ -> Reporting.unreachable (snd iannot) __POS__ "Invalid arguments for reg_deref"
                  )
                  else SkipChildren
                )
                else SkipChildren
          end
        | _ -> DoChildren
    end

  let sv_name_is_constructor spec_info = function SVN_id id -> IdSet.mem id spec_info.constructors | _ -> false

  (* This rewrite lifts statements out of an always_comb block in a
     module, that need to appear in the toplevel of the module as
     definitions. *)
  class hoist_module_statements spec_info decls instantiations : svir_visitor =
    object
      inherit empty_svir_visitor

      method! vctyp _ = SkipChildren

      method! vstatement (SVS_aux (aux, l) as no_change) =
        match aux with
        | SVS_var (name, ctyp, exp_opt) ->
            begin
              match name with Name (id, _) -> decls := Bindings.add id ctyp !decls | _ -> ()
            end;
            begin
              match exp_opt with
              | Some exp -> ChangeTo (SVS_aux (SVS_assign (SVP_id name, exp), l))
              | None -> ChangeTo (SVS_aux (SVS_skip, l))
            end
        | SVS_call (place, f, args) ->
            if sv_name_is_constructor spec_info f then SkipChildren
            else (
              Queue.add (place, f, args) instantiations;
              ChangeTo (SVS_aux (SVS_split_comb, l))
            )
        | SVS_block _ ->
            ChangeDoChildrenPost
              ( no_change,
                fun (SVS_aux (aux, l) as no_change) ->
                  match aux with SVS_block stmts -> SVS_aux (SVS_block (filter_skips stmts), l) | _ -> no_change
              )
        | _ -> DoChildren
    end

  (* We want to be able tp find the final assigned value of any
     variable v in the SSA control flow graph, as that is the variable
     that will be passed on to output ports if needed. *)
  let get_final_names ssa_vars cfg =
    let open Jib_ssa in
    let phi_graph, phi_nodes = phi_dependencies cfg in
    let phi_names, final_names =
      phi_graph |> NameGraph.topsort
      |> List.fold_left
           (fun (seen, fins) ssa_name ->
             let name, n = Jib_ssa.unssa_name ssa_name in
             if NameSet.mem name seen then (seen, fins) else (NameSet.add name seen, NameMap.add name ssa_name fins)
           )
           (NameSet.empty, NameMap.empty)
    in
    (* Once we find the final assignment to a variable v by a phi function,
       we explore all successor nodes from where that phi function is to check for cases like:

       v_a = phi(v_b, v_c);
       v_d = f(v_a);
       v_e = g(v_d);

       here v_e is the last assignment to v, not v_a
    *)
    let rec explore_successors node name ssa_name =
      match get_vertex cfg node with
      | Some ((_, cf_node), _, succs) ->
          let num_succs = IntSet.cardinal succs in
          let ssa_name =
            match cf_node with
            | CF_block (instrs, _) ->
                let last_write =
                  List.fold_left
                    (fun acc instr ->
                      match acc with
                      | None ->
                          let writes =
                            instr_writes instr
                            |> NameSet.filter (fun w ->
                                   let w', _ = unssa_name w in
                                   Name.compare name w' = 0
                               )
                          in
                          let num_writes = NameSet.cardinal writes in
                          if num_writes = 0 then None
                          else (
                            assert (num_writes = 1);
                            let write = NameSet.min_elt writes in
                            Some write
                          )
                      | Some v -> Some v
                    )
                    None (List.rev instrs)
                in
                Option.value last_write ~default:ssa_name
            | _ -> ssa_name
          in
          if num_succs = 0 then ssa_name
          else
            (* Note if we have successors like

                 A
                / \
               B   C
                \ /
                 D

               There could be updates in D, but there cannot be any in
               B or C because then D would have a phi function, and we
               would then have started from there. Therefore we can
               just choose a single successor here. *)
            explore_successors (IntSet.min_elt succs) name ssa_name
      | None -> assert false
    in
    let final_names =
      NameMap.mapi
        (fun name ssa_name ->
          let node = NameMap.find ssa_name phi_nodes in
          explore_successors node name ssa_name
        )
        final_names
    in
    let final_names =
      NameMap.fold
        (fun name nums fins ->
          if NameSet.mem name phi_names then fins
          else NameMap.add name (Jib_ssa.ssa_name (IntSet.max_elt nums) name) fins
        )
        ssa_vars final_names
    in
    final_names

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

  let never_returns end_node cfg =
    let open Jib_ssa in
    let _, preds, _ = Option.get (get_vertex cfg end_node) in
    IntSet.for_all
      (fun pred -> match get_vertex cfg pred with Some ((_, CF_block (_, T_exit _)), _, _) -> true | _ -> false)
      preds

  let natural_name_compare variable_locations n1 n2 =
    let open Lexing in
    let name_compare id1 id2 ssa_num1 ssa_num2 =
      let c = natural_id_compare id1 id2 in
      if c <> 0 then c else Int.compare ssa_num1 ssa_num2
    in
    match (n1, n2) with
    | Name (id1, ssa_num1), Name (id2, ssa_num2) -> (
        let get_pos id = Option.bind (Bindings.find_opt id variable_locations) Reporting.simp_loc in
        match (get_pos id1, get_pos id2) with
        | Some (p1, _), Some (p2, _) ->
            let c = Int.compare p1.pos_cnum p2.pos_cnum in
            if c <> 0 then c else name_compare id1 id2 ssa_num1 ssa_num2
        | _ -> name_compare id1 id2 ssa_num1 ssa_num2
      )
    | _ -> Name.compare n1 n2

  let svir_module ?debug_attr ?(footprint = pure_footprint) ?(return_vars = [Jib_util.return]) spec_info ctx name params
      param_ctyps ret_ctyps body =
    let footprint, is_recursive =
      match name with
      | SVN_id id ->
          let footprint = Bindings.find_opt id spec_info.footprints |> Option.value ~default:footprint in
          let is_recursive =
            IdGraph.children spec_info.callgraph id
            |> List.find_opt (fun callee -> Id.compare id callee = 0)
            |> Option.is_some
          in
          (footprint, is_recursive)
      | SVN_string _ -> (footprint, false)
    in

    let always_comb = Queue.create () in
    let declvars = ref Bindings.empty in
    let ssa_vars = ref NameMap.empty in

    (* Add a statement to the always_comb block *)
    let add_comb_statement stmt =
      let stmt = visit_sv_statement (new register_fix_visitor spec_info ssa_vars) stmt in
      Queue.add stmt always_comb
    in

    let open Jib_ssa in
    let _, end_node, cfg =
      ssa
        ~globals:(NameSet.diff spec_info.global_lets (NameSet.of_list (List.map Jib_util.name params)))
        ?debug_prefix:(Option.map (fun _ -> string_of_sv_name name) debug_attr)
        (visit_instrs (new thread_registers ctx spec_info) body)
    in

    if never_returns end_node cfg then prerr_endline ("NEVER RETURNS: " ^ string_of_sv_name name);

    if Option.is_some debug_attr && not (debug_attr_skip_graph debug_attr) then dump_graph (string_of_sv_name name) cfg;

    let visit_order =
      try topsort cfg
      with Not_a_DAG n ->
        raise
          (Reporting.err_general Parse_ast.Unknown
             (Printf.sprintf "%s: control flow graph is not acyclic (node %d is in cycle)" (string_of_sv_name name) n)
          )
    in

    let variable_locations = ref Bindings.empty in
    List.iter
      (iter_instr (function
        | I_aux (I_decl (_, Name (id, _)), (_, l)) | I_aux (I_init (_, Name (id, _), _), (_, l)) ->
            variable_locations := Bindings.add id l !variable_locations
        | _ -> ()
        )
        )
      body;

    let phivars = ref (-1) in
    let phivar () =
      incr phivars;
      Jib_util.name (mk_id ("phi#" ^ string_of_int !phivars))
    in

    (* Generate the contents of the always_comb block *)
    let _ =
      Smt_gen.iterM
        (fun n ->
          match get_vertex cfg n with
          | None -> return ()
          | Some ((ssa_elems, cfnode), preds, _) ->
              let preds =
                List.map
                  (fun pred ->
                    match Option.get (get_vertex cfg pred) with
                    | (_, CF_block (_, T_exit _)), _, _ -> None
                    | _ -> Some pred
                  )
                  (IntSet.elements preds)
              in
              let get_pi n =
                match get_vertex cfg n with
                | Some ((ssa_elems, _), _, _) ->
                    List.concat (List.map (function Pi guards -> guards | _ -> []) ssa_elems)
                | None -> failwith "Predecessor node does not exist"
              in
              let pis = List.map (Option.map get_pi) preds in
              let* pathconds =
                mapM
                  (function
                    | Some pi ->
                        let* pi = mapM Smt.smt_cval pi in
                        return (Some (Smt_exp.simp SimpSet.empty (smt_conj pi)))
                    | None -> return None
                    )
                  pis
              in
              let pathcond_vars =
                List.map
                  (function
                    | Some pathcond ->
                        let id = phivar () in
                        add_comb_statement (SVS_aux (SVS_var (id, CT_bool, Some pathcond), Parse_ast.Unknown));
                        Some (Var id)
                    | None -> None
                    )
                  pathconds
              in
              let* muxers = fmap Util.option_these (mapM (smt_ssanode cfg pathcond_vars) ssa_elems) in
              let muxers =
                List.stable_sort
                  (fun (id1, _, _) (id2, _, _) -> natural_name_compare !variable_locations id1 id2)
                  muxers
              in
              List.iter
                (fun (id, ctyp, mux) ->
                  add_comb_statement
                    (SVS_aux (SVS_assign (SVP_id id, Smt_exp.simp SimpSet.empty mux), Parse_ast.Unknown))
                )
                muxers;
              let* this_pathcond =
                let* pi = mapM Smt.smt_cval (get_pi n) in
                return (Smt_exp.simp SimpSet.empty (smt_conj pi))
              in
              let* block = svir_cfnode spec_info ctx this_pathcond cfnode in
              List.iter add_comb_statement block;
              return ()
        )
        visit_order
      |> fun m -> Smt_gen.run m Parse_ast.Unknown
    in

    let final_names = get_final_names !ssa_vars cfg in

    (* Create the always_comb definition, lifting/hoisting the module instantations out of the block *)
    let module_instantiations = Queue.create () in
    let always_comb_def =
      let fix s = visit_sv_statement (new hoist_module_statements spec_info declvars module_instantiations) s in
      let mk_always_comb = function
        | [] -> None
        | [statement] -> Some (fix statement)
        | statements -> Some (fix (SVS_aux (SVS_block statements, Parse_ast.Unknown)))
      in
      match Queue.to_seq always_comb |> List.of_seq |> mk_always_comb with
      | None -> []
      | Some (SVS_aux (SVS_block statements, l)) ->
          Util.delimit_list is_split_comb statements
          |> List.map (function [] -> None | statements -> Some (SVD_always_comb (SVS_aux (SVS_block statements, l))))
          |> Util.option_these
      | Some (SVS_aux (SVS_split_comb, _)) -> []
      | Some statement -> [SVD_always_comb statement]
    in
    let module_instantiation_defs, _ =
      Queue.fold
        (fun (defs, numbers) (place, module_name, inputs) ->
          let number = match SVNameMap.find_opt module_name numbers with None -> 0 | Some n -> n in
          let instance_name =
            match modify_sv_name ~prefix:("inst_" ^ string_of_int number ^ "_") module_name with
            | SVN_id id -> pp_id_string id
            | SVN_string s -> s
          in
          let outputs = match place with SVP_multi places -> places | place -> [place] in
          ( SVD_instantiate { module_name; instance_name; input_connections = inputs; output_connections = outputs }
            :: defs,
            SVNameMap.add module_name (number + 1) numbers
          )
        )
        ([], SVNameMap.empty) module_instantiations
    in

    (* Create the input and output ports *)
    let input_ports : sv_module_port list =
      List.map2 (fun id ctyp -> { name = Name (id, 0); external_name = string_of_id id; typ = ctyp }) params param_ctyps
      @ List.map
          (fun id ->
            {
              name = Name (id, 0);
              external_name = string_of_id (prepend_id "in_" id);
              typ = Bindings.find id spec_info.registers;
            }
          )
          (natural_sort_ids (IdSet.elements (IdSet.union footprint.all_writes footprint.all_reads)))
      @ ( if footprint.need_stdout then
            [{ name = Channel (Chan_stdout, 0); external_name = "in_stdout"; typ = CT_string }]
          else []
        )
      @ ( if footprint.need_stderr then
            [{ name = Channel (Chan_stderr, 0); external_name = "in_stderr"; typ = CT_string }]
          else []
        )
      @ ( if footprint.writes_mem then [{ name = Memory_writes 0; external_name = "in_writes"; typ = CT_memory_writes }]
          else []
        )
      @
      if footprint.contains_assert then
        [{ name = Name (mk_id "assert_reachable#", -1); external_name = "assert_reachable"; typ = CT_bool }]
      else []
    in

    let register_passthroughs = Queue.create () in
    let output_register name =
      match NameMap.find name final_names with
      | Name (id, 0) ->
          Queue.add
            (SVS_aux (SVS_assign (SVP_id (Name (id, 1)), Var (Name (id, 0))), Parse_ast.Unknown))
            register_passthroughs;
          Name (id, 1)
      | name -> name
    in

    let get_final_name name = match NameMap.find_opt name final_names with Some n -> n | None -> name in

    let output_ports : sv_module_port list =
      List.map2
        (fun var ret_ctyp -> { name = get_final_name var; external_name = ""; typ = ret_ctyp })
        return_vars ret_ctyps
      @ List.map
          (fun id ->
            {
              name = output_register (Name (id, -1));
              external_name = string_of_id (prepend_id "out_" id);
              typ = Bindings.find id spec_info.registers;
            }
          )
          (natural_sort_ids (IdSet.elements footprint.all_writes))
      @ ( if footprint.throws || footprint.exits then
            [
              { name = get_final_name (Have_exception (-1)); external_name = "have_exception"; typ = CT_bool };
              {
                name = get_final_name (Current_exception (-1));
                external_name = "current_exception";
                typ = spec_info.exception_ctyp;
              };
            ]
          else []
        )
      @ ( if footprint.need_stdout then
            [
              {
                name = NameMap.find (Channel (Chan_stdout, -1)) final_names;
                external_name = "out_stdout";
                typ = CT_string;
              };
            ]
          else []
        )
      @ ( if footprint.writes_mem then
            [{ name = get_final_name (Memory_writes (-1)); external_name = "out_writes"; typ = CT_memory_writes }]
          else []
        )
      @
      if footprint.need_stderr then
        [{ name = NameMap.find (Channel (Chan_stderr, -1)) final_names; external_name = "out_stderr"; typ = CT_string }]
      else []
    in

    (* Create toplevel variables for all things in the always_comb
       block that aren't ports. We can push variables that aren't used
       in the block back down later if we want. *)
    let module_vars = Queue.create () in
    NameMap.iter
      (fun name nums ->
        let get_ctyp = function
          | Return _ -> Some (List.hd ret_ctyps)
          | Name (id, _) -> begin
              match Bindings.find_opt id spec_info.registers with
              | Some ctyp -> Some ctyp
              | None -> (
                  match Bindings.find_opt id !declvars with
                  | Some ctyp -> Some ctyp
                  | None -> (
                      match Util.list_index (fun p -> Id.compare p id = 0) params with
                      | Some i -> Some (List.nth param_ctyps i)
                      | None -> None
                    )
                )
            end
          | Channel _ -> Some CT_string
          | Memory_writes _ -> Some CT_memory_writes
          | Have_exception _ -> Some CT_bool
          | Throw_location _ -> Some CT_string
          | Current_exception _ -> Some spec_info.exception_ctyp
        in
        match get_ctyp name with
        | Some ctyp ->
            IntSet.iter
              (fun n ->
                let name = Jib_ssa.ssa_name n name in
                if
                  List.for_all
                    (fun (port : sv_module_port) -> Name.compare name port.name <> 0)
                    (input_ports @ output_ports)
                then Queue.add (SVD_var (name, ctyp)) module_vars
              )
              nums
        | None -> ()
      )
      !ssa_vars;

    let passthroughs =
      match List.of_seq (Queue.to_seq register_passthroughs) with
      | [] -> []
      | statements -> [SVD_always_comb (SVS_aux (SVS_block statements, Parse_ast.Unknown))]
    in

    let defs =
      passthroughs @ List.of_seq (Queue.to_seq module_vars) @ List.rev module_instantiation_defs @ always_comb_def
    in
    { name; recursive = is_recursive; input_ports; output_ports; defs = List.map mk_def defs }

  let toplevel_module id spec_info fn_ctyps =
    if not (Bindings.mem id fn_ctyps && Bindings.mem id spec_info.footprints) then
      raise
        (Reporting.err_general Parse_ast.Unknown
           ("Cannot generate toplevel module for " ^ string_of_id id ^ " as it has no type or footprint")
        );

    let def_annot, arg_ctyps, ret_ctyp = Bindings.find id fn_ctyps in
    let footprint = Bindings.find id spec_info.footprints in

    (* Handle any options on the sv_toplevel attribute, if present *)
    let attr, (module ToplevelAttr) = get_sv_def_attribute "sv_toplevel" def_annot in
    let module Attr = AttributeParser (ToplevelAttr) in
    (* If true, we will generate a module with an input clk and reset signal. *)
    let clk = Attr.get_bool ~default:false "clk" attr in
    (* Type conversions for the module input signals derived from function arguments. *)
    let arg_conversions = Attr.get_types ~arity:(List.length arg_ctyps) attr in
    (* Registers that are exposed as output ports *)
    let exposed = Attr.get_string_set ~default:StringSet.empty "expose" attr in
    (* Text used to bracket output *)
    let prefix = Attr.get_string ~default:"SAIL START\\n" "prefix" attr in
    let suffix = Attr.get_string ~default:"SAIL END\\n" "suffix" attr in

    let register_resets, register_inputs, register_outputs =
      Bindings.fold
        (fun reg ctyp (resets, ins, outs) ->
          ( mk_port (Name (prepend_id "reset_" reg, -1)) ctyp :: resets,
            SVD_var (Name (prepend_id "in_" reg, -1), ctyp) :: ins,
            SVD_var (Name (prepend_id "out_" reg, -1), ctyp) :: outs
          )
        )
        spec_info.registers ([], [], [])
    in
    let exposed_registers =
      Bindings.fold
        (fun reg ctyp ports -> if StringSet.mem (string_of_id reg) exposed then (reg, ctyp) :: ports else ports)
        spec_info.registers []
    in
    let memory_writes =
      [
        SVD_var (Name (mk_id "empty_memory_writes", -1), CT_memory_writes);
        SVD_var (Name (mk_id "out_memory_writes", -1), CT_memory_writes);
      ]
    in
    let throws_outputs =
      if footprint.throws || footprint.exits then
        [SVD_var (Have_exception (-1), CT_bool); SVD_var (Current_exception (-1), spec_info.exception_ctyp)]
      else []
    in
    let channel_outputs =
      (if footprint.need_stdout then [SVD_var (Name (mk_id "out_stdout", -1), CT_string)] else [])
      @ if footprint.need_stderr then [SVD_var (Name (mk_id "out_stderr", -1), CT_string)] else []
    in
    let arg_name n = name (mk_id ("arg" ^ string_of_int n)) in
    let arg_cvals = List.mapi (fun n ctyp -> V_id (arg_name n, ctyp)) arg_ctyps in
    let args, arg_ctyps =
      List.split (fst (Smt_gen.run (convert_arguments ~reverse:true arg_cvals arg_conversions) Parse_ast.Unknown))
    in
    let arg_ports = List.mapi (fun n ctyp -> mk_port (arg_name n) ctyp) arg_ctyps in
    let instantiate_main =
      SVD_instantiate
        {
          module_name = SVN_id id;
          instance_name = string_of_id (prepend_id "inst_" id);
          input_connections =
            (args
            @ List.map
                (fun reg -> Var (Name (prepend_id "in_" reg, -1)))
                (natural_sort_ids (IdSet.elements (IdSet.union footprint.all_writes footprint.all_reads)))
            @ (if footprint.need_stdout then [String_lit ""] else [])
            @ (if footprint.need_stderr then [String_lit ""] else [])
            @ (if footprint.writes_mem then [Var (Name (mk_id "empty_memory_writes", -1))] else [])
            @ if footprint.contains_assert then [Bool_lit true] else []
            );
          output_connections =
            ([SVP_id Jib_util.return]
            @ List.map
                (fun reg -> SVP_id (Name (prepend_id "out_" reg, -1)))
                (natural_sort_ids (IdSet.elements footprint.all_writes))
            @ ( if footprint.throws || footprint.exits then
                  [SVP_id (Have_exception (-1)); SVP_id (Current_exception (-1))]
                else []
              )
            @ (if footprint.need_stdout then [SVP_id (Name (mk_id "out_stdout", -1))] else [])
            @ (if footprint.need_stderr then [SVP_id (Name (mk_id "out_stderr", -1))] else [])
            @ if footprint.writes_mem then [SVP_id (Name (mk_id "out_memory_writes", -1))] else []
            );
        }
    in
    let initialize_letbindings =
      List.map
        (fun (n, ids) ->
          let module_name = SVN_string (sprintf "sail_setup_let_%d" n) in
          SVD_instantiate
            {
              module_name;
              instance_name = sprintf "sail_inst_let_%d" n;
              input_connections = [];
              output_connections = List.map (fun id -> SVP_id (name id)) ids;
            }
        )
        (IntMap.bindings spec_info.global_let_numbers)
    in
    let always_block =
      let channel_writes =
        ( if footprint.need_stdout then
            [
              mk_statement
                (svs_raw
                   (Printf.sprintf "$write({\"%s\", out_stdout, \"%s\"})" prefix suffix)
                   ~inputs:[Name (mk_id "out_stdout", -1)]
                );
            ]
          else []
        )
        @ ( if footprint.need_stderr then
              [mk_statement (svs_raw "$write(out_stderr)" ~inputs:[Name (mk_id "out_stderr", -1)])]
            else []
          )
        @ List.map
            (fun (reg, _) ->
              mk_statement (SVS_continuous_assign (SVP_id (Name (reg, -1)), Var (Name (prepend_id "out_" reg, -1))))
            )
            exposed_registers
        @ [mk_statement (svs_raw "sail_flush_writes(out_memory_writes)" ~inputs:[Name (mk_id "out_memory_writes", -1)])]
      in
      if clk then (
        let reset_regs, inout_regs =
          Bindings.fold
            (fun reg ctyp (resets, inouts) ->
              ( mk_statement
                  (SVS_continuous_assign
                     (SVP_id (Name (prepend_id "in_" reg, -1)), Var (Name (prepend_id "reset_" reg, -1)))
                  )
                :: resets,
                mk_statement
                  (SVS_continuous_assign
                     (SVP_id (Name (prepend_id "in_" reg, -1)), Var (Name (prepend_id "out_" reg, -1)))
                  )
                :: inouts
              )
            )
            spec_info.registers ([], [])
        in
        let on_reset = mk_statement (SVS_block reset_regs) in
        let on_clock = mk_statement (SVS_block (inout_regs @ channel_writes)) in
        SVD_always_ff
          (mk_statement (SVS_block [mk_statement (SVS_if (Var (name (mk_id "reset")), Some on_reset, Some on_clock))]))
      )
      else (
        let unchanged_registers =
          Bindings.fold
            (fun reg _ unchanged ->
              if not (IdSet.mem reg footprint.all_writes) then
                mk_statement
                  (SVS_assign (SVP_id (Name (prepend_id "out_" reg, -1)), Var (Name (prepend_id "in_" reg, -1))))
                :: unchanged
              else unchanged
            )
            spec_info.registers []
        in
        SVD_always_comb
          (mk_statement (SVS_block (unchanged_registers @ channel_writes @ [mk_statement (svs_raw "$finish")])))
      )
    in
    let initialize_registers =
      let reset_target reg = prepend_id (if clk then "reset_" else "in_") reg in
      List.mapi
        (fun i reg ->
          let name = sprintf "sail_setup_reg_%s" (pp_id_string reg) in
          SVD_instantiate
            {
              module_name = SVN_string name;
              instance_name = sprintf "reg_init_%d" i;
              input_connections = [];
              output_connections = [SVP_id (Name (reset_target reg, -1))];
            }
        )
        spec_info.initialized_registers
    in
    let return_def, output_ports =
      match ret_ctyp with
      | CT_unit -> ([SVD_var (Jib_util.return, CT_unit)], [])
      | _ -> ([], [mk_port Jib_util.return ret_ctyp])
    in
    let defs =
      register_inputs @ register_outputs @ throws_outputs @ channel_outputs @ memory_writes @ return_def
      @ initialize_letbindings @ initialize_registers @ [instantiate_main; always_block]
    in
    {
      name = SVN_string "sail_toplevel";
      recursive = false;
      input_ports =
        ( if clk then
            [mk_port (name (mk_id "clk")) CT_bit; mk_port (name (mk_id "reset")) CT_bit] @ arg_ports @ register_resets
          else arg_ports
        );
      output_ports = output_ports @ List.map (fun (reg, ctyp) -> mk_port (Name (reg, -1)) ctyp) exposed_registers;
      defs = List.map mk_def defs;
    }

  let rec pp_module m =
    let params = if m.recursive then space ^^ string "#(parameter RECURSION_DEPTH = 10)" ^^ space else empty in
    let ports =
      match (m.input_ports, m.output_ports) with
      | [], [] -> semi
      | inputs, outputs ->
          let ports = List.map (fun port -> ("input", port)) inputs @ List.map (fun port -> ("output", port)) outputs in
          let pp_port (dir, { name; external_name; typ }) =
            let external_name_hint =
              if external_name = "" then empty else space ^^ string (Printf.sprintf "/* %s */" external_name)
            in
            string dir ^^ space ^^ wrap_type typ (pp_name name) ^^ external_name_hint
          in
          nest 4 (char '(' ^^ hardline ^^ separate_map (comma ^^ hardline) pp_port ports)
          ^^ hardline ^^ char ')' ^^ semi
    in
    let generate doc =
      if m.recursive then (
        let wrap_generate doc = nest 4 (hardline ^^ string "generate" ^^ doc ^^ hardline ^^ string "endgenerate") in
        wrap_generate (nest 4 (hardline ^^ string "if (RECURSION_DEPTH > 0) begin" ^^ doc ^^ hardline ^^ string "end"))
      )
      else doc
    in
    string "module" ^^ space ^^ pp_sv_name m.name ^^ params ^^ ports
    ^^ generate (nest 4 (hardline ^^ separate_map hardline (pp_def (Some m.name)) m.defs))
    ^^ hardline ^^ string "endmodule"

  and pp_fundef f =
    let ret_ty, typedef =
      match f.return_type with
      | Some ret_ctyp ->
          let ret_ty, index_ty = sv_ctyp ret_ctyp in
          begin
            match index_ty with
            | Some index ->
                let encoded = Util.zencode_string (string_of_ctyp ret_ctyp) in
                let new_ty = string ("t_" ^ pp_sv_name_string f.function_name ^ "_" ^ encoded) in
                ( new_ty,
                  separate space [string "typedef"; string ret_ty; new_ty; string index] ^^ semi ^^ twice hardline
                )
            | None -> (string ret_ty, empty)
          end
      | None -> (string "void", empty)
    in
    let param_docs = List.map (fun (param, ctyp) -> wrap_type ctyp (pp_id param)) f.params in
    let block_terminator last = if last then semi else semi ^^ hardline in
    let pp_body = function
      | SVS_aux (SVS_block statements, _) ->
          concat (Util.map_last (fun last -> pp_statement ~terminator:(block_terminator last)) statements)
      | statement -> pp_statement ~terminator:semi statement
    in
    typedef
    ^^ separate space [string "function"; string "automatic"; ret_ty; pp_sv_name f.function_name]
    ^^ parens (separate (comma ^^ space) param_docs)
    ^^ semi
    ^^ nest 4 (hardline ^^ pp_body f.body)
    ^^ hardline ^^ string "endfunction"

  and pp_def in_module (SVD_aux (aux, _)) =
    match aux with
    | SVD_null -> empty
    | SVD_var (id, ctyp) -> wrap_type ctyp (pp_name id) ^^ semi
    | SVD_initial statement -> string "initial" ^^ space ^^ pp_statement ~terminator:semi statement
    | SVD_always_ff statement ->
        let posedge_clk = char '@' ^^ parens (string "posedge" ^^ space ^^ string "clk") in
        separate space [string "always_ff"; posedge_clk; pp_statement ~terminator:semi statement]
    | SVD_always_comb statement -> string "always_comb" ^^ space ^^ pp_statement ~terminator:semi statement
    | SVD_instantiate { module_name; instance_name; input_connections; output_connections } ->
        let params =
          match in_module with
          | Some name when SVName.compare module_name name = 0 -> space ^^ string "#(RECURSION_DEPTH - 1)"
          | _ -> empty
        in
        let inputs = List.map (fun exp -> pp_smt exp) input_connections in
        let outputs = List.map pp_place output_connections in
        let connections =
          match inputs @ outputs with
          | [] -> parens empty
          | connections -> parens (separate (comma ^^ space) connections)
        in
        pp_sv_name module_name ^^ params ^^ space ^^ string instance_name ^^ connections ^^ semi
    | SVD_fundef f -> pp_fundef f
    | SVD_module m -> pp_module m
    | SVD_type type_def -> pp_type_def type_def
    | SVD_dpi_function { function_name; return_type; param_types } ->
        let ret_ty, typedef =
          match return_type with
          | Some ret_ctyp ->
              (* Per the SystemVerilog LRM, a DPI function can only return
                 two-state types other than a single logic *)
              let ret_ty, index_ty = sv_ctyp ~two_state:true ret_ctyp in
              begin
                match index_ty with
                | Some index ->
                    let encoded = Util.zencode_string (string_of_ctyp ret_ctyp) in
                    let new_ty = string ("t_" ^ pp_sv_name_string function_name ^ "_" ^ encoded) in
                    ( new_ty,
                      separate space [string "typedef"; string ret_ty; new_ty; string index] ^^ semi ^^ twice hardline
                    )
                | None -> (string ret_ty, empty)
              end
          | None -> (string "void", empty)
        in
        let params = List.mapi (fun n ctyp -> wrap_type ctyp (string ("param" ^ string_of_int n))) param_types in
        typedef
        ^^ separate space [string "import"; string "\"DPI-C\""; string "function"; ret_ty; pp_sv_name function_name]
        ^^ parens (separate (comma ^^ space) params)
        ^^ semi

  let sv_fundef_with ctx f params param_ctyps ret_ctyp fun_body =
    let sv_ret_ty, index_ty = sv_ctyp ret_ctyp in
    let sv_ret_ty, typedef =
      match index_ty with
      | Some index ->
          let encoded = Util.zencode_string (string_of_ctyp ret_ctyp) in
          let new_ty = string ("t_" ^ f ^ "_" ^ encoded) in
          (new_ty, separate space [string "typedef"; string sv_ret_ty; new_ty; string index] ^^ semi ^^ twice hardline)
      | None -> (string sv_ret_ty, empty)
    in
    let param_docs =
      try List.map2 (fun param ctyp -> wrap_type ctyp (pp_id param)) params param_ctyps
      with Invalid_argument _ -> Reporting.unreachable Unknown __POS__ "Function arity mismatch"
    in
    typedef
    ^^ separate space [string "function"; string "automatic"; sv_ret_ty; string f]
    ^^ parens (separate (comma ^^ space) param_docs)
    ^^ semi
    ^^ nest 4 (hardline ^^ fun_body)
    ^^ hardline ^^ string "endfunction"

  let sv_fundef spec_info ctx f params param_ctyps ret_ctyp body =
    pp_module (svir_module spec_info ctx f params param_ctyps ret_ctyp body)

  let filter_clear = filter_instrs (function I_aux (I_clear _, _) -> false | _ -> true)

  let variable_decls_to_top instrs =
    let decls, others =
      List.fold_left
        (fun (decls, others) instr ->
          match instr with
          | I_aux (I_decl (ctyp, id), (_, l)) -> (idecl l ctyp id :: decls, others)
          | I_aux (I_init (ctyp, id, Init_cval cval), (_, l)) ->
              (idecl l ctyp id :: decls, icopy l (CL_id (id, ctyp)) cval :: others)
          | other -> (decls, other :: others)
        )
        ([], []) instrs
    in
    List.rev decls @ List.rev others

  let sv_setup_function spec_info ctx name setup =
    let setup =
      Jib_optimize.(
        setup |> remove_undefined |> flatten_instrs |> remove_dead_code |> variable_decls_to_top
        |> structure_control_flow_block |> filter_clear
      )
    in
    separate space [string "function"; string "automatic"; string "void"; string name]
    ^^ string "()" ^^ semi
    ^^ nest 4 (hardline ^^ separate_map hardline (sv_checked_instr spec_info ctx) setup)
    ^^ hardline ^^ string "endfunction" ^^ twice hardline

  let svir_setup_module spec_info ctx name out ctyp setup =
    svir_module ~return_vars:[out] spec_info ctx name [] [] [ctyp] setup

  let svir_setup_function l spec_info ctx name setup =
    let setup =
      Jib_optimize.(
        setup |> remove_undefined |> flatten_instrs |> remove_dead_code |> variable_decls_to_top
        |> structure_control_flow_block |> filter_clear
      )
    in
    let statements, _ = Smt_gen.run (fmap Util.option_these (mapM (svir_instr spec_info ctx) setup)) (gen_loc l) in
    SVD_fundef
      {
        function_name = SVN_string name;
        return_type = None;
        params = [];
        body = SVS_aux (SVS_block statements, gen_loc l);
      }

  let collect_registers cdefs =
    List.fold_left
      (fun rmap cdef ->
        match cdef with
        | CDEF_aux (CDEF_register (id, ctyp, _), _) ->
            CTMap.update ctyp (function Some ids -> Some (id :: ids) | None -> Some [id]) rmap
        | _ -> rmap
      )
      CTMap.empty cdefs

  let sv_register_references spec_info =
    let rmap = spec_info.register_ctyp_map in
    let reg_ref id = "SAIL_REG_" ^ Util.zencode_upper_string (string_of_id id) in
    let check reg = parens (separate space [char 'r'; string "=="; string (reg_ref reg)]) in
    let reg_ref_enums =
      List.map
        (fun (ctyp, regs) ->
          let regs = natural_sort_ids (IdSet.elements regs) in
          separate space [string "typedef"; string "enum"; lbrace]
          ^^ nest 4 (hardline ^^ separate_map (comma ^^ hardline) (fun r -> string (reg_ref r)) regs)
          ^^ hardline ^^ rbrace ^^ space
          ^^ ksprintf string "sail_reg_%s" (Util.zencode_string (string_of_ctyp ctyp))
          ^^ semi
        )
        (CTMap.bindings rmap)
      |> separate (twice hardline)
    in
    let reg_ref_functions =
      List.map
        (fun (ctyp, regs) ->
          let regs = natural_sort_ids (IdSet.elements regs) in
          let encoded = Util.zencode_string (string_of_ctyp ctyp) in
          let sv_ty, index_ty = sv_ctyp ctyp in
          let sv_ty, typedef =
            match index_ty with
            | Some index ->
                let new_ty = string ("t_reg_deref_" ^ encoded) in
                (new_ty, separate space [string "typedef"; string sv_ty; new_ty; string index] ^^ semi ^^ twice hardline)
            | None -> (string sv_ty, empty)
          in
          let port ~input ty v = separate space [string (if input then "input" else "output"); ty; v] in
          let assign_module =
            let ports =
              port ~input:true (string ("sail_reg_" ^ encoded)) (char 'r')
              :: port ~input:true sv_ty (char 'v')
              :: List.map (fun r -> port ~input:true sv_ty (pp_id (prepend_id "in_" r))) regs
              @ List.map (fun r -> port ~input:false sv_ty (pp_id (prepend_id "out_" r))) regs
            in
            let assignment reg =
              separate space
                [
                  pp_id (prepend_id "out_" reg);
                  equals;
                  check reg;
                  char '?';
                  char 'v';
                  colon;
                  pp_id (prepend_id "in_" reg);
                ]
            in
            let comb =
              nest 4 (string "begin" ^^ hardline ^^ separate_map (semi ^^ hardline) assignment regs ^^ semi)
              ^^ hardline ^^ string "end" ^^ semi
            in
            string "module" ^^ space
            ^^ string ("sail_reg_assign_" ^ encoded)
            ^^ nest 4 (lparen ^^ hardline ^^ separate (comma ^^ hardline) ports)
            ^^ hardline ^^ rparen ^^ semi
            ^^ nest 4 (hardline ^^ string "always_comb" ^^ space ^^ comb)
            ^^ hardline ^^ string "endmodule"
          in
          let deref_module =
            let ports =
              port ~input:true (string ("sail_reg_" ^ encoded)) (char 'r')
              :: List.map (fun r -> port ~input:true sv_ty (pp_id (prepend_id "in_" r))) regs
              @ [port ~input:false sv_ty (char 'v')]
            in
            let cases =
              List.map
                (fun reg ->
                  let assign = separate space [char 'v'; equals; pp_id (prepend_id "in_" reg)] in
                  (check reg, assign)
                )
                regs
            in
            let ifstmt =
              match cases with
              | [(_, assign)] -> assign
              | _ ->
                  let ifs =
                    Util.map_last
                      (fun last (check, assign) ->
                        if last then nest 4 (hardline ^^ assign)
                        else string "if" ^^ space ^^ check ^^ nest 4 (hardline ^^ assign ^^ semi)
                      )
                      cases
                  in
                  separate (hardline ^^ string "else" ^^ space) ifs
            in
            string "module" ^^ space
            ^^ string ("sail_reg_deref_" ^ encoded)
            ^^ nest 4 (lparen ^^ hardline ^^ separate (comma ^^ hardline) ports)
            ^^ hardline ^^ rparen ^^ semi
            ^^ nest 4 (hardline ^^ string "always_comb" ^^ space ^^ ifstmt ^^ semi)
            ^^ hardline ^^ string "endmodule"
          in
          typedef ^^ assign_module ^^ twice hardline ^^ deref_module
        )
        (CTMap.bindings rmap)
      |> separate (twice hardline)
    in
    (reg_ref_enums ^^ twice hardline, reg_ref_functions ^^ twice hardline)

  type cdef_doc = { outside_module : document; inside_module_prefix : document; inside_module : document }

  let empty_cdef_doc = { outside_module = empty; inside_module_prefix = empty; inside_module = empty }

  let svir_cdef spec_info ctx fn_ctyps (CDEF_aux (aux, def_annot)) =
    match aux with
    | CDEF_val (f, ext_name, param_ctyps, ret_ctyp) ->
        let attr, (module FunctionAttr) = get_sv_def_attribute "sv_function" def_annot in
        if Option.is_some attr then
          let module Attr = AttributeParser (FunctionAttr) in
          match Attr.get_dpi Config.dpi_sets attr with
          (* If the dpi attribute isn't present, or is false don't do anything *)
          | None | Some false -> ([], Bindings.add f (def_annot, param_ctyps, ret_ctyp) fn_ctyps)
          | Some true ->
              let ret_ctyp = match Attr.get_return_type attr with None -> ret_ctyp | Some ctyp' -> ctyp' in
              let param_ctyps =
                match Attr.get_types ~arity:(List.length param_ctyps) attr with
                | None -> param_ctyps
                | Some conversions ->
                    List.map
                      (fun (ctyp, convert) -> match convert with None -> ctyp | Some ctyp' -> ctyp')
                      (List.combine param_ctyps conversions)
              in

              let dpi_import =
                SVD_aux
                  ( SVD_dpi_function
                      {
                        function_name = Option.fold ~none:(SVN_id f) ~some:(fun s -> SVN_string s) ext_name;
                        return_type = Some ret_ctyp;
                        param_types = param_ctyps;
                      },
                    def_annot.loc
                  )
              in
              ([dpi_import], Bindings.add f (def_annot, param_ctyps, ret_ctyp) fn_ctyps)
        else ([], Bindings.add f (def_annot, param_ctyps, ret_ctyp) fn_ctyps)
    | CDEF_fundef (f, _, params, body) ->
        let debug_attr = get_def_attribute "jib_debug" def_annot in
        if List.mem (string_of_id f) Config.ignore then ([], fn_ctyps)
        else (
          let body =
            Jib_optimize.(
              body |> remove_undefined |> remove_functions_to_references |> flatten_instrs |> remove_dead_code
              |> variable_decls_to_top |> filter_clear
            )
          in
          if Option.is_some debug_attr then (
            prerr_endline Util.("Pre-SV IR for " ^ string_of_id f ^ ":" |> yellow |> bold |> clear);
            List.iter (fun instr -> prerr_endline (string_of_instr instr)) body
          );
          match Bindings.find_opt f fn_ctyps with
          | Some (_, param_ctyps, ret_ctyp) ->
              ( [
                  SVD_aux
                    ( SVD_module (svir_module ?debug_attr spec_info ctx (SVN_id f) params param_ctyps [ret_ctyp] body),
                      def_annot.loc
                    );
                ],
                fn_ctyps
              )
          | None -> Reporting.unreachable (id_loc f) __POS__ ("No function type found for " ^ string_of_id f)
        )
    | CDEF_type type_def -> ([SVD_aux (SVD_type type_def, def_annot.loc)], fn_ctyps)
    | CDEF_let (n, bindings, setup) ->
        let setup =
          Jib_optimize.(
            setup |> remove_undefined |> remove_functions_to_references |> flatten_instrs |> remove_dead_code
            |> variable_decls_to_top |> filter_clear
          )
        in
        let module_name = SVN_string (sprintf "sail_setup_let_%d" n) in
        let setup_module =
          svir_module
            ~return_vars:(List.map (fun (id, _) -> name id) bindings)
            spec_info ctx module_name [] [] (List.map snd bindings)
            (setup @ [iundefined CT_unit])
        in
        ( List.map (fun (id, ctyp) -> SVD_aux (SVD_var (name id, ctyp), def_annot.loc)) bindings
          @ [SVD_aux (SVD_module setup_module, def_annot.loc)],
          fn_ctyps
        )
    | CDEF_register (id, ctyp, setup) -> begin
        match setup with
        | [] -> ([], fn_ctyps)
        | _ ->
            let setup =
              Jib_optimize.(
                setup |> remove_undefined |> remove_functions_to_references |> flatten_instrs |> remove_dead_code
                |> variable_decls_to_top |> filter_clear
              )
            in
            let setup_module =
              svir_setup_module spec_info ctx
                (SVN_string (sprintf "sail_setup_reg_%s" (pp_id_string id)))
                (name id) ctyp
                (setup @ [iend_id def_annot.loc id])
            in
            ([SVD_aux (SVD_module setup_module, def_annot.loc)], fn_ctyps)
      end
    | _ -> ([], fn_ctyps)

  let sv_cdef spec_info ctx fn_ctyps setup_calls (CDEF_aux (aux, _)) =
    match aux with
    | CDEF_register (id, ctyp, setup) ->
        let binding_doc = wrap_type ctyp (pp_id id) ^^ semi ^^ twice hardline in
        let name = sprintf "sail_setup_reg_%s" (pp_id_string id) in
        ( {
            empty_cdef_doc with
            inside_module_prefix = binding_doc;
            inside_module = sv_setup_function spec_info ctx name setup;
          },
          fn_ctyps,
          name :: setup_calls
        )
    | CDEF_type td -> ({ empty_cdef_doc with outside_module = pp_type_def td ^^ twice hardline }, fn_ctyps, setup_calls)
    | CDEF_val (f, _, param_ctyps, ret_ctyp) ->
        (empty_cdef_doc, Bindings.add f (param_ctyps, ret_ctyp) fn_ctyps, setup_calls)
    | CDEF_fundef (f, _, params, body) ->
        if List.mem (string_of_id f) Config.ignore then (empty_cdef_doc, fn_ctyps, setup_calls)
        else (
          let body =
            Jib_optimize.(
              body |> flatten_instrs |> remove_dead_code |> variable_decls_to_top (* |> structure_control_flow_block *)
              |> remove_undefined |> filter_clear
            )
          in
          begin
            match Bindings.find_opt f fn_ctyps with
            | Some (param_ctyps, ret_ctyp) ->
                ( {
                    empty_cdef_doc with
                    inside_module =
                      sv_fundef spec_info ctx (SVN_id f) params param_ctyps [ret_ctyp] body ^^ twice hardline;
                  },
                  fn_ctyps,
                  setup_calls
                )
            | None -> Reporting.unreachable (id_loc f) __POS__ ("No function type found for " ^ string_of_id f)
          end
        )
    | CDEF_let (n, bindings, setup) ->
        let bindings_doc =
          separate_map (semi ^^ hardline) (fun (id, ctyp) -> wrap_type ctyp (pp_id id)) bindings
          ^^ semi ^^ twice hardline
        in
        let name = sprintf "sail_setup_let_%d" n in
        ( { empty_cdef_doc with inside_module = bindings_doc ^^ sv_setup_function spec_info ctx name setup },
          fn_ctyps,
          name :: setup_calls
        )
    | _ -> (empty_cdef_doc, fn_ctyps, setup_calls)

  let main_args main fn_ctyps =
    match main with
    | Some (CDEF_aux (CDEF_fundef (f, _, params, body), _)) -> begin
        match Bindings.find_opt f fn_ctyps with
        | Some (param_ctyps, ret_ctyp) -> begin
            let main_args =
              List.map2
                (fun param param_ctyp -> match param_ctyp with CT_unit -> string "SAIL_UNIT" | _ -> pp_id param)
                params param_ctyps
            in
            let non_unit =
              List.filter_map
                (fun x -> x)
                (List.map2
                   (fun param param_ctyp -> match param_ctyp with CT_unit -> None | _ -> Some (param, param_ctyp))
                   params param_ctyps
                )
            in
            let module_main_in =
              List.map
                (fun (param, param_ctyp) -> string "input" ^^ space ^^ wrap_type param_ctyp (pp_id param))
                non_unit
            in
            match ret_ctyp with
            | CT_unit -> (main_args, None, module_main_in)
            | _ ->
                ( main_args,
                  Some (string "main_result"),
                  (string "output" ^^ space ^^ wrap_type ret_ctyp (string "main_result")) :: module_main_in
                )
          end
        | None -> Reporting.unreachable (id_loc f) __POS__ ("No function type found for " ^ string_of_id f)
      end
    | _ -> ([], None, [])

  let make_call_precise ctx id =
    if ctx_is_extern id ctx then (
      let name = ctx_get_extern id ctx in
      Option.is_none (Smt.builtin name)
    )
    else true
end
