(* This module contains a bunch of hacks to prepend global references with an SV macro.

    {1. Initial problem}

    For compatibility with EDA tools, global signals cannot be defined at toplevel.

    For example, below generated SV will throw [unresolved reference to my_global] :

    {[
      logic  another_toplevel_signal;
      logic  toplevel_signal;  // <<------ Global declared at toplevel

      module sail_setup_let_42 (
          output logic toplevel_signal_1
        );
        always_comb begin
          if (another_toplevel_signal)
              toplevel_signal_1 = 42;
    else
      toplevel_signal_1 = 24;
    end
      endmodule

      module yyy (input logic myin);
        logic y;
        assign y = toplevel_signal; // <<------ Global reference unresovled
          endmodule

      module sail_toplevel ();
        sail_setup_let_42 sail_setup_inst_42(toplevel_signal);
        always_comb begin
        end
          endmodule
    ]}

    {2. Suggested solution}

    This module contains a set of hacks to insert at various places during JIB-SV conversion
    which will yield the following changes :
    1. Moving the declaration of globals from toplevel into the [sail_toplevel] module
    2. Prepend references to globals with a macro where the user will insert the hierarchical path
       to the [sail_toplevel] instance.

    However there are a few additional things to do to make it work :
    3. Prepending should NOT be done in the sail_toplevel module (because this is where the globals are declared)
    4. Prepending in the the [sail_setup_let_] modules (where the globals are initialized),
       should ideally be done everywhere in the module but NOT on the output (we don't want [output logic `SAIL_GLOBALS.my_global]).
       But removing prepending only on the output is an intrusive change in the sail codebase,
       so what we'll do is just remove the output,
       and the [sail_setup_let_] module will drive the globals via the hierarchical reference.
    5. The very last thing is also on the [sail_setup_let_] modules,
       for the global [`SAIL_GLOBALS.my_global], the [sail_setup_let_] module
       will drive [`SAIL_GLOBALS.my_global_1] (notice the [_1]).
       And we haven't found a non-impactful easy way to just remove the [_1] in the [sail_setup_let_] modules,
       so we'll just add a "duplicate" [my_global_1] signal in [sail_toplevel] and assign it to [my_global] to make the connection.

    With all those changes, the diff will be :

    {[
      + `define SAIL_GLOBALS path.to.sail_toplevel_instance          // will be manually added by the user
                                    +
                                    - logic  another_toplevel_signal;                              // (1.) moved to sail_toplevel
                                                                                                                    - logic  toplevel_signal;                                      // (1.) moved to sail_toplevel

      module sail_setup_let_42 (
          -   output `SAIL_GLOBALS.logic toplevel_signal_1               // (4.) remove output
        );
        always_comb begin
          +     if (`SAIL_GLOBALS.another_toplevel_signal)               // (2.) prepending
                   +       `SAIL_GLOBALS.toplevel_signal_1 = 42;                  // (2.) prepending
    else
      +       `SAIL_GLOBALS.toplevel_signal_1 = 24;                  // (2.) prepending
    end
      endmodule

      module yyy (input logic myin);
        logic y;
        +   assign y = `SAIL_GLOBALS.toplevel_signal;                  // (2.) prepending (Global reference is fixed !)
          endmodule

      module sail_toplevel ();
        + logic  another_toplevel_signal;                              // (1.) moved to sail_toplevel
                                                                                        + logic  toplevel_signal;                                      // (1.) moved to sail_toplevel
                                                                                                                                                                        + logic  another_toplevel_signal_1;                            // (5.) Adding duplicate (driven by sail_setup_let)
                                                                                                                                                                                                                                       + logic  toplevel_signal_1;                                    // (5.) Adding duplicate (driven by seail_setup_let)
                                                                                                                                                                                                                                                                                                      -   sail_setup_let_42 sail_setup_inst_42();
        +   sail_setup_let_42 sail_setup_inst_42(toplevel_signal);     // (4.) Remove output
          always_comb begin
          +     toplevel_signal = toplevel_signal_1;                     // (5.) Assign from duplicate (driven by sail_setup_let)
                                                                         +     another_toplevel_signal = another_toplevel_signal_1;     // (5.) Assign from duplicate (driven by sail_setup_let)
        end
          endmodule
    ]}

*)

open Libsail

open Ast
open Ast_util
open Jib
open Jib_compile
open Jib_util
open Jib_visitor
open PPrint
open Printf
open Smt_exp

open Generate_primop2
open Sv_ir
open Sv_attribute

module IntSet = Util.IntSet
module IntMap = Util.IntMap
module StringMap = Util.StringMap

(** In order to prefix all the global references, we "interecept" a SV pprint function [NameGen.to_string], and prepend
    when the thing to print is a global reference. To do so, we must have the list of globals somewhere, this is the
    purpose of below [list] variable. It contains the list of globals :
    - filled once at the "initialization point" when going through all global declarations
    - Used at each call of [NameGen.to_string] (the "interception point") to compare the variable to print against the
      globals.

    It is a mutable reference because it's the least impactful way (in terms of git rebasing) to bring it from the
    "initialization point" to the "interception point". *)
let list : (Libsail__Ast.id * ctyp) list ref = ref []

(** Prepending should be done everywhere except in the sail_toplevel module (where globals are locally declared). To do
    so, we use below [active] switch and [toggle] function. When calling [pp_module], [toggle] will set [active] to
    [false] if and only if we're pprinting the [sail_toplevel] module. *)
let active : bool ref = ref true

let get_strlist () = List.map (fun (id, _) -> string_of_id id) !list

(** This is the function filling the list of globals, to be called at the "initialization point". *)
let add id ctyp = list := (id, ctyp) :: !list

(** This is the function doing the actual prepending (and comparing against the global list), to be called at the
    "interception point". *)
let prepend prefix_opt s =
  let prefix = match prefix_opt with Some s -> s ^ "." | None -> "" in
  if !active && List.mem s (get_strlist ()) then prefix ^ s else s

let pp () =
  let print_id id = print_endline @@ Printf.sprintf "global let(id) : %s" id in
  List.iter print_id @@ get_strlist ()

(** This is the function used to diable prepending for the [sail_toplevel] module, to be called at the top of
    [pp_module] *)
let toggle module_name = active := not @@ String.equal "sail_toplevel" module_name

(** Because of issue (4.) mentioned in the [Globals] doc above, we remove all output of the [sail_setup_let_] modules.

    This manual hack raises an exception in the List.map2 function which is called with a list of 1 returned value
    [my_global_1] and 0 output (the previously removed [my_global_1].

    This function intercepts and discards that exception since the behaviour is expected. *)
let map2 f l1 l2 =
  match l1 with
  | [] -> [] (* Case when connecting sail_setup_let_ modules, with 1 return value but 0 output *)
  | _ -> List.map2 f l1 l2

module Gen = struct
  (* returns a list of globals and their duplicates (eponymous with "_1" at the end) *)
  (* e.g. for [a, b, c] it will return [a, a_1, b, b_1, c, c_1] *)
  (* This is used in toplevel, where all globals are declared, *)
  let list_with_dup global_prefix =
    if Option.is_none global_prefix then []
    else List.flatten @@ List.map (fun (id, ctyp) -> [(id, ctyp); (append_id id "_1", ctyp)]) !list

  let top_ids global_prefix = List.map (fun (id, _ctyp) -> name id) @@ list_with_dup global_prefix

  (** This function generates the list of declarations to add in [sail_toplevel] *)
  let top_defs global_prefix = List.map (fun (id, ctyp) -> SVD_var (name id, ctyp)) @@ list_with_dup global_prefix

  let asgn (id, _ctyp) =
    let s = string_of_id id in
    let s_dup = Printf.sprintf "%s_1" s in
    let id_dup = mk_id s_dup in
    mk_statement @@ svs_raw (Printf.sprintf "%s = %s" s s_dup) ~inputs:[name id; name id_dup]

  (** This function generates the assignments to add in the [sail_toplevel] [always_comb] block *)
  let always_comb_assignments global_prefix = if Option.is_none global_prefix then [] else List.map asgn !list
end
(* module Gen *)

let remove_top_vars global_prefix in_module = Option.is_some global_prefix && Option.is_none in_module
