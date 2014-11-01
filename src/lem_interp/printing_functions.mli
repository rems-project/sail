open Interp_utilities;;
open Interp_ast ;;
open Interp_interface ;;

(*Functions to translate values, registers, or locations strings *)
(*Takes a location to a formatted string*)
val loc_to_string : l -> string
(*Returns the result of above for the exp's location *)
val get_loc : tannot exp -> string
(*interp_interface.value to string*)
val val_to_string : value0 -> string
val val_to_string_internal : Interp.value -> string
(*Force all representations to hex strings instead of a mixture of hex and binary strings*)
val val_to_hex_string : value0 -> string
(* format one register *)
val reg_name_to_string : reg_name -> string
(* format the register dependencies *)
val dependencies_to_string : reg_name list -> string
(* formats an expression, using interp_pretty *)
val exp_to_string : tannot exp -> string

(* Functions to set the color of parts of the output *)
val red : string -> string
val blue : string -> string
val green : string -> string
val yellow : string -> string
val grey : string -> string


(*Functions to modify the instruction state and expression used in printing and in run_model*)
val compact_exp : tannot exp -> tannot exp
val top_frame_exp : instruction_state -> tannot exp


(*functions to format events and instruction_states to strings *)
(*Create one large string of all of the events (indents automatically) *)
val format_events : event list -> string
(*format a portion of the instruction state for easy viewing *)
val instruction_state_to_string : instruction_state -> string
(*format just the top of the call stack*)
val top_instruction_state_to_string : instruction_state -> string

val instruction_to_string : instruction -> string

(*Functions to take a print function and cause a print event for the above functions *)
val print_exp : (string-> unit) -> tannot exp -> unit 
val print_backtrace_compact : (string -> unit) -> instruction_state -> unit
val print_continuation : (string -> unit) -> instruction_state -> unit
val print_instruction : (string -> unit) -> instruction -> unit
