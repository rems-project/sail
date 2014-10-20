open Interp_utilities;;
open Interp_ast ;;
open Interp_interface ;;

val loc_to_string : l -> string
val top_frame_exp : instruction_state -> tannot exp
val get_loc : tannot exp -> string
val compact_exp : tannot exp -> tannot exp
val val_to_string : value0 -> string
val dependencies_to_string : reg_name list -> string
val reg_name_to_string : reg_name -> string

val format_events : event list -> string

val exp_to_string : tannot exp -> string
val print_exp : (string-> unit) -> tannot exp -> unit 
val print_backtrace_compact : (string -> unit) -> instruction_state -> unit
val print_continuation : (string -> unit) -> instruction_state -> unit

val red : string -> string
val blue : string -> string
val green : string -> string
val yellow : string -> string
val grey : string -> string
