$ifndef _MAPPING
$define _MAPPING

$include <arith.sail>
$include <option.sail>

val string_take = "string_take" : (string, nat) -> string
val string_drop = "string_drop" : (string, nat) -> string
val string_length = "string_length" : string -> nat
val string_append = {c: "concat_str", _: "string_append"} : (string, string) -> string
val string_startswith = "string_startswith" : (string, string) -> bool

val n_leading_spaces : string -> nat
function n_leading_spaces s =
  match s {
    "" => 0,
    _ => match string_take(s, 1) {
      " " => 1 + n_leading_spaces(string_drop(s, 1)),
      _ => 0
    }
  }

val spc     : unit <-> string
val opt_spc : unit <-> string
val def_spc : unit <-> string

val spc_forwards : unit -> string
function spc_forwards () = " "
val spc_backwards : string -> unit
function spc_backwards s = ()
val spc_matches_prefix : string -> option((unit, nat))
function spc_matches_prefix s = {
  let n = n_leading_spaces(s);
  match n {
    0 => None(),
    _ => Some((), n)
  }
}

val opt_spc_forwards : unit -> string
function opt_spc_forwards () = ""
val opt_spc_backwards : string -> unit
function opt_spc_backwards s = ()
val opt_spc_matches_prefix : string -> option((unit, nat))
function opt_spc_matches_prefix s =
  Some((), n_leading_spaces(s))

val def_spc_forwards : unit -> string
function def_spc_forwards () = " "
val def_spc_backwards : string -> unit
function def_spc_backwards s = ()
val def_spc_matches_prefix : string -> option((unit, nat))
function def_spc_matches_prefix s = opt_spc_matches_prefix(s)

val sep : unit <-> string
mapping sep : unit <-> string = {
  ()     <-> opt_spc() ^ "," ^ def_spc()
}

$ifdef _DEFAULT_DEC
$include <vector_dec.sail>

val hex_bits_20 : bits(20) <-> string
val hex_bits_20_forwards = "decimal_string_of_bits" : bits(20) -> string
val hex_bits_20_forwards_matches : bits(20) -> bool
function hex_bits_20_forwards_matches bv = true
val "hex_bits_20_matches_prefix" : string -> option((bits(20), nat))
val hex_bits_20_backwards_matches : string -> bool
function hex_bits_20_backwards_matches s = match s {
  s if match hex_bits_20_matches_prefix(s) {
    Some (_, n) if n == string_length(s) => true,
    _ => false
  } => true,
  _ => false
}
val hex_bits_20_backwards : string -> bits(20)
function hex_bits_20_backwards s =
  match hex_bits_20_matches_prefix(s) {
      Some (bv, n) if n == string_length(s) => bv
  }

$endif

$endif
