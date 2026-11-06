default Order dec
$include <prelude.sail>
$include <result.sail>

function try_option(option : bits(8)) -> option(bool) = Some(option == 0x12)
function try_bool(bool : bits(8)) -> bool = bool == 0x12
function try_string(string : bits(8)) -> string = bits_str(string)

function main() -> unit = {
  assert(match try_option(0x12) { Some(b) => b, None() => false });
  assert(try_bool(0x12));
  assert(try_string(0x12) == "0x12");
}
