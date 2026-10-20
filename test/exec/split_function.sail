default Order dec

$include <prelude.sail>

$iftarget c cpp
$option --c-split extension_enabled
$option --c-split execute
$option --c-split extension_enabled
$endif

enum Extension = { ExtA, ExtB }

union Instruction = {
  Item : int,
  Pair : (int, int),
  Empty : unit
}

register enabled : bool
register bias : int
register calls : int
register current_extension : Extension
register current_instruction : Instruction = Empty()

val extension_enabled : Extension -> bool
function static_enum() -> bool = extension_enabled(ExtA)
scattered function extension_enabled
function clause extension_enabled ExtA = enabled
function clause extension_enabled ExtB = false
end extension_enabled

val execute : Instruction -> int
function execute (Item(0)) = bias
and execute (Item(n)) = n + bias
and execute (Pair(x, y)) = x + y + bias
and execute (Empty()) = bias

function dynamic_enum() -> bool = extension_enabled(current_extension)
function static_union(x : int) -> int = execute(Pair(x, 4))
function dynamic_union() -> int = execute(current_instruction)

function next_payload() -> int = {
  calls = calls + 1;
  calls
}

function effectful_payload() -> int = execute(Item(next_payload()))

function main() -> unit = {
  enabled = true;
  bias = 10;
  calls = 0;
  current_extension = ExtA;
  current_instruction = Item(0);
  print_endline(if static_enum() then "static enum: true" else "static enum: false");
  print_endline(if dynamic_enum() then "dynamic enum: true" else "dynamic enum: false");
  current_extension = ExtB;
  print_endline(if dynamic_enum() then "dynamic enum: true" else "dynamic enum: false");
  print_int("static union: ", static_union(3));
  print_int("dynamic zero: ", dynamic_union());
  current_instruction = Item(5);
  print_int("dynamic item: ", dynamic_union());
  current_instruction = Empty();
  print_int("dynamic empty: ", dynamic_union());
  print_int("effectful payload: ", effectful_payload());
  print_int("payload calls: ", calls)
}
