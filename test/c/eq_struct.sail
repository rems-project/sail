default Order dec

$include <flow.sail>
$include <exception_basic.sail>
$include <generic_equality.sail>

overload ~ = {not_bool}

struct S = {
  field1: int,
  field2: bitvector(8, dec)
}

val "print" : string -> unit

val main : unit -> unit effect {escape}

function main() = {
  let s : S = struct {
    field1 = 4,
    field2 = 0xFF
  };
  assert(s == s, "1");
  assert(~(s == { s with field2 = 0xAB }), "2");
  assert(s != { s with field1 = 5}, "3");
  assert(s == { s with field2 = 0xFF });
  assert({ s with field1 = 0} == {s with field1 = 0});
  print("ok\n")
}
