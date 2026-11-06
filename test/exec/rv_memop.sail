default Order dec

$include <prelude.sail>
$include <string.sail>

union ExceptionType = {
 E_A : unit,
 E_B : unit,
 E_C : unit,
}

union MemoryOpResult('a : Type) = {
  MemValue     : 'a,
  MemException : ExceptionType
}

val test : unit -> MemoryOpResult(bool)

function test() = {
  let x = MemValue(0x0000_0000_0000_0000_0000_0000);
  MemValue(true)
}

val main : unit -> unit

function main() = {
  let _ = test();
  print_endline("ok");
  ()
}
