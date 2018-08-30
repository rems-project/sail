default Order dec

$include <flow.sail>

val f1 : forall 'n, 0 < 'n <= 8. int('n) -> unit

function f1(_) = ()

val f2 : forall 'n, 'n > 0. int('n) -> unit

function f2(width) =
  if 'n <= 8 then
    f1(width)
  else ()

val "print" : string -> unit

val main : unit -> unit

function main() = {
  f2(3);
  print("ok\n")
}
