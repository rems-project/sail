default Order dec
$include <prelude.sail>

union U('t :  Type) = {
  A : ('t, bits(1))
}

val f : U(unit) -> bits(1)
function f(u) = {
  match u {
     A(_, bs) => bs
  }
}

val main : unit -> unit
function main () = {
  let u : U(unit) = A((), 0b1) in
  let res = f(u) in
  print_endline("ok");
}
