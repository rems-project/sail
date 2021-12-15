default Order dec

$sail_internal

val "print" : string -> unit
val "print_int" : (string, int) -> unit

union option ('a : Type) = {
  Some : 'a,
  None : unit
}

function main() : unit -> unit = {
  let r = (3, 2);
  let o = Some(r);
  match o {
    Some(x, y) => print_int("x = ", x),
    None() => ()
  };
  print("ok\n");
}