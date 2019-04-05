default Order dec

$include <prelude.sail>

val "print_endline" : string -> unit

union U('a: Type) = {
  Err : 'a,
  Ok : bits(16)
}

function main((): unit) -> unit = {
  let x : U(unit) = Ok(0xFFFF);
  match x {
    Err() => print_endline("error"),
    Ok(y) => print_bits("y = ", y)
  }
}
