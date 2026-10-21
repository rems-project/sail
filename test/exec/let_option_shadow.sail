default Order dec

$include <prelude.sail>
$include <result.sail>

type bits2 = (bits(32), option(bits(32)))

function foo() -> result(bits2, unit) = {
  let tr1 = {
    let tr1 : bits(32) = 0x12345678;
    Some(tr1)
  };
  Ok(0x12345678, tr1)
}

val main : unit -> unit

function main() = {
  match foo() {
    Ok(x, Some(y)) => {
      print_bits("x = ", x);
      print_bits("y = ", y);
    },
    _ => (),
  }
}
