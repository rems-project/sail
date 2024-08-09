default Order dec

$include <vector_dec.sail>

val print_endline = "print_endline" : string -> unit

val test : bits(8) -> unit

function test 0b00 @ 0xF @ 0b00 = print_endline("0b00111100")
and test 0b0 @ _ : bits(5) @ 0b1 @ [bitzero] = print_endline ("0b0_____10")
and test 0b0 @ _ : bits(5) @ 0b1 @ [_] = print_endline("0b0_____1_")
and test 0b0 @ _ : bits(5) @ 0b1 @ [bitone] = print_endline ("0b0_____11")
and test _ = print_endline("wildcard")

val main : unit -> unit

function main () = {
  test(0b00111100);
  test(0b01111111);
  test(0b01111110);
}
