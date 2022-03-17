default Order dec

$include <prelude.sail>
$include <mapping.sail>

val bin_bits_2 : bits(2) <-> string

val assembly : bits(3) <-> string

mapping assembly = {
  0b0 @ (x : bits(2)) <-> "zero" ^ spc() ^ bin_bits_2(x),
  0b1 @ (x : bits(2)) <-> "one" ^ spc() ^ bin_bits_2(x),
}

$non_exec test1

val test1 : unit -> unit

function test1() = {
  let _ = assembly("one 0b11")
}

val test2 : unit -> unit

function test2() = {
  let _ = assembly(0b111)
}
