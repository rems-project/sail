default Order dec

$include <prelude.sail>
$include <mapping.sail>

scattered union ast

union clause ast = LDR : (bits(5), bits(5))

union clause ast = STR : bits(5)

val assembly : string <-> ast

mapping clause assembly =
  "ldr" ^ spc() ^ x <- bits(5) ^ sep() ^ y <- bits(5) <-> LDR(x, y)

mapping clause assembly =
  "str" ^ spc() ^ x <- bits(5) <-> STR(x)
