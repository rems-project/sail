default Order dec

$include <mapping.sail>

mapping test : string <-> (vector(5, dec, bit), vector(5, dec, bit)) = {
  "ldr" ^ spc() ^ x <- bits(5) ^ sep() ^ y <- bits(5) <-> (x, y)
}
