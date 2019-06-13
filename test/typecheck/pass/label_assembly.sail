default Order dec

$include <prelude.sail>
$include <mapping.sail>

type labels = list((string, int))

val assoc : forall ('a : Type). (list((string, 'a)), string) -> option('a)

function assoc(map, key) = {
  match map {
    (key', value) :: map if key == key' => Some(value),
    _ :: map => assoc(map, key),
    [||] => None()
  }
}

mapping label forall 'size, 'size > 0. (n: int, labels: labels, size: int('size)) -> string <-> option(bits('size)) = {
  x <- bits(size) <-> Some(x),
  forwards l =>
    match assoc(labels, l) {
      Some(offset) => Some(get_slice_int(size, offset - n, 0)),
      None() => None()
    }
}

union ast = {
  Branch : (bits(16)),
  Add : (bits(5), bits(5), bits(5))
}

mapping assembly(n: int, labels: labels) -> string <-> ast = {
  "b" ^ spc() ^ Some(offset) <- label(n, labels, 16) <-> Branch(offset),
  "add" ^ spc() ^ dst <- bits(5) ^ sep() ^ src1 <- bits(5) ^ sep() ^ src2 <- bits(5) <-> Add(dst, src1, src2)
}
