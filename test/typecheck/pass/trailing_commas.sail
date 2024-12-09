// This file is testing that trailing commas are allowed in certain places

val foo = pure {
  a: "a",
  b: "b",
} : unit -> unit

struct S = {
  f1 : int,
  f2 : int,
}

let struct {
  f1 = _,
  f2 = _,
} : S = struct { f1 = 1, f2 = 2, }

struct Sp(
  'a,
  'b,
) = {
  pair_field : ('a, 'b),
}

mapping mp : (int, int, ) <-> S = {
  (x, y, ) <-> struct { f1 = x, f2 = y, },
}
