
val (int, int) -> int effect pure add_int
overload (deinfix +) [add_int]

val forall Type 'a. ('a, 'a) -> bool effect pure eq
val forall Type 'a. ('a, 'a) -> bool effect pure neq

overload (deinfix ==) [eq]
overload (deinfix !=) [neq]

val (int, int) -> int effect pure quotient

overload (deinfix quot) [quotient]

typedef T = const union { int C1; int C2 }

function int test ((int) x, (T) y) =
  switch y {
    case (C1(z)) when z == 0 -> 0
    case (C1(z)) when z != 0 -> x quot z
    case (C2(z)) -> z
  }
