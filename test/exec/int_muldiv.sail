default Order dec

$include <prelude.sail>

// Multiply, divide and remainder on integers that fit in 64 bits.

val quot = pure {coq: "Z.quot", lean: "Int.tdiv", _: "tdiv_int"} : forall 'n 'm, 'n >= 0 & 'm > 0. (int('n), int('m)) -> int(div('n, 'm))

val rem = pure {coq: "Z.rem", lean: "Int.tmod", _: "tmod_int"} : forall 'n 'm, 'n >= 0 & 'm > 0. (int('n), int('m)) -> int(mod('n, 'm))

// The divisor can be -1.
val rem_any = pure {coq: "Z.rem", lean: "Int.tmod", _: "tmod_int"} : forall 'n 'm, 'n >= 0 & 'm != 0. (int('n), int('m)) -> int(mod('n, 'm))

val mul : forall 'n 'm, -1000 <= 'n <= 1000 & -1000 <= 'm <= 1000. (int('n), int('m)) -> int('n * 'm)

function mul(x, y) = x * y

val calc : forall 'n 'm, 0 <= 'n <= 1000 & 1 <= 'm <= 1000. (int('n), int('m)) -> unit

function calc(x, y) = {
  print_int("quot = ", quot(x, y));
  print_int("rem = ", rem(x, y));
  // The divisor does not fit in 64 bits.
  print_int("quot_big = ", quot(x, 1180591620717411303424))
}

val calc_neg : forall 'n 'm, 0 <= 'n <= 1000 & -1 <= 'm <= 3 & 'm != 0. (int('n), int('m)) -> unit

function calc_neg(x, y) = print_int("rem_any = ", rem_any(x, y))

val main : unit -> unit

function main() = {
  print_int("mul = ", mul(-7, 3));
  calc(7, 2);
  calc_neg(7, -1);
  calc_neg(7, 3)
}
