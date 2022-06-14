default Order dec
$include <prelude.sail>

enum e1 = {ABC, DEF}
enum e2 = {GHI, JKL}

struct s1 = {
  fA : int,
  fB : e2,
}

struct s2 = {
  fC : int,
  fD : e1,
}

struct s3 = {
  fE : s1,
  fF : int,
}

val f : int -> int
function f(x) = 2 * x

val g : int -> int
function g(x) = 3 * x

val h : int -> int
function h(x) = x + f(x)

val j : s3 -> int
function j(x) = f(x.fF)

val k : int -> int
function k(x) = {
  s : s3 = undefined;
  s.fF = x;
  f(s.fF)
}
