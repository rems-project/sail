default Order dec

$include <prelude.sail>

union exception = {
  Exc_list_string : list(string),
  Exc_list_int : list(int),
}

val list_length : forall ('a : Type). list('a) -> int

function list_length(xs) = match xs {
  x :: xs => 1 + list_length(xs),
  [||] => 0,
}

val my_cons : forall ('a : Type). ('a, list('a)) -> list('a)

val my_cons_n : forall 'n 'm, 'n >= 32 & 'n == 'm. (int('n), list(int('m))) -> list(int('m))

val specialized_cons : forall 'n, 'n == 32. (int('n), list(int('n))) -> list(int('n))

function my_cons(x, xs) = x :: xs

function my_cons_n(x, xs) = x :: xs

function specialized_cons(x, xs) = x :: xs

val hd_or_zero : list(int) -> int

function hd_or_zero(xs) = match xs {
  x :: xs => x,
  [||] => 0,
}

let toplevel_list : list(string) = [|"hello", "world"|]

val main : unit -> unit

function main() = {
    let xs: list(int) = my_cons(1, 2 :: my_cons(3, [|4|]));
    let ys = xs;
    var zs = xs;
    zs = 5 :: ys;
    print_int("hd_or_zero(zs) = ", hd_or_zero(zs));
    let xs = my_cons_n(32, [|32, 32, 32|]);
    var ws = specialized_cons(32, [|32|]);
    ws = xs;
    print_int("list_length(xs) = ", list_length(xs));
    print_int("list_length(ys) = ", list_length(ys));
    print_int("list_length(zs) = ", list_length(zs));
    try throw Exc_list_int(xs) catch {
      Exc_list_int(x :: _) => print_int("32 == ", x),
      Exc_list_string(_ :: _) => assert(false),
      _ => assert(false),
    };
    ()
}