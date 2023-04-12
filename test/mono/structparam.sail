default Order dec
$include <prelude.sail>

// If a struct is parametrised by a number of bytes, then the monomorphised
// version needs to be parametrised by the number of *bits*

struct Info('n: Int) = {
  size : int('n),
  contents : bits(8 * 'n)
}

val make : (int(4), int) -> Info(4)

function make(size, value) = struct { size = size, contents = get_slice_int(8*size, value, 0) }

val check : int -> bool

function check(i) = {
  let info = make(4, i);
  i == unsigned(info.contents)
}
/*
val make : forall 'n, 'n in {1,2,4,8}. (int('n), int) -> Info('n)

function make(size, value) = struct { size = size, contents = get_slice_int(8*size, value, 0) }

val check : int -> bool

function check(i) = {
  let info = make(4, i);
  i == unsigned(info.contents)
}

val make_bits : forall 'n, 'n > 0. (int('n), bits(8 * 'n)) -> Info('n)

function make_bits(size, value) = struct { size = size, contents = value }

val check_bits : forall 'n, 'n > 0. (implicit('n), bits(8 * 'n)) -> bool

function check_bits(n, v) = {
  let info = make_bits(n, v);
  v == info.contents
}
*/
val run : unit -> unit

function run() = {
  assert(check(5));
  assert(check(1000));
/*  assert(check_bits(0x35));
  assert(check_bits(0x1234));*/
}
