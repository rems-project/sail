default Order dec

$include <prelude.sail>

// Make sure the my_pair type is included in the C output
$option --c-preserve-type my_pair

$option --c-include includes/pair_fn.h

type my_pair = (range(0, 64), range(0, 64))

$c_override {
  id = my_pair,
  target = "my_pair_in_c"
}

// The fact that tuple fields are named this is a bit of an
// implementation detail, but it works for now

$c_override {
  id = tup0,
  target = "first"
}

$c_override {
  id = tup1,
  target = "second"
}

// Just so this test works in non-C backends
$iftarget c cpp
val mk_pair = pure "mk_pair" : unit -> my_pair
$else
val mk_pair : unit -> my_pair

function mk_pair() = (0, 3)
$endif

val main : unit -> unit

function main() = {
  let x : my_pair = mk_pair();
  match x {
    (_, y) => print_int("", y)
  }
}
