default Order dec
$include <prelude.sail>

/* Test splitting required because there's a size calculation in the function */

val foo : forall 'n. atom('n) -> unit effect {escape}

function foo(n) = {
  assert(constraint('n in {2,4}));
  let 'm = 8 * n in
  let x : bits('m) = replicate_bits(0b0,m) in
  let y : bits('n) = replicate_bits(0b0,n) in
  ()
}

val run : unit -> unit effect {escape}

function run () = {
    foo(2);
    foo(4);
}
