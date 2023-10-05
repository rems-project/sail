default Order dec
$include <prelude.sail>

/* Should find a set constraint below the let */

val f : forall 'n. int('n) -> unit

function f(n) = {
    let 'm = 2 * n in {
      assert(constraint('n in {8,16}));
      let x : bits('m) = replicate_bits(0b0,'m) in
      ()
    }
}


val run : unit -> unit

function run () = {
    f(8);
    f(16);
}
