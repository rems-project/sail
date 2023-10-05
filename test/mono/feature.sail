default Order dec
$include <prelude.sail>

union exception = {
  Error_undefined : unit
}

/* Inlining feature test functions, as in aarch64 */

val HaveSomeFeature : unit -> bool

function HaveSomeFeature () = return(true)

val foo : bits(1) -> unit

function foo(x) = {
  let i : int =
    match x {
    0b0 => 8,
    0b1 => if HaveSomeFeature() then 16 else throw(Error_undefined())
    }
  in
  let 'n = i in {
    assert(constraint('n >= 0));
    let y : bits('n) = replicate_bits(0b0, n) in
    ()
  }
}

val run : unit -> unit

function run () = {
    foo(0b0);
    foo(0b1);
}
