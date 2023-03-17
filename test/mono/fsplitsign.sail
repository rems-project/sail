/* Example of returning a tuple where one of the elements needs a cast */

default Order dec
$include <prelude.sail>

/* Split sign and the remain of floating point number */
val      fsplitsign : forall 'n, 'n in {16, 32, 64}. bits('n) -> (bits(1), bits('n - 1))
function fsplitsign   (xf) = {
  match 'n {
    16 => (xf[15..15], xf[14..0]),
    32 => (xf[31..31], xf[30..0]),
    64 => (xf[63..63], xf[62..0])
  }
}

val test : forall 'n, 'n in {16, 32, 64}. (implicit('n), bits('n), bits(1), bits('n)) -> bool
function test (n,x,s0,r0) = {
  let (s,r) = fsplitsign(x);
  s0 == s & r0 == 0b0 @ r
}

val run : unit -> unit

function run() = {
  assert(test(0xffff, 0b1, 0x7fff));
  assert(test(0x7fff, 0b0, 0x7fff));
  assert(test(0x1234, 0b0, 0x1234));
  assert(test(0x8765, 0b1, 0x0765));
}
