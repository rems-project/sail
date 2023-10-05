default Order dec
$include <prelude.sail>

val test : forall 'n, 'n in {8,16}. (int('n),int('n),bits(1)) -> bits(64)

function test(x,y,b) = {
  let 'z = x + y in
  let v : bits('z) = sail_zero_extend(b,z) in
  sail_zero_extend(v,64)
}

val run : unit -> unit

function run () = {
  assert(test(8,8,0b0) == 0x0000000000000000);
  assert(test(16,16,0b1) == 0x0000000000000001);
}
