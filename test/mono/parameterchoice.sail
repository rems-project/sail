default Order dec

$include <prelude.sail>

val f : forall 'm 'n, 4 < 'm <= 32 & 4 <= 'n <= 32. (int('m), int('n), bool) -> bits(32)

function f(m,n,b) = {
  let 'p = if b then n else m;
  let x : bits('p) = sail_sign_extend(0b1010, p);
  sail_zero_extend(x, 32)
}

val run : unit -> unit

function run () = {
  assert(f(8,16,false) == 0x000000fa);
  assert(f(8,16,true)  == 0x0000fffa);
  assert(f(16,32,false) == 0x0000fffa);
  assert(f(16,32,true)  == 0xfffffffa);
}
