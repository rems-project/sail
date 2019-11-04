default Order dec
$include <prelude.sail>

/* Simple case split example on a variant datatype */

union ast = {
  SomeOp : {'n, 'n in {8,16}. (int('n),bits('n))}
}

val execute : ast -> bits(32)

function execute(SomeOp(n as int('n),v)) = {
  a : bits('n) = sail_zero_extend(0x12,n);
  b : bits('n) = and_vec(v, a);
  sail_zero_extend(b,32)
}

val run : unit -> unit effect {escape}

function run () = {
  assert(execute(SomeOp(8,0x11)) == 0x00000010);
  assert(execute(SomeOp(16,0x3333)) == 0x00000012);
}
