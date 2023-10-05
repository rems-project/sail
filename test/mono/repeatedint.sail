/* Silly, but it did appear in a model, and we didn't handle it... */

default Order dec
$include <prelude.sail>

union ast = {
  SomeInstr : {'size, 'size in {8,16}. (int('size), int('size))}
}

val test : ast -> bits(32)

function test(SomeInstr(s as int('size),r)) = {
  x : bits('size) = sail_zero_extend(0x80, s);
  sail_sign_extend(x,32)
}

val run : unit -> unit

function run () = {
  assert(test(SomeInstr(8,8)) == 0xffffff80);
  assert(test(SomeInstr(16,16)) == 0x00000080);
}
