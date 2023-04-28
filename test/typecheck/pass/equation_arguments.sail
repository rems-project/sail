default Order dec
$include <prelude.sail>

// In this example, the second argument of set_mem instantiates 'size,
// so the final argument can be checked at bits(32)...

val set_mem : forall ('size : Int), 8 * 'size >= 0.
         (bitvector(64,dec), atom('size), bits(8 * 'size)) -> unit

val get_reg : forall ('width : Int), 'width >= 0. int -> bits('width)

function m(address: bitvector(64,dec), s: int) -> unit = {
  set_mem(address, 4, get_reg(s));
}

// ...but in this version it infers the type because 'bytes hasn't been
// instantiated yet (if we don't instantiate from equations in the
// context), and inference fails because the 'width >= 0 constraint can't
// be satisfied.

val set_mem2 : forall ('size : Int) 'bytes, 'bytes >= 0 & 'bytes == 8 * 'size.
         (bitvector(64,dec), atom('size), bits('bytes)) -> unit

function m2(address: bitvector(64,dec), s: int) -> unit = {
  set_mem2(address, 4, get_reg(s));
}

