/* A small vector example, inspired by the proposed RISC-V extension. */

default Order dec
$include <prelude.sail>
$include <smt.sail>

type vmax : Int = 64

register vsize : bits(2)

function get_vector_size() -> {|8,16,32,64|} = {
  shl_int(8, unsigned(vsize))
}

register V : vector(16, dec, bits(vmax))

val get_elements : forall 'n 'm, 0 <= 'n & 0 <= 'm. (int('n), int('m), range(0,15)) -> vector('n, dec, bits('m))

function get_elements(n, m, reg) = {
  let bv = V[reg];
  var res : vector('n, dec, bits('m)) = undefined;
  assert ('m * 'n <= sizeof(vmax));
  foreach (i from 0 to (n - 1)) {
    res[i] = slice(bv, 'm * i, 'm);
  };
  res
}

function accumulate(in_reg : range(0,15), out_reg : range(0,15)) -> unit = {
  let 'n = get_vector_size();
  let 'elems = ediv_int(sizeof(vmax), 'n);
  var x : bits('n) = sail_zeros('n);
  var ys : vector('elems, dec, bits('n)) = get_elements('elems, 'n, in_reg);
  foreach (i from 0 to ('elems - 1)) {
    x = x + ys[i]
  };
  V[out_reg] = sail_zero_extend(x, sizeof(vmax))
}

function alt_accumulate(in_reg : range(0,15), out_reg : range(0,15)) -> unit = {
  let vsz = get_vector_size();
  let 'elems = ediv_int(sizeof(vmax), vsz);
  let 'n = vsz;
  var x : bits('n) = sail_zeros('n);
  var ys : vector('elems, dec, bits('n)) = get_elements('elems, 'n, in_reg);
  foreach (i from 0 to ('elems - 1)) {
    x = x + ys[i]
  };
  V[out_reg] = sail_zero_extend(x, sizeof(vmax))
}

function run() -> unit = {
  vsize = 0b00;
  V[0] = 0x0102030405060708;
  accumulate(0,1);
  assert(V[1] == 0x0000000000000024);
  vsize = 0b01;
  accumulate(0,2);
  assert(V[2] == 0x0000000000001014);

  vsize = 0b00;
  V[0] = 0x0102030405060708;
  alt_accumulate(0,1);
  assert(V[1] == 0x0000000000000024);
  vsize = 0b01;
  alt_accumulate(0,2);
  assert(V[2] == 0x0000000000001014);
}
