default Order dec
$include <prelude.sail>

union myunion = {
  MyConstr : {'n, 'n in {8,16}. (int('n),bits('n))}
}

val make : bits(2) -> myunion

function make(v) =
  let r : {'n, 'n in {8,16}. (int('n),bits('n))} = match v {
    0b00 => ( 8,  0x12),
    0b01 => (16,0x1234),
    0b10 => ( 8,  0x56),
    0b11 => (16,0x5678)
  } in MyConstr(r)

val use : myunion -> bits(32)

function use(MyConstr(n,v)) = sail_zero_extend(v,32)

val run : unit -> unit

function run () = {
  assert(use(make(0b00)) == 0x00000012);
  assert(use(make(0b01)) == 0x00001234);
  assert(use(make(0b10)) == 0x00000056);
  assert(use(make(0b11)) == 0x00005678);
}
