default Order dec
$include <prelude.sail>

union myunion = {
  MyConstr : {'n 'm 'o, 'n in {8,16} & 'o in {8,16} & 'n <= 'm & 'm <= 'o. (int('n),bits('n),int('o),bits('o),int('m))}
}

val make : bits(2) -> myunion

function make(v) =
  let (n,v,m) : {'n 'm, 'n in {8,16} & 'm in {8,16} & 'n <= 'm. (int('n),bits('n),int('m))} = match v {
    0b00 => ( 8,  0x12, 8),
    0b01 => (16,0x1234,16),
    0b10 => ( 8,  0x56,16),
    0b11 => (16,0x5678,16)
  } in
  let w = sail_zero_extend(0x5,m) in
  MyConstr(n,v,m,w,m)

val use : myunion -> bits(32)

function use(MyConstr(n,v,_,_,_)) = sail_zero_extend(v,32)

val run : unit -> unit

function run () = {
  assert(use(make(0b00)) == 0x00000012);
  assert(use(make(0b01)) == 0x00001234);
  assert(use(make(0b10)) == 0x00000056);
  assert(use(make(0b11)) == 0x00005678);
}
