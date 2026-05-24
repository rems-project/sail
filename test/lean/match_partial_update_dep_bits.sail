default Order dec

$include <prelude.sail>

union boxed_imm = {
  Boxed32 : bits(32),
  Boxed64 : bits(64)
}

function partial_update_match(shift : bits(2), imm12 : bits(12), use64 : bool) -> boxed_imm = {
  let datasize : {32, 64} = if use64 then 64 else 32;
  imm = sail_zeros(datasize);
  match shift {
    0b00 => imm = sail_zero_extend(imm12, datasize),
    0b01 => imm = sail_zero_extend(imm12 @ 0x000, datasize),
    _ => print("reserved")
  };
  if datasize == 64 then {
    Boxed64(imm)
  } else {
    Boxed32(imm)
  }
}
