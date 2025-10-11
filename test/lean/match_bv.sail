default Order dec

$include <prelude.sail>

val decode : bits(32) -> bool

function clause decode (0b11@0b111@0b0@0b00@(opc:bits(2))@0b1@(Rm:bits(5))@(option_v:bits(3))@[S]@0b10@(Rn:bits(5))@(Rt:bits(5))) = {
  if Rm==Rn then
    true
  else
    false 
}

function clause decode ([sf]@0b10@0b01010@(shift:bits(2))@[N]@(Rm:bits(5))@(imm6:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  if Rn==Rd then
    true
  else
    false  
}

function clause decode (0b1101010100@0b0@0b00@0b011@0b0011@(CRm : bits(4))@0b1@0b01@0b11111) = {
  true
}

function clause decode (0b1@0b011010@0b0@(imm19:bits(19))@(Rt:bits(5))) = {
  false
}

function clause decode(_) = { true }

let xlen = 32
val write_CSR : (bits(12)) -> bool
function clause write_CSR((0b1011000 : bits(7) /* 0xB00 */ @ index : bits(5)) if unsigned(index) >= 3) = {
  true
}
function clause write_CSR((0b1011100 /* 0xB80 */ @ index : bits(5)) if xlen == 32 & unsigned(index) >= 3) = {
  true
}

val write_CSR2 : (bits(12)) -> bool
function write_CSR2((0b1011100 /* 0xB80 */ @ index : bits(5)) if xlen == 32 & unsigned(index) >= 3) = {
  true
}
