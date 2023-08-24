default Order dec

/* this is here because if we don't have it before including vector_dec
   we get infinite loops caused by interaction with bool/bit casts */
val eq_bit2 = pure "eq_bit" : (bit, bit) -> bool
overload operator == = {eq_bit2}

$include <vector_dec.sail>

val "reg_deref" : forall ('a : Type). register('a) -> 'a
/* sneaky deref with no effect necessary for bitfield writes */
val _reg_deref = monadic "reg_deref" : forall ('a : Type). register('a) -> 'a

val zeros_0 = pure "zeros" : forall 'n. int('n) -> bits('n)

val zeros : forall 'n. (implicit('n), unit) -> bits('n)
function zeros(n, _) = zeros_0(n)

val ones : forall 'n, 'n >= 0. (implicit('n), unit) -> bits('n)
function ones(n, _) = replicate_bits(0b1, n)

val int_power = pure {ocaml: "int_power", lem: "pow", coq: "Z.pow"} : (int, int) -> int

overload operator ^ = {xor_vec, int_power}

val bool_to_bits : bool -> bits(1)
function bool_to_bits x = if x then 0b1 else 0b0

val bit_to_bool : bit -> bool
function bit_to_bool b = match b {
  bitone => true,
  bitzero => false
}

val to_bits : forall 'l, 'l >= 0 .(atom('l), int) -> bits('l)
function to_bits (l, n) = get_slice_int(l, n, 0)

/* 256 bit cap + tag */
type CapReg = bits(257)

struct CapStruct = {
  tag                     : bool    ,
  padding                 : bits(8) ,
  otype                   : bits(24),
  uperms                  : bits(16),
  perm_reserved11_14      : bits(4) ,
  access_system_regs      : bool    ,
  permit_unseal           : bool    ,
  permit_ccall            : bool    ,
  permit_seal             : bool    ,
  permit_store_local_cap  : bool    ,
  permit_store_cap        : bool    ,
  permit_load_cap         : bool    ,
  permit_store            : bool    ,
  permit_load             : bool    ,
  permit_execute          : bool    ,
  global                  : bool    ,
  sealed                  : bool    ,
  address                 : bits(64),
  base                    : bits(64),
  length                  : bits(64),
}

let default_cap : CapStruct = struct {
  tag = true,
  padding = zeros(),
  otype = zeros(),
  uperms = ones(),
  perm_reserved11_14 = zeros(),
  access_system_regs = true,
  permit_unseal = true,
  permit_ccall = true,
  permit_seal = true,
  permit_store_local_cap = true,
  permit_store_cap = true,
  permit_load_cap = true,
  permit_store = true,
  permit_load = true,
  permit_execute = true,
  global = true,
  sealed = false,
  address = zeros(),
  base = zeros(),
  length = 0xffffffffffffffff
}

let null_cap : CapStruct = struct {
  tag = false,
  padding = zeros(),
  otype = zeros(),
  uperms = zeros(),
  perm_reserved11_14 = zeros(),
  access_system_regs = false,
  permit_unseal = false,
  permit_ccall = false,
  permit_seal = false,
  permit_store_local_cap = false,
  permit_store_cap = false,
  permit_load_cap = false,
  permit_store = false,
  permit_load = false,
  permit_execute = false,
  global = false,
  sealed = false,
  address = zeros(),
  base = zeros(),
  length = 0xffffffffffffffff
}

let 'cap_size = 32

function capRegToCapStruct(capReg) : CapReg -> CapStruct =
  struct {
    tag                        = bit_to_bool(capReg[256]),
    padding                    = capReg[255..248],
    otype                      = capReg[247..224],
    uperms                     = capReg[223..208],
    perm_reserved11_14         = capReg[207..204],
    access_system_regs         = bit_to_bool(capReg[203]),
    permit_unseal              = bit_to_bool(capReg[202]),
    permit_ccall               = bit_to_bool(capReg[201]),
    permit_seal                = bit_to_bool(capReg[200]),
    permit_store_local_cap     = bit_to_bool(capReg[199]),
    permit_store_cap           = bit_to_bool(capReg[198]),
    permit_load_cap            = bit_to_bool(capReg[197]),
    permit_store               = bit_to_bool(capReg[196]),
    permit_load                = bit_to_bool(capReg[195]),
    permit_execute             = bit_to_bool(capReg[194]),
    global                     = bit_to_bool(capReg[193]),
    sealed                     = bit_to_bool(capReg[192]),
    address                    = capReg[191..128],
    base                       = capReg[127..64],
    length                     = capReg[63..0]
  }

function getCapPerms(cap) : CapStruct -> bits(31) = 
  (
    cap.uperms
      @ cap.perm_reserved11_14
      @ bool_to_bits(cap.access_system_regs)
      @ bool_to_bits(cap.permit_unseal)
      @ bool_to_bits(cap.permit_ccall)
      @ bool_to_bits(cap.permit_seal)
      @ bool_to_bits(cap.permit_store_local_cap)
      @ bool_to_bits(cap.permit_store_cap)
      @ bool_to_bits(cap.permit_load_cap)
      @ bool_to_bits(cap.permit_store)
      @ bool_to_bits(cap.permit_load)
      @ bool_to_bits(cap.permit_execute)
      @ bool_to_bits(cap.global)
  )


/* Function to convert capabilities to in-memory format. */
function capStructToMemBits256(cap) : CapStruct -> bits(256) =
  (
        cap.padding
      @ cap.otype
      @ getCapPerms(cap)
      @ bool_to_bits(cap.sealed)
      @ cap.address
      @ cap.base
      @ cap.length
  )


/* When saving/restoring capabilities xor them with bits of null_cap --
   this ensures that canonical null_cap is always all-zeros in memory
   even though it may have bits set logically (e.g. length or exponent) */

let null_cap_bits : bits(256) = capStructToMemBits256(null_cap)

function capStructToMemBits(cap) : CapStruct -> bits(256)=
  capStructToMemBits256(cap) ^ null_cap_bits

function memBitsToCapBits(tag, b) : (bool, bits(256)) -> bits(257)  =
  bool_to_bits(tag) @ (b ^ null_cap_bits)

function capStructToCapReg(cap) : CapStruct -> CapReg = bool_to_bits(cap.tag) @ capStructToMemBits256(cap)

register DDC : CapReg
register C01 : CapReg
register C02 : CapReg
register C03 : CapReg

let CapRegs : vector(4, dec, register(CapReg)) =
  [
    ref C03,
    ref C02,
    ref C01,
    ref DDC
  ]

val readCapReg : bits(2) -> CapStruct
function readCapReg(n) =
  if (n == 0b00) then
    default_cap
  else
    let i = unsigned(n) in
    capRegToCapStruct(reg_deref(CapRegs[i]))

function writeCapReg(n, cap) : (bits(2), CapStruct) -> unit =
  if (n == 0b00) then
    ()
  else
    let i = unsigned(n) in
    (*CapRegs[i]) = capStructToCapReg(cap)

val main : unit -> unit

function main() = {
  print_bits("default_cap = ", capStructToCapReg(default_cap));
  print_bits("null_cap = ", capStructToCapReg(null_cap));
  DDC = capStructToCapReg(default_cap);
  print_bits("C03 = ", C03);
  print_bits("C02 = ", C02);
  print_bits("C01 = ", C01);
  print_bits("DDC = ", DDC);
  foreach(i from 1 to 3) {
    let idx = to_bits(2, i);
    writeCapReg(idx, null_cap)
  };
  print_bits("C03 = ", C03);
  print_bits("C02 = ", C02);
  print_bits("C01 = ", C01);
  print_bits("DDC = ", DDC);
}
