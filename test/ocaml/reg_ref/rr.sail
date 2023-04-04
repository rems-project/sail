
val "reg_deref" : forall ('a : Type). register('a) -> 'a effect {rreg}

/* *** Register reference list example *** */

type regno ('n : Int), 0 <= 'n < 4 = atom('n)

/* register x0 : bits(32) is always 0 */
register x1 : bits(32)
register x2 : bits(32)
register x3 : bits(32)

let GPRs : vector(3, dec, register(bits(32))) =
  [ ref x3, ref x2, ref x1 ]

val rGPR : forall 'n, 0 <= 'n < 4. regno('n) -> bits(32) effect {rreg}

function rGPR 0 = 0x00000000
and rGPR (r if r > 0) = reg_deref(GPRs[r - 1])

val wGPR : forall 'n, 1 <= 'n < 4. (regno('n), bits(32)) -> unit effect {wreg}

function wGPR (r, v) = {
  print_int("Register ", r);
  print_bits("Assigning ", v);
  (*GPRs[r - 1]) = v
}

overload _mod_GPR = { rGPR, wGPR }

/* *** Power style vector slicing *** */

/* Create a new type which is a pair of a bitvector and a start index

   slice('n, 'm) is equivalent to old-sail vector('n, 'm, dec, bit) */
newtype slice ('n : Int, 'm : Int) = MkSlice : (atom('n), bits('m))

/* Extract the bitvector from a slice */
val slice_bits : forall 'n 'm. slice('n, 'm) -> bits('m)

function slice_bits MkSlice(_, xs) = xs

/* Take a slice from a bitvector */
val vector_slice : forall 'n 'm 'o, 0 <= 'm <= 'o < 'n.
  (bits('n), atom('o), atom('m)) -> slice('m, 'o - ('m - 1))

function vector_slice (v, to, from) = MkSlice(from, v[to .. from])

val slice_slice : forall 'n 'm 'o 'p, 0 <= 'p <= 'm <= 'o & 'o - 'p < 'n.
  (slice('p, 'n), atom('o), atom('m)) -> slice('m, 'o - ('m - 1))

function slice_slice (MkSlice(start, v), to, from) = MkSlice(from, v[to - start .. from - start])

/* We can update a bitvector from another bitvector or a slice */
val _set_slice : forall 'n 'm 'o, 0 <= 'm <= 'o < 'n.
  (register(bits('n)), atom('o), atom('m), bits('o - ('m - 1))) -> unit effect {wreg, rreg}

function _set_slice (v, stop, start, update) = {
  v2 = reg_deref(v);
  v2[stop .. start] = update;
  (*v) = v2;
}

val _set_slice2 : forall 'n 'm 'o 'p, 0 <= 'm <= 'o < 'n.
  (register(bits('n)), atom('o), atom('m), slice('p, 'o - ('m - 1))) -> unit effect {wreg, rreg}

function _set_slice2 (v, stop, start, MkSlice(_, update)) = _set_slice(v, stop, start, update)

val slice_bit : forall 'n. slice('n, 1) -> bit

function slice_bit MkSlice(_, [b]) = b

/* Overload slice modifier */
overload _mod_slice = {_set_slice, _set_slice2, vector_slice, slice_slice}

/* Set up a struct with an aliased LT bit in CR0, mimicking old-style syntax */
infix 1 ...

type operator ...('n : Int, 'm : Int) = slice('m, 'n - ('m - 1))

struct cr = {
  CR0 : 7 ... 4,
  /* 7 : LT; 6 : GT; 5 : EQ; 4 : SO; */
  CR1 : 3 ... 2,
  CR3 : 1 ... 0,
}

register CR : cr

val _get_LT : cr -> bit
val _set_LT : (register(cr), bit) -> unit effect {rreg, wreg}

function _get_LT cr = slice_bit(cr.CR0.slice(7, 7))
function _set_LT (cr_ref, b) = {
  cr = reg_deref(cr_ref);
  cr.CR0 = MkSlice(4, [slice_bits(cr.CR0) with (7 - 4) = b]);
  (*cr_ref) = cr;
}

overload _mod_LT = {_get_LT, _set_LT}

/* *** Test Program *** */

val main : unit -> unit effect {wreg, rreg}

val print_regs : unit -> unit effect {rreg}

function print_regs () = {
  print_bits("1 = ", rGPR(1));
  print_bits("2 = ", rGPR(2));
  print_bits("3 = ", rGPR(3));
}

register b : bits(5)

function main () = {
  print("Testing register references");
  wGPR(1) = 0x00000000;
  wGPR(2) = 0x00000000;
  wGPR(3) = 0x00000000;

  print_regs ();

  /* Assign to lowest assignable register */
  wGPR(1) = 0xCAFEBEEF;
  print_regs ();

  /* Reading to variable */
  print("Reading 1 to variable");
  v = rGPR(1);
  print_bits("v = ", v);

  /* Assign to highest register */
  wGPR(3) = 0x00BEEF00;
  print_regs ();

  print("Reading zero register");
  print_bits("0 = ", rGPR(0));

  /* Test overloaded version */
  _mod_GPR(2) = 0xDEADCAFE;
  print_bits("2 = ", _mod_GPR(2));

  /* Method syntax */
  print("Assigning register 2 to register 1");
  2.GPR() = 1.GPR();
  print_regs();

  /* Slice testing */
  print("\nTesting slicing");
  let s = 0b01110.slice(3, 1);
  print_bits("s = ", slice_bits(s));
  let s = 0b01110.slice(4, 0);
  print_bits("s = ", slice_bits(s));
  let s = 0b01110.slice(3, 0);
  print_bits("s = ", slice_bits(s));

  /* Updating slices */
  b = 0b01110;
  print_bits("b = ", b);
  b->slice(3, 1) = 0b101;
  print_bits("b = ", b);
  b->slice(2, 0) = 0xFF.slice(5, 3);
  print_bits("b = ", b);

  /* Bit aliasing */
  print("\nTesting bit aliasing");
  print_bits("CR0 = ", slice_bits(CR.CR0));
  print_bits("LT = ", [CR.LT()]);
  print("Setting LT to bitone");
  CR->LT() = bitone;
  print_bits("CR0 = ", slice_bits(CR.CR0));
  print_bits("LT = ", [CR.LT()]);
  print("Setting CR0 to 0b0111");
  CR.CR0 = MkSlice(4, 0b0111);
  print_bits("CR0 = ", slice_bits(CR.CR0));
  print_bits("LT = ", [CR.LT()]);
}
