default Order dec
$include <prelude.sail>

/* We do a calculation on the size so we'll need to case split */

val depends : forall 'n, 1 <= 'n <= 4. int('n) -> bits(32)

function depends(n) = {
  let 'm = 8 * n in
  let x : bits('m) = sail_sign_extend(0x80, m) in
  sail_zero_extend(x, 32)
}

/* check other forms */

val depends2 : forall 'n, 0 < 'n <= 4. int('n) -> bits(32)

function depends2(n) = {
  let 'm = 8 * n in
  let x : bits('m) = sail_sign_extend(0x80, m) in
  sail_zero_extend(x, 32)
}

val depends3 : forall 'n, 1 <= 'n < 5. int('n) -> bits(32)

function depends3(n) = {
  let 'm = 8 * n in
  let x : bits('m) = sail_sign_extend(0x80, m) in
  sail_zero_extend(x, 32)
}

val depends4 : forall 'n, 0 < 'n < 5. int('n) -> bits(32)

function depends4(n) = {
  let 'm = 8 * n in
  let x : bits('m) = sail_sign_extend(0x80, m) in
  sail_zero_extend(x, 32)
}

val run : unit -> unit

function run () = {
  assert(depends(1) == 0x00000080);
  assert(depends(2) == 0x0000ff80);
  assert(depends(3) == 0x00ffff80);
  assert(depends(4) == 0xffffff80);
  assert(depends2(1) == 0x00000080);
  assert(depends2(2) == 0x0000ff80);
  assert(depends2(3) == 0x00ffff80);
  assert(depends2(4) == 0xffffff80);
  assert(depends3(1) == 0x00000080);
  assert(depends3(2) == 0x0000ff80);
  assert(depends3(3) == 0x00ffff80);
  assert(depends3(4) == 0xffffff80);
  assert(depends4(1) == 0x00000080);
  assert(depends4(2) == 0x0000ff80);
  assert(depends4(3) == 0x00ffff80);
  assert(depends4(4) == 0xffffff80);
}
