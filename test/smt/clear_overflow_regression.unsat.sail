default Order dec

$include <arith.sail>
$include <vector_dec.sail>

infix 1 >>
infix 1 <<
overload operator - = {sub_bits}
overload operator >> = {sail_shiftright}
overload operator << = {sail_shiftleft}

infix 4 <+
infix 4 >+
infix 4 <=+
infix 4 >=+
val operator <+ : forall 'n. (bits('n), bits('n)) -> bool
val operator >+ : forall 'n. (bits('n), bits('n)) -> bool
val operator <=+ : forall 'n. (bits('n), bits('n)) -> bool
val operator >=+ : forall 'n. (bits('n), bits('n)) -> bool
function operator <+ (x, y) = unsigned(x) < unsigned(y)
function operator >+ (x, y) = unsigned(x) > unsigned(y)
function operator <=+ (x, y) = unsigned(x) <= unsigned(y)
function operator >=+ (x, y) = unsigned(x) >= unsigned(y)

val full_bounds : (int, bits(32), bits(3)) -> bits(32)

function full_bounds(E, a, r_tip) = {
  let a_top : bits(32) = a >> (E + 9);
  let a_tip : bits(3) = truncate(a >> (E + 6), 3);
  let r_mid : bits(9) = sail_zero_extend(r_tip, 9) << 6;
  let adjust : bits(32) = if (a_tip <+ r_tip) then 0xFFFFFFFF else 0x00000000;
  let r_bot : bits(32) = sail_zero_extend(r_mid, 32) << E;
  ((a_top + adjust) << (E + 9)) + r_bot
}

val inside_rep_bounds : (int, bits(32), bits(3), bits(32)) -> bool

function inside_rep_bounds(E, a, r_tip, i) = {
  let a_mid : bits(9) = truncate(a >> E, 9);
  let i_mid : bits(9) = truncate(i >> E, 9);
  let r_mid : bits(9) = sail_zero_extend(r_tip, 9) << 6;
  let s : bits(35) = sail_zero_extend(0b1, 35) << (E + 9);
  let in_limits : bool = if (0 <= signed(i)) then i_mid <+ (r_mid - a_mid - 0b000000001) else (i_mid >=+ (r_mid - a_mid) & r_mid != a_mid);
  E >= 23 | (abs_int(signed(i)) < unsigned(s) & in_limits)
}

$property
function prop_safe(E : int, a : bits(32), r : bits(3), i : bits(32)) -> bool = {
  if 0 <= E & E < 26 then {
    let r_b = full_bounds(E, a, r);
    let p = a + i;
    if inside_rep_bounds(E, a, r, i) then (sail_zero_extend(p-r_b, 35) <+ (sail_zero_extend(0b1, 35) << (E + 9))) else true;
  } else true;
}

$property
function prop(E : int, a : bits(32), r : bits(3), i : bits(32)) -> bool = {
  if 0 <= E then {
    let r_b = full_bounds(E, a, r);
    let p = a + i;
    let diff = (p >> E) - (r_b >> E);
    if (unsigned(diff) >= 1 & unsigned(diff) <= 510) then inside_rep_bounds(E, a, r, i) else true;
  } else true;
}
