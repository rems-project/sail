default Order dec

$include <arith.sail>
$include <real.sail>
$include <exception_basic.sail>

val "prerr" : string -> unit
val "print" : string -> unit

val main : unit -> unit effect {escape}

function main() = {
  print_real("0.5 ", 0.5);
  print_real("1.0 ", 1.0);
  print_real("2.0 ", 2.0);
  print_real("2.5 ", 2.5);
  print_real("0.25 ", 0.25);
  print_real("0.1 ", 0.1);
  print_real("0.01 ", 0.01);
  print_real("0.001 ", 0.001);
  print_real("0.0001 ", 0.0001);
  print_real("0.00001 ", 0.00001);
  print_real("0.000001 ", 0.000001);
  print_real("0.0000001 ", 0.0000001);

  foreach (i from 1 to 1000 by 1 in inc) {
    let x = random_real();
    let y = random_real();
    let z = random_real();

    assert(x + y == y + x, "add_commutative");
    assert(x + 0.0 == x, "add_unit");
    assert((x + y) + z == x + (y + z), "add_assoc");
    assert(x + 1.0 >= x, "add_order");

    assert(x + x == 2.0 * x, "mult_two");

    assert(x * y == y * x, "mul_commutative");
    assert(x * 1.0 == x, "mul_unit");
    assert(x * 0.0 == 0.0, "mul_zero");
    assert((x * y) * z == x * (y * z), "mul_assoc");

    assert(x * (y + z) == (x * y) + (x * z), "mul_left_distrib");

    if not_bool(y == 0.0 | z == 0.0) then {
      assert((x * y) / y == x, "mul_div_cancel");
      assert((x + y) / z == (x / z) + (y / z), "div_right_distrib");
    } else {
      prerr("avoiding division by zero\n");
    };

    assert(abs_real(x) >= x, "abs_gteq_1");
    assert(abs_real(x) >= 0.0, "abs_gteq_2");

    assert(to_real(floor(x)) <= x, "floor_lteq");
    assert(to_real(ceil(x)) >= x, "ceil_gteq");

    if x >= 0.0 then {
       assert(abs_real(x) == x, "abs_id")
    };

    assert(sqrt(x * x) - abs_real(x) == 0.0, "sqrt_square_is_abs");

    let a = abs_real(x);
    let s = sqrt(a);
    assert(floor(abs_real(s * s - a)) == 0, "sqrt_floor_zero");
    assert(ceil(abs_real(s * s - a)) == 1, "sqrt_ceil_one");
    assert(abs_real((s * s) - a) <= 0.000000001, "sqrt_close");
    assert(abs_real((s * s) / a - 1.0) <= 0.000000001, "sqrt_close_relative");
    if x > 1.0 then {
      assert(s < x, "sqrt_lt");
    };

    assert(to_real(floor(x)) <= x, "floor_lteq");
    assert(to_real(ceil(x)) >= x, "ceil_gteq");
    assert(floor(to_real(floor(x))) == floor(x), "floor_to_real");
    assert(ceil(to_real(ceil(x))) == ceil(x), "floor_to_real");
  };

  print("ok\n");
}
