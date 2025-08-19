default Order dec

$include <prelude.sail>
$include <arith.sail>

register r : nat

function foreach_loop(m : nat, n : nat) -> nat = {
  var res : nat = 0;
  foreach (i from m to n) {
    res = res + 1;
  };
  res
}

function foreach_loopmon(m : nat, n : nat) -> nat = {
  foreach (i from n to m) {
    r = r + 1;
  };
  r
}

function foreach_loopboth(m : nat, n : nat) -> nat = {
  var res : nat = 0;
  foreach (i from n to m) {
    res = res + 1;
    r = r + res;
  };
  res + 1
}

function foreach_loopmultiplevar(m : nat, n : nat) -> nat = {
  var res : nat = 0;
  var mult : nat = 1;
  foreach (i from m to n) {
    res = res + 1;
    mult = res * mult;
  };
  mult
}

function foreach_loopuseindex(m : nat, n : nat) -> nat = {
  var res : nat = 0;
  foreach (i from m to n) {
    res = res + i;
  };
  res
}

function while_loop(m : nat, n : nat) -> nat = {
  var res : nat = 0;
  while (res < n) do {
    res = res + 1;
  };
  res
}

function while_loopmon(m : nat, n : nat) -> nat = {
  while (r < n) do {
    r = r + 1;
  };
  r
}

function while_loopboth(m : nat, n : nat) -> nat = {
  var res : nat = 0;
  while (res < n) do {
    res = res + 1;
    r = r + res;
  };
  res + 1
}

function while_loopmultiplevar(m : nat, n : nat) -> nat = {
  var res : nat = 0;
  var mult : nat = 1;
  while (res < n) do {
    res = res + 1;
    mult = res * mult;
  };
  mult
}

val while_print : unit -> unit
function while_print() = {
  var i : int = 0;
  while i < 10 do {
    i = i + 1
  };
  print_int("i = ", i)
}


val while_print_fuel : unit -> unit
function while_print_fuel() = {
  var i : int = 0;
  while i < 100 do {
    i = i + 1
  };
  print_int("i = ", i)
}
termination_measure while_print_fuel while 100

val until_print_fuel : int -> unit
function until_print_fuel(n) = {
  var i : int = 0;
  repeat
    i = i + 1
  until i < 100;
  print_int("i = ", i)
}
termination_measure until_print_fuel repeat n

val while_print_long : unit -> unit
function while_print_long() = {
  var this_is_a_very_long_variable_name_to_stress_the_formatting : int = 0;
  while this_is_a_very_long_variable_name_to_stress_the_formatting + this_is_a_very_long_variable_name_to_stress_the_formatting < 10 do {
    this_is_a_very_long_variable_name_to_stress_the_formatting = this_is_a_very_long_variable_name_to_stress_the_formatting + 1
  };
  print_int("i = ", this_is_a_very_long_variable_name_to_stress_the_formatting)
}

val nothing : unit -> unit
function nothing() : unit = ()

val foreachpure : (int, int) -> unit
function foreachpure (n : int, m : int) = {
  x : int = n;
  foreach (rr from 0 to (m - 1) by 1 in inc) {
    let 'vec = n in
      {
          foreach (i from 0 to (m - 1) by 1 in inc) { nothing(); }
      };
    x = x + 1;
  }
}

val foreachnotsopure : (nat, int) -> unit
function foreachnotsopure (n : nat, m : int) = {
  x : nat = n;
  foreach (rr from 0 to (m - 1) by 1 in inc) {
    let 'vec = n in
      {
          foreach (i from 0 to (m - 1) by 1 in inc) { r = x; }
      };
    x = x + 1;
  }
}
