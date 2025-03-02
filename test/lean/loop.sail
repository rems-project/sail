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
