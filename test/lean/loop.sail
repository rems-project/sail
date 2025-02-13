default Order dec

$include <prelude.sail>
$include <arith.sail>

register r : int

function foreachloop(m : nat, n : nat) -> int = {
  var res : int = 0;
  foreach (i from m to n) {
    res = res + 1;
  };
  res
}

function foreachloopmon(m : nat, n : nat) -> int = {
  foreach (i from n to m) {
    r = r + 1;
  };
  r
}

function foreachloopboth(m : nat, n : nat) -> int = {
  var res : int = 0;
  foreach (i from n to m) {
    res = res + 1;
    r = r + res;
  };
  res + 1
}

function foreachloopmultiplevar(m : nat, n : nat) -> int = {
  var res : int = 0;
  var mult : int = 1;
  foreach (i from m to n) {
    res = res + 1;
    mult = res * mult;
  };
  mult
}

function foreachloopuseindex(m : nat, n : nat) -> nat = {
  var res : nat = 0;
  foreach (i from m to n) {
    res = res + i;
  };
  res
}
