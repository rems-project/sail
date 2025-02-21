default Order dec

$include <prelude.sail>
$include <arith.sail>

register r : int

function foreach_loop(m : nat, n : nat) -> int = {
  var res : int = 0;
  foreach (i from m to n) {
    res = res + 1;
  };
  res
}

function foreach_loopmon(m : nat, n : nat) -> int = {
  foreach (i from n to m) {
    r = r + 1;
  };
  r
}

function foreach_loopboth(m : nat, n : nat) -> int = {
  var res : int = 0;
  foreach (i from n to m) {
    res = res + 1;
    r = r + res;
  };
  res + 1
}

function foreach_loopmultiplevar(m : nat, n : nat) -> int = {
  var res : int = 0;
  var mult : int = 1;
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

function foreach_earlyreturneffect(n : nat) -> bool = {
  foreach (i from 0 to n) {
    if i > 5 then return false;
    r = r + 1;
  };
  r > n
}

function foreach_earlyreturnpure(n : nat) -> bool = {
  var res : nat = 0;
  foreach (i from 0 to n) {
    if i > 5 then return false;
    res = res + i;
  };
  res > n
}

function while_loop(m : nat, n : nat) -> int = {
  var res : int = 0;
  while (res < n) do {
    res = res + 1;
  };
  res
}

function while_loopmon(m : nat, n : nat) -> int = {
  while (r < n) do {
    r = r + 1;
  };
  r
}

function while_loopboth(m : nat, n : nat) -> int = {
  var res : int = 0;
  while (res < n) do {
    res = res + 1;
    r = r + res;
  };
  res + 1
}

function while_loopmultiplevar(m : nat, n : nat) -> int = {
  var res : int = 0;
  var mult : int = 1;
  while (res < n) do {
    res = res + 1;
    mult = res * mult;
  };
  mult
}

function while_earlyreturneffect(n : nat) -> bool = {
  while (r < n) do {
    if r > 5 then return false;
    r = r + 1;
  };
  r > n
}

function while_earlyreturnpure(n : nat) -> bool = {
  var res : nat = 0;
  while (res < n) do {
    if res > 5 then return false;
    res = res + 1;
  };
  res > n
}