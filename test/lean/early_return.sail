default Order dec

$include <prelude.sail>
$include <arith.sail>

$[no_enum_number_conversions]
enum E = A | B | C

register r_A : E
register r_B : E
register r_C : E

register r : nat

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

function foreach_inner_earlyreturneffect(n : nat) -> bool = {
  foreach (i from 0 to n) {
    foreach (j from 0 to i) {
      if i > 5 then return false;
      r = r + 1;
    }
  };
  r > n
}

function foreach_inner_earlyreturnpure(n : nat) -> bool = {
  var res : nat = 0;
  foreach (i from 0 to n) {
    foreach (j from 0 to i) {
      if i > 5 then return false;
      res = res + 1;
    };
  };
  res > n
}

function foreach_inner_earlyreturneffect_catch(n : nat) -> bool = {
  foreach (i from 0 to n) {
    foreach (j from 0 to i) {
      if i > 5 then return false;
      r = r + 1;
    };
    r = r * 2;
  };
  r > n
}

function foreach_inner_earlyreturnpure_catch(n : nat) -> bool = {
  var res : nat = 0;
  foreach (i from 0 to n) {
    foreach (j from 0 to i) {
      if i > 5 then return false;
      res = res + 1;
    };
    res = res * 2;
  };
  res > n
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

function while_inner_earlyreturneffect(n : nat) -> bool = {
  while (r < n) do {
    while (r < n) do {
      if n > 5 then return false;
      r = r + 1;
    }
  };
  r > n
}

function while_inner_earlyreturnpure(n : nat) -> bool = {
  var res : nat = 0;
  while (res < n) do {
    while (res < n) do {
      if n > 5 then return false;
      res = res + 1;
    };
  };
  res > n
}

function while_inner_earlyreturneffect_catch(n : nat) -> bool = {
  while (r < n) do {
    while (r < n) do {
      if n > 5 then return false;
      r = r + 1;
    };
    r = r * 2;
  };
  r > n
}

function while_inner_earlyreturnpure_catch(n : nat) -> bool = {
  var res : nat = 0;
  while (res < n) do {
    while (res < n) do {
      if n > 5 then return false;
      res = res + 1;
    };
    res = res * 2;
  };
  res > n
}

function match_early_return(x : E) -> E = {
  match x {
    A => return r_A,
    B => r_B = A,
    C => r_C = A,
  };
  r_B
}

function match_early_return_inloop(x : E) -> E = {
  foreach (i from 0 to 10) {
    match x {
      A => return r_A,
      B => r_B = A,
      C => r_C = A,
    }};
  r_B
}

function match_early_return_inloop_2(x : E) -> E = {
  foreach (i from 0 to 10) {
    let y : E = match x {
      A => return r_A,
      B => r_B,
      C => r_C,
    }};
  r_B
}

function match_early_return_loop(x : E) -> E = {
  match x {
    A => foreach (i from 0 to 10) {
      return r_A
    },
    B => r_B = A,
    C => r_C = A,
  };
  r_B
}

function ite_early_return(x : bool) -> E = {
  r_A = r_C;
  let y : E = if x then return r_A else r_B;
  r_B
}

function ite_early_return_inloop(x : bool) -> E = {
  foreach (i from 0 to 10){
  r_A = r_C;
  let y : E = if x then return r_A else r_B;};
  r_B
}

function ite_early_return_loop(x : bool) -> E = {
  if x then foreach (i from 0 to 10) {
      return r_A
    } else r_B = A;
  r_B
}

function unit_type(x : E) -> unit = {
  r_A = x;
}

function ite_early_return_seq(x : bool) -> E = {
  r_A = r_C;
  let y : E = if x then {unit_type(A); return r_A} else r_B;
  r_B
}

function ite_early_return_exit(x : bool) -> E = {
  r_A = r_C;
  let y : E = if x then return r_A else r_B;
  if x then exit();
  r_B
}

