default Order dec

$include <prelude.sail>

register R : nat
register B : bool

function elif(n : nat) -> bit = {
  if n == 0 then
    bitone
  else if n == 1 then
    bitone
  else
    bitzero
}

function monadic_in_out(n : nat) -> nat = {
    if B then
        R = n
    else
        ();
    R
}

function monadic_lines(n : nat) -> unit = {
    let b = n == 0;
    if b then {
        R = n;
        B = b
    }
    else
        B = b
}