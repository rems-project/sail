
default Order dec

val cast int -> exist 'n. [:'n:] effect pure ex_int

val [:'n:] -> bit['n] effect pure zeros

val int -> unit effect pure test

function test n = {
  x := zeros(n)
}
