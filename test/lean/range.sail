default Order dec
$include <prelude.sail>


val f_int : range(0, 31) -> range(-2, 2)
function f_int(x) = {
  0
}

val f_nat : range(0, 31) -> range(0, 2)
function f_nat(x) = {
  0
}

val f_negvar : forall 'n. range(0, 'n) -> range(- 'n, 'n)
function f_negvar(x) = {
  x
}

val f_nnegvar : forall 'n. range(0, 'n) -> range(0, 'n)
function f_nnegvar(x) = {
  x
}

val f_unkn : forall 'n 'm. range('n, 'm) -> range('n, 'm)
function f_unkn(x) = {
  x
}
