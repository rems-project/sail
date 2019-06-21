default Order dec
$include <prelude.sail>

val f : int -> range(2,6) effect {escape}

val g1 : (bool,int) -> range(0,8) effect {escape}

function g1(b,x) = {
  if b then
    return f(x)
  else {
    return f(x+1);
    5
  }
}

val g2 : int -> range(0,8) effect {escape}

function g2(x) = f(x)
