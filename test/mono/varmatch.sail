(* Check that when we case split on a variable that the constant propagation
   handles the default case correctly. *)

typedef AnEnum = enumerate { One; Two; Three }

function AnEnum foo((AnEnum) x) = {
  switch (x) {
  case One -> Two
  case y -> y
  }
}

val unit -> bool effect pure run

function run () = {
  foo(One) == Two &
  foo(Two) == Two &
  foo(Three) == Three
}
