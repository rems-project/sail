struct rectangle = {
    width : int,
    height : int,
}

struct circle = { radius : int }

union shape = {
    Rectangle : rectangle,
    Circle : circle,
}

union my_option('a: Type) = {
  MySome : 'a,
  MyNone : unit
}

val is_none : forall ('a : Type). my_option('a) -> bool

function is_none opt = match opt {
  MySome(_) => false,
  MyNone()  => true
}

val use_is_none : forall ('a : Type). my_option('a) -> bool

function use_is_none opt = {
  is_none(opt)
}
