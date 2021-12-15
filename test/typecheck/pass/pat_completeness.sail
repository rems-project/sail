$sail_internal

union option ('a : Type) = {None : unit, Some : 'a}

union ast = {Foo : unit}

let x : option(ast) = Some(Foo())

let y : unit = match(x) {
  Some(Foo()) => (),
  Some(a)   => (),
  None()    => ()
}
