
val foo : forall 'n. int('n) -> unit

function foo(x) = {
  let _ = foo(sizeof('n));
  ()
}
