default Order dec

val foo : forall ('a : Type). 'a -> ('a, 'a)

function foo x = {
  (x, x)
}
