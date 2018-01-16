type ty = list(vector(8, inc, bit))

val foo : ty -> bool

function foo l = match l {
  _ :: _ => false,
  _ => true
}
