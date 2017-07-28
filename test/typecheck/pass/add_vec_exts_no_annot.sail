default Order dec

val forall Nat 'n, Nat 'm, Nat 'o, Nat 'p, Order 'ord.
    vector<'o, 'n, 'ord, bit> -> vector<'p, 'm, 'ord, bit> effect pure exts

overload EXTS [exts]

val forall Nat 'n, Nat 'o, Order 'ord.
    (vector<'o, 'n, 'ord, bit>, vector<'o, 'n, 'ord, bit>) -> vector<'o, 'n, 'ord, bit> effect pure add_vec

overload (deinfix +) [add_vec]

val (bit[32], bit[32]) -> unit effect pure test

function test (x, y) =
{
  let (bit[64]) z = add_vec(exts(x), exts(y)) in
  ()
}
