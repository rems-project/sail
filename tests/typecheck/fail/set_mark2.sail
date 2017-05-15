
function forall Nat 'N, 'N IN {32}. bit['N] Foo32( (bit['N]) x) = x

let x = Foo32( (bit[31]) 0)
