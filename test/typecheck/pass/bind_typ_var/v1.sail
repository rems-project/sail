
val mk_vector : unit -> {'n, 'n in {32, 64}. vector('n, dec, bit)}

val mk_square : unit -> {'n 'm, 'n == 'm. vector('n, dec, vector('m, dec, bit))}

val test : unit -> unit

function test () = {
  let v as vector('len, _, _) = mk_vector ();
  // could still be
  let v2 as 'len2 = mk_vector ();
  let matrix as vector('width, 'height) = mk_square ();
  _prove(constraint('width == 'height));
  _prove(constraint('len == 32 | 'len == 64));
  _prove(constraint('len2 == 32 | 'len2 == 64));
  ()
}
