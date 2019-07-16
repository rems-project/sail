function Poly32Mod2 (data__arg, poly) = {
  data = data__arg;
  assert('N > 32, "(N > 32)");
  let poly' : bits('N) = extzv(poly) in
  foreach (i from ('N - 1) to 32 by 1 in dec)
    if [data[i]] == 0b1 then data = data | (poly' << i - 32) else ();
  return(slice(data, 0, 32))
}
