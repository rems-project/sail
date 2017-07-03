
register int z

function int test () = {
  nondet {
    z := 0;
    return z;
    z := 1;
  };
  z
}
