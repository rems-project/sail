
register int z

function int test () = {
  nondet {
    z := 0;
    assert(false, "Nondeterministic assert");
    return z;
    z := 1;
  };
  z
}
