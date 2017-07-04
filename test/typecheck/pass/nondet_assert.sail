
register int z

val unit -> int effect {wreg, rreg} test

function int test () = {
  nondet {
    z := 0;
    assert(false, "Nondeterministic assert");
    return z;
    z := 1;
  };
  z
}
