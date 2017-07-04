
register int z

val unit -> int effect {wreg, rreg} test

function int test () = {
  nondet {
    z := 0;
    return z;
    z := 1;
  };
  z
}
