
register int z

function int test () = {
  nondet {
    z := 0;
    z := 1;
    z
  }
}
