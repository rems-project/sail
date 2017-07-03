
register int z

function unit test () = {
  nondet {
    z := 0;
    z := 1;
    z := 2;
  }
}
