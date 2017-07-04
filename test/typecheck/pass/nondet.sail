
register int z

val unit -> unit effect {wreg} test

function unit test () = {
  nondet {
    z := 0;
    z := 1;
    z := 2;
  }
}
