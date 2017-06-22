
default Order dec

register bit[3] test

val unit -> unit effect pure test
    
function unit test () =
{
  let i = 10 in {
    i := 20
  };
  z := 9;
  z := 10;
  test := 3
}