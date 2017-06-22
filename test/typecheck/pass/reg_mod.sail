
register [|0:10|] reg

val unit -> unit effect {wreg} test
    
function unit test () =
{
  reg := 9;
  reg := 10;
  reg := 8
}