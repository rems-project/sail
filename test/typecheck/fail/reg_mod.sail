
register [|0:10|] reg

val unit -> unit effect pure test
    
function unit test () =
{
  reg := 9;
  reg := 10;
  reg := 8
}