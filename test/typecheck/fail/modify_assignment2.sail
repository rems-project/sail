
val unit -> unit effect pure test
    
function unit test () =
{
  ([|0:9|]) z := 9;
  z := ([|0:10|]) 10
}