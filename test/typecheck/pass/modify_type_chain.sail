
val unit -> unit effect pure test
    
function unit test () =
{
  ([|0:10|]) z := 9;
  ([|0:9|]) z := ([|0:8|]) 8
}