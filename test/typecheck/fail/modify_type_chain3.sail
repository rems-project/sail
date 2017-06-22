
val unit -> unit effect pure test
    
function unit test () =
{
  ([|0:6|]) z := 9;
  ([|0:7|]) z := ([|0:8|]) 8
}