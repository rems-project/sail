
val unit -> unit effect pure test
    
function unit test () =
{
  ([|0:10|]) z := 9;
  ([|0:11|]) z := ([|0:13|]) 8
}