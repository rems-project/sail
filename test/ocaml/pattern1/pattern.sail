
val unit -> unit effect pure main

function main () = {
  vec := 0x4F;
  switch vec {
    case (0b01 : (bit[2]) x : 0xF) ->
      if (x == 0b00) then print("pass") else print("x is incorrect")
    case _ -> print("pattern fail")
  }
}
